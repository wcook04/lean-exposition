#!/usr/bin/env python3
"""Import exact annotation review returns into a captured Library publication."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile


def read_json(path):
    return json.loads(path.read_bytes())


def jsonl(archive, name):
    return [json.loads(line) for line in archive.read(name).splitlines() if line]


def write_json(path, data, *, compact=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":") if compact else None,
                               indent=None if compact else 2) + ("" if compact else "\n"), encoding="utf-8")


def digest(text):
    return sha256(text.encode("utf-8")).hexdigest()


def annotation_rows(payload):
    return {f"{tie.get('phrase') or tie['at']}|{row['name']}|{number}": row
            for tie in payload["ties"] for number, row in enumerate(tie.get("rows", []), 1)
            if isinstance(row.get("annotation"), str)}


def document_paths(paper, slot):
    edition = paper / "edition"
    folder = edition / "docs" / slot
    stage = "short" if (folder / "index.json").is_file() else slot
    index = read_json((folder if stage != slot else edition) / "index.json")
    return (edition / index["documents"][stage], edition / index["responses"][f"/ties/{stage}"])


def source_slot(root, paper, slot):
    if paper == "pcp" and slot == "guide-short":
        return root / paper / "reading-guide", "short"
    return root / paper, slot


def occurrence(text, needle, index):
    if not needle or not isinstance(index, int) or index < 1:
        return None
    start = 0
    for _ in range(index):
        start = text.find(needle, start)
        if start < 0:
            return None
        end = start + len(needle)
        start = end
    return end - len(needle), end


LITERALS = re.compile(r"`[^`]*`|(?<!\\)\$(?:\\.|[^$])*\$|https?://[^\s)]+")
KEY = re.compile(r"[a-z0-9][a-z0-9.:/-]*\Z")
NUMBER = re.compile(r"[a-z]?\.?\d+(?:\.\d+)*(?:[a-z])?\Z", re.I)
REFERENCE_KIND = {
    "equation": r"Equations?|Eqs?\.?",
    "section": r"Sections?|Sects?\.?|§",
    "figure": r"Figures?|Figs?\.?",
    "proof-item": r"Items?|Steps?",
    "condition": r"Conditions?|Clauses?",
    "page": r"pages?|pp?\.?",
}


def reference_candidates(text, row):
    """Locate reader-visible labels within the exact reviewed window."""
    target = row["target"]
    kind, _, suffix = target["key"].partition(":")
    printed = target.get("printed_label") or suffix
    number = printed.strip("()")
    candidates = []

    def add(pattern, priority):
        if pattern:
            candidates.extend((match.start(), match.end(), priority)
                              for match in re.finditer(pattern, text, flags=re.I))

    label = row.get("display")
    if label:
        add(re.escape(label), 0)
        if kind == "proof-item":
            add(re.escape(re.sub(r"\s+\(Section [^)]+\)$", "", label)), 1)
        if kind == "equation":
            for numbered in re.findall(r"\([Mm]\.[A-Za-z0-9.]+\)", label):
                add(re.escape(numbered), 1)
        for i, code in enumerate(reversed(re.findall(r"`[^`]+`", label))):
            add(re.escape(code), 1 + i)
    if NUMBER.fullmatch(number):
        normalized = re.escape(number)
        boundary = r"(?![\w.]\d|\w)"
        kind_pattern = REFERENCE_KIND.get(kind, re.escape(kind))
        add(rf"(?<!\w)(?:{kind_pattern})\s*(?:\({normalized}\)|{normalized}){boundary}", 1)
        add(rf"\({normalized}\)", 2)
        add(rf"(?<![\w.]){normalized}{boundary}", 3)
    elif printed:
        add(rf"`{re.escape(printed)}`", 1)
        if len(printed) >= 3:
            add(rf"(?<!\w){re.escape(printed)}(?!\w)", 2)
    original = row["original"]
    if len(original) < 112:
        add(re.escape(original), 4)

    literals = [m.span() for m in LITERALS.finditer(text)]
    return sorted(set((start, end, rank) for start, end, rank in candidates
                      if all(end <= a or start >= b or (start == a and end == b and text[a] == "`")
                             for a, b in literals)), key=lambda item: (item[2], item[0], -item[1]))


def resolve_target(paper, source, row, targets, overrides, palettes):
    citation = row["target"]
    slot = citation["slot"]
    key = citation["key"].lower()
    line = citation.get("markdown_line")
    page = citation.get("pdf_page")
    if not KEY.fullmatch(key):
        return None
    key = overrides.get((paper, slot, key, line, page), key)
    record = targets[paper, slot].get(key)
    if not record:
        return None
    if line is not None and ("line" not in record or abs(line - record["line"]) > 4):
        return None
    if page is not None and record.get("page", page) != page:
        return None
    if slot != source:
        # These are links to a different edition of the same Library paper.
        if "guide-" in (source + slot):
            return None
        alias = f"{slot}/{key}"
        colours = palettes[paper, slot].get(record.get("tone"))
        targets[paper, source][alias] = {**record, "stage": slot, **({"colours": colours} if colours else {})}
        return alias
    return key


def edit_ranges(text, edits, resolved, report):
    ranges = []
    verified = {ref["target"]["key"] for ref, _, _ in resolved}
    for edit in edits:
        span = occurrence(text, edit["old"], edit["occurrence"])
        keyset = set(edit["reference_keys"])
        if not span:
            report["edit source missing"] += 1
            continue
        a, b = span
        if not keyset <= verified:
            report["edit destination unverified"] += 1
            continue
        old, new = edit["old"], edit["new"]
        if [(m[0], m[0][0]) for m in LITERALS.finditer(old) if m[0][0] != "`"] != [
            (m[0], m[0][0]) for m in LITERALS.finditer(new) if m[0][0] != "`"
        ]:
            report["edit changes mathematics or URL"] += 1
            continue
        exposed = {ref["target"]["key"] for ref, _, _ in resolved if ref["target"]["key"] in keyset
                   and any(rank < 4 for _, _, rank in reference_candidates(new, ref))}
        if not exposed:
            report["edit does not expose its reference"] += 1
            continue
        if any(a < end and b > start for start, end, _, _ in ranges):
            if (a, b, new, keyset) not in ranges:
                report["edit overlaps another change"] += 1
            continue
        ranges.append((a, b, new, exposed))
    return sorted(ranges)


def render_ranges(text, edits):
    pieces = []
    mapped = []
    cursor = offset = 0
    for start, end, replacement, keys in edits:
        pieces.extend((text[cursor:start], replacement))
        mapped.append((start, end, start + offset, start + offset + len(replacement), keys))
        offset += len(replacement) - (end - start)
        cursor = end
    return "".join(pieces) + text[cursor:], mapped


def bind_annotation(text, refs, edits, paper, slot, targets, overrides, palettes, report):
    resolved = []
    for ref in refs:
        if ref["status"] != "verified":
            report[f"reference {ref['status']}"] += 1
            continue
        key = resolve_target(paper, slot, ref, targets, overrides, palettes)
        span = occurrence(text, ref["original"], ref["occurrence"])
        if not key or not span:
            report["reference destination unverified" if not key else "reference source missing"] += 1
            continue
        resolved.append((ref, key, span))

    accepted = edit_ranges(text, edits, resolved, report)
    final, mapped = render_ranges(text, accepted)
    report["edits applied"] += len(accepted)
    spans = []
    for ref, key, (start, end) in sorted(resolved, key=lambda item: item[2]):
        delta = 0
        for a, b, x, y, keys in mapped:
            if start < b and end > a and ref["target"]["key"] in keys:
                window = (x, y)
                break
            if b <= start:
                delta = y - b
        else:
            window = (start + delta, end + delta)
        a, b = window
        for left, right, rank in reference_candidates(final[a:b], ref):
            if rank == 4 and (a, b) != (start + delta, end + delta):
                continue
            candidate = (a + left, a + right, key)
            if candidate in spans:
                break
            if all(candidate[1] <= x or candidate[0] >= y for x, y, _ in spans):
                spans.append(candidate)
                break
        else:
            report["reference label unavailable"] += 1
    for a, b, x, y, keys in mapped:
        for ref, key, _ in resolved:
            if ref["target"]["key"] not in keys or any(x <= start < y and found == key for start, _, found in spans):
                continue
            for left, right, rank in reference_candidates(final[x:y], ref):
                if rank < 4 and all(x + right <= start or x + left >= end for start, end, _ in spans):
                    spans.append((x + left, x + right, key))
                    break
    report["reference occurrences linked"] += len(spans)
    return final, [
        {"start": len(final[:start].encode("utf-16-le")) // 2,
         "end": len(final[:end].encode("utf-16-le")) // 2, "key": key}
        for start, end, key in sorted(spans)
    ]


def apply_overlay(manifest, publication):
    """Reapply the reviewed rows when rebuilding the exact same paper and annotation edition."""
    overlay = read_json(manifest)
    if overlay["schema"] != "reviewed-annotation-references/1":
        raise ValueError(f"{manifest}: unsupported review overlay")
    updates = []
    for slot, stage in overlay["slots"].items():
        body, tie_path = document_paths(publication, slot)
        if sha256(body.read_bytes()).hexdigest() != stage["paper_sha256"]:
            raise ValueError(f"{body}: manuscript changed since reference review")
        payload = read_json(tie_path)
        rows = annotation_rows(payload)
        for key, change in stage["annotations"].items():
            row = rows[key]
            original = row["annotation"]
            reviewed = change.get("annotation", original)
            if digest(original) != change["base"] and original != change.get("annotation"):
                raise ValueError(f"{tie_path}: annotation changed since reference review at {key}")
            row["annotation"] = reviewed
            row["annotation_references"] = change["references"]
        updates.append((tie_path, payload, True))
        reference_path = publication / "paper-references" / f"{slot}.json"
        targets = read_json(reference_path)["targets"] if reference_path.is_file() else {}
        targets.update(stage["target_updates"])
        missing = {reference["key"] for change in stage["annotations"].values()
                   for reference in change["references"]} - targets.keys()
        if missing:
            raise ValueError(f"{reference_path}: missing reviewed target {min(missing)}")
        updates.append((reference_path, {"schema": "paper-references/1", "targets": targets}, False))
    for path, data, compact in updates:
        write_json(path, data, compact=compact)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("publication", type=Path)
    parser.add_argument("assignments", type=Path)
    parser.add_argument("supplement", type=Path)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("returns", type=Path, nargs="+")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    targets = defaultdict(dict)
    palettes = {}
    paths = {}
    docs = {}
    supplement = read_json(args.supplement)
    overrides = {tuple(row[:5]): row[5] for row in supplement.get("aliases", [])}
    corrections = {tuple(row[:3]): row[3] for row in supplement.get("edit_corrections", [])}
    totals = Counter()
    receipts = {}
    exceptions = []

    def document(paper, slot):
        key = (paper, slot)
        if key not in docs:
            folder, native = source_slot(args.publication, paper, slot)
            body, ties = document_paths(folder, native)
            index = folder / "paper-references" / f"{native}.json"
            prior = read_json(index)["targets"] if index.is_file() else {}
            targets[key].update(prior)
            targets[key].update(supplement.get("targets", {}).get(paper, {}).get(slot, {}))
            payload = read_json(ties)
            palettes[key] = {topic["tone"]: {theme: topic[theme] for theme in ("light", "dark")}
                             for topic in payload.get("topics", []) if topic.get("light") and topic.get("dark")}
            docs[key] = body, ties, payload, prior
            paths[key] = index
        return docs[key]

    for path in args.returns:
        report = Counter()
        with ZipFile(path) as archive:
            review = json.loads(archive.read("review.json"))
            refs = jsonl(archive, "references.jsonl")
            edits = jsonl(archive, "annotation-edits.jsonl")
        if not re.fullmatch(r"[0-9]{2}-[a-z0-9-]+", review["packet"]) or not path.name.startswith(review["packet"] + "-"):
            raise ValueError(f"{path}: unexpected packet name")
        with ZipFile(args.assignments / f"{review['packet']}.zip") as outbound:
            assigned = {row["id"]: row for row in jsonl(outbound, "assigned-annotations.jsonl")}
            metadata = json.loads(outbound.read("manifest.json"))
        paper = metadata["reader"]
        if set(review["completed_annotation_ids"]) != assigned.keys():
            raise ValueError(f"{path}: review IDs differ from the assignment")
        refs_by_id, edits_by_id = defaultdict(list), defaultdict(list)
        for entries, grouped in ((refs, refs_by_id), (edits, edits_by_id)):
            for row in entries:
                anchor = assigned[row["annotation_id"]]
                if row["annotation_sha256"] != anchor["annotation_sha256"]:
                    raise ValueError(f"{path}: review digest differs from the assignment")
                if grouped is edits_by_id:
                    correction = corrections.get((review["packet"], row["annotation_id"], row["old"]))
                    if correction is not None:
                        row["new"] = correction
                grouped[row["annotation_id"]].append(row)
        report["annotations reviewed"] = len(assigned)
        for slot in {row["slot"] for row in assigned.values()}:
            body, tie_path, payload, _ = document(paper, slot)
            expected = metadata["source_editions"][slot]["manuscript_sha256"]
            if sha256(body.read_bytes()).hexdigest() != expected:
                raise ValueError(f"{body}: publication manuscript differs from the assignment")
            current = annotation_rows(payload)
            for ident, base in assigned.items():
                if base["slot"] != slot:
                    continue
                row = current[ident.split("|", 1)[1]]
                annotation = row["annotation"]
                if digest(annotation) != base["annotation_sha256"]:
                    raise ValueError(f"{tie_path}: annotation drift at {ident}")
                references = refs_by_id.get(ident, [])
                if not references:
                    continue
                for ref in references:
                    if ref["status"] == "verified":
                        document(paper, ref["target"]["slot"])
                prior = report.copy()
                new, spans = bind_annotation(annotation, references, edits_by_id.get(ident, []),
                                             paper, slot, targets, overrides, palettes, report)
                reasons = {name: count for name, count in (report - prior).items()
                           if name not in {"edits applied", "reference occurrences linked"}}
                if reasons:
                    exceptions.append({"packet": review["packet"], "id": ident, "reasons": reasons,
                                       "resolved_links": spans})
                if new != annotation:
                    row["annotation"] = new
                    report["annotation texts changed"] += 1
                row["annotation_references"] = spans
        receipts[path.name] = dict(report)
        totals.update(report)

    if args.write:
        for key, (_, path, payload, prior) in docs.items():
            if payload != read_json(path):
                write_json(path, payload, compact=True)
            if targets[key] != prior:
                write_json(paths[key], {"schema": "paper-references/1", "targets": targets[key]})
    write_json(args.receipt, {"total": dict(totals), "packets": receipts, "exceptions": exceptions})
    print(json.dumps(dict(totals), indent=2))


if __name__ == "__main__":
    if sys.argv[1:2] == ["--apply-overlay"]:
        if len(sys.argv) != 4:
            raise SystemExit("Usage: import_annotation_references.py --apply-overlay OVERLAY_JSON DIST")
        apply_overlay(Path(sys.argv[2]), Path(sys.argv[3]))
    else:
        main()
