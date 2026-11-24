#!/usr/bin/env python3
"""Project revised declaration titles onto fixed-path responses of a captured reader."""
from __future__ import annotations

import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

if __package__:
    from .apply_passage_annotations import unique_keys
else:
    from apply_passage_annotations import unique_keys


STAGES = ("short", "long", "expository")
REVISION = re.compile(r"[0-9a-f]{40}\Z")


def digest(content):
    return sha256(content).hexdigest()


def read_capture(path):
    if path.resolve() != path:
        raise ValueError(f"{path}: expected a regular path in the published artifact")
    raw = path.read_bytes()
    return raw, json.loads(raw, object_pairs_hook=unique_keys)


def titles_only(data):
    if not isinstance(data, dict) or any(
        not name or not isinstance(title, str) or not title or title.strip() != title
        or any(ord(char) < 32 for char in title)
        for name, title in data.items()
    ):
        raise ValueError("Expected an object from exact Lean names to single-line display titles")
    return data


def title_source(path):
    _, data = read_capture(path.resolve())
    if not isinstance(data, dict) or data.keys() - {"names", "slots"} or "names" not in data:
        raise ValueError(f"{path}: expected names and optional slots")
    names = titles_only(data["names"])
    slots = data.get("slots", {})
    if not isinstance(slots, dict) or any(
        not slot or not isinstance(parts, list) or not parts for slot, parts in slots.items()
    ):
        raise ValueError(f"{path}: expected slot names mapped to one title map per part")
    return names, {slot: [titles_only(part) for part in parts] for slot, parts in slots.items()}


def capture_file(edition, index, route, expected):
    recorded = index["responses"].get(route)
    if recorded is None:
        return None
    if recorded != expected:
        raise ValueError(f"{edition}: {route} does not name the fixed response {expected}")
    return edition / expected


def show_name(row):
    return row.get("name") or row.get("declaration")


def named_rows(value):
    if isinstance(value, dict):
        if "plain" in value and show_name(value):
            yield value
        for item in value.values():
            yield from named_rows(item)
    elif isinstance(value, list):
        for item in value:
            yield from named_rows(item)


def serialize(raw, value):
    if raw.endswith(b"\n"):
        return (json.dumps(value, ensure_ascii=False) + "\n").encode()
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()


def project_edition(artifact, root, edition, names, slots, known):
    """Prepare changed title payloads without writing to the captured edition."""
    index_path = edition / "index.json"
    index_raw, index = read_capture(index_path)
    prefix = "" if root == edition else f"{edition.relative_to(root)}/"

    def response(route, file):
        return capture_file(root, index, route, prefix + file)
    updates = {}
    used = set()
    used_slots = set()
    rh = "proof_source" in index
    rh_records = {"lean." + digest(name.encode())[:24]: title for name, title in names.items()} if rh else {}

    def apply(path, mutate):
        if path is None:
            return
        raw, payload = read_capture(path)
        scopes = defaultdict(int)

        def set_title(row, field, title, scope):
            if title is not None and row.get(field) != title:
                row[field] = title
                scopes[scope] += 1

        mutate(payload, set_title)
        if scopes:
            data = serialize(raw, payload)
            updates[path.relative_to(artifact)] = (data, {
                "before_sha256": digest(raw), "after_sha256": digest(data), "fields": dict(scopes),
            })

    def align(payload, set_title, *, full=False):
        if full:
            for name in sorted(names.keys() & known):
                set_title(payload["names"], name, names[name], "names[Lean name]")
                used.add(name)
        for row in named_rows(payload.get("records", payload)):
            set_title(row, "plain", names.get(show_name(row)), "Lean rows[].plain")
        if rh and full:
            for rid, row in payload.get("records", {}).items():
                set_title(row, "short", rh_records.get(rid), "records[declaration ID].short")

    for route, file in (("/alignment", "alignment.json"), ("/alignment/core", "alignment/core.json")):
        apply(response(route, file), lambda payload, put: align(payload, put, full=True))

    for stage in STAGES:
        context = slots.get(stage)
        seen = set()
        tied = defaultdict(set)

        def title(name, part):
            if context is not None and part < len(context) and name in context[part]:
                seen.add((part, name))
                return context[part][name]
            return names.get(name)

        def ties(payload, set_title):
            for tie in payload["ties"]:
                part = tie.get("part", 0)
                name = show_name(tie)
                if name:
                    set_title(tie, "plain", title(name, part), "ties[].plain")
                for row in tie.get("rows") or ():
                    if "phrase" in tie:
                        tied[part].add(row["name"])
                    set_title(row, "plain", title(row["name"], part), "ties[].rows[].plain")

        def phrases(payload, set_title):
            for part, item in enumerate(payload["parts"]):
                for name in sorted(item["titles"].keys() | (tied[part] & names.keys())):
                    set_title(item["titles"], name, title(name, part), "parts[].titles[Lean name]")

        apply(response(f"/alignment/{stage}", f"alignment/{stage}.json"), align)
        apply(response(f"/ties/{stage}", f"ties/{stage}.json"), ties)
        apply(response(f"/phrases/{stage}", f"phrases/{stage}.json"), phrases)
        if context is not None:
            expected = {(part, name) for part, titles in enumerate(context) for name in titles}
            if missing := expected - seen:
                raise ValueError(f"{edition}: unknown {stage} part and declaration {min(missing)!r}")
            used_slots.add(stage)

    if rh:
        # RH records are generated from the declarations themselves. Their fixed-path
        # cards repeat the Lean title, whereas native argument records have their own labels.
        for rid, title in rh_records.items():
            if not (path := edition / f"alignment/record/{rid}.json").is_file():
                continue
            def record(payload, set_title):
                align(payload, set_title)
                set_title(payload, "short", title, "declaration record.short")
            apply(path, record)

        def cards(payload, set_title):
            for row in payload:
                set_title(row, "label", rh_records.get(row["id"]), "declaration card.label")

        if index["summaries_by_table"].get("nodes") == "rh-paper-nodes.json":
            apply(edition / "rh-paper-nodes.json", cards)

        for path in sorted((edition / "lean/module").glob("*.json")):
            def module(payload, set_title):
                for row in payload["declarations"]:
                    set_title(row, "display_title", names.get(row["name"]), "declarations[].display_title")
                    neighbourhood = row.get("neighbourhood", {})
                    for direction in ("dependencies", "users"):
                        for neighbour in neighbourhood.get(direction, ()):
                            set_title(neighbour, "display_title", names.get(neighbour["name"]),
                                      "declarations[].neighbourhood[].display_title")
            apply(path, module)

    return updates, digest(index_raw), used, used_slots


def project(artifact, mount, names, slots=None):
    slots = slots or {}
    edition = (artifact / mount / "edition").absolute()
    if artifact not in edition.parents or edition.resolve() != edition:
        raise ValueError(f"{edition}: invalid artifact mount")
    _, main_index = read_capture(edition / "index.json")
    lean_path = capture_file(edition, main_index, "/lean/names", "lean/names.json")
    if lean_path is None:
        raise ValueError(f"{edition}: missing the compiled declaration name index")
    _, lean = read_capture(lean_path)
    known = {row[0] for row in lean["names"]}
    if "proof_source" in main_index:
        core_path = capture_file(edition, main_index, "/alignment/core", "alignment/core.json")
        if core_path:
            _, core = read_capture(core_path)
            known.update(name for step in core.get("steps", {}).values() for name in step.get("route", ()))
        for file in (edition / "lean/module").glob("*.json"):
            _, module = read_capture(file)
            for row in module["declarations"]:
                neighbourhood = row.get("neighbourhood", {})
                for direction in ("dependencies", "users"):
                    known.update(neighbour["name"] for neighbour in neighbourhood.get(direction, ()))
    updates, indexes, used, used_slots = {}, {}, set(), set()
    children = sorted((edition / "docs").glob("*/index.json"))
    for path in [edition, *(child.parent for child in children)]:
        if path == edition:
            stages = {stage: slots[stage] for stage in STAGES if stage in slots}
        else:
            stages = {"short": slots[path.name]} if path.name in slots else {}
        files, index_hash, names_used, stages_used = project_edition(artifact, edition, path, names, stages, known)
        updates.update(files)
        indexes[str((path / "index.json").relative_to(artifact))] = index_hash
        used.update(names_used)
        used_slots.update(stages_used if path == edition else {path.name} if stages_used else ())
    if missing := names.keys() - used:
        raise ValueError(f"{edition}: {len(missing)} title(s) absent from its Lean index, including {min(missing)!r}")
    if missing := slots.keys() - used_slots:
        raise ValueError(f"{edition}: {len(missing)} slot(s) absent from the capture, including {min(missing)!r}")
    return updates, indexes


def graph_title_coverage(artifact, mount, updates=None):
    """Check the names a dependency card can display, including declarations with no passage."""
    edition = (artifact / mount / "edition").absolute()
    if artifact not in edition.parents or edition.resolve() != edition:
        raise ValueError(f"{edition}: invalid artifact mount")
    _, index = read_capture(edition / "index.json")

    def effective(path):
        change = (updates or {}).get(path.relative_to(artifact))
        return json.loads(change[0]) if change else read_capture(path)[1]

    compiled = capture_file(edition, index, "/lean/names", "lean/names.json")
    if compiled is None:
        raise ValueError(f"{edition}: missing the compiled declaration name index")
    rows = effective(compiled)["names"]
    owners = defaultdict(set)
    for name, _kind, module, *_ in rows:
        owners[name].add(module)

    sources = {}
    for route, file in (("/alignment/core", "alignment/core.json"), ("/alignment", "alignment.json")):
        path = capture_file(edition, index, route, file)
        if path is not None:
            sources[route] = effective(path)["names"]
    if not sources:
        raise ValueError(f"{edition}: missing the alignment titles")

    missing, identifiers, inconsistent = [], [], []
    for name in sorted(owners):
        values = {titles.get(name) for titles in sources.values()}
        if len(values) > 1:
            inconsistent.append(name)
        if None in values or "" in values:
            missing.append(name)
        short = name.rsplit(".", 1)[-1].replace("_", " ").casefold()
        if any(value and value.casefold() in {name.casefold(), short} for value in values):
            identifiers.append(name)
    return {
        "compiled_declarations": len(rows),
        "unique_names": len(owners),
        "names_in_multiple_modules": sorted(name for name, modules in owners.items() if len(modules) > 1),
        "without_explicit_title": missing,
        # An exact mathematical term may be a good title. These entries need editorial judgement.
        "titles_repeating_identifier": identifiers,
        "inconsistent_alignment_titles": inconsistent,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path, help="Git checkout of the published reader artifact")
    parser.add_argument("output", type=Path, help="new sparse output directory, outside the artifact")
    parser.add_argument("titles", type=Path, help="JSON with exact Lean names and optional per-slot titles")
    parser.add_argument("--mount", default=".", help="path beneath artifact containing edition/")
    parser.add_argument("--source-commit", action="append", required=True)
    parser.add_argument("--audit-graph-titles", action="store_true",
                        help="Include title coverage over the whole compiled Lean index in the receipt")
    args = parser.parse_args()
    try:
        artifact, output = args.artifact.resolve(), args.output.resolve()
        if output == artifact or artifact in output.parents or output.exists():
            raise ValueError(f"{output}: use a new directory outside the artifact")
        if not all(REVISION.fullmatch(revision) for revision in args.source_commit):
            raise ValueError("Expected full source commit hashes")
        artifact_commit = subprocess.check_output(
            ["git", "-C", str(artifact), "rev-parse", "HEAD"], text=True).strip()
        names, slots = title_source(args.titles)
        files, indexes = project(artifact, args.mount, names, slots)
        # Verify the receipt's before-bytes against the Git object, even if the artifact
        # checkout happens to contain unrelated staged or untracked front-end assets.
        before = {str(path): row["before_sha256"] for path, (_, row) in files.items()} | indexes
        for path, expected in before.items():
            original = subprocess.check_output(["git", "-C", str(artifact), "show", f"{artifact_commit}:{path}"])
            if digest(original) != expected:
                raise ValueError(f"{path}: input differs from pinned artifact commit")
        output.mkdir(parents=True)
        for path, (data, _) in files.items():
            target = output / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        receipt = {"schema": "reader-display-titles/1", "artifact_commit": artifact_commit,
                   "source_commits": args.source_commit, "title_source_sha256": digest(args.titles.read_bytes()),
                   "unchanged_edition_indexes": indexes,
                   "files": {str(path): row for path, (_, row) in files.items()}}
        if args.audit_graph_titles:
            receipt["graph_title_coverage"] = graph_title_coverage(artifact, args.mount, files)
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except (KeyError, OSError, ValueError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"{exc}\n")


if __name__ == "__main__":
    main()
