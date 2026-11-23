#!/usr/bin/env python3
"""Build the licensed RH paper and compiled-source annotations for the reader."""
from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
from contextlib import closing
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
from tempfile import TemporaryDirectory
from urllib.parse import quote

import numpy as np
import pyarrow.parquet as pq
from pypdf import PdfReader
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import breadth_first_order

from build_rh_paths import HASHES, INSTANCE, write_json
from pdf_marks import lines, pdf_words

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from lean_exposition.proof_index import ProofIndex

INPUT = re.compile(r"\\input\{(sections/[^{}]+)\}")
LEAN = re.compile(r"\\lean\{([^{}\n]+)\}(?:\\textsubscript\{\\ttfamily\s+(\d+)\})?")
SUBSCRIPTS = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
HEADING = re.compile(r"^\s*\\(subsection|section)\b")
LABEL = re.compile(r"\\label\{([^{}]+)\}")
TABLE_PATH = re.compile(r"(?:…/|\.{3}/)?([\w₂₃./-]+\.lean):(\d+)(?:[–-](\d+))?")
TEX_COMMENT = re.compile(r"(?<!\\)%.*$")
NUMBERED_BOOKMARK = re.compile(r"^(\d+(?:\.\d+)*)\.\s")
PDF_PUNCTUATION = " \t.,:;!?()[]{}“”\""
EVIDENCE = {
    "M": "Computed or checked by the paper's authors",
    "S": "Lean statement read by the paper's authors",
    "P": "Lean proof read by the paper's authors",
    "C": "Compared with the published theorem by the paper's authors",
    "D": "From a reader's report",
}


def blob(source: Path, revision: str, name: str) -> bytes:
    return repository_file(source, revision, f"paper/{name}")


def repository_file(source: Path, revision: str, name: str) -> bytes:
    return subprocess.check_output(["git", "--no-replace-objects", "-C", str(source), "show", f"{revision}:{name}"])


def archive_checks(source, config, targets):
    """Join the paper authors' two successful reports by exact theorem name."""
    print_file = "verify/results/check.txt"
    replay_file = "verify/results/replay-targets.txt"
    reports = {file: repository_file(source, config["revision"], file).decode().splitlines()
               for file in (print_file, replay_file, "verify/results/replay-provenance.txt")}
    if "CHECK-EXIT 0" not in reports[print_file] or "exit code 0" not in reports["verify/results/replay-provenance.txt"]:
        raise ValueError("The RH archive reports do not record successful runs")

    def read_axioms(file, pattern):
        rows = {}
        for number, line in enumerate(reports[file], 1):
            if match := re.fullmatch(pattern, line):
                name, raw_axioms = match.groups()
                if name in rows:
                    raise ValueError(f"Duplicate axiom result for {name} in {file}")
                href = f'{config["repository"]}/blob/{config["revision"]}/{file}#L{number}'
                rows[name] = (raw_axioms.split(", ") if raw_axioms else [], href)
        return rows

    printed = read_axioms(print_file, r"'([^']+)' depends on axioms: \[([^\]]*)\]")
    replayed = read_axioms(replay_file, r"([^:]+): a theorem, checked by the kernel; it depends on \d+ constants; axioms: \[([^\]]*)\]")
    main = {name for name, source in targets.items() if source["module"] == "Main" and source["kind"] == "theorem"}
    if len(main) != 5 or printed.keys() != main or replayed.keys() != main:
        raise ValueError("The RH archive reports and paper links must identify the same five Main theorems")
    checks = {}
    for name in sorted(main):
        axioms, print_href = printed[name]
        replay_axioms, replay_href = replayed[name]
        if sorted(axioms) != sorted(replay_axioms):
            raise ValueError(f"The archive's two axiom reports differ for {name}")
        checks[name] = {"axioms": axioms, "print_href": print_href, "replay_href": replay_href}
    return checks


def graph_axioms(proof, db, names):
    """Find axioms reachable through the exact edges served by the compiled graph."""
    axiom_nodes = db.execute("SELECT id, name FROM node WHERE kind = 'axiom' ORDER BY name").fetchall()
    nodes = {node[0]: name for name in names if (node := db.execute("SELECT id FROM node WHERE name = ?", (name,)).fetchone())}
    # Searching backward from each axiom shares work across the paper's declarations.
    offsets, packed = proof.offsets["in"], proof.edges["in"]
    size = len(offsets) - 1
    indices = np.right_shift(packed.view(np.int32), 3)
    graph = csr_matrix((np.ones(len(indices), dtype=np.bool_), indices, offsets), shape=(size, size))
    rows = {name: [] for name in nodes.values()}
    for node, axiom in axiom_nodes:
        reachable = breadth_first_order(graph, node, return_predecessors=False)
        reached = np.zeros(size, dtype=np.bool_)
        reached[reachable] = True
        for ident, name in nodes.items():
            if reached[ident]:
                rows[name].append(axiom)
    return {name: {"axioms": axioms, "href": proof.manifest["dataset"]} for name, axioms in rows.items()}


def source_link(config, source):
    file = quote(source["file"], safe="/")
    url = f'{config["repository"]}/blob/{config["revision"]}/{file}#L{source["line"]}-L{source["end_line"]}'
    return {**source, "url": url}


def source_references(source: Path, revision: str):
    main = blob(source, revision, "main.tex").decode()
    names = [name + ".tex" for name in INPUT.findall(main) if not name.startswith("sections/appendix-")]
    section = 0
    for name in names:
        text = blob(source, revision, name).decode().splitlines()
        subsection = 0
        for number, raw_line in enumerate(text, 1):
            line = TEX_COMMENT.sub("", raw_line)
            heading = HEADING.match(line)
            if heading:
                if heading[1] == "section":
                    section += 1
                    subsection = 0
                else:
                    subsection += 1
            location = str(section) + (f".{subsection}" if subsection else "")
            matches = list(LEAN.finditer(line))
            label = LABEL.search(line) if r"\begin{statement}" in line else None
            for pos, match in enumerate(matches, 1):
                anchor = label[1] if label else f"{Path(name).stem}:{number}:{pos}"
                end_line = number
                if label:
                    end_line = next((n for n, body in enumerate(text[number:], number + 1)
                                     if r"\end{statement}" in body), number)
                yield {
                    "id": f"{anchor}:{pos}" if label and len(matches) > 1 else anchor,
                    "anchor": anchor,
                    "name": match[1].strip() + (match[2] or "").translate(SUBSCRIPTS),
                    "section": location,
                    "source": {"file": "paper/" + name, "line": number, "end_line": end_line},
                    "role": "statement" if label else "reference",
                }


def basis_rows(text: str):
    by_name = defaultdict(list)
    by_file = defaultdict(list)
    for line in text.splitlines():
        if not re.match(r"^\| \d", line):
            continue
        _, section, statement, tag, where, _ = [part.strip() for part in line.split("|", 5)]
        row = {"section": section, "description": statement, "kind": tag, "authority": EVIDENCE.get(tag), "source_text": where}
        for name in set(re.findall(r"`([^`]+)`", statement + " " + where)):
            if re.fullmatch(r"[\w.₀-₉']+", name):
                by_name[name].append(row)
        for filename, number, end in TABLE_PATH.findall(where):
            by_file[Path(filename).name].append((int(number), int(end or number), row))
    return by_name, by_file


def index_candidates(path: Path, wanted: set[str]) -> dict[str, list[dict]]:
    with path.open("rb") as stream:
        if hashlib.file_digest(stream, "sha256").hexdigest() != HASHES["decls.parquet"]:
            raise ValueError("The declaration table does not match the pinned compilation")
    by_name = defaultdict(list)
    for batch in pq.ParquetFile(path).iter_batches(columns=["decl", "file", "module", "start_line", "end_line", "kind"]):
        for row in batch.to_pylist():
            full = row["decl"]
            leaf = full.rsplit(".", 1)[-1]
            for name in {full, leaf} & wanted:
                by_name[name].append(row)
    return by_name


def resolve(rows: list[dict], name: str, basis: list[dict]):
    exact = [row for row in rows if row["decl"] == name]
    if len(exact) == 1:
        return exact[0], "exact_name"
    if len(rows) == 1:
        return rows[0], "unique_short_name"
    spans = {(file, int(first), int(last or first)) for entry in basis
             for file, first, last in TABLE_PATH.findall(entry["source_text"])}
    supported = [
        row for row in rows
        if row["file"] and row["start_line"] is not None and any(
            row["file"].endswith(file) and row["start_line"] <= last and (row["end_line"] or row["start_line"]) >= first
            for file, first, last in spans
        )
    ]
    return (supported[0], "source_table") if len(supported) == 1 else (None, "ambiguous" if rows else "no_declaration_match")


def subsection_titles(source: Path, revision: str) -> dict[str, str]:
    titles = {}
    section = 0
    for name in INPUT.findall(blob(source, revision, "main.tex").decode()):
        if name.startswith("sections/appendix-"):
            continue
        for raw in blob(source, revision, name + ".tex").decode().splitlines():
            line = TEX_COMMENT.sub("", raw).strip()
            if line.startswith(r"\section{"):
                section += 1
                subsection = 0
            elif line.startswith(r"\subsection{"):
                subsection += 1
                title = line.split(r"\label", 1)[0].removeprefix(r"\subsection{").rstrip().removesuffix("}")
                title = title.replace(r"\tfrac12", "½").replace("$", "").replace("N_u", "Nᵤ")
                number = f"{section}.{subsection}"
                titles[number] = f"{number} {title}"
    return titles


def bookmarks(path: Path, sizes: list, titles: dict[str, str]):
    pdf = PdfReader(path)
    locations = []
    def collect(items):
        for item in items:
            if isinstance(item, list):
                collect(item)
            else:
                page = pdf.get_destination_page_number(item) + 1
                if page <= 0:
                    continue
                match = NUMBERED_BOOKMARK.match(item.title)
                y = sizes[page - 1][1] - float(item.top or sizes[page - 1][1])
                locations.append({"section": match[1] if match else None, "title": item.title,
                                  "page": page, "y": round(y, 3)})
    collect(pdf.outline)
    for key, item in pdf.named_destinations.items():
        match = re.fullmatch(r"subsection\.(\d+\.\d+)", key)
        if not match:
            continue
        page = pdf.get_destination_page_number(item) + 1
        if page <= 0 or item.top is None:
            raise ValueError(f"Missing PDF destination for subsection {match[1]}")
        locations.append({"section": match[1], "title": titles[match[1]], "kind": "subsection",
                          "page": page, "y": round(sizes[page - 1][1] - float(item.top), 3)})
    return sorted(locations, key=lambda row: (row["page"], row["y"]))


def pdf_locations(refs: list[dict], outline: list[dict], words: list[dict]):
    numbered = [row for row in outline if row["section"]]
    starts = [(row["page"], row["y"]) for row in numbered]
    if starts != sorted(starts):
        raise ValueError("PDF's numbered outline is not in page order")
    appendix = next(row for row in outline if row["title"].startswith("Appendix A."))
    main_end = appendix["page"], appendix["y"]
    seen = defaultdict(list)
    for index, word in enumerate(words):
        position = word["page"], word["box"][1] + 2
        if position >= main_end:
            break
        at = bisect_right(starts, position) - 1
        if at >= 0:
            name = word["text"].strip(PDF_PUNCTUATION)
            seen[numbered[at]["section"], name].append(index)
    groups = defaultdict(list)
    for ref in refs:
        groups[ref["section"], ref["name"]].append(ref)
    placed = {}
    for identity, group in groups.items():
        found = seen.get(identity, [])
        if len(found) == len(group):
            for ref, index in zip(group, found, strict=True):
                placed[ref["id"]] = (index, index + 1)
    return placed


def token_text(words: list[dict]):
    out = bytearray()
    spans = []
    page = 1
    for word in words:
        if word["page"] != page:
            out.extend(b"\f\n")
            page = word["page"]
        if out and not out.endswith(b"\n"):
            out.extend(b" ")
        start = len(out)
        out.extend(word["text"].encode("utf-8"))
        spans.append((start, len(out)))
    out.extend(b"\n")
    return bytes(out), spans


def pdf_token_hits(words: list[dict], page: int, tokens: list[str]) -> list[int]:
    return [i for i, word in enumerate(words) if word["page"] == page
            and [w["text"] for w in words[i:i + len(tokens)] if w["page"] == page] == tokens]


def passage_location(words: list[dict], config: dict) -> tuple[int, int]:
    starts = pdf_token_hits(words, config["pdf_page"], config["pdf_from"])
    ends = pdf_token_hits(words, config.get("pdf_end_page", config["pdf_page"]), config["pdf_before"])
    if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
        raise ValueError(f"PDF anchors do not delimit one span for {config['title']}: {starts=}, {ends=}")
    return starts[0], ends[0]


def reviewed_pdf_location(words, entry, name):
    tokens = entry["tokens"]
    start, end = entry["span"]
    hits = pdf_token_hits(words, entry["page"], tokens)
    printed = "".join(tokens[start:end]).strip(PDF_PUNCTUATION).translate(SUBSCRIPTS)
    if len(hits) != 1 or not 0 <= start < end <= len(tokens) or printed != name:
        raise ValueError(f"Reviewed PDF context no longer lands on {name} on page {entry['page']}")
    return hits[0] + start, hits[0] + end


def make_topic_palette(config, annotations, passages):
    topics = config["topics"]
    families = config["families"]
    rows = [{"section": item["section"], "topic": item["topic"], "lean": [item["lean"]["name"]]}
            for item in annotations.values()]
    rows.extend({"section": item["section"], "topic": item["topic"], "lean": [target["name"] for target in item["lean"]]}
                for item in passages.values())
    data = {"families": families, "topics": topics, "phrases": rows}
    script = Path(__file__).with_name("build_rh_topic_colours.ts")
    result = json.loads(subprocess.check_output(["node", script], input=json.dumps(data).encode()))
    colours = {row["id"]: row for row in result["topics"]}
    return {
        "schema": "rh-paper-topics/1",
        "families": [{**row, "part": 0} for row in result["families"]],
        "topics": [{**topic, "part": 0, "description": topic["name"], "tone": tone,
                    "light": colours[topic["id"]]["light"], "dark": colours[topic["id"]]["dark"]}
                   for tone, topic in enumerate(topics, 1)],
    }


def note_sources(args, config, targets):
    data = {}
    notes = json.loads((INSTANCE / "lean-notes.json").read_text(encoding="utf-8"))
    for name, sources in notes["excerpts"].items():
        if name not in targets:
            raise ValueError(f"Note for a declaration absent from the paper's anchors: {name}")
        data[name] = []
        for entry in sources:
            file = entry["file"]
            start, end = entry["lines"]
            path = f"notes/slices/{file}"
            text = repository_file(args.source, config["revision"], path).decode().splitlines()
            if not 1 <= start <= end <= len(text):
                raise ValueError(f"Invalid upstream note range: {path}:{start}-{end}")
            url = f'{config["repository"]}/blob/{config["revision"]}/{path}#L{start}-L{end}'
            first, last = entry["lean_lines"]
            declaration_first, declaration_last = targets[name]["lines"]
            if not declaration_first <= first <= last <= declaration_last:
                raise ValueError(f"Note {path}:{start}-{end} targets lines outside {name}")
            reading_note = entry.get("reading_note")
            if reading_note is not None and (not isinstance(reading_note, str) or not reading_note.strip()):
                raise ValueError(f"Invalid reading note for {name} at {path}:{start}-{end}")
            data[name].append({"title": entry["title"], "markdown": "\n".join(text[start - 1:end]),
                               **({"reading_note": reading_note} if reading_note else {}),
                               "url": url, "authors": config["authors"], "license": config["license"],
                               "lean_lines": [first, last],
                               "evidence": entry.get("evidence", "Contributor reading of the source")})
    for name, sources in notes["references"].items():
        if name not in targets:
            raise ValueError(f"Linked notes for a declaration absent from the paper: {name}")
        data.setdefault(name, []).extend(sources)
    return data


def reader_notes(sources):
    """Project reading notes while preserving the original excerpts in the source records."""
    notes = {}
    for name, entries in sources.items():
        excerpts = [entry for entry in entries if "markdown" in entry]
        if not excerpts:
            continue
        paragraphs = []
        for entry in excerpts:
            if entry.get("reading_note"):
                paragraphs.append(entry["reading_note"])
                continue
            author_credit = " and ".join(entry["authors"])
            text = re.sub(r"\*+(\[[\w-]+\])\*+", r"\1", entry["markdown"]).replace("**", "")
            paragraphs.append(f'{entry["title"]}\n\n{text}\n\n{author_credit} · {entry["license"]}')
        notes[name] = {"text": "\n\n".join(paragraphs)}
    return notes


def lean_target(row, proof, db, statement_ends):
    name = row["decl"]
    first, last = row["start_line"], row["end_line"] or row["start_line"]
    split = statement_ends.get(name)
    statement_end = split if split is not None else last
    if not first <= statement_end <= last:
        raise ValueError(f"The Lean statement is outside the compiled declaration: {name}")
    base = f'{proof["upstream"]}/blob/{proof["revision"]}/{quote(row["file"], safe="/")}'
    value = {"name": name, "file": row["file"], "module": row["module"], "kind": row["kind"], "lines": [first, last],
             "url": f"{base}#L{first}-L{last}", "revision": proof["revision"],
             "in_proof": db.execute("SELECT EXISTS(SELECT 1 FROM node WHERE name=?)", (name,)).fetchone()[0] == 1}
    if split is not None:
        # The term following := can begin on the last line of the statement.
        value["statement_lines"] = [first, split]
        value["proof_lines"] = [split, last]
    elif row["kind"] == "def":
        value["statement_lines"] = [first, last]
    return value


def checked_source(source_checkout, config, entry, fallback):
    source = entry.get("source") or fallback
    cue = entry.get("tex_anchor")
    if cue:
        contents = repository_file(source_checkout, config["revision"], source["file"]).decode().splitlines()
        first, last = source["line"], source["end_line"]
        if not 1 <= first <= last <= len(contents) or cue not in "\n".join(contents[first - 1:last]):
            raise ValueError(f"TeX anchor no longer lands for {entry['title']}")
    return source_link(config, source)


def checked_edges(index, entry):
    witnesses = []
    for consumer, prerequisite, kind in entry.get("compiled_edges", []):
        if kind not in index.dependency_kinds(consumer, prerequisite):
            raise ValueError(f"Missing compiled {kind} edge {consumer} → {prerequisite} for {entry['title']}")
        witnesses.append({"from": consumer, "to": prerequisite, "kind": kind})
    return witnesses


def reading_line_index(passages, annotations, marks, bindings, notes):
    """Find the best paper address and available notes from a Lean module and line."""
    modules = defaultdict(list)
    priority = {"statement": 0, "definition": 1, "derivation": 2, "explanation": 3, "mention": 4}
    for name, binding in bindings.items():
        source = binding["source"]
        links = []
        for key in binding["passages"]:
            passage = passages[key]
            target = next(row for row in passage["lean"] if row["name"] == name)
            focus = target.get("focus_lines")
            span = focus or target.get("statement_lines") or target["lines"]
            links.append({"mark": key, "lines": span, "role": passage["role"],
                          "topic": passage["topic"], "precision": "reviewed_span" if focus else "declaration"})
        for key in binding["references"]:
            item = annotations[key]
            mark = item.get("covered_by", key)
            if mark not in marks or any(link["mark"] == mark for link in links):
                continue
            links.append({"mark": mark, "reference": key, "lines": source["lines"],
                          "role": "mention", "topic": item["topic"], "precision": "declaration"})
        links.sort(key=lambda row: (priority.get(row["role"], 4), marks[row["mark"]]["boxes"][0][0],
                                    int(marks[row["mark"]]["at"][1:].partition("-")[0]), row["mark"]))
        modules[source["module"]].append({
            "name": name, "lines": source["lines"], "canonical": links[0]["mark"] if links else None,
            "links": links,
            "notes": [{"index": i, "lines": note["lean_lines"]}
                      for i, note in enumerate(notes.get(name, [])) if "lean_lines" in note],
        })
    return {module: sorted(rows, key=lambda row: (*row["lines"], row["name"]))
            for module, rows in sorted(modules.items())}


def archive_runs(source, config):
    """Record selected proof checks from the authors' pinned archive logs."""
    files = (
        "build-summary.txt", "check.txt", "replay-summary.txt", "replay-provenance.txt", "replay-targets.txt",
        "fresh-main/stock.txt", "fresh-main/stock-fresh-Main.log.txt", "independent-fresh.txt",
        "sample-summary.txt", "independent-sample-summary.txt", "sample-alone.txt", "sample-exact.txt",
        "sample-prefixes.txt", "file-times.txt",
    )
    revision, repository = config["revision"], config["repository"]
    paths = {name: f"verify/results/{name}" for name in files}
    raw = {name: repository_file(source, revision, path) for name, path in paths.items()}
    logs = {name: data.decode() for name, data in raw.items()}
    times = dict(line.split() for line in logs["file-times.txt"].splitlines())
    runs = []

    def match(file, pattern):
        found = re.search(pattern, logs[file], re.MULTILINE)
        if not found:
            raise ValueError(f"RH archive run summary does not match {paths[file]}: {pattern}")
        return found

    def add(id_, tool, command, date_file, files, outcome, shows, limit, status="passed"):
        date = datetime.fromtimestamp(int(times[date_file]), timezone.utc).date().isoformat()
        runs.append({
            "record_type": "upstream_run_observation", "id": f"rh.archive.{id_}", "status": status,
            "tool": tool, "command": command, "date": date, "repository": repository, "commit": revision,
            "where": "The paper authors’ archive run", "outcome": outcome, "shows": shows,
            "does_not_show": limit, "logs": [
                {"path": paths[name], "url": f"{repository}/blob/{revision}/{paths[name]}",
                 "sha256": hashlib.sha256(raw[name]).hexdigest()}
                for name in (*files, "file-times.txt")
            ],
        })

    archive_limit = "The community import shown in this reader is a separate build."
    match("build-summary.txt", r"^LAKE-EXIT 0$")
    add("build", "Lean archive build", ["lake", "build", "Main"], "build-summary.txt", ("build-summary.txt",),
        "Lake exited with code 0", "The authors compiled the archive's Main with Mathlib built from source.", archive_limit)

    match("check.txt", r"^CHECK-EXIT 0\nleanchecker Statements: exit 0\nlean4lean Statements: exit 0$")
    add("statements", "Statement and axiom checks", ["bash", "check.sh"], "check.txt", ("check.txt",),
        "The statement check, leanchecker and lean4lean all exited with code 0",
        "The authors re-elaborated the three main statements, printed axioms for five theorems, and ran both checkers on Statements.",
        "This check targets the archive's Statements module and selected types.")

    match("replay-provenance.txt", r"^root Main$")
    match("replay-provenance.txt", r"^exit code 0$")
    match("replay-summary.txt", r"^failed 0$")
    replayed = int(match("replay-summary.txt", r"^replayed (\d+)$")[1])
    skipped = int(match("replay-summary.txt", r"^unsafe-or-partial-not-replayed (\d+)$")[1])
    add("replay", "Authors’ kernel replay of Main", ["bash", "replay.sh"], "replay-summary.txt",
        ("replay-summary.txt", "replay-provenance.txt", "replay-targets.txt"),
        f"The replay reported {replayed:,} constants replayed and zero failures",
        "The authors replayed the eligible constants in the import closure of the archive's Main.",
        f"The replay skipped {skipped:,} unsafe or partial constants. {archive_limit}")

    match("fresh-main/stock.txt", r"^leanchecker --fresh Main: exit 0;")
    if raw["fresh-main/stock-fresh-Main.log.txt"]:
        raise ValueError("Lean's fresh Main replay wrote to its checker log")
    add("fresh-main", "Lean’s fresh replay of Main", ["leanchecker", "--fresh", "Main"],
        "fresh-main/stock-fresh-Main.log.txt", ("fresh-main/stock.txt", "fresh-main/stock-fresh-Main.log.txt"),
        "Lean’s own checker exited with code 0", "Lean ran in fresh mode over the archive's Main import closure.", archive_limit)

    for module in ("RiemannZeta", "DirichletContinuation"):
        match("independent-fresh.txt", rf"^lean4lean --fresh Mathlib\.NumberTheory\.LSeries\.{module}: exit 0;")
    add("fresh-mathlib", "lean4lean fresh checks on Mathlib", ["bash", "independent.sh", "fresh"],
        "independent-fresh.txt", ("independent-fresh.txt",), "Both Mathlib module runs exited with code 0",
        "lean4lean checked the import closures of Mathlib's RiemannZeta and DirichletContinuation modules.",
        "The two runs target Mathlib modules. The archive's Main has a larger import closure.")

    prefix = "Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients"
    for file in ("sample-summary.txt", "independent-sample-summary.txt"):
        match(file, r"^modules checked 501[^\n]*\naccepted 500\nnot accepted 1\nMain accepted$")
    for tool in ("leanchecker", "lean4lean"):
        match("sample-alone.txt", rf"^DONE-STEP probe {tool} {re.escape(prefix)} exit 137 .* oom_kill \d+$")
    add("sample", "Sample runs by both checkers", [], "sample-alone.txt",
        ("sample-summary.txt", "independent-sample-summary.txt", "sample-alone.txt"),
        "Each checker accepted 500 of 501 sampled names and ran out of memory on the remaining name",
        "Both checkers recorded acceptance on 500 names, including Main.",
        "The memory limit interrupted the check of the PlaneCoefficients module prefix in both runs.", "unavailable")

    descendants = set(re.findall(rf"^{re.escape(prefix)} (\S+)$", logs["sample-prefixes.txt"], re.MULTILINE))
    if len(descendants) != 29 or not all(name.startswith(prefix + ".") for name in descendants):
        raise ValueError("RH archive sample prefixes do not record the expected descendants")
    modules = descendants | {prefix}
    for tool in ("leanchecker", "lean4lean"):
        results = re.findall(rf"^{tool} {re.escape(prefix)} (\S+) (\d+) \d+", logs["sample-exact.txt"], re.MULTILINE)
        if len(results) != len(modules) or dict(results) != dict.fromkeys(modules, "0"):
            raise ValueError(f"RH archive exact sample is incomplete for {tool}")
    add("sample-exact", "One-module follow-up by both checkers", ["bash", "sample-exact.sh"],
        "sample-exact.txt", ("sample-exact.txt", "sample-prefixes.txt"), "Both checkers exited with code 0 on all 30 modules",
        "Individual checks covered PlaneCoefficients and 29 modules beneath its name.",
        "Each invocation checked one module. The earlier prefix-wide processes still ended at the memory limit.")
    return {"paper_revision": revision, "runs": runs}


def build(args) -> None:
    config = json.loads((INSTANCE / "paper.json").read_text(encoding="utf-8"))
    ties = json.loads((INSTANCE / "passage-ties.json").read_text(encoding="utf-8"))
    topic_by_section = {section: item["id"] for item in ties["topics"] for section in item["sections"]}
    def topic(section):
        return topic_by_section.get(section) or topic_by_section[section.split(".", 1)[0]]
    proof_index = ProofIndex(args.proof_index)
    proof = proof_index.manifest
    expected = json.loads((INSTANCE / "reader.json").read_text(encoding="utf-8"))
    for key in ("revision", "dataset", "upstream"):
        if proof[key] != expected[key]:
            raise ValueError(f"The paper expects a different Lean proof {key}")
    root = (args.proof_index / "nodes.sqlite").resolve().as_uri() + "?mode=ro&immutable=1"
    revision = config["revision"]
    refs = list(source_references(args.source, revision))
    printed = {ref["id"]: ref["name"] for ref in refs}
    if len(printed) != len(refs):
        raise ValueError("The paper produced duplicate annotation identifiers")
    literals = ties["text_literals"]
    reviewed = ties["reviewed_references"]
    for key, name in literals.items():
        if printed.get(key) != name:
            raise ValueError(f"The printed source for the literal {key} changed")
    for key, name in reviewed.items():
        if key not in printed or key in literals or (name != printed[key] and not name.endswith("." + printed[key])):
            raise ValueError(f"The printed source for the reviewed reference {key} changed")
    authority, file_evidence = basis_rows(blob(args.source, revision, "basis.md").decode())
    curated = {**ties["statements"], **ties["passages"]}
    required = {name for entry in curated.values() for name in entry["names"]}
    candidates = index_candidates(args.declarations, set(printed.values()) | required | set(reviewed.values()))
    output = args.out
    output.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output) as temporary:
        stage = Path(temporary)
        for filename, expected_hash in config["source_files"].items():
            content = blob(args.source, revision, filename)
            if hashlib.sha256(content).hexdigest() != expected_hash:
                raise ValueError(f"The pinned PDF changed: {filename}")
            (stage / ("paper.pdf" if filename == "main.pdf" else "outline.pdf")).write_bytes(content)
        sizes, words = pdf_words(stage / "paper.pdf")
        outline = bookmarks(stage / "paper.pdf", sizes, subsection_titles(args.source, revision))
        placements = pdf_locations(refs, outline, words)
        reviewed_pdf = ties.get("reviewed_pdf_references", {})
        for key, entry in reviewed_pdf.items():
            placements[key] = reviewed_pdf_location(words, entry, printed[key])
        text, spans = token_text(words)
        (stage / "paper.txt").write_bytes(text)
        annotations, marks, passages, review = {}, {}, {}, []
        counts = Counter()
        with closing(sqlite3.connect(root, uri=True)) as db:
            for ref in refs:
                ref_id = ref["id"]
                name = ref["name"]
                basis = authority.get(name, [])
                if ref_id in literals:
                    counts["text_literal"] += 1
                    review.append({**ref, "issue": "text_literal"})
                    continue
                if ref_id in reviewed:
                    matches = [item for item in candidates[reviewed[ref_id]] if item["decl"] == reviewed[ref_id]]
                    if len(matches) != 1:
                        raise ValueError(f"The reviewed Lean declaration for {ref_id} is absent or ambiguous")
                    row, resolution = matches[0], "reviewed_name"
                else:
                    row, resolution = resolve(candidates[name], name, basis)
                counts[resolution] += 1
                if row is None or not row["file"] or row["start_line"] is None:
                    review.append({**ref, "issue": resolution, "choices": [x["decl"] for x in candidates[name]]})
                    continue
                place_evidence = [
                    entry for first, last, entry in file_evidence[Path(row["file"]).name]
                    if first <= row["start_line"] <= last
                ]
                for evidence in place_evidence:
                    if evidence not in basis:
                        basis = [*basis, evidence]
                anchor = placements.get(ref_id)
                data = {
                    **ref, "resolution": resolution, "fidelity": "unassessed", "author_evidence": basis,
                    "source": source_link(config, ref["source"]),
                    "topic": topic(ref["section"]),
                    "lean": lean_target(row, proof, db, ties["statement_ends"]),
                }
                if anchor:
                    start, end = anchor
                    at = f"b{spans[start][0]}-{spans[end - 1][1]}"
                    boxes = lines(words[start:end])
                    data["pdf"] = {"page": words[start]["page"], "at": at, "boxes": boxes,
                                   "placement": "reviewed_context" if ref_id in reviewed_pdf else "unique_section_match"}
                    marks[ref_id] = {"at": at, "tone": None, "record": ref_id, "boxes": boxes}
                else:
                    review.append({**ref, "issue": "pdf_location_not_unique"})
                annotations[ref_id] = data
            for anchor, entry in curated.items():
                matching = [item for item in annotations.values() if item["anchor"] == anchor]
                if anchor in ties["statements"] and [item["lean"]["name"] for item in matching] != entry["names"]:
                    raise ValueError(f"Paper statement {anchor} does not resolve to its reviewed Lean declarations")
                targets = []
                focus = entry.get("focus", {})
                if not focus.keys() <= set(entry["names"]):
                    raise ValueError(f"Unknown source focus in {anchor}")
                for name in entry["names"]:
                    row = next((row for row in candidates[name] if row["decl"] == name), None)
                    if row is None:
                        raise ValueError(f"Missing exact Lean declaration {name}")
                    target = lean_target(row, proof, db, ties["statement_ends"])
                    if name in focus:
                        first, last = focus[name]["lines"]
                        lo, hi = target["lines"]
                        if not lo <= first <= last <= hi:
                            raise ValueError(f"Focused source span for {anchor} is outside {name}")
                        target.update(focus_lines=[first, last], focus_note=focus[name]["note"])
                    targets.append(target)
                source = checked_source(args.source, config, entry, matching[0]["source"] if matching else None)
                section = entry.get("section") or matching[0]["section"]
                start, end = passage_location(words, entry)
                at = f"b{spans[start][0]}-{spans[end - 1][1]}"
                body = [word for word in words[start:end] if word["box"][1] >= 77]
                boxes = lines(body)
                passages[anchor] = {
                    "id": anchor, "title": entry["title"], "section": section,
                    "role": entry.get("role", "statement"), "topic": topic(section), "source": source,
                    "lean": targets, "reference_ids": [item["id"] for item in matching], "fidelity": "unassessed",
                    "pdf": {"page": words[start]["page"], "at": at, "boxes": boxes, "placement": "reviewed_span"},
                    "compiled_edges": checked_edges(proof_index, entry),
                    **({"route": entry["route"]} if "route" in entry else {}),
                }
                # One clickable span for the whole passage, with its inline references
                # still accessible from that passage's references.
                for mark_id, mark in list(marks.items()):
                    first, last = map(int, mark["at"][1:].split("-"))
                    if spans[start][0] <= first and last <= spans[end - 1][1]:
                        if mark_id != anchor and mark_id in passages:
                            raise ValueError(f"Full passage {mark_id} is contained in {anchor}")
                        annotations[mark_id]["covered_by"] = anchor
                        if mark_id not in passages[anchor]["reference_ids"]:
                            passages[anchor]["reference_ids"].append(mark_id)
                        del marks[mark_id]
                marks[anchor] = {"at": at, "record": anchor, "boxes": boxes}
        palette = make_topic_palette(ties, annotations, passages)
        tones = {item["id"]: item["tone"] for item in palette["topics"]}
        for mark_id, mark in marks.items():
            item = passages.get(mark_id) or annotations[mark_id]
            mark["tone"] = tones[item["topic"]]
        for item in outline:
            if item["section"]:
                item["topic"] = topic(item["section"])
        bindings = defaultdict(lambda: {"references": [], "marks": [], "passages": [], "topics": []})
        targets = {}
        for key, item in passages.items():
            for target in item["lean"]:
                targets[target["name"]] = {key: value for key, value in target.items()
                                           if key not in {"focus_lines", "focus_note"}}
                binding = bindings[target["name"]]
                binding["passages"].append(key)
                if item["topic"] not in binding["topics"]:
                    binding["topics"].append(item["topic"])
        for key, item in annotations.items():
            target = item["lean"]
            targets[target["name"]] = target
            binding = bindings[target["name"]]
            binding["references"].append(key)
            mark = item.get("covered_by", key)
            if mark in marks and mark not in binding["marks"]:
                binding["marks"].append(mark)
            if item["topic"] not in binding["topics"]:
                binding["topics"].append(item["topic"])
        notes = note_sources(args, config, targets)
        for name, target in targets.items():
            bindings[name]["source"] = target
        with closing(sqlite3.connect(root, uri=True)) as db:
            graph_checks = graph_axioms(proof_index, db, targets)
        if graph_checks.keys() != {name for name, target in targets.items() if target["in_proof"]}:
            raise ValueError("The axiom graph and paper links disagree on declaration membership")
        modules = reading_line_index(passages, annotations, marks, bindings, notes)
        write_json(stage / "topics.json", palette)
        write_json(stage / "passages.json", {"schema": "rh-paper-passages/1", "paper_revision": revision,
                                              "lean_revision": proof["revision"], "passages": passages})
        write_json(stage / "lean-notes.json", {
            "schema": 1, "paper_revision": revision, "lean_revision": proof["revision"],
            "notes": reader_notes(notes), "sources": notes, "bindings": bindings,
        })
        write_json(stage / "lean-lines.json", {
            "schema": "rh-lean-lines/1", "paper_revision": revision, "lean_revision": proof["revision"],
            "modules": modules,
        })
        write_json(stage / "lean-checks.json", {
            "schema": "rh-lean-checks/1", "paper_revision": revision, "lean_revision": proof["revision"],
            "archive": archive_checks(args.source, config, targets), "graph": graph_checks,
        })
        write_json(stage / "archive-runs.json", archive_runs(args.source, config))
        write_json(stage / "annotations.json", {"schema": "rh-paper-annotations/1", "paper_revision": revision,
                                                "lean_revision": proof["revision"], "annotations": annotations})
        write_json(stage / "pdf-marks.json", {"schema": "pdf-marks/1", "pages": sizes, "marks": marks,
                                              "unplaced": sorted(key for key, item in annotations.items() if "pdf" not in item)})
        write_json(stage / "sections.json", {"sections": outline})
        files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(stage.iterdir())}
        write_json(stage / "manifest.json", {
            "schema": "rh-paper-edition/1",
            "paper": {key: config[key] for key in ("version", "repository", "revision", "title", "authors", "license")},
            "lean": {key: proof[key] for key in ("revision", "upstream", "dataset", "verification")},
            "pages": len(sizes), "counts": {"source_references": len(refs), "resolved": len(annotations), "pdf_marks": len(marks),
                                            "passages": len(passages), "topics": len(palette["topics"]),
                                            "bound_declarations": len(bindings), "notes": sum(map(len, notes.values())),
                                            "compiled_witnesses": sum(len(item["compiled_edges"]) for item in passages.values())},
            "files": files,
        })
        for path in sorted(stage.iterdir()):
            if path.name != "manifest.json":
                path.replace(output / path.name)
        (stage / "manifest.json").replace(output / "manifest.json")
    args.review.parent.mkdir(parents=True, exist_ok=True)
    write_json(args.review, {"paper_revision": revision, "lean_revision": proof["revision"], "resolution_counts": counts, "review": review})
    print(f"{len(sizes)} pages; {len(refs)} references; {len(annotations)} resolved; {len(marks)} placed on the PDF")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="checkout with the pinned paper revision")
    parser.add_argument("declarations", type=Path, help="v0.2.1 decls.parquet")
    parser.add_argument("proof_index", type=Path, help="the indexed RH closure for the same Lean revision")
    parser.add_argument("--out", type=Path, default=INSTANCE / "edition" / "paper")
    parser.add_argument("--review", type=Path, default=INSTANCE.parents[1] / "build" / "rh-paper-review.json")
    build(parser.parse_args())


if __name__ == "__main__":
    main()
