"""Resolve authored record alignment against a Lean index and the papers' bytes.

The alignment is a sidecar of pointers: a pass means each pointer lands where it
was written, and says nothing about whether two statements mean the same thing.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from .bundle import STAGES
from .consumer import _paper_sections
from .contracts import ContractError, read_json
from .lean_index import canonical, load_index

ALIGNMENT_SCHEMA_VERSION = "1.0"
RELATIONS = {"states", "contains", "part", "proof", "defines"}
ROLES = {"statement", "definition", "explanation", "derivation", "example", "mention"}
MAX_SLICE_CHARACTERS = 1800
MAX_NOTE_WORDS = 25
_PASSAGE = re.compile(rb"<!-- passage:([^\s>]+) -->")
_EXPLICIT_ID = re.compile(rb"<a\s+[^>]*\bid=[\"']([^\"']+)[\"']")


def _pandoc_identifier(title):
    """Pandoc's auto identifier, as `site/src/reader/anchors.ts` computes it."""
    plain = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", title)
    plain = re.sub(r"[*`$]|(?<![0-9A-Za-z])_|_(?![0-9A-Za-z])", "", plain).lower()
    kept = "".join(c for c in plain if c.isspace() or c.isalnum() or c in "_-.")
    joined = "-".join(kept.split())
    start = next((i for i, c in enumerate(joined) if c.isalpha()), len(joined))
    return joined[start:] or "section"


class _Paper:
    """One paper's bytes with its outline and passage spans."""

    def __init__(self, content):
        self.content = content
        self.text = content.decode("utf-8")
        starts = [0] + [m.end() for m in re.finditer(rb"\r\n?|\n", content)]
        self.sections = _paper_sections(content, "", starts)
        self.passages = []
        for match in _PASSAGE.finditer(content):
            anchor = match.group(1)
            closing = content.find(b"<!-- /passage:" + anchor + b" -->", match.end())
            if closing >= 0:
                self.passages.append((match.end(), closing, anchor.decode("utf-8")))
        used = {m.group(1).decode("utf-8") for m in _EXPLICIT_ID.finditer(content)}
        for section in self.sections:
            base = identifier = _pandoc_identifier(section["title"])
            number = 0
            while identifier in used:
                number += 1
                identifier = f"{base}-{number}"
            used.add(identifier)
            section["heading_id"] = identifier

    def locate(self, row):
        """Return the slice, its byte span and enclosing places, or raise ValueError."""
        text, begin = self.text, 0
        after = row.get("after")
        if after is not None:
            if type(after) is not str or not after or text.count(after) == 0:
                raise ValueError(f"after not found: {str(after)[:70]!r}")
            if text.count(after) > 1:
                raise ValueError(f"after is ambiguous: {after[:70]!r}")
            begin = text.index(after) + len(after)
        first, last = row.get("from"), row.get("to")
        if type(first) is not str or not first or type(last) is not str or not last:
            raise ValueError("from and to must be nonempty text")
        start = text.find(first, begin)
        if start < 0:
            raise ValueError(f"from not found: {first[:70]!r}")
        if text.find(first, start + 1) >= 0:
            raise ValueError(f"from is ambiguous, add after: {first[:70]!r}")
        stop = text.find(last, start)
        if stop < 0:
            raise ValueError(f"to not found after from: {last[:70]!r}")
        stop += len(last)
        markdown = text[start:stop]
        if len(markdown) > MAX_SLICE_CHARACTERS:
            raise ValueError(f"slice is {len(markdown)} characters")
        bare = markdown.replace("\\$", "")
        if bare.count("$$") % 2 or bare.replace("$$", "").count("$") % 2:
            raise ValueError("slice has unbalanced mathematics")
        start_byte = len(text[:start].encode("utf-8"))
        end_byte = start_byte + len(markdown.encode("utf-8"))
        anchor = next((name for left, right, name in self.passages
                       if left <= start_byte and end_byte <= right), None)
        enclosing = [s for s in self.sections if s["span"]["start_byte"] <= start_byte
                     and end_byte <= s["span"]["end_byte"]]
        section = enclosing[-1] if enclosing else None
        return {"markdown": markdown, "start_byte": start_byte, "end_byte": end_byte, "anchor": anchor,
                "section": section["title"] if section else "",
                "heading_id": section["heading_id"] if section else None}


def _declarations(index):
    return {module["path"]: (module["name"], module["declarations"]) for module in index["modules"]}


def _find(modules, file, name):
    """Resolve a name as written in one file to its one declaration."""
    if file not in modules:
        raise ValueError(f"no Lean file {file}")
    module, rows = modules[file]
    found = ([row for row in rows if row["written"] == name] or [row for row in rows if row["name"] == name]
             or [row for row in rows if row["name"].endswith("." + name)])
    if not found:
        raise ValueError(f"no declaration {name} in {file}")
    if len(found) > 1:
        raise ValueError(f"declaration {name} is ambiguous in {file}")
    return module, found[0]


def _check_keys(row, required, optional, where, errors):
    if not isinstance(row, dict):
        errors.append(f"{where}: must be an object")
        return False
    missing, unknown = required - row.keys(), row.keys() - required - optional
    if missing or unknown:
        errors.append(f"{where}: missing {sorted(missing)}, unknown {sorted(unknown)}")
    return not missing


def resolve_alignment(directory, index, papers, record_ids, *, strict=True):
    """Resolve every authored file; `records` covers only the records written so far.

    A partial directory is valid. With `strict=False` a failing row is left out and
    its error returned, so a reading edition survives a file still being written.
    """
    directory = Path(directory)
    if not directory.is_dir():
        raise ContractError(f"alignment directory is absent: {directory}")
    if set(papers) != set(STAGES):
        raise ContractError("alignment requires the long, short and expository papers")
    prepared = {stage: _Paper(content) for stage, content in papers.items()}
    modules, errors = _declarations(index), []
    records, dictionary = {}, []
    for path in sorted(directory.glob("*.json")):
        try:
            data = json.loads(path.read_bytes())
        except ValueError as exc:
            errors.append(f"{path.name}: not valid JSON: {exc}")
            continue
        if not isinstance(data, dict) or not data.keys() & {"records", "terms"}:
            continue  # Other authored companions may share the directory.
        if data.get("schema_version") != ALIGNMENT_SCHEMA_VERSION:
            errors.append(f"{path.name}: expected schema_version {ALIGNMENT_SCHEMA_VERSION}")
            continue
        for record_id, row in data.get("records", {}).items():
            where = f"{path.name}:{record_id}"
            if record_id not in record_ids:
                errors.append(f"{where}: not a record in the graph")
                continue
            if record_id in records:
                errors.append(f"{where}: already aligned in another file")
                continue
            if not _check_keys(row, {"short", "lean", "statements"}, set(), where, errors):
                continue
            words = len(str(row["short"]).split())
            if not 1 <= words <= 6:
                errors.append(f"{where}: short has {words} words, expected one to six")
            lean, statements = [], []
            for n, item in enumerate(row["lean"]):
                at = f"{where}.lean[{n}]"
                if not _check_keys(item, {"file", "name", "relation"}, {"note"}, at, errors):
                    continue
                note = item.get("note", "")
                if item["relation"] not in RELATIONS:
                    errors.append(f"{at}: unknown relation {item['relation']}")
                if len(note.split()) > MAX_NOTE_WORDS:
                    errors.append(f"{at}: note exceeds {MAX_NOTE_WORDS} words")
                try:
                    module, target = _find(modules, item["file"], item["name"])
                except ValueError as exc:
                    errors.append(f"{at}: {exc}")
                    continue
                lean.append({"name": target["name"], "module": module, "line": target["line"],
                             "end_line": target["end_line"], "relation": item["relation"], "note": note})
            for n, item in enumerate(row["statements"]):
                at = f"{where}.statements[{n}]"
                if not _check_keys(item, {"paper", "role", "from", "to"}, {"after", "note"}, at, errors):
                    continue
                if item["role"] not in ROLES:
                    errors.append(f"{at}: unknown role {item['role']}")
                if item["paper"] not in prepared:
                    errors.append(f"{at}: unknown paper {item['paper']}")
                    continue
                try:
                    statements.append({"paper": item["paper"], "role": item["role"],
                                       **prepared[item["paper"]].locate(item),
                                       **({"note": item["note"]} if "note" in item else {})})
                except ValueError as exc:
                    errors.append(f"{at}: {exc}")
            records[record_id] = {"short": row["short"], "lean": lean, "statements": statements}
        for n, item in enumerate(data.get("terms", ())):
            at = f"{path.name}:terms[{n}]"
            if not _check_keys(item, {"file", "name", "words"}, {"tex", "paper", "parent", "from", "to", "after"},
                                at, errors):
                continue
            try:
                written = f"{item['parent']}.{item['name']}" if "parent" in item else item["name"]
                module, target = _find(modules, item["file"], written)
                term = {"name": target["name"], "module": module, "line": target["line"],
                        "end_line": target["end_line"], "tex": item.get("tex"), "words": item["words"]}
                if "paper" in item:
                    if item["paper"] not in prepared:
                        raise ValueError(f"unknown paper {item['paper']}")
                    term.update(paper=item["paper"], **prepared[item["paper"]].locate(item))
                dictionary.append(term)
            except ValueError as exc:
                errors.append(f"{at}: {exc}")
    if errors and strict:
        raise ContractError(f"{len(errors)} alignment error(s):\n" + "\n".join(errors))
    return {"records": dict(sorted(records.items())), "dictionary": dictionary}, errors


def default_papers(directory):
    """The maintained papers of the example that holds this alignment directory."""
    directory = Path(directory).resolve()
    root = directory.parents[2] / "papers" / directory.parent.name
    return {"long": root / "long/reasoning-record.md", "short": root / "short/paper.md",
            "expository": root / "expository/main.md"}


def check_alignment(directory, *, lean_tree=None, graph=None, papers=None, out=None):
    """Resolve an alignment directory from files, and report what it covers."""
    directory = Path(directory)
    example = directory.resolve().parent
    index = load_index(lean_tree or example / "upstream/lean")
    nodes = read_json(graph or example / "evidence-graph.json")["nodes"]
    paths = {**default_papers(directory), **(papers or {})}
    contents = {stage: Path(path).read_bytes() for stage, path in paths.items()}
    ids = {row["id"] for row in nodes}
    resolved, _ = resolve_alignment(directory, index, contents, ids)
    if out is not None:
        Path(out).write_bytes(canonical(resolved))
    return {"records": len(resolved["records"]), "graph_records": len(ids),
            "unaligned_records": sorted(ids - resolved["records"].keys()),
            "lean_rows": sum(len(row["lean"]) for row in resolved["records"].values()),
            "statements": sum(len(row["statements"]) for row in resolved["records"].values()),
            "dictionary_terms": len(resolved["dictionary"]),
            "meaning": "Every pointer lands. Whether the statements match remains a reading."}
