"""Resolve authored record alignment against a Lean index and the papers' bytes.

The alignment is a sidecar of pointers: a pass means each pointer lands where it
was written, and says nothing about whether two statements mean the same thing.
"""
from __future__ import annotations

import json
import re
from bisect import bisect_left, bisect_right
from itertools import accumulate
from pathlib import Path

from .bundle import STAGES
from .consumer import _paper_sections
from .contracts import ContractError, read_json
from .lean_index import canonical, load_index

ALIGNMENT_SCHEMA_VERSION = "1.0"
TIES_SCHEMA = 1
NAMES_SCHEMA = 1
NAMES_FILE = "names.json"
RELATIONS = {"states", "contains", "part", "proof", "defines"}
ROLES = {"statement", "definition", "explanation", "derivation", "example", "mention"}
MAX_SLICE_CHARACTERS = 1800
MAX_NOTE_WORDS = 25
# A theorem's type is its statement and the rest is proof. A definition's body is
# part of what it says, so it has no proof lines.
PROOF_KINDS = {"theorem", "lemma"}
_PASSAGE = re.compile(rb"<!-- passage:([^\s>]+) -->")
_EXPLICIT_ID = re.compile(rb"<a\s+[^>]*\bid=[\"']([^\"']+)[\"']")
_COMMENT = re.compile(r"<!--.*?-->", re.S)
_HEADING = re.compile(r" {0,3}#{1,6}(?:[ \t]|$)")
_FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")


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
        return {"markdown": markdown, "start_byte": start_byte, "end_byte": end_byte,
                "at": f"b{start_byte}-{end_byte}", "anchor": anchor,
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


def _statement_lines(declaration):
    """The lines that say what a declaration is, leaving out a theorem's proof."""
    last = declaration["signature_end_line" if declaration["kind"] in PROOF_KINDS else "end_line"]
    return [declaration["line"], last]


def _proof_lines(declaration):
    """A theorem's body when it runs past its statement; a one-line proof has none of its own."""
    stated = declaration["signature_end_line"]
    if declaration["kind"] in PROOF_KINDS and declaration["end_line"] > stated:
        return {"proof_lines": [stated + 1, declaration["end_line"]]}
    return {}


def _places(source, declaration, clause, within=None):
    """Each `[first, last]` a quotation occupies in a declaration, its statement preferred."""
    first, last = within or (declaration["line"], declaration["end_line"])
    text = "\n".join(source[first - 1:last])
    places, at = [], text.find(clause)
    while at >= 0:
        top = first + text.count("\n", 0, at)
        place = [top, top + clause.count("\n")]
        if place not in places:
            places.append(place)
        at = text.find(clause, at + 1)
    top, bottom = _statement_lines(declaration)
    return [place for place in places if top <= place[0] and place[1] <= bottom] or places


def _clause(modules, sources, item, module, target):
    """The authored quotation of a lean row with the lines it sits on, checked against the source."""
    keys = {"clause", "clause_file", "clause_name"} & item.keys()
    if not keys:
        return {}
    clause = item.get("clause")
    if type(clause) is not str or not clause:
        raise ValueError("clause must be nonempty text")
    if keys not in ({"clause"}, {"clause", "clause_file", "clause_name"}):
        raise ValueError("clause_file and clause_name go together, with clause")
    home, owner = (module, target) if keys == {"clause"} else _find(modules, item["clause_file"], item["clause_name"])
    found = {"clause": clause} if owner is target else {"clause": clause, "clause_in": owner["name"]}
    if home not in sources:
        return found
    places = _places(sources[home], owner, clause)
    if not places:
        raise ValueError(f"clause is not in {owner['name']}")
    if owner is target:
        return {**found, "lines": places[0]}
    return {**found, "clause_module": home, "clause_lines": places[0]}


def _named(names, item, rows):
    """The one declaration a statement names, by full name or an unambiguous ending."""
    name = item["name"]
    if type(name) is not str or not name:
        raise ValueError("name must be nonempty text")
    found = names.get(name) or [row for key, group in names.items() if key.endswith("." + name) for row in group]
    if "file" in item:
        found = [row for row in found if row[0]["path"] == item["file"]]
    if not found:
        raise ValueError(f"no declaration {name} in the Lean index"
                         + (f" in {item['file']}" if "file" in item else ""))
    if len(found) > 1:
        held = {(row["module"], row["name"]) for row in rows}
        found = [row for row in found if (row[0]["name"], row[1]["name"]) in held] or found
    if len(found) > 1:
        files = ", ".join(sorted(row[0]["path"] for row in found))
        raise ValueError(f"declaration {name} is ambiguous, add file: {files}")
    return found[0]


def _authored_lines(item, declaration):
    """Check authored lines against the declaration they must lie inside."""
    if "lines" not in item:
        return None
    lines = item["lines"]
    if (type(lines) is not list or len(lines) != 2 or any(type(line) is not int for line in lines)
            or lines[0] > lines[1]):
        raise ValueError(f"lines must be [first, last], got {lines!r}")
    if lines[0] < declaration["line"] or lines[1] > declaration["end_line"]:
        raise ValueError(f"lines {lines} lie outside {declaration['name']}, "
                         f"which runs from line {declaration['line']} to {declaration['end_line']}")
    return lines


def _narrowed(item, rows, names, sources):
    """One authored row of a statement's `lean`, resolved to what the reader receives."""
    module, target = _named(names, item, rows)
    own = next((row for row in rows if (row["module"], row["name"]) == (module["name"], target["name"])), None)
    note, relation = item.get("note", (own or {}).get("note", "")), item.get("relation", (own or {}).get("relation"))
    if type(note) is not str or len(note.split()) > MAX_NOTE_WORDS:
        raise ValueError(f"note must be text of at most {MAX_NOTE_WORDS} words")
    if relation is not None and relation not in RELATIONS:
        raise ValueError(f"unknown relation {relation}")
    lines = _authored_lines(item, target)
    clause = item.get("clause")
    if clause is None:
        if lines is None and own is not None:
            return {**own, "note": note, "relation": relation}
        lines = lines or _statement_lines(target)
    else:
        if type(clause) is not str or not clause:
            raise ValueError("clause must be nonempty text")
        if module["name"] not in sources:
            raise ValueError(f"clause cannot land: the index has no source for {module['name']}")
        places = _places(sources[module["name"]], target, clause, lines)
        if not places:
            within = f" within lines {lines}" if lines else ""
            raise ValueError(f"clause does not land in {target['name']}{within}: {clause[:70]!r}")
        if len(places) > 1:
            raise ValueError(f"clause is ambiguous in {target['name']}, on lines {places}; add lines to choose one")
        lines = places[0]
    return {"name": target["name"], "module": module["name"], "line": target["line"], "end_line": target["end_line"],
            "relation": relation, "note": note, "lines": lines, **_proof_lines(target),
            **({"clause": clause} if clause is not None else {})}


def _plain_names(path, known, errors):
    """Plain titles of declarations from an optional file; a bad entry is reported and left out."""
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_bytes())
    except ValueError as exc:
        errors.append(f"{path.name}: not valid JSON: {exc}")
        return {}
    if not isinstance(data, dict) or data.get("schema") != NAMES_SCHEMA or not isinstance(data.get("names"), dict):
        errors.append(f"{path.name}: expected schema {NAMES_SCHEMA} and a names object")
        return {}
    plain = {}
    for name, title in data["names"].items():
        words = len(title.split()) if type(title) is str else 0
        if name not in known:
            errors.append(f"{path.name}:{name}: not a declaration in the Lean index")
        elif not 2 <= words <= 6:
            errors.append(f"{path.name}:{name}: title has {words} words, expected two to six")
        else:
            plain[name] = title
    return dict(sorted(plain.items()))


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
    `ties-<paper>.json` files add statements to records after the batch files, and an
    optional `names.json` gives declarations plain titles.
    """
    directory = Path(directory)
    if not directory.is_dir():
        raise ContractError(f"alignment directory is absent: {directory}")
    if set(papers) != set(STAGES):
        raise ContractError("alignment requires the long, short and expository papers")
    prepared = {stage: _Paper(content) for stage, content in papers.items()}
    modules, errors = _declarations(index), []
    sources = {module["name"]: module["source"].split("\n") for module in index["modules"] if "source" in module}
    names = {}
    for module in index["modules"]:
        for declaration in module["declarations"]:
            names.setdefault(declaration["name"], []).append((module, declaration))
    records, dictionary = {}, []

    def statement(item, lean, at):
        """One authored slice with the Lean it means, or None after recording why not."""
        if item["role"] not in ROLES:
            errors.append(f"{at}: unknown role {item['role']}")
        if item["paper"] not in prepared:
            errors.append(f"{at}: unknown paper {item['paper']}")
            return None
        narrowed = []
        if "lean" in item:
            if type(item["lean"]) is not list:
                errors.append(f"{at}.lean: must be a list; [] says this statement has no Lean of its own")
            for n, row in enumerate(item["lean"] if type(item["lean"]) is list else ()):
                where = f"{at}.lean[{n}]"
                if _check_keys(row, {"name"}, {"file", "lines", "clause", "note", "relation"}, where, errors):
                    try:
                        narrowed.append(_narrowed(row, lean, names, sources))
                    except ValueError as exc:
                        errors.append(f"{where}: {exc}")
        # An empty list is a claim of its own; only a list left out, or one that failed, falls back.
        own = bool(narrowed) or item.get("lean") == []
        try:
            return {"paper": item["paper"], "role": item["role"], **prepared[item["paper"]].locate(item),
                    "lean": narrowed if own else lean, "lean_source": "statement" if own else "record",
                    **({"note": item["note"]} if "note" in item else {})}
        except ValueError as exc:
            errors.append(f"{at}: {exc}")
            return None

    for path in sorted(directory.glob("*.json")):
        if path.name.startswith("ties-") or path.name == NAMES_FILE:
            continue
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
                if not _check_keys(item, {"file", "name", "relation"},
                                   {"note", "clause", "clause_file", "clause_name"}, at, errors):
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
                resolved = {"name": target["name"], "module": module, "line": target["line"],
                            "end_line": target["end_line"], "relation": item["relation"], "note": note,
                            "lines": _statement_lines(target), **_proof_lines(target)}
                try:
                    resolved.update(_clause(modules, sources, item, module, target))
                except ValueError as exc:
                    errors.append(f"{at}: {exc}")
                lean.append(resolved)
            for n, item in enumerate(row["statements"]):
                at = f"{where}.statements[{n}]"
                if _check_keys(item, {"paper", "role", "from", "to"}, {"after", "lean", "note"}, at, errors):
                    resolved = statement(item, lean, at)
                    if resolved is not None:
                        statements.append(resolved)
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
    tied = set()
    for path in sorted(directory.glob("ties-*.json")):
        paper = path.stem.removeprefix("ties-")
        try:
            data = json.loads(path.read_bytes())
        except ValueError as exc:
            errors.append(f"{path.name}: not valid JSON: {exc}")
            continue
        if paper not in prepared:
            errors.append(f"{path.name}: {paper} is not a paper")
            continue
        if not isinstance(data, dict) or data.get("schema") != TIES_SCHEMA or type(data.get("statements")) is not list:
            errors.append(f"{path.name}: expected schema {TIES_SCHEMA} and a statements list")
            continue
        for n, item in enumerate(data["statements"]):
            at = f"{path.name}:statements[{n}]"
            if not _check_keys(item, {"record", "paper", "role", "from", "to"}, {"after", "lean", "note"}, at, errors):
                continue
            if item["record"] not in records:
                errors.append(f"{at}: {item['record']} is not an aligned record")
                continue
            if item["paper"] != paper:
                errors.append(f"{at}: paper {item['paper']} in a file for {paper}")
                continue
            row = records[item["record"]]
            resolved = statement(item, row["lean"], at)
            if resolved is None:
                continue
            key = (item["record"], paper, resolved["at"])
            if key in tied:
                errors.append(f"{at}: this slice of {item['record']} is already tied")
                continue
            tied.add(key)
            # The same slice in a batch file gives way, so a file of ties can narrow it.
            same = [i for i, old in enumerate(row["statements"]) if (old["paper"], old["at"]) == key[1:]]
            if same:
                row["statements"][same[0]] = resolved
            else:
                row["statements"].append(resolved)
    plain = _plain_names(directory / NAMES_FILE, names, errors)
    for record in records.values():
        for row in (*record["lean"], *(line for item in record["statements"] for line in item["lean"])):
            if row["name"] in plain:
                row["plain"] = plain[row["name"]]
    if errors and strict:
        raise ContractError(f"{len(errors)} alignment error(s):\n" + "\n".join(errors))
    return {"records": dict(sorted(records.items())), "dictionary": dictionary, "names": plain}, errors


def _math_close(text, start, display):
    """Where a dollar span opened before `start` closes, or -1, as `findClose` in the reader."""
    j = start
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if not display and c == "\n" and re.match(r"[ \t]*\n", text[j + 1:j + 80]):
            return -1
        if c == "$":
            if display:
                if text[j + 1:j + 2] == "$":
                    return j
            else:
                after = text[j + 1:j + 2]
                return j if not text[j - 1].isspace() and not (after and after in "0123456789") else -1
        j += 1
    return -1


def _math_spans(text):
    """The `$...$` and `$$...$$` spans of Markdown, by the rules of `site/src/reader/math.ts`."""
    spans, i, n, line_start, fence = [], 0, len(text), True, None
    while i < n:
        if line_start:
            stop = text.find("\n", i)
            stop = n if stop < 0 else stop
            line = text[i:stop]
            mark = _FENCE.match(line)
            if fence is not None or mark:
                if fence is None:
                    fence = mark.group(1)
                elif mark and mark.group(1)[0] == fence[0] and len(mark.group(1)) >= len(fence) \
                        and line.strip() == mark.group(1):
                    fence = None
                i = min(stop + 1, n)
                continue
        c = text[i]
        line_start = False
        if c == "\n":
            line_start = True
        elif c == "\\":
            i += 1
        elif c == "`":
            run = 1
            while text[i + run:i + run + 1] == "`":
                run += 1
            close = text.find("`" * run, i + run)
            while close >= 0 and text[close + run:close + run + 1] == "`":
                close = text.find("`" * run, close + run + 1)
            i = (close + run if close >= 0 else i + run) - 1
        elif c == "$":
            display = text[i + 1:i + 2] == "$"
            if display or (i + 1 < n and not text[i + 1].isspace()):
                width = 2 if display else 1
                close = _math_close(text, i + width, display)
                if close > i + width:
                    spans.append((i, close + width, display))
                    i = close + width
                    continue
        i += 1
    return spans


def _blocks(text, begin, end):
    """The spans of `text[begin:end]` between blank lines, with each heading on its own."""
    blocks, left, right = [], None, None

    def close():
        nonlocal left
        if left is not None:
            blocks.append((left, right))
        left = None

    for match in re.finditer(r"[^\n]+", text[begin:end]):
        first, last = begin + match.start(), begin + match.end()
        heading = (first == 0 or text[first - 1] == "\n") and _HEADING.match(match.group())
        if left is not None and (heading or first > right + 1):
            close()
        if match.group().strip():
            left, right = first if left is None else left, last
            if heading:
                close()
        else:
            close()
    close()
    return blocks


def _pieces(text):
    """What a segment must stay inside: text blocks and whole displays, with the inline math."""
    pieces, inline, at = [], [], 0
    for left, right in [*(m.span() for m in _COMMENT.finditer(text)), (len(text), len(text))]:
        cursor = at
        for start, stop, display in _math_spans(text[at:left]):
            start, stop = start + at, stop + at
            if display:
                pieces.extend((*block, False) for block in _blocks(text, cursor, start))
                pieces.append((start, stop, True))
                cursor = stop
            else:
                inline.append((start, stop))
        pieces.extend((*block, False) for block in _blocks(text, cursor, left))
        at = right
    return pieces, inline


def _outward(left, right, inline, starts):
    """Move a range's ends out of any inline math they fall inside."""
    before = bisect_left(starts, left) - 1
    if before >= 0 and inline[before][1] > left:
        left = inline[before][0]
    before = bisect_left(starts, right) - 1
    if before >= 0 and inline[before][1] > right:
        right = inline[before][1]
    return left, right


def _tie(record_id, row, names=()):
    """What a statement offers a reader at a glance; the first Lean row is the most direct."""
    lean = row["lean"][0] if row["lean"] else None
    exact = lean is not None and "clause_in" in lean and "clause_lines" in lean
    name = None if lean is None else lean["clause_in"] if exact else lean["name"]
    return {"record": record_id, "role": row["role"], "lean": lean is not None,
            "from_record": lean is not None and row["lean_source"] == "record",
            "name": name, **({"plain": names[name]} if name in names else {}),
            "module": None if lean is None else lean["clause_module"] if exact else lean["module"],
            "lines": None if lean is None else lean["clause_lines"] if exact else lean["lines"],
            "anchor": row["anchor"], "at": row["at"]}


def tie_index(content, records, stage, passages=(), names=()):
    """Every statement slice of one paper, cut to where a reader can mark it.

    `segments` never overlap. Each stays inside one block and keeps its math whole, and
    any display a slice touches is tied whole. A segment lists its ties with Lean first,
    then the narrowest. `passages` take `(start, end, record ids, anchor)` and fall back
    for text with no slice, and `names` gives a tie its declaration's plain title. Each
    entry is a pointer that landed, not a mathematical check.
    """
    text = content.decode("utf-8")
    bytes_at = [0, *accumulate(len(c.encode("utf-8")) for c in text)]
    rows = {(row["start_byte"], row["end_byte"], record_id): row for record_id, record in records.items()
            for row in record["statements"] if row["paper"] == stage}
    keys = sorted(rows)
    ties = [_tie(key[2], rows[key], names) for key in keys]
    pieces, inline = _pieces(text)
    starts = [left for left, _ in inline]
    piece_starts = [piece[0] for piece in pieces]
    covering = [[] for _ in pieces]
    for number, (start_byte, end_byte, _) in enumerate(keys):
        start, end = bisect_left(bytes_at, start_byte), bisect_left(bytes_at, end_byte)
        for i in range(max(bisect_right(piece_starts, start) - 1, 0), bisect_left(piece_starts, end)):
            left, right, display = pieces[i]
            clipped = (max(start, left), min(end, right))
            if clipped[0] < clipped[1]:
                covering[i].append((left, right, number) if display else
                                   (*_outward(*clipped, inline, starts), number))
    order = lambda number: (not ties[number]["lean"], keys[number][1] - keys[number][0], number)
    segments = []
    for ranges in covering:
        points = sorted({point for row in ranges for point in row[:2]})
        for left, right in zip(points, points[1:]):
            members = sorted((number for start, stop, number in ranges if start <= left and right <= stop), key=order)
            body = text[left:right]
            if members and body.strip():
                left += len(body) - len(body.lstrip())
                right -= len(body) - len(body.rstrip())
                segments.append([bytes_at[left], bytes_at[right], members])
    fallback = []
    for start, end, ids, anchor in passages:
        held = {tie["record"] for tie in ties if tie["anchor"] == anchor}
        if ids or held:
            fallback.append([start, end, sorted({*ids, *held}), anchor])
    return {"segments": segments, "ties": ties, "passages": sorted(fallback, key=lambda row: row[:2]),
            "meaning": "Each tie is a pointer that landed. Whether the paper and the Lean say the same thing is a reading."}


def lean_steps(alignment, index, edges, *, max_depth=8):
    """Follow each curated step through the Lean source, where both records have Lean links.

    A step records that one result uses another. When declarations are linked to both,
    the shortest chain of names from a consumer's declaration to a prerequisite's says
    where the Lean makes that use. `route` is null when no chain was found within
    `max_depth`; names reached only through tactics or notation are not in the source
    scan, so a missing chain does not show that the step is absent.
    """
    # The Comparator challenge restates names from the proof tree, so a name can have two rows.
    uses = {}
    for module in index["modules"]:
        for row in module["declarations"]:
            uses.setdefault(row["name"], []).extend(row.get("uses", ()))
    records = alignment["records"]
    steps = {}
    for edge in edges:
        if edge.get("kind") != "supports":
            continue
        starts = [row["name"] for row in records.get(edge["from"], {}).get("lean", ()) if row["relation"] != "defines"]
        targets = {row["name"] for row in records.get(edge["to"], {}).get("lean", ())}
        if not starts or not targets:
            continue
        route = None
        if targets & set(starts):
            route = [next(name for name in starts if name in targets)]
        else:
            parent = dict.fromkeys(starts)
            frontier = list(parent)
            for _ in range(max_depth):
                following = []
                for name in frontier:
                    for used in uses.get(name, ()):
                        if used not in parent:
                            parent[used] = name
                            following.append(used)
                hit = next((name for name in following if name in targets), None)
                if hit is not None:
                    route = [hit]
                    while parent[route[-1]] is not None:
                        route.append(parent[route[-1]])
                    route.reverse()
                    break
                frontier = following
        steps[f"{edge['from']}→{edge['to']}→{edge['kind']}"] = {"route": route}
    return dict(sorted(steps.items()))


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
    statements = [row for record in resolved["records"].values() for row in record["statements"]]
    return {"records": len(resolved["records"]), "graph_records": len(ids),
            "unaligned_records": sorted(ids - resolved["records"].keys()),
            "lean_rows": sum(len(row["lean"]) for row in resolved["records"].values()),
            "statements": len(statements),
            "statements_naming_lean": sum(row["lean_source"] == "statement" and bool(row["lean"]) for row in statements),
            "statements_with_no_lean_of_their_own": sum(row["lean_source"] == "statement" and not row["lean"]
                                                        for row in statements),
            "statements_showing_the_records_lean": sum(row["lean_source"] == "record" and bool(row["lean"])
                                                       for row in statements),
            "tie_segments": {stage: len(tie_index(content, resolved["records"], stage)["segments"])
                             for stage, content in contents.items()},
            "dictionary_terms": len(resolved["dictionary"]),
            "plain_names": len(resolved["names"]),
            "meaning": "Every pointer lands. Whether the statements match remains a reading."}
