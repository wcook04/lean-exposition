#!/usr/bin/env python3
"""Convert one Proof Reader page into a library instance of this reader.

A Proof Reader page is a folder `papers/<slug>/` of wcook04/proof-reader: `paper.toml`
(title, authors, credit, the Lean project), `links.json` (passages quoting the
paper with their Lean, topics with families, per-passage comparisons, claims, plain
titles, reading notes, the declarations no sentence names), the reading copy
(`paper.md`) and the Lean project. This writes `instances/<paper>/` in the layout
docs/library-architecture.md describes:

    instance.json                 who wrote what, credit lines, documents, families, topics
    papers/<slot>/paper.md        the reading copy, with passage markers and section anchors
    papers/<slot>/correspondence.json   the paper mapping (artifact schema 1.2)
    papers/<slot>/figures/        the paper's figures
    evidence-graph.json           graph schema 1.2: the numbered results, their Lean, the links
    alignment/phrases-<slot>.json phrase-ties/1: every passage as a tie, topics carry `family`
    alignment/names.json          plain titles of two to six words
    alignment/references-*.json   the citation table
    alignment/results.json        numbered results by address (theorem-1.1) and old claim id
    alignment/aliases.json        old passage ids and where each now lands
    upstream/lean/                the Lean the instance cites, unchanged, with source-lock.json
    generated/                    supplementary checks, the declarations no sentence names

The engine still reads three document slots (long, short, expository). A page uses one
slot; the other two hold an empty scaffold that the reader does not show.

Everything is derived from the inputs. Titles longer than six words are replaced from
`--titles` (an authored file of plain titles); a title missing there is reported. Nothing
here judges whether a phrase and its Lean say the same: that is the comparison the source
recorded, carried through with its AI label.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from lean_exposition.alignment import _math_spans  # noqa: E402

SLOTS = ("long", "short", "expository")
ROLE = {"states": ("statement", "states"), "defines": ("definition", "defines"),
        "proves": ("derivation", "proof"), "explains": ("explanation", "part"),
        "mentions": ("mention", "states"), "uses": ("explanation", "part"), "mirrors": ("statement", "states")}
KIND_WORDS = ("theorem", "proposition", "lemma", "corollary", "definition", "remark", "conjecture",
              "problem", "example", "assumption", "claim", "step")
AI = "Claude (Anthropic), an AI agent"
HEADING = re.compile(r"^(#{1,6}) (.+)$", re.M)
CITE = re.compile(r"\[([^\[\]\n]+)\]\(#(cite-[^)\s]+)\)")
REF_ANCHOR = re.compile(r'<a id="(cite-[^"]+)"></a>')
EMPTY = ("<!-- EMPTY SCAFFOLD: this paper has no document in this slot. No result or review is "
         "asserted here, and the reader does not show it. -->\n")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dumps(value) -> str:
    return json.dumps(value, indent=1, ensure_ascii=False) + "\n"


def write(path: Path, text: str | bytes) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = text.encode("utf-8") if isinstance(text, str) else text
    path.write_bytes(data)
    return sha(data)


def words(text: str) -> int:
    return len(text.split())


def slug_of(title: str) -> str | None:
    """`Theorem 1.1` -> `theorem-1.1`: the numbered result's address in the authors' own numbering."""
    m = re.match(r"^\s*([A-Za-z]+)\s+([0-9A-Za-z.]+)", title)
    if not m or m.group(1).lower() not in KIND_WORDS:
        return None
    return f"{m.group(1).lower()}-{m.group(2).lower().rstrip('.')}"


def address_of(claim: dict) -> str:
    """A result's address: its number in the authors' numbering (`theorem-1.1`), or, for a result the
    page states without a number ("The PCP theorem"), its Proof Reader claim id under `claim-`
    (`claim-1`, `claim-reference-np-equivalence`), so the old claim address maps onto it exactly."""
    numbered = slug_of(claim["title"])
    if numbered:
        return numbered
    cid = re.sub(r"[^0-9a-z.-]+", "-", claim["id"].lower()).strip("-")
    return cid if re.match(r"^claim-[0-9a-z.]", cid) else f"claim-{cid}"


LABEL = re.compile(r"\*\*\s*((" + "|".join(w.capitalize() for w in KIND_WORDS) + r")\s+([0-9A-Z](?:[0-9A-Za-z]|\.(?=[0-9A-Za-z]))*))\.?(?:\s*\(([^;)]*)[;)])?")


def printed_label(claim: dict, quote: str, text: str) -> str | None:
    """The authors' own label for a result Proof Reader titles in words: the bold label that opens
    its statement ("**Lemma 4.1 (standard low-degree test; ...).**"), found where its phrase begins,
    or as the label whose parenthesised name is the claim's title. None when the paper prints no number."""
    m = LABEL.match(quote.lstrip())
    if m:
        return m.group(1)
    title = claim["title"].strip().lower()
    for m in LABEL.finditer(text):
        if m.group(4) and m.group(4).strip().lower() == title:
            return m.group(1)
    return None


def section_number(heading: str) -> str | None:
    """`5.5.1 The equations at each level` -> `5.5.1`; `Appendix A ...` -> `appendix-a`.

    A number may end in a full stop, as papers set with Pandoc print them (`3.1. The promise`,
    `Appendix A. The upper bound`, `A.2. The adversary bound` -> `appendix-a.2`).
    """
    m = re.match(r"^(\d+(?:\.\d+)*)\.?\s", heading)
    if m:
        return m.group(1)
    m = re.match(r"^(?:Appendix\s+)?([A-Z])(?:\.(\d+(?:\.\d+)*))?\.?\s", heading)
    if m and (heading.startswith("Appendix") or m.group(2)):
        return "appendix-" + m.group(1).lower() + (f".{m.group(2)}" if m.group(2) else "")
    return None


class Lean:
    """The vendored Lean, indexed by this repository's text scan, and the names Proof Reader uses."""

    def __init__(self, index: dict):
        self.by_name, self.by_module_short = {}, {}
        for module in index["modules"]:
            for d in module["declarations"]:
                row = (module["path"], d)
                self.by_name.setdefault(d["name"], row)
                self.by_module_short.setdefault((module["name"], d["short"]), row)

    def resolve(self, name: str):
        """(lean-index name, file, declaration row) or None. `_private.<module>.0.<name>` names a private helper."""
        if name in self.by_name:
            path, d = self.by_name[name]
            return d["name"], path, d
        m = re.match(r"^_private\.(.+?)\.0\.(.+)$", name)
        if m:
            short = m.group(2).rsplit(".", 1)[-1]
            row = self.by_module_short.get((m.group(1), short))
            if row:
                return row[1]["name"], row[0], row[1]
        return None


def reading_copy(md: str, passages: list[dict]) -> tuple[str, list[dict], dict]:
    """Wrap each top-level section in passage markers and anchor each numbered heading.

    Returns the new text, the passages of the mapping (anchor, heading, text) and the
    section anchors by number. A Proof Reader quote never crosses a heading, so every
    quote stays inside one marked section.
    """
    # The source's own markup that this reader writes itself: a YAML front-matter block, and Proof
    # Reader's block markers (<!-- passage:id --> ... <!-- /passage:id -->), which would nest inside
    # the section markers below. The passages keep their ids as ties; the markers carry no text.
    md = re.sub(r"\A---\n.*?\n---\n+", "", md, flags=re.S)
    md = re.sub(r"^<!-- /?passage:[^>]*-->[ \t]*\n?", "", md, flags=re.M)
    heads = [(m.start(), len(m.group(1)), m.group(2).strip()) for m in HEADING.finditer(md)]
    out, sections, anchors, last = [], [], {}, 0
    bounds = [h for h in heads if h[1] <= 2]
    # The front matter (title, authors, abstract) up to the first section is one passage.
    cuts = [(0, 0, "Front matter")] + [b for b in bounds if b[0] > 0]
    for k, (start, level, title) in enumerate(cuts):
        stop = cuts[k + 1][0] if k + 1 < len(cuts) else len(md)
        chunk = md[start:stop]
        # Anchor every numbered heading inside the chunk, top level or not.
        def anchor(m):
            number = section_number(m.group(2).strip())
            if not number or number in anchors:
                return m.group(0)
            anchors[number] = m.group(2).strip()
            return f'<a id="{number}"></a>\n\n{m.group(0)}'
        chunk = HEADING.sub(anchor, chunk)
        name = "front" if k == 0 else (("sec-" + section_number(title)) if section_number(title) else
                                       "sec-" + re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-"))
        # Markers go after the heading line so the heading itself stays a heading.
        body_at = 0
        if k > 0:
            hm = re.search(rf"^#{{1,2}} {re.escape(title)}\n", chunk, re.M)
            body_at = hm.end() if hm else 0
        head, body = chunk[:body_at], chunk[body_at:]
        body = body.rstrip("\n")
        marked = f"{head}\n<!-- passage:{name} -->\n{body}\n<!-- /passage:{name} -->\n\n"
        out.append(marked)
        sections.append({"anchor": name, "heading": title, "text": "\n" + body + "\n"})
    return "".join(out), sections, anchors


def github_slug(heading: str) -> str:
    """The fragment GitHub gives a Markdown heading: `4.2 The standard test` -> `42-the-standard-test`."""
    text = re.sub(r"[*_`$\\]", "", heading.strip().lower())
    return re.sub(r"\s", "-", re.sub(r"[^\w\s-]", "", text))


def section_slugs(md: str) -> dict[str, str]:
    """Each numbered heading's GitHub fragment and the section number this reader anchors it at."""
    out = {}
    for m in HEADING.finditer(md):
        number = section_number(m.group(2).strip())
        if number:
            out.setdefault(github_slug(m.group(2)), number)
    return out


LINK = re.compile(r"\]\(([^()\s]*)\)")


def relink(md: str, own: dict[str, str], companions: dict[str, dict[str, str]], base_url: str) -> str:
    """Point a page's links where this reader can follow them. A fragment written as GitHub's heading
    slug (`#42-the-standard-test`), in the page itself or in a companion page this paper carries, names
    the section number the reader anchors (`#4.2`). Any other relative link (a README or a Lean file of
    the authors' repository) is resolved against the page's own URL in that repository."""
    from urllib.parse import urljoin

    def one(m):
        href = m.group(1)
        path, _, frag = href.partition("#")
        if not path:
            return f"]({'#' + own.get(frag, frag) if frag else href})"
        if path in companions:
            return f"]({path}{'#' + companions[path].get(frag, frag) if frag else ''})"
        if re.match(r"^[a-z][a-z0-9+.-]*:", path) or path.startswith("/") or not base_url:
            return m.group(0)
        return f"]({urljoin(base_url, href)})"
    return LINK.sub(one, md)


UNASSESSED = "unassessed"


def assessment(comparisons: dict, name: str) -> dict:
    """The comparison the source recorded for this Lean name, or the explicit unassessed state.

    Three states, never defaulted into one another: assessed (a verdict, with its note), held
    (a comparison exists but is not shown) and unassessed (the source records none).
    """
    c = comparisons.get(name)
    if c is None:
        return {"fidelity": UNASSESSED, "note": ""}
    return {"fidelity": c["fidelity"], "note": (c.get("note") or "").strip()}


def md_escape(text: str) -> str:
    """Text from a PDF's text layer as literal Markdown: no character starts markup or maths."""
    text = re.sub(r"([\\`*_\[\]<>#$|~])", r"\\\1", text)
    return re.sub(r"(?m)^(\s*)(\d+)\.(\s)", r"\1\2\\.\3", re.sub(r"(?m)^(\s*)([-+])(\s)", r"\1\\\2\3", text))


def pdf_index(title: str, passages: list[dict]) -> str:
    """An index of a PDF's quoted passages: one heading per section, the quotes in page order."""
    rows = sorted(passages, key=lambda p: (p.get("page", 0), passages.index(p)))
    for p in rows:
        p["quote"] = md_escape(re.sub(r"\s+", " ", p["quote"]).strip())
    # A quote that repeats another, or lies inside a longer one, is not printed again: its phrase is
    # found inside the one printed, and shares or nests in its tie.
    quotes = [p["quote"] for p in rows]
    out, section, printed = [f"# {title}\n"], None, set()
    for p in rows:
        if p["quote"] in printed or any(p["quote"] in q and p["quote"] != q for q in quotes):
            continue
        printed.add(p["quote"])
        if p.get("section") != section:
            section = p.get("section")
            out.append(f"\n## {section} {md_escape(p.get('title') or '')}".rstrip() + "\n")
        out.append(f"\n{p['quote']}\n")
    return "".join(out)


def plain_index(text: str) -> tuple[str, list[int]]:
    """The text a reader sees, without Markdown's inline markup (code ticks, emphasis, link targets,
    escapes, HTML tags, footnote marks), and for each of its characters the offset in the source."""
    out, at, i, n = [], [], 0, len(text)
    while i < n:
        c = text[i]
        if c == "\\" and i + 1 < n and text[i + 1] in "[]()*_`$#\\":
            out.append(text[i + 1]); at.append(i + 1); i += 2; continue
        if c in "`*" or (c == "_" and (i == 0 or not text[i - 1].isalnum() or i + 1 >= n or not text[i + 1].isalnum())):
            i += 1; continue
        if c == "]" and text.startswith("(", i + 1):
            close = text.find(")", i + 1)
            i = close + 1 if close > 0 else i + 1; continue
        if c == "[" and text.startswith("^", i + 1):
            close = text.find("]", i)
            i = close + 1 if close > 0 else i + 1; continue
        if c in "[":
            i += 1; continue
        if c == "<":
            close = text.find(">", i)
            if 0 < close < i + 200:
                i = close + 1; continue
        if c.isspace():
            if out and out[-1] == " ":
                i += 1; continue
            out.append(" "); at.append(i); i += 1; continue
        out.append(c); at.append(i); i += 1
    return "".join(out), at


def locate(text: str, quote: str, section: str | None, plain: tuple[str, list[int]]) -> tuple[int, int] | None:
    """Where a quote stands in the source: exactly once, or once as the reader sees the text (markup
    removed), taking the first place inside the quote's own section when the words recur. The span is
    widened to whole code spans, emphasis and links so the phrase never cuts the markup."""
    at = text.find(quote)
    if at >= 0 and text.find(quote, at + 1) < 0:
        return at, at + len(quote)
    flat, back = plain
    q = re.sub(r"\s+", " ", re.sub(r"[`*]", "", quote)).strip()
    hits = [m.start() for m in re.finditer(re.escape(q), flat)] if q else []
    if len(hits) > 1 and section:
        mark = text.find(f'<a id="{section}"></a>')
        if mark >= 0:
            inside = [h for h in hits if back[h] >= mark]
            hits = inside[:1] if inside else hits
    if len(hits) != 1:
        return None
    start, stop = back[hits[0]], back[hits[0] + len(q) - 1] + 1
    for delim in ("`", "**", "*"):
        while text[start:stop].count(delim) % 2 and text[start - len(delim):start] == delim:
            start -= len(delim)
        while text[start:stop].count(delim) % 2 and text[stop:stop + len(delim)] == delim:
            stop += len(delim)
    # A link cut by the end of the phrase keeps its target; one cut by its start keeps its bracket.
    if text[start:stop].count("[") > text[start:stop].count("]"):
        close = text.find(")", text.find("](", stop) + 1) if text.find("](", stop) >= 0 else -1
        if close > 0:
            stop = close + 1
    if text[start:stop].count("](") > text[start:stop].count("["):
        start = text.rfind("[", 0, start)
    if re.search(r"\]\([^)]*$", text[start:stop]):
        stop = text.find(")", stop) + 1
    return start, stop


def phrase_rows(text: str, passages: list[dict], lean: Lean, links: dict, report: dict):
    """Every passage as a phrase tie.

    The reader's phrases may not overlap, so identical or nested spans share one tie; its id is the
    first phrase's and the others are kept as aliases. Nothing is lost in the merge: the tie records
    every phrase it holds (`merged`), and each Lean row keeps every phrase's own comparison of it
    (`assessments`), so a verdict about one phrase is never shown as a verdict about another.
    """
    spans, plain = [], plain_index(text)
    for p in passages:
        found = locate(text, p["quote"], p.get("section"), plain)
        if not found:
            report["quote_not_unique"].append(p["id"])
            continue
        if text[found[0]:found[1]] != p["quote"]:
            report.setdefault("quote_read_through_markup", []).append(p["id"])
        spans.append([found[0], found[1], p])
    spans.sort(key=lambda s: (s[0], -s[1]))
    merged, aliases = [], {}
    for s in spans:
        if merged and s[0] < merged[-1][1]:
            host = merged[-1]
            host[1] = max(host[1], s[1])
            host[3].append(s[2])
            aliases[s[2]["id"]] = host[2]["id"]
            continue
        merged.append([s[0], s[1], s[2], [s[2]]])
    ties = []
    for start, stop, first, group in merged:
        role, _ = ROLE[first["role"]]
        rows, by_target = [], {}
        for p in group:
            comparisons = {c["lean"]: c for c in p.get("comparisons", [])}
            for name in p["lean"]:
                found = lean.resolve(name)
                if not found:
                    report["lean_not_in_index"].append(name)
                    continue
                target, path, decl = found
                c = assessment(comparisons, name)
                if c["fidelity"] == UNASSESSED:
                    report["unassessed"].append([p["id"], target])
                note = c["note"]
                if c["fidelity"] not in {"same", UNASSESSED} and not note:
                    note = "The source records this verdict without a note."
                    report["verdict_without_note"].append(p["id"])
                one = {"phrase": p["id"], "fidelity": c["fidelity"], **({"fidelity_note": note} if note else {})}
                if target in by_target:
                    by_target[target]["assessments"].append(one)
                    continue
                row = {"name": target, "file": path, "relation": ROLE[p["role"]][1], "fidelity": c["fidelity"]}
                if note:
                    row["fidelity_note"] = note
                matters = (comparisons.get(name) or {}).get("matters")
                if isinstance(matters, dict):
                    row["matters"] = matters
                row["assessments"] = [one]
                by_target[target] = row
                rows.append(row)
        for row in rows:
            # A row's own fields are the first phrase's assessment; the others travel with it. A tie
            # of one phrase needs no list.
            if len(group) == 1:
                del row["assessments"]
            elif len({(a["fidelity"], a.get("fidelity_note", "")) for a in row["assessments"]}) > 1:
                report["merged_assessments_differ"].append([first["id"], row["name"],
                                                            [[a["phrase"], a["fidelity"]] for a in row["assessments"]]])
        body = text[start:stop]
        tie = {"id": first["id"], "from": body, "to": body, "role": role, "topic": first["topic"],
               "status": "new", "lean": rows}
        if role in {"statement", "definition"} and not rows:
            tie["role"] = "explanation"
            report["statement_without_lean"].append(first["id"])
        if isinstance(first.get("explanation"), dict):
            tie["explanation"] = first["explanation"]
        if len(group) > 1:
            tie["replaces"] = [p["id"] for p in group[1:]]
            # The merge, recorded: each phrase the tie holds, with its own words, role and topic.
            tie["merged"] = [{"id": p["id"], "quote": p["quote"], "role": ROLE[p["role"]][0], "topic": p["topic"]}
                             for p in group]
            report["merged"].append([p["id"] for p in group])
        ties.append(tie)
    return ties, aliases


MAX_BLOCK = 1700  # under the alignment's limit on one statement slice (MAX_SLICE_CHARACTERS)


def math_open(text: str, start: int, stop: int) -> bool:
    """Whether `stop` falls inside a formula, reading from `start` (a paragraph's beginning)."""
    i, inline, display = start, False, False
    while i < stop:
        if text.startswith("\\$", i):
            i += 2
            continue
        if text.startswith("$$", i):
            display = not display
            i += 2
            continue
        if text[i] == "$" and not display:
            inline = not inline
        i += 1
    return inline or display


def statement_block(text: str, title: str, section_at: int | None, fallback: tuple[int, int] | None) -> tuple[int, int, bool]:
    """A numbered result's canonical target: its statement block, from the authors' bold label
    ("**Theorem 1.1.**") to the end of that paragraph, displays included.

    Where the label occurs more than once, the first occurrence in the result's own section wins.
    A block longer than the alignment allows ends at its last sentence that fits. Without a label,
    the claim's own phrase is the block. Returns (start, stop, found_label).
    """
    label = re.compile(r"\*\*" + re.escape(title) + r"(?=[.\s(*:])(?!\.\d)")
    hits = [m.start() for m in label.finditer(text)]
    if section_at is not None and any(h >= section_at for h in hits):
        hits = [h for h in hits if h >= section_at]
    if not hits:
        if fallback is None:
            raise ValueError(f"no statement of {title}")
        return fallback[0], fallback[1], False
    begin = hits[0]
    stop = begin
    while True:
        nxt = text.find("\n\n", stop)
        if nxt < 0:
            stop = len(text)
            break
        if not math_open(text, begin, nxt):
            stop = nxt
            break
        stop = nxt + 2
    while text[stop - 1:stop].isspace():
        stop -= 1
    if stop - begin > MAX_BLOCK:
        cuts = [m.end() for m in re.finditer(r"[.;:](?=\s)", text[begin:begin + MAX_BLOCK])]
        cuts = [begin + c for c in cuts if not math_open(text, begin, begin + c)]
        stop = cuts[-1] if cuts else min(stop, (fallback or (begin, begin + MAX_BLOCK))[1])
    return begin, stop, True


def keep_addresses(old_order: list[str], old_aliases: dict, aliases: dict, new_ids: list[str], report: dict,
                   date: str, old_retired: dict | None = None) -> tuple[dict, dict]:
    """Every old tie id stays an address, without ever silently meaning something else.

    A phrase merged into another (`aliases`) genuinely lives inside it, so its id is an alias of the
    tie that holds it. A tie that is gone, or an old alias no current merge explains, is retired: its address
    opens a notice saying when it was retired and naming the nearest current phrase in the old reading
    order, which the reader may follow; it never lands there by itself.
    Returns (aliases, retired).
    """
    alive = set(new_ids)
    out = dict(aliases)
    retired = {}
    for old, row in (old_retired or {}).items():
        if old in alive or old in out:
            continue  # a retired id that names a phrase again is an address of that phrase
        nearest = row.get("nearest")
        while nearest in out and nearest not in alive:
            nearest = out[nearest]
        retired[old] = {**row, "nearest": nearest if nearest in alive else None}
    gone = [i for i in old_order if i not in alive and i not in out]
    for k, old in enumerate(old_order):
        if old in alive or old in out:
            continue
        before = next((old_order[j] for j in range(k - 1, -1, -1) if old_order[j] in alive), None)
        after = next((old_order[j] for j in range(k + 1, len(old_order)) if old_order[j] in alive), None)
        retired[old] = {"retired": date, "nearest": before or after}
    # An old alias is kept only when this import merges the same phrase again (it is then in `out`).
    # Any other old alias names a phrase that is gone, or one an earlier import sent to a neighbour;
    # it is retired, with the tie it pointed at offered as the nearest current phrase.
    for old, host in old_aliases.items():
        if old in alive or old in out or old in retired:
            continue
        while host in out and host not in alive:
            host = out[host]
        retired[old] = {"retired": date, "nearest": host if host in alive else None}
    report["gone_kept_as_addresses"] = gone
    report["retired"] = sorted(retired)
    return out, dict(sorted(retired.items()))


def references(text: str, slot: str) -> dict:
    data = text.encode("utf-8")
    offsets = [0]
    for ch in text:
        offsets.append(offsets[-1] + len(ch.encode("utf-8")))
    sources, rows = {}, []
    for m in REF_ANCHOR.finditer(text):
        line_end = text.find("\n", m.end())
        entry = text[m.end():line_end if line_end >= 0 else len(text)]
        href = re.search(r"\]\((https?://[^)\s]+)\)", entry)
        body = re.sub(r"^\\\[\d+\\\]\s*", "", entry)
        authors = re.split(r",\s*\*|,\s*\[", body, maxsplit=1)[0].strip()
        year = re.search(r"\((\d{4})\)", entry)
        sources[m.group(1)[len("cite-"):]] = {
            "name": f"{authors} ({year.group(1)})" if year else authors,
            "href": href.group(1) if href else f"#{m.group(1)}",
            "entry": [offsets[m.end()], offsets[line_end if line_end >= 0 else len(text)]]}
    for m in CITE.finditer(text):
        key = m.group(2)[len("cite-"):]
        if key not in sources:
            continue
        rows.append({"start_byte": offsets[m.start()], "end_byte": offsets[m.end()], "quote": m.group(0),
                     "before": text[max(0, m.start() - 60):m.start()], "kind": "citation", "source": key,
                     "cited_as": m.group(1)})
    return {"schema_version": "1.0", "paper": slot, "paper_sha256": sha(data),
            "provenance": "Generated by scripts/from_proof_reader.py from the paper's own citation links",
            "targets": {}, "sources": sources, "references": rows}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("page", type=Path, help="a Proof Reader papers/<slug>/ folder")
    ap.add_argument("--paper", required=True, help="the library paper id, e.g. euler")
    ap.add_argument("--out", type=Path, required=True, help="instances/<paper>/")
    ap.add_argument("--source-commit", required=True, help="the proof-reader commit the page was read at")
    ap.add_argument("--titles", type=Path, help="authored plain titles replacing any longer than six words")
    ap.add_argument("--goal", default="theorem-1.1", help="the numbered result the map starts from")
    ap.add_argument("--slot", default="short", choices=SLOTS)
    ap.add_argument("--pdf", type=Path, help="the authors' own PDF of the paper, published byte for byte")
    ap.add_argument("--reimport", action="store_true",
                    help="replace the ties, comparisons and notes of an existing instance, keeping every old tie id as an address")
    ap.add_argument("--retired-on", default=__import__("datetime").date.today().isoformat(),
                    help="the date a re-import records for the phrase links it retires (YYYY-MM-DD; default today)")
    ap.add_argument("--start-here", type=Path, help="a long Markdown 'Start here' for the paper, read as a page of its own")
    ap.add_argument("--guide", type=Path, help="a Markdown guide to how the Lean encodes the paper's objects, read as a page of its own")
    ap.add_argument("--hold-comparisons", action="store_true",
                    help="keep the page's comparisons hidden: every comparison is replaced by the page's held text (fidelity_held)")
    ap.add_argument("--lean-exposition", default="lean-exposition", help="the lean-exposition command")
    ap.add_argument("--partial", action="store_true",
                    help="allow linked declarations without a plain title or reading note (the card shows the Lean name)")
    ap.add_argument("--companion", action="append", default=[], metavar="SLOT=PAGE[+PAGE...][|slug|Title]",
                    help="a companion reading page in another document slot, read beside the same Lean "
                         "(several pages joined with + are read as one document, in order)")
    ap.add_argument("--paper-logic", type=Path,
                    help="authored JSON: the paper's own stated logic between its results, as supports edges sourced to the "
                         "paper, and unnumbered results it states (nodes with their phrase and Lean)")
    ap.add_argument("--lean-index", type=Path,
                    help="a prebuilt Lean index (with uses) of another instance's vendored Lean, read instead of "
                         "vendoring and indexing the page's project (a companion read beside its paper's Lean)")
    ap.add_argument("--lean-lock", type=Path, help="with --lean-index: the source lock of that instance's Lean")
    ap.add_argument("--companions-index", type=Path,
                    help="index.json of companion pages (<slug>/document.md, <slug>/links.json beside it), each read as a "
                         "document of its own at its library_page, beside the same Lean")
    ap.add_argument("--credit", help="the credit line, exactly, in place of paper.toml's [credit] text")
    ap.add_argument("--authors", action="append", help="the paper's authors as the header names them, in place of paper.toml's (repeat for each)")
    ap.add_argument("--companion-credit", help="the line companion pages carry, in place of 'Paper and Lean by <authors>, from their repository ...'")
    ap.add_argument("--path", help="where the paper is served under the library, when not at its id (a document of another paper: pcp/reading-guide)")
    ap.add_argument("--external", action="append", default=[], metavar="HREF|Title|noun",
                    help="a document of the same paper read in another build, at HREF under the library root (pcp/reading-guide/); the Read menu links to it")
    args = ap.parse_args()
    page, out, slot = args.page, args.out, args.slot
    toml = tomllib.loads((page / "paper.toml").read_text())
    links = json.loads((page / "links.json").read_text())
    pdf_only = not toml["paper"].get("markdown") and not (page / "paper.md").is_file()
    if pdf_only:
        # A PDF with no reading copy (a standard): the reader shows the PDF itself, and this index of
        # the passages Proof Reader quotes from it, in the PDF's order and under its section numbers,
        # carries the phrases, cards and search. It is never shown as the document's text.
        md = pdf_index(toml["paper"]["title"], links["passages"])
    else:
        md = (page / toml["paper"].get("markdown", "paper.md")).read_text()
    report = {k: [] for k in ("quote_not_unique", "lean_not_in_index", "verdict_without_note",
                              "statement_without_lean", "merged", "merged_assessments_differ", "unassessed",
                              "result_label_not_found", "result_without_statement", "long_title_without_override")}
    # Re-import: the old ties in reading order and the old aliases, so no address that worked stops working.
    old_order, old_aliases, old_retired = [], {}, {}
    if args.reimport:
        old_phrases = out / f"alignment/phrases-{slot}.json"
        if not old_phrases.is_file():
            raise SystemExit(f"--reimport needs an existing instance: {old_phrases} is missing")
        old_order = [t["id"] for t in json.loads(old_phrases.read_text())["ties"]]
        if (out / "alignment/aliases.json").is_file():
            old_table = json.loads((out / "alignment/aliases.json").read_text())
            old_aliases, old_retired = old_table.get("passages", {}), old_table.get("retired", {})
    # Pages that moved keep their addresses across conversions (instance.json moved_pages, kept as it was).
    moved_pages = (json.loads((out / "instance.json").read_text()).get("moved_pages")
                   if (out / "instance.json").is_file() else None)
    if out.exists():
        for child in ("papers", "alignment", "upstream", "generated", "evidence-graph.json", "instance.json"):
            target = out / child
            shutil.rmtree(target) if target.is_dir() else target.unlink(missing_ok=True)
    out.mkdir(parents=True, exist_ok=True)

    # ---- Lean: vendor the project's sources unchanged and index them.
    project = (page / toml["lean"]["project"]).resolve() if not args.lean_index else None
    lean_out = out / "upstream/lean"
    locked = []
    for path in (sorted(project.rglob("*")) if project else []):
        rel = path.relative_to(project)
        if path.is_file() and (path.suffix == ".lean" or rel.name in {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}) \
                and ".lake" not in rel.parts:
            data = path.read_bytes()
            write(lean_out / rel, data)
            locked.append({"path": f"upstream/lean/{rel}", "sha256": sha(data), "bytes": len(data)})
    src = toml["lean"].get("source", "")
    m = re.match(r"https://github.com/([^/]+/[^/]+)/tree/([0-9a-f]{40})", src)
    upstream_repo, upstream_rev = (f"https://github.com/{m.group(1)}", m.group(2)) if m else (src, "")
    # A source that is not a pinned git tree (an archive DOI) is its own revision.
    revision = upstream_rev or src
    write(out / "upstream/source-lock.json", dumps({
        "schema_version": "1.0", "id": args.paper, "repository": upstream_repo, "revision": revision,
        "via": f"wcook04/proof-reader {args.source_commit}, papers/{page.name}/{toml['lean']['project']}",
        "license": "NOASSERTION", "files": locked,
        # The modules the page reads: their top-level directories, and top-level module files such as Solution.
        **({"lean_roots": sorted({m.split(".")[0] for m in toml["lean"]["modules"]})} if toml["lean"].get("modules") else {})}))
    if args.lean_index:
        # A companion reads its paper's Lean: the index names the files, and their locked hashes come
        # from the paper's own source lock beside it.
        shared = json.loads(args.lean_index.read_text())
        lean = Lean(shared)
        lock = json.loads(args.lean_lock.read_text()) if args.lean_lock else {"files": []}
        locked = lock["files"]
    else:
        index_path = out / "generated/lean-index.json"
        index_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([args.lean_exposition, "lean-index", str(lean_out), "--out", str(index_path)], check=True,
                       stdout=subprocess.DEVNULL)
        lean = Lean(json.loads(index_path.read_text()))
        index_path.unlink()  # the site builds its own index from upstream/lean
    # Lean's own dependencies, from Proof Reader's report of the compiled modules: what each
    # declaration's type uses, what its value uses (recorded for definitions) and its axioms.
    facts = {}
    for report_name in ("generated/lean.json.gz", "generated/lean.json"):
        report_path = page / report_name
        if report_path.is_file():
            raw = gzip.open(report_path).read() if report_name.endswith(".gz") else report_path.read_bytes()
            for row in json.loads(raw)["declarations"]:
                found = lean.resolve(row["name"])
                if not found:
                    continue
                keep = lambda names: sorted({r[0] for n in names if (r := lean.resolve(n))})
                facts[found[0]] = {"s": keep(row.get("type_dependencies", [])), "v": keep(row.get("value_dependencies", [])),
                                   "axioms": row.get("axioms")}
            break
    write(out / "generated/lean-facts.json", json.dumps({"schema": 1, "source": f"wcook04/proof-reader {args.source_commit[:12]} papers/{page.name}",
                                                        "facts": dict(sorted(facts.items()))}, ensure_ascii=False, separators=(",", ":")))
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    if args.lean_index:
        uses_of = {d["name"]: d.get("uses", []) for m in shared["modules"] for d in m["declarations"]}
    else:
        from enrich_lean_index import enrich
        enriched = enrich(lean_out, facts)
        uses_of = {d["name"]: d["uses"] for m in enriched["modules"] for d in m["declarations"]}

    # ---- the reading copy
    # Links between the pages: Proof Reader's [reading.companions] names each page another file stands for.
    pr_companions = toml.get("reading", {}).get("companions", {})
    page_md = {page.name: md}
    for spec in args.companion:
        for cp in spec.split("=", 1)[1].split("|")[0].split("+"):
            cp = Path(cp)
            page_md[cp.name] = (cp / tomllib.loads((cp / "paper.toml").read_text())["paper"].get("markdown", "paper.md")).read_text()
    slugs_of = {name: section_slugs(text_) for name, text_ in page_md.items()}
    base_url = toml["paper"].get("url", "") if "/blob/" in toml["paper"].get("url", "") else ""

    def relinked(source_md: str, page_name: str, own_companions: dict, own_base: str) -> str:
        targets = {path: slugs_of.get(name, {}) for path, name in own_companions.items()}
        return relink(source_md, slugs_of.get(page_name) or section_slugs(source_md), targets, own_base)

    def relink_quotes(passages, page_name, own_companions, own_base):
        for p in passages:
            p["quote"] = relinked(p["quote"], page_name, own_companions, own_base)

    md = relinked(md, page.name, pr_companions, base_url)
    relink_quotes(links["passages"], page.name, pr_companions, base_url)
    text, sections, section_anchors = reading_copy(md, links["passages"])
    paper_dir = out / "papers" / slot
    write(paper_dir / "paper.md", text)
    if (page / "figures").is_dir():
        for fig in sorted((page / "figures").iterdir()):
            write(paper_dir / "figures" / fig.name, fig.read_bytes())

    pdf = None
    if args.pdf:
        data = args.pdf.read_bytes()
        write(paper_dir / "paper.pdf", data)
        pdf = {"file": "paper.pdf", "sha256": sha(data), "bytes": len(data), "url": toml["paper"].get("url", "")}

    # ---- phrase ties, titles and notes
    held = None
    if args.hold_comparisons:
        held = links.get("fidelity_held") if isinstance(links.get("fidelity_held"), str) else None
        held = held or "The comparisons for this paper are held until the authors have seen them."
        for p in links["passages"]:
            p["comparisons"] = [{"lean": n, "fidelity": "held", "note": held} for n in p["lean"]]
        links["fidelity"] = {}
    ties, aliases = phrase_rows(text, links["passages"], lean, links, report)
    retired = {}
    if args.reimport:
        aliases, retired = keep_addresses(old_order, old_aliases, aliases, [t["id"] for t in ties], report,
                                          args.retired_on, old_retired)
    # A tie the source replaced by other phrases keeps its address: it opens the first of them. This is
    # the source's own relocation, so it is an alias, not a retirement.
    for old_id, new_id in links.get("redirects", {}).items():
        aliases.setdefault(old_id, aliases.get(new_id, new_id))
        retired.pop(old_id, None)
    overrides = json.loads(args.titles.read_text())["titles"] if args.titles else {}
    result_titles = json.loads(args.titles.read_text()).get("results", {}) if args.titles else {}
    named = sorted({row["name"] for t in ties for row in t["lean"]})
    back = {}
    for name in links["plain"]:
        found = lean.resolve(name)
        if found:
            back.setdefault(found[0], name)
    titles, notes = {}, {}
    for target in named:
        source = back.get(target, target)
        title = overrides.get(source) or links["plain"].get(source, "")
        if not 2 <= words(title) <= 6:
            report["long_title_without_override"].append(source)
            if not args.partial:
                continue
        else:
            titles[target] = title
        note = links["notes"].get(source, {})
        notes[target] = note.get("text", "").strip() or note.get("summary", "").strip()
    topic_order = [t["id"] for t in links["topics"]]
    first_line, last_line = 1, text.count("\n") + 1
    phrases = {
        "schema": "phrase-ties/1", "paper": slot,
        "meaning": ("Each tie names the phrase of the paper that a Lean declaration states, as read side by side for "
                    f"Proof Reader (wcook04/proof-reader {args.source_commit[:12]}, papers/{page.name}). Titles, reading "
                    "notes, topics and comparisons are AI-drafted or AI-assessed; no mathematician has reviewed them."),
        "families": links.get("families", []),
        **({"main_result": links["main_result"]} if isinstance(links.get("main_result"), str) else {}),
        "topic_order": topic_order,
        "parts": [{"name": "", "lines": [first_line, last_line], "source_commit": args.source_commit,
                   "topics": [{"id": t["id"], "name": t["name"], "description": t.get("description", ""),
                               "family": t.get("family")} for t in links["topics"]],
                   "titles": titles, "notes": {k: v for k, v in notes.items() if v},
                   **({"partial": True} if args.partial else {})}],
        "ties": ties,
        "removed": [],
    }
    write(out / f"alignment/phrases-{slot}.json", dumps(phrases))
    plain = {}
    for name, title in links["plain"].items():
        found = lean.resolve(name)
        title = overrides.get(name, title)
        if found and 2 <= words(title) <= 6:
            plain.setdefault(found[0], title)
    write(out / "alignment/names.json", dumps({"schema": 1, "names": dict(sorted(plain.items()))}))
    for s in SLOTS:
        write(out / f"alignment/references-{s}.json",
              dumps(references(text if s == slot else EMPTY, s)))

    # ---- numbered results and the graph
    tie_of = {}
    for t in ties:
        tie_of[t["id"]] = t["id"]
        for old in t.get("replaces", []):
            tie_of[old] = t["id"]
    relabel = json.loads(args.paper_logic.read_text()).get("labels", {}) if args.paper_logic else {}
    results, claims = {}, []
    quote_of = {p["id"]: p["quote"] for p in links["passages"]}
    for c in links.get("claims", []):
        # A result Proof Reader titles in words keeps the number the paper prints for it, when it prints one.
        if not slug_of(c["title"]):
            label = printed_label(c, quote_of.get(c.get("passage"), ""), text)
            if label:
                c = dict(c, title=label, name=c["title"])
        address = address_of(c)
        if address in results:
            continue
        # The paper's stated logic may name a result by its role ("Corollary 7.2: how the profile is obtained").
        if address in relabel:
            c = dict(c, title=relabel[address])
        results[address] = {"claim": c["id"], "title": c["title"], "section": c.get("section"),
                            "tie": tie_of.get(c.get("passage")), "lean": c.get("lean", [])}
        claims.append((address, c))
    write(out / "alignment/results.json", dumps({"schema": 1, "results": results, "sections": section_anchors}))
    # Each numbered result's canonical target, its statement block: from the authors' bold label to the
    # end of that paragraph. The claim's own phrase in the source can be an introduction or a mention
    # before the result, so it is used only where the paper prints no label.
    batch, blocks = {}, {}
    for address, c in claims:
        tie = next((t for t in ties if t["id"] == tie_of.get(c.get("passage"))), None)
        at = text.find(tie["from"]) if tie else -1
        marker = text.find(f'<a id="{c.get("section")}"></a>') if c.get("section") else -1
        try:
            begin, stop, labelled = statement_block(text, c["title"], marker if marker >= 0 else None,
                                                    (at, at + len(tie["from"])) if tie else None)
        except ValueError:
            report["result_without_statement"].append(address)
            continue
        if not labelled:
            report["result_label_not_found"].append(address)
        blocks[address] = (begin, stop)
        # The slice is located by its first and last words: each found once, and never cutting a formula.
        spans = _math_spans(text[begin:stop])

        def whole(cut_a, cut_b):
            for x, y, _ in spans:
                if x < cut_a - begin < y:
                    cut_a = begin + y
                if x < cut_b - begin < y:
                    cut_b = begin + x
            return min(cut_a, stop), max(begin, cut_b)

        grow = 0
        while True:
            a, b = whole(begin + min(80 + grow, stop - begin), stop - min(60 + grow, stop - begin))
            first, last = text[begin:a], text[b:stop]
            if (text.count(first) == 1 and text.find(last, begin) + len(last) == stop) or a >= stop:
                break
            grow += 20
        rows = []
        for name in c.get("lean", []):
            found = lean.resolve(name)
            if not found:
                continue
            # Assessed, held or unassessed: a missing verdict is never read as "same".
            if held is not None:
                row = {"file": found[1], "name": found[0], "relation": "states", "fidelity": "held",
                       "fidelity_note": held, "fidelity_source": "ai"}
                rows.append(row)
                continue
            verdict = links.get("fidelity", {}).get(name)
            if not verdict or not verdict.get("verdict"):
                report["unassessed"].append([address, found[0]])
                rows.append({"file": found[1], "name": found[0], "relation": "states", "fidelity": UNASSESSED})
                continue
            row = {"file": found[1], "name": found[0], "relation": "states",
                   "fidelity": verdict["verdict"], "fidelity_source": "ai"}
            if (verdict.get("text") or "").strip():
                row["fidelity_note"] = verdict["text"].strip()
            elif row["fidelity"] != "same":
                row["fidelity_note"] = "The source records this verdict without a note."
            rows.append(row)
        # A result titled in words longer than six takes its authored short title (--titles "results").
        short = result_titles.get(c["id"]) or (c["title"] if words(c["title"]) <= 6 else c["title"].split(":")[0].strip())
        if words(short) > 6:
            raise SystemExit(f"result {address} ({c['id']}): its title has {words(short)} words; give a short one in --titles under \"results\"")
        batch[f"{args.paper}.{address}"] = {slot: short, "lean": rows,
                                             "statements": [{"paper": slot, "role": "statement", "from": first, "to": last,
                                                             "origin": "ai"}]}
    write(out / "alignment/m1-results.json", dumps({
        "schema_version": "1.0", "provenance": "Generated by scripts/from_proof_reader.py from Proof Reader's claims and fidelity",
        "records": dict(sorted(batch.items()))}))
    write(out / "alignment/aliases.json", dumps({"schema": 1, "passages": aliases,
                                                 **({"retired": retired} if retired else {}),
                                                 "claims": {c["id"]: a for a, c in claims}}))

    paper_md = text.encode("utf-8")
    title = toml["paper"]["title"]
    authors = args.authors or toml["paper"].get("authors", [])
    sources, citations, nodes, edges, evidence = {}, {}, {}, [], {}

    def node(nid, kind, label, status, **extra):
        nodes[nid] = {"id": nid, "kind": kind, "label": label, "status": status,
                      "assumption_ids": [], "evidence_ids": [], "citation_ids": [], **extra}

    sources["paper"] = {"id": "paper", "kind": "file", "url": toml["paper"].get("url", upstream_repo),
                        "revision": upstream_rev or args.source_commit, "license": "NOASSERTION",
                        "redistribution": "reference_only", "sha256": sha(paper_md)}
    sources["upstream"] = {"id": "upstream", "kind": "repository", "url": upstream_repo, "revision": revision,
                           "license": "NOASSERTION", "redistribution": "reference_only"}
    sources["proof_reader"] = {"id": "proof_reader", "kind": "repository", "url": "https://github.com/wcook04/proof-reader",
                               "revision": args.source_commit, "license": "MIT", "redistribution": "reference_only"}
    locked_by_path = {row["path"]: row for row in locked}
    goal = f"{args.paper}.{args.goal}"
    for address, c in claims:
        nid = f"{args.paper}.{address}"
        cid = f"cite.{nid}"
        citations[cid] = {"id": cid, "title": f"{title}, {c['title']}", "url": sources["paper"]["url"],
                          "source_id": "paper", "locator": f"{c['title']}, Section {c.get('section')}"}
        tie = next((t for t in ties if t["id"] == tie_of.get(c.get("passage"))), None)
        # The map shows the result's own statement block, the same canonical target the reader opens.
        statement = text[blocks[address][0]:blocks[address][1]] if address in blocks else (tie["from"] if tie else c["title"])
        node(nid, "goal" if nid == goal else "claim", c["title"], "unverified", source_id="paper",
             locator=f"{c['title']}, Section {c.get('section')}", statement=statement, citation_ids=[cid],
             boundary="A result as the authors number it. Its links to the Lean were made with AI for Proof Reader "
                      "and have not been reviewed by the authors.")
        decls = []
        for name in c.get("lean", []):
            found = lean.resolve(name)
            if not found:
                report["lean_not_in_index"].append(name)
                continue
            target, path, d = found
            did = "lean." + target
            if did not in nodes:
                lp = f"upstream/lean/{path}"
                sid = "lean:" + path
                sources[sid] = {"id": sid, "kind": "file", "url": f"{upstream_repo}/blob/{upstream_rev}/lean/{path}",
                                "revision": revision, "license": "NOASSERTION", "redistribution": "vendored",
                                "sha256": locked_by_path[lp]["sha256"], "path": lp}
                dcid = f"cite.{did}"
                citations[dcid] = {"id": dcid, "title": target, "url": f"{upstream_repo}/blob/{upstream_rev}/lean/{path}#L{d['line']}",
                                   "source_id": sid, "locator": f"{path}, line {d['line']}"}
                node(did, "declaration", target, "unverified", source_id=sid, declaration=target,
                     statement=titles.get(target, target), locator=f"{path}, line {d['line']}", citation_ids=[dcid],
                     boundary="Status unverified in this edition: no build or extraction receipt of this tool binds it.")
            decls.append(did)
        if decls:
            eid = f"link.{nid}"
            evidence[eid] = {"id": eid, "kind": "semantic_review", "status": "not_run", "command": [],
                             "tool": f"Links made with AI for Proof Reader; carried by scripts/from_proof_reader.py",
                             "source_ids": ["proof_reader"], "subject_ids": sorted({nid, *decls}),
                             "details": (f"Proof Reader's links.json at {args.source_commit[:12]} names these Lean declarations for "
                                         f"{c['title']}. The links were made with AI and have not been reviewed by the authors.")}
            nodes[nid]["evidence_ids"].append(eid)
            for d in dict.fromkeys(decls):
                edges.append({"from": nid, "to": d, "kind": "formalizes", "evidence_ids": [eid]})
    # The Lean of the main result's own phrase belongs to it too (Theorem 1.1's tie names theorem11).
    # Then join the declarations on the map by Lean's dependencies: A to B when A uses B directly or
    # through declarations that are not on the map.
    def add_decl(target, path, d):
        did = "lean." + target
        if did in nodes:
            return did
        lp, sid = f"upstream/lean/{path}", "lean:" + path
        sources[sid] = {"id": sid, "kind": "file", "url": f"{upstream_repo}/blob/{upstream_rev}/lean/{path}", "revision": revision,
                        "license": "NOASSERTION", "redistribution": "vendored", "sha256": locked_by_path[lp]["sha256"], "path": lp}
        dcid = f"cite.{did}"
        citations[dcid] = {"id": dcid, "title": target, "url": f"{upstream_repo}/blob/{upstream_rev}/lean/{path}#L{d['line']}",
                           "source_id": sid, "locator": f"{path}, line {d['line']}"}
        node(did, "declaration", target, "unverified", source_id=sid, declaration=target, statement=titles.get(target, target),
             locator=f"{path}, line {d['line']}", citation_ids=[dcid],
             boundary="Status unverified in this edition: no build or extraction receipt of this tool binds it.")
        return did
    for address, c in claims:
        nid = f"{args.paper}.{address}"
        tie = next((t for t in ties if t["id"] == tie_of.get(c.get("passage"))), None)
        extra = [row["name"] for row in (tie["lean"] if tie else []) if row["relation"] == "states"]
        for target in extra:
            found = lean.resolve(target)
            if not found:
                continue
            did = add_decl(*found)
            if not any(e["from"] == nid and e["to"] == did for e in edges):
                eid = f"link.{nid}"
                if eid not in evidence:
                    evidence[eid] = {"id": eid, "kind": "semantic_review", "status": "not_run", "command": [],
                                     "tool": "Links made with AI for Proof Reader; carried by scripts/from_proof_reader.py",
                                     "source_ids": ["proof_reader"], "subject_ids": [nid],
                                     "details": f"Proof Reader's phrase for {c['title']} names this Lean. Made with AI; not reviewed by the authors."}
                    nodes[nid]["evidence_ids"].append(eid)
                evidence[eid]["subject_ids"] = sorted(set(evidence[eid]["subject_ids"]) | {nid, did})
                edges.append({"from": nid, "to": did, "kind": "formalizes", "evidence_ids": [eid]})
    # The paper's own stated logic: edges the authors' text states between results ("If there exists a
    # certificate, then the conclusions of Theorem 1.1 hold"), sourced to the paper, beside Lean's.
    if args.paper_logic:
        logic = json.loads(args.paper_logic.read_text())
        for extra_node in logic.get("nodes", []):
            nid = f"{args.paper}.{extra_node['id']}"
            tie = next((t for t in ties if t["id"] == tie_of.get(extra_node["tie"], extra_node["tie"])), None)
            node(nid, "claim", extra_node["label"], "unverified", source_id="paper", locator=extra_node["locator"],
                 statement=tie["from"] if tie else extra_node["label"], citation_ids=[],
                 boundary="A result the paper states without a number. Its link to the Lean was made with AI and has not "
                          "been reviewed by the authors.")
            for target in extra_node.get("lean", []):
                found = lean.resolve(target)
                if not found:
                    raise SystemExit(f"--paper-logic: {target} is not in the Lean index")
                did = add_decl(*found)
                eid = f"link.{nid}"
                evidence.setdefault(eid, {"id": eid, "kind": "semantic_review", "status": "not_run", "command": [],
                                          "tool": "Links made with AI; carried by scripts/from_proof_reader.py",
                                          "source_ids": ["proof_reader"], "subject_ids": [nid],
                                          "details": f"The phrase {extra_node['tie']} names this Lean. Made with AI; not reviewed by the authors."})
                if eid not in nodes[nid]["evidence_ids"]:
                    nodes[nid]["evidence_ids"].append(eid)
                evidence[eid]["subject_ids"] = sorted(set(evidence[eid]["subject_ids"]) | {nid, did})
                edges.append({"from": nid, "to": did, "kind": "formalizes", "evidence_ids": [eid]})
        for address, label in logic.get("labels", {}).items():
            nodes[f"{args.paper}.{address}"]["label"] = label
        # Each edge carries its own evidence (paper_logic.<from>.<to>): the sentence that states it.
        for e in logic.get("edges", []):
            a, b = f"{args.paper}.{e['from']}", f"{args.paper}.{e['to']}"
            if a not in nodes or b not in nodes:
                raise SystemExit(f"--paper-logic: {e['from']} or {e['to']} is not a result on the map")
            eid = f"paper_logic.{e['from']}.{e['to']}"
            evidence[eid] = {"id": eid, "kind": "semantic_review", "status": "not_run", "command": [],
                             "tool": "The paper's own statement of how its results join; transcribed with AI",
                             "source_ids": ["paper"], "subject_ids": sorted({a, b}), "details": e["why"]}
            same = next((x for x in edges if x["from"] == a and x["to"] == b and x["kind"] == "supports"), None)
            if same:
                same["evidence_ids"] = sorted(set(same["evidence_ids"]) | {eid})
            else:
                edges.append({"from": a, "to": b, "kind": "supports", "evidence_ids": [eid]})
    # A document that numbers no results (a standard): its root is the document itself, linked to the
    # Lean each passage defines or states, so the map has a top and every declaration a place on it.
    if args.goal == "document" and goal not in nodes:
        node(goal, "goal", title, "unverified", source_id="paper", locator=title,
             statement=f"{title}: the document as a whole. It numbers no results; each passage links the Lean that states it.",
             citation_ids=[], boundary="The document itself, as the map's root. Its links to the Lean were made with AI and have not been reviewed by the authors.")
        eid = f"link.{goal}"
        evidence[eid] = {"id": eid, "kind": "semantic_review", "status": "not_run", "command": [],
                         "tool": "Links made with AI for Proof Reader; carried by scripts/from_proof_reader.py",
                         "source_ids": ["proof_reader"], "subject_ids": [goal],
                         "details": "The Lean the document's passages define or state, as Proof Reader links them. Made with AI; not reviewed by the authors."}
        nodes[goal]["evidence_ids"].append(eid)
        for t in ties:
            for row in t["lean"]:
                if row["relation"] in ("states", "defines") and (found := lean.resolve(row["name"])):
                    did = add_decl(*found)
                    if not any(e["from"] == goal and e["to"] == did for e in edges):
                        edges.append({"from": goal, "to": did, "kind": "formalizes", "evidence_ids": [eid]})
                        evidence[eid]["subject_ids"] = sorted(set(evidence[eid]["subject_ids"]) | {did})
    on_map = {n[len("lean."):] for n in nodes if n.startswith("lean.")}
    if facts and on_map:
        evidence["lean_dependencies"] = {
            # The graph contract reserves lean_*_dependency edges for this tool's own extraction receipts;
            # these come from another repository's run, so they are recorded as supports edges with
            # their source named, and no assurance is claimed for them here.
            "id": "lean_dependencies", "kind": "semantic_review", "status": "not_run", "command": [],
            "tool": "Lean's report of the authors' compiled modules, made on GitHub Actions for Proof Reader; outside observation",
            "source_ids": ["proof_reader", "upstream"], "subject_ids": sorted("lean." + n for n in on_map),
            "details": ("Each edge joins two declarations on the map when the first uses the second directly or through "
                        "declarations not drawn here: type dependencies from Lean's report, proof dependencies from the report "
                        "where recorded and otherwise from the proof's text.")}
        for start in sorted(on_map):
            seen, frontier, reach = {start}, list(uses_of.get(start, [])), set()
            while frontier:
                name = frontier.pop()
                if name in seen:
                    continue
                seen.add(name)
                if name in on_map:
                    reach.add(name)
                    continue
                frontier.extend(uses_of.get(name, []))
            for target in sorted(reach):
                edges.append({"from": "lean." + start, "to": "lean." + target, "kind": "supports",
                              "evidence_ids": ["lean_dependencies"]})
    # The paper's own chain: a numbered result uses another when the Lean of the first uses the Lean of
    # the second, directly or through declarations that state no numbered result.
    if facts:
        owners = {}
        for e in edges:
            if e["kind"] == "formalizes":
                owners.setdefault(e["to"][len("lean."):], set()).add(e["from"])
        result_uses = {}
        for address, c in claims:
            nid = f"{args.paper}.{address}"
            starts = [e["to"][len("lean."):] for e in edges if e["from"] == nid and e["kind"] == "formalizes"]
            seen, frontier, used = set(starts), [u for s_ in starts for u in uses_of.get(s_, [])], set()
            while frontier:
                name = frontier.pop()
                if name in seen:
                    continue
                seen.add(name)
                others = owners.get(name, set()) - {nid}
                if others:
                    used |= others
                    continue
                frontier.extend(uses_of.get(name, []))
            result_uses[nid] = used
        # Results that share Lean reach each other both ways; the map needs a direction. Within a
        # cycle a result uses only results printed before it, so the main result and the results it
        # rests on stay joined and no edge points back.
        order = {f"{args.paper}.{address}": k for k, (address, _) in enumerate(claims)}
        reach = {}
        def reaches(a, b):
            seen, stack = set(), [a]
            while stack:
                x = stack.pop()
                if x == b:
                    return True
                if x in seen:
                    continue
                seen.add(x)
                stack.extend(result_uses.get(x, ()))
            return False
        for nid, used in sorted(result_uses.items()):
            for other in sorted(used):
                if reaches(other, nid) and order.get(nid, 0) < order.get(other, 0):
                    continue
                same = next((x for x in edges if x["from"] == nid and x["to"] == other and x["kind"] == "supports"), None)
                if same:
                    same["evidence_ids"] = sorted(set(same["evidence_ids"]) | {"lean_dependencies"})
                    continue
                edges.append({"from": nid, "to": other, "kind": "supports", "evidence_ids": ["lean_dependencies"]})
                evidence["lean_dependencies"]["subject_ids"] = sorted(set(evidence["lean_dependencies"]["subject_ids"]) | {nid, other})
    if goal not in nodes:
        raise SystemExit(f"the goal {args.goal} is not a numbered result of this page")
    graph = {
        "schema_version": "1.2", "id": f"{args.paper}-library-edition", "title": title,
        "selected_goals": [goal],
        "sources": [sources[k] for k in sorted(sources)],
        "citations": [citations[k] for k in sorted(citations)],
        "nodes": [nodes[k] for k in sorted(nodes)],
        "edges": sorted(edges, key=lambda e: (e["from"], e["to"], e["kind"])),
        "evidence": [evidence[k] for k in sorted(evidence)],
        "scope": (f"{title}, by {', '.join(authors)}, with their Lean at {upstream_repo} {upstream_rev}, as read for Proof Reader "
                  f"(wcook04/proof-reader {args.source_commit}). The numbered results are the authors'; their links to the Lean "
                  "were made with AI."),
        "extraction_status": "not_run",
        "notes": ["Converted by scripts/from_proof_reader.py. Every record is unverified: this edition ran no Lean build or "
                  "extraction. The phrase ties, titles, notes and comparisons are AI-drafted or AI-assessed."],
    }
    graph_bytes = dumps(graph).encode("utf-8")
    write(out / "evidence-graph.json", graph_bytes)

    # ---- paper mappings
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
    from lean_exposition.contracts import closure, required_citation_ids
    claim_at = {f"{args.paper}.{address}": blocks[address][0] for address, _ in claims if address in blocks}

    def mapping(s, content, passages):
        claim_ids = list(dict.fromkeys([goal] + [c for p in passages for c in p["claim_ids"]]))
        required = closure(graph, claim_ids)
        return {"schema_version": "1.2", "stage": s, "state": "draft" if passages else "scaffold",
                "path": f"papers/{s}.md", "content_sha256": sha(content), "graph_sha256": sha(graph_bytes),
                "selected_goal_ids": [goal], "claim_ids": claim_ids if passages else [],
                "citation_ids": sorted(required_citation_ids(graph, claim_ids) | {c for p in passages for c in p["citation_ids"]}),
                "assumption_ids": [],
                "unresolved_ids": sorted(n for n in required if nodes[n]["status"] in {"open", "unverified", "external", "conditional"}),
                "passages": passages, "review_state": "not_reviewed",
                "review_notes": [] if not passages else [
                    "Converted from Proof Reader; the links were made with AI and no mathematician has reviewed them.",
                    "Each passage is one section of the paper; its claim ids are the numbered results stated inside it."]}

    passages, cursor = [], 0
    for sec in sections:
        marker, end = f"<!-- passage:{sec['anchor']} -->", f"<!-- /passage:{sec['anchor']} -->"
        start = text.index(marker, cursor) + len(marker)
        stop = text.index(end, start)
        cursor = stop
        ids = [nid for nid, at in claim_at.items() if start <= at < stop]
        # A document that is its own root is stated by its opening passage.
        if not passages and goal.endswith(".document") and goal not in claim_at:
            ids = [goal]
        statuses = {nodes[i]["status"] for i in ids}
        passages.append({"anchor": sec["anchor"], "text_sha256": sha(text[start:stop].encode("utf-8")),
                         "claim_ids": ids, "citation_ids": sorted(required_citation_ids(graph, ids)) if ids else [],
                         "assumption_ids": [],
                         "evidence_class": "context" if not ids else ("open_question" if statuses == {"open"} else "source_argument"),
                         "rationale": f"{sec['heading']}: " + ("states or proves the listed results." if ids else "context with no numbered result.")})
    write(paper_dir / "correspondence.json", dumps(mapping(slot, paper_md, passages)))
    companion_docs = []
    # Companion documents: --companion fills one of the reader's three fixed slots; --companions-index
    # adds any number of documents, each in a slot of its own named by its page (digest, library-07),
    # grouped and ordered as the index says.
    specs = []
    for spec in args.companion:
        cslot, pages_spec = spec.split("=", 1)
        pages_spec, cslug, ctitle_given, cnoun = (pages_spec.split("|") + ["", "", ""])[:4]
        if cslot == slot or cslot not in SLOTS or cslot in {d["slot"] for d in companion_docs}:
            raise SystemExit(f"--companion {spec}: the slot must be a free one of {SLOTS}")
        specs.append((cslot, [Path(x) for x in pages_spec.split("+")], cslug, ctitle_given, {"noun": cnoun} if cnoun else {}))
    if args.companions_index:
        cindex = json.loads(args.companions_index.read_text())
        for d in sorted(cindex["documents"], key=lambda d: d["order"]):
            if d["library_page"] in SLOTS or not re.fullmatch(r"[a-z0-9][a-z0-9-]*", d["library_page"]):
                raise SystemExit(f"companion page {d['library_page']!r} is not a page name")
            specs.append((d["library_page"], [args.companions_index.parent / d["slug"]], d["library_page"], d["title"],
                          {"group": d["group"], "group_title": d["group_title"], "order": d["order"],
                           "credit": d.get("credit", ""), "authors": d.get("authors", []), "kind": "companion"}))
    for cslot, cpages, cslug, ctitle_given, cmeta in specs:
        if cslot in {d["slot"] for d in companion_docs}:
            raise SystemExit(f"companion slot {cslot} is used twice")
        ctomls = [tomllib.loads((cp / "paper.toml").read_text()) if (cp / "paper.toml").is_file()
                  else {"paper": {"title": ctitle_given or cp.name, "markdown": "document.md", "noun": "companion"}} for cp in cpages]
        clinks = [json.loads((cp / "links.json").read_text()) for cp in cpages]
        cmd = "\n\n".join(relinked((cp / t["paper"].get("markdown", "paper.md")).read_text(), cp.name,
                                     t.get("reading", {}).get("companions", {}), "").rstrip("\n")
                            for cp, t in zip(cpages, ctomls)) + "\n"
        for cp, t, cl in zip(cpages, ctomls, clinks):
            relink_quotes(cl["passages"], cp.name, t.get("reading", {}).get("companions", {}), "")
        cpassages = [x for cl in clinks for x in cl["passages"]]
        ctext, csections, _ = reading_copy(cmd, cpassages)
        cdir = out / "papers" / cslot
        write(cdir / "paper.md", ctext)
        for cp in cpages:
            if (cp / "figures").is_dir():
                for fig in sorted((cp / "figures").iterdir()):
                    write(cdir / "figures" / fig.name, fig.read_bytes())
        cplain = {k: v for cl in clinks for k, v in cl.get("plain", {}).items()}
        cnotes = {k: v for cl in clinks for k, v in cl.get("notes", {}).items()}
        merged_links = {"plain": cplain, "notes": cnotes}
        creport = {k: [] for k in report}
        cties, caliases = phrase_rows(ctext, cpassages, lean, merged_links, creport)
        aliases.update({k: v for k, v in caliases.items() if k not in aliases})
        cback = {}
        for name in cplain:
            found = lean.resolve(name)
            if found:
                cback.setdefault(found[0], name)
        ctitles, cnote_rows = {}, {}
        for target in sorted({row["name"] for t in cties for row in t["lean"]}):
            source = cback.get(target, target)
            ctitle = overrides.get(source) or cplain.get(source, "") or plain.get(target, "")
            if 2 <= words(ctitle) <= 6:
                ctitles[target] = ctitle
            elif not args.partial:
                creport["long_title_without_override"].append(source)
                continue
            note = cnotes.get(source, {})
            text_note = (note.get("text", "").strip() or note.get("summary", "").strip()) if isinstance(note, dict) else ""
            if text_note:
                cnote_rows[target] = text_note
            if 2 <= words(ctitle) <= 6:
                plain.setdefault(target, ctitle)
        ctopics = clinks[0].get("topics", links.get("topics", []))
        write(out / f"alignment/phrases-{cslot}.json", dumps({
            "schema": "phrase-ties/1", "paper": cslot,
            "meaning": phrases["meaning"].replace(f"papers/{page.name}", "papers/" + "+".join(cp.name for cp in cpages)),
            "families": clinks[0].get("families", links.get("families", [])),
            "topic_order": [t["id"] for t in ctopics],
            "parts": [{"name": "", "lines": [1, ctext.count("\n") + 1], "source_commit": args.source_commit,
                       "topics": [{"id": t["id"], "name": t["name"], "description": t.get("description", ""),
                                   "family": t.get("family")} for t in ctopics],
                       "titles": ctitles, "notes": cnote_rows, **({"partial": True} if args.partial else {})}],
            "ties": cties, "removed": []}))
        write(out / f"alignment/references-{cslot}.json", dumps(references(ctext, cslot)))
        cbytes = ctext.encode("utf-8")
        cps, cursor = [], 0
        for sec in csections:
            marker, end = f"<!-- passage:{sec['anchor']} -->", f"<!-- /passage:{sec['anchor']} -->"
            start = ctext.index(marker, cursor) + len(marker)
            stop = ctext.index(end, start)
            cursor = stop
            # A companion is an account of the whole paper: its first section carries the paper's goal.
            ids = [goal] if not cps else []
            cps.append({"anchor": sec["anchor"], "text_sha256": sha(ctext[start:stop].encode("utf-8")), "claim_ids": ids,
                        "citation_ids": sorted(required_citation_ids(graph, ids)) if ids else [], "assumption_ids": [],
                        "evidence_class": "context",
                        "rationale": f"{sec['heading']}: a companion account of the paper; its links to the Lean are its phrase ties."})
        write(cdir / "correspondence.json", dumps(mapping(cslot, cbytes, cps)))
        t0 = ctomls[0]["paper"]
        companion_docs.append({"id": "+".join(cp.name for cp in cpages), "slot": cslot,
                               "slug": cslug or (cpages[0].name.removeprefix(f"{page.name.split('-paper')[0]}-") if len(cpages) == 1 else "accounts"),
                               "title": ctitle_given or (t0["title"] if len(cpages) == 1 else " · ".join(t["paper"]["short_title"] for t in ctomls)),
                               "noun": t0.get("noun", "account"), **cmeta})
        summary_c = {k: (len(v) if isinstance(v, list) else v) for k, v in creport.items()}
        report.setdefault("companions", {})["+".join(cp.name for cp in cpages)] = {**summary_c, "ties": len(cties), "titled": len(ctitles), "noted": len(cnote_rows)}
    if specs:
        write(out / "alignment/names.json", dumps({"schema": 1, "names": dict(sorted(plain.items()))}))
        write(out / "alignment/aliases.json", dumps({"schema": 1, "passages": aliases,
                                                     "claims": {c["id"]: a for a, c in claims}}))
    used = {slot, *(d["slot"] for d in companion_docs)}
    for s in SLOTS:
        if s not in used:
            write(out / "papers" / s / "absent.md", EMPTY)
            write(out / "papers" / s / "absent.json", dumps(mapping(s, EMPTY.encode("utf-8"), [])))

    # ---- Comparator: the layout Proof Reader's paper.py reads (Challenge, Solution, config, receipt.json), carried unchanged
    comparator = None
    folder = toml.get("comparator", {}).get("evidence")
    folder = (page / folder) if folder else (page / "comparator")
    if folder.is_dir():
        files = {}
        for f in sorted(folder.rglob("*")):
            if f.is_file():
                rel = f.relative_to(folder).as_posix()
                files[rel] = write(out / "generated/comparator" / rel, f.read_bytes())
        receipt = json.loads((folder / "receipt.json").read_text()) if (folder / "receipt.json").is_file() else None
        comparator = {"files": files, "receipt": "receipt.json" if receipt else None}

    # ---- companion pages read as documents of their own, in the free document slots: the guide to how
    # the Lean encodes the paper (--guide) and the long "Start here" (--start-here).
    def companion(path, doc_id, slug, title, why):
        free = [x for x in ("expository", "long") if x != slot and x not in taken]
        if not free:
            raise SystemExit(f"no free document slot for {title}")
        gslot = free[0]
        taken.add(gslot)
        gtext, gsections, _ = reading_copy(path.read_text(), [])
        gbytes = gtext.encode("utf-8")
        write(out / "papers" / gslot / "paper.md", gtext)
        (out / "papers" / gslot / "absent.md").unlink(missing_ok=True)
        (out / "papers" / gslot / "absent.json").unlink(missing_ok=True)
        gpassages, cursor = [], 0
        for sec in gsections:
            marker, end = f"<!-- passage:{sec['anchor']} -->", f"<!-- /passage:{sec['anchor']} -->"
            begin = gtext.index(marker, cursor) + len(marker)
            stop = gtext.index(end, begin)
            cursor = stop
            gpassages.append({"anchor": sec["anchor"], "text_sha256": sha(gtext[begin:stop].encode("utf-8")), "claim_ids": [],
                              "citation_ids": [], "assumption_ids": [], "evidence_class": "context",
                              "rationale": f"{sec['heading']}: {why}"})
        # The page is about the main result; its opening section carries that result.
        if gpassages:
            gpassages[0].update(claim_ids=[goal], citation_ids=sorted(required_citation_ids(graph, [goal])),
                                evidence_class="source_argument")
        mapped = mapping(gslot, gbytes, gpassages)
        mapped["state"] = "draft"
        write(out / "papers" / gslot / "correspondence.json", dumps(mapped))
        write(out / f"alignment/references-{gslot}.json", dumps(references(gtext, gslot)))
        return {"id": doc_id, "slot": gslot, "slug": slug, "title": title, "noun": "guide"}

    taken = {d["slot"] for d in companion_docs}
    companions = []
    if args.guide:
        companions.append(companion(args.guide, "encoding", "how-the-lean-encodes-it", "How the Lean encodes it",
                                    "how the formalisation encodes the paper's objects."))
    if args.start_here:
        companions.append(companion(args.start_here, "start-here", "start-here", "Start here",
                                    "an orientation to the paper and its Lean."))
    guide = companions[0] if companions else None

    # ---- supplementary checks and the declarations no sentence names
    if (page / "generated/checks.json").is_file():
        write(out / "generated/checks.json", (page / "generated/checks.json").read_bytes())
        for f in sorted((page / "checks").glob("*.lean")) if (page / "checks").is_dir() else ():
            write(out / "generated/checks" / f.name, f.read_bytes())
    # Reading notes on every declaration Proof Reader wrote one for, by its name in the Lean index.
    lean_notes = {}
    for name, note in links.get("notes", {}).items():
        found = lean.resolve(name)
        if found and (note.get("text") or "").strip():
            lean_notes[found[0]] = {"text": note["text"].strip(), **({"summary": note["summary"]} if note.get("summary") else {})}
    write(out / "generated/lean-notes.json", json.dumps({"schema": 1, "notes": dict(sorted(lean_notes.items()))},
                                                        ensure_ascii=False, separators=(",", ":")))
    # Why a paragraph has no phrase, or which phrases link it (Proof Reader's paragraph dispositions),
    # kept with the instance until the reader shows them.
    # Optional reading aids the reader does not draw yet: the paper's glossary of conventions, section
    # aids and showcase cards. Carried unchanged so a later design pass can render them.
    for aid in ("glossary.json", "section-aids.json", "showcase.json", "route.json", "start-here-summary.md",
                "start-here.md", "differences-summary.md", "ours.json"):
        if (page / "notes" / aid).is_file():
            write(out / "generated" / aid, (page / "notes" / aid).read_bytes())
    if (page / "notes/paragraph-dispositions.json").is_file():
        write(out / "generated/paragraph-dispositions.json", (page / "notes/paragraph-dispositions.json").read_bytes())
    unnamed = sorted({r[0] for n in links.get("show_also", []) if (r := lean.resolve(n))})
    write(out / "generated/unnamed.json", dumps({"schema": 1, "names": unnamed}))

    # ---- the instance
    credit = args.credit or toml.get("credit", {}).get("text", "")
    instance = {
        "schema": "library-instance/1", "id": args.paper, **({"path": args.path} if args.path else {}), "title": title,
        "short_title": toml["paper"].get("short_title", title), "authors": authors,
        "venue": toml["paper"].get("venue", ""),
        "credit_lines": [credit] if credit else [],
        # Companion pages credit the authors and their repository only; the main paper's own
        # header and About carry the full credit line (credit_lines).
        "companion_credit": args.companion_credit or (f"Paper and Lean by {', '.join(authors[:-1]) + ' and ' + authors[-1] if len(authors) > 1 else ''.join(authors)}, "
                             f"from their repository {upstream_repo.replace('https://github.com/', '')} at {upstream_rev[:7]}."),
        **({"licence": toml["paper"]["licence"]} if toml["paper"].get("licence") else {}),
        "host": "Hosted by Will Cook in his reading library, with credit to the authors.",
        "review": ("The links from the text to the Lean, the plain titles, the reading notes and the comparisons were made "
                   "with AI and have not been reviewed by the authors. No mathematician has reviewed them."),
        "source": {"proof_reader": {"repository": "https://github.com/wcook04/proof-reader", "commit": args.source_commit,
                                    "page": page.name},
                   "upstream": {"repository": upstream_repo, "commit": upstream_rev, "paper": toml["paper"].get("url")},
                   "lean_scope": toml["lean"].get("scope", "")},
        "documents": [{"id": "paper", "slot": slot, "slug": "", "title": title, "noun": toml["paper"].get("noun", "paper"),
                       "main": True, **({"pdf": pdf} if pdf else {}), **({"pdf_only": True} if pdf_only else {})}, *companion_docs] + companions
                     + [{"id": "external:" + href, "href": href, "slug": "", "title": t, "noun": n or "page"}
                        for href, t, n in ((x.split("|") + ["", ""])[:3] for x in args.external)],
        **({"moved_pages": moved_pages} if moved_pages else {}),
        **({"comparator": comparator} if comparator else {}),
        **({"comparisons_hidden": True, "comparisons_held_text": held} if held else {}),
        "families": links.get("families", []),
        "topics": [{"id": t["id"], "name": t["name"], "description": t.get("description", ""), "family": t.get("family")}
                   for t in links["topics"]],
        "topic_order": topic_order,
        "goal": goal,
        # The main result's Lean: the first theorem its own phrase names (the graph's root for the reader).
        "main_lean": next((row["name"] for t in ties if t["id"] == tie_of.get(next((c.get("passage") for a, c in claims if f"{args.paper}.{a}" == goal), None))
                           for row in t["lean"] if (lean.resolve(row["name"]) or (None, None, {}))[2].get("kind") == "theorem"), None),
    }
    write(out / "instance.json", dumps(instance))
    summary = {k: (len(v) if isinstance(v, list) else v) for k, v in report.items()}
    summary.update(ties=len(ties), titled=len(titles), names=len(plain), results=len(results), sections=len(section_anchors),
                   lean_files=len(locked), unnamed=len(unnamed))
    write(out / "generated/conversion-report.json", dumps({"summary": summary, **report}))
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
