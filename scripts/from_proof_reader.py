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


def section_number(heading: str) -> str | None:
    """`5.5.1 The equations at each level` -> `5.5.1`; `Appendix A ...` -> `appendix-a`."""
    m = re.match(r"^(\d+(?:\.\d+)*)\s", heading)
    if m:
        return m.group(1)
    m = re.match(r"^(?:Appendix\s+)?([A-Z])(?:\.(\d+(?:\.\d+)*))?\s", heading)
    if m and heading.startswith("Appendix"):
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


def phrase_rows(text: str, passages: list[dict], lean: Lean, links: dict, report: dict):
    """Every passage as a phrase tie. Identical or nested spans merge; the merged id is kept as an alias."""
    spans = []
    for p in passages:
        at = text.find(p["quote"])
        if at < 0 or text.find(p["quote"], at + 1) >= 0:
            report["quote_not_unique"].append(p["id"])
            continue
        spans.append([at, at + len(p["quote"]), p])
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
        rows, seen = [], set()
        for p in group:
            comparisons = {c["lean"]: c for c in p.get("comparisons", [])}
            for name in p["lean"]:
                found = lean.resolve(name)
                if not found:
                    report["lean_not_in_index"].append(name)
                    continue
                target, path, decl = found
                if target in seen:
                    continue
                seen.add(target)
                c = comparisons.get(name, {"fidelity": "same", "note": ""})
                row = {"name": target, "file": path, "relation": ROLE[p["role"]][1], "fidelity": c["fidelity"]}
                note = c.get("note", "").strip()
                if c["fidelity"] != "same" and not note:
                    note = "The source records this verdict without a note."
                    report["verdict_without_note"].append(p["id"])
                if note:
                    row["fidelity_note"] = note
                rows.append(row)
        body = text[start:stop]
        tie = {"id": first["id"], "from": body, "to": body, "role": role, "topic": first["topic"],
               "status": "new", "lean": rows}
        if role in {"statement", "definition"} and not rows:
            tie["role"] = "explanation"
            report["statement_without_lean"].append(first["id"])
        if len(group) > 1:
            tie["replaces"] = [p["id"] for p in group[1:]]
            report["merged"].append([p["id"] for p in group])
        ties.append(tie)
    return ties, aliases


def keep_addresses(old_order: list[str], old_aliases: dict, aliases: dict, new_ids: list[str], report: dict) -> dict:
    """Every old tie id stays an address: a tie that is gone points at its nearest surviving neighbour
    in the old reading order (the one before it, else the one after), and old aliases follow."""
    alive = set(new_ids)
    out = dict(aliases)
    gone = [i for i in old_order if i not in alive]
    for k, old in enumerate(old_order):
        if old in alive:
            continue
        before = next((old_order[j] for j in range(k - 1, -1, -1) if old_order[j] in alive), None)
        after = next((old_order[j] for j in range(k + 1, len(old_order)) if old_order[j] in alive), None)
        target = before or after or (new_ids[0] if new_ids else None)
        if target:
            out[old] = target
    for old, host in old_aliases.items():
        while host in out and host not in alive and out[host] != host:
            host = out[host]
        if old not in alive and host in alive:
            out.setdefault(old, host)
    report["gone_kept_as_addresses"] = gone
    return out


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
    ap.add_argument("--guide", type=Path, help="a Markdown guide to how the Lean encodes the paper's objects, read as a page of its own")
    ap.add_argument("--lean-exposition", default="lean-exposition", help="the lean-exposition command")
    args = ap.parse_args()
    page, out, slot = args.page, args.out, args.slot
    toml = tomllib.loads((page / "paper.toml").read_text())
    links = json.loads((page / "links.json").read_text())
    md = (page / toml["paper"].get("markdown", "paper.md")).read_text()
    report = {k: [] for k in ("quote_not_unique", "lean_not_in_index", "verdict_without_note",
                              "statement_without_lean", "merged", "long_title_without_override")}
    # Re-import: the old ties in reading order and the old aliases, so no address that worked stops working.
    old_order, old_aliases = [], {}
    if args.reimport:
        old_phrases = out / f"alignment/phrases-{slot}.json"
        if not old_phrases.is_file():
            raise SystemExit(f"--reimport needs an existing instance: {old_phrases} is missing")
        old_order = [t["id"] for t in json.loads(old_phrases.read_text())["ties"]]
        if (out / "alignment/aliases.json").is_file():
            old_aliases = json.loads((out / "alignment/aliases.json").read_text()).get("passages", {})
    if out.exists():
        for child in ("papers", "alignment", "upstream", "generated", "evidence-graph.json", "instance.json"):
            target = out / child
            shutil.rmtree(target) if target.is_dir() else target.unlink(missing_ok=True)
    out.mkdir(parents=True, exist_ok=True)

    # ---- Lean: vendor the project's sources unchanged and index them.
    project = (page / toml["lean"]["project"]).resolve()
    lean_out = out / "upstream/lean"
    locked = []
    for path in sorted(project.rglob("*")):
        rel = path.relative_to(project)
        if path.is_file() and (path.suffix == ".lean" or rel.name in {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}) \
                and ".lake" not in rel.parts:
            data = path.read_bytes()
            write(lean_out / rel, data)
            locked.append({"path": f"upstream/lean/{rel}", "sha256": sha(data), "bytes": len(data)})
    src = toml["lean"].get("source", "")
    m = re.match(r"https://github.com/([^/]+/[^/]+)/tree/([0-9a-f]{40})", src)
    upstream_repo, upstream_rev = (f"https://github.com/{m.group(1)}", m.group(2)) if m else (src, "")
    write(out / "upstream/source-lock.json", dumps({
        "schema_version": "1.0", "id": args.paper, "repository": upstream_repo, "revision": upstream_rev,
        "via": f"wcook04/proof-reader {args.source_commit}, papers/{page.name}/{toml['lean']['project']}",
        "license": "NOASSERTION", "files": locked}))
    index_path = out / "generated/lean-index.json"
    index_path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([args.lean_exposition, "lean-index", str(lean_out), "--out", str(index_path)], check=True,
                   stdout=subprocess.DEVNULL)
    lean = Lean(json.loads(index_path.read_text()))
    index_path.unlink()  # the site builds its own index from upstream/lean

    # ---- the reading copy
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
    ties, aliases = phrase_rows(text, links["passages"], lean, links, report)
    if args.reimport:
        aliases = keep_addresses(old_order, old_aliases, aliases, [t["id"] for t in ties], report)
    overrides = json.loads(args.titles.read_text())["titles"] if args.titles else {}
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
            continue
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
        "topic_order": topic_order,
        "parts": [{"name": "", "lines": [first_line, last_line], "source_commit": args.source_commit,
                   "topics": [{"id": t["id"], "name": t["name"], "description": t.get("description", ""),
                               "family": t.get("family")} for t in links["topics"]],
                   "titles": titles, "notes": notes}],
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
    results, claims = {}, []
    for c in links.get("claims", []):
        address = slug_of(c["title"])
        if not address or address in results:
            continue
        results[address] = {"claim": c["id"], "title": c["title"], "section": c.get("section"),
                            "tie": tie_of.get(c.get("passage")), "lean": c.get("lean", [])}
        claims.append((address, c))
    write(out / "alignment/results.json", dumps({"schema": 1, "results": results, "sections": section_anchors}))
    # Each numbered result's statement as a record of the map: from its bold label to the end of its paragraph.
    batch = {}
    for address, c in claims:
        tie = next((t for t in ties if t["id"] == tie_of.get(c.get("passage"))), None)
        if not tie:
            continue
        at = text.find(tie["from"])
        para = text.rfind("\n\n", 0, at) + 2
        label = f"**{c['title']}"
        lab = text.find(label, para, at + 1)
        begin = lab if lab >= 0 else at
        stop = text.find("\n\n", max(at + len(tie["from"]), begin))
        stop = len(text) if stop < 0 else stop
        if stop - begin > 1700:
            begin, stop = at, at + len(tie["from"])
        first = text[begin:begin + min(80, stop - begin)]
        last = text[max(begin, stop - 60):stop]
        rows = []
        for name in c.get("lean", []):
            found = lean.resolve(name)
            if not found:
                continue
            verdict = links.get("fidelity", {}).get(name, {})
            row = {"file": found[1], "name": found[0], "relation": "states",
                   "fidelity": verdict.get("verdict", "same"), "fidelity_source": "ai"}
            if verdict.get("text"):
                row["fidelity_note"] = verdict["text"]
            elif row["fidelity"] != "same":
                row["fidelity_note"] = "The source records this verdict without a note."
            rows.append(row)
        batch[f"{args.paper}.{address}"] = {slot: c["title"], "lean": rows,
                                             "statements": [{"paper": slot, "role": "statement", "from": first, "to": last,
                                                             "origin": "ai"}]}
    write(out / "alignment/m1-results.json", dumps({
        "schema_version": "1.0", "provenance": "Generated by scripts/from_proof_reader.py from Proof Reader's claims and fidelity",
        "records": dict(sorted(batch.items()))}))
    write(out / "alignment/aliases.json", dumps({"schema": 1, "passages": aliases,
                                                 "claims": {c["id"]: a for a, c in claims}}))

    paper_md = text.encode("utf-8")
    title = toml["paper"]["title"]
    authors = toml["paper"].get("authors", [])
    sources, citations, nodes, edges, evidence = {}, {}, {}, [], {}

    def node(nid, kind, label, status, **extra):
        nodes[nid] = {"id": nid, "kind": kind, "label": label, "status": status,
                      "assumption_ids": [], "evidence_ids": [], "citation_ids": [], **extra}

    sources["paper"] = {"id": "paper", "kind": "file", "url": toml["paper"].get("url", upstream_repo),
                        "revision": upstream_rev or args.source_commit, "license": "NOASSERTION",
                        "redistribution": "reference_only", "sha256": sha(paper_md)}
    sources["upstream"] = {"id": "upstream", "kind": "repository", "url": upstream_repo, "revision": upstream_rev,
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
        statement = tie["from"] if tie else c["title"]
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
                                "revision": upstream_rev, "license": "NOASSERTION", "redistribution": "vendored",
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
    claim_at = {}
    for address, c in claims:
        tie = next((t for t in ties if t["id"] == tie_of.get(c.get("passage"))), None)
        if tie:
            claim_at[f"{args.paper}.{address}"] = text.find(tie["from"])

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
        statuses = {nodes[i]["status"] for i in ids}
        passages.append({"anchor": sec["anchor"], "text_sha256": sha(text[start:stop].encode("utf-8")),
                         "claim_ids": ids, "citation_ids": sorted(required_citation_ids(graph, ids)) if ids else [],
                         "assumption_ids": [],
                         "evidence_class": "context" if not ids else ("open_question" if statuses == {"open"} else "source_argument"),
                         "rationale": f"{sec['heading']}: " + ("states or proves the listed results." if ids else "context with no numbered result.")})
    write(paper_dir / "correspondence.json", dumps(mapping(slot, paper_md, passages)))
    for s in SLOTS:
        if s != slot:
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

    # ---- the guide to how the Lean encodes the paper, as a page of its own (the exposition slot)
    guide = None
    if args.guide:
        gslot = next(s for s in ("expository", "long") if s != slot)
        gtext = args.guide.read_text()
        gtext, gsections, _ = reading_copy(gtext, [])
        gbytes = gtext.encode("utf-8")
        write(out / "papers" / gslot / "paper.md", gtext)
        (out / "papers" / gslot / "absent.md").unlink(missing_ok=True)
        (out / "papers" / gslot / "absent.json").unlink(missing_ok=True)
        gpassages, cursor = [], 0
        for sec in gsections:
            marker, end = f"<!-- passage:{sec['anchor']} -->", f"<!-- /passage:{sec['anchor']} -->"
            start = gtext.index(marker, cursor) + len(marker)
            stop = gtext.index(end, start)
            cursor = stop
            gpassages.append({"anchor": sec["anchor"], "text_sha256": sha(gtext[start:stop].encode("utf-8")), "claim_ids": [],
                              "citation_ids": [], "assumption_ids": [], "evidence_class": "context",
                              "rationale": f"{sec['heading']}: how the formalisation encodes the paper's objects."})
        mapped = mapping(gslot, gbytes, gpassages)
        mapped["state"] = "draft"
        mapped["claim_ids"] = [goal]
        write(out / "papers" / gslot / "correspondence.json", dumps(mapped))
        write(out / f"alignment/references-{gslot}.json", dumps(references(gtext, gslot)))
        guide = {"id": "encoding", "slot": gslot, "slug": "how-the-lean-encodes-it", "title": "How the Lean encodes it", "noun": "guide"}

    # ---- supplementary checks and the declarations no sentence names
    if (page / "generated/checks.json").is_file():
        write(out / "generated/checks.json", (page / "generated/checks.json").read_bytes())
        for f in sorted((page / "checks").glob("*.lean")) if (page / "checks").is_dir() else ():
            write(out / "generated/checks" / f.name, f.read_bytes())
    unnamed = sorted({r[0] for n in links.get("show_also", []) if (r := lean.resolve(n))})
    write(out / "generated/unnamed.json", dumps({"schema": 1, "names": unnamed}))

    # ---- the instance
    credit = toml.get("credit", {}).get("text", "")
    instance = {
        "schema": "library-instance/1", "id": args.paper, "title": title,
        "short_title": toml["paper"].get("short_title", title), "authors": authors,
        "venue": toml["paper"].get("venue", ""),
        "credit_lines": [credit] if credit else [],
        # Companion pages credit the authors and their repository only; the main paper's own
        # header and About carry the full credit line (credit_lines).
        "companion_credit": (f"Paper and Lean by {', '.join(authors[:-1]) + ' and ' + authors[-1] if len(authors) > 1 else ''.join(authors)}, "
                             f"from their repository {upstream_repo.replace('https://github.com/', '')} at {upstream_rev[:7]}."),
        "host": "Hosted by Will Cook in his reading library, with credit to the authors.",
        "review": ("The links from the text to the Lean, the plain titles, the reading notes and the comparisons were made "
                   "with AI and have not been reviewed by the authors. No mathematician has reviewed them."),
        "source": {"proof_reader": {"repository": "https://github.com/wcook04/proof-reader", "commit": args.source_commit,
                                    "page": page.name},
                   "upstream": {"repository": upstream_repo, "commit": upstream_rev, "paper": toml["paper"].get("url")},
                   "lean_scope": toml["lean"].get("scope", "")},
        "documents": [{"id": "paper", "slot": slot, "slug": "", "title": title, "noun": toml["paper"].get("noun", "paper"),
                       "main": True, **({"pdf": pdf} if pdf else {})}] + ([guide] if guide else []),
        **({"comparator": comparator} if comparator else {}),
        "families": links.get("families", []),
        "topics": [{"id": t["id"], "name": t["name"], "description": t.get("description", ""), "family": t.get("family")}
                   for t in links["topics"]],
        "topic_order": topic_order,
        "goal": goal,
    }
    write(out / "instance.json", dumps(instance))
    summary = {k: (len(v) if isinstance(v, list) else v) for k, v in report.items()}
    summary.update(ties=len(ties), titled=len(titles), names=len(plain), results=len(results), sections=len(section_anchors),
                   lean_files=len(locked), unnamed=len(unnamed))
    write(out / "generated/conversion-report.json", dumps({"summary": summary, **report}))
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
