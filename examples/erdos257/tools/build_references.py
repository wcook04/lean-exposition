#!/usr/bin/env python3
"""Write examples/erdos257/alignment/references-{short,long,expository}.json.

The reader copies already write every internal reference as a Markdown link to
an explicit anchor: `Theorem [3.1](#thm:...)`, `[(W)](#eq:...)`,
`Section [2](#sec:...)`, and citations `\\[[7](#ref-erdos1968), p. 222\\]`. So each
row is decided by its link target, not guessed from words: one row per link,
covering the link's bytes. Labels and titles come from papers/erdos257/numbering.json
and the anchored headings. Links to an anchor the paper lacks are reported and
left out. Rerunning on the same bytes gives the same files.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PAPERS = {"short": "short/paper.md", "long": "long/reasoning-record.md", "expository": "expository/main.md"}
LINK = re.compile(r"(?<!!)\[([^\[\]\n]+)\]\(#([^)\s]+)\)")
ANCHOR = re.compile(r'<a id="([^"]+)"></a>')
SECTION_PREFIXES = ("sec:", "ssec:", "app:", "sec-", "app-")


def main() -> None:
    numbering = json.loads((ROOT / "papers/erdos257/numbering.json").read_text())
    report = {}
    for stage, rel in PAPERS.items():
        path = ROOT / "papers/erdos257" / rel
        data = path.read_bytes()
        text = data.decode("utf-8")
        offsets = [0]
        for ch in text:
            offsets.append(offsets[-1] + len(ch.encode("utf-8")))
        labels = numbering.get(stage, {}).get("labels", {})
        anchors = {m.group(1): m.end() for m in ANCHOR.finditer(text)}

        def block_end(start: int, kind: str) -> int:
            if kind == "equation":
                opening = text.find("$$", start)
                closing = text.find("$$", opening + 2)
                return closing + 2 if opening >= 0 and closing >= 0 else start
            if kind == "section":
                heading = text.find("\n#", start - 1)
                return text.find("\n", heading + 1) if heading >= 0 else start
            stop = text.find("\n\n", text.find("**", start))
            return stop if stop >= 0 else len(text)

        targets, sources, rows, missing = {}, {}, [], []
        for m in ANCHOR.finditer(text):
            key = m.group(1)
            if not key.startswith("ref-"):
                continue
            line_end = text.find("\n", m.end())
            entry = text[m.end():line_end if line_end >= 0 else len(text)]
            href = re.search(r"\]\((https://[^)\s]+)\)", entry) or re.search(r"<(https://[^>\s]+)>", entry)
            authors = re.split(r",\s*\[|\s*\[\*|,\s*\*", re.sub(r"^\\\[\d+\\\]\s*", "", entry), maxsplit=1)[0]
            year = re.search(r"\((?:[^()]*?)(\d{4})\)", entry)
            sources[key[4:]] = {"name": authors.strip(" ,") + (f" ({year.group(1)})" if year else ""),
                                "href": href.group(1) if href else f"#{key}",
                                "entry": [offsets[m.end()], offsets[line_end if line_end >= 0 else len(text)]]}
        for m in LINK.finditer(text):
            quote, target = m.group(0), m.group(2)
            start, end = offsets[m.start()], offsets[m.end()]
            before = data[max(0, start - 60):start].decode("utf-8", errors="ignore")
            if target.startswith("ref-"):
                tail = text[m.end():m.end() + 80]
                locator = re.match(r",\s*([^\]\\]+?)\s*\\\]", tail)
                row = {"start_byte": start, "end_byte": end, "quote": quote, "before": before, "kind": "citation",
                       "source": target[4:], "cited_as": m.group(1)}
                if locator:
                    row["locator"] = locator.group(1)
                rows.append(row)
                continue
            if target not in anchors:
                missing.append(target)
                continue
            info = labels.get(target, {})
            kind = ("equation" if target.startswith("eq") else "section" if target.startswith(SECTION_PREFIXES)
                    else "figure" if target.startswith("fig") else "label")
            if target not in targets:
                at = anchors[target]
                printed = info.get("printed") or m.group(1)
                head = re.compile(r"\*\*([^*\n]+?)\*\*").search(text, at)
                label = (f"({printed})" if kind == "equation" else f"§{printed}" if kind == "section"
                         else (head.group(1).split(" (")[0].rstrip(".") if head and kind == "label" else printed))
                entry = {"kind": info.get("kind", kind), "label": label,
                         "start_byte": offsets[at], "end_byte": offsets[max(block_end(at, kind), at)]}
                if info.get("title"):
                    entry["title"] = f"{printed} {info['title']}" if kind == "section" else info["title"]
                targets[target] = entry
            rows.append({"start_byte": start, "end_byte": end, "quote": quote, "before": before,
                         "kind": kind, "target": target})
        # Plain self-references the paper prints without a link ("Sections 5–8", "Section 13"):
        # each becomes a row to the section whose printed number it names, when this paper has
        # one. A reference followed by a page ("Section 2, pp. 5–6") or "of [...]" names
        # another work and stays text, as does one inside a link or a citation.
        linked = [(m.start(), m.end()) for m in re.finditer(r"\[[^\]\n]*\]\([^)\s]+\)|\\\[[\s\S]*?\\\]", text)]
        # A numbered heading ("### 5. The series, …") and the anchor just above it.
        section_of, titles = {}, {}
        for h in re.finditer(r'<a id="([^"]+)"></a>\s*\n\s*\n?#{2,6} (\d+(?:\.\d+)*)\.? ([^\n]+)', text):
            section_of.setdefault(h.group(2), h.group(1))
            titles.setdefault(h.group(1), (h.group(2), h.group(3).strip()))
        references_at = text.find('<a id="references"></a>')
        for m in re.finditer(r"\bSections?[ \u00a0](\d+)(?:–\d+)?\b", text):
            if references_at >= 0 and m.start() > references_at:
                continue
            if any(a <= m.start() < b for a, b in linked):
                continue
            if re.match(r"^[^\n]{0,40}?\bpp?\.\s?\d|^[^.\n]{0,60}?\bof (?:the |their |his )?\[", text[m.end():]):
                continue
            target = section_of.get(m.group(1))
            if not target:
                continue
            if target not in targets:
                at = anchors[target]
                printed, title = titles[target]
                targets[target] = {"kind": "section", "label": f"§{printed}", "title": f"{printed} {title}",
                                   "start_byte": offsets[at], "end_byte": offsets[max(block_end(at, "section"), at)]}
            start, end = offsets[m.start()], offsets[m.end()]
            rows.append({"start_byte": start, "end_byte": end, "quote": m.group(0),
                         "before": data[max(0, start - 60):start].decode("utf-8", errors="ignore"),
                         "kind": "section", "target": target})
        rows.sort(key=lambda r: r["start_byte"])
        table = {"schema_version": "1.0", "paper": stage, "paper_sha256": hashlib.sha256(data).hexdigest(),
                 "provenance": "Generated by examples/erdos257/tools/build_references.py from the paper's own links",
                 "targets": dict(sorted(targets.items())), "sources": dict(sorted(sources.items())),
                 "references": rows}
        (HERE / "alignment" / f"references-{stage}.json").write_text(
            json.dumps(table, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        kinds = {}
        for r in rows:
            kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
        report[stage] = {"rows": len(rows), "by_kind": kinds, "targets": len(targets), "sources": len(sources),
                         "links_to_missing_anchors": sorted(set(missing)),
                         "sources_without_https": sorted(k for k, s in sources.items() if not s["href"].startswith("https://"))}
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
