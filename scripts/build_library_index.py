#!/usr/bin/env python3
"""Write the library's one home page and its catalog from instances/*/instance.json.

Usage: build_library_index.py OUT [PAPER...]
OUT receives index.html, catalog.json and 404.html. With PAPER names, only those papers are
listed (the ones published); without, every instance. The page is short: each paper, who
wrote it, its credit line and its pages. It loads nothing from another host.
"""
from __future__ import annotations

import html
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STYLE = """
:root{--bg:#fbfaf7;--fg:#1d1b22;--muted:#5d5866;--rule:#dedad2;--link:#2a4f9e}
@media (prefers-color-scheme:dark){:root{--bg:#1c1724;--fg:#ece8f2;--muted:#b0a9bb;--rule:#3a3346;--link:#9fbcf5}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.55 "STIX Two Text",Georgia,serif}
main{max-width:46rem;margin:0 auto;padding:3rem 16px 4rem}h1{font-size:1.9rem;font-weight:500;margin:0 0 .4rem}
.lede{color:var(--muted);margin:0 0 2.2rem}ol{list-style:none;padding:0;margin:0}
li.paper{border-top:1px solid var(--rule);padding:1.3rem 0}li.paper h2{font-size:1.25rem;font-weight:500;margin:0 0 .2rem}
a{color:var(--link);text-decoration-thickness:1px;text-underline-offset:3px}.by{margin:0 0 .4rem}
.credit{color:var(--muted);font-size:.92rem;margin:.3rem 0 0}.pages{font-size:.95rem;margin:.4rem 0 0}
footer{margin-top:2.5rem;color:var(--muted);font-size:.9rem}
"""


def names(people: list[str]) -> str:
    return people[0] if len(people) < 2 else f"{', '.join(people[:-1])} and {people[-1]}"


def main() -> None:
    out = Path(sys.argv[1])
    only = set(sys.argv[2:])
    papers = []
    for path in sorted((ROOT / "instances").glob("*/instance.json")):
        inst = json.loads(path.read_text())
        if only and inst["id"] not in only:
            continue
        papers.append(inst)
    catalog = {"schema": "library-catalog/1", "papers": [
        {"id": p["id"], "title": p["title"], "short_title": p.get("short_title", p["title"]), "authors": p["authors"],
         "pages": [{"slug": d["slug"], "title": d["title"], "noun": d.get("noun", "paper")} for d in p["documents"]]}
        for p in papers]}
    items = []
    for p in papers:
        pages = [d for d in p["documents"] if not d.get("main")]
        extra = (f'<p class="pages">Also: ' + ", ".join(
            f'<a href="{html.escape(p["id"])}/{html.escape(d["slug"])}/">{html.escape(d["title"])}</a>' for d in pages) + "</p>") if pages else ""
        credit = "".join(f'<p class="credit">{html.escape(line)}</p>' for line in p.get("credit_lines", []))
        items.append(f'<li class="paper"><h2><a href="{html.escape(p["id"])}/">{html.escape(p["title"])}</a></h2>'
                     f'<p class="by">By {html.escape(names(p["authors"]))}.</p>{credit}{extra}</li>')
    page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Reading library</title>
<meta name="description" content="Papers read sentence by sentence beside their Lean.">
<link rel="canonical" href="https://wcook04.github.io/library/">
<style>{STYLE}</style>
</head>
<body>
<main>
<h1>Reading library</h1>
<p class="lede">Papers read sentence by sentence beside their Lean. Click an underlined phrase to see the Lean that states it.
The links, titles, notes and comparisons were made with AI; no mathematician has reviewed them.</p>
<ol>
{''.join(items)}
</ol>
<footer>Hosted by <a href="https://wcook04.github.io/">Will Cook</a>. Each paper is its authors’ work and is credited on its page.
Source: <a href="https://github.com/wcook04/lean-exposition">lean-exposition</a>.</footer>
</main>
</body>
</html>
"""
    out.mkdir(parents=True, exist_ok=True)
    (out / "index.html").write_text(page)
    (out / "404.html").write_text(page.replace("<h1>Reading library</h1>", "<h1>Reading library</h1>\n<p>There is no page at this address. These are the papers.</p>"))
    (out / "catalog.json").write_text(json.dumps(catalog, indent=1, ensure_ascii=False) + "\n")
    (out / ".nojekyll").write_text("")
    print(f"library index: {len(papers)} paper(s)")


if __name__ == "__main__":
    main()
