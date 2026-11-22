#!/usr/bin/env python3
"""Write the redirect stubs that replace a paper's old reader site, and test them.

    redirect_stubs.py PAPER OUT [--dist DIST]   write the stubs for instances/PAPER/redirects.json into OUT
    redirect_stubs.py PAPER --test               run every example of the table through the stubs' script

A paper that moved into the library keeps every address of its old site (docs/library-architecture.md,
"Redirects"). The old site becomes small static pages: each has a `meta refresh` to its deep match, a
`location.replace` that carries the query and the fragment to the same place in the library, and a
visible link for readers without JavaScript. `404.html` holds the same script, so every other old
address (a phrase, an edition file, a Lean name) lands on its own path under the library paper,
never only on the root. The old site's files that other pages link to directly (the PDFs and the run
receipts, `files` in the table) are copied from the library build (DIST, its site/dist), not
redirected, so a link to a PDF still returns the PDF.

The table (instances/PAPER/redirects.json) lists the old base path, the paper's library address, the
old reading routes and the library page each opens, and examples [old address, new address] that
--test checks with node.
"""
from __future__ import annotations

import argparse
import html
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# The mapping, as the stubs run it: from an old address to its library address. `T` is the table.
SCRIPT = r"""function libraryAddress(T, path, search, hash) {
  var p = path.indexOf(T.old_base) === 0 ? path.slice(T.old_base.length) : path.replace(/^\/+/, "");
  p = p.replace(/index\.html$/, "").replace(/\/+$/, "");
  var q = new URLSearchParams(search);
  var map = ["g", "n", "t", "lens", "e"].some(function (k) { return q.has(k); });
  if (p === "") {
    // The old front page: with map parameters it was the map; its own sections moved to About.
    if (map) return T.new + "map/" + search + hash;
    if (hash && hash.length > 1) return T.new + "about/" + search;
    return T.new + search;
  }
  var read = p.match(/^read\/(long|short|expository)$/);
  if (read) {
    // A passage opened beside another keeps the reader's own route, which the library serves too.
    if (q.has("beside")) return T.new + "read/" + read[1] + "/" + search + hash;
    return T.new + T.pages[read[1]] + search + hash;
  }
  if (T.views.indexOf(p) >= 0) return T.new + p + "/" + search + hash;
  // Any other address keeps its path under the library paper: a file keeps its name, a route its slash.
  return T.new + p + (/\.[A-Za-z0-9]+$/.test(p) ? "" : "/") + search + hash;
}"""

PAGE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title} has moved to the library</title>
<meta name="robots" content="noindex">
<link rel="canonical" href="{target}">
<script>
{script}
(function () {{
  var T = {table};
  location.replace(libraryAddress(T, location.pathname, location.search, location.hash));
}})();
</script>
<noscript><meta http-equiv="refresh" content="0; url={target}"></noscript>
<meta http-equiv="refresh" content="1; url={target}">
<style>
:root {{ color-scheme: light dark; --ink: #1d1d1b; --page: #fbfaf7; --link: #1f4f8f; }}
@media (prefers-color-scheme: dark) {{ :root {{ --ink: #e9e6df; --page: #161614; --link: #8db4ec; }} }}
body {{ margin: 0; padding: 48px 16px; background: var(--page); color: var(--ink); font: 18px/1.5 Georgia, "Times New Roman", serif; }}
main {{ max-width: 34em; margin: 0 auto; }}
a {{ color: var(--link); overflow-wrap: anywhere; }}
</style>
</head>
<body>
<main>
<p>{title} is now read in Will Cook's library.</p>
<p><a href="{target}">{target}</a></p>
</main>
</body>
</html>
"""


def load(paper: str) -> dict:
    return json.loads((ROOT / "instances" / paper / "redirects.json").read_text())


def table_js(t: dict) -> str:
    return json.dumps({k: t[k] for k in ("old_base", "new", "pages", "views")}, ensure_ascii=False)


def page(t: dict, target: str) -> str:
    return PAGE.format(title=html.escape(t["title"]), target=html.escape(target, quote=True), script=SCRIPT, table=table_js(t))


def write(paper: str, out: Path, dist: Path | None) -> int:
    t = load(paper)
    if out.exists():
        for child in out.iterdir():
            if child.name == ".git":
                continue
            shutil.rmtree(child) if child.is_dir() else child.unlink()
    out.mkdir(parents=True, exist_ok=True)
    pages = {"": t["new"], **{f"read/{slot}": t["new"] + slug for slot, slug in t["pages"].items()},
             **{view: f"{t['new']}{view}/" for view in t["views"]}}
    for path, target in pages.items():
        folder = out / path
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "index.html").write_text(page(t, target))
    (out / "404.html").write_text(page(t, t["new"]))
    (out / ".nojekyll").write_text("")
    (out / "README.md").write_text(
        f"# {t['title']}\n\nThis site has moved to [{t['new']}]({t['new']}). Every old address redirects to the same place there.\n"
        f"The pages here are redirect stubs written by `scripts/redirect_stubs.py {paper}` in "
        f"[wcook04/lean-exposition](https://github.com/wcook04/lean-exposition); the PDFs and run receipts stay as files.\n")
    copied = 0
    for name in t.get("files", []):
        source = (dist / name) if dist else None
        if not source or not source.exists():
            raise SystemExit(f"{name}: not in the library build {dist}; build the paper first")
        (out / name).parent.mkdir(parents=True, exist_ok=True)
        if source.is_dir():
            shutil.copytree(source, out / name)
            copied += sum(1 for p in (out / name).rglob("*") if p.is_file())
        else:
            shutil.copyfile(source, out / name)
            copied += 1
    print(f"{paper}: {len(pages)} stub pages, 404.html and {copied} copied files in {out}")
    return 0


def test(paper: str) -> int:
    t = load(paper)
    js = SCRIPT + f"\nconst T = {table_js(t)};\nconst rows = {json.dumps(t['examples'])};\nlet bad = 0;\n" + r"""
for (const [old, want] of rows) {
  const u = new URL(old);
  const got = libraryAddress(T, u.pathname, u.search, u.hash);
  if (got !== want) { bad++; console.log(`FAIL ${old}\n  got  ${got}\n  want ${want}`); }
}
console.log(`${rows.length - bad} of ${rows.length} examples land on their deep match`);
process.exit(bad ? 1 : 0);
"""
    return subprocess.run(["node", "-e", js]).returncode


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paper")
    ap.add_argument("out", nargs="?", type=Path)
    ap.add_argument("--dist", type=Path)
    ap.add_argument("--test", action="store_true")
    a = ap.parse_args()
    if a.test:
        return test(a.paper)
    if not a.out:
        ap.error("name OUT, or --test")
    return write(a.paper, a.out, a.dist)


if __name__ == "__main__":
    sys.exit(main())
