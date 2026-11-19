#!/usr/bin/env python3
"""Write the forwarding page for the old Erdős #257 problem page and its fragment map.

The present problem page (practical-formal-verification/maths/problems/erdos_257.html) is to
become a forwarding page to the Erdős 257 Reader. This script writes, under
site/src/instances/erdos257/:

- forward-map.json: every old fragment the page answers, with the reader path it lands on;
- forward/erdos_257.html: the page itself, plain HTML with one small inline script that maps
  location.hash, keeps location.search, and falls back to the reader's front page.

It reads the #257 static edition (site/public/edition, exported by site/scripts/export-static.py)
for the place of each result in the papers, and examples/erdos257/upstream/lean for the Lean
modules the reader has. Rerunning on the same inputs gives the same bytes.

    python examples/erdos257/tools/build_forward.py
"""
from __future__ import annotations

import html
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
EDITION = ROOT / "site/public/edition"
LEAN = HERE / "upstream/lean"
OUT = ROOT / "site/src/instances/erdos257"
PAPERS = ROOT / "papers/erdos257"

READER = "https://wcook04.github.io/erdos-257-reader/"
OVERVIEW = "https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_257_overview.html"
OLD = "https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_257.html"

# Old fragment -> reader path (relative to the reader's base). "" is the front page.
FIXED = {
    "": "",
    "paper": "#papers",
    "versions": "#papers",
    "paper-erdos-257-mersenne-support-subseries": "read/short",
    "paper-erdos257-mersenne-reasoning-surface": "read/long",
    "paper-erdos257-expository-sums-never-fractions": "read/expository",
    "source-map": "lean",
    "modules": "lean",
    "current-results": "#asked",
    "checked": "#asked",
    "unchecked": "#asked",
    "results": "#asked",
    "obligations": "#asked",
    "comparator": "checks",
}
# These stay on the old page's content, kept at the overview address with the same fragment.
TO_OVERVIEW = ["the-problem", "plate-erdos-257-problem", "plate-erdos-257-weighted", "plate-erdos-257-halving", "experiment"]


def edition_route(route: str):
    index = json.loads((EDITION / "index.json").read_text())
    body = json.loads((EDITION / index["responses"][route]).read_text())
    return body.get("data", body)


def anchors(stage_md: Path) -> set[str]:
    return set(re.findall(r'<a id="([^"]+)"></a>', stage_md.read_text(encoding="utf-8")))


def result_paths() -> dict[str, str]:
    """A paper's result label (res:reciprocal-support) -> that result in the reader with its Lean open."""
    records = edition_route("/alignment")["records"]
    found: dict[str, str] = {}
    for stage, md in (("long", PAPERS / "long/reasoning-record.md"), ("short", PAPERS / "short/paper.md")):
        names = anchors(md)
        for rid, record in sorted(records.items()):
            if not rid.startswith(f"{stage}.") or not record.get("lean"):
                continue
            label = rid[len(stage) + 1:].replace("-", ":", 1)
            statement = next((s for s in record["statements"] if s["paper"] == stage and s.get("at")), None)
            if label in names and statement:
                # The short paper's results win over the long record's where both have the label.
                found[label] = f"read/{stage}?l={statement['at']}&n={rid}#{label}"
    return dict(sorted(found.items()))


def modules() -> list[str]:
    return sorted(str(p.relative_to(LEAN).with_suffix("")).replace("/", ".") for p in LEAN.rglob("*.lean"))


def page(table: dict) -> str:
    data = json.dumps(table, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    return f"""<!doctype html>
<html lang="en-GB">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Erdős problem #257: moved to the Erdős 257 Reader</title>
<link rel="canonical" href="{READER}">
<meta http-equiv="refresh" content="0; url={READER}">
<meta name="robots" content="noindex">
<style>
  body {{ margin: 0; padding: 48px 16px; font: 18px/1.5 Georgia, serif; color: #1d1b17; background: #f6f1e7; }}
  main {{ max-width: 36rem; margin: 0 auto; }}
  a {{ color: inherit; }}
  @media (prefers-color-scheme: dark) {{ body {{ color: #ece6da; background: #1b1a17; }} }}
</style>
<script>
(function () {{
  // The reader's address. On this machine only, ?reader=<address> points it at a local copy for testing.
  var READER = "{READER}";
  var MAP = {data};
  var search = new URLSearchParams(location.search);
  var local = /^(localhost|127\\.0\\.0\\.1|\\[::1\\])$/.test(location.hostname);
  if (local && search.get("reader")) READER = search.get("reader");
  search.delete("reader");
  var query = search.toString();
  function at(path) {{
    var cut = path.indexOf("#"), hash = cut < 0 ? "" : path.slice(cut), rest = cut < 0 ? path : path.slice(0, cut);
    var q = rest.indexOf("?"), route = q < 0 ? rest : rest.slice(0, q), own = q < 0 ? "" : rest.slice(q + 1);
    var both = [own, query].filter(Boolean).join("&");
    return READER + route + (both ? "?" + both : "") + hash;
  }}
  var fragment = location.hash.slice(1);
  try {{ fragment = decodeURIComponent(fragment); }} catch (e) {{}}
  var target;
  if (Object.prototype.hasOwnProperty.call(MAP.fixed, fragment)) target = at(MAP.fixed[fragment]);
  else if (fragment.indexOf("lean-module:") === 0) {{
    var name = fragment.slice("lean-module:".length);
    target = at(MAP.modules.indexOf(name) >= 0 ? "lean?m=" + encodeURIComponent(name) : "lean");
  }} else if (fragment.indexOf("lean=") === 0) {{
    var label = fragment.slice("lean=".length);
    target = at(Object.prototype.hasOwnProperty.call(MAP.results, label) ? MAP.results[label] : "read/short");
  }} else if (MAP.overview.indexOf(fragment) >= 0 || fragment.indexOf("plate-") >= 0) {{
    target = MAP.overviewUrl + (query ? "?" + query : "") + "#" + encodeURIComponent(fragment);
  }} else target = at("");
  location.replace(target);
}})();
</script>
</head>
<body>
<main>
<h1>Erdős problem #257</h1>
<p>This page has moved. The three papers on Erdős problem #257, with their Lean proofs, are in the <a href="{READER}">Erdős 257 Reader</a>.</p>
<p>The worked figures, the 189/388 calculation and the full list of results are on <a href="{html.escape(OVERVIEW)}">the overview page</a>.</p>
</main>
</body>
</html>
"""


def main() -> None:
    results = result_paths()
    table = {"fixed": FIXED, "overview": TO_OVERVIEW, "overviewUrl": OVERVIEW, "results": results, "modules": modules()}
    forward_map = {
        "about": "Old fragments of " + OLD + " and where forward/erdos_257.html sends each, relative to " + READER
                 + ". Written by examples/erdos257/tools/build_forward.py.",
        "reader": READER,
        "fragments": {("#" + k if k else "(none)"): v for k, v in FIXED.items()},
        "to_overview": {"#" + k: OVERVIEW + "#" + k for k in TO_OVERVIEW},
        "patterns": {
            "#lean-module:<Lean.Module.Name>": "lean?m=<Lean.Module.Name> when the reader has the module, else lean",
            "#lean=<result label>": "that result in its paper with its Lean open (results below), else read/short",
            "#<anything containing plate->": OVERVIEW + "#<same fragment>",
            "any other fragment": "the front page",
            "query string": "kept, and added to the reader address",
        },
        "results": {"#lean=" + k: v for k, v in results.items()},
        "modules": len(table["modules"]),
    }
    (OUT / "forward").mkdir(exist_ok=True)
    (OUT / "forward-map.json").write_text(json.dumps(forward_map, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUT / "forward/erdos_257.html").write_text(page(table), encoding="utf-8")
    print(f"forward-map.json: {len(FIXED)} fixed fragments, {len(TO_OVERVIEW)} to the overview, {len(results)} results, {len(table['modules'])} modules")


if __name__ == "__main__":
    main()
