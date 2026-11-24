#!/usr/bin/env python3
"""Write the redirect page that replaces the old quartic reader's gh-pages root.

    quartic_redirect_stub.py OUT --table instances/quartic/generated/redirects.json --editions EDITIONS.json

The old reader (https://wcook04.github.io/quartic-query-lean/) used hash routes,
`#/read/<paper>?st=&d=&ph=&s=&p=&a=&v=&j=&step=&e=&ed=`. This writes OUT/index.html and OUT/404.html,
one small page whose script maps each old address to its deep library address with
location.replace (so Back is not broken), and a visible link for readers without JavaScript:

  #/ and #/read/expert…            /library/quartic/…            (the expert companion, the main document)
  #/read/exposition…, reconstruction…   /library/quartic/<slug>/…
  ed=edition-<sha>.json            /library/quartic/editions/<sha>/#<the same route>   (the frozen snapshot)
  #/read/original…, verification…  /library/quartic/source/#<the same route>   (OpenAI's paper and the supplement)
  #/about                          /library/quartic/about/      #/results → /library/quartic/about/#results
  st= (an OpenAI statement)        the expert companion's result restating it, /<result>/
  d=, ph=, s=, a=, v=, p=, j=, step=, e=   /lean/<d>, /@<ph>, ?l=<bytes>, #<anchor>, v, page, j and step, map/?e=
An address whose target is unknown lands on the paper with the reader's "not found" line.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

PAGE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>The quartic reader has moved to the library</title>
<link rel="canonical" href="https://wcook04.github.io/library/quartic/">
<meta name="robots" content="noindex">
<style>
:root { color-scheme: light dark; --bg: #fbfaf7; --fg: #1d1b16; --link: #174ea6; }
@media (prefers-color-scheme: dark) { :root { --bg: #16150f; --fg: #ece9df; --link: #8ab4f8; } }
body { margin: 0; padding: 32px 16px; background: var(--bg); color: var(--fg); font: 17px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 40rem; margin: 0 auto; }
a { color: var(--link); overflow-wrap: anywhere; }
</style>
<script>
var TABLE = %(table)s;
var EDITIONS = %(editions)s;
%(script)s
</script>
</head>
<body>
<main>
<p>The quartic reader has moved to the reading library.</p>
<p><a id="go" href="/library/quartic/">Open it in the library</a></p>
</main>
</body>
</html>
"""

SCRIPT = r"""
function target(hash) {
  var L = "/library/quartic/";
  var route = hash.replace(/^#/, "") || "/";
  var cut = route.indexOf("?");
  var path = cut < 0 ? route : route.slice(0, cut);
  var q = new URLSearchParams(cut < 0 ? "" : route.slice(cut + 1));
  var notFound = function (what) { return L + "#" + encodeURIComponent("not found: " + what); };
  var ed = q.get("ed");
  if (ed) {
    var m = /^edition-([a-f0-9]{64})\.json$/.exec(ed);
    if (m && EDITIONS.indexOf(m[1]) >= 0) return L + "editions/" + m[1] + "/#" + route;
    return notFound("edition " + ed);
  }
  if (path === "/" || path === "") return L;
  if (path === "/about") return L + "about/";
  if (path === "/results") return L + "about/#results";
  var read = /^\/read\/([a-z]+)$/.exec(path);
  if (!read) return notFound(route);
  var paper = read[1];
  if (paper === "original" || paper === "verification") return L + "source/#" + route;
  if (!(paper in TABLE.papers)) return notFound(route);
  var slug = TABLE.papers[paper];
  var main = slug === "";
  var base = L + (main ? "" : slug + "/");
  var out = new URLSearchParams();
  var at = null, sub = "", anchor = "";
  var st = q.get("st"), d = q.get("d"), ph = q.get("ph"), s = q.get("s"), a = q.get("a"), v = q.get("v"), e = q.get("e");
  if (e) {
    var parts = e.split("→");
    return parts.length === 3 ? L + "map/?e=" + parts.map(encodeURIComponent).join("~") : notFound("edge " + e);
  }
  if (st) {
    var result = main && TABLE.statements[st];
    if (result) sub = result + "/";
    else if (!s && !ph && !d) return notFound("statement " + st);
  }
  if (ph) {
    if (main && !sub) sub = "@" + encodeURIComponent(ph);
    else out.set("n", "phrase:" + ph);
  }
  if (s) {
    var place = (TABLE.selections[paper] || {})[s];
    if (place) at = place;
    else if (!ph && !d && !sub) return notFound("passage " + s);
  }
  if (d) {
    if (main && !sub) sub = "lean/" + d;
    else out.set("d", d);
  }
  if (at) out.set("l", at);
  if (v === "lean" || v === "graph") out.set("v", v);
  else if (d && !(main && sub.indexOf("lean/") === 0)) out.set("v", "lean");
  if (q.get("p")) out.set("page", q.get("p"));
  if (q.get("j")) out.set("j", q.get("j"));
  if (q.get("step")) out.set("step", q.get("step"));
  if (a) {
    var where = (TABLE.anchors[paper] || {})[a];
    anchor = "#" + encodeURIComponent(where || ("not found: " + a));
  }
  var query = out.toString();
  return base + sub + (query ? "?" + query : "") + anchor;
}
try {
  var to = target(location.hash);
  document.addEventListener("DOMContentLoaded", function () { var g = document.getElementById("go"); if (g) g.href = to; });
  location.replace(to);
} catch (err) {
  location.replace("/library/quartic/");
}
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", type=Path)
    ap.add_argument("--table", type=Path, required=True)
    ap.add_argument("--editions", type=Path, required=True)
    ap.add_argument("--newest", required=True, help="the SHA-256 of the frozen edition used by the current source reader")
    args = ap.parse_args()
    table = json.loads(args.table.read_text())
    editions = [row["sha256"] for row in json.loads(args.editions.read_text())["editions"]]
    if args.newest not in editions:
        raise SystemExit("the newest edition has no snapshot")
    slim = {k: table[k] for k in ("papers", "statements", "selections", "anchors")}
    page = PAGE % {"table": json.dumps(slim, ensure_ascii=False, separators=(",", ":")),
                   "editions": json.dumps(editions), "script": SCRIPT}
    args.out.mkdir(parents=True, exist_ok=True)
    for name in ("index.html", "404.html"):
        (args.out / name).write_text(page)
    (args.out / ".nojekyll").write_text("")
    print(f"redirect page: {len(page)} bytes, {len(editions)} editions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
