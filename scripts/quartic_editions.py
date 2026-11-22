#!/usr/bin/env python3
"""Publish every edition the quartic reader ever served as a frozen, read-only snapshot.

    quartic_editions.py QUARTIC_GIT_DIR OUT [--ref origin/gh-pages] [--base /library/quartic/editions/]

The old quartic reader (wcook04/quartic-query-lean, gh-pages) pinned content-addressed editions in
its links (`#/read/<paper>?…&ed=edition-<sha256>.json`), and those links went out as fixed versions.
For each edition in the gh-pages history this writes OUT/<sha256>/index.html: the reader app as it
was published while that edition was current (the last gh-pages commit whose index.json named it,
else the first commit that carried it), opening that edition, with a one-line banner linking to the
current reading in the library.

Everything is copied from the history unchanged except the app's base path, which moves from
/quartic-query-lean/ to the snapshot folders. Edition manifests and their objects are pooled once
in OUT/_site/reading-api/v1/ (every object is content-addressed, so pooling changes no byte the
reader verifies); app assets are pooled in OUT/_site/assets/ unless two commits published different
files under one name, in which case that commit keeps its own copy under OUT/_c<commit>/. A small
script in each snapshot page answers the app's request for the current edition (index.json) with
the snapshot's own edition, so it opens exactly as it did when that edition was current.
Writes OUT/editions.json: each edition with its commit and date, for the redirect stub.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

TEXT = (".js", ".mjs", ".css", ".html", ".json", ".svg", ".map", ".txt", ".webmanifest")
OLD_BASE = re.compile(r"(?<![\w.])/quartic-query-lean/")
EDITION = re.compile(r"^reading-api/v1/edition-([a-f0-9]{64})\.json$")


def git(repo: Path, *args: str, binary: bool = False):
    out = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, check=True).stdout
    return out if binary else out.decode()


def tree(repo: Path, commit: str) -> dict[str, str]:
    rows = {}
    for line in git(repo, "ls-tree", "-r", commit).splitlines():
        meta, path = line.split("\t", 1)
        rows[path] = meta.split()[2]
    return rows


SHIM = """<script>
/* A frozen edition: the reader's request for the current edition (index.json) is answered with this
   snapshot's own edition, and the pooled edition files are read from %(api)s. */
(function () {
  var api = "%(api)s", own = "edition-%(hex)s.json", real = window.fetch.bind(window);
  window.fetch = function (input, init) {
    var u;
    try { u = new URL(typeof input === "string" ? input : (input && input.url) || String(input), location.href); }
    catch (e) { return real(input, init); }
    var m = u.origin === location.origin && u.pathname.match(/\\/reading-api\\/v1\\/(.*)$/);
    if (!m) return real(input, init);
    var rest = m[1] === "index.json" ? own : m[1];
    return real(location.origin + api + rest, init).then(function (r) {
      return new Response(r.body, { status: r.status, statusText: r.statusText, headers: r.headers });
    });
  };
})();
</script>"""

BANNER = """<div class="frozen-edition" role="note" style="position:relative;z-index:2147483647;margin:0;padding:6px 16px;font:14px/1.45 system-ui,-apple-system,'Segoe UI',sans-serif;background:#fdf3d0;color:#3b2f00;border-bottom:1px solid #e2cf8a;overflow-wrap:anywhere">A fixed edition of the quartic reader, as published on %(date)s. <a href="%(current)s" style="color:#174ea6;font-weight:600">Read the current version in the library →</a></div>"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--ref", default="origin/gh-pages")
    ap.add_argument("--base", default="/library/quartic/editions/")
    ap.add_argument("--current", default="/library/quartic/")
    args = ap.parse_args()
    repo, out, base = args.repo, args.out, args.base
    commits = git(repo, "rev-list", "--reverse", args.ref).split()
    trees, current, dates = {}, {}, {}
    for c in commits:
        trees[c] = tree(repo, c)
        dates[c] = git(repo, "log", "-1", "--format=%cs", c).strip()
        if "reading-api/v1/index.json" in trees[c]:
            index = json.loads(git(repo, "cat-file", "-p", trees[c]["reading-api/v1/index.json"]))
            current[c] = index.get("permalink")
    editions = {}
    for c in commits:
        for path in trees[c]:
            m = EDITION.match(path)
            if m:
                editions.setdefault(m.group(1), {"first": c})
    for hex_, row in editions.items():
        named = [c for c in commits if current.get(c) == f"edition-{hex_}.json"]
        row["home"] = named[-1] if named else row["first"]
        row["current_from"] = dates[named[0]] if named else None
    if out.exists():
        shutil.rmtree(out)
    site = out / "_site"
    blob_of = {}
    for c in commits:
        for path, blob in trees[c].items():
            blob_of.setdefault(path, blob)

    def put(path: Path, blob: str, new_base: str):
        data = git(repo, "cat-file", "-p", blob, binary=True)
        if path.suffix in TEXT:
            data = OLD_BASE.sub(new_base, data.decode("utf-8")).encode("utf-8")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    # Pooled editions and their objects.
    objects = set()
    for hex_ in sorted(editions):
        path = f"reading-api/v1/edition-{hex_}.json"
        blob = blob_of[path]
        manifest = git(repo, "cat-file", "-p", blob, binary=True)
        (site / path).parent.mkdir(parents=True, exist_ok=True)
        (site / path).write_bytes(manifest)  # byte for byte: the reader checks its hash
        for entry in json.loads(manifest)["resources"].values():
            objects.add("reading-api/v1/" + entry["href"])
    missing = []
    for path in sorted(objects):
        if path not in blob_of:
            missing.append(path)
            continue
        target = site / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git(repo, "cat-file", "-p", blob_of[path], binary=True))  # unchanged
    # App assets, pooled unless a commit published a different file under a name already taken.
    pooled, homes = {}, sorted({row["home"] for row in editions.values()}, key=commits.index)
    app_base = {}
    for c in homes:
        assets = {p: b for p, b in trees[c].items() if p.startswith("assets/")}
        clash = any(p in pooled and pooled[p] != b for p, b in assets.items())
        if clash:
            app_base[c] = f"{base}_c{c[:12]}/"
            for p, b in assets.items():
                put(out / f"_c{c[:12]}" / p, b, app_base[c])
        else:
            app_base[c] = f"{base}_site/"
            for p, b in assets.items():
                if p not in pooled:
                    pooled[p] = b
                    put(site / p, b, app_base[c])
    # One page per edition.
    listing = []
    for hex_, row in sorted(editions.items(), key=lambda kv: (commits.index(kv[1]["home"]), kv[0])):
        c = row["home"]
        page = git(repo, "cat-file", "-p", trees[c]["index.html"])
        page = OLD_BASE.sub(app_base[c], page)
        date = row["current_from"] or dates[row["first"]]
        page = re.sub(r"(<head[^>]*>)", lambda m: m.group(1) + "\n" + SHIM % {"api": f"{base}_site/reading-api/v1/", "hex": hex_}, page, count=1)
        page = re.sub(r"(<body[^>]*>)", lambda m: m.group(1) + "\n" + BANNER % {"date": date, "current": args.current}, page, count=1)
        page = page.replace("<title>", '<meta name="robots" content="noindex">\n    <title>', 1)
        (out / hex_).mkdir(parents=True, exist_ok=True)
        (out / hex_ / "index.html").write_text(page)
        listing.append({"edition": f"edition-{hex_}.json", "sha256": hex_, "commit": c, "published": date,
                        "app": app_base[c]})
    (out / "editions.json").write_text(json.dumps({
        "schema": 1, "source": f"{repo.resolve().name} {args.ref}",
        "meaning": "Each edition the old quartic reader served, frozen at /library/quartic/editions/<sha256>/ with the app it was published with.",
        "editions": listing}, indent=1) + "\n")
    print(f"{len(listing)} editions from {len(commits)} commits; {len(objects) - len(missing)} objects; "
          f"{sum(1 for v in app_base.values() if '_c' in v)} commit(s) with their own assets; missing {len(missing)}")
    for path in missing[:10]:
        print("missing object:", path)
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
