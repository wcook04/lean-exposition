#!/usr/bin/env python3
"""Build each companion document of a library paper as a small edition of its own, beside the paper's.

A companion (instances/<paper>/papers/<page>/, alignment/phrases-<page>.json, kind "companion" in
instance.json) is read by the reader as a document in its own right, with its own text, structure,
ties and notes, against the paper's graph and Lean. The edition tools know three document slots, so
each companion is assembled in the short slot of a scratch bundle and exported, and the export's
document-specific responses are filed under <edition>/docs/<page>/, with every file name in its
index prefixed by docs/<page>/. The reader asks for a companion's responses under its own page name
and is answered from that index (site/src/api/static.ts); the Lean, the records and the map stay the
paper's own.

Usage: build_companion_editions.py <paper> <lean-index> <edition-out> [--only PAGE ...] [--jobs N]
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("paper")
ap.add_argument("lean_index", type=Path)
ap.add_argument("edition", type=Path)
ap.add_argument("--only", nargs="*")
ap.add_argument("--jobs", type=int, default=3)
a = ap.parse_args()
LX = os.environ.get("LEAN_EXPOSITION", "lean-exposition")
PY = os.environ.get("PYTHON", sys.executable)
I = Path("instances") / a.paper
inst = json.loads((I / "instance.json").read_text())
docs = [d for d in inst["documents"] if d.get("kind") == "companion" and (not a.only or d["slot"] in a.only)]


def restage(data: dict, old: str, new: str) -> dict:
    """The same mapping, filed under another slot."""
    out = dict(data)
    if out.get("stage") == old:
        out["stage"] = new
    if out.get("path") == f"papers/{old}.md":
        out["path"] = f"papers/{new}.md"
    if out.get("paper") == old:
        out["paper"] = new
    return out


def prefix(value, pre: str):
    if isinstance(value, str):
        return pre + value
    if isinstance(value, dict):
        return {k: prefix(v, pre) for k, v in value.items()}
    return value


def build(doc: dict) -> str:
    page = doc["slot"]
    # An edition newer than everything it is made from is kept.
    done = a.edition / "docs" / page / "index.json"
    inputs = [I / f"papers/{page}/paper.md", I / f"alignment/phrases-{page}.json", I / "evidence-graph.json",
              I / "alignment/names.json"]
    if done.is_file() and all(done.stat().st_mtime > f.stat().st_mtime for f in inputs if f.is_file()):
        return f"{page}: current"
    tmp = Path("build") / f"{a.paper}-companions" / page
    shutil.rmtree(tmp, ignore_errors=True)
    (tmp / "alignment").mkdir(parents=True)
    for f in (I / "alignment").iterdir():
        if f.name.startswith(("phrases-", "references-", "colours-", "m1-")) or f.name == "results.json":
            continue
        shutil.copyfile(f, tmp / "alignment" / f.name)
    put = lambda name, data: (tmp / name).write_text(json.dumps(data, ensure_ascii=False))
    put("alignment/phrases-short.json", restage(json.loads((I / f"alignment/phrases-{page}.json").read_text()), page, "short"))
    put("alignment/references-short.json", restage(json.loads((I / f"alignment/references-{page}.json").read_text()), page, "short"))
    absent = json.loads((I / "papers/long/absent.json").read_text())
    empty = (I / "papers/long/absent.md").read_text()
    for s in ("long", "expository"):
        refs = restage(json.loads((I / "alignment/references-long.json").read_text()), "long", s)
        put(f"alignment/references-{s}.json", {**refs, "references": [], "sources": {}})
        put(f"{s}.json", restage(absent, "long", s))
        (tmp / f"{s}.md").write_text(empty)
    if (I / f"alignment/colours-{page}.json").is_file():
        put("alignment/colours-short.json", json.loads((I / f"alignment/colours-{page}.json").read_text()))
    shutil.copyfile(I / f"papers/{page}/paper.md", tmp / "short.md")
    put("short.json", restage(json.loads((I / f"papers/{page}/correspondence.json").read_text()), page, "short"))
    graph = I / "evidence-graph.json"
    run = lambda *cmd: subprocess.run([str(c) for c in cmd], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    try:
        run(LX, "check-alignment", tmp / "alignment", "--lean-tree", a.lean_index, "--graph", graph,
            "--paper", "long", tmp / "long.md", "--paper", "short", tmp / "short.md", "--paper", "expository", tmp / "expository.md")
        run(LX, "assemble", graph, "--long", tmp / "long.md", tmp / "long.json", "--short", tmp / "short.md", tmp / "short.json",
            "--expository", tmp / "expository.md", tmp / "expository.json", "--out", tmp / "bundle")
        run(PY, "site/scripts/export-static.py", tmp / "bundle", "--out", tmp / "edition", "--alignment", tmp / "alignment",
            "--lean-tree", a.lean_index, "--oracle", tmp / "oracle")
    except subprocess.CalledProcessError as e:
        return f"{page}: FAILED {e.cmd[1] if len(e.cmd) > 1 else e.cmd}: {e.stderr.decode()[-600:]}"
    # File the export's own document responses under docs/<page>/, every name prefixed; the rest of the
    # export (the graph, the records, the Lean, the search) is the paper's own and is not repeated.
    out = a.edition / "docs" / page
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True)
    pre = f"docs/{page}/"
    src = tmp / "edition"
    index = json.loads((src / "index.json").read_text())
    staged = lambda key: key.startswith(("/alignment/short", "/papers/short/", "/phrases/short", "/ties/short")) \
        or ("paper=short" in key and key.startswith(("/papers/reading", "/papers/query")))
    kept = {"version": index["version"], "api_version": index["api_version"], "snapshot": index["snapshot"],
            "documents": {"short": pre + index["documents"]["short"]},
            "responses": {k: pre + v for k, v in index["responses"].items() if staged(k)}, "route_maps": {}}
    files = {index["documents"]["short"], *(v for k, v in index["responses"].items() if staged(k))}
    for route, name in (index.get("route_maps") or {}).items():
        if route not in ("/papers/reading", "/papers/query"):
            continue
        table = {k: v for k, v in json.loads((src / name).read_text()).items() if staged(k)}
        files |= set(table.values())
        (out / name).write_text(json.dumps({k: pre + v for k, v in table.items()}, ensure_ascii=False))
        kept["route_maps"][route] = pre + name
    for name in files:
        (out / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src / name, out / name)
    (out / "index.json").write_text(json.dumps(kept, ensure_ascii=False))
    shutil.rmtree(tmp / "edition", ignore_errors=True)
    shutil.rmtree(tmp / "bundle", ignore_errors=True)
    return f"{page}: ok"


with ThreadPoolExecutor(a.jobs) as pool:
    results = list(pool.map(build, docs))
print("\n".join(results))
sys.exit(1 if any("FAILED" in r for r in results) else 0)
