#!/usr/bin/env python3
"""Check a library paper's Lean dependencies and its map before it is built.

    check_instance.py PAPER LEAN_INDEX

LEAN_INDEX is the index the reader will show (a JSON file from enrich_lean_index.py, or the
Lean tree). Fails, naming each problem, when:
  * the main result's Lean has no statement uses;
  * a numbered result of the paper is not used, through the map's edges in the direction of use,
    by the main result (unless authored/check.json records why);
  * a declaration a phrase names shows no uses, unless its own source names none either
    (the text scan finds nothing outside its own name).
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from lean_exposition.lean_index import load_index


def main() -> int:
    paper, index_path = sys.argv[1], Path(sys.argv[2])
    root = Path("instances") / paper
    index = load_index(index_path)
    rows = {d["name"]: d for m in index["modules"] for d in m["declarations"]}
    graph = json.loads((root / "evidence-graph.json").read_text())
    instance = json.loads((root / "instance.json").read_text())
    problems = []
    goal = instance["goal"]
    goal_lean = [e["to"][len("lean."):] for e in graph["edges"] if e["from"] == goal and e["kind"] == "formalizes"]
    if not goal_lean:
        problems.append(f"the main result {goal} has no Lean on the map")
    for name in goal_lean:
        d = rows.get(name, {})
        uses = d.get("statement_uses", d.get("uses", []))
        if not uses:
            problems.append(f"the main result's Lean {name} has no statement uses")
    # Every numbered result the main result uses: following the map's edges in the direction of use
    # (a result to its Lean, a declaration to what it uses), from the main result. A result is joined
    # when the main result reaches it this way, or reaches any declaration it states.
    out = {}
    for e in graph["edges"]:
        out.setdefault(e["from"], set()).add(e["to"])
    formal = {}
    for e in graph["edges"]:
        if e["kind"] == "formalizes":
            formal.setdefault(e["to"], set()).add(e["from"])
    seen, frontier = {goal}, [goal]
    while frontier:
        for n in out.get(frontier.pop(), ()):
            if n not in seen:
                seen.add(n)
                frontier.append(n)
    # A route into the main result joins too: a result used by anything that itself uses the main result
    # (Corollary 7.2 draws Theorem 1.1's conclusions; what it, or what leads to it, uses is on that route).
    into, back, frontier = {goal}, {}, [goal]
    for e in graph["edges"]:
        if e["kind"] != "formalizes":
            back.setdefault(e["to"], set()).add(e["from"])
    while frontier:
        for n in back.get(frontier.pop(), ()):
            if n not in into:
                into.add(n)
                frontier.append(n)
    frontier = [n for n in into if n not in seen]
    seen |= into
    while frontier:
        for n in out.get(frontier.pop(), ()):
            if n not in seen:
                seen.add(n)
                frontier.append(n)
    seen |= {r for d in list(seen) for r in formal.get(d, ())}
    results = [n["id"] for n in graph["nodes"] if n["kind"] in ("claim", "goal") and n["id"].startswith(f"{paper}.")]
    # A result may be known to stand apart, with the reason recorded in authored/check.json.
    allowed = {}
    if (root / "authored/check.json").is_file():
        allowed = json.loads((root / "authored/check.json").read_text()).get("not_joined", {})
    apart = [r for r in results if r not in seen and r not in allowed]
    if apart:
        problems.append(f"{len(apart)} numbered result(s) not joined to the main result: {', '.join(apart[:8])}")
    # The map is drawn in layers, so its edges may not form a cycle.
    colour, cycle = {}, []
    def visit(u, path):
        colour[u] = 1
        path.append(u)
        for v in sorted(out.get(u, ())):
            if colour.get(v) == 1 and not cycle:
                cycle.extend(path[path.index(v):] + [v])
            elif not colour.get(v):
                visit(v, path)
        path.pop()
        colour[u] = 2
    sys.setrecursionlimit(max(10000, 4 * len(graph["nodes"])))
    for n in sorted(out):
        if not colour.get(n) and not cycle:
            visit(n, [])
    if cycle:
        problems.append(f"the map has a cycle: {' -> '.join(cycle[:6])}")
    # No phrase's declaration shows zero uses unless its source names nothing.
    named = set()
    for path in sorted((root / "alignment").glob("phrases-*.json")):
        named |= {row["name"] for t in json.loads(path.read_text())["ties"] for row in t["lean"]}
    empty = [n for n in sorted(named) if n in rows and not rows[n].get("uses") and rows[n].get("dependency_source") != "lean_report"
             and rows[n]["kind"] not in ("axiom", "inductive", "structure", "class")]
    if empty:
        problems.append(f"{len(empty)} declaration(s) a phrase names show no uses and carry no Lean report: {', '.join(empty[:6])}")
    # Page slugs (/<paper>/<page>/) may not take a reserved word or a numbered result's address.
    reserved = {"lean", "topic", "map", "compare", "checks", "source", "about", "search", "read", "edition", "pdf"}
    result_slug = re.compile(r"^(theorem|proposition|lemma|corollary|definition|remark|conjecture|problem|example|assumption|claim|step)-[0-9a-z.]+$")
    slugs = [d.get("slug") for d in instance["documents"] if d.get("slug")]
    clash = sorted({s for s in slugs if s in reserved or result_slug.match(s)} | {s for s in slugs if slugs.count(s) > 1})
    if clash:
        problems.append(f"page slugs that collide with a reserved word, a result address or each other: {', '.join(clash)}")
    # A moved page's old slug keeps its address, so it may not be taken again, and it moves to a page.
    for old, row in instance.get("moved_pages", {}).items():
        if old in slugs or old in reserved or result_slug.match(old) or row.get("to") not in slugs:
            problems.append(f"moved page {old}: its old slug is taken, or it moves to {row.get('to')}, which is no page")
    for p in problems:
        print(f"instance {paper}: {p}", file=sys.stderr)
    if not problems:
        print(f"instance {paper}: the main result has statement uses; {len(results)} numbered results joined to it; "
              f"{len(named)} named declarations carry their uses")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
