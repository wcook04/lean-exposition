#!/usr/bin/env python3
"""Build a library paper's Lean index: the text scan of its Lean, with Lean's own dependencies.

    enrich_lean_index.py LEAN_TREE FACTS.json OUT.json

FACTS.json (written by from_proof_reader.py from Proof Reader's compiled report) gives, for each
declaration by its name in the text index, the constants its type uses (`s`), those its value
uses (`v`, recorded for definitions only) and its axioms. A theorem's statement uses are Lean's
type dependencies, and its proof uses its value dependencies where recorded, else the names the
text scan finds outside its statement. A definition is read whole: everything it names is in its
statement. Every list is restricted to declarations of the
index, and `used_by` (with its statement and proof halves) is recomputed from them. The reader's
Lean card and graph read these fields (site/src/lean/data.ts, CompiledFacts).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from lean_exposition.lean_index import build_index, canonical


PROVED = {"theorem", "lemma", "example"}


def enrich(tree: Path, facts: dict) -> dict:
    index = build_index(tree)
    rows = {d["name"]: d for m in index["modules"] for d in m["declarations"]}
    for name, d in rows.items():
        f = facts.get(name)
        if not f:
            continue
        statement = {n for n in f.get("s", []) if n in rows and n != name}
        value = {n for n in (f.get("v") or d["uses"]) if n in rows and n != name}
        if d["kind"] not in PROVED:
            # A definition is read whole: what its body names is part of what it says.
            statement, value = statement | value, set()
        statement, proof = sorted(statement), sorted(value - statement)
        d["statement_uses"], d["proof_uses"] = statement, proof
        d["uses"] = sorted(set(statement) | set(proof))
        if f.get("axioms") is not None:
            d["axioms"] = f["axioms"]
            d["sorry"] = "sorryAx" in f["axioms"]
        d["dependency_source"] = "lean_report"
    used_by, s_by, p_by = {}, {}, {}
    for name, d in rows.items():
        for n in d["uses"]:
            used_by.setdefault(n, set()).add(name)
        for n in d.get("statement_uses", []):
            s_by.setdefault(n, set()).add(name)
        for n in d.get("proof_uses", []):
            p_by.setdefault(n, set()).add(name)
    for name, d in rows.items():
        d["used_by"] = sorted(used_by.get(name, ()))
        if "statement_uses" in d:
            d["statement_used_by"] = sorted(s_by.get(name, ()))
            d["proof_used_by"] = sorted(p_by.get(name, ()))
    index["dependency_source"] = "lean_report"
    index["dependency_note"] = ("Statement uses are Lean's type dependencies from the compiled modules; proof uses are "
                                "Lean's value dependencies where recorded, else names found in the proof's text.")
    return index


def main() -> None:
    tree, facts, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    index = enrich(tree, json.loads(facts.read_text())["facts"])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(canonical(index))
    n = sum(1 for m in index["modules"] for d in m["declarations"] if d.get("dependency_source") == "lean_report")
    print(f"lean index: {n} declarations carry Lean's own dependencies")


if __name__ == "__main__":
    main()
