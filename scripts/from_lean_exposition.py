#!/usr/bin/env python3
"""Lay out one of this repository's own readers (examples/<x>/ and papers/<x>/) as a library paper.

    from_lean_exposition.py SOURCE PAPER     e.g. erdos257 erdos-257, or qaoa-sk sk

The SK and Erdős #257 readers are already in this repository's own format: one evidence graph,
three papers (the long record, the short paper and the exposition) with their passage
correspondences, phrase ties with topics and their stored colours, names, references, run
receipts and the vendored Lean. This converter copies them, unchanged, into the library layout
(docs/library-architecture.md, "Instance format"), so the library build reads them like any
other paper:

    examples/<x>/evidence-graph.json, source-lock.json   -> instances/<paper>/
    examples/<x>/alignment/*, authored/*, verification/*  -> the same folders
    examples/<x>/upstream/**                              -> upstream/ (the Lean, as vendored)
    papers/<x>/long/reasoning-record.{md,json,pdf}        -> papers/long/paper.md, correspondence.json, paper.pdf
    papers/<x>/short/paper.{md,pdf}, correspondence.json  -> papers/short/...
    papers/<x>/expository/main.{md,pdf}, correspondence.json, figures/ -> papers/expository/...

It also writes alignment/results.json: each numbered result of the main document (a record whose
label begins "Theorem A.1", "Proposition 5.1", ...) with its address (`theorem-a.1`), its record
and the Lean that formalises it. instance.json (the credit, documents, topics and the reader's
words) is authored and kept; the converter never writes it. Re-run after the source changes:
every copied file is replaced, and files the source no longer has are removed.
"""
from __future__ import annotations

import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KIND_WORDS = ("theorem", "proposition", "lemma", "corollary", "definition", "remark", "conjecture",
              "problem", "example", "assumption", "claim", "step")
# Each slot's files in papers/<x>/<slot>/: (markdown, correspondence, pdf).
SLOT_FILES = {
    "long": ("reasoning-record.md", "reasoning-record.json", "reasoning-record.pdf"),
    "short": ("paper.md", "correspondence.json", "paper.pdf"),
    "expository": ("main.md", "correspondence.json", "main.pdf"),
}
COPIED_DIRS = ("alignment", "authored", "verification", "upstream")
COPIED_FILES = ("evidence-graph.json", "source-lock.json", "references.bib")
# Files the library instance owns itself, kept when the copied folders are replaced.
OWN = {"alignment": {"results.json"}, "authored": {"check.json"}}


def dumps(value) -> str:
    return json.dumps(value, indent=1, ensure_ascii=False) + "\n"


def slug_of(label: str) -> str | None:
    """`Theorem A.1 (reciprocal-summable supports)` -> `theorem-a.1`."""
    m = re.match(r"^\s*([A-Za-z]+)\s+([0-9A-Za-z]+(?:\.[0-9A-Za-z]+)*)", label)
    if not m or m.group(1).lower() not in KIND_WORDS:
        return None
    return f"{m.group(1).lower()}-{m.group(2).lower()}"


def replace_dir(source: Path, target: Path, keep: set[str]) -> int:
    kept = {name: (target / name).read_bytes() for name in keep if (target / name).is_file()}
    if target.exists():
        shutil.rmtree(target)
    shutil.copytree(source, target, symlinks=False, ignore=shutil.ignore_patterns(".lake", "__pycache__", ".DS_Store"))
    for name, data in kept.items():
        (target / name).write_bytes(data)
    return sum(1 for p in target.rglob("*") if p.is_file())


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    source, paper = argv
    example, papers = ROOT / "examples" / source, ROOT / "papers" / source
    out = ROOT / "instances" / paper
    if not (example / "evidence-graph.json").is_file() or not papers.is_dir():
        raise SystemExit(f"no reader {source}: examples/{source}/evidence-graph.json and papers/{source}/ are needed")
    if not (out / "instance.json").is_file():
        raise SystemExit(f"instances/{paper}/instance.json is authored; write it before converting")
    instance = json.loads((out / "instance.json").read_text())
    copied = 0
    for name in COPIED_FILES:
        if (example / name).is_file():
            shutil.copyfile(example / name, out / name)
            copied += 1
    for name in COPIED_DIRS:
        if (example / name).is_dir():
            copied += replace_dir(example / name, out / name, OWN.get(name, set()))
    for slot, (md, corr, pdf) in SLOT_FILES.items():
        home = papers / slot
        target = out / "papers" / slot
        if target.exists():
            shutil.rmtree(target)
        target.mkdir(parents=True)
        if not (home / md).is_file():
            # The build reads a slot the paper does not have as absent.md / absent.json.
            continue
        shutil.copyfile(home / md, target / "paper.md")
        shutil.copyfile(home / corr, target / "correspondence.json")
        copied += 2
        if (home / pdf).is_file():
            shutil.copyfile(home / pdf, target / "paper.pdf")
            copied += 1
        if (home / "figures").is_dir():
            copied += replace_dir(home / "figures", target / "figures", set())
    if (papers / "numbering.json").is_file():
        (out / "generated").mkdir(exist_ok=True)
        shutil.copyfile(papers / "numbering.json", out / "generated" / "numbering.json")
        copied += 1

    # The numbered results of the main document, in the authors' numbering.
    graph = json.loads((out / "evidence-graph.json").read_text())
    main = next(d for d in instance["documents"] if d.get("main"))
    prefix = {"long": "long.", "short": "short.", "expository": "exp."}[main["slot"]]
    lean: dict[str, list[str]] = {}
    for e in graph["edges"]:
        if e["kind"] == "formalizes" and e["to"].startswith("lean."):
            lean.setdefault(e["from"], []).append(e["to"][len("lean."):])
    results = {}
    for node in graph["nodes"]:
        if node["kind"] not in ("claim", "goal") or not node["id"].startswith(prefix):
            continue
        slug = slug_of(node.get("label", ""))
        if not slug:
            continue
        if slug in results:
            raise SystemExit(f"two records are numbered {slug}: {results[slug]['record']} and {node['id']}")
        title = re.match(r"^\s*([A-Za-z]+\s+[0-9A-Za-z.]+)", node["label"]).group(1)
        results[slug] = {"record": node["id"], "title": title, "lean": sorted(set(lean.get(node["id"], [])))}
    # Numbered sections first (1.2, 3.1, ...), then the appendices (A.1, B.1, ...), each in order.
    order = lambda slug: [(0, int(p), "") if p.isdigit() else (1, 0, p) for p in slug.split("-", 1)[1].split(".")]
    results = {k: results[k] for k in sorted(results, key=lambda s: (order(s), s))}
    (out / "alignment" / "results.json").write_text(dumps({
        "schema": 1,
        "meaning": f"Each numbered result of the {main['title'].lower()}, by its address in the paper's own numbering, with its record in "
                   f"the evidence graph and the Lean that formalises it. Written by scripts/from_lean_exposition.py from examples/{source}.",
        "results": results,
    }))
    print(f"instances/{paper}: {copied} files from examples/{source} and papers/{source}; {len(results)} numbered results")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
