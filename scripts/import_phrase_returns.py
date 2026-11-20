#!/usr/bin/env python3
"""Write an example's phrase files from reviewed phrase-tie returns.

A return (schema `phrase-ties/1`) ties each Lean declaration to the exact phrase of one
paper that states it, groups the ties under topics, and gives each declaration a plain
title and a reading note in that paper's register. This command copies the accepted
returns of one example into `examples/<example>/alignment/phrases-<paper>.json`, one
file per paper, and refreshes the example's `names.json`, where the site needs one title
per declaration.

A paper may come in several returns over consecutive line ranges (`--part`): each part
keeps its own topics, titles and notes, and a part's topic ids are prefixed `p1-`,
`p2-`, ... so that one file can hold them all. `lean-exposition check-alignment` checks
the result against the papers and the Lean.

Usage:

    python scripts/import_phrase_returns.py examples/qaoa-sk/alignment \\
        --paper short RETURNS/01_sk_short --paper expository RETURNS/02_sk_expository \\
        --paper long RETURNS/03_sk_long
    python scripts/import_phrase_returns.py examples/erdos257/alignment \\
        --paper short RETURNS/04_erdos257_short --paper expository RETURNS/05_erdos257_expository \\
        --paper long RETURNS/06_erdos257_long_I_II "Parts I–II" \\
        --paper long RETURNS/07_erdos257_long_III_V "Parts III–V"

The returns are not modified. Two kinds of pointer are corrected against the example's
vendored Lean index, and each correction is listed in the file's `corrections`: a name the
file does not declare, where exactly one declaration in that file has the same last
component, takes that declaration's full name (its title and note follow it); and `lines`
that run past the declaration are cut to it, or dropped when none of them lies inside it.

Every title of a paper's return replaces the declaration's entry in `names.json`, the
short paper's first, then the exposition's, then the long record's.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from lean_exposition.lean_index import load_index

SCHEMA = "phrase-ties/1"
PRIORITY = ("long", "expository", "short")  # later wins in names.json


def load(folder: Path, name: str):
    return json.loads((folder / name).read_text(encoding="utf-8"))


def part_of(folder: Path, name: str | None, prefix: str) -> tuple[dict, list, list, str]:
    packet = load(folder, "packet.json")
    ties = load(folder, "ties.json")
    if ties.get("schema") != SCHEMA:
        raise SystemExit(f"{folder}: expected schema {SCHEMA}")
    topics = load(folder, "topics.json")["topics"]
    rename = {t["id"]: prefix + t["id"] for t in topics}
    rows = []
    for tie in ties["ties"]:
        row = dict(tie)
        row["topic"] = rename[tie["topic"]]
        if prefix:
            row["id"] = prefix + tie["id"]
        rows.append(row)
    part = {
        "name": name or "",
        "packet": packet["packet"],
        "source_commit": packet["source_commit"],
        "lines": packet["assigned_lines"],
        "topics": [{**t, "id": rename[t["id"]]} for t in topics],
        "titles": dict(sorted(load(folder, "titles.json").items())),
        "notes": dict(sorted(load(folder, "notes.json").items())),
    }
    removed = [{**r, "id": prefix + r["id"]} if prefix else r for r in ties.get("removed", [])]
    return part, rows, removed, ties["paper"]


def correct(rows: list, part: dict, index: dict, corrections: list) -> None:
    """Point each Lean row at a declaration of the vendored index, inside its lines."""
    by_file = {}
    for module in index["modules"]:
        for declaration in module["declarations"]:
            by_file.setdefault(module["path"], []).append(declaration)
    for tie in rows:
        for row in tie["lean"]:
            declarations = by_file.get(row["file"], [])
            found = [d for d in declarations if d["name"] == row["name"]]
            if not found:
                last = row["name"].rpartition(".")[2]
                found = [d for d in declarations if d["name"].rpartition(".")[2] == last]
                if len(found) != 1:
                    continue  # check-alignment reports it
                old, new = row["name"], found[0]["name"]
                corrections.append(f"{tie['id']}: {old} is declared as {new} in {row['file']}")
                row["name"] = new
                for key in ("titles", "notes"):
                    if old in part[key] and new not in part[key]:
                        part[key][new] = part[key].pop(old)
            declaration = found[0]
            if "lines" in row:
                first, last = row["lines"]
                top, bottom = declaration["line"], declaration["end_line"]
                if top <= first <= last <= bottom:
                    continue
                cut = [max(first, top), min(last, bottom)]
                if cut[0] > cut[1]:
                    corrections.append(f"{tie['id']}: lines {first}-{last} lie outside {declaration['name']} "
                                       f"({top}-{bottom}); dropped, so its statement is lit")
                    del row["lines"]
                else:
                    corrections.append(f"{tie['id']}: lines {first}-{last} cut to {cut[0]}-{cut[1]}, "
                                       f"the extent of {declaration['name']}")
                    row["lines"] = cut


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("alignment", type=Path, help="the example's alignment directory")
    parser.add_argument("--paper", nargs="+", action="append", required=True,
                        metavar=("PAPER RETURN", "NAME"),
                        help="a paper, one return folder for it and, for a paper in several returns, the part's name")
    parser.add_argument("--lean-tree", type=Path, help="the vendored Lean (default: the example's upstream/lean)")
    args = parser.parse_args()
    index = load_index(args.lean_tree or args.alignment.resolve().parent / "upstream/lean")
    by_paper: dict[str, list] = {}
    for spec in args.paper:
        if len(spec) not in (2, 3):
            raise SystemExit("--paper takes PAPER RETURN [NAME]")
        by_paper.setdefault(spec[0], []).append((Path(spec[1]), spec[2] if len(spec) == 3 else None))
    titles_by_paper = {}
    for paper, returns in by_paper.items():
        several = len(returns) > 1
        if several and any(name is None for _, name in returns):
            raise SystemExit(f"{paper}: a paper in several returns needs a name for each part")
        parts, ties, removed, corrections = [], [], [], []
        for number, (folder, name) in enumerate(returns, 1):
            part, rows, gone, written = part_of(folder, name, f"p{number}-" if several else "")
            if written != paper:
                raise SystemExit(f"{folder}: a return for {written}, not {paper}")
            correct(rows, part, index, corrections)
            parts.append(part)
            ties.extend(rows)
            removed.extend(gone)
        parts.sort(key=lambda p: p["lines"][0])
        for part in parts:
            part["titles"] = dict(sorted(part["titles"].items()))
            part["notes"] = dict(sorted(part["notes"].items()))
        out = {"schema": SCHEMA, "paper": paper,
               "meaning": "Each tie names the phrase of the paper that a Lean declaration states, as an AI agent "
                          "read them side by side. Titles, reading notes, topics and comparisons are AI-drafted; "
                          "no mathematician has reviewed them.",
               "parts": parts, "corrections": corrections, "ties": ties, "removed": removed}
        path = args.alignment / f"phrases-{paper}.json"
        path.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        merged = {}
        for part in parts:
            for key, title in part["titles"].items():
                merged.setdefault(key, title)
        titles_by_paper[paper] = merged
        print(f"{path}: {len(ties)} ties in {len(parts)} part(s), {len(removed)} seed ties removed, "
              f"{len(corrections)} pointers corrected")
        for line in corrections:
            print("  ", line)
    names_path = args.alignment / "names.json"
    names = json.loads(names_path.read_text(encoding="utf-8")) if names_path.exists() else {"schema": 1, "names": {}}
    before = dict(names["names"])
    for paper in PRIORITY:
        names["names"].update(titles_by_paper.get(paper, {}))
    names["names"] = dict(sorted(names["names"].items()))
    names_path.write_text(json.dumps(names, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    changed = sum(1 for k, v in names["names"].items() if before.get(k) != v)
    print(f"{names_path}: {len(names['names'])} titles, {changed} new or changed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
