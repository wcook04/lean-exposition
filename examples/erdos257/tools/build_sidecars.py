#!/usr/bin/env python3
"""Write the three paper mappings (artifact schema 1.2) for the #257 reader copies.

Reads papers/erdos257/<stage>/{*.md, passages.json} (written by the paper copy
step) and examples/erdos257/evidence-graph.json. A passage's claim ids are the
graph records whose anchors lie inside it (passages.json `results`) plus the
authored step records placed in that passage below. Hashes are computed as
contracts.validate_artifact checks them. Rerunning on the same bytes gives the
same files.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from lean_exposition.contracts import closure, required_citation_ids

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
GRAPH = HERE / "evidence-graph.json"
STAGES = {"short": ("short/paper.md", "short/correspondence.json"),
          "long": ("long/reasoning-record.md", "long/reasoning-record.json"),
          "expository": ("expository/main.md", "expository/correspondence.json")}
GOALS = {"short": ["short.res-mixed-supports", "short.res-weighted-support", "short.thm-variable-fractional-cover",
                   "short.res-reciprocal-support", "short.res-period"],
         "long": ["short.res-mixed-supports", "short.thm-variable-fractional-cover"],
         "expository": ["exp.thm-main"]}
# Authored records, by the passage (section) of their paper that states them.
PLACED = {
    "short": {
        "sec:problem": ["step.displacement_identity", "step.positive_displacement", "step.rational_gap",
                        "lit.erdos1948", "lit.erdos1968"],
        "sec:eight-return-extensions": ["step.orbit_bound", "step.outer_bound", "step.dyadic_estimate",
                                        "step.choice_of_modulus", "step.combined_bound", "step.weighted_base_monotone"],
        "sec:common-kernel": ["step.incidence", "step.cover_condition", "step.kernel_estimate", "step.subadditivity",
                              "step.tail_displacement", "step.base_comparison", "step.cover_allocation"],
        "sec:mixed": ["step.common_distribution"],
        "sec:comparison": ["step.log_obstruction", "step.construction_weighted_not_cover",
                           "step.construction_cover_not_weighted", "open.cor52_lean"],
        "sec:map": ["step.full_support_limit", "step.primes_limit", "context.sufficient_not_necessary",
                    "lit.tao_teravainen", "lit.duverney_tachiya", "lit.erdos1975"],
        "sec:reciprocal-support": ["step.gcd_orbit_mean", "step.dominated_convergence", "step.lcm_limit"],
        "sec:period": ["step.unique_valuation"],
        "sec:rational-membership": ["open.half_and_twenty_first"],
        "app:elementary-details": ["step.cyclotomic_prime_power"],
    },
    "expository": {
        "sec:test": ["exp.step.gap"],
        "sec:split": ["exp.step.fractional_part", "exp.step.split"],
        "sec:general": ["exp.step.average", "exp.step.cycle_bound", "exp.step.uniform_bound"],
        "sec:proof": ["exp.step.explicit_choices"],
    },
    "long": {},
}
LABEL_RECORD = {("short", "res:problem"): "problem.erdos257", ("expository", "thm:main"): "exp.thm-main"}
REVIEW = ["AI-transcribed from the pinned papers; no independent review of the mapping.",
          "Claim ids of a passage are the records whose anchors lie inside it, from passages.json, plus the "
          "argument steps the AI author placed in that section (examples/erdos257/tools/build_sidecars.py)."]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--papers", type=Path, default=ROOT / "papers/erdos257",
                        help="folder holding short/, long/ and expository/ (default: papers/erdos257)")
    args = parser.parse_args()
    graph_bytes = GRAPH.read_bytes()
    graph = json.loads(graph_bytes)
    nodes = {n["id"]: n for n in graph["nodes"]}
    status = json.loads((HERE / "authored/evidence-status.json").read_text())["records"]
    for rid, entries in status.items():
        for e in entries:
            LABEL_RECORD[(e["paper"], e["label"])] = rid
    for rid in nodes:
        if rid.startswith("short.prob-"):
            LABEL_RECORD[("short", "prob:" + rid[len("short.prob-"):])] = rid
    report = {}
    for stage, (md, out) in STAGES.items():
        folder = args.papers
        content = (folder / md).read_bytes()
        text = content.decode("utf-8")
        listed = json.loads((folder / stage / "passages.json").read_text())
        passages, claims, unknown = [], [], []
        for p in listed:
            ids = [LABEL_RECORD[(stage, label)] for label in p["results"] if (stage, label) in LABEL_RECORD]
            unknown += [label for label in p["results"] if (stage, label) not in LABEL_RECORD]
            # Passage names may be the TeX labels or the same with ':' written as '-'.
            ids += PLACED[stage].get(p["name"], PLACED[stage].get(p["name"].replace("-", ":", 1), []))
            ids = list(dict.fromkeys(ids))
            marker, end = f"<!-- passage:{p['name']} -->", f"<!-- /passage:{p['name']} -->"
            start, stop = text.index(marker) + len(marker), text.index(end)
            statuses = {nodes[i]["status"] for i in ids}
            evidence_class = ("context" if not ids else
                              "open_question" if statuses == {"open"} else "source_argument")
            passages.append({
                "anchor": p["name"], "text_sha256": sha(text[start:stop].encode("utf-8")),
                "claim_ids": ids, "citation_ids": sorted(required_citation_ids(graph, ids)),
                "assumption_ids": [], "evidence_class": evidence_class,
                "rationale": (f"{p['heading']}: " + ("states or proves the listed records; the papers' own "
                              "statements are not Lean checks in this edition." if ids else
                              "context with no mapped record."))})
            claims += ids
        claims = list(dict.fromkeys(GOALS[stage] + claims))
        roots = claims
        required = closure(graph, roots)
        artifact = {
            "schema_version": "1.2", "stage": stage, "state": "draft", "path": f"papers/{stage}.md",
            "content_sha256": sha(content), "graph_sha256": sha(graph_bytes),
            "selected_goal_ids": GOALS[stage], "claim_ids": claims,
            "citation_ids": sorted(required_citation_ids(graph, roots) | {c for p in passages for c in p["citation_ids"]}),
            "assumption_ids": [],
            "unresolved_ids": sorted(n for n in required if nodes[n]["status"] in {"open", "unverified", "external", "conditional"}),
            "passages": passages, "review_state": "not_reviewed", "review_notes": REVIEW,
        }
        (folder / out).write_text(json.dumps(artifact, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        report[stage] = {"passages": len(passages), "claims": len(claims), "unknown_labels": unknown,
                         "unplaced_goals": [g for g in GOALS[stage] if g not in {c for p in passages for c in p["claim_ids"]}]}
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
