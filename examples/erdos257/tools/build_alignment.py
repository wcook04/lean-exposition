#!/usr/bin/env python3
"""Write examples/erdos257/alignment/*.json mechanically from the evidence mapping.

For every result record of the graph that the evidence mapping covers, one batch
row: its Lean declarations (relation and fidelity from the mapping's lean.status
and relation_note) and its statement in each paper, located by the result's
anchor `<a id="LABEL"></a>` in the reader copy of the paper. Rows whose relation
needed a judgement beyond the mapping's own status carry fidelity_source "ai".

The relation for an exact_or_stronger result is chosen by rule from the
relation note (see `classify`) and recorded with fidelity_source "ai"; the rule
is printed with every run so it can be checked against the notes.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PAPERS = {"short": ROOT / "papers/erdos257/short/paper.md", "long": ROOT / "papers/erdos257/long/reasoning-record.md"}
MAX_SLICE = 1800
# Phrases in a relation note that say the Lean statement says more than the print.
WIDER = re.compile(r"\b(stronger|more general|adds|also (proves|gives|states)|every (integer )?base|"
                   r"arbitrary|for all|any finite|without (the|its) hypothesis|drops? the|weaker hypothes)",
                   re.I)


def words(text: str, limit: int = 25) -> str:
    text = re.sub(r"\s+", " ", re.sub(r"`", "", text or "")).strip()
    first = re.split(r"(?<=[.;])\s", text)[0]
    parts = first.split()
    return " ".join(parts[:limit]) if len(parts) <= limit else " ".join(parts[:limit - 1]) + " …"


_P = "An AI agent read the two statements side by side. "
# (label, last segment of the declaration name) -> (relation, fidelity, fidelity_note), written by
# reading the printed statement and the Lean statement side by side.
READ = {
    ("res:weighted-support", "divisibilityWeightedClaim"): ("part", "same", "States the fixed-base irrationality and the all-base hereditary clause under (W), with the paper's A ⊆ ℕ>0 written as 0 ∉ A."),
    ("res:weighted-support", "finitePrimeWeighted_fixedBase_hereditary"): ("part", "same", "States heredity of the fixed-base conclusion: every infinite subset of a support satisfying (1) at base b."),
    ("thm:257-weighted", "divisibilityWeightedClaim"): ("part", "stronger", "States the fixed-base irrationality and adds a second conjunct, all-base irrationality for every infinite subset under the base-two condition, which this statement does not print."),
    ("thm:257-weighted", "weighted_displacement_cofinal_close_return"): ("part", "same", "States the 'more precisely' clause: for every ε > 0 and N some m ≥ N has a displacement at m strictly between 0 and ε."),
    ("thm:variable-fractional-cover", "strengthenedPositiveCoverClaim"): ("states", "same", "Same hypotheses and conclusion, with the cover index starting at 0. The mapping records this result as exact for the short paper but exact_or_stronger for long Theorem 1.3."),
    ("thm:257-variable-fractional-cover", "strengthenedPositiveCoverClaim"): ("states", "same", "Same hypotheses and conclusion, with the cover index starting at 0. The mapping records this result as exact for the short paper but exact_or_stronger for long Theorem 1.3."),
    ("res:mixed-supports", "mixedSupportClaim"): ("part", "weaker", "Only the case of a cover satisfying (V), its index starting at 0; the positive-weight variant the theorem also allows is arbitraryWeightMixedSupport_allBase_hereditary. Stated with the paper's E ⊆ ℕ>0 written as 0 ∉ E."),
    ("res:mixed-supports", "arbitraryWeightMixedSupport_allBase_hereditary"): ("part", "same", "The positive-weight variant of the cover condition, with weights η_j > 0 summing to 1."),
    ("thm:257-mixed-supports", "mixedSupportClaim"): ("part", "same", "The case of a cover satisfying (14), its index starting at 0, with the paper's E ⊆ ℕ>0 written as 0 ∉ E."),
    ("thm:257-mixed-supports", "arbitraryWeightMixedSupport_allBase_hereditary"): ("part", "same", "The positive-weight variant of the cover condition, with weights η_j > 0 summing to 1."),
    ("res:weighted-cover-incomparability", "exists_weighted_not_strengthened_host"): ("part", "stronger", "Gives the support E, and adds divergent reciprocals, no weighted log-budget cover and irrationality for every infinite subset."),
    ("res:weighted-cover-incomparability", "exists_strengthened_not_old_or_weighted_host"): ("part", "stronger", "Gives the support V with divergent reciprocals, and adds squarefree elements, no cover of the older kind and irrationality for every infinite subset."),
    ("res:reciprocal-support", "irrational_erdosSupportSeries_of_summable_reciprocal"): ("contains", "stronger", "The Lean set A may contain 0; the exponent 0 contributes 0 to both sums, so the printed theorem is the case 0 ∉ A."),
    ("res:period", "coprime_base_den_finiteErdosSum"): ("part", "stronger", "Coprimality of D_F and b, proved without assuming F nonempty."),
    ("res:period", "finite_period_noncollapse_rat_den"): ("part", "same", "The multiplicative order of b modulo the reduced denominator of the finite sum equals lcm(F), with the paper's F ⊆ ℕ>0 written as 0 ∉ F."),
    ("res:period", "lcm_lt_den_finiteErdosSum"): ("part", "same", "lcm(F) < D_F when lcm(F) ≥ 2."),
    ("res:one-over-twenty-one-frontier", "one_div_twenty_one_mem_iff_not_fatalAlignedBranch"): ("part", "same", "Item 1 as printed."),
    ("res:one-over-twenty-one-frontier", "twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows"): ("part", "same", "Turns ranks with s_R ≤ 2^R into the decay hypothesis of the next declaration."),
    ("res:one-over-twenty-one-frontier", "one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay"): ("part", "stronger", "Concludes 1/21 ∈ 𝒜 from decay of (s(R) + 2R + 1)/4^R along some ranks, a weaker hypothesis than item 2's."),
    ("res:one-over-twenty-one-frontier", "twentyOneFatalAlignedBranch_eventually_strict_supercapacity"): ("part", "same", "Item 3, first clause: eventually s_R > 2^R."),
    ("res:one-over-twenty-one-frontier", "twentyOneFatalAlignedBranch_eventually_affine_supercapacity"): ("part", "same", "Item 3, the support step and the recurrence, written with natural-number subtraction, which agrees because s(R+1) > 2^(R+1) for large R."),
    ("res:terminalhalf", "paper_terminalhalf_iff"): ("contains", "stronger", "An equivalence: its right-to-left direction is the theorem, and Lean also proves the converse."),
    ("res:cylinderhalf", "exists_infinite_positive_support_half_of_cofinalCylinderStages"): ("states", "same", "Same hypothesis and conclusion, with the paper's A ⊆ ℕ>0 written as 0 ∉ A."),
}


def classify(row: dict) -> list[dict]:
    lean = row["lean"]
    decls = lean["declarations"]
    note = lean.get("relation_note") or ""
    out = []
    for d in decls:
        entry = {"file": d["path"].removeprefix("lean/"), "name": d["name"]}
        read = READ.get((row["label"], d["name"].rsplit(".", 1)[-1]))
        if read is not None:
            relation, fidelity, text = read
            entry.update(relation=relation, fidelity=fidelity, fidelity_source="ai", fidelity_note=_P + text,
                         note=("The papers' evidence record marks this pair " + {"exact": "exact", "exact_or_stronger": "exact or stronger"}.get(lean["status"], lean["status"]) + "."))
        elif lean["status"] == "exact":
            entry.update(relation="states", fidelity="same", fidelity_source="recorded",
                         note="Evidence mapping: the Lean statement is exactly the printed one.")
        else:  # classified from the recorded note, not from a fresh reading of both statements
            wider = bool(WIDER.search(note))
            relation = "part" if len(decls) > 1 else "contains" if wider else "states"
            entry.update(relation=relation, fidelity="stronger" if wider else "same", fidelity_source="ai",
                         note=("Evidence mapping: exact_or_stronger. Fidelity classified by rule from the recorded note."
                               if len(decls) == 1 else
                               f"One of {len(decls)} declarations that together state the result; fidelity classified from the recorded note."),
                         fidelity_note=re.sub(r"\s+", " ", note).strip())
        unfolds = d.get("unfolds") or []
        if len(unfolds) == 1 and ":=" in (unfolds[0].get("text") or ""):
            body = unfolds[0]["text"].split(":=", 1)[1].strip()
            entry.update(clause=body, clause_file=unfolds[0]["path"].removeprefix("lean/"),
                         clause_name=unfolds[0]["name"])
        out.append(entry)
    return out


def locate(text: str, label: str):
    """(from, to) for the result whose anchor is LABEL, or None with a reason."""
    anchor = f'<a id="{label}"></a>'
    at = text.find(anchor)
    if at < 0 or text.find(anchor, at + 1) >= 0:
        return None, "anchor missing or repeated"
    head = re.compile(r"\*\*[^*\n]+?\*\*").search(text, at)
    if head is None:
        return None, "no bold heading after the anchor"
    start = head.start()
    # The statement is italic: it ends at the first line outside a display that
    # closes a sentence and the italics (".*"), or, for a statement that ends in a
    # display, at the last display before a paragraph that is not italic.
    pos, in_math, end, last_display_end, blank = head.start(), False, None, None, False
    for line in text[head.start():].split("\n"):
        stripped = line.rstrip()
        if not in_math and blank and stripped and (not stripped.startswith(("*", "$$", "<a id="))
                                                   or stripped.startswith(("*Proof", "**"))):
            end = last_display_end
            break
        if stripped.strip() == "$$":
            in_math = not in_math
            if not in_math:
                last_display_end = pos + len(stripped)
        if not in_math and re.search(r"[.?]\*\)?$", stripped):
            end = pos + len(stripped)
            break
        blank = stripped == "" if not in_math else blank
        pos += len(line) + 1
    if end is None or end - start > MAX_SLICE:  # the heading alone, when no end is found or the slice is too long
        end = head.end()
    block = text[start:end].rstrip()
    frm = head.group(0)
    tail = block[-60:] if len(block) > len(frm) else frm
    tail = tail[tail.find(" ") + 1:] if " " in tail[:-1] and len(block) > len(frm) else tail
    return (frm, tail.lstrip()), None


# Authored step records (origin "ai"): where each paper states the step. A
# tagged display is located after its anchor; other steps by a quoted sentence.
# No Lean declaration was matched to a step by reading both, so every step row
# has "lean": [] and says so.
STEP_SPANS = {
    "short": {
        "step.displacement_identity": ("eq:intro-displacement", "D"),
        "step.orbit_bound": ("eq:weighted-finite-orbit", "2"),
        "step.outer_bound": ("eq:weighted-outer-short", "3"),
        "step.dyadic_estimate": ("eq:weighted-dyadic-short", "4"),
        "step.combined_bound": ("eq:weighted-main-bound", "5"),
        "step.incidence": ("eq:incidence", "6"),
        "step.cover_condition": ("eq:strengthened-cover", "V"),
        "step.kernel_estimate": ("eq:mixed-finite-kernel", "S"),
        "step.log_obstruction": ("eq:cover-log-obstruction", "7"),
        "step.gcd_orbit_mean": ("eq:gcd-orbit-mean", "8"),
        "step.lcm_limit": ("eq:lcm-prefix-orbit-limit", "9"),
        "step.positive_displacement": ("and for infinite $A$ the displacement", "exceeds $N$."),
        "step.rational_gap": ("Hence, if $X_A(b)=p/q$", "It therefore suffices to find displacements tending to zero."),
        "step.weighted_base_monotone": ("Finally, $W_{b,P}(A)\\le W_{2,P}(A)$", "pass to a subset."),
        "step.tail_displacement": ("For the displacement itself, the geometric-series identity gives", "\\le U_j(N).\n$$"),
        "step.base_comparison": ("To pass to larger bases, note that", "for every real $b\\ge2$"),
        "context.sufficient_not_necessary": ("All three criteria are sufficient conditions;", "characterises the supports in Problem"),
    },
    "expository": {
        "exp.step.gap": ("eq:goal", "1"),
        "exp.step.fractional_part": ("eq:fracpart-main", "2"),
        "exp.step.split": ("eq:split-main", "3"),
        "exp.step.average": ("eq:average-main", "4"),
        "exp.step.cycle_bound": ("eq:cycle-main", "5"),
        "exp.step.uniform_bound": ("eq:uniform-main", "6"),
    },
}


RS = "Erdos249257/ReciprocalSupportIrrationality.lean"
# Lean for a step, found by reading the Lean proof of Theorem A.1
# (AllBaseReciprocalSupportIrrationality.lean and the binary file it imports).
STEP_LEAN = {
    "step.gcd_orbit_mean": [
        {"file": RS, "name": "Erdos249257.tendsto_cesaroMean_shiftedMersenneAtom_mul", "relation": "part",
         "note": "Base two: the Cesàro mean along multiples of Q tends to the gcd-orbit mean.",
         "fidelity": "weaker", "fidelity_source": "ai",
         "fidelity_note": "Lean proves the base-two case only; the Lean proof of Theorem A.1 reaches other bases by bounding each base-b displacement by twice the binary one."},
        {"file": RS, "name": "Erdos249257.shiftedMersenneOrbitMean_le_reciprocal", "relation": "part",
         "note": "The bound of (8): the orbit mean is at most 1/d.", "fidelity": "weaker", "fidelity_source": "ai",
         "fidelity_note": "Base two only."}],
    "step.dominated_convergence": [
        {"file": RS, "name": "Erdos249257.tendsto_cesaroMean_tsum_shiftedSupportAtom_mul", "relation": "proof",
         "note": "Dominated convergence for a fixed step Q, at base two.", "fidelity": "weaker", "fidelity_source": "ai",
         "fidelity_note": "Base two only, and the Lean majorant is 2(Q+1)/d where the paper uses (Q+2)/d."}],
    "step.lcm_limit": [
        {"file": RS, "name": "Erdos249257.tendsto_tsum_shiftedSupportOrbitMean_periodLcm", "relation": "part",
         "note": "Along lcm-prefix moduli the orbit-mean sums tend to the zero-shift sum.", "fidelity": "weaker",
         "fidelity_source": "ai", "fidelity_note": "Base two only; the zero-shift support sum is X_A(2)."}],
}
NO_LEAN = {
    "short": "An AI agent placed this tie. The Lean proof of Theorem 1.2 (PaperCompleteR8/WeightedReturn.lean) runs through dyadic means and a mixed-gauge estimate; its lines were not matched to this step.",
    "expository": "An AI agent placed this tie. The exposition's finite argument is not checked line by line by the Lean proof (its Appendix A.6).",
}


# A step's tile title where cutting its label at six words leaves a dangling phrase or drops a
# symbol: one to six plain words, never stronger than the label.
SHORT_TITLES = {
    "step.positive_displacement": "Positive displacement for infinite support",
    "step.rational_gap": "Rationality forces displacements at least 1/q",
    "step.tail_displacement": "Cover displacement at most the tail",
    "step.base_comparison": "The base comparison",
    "exp.step.gap": "A rational's fixed positive gap",
    "exp.step.uniform_bound": "A bound for every attempt count",
}


def step_rows(misses: list) -> dict:
    graph = {n["id"]: n for n in json.loads((HERE / "evidence-graph.json").read_text())["nodes"]}
    texts = {"short": PAPERS["short"].read_text(encoding="utf-8"),
             "expository": (ROOT / "papers/erdos257/expository/main.md").read_text(encoding="utf-8")}
    rows = {}
    for paper, spans in STEP_SPANS.items():
        text = texts[paper]
        for rid, (first, second) in spans.items():
            item = {"paper": paper, "role": "statement", "origin": "ai"}
            if rid not in STEP_LEAN:
                item["note"] = NO_LEAN[paper]
            if first.startswith("eq:"):
                after = f'<a id="{first}"></a>'
                at = text.find(after)
                tag = re.compile(r"\\tag\{" + re.escape(second) + r"\}\s*\n\$\$")
                match = tag.search(text, at) if at >= 0 else None
                if match is None:
                    misses.append(f"{rid}: display {first} with tag ({second}) not found")
                    continue
                opening = text.find("$$\n", at)
                stop = opening + 3
                while True:  # the opening $$ and enough display lines to be unique after the anchor
                    stop = text.find("\n", stop + 1)
                    first_lines = text[opening:stop]
                    if text.find(first_lines, opening + 1) < 0 or stop >= match.start():
                        break
                item.update({"after": after, "from": first_lines, "to": match.group(0)})
            else:
                start = text.find(first)
                stop = text.find(second, start)
                if start < 0 or stop < 0 or text.count(first) != 1 or text[start:stop + len(second)].count("$$") % 2:
                    misses.append(f"{rid}: sentence not found once")
                    continue
                item.update({"from": first, "to": second})
            rows[rid] = {"short": SHORT_TITLES.get(rid) or " ".join(re.sub(r"\(.*?\)|[^A-Za-z0-9 /≤-]", "", graph[rid]["label"]).split()[:6]),
                         "lean": STEP_LEAN.get(rid, []), "statements": [item]}
    return rows


def main() -> None:
    export = Path("/Users/willcook/src/_builds/erdos257-reader/src/plectis-erdos")
    mapping = json.loads((export / "evidence/paper_evidence.json").read_text())
    papers = {p["paper_id"]: p for p in mapping["papers"]}
    status = json.loads((HERE / "authored/evidence-status.json").read_text())["records"]
    rows_by_label = {("short", r["label"]): r for r in papers["erdos-257-mersenne-support-subseries"]["results"]}
    rows_by_label.update({("long", r["label"]): r for r in papers["erdos257-mersenne-reasoning-surface"]["results"]})
    texts = {k: p.read_text(encoding="utf-8") for k, p in PAPERS.items()}
    records, misses, rule_rows = {}, [], {"recorded": 0, "ai": 0}
    for rid, entries in sorted(status.items()):
        lean, statements, seen = [], [], set()
        for entry in entries:
            row = rows_by_label[(entry["paper"], entry["label"])]
            for item in classify(row):
                key = (item["file"], item["name"])
                if key not in seen:
                    seen.add(key)
                    lean.append(item)
                    rule_rows[item["fidelity_source"]] += 1
            found, why = locate(texts[entry["paper"]], entry["label"])
            if found is None:
                misses.append(f"{rid} ({entry['paper']} {entry['label']}): {why}")
                continue
            frm, to = found
            statements.append({"paper": entry["paper"], "role": "statement", "from": frm, "to": to,
                               "origin": "evidence_record"})
        title = (entries[0]["title"] or "").strip().rstrip(".")
        short = " ".join(title.split()[:6]) or entries[0]["printed"]
        short = re.sub(r"\$[^$]*\$", "", short).strip() or entries[0]["printed"]
        records[rid] = {"short": short[0].upper() + short[1:], "lean": lean, "statements": statements}
    halves = {"m1-short-and-front.json": {}, "m2-long.json": {}}
    for rid, row in records.items():
        halves["m1-short-and-front.json" if rid.startswith("short.") else "m2-long.json"][rid] = row
    # The exposition has no evidence mapping: its Theorem 1 is tied by hand (origin "ai").
    exposition = (ROOT / "papers/erdos257/expository/main.md").read_text(encoding="utf-8")
    found, why = locate(exposition, "thm:main")
    if found is None:
        misses.append(f"exp.thm-main (expository thm:main): {why}")
    halves["a1-exposition.json"] = {"exp.thm-main": {
        "short": "Reciprocal-summable exponents, base two",
        "lean": [{"file": "Erdos249257/AllBaseReciprocalSupportIrrationality.lean",
                  "name": "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal",
                  "relation": "contains", "fidelity": "stronger", "fidelity_source": "ai",
                  "note": "States every integer base b ≥ 2; at b = 2 it is Theorem 1.",
                  "fidelity_note": ("Lean covers every integer base and A ⊆ ℕ, where exponent 0 contributes 0; "
                                    "the exposition's Appendix A.6 says so.")}],
        "statements": ([{"paper": "expository", "role": "statement", "from": found[0], "to": found[1],
                         "origin": "ai"}] if found else [])}}
    halves["a2-steps.json"] = step_rows(misses)
    out = HERE / "alignment"
    out.mkdir(exist_ok=True)
    for name, recs in halves.items():
        (out / name).write_text(json.dumps({"schema_version": "1.0",
                                            "provenance": "Generated by examples/erdos257/tools/build_alignment.py from evidence/paper_evidence.json",
                                            "records": recs}, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"records": len(records), "lean_rows": rule_rows, "statement_misses": misses}, indent=1))


if __name__ == "__main__":
    main()
