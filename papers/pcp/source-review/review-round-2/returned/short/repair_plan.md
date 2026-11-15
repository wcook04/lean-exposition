# Repair plan for author adjudication

All recommendations are **proposed**, not incorporated. The original findings remain in findings.json; this plan orders their resolution. The primary target is the specialist paper. Changes to the long account and worked exposition are dependency checks or specific local repairs, not permission to rewrite unreviewed sections. No source manuscript or live site was changed during this review.

## 1. Correct the small factual and attribution statements

Apply FA01, FA02, LIT-01 and LIT-03 before stylistic revisions. In short §7, line 393, name the finite multi-stack FinTM2 compilation target; retain the separate connection to reference NP. In the short resource paragraph, line 376, say “at most 187” and identify the unamplified verifier. Make the same bound wording change at long line 1409; long line 1687 already describes FinTM2 correctly. Inspect the exposition's corresponding resource paragraph (sampled lines 942–1002) for the same exact-versus-upper-bound wording, without assuming an error there.

At short line 413, replace blanket origin credit for both encodings by credit for the construction and its set-multilinear inverse-Kronecker variant, while identifying low-degree Hadamard encoding as established. Retain Lee's formalization and correction credit, Cook's AI-assistance disclosure, and the absence of a new PCP theorem. In short line 174, restore Kaufman–Sudan's word “formal”. Check parallel credit sentences in both companions against the supplied v2 introduction before editing them. R10 and R12 are ready replacements.

**Validation:** compare the revised sentences to Machine.lean, the query-bound definitions and the exact v2 source locators. No new mathematics or Lean proof change is called for. Record an author disposition for each finding rather than marking the entire review accepted.

## 2. Establish the reader's object and resource map

Use R01 and R11 for the opening. Keep the exact theorem unchanged. Explain the proof-size/randomness problem with direct coefficient-vector encoding before introducing the two-stage construction. Introduce the four primary received tables and their intended roles near the end of §2 (line 78), with their four auxiliary line tables; defer fully symbolic label domains until §3 has defined them. R07 can supply the inventory and the corrected §6 operational notation. Avoid maintaining two competing inventories.

State that an arbitrary received table is not presumed to be an encoding. Keep Q independent of P until the difference test proves the identity. At equation (17), use received bits w_Q((x,y),L), w_P(x,L), w_P(y,L), with any reader notation mapped to the formal query addresses. In the proof, choose P,Q,M_A,M_B once. Auxiliary row decodings used in local correction need not be a single globally unique family.

**Dependencies:** the short introduction, §2 ending, §3 label definitions and §6 opening must agree. The corresponding long sections “The eight tables and seven checks” (line 1370 onward) and “Soundness of the seven-check verifier” (1432 onward) provide destinations and comparison material. The worked exposition may already supply illustrative examples; check those passages before adding an additional example there.

**Validation:** ask a reader to identify a physical query address and its stored bit, and to distinguish honest, received and decoded objects at equation (17). This is a proposed acceptance exercise, not a completed human test.

## 3. Repair the proof interfaces before shortening prose

Apply R02 and R09 to short §4: add the affine-consistency deduction for the same decoded field value and the pointwise weighted prediction estimate. Preserve the good-row/bad-row argument and the unconditional Kκ conclusion. Split the row-structure proof from the two-domain estimate; split the point-line theorem statement from its history and proof sketch.

Apply R03–R06 to short §§4–5. Give the actual three-part outer experiment, the per-target correction experiment, the averaged binary root inequality, and the ZERO equalities with shared x,L. Retain zero directions where the formal algorithms allow them, nonzero z in the correction analysis, the same inner correction direction used for the two corrected values, independent tester seeds, and conjunctive acceptance. Keep the correction failure event rejection **or** wrong output. Do not strengthen it to every fixed label or to arbitrary advice with no rejection loss.

**Mathematical adjudication required:** compare the proposed prose against the existing algorithm sample types and theorem contracts. The replacements explain current proofs but are new prose and should not be declared kernel-checked. Confirm the three weighted error losses, both uses of the same decoded value, and the coupling of actual fresh-mask reads. None of these changes should alter any theorem statement, source hypothesis or constant.

**Companion destinations:** weighted proof at long §2 (194–345); Hadamard testing at 868–990; outer testing at 1077–1134; outer correction at 1135–1183; ZERO at 1184–1255; randomized derived reads at 1256–1299. Keep these full arguments as proof destinations. Only correct a companion if comparison identifies a concrete inconsistency; the short paper need not duplicate every lemma.

## 4. Rebalance and render the specialist account

Fund the added explanation primarily from the resource ledger. Keep the parameter choices (21), logarithmic-address reasoning and the labelled seven query bounds. R08 names the branch order P,M_A,Q,M_B,vertex ZERO,edge ZERO,difference and identifies δ=g₄/16. The large decimal randomness and proof-length bounds at short lines 376–389 can move to or be consolidated with long “Parameters for every finite graph” (1520–1569), “From finite samples to fair random bits” (1570–1648), and “Repetition on one fixed proof” (1649–1683), where their detailed budgets already belong. Verify that every unique bound remains there; do not silently delete a number solely because it is large.

Keep the definition and role of the small positive gap in §6. If equation (20)'s full minimum moves, retain enough local inequalities to show the two contradictions and a precise destination in long “Soundness of the seven-check verifier” (1432–1519). Prefer moving the decimal evaluations first: the symbolic soundness budget currently makes the common-decoding proof inspectable.

The page-share table in review.md is an editorial target, not a fixed page limit. Reflow the PDF and inspect every page. Keep the point-line theorem, its conditions and equation (13) together across the current pages 6–7; preserve punctuation and formula numbering. Retain all nine bibliography entries and explicit source versions. Do not shorten necessary negative statements such as the lack of a small-rejection premise or the absence of an auxiliary-proximity assumption.

**Validation:** read the revised short account from the opening through the seven-check conclusion without the companion, recording exactly which imported theorem is needed. Confirm every altered display, source association, query bound and cross-reference after reflow. A source build and reader checks, if run later, must be recorded as later checks rather than attributed to this review.

## 5. Repair the reader journey and evidence entry points

Fix the section-route generation or router interpretation responsible for the double-hash URL reached by “full weighted argument” at short line 174. The expected behavior is the correct long paper at “The corrected short low-degree test”. This review intentionally does not invent an unverified replacement URL syntax. Verify source link → target heading → return to the original passage. Inspect the other companion section links sharing that static pattern; only the weighted link was actually clicked and observed failing here. Preserve the working plain companion route and the packaged PDF destinations.

Add an ordinary link or selected association at equation (16) to `PCP.Algebraic.DerivedZeroOnGrid.rejectionRate_lower_bound`, DerivedZeroOnGridSoundness.lean 246–277 (signature 246–264). Keep the base ZERO link for (15). Expose `PCP.ReferenceNP.inNP_iff_mem` as a prerequisite near the headline theorem; it is already correctly linked in the credits. Do not advertise either addition as an independently compiled new graph unless extraction/elaboration is actually rerun and succeeds.

**Validation:** reproduce the live weighted-link failure before the fix, then demonstrate the working journey afterward. Confirm all twelve existing associations still select the intended source propositions. If the contents panel is compacted, test the normal desktop route and a narrow viewport; its current size is an optional design finding, not a blocker of the mathematical account.

## Deliberate non-changes and closure

Do not optimize constants, replace the construction, launch a new research programme, remove the K₄ example, expand the historical counterexample into a claimed verifier attack, or recast ordinary source inspection as a new formal proof. Do not rewrite the long account or exposition wholesale on the strength of this specialist review. Do not add a new production system or outside reviewer gate. The existing author can adjudicate every finding as incorporated, superseded, rejected with reason or deferred.

The short-paper release decision should follow completed source-consistent repairs, rendered inspection and working proof-navigation links. The long record remains a sampled supporting proof source pending any separate full review. The exposition remains outside this review's full assessment. These are separate dispositions, not a single approval of all three papers.
