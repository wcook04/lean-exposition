# Final theorem chapter: independent mathematical review

Reviewed snapshot SHA-256 `3927de614400080f2fa4a0fe051c68ac30366148b21750130bf95d7eeab120a3` (the chapter was live and may have changed since). The requested checkout reports `a0ce13ed0fa264f051c1278e039596ce65557fa4`. `git diff --stat a0ce13ed -- PCP/Algebraic PCP/Complexity PCP/Reduction PCP/Theorem.lean PCP/ReverseConcrete.lean` in the accessible `tcs-pub` checkout returned no changes for those paths. No full build was run. Primary-paper comparison is to arXiv:2608.17429v2 §7 and Appendix E, with formal deviations explicitly identified.

## Actionable finding

1. **The constant literals in the 3-colouring gadget lack their graph representation** (snapshot lines 460–470). The reduction explicitly introduces `0` in the second NAE clause, and clause padding and relation values also introduce Boolean constants. The next paragraph constructs vertices only for variables and their negations, leaving the clause edges for constant literals unspecified. This is a missing construction step in an otherwise correct gadget, not a false equivalence. Fix: state that a constant `0` or `1` literal is represented by the corresponding palette vertex and the gadget triangle connects to that vertex. This matches `PCP/Reduction/NAEThreeColor.lean`, `Literal`, `literalVertex` and `direct` (roughly lines 71–104). Author notified.

## Source/link corrections

- `[lean-one-hot]` is used at line 443 but lacks a link definition in this snapshot. `PCP/Reduction/FiniteDomainBoolean.lean` or its actual imported finite-domain encoder should be verified and linked; the executable route is `FiniteDomainLang.lean` and `FiniteDomainGraphLang.lean`. (The source does use one-hot expansion.)
- `[lean-query-budget]` targets `ThreeColorVerifier.lean#L277`, within the branch congruence proof. The branch bounds are lines 319–326 and total bound at 362–368. Point the link at #L319 or #L362. This is a locator error, not an error in 187.

## Checked against proof bodies

- Characteristic-two cube-root difference and vertex condition are valid; the K4 example witnesses necessity of the vertex condition. Grid adjacency interpolation has degree at most `2d(h-1)` and the two constraints have degrees at most `3d(h-1)` and `5d(h-1)`.
- `ThreeColorVerifier.lean` lines 84–115 and 319–368 has the stated seven branches, eight physical tables, per-branch bounds and total `20c+107`; the `c=4` upper bound is 187. The line-encoded certificate used in ZERO is the same physical table. This is an upper bound, not a claim all executions read 187 distinct addresses.
- `ThreeColorDecodedSoundness.lean` lines 54–175 explicitly requires the full cubic proximity and homogeneous linear proximities, establishes the difference identity via the `κ+3ε` condition, and uses `5D` in both ZERO applications. Its bound includes `(1+2C_c)(κ+2ε)+2ε+5D/(Q−1)`, agreeing with the chapter. `ThreeColorSoundnessBudget.lean` definitions and proofs support the displayed gap/minimum and strict comparison. These are proof-body checks, not a new independent formal validation of their imported low-degree and ZERO theorems.
- `ThreeColorParameters.lean`, `ThreeColorSeedSize.lean`, `ThreeColorResourceBounds.lean` and `ThreeColorFullFieldSampling.lean` support the stated parameter family, exact seed exponent, four nonzero draws and retention factor, total query-space bound, and polynomial exponents. The capacity and elementary inequalities were checked algebraically. The factor `(Q−1)^4/Q^4` is exact because the valid raw seeds biject with the original seeds.
- `ReductionResources.lean` lines 24–79 proves the exact source-budget formulas and polynomial composition; padding preserves the finite uniform distribution. Fixed-proof-before-seeds order and repeated same-oracle probability are correctly stated. Reverse direction `ReverseConcrete.lean` invokes the certified finite-witness checker and `ReferenceNPConverse.lean` proves both model bridges; enumeration argument has the right polynomial seed count.
- `FiniteBooleanConstraints.lean` confirms the fixed-arity comparison chain and `2^k(3k+2)` clauses; `NAEThreeColor.lean` confirms OR-to-two-NAE and triangle gadgets. The chapter provides ordinary proofs for those reductions, but the missing constant-vertex mapping above should be added to make its graph construction complete.

## Scope

The runtime and NP-tableau sections summarize machine-compiler and finite-support arguments through their cited semantic and cost theorems; they do not reproduce those lower-level proofs. This review checked representative definitions and theorem bodies, not every dependency or executable build. If the requested chapter requires literally all machine-simulation derivations, those remain imported proof interfaces rather than independently expanded arguments. The author was asked to signal stabilization for a recheck.

## Recheck of final revision

Author-stabilized SHA-256 `2b631d1bcd117c38a41b4f20d8d510d0575b6c2168d214aa1a1f54efedf35937` verified. The NAE graph now explicitly maps constant literals to palette vertices; the one-hot link points to `FiniteDomainConstraints.lean#L119`, and query-list link to `ThreeColorVerifier.lean#L362`. All three identified issues are closed. No additional mathematical error found in the reviewed scope. The stated limitations concerning imported theorem interfaces, full build and uninspected dependencies remain.
