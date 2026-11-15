# Independent algebra chapter review

Reviewed `work/pcp-chapters/algebra.md` at SHA-256 `a5378c365384c9c2cc73d179374d92d6aea2572e598df347b7772d5398e33705`. The checkout HEAD differs from the specified pin a0ce13ed0fa264f051c1278e039596ce65557fa4, but both `git diff --name-only <pin> HEAD -- PCP/Algebraic` and `git status --short -- PCP/Algebraic` were empty: the inspected source files therefore match tracked pinned bytes. This is a selective ordinary-mathematics/source review, not a build or exhaustive independent verification. The chapter was still being edited; recheck its final hash.

## Finding

**Crossing lemma omits field-size and degree hypotheses.** At `pcp-long-algebra-crossing` the stated assumptions are small row/column errors, ε≤1/100, and (A26). The proof then invokes the bivariate agreement theorem, whose stated hypotheses additionally include d>0 and q≥1000d³. Those do not follow from (A26). The nearest and candidate crossing theorems in `PCP/Algebraic/BivariateCrossingSoundness.lean:32–44` and `CandidateCrossing.lean:27–39` explicitly require `0 < d` and `1000*d^3 ≤ card F`. Add those assumptions at the crossing statement; the subsequent point-line proof has them via its d>0 branch and (A22). The d=0 case is handled separately later. Author and parent notified.

Minor wording: in `pcp-long-algebra-ruled-surface`, “Independently, (A28) gives” can be read as statistical independence of events, although the next step uses only a union bound. Replace with “Separately” or “Also”; no probabilistic independence is needed.

## Checked transitions

- Grid interpolation has individual degree ≤h−1, while line characterization uses total degree. In the latter the slice interpolant has total degree ≤2d, and q>2d makes the homogeneous-component argument valid; no unsupported identification of arbitrary polynomial functions is needed.
- Weighted-grid sampling uses nonzero nodes to make each sampled constraint uniformly distributed; symmetry gives the `2nδ` fixed-center prediction bound and the three comparison costs yield `(2n²+3n)δ<1`. Plurality gives Δ(f,g)≤2δ. The generator-based exact characterization and q>2c are tied to the correct weighted test (`WeightedConstraintSoundness.lean`, `GeneratorLowDegreeTest.lean`; corrected v2 Fact 2.7 and Lemma 3.3).
- Bivariate proof: `10d` selected columns, e-mean≤d, nonzero specialized kernel on ≥q/2 rows, bounded-degree polynomial kernel via minors, exclusion of E=0, and removal of at most `(d+1)(5d+1)d≤q/10` rows all follow from stated q bound. The clean rectangle gives ≤ε+1/9; the transverse counting estimate then gives at most 3ε discrepant rows and total distance ≤4ε. This matches the mechanisms in `BivariateAgreement.lean`, `PolynomialMatrixKernel.lean`, `BerlekampWelchCertificate.lean`, `BivariateCleanRectangle.lean`, `BivariateAgreementFromRectangle.lean`, and `BivariateAgreementBoost.lean`. No bivariate total-degree≤d claim is made.
- For the nearest-line fixed-parameter bound, uniqueness on errors <1/3 when q≥3d justifies transporting the chosen minimizer under shifts; tied bad lines are charged separately. Point-line correction averages all field parameters, unlike paper's nonzero-parameter version. Explicit `fieldFactor=1000000`, `smallError=1/4000000` agree with `PointLineConstants.lean`.
- Mixed-plane proof uses four mean error bounds and a union bound, with explicit exceptional parameter slices; the plurality step justifies the factor two. Ruled-surface construction fixes Q once per target line, not once per parameter; five error means and Markov allow a witness for each parameter, and fixed Q then gives the exact line. The numeric budget B≤0.00480425 and B/0.01+γ≤0.482025 checks arithmetically. Exact lines imply total degree via the earlier q>2d lemma. Compare `MixedPlaneSampling.lean`, `PointLineEndpointConsistency.lean`, `RuledSurfaceSampling.lean`, `RuledSurfaceRigidity.lean`.
- Local correction at a fixed center uses only uniformity of each queried point and a union bound; the line-table bound concerns accepted wrong outputs, not rejection probability or arbitrary-table completeness. The separate degree-zero point-line proof uses an invertible pair transformation and has no cubic field-size demand.

## Review limits

Inspected the chapter's mathematical chain and selected named formal statements and bodies, plus corrected-paper statements and relevant Arora–Safra/ALMSS acquisition notes. Did not replay Lean, audit every helper, prove freshness of other chapters, or reproduce all matrix formalization details. The counterexample was reviewed separately and is not reconsidered here. Chapter references to external work are attribution/source relationships, not a claim that the exact explicit constants or proof choices appear verbatim there.

## Recheck of final author revision

Rechecked final `algebra.md` SHA-256 `5d22ab32ab81f127bb8e13a63d746948cb894f6f294f8fabee1198598c08c093`. The crossing statement now explicitly assumes d>0 and q≥1000d³, and the ruled-surface wording uses “Separately.” Both findings are resolved. This recheck covers those revisions only; review limits above remain.
