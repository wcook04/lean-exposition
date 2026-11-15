# Long reader algebra correspondence review

Read-only review of the eight `pcp-long-algebra-*` claims in `work/proof-reader/papers/pcp-full-argument/links.json`, the corresponding passage text in `work/lean-exposition/papers/pcp/long/reasoning-record.md`, and the actual Lean statements in the pinned checkout at revision `a0ce13ed0fa264f051c1278e039596ce65557fa4`. Locators below are relative to `PCP/Algebraic/`. This reviews source correspondence, not dependencies or a fresh kernel check.

## Corrections

- **claim-6, line-characterization:** `GeneratorLowDegreeTest.exists_close` is a different approximate-decoding theorem and does not state the exact-line characterization. Use `PCP.Algebraic.PolynomialLine.exists_polynomial_of_hasLowDegreeLines_finite`, `PolynomialLineCharacterization.lean:163`, or the corresponding iff theorem `hasLowDegreeLines_iff_exists_polynomial_finite` at line 184. The Fin-indexed version is at lines 104 and 154.
- **claim-5, grid-vanishing:** `GridVanishing.vanishesOn_iff_exists_decomposition`, `GridVanishing.lean:134`, matches the first part, including the decomposition; the marked passage additionally covers certificates and substitution degree. Add `PCP.Algebraic.GridVanishing.vanishesOn_iff_exists_certificate`, `VanishingCertificate.lean:119`, and `PCP.Algebraic.GridVanishing.totalDegree_substitute_coordinate_le`, line 142. The certificate converse and degree support are at lines 62 and 99.
- **claim-3, polynomial-distance:** `PCP.Algebraic.eval_distance_ge`, `PolynomialDistance.lean:49`, supports distance of distinct polynomials, but is an incomplete highlight for the marked passage. Add `eval_zero_agreement_le` at line 29, `eval_injective_of_totalDegree_lt_card` at line 73, and `eq_of_eval_close` at line 85 for the zero bound, injectivity, and uniqueness from proximity respectively.
- **claim-10, point-line statement:** `PCP.Algebraic.PointLineTest.exists_close_of_small_rejection` is the correct theorem, located in `PointLineSoundness.lean:58`, despite its namespace. The definition of the tested event and rejection rate is in `PointLineTest.lean:43,61`; include this source context if the lead otherwise only exposes the theorem.

## Corresponding main statements

- **claim-4:** `GridInterpolation.existsUnique_extension`, `GridInterpolation.lean:170`; individual and total degree bounds also appear at lines 90 and 100.
- **claim-7:** `StandardLocalCorrection.failure_le`, `StandardLocalCorrection.lean:63`; exact-polynomial success is `correct_eval` at line 52.
- **claim-8:** `LineTableLocalCorrection.correct_wrong_le`, `LineTableLocalCorrection.lean:249`.
- **claim-9:** `BivariateAgreement.exists_polynomial_of_row_column_agreement`, `BivariateAgreement.lean:141`.

The correction list was sent to the reader-repair agent. The mathematical preservation of the surrounding ordinary argument is assessed in the separate preservation review; this receipt makes no new claim about it.

## Complete intermediate-passage mapping

The earlier eight-claim audit omitted intermediate passage rows. Replace the downstream final-theorem fallback in each row below with its corresponding stage declarations. All IDs are prefixed `PCP.Algebraic.`; all 31 declarations below were found as nodes in `work/lean-exposition/examples/pcp/evidence-graph.json`. Source lines refer to `PCP/Algebraic/` in the pinned checkout.

| Passage suffix (`pcp-long-algebra-`) | Corresponding declaration IDs and source locators |
| --- | --- |
| generator-test | `GeneratorLowDegreeTest.check_eq_interpolation`, `nodes_injective`, `weights_ne_zero`, `polynomial_predict` — GeneratorLowDegreeTest.lean:55,84,93,125 |
| weighted-plurality | `WeightedConstraint.distance_correction_le`, `prediction_error_le`, `correction_satisfies` — WeightedConstraintSoundness.lean:38,130,136 |
| generator-soundness | `GeneratorLowDegreeTest.exists_close` — GeneratorLowDegreeTest.lean:274 (retain) |
| column-selection | `BivariateColumnSelection.mean_column_error_le`, `exists_good_columns` — BivariateColumnSelection.lean:85,94 |
| error-locator | `BerlekampWelchCertificate.exists_certificate_of_good_specializations` — BerlekampWelchCertificate.lean:237 |
| clean-rectangle | `BivariateCleanRectangle.certificate_row_eq`, `fraction_clean_rows_ge`, `exists_nonzero_columns` — BivariateCleanRectangle.lean:141,177,241 |
| coarse-agreement | `BivariateAgreementFromRectangle.exists_nearby_polynomial` — BivariateAgreementFromRectangle.lean:174 |
| agreement-boost | `BivariateAgreementBoost.transverse_error_le`, `distance_le_four_mul` — BivariateAgreementBoost.lean:70,105 |
| nearest-lines | `PointLineTest.distance_decoded_correction_le`, `Plurality.distance_le_twice_prediction_error` — PointLineCorrection.lean:142,71 |
| fixed-parameter | `PointLineTest.rejectionAt_le_four_mul` — PointLineParameterError.lean:151 |
| crossing | `BivariateCrossingSoundness.crossing_bestApproximation_eq` — BivariateCrossingSoundness.lean:32 |
| mixed-plane | `MixedPlaneSampling.expect_mixedRowError_le`, `expect_mixedColumnError_le`, `expect_mixedLocalColumnError_le`, `expect_mixedLocalRowError_decoded_le` — MixedPlaneSampling.lean:199,207,216,243; `PointLineEndpointConsistency.endpoint_error_le` — PointLineEndpointConsistency.lean:108 |
| ruled-surface | `RuledSurface.endpoint_error_le` — RuledSurfaceSampling.lean:253; `RuledSurface.hasLowDegreeLines_of_endpoint_bounds` — RuledSurfaceRigidity.lean:74 |
| point-line-constants | `PointLineConstants.field_bounds`, `rigidity_budget` — PointLineConstants.lean:32,62 |
| degree-zero | `PointLineTest.pairDisagreement_le_twice_rejectionRate_degree_zero`, `exists_close_degree_zero` — PointLineConstant.lean:145,160 |

The old-test counterexample is an ordinary explanatory derivation, not a Lean-checked declaration; it should not acquire a misleading formal fallback. Scope/introduction can remain unlinked. Existing theorem-statement and correction mappings are discussed above. The repair owners were sent these mappings. Final recheck is pending their regenerated reader.

## Repair recheck

Rechecked all algebra passage mappings in the updated canonical `work/lean-exposition/papers/pcp/long/reasoning-record.json`. The intermediate fallback replacements above are present; the mixed-plane row uses the endpoint theorem and two global expectation bounds, a useful subset of the proposed local nodes. The exact-line row uses the `Fin`-indexed theorem, appropriate for the passage's finite-dimensional `F^m`. The previously missing polynomial-distance and grid-substitution support was added. The old-test row identifies an ordinary argument rather than a Lean theorem. The correspondence repair is accepted at source-sidecar level; citation closure, final hashes, and the regenerated reader are separately pending the owning agent's build and check.

## Final reader data recheck

The reader owner froze `work/proof-reader/papers/pcp-full-argument/links.json` at SHA-256 `7cf6581bd4fabe6926d011dd406a46f48e4bd51c582b651f4b1c43ce83ebcb6d` and `generated/lean.json` at `d30a988f342ad3639b4f92612501c196088394db64d31008ee5e7a2f2d542997`; independently checked the files and all 16 remaining algebra passage bindings resolve to their source-read entries and correspond to the intended proof stage. The earlier coarse-agreement context link was omitted because its conclusion is display-only; the agreement-boost quote now states the 4ε conclusion. Formula-only links were intentionally omitted; this is a selected-entry-point review, not exhaustive linkage of every statement. The parent separately inspected reader screenshots. This review did not independently rerun the UI or extract Lean dependencies or perform a kernel check.
