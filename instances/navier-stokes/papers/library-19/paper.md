
<!-- passage:front -->
# Library guide 19: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) **19** [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.GivenProfilePowerFieldParts` to `Breakdown.FracCell.ModeRadialPartsA` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.GivenProfilePowerFieldParts

This module packages a measurable weak second derivative with cubic decay and a weighted translation estimate for use in fractional-power construction. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · A negative cubic power is reciprocal.** For a positive real number, its real power −3 equals the inverse of its ordinary cube. [`rpow_neg_three_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldParts.lean#L20).

**Theorem · Total second derivative decays cubically.** Valid field data with high radial order one give a global cubic decay bound for the total second Fréchet derivative of the reconstructed field. [`second_decay`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldParts.lean#L23).

**Theorem · The field is continuously differentiable.** A field reconstructed from valid chart and field data with high radial order one is C¹. [`fieldOf_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldParts.lean#L71).

**Theorem · Weak derivative with translation control.** A field reconstructed from valid data with high radial order one has a measurable weak second derivative with cubic decay and a weighted L¹ translation bound linear in shifts of norm at most 1. [`fieldOf_second_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerFieldParts.lean#L75).

### Breakdown.FracCell.GivenProfilePowerModulus

This module uses the L² representation of a bounded test-field functional to construct a weak fractional power from a second-derivative translation modulus. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Test vector fields belong to L².** Every test vector field belongs to L². [`test_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L19).

**Theorem · Represent an L²-bounded test functional.** A real-linear functional on test vector fields bounded by their L² norm is pairing with an L² vector field. [`represent_of_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L22).

**Theorem · Fractional powers add on test fields.** For 1<α<3/2, the pointwise fractional power of a sum of two test vector fields is the sum of their fractional powers. [`power_add_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L76).

**Theorem · Fractional powers commute with scaling.** The pointwise fractional power of a real scalar multiple of a test vector field is that scalar multiple of its fractional power. [`power_smul_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L85).

**Theorem · Test vector fields are closed under sums.** The sum of two test vector fields is again a test vector field. [`test_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L89).

**Theorem · A Hessian modulus gives a weak power.** For 1<α<5/4, a C¹ L⁶ field with an L² weak second derivative whose squared L² translation difference is bounded by C‖h‖ for ‖h‖≤1 admits a weak fractional power. [`weakPower_of_secondModulus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulus.lean#L93).

### Breakdown.FracCell.GivenProfilePowerModulusBound

This module rewrites the fractional-power pairing using translated weak second derivatives and proves its L² test-function bound, with the restriction α<5/4 arising from the near-zero kernel integral. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · The L² norm is the square-root integral.** For an L² field, the square root of its integrated squared norm equals the norm of its L² equivalence class. [`sqrt_sq_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L17).

**Theorem · The L² pairing obeys Cauchy-Schwarz.** The absolute integral pairing of two L² fields is bounded by the product of their square-root squared-norm integrals. [`abs_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L23).

**Theorem · Translation preserves L² membership.** Translating an L² field by a fixed vector preserves L² membership. [`shift_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L33).

**Theorem · Translation differences have an L² bound.** The L² norm of a translated field minus the original is at most twice the original L² norm. [`diff_le_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L37).

**Theorem · Use translation bounds along a segment.** A squared L² translation modulus C‖h‖ for shifts of norm at most one bounds the difference along any fraction of such a shift by |C| times its norm. [`diff_le_mod`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L50).

**Theorem · Bound a translated Hessian pairing.** Pairing a second-derivative translation difference evaluated twice on z with an L² test field is bounded by ‖z‖² times the two L² norms. [`pair_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L67).

**Theorem · Compactly supported continuous pairings.** The inner product of two continuous fields is integrable when the second field has compact support. [`pairProd_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L91).

**Theorem · Expand a vector in Cartesian units.** Every spatial vector is the sum of its coordinates times the Cartesian unit vectors. [`sum_unit'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L97).

**Theorem · Expand a bilinear map in both inputs.** A real bilinear map evaluated at two vectors equals the double coordinate sum of its values on Cartesian unit pairs. [`expand_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L101).

**Theorem · Weak second derivatives in directions.** A C¹ field with an L² weak second derivative satisfies the integration-by-parts identity in any two fixed directions against a scalar test function. [`weak_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L121).

**Theorem · Move two test derivatives to the field.** Pairing a C¹ field with a test vector field's second derivative along w equals pairing its L² weak second derivative evaluated on w,w with that test field. [`second_pairing_by_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L159).

**Theorem · Hessian integral for the remainder.** For a C² test field, the second-order remainder is the integral of its Hessian difference along the shift segment with weight 1−s. [`remainder_integral_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L233).

**Theorem · Interchange the remainder integrals.** For a continuous field and test vector field, the spatial pairing can be interchanged with the weighted segment integral of the Hessian difference. [`pairing_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L277).

**Theorem · Translations preserve test vector fields.** Translating a test vector field preserves its test-field properties. [`test_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L360).

**Theorem · Integrability of Hessian test pairings.** A continuous field paired with a test field's second directional derivative gives an integrable scalar function. [`second_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L364).

**Theorem · Evaluating an L² Hessian preserves L².** Evaluating an L² operator-valued second derivative twice on a fixed vector gives an L² vector field. [`eval_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L381).

**Theorem · L² inner products are integrable.** The pointwise inner product of two L² vector fields is integrable. [`inner_integrable2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L386).

**Theorem · Pair remainders by Hessian differences.** For a C¹ L⁶ field with L² weak second derivative, pairing with a test-field remainder equals the segment integral of translated second-derivative differences. [`remainder_pairing_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L392).

**Theorem · Fractional shift decay of pairings.** The second-derivative modulus bounds remainder pairings by a constant times ‖z‖⁵ᐟ² near zero and ‖z‖² farther away, times the test-field L² norm. [`remainder_pairing_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L428).

**Theorem · A large-shift remainder bound.** For shifts of norm at least 1, the second-order remainder is bounded by the shifted field value plus the local value and derivative terms times ‖z‖². [`rem_far_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L475).

**Theorem · Integrability from near and far powers.** A measurable scalar function with near-zero singularity exponent below 3 and far decay exponent above 3 is integrable under the bounds. [`near_far_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L499).

**Theorem · Uniform bounds for translated pairings.** A continuous L⁶ field paired in norm with translations of a continuous compactly supported field has a uniformly bounded integral. [`translate_bound6`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L532).

**Theorem · Combine a real and a natural power.** For t≥0, natural n and real r with r≠0 and r+n≠0, multiplying tʳ by tⁿ gives t^(r+n). [`rpow_pow_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L564).

**Theorem · The remainder is jointly continuous.** For a smooth field, the second-order remainder is continuous jointly in its base point and shift. [`rem_continuous_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L570).

**Theorem · A fixed-shift remainder is continuous.** For a smooth field and fixed shift, the second-order remainder is continuous in its base point. [`rem_continuous_section`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L585).

**Theorem · Remainders vanish away from test support.** For a shift of norm at most r, the remainder vanishes outside the closed r-neighborhood of the field's support. [`rem_zero_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L595).

**Theorem · Weighted remainder pairing is integrable.** For 1<α<3/2, a continuous L⁶ field and smooth compactly supported test field give an integrable kernel-weighted remainder pairing on the product space. [`prod_integrable6`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L612).

**Theorem · Fractional pairing by iterated integrals.** For 1<α<5/4, the pairing with a test fractional power equals the normalized kernel integral of the field's remainder pairing. [`pairing_eq_iterated`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L733).

**Theorem · The remainder kernel is integrable.** For 1<α<5/4, the kernel times the piecewise ‖z‖⁵ᐟ² and ‖z‖² remainder bound is integrable over space. [`weight_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L758).

**Theorem · The fractional pairing is L²-bounded.** For 1<α<5/4, the C¹, L⁶, weak second-derivative and translation conditions bound every fractional-power test pairing by a constant times the test-field L² norm. [`pairing_bound_of_secondModulus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfilePowerModulusBound.lean#L786).

### Breakdown.FracCell.GivenProfileRate

This module transfers continuity of the profile rates to the certificate parameter box. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Rotation rate is continuous on the box.** A valid profile instance has a rotation rate continuous on its parameter box. [`rotationRate_continuous_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileRate.lean#L13).

**Theorem · The multiplier is continuous on the box.** A valid profile instance has a multiplier continuous on its parameter box. [`multiplier_continuous_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileRate.lean#L21).

### Breakdown.FracCell.GivenProfileSmooth

This module assembles the finite field sum into a C¹, divergence-free profile with a measurable weak second derivative and the prescribed class symmetries. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · The profile is a finite field sum.** The profile is the finite sum of its phase-dependent component fields weighted by parameter monomials. [`profile_fun_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L18).

**Theorem · The assembled profile is C¹.** Valid profile data give a continuously differentiable spatial profile at every parameter. [`profile_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L22).

**Theorem · Each profile summand is differentiable.** Every listed component field of valid profile data is differentiable in space at the chosen phase. [`parts_differentiable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L28).

**Theorem · Certificate profiles are C¹.** For a valid profile instance, each parameter in the certificate box gives a continuously differentiable spatial profile. [`profile_smooth_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L32).

**Theorem · Profiles have weak second derivatives.** For each parameter in the certificate box, the assigned second derivative is a measurable weak second derivative of the profile gradient. [`profile_second_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L39).

**Theorem · Certificate profiles are divergence-free.** For a valid profile instance, each parameter in the certificate box gives a profile with zero divergence everywhere. [`profile_divergence_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L56).

**Theorem · Certificate profiles have class symmetry.** For a valid profile instance, each profile in the parameter box belongs to the class of the certificate symmetry order. [`profile_class_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmooth.lean#L64).

### Breakdown.FracCell.GivenProfileSmoothField

This module assembles regular single-mode fields and transfers their derivative bounds, divergence and symmetries to a reconstructed field. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Component reconstruction preserves sums.** Reconstructing the sum of vector components equals the finite sum of the reconstructed component vectors. [`ofComponents_finset_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L17).

**Theorem · A field is the sum of its mode fields.** The reconstructed field equals the finite sum of its listed single-mode fields. [`fieldOf_eq_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L22).

**Theorem · Every listed mode field is C¹.** Valid chart and field data with high radial order one make every listed single-mode field continuously differentiable. [`modeFieldOf_contDiff_all`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L32).

**Theorem · The finite reconstructed field is C¹.** Valid chart and field data with high radial order one make the reconstructed field continuously differentiable at every phase. [`fieldOf_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L51).

**Theorem · Field derivative is locally Lipschitz.** For valid field data with high radial order one, the reconstructed field derivative has a finite Lipschitz bound on each closed ball. [`fieldOf_fderiv_slopeOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L56).

**Theorem · Nonzero-mode reduced divergence vanishes.** With nonzero symmetry order and nonzero mode, the reduced divergence is identically zero. [`reducedDivergence_wave_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L78).

**Theorem · Divergence of a finite mode sum.** At a common differentiability point, the divergence of a finite mode sum equals the sum of its mode divergences. [`divergenceAt_sum_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L102).

**Theorem · Field is solenoidal almost everywhere.** A reconstructed field from valid field data with high radial order one has zero divergence almost everywhere. [`fieldOf_divergence_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L110).

**Theorem · The field is solenoidal everywhere.** A reconstructed field from valid field data with high radial order one has zero divergence at every point. [`fieldOf_divergence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L150).

**Theorem · Rotation symmetry almost everywhere.** For valid field data with high radial order one, the reconstructed field commutes with the symmetry rotation almost everywhere in space. [`fieldOf_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L154).

**Theorem · Reflection symmetry almost everywhere.** For valid field data with high radial order one, the reconstructed field commutes with horizontal reflection almost everywhere in space. [`fieldOf_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothField.lean#L159).

### Breakdown.FracCell.GivenProfileSmoothModes

This module differentiates the reduced cylindrical mode formula, identifies physical divergence with reduced divergence and verifies the zero-mode cancellation away from spline interfaces. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Definition · Divergence in reduced chart variables.** The reduced divergence combines the twisted radial derivative, twice the radial component, the weighted height derivative of the polar component and the angular mode term. [`reducedDivergence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L17).

**Theorem · Local Lipschitzness of wave slopes.** For valid field data with high radial order one, the derivative of every listed nonzero mode field is locally Lipschitz. [`modeFieldOf_fderiv_locallySlope_wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L22).

**Theorem · Local Lipschitzness of the mean slope.** For valid field data with high radial order one containing mode zero, the zero-mode field derivative is locally Lipschitz. [`modeFieldOf_fderiv_locallySlope_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L27).

**Theorem · Divergence product rule.** At common differentiability points, divergence of a scalar times a vector field is the scalar derivative on that vector plus scalar times vector divergence. [`g_div_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L32).

**Theorem · Divergence is additive.** At a common differentiability point, divergence of the sum of two fields is the sum of their divergences. [`g_div_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L48).

**Theorem · Divergence is invariant under shifts.** Adding a constant vector to a field leaves its totalized divergence unchanged. [`g_div_add_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L55).

**Theorem · The identity field has divergence three.** The spatial identity map has divergence 3. [`g_div_id`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L60).

**Theorem · The norm has a derivative off zero.** At a nonzero point y, the Fréchet derivative of the Euclidean norm sends a direction w to the inner product of y and w divided by ‖y‖. [`g_norm_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L65).

**Theorem · Coordinate formula for norm derivative.** At a nonzero point, the norm derivative in direction w is the coordinate dot product y·w divided by ‖y‖. [`g_norm_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L72).

**Theorem · Differentiate a radial scalar function.** At a nonzero point, the derivative of h(‖y‖) is h′(‖y‖) times the normalized radial dot product. [`g_radial_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L80).

**Theorem · Differentiate radial compositions.** A scalar function differentiable at a nonzero point's norm gives a differentiable radial spatial composition there. [`g_radial_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L87).

**Theorem · Derivative of a Cartesian coordinate.** The derivative of the jth coordinate in direction w is w_j. [`g_coord_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L91).

**Theorem · Radial frame as normalized position.** Reconstructing the reduced radial frame gives y/‖y‖. [`g_rvec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L97).

**Theorem · The polar frame has a Cartesian formula.** Reconstructing the reduced polar frame gives y₂y/‖y‖² minus the vertical unit vector. [`g_pvec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L101).

**Theorem · Azimuthal frame is normalized turning.** Reconstructing the reduced azimuthal frame gives the horizontal quarter-turn of y divided by ‖y‖. [`g_avec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L105).

**Theorem · Coordinate dot square is the norm square.** The sum of the three squared Cartesian coordinates equals ‖y‖². [`g_inner_self`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L111).

**Theorem · Differentiate inverse radius off zero.** The inverse norm is differentiable at every nonzero point. [`g_inv_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L115).

**Theorem · Derivative of inverse radius.** At a nonzero point, the inverse-norm derivative in direction w is −(y·w)/‖y‖³. [`g_inv_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L118).

**Theorem · Constant fields have zero divergence.** Every constant vector field has divergence zero. [`g_div_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L124).

**Theorem · Divergence of the radial unit field.** Off zero, the field y/‖y‖ has divergence 2/‖y‖. [`g_div_rvec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L128).

**Theorem · Divergence of the reduced polar field.** Off zero, the reduced polar-frame field has divergence 2y₂/‖y‖². [`g_div_pvec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L135).

**Theorem · Reduced azimuthal field is solenoidal.** Off zero, the reduced azimuthal-frame field has divergence zero. [`g_div_avec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L152).

**Theorem · Derivative of compactified radius.** At a nonzero point, the chart radius derivative is L₀/(‖y‖+L₀)² times the normalized radial dot product. [`g_T_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L169).

**Theorem · Derivative of normalized height.** At a nonzero point, normalized height has derivative w₂/‖y‖−y₂(y·w)/‖y‖³. [`g_X_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L187).

**Theorem · Derivative of logarithmic phase.** At a nonzero point, the logarithmic phase derivative is (y·w)/(r_c²+‖y‖²). [`g_ell_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L202).

**Theorem · Derivative of the angle off its branch.** When the second Cartesian coordinate is nonzero, the angle derivative is (y₀w₁−y₁w₀)/(y₀²+y₁²). [`g_angle_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L216).

**Theorem · Derivative of the decay factor.** For valid chart parameters at y≠0, the decay-factor derivative in direction w is −2ε times the decay factor times the inner product of y and w, divided by (‖y‖+L₀)‖y‖. [`g_decay_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L245).

**Theorem · Derivative of decay times mode phase.** Away from the angle branch, the derivative of decay times mode phase combines the radial decay derivative with the angular and logarithmic-phase derivatives. [`g_phase_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L269).

**Theorem · Separate real frame coefficients.** The real part of a complex amplitude times three real frame coefficients equals the sum of the three corresponding real scalar products. [`g_re_combo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L294).

**Theorem · Three real frame fields for one mode.** A mode field is the sum of its real reduced amplitudes multiplying the Cartesian radial, polar and azimuthal frame expressions. [`g_decomp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L300).

**Theorem · Differentiate one reduced amplitude.** Under the differentiability hypotheses, a complex prefactor times a reduced chart function has the real product-and-chain-rule derivative displayed in the statement. [`g_part_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L313).

**Theorem · Physical and reduced divergence agree.** Away from the angle branch and where reduced components are differentiable, physical mode divergence is the real weighted reduced divergence divided by radius. [`g_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L344).

**Theorem · Export the reduced divergence formula.** Under the chart differentiability and nonzero-coordinate assumptions, the mode divergence equals its weighted reduced divergence divided by radius. [`modeFieldOf_divergence_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L476).

**Theorem · Partial slopes from frame evaluations.** Near a point of C² regularity, the two coordinate partial derivatives equal the Fréchet derivative evaluated on the coordinate directions. [`partials_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L485).

**Theorem · Mixed partial derivatives commute.** At a point of C² regularity, the two mixed chart derivatives agree and both relevant first-derivative slices are differentiable. [`mixed_partials`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L496).

**Theorem · Reduced slopes give mode derivatives.** Away from the angle branch, differentiability of all reduced components gives differentiability of the physical mode field. [`modeFieldOf_differentiableAt_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L527).

**Theorem · Differentiate reduced fields off breaks.** Away from height zero and all four spline mesh breaks, every reduced field component is differentiable in the chart coordinates. [`reducedField_differentiableAt_generic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L549).

**Theorem · The mean reduced divergence vanishes.** Away from height zero and stream-spline breaks, the zero-mode reduced divergence is zero. [`reducedDivergence_mean_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenProfileSmoothModes.lean#L559).

### Breakdown.FracCell.GivenToolkit

This module collects the finite-sum, weak-derivative, parity and generic-point facts used to assemble profile regularity and symmetry from spline modes. **Reading context:** Appendix B: the represented profile and its regularity, decay and parameter dependence, supplying the data conditions in B.14.

**Theorem · Symmetry rotations preserve addition.** The discrete symmetry rotation preserves vector addition. [`givenTurn_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L15).

**Theorem · Symmetry rotations preserve real scaling.** The discrete symmetry rotation commutes with real scalar multiplication. [`givenTurn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L19).

**Theorem · Reflection preserves addition.** Horizontal reflection preserves vector addition. [`givenMirror_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L23).

**Theorem · Reflection preserves real scaling.** Horizontal reflection commutes with real scalar multiplication. [`givenMirror_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L27).

**Definition · The symmetry step as a linear map.** The discrete symmetry step is packaged as a real linear map. [`givenTurnLinear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L31).

**Definition · Horizontal reflection as a linear map.** Horizontal reflection is packaged as a real linear map. [`givenMirrorLinear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L36).

**Theorem · Class symmetries pass to finite sums.** A finite real linear combination of class fields with the same symmetry order is a class field of that order. [`classField_finset_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L41).

**Theorem · Differentiate finite linear combinations.** For differentiable summands, the derivative of a finite real linear combination is the same combination of their derivatives. [`fderiv_finset_sum_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L61).

**Theorem · Divergence preserves finite linear sums.** For differentiable summands, divergence of a finite real linear combination is the corresponding real combination of divergences. [`divergenceAt_finset_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L70).

**Theorem · Sum ballwise Lipschitz bounds.** A finite real linear combination of fields Lipschitz on every closed ball is Lipschitz on every closed ball. [`slopeOn_finset_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L81).

**Theorem · Weak derivatives of Lipschitz gradients.** A gradient field Lipschitz on every closed ball has its total Fréchet derivative as an almost everywhere strongly measurable weak second derivative. [`weakSecond_of_slopeOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L96).

**Theorem · Spline evaluation respects parity.** At nonzero height, reflecting the height multiplies spline evaluation by −1 for odd parity and by 1 for even parity. [`spline_eval_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L197).

**Theorem · Height differentiation reverses parity.** At nonzero height, a height derivative transforms with the negative of the original function's reflection factor. [`heightDeriv_parity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L208).

**Theorem · Radial scaling preserves height parity.** The radial scaling operator preserves the height-reflection factor. [`radialScale_parity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L221).

**Theorem · Twisted scaling preserves height parity.** The twisted radial scaling operator preserves the height-reflection factor. [`twistedScale_parity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L228).

**Theorem · Parity of the reduced field components.** Reflecting nonzero height leaves the radial and azimuthal reduced components unchanged and negates the polar component. [`reducedField_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L235).

**Theorem · Read a reconstructed Cartesian component.** The kth coordinate of the vector reconstructed from components is the kth supplied component. [`ofComponents_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L282).

**Theorem · Reflection preserves spatial norm.** Horizontal reflection leaves the Euclidean norm unchanged. [`givenNorm_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L285).

**Theorem · Coordinate planes are null.** Each Cartesian coordinate is nonzero at almost every spatial point. [`ae_coord_ne_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L289).

**Theorem · Mirror rule away from the plane.** Away from height zero, reflecting the input multiplies a reconstructed field component by −1 vertically and by 1 horizontally. [`fieldOf_mirror_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L303).

**Theorem · Almost everywhere mirror symmetry.** The reconstructed field commutes with horizontal reflection almost everywhere in space. [`fieldOf_mirror_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L339).

**Theorem · Coordinates of the symmetry step.** The discrete symmetry step applies the sine-cosine rotation through 2π/m horizontally and fixes height. [`givenTurn_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L346).

**Theorem · Symmetry rotations preserve spatial norm.** The discrete symmetry rotation leaves the Euclidean norm unchanged. [`givenNorm_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L352).

**Theorem · The mode phase obeys discrete symmetry.** For nonzero symmetry order and nonzero first coordinate, the mode phase is unchanged by the symmetry step. [`modePhase_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L360).

**Theorem · Real harmonic sums respect linear sums.** Taking the real part of the harmonic sum commutes with a real linear combination of its two component families. [`givenRe_combo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L409).

**Theorem · Symmetry away from a coordinate plane.** For nonzero symmetry order and nonzero first coordinate, the reconstructed field commutes with the discrete symmetry rotation. [`fieldOf_turn_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L421).

**Theorem · Rotation symmetry almost everywhere.** For nonzero symmetry order, the reconstructed field commutes with the discrete symmetry rotation almost everywhere. [`fieldOf_turn_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L470).

**Theorem · C¹ fields have continuous divergence.** The divergence of a C¹ field is continuous. [`divergenceAt_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L476).

**Theorem · Extend zero divergence everywhere.** A C¹ field with divergence zero almost everywhere has divergence zero everywhere. [`divergenceAt_eq_zero_of_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L481).

**Theorem · Local constancy of cell selection.** Away from a listed break, the selected cell index is constant in a neighborhood. [`cellIndex_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L488).

**Theorem · Smoothness under polynomial substitution.** Substituting two smooth real functions into a complex bivariate polynomial gives a smooth function. [`mvPoly_eval_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L507).

**Theorem · Smooth local polynomial spline formula.** Away from chart breaks, absolute-height breaks and height zero, spline evaluation agrees locally with a smooth polynomial expression. [`spline_eventually_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L522).

**Theorem · Fixed height-ratio cone has zero volume.** For every real c, the set y₂=c‖y‖ has volume zero. [`cone_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L550).

**Theorem · A fixed chart-radius level is null.** For positive L₀, almost every point avoids any prescribed compactified-radius level. [`ae_chartT_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L628).

**Theorem · Absolute height-ratio levels are null.** Almost every spatial point avoids any prescribed absolute normalized-height level. [`ae_heightRatio_abs_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L645).

**Theorem · Generic chart points have full measure.** For positive L₀ and finite break lists, almost every point avoids all coordinate planes and the listed chart-radius and absolute-height breaks. [`ae_generic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/GivenToolkit.lean#L673).

### Breakdown.FracCell.HeightModeIbp

Smooth interval cutoffs extend the height-mode integration-by-parts identity to the endpoint-vanishing tests needed on a cell. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Interior interval cutoff.** The smooth bump is centred at the interval midpoint and leaves a boundary margin that shrinks as its index increases. [`cutBump`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L12).

**Theorem · Positive cutoff margin.** For an interval of positive length, the cutoff margin is strictly positive at every natural index. [`cutEps_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L26).

**Theorem · Cutoff margin bound.** The cutoff margin is at most one eighth of the interval length. [`cutEps_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L29).

**Theorem · Polynomial evaluation is smooth.** Evaluating a real polynomial defines a smooth real function. [`poly_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L34).

**Theorem · Cutoff vanishes near the endpoints.** The interval bump vanishes outside its open inner support interval. [`cutBump_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L41).

**Theorem · Cutoff equals one in the interior.** The interval bump equals one on the closed interval with twice the cutoff margin removed from each end. [`cutBump_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L52).

**Theorem · Cutoff eventually equals one.** At each point of the open interval, all sufficiently late cutoffs equal one. [`cutBump_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L60).

**Theorem · Cutoffs converge to one.** The sequence of cutoff values converges to one at every point strictly between the endpoints. [`cutBump_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L76).

**Theorem · Cutoff preserves a uniform bound.** Multiplying by the interval cutoff preserves any nonnegative bound on the absolute value of the original function over the interval. [`bump_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L80).

**Theorem · Smooth approximation inside an interval.** Every continuous function on a closed interval admits uniformly bounded smooth approximants supported strictly inside the interval and converging pointwise in its interior. [`approx_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L94).

**Theorem · Cutoff vanishes outside the interval.** The interval bump is zero at every point outside the original open interval. [`bump_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L124).

**Theorem · Approximate a test and its derivative.** A continuously differentiable test vanishing at both endpoints admits smooth supported approximants whose values and derivatives converge in the interior with uniform bounds. [`approx_c1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L130).

**Theorem · A vertical line has zero area.** Almost every point of the plane has first coordinate different from any fixed real number. [`line_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L282).

**Theorem · A horizontal line has zero area.** Almost every point of the plane has second coordinate different from any fixed real number. [`line_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L288).

**Theorem · Height-mode integration by parts.** For second-order fields on valid cells, the axial gradient mode is line-weight integrable and its pairing with a separated continuous radial and C¹ endpoint-vanishing height test equals minus the velocity-mode pairing with the height derivative. [`heightModeIbp_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeIbp.lean#L301).

### Breakdown.FracCell.HeightModeWeak

A weak height derivative is reduced to a one-dimensional identity on almost every radial slice, with the integrability needed for second-order fields. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Enclose compact support in an interval.** A compactly supported real function has its support inside some open interval centred at zero. [`tsupp_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L16).

**Theorem · Local integrability on an interval.** A locally integrable complex function is integrable between any two finite real endpoints. [`interval_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L24).

**Theorem · Integrable compactly supported product.** Multiplying a locally integrable function by a continuous compactly supported real function gives an integrable function. [`cont_csupp_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L28).

**Theorem · Integrating against a primitive.** For a smooth compactly supported test, pairing its derivative with an integral primitive equals the negative pairing with the original locally integrable function. [`prim_ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L32).

**Theorem · Weak derivative on a closed interval.** A distributional derivative identity implies the zero integral of the product-rule sum for every continuously differentiable test vanishing at both interval endpoints. [`one_dim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L74).

**Theorem · Rectangle measure factors.** Lebesgue measure restricted to a rectangle is the product of the two restricted one-dimensional measures. [`restrict_prod_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L186).

**Theorem · Integrate radius before height.** An integrable function on a rectangle can be integrated first in radius and then in height. [`iter_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L190).

**Theorem · Integrate height before radius.** An integrable function on a rectangle can be integrated first in height and then in radius. [`iter_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L196).

**Theorem · Height integrals are integrable.** Integrating an integrable rectangle function over height gives an integrable function of radius. [`slice_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L202).

**Theorem · Radial integrals are integrable.** Integrating an integrable rectangle function over radius gives an integrable function of height. [`slice_int'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L208).

**Theorem · Integrability with continuous weights.** On a product of compact sets, multiplication by a continuous real weight preserves integrability. [`box_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L214).

**Theorem · A compact set has a finite bound.** Every compact subset of the real line lies in some closed interval centred at zero with positive radius. [`bounded_box`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L219).

**Theorem · Weak identity on almost every slice.** A two-dimensional weak height identity yields the endpoint-vanishing integration-by-parts identity on almost every positive radial slice. [`slice_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L227).

**Definition · Cylindrical frame from plane coordinates.** The definition forms radial, angular and axial frame vectors from two plane coordinates. [`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L352).

**Theorem · Frame on the unit circle.** At cosine and sine coordinates, the constructed vectors equal the cylindrical orthonormal frame. [`unitAt_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L356).

**Definition · A frame-coordinate functional.** The definition forms the continuous linear functional extracting the component along a chosen frame vector. [`angQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L358).

**Theorem · Frame functional as an inner product.** On the unit circle, the coordinate functional equals inner product with the corresponding cylindrical frame vector. [`angQ_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L361).

**Theorem · Smooth frame coordinates.** Every coordinate of the frame construction varies smoothly with its two plane arguments. [`unitAt_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L365).

**Theorem · The frame construction is smooth.** Each vector in the extended cylindrical frame depends smoothly on the plane coordinates. [`unitAt_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L370).

**Theorem · Smooth coordinate functional.** The frame-coordinate functional depends smoothly on its plane coordinates. [`angQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L373).

**Definition · A matrix entry in the moving frame.** The definition evaluates a linear map on one frame vector and extracts its component along another frame vector. [`colQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L377).

**Theorem · Smooth moving-frame matrix entry.** The continuous linear functional extracting a moving-frame matrix entry depends smoothly on the plane coordinates. [`colQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L380).

**Theorem · Matrix entry as a frame pairing.** On the unit circle, the matrix-entry functional equals the inner product of the mapped input frame vector with the output frame vector. [`colQ_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L383).

**Theorem · Expand a vector in coordinate axes.** Every spatial vector equals the sum of its three coordinates multiplied by the standard unit vectors. [`vec_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L388).

**Theorem · Operator norm bounded by columns.** The operator norm of a linear map from three-dimensional space is at most the sum of the norms of its coordinate columns. [`norm_le_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L391).

**Theorem · The norm is locally integrable.** Taking the norm preserves local integrability of a normed-space-valued function. [`loc_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L400).

**Theorem · Local integrability from columns.** An almost everywhere strongly measurable field of linear maps is locally integrable when each of its three coordinate columns is locally integrable. [`loc_of_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L404).

**Theorem · Gradient columns belong to L2.** Measurability and integrability of the squared matrix-entry norm put each gradient column in L2. [`memLp_col`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L414).

**Theorem · Second derivative entries belong to L2.** Measurability and integrability of the sum of squared second-derivative entries put every coordinate entry in L2. [`memLp_col2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L423).

**Theorem · Scale a weak identity.** Multiplying both fields in a weak integral identity by the same complex constant preserves the identity. [`scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L437).

**Theorem · Weak height derivative of gradient modes.** For a second-order field, the height derivative of a gradient mode is represented weakly by the corresponding mode of the second derivative away from the axis. [`weak_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L443).

**Theorem · Weighted derivative modes are integrable.** For a second-order field, the radial-weighted gradient and second-derivative modes are integrable on every finite rectangle meeting the axis. [`weighted_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L487).

**Theorem · Height derivative of a separated test.** The height derivative of a product of a radial function and a height function is the radial factor times the derivative of the height factor. [`prod_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L515).

**Theorem · Separated tests for the height identity.** Smooth compactly supported separated tests away from the axis satisfy the weak height identity for radial-weighted derivative modes. [`prod_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L529).

**Theorem · Factor a radial weight.** A continuous weight factors continuously by radius on the cell interval when that interval avoids zero or the weight already has a continuous radial factor. [`weight_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L566).

**Theorem · The weak height-mode identity.** For a second-order field, each gradient mode and its height derivative satisfy integrability and height integration by parts against continuous separated weights, with a radial factor required on axis-touching cells and zero endpoint values for the C¹ height test. [`heightModeWeak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightModeWeak.lean#L584).

### Breakdown.FracCell.HeightProjBound

Weighted polynomial projection is characterized by its moments, then used to bound the unresolved height contribution by higher projection energy and the tail. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · L2 functions are closed under addition.** The squared norm of the sum is integrable when both complex functions are measurable and have integrable squared norms. [`sq_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L21).

**Theorem · Subtract two L2 functions.** The squared norm of the difference is integrable when both complex functions are measurable and have integrable squared norms. [`sq_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L31).

**Theorem · L2 cross products are integrable.** The product of one L2 function with the complex conjugate of another is integrable. [`cross_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L37).

**Theorem · Finite sums remain in L2.** A finite sum of measurable functions with integrable squared norms is measurable and has an integrable squared norm. [`sq_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L45).

**Theorem · Orthogonality lowers squared norm.** With a bounded nonnegative weight, adding a weighted-orthogonal L2 function cannot decrease the weighted squared norm. [`weighted_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L57).

**Theorem · Exchange two finite expansion orders.** The same finite tensor-product expansion results whether the radial or height sum is taken first. [`sum_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L84).

**Theorem · Line projection is a polynomial.** The chosen line projection is a polynomial of degree at most the prescribed natural degree. [`lineProj_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L90).

**Theorem · Choice respects equal predicates.** Equal predicates give equal choice-based polynomial expressions, including their common zero fallback. [`dite_pred`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L104).

**Reader note.** The expression is defined by choice when admissible coefficients exist and by zero otherwise; this lemma only transports that definition across equal predicates.

**Theorem · Line projection respects a.e. equality.** Functions equal almost everywhere on the projection interval have the same line projection. [`lineProj_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L110).

**Theorem · Expand the double polynomial sum.** The nested tensor-product expression equals the explicit double sum of coefficients times radial and height factors. [`dsum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L122).

**Theorem · Cell projection has bounded degrees.** The cell projection lies in the polynomial space with the specified radial and height degree bounds. [`proj_mem'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L127).

**Theorem · Bivariate polynomials are continuous.** Every member of the finite bivariate polynomial space is continuous. [`poly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L133).

**Theorem · Cell rectangle measure factors.** Lebesgue measure on the cell rectangle is the product of the restricted radial and height measures. [`rect_prod`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L142).

**Theorem · The line weight is continuous.** The cell's radial line weight is a continuous real function. [`lw_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L146).

**Theorem · The line weight is nonnegative.** For a valid cell, the line weight is nonnegative at every radius above the left radial endpoint. [`lw_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L153).

**Theorem · Uniform bound on the line weight.** On a valid cell's radial interval, the norm of the line weight is at most the outer radius plus one. [`lw_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L159).

**Theorem · A polynomial factor preserves L2.** Multiplying an L2 height coefficient by a fixed radial monomial gives a measurable square-integrable function on the cell rectangle. [`term_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L166).

**Theorem · Continuous fields are L2 on a cell.** A continuous complex function is measurable and square-integrable on the compact cell rectangle. [`cont_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L179).

**Theorem · Assemble the height projection bound.** The line projection specification, radial coefficient representation and radial top bound together imply the height projection bound. [`heightProjBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186).

**Definition · Weighted polynomial moment matrix.** The matrix records weighted inner products of radial monomials through the selected degree. [`momentMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L373).

**Theorem · Continuous functions are integrable.** A continuous normed-space-valued function is integrable on every closed bounded real interval. [`cont_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L376).

**Theorem · Moments are matrix multiplication.** The weighted moments of a polynomial equal its coefficient vector multiplied by the moment matrix. [`poly_moment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L379).

**Theorem · The moment matrix has trivial kernel.** For a continuous weight positive inside a nondegenerate interval, a polynomial coefficient vector with zero weighted moments is zero. [`poly_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L394).

**Theorem · Weighted monomial moments exist.** A measurable function with finite weighted squared norm has integrable weighted products with every monomial when the weight is continuous and nonnegative. [`moment_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L460).

**Theorem · Characterize weighted line projection.** For a continuous positive interior weight, line projection has zero residual moments and is uniquely characterized among polynomials by those moments. [`lineProj_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L473).

**Theorem · Supply the line projection specification.** The theorem proves the orthogonality and uniqueness specification for the permitted constant and radial line weights. [`lineProjSpec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L535).

**Theorem · Weighted Cauchy–Schwarz inequality.** The squared norm of a weighted complex inner product is bounded by the product of the two weighted squared norms for a nonnegative measurable weight. [`weightedInner_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L544).

**Theorem · Positive line weight inside a cell.** The line weight is strictly positive at every interior radius of a valid cell. [`lw_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L583).

**Theorem · L2 coefficients of radial projection.** For a measurable field with integrable line-weighted squared norm, radial projection has monomial coefficients that are measurable and L² in height and represent the projection at every radius for almost every height. [`projRCoeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L593).

**Predicate · Weighted L2 condition on a cell.** The predicate requires almost everywhere strong measurability and integrability of the squared norm multiplied by the cell's line weight. [`WL2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L670).

**Theorem · The rectangle weight is measurable.** The radial line weight, viewed as a function on the rectangle, is almost everywhere strongly measurable. [`w_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L674).

**Theorem · The rectangle weight is bounded.** On a valid cell rectangle, the line weight has norm at most the outer radius plus one almost everywhere. [`w_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L677).

**Theorem · The rectangle weight is nonnegative.** On a valid cell rectangle, the line weight is nonnegative almost everywhere. [`w_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L681).

**Theorem · Ordinary L2 implies weighted L2.** A measurable square-integrable function on a valid cell rectangle satisfies the weighted L2 condition. [`wl2_of_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L685).

**Theorem · Weighted L2 is closed under addition.** The sum of two weighted L2 functions on a valid cell remains weighted L2. [`wl2_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L689).

**Theorem · Weighted L2 is closed under scaling.** Multiplication by a complex constant preserves the weighted L2 condition. [`wl2_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L702).

**Theorem · Weighted L2 is closed under subtraction.** The difference of two weighted L2 functions on a valid cell remains weighted L2. [`wl2_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L711).

**Theorem · Finite sums preserve weighted L2.** A finite sum of weighted L2 functions on a valid cell remains weighted L2. [`wl2_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L720).

**Theorem · Continuous fields satisfy weighted L2.** A continuous complex function satisfies the weighted L2 condition on a valid cell. [`wl2_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L732).

**Theorem · Weighted cross products are integrable.** Two weighted L2 functions on a valid cell have an integrable line-weighted conjugate product. [`wcross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L735).

**Theorem · Subtract in the first pairing argument.** The cell's weighted pairing is additive over subtraction in its first argument for weighted L2 functions. [`pair_sub_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L744).

**Theorem · Subtract in the second pairing argument.** The cell's weighted pairing distributes over subtraction in its second argument for weighted L2 functions. [`pair_sub_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L751).

**Theorem · Self-pairing equals squared norm.** The cell's weighted pairing of a function with itself equals its real weighted squared norm embedded in the complex numbers. [`pair_self`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L759).

**Theorem · Expand the squared norm of a sum.** The weighted squared norm of a sum is the sum of both squared norms plus twice the real part of their pairing. [`normSq_add'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L769).

**Theorem · Extend monomial orthogonality.** Vanishing pairings with all monomials within the degree bounds imply vanishing pairing with every polynomial within those bounds. [`orth_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L784).

**Theorem · Pairing as iterated radial moments.** The pairing against a radial monomial times an L2 height factor equals the height integral of the conjugate factor times the radial moment. [`slice_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L815).

**Theorem · Zero moments give zero pairing.** Almost everywhere vanishing radial moments make the pairing with the corresponding finite polynomial expansion vanish. [`slice_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L836).

**Theorem · Pairing distributes over left addition.** The cell's weighted pairing is additive in its first argument for weighted L2 functions. [`pair_add_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L867).

**Theorem · A polynomial moment stays polynomial.** Taking a weighted radial moment of a bivariate polynomial gives a height polynomial with the original height degree bound. [`slice_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L874).

**Theorem · Orthogonality gives the radial top bound.** The projection orthogonality proposition implies the radial top estimate used to control height projection error. [`radialTopBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L907).

**Theorem · A polynomial vanishing on an interval.** If a finite monomial expansion vanishes on a nonempty open interval, all its coefficients are zero. [`poly_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1133).

**Theorem · A monomial lies in its degree space.** A radial-height monomial belongs to the bivariate polynomial space whenever each exponent is within its corresponding degree bound. [`mono_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1156).

**Theorem · Residual projection is orthogonal.** The theorem proves that the cell projection residual is orthogonal to every monomial within the projection's degree bounds. [`projOrth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1178).

**Theorem · The height projection bound.** For Q at least five and a measurable field with finite line-weighted energy, the height truncation error after radial projection is integrable and bounded by the retained height-band energy plus the full degree-Q tail energy. [`heightProjBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1277).

### Breakdown.FracCell.HeightProjBoundSt

These proposition definitions specify line projection, its height-dependent coefficients, residual orthogonality and the radial top estimate. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · Line projection specification.** The proposition requires vanishing residual moments and uniqueness of the projected polynomial for the permitted line weights and weighted L2 inputs. [`LineProjSpecStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBoundSt.lean#L15).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.lineProjSpec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L535) ([lean/Breakdown/FracCell/HeightProjBound.lean:535](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L535); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.heightProjBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186) ([lean/Breakdown/FracCell/HeightProjBound.lean:186](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186); named reference in type).

**Interface · Radial projection coefficient condition.** The proposition requires radial projection to have measurable L2 height coefficients and an almost everywhere polynomial representation in radius. [`ProjRCoeffStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBoundSt.lean#L25).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.projRCoeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L593) ([lean/Breakdown/FracCell/HeightProjBound.lean:593](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L593); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.heightProjBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186) ([lean/Breakdown/FracCell/HeightProjBound.lean:186](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186); named reference in type).

**Interface · Radial top projection estimate.** For degrees at least five, the proposition bounds the radial-only projection error by the difference of two bivariate projection energies plus the tail energy. [`RadialTopBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBoundSt.lean#L34).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.radialTopBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L907) ([lean/Breakdown/FracCell/HeightProjBound.lean:907](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L907); named premises: `ProjOrthStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.heightProjBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186) ([lean/Breakdown/FracCell/HeightProjBound.lean:186](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L186); named reference in type).

**Interface · Projection residual orthogonality.** The proposition requires the weighted pairing of the cell projection residual with every retained monomial to vanish. [`ProjOrthStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBoundSt.lean#L42).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.projOrth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1178) ([lean/Breakdown/FracCell/HeightProjBound.lean:1178](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L1178); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.radialTopBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L907) ([lean/Breakdown/FracCell/HeightProjBound.lean:907](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/HeightProjBound.lean#L907); named reference in type).

### Breakdown.FracCell.IntervalClosed

Polynomial endpoint and derivative estimates control an explicit cutoff trial function, giving the closed bound for the interval resolvent. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Clamp a real number to the unit interval.** The function clips its argument to the interval from minus one to one. [`clampUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L19).

**Lemma · Clamping stays in the interval.** Every clamped value belongs to the closed interval from minus one to one. [`clampUnit_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L21).

**Lemma · Clamping fixes interior values.** Clamping leaves every point of the closed unit interval unchanged. [`clampUnit_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L24).

**Lemma · Clamping is nonexpansive.** Clamping to the unit interval is Lipschitz with constant one. [`clampUnit_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L28).

**Lemma · A clamped polynomial is Lipschitz.** Evaluating a polynomial after clamping gives a globally Lipschitz function. [`slope_eval_clamp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L31).

**Lemma · Derivative of a clamped polynomial.** Inside the open unit interval, the derivative of the clamped polynomial equals the evaluation of its polynomial derivative. [`deriv_eval_clamp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L43).

**Lemma · Clamping preserves derivative energy.** Clamping a polynomial to [-1,1] leaves the integral of its squared derivative on that interval equal to the integral of the original polynomial derivative squared. [`integral_deriv_clamp_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L50).

**Lemma · Integral of an even monomial.** The integral of the power with exponent twice n over the symmetric unit interval is two divided by twice n plus one. [`integral_pow_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L61).

**Lemma · Even powers lie between zero and one.** On the closed unit interval, every even power with exponent at least two lies between zero and one. [`pow_unit_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L68).

**Lemma · Derivative of the polynomial cutoff.** Differentiating the polynomial multiplied by one minus an even monomial gives the product-rule expression for the cutoff derivative. [`eval_derivative_cut`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L74).

**Lemma · Integrate a polynomial derivative.** The integral of a polynomial derivative from minus one to one equals the difference of its endpoint values. [`integral_derivative_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L80).

**Lemma · Energy identity for the cutoff.** The squared derivative of the cutoff polynomial splits into its weighted derivative energy, an explicit weighted polynomial square and a total derivative. [`cut_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L85).

**Lemma · The cutoff boundary term vanishes.** The boundary contribution involving the cutoff, its derivative and the polynomial square is zero at the two interval endpoints. [`cut_boundary`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L93).

**Lemma · Bound the cutoff constant.** Choosing the integer cutoff index to bracket half the positive scale bounds the explicit cutoff constant by four over the square root of three times the inverse scale. [`cut_constant`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L100).

**Lemma · Collect the cutoff energy coefficients.** The displayed algebraic identity collects the cutoff trial energy into a quadratic-degree term and a quartic-degree term at positive scale. [`cut_algebra`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L145).

**Theorem · Closed estimate for the interval.** The interval identity and minimality inputs yield the explicit degree-dependent bound for the smoothed polynomial pairing. [`intervalClosed_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosed.lean#L165).

### Breakdown.FracCell.IntervalClosedBounds

Explicit polynomial kernels on the unit interval give pointwise and derivative-energy bounds with constants depending only on the degree. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Polynomial with negative integer roots.** The polynomial is the product of the linear factors whose roots are the first n plus one negative integers. [`nodeUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L20).

**Definition · Polynomial with nonnegative roots.** The polynomial is the product of the linear factors with roots zero through n. [`nodeDown`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L22).

**Definition · Remove one negative-root factor.** The polynomial multiplies all the negative-root factors except the selected index. [`partUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L24).

**Definition · Interpolation coefficient at a root.** The coefficient is the negative ratio of the nonnegative-root polynomial to the omitted-factor polynomial at the selected negative root. [`weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L26).

**Lemma · The negative-root polynomial is monic.** The product defining the negative-root polynomial has leading coefficient one. [`monic_nodeUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L28).

**Lemma · The nonnegative-root polynomial is monic.** The product defining the nonnegative-root polynomial has leading coefficient one. [`monic_nodeDown`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L30).

**Lemma · The omitted-factor polynomial is monic.** Removing one indexed factor from the product leaves a monic polynomial. [`monic_partUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L32).

**Lemma · Degree of the negative-root polynomial.** The negative-root polynomial indexed by n has degree n plus one. [`natDegree_nodeUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L34).

**Lemma · Degree of the root polynomial.** The nonnegative-root polynomial indexed by n has degree n plus one. [`natDegree_nodeDown`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L38).

**Lemma · Degree after removing a factor.** Removing a factor whose index is in range gives a polynomial of degree n. [`natDegree_partUp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L42).

**Lemma · Leading terms cancel in the difference.** The difference of the two monic degree n plus one products has degree at most n. [`natDegree_nodeUp_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L47).

**Lemma · The omitted-root value is nonzero.** The omitted-factor polynomial is nonzero at the negative point corresponding to its omitted index. [`eval_partUp_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L60).

**Lemma · Other indexed roots remain roots.** At an in-range negative root different from the omitted index, the omitted-factor polynomial vanishes. [`eval_partUp_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L69).

**Lemma · The negative nodes are roots.** The negative-root polynomial vanishes at every negative integer node in its index range. [`eval_nodeUp_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L75).

**Lemma · Decompose the difference of products.** The difference of the two root polynomials equals the weighted sum of their omitted-factor polynomials. [`decomp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L80).

**Lemma · Reciprocal moments of the weights.** For each index in range, summing the interpolation weights divided by the pairwise index sum plus one gives one. [`weight_sum_inv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L101).

**Lemma · Sum of consecutive odd integers.** The first n plus one odd positive integers sum to the square of n plus one. [`sum_odd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L131).

**Lemma · Sum of interpolation weights.** The interpolation weights sum to the square of n plus one. [`weight_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L139).

**Definition · Endpoint evaluation kernel.** The kernel polynomial uses the interpolation weights as its monomial coefficients. [`kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L165).

**Lemma · Degree bound for the kernel.** The endpoint kernel indexed by n has degree at most n. [`natDegree_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L167).

**Lemma · Kernel value at the right endpoint.** The endpoint kernel at one equals the square of n plus one. [`eval_kernel_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L171).

**Lemma · Monomial integral on the unit interval.** The integral of the mth power from zero to one equals the reciprocal of m plus one. [`integral_pow_zero_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L176).

**Lemma · The kernel reproduces endpoint values.** Integrating a polynomial of degree at most n against the nth kernel gives its value at one. [`reproduce`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L180).

**Lemma · Cauchy–Schwarz for polynomial integrals.** For real polynomials f and g with positive integral of g² on [0,1], the square of the integral of fg is at most the product of the integrals of f² and g². [`polyInner_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L213).

**Lemma · Right endpoint controlled by L2 norm.** For a real polynomial of degree at most n, its squared value at one is at most $(n+1)^2$ times its integral of its square on [0,1]. [`sq_eval_one_le_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L236).

**Lemma · Endpoint bound on the symmetric interval.** For a real polynomial of degree at most q, its squared value at one is at most $(q+1)^2/2$ times its integral of its square on [-1,1]. [`sq_eval_one_le_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L248).

**Definition · Orthogonal kernel differences.** The polynomial family starts with the zeroth kernel and then takes differences of consecutive endpoint kernels. [`orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L268).

**Lemma · Degree of the orthogonal polynomial.** The mth kernel-difference polynomial has degree at most m. [`natDegree_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L272).

**Lemma · Orthogonality to lower degrees.** The mth kernel-difference polynomial has zero integral pairing with every polynomial of smaller degree. [`integral_orth_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L278).

**Lemma · Orthogonal polynomial at one.** The mth kernel-difference polynomial takes the value twice m plus one at the right endpoint. [`eval_orth_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L289).

**Lemma · Norm of the orthogonal polynomial.** The integral of the square of the mth kernel-difference polynomial on [0,1] equals $2m+1$. [`integral_orth_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L297).

**Lemma · Orthogonal kernel differences.** Two kernel-difference polynomials with different indices have zero integral pairing. [`integral_orth_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L318).

**Lemma · Nonzero leading interpolation weight.** The interpolation weight at the largest index is nonzero. [`weight_diag_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L326).

**Lemma · Monomial coefficients of the kernel.** The jth kernel coefficient is its interpolation weight inside the index range and zero outside that range. [`coeff_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L337).

**Lemma · Nonzero top orthogonal coefficient.** The coefficient at degree m in the mth kernel-difference polynomial is nonzero. [`coeff_orth_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L355).

**Lemma · Expand in orthogonal kernel differences.** Every polynomial within the degree bound expands in kernel differences with coefficients given by their integral pairings divided by their squared norms. [`expansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L362).

**Lemma · Root polynomial evaluated at minus one.** The nonnegative-root polynomial at minus one is the factorial of n plus one multiplied by its alternating sign. [`eval_nodeDown_neg_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L435).

**Lemma · Omitted-factor value at minus one.** Omitting the first negative-root factor makes the value at minus one equal to n factorial. [`eval_partUp_zero_neg_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L446).

**Lemma · The first interpolation weight.** The first interpolation weight equals n plus one with sign alternating in n. [`weight_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L466).

**Lemma · Kernel value at zero.** The kernel at zero equals its first interpolation weight. [`eval_kernel_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L476).

**Lemma · Left endpoint of the orthogonal family.** The square of the mth kernel-difference polynomial at zero is the square of twice m plus one. [`eval_orth_zero_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L484).

**Lemma · Left endpoint controlled by L2 norm.** For a real polynomial of degree at most n, its squared value at zero is at most $(n+1)^2$ times its integral of its square on [0,1]. [`sq_eval_zero_le_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L497).

**Lemma · Energy of orthogonal derivatives.** The integral of the squared derivative of the mth kernel-difference polynomial on [0,1] is at most $4m^2(2m+1)^2$. [`integral_deriv_orth_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L515).

**Lemma · Sum the derivative-energy coefficients.** The sum of $4m^2(2m+1)$ from m=0 through q is at most $2(q+1)^4$. [`sum_weight_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L578).

**Lemma · Derivative energy on the unit interval.** For a real polynomial of degree at most q, the integral of its squared derivative on [0,1] is at most $2(q+1)^4$ times the integral of its square. [`integral_derivative_sq_le_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L588).

**Lemma · Symmetric-interval derivative energy.** For a real polynomial of degree at most q, the integral of its squared derivative on [-1,1] is at most $(q+1)^4/2$ times the integral of its square. [`integral_derivative_sq_le_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L663).

**Theorem · Polynomial endpoint estimate.** For a real polynomial of degree at most q, its squared value at one is at most $(q+1)^2/2$ times its integral of its square on [-1,1]. [`sq_eval_one_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L700).

**Theorem · Polynomial derivative-energy estimate.** For a real polynomial of degree at most q, the integral of its squared derivative on [-1,1] is at most $(q+1)^4/2$ times the integral of its square. [`integral_derivative_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L704).

**Lemma · Pointwise bound on the positive half.** For a real polynomial of degree at most q and a point in [0,1], its squared value is at most $(q+1)^2$ times its integral of its square on [-1,1]. [`sq_eval_le_of_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L709).

**Theorem · Pointwise polynomial bound.** At every point of [-1,1], the squared value of a real polynomial of degree at most q is at most $(q+1)^2$ times its integral of its square on that interval. [`sq_eval_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalClosedBounds.lean#L744).

### Breakdown.FracCell.IntervalIdentity

The polynomial and hyperbolic formula for the interval resolvent satisfies its differential equation, endpoint conditions and energy identity. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · Second derivative of the even series.** For nonzero parameter, the second derivative of the finite even-derivative series is the parameter times that series minus the original polynomial. [`evenSeries_second_derivative`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalIdentity.lean#L14).

**Lemma · Differentiate the hyperbolic correction.** The derivative of a polynomial minus its hyperbolic correction is the polynomial derivative minus the corresponding scaled sinh and cosh terms. [`hasDerivAt_combination`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalIdentity.lean#L33).

**Lemma · Differentiate the correction twice.** The second derivative of the corrected polynomial has the second polynomial derivative minus the twice-scaled hyperbolic terms. [`hasDerivAt_combination_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalIdentity.lean#L39).

**Lemma · Energy identity from the resolvent form.** A corrected polynomial satisfying the resolvent equation and zero endpoint values is twice continuously differentiable and obeys the interval energy identity. [`identity_of_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalIdentity.lean#L47).

**Theorem · The interval resolvent energy identity.** The theorem proves the resolvent's second-order regularity, zero endpoint values and equality between its residual-plus-derivative energy and smoothed pairing. [`intervalIdentity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalIdentity.lean#L95).

### Breakdown.FracCell.IntervalMinimal

The interval resolvent differential equation and energy identity show that its smoothed pairing is bounded by every admissible trial energy. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Differential equation of the even series.** For nonzero parameter, the second derivative of the even series equals the parameter times its difference from the original polynomial. [`evenSeries_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMinimal.lean#L16).

**Theorem · Second derivative of the corrected form.** The second derivative of a polynomial minus the hyperbolic correction equals the polynomial's second derivative minus the scale squared times the correction. [`second_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMinimal.lean#L40).

**Theorem · The interval resolvent equation.** For positive parameter, the second derivative of the interval resolvent equals the parameter times the resolvent minus its polynomial input. [`resolvent_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMinimal.lean#L67).

**Theorem · The interval resolvent minimizes energy.** The interval identity implies that the smoothed pairing is bounded by the residual-plus-derivative energy of any Lipschitz trial function vanishing at both endpoints. [`intervalMinimal_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMinimal.lean#L84).

### Breakdown.FracCell.IntervalMonotone

Clamped trial functions allow the variational estimate to compare the interval smoothed pairing at two positive parameters. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Clamp to the symmetric unit interval.** The real function clips an input below minus one or above one to the respective interval endpoint. [`clampUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L14).

**Theorem · Clamping lies inside the interval.** The clamped input always belongs to the closed symmetric unit interval. [`clampUnit_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L16).

**Theorem · Clamping does not increase distance.** The distance between two clamped values is at most the distance between the original inputs. [`clampUnit_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L19).

**Theorem · Clamping fixes the interval.** A real number already in the closed symmetric unit interval is unchanged by clamping. [`clampUnit_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L27).

**Theorem · Clamped smooth functions are Lipschitz.** A twice continuously differentiable function composed with the interval clamp is globally Lipschitz. [`slope_comp_clamp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L31).

**Theorem · Clamping preserves interior derivatives.** At an interior point, composing any real function with the clamp leaves its derivative unchanged. [`deriv_comp_clamp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L39).

**Theorem · Monotonicity in the resolvent parameter.** The identity and minimality propositions imply that increasing the positive resolvent parameter cannot increase the smoothed polynomial pairing. [`intervalMonotone_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/IntervalMonotone.lean#L45).

### Breakdown.FracCell.LayoutRowNormalFace

The normal part of viscous segment moments is assembled into the four face rows using polynomial trace expansions. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Convert a truncated finite-index sum.** A sum over a finite type restricted to indices at most l equals the natural-index sum through l when l is in range. [`range_sum_fin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L12).

**Theorem · Triangular polynomials span monomials.** A family of degree-indexed polynomials with nonzero leading coefficients spans every monomial expansion within the same finite degree range. [`poly_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L20).

**Theorem · Recover an orthonormal expansion.** For a triangular weighted orthonormal polynomial family, a polynomial equals the sum of its weighted moments times the basis functions. [`poly_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L49).

**Definition · Normal viscous segment contribution.** The definition sums viscous side coefficients against gradient moments only for the component normal to each segment. [`gradSideNormalSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L90).

**Definition · Tangential viscous segment contribution.** The definition sums viscous side coefficients against gradient moments for the components tangent to each segment. [`gradSideTangentSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L99).

**Theorem · Split normal and tangential side terms.** The complete viscous side sum equals its tangential contribution plus its normal contribution. [`gradSide_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L108).

**Theorem · Insert an edge orientation twice.** A complex orientation factor whose square is one can be inserted twice into the viscous product without changing its value. [`edge_alg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L115).

**Theorem · Insert the squared edge sign.** Multiplying both factors of the viscous product by an orientation with square one leaves the product unchanged. [`edge_alg'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L118).

**Theorem · Assemble a normal radial face.** For compatible cell data with polynomial row traces, summing normal radial segment moments gives the oriented viscous radial-face pairing. [`radial_face`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L121).

**Theorem · Assemble a normal height face.** For compatible cell data with polynomial row traces, summing normal height segment moments gives the oriented viscous height-face pairing. [`height_face`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L266).

**Theorem · Collect normal terms on all faces.** With polynomial segment and face traces, the normal viscous segment sum for one mode equals the corresponding sum over the four faces. [`mode_normal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L415).

**Theorem · Normal face row evaluates the side sum.** The strain-face identity and polynomial trace hypotheses identify the total normal viscous side sum with evaluation of the normal face row on true cell data. [`normal_face_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowNormalFace.lean#L525).

### Breakdown.FracCell.LayoutRowPressureBoundary

Lipschitz row traces identify the strip-based pressure moments with actual boundary integrals and convert the pressure pairing into segment data. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Subtract points at a common angle.** Subtracting two cylindrical points with the same angle subtracts their radial and height coordinates. [`cyl_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L14).

**Theorem · Recover the cylindrical radius.** For nonnegative radial coordinate, the cylindrical radius of the constructed point equals that coordinate. [`cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L18).

**Theorem · Recover the cylindrical height.** The height of a point built in cylindrical coordinates equals its supplied height coordinate. [`cyl_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L24).

**Theorem · A cell rectangle maps into its solid.** Every angle sends a point of a valid cell rectangle into the cell solid with nonnegative height. [`cyl_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L27).

**Theorem · Bound distance along a fixed angle.** At a fixed angle, the spatial distance of cylindrical points is at most twice the distance of their radius-height coordinates. [`cyl_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L40).

**Theorem · The angular circle is continuous.** At fixed radius and height, the cylindrical point varies continuously with angle. [`cyl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L48).

**Theorem · The mode integrand is continuous.** A continuous field along the angular circle has a continuous phase-weighted frame-component integrand. [`integrand_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L53).

**Theorem · Lipschitz bound for mode integrands.** For a Lipschitz field, the difference of phase-weighted frame integrands is bounded by twice its Lipschitz constant times radius-height distance. [`integrand_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L63).

**Theorem · Modes inherit a Lipschitz bound.** If all relevant circles lie in a field's Lipschitz domain, each angular mode is Lipschitz in radius and height with twice the field constant. [`mode_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L84).

**Theorem · Row modes are Lipschitz on a cell.** The valid cell and row-shape assumptions give a Lipschitz bound for each row-mode component on the rectangle. [`row_mode_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L107).

**Theorem · A Lipschitz derivative is integrable.** The derivative of a Lipschitz complex function is integrable on every finite interval. [`deriv_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L114).

**Theorem · Affine product rule under a real map.** Applying a real linear functional to the affine product-rule integral gives the corresponding weighted endpoint values of a Lipschitz function. [`part_ftc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L119).

**Theorem · Affine product rule on an interval.** The integral of a Lipschitz function times an affine derivative plus its derivative times the affine function equals the endpoint product difference. [`slice_ftc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L152).

**Theorem · Normalized affine product rule.** The normalized affine product-rule integral equals the difference of the normalized endpoint products for a Lipschitz complex function. [`slice_ftc'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L163).

**Theorem · Radial strip moment equals a trace.** For a Lipschitz rectangle function and distinct face levels, its radial strip moment equals the tested integral of its value on the selected face. [`radial_strip_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L170).

**Theorem · Height strip moment equals a trace.** For a Lipschitz rectangle function and distinct height levels, its unweighted height strip moment equals the tested integral on the selected face. [`height_strip_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L278).

**Theorem · Segment test polynomials are continuous.** Every segment test polynomial is a continuous real function. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L294).

**Theorem · Trace coefficients are boundary moments.** For compatible cell and pressure data, a row's segment trace equals the integral of its represented boundary function against the segment test polynomial. [`trace_coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L298).

**Theorem · Pressure pairing becomes boundary data.** For an admissible field and polynomial normal row traces, the pressure-gradient pairing equals the oriented sum of pressure segment moments weighted by conjugate trace coefficients. [`boundary_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundary.lean#L355).

### Breakdown.FracCell.LayoutRowPressureBoundaryParts

The pressure mode equation, divergence-free row identity and segment partitions turn radial and height integration by parts into pressure boundary sums. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Angular pressure mode derivative.** For an admissible field, radius times the angular pressure-gradient mode equals the pressure mode multiplied by the imaginary angular frequency almost everywhere off the axis. [`pressure_angular_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L20).

**Theorem · Differentiate an angular integral.** A twice differentiable field along a differentiable family of circles can be differentiated under its continuous weighted angular integral. [`cmode_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L74).

**Theorem · Divergence-free identity for row modes.** For compatible cell and row data, the weighted radial derivative, angular-frequency term and weighted height derivative of a row mode sum to zero inside the cell. [`row_mode_divergence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L93).

**Theorem · Partition a rectangle into height strips.** A finite cover by nonoverlapping height intervals splits an integrable rectangle integral into the sum over those strips. [`strip_partition`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L272).

**Theorem · Partition a rectangle into radial strips.** A finite cover by nonoverlapping radial intervals splits an integrable rectangle integral into the sum over those strips. [`strip_partition_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L307).

**Theorem · Pressure segments cover a radial face.** The pressure segments on a selected radial face cover its height interval, lie within it and have pairwise disjoint interiors. [`radial_side_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L342).

**Theorem · Pressure segments cover a height face.** The pressure segments on a selected height face cover its radial interval, lie within it and have pairwise disjoint interiors. [`height_side_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L365).

**Theorem · Conjugate a radial derivative.** The radial derivative of a conjugated complex field is the conjugate of its radial derivative under the differentiability hypothesis. [`radialDeriv_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L388).

**Theorem · Conjugate a height derivative.** The height derivative of a conjugated complex field is the conjugate of its height derivative under the differentiability hypothesis. [`heightDeriv_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L393).

**Theorem · Subtract points at a common angle.** Subtracting two cylindrical points with the same angle subtracts their radial and height coordinates. [`lp_cyl_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L398).

**Theorem · Recover the cylindrical radius.** For nonnegative radial coordinate, the cylindrical radius of the constructed point equals that coordinate. [`lp_cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L402).

**Theorem · Recover the cylindrical height.** The height of a point built in cylindrical coordinates equals its supplied height coordinate. [`lp_cyl_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L408).

**Theorem · A cell rectangle maps into its solid.** Every angle sends a point of a valid cell rectangle into the cell solid with nonnegative height. [`lp_cyl_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L411).

**Theorem · Bound distance along a fixed angle.** At a fixed angle, the spatial distance of cylindrical points is at most twice the distance of their radius-height coordinates. [`lp_cyl_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L424).

**Theorem · The angular circle is continuous.** At fixed radius and height, the cylindrical point varies continuously with angle. [`lp_cyl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L432).

**Theorem · The mode integrand is continuous.** A continuous field along the angular circle has a continuous phase-weighted frame-component integrand. [`lp_integrand_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L437).

**Theorem · Lipschitz bound for mode integrands.** For a Lipschitz field, the difference of phase-weighted frame integrands is bounded by twice its Lipschitz constant times radius-height distance. [`lp_integrand_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L447).

**Theorem · Modes inherit a Lipschitz bound.** If all relevant circles lie in a field's Lipschitz domain, each angular mode is Lipschitz in radius and height with twice the field constant. [`lp_mode_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L468).

**Theorem · Row modes are Lipschitz on a cell.** The valid cell and row-shape assumptions give a Lipschitz bound for each row-mode component on the rectangle. [`lp_row_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L491).

**Theorem · Lipschitz bound after radial weighting.** A bounded Lipschitz function multiplied by radius and conjugated is Lipschitz with the radius-bound times the old constant plus the value bound. [`lp_coord_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L498).

**Theorem · Segment test polynomials are continuous.** Every segment test polynomial is a continuous real function. [`lp_test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L518).

**Theorem · The edge sign squares to one.** For distinct face levels, multiplying the edge orientation sign by itself gives one. [`lp_edge_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L522).

**Theorem · Bound an interval symmetrically.** A closed interval lies inside the symmetric interval whose radius is the sum of the absolute values of its endpoints. [`lp_box_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L525).

**Theorem · Convert a radial face to segment moments.** Under the pressure-segment cover and polynomial trace hypotheses, the radial affine-strip integral equals the oriented sum of pressure segment moments on that face. [`radial_side_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L531).

**Theorem · Convert a height face to segment moments.** Under the pressure-segment cover and polynomial trace hypotheses, the weighted height affine-strip integral equals the oriented sum of pressure segment moments on that face. [`height_side_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L610).

**Theorem · Radial pressure pairing at the boundary.** For compatible cell data and polynomial traces, the radial pressure product-rule integrand is integrable and its integral equals the radial pressure segment sum. [`radial_side_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L689).

**Theorem · Height pressure pairing at the boundary.** For compatible cell data and polynomial traces, the weighted height pressure product-rule integrand is integrable and its integral equals the height pressure segment sum. [`height_side_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureBoundaryParts.lean#L780).

### Breakdown.FracCell.LayoutRowPressureModeIdentity

Orthonormal segment tests recover the pressure row coefficients from boundary traces and close the pressure identity for each mode. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Segment test polynomials are continuous.** Every segment test polynomial is a continuous real function. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureModeIdentity.lean#L12).

**Theorem · Recover a coefficient from its trace.** For an orthonormal segment test family, integrating a finite test expansion against one basis test recovers its coefficient. [`coef_of_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureModeIdentity.lean#L16).

**Theorem · Pressure row identity for one mode.** With compatible cell data and polynomial normal pressure traces, the pressure-gradient pairing for one mode equals the sum of pressure row coefficients times segment moments. [`mode_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureModeIdentity.lean#L46).

### Breakdown.FracCell.LayoutRowPressureSideCore

Piecewise linear tent approximations extend weak radial and height integration by parts to Lipschitz tests and express their boundary terms through strip moments. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Tent value and slope on the right.** On the right half of an equal-width tent, the value is the descending affine ramp and the slope is minus the inverse width. [`tent_right_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L11).

**Theorem · Tent value and slope on the left.** On the left half of an equal-width tent, the value is the ascending affine ramp and the slope is the inverse width. [`tent_left_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L23).

**Theorem · The tent and slope vanish outside.** Outside the closed support interval of an ordered tent, both its value and its chosen slope are zero. [`tent_outside`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L34).

**Theorem · The tent is bounded by a radial ramp.** With nonnegative left endpoint and argument, the tent value is at most the argument divided by the left interval width. [`tent_le_ramp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L44).

**Theorem · Tent values are at most one.** An ordered tent function is bounded above by one everywhere. [`tent_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L55).

**Theorem · Tent values are nonnegative.** Every value of the tent function is nonnegative. [`tent_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L63).

**Theorem · A nonnegative tent starts at zero.** An ordered tent with nonnegative left endpoint vanishes at zero. [`tent_at_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L66).

**Theorem · Bound the tent slope.** The absolute tent slope is bounded by the sum of the inverse left and right widths. [`slope_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L70).

**Theorem · The chosen tent slope is measurable.** The piecewise-defined tent slope is measurable for all three endpoint parameters. [`slope_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L80).

**Theorem · The tent function is continuous.** The tent function is continuous for every choice of its endpoint parameters. [`tent_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L85).

**Theorem · Enclose an interval symmetrically.** A closed interval lies in the symmetric interval of radius equal to the sum of its endpoint absolute values. [`icc_sub_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L90).

**Theorem · Countably many vertical lines are null.** The product of a countable radial set with the whole height line has zero planar Lebesgue measure. [`null_fst_set`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L96).

**Theorem · Countably many horizontal lines are null.** The product of the whole radial line with a countable height set has zero planar Lebesgue measure. [`null_snd_set`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L99).

**Theorem · Radial slices are a.e. differentiable.** A globally Lipschitz complex function of two variables is differentiable along its radial slices at almost every planar point. [`ae_diff_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L102).

**Theorem · Height slices are a.e. differentiable.** A globally Lipschitz complex function of two variables is differentiable along its height slices at almost every planar point. [`ae_diff_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L113).

**Theorem · Locate a point between grid nodes.** A point strictly inside a uniform grid interval and outside its nodes lies strictly between two consecutive grid nodes. [`grid_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L122).

**Theorem · Evaluate the tent interpolation sum.** Inside a grid cell, the weighted tent-and-slope sum reduces to the linear interpolant of the two endpoint values and their difference quotient. [`grid_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L139).

**Theorem · Interpolation converges with its slope.** For intervals shrinking around a differentiability point of a Lipschitz function, the interpolated value and difference quotient converge to the function and derivative combination. [`straddle_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L172).

**Theorem · Bound slopes and interpolation.** For a Lipschitz function vanishing at a left basepoint, the interpolation-and-slope combination is bounded by the stated value-distance term and Lipschitz term. [`interp_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L242).

**Theorem · Radial tent testing is integrable.** A radial weak pair tested with a radial tent and continuous height factor gives an integrable function on a finite nonnegative rectangle. [`tent_int_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L279).

**Theorem · Radial tent testing has zero integral.** If a tent is supported inside the radial interval, testing a radial weak pair with that tent and a continuous height factor has zero integral. [`tent_zero_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L324).

**Theorem · Height tent testing is integrable.** A height weak pair tested with a height tent, radius and a continuous radial factor gives an integrable rectangle function. [`tent_int_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L356).

**Theorem · Height tent testing has zero integral.** A tent supported inside the height interval gives zero integral when used in the radial-weighted height weak identity. [`tent_zero_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L392).

**Theorem · A radial grid term integrates to zero.** For a continuous test vanishing on both radial faces, each sampled radial tent term is integrable and has zero integral. [`node_term_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L403).

**Theorem · A height grid term integrates to zero.** For a continuous test vanishing on both height faces, each radial-weighted sampled height tent term is integrable and has zero integral. [`node_term_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L428).

**Theorem · Uniform mesh widths shrink to zero.** Dividing a nonempty interval into N plus one equal pieces gives positive widths, the correct final endpoint and widths converging to zero. [`step_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L453).

**Theorem · Avoid every uniform grid node.** A point outside all rational affine subdivisions avoids every node of each finite uniform subdivision. [`off_grid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L462).

**Theorem · Lipschitz bounds on radial slices.** Fixing the height in a globally Lipschitz rectangle function preserves its Lipschitz constant in radius. [`slope_slice_fst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L471).

**Theorem · Lipschitz bounds on height slices.** Fixing the radius in a globally Lipschitz rectangle function preserves its Lipschitz constant in height. [`slope_slice_snd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L475).

**Theorem · Radial weak identity for Lipschitz tests.** A globally Lipschitz test vanishing at both radial faces makes the radial product-rule sum integrable with zero integral on the rectangle. [`radial_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L479).

**Theorem · Height weak identity for Lipschitz tests.** A globally Lipschitz test vanishing at both height faces makes the radial-weighted height product-rule sum integrable with zero integral. [`height_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L574).

**Theorem · Local Lipschitz radial test identity.** A test Lipschitz on the rectangle and vanishing on both radial faces satisfies the integrable radial product-rule identity with zero integral. [`radial_slope_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L679).

**Theorem · Local Lipschitz height test identity.** A test Lipschitz on a nonnegative-radius rectangle and vanishing on both height faces satisfies the weighted height product-rule identity with zero integral. [`height_slope_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L721).

**Theorem · Bounds on compact Lipschitz domains.** A function Lipschitz on a compact set has a nonnegative uniform bound on its norm there. [`slope_bound_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L764).

**Theorem · Lipschitz constant for a bounded product.** The product of two bounded Lipschitz functions has Lipschitz constant bounded by each function's value bound times the other's Lipschitz constant, added together. [`slope_mul_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L769).

**Theorem · Lipschitz constant of the radial ramp.** The complex radial affine ramp has Lipschitz constant equal to the absolute inverse scale converted to a nonnegative real. [`ramp_slope_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L787).

**Theorem · Lipschitz constant of the height ramp.** The complex height affine ramp has Lipschitz constant equal to the absolute inverse scale converted to a nonnegative real. [`ramp2_slope_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L796).

**Theorem · A vertical line has zero measure.** A fixed radial coordinate times the entire height line has zero planar Lebesgue measure. [`null_line`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L805).

**Theorem · A horizontal line has zero measure.** The entire radial line times a fixed height coordinate has zero planar Lebesgue measure. [`null_line2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L808).

**Theorem · A.e. radial derivatives on a rectangle.** A function Lipschitz on a closed rectangle is differentiable along radial slices almost everywhere with respect to restricted area measure. [`ae_line_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L811).

**Theorem · A.e. height derivatives on a rectangle.** A function Lipschitz on a closed rectangle is differentiable along height slices almost everywhere with respect to restricted area measure. [`ae_line_diff2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L848).

**Theorem · A symmetric bound for an interval.** Every point of a closed interval has absolute value at most the sum of the absolute values of its endpoints. [`box_sub'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L883).

**Theorem · Radial Lipschitz boundary terms.** For a radial weak pair, a Lipschitz test with the required axis vanishing gives an integrable product-rule sum whose integral equals the two affine-strip boundary terms. [`radial_slope_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L889).

**Theorem · Height Lipschitz boundary terms.** For a radial-weighted height weak pair, a Lipschitz rectangle test gives an integrable product-rule sum whose integral equals the two height affine-strip boundary terms. [`height_slope_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowPressureSideCore.lean#L988).

### Breakdown.FracCell.LayoutRowValue

The volume, viscous-face and pressure identities are combined to identify a physical low-row value with evaluation of the finite layout row. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · L2 fields have integrable pairings.** The pointwise inner product of two L2 spatial fields is integrable. [`inner_integrable_of_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValue.lean#L21).

**Theorem · Split the model row pairing.** When its component pairings are integrable, the model-plus-pressure row pairing splits into transport, viscous trace, pressure and actuator contributions. [`field_pairing_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValue.lean#L27).

**Theorem · Split the finite layout row sum.** Evaluating the layout row data on true cell data gives the sum of the strain, velocity, viscous-side and pressure-side contributions. [`data_sum_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValue.lean#L56).

**Theorem · Identify the low row from strain faces.** The strain-face proposition supplies the remaining input needed to equate the physical low-row value with the finite layout-row evaluation. [`layoutRowValue_of_strainFace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValue.lean#L68).

**Theorem · The layout row evaluates the low row.** The theorem proves that compatible cell and pressure-layout data with the required polynomial traces represent the physical low-row value exactly. [`layoutRowValue_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValue.lean#L86).

### Breakdown.FracCell.LayoutRowValueModes

Angular Fourier expansions and reflection symmetry reduce a three-dimensional row pairing to finitely many weighted mode pairings on the cell rectangle. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Reduce a spatial pairing to the cell.** A supported, integrable, reflection-symmetric pairing with a known angular integral equals four pi times its radial-weighted rectangle integral. [`pairing_mode_reduction`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L17).

**Theorem · Inner products in the moving frame.** A spatial inner product equals the sum of the three products of its moving-frame components. [`frame_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L41).

**Theorem · Conjugate the Fourier integral.** For a real integrand, the positive-phase integral is the complex conjugate of the corresponding negative-phase integral. [`mode_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L51).

**Theorem · Interval integrability of finite sums.** A finite sum of interval-integrable complex functions remains interval integrable. [`sum_ii`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L60).

**Theorem · Move the real part through an integral.** The integral of a real factor times a complex real part equals the real part of the corresponding complex product integral. [`re_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L66).

**Theorem · Pair an angular mode expansion.** An angularly integrable field paired with a finite row expansion has circle integral equal to two pi times the real sum of mode pairings. [`circle_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L77).

**Theorem · Express a spatial pairing by modes.** Support, integrability, reflection symmetry and a finite angular row expansion give the spatial pairing as four pi times the weighted rectangle sum of mode pairings. [`pairing_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L130).

**Theorem · Reflection preserves inner products.** Reflecting both spatial vectors leaves their inner product unchanged. [`mirror_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L144).

**Theorem · Class-field pairings respect reflection.** The pointwise pairing of two fields in the same symmetry class is reflection invariant almost everywhere. [`class_pairing_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueModes.lean#L150).

### Breakdown.FracCell.LayoutRowValueParts

This file defines the four finite row contributions and supplies the measurability, bounds and integrability needed to split transport and high-mode coupling. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The transport part of the model.** The transport field combines the similarity drift with curl-velocity cross products involving the model and perturbation fields. [`transportPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L17).

**Definition · Gradient pairing against a row.** The definition integrates the matrix-entry pairing of the perturbation gradient with the derivative of the selected row. [`gradientPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L21).

**Definition · Finite strain-coefficient contribution.** The strain sum pairs each retained strain row coefficient with the corresponding true gradient-mode coefficient. [`strainSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L24).

**Definition · Finite velocity-coefficient contribution.** The velocity sum pairs each retained velocity row coefficient with the corresponding true velocity-mode coefficient. [`velocitySum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L30).

**Definition · Viscous segment-moment contribution.** The viscous side sum pairs each segment coefficient with the normal gradient trace moment in the segment's radial or height direction. [`gradSideSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L36).

**Definition · Pressure segment-moment contribution.** The pressure side sum pairs retained pressure row coefficients with pressure trace moments on the selected segments. [`presSideSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L45).

**Theorem · The cell solid is measurable.** The spatial solid associated with a cell box is a measurable set. [`solid_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L52).

**Theorem · A selected row is globally bounded.** For valid form, cell and row-shape data, every selected row has a uniform bound on its spatial norm. [`row_bounded`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L62).

**Theorem · The cell solid has finite volume.** The spatial solid associated with a cell box has finite Lebesgue volume. [`solid_finite`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L104).

**Theorem · A bounded supported row can be paired.** A bounded measurable row supported in a measurable set has an integrable pairing with a measurable field whose norm is integrable on that set. [`inner_row_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L109).

**Theorem · L2 implies L1 on finite volume.** A measurable field with integrable squared norm has integrable norm on a finite-volume set. [`integrableOn_of_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L122).

**Theorem · Bound continuous fields on compact sets.** A continuous spatial field has a nonnegative uniform norm bound on any compact set. [`bound_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L130).

**Theorem · Transport is locally integrable.** Under the field and model regularity hypotheses, the transport part is measurable and its norm is integrable on the stated bounded region. [`transport_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L135).

**Theorem · Second traces are locally integrable.** The regularity hypotheses on the second derivative make its trace measurable with integrable norm on the specified finite region. [`trace_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L203).

**Theorem · Gradient fields are locally integrable.** A gradient field is measurable and has integrable norm on a finite-volume set contained in a compact set. [`pressure_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L236).

**Theorem · Continuity of cell projections.** Every finite-degree cell projection is a continuous function. [`proj_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L243).

**Theorem · The cylindrical angle is measurable.** The chosen cylindrical angle function is measurable. [`angle_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L252).

**Theorem · The reflection sign is measurable.** The coordinate sign used in the reflected frame construction is measurable. [`sign_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L256).

**Theorem · Continuity of the angular frame.** Each cylindrical frame vector is a continuous function of the angle. [`unit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L262).

**Theorem · A uniform bound for frame vectors.** The norm of each cylindrical frame vector is at most two. [`unit_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L268).

**Theorem · Frame rank-one operators are continuous.** The rank-one operator formed from two cylindrical frame vectors varies continuously with angle. [`op_term_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L280).

**Theorem · Bound a reconstructed frame matrix.** The norm of a Cartesian operator reconstructed from frame entries is at most four times the sum of their absolute values. [`op_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L285).

**Theorem · Bound a reconstructed frame vector.** The norm of a Cartesian vector reconstructed from frame coordinates is at most twice the sum of their absolute values. [`vec_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L295).

**Theorem · Continuity of absolute cell coordinates.** The map taking a spatial point to its radius and absolute height is continuous. [`rho_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L302).

**Theorem · Solid coordinates lie in the rectangle.** The radius and absolute height of a point in the cell solid belong to the cell rectangle. [`rho_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L305).

**Theorem · Reflection signs have absolute value one.** Every coordinate reflection sign has absolute value one. [`sign_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L308).

**Theorem · Measurability of the Fourier phase.** The complex angular Fourier phase is a measurable function of the spatial point. [`wave_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L311).

**Theorem · Measurability of reconstructed modes.** Continuous radius-height coefficients give a measurable real field after finite Fourier summation and reflection in height. [`mode_sum_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L315).

**Theorem · Bound a finite mode sum on the solid.** Continuous radius-height coefficients give a uniform bound for the reconstructed finite mode sum on the cell solid. [`mode_sum_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L321).

**Theorem · Bounded measurable low gradient.** The reconstructed low-gradient field is measurable and uniformly bounded on the cell solid. [`lowGrad_props`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L333).

**Theorem · Bounded measurable low velocity.** The reconstructed low-velocity field is measurable and uniformly bounded on the cell solid. [`lowVel_props`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L353).

**Theorem · High coupling is integrable on the solid.** Under the admissibility and cell-data hypotheses, the high-mode coupling is measurable and has integrable norm on the cell solid. [`coupling_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L373).

**Theorem · High coupling can be paired with a row.** The high-mode coupling field has an integrable pointwise pairing with each permitted row. [`coupling_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L423).

**Theorem · The four row pairings are integrable.** The transport, second trace, pressure and high-coupling terms all have integrable pairings with a selected row under the admissible cell-data hypotheses. [`pairings_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L440).

**Theorem · Curl extraction preserves subtraction.** Extracting curl from a difference of linear maps gives the difference of their extracted curls. [`curlOf_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L466).

**Theorem · Cross product distributes on the left.** The cross product of a vector difference with a fixed vector equals the difference of the two cross products. [`crossVec_sub_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L470).

**Theorem · Cross product distributes on the right.** The cross product of a fixed vector with a vector difference equals the difference of the two cross products. [`crossVec_sub_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L474).

**Definition · Transport using retained low fields.** The definition keeps the drift and replaces the two perturbation factors in the model cross products by their low-gradient and low-velocity reconstructions. [`lowTransport`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L478).

**Theorem · Remove high coupling pointwise.** Subtracting the high-mode coupling from the full transport field gives the low-transport field pointwise. [`transport_sub_coupling_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L483).

**Theorem · Remove high coupling in the row pairing.** The low-transport row pairing is integrable and equals the full transport pairing minus the high-coupling pairing. [`transport_sub_coupling`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L489).

**Theorem · Low transport is integrable on the solid.** The low-transport field is measurable and has integrable norm on the cell solid under the compatible admissibility hypotheses. [`lowTransport_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L505).

**Theorem · Second trace is integrable on the solid.** The admissible second-derivative trace is measurable and has integrable norm on the cell solid. [`secondTrace_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueParts.lean#L529).

### Breakdown.FracCell.LayoutRowValuePressure

Finite row Fourier support and pressure trace identities reduce the physical pressure pairing to the pressure side sum with its four-pi normalization. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Reconstruct finite Fourier support.** A continuous periodic function with vanishing Fourier coefficients outside a finite set equals its finite Fourier expansion when the symmetry order is positive. [`trig_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L14).

**Theorem · Continuity of cylindrical coordinates.** The spatial point depends continuously on its radius, height and angle arguments jointly. [`cyl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L82).

**Theorem · The symmetry rotation is continuous.** The rotation through the symmetry step is a continuous spatial map. [`turn_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L87).

**Theorem · Angular shift equals spatial rotation.** Adding one symmetry angle to a cylindrical point equals rotating that point by the symmetry step. [`turn_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L92).

**Theorem · The moving frame respects rotation.** Rotating a vector and shifting its frame angle by the symmetry step leaves its frame components unchanged. [`turn_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L97).

**Theorem · The symmetry rotation preserves radius.** The cylindrical radius is unchanged by one symmetry rotation. [`turn_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L107).

**Theorem · The symmetry rotation preserves height.** The cylindrical height is unchanged by one symmetry rotation. [`turn_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L114).

**Theorem · Cylindrical cell points lie in the solid.** Every angle sends a point of the valid cell rectangle into its spatial solid. [`mem_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L117).

**Theorem · The upper cell interior is open.** The strict radial and height inequalities defining the upper cell interior form an open spatial set. [`upper_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L126).

**Theorem · Cell points lie in the upper solid.** Cylindrical points from the valid cell rectangle lie in the cell solid with nonnegative height. [`mem_upper`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L133).

**Theorem · Rotation symmetry inside the cell.** Continuity on the upper solid upgrades a class field's rotational symmetry to every point in the strict cell interior. [`turn_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L140).

**Theorem · Symmetry period of row frame components.** The frame components of the row along a circle repeat after one symmetry angle under the stated symmetry hypotheses. [`frame_periodic_f`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L163).

**Theorem · Rows equal their finite mode expansions.** For valid row-shape data, each row frame component equals the real part of its retained finite angular mode expansion on the cell rectangle. [`row_expansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L195).

**Theorem · Identify the cylindrical coordinate map.** The inverse cylindrical change of variables followed by the spatial identification gives the usual cylindrical point formula. [`cyl_fun_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L227).

**Theorem · Measurability in cylindrical variables.** A spatially measurable field pulled back to positive-radius cylindrical coordinates is almost everywhere strongly measurable for the product measure. [`joint_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L231).

**Theorem · Integrability with the radial Jacobian.** An integrable spatial scalar field pulled back to cylindrical coordinates remains integrable after multiplication by the radial Jacobian. [`joint_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L243).

**Theorem · Full angular period of frame components.** The cylindrical frame component of any spatial field is periodic with period two pi. [`frame_periodic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L257).

**Theorem · Circle-integrable frame components.** The spatial integrability hypotheses imply angular integrability of every frame component for almost every point of the cell rectangle. [`circle_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L262).

**Theorem · Mode kernels are jointly measurable.** The phase-weighted cylindrical mode kernel is almost everywhere strongly measurable on the positive-radius product domain. [`kern_meas_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L303).

**Theorem · Angular modes are measurable.** The angular Fourier coefficient of a measurable spatial field is measurable as a function of positive radius and height. [`mode_meas_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L329).

**Theorem · The mode kernel is bounded by the field.** The norm of the phase-weighted frame-component kernel is at most the norm of the underlying spatial field. [`kern_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L340).

**Theorem · Integrability of radius-weighted modes.** A measurable field with integrable norm on the cell solid has radial-weighted integrable mode norm on the cell rectangle. [`mode_r_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L347).

**Theorem · A uniform field bound also bounds modes.** A global bound on the field norm also bounds the norm of each angular mode component. [`mode_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L407).

**Theorem · Mode pairings are integrable on the cell.** Under the given pressure integrability and bounded-row hypotheses, the radial-weighted pressure-row mode pairing is integrable on the rectangle. [`pair_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L427).

**Theorem · Reflection preserves the norm.** The spatial reflection leaves every vector norm unchanged. [`mirror_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L462).

**Theorem · Selected rows have a uniform norm bound.** The valid cell and row hypotheses provide a global bound for the selected row norm. [`row_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L465).

**Theorem · A vanishing row mode pairs to zero.** If a row mode vanishes throughout the rectangle, its radial-weighted pairing with any pressure mode has zero integral. [`mode_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L503).

**Theorem · Sum the pressure mode identities.** For compatible cell data and polynomial pressure traces, the real weighted sum of pressure-row mode pairings equals the real pressure side sum. [`pressure_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L510).

**Theorem · The physical pressure row identity.** Under compatible cell and trace hypotheses, the physical pressure-row pairing divided by four pi equals the real part of the pressure side sum. [`pressure_identity_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValuePressure.lean#L566).

### Breakdown.FracCell.LayoutRowValueVolume

Moving-frame algebra, Fourier products and polynomial pairings identify the volume strain and velocity coefficients with the physical transport and viscous gradient pairings. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Two basis-value definitions agree.** The layout basis value equals the complex-valued cell basis function at the same radial and height indices. [`basisVal_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L18).

**Theorem · Convert radial weight to line weight.** An identity after multiplication by the modified radial factor becomes the corresponding identity between radius weighting and cell line weighting. [`weight_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L20).

**Theorem · Polynomial spaces preserve conjugation.** Complex conjugation preserves the radial and height degree bounds of the bivariate polynomial space. [`poly_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L36).

**Theorem · Polynomial testing recovers the pairing.** For valid cell bases and a test whose modified radial product is a bounded-degree polynomial, summing basis moments against field coefficients recovers the original weighted pairing. [`poly_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L44).

**Theorem · Identify projected coefficient pairings.** For valid cell bases and integrable inputs, the basis-moment sum equals the radial-weighted pairing with the finite cell projection. [`proj_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L83).

**Theorem · Reflection preserves finite sums.** Reflecting a finite vector sum gives the sum of the reflected vectors. [`mirror_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L112).

**Theorem · Reflection preserves real scaling.** Reflecting a real scalar multiple gives the same scalar multiple of the reflected vector. [`mirror_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L116).

**Theorem · Reflection preserves addition.** The reflection of a sum is the sum of the reflected vectors. [`mirror_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L119).

**Theorem · Reflection preserves subtraction.** The reflection of a difference is the difference of the reflected vectors. [`mirror_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L122).

**Theorem · Axial turn commutes with reflection.** Applying the axial turn and reflection in either order gives the same spatial vector. [`turn_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L125).

**Theorem · Cross products under reflection.** The cross product of a negative reflected first vector and a reflected second vector is the reflection of the original cross product. [`cross_mirror_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L128).

**Theorem · Curl changes parity under reflection.** Conjugating a linear map by spatial reflection changes its extracted curl to the negative reflected curl. [`curl_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L131).

**Theorem · The drift preserves reflection symmetry.** Reflection symmetry of the velocity and its derivative implies reflection symmetry of the similarity drift field. [`drift_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L138).

**Theorem · Reflection of cylindrical frame vectors.** Reflecting a cylindrical frame vector multiplies it by its coordinate parity sign. [`frameUnit_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L143).

**Theorem · Parity signs reconstruct reflection.** Reconstructing a vector from parity-adjusted frame coordinates gives the reflection of the original reconstruction. [`cartOfFrame_sgn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L146).

**Theorem · Transfer reflection across a pairing.** Reflecting the second vector in an inner product gives the same value as reflecting the first vector. [`inner_mirror_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L153).

**Theorem · Reconstruct reflected frame operators.** Multiplying frame matrix entries by both coordinate signs reconstructs the operator conjugated by spatial reflection. [`cartOp_sgn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L156).

**Theorem · Reflection preserves cylindrical angle.** Reflecting height leaves the cylindrical angle unchanged. [`angle_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L166).

**Theorem · Reflection transforms coordinate signs.** Away from zero height, the coordinate sign at a reflected point equals its original sign times the frame parity sign. [`sign_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L169).

**Theorem · The low velocity respects reflection.** The reconstructed low-velocity field transforms under height reflection as a spatial vector away from the symmetry boundary. [`lowV_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L181).

**Theorem · The low gradient respects reflection.** The reconstructed low-gradient operator transforms under height reflection by conjugating both its input and output. [`lowG_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L191).

**Theorem · Low transport reflects pointwise.** Under the field symmetry hypotheses, low transport at a reflected point is the reflection of its original value. [`lowTransport_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L201).

**Theorem · Reflection of the low-transport pairing.** The low-transport pairing with a valid row is reflection invariant almost everywhere on the cell solid. [`lowTransport_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L211).

**Theorem · Second trace transforms as a vector.** A second-order tensor transformed by reflection has second trace equal to the reflected original trace. [`trace_of_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L224).

**Theorem · Second-trace pairing respects reflection.** The pairing of an admissible second trace with a symmetric row is reflection invariant almost everywhere on the cell solid. [`trace_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L232).

**Theorem · Matrix pairing in the moving frame.** The matrix-entry pairing equals the sum of products of all corresponding moving-frame matrix entries. [`frame_entryInner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L240).

**Theorem · Interval integrability of finite sums.** A finite sum of interval-integrable complex functions remains interval integrable. [`ii_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L249).

**Theorem · Move the real part through an integral.** The integral of a real factor times a complex real part equals the real part of the corresponding complex product integral. [`re_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L255).

**Theorem · Conjugate the Fourier integral.** For a real integrand, the positive-phase integral is the complex conjugate of the corresponding negative-phase integral. [`exp_integral_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L265).

**Theorem · Angular pairing of matrix expansions.** For a finite angular expansion of one matrix field, its circle pairing with an integrable matrix field equals two pi times the real sum of mode-entry pairings. [`circle_pairing_mat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L274).

**Theorem · The rectangle boundary has zero area.** Removing the open rectangle interior from the closed cell rectangle leaves a set of zero planar measure. [`rim_null_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L338).

**Theorem · Interior polynomial testing suffices.** An almost everywhere polynomial test identity on the cell interior suffices to recover the weighted field pairing from its finite coefficients. [`poly_pairing_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L355).

**Definition · The open reflected cell interior.** The open core consists of points satisfying strict radial bounds and strict bounds on absolute height. [`openCore`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L405).

**Theorem · The reflected cell core is open.** The strict radial and absolute-height conditions define an open subset of space. [`openCore_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L408).

**Theorem · The open core lies inside the cell.** Every point of the open cell core belongs to the cell solid. [`openCore_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L414).

**Theorem · The spatial cell boundary is null.** The part of the cell solid outside its open core has zero spatial Lebesgue measure. [`rim_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L417).

**Theorem · Frame entries from Cartesian columns.** A moving-frame matrix entry is the sum of Cartesian column components weighted by the input frame vector's coordinates. [`frameMat_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L464).

**Theorem · Circle-integrable gradient entries.** For an admissible field, every moving-frame gradient entry is integrable around almost every cell circle. [`gradient_circle_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L473).

**Theorem · The cell solid is closed.** The cell solid defined by closed radial and absolute-height intervals is a closed spatial set. [`solid_isClosed`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L504).

**Theorem · Rows have zero derivative off the solid.** For valid cell data, a selected row has zero derivative at every point outside the cell solid. [`row_deriv_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L511).

**Theorem · Reflection negates height.** The cylindrical height of a reflected point is the negative of its original height. [`vol_height_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L520).

**Theorem · Reflection preserves spatial norm.** Reflecting a spatial vector leaves its norm unchanged. [`vol_norm_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L523).

**Theorem · The cell core is reflection invariant.** A reflected point belongs to the open cell core exactly when the original point does. [`core_mirror_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L527).

**Theorem · The upper solid contains a neighbourhood.** An interior point with positive height has a neighbourhood contained in the nonnegative-height part of the cell solid. [`upper_nhds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L530).

**Theorem · Reflect a row near a lower point.** Near a negative-height interior point, the row agrees with the reflection of its values at reflected points. [`lower_eq_near`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L536).

**Theorem · Derivative of the reflected lower row.** At a lower interior point, the row derivative is obtained by reflecting the input and output of the derivative at the reflected point. [`lower_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L544).

**Theorem · Lipschitz bound for the upper derivative.** The derivative norm of the upper row at an interior point is at most its Lipschitz constant. [`upper_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L557).

**Theorem · Bound row derivatives on both halves.** A Lipschitz bound for the upper row also bounds its derivative on either nonzero-height half of the open cell core. [`row_norm_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L562).

**Theorem · Row derivatives have an a.e. bound.** The compatible row-shape hypotheses give a nonnegative uniform bound on the row derivative almost everywhere in space. [`row_deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L574).

**Theorem · The gradient-row pairing is integrable.** The entry pairing of an admissible gradient with the derivative of a selected row is integrable. [`gradient_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L594).

**Theorem · The gradient pairing respects reflection.** The gradient-row derivative pairing is reflection invariant almost everywhere on the cell solid. [`gradient_pair_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L635).

**Theorem · Derivative of a radial coordinate path.** Differentiating a cylindrical point in radius gives the radial unit vector. [`path_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L663).

**Theorem · Derivative of a height coordinate path.** Differentiating a cylindrical point in height gives the axial unit vector. [`path_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L670).

**Theorem · Derivative of the radial unit vector.** The angular derivative of the radial unit vector is the angular unit vector. [`path_radialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L677).

**Theorem · Derivative of the angular unit vector.** The angular derivative of the angular unit vector is the negative radial unit vector. [`path_angularUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L690).

**Theorem · Derivative of a circular path.** The angular derivative of a cylindrical point is radius times the angular unit vector. [`path_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L703).

**Theorem · Derivative of each moving-frame vector.** The angular derivatives of the radial, angular and axial frame vectors are respectively the angular vector, negative radial vector and zero. [`path_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L709).

**Theorem · Radial derivative in frame coordinates.** The radial derivative of a differentiable field's frame component is the radial column of its moving-frame derivative matrix. [`frame_radial_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L716).

**Theorem · Height derivative in frame coordinates.** The height derivative of a differentiable field's frame component is the axial column of its moving-frame derivative matrix. [`frame_height_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L727).

**Theorem · Angular derivative in a moving frame.** The angular derivative of a frame component is radius times the angular derivative-matrix column plus the correction from rotation of the frame itself. [`frame_angle_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L738).

**Theorem · Bound frame entries by operator norm.** The absolute value of each moving-frame matrix entry is at most the operator norm. [`frameMat_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L758).

**Theorem · Differentiate a zero Fourier coefficient.** Under the stated uniform derivative and continuity bounds, a Fourier coefficient vanishing throughout a parameter neighbourhood also vanishes for the parameter derivative. [`param_mode_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L771).

**Theorem · Differentiate Fourier coefficients.** A continuously differentiable function with equal angular endpoint values has derivative coefficient equal to its coefficient multiplied by the imaginary angular frequency. [`mode_of_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L796).

**Theorem · Reconstruct finite Fourier support.** A continuous periodic function with vanishing Fourier coefficients outside a finite set equals its finite Fourier expansion when the symmetry order is positive. [`mode_trig_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L825).

**Theorem · Finite expansion of the row gradient.** At a positive-radius cell interior point, each moving-frame row derivative entry equals its finite angular mode expansion. [`row_grad_at`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L893).

**Theorem · The row gradient expansion holds a.e..** The moving-frame row derivative agrees with its retained finite Fourier expansion for almost every radius-height point in the cell. [`rowGrad_expansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1110).

**Theorem · Reduce a gradient pairing to its modes.** A supplied finite row-gradient expansion identifies the spatial gradient pairing with four pi times the real weighted sum of gradient-mode pairings. [`gradient_modes_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1128).

**Theorem · The gradient pairing mode identity.** The proved row-gradient expansion gives the spatial gradient pairing as four pi times its radial-weighted finite mode pairing integral. [`gradient_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1156).

**Theorem · Reconstruct a vector from its frame.** Every spatial vector is the sum of its three moving-frame components times their frame vectors. [`frame_expand_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1164).

**Theorem · Apply an operator in frame coordinates.** Each frame component of a linear map applied to a vector is the matrix-vector product of its frame matrix and the vector's frame coordinates. [`frameVec_apply_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1177).

**Theorem · Frame coordinates of a cylindrical point.** A cylindrical point has frame coordinates radius, zero and height. [`frameVec_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1185).

**Theorem · Frame coordinates of a rotated position.** The axial turn of a cylindrical point has frame coordinates zero, radius and zero. [`frameVec_turn_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1194).

**Theorem · Frame coordinates of the axial turn.** The axial turn sends a vector's frame coordinates to negative angular component, radial component and zero. [`frameVec_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1203).

**Theorem · The drift in frame coordinates.** The drift's frame formula combines the similarity-scaled velocity, derivative applied to position and the rotation-rate correction. [`frameVec_drift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1210).

**Theorem · Fourier formula for the drift.** Each drift mode splits into a scaled velocity mode, derivative modes contracted with position and the rotation-rate correction. [`modeVec_drift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1228).

**Theorem · Split drift and viscosity coefficients.** The drift-plus-gradient pairing reorganizes into gradient entries times strain weights and velocity entries times velocity weights. [`drift_pair_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1282).

**Theorem · Cross product in frame coordinates.** The cross product has the usual three-coordinate antisymmetric formula in the cylindrical orthonormal frame. [`frameVec_cross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1299).

**Theorem · The cylindrical frame is orthonormal.** The inner product of two cylindrical frame vectors is one when their indices agree and zero otherwise. [`frame_orthonormal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1314).

**Theorem · Recover a reconstructed frame matrix.** Taking frame entries of the Cartesian operator reconstructed from a matrix returns the original matrix entries. [`frameMat_cartOp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1324).

**Theorem · Recover reconstructed frame coordinates.** Taking frame components of a Cartesian vector reconstructed from frame coordinates returns the original coordinates. [`frameVec_cartOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1333).

**Theorem · The chosen angle differs by full turns.** At positive radius, the cylindrical angle of a cylindrical point differs from its supplied angle by an integer multiple of two pi. [`cylAngle_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1339).

**Theorem · Frame vectors ignore full angular turns.** Subtracting an integer multiple of two pi from the angle leaves every cylindrical frame vector unchanged. [`frameUnit_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1351).

**Theorem · Fourier phases ignore full turns.** Subtracting an integer multiple of two pi from the angle leaves each integer-frequency cylindrical Fourier phase unchanged. [`exp_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1354).

**Theorem · Upper-half reflection signs are one.** At a cylindrical point with nonnegative height, every coordinate reflection sign is one. [`mirrorSign_upper`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1362).

**Theorem · Frame expansion of the low gradient.** On the upper positive-radius region, the low-gradient frame entries equal the real finite Fourier expansion of their retained projected strain modes. [`lowGrad_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1367).

**Theorem · Frame expansion of the low velocity.** On the upper positive-radius region, the low-velocity frame coordinates equal the real finite Fourier expansion of their retained projected velocity modes. [`lowVel_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1380).

**Theorem · Curl from antisymmetric frame entries.** Each frame component of the extracted curl is the signed sum of the derivative matrix entries prescribed by the permutation signs. [`frameVec_curl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1393).

**Theorem · Modes of a real Fourier product.** Multiplying the real part of a finite Fourier sum by a real function gives the half-sum of difference-frequency terms and conjugate sum-frequency terms. [`mode_re_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1413).

**Theorem · Negative frequency is the conjugate.** For a real angular function, its negative-frequency Fourier integral is the conjugate of its positive-frequency integral. [`mode_integral_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1461).

**Theorem · Negative matrix modes are conjugates.** Each negative-frequency matrix mode equals the complex conjugate of its corresponding positive-frequency mode. [`modeMat_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1472).

**Theorem · Negative vector modes are conjugates.** Each negative-frequency vector mode equals the complex conjugate of its corresponding positive-frequency mode. [`modeVec_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1479).

**Theorem · Cell coefficients preserve conjugation.** Taking a cell coefficient after complex conjugation gives the conjugate of the original coefficient. [`coef_conj_fn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1486).

**Theorem · Cell projection preserves conjugation.** Projecting the conjugated function gives the complex conjugate of its projection. [`proj_conj_fn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1493).

**Theorem · Negative low-strain modes are conjugates.** The low-strain projection at negative frequency is the conjugate of the corresponding positive-frequency projection. [`lowStrain_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1507).

**Theorem · Conjugacy of low-velocity modes.** The low-velocity projection at negative frequency is the conjugate of the corresponding positive-frequency projection. [`lowVelocity_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1517).

**Theorem · Vector modes preserve addition.** The mode of a sum of angularly integrable fields equals the sum of their modes. [`modeVec_add_fn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1527).

**Theorem · Finite Fourier products are integrable.** A finite real Fourier expansion multiplied by an angularly integrable real function and a Fourier phase remains interval integrable. [`mode_re_mul_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1550).

**Theorem · Expand a real Fourier cross product.** The mode of a cross product with a real finite Fourier expansion splits into difference-frequency and conjugate sum-frequency cross products. [`mode_cross_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1562).

**Theorem · Convolve cross-product modes.** A sign-symmetric, conjugate-symmetric finite Fourier expansion turns the cross-product mode into a finite sum of shifted mode cross products. [`mode_cross_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1621).

**Theorem · Complex cross products are antisymmetric.** Swapping the two complex vectors in the cross product negates each component. [`crossC_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1652).

**Theorem · Frame cross products are antisymmetric.** Swapping the two spatial vectors negates every frame component of their cross product. [`frameVec_cross_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1655).

**Theorem · Convolve with the expansion on the right.** With the finite Fourier expansion in the second cross-product factor, the mode is the corresponding sum of shifted first-factor modes crossed with its coefficients. [`mode_cross_gen_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1660).

**Theorem · Curl of a frame Fourier expansion.** Taking curl components of a finite frame-matrix Fourier expansion gives the real Fourier expansion of the coefficient curls. [`curl_frame_re`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1674).

**Theorem · Coefficient curl preserves conjugation.** The complex curl component of a conjugated matrix is the conjugate of its original curl component. [`curlComp_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1693).

**Theorem · Frame coordinates preserve addition.** The frame coordinate of a sum of vectors equals the sum of their frame coordinates. [`frameVec_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1698).

**Theorem · Integrate cross-product components.** A bounded finite Fourier first factor crossed with an angularly integrable second factor has integrable frame components. [`cross_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1701).

**Theorem · Integrate a pairing with the right sum.** An angularly integrable first factor crossed with a bounded finite Fourier second factor has integrable frame components. [`cross_integrable_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1722).

**Theorem · Fourier convolution of low transport.** Each low-transport mode equals its drift mode plus the finite convolution of low strain and velocity modes with the model velocity and curl modes. [`lowTransport_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1731).

**Theorem · Separate strain and velocity cross terms.** The paired sum of curl-strain and velocity cross products expands linearly into individual matrix-entry and vector-coordinate coefficients. [`cross_pair_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1815).

**Theorem · Complex pairings preserve left addition.** The complex pairing of a sum in its first argument equals the sum of the pairings. [`pairC_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1823).

**Theorem · Complex pairings preserve finite sums.** Pairing a finite sum of complex vectors against a fixed vector gives the finite sum of their pairings. [`pairC_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1826).

**Theorem · Split the volume pairing pointwise.** At the mode level, low transport plus the viscous gradient pairing splits into direct strain and velocity terms and their finite model-mode convolutions. [`volume_pointwise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1831).

**Theorem · Conjugate symmetry of retained modes.** The retained low-strain and low-velocity mode families both satisfy negative-frequency conjugate symmetry. [`volume_mode_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1867).

**Theorem · Integrate bounded fields on the solid.** A measurable field bounded on the cell solid has integrable norm there because the solid has finite volume. [`bounded_solid_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1879).

**Theorem · All volume factors are circle integrable.** Under admissibility, the drift, model velocity, model curl, perturbation velocity and gradient frame entries are angularly integrable on almost every positive-radius cell circle. [`volume_circle_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1887).

**Theorem · Finite coefficients equal volume modes.** The weighted mode integrals of low transport and viscous gradient pairing equal the real sum of the finite strain and velocity coefficient contributions. [`volume_mode_algebra`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1934).

**Theorem · The physical volume row identity.** The transport pairing minus high coupling plus the viscous gradient pairing, divided by four pi, equals the real finite strain-plus-velocity sum. [`volume_identity_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1966).

**Theorem · Cancel a nonzero pairing normalization.** Scaling both pairings by a common nonzero factor and dividing it back out preserves the viscous identity. [`scale_alg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1981).

**Theorem · Viscous mode identity with side terms.** The negative viscous second-trace mode pairing equals the viscous gradient-mode pairing plus the real viscous side sum. [`viscous_mode_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L1989).

**Theorem · The physical viscous row identity.** The negative viscous second-trace pairing divided by four pi equals the similarly normalized gradient pairing plus the real viscous side sum. [`viscous_identity_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowValueVolume.lean#L2070).

### Breakdown.FracCell.LayoutRowViscousSides

The second-trace pairing is integrated by parts mode by mode; the angular terms cancel and the radial and height terms become viscous segment moments. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Subtract points at a common angle.** Subtracting two cylindrical points with the same angle subtracts their radial and height coordinates. [`lp_cyl_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L19).

**Theorem · Recover the cylindrical radius.** For nonnegative radial coordinate, the cylindrical radius of the constructed point equals that coordinate. [`lp_cyl_radius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L23).

**Theorem · Recover the cylindrical height.** The height of a point built in cylindrical coordinates equals its supplied height coordinate. [`lp_cyl_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L29).

**Theorem · A cell rectangle maps into its solid.** Every angle sends a point of a valid cell rectangle into the cell solid with nonnegative height. [`lp_cyl_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L32).

**Theorem · Bound distance along a fixed angle.** At a fixed angle, the spatial distance of cylindrical points is at most twice the distance of their radius-height coordinates. [`lp_cyl_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L45).

**Theorem · The angular circle is continuous.** At fixed radius and height, the cylindrical point varies continuously with angle. [`lp_cyl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L53).

**Theorem · The mode integrand is continuous.** A continuous field along the angular circle has a continuous phase-weighted frame-component integrand. [`lp_integrand_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L58).

**Theorem · Lipschitz bound for mode integrands.** For a Lipschitz field, the difference of phase-weighted frame integrands is bounded by twice its Lipschitz constant times radius-height distance. [`lp_integrand_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L68).

**Theorem · Modes inherit a Lipschitz bound.** If all relevant circles lie in a field's Lipschitz domain, each angular mode is Lipschitz in radius and height with twice the field constant. [`lp_mode_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L89).

**Theorem · Row modes are Lipschitz on a cell.** The valid cell and row-shape assumptions give a Lipschitz bound for each row-mode component on the rectangle. [`lp_row_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L112).

**Theorem · Lipschitz bound after radial weighting.** A bounded Lipschitz function multiplied by radius and conjugated is Lipschitz with the radius-bound times the old constant plus the value bound. [`lp_coord_slope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L119).

**Theorem · Segment test polynomials are continuous.** Every segment test polynomial is a continuous real function. [`lp_test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L139).

**Theorem · The edge sign squares to one.** For distinct face levels, multiplying the edge orientation sign by itself gives one. [`lp_edge_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L143).

**Theorem · Bound an interval symmetrically.** A closed interval lies inside the symmetric interval whose radius is the sum of the absolute values of its endpoints. [`lp_box_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L146).

**Theorem · Identify the side containing a segment.** In a valid layout, a segment whose radial flag and level match a face belongs to that face's segment set. [`seg_side_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L152).

**Theorem · Segments partition their assigned face.** The matching segments cover a selected face interval, stay inside it and have pairwise disjoint interiors. [`seg_cover_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L165).

**Theorem · Viscous segments cover a radial face.** Segments at a selected radial boundary cover the full height interval with disjoint interiors and no extension beyond that interval. [`seg_radial_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L198).

**Theorem · Viscous segments cover a height face.** Segments at a selected height boundary cover the full radial interval with disjoint interiors and no extension beyond that interval. [`seg_height_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L216).

**Theorem · Split radial viscous strip integrals.** A polynomial row trace and a compatible radial face cover turn the affine-strip integral into the oriented weighted sum of viscous segment moments. [`radial_side_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L234).

**Theorem · Split height viscous strip integrals.** A polynomial row trace and a compatible height face cover turn the radial-weighted affine-strip integral into the oriented viscous segment sum. [`height_side_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L313).

**Theorem · A Lipschitz derivative is integrable.** The derivative of a Lipschitz complex function is integrable on every finite interval. [`deriv_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L393).

**Theorem · Affine product rule under a real map.** Applying a real linear functional to the affine product-rule integral gives the corresponding weighted endpoint values of a Lipschitz function. [`part_ftc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L398).

**Theorem · Affine product rule on an interval.** The integral of a Lipschitz function times an affine derivative plus its derivative times the affine function equals the endpoint product difference. [`slice_ftc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L431).

**Theorem · Normalized affine product rule.** The normalized affine product-rule integral equals the difference of the normalized endpoint products for a Lipschitz complex function. [`slice_ftc'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L442).

**Theorem · Radial strip moment equals a trace.** For a Lipschitz rectangle function and distinct face levels, its radial strip moment equals the tested integral of its value on the selected face. [`radial_strip_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L449).

**Theorem · Height strip moment equals a trace.** For a Lipschitz rectangle function and distinct height levels, its unweighted height strip moment equals the tested integral on the selected face. [`height_strip_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L557).

**Theorem · Cylindrical cell points lie in the solid.** Every angle sends a point of the valid cell rectangle into its spatial solid. [`vi_mem_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L578).

**Theorem · Identify the cylindrical coordinate map.** The inverse cylindrical change of variables followed by the spatial identification gives the usual cylindrical point formula. [`vi_cyl_fun_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L587).

**Theorem · Measurability in cylindrical variables.** A spatially measurable field pulled back to positive-radius cylindrical coordinates is almost everywhere strongly measurable for the product measure. [`vi_joint_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L591).

**Theorem · Integrability with the radial Jacobian.** An integrable spatial scalar field pulled back to cylindrical coordinates remains integrable after multiplication by the radial Jacobian. [`vi_joint_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L603).

**Theorem · Mode kernels are jointly measurable.** The phase-weighted cylindrical mode kernel is almost everywhere strongly measurable on the positive-radius product domain. [`vi_kern_meas_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L618).

**Theorem · Angular modes are measurable.** The angular Fourier coefficient of a measurable spatial field is measurable as a function of positive radius and height. [`vi_mode_meas_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L644).

**Theorem · The mode kernel is bounded by the field.** The norm of the phase-weighted frame-component kernel is at most the norm of the underlying spatial field. [`vi_kern_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L655).

**Theorem · Integrability of radius-weighted modes.** A measurable field with integrable norm on the cell solid has radial-weighted integrable mode norm on the cell rectangle. [`vi_mode_r_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L662).

**Theorem · A uniform field bound also bounds modes.** A global bound on the field norm also bounds the norm of each angular mode component. [`vi_mode_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L722).

**Theorem · Integrability of weighted mode pairings.** The spatial integrability and bounded-row hypotheses make the radial-weighted pairing of the two vector modes integrable on the cell rectangle. [`vi_pair_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L742).

**Theorem · Reflection preserves the norm.** The spatial reflection leaves every vector norm unchanged. [`vi_mirror_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L777).

**Theorem · Selected rows have a uniform norm bound.** The valid cell and row hypotheses provide a global bound for the selected row norm. [`vi_row_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L780).

**Theorem · Integrability of gradient row pairings.** For compatible admissible cell data, the radial-weighted sum of gradient-mode entries paired with row-gradient modes is integrable. [`grad_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L820).

**Theorem · Both viscous volume terms are integrable.** The radial-weighted second-trace pairing and gradient-row derivative pairing are integrable on the cell rectangle. [`volume_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L873).

**Definition · The open reflected cell interior.** The open core consists of points satisfying strict radial bounds and strict bounds on absolute height. [`vd_openCore`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L909).

**Theorem · The reflected cell core is open.** The strict radial and absolute-height conditions define an open subset of space. [`vd_openCore_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L912).

**Theorem · The open core lies inside the cell.** Every point of the open cell core belongs to the cell solid. [`vd_openCore_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L918).

**Theorem · The upper solid contains a neighbourhood.** An interior point with positive height has a neighbourhood contained in the nonnegative-height part of the cell solid. [`vd_upper_nhds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L921).

**Theorem · Lipschitz bound for the upper derivative.** The derivative norm of the upper row at an interior point is at most its Lipschitz constant. [`vd_upper_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L927).

**Theorem · Derivative of a radial coordinate path.** Differentiating a cylindrical point in radius gives the radial unit vector. [`vd_path_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L932).

**Theorem · Derivative of a height coordinate path.** Differentiating a cylindrical point in height gives the axial unit vector. [`vd_path_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L939).

**Theorem · Derivative of the radial unit vector.** The angular derivative of the radial unit vector is the angular unit vector. [`vd_path_radialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L946).

**Theorem · Derivative of the angular unit vector.** The angular derivative of the angular unit vector is the negative radial unit vector. [`vd_path_angularUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L959).

**Theorem · Derivative of a circular path.** The angular derivative of a cylindrical point is radius times the angular unit vector. [`vd_path_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L972).

**Theorem · Derivative of each moving-frame vector.** The angular derivatives of the radial, angular and axial frame vectors are respectively the angular vector, negative radial vector and zero. [`vd_path_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L978).

**Theorem · Radial derivative in frame coordinates.** The radial derivative of a differentiable field's frame component is the radial column of its moving-frame derivative matrix. [`vd_frame_radial_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L985).

**Theorem · Height derivative in frame coordinates.** The height derivative of a differentiable field's frame component is the axial column of its moving-frame derivative matrix. [`vd_frame_height_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L996).

**Theorem · Angular derivative in a moving frame.** The angular derivative of a frame component is radius times the angular derivative-matrix column plus the correction from rotation of the frame itself. [`vd_frame_angle_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1007).

**Theorem · Bound frame entries by operator norm.** The absolute value of each moving-frame matrix entry is at most the operator norm. [`vd_frameMat_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1027).

**Theorem · Differentiate Fourier coefficients.** A continuously differentiable function with equal angular endpoint values has derivative coefficient equal to its coefficient multiplied by the imaginary angular frequency. [`vd_mode_of_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1040).

**Theorem · Expand a vector in the standard basis.** Every spatial vector is the sum of its coordinates times the three standard unit vectors. [`ts_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1076).

**Theorem · Expand a quadratic tensor evaluation.** Applying a bilinear second derivative twice to one vector equals the double sum of coordinate products times its coordinate tensor entries. [`ts_bilin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1080).

**Theorem · Second derivatives in frame coordinates.** A moving-frame second-derivative entry expands as the double sum of input-frame coordinate products times the corresponding Cartesian tensor outputs. [`ts_third`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1089).

**Theorem · The frame-coordinate identity matrix.** Summing products of the frame vectors' two Cartesian coordinates gives one for equal coordinates and zero otherwise. [`ts_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1098).

**Theorem · Contract the frame to the second trace.** Summing the diagonal moving-frame second-derivative entries gives the corresponding frame component of the Cartesian second trace. [`ts_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1104).

**Theorem · Split a trace mode into tensor modes.** For an admissible field, the mode of its second trace equals the sum of its diagonal second-derivative modes almost everywhere on the rectangle. [`trace_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1121).

**Theorem · Radial and height row-mode derivatives.** Almost everywhere in the cell, the derivative of radius times a row mode follows the product rule and its height derivative equals the height row-gradient mode. [`row_mode_derivs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1184).

**Theorem · Angular second derivatives from modes.** The angular second-derivative mode is the specified frequency-dependent linear combination of gradient-mode entries almost everywhere. [`second_angular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1313).

**Theorem · Angular row-gradient identities.** Radius times the angular row-gradient entries equals the imaginary-frequency row modes with the radial-angular frame-rotation corrections. [`row_angular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1382).

**Theorem · Cancel angular viscous contributions.** The sum of angular second-derivative and gradient pairings reduces to the remaining radial-gradient pairing almost everywhere on the cell. [`angular_cancel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1534).

**Theorem · Split viscosity into two product rules.** The trace-plus-gradient mode integrand equals the sum of radial and height product-rule integrands after the angular cancellation. [`pointwise_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1560).

**Theorem · Radial viscous integration by parts.** With compatible data and polynomial row traces, the radial viscous product-rule term is integrable and its integral equals the radial segment-moment sum. [`radial_side`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1579).

**Theorem · Height viscous integration by parts.** With compatible data and polynomial row traces, the weighted height viscous product-rule term is integrable and its integral equals the height segment-moment sum. [`height_side`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1667).

**Theorem · Viscous traces are boundary moments.** A represented row trace on a viscous segment has trace coefficient equal to its boundary integral against the segment test polynomial. [`trace_coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1733).

**Theorem · Segment test polynomials are continuous.** Every segment test polynomial is a continuous real function. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1789).

**Theorem · Recover a coefficient from its trace.** For an orthonormal segment test family, integrating a finite test expansion against one basis test recovers its coefficient. [`coef_of_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1793).

**Theorem · Viscous identity for one angular mode.** The negative viscous trace-mode integral equals the viscous gradient-mode integral plus the segment-moment contribution, with both volume terms integrable. [`mode_parts_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1821).

**Theorem · Zero fields have zero segment trace.** A function vanishing throughout a valid cell rectangle has zero trace coefficient on every layout segment. [`trace_of_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowViscousSides.lean#L1899).

### Breakdown.FracCell.LayoutRowVolumeSplit

Polynomial testing separates diagonal and convolution terms, then rearranges the finite mode sums into the stored strain and velocity row coefficients. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Two basis-value definitions agree.** The layout basis value equals the complex-valued cell basis function at the same radial and height indices. [`basisVal_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L16).

**Theorem · Convert radial weight to line weight.** An identity after multiplication by the modified radial factor becomes the corresponding identity between radius weighting and cell line weighting. [`weight_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L18).

**Theorem · Polynomial spaces preserve conjugation.** Complex conjugation preserves the radial and height degree bounds of the bivariate polynomial space. [`poly_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L34).

**Theorem · Polynomial testing recovers the pairing.** For valid cell bases and a test whose modified radial product is a bounded-degree polynomial, summing basis moments against field coefficients recovers the original weighted pairing. [`poly_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L42).

**Theorem · Identify projected coefficient pairings.** For valid cell bases and integrable inputs, the basis-moment sum equals the radial-weighted pairing with the finite cell projection. [`proj_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L81).

**Theorem · The rectangle boundary has zero area.** Removing the open rectangle interior from the closed cell rectangle leaves a set of zero planar measure. [`rim_null_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L110).

**Theorem · Interior polynomial testing suffices.** An almost everywhere polynomial test identity on the cell interior suffices to recover the weighted field pairing from its finite coefficients. [`poly_pairing_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L127).

**Definition · The open reflected cell interior.** The open core consists of points satisfying strict radial bounds and strict bounds on absolute height. [`openCore`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L177).

**Theorem · The reflected cell core is open.** The strict radial and absolute-height conditions define an open subset of space. [`openCore_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L180).

**Theorem · The open core lies inside the cell.** Every point of the open cell core belongs to the cell solid. [`openCore_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L186).

**Theorem · The upper solid contains a neighbourhood.** An interior point with positive height has a neighbourhood contained in the nonnegative-height part of the cell solid. [`upper_nhds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L189).

**Theorem · Reflect a row near a lower point.** Near a negative-height interior point, the row agrees with the reflection of its values at reflected points. [`lower_eq_near`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L195).

**Theorem · Derivative of the reflected lower row.** At a lower interior point, the row derivative is obtained by reflecting the input and output of the derivative at the reflected point. [`lower_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L203).

**Theorem · Lipschitz bound for the upper derivative.** The derivative norm of the upper row at an interior point is at most its Lipschitz constant. [`upper_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L216).

**Theorem · Derivative of a radial coordinate path.** Differentiating a cylindrical point in radius gives the radial unit vector. [`path_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L225).

**Theorem · Derivative of a height coordinate path.** Differentiating a cylindrical point in height gives the axial unit vector. [`path_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L232).

**Theorem · Derivative of the radial unit vector.** The angular derivative of the radial unit vector is the angular unit vector. [`path_radialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L239).

**Theorem · Derivative of the angular unit vector.** The angular derivative of the angular unit vector is the negative radial unit vector. [`path_angularUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L252).

**Theorem · Derivative of a circular path.** The angular derivative of a cylindrical point is radius times the angular unit vector. [`path_angle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L265).

**Theorem · Derivative of each moving-frame vector.** The angular derivatives of the radial, angular and axial frame vectors are respectively the angular vector, negative radial vector and zero. [`path_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L271).

**Theorem · Radial derivative in frame coordinates.** The radial derivative of a differentiable field's frame component is the radial column of its moving-frame derivative matrix. [`frame_radial_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L278).

**Theorem · Height derivative in frame coordinates.** The height derivative of a differentiable field's frame component is the axial column of its moving-frame derivative matrix. [`frame_height_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L289).

**Theorem · Angular derivative in a moving frame.** The angular derivative of a frame component is radius times the angular derivative-matrix column plus the correction from rotation of the frame itself. [`frame_angle_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L300).

**Theorem · Bound frame entries by operator norm.** The absolute value of each moving-frame matrix entry is at most the operator norm. [`frameMat_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L320).

**Theorem · Differentiate a zero Fourier coefficient.** Under the stated uniform derivative and continuity bounds, a Fourier coefficient vanishing throughout a parameter neighbourhood also vanishes for the parameter derivative. [`param_mode_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L333).

**Theorem · Differentiate Fourier coefficients.** A continuously differentiable function with equal angular endpoint values has derivative coefficient equal to its coefficient multiplied by the imaginary angular frequency. [`mode_of_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L358).

**Theorem · A vanishing row mode has zero gradient.** Under valid row-shape data, a mode vanishing throughout the rectangle has every row-gradient mode entry zero in its interior. [`grad_mode_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L391).

**Theorem · Continuity of cell projections.** Every finite-degree cell projection is a continuous function. [`proj_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L541).

**Theorem · The cell solid is measurable.** The spatial solid associated with a cell box is a measurable set. [`solid_meas'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L547).

**Theorem · Cylindrical cell points lie in the solid.** Every angle sends a point of the valid cell rectangle into its spatial solid. [`cyl_in_solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L557).

**Theorem · Integrability of line-weighted modes.** A measurable field with integrable norm on the cell solid has integrable line-weighted vector modes on the rectangle. [`modeVec_int_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L566).

**Theorem · Extend a weighted identity to the axis.** A modified radial identity valid off the axis gives the radius-versus-line-weight identity everywhere on a valid cell rectangle. [`weight_eq_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L585).

**Theorem · Almost every cell point is interior.** Almost every point with respect to cell rectangle area measure lies in its open radial-height interior. [`open_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L593).

**Theorem · Conjugate a real-weighted identity.** Complex conjugation preserves an equality between complex quantities multiplied by real weights. [`conj_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L601).

**Theorem · Real weighted integrals are integrable.** Integrability of the complex radial-weighted function implies integrability of radius times its real part. [`re_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L606).

**Theorem · Transport and gradient mode sums exist.** For compatible admissible cell data, both weighted real mode sums on the volume identity's left side are integrable. [`volume_lhs_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L612).

**Definition · Mode density for the volume row.** The density combines direct strain and velocity coefficients with the resolved-mode model-velocity and model-curl convolution terms. [`volumeDensity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L652).

**Theorem · Identify projected coefficient pairings.** For valid cell bases and integrable inputs, the basis-moment sum equals the radial-weighted pairing with the finite cell projection. [`proj_pairing'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L666).

**Theorem · Separate exact and projected pairings.** The finite coefficient sum splits into exact pairings for polynomial diagonal tests and projected pairings for the integrable convolution tests. [`gen_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L694).

**Definition · Direct strain weight for a row mode.** The direct strain weight combines similarity-position drift, rotation-position drift and the conjugated row-gradient viscosity term. [`strainDiag`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L747).

**Definition · Direct velocity weight for a row mode.** The direct velocity weight combines similarity scaling of the conjugated row mode with its axial rotation correction. [`velDiag`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L753).

**Definition · Strain weight from model velocity.** The strain convolution weight pairs a permutation-sign cross product with the model-velocity mode against the selected row mode. [`strainCross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L757).

**Definition · Velocity weight from model curl.** The velocity convolution weight pairs the model-curl mode crossed with a coordinate unit vector against the selected row mode. [`velCross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L761).

**Theorem · Position-frame coordinates are real.** Complex conjugation leaves each position-frame coordinate unchanged. [`frameY_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L764).

**Theorem · Turned-position coordinates are real.** Complex conjugation leaves each turned-position frame coordinate unchanged. [`frameTurnY_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L767).

**Theorem · Conjugate a modified radial identity.** An identity after multiplying by the real modified radial factor remains valid after complex conjugation. [`conj_rhat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L770).

**Theorem · Direct strain weights are polynomial.** After multiplication by the modified radial factor, the direct strain weights agree in the cell interior with polynomials of the retained strain degree. [`strainDiag_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L774).

**Theorem · Direct velocity weights are polynomial.** After multiplication by the modified radial factor, the direct velocity weights agree in the cell interior with polynomials of one lower retained degree. [`velDiag_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L794).

**Theorem · Integrability with polynomial tests.** A line-weighted integrable field paired with a test that becomes polynomial after modified radial weighting gives an integrable radius-weighted product. [`int_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L814).

**Theorem · Polynomial vector tests are integrable.** Line-weighted integrable vector components paired against modified-radial polynomial tests give an integrable radius-weighted complex pairing. [`int_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L826).

**Theorem · Integrate a constant left cross product.** Crossing a line-weighted integrable vector field with a constant vector on the left preserves componentwise integrability. [`cross_left_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L840).

**Theorem · Integrate a constant right cross product.** Crossing a line-weighted integrable vector field with a constant vector on the right preserves componentwise integrability. [`cross_right_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L852).

**Theorem · Reindex strain and velocity mode sums.** When direct terms outside the resolved set vanish, the combined row-mode sum can be regrouped by resolved strain and velocity indices with diagonal indicators. [`sum_algebra`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L864).

**Theorem · Integrate finite volume contributions.** For integrable summands, the integral of the four finite direct and convolution sums equals the sum of their individual integrals. [`int_sum4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L907).

**Theorem · Row coefficients from the volume density.** The real radial-weighted integral of the finite volume densities equals the real part of the strain and velocity coefficient sums. [`volume_sum_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LayoutRowVolumeSplit.lean#L935).

### Breakdown.FracCell.LocalFormBound

The energy, class, pair and cross estimates are combined into the local matrix-form lower bound used for cell data. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · Quadratic values split over matrix sums.** Evaluating a matrix difference plus another matrix as a quadratic form gives the corresponding difference and sum of the three quadratic values. [`quadFormValue_add_sub_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LocalFormBound.lean#L11).

**Theorem · Assemble the local form bound.** The energy, class, pair and cross-form propositions imply that the stored local matrix quadratic value is bounded above by the analytic local cell form. [`localFormBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LocalFormBound.lean#L16).

### Breakdown.FracCell.LowEntry

Tensor-product basis orthogonality and cylindrical integrability identify stored low layout entries with the corresponding physical mode coefficients. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The line weight is continuous.** The radial line weight attached to a cell box is continuous. [`lineWeight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L14).

**Theorem · The cell rectangle is compact.** The product of the closed bounded radial and height intervals is compact. [`rect_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L21).

**Theorem · The cell rectangle is measurable.** The radial-height cell rectangle is a measurable planar set. [`rect_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L23).

**Theorem · Radial basis polynomials are continuous.** Each radial basis polynomial defines a continuous real function. [`radialPoly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L25).

**Theorem · Height basis polynomials are continuous.** Each height basis polynomial defines a continuous real function. [`heightPoly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L29).

**Definition · The tensor-product cell basis.** The complex cell basis function is the real radial basis polynomial times the real height basis polynomial, embedded in the complex numbers. [`bas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L33).

**Theorem · Cell basis functions are continuous.** Each tensor-product cell basis function is continuous on the radius-height plane. [`bas_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L35).

**Theorem · Zero belongs to each polynomial space.** The zero function lies in every bivariate polynomial space with specified nonnegative degree bounds. [`poly_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L39).

**Theorem · Polynomial spaces preserve addition.** The sum of two bivariate polynomials with the same degree bounds remains in that polynomial space. [`poly_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L41).

**Theorem · Polynomial spaces preserve scaling.** Multiplying a bivariate polynomial by a complex constant preserves its degree bounds. [`poly_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L53).

**Theorem · A monomial fits its degree bounds.** A radial-height monomial belongs to the selected polynomial space when both exponents fit its degree bounds. [`poly_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L64).

**Theorem · Degree bounds for finite polynomial sums.** A finite sum of functions in the same bounded-degree polynomial space remains in that space. [`poly_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L79).

**Theorem · Continuity of finite polynomials.** Every function in a bivariate polynomial space is continuous. [`poly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L89).

**Theorem · Degree bounds for basis functions.** A tensor-product cell basis function lies in every bivariate polynomial space whose bounds contain its two indices. [`bas_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L96).

**Theorem · The tensor-product basis is orthonormal.** For valid cell bases, the line-weighted integral of two tensor-product basis functions is one for equal index pairs and zero otherwise. [`ortho`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L108).

**Theorem · Vanishing on a triangular basis suffices.** A linear functional vanishing on triangular polynomials with nonzero leading coefficients also vanishes on each monomial up to the same degree. [`span_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L119).

**Definition · Integral testing by a real function.** The functional integrates a complex field multiplied by a real test function over the cell rectangle. [`psi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L158).

**Theorem · Continuous tests preserve integrability.** Multiplying an integrable cell field by a continuous real test function gives an integrable product on the rectangle. [`psi_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L160).

**Theorem · Integral testing preserves addition.** The integral test functional is additive in its continuous real test argument. [`psi_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L164).

**Theorem · Integral testing preserves real scaling.** Scaling a continuous real test scales its complex integral against the cell field by the same real factor. [`psi_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L170).

**Theorem · The complex line weight is continuous.** Embedding the cell's line weight in the complex numbers gives a continuous function on the rectangle plane. [`weight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L176).

**Theorem · Coefficients of orthogonal residuals.** If a polynomial has residual orthogonal to the retained polynomial space, its cell coefficients equal those of the original field within the retained degree bounds. [`coef_eq_of_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L179).

**Theorem · Preserve coefficients under projection.** The finite cell projection has the same retained cell coefficients as the original integrable field. [`coef_proj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L198).

**Definition · Spatial point from product coordinates.** The coordinate map takes a radius-height pair and an angle to their cylindrical spatial point. [`cylArg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L327).

**Definition · Measure on positive-radius coordinates.** The measure is the product of plane volume restricted to positive radius and angular volume restricted between minus pi and pi. [`muU`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L329).

**Theorem · Expand the cylindrical product measure.** The cylindrical coordinate measure is explicitly the product of the positive-radius plane measure and the restricted angular measure. [`muU_def`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L332).

**Theorem · The product measure is restricted volume.** The cylindrical product measure equals ordinary product-space volume restricted to its positive-radius and angular domain. [`muU_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L334).

**Theorem · Measurability of the cylindrical map.** The map from radius-height-angle coordinates to space is measurable. [`cylArg_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L337).

**Theorem · Cylindrical change of variables.** For a nonnegative extended-real function, its cylindrical integral weighted by radius equals its spatial Lebesgue integral. [`key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L343).

**Theorem · Null sets in cylindrical coordinates.** The cylindrical coordinate map is quasi-measure-preserving from the positive-radius product domain to spatial volume. [`qmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L364).

**Theorem · A norm bound for cylindrical points.** The norm of a cylindrical point is at most twice the absolute radius plus the absolute height. [`cylPoint_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L385).

**Theorem · Line-weighted angular integrability.** A locally integrable spatial field passed through a continuous norm-bounded angular functional has an integrable line-weighted angular average on a valid cell. [`mode_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L395).

**Theorem · Scale a Cartesian unit vector.** The coordinate vector with value a at one index equals a times the corresponding unit coordinate vector. [`single_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L482).

**Theorem · The radial unit vector is continuous.** The radial unit vector varies continuously with angle. [`radialUnit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L486).

**Theorem · The angular unit vector is continuous.** The angular unit vector varies continuously with angle. [`angularUnit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L492).

**Theorem · Continuity of cylindrical frame vectors.** The radial, angular and axial frame vectors are continuous functions of angle. [`unit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L498).

**Theorem · Frame vectors have norm at most one.** Each vector in the cylindrical frame has norm at most one. [`unit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L504).

**Theorem · Bound frame pairings by vector norm.** The absolute inner product with any cylindrical frame vector is at most the norm of the original vector. [`inner_unit_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L507).

**Theorem · Frame matrix entries are norm bounded.** The absolute value of a moving-frame matrix entry is at most the linear map's operator norm. [`frameMat_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L512).

**Theorem · Frame components are inner products.** A vector's moving-frame component equals its inner product with the corresponding frame vector. [`frameVec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L518).

**Theorem · Continuity of frame matrix entries.** Each frame matrix entry depends continuously on the angle and the linear map jointly. [`frameMat_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L522).

**Theorem · Continuity of frame vector entries.** Each frame vector component depends continuously on the angle and the spatial vector jointly. [`frameVec_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L527).

**Theorem · Angular Fourier phases are continuous.** The cylindrical Fourier phase is a continuous function of angle and any unused auxiliary argument. [`phase_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L531).

**Theorem · Angular Fourier phases have unit norm.** Every cylindrical Fourier phase has complex norm one. [`phase_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L536).

**Theorem · Fourier phases have period two pi.** Adding a full angular turn leaves every integer-frequency cylindrical Fourier phase unchanged. [`phase_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L539).

**Theorem · Cylindrical points have period two pi.** Adding a full turn to the angle leaves the cylindrical spatial point unchanged. [`cylPoint_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L547).

**Theorem · Frame matrix entries have full period.** Adding two pi to the frame angle leaves each matrix entry unchanged. [`frameMat_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L550).

**Theorem · Frame vector entries have full period.** Adding two pi to the frame angle leaves each vector component unchanged. [`frameVec_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L554).

**Theorem · Shift an angular integration interval.** For a two-pi-periodic integrand, the integral from zero to two pi equals the integral over the open interval from minus pi to pi. [`per_interval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L557).

**Definition · Kernel for a gradient Fourier mode.** The gradient kernel multiplies a moving-frame matrix entry by the negative-frequency complex phase. [`gradKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L563).

**Definition · Kernel for a velocity Fourier mode.** The velocity kernel multiplies a moving-frame vector component by the negative-frequency complex phase. [`velKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L566).

**Theorem · Gradient mode kernels are continuous.** The gradient-mode kernel is jointly continuous in angle and linear-map input. [`gradKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L569).

**Theorem · Velocity mode kernels are continuous.** The velocity-mode kernel is jointly continuous in angle and vector input. [`velKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L573).

**Theorem · Bound gradient kernels by operator norm.** The complex norm of a gradient-mode kernel is at most the operator norm of its linear-map input. [`gradKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L577).

**Theorem · Velocity kernels are vector-norm bounded.** The complex norm of a velocity-mode kernel is at most the norm of its spatial vector input. [`velKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L582).

**Theorem · Center the gradient-mode integral.** The gradient mode equals the centred angular integral of its kernel divided by two pi. [`gradMode_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L587).

**Theorem · Center the velocity-mode integral.** The velocity mode equals the centred angular integral of its kernel divided by two pi. [`modeVec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L595).

**Theorem · Line-weighted gradient integrability.** A measurable gradient with integrable squared entry norm has integrable line-weighted mode entries on every valid cell. [`gradMode_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L603).

**Theorem · L6 velocity gives integrable cell modes.** A spatial L6 velocity field has integrable line-weighted mode components on every valid cell. [`modeVec_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L619).

**Theorem · Identify low layout coefficients.** The theorem proves that each successfully selected low layout entry in true data equals the corresponding physical low coefficient. [`lowEntry_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowEntry.lean#L638).

### Breakdown.FracCell.LowStrainExpansion

The retained strain projection is written explicitly in the radial-height cell basis under the energy-setting hypotheses. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · Integrate strain modes with polynomials.** The line-weighted gradient mode remains integrable after multiplication by the stated continuous radial and height test factors. [`weighted_mode_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowStrainExpansion.lean#L13).

**Theorem · Expand the retained strain field.** The theorem expresses each retained low-strain mode as the finite tensor-product basis expansion of its gradient-mode coefficients. [`lowStrainExpansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowStrainExpansion.lean#L26).

### Breakdown.FracCell.LowVelocityExpansion

Orthonormal cell bases reconstruct polynomials and their projections, giving the finite retained-velocity expansion. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Exchange two pairs of finite sums.** The order of four finite sums can be rearranged by exchanging the first index pair with the second. [`swap4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowVelocityExpansion.lean#L17).

**Theorem · Recover a cell expansion coefficient.** Pairing a finite cell-basis expansion with one retained basis function recovers the corresponding coefficient by orthonormality. [`pair_expansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowVelocityExpansion.lean#L27).

**Theorem · Recover cell polynomials from moments.** A bounded-degree cell polynomial equals its finite basis expansion with coefficients given by its weighted basis pairings. [`poly_recon`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowVelocityExpansion.lean#L45).

**Theorem · Expand the cell projection in its basis.** The finite cell projection equals the tensor-product basis sum of the original field's cell coefficients. [`proj_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowVelocityExpansion.lean#L78).

**Theorem · Expand the retained velocity field.** The theorem expresses each retained low-velocity mode as the finite cell-basis expansion of its velocity-mode coefficients. [`lowVelocityExpansion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/LowVelocityExpansion.lean#L126).

### Breakdown.FracCell.MeshAssembly

The individual trace, root, jump, gauge and moment propositions are assembled into mesh compatibility and flux-stream interfaces. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Assemble mesh compatibility.** The skeleton-slot, root-zero, edge-jump, gauge-linearity and moment-linearity propositions together imply the mesh compatibility proposition. [`meshCompatibility_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L11).

**Theorem · Assemble the flux-stream relation.** The radial-flux, height-flux and stream-plane propositions together supply the flux-stream proposition. [`fluxStream_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L18).

### Breakdown.FracCell.MeshDataAffine

True cell data are affine in admissible fields, with the sole extra term represented by constant-pressure data and a gauge-dependent scalar. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Integrate an affine combination.** An almost everywhere affine combination of integrable functions has integral equal to the corresponding affine combination of their integrals. [`setInt_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L18).

**Theorem · Closed rectangles are compact.** A product of two closed bounded real intervals is compact. [`rect_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L27).

**Theorem · Affine combinations of radial moments.** Under the weak-pair and integrability hypotheses, a radial strip moment respects a real linear combination plus the specified constant-potential contribution. [`radial_aff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L30).

**Theorem · Affine combinations of height moments.** Under the weak-pair and integrability hypotheses, a weighted height strip moment respects a real linear combination plus the specified constant-potential contribution. [`height_aff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L70).

**Theorem · Linear combinations of corner moments.** Compatible linear combinations of the field and its derivative data give the same linear combination of corner moments. [`corner_aff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L116).

**Theorem · The cell line weight is continuous.** The radial line weight of a cell box is continuous. [`lw_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L175).

**Theorem · Linear combinations of cell coefficients.** An almost everywhere linear combination of integrable cell fields has coefficients equal to the same combination of their coefficients. [`coef_aff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L181).

**Theorem · Integrate the radial affine derivative.** The weak radial integrability hypotheses make the affine-ramp multiple of the derivative integrable on the strip rectangle. [`wcase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L202).

**Theorem · Remove a radial weight away from zero.** If the lower radius is strictly positive, radial-weighted integrability of a complex rectangular field implies its unweighted integrability. [`unweight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L224).

**Theorem · Face test polynomials are continuous.** Every polynomial test attached to a face segment is continuous. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L236).

**Theorem · Fourier modes of constant pressure.** For positive symmetry order, the constant-one pressure field has mode one at zero frequency and zero at every other frequency. [`presMode_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L240).

**Theorem · Orientation cancels the strip length.** For distinct levels, the edge sign times the absolute strip width divided by the oriented width is one. [`edge_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L269).

**Theorem · Radial moment of a constant potential.** On a valid radial segment, the strip moment of a constant potential equals that constant times the integral of the segment test. [`radial_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L283).

**Theorem · Height moment of a constant potential.** On a valid height segment, the weighted strip moment of a constant potential equals that constant times the radial-weighted test integral. [`height_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L304).

**Theorem · Linearity of unshifted radial moments.** With no constant-potential term, radial strip moments preserve the given real linear combination exactly. [`radial_aff0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L326).

**Theorem · Linearity of unshifted height moments.** With no constant-potential term, weighted height strip moments preserve the given real linear combination exactly. [`height_aff0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L343).

**Theorem · Integrate with continuous real weights.** A continuous real weight on the compact integration region preserves integrability of the complex field it multiplies. [`cw_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L358).

**Theorem · Side test functions are continuous.** Each side test polynomial in a cell layout is continuous. [`sideTest_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L362).

**Theorem · Radial pressure-shift weights.** The left and right shift coefficients on a radial pressure segment sum to the unweighted integral of its test function. [`shiftSum_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L369).

**Theorem · Height pressure-shift weights.** The left and right shift coefficients on a height pressure segment sum to the radial-weighted integral of its test function. [`shiftSum_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L377).

**Definition · The scalar pressure gauge level.** The gauge level is the real part of the zero-mode potential gauge moment divided by the same moment of the constant-one potential. [`gaugeLevel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L393).

**Theorem · The layout gauge equals the gauge level.** For a layout with the specified order and gauge segment, its normalized gauge value agrees with the scalar gauge level. [`gaugeLevel_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L398).

**Theorem · True data are affine up to pressure.** The theorem supplies one scalar constant-pressure correction, shared by layouts with the same gauge, for true data of any real linear combination of admissible fields. [`dataAffine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L403).

**Reader note.** The extra scalar multiplies constant-pressure data; treating this theorem as strict linearity would erase the gauge shift that later mesh arguments remove.

### Breakdown.FracCell.MeshDataAffineModes

Half-turn symmetry, cylindrical integrability and potential uniqueness establish affine formulas for all modes, including the constant offset in pressure potentials. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Negative radius is a half angular turn.** Changing the sign of the radius gives the same spatial point as adding pi to the angle. [`cyl_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L21).

**Definition · Frame signs under a half turn.** The axial component receives sign one and the two transverse components receive sign minus one. [`unitSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L24).

**Theorem · Half-turn signs square to one.** Each coordinate half-turn sign multiplied by itself is one. [`unitSign_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L26).

**Theorem · Frame vectors under a half turn.** Adding pi to the angle multiplies each cylindrical frame vector by its half-turn sign. [`frameUnit_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L29).

**Theorem · Shift the Fourier phase by a half turn.** The Fourier phase at one angle equals its phase at angle plus pi multiplied by the corresponding constant half-turn factor. [`phase_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L34).

**Theorem · Reflect the radial argument of a mode.** A kernel with the stated half-turn transformation converts a negative-radius angular integral into a fixed constant times its positive-radius integral. [`mode_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L43).

**Theorem · Centre the mode integration interval.** For the stated periodic kernel, its angular integral from zero to two pi equals the integral between minus pi and pi. [`mode_ioo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L61).

**Definition · Kernel for a second-derivative mode.** The kernel multiplies a moving-frame second-derivative entry by its negative-frequency angular phase. [`thirdKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L67).

**Definition · Kernel for a pressure Fourier mode.** The pressure kernel is a real scalar multiplied by its negative-frequency complex phase. [`presKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L70).

**Theorem · Frame coordinates under a half turn.** Adding pi to the angle multiplies a vector frame component by its coordinate half-turn sign. [`frameVec_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L73).

**Theorem · Matrix frame entries under a half turn.** Adding pi to the angle multiplies a matrix frame entry by the signs of both its output and input components. [`frameMat_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L80).

**Theorem · Tensor frame entries under a half turn.** Adding pi to the angle multiplies a second-derivative frame entry by the signs of its output and two input components. [`frameThird_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L88).

**Theorem · Half-turn factor for velocity kernels.** There is a complex constant relating the velocity-mode kernel at an angle to the same kernel at angle plus pi. [`velKernel_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L94).

**Theorem · Half-turn factor for gradient kernels.** There is a complex constant relating the gradient-mode kernel at an angle to the same kernel at angle plus pi. [`gradKernel_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L102).

**Theorem · Half-turn factor for tensor kernels.** There is a complex constant relating the second-derivative mode kernel at an angle to the same kernel at angle plus pi. [`thirdKernel_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L117).

**Theorem · Half-turn factor for pressure kernels.** There is a complex constant relating the pressure-mode kernel at an angle to the same kernel at angle plus pi. [`presKernel_pi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L135).

**Theorem · Tensor kernels have full angular period.** Adding two pi to the angle leaves the second-derivative mode kernel unchanged. [`thirdKernel_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L142).

**Theorem · Full angular period of pressure kernels.** Adding two pi to the angle leaves the pressure-mode kernel unchanged. [`presKernel_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L147).

**Theorem · Full angular period of velocity kernels.** Adding two pi to the angle leaves the velocity-mode kernel unchanged. [`velKernel_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L150).

**Theorem · Full angular period of gradient kernels.** Adding two pi to the angle leaves the gradient-mode kernel unchanged. [`gradKernel_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L154).

**Theorem · Velocity modes as kernel averages.** Each velocity-mode component is the angular average of its velocity kernel over one full turn. [`modeVec_k`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L158).

**Theorem · Gradient modes as kernel averages.** Each gradient-mode entry is the angular average of its gradient kernel over one full turn. [`gradMode_k`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L162).

**Theorem · Second-derivative modes as averages.** Each second-derivative mode entry is the angular average of its tensor kernel over one full turn. [`modeThird_k`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L167).

**Theorem · Pressure modes as kernel averages.** Each pressure mode is the angular average of its scalar pressure kernel over one full turn. [`presMode_k`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L173).

**Theorem · Integrable circles from local control.** A locally integrable spatial field is angularly integrable on almost every positive-radius circle. [`ae_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L178).

**Definition · Reflection of the radial coordinate.** The measurable equivalence negates the first plane coordinate and leaves the second coordinate fixed. [`negFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L223).

**Theorem · Evaluate radial-coordinate reflection.** Applying the radial reflection to a radius-height pair gives negative radius and unchanged height. [`negFirst_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L225).

**Theorem · Plane measure under radial reflection.** Negating the radial coordinate preserves planar Lebesgue measure. [`negFirst_mp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L227).

**Theorem · Transport a.e. facts through reflection.** An almost everywhere planar property remains almost everywhere true after negating the radial coordinate. [`ae_negFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L231).

**Theorem · The radial axis is negligible.** Almost every planar point has nonzero radial coordinate. [`ae_off_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L234).

**Theorem · Extend an a.e. fact to both radial signs.** An almost everywhere property on positive radius extends almost everywhere to the plane when it is preserved by radial reflection. [`ae_transfer`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L242).

**Theorem · Integrability extends to negative radius.** A fixed scalar reflection law transfers integrability from a positive radial strip to the reflected negative strip. [`int_negSide`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L249).

**Theorem · Reflection gives all rectangle integrals.** A fixed scalar reflection law and integrability on positive-radius centred strips imply integrability on every finite rectangle. [`int_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L262).

**Theorem · Tensor frame entries are norm bounded.** The absolute value of a moving-frame second-derivative entry is at most the tensor's operator norm. [`frameThird_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L279).

**Theorem · Tensor mode kernels are continuous.** The second-derivative mode kernel is jointly continuous in angle and tensor input. [`thirdKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L289).

**Theorem · Tensor kernels are operator-norm bounded.** The norm of a second-derivative mode kernel is at most the norm of the input tensor. [`thirdKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L296).

**Theorem · Pressure mode kernels are continuous.** The pressure-mode kernel is jointly continuous in angle and real scalar input. [`presKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L301).

**Theorem · Pressure kernels obey the scalar bound.** The norm of the pressure-mode kernel is at most the norm of its real scalar input. [`presKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L304).

**Theorem · Velocity kernels are real linear.** The velocity kernel maps a real linear combination of vectors to the same complex-valued linear combination of kernel values. [`velKernel_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L307).

**Theorem · Gradient kernels are real linear.** The gradient kernel maps a real linear combination of linear maps to the same combination of kernel values. [`gradKernel_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L313).

**Theorem · Tensor kernels are real linear.** The second-derivative kernel maps a real linear combination of tensors to the same combination of kernel values. [`thirdKernel_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L321).

**Theorem · Pressure kernels are real linear.** The pressure kernel maps a real linear combination of scalar inputs to the same combination of kernel values. [`presKernel_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L329).

**Theorem · Integrability of norm-bounded kernels.** A continuous angular kernel bounded by its input norm sends an integrable input to an integrable complex integrand. [`kint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L335).

**Theorem · Integrate a real-linear angular kernel.** Integrating a real-linear angular kernel over a set preserves real linear combinations of its integrable inputs. [`lin_set`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L340).

**Theorem · Local integrability from L2 control.** A measurable function with locally integrable squared norm is locally integrable. [`locInt_of_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L351).

**Theorem · Operator norm is bounded by its columns.** The operator norm of a map from space is at most the sum of the norms of its three coordinate columns. [`op_le_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L361).

**Theorem · Locally integrable second derivatives.** The second-order field hypotheses imply local integrability of the second-derivative tensor field. [`second_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L377).

**Theorem · Cut off a potential into L6.** A valid potential of a locally square-integrable gradient, multiplied by a bounded smooth compactly supported test, belongs to L6. [`pot_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L387).

**Theorem · Gradients are locally integrable.** The gradient-field measurability and squared-entry hypotheses imply local integrability of the gradient as an operator-valued function. [`grad_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L523).

**Theorem · Local integrability of potentials.** The selected potential of a gradient field is locally integrable under the stated gradient hypotheses. [`pot_locInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L531).

**Theorem · Normalized modes obey radial reflection.** The normalized angular average satisfies the same constant-factor radial reflection law as its kernel. [`mode_refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L535).

**Theorem · Integrate constants over an angular turn.** A constant complex function is integrable between minus pi and pi. [`const_ioo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L542).

**Theorem · Integrability of shifted potential modes.** The pressure modes of a selected potential minus a constant are integrable on every positive-radius bounded strip. [`pres_strip`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L544).

**Theorem · Integrability of weighted mode averages.** A locally integrable field passed through a continuous norm-bounded angular kernel has integrable radial-weighted averages on positive-radius bounded strips. [`weighted_strip`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L608).

**Theorem · Tensor modes on the centred interval.** The second-derivative mode equals its kernel average over the centred angular interval. [`third_ioo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L619).

**Theorem · Pressure modes on the centred interval.** The pressure mode equals its scalar-kernel average over the centred angular interval. [`pres_ioo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L624).

**Theorem · Velocity modes at opposite radial signs.** For each mode and component, a fixed complex scalar relates every velocity mode at a radius to that at the opposite radius. [`vec_refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L629).

**Theorem · Gradient modes at opposite radial signs.** For each mode and matrix entry, a fixed complex scalar relates gradient modes at opposite radial signs. [`grad_refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L637).

**Theorem · Tensor modes at opposite radial signs.** For each mode and tensor entry, a fixed complex scalar relates second-derivative modes at opposite radial signs. [`third_refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L645).

**Theorem · Pressure modes at opposite radial signs.** For each frequency, a fixed complex scalar relates pressure modes at opposite radial signs for every real pressure field. [`pres_refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L654).

**Theorem · Almost everywhere equality on circles.** Spatially almost everywhere equal scalar fields agree at almost every angle on almost every positive-radius circle. [`ae_circle_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L662).

**Theorem · Rectangle integrability of mode fields.** A second-order field has integrable velocity and gradient modes and radial-weighted integrable second-derivative modes on every finite rectangle. [`secondOrder_modes_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L687).

**Theorem · Integrate potential and gradient modes.** A gradient field has integrable shifted-potential modes and radial-weighted integrable gradient-vector modes on every finite rectangle. [`gradient_modes_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L715).

**Theorem · Real combinations of second-order modes.** Velocity, gradient and second-derivative modes of a real linear combination agree almost everywhere with the same combination of their respective modes. [`secondOrder_modes_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L738).

**Theorem · Constant correction to pressure modes.** Combining gradient fields gives the corresponding combination of vector modes, while their selected potential modes include the constant-potential correction determined by the chosen gauges. [`gradient_modes_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffineModes.lean#L798).

### Breakdown.FracCell.MeshDefs

The tail, far-field and mesh propositions specify the finite bounds and coordinate compatibility that the later analytic proofs must supply. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Reconstruct a tail-family input.** The tail-family input is the finite sum of its coefficient array against radial-height basis polynomials and input Fourier modes. [`inputFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L27).

**Definition · Fourier output of a tail family.** The output mode is the normalized Fourier coefficient of the multiplier-weighted sum of the reconstructed input fields. [`outputMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L33).

**Definition · Quadratic coefficient tail majorant.** The majorant sums input coefficient squared norms against the specified radial-total and height-total bound weights. [`majorant`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L39).

**Predicate · Regularity required of tail multipliers.** The structure requires joint measurability of each multiplier and a uniform bound on it over the cell and all angles. [`IsTailRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L45).

**Predicate · Radial and height tail inequalities.** The structure requires nonnegative weights and radial and height tail bounds for every retained input degree and coefficient vector. [`IsTailBounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L50).

**Definition · Squared coefficients beyond the cutoff.** The far coefficient sum is the infinite sum of coefficient squared norms whose radial or height index exceeds the selected cutoff. [`farCoefSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L64).

**Interface · Tail-family majorant condition.** The proposition bounds the weighted output-mode far coefficient sums by the input coefficient majorant for regular families satisfying the tail inequalities. [`TailMajorantStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L67).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.tailMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L52) ([lean/Breakdown/FracCell/MeshTail.lean:52](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L52); named premises: `TailFiniteStatement`); [`Breakdown.CellCert.CellAnalysis.tailMajorant_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L60) ([lean/Breakdown/FracCell/MeshTail.lean:60](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L60); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`_private.Breakdown.FracCell.MeshFar.0.Breakdown.CellCert.CellAnalysis.farMajorant_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180) ([lean/Breakdown/FracCell/MeshFar.lean:180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351) ([lean/Breakdown/FracCell/MeshFar.lean:351](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374) ([lean/Breakdown/FracCell/MeshFar.lean:374](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374); named reference in type).

**Predicate · Conditions for the far-field majorant.** The structure bundles the tail bounds, positive floors and share, rotation bound, polynomial auxiliary fields, support coverage and matrix domination needed for the far estimate. [`IsFarMajorant`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L79).

**Interface · Far-field energy bounded by its form.** The proposition bounds the analytic far weighted quantity by the finite far quadratic form under the complete admissible cell and far-majorant hypotheses. [`FarMajorantStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L106).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.farMajorant_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365); named premises: `CylinderCompStatement`, `FarCoefStatement`); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L538) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:538](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L538); named premises: `FarCoefStatement`); [`Breakdown.CellCert.CellAnalysis.farMajorant_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L596) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:596](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L596); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351) ([lean/Breakdown/FracCell/MeshFar.lean:351](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351); named premises: `FarCoefStatement`, `FarRegularStatement`, `FarSummableStatement`, `TailMajorantStatement`); [`Breakdown.CellCert.CellAnalysis.farMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374) ([lean/Breakdown/FracCell/MeshFar.lean:374](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374); named premises: `CylinderCompStatement`, `FarCoefStatement`, `TailMajorantStatement`).

**Theorems using this interface name.** None found in the library.

**Predicate · Polynomial row-coupling condition.** The structure requires the folded strain coupling and velocity coupling of each selected row to agree with bounded-degree polynomials in the cell interior. [`IsRowPolynomial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L120).

**Interface · Far row sum reduces to a finite sum.** The proposition requires the infinite row far-square sum to equal the sum truncated at the polynomial degree bound. [`RowFarFiniteStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L127).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.rowFarFinite_closed`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L368) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:368](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L368); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.CellAnalysis.rowFarFinite_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L201) ([lean/Breakdown/FracCell/MeshRowFar.lean:201](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L201); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Interface · Independence of auxiliary stream levels.** The proposition states that the zero-mode height-strip stream value is independent of the distinct auxiliary height level for positive radius. [`StreamIndependenceStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L145).

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.streamIndependence_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L100) ([lean/Breakdown/FracCell/MeshStreamInd.lean:100](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L100); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellCoordinates.fluxStream_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:376](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxStream_of_stream`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L565) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:565](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L565); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxStream_of_segment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L621) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:621](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L621); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshFluxHeight.fluxHeight_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L72) ([lean/Breakdown/FracCell/MeshFluxHeight.lean:72](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L72); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxRadial_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L23) ([lean/Breakdown/FracCell/MeshFluxRadial.lean:23](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L23); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.segSplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L15) ([lean/Breakdown/FracCell/MeshSkeleton.lean:15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L15); named reference in type); [`Breakdown.CellCert.CellCoordinates.meshSkeletonSlot_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L117) ([lean/Breakdown/FracCell/MeshSkeleton.lean:117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L117); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.stream_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L113) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L113); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.shifted_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L186) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:186](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L186); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.stream_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L315) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:315](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L315); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.shifted_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L326) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:326](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L326); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.value_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L427) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:427](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L427); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.localValue_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L444) ([lean/Breakdown/FracCell/MeshSkeletonPair.lean:444](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L444); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxSplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L825) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:825](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L825); named reference in type); [`Breakdown.CellCert.CellCoordinates.streamPlane_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamPlane.lean#L23) ([lean/Breakdown/FracCell/MeshStreamPlane.lean:23](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamPlane.lean#L23); named reference in type).

**Definition · A stream value from a height moment.** The stream value is the radius-weighted zero-mode vertical-velocity strip moment from the axis to the selected radius. [`streamValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L151).

**Interface · Flux moments are stream differences.** The proposition identifies radial and height flux moments with differences of stream values and requires the stream value to vanish on the symmetry plane. [`FluxStreamStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L154).

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.fluxStream_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:376](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376); named premises: `CylinderFluxStatement`, `FluxHeightStatement`, `RadialAxisCrossStatement`, `StreamIndependenceStatement`); [`Breakdown.CellCert.CellCoordinates.fluxStream_of_stream`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L565) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:565](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L565); named premises: `FluxHeightStatement`, `StreamIndependenceStatement`, `StripTraceStatement`); [`Breakdown.CellCert.CellCoordinates.fluxStream_of_segment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L621) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:621](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L621); named premises: `FluxHeightStatement`, `StreamIndependenceStatement`); [`Breakdown.CellCert.CellCoordinates.fluxStream_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L809) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:809](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L809); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.CellCoordinates.fluxStream_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L18) ([lean/Breakdown/FracCell/MeshAssembly.lean:18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L18); named premises: `FluxHeightStatement`, `FluxRadialStatement`, `StreamPlaneStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellCoordinates.meshSkeletonSlot_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L117) ([lean/Breakdown/FracCell/MeshSkeleton.lean:117](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L117); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonSplitInternal.streamC_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L583) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:583](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L583); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonSplitInternal.flux_rad_rel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L644) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:644](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L644); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonSplitInternal.flux_hgt_rel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L671) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:671](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L671); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshSkeletonSplitInternal.flux_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L763) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:763](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L763); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxSplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L825) ([lean/Breakdown/FracCell/MeshSkeletonSplit.lean:825](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L825); named reference in type).

**Interface · Canonical moments fit the mesh.** The proposition requires local-coordinate reconstruction, root normalization, edge gauge jumps, linear canonical gauges and moments, and recovery of the actuator coordinates. [`MeshCompatibilityStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDefs.lean#L168).

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.meshCompatibility_of_slot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L380) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:380](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L380); named premises: `DataAffineStatement`, `MeshGaugeLinearStatement`, `MeshSkeletonSlotStatement`); [`Breakdown.CellCert.CellCoordinates.meshCompatibility_of_rest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L716) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:716](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L716); named premises: `MeshSkeletonSlotStatement`); [`Breakdown.CellCert.CellCoordinates.meshCompatibility_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L812) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:812](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L812); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.CellCoordinates.meshCompatibility_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L11) ([lean/Breakdown/FracCell/MeshAssembly.lean:11](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshAssembly.lean#L11); named premises: `MeshEdgeJumpStatement`, `MeshGaugeLinearStatement`, `MeshMomentLinearStatement`, `MeshRootZeroStatement`, `MeshSkeletonSlotStatement`).

**Theorems using this interface name.** None found in the library.

### Breakdown.FracCell.MeshDelayVanish

The sparse delay rows are evaluated on the mesh state and shown to contribute zero quadratic value for admissible fields. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Evaluate a sparse row list.** Summing the accumulated row entries times a function equals the list sum of each stored coefficient times the function at its index. [`sum_rowEntries_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDelayVanish.lean#L13).

**Theorem · Delay forms vanish on admissible states.** The supplied mesh compatibility hypotheses imply that every delay form has zero quadratic value on the state represented by an admissible field. [`delayVanish_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDelayVanish.lean#L28).

### Breakdown.FracCell.MeshEdgeJump

Equivalent dependent root coordinates give the same root value, allowing the canonical right gauge to be expressed by the left gauge and edge jump. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Transport a dependent coordinate value.** Equal dependent indices and their matching coordinate elements give equal values of the indexed function. [`dep_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshEdgeJump.lean#L15).

**Theorem · Equivalent roots have equal values.** The mesh root value is unchanged when the root descriptions identify the same dependent coordinate. [`rootValue_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshEdgeJump.lean#L20).

**Theorem · The canonical gauges obey the edge jump.** For valid mesh and form data with $1<α<5/4$, a cell whose gauge specification names an edge has canonical right gauge equal to its canonical left gauge plus the layout gauge jump for every admissible field. [`meshEdgeJump`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshEdgeJump.lean#L34).

### Breakdown.FracCell.MeshFar

The tail-family bounds are combined with positive spectral floors and the stored kernel domination to prove the far-field quadratic bound. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Symmetric and antisymmetric energies add.** The squared norms of the symmetric and antisymmetric matrix parts sum to the full entrywise squared norm. [`symSq_add_antiSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L18).

**Theorem · Split a squared norm by a positive share.** For any positive share parameter, the squared norm of a sum is bounded by the two squared norms weighted by one plus the share and its reciprocal. [`sq_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L29).

**Theorem · Bound a matrix with one added column.** Adding a vector in the angular matrix column is controlled by the full matrix and vector squared norms with the positive-share weights. [`sumSq_fold`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L41).

**Theorem · Apply the common positive strain floor.** Positive lower bounds for both strain weights control the symmetric and antisymmetric folded energies by the common-floor matrix and optional band-vector estimate. [`strain_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L51).

**Theorem · Compare total sums with a majorant.** The total infinite sum of a pointwise smaller real family is at most the sum of a nonnegative summable majorant. [`tsum_le_of_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L78).

**Reader note.** The result compares the total infinite-sum operation and does not assert that the smaller family is summable; a separate summability statement is available in this route.

**Theorem · Exchange finite sums and infinite tails.** Summable coefficient tails remain summable after the finite output and mode sums, and their total sum can be taken in either order. [`family_tsum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L85).

**Theorem · Trim group weights to input degree.** Once the external degree bound includes the family's input degree, the weighted sum reduces to exactly that input-degree range. [`sum_groupWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L96).

**Theorem · Flatten the nine matrix entries.** A finite sum over nine flattened indices equals the double sum over the three-by-three matrix coordinates. [`sum_nine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L120).

**Theorem · Flatten the matrix squared norm.** The squared norms of all nine flattened matrix entries sum to the full entrywise matrix energy. [`sum_nine_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L130).

**Theorem · Regroup four equal contributions.** Replacing the four summands by equal counterparts and regrouping them preserves their total sum. [`add4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L134).

**Theorem · Combine the three family majorants.** The strain, velocity and band-family coefficient majorants sum to the stored far-majorant quadratic form. [`majorant_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L140).

**Definition · Zero the unused band contribution.** The record update replaces the band multiplier bounds and band velocity weight by zero while retaining the other far-majorant data. [`bandless`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L174).

**Reader note.** This is a data-record update used for an empty band, so the zeroed fields should be read together with the empty-band case in the enclosing proof.

**Theorem · The far bound from analytic inputs.** Tail majorization, coefficient representation, regularity and summability imply the far weighted estimate under the specified band and kernel conditions. [`farMajorant_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180).

**Theorem · Assemble the far-majorant proposition.** The tail majorant, far coefficient, regularity and summability propositions together supply the far-majorant bound. [`farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351).

**Theorem · Far bound from cylindrical measurability.** The tail majorant, far coefficient and cylindrical composition propositions suffice to supply the full far-majorant proposition. [`farMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374).

### Breakdown.FracCell.MeshFarCoef

Fourier convolution and basis reconstruction identify the high-degree coefficients with the output modes of the three tail families. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Phase products subtract frequencies.** Multiplying a negative Fourier phase by a positive Fourier phase gives the negative phase at the difference frequency. [`exp_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L21).

**Theorem · Finite angular sums are integrable.** A finite sum of angularly interval-integrable functions is interval integrable over a full turn. [`iint_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L30).

**Theorem · Continuity of the angular Fourier phase.** The negative-frequency complex phase is continuous on the closed angular interval used for integration. [`exp_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L42).

**Theorem · Expand a tail-family output convolution.** The output mode equals the sum of input polynomial expansions multiplied by the multiplier's Fourier coefficients at the difference frequencies. [`output_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L46).

**Definition · A unit matrix entry.** The matrix has value one at its chosen row and column and zero at every other entry. [`unitE`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L95).

**Theorem · Expand a matrix linear functional.** A complex-linear functional on matrices equals the sum of each matrix entry times its value on the corresponding unit-entry matrix. [`lin_rep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L97).

**Theorem · Commute a matrix functional with modes.** The Fourier coefficient of a scalar multiple of a matrix-linear functional equals that scalar times the functional of the entrywise Fourier coefficients. [`mode_map`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L122).

**Theorem · Integrate bounded angular functions.** A measurable complex angular function with a uniform bound is interval integrable over one full turn. [`iint_of_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L150).

**Theorem · The cell rectangle is measurable.** The radial-height rectangle of a cell box is measurable. [`rect_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L157).

**Theorem · Tail multipliers are circle integrable.** A regular tail family has angularly integrable multipliers for almost every point of the cell rectangle. [`mult_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L159).

**Theorem · Circle-integrable model entries.** The cylindrical measurability and model bounds give angular integrability of the strain and curl-gradient entries almost everywhere on the cell. [`entries_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L166).

**Theorem · Conjugating a mode reverses frequency.** The conjugate of a real matrix field's Fourier mode equals its mode at the negative frequency. [`conj_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L186).

**Definition · Express velocity action as a linear map.** The definition expresses the velocity wave action through a fixed linear combination of matrix entries and permutation signs. [`velLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L201).

**Theorem · Linear form of the velocity wave action.** The velocity wave action equals its matrix-linear expression evaluated on the conjugated coefficient matrix. [`wav_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L206).

**Theorem · Reconstruct from nine unit matrices.** Summing the flattened matrix coefficients against unit-entry matrices recovers the original entrywise linear expression. [`lin9`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L209).

**Theorem · Reconstruct the velocity wave action.** The weighted sum of velocity wave actions on the nine unit matrices equals the wave action on the reconstructed strain matrix. [`vel_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L228).

**Theorem · Reconstruct the strain wave action.** The curl and velocity component sums against their unit inputs combine into the strain wave action. [`strain_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L238).

**Theorem · Curl components commute with finite sums.** Taking the coefficient curl after a finite weighted matrix expansion gives the corresponding weighted sum of coefficient curls. [`curl_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L247).

**Theorem · Projections belong to polynomial spaces.** The cell projection belongs to the bivariate polynomial space with its selected radial and height degrees. [`proj_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L255).

**Theorem · Reconstruct from cell coefficients.** For valid bases, the finite coefficient expansion reconstructs a polynomial within the selected degree bounds pointwise. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L261).

**Theorem · Reorder two component-mode sums.** Two component-first sums can be combined into one mode-first sum of their component sums. [`sum_swap2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L271).

**Theorem · Exchange matrix-entry and mode sums.** The finite sum over nine matrix entries commutes with the finite mode sum. [`sum_swap9`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L277).

**Theorem · Additivity of the velocity matrix form.** The linear matrix expression for the velocity wave action preserves addition in its matrix input. [`velLin_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L280).

**Theorem · Scale the velocity matrix form.** Scaling the matrix input scales the velocity wave-action expression by the same complex factor. [`velLin_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L285).

**Theorem · Transform the velocity wave action.** The multiplier Fourier coefficient of the velocity wave action is the action evaluated on the curl-gradient mode with the reversed difference frequency. [`vel_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L290).

**Theorem · Strain-family convolution identity.** The strain tail family's output equals the modified radial factor times the finite wave-action convolution of model modes with retained strain and velocity modes. [`conv_strain`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L312).

**Theorem · Velocity-family convolution identity.** The velocity tail family's output equals the modified radial factor times the finite velocity wave-action convolution with retained strain modes. [`conv_vel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L379).

**Theorem · The band family adds a radial factor.** The band tail family's output equals radius times the modified radial factor times the velocity wave-action convolution with retained strain modes. [`conv_band`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L410).

**Theorem · Increase polynomial degree bounds.** A bivariate polynomial remains in its polynomial space after either allowed degree bound is increased. [`poly_raise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L441).

**Theorem · Radial multiplication raises one degree.** Multiplication by the radial coordinate raises the radial degree bound by one and leaves the height bound unchanged. [`poly_mulfst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L453).

**Theorem · Polynomial modified radial weights.** Off the axis, multiplying a bounded-degree polynomial by the modified radial factor produces a polynomial within a degree bound larger by at least one. [`rhat_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L468).

**Theorem · Polynomial components after a linear map.** A fixed matrix acting on paired polynomial strain and velocity components produces polynomial components with the same degree bounds. [`matAct_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L476).

**Theorem · Integrability of coefficient integrands.** The coefficient integrand is integrable when the field is line-weight integrable, since the basis factors are continuous on the compact cell. [`intg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L487).

**Theorem · Cell coefficients are complex linear.** The cell coefficient of a complex linear combination of integrable fields equals the same combination of their coefficients. [`coef_lin2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L502).

**Theorem · Cell coefficients respect a.e. equality.** Functions equal almost everywhere on the cell rectangle have the same cell coefficients. [`coef_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L512).

**Theorem · Scale the inverse turn operator.** A real scalar can be moved inside the adjoint turn inverse without changing its value. [`turn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L517).

**Theorem · Coefficients commute with inverse turns.** Taking cell coefficients after the adjoint turn inverse equals applying that inverse to the vector of cell coefficients. [`coef_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L521).

**Theorem · Almost every cell point is off the axis.** The radial coordinate is nonzero almost everywhere with respect to the cell rectangle measure. [`axis_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L554).

**Theorem · Integrate inverse-turn coefficients.** The integrability hypotheses on vector components imply integrability of the basis-weighted coefficient integrand after the adjoint turn inverse. [`intg_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L567).

**Theorem · The turn inverse sends zero to zero.** Applying the adjoint turn inverse to the zero vector gives the zero vector. [`turn_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L585).

**Theorem · A fixed radius has zero area.** Almost every planar point has radial coordinate different from any fixed real value. [`fst_ne_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L589).

**Theorem · A fixed height has zero area.** Almost every planar point has height coordinate different from any fixed real value. [`snd_ne_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L596).

**Theorem · Full measure of the cell interior.** Almost every point of a valid cell rectangle lies strictly between its radial and height endpoints. [`open_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L603).

**Theorem · Represent the far coefficients.** The cylindrical composition proposition yields the far coefficient identities, including the band correction through the adjoint turn inverse. [`farCoef_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L611).

**Theorem · Represent the far coefficients.** The cylindrical-composition proposition yields the far-coefficient identities expressing folded strain coefficients as the strain-tail output plus the optional inverse-turn band correction, and velocity coefficients as the velocity-tail output. [`farCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L775).

### Breakdown.FracCell.MeshFarCoefEnergy

Weighted basis orthogonality bounds finite coefficient energies and proves summability of the output coefficient tails. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The cell rectangle has finite measure.** Restricted Lebesgue measure on the closed bounded cell rectangle is a finite measure. [`rect_finite`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L17).

**Theorem · The cell rectangle is measurable.** The radial-height cell rectangle is measurable. [`rect_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L20).

**Definition · A basis function indexed by a pair.** The function is the radial polynomial at the first index times the height polynomial at the second, embedded in the complex numbers. [`basisFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L22).

**Theorem · Tensor basis functions are continuous.** Each pair-indexed tensor-product basis function is continuous. [`basisFn_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L24).

**Theorem · Complex cell-basis orthogonality.** For valid bases, the line-weighted integral of two pair-indexed basis functions is one for equal pairs and zero otherwise. [`basis_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L30).

**Theorem · Bound finite coefficient energy by L2.** The sum of squared norms of any finite set of cell coefficients is at most the field's line-weighted squared norm. [`coefEnergy_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L53).

**Theorem · Tail inputs are jointly continuous.** The finite basis-and-Fourier reconstruction of a tail-family input is jointly continuous in radius, height and angle. [`inputFn_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L188).

**Theorem · Bound reconstructed tail inputs.** Each reconstructed tail input has a uniform bound over the compact cell rectangle and every angle. [`inputFn_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L196).

**Theorem · Bounded measurable tail outputs.** For a regular tail family, every output mode is measurable on the cell and has a uniform bound there. [`outputMode_regular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L212).

**Theorem · Summability of far output squares.** The theorem proves summability of the squared cell coefficients beyond any cutoff for each output mode of a regular tail family. [`farSummable_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L260).

### Breakdown.FracCell.MeshFarPoly

Basis orthogonality removes low-degree polynomial additions from all coefficients beyond their degree cutoff. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The radial line weight is continuous.** The cell line weight is continuous as a function of radius. [`lineWeight_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L17).

**Theorem · Radial basis polynomials are continuous.** Each radial basis polynomial is a continuous function. [`radialPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L23).

**Theorem · Height basis polynomials are continuous.** Each height basis polynomial is a continuous function. [`heightPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L27).

**Theorem · Radial orthogonality to lower powers.** For valid cell bases, a radial basis polynomial is line-weight orthogonal to every smaller-degree monomial. [`radial_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L31).

**Theorem · Height orthogonality to lower powers.** For valid cell bases, a height basis polynomial is orthogonal to every smaller-degree monomial. [`height_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L69).

**Theorem · Cell polynomials are continuous.** Every bounded-degree bivariate polynomial is continuous. [`poly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L106).

**Theorem · Coefficient vanishing above the degree.** A polynomial with both degrees at most D has zero cell coefficient whenever either coefficient index exceeds D. [`coef_poly_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L111).

**Theorem · Far coefficients ignore low polynomials.** Adding a polynomial of degree at most D in each variable leaves every coefficient beyond D unchanged. [`coef_add_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L155).

**Theorem · Off-axis equality preserves coefficients.** Functions agreeing on the cell rectangle away from the radial axis have identical cell coefficients. [`coef_congr_off_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L183).

**Theorem · Far coefficients under polynomial shifts.** If two functions differ off the axis by a polynomial of bounded degree, their coefficients agree beyond that degree cutoff. [`coef_far_off_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarPoly.lean#L199).

### Breakdown.FracCell.MeshFarRegular

Cylindrical pullback measurability and bounded frame entries verify regularity of the strain, velocity and band tail multiplier families. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · Measurability after cylindrical pullback.** The proposition requires a measurable operator-valued spatial field to remain almost everywhere strongly measurable after cylindrical coordinate substitution. [`CylinderCompStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L15).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.cylinderComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CylinderComp.lean#L120) ([lean/Breakdown/FracCell/CylinderComp.lean:120](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CylinderComp.lean#L120); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.farMajorant_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374) ([lean/Breakdown/FracCell/MeshFar.lean:374](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374); named reference in type); [`Breakdown.CellCert.CellAnalysis.MeshFarCoefInternal.entries_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L166) ([lean/Breakdown/FracCell/MeshFarCoef.lean:166](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L166); named reference in type); [`Breakdown.CellCert.CellAnalysis.MeshFarCoefInternal.farCoef_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L611) ([lean/Breakdown/FracCell/MeshFarCoef.lean:611](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L611); named reference in type); [`Breakdown.CellCert.CellAnalysis.farCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L775) ([lean/Breakdown/FracCell/MeshFarCoef.lean:775](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L775); named reference in type); [`Breakdown.CellCert.CellAnalysis.MeshFarRegularInternal.entry_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L86) ([lean/Breakdown/FracCell/MeshFarRegular.lean:86](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L86); named reference in type); [`Breakdown.CellCert.CellAnalysis.farRegular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L154) ([lean/Breakdown/FracCell/MeshFarRegular.lean:154](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L154); named reference in type).

**Theorem · Continuity of coordinate insertion.** Inserting a real number into a fixed spatial coordinate is a continuous map. [`single_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L21).

**Theorem · Frame matrix entries are continuous.** A moving-frame matrix entry varies continuously with the linear map and angle jointly. [`frameMat_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L31).

**Theorem · A coarse norm bound for frame vectors.** Each cylindrical frame vector has norm at most two. [`frame_vec_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L42).

**Theorem · A coarse frame-entry norm bound.** The norm of a moving-frame matrix entry is at most four times the operator norm. [`frameMat_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L57).

**Theorem · Regularity of bounded multipliers.** A tail multiplier obtained by continuous functions of a bounded measurable finite-dimensional input satisfies the tail regularity structure. [`regular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L69).

**Theorem · Cylindrical frame entries are measurable.** The cylindrical composition hypothesis makes complex frame entries of a measurable operator field measurable on the cell-angle product. [`entry_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L86).

**Theorem · Build matrix measurability from entries.** A finite matrix-valued function is almost everywhere strongly measurable when all its entries are. [`mat_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L104).

**Theorem · The modified radial factor is measurable.** The modified radial factor is a measurable function on the radius-height plane. [`rHat_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L109).

**Theorem · Bound the modified radial factor.** On a valid cell rectangle, the modified radial factor has absolute value at most the maximum of one and the outer radius. [`rHat_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L113).

**Theorem · A cylindrical cell point is in the solid.** A point from the valid cell rectangle, at any angle, lies in the cell solid. [`cyl_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L123).

**Theorem · Bound all frame matrix entries together.** An operator norm bound C gives a bound of four C on the finite complex matrix of moving-frame entries. [`mat_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L144).

**Theorem · The three far families are regular.** The cylindrical composition proposition supplies regularity of the strain, velocity and band tail families under the valid form and cell hypotheses. [`farRegular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L154).

### Breakdown.FracCell.MeshFarSt

The coefficient input encodings and three far-field propositions separate output identification, multiplier regularity and summability. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Inputs for the strain tail family.** The two input blocks select the curl of the low-strain coefficient matrix and the low-velocity coefficient vector respectively. [`strainInput`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarSt.lean#L19).

**Definition · Flatten the velocity strain input.** The velocity-family input lists the nine low-strain matrix entries using a single finite index. [`velocityInput`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarSt.lean#L23).

**Interface · Far coefficients as family outputs.** The proposition identifies the high-degree folded strain and velocity coefficients with tail-family outputs, including the angular-column band correction. [`FarCoefStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarSt.lean#L29).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.MeshFarCoefInternal.farCoef_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L611) ([lean/Breakdown/FracCell/MeshFarCoef.lean:611](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L611); named premises: `CylinderCompStatement`); [`Breakdown.CellCert.CellAnalysis.farCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L775) ([lean/Breakdown/FracCell/MeshFarCoef.lean:775](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoef.lean#L775); named premises: `CylinderCompStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.farMajorant_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:365](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L365); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L538) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:538](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L538); named reference in type); [`_private.Breakdown.FracCell.MeshFar.0.Breakdown.CellCert.CellAnalysis.farMajorant_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180) ([lean/Breakdown/FracCell/MeshFar.lean:180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351) ([lean/Breakdown/FracCell/MeshFar.lean:351](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374) ([lean/Breakdown/FracCell/MeshFar.lean:374](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L374); named reference in type).

**Interface · Regularity of the three far families.** The proposition requires the strain, velocity and band families to satisfy tail regularity for every compatible cell inside the model region. [`FarRegularStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarSt.lean#L48).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.farRegular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L154) ([lean/Breakdown/FracCell/MeshFarRegular.lean:154](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarRegular.lean#L154); named premises: `CylinderCompStatement`).

**Theorems using this interface name.** [`_private.Breakdown.FracCell.MeshFar.0.Breakdown.CellCert.CellAnalysis.farMajorant_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180) ([lean/Breakdown/FracCell/MeshFar.lean:180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351) ([lean/Breakdown/FracCell/MeshFar.lean:351](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351); named reference in type).

**Interface · Summability of far output coefficients.** The proposition requires the squared coefficients beyond the cutoff to be summable for every mode and output of a regular tail family. [`FarSummableStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarSt.lean#L55).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.farSummable_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L260) ([lean/Breakdown/FracCell/MeshFarCoefEnergy.lean:260](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFarCoefEnergy.lean#L260); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`_private.Breakdown.FracCell.MeshFar.0.Breakdown.CellCert.CellAnalysis.farMajorant_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180) ([lean/Breakdown/FracCell/MeshFar.lean:180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L180); named reference in type); [`Breakdown.CellCert.CellAnalysis.farMajorant_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351) ([lean/Breakdown/FracCell/MeshFar.lean:351](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFar.lean#L351); named reference in type).

### Breakdown.FracCell.MeshFluxHeight

Height-strip additivity and polynomial test recombination identify a vertical flux with the difference of two stream values. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Height strip integrands are integrable.** The weighted weak-pair and continuous-test hypotheses make the height-strip integrand integrable on the specified finite rectangle. [`term_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L15).

**Theorem · Split a height moment in radius.** A height-strip moment over a radial interval equals the sum of the moments over its two adjacent radial pieces. [`strip_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L36).

**Theorem · A zero-width strip moment vanishes.** A height-strip moment with equal radial endpoints is zero. [`strip_point`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L60).

**Theorem · Combine two tests into radial weight.** When two test values combine to the radial coordinate, their weighted complex products combine to the radial-weighted product. [`combine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L66).

**Theorem · Height flux from stream independence.** The stream-independence proposition and height-strip identities imply the height-flux proposition. [`fluxHeight_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L72).

**Theorem · Supply the height-flux identity.** The theorem proves the height-flux proposition using the established stream-independence result. [`fluxHeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxHeight.lean#L123).

### Breakdown.FracCell.MeshFluxRadial

The radial flux proof removes an auxiliary strip crossing the axis and then identifies the flux with endpoint stream values. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · Move a radial strip boundary to the axis.** The proposition requires a zero-frequency radial-velocity strip moment with a negative auxiliary level to equal the moment using zero as its auxiliary level. [`RadialAxisCrossStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L16).

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.radialAxisCross_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L453) ([lean/Breakdown/FracCell/RadialAxisCross.lean:453](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L453); named premises: `AxisPrimitiveStatement`); [`Breakdown.CellCert.CellCoordinates.radialAxisCross_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L460) ([lean/Breakdown/FracCell/RadialAxisCross.lean:460](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L460); named premises: `ModeRadialWeakStatement`); [`Breakdown.CellCert.CellCoordinates.radialAxisCross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L463) ([lean/Breakdown/FracCell/RadialAxisCross.lean:463](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L463); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellCoordinates.fluxStream_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:376](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L376); named reference in type); [`Breakdown.CellCert.CellCoordinates.fluxRadial_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L23) ([lean/Breakdown/FracCell/MeshFluxRadial.lean:23](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L23); named reference in type).

**Theorem · Derive radial flux from axis crossing.** The axis-crossing proposition supplies the remaining input for expressing radial flux as the difference of two stream values. [`fluxRadial_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshFluxRadial.lean#L23).

### Breakdown.FracCell.MeshGaugeLinear

Gauge-normalized pressure data and finite path sums make the canonical left and right mesh gauges linear in admissible fields. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Finite path sums preserve linearity.** If each value along a finite list is linear in the fields, the list sum preserves the same real linear combination. [`list_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinear.lean#L17).

**Theorem · Gauge class values are linear.** Under the pressure-gauge linearity hypotheses, each mesh class value preserves real linear combinations of admissible fields. [`classValue_linear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinear.lean#L27).

**Theorem · Canonical gauge linearity.** With the stated valid nonzero gauge-segment conditions, both canonical mesh gauge shifts preserve real linear combinations of admissible fields. [`meshGaugeLinear_of_gauge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinear.lean#L69).

**Theorem · The canonical mesh gauges are linear.** The theorem supplies linearity of the canonical left and right gauge shifts under the mesh-data hypotheses. [`meshGaugeLinear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinear.lean#L82).

### Breakdown.FracCell.MeshGaugeLinearMoment

Affine pressure-potential formulas are integrated through radial and height moments, keeping the constant-pressure correction explicit. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Closed rectangles are compact.** A product of two closed bounded real intervals is compact. [`rect_cpt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L17).

**Theorem · Integrate an affine combination.** An almost everywhere affine combination of integrable functions has integral equal to the corresponding affine combination of their integrals. [`int_aff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L20).

**Theorem · Integrability with continuous tests.** Multiplying an integrable complex function by a continuous real test on a compact region preserves integrability. [`mulc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L29).

**Theorem · The constant zero-pressure mode is one.** The zero Fourier mode of the constant-one pressure field equals one at every radius and height. [`presMode_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L33).

**Theorem · Integrate the radial affine derivative.** The weak radial integrability hypotheses make the affine-ramp multiple of the derivative integrable on the strip rectangle. [`weighted_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L38).

**Theorem · Affine combinations of radial moments.** Under the weak-pair and integrability hypotheses, a radial strip moment respects a real linear combination plus the specified constant-potential contribution. [`radial_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L66).

**Theorem · Affine sums of weighted height moments.** A radial-weighted height moment of an affine field combination equals the same moment combination plus the constant-potential moment. [`height_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L101).

**Theorem · Face test polynomials are continuous.** Every polynomial test attached to a face segment is continuous. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L139).

**Theorem · Constant correction to pressure moments.** The zero-mode pressure moment of a real combination of gradient fields equals the combination of their pressure moments plus the selected potential-constant correction. [`presMoment_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearMoment.lean#L143).

### Breakdown.FracCell.MeshGaugeLinearParts

A nonzero constant test makes the pressure gauge normalization well-defined and removes the constant offset from pressure datum values. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Volume of an ordered rectangle.** The real Lebesgue area of an ordered rectangle is the product of its radial and height side lengths. [`vol_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearParts.lean#L19).

**Theorem · The zeroth segment test is constant.** The zeroth segment test evaluates everywhere to its constant coefficient. [`test_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearParts.lean#L24).

**Theorem · A distinct-level edge sign is nonzero.** The edge orientation sign is nonzero when its two levels are distinct. [`edgeSign_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearParts.lean#L27).

**Theorem · The gauge normalization is nonzero.** The valid gauge-segment and nonzero zeroth-test assumptions imply that the layout's constant-pressure gauge moment is nonzero. [`gaugeUnit_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearParts.lean#L31).

**Theorem · Normalized pressure data are linear.** After the gauge normalization, pressure datum values preserve real linear combinations of admissible fields. [`pressureDatum_linear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearParts.lean#L75).

### Breakdown.FracCell.MeshGaugeLinearPotential

Weak potentials for the same gradient differ by an almost everywhere constant, which explains the affine correction when chosen potentials are combined. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Valid potentials are locally integrable.** A potential satisfying the stated weak-gradient regularity assumptions is locally integrable. [`loc_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L23).

**Theorem · Integrate potential derivative pairings.** The product of a valid potential with a compactly supported test's coordinate derivative is integrable. [`test_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L31).

**Theorem · Zero coordinate values force a zero map.** A continuous linear functional vanishing on all three standard unit vectors is zero. [`clm_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L39).

**Theorem · Smoothing preserves zero weak gradients.** Convolving a locally integrable function with zero weak gradient against a smooth compactly supported test gives a function with zero spatial derivative. [`conv_deriv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L45).

**Theorem · Weakly constant fields are a.e. constant.** A locally integrable real function with vanishing weak derivatives agrees almost everywhere with a constant. [`const_of_zero_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L76).

**Theorem · Gradient of the chosen potential.** For a gradient field, the selected potential satisfies the formal weak potential specification. [`potentialOf_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L109).

**Theorem · Two potentials differ by a constant.** Two valid potentials of the same gradient field differ almost everywhere by a real constant. [`pot_zero_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L116).

**Theorem · Combine potentials of combined gradients.** The real linear combination of two valid potentials is a potential of the same linear combination of their gradient fields. [`pot_combo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L132).

**Theorem · Affine potentials up to a constant.** The selected potential of a real linear combination of gradient fields equals the combination of their selected potentials plus an almost everywhere constant. [`potential_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshGaugeLinearPotential.lean#L166).

### Breakdown.FracCell.MeshMomentLinear

The constant-pressure correction in true data cancels against the canonical gauge shifts, leaving linear canonical mesh moments. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Cell data of a constant pressure shift.** The data vector is zero except on zero-frequency pressure entries, where it equals the sum of the left and right pressure-shift coefficients. [`constPressureData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L17).

**Interface · Affine true data with a common gauge.** The proposition requires true data of combined admissible fields to equal their linear combination plus a single constant-pressure correction shared by layouts with the same gauge. [`DataAffineStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L23).

**Reader note.** The scalar correction is chosen before the layout and applies uniformly to every permitted layout with that fixed gauge; this quantifier order is needed when comparing cells.

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.dataAffine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L403) ([lean/Breakdown/FracCell/MeshDataAffine.lean:403](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshDataAffine.lean#L403); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellCoordinates.meshCompatibility_of_slot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L380) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:380](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L380); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshMomentLinear.base_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L158) ([lean/Breakdown/FracCell/MeshMomentLinear.lean:158](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L158); named reference in type); [`Breakdown.CellCert.CellCoordinates.MeshMomentLinear.moment_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L173) ([lean/Breakdown/FracCell/MeshMomentLinear.lean:173](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L173); named reference in type); [`Breakdown.CellCert.CellCoordinates.meshMomentLinear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L191) ([lean/Breakdown/FracCell/MeshMomentLinear.lean:191](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L191); named reference in type).

**Theorem · Preserve a relation under finite sums.** A pointwise linear relation on the entries of a finite list gives the same relation between their list sums. [`list_sum_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L39).

**Theorem · Constant pressure shifts in datum values.** The affine true-data relation adds the constant times the sum of shift coefficients to the corresponding pressure datum combination. [`pdv_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L53).

**Theorem · Gauge jumps cancel the constant offset.** The gauge jump preserves the real linear combination when the shared constant-pressure offset is inserted into the pressure data. [`jump_linear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L64).

**Theorem · Gauge-shifted data are linear.** The matching affine gauge shifts cancel the constant-pressure correction, so shifted data preserve the real linear combination exactly. [`shifted_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L76).

**Theorem · Gauge class values absorb the offset.** Under the affine pressure-data relation, a class value is the linear combination of the original class values minus the common pressure constant. [`classValue_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L105).

**Theorem · Local mesh values are linear.** Once the compatible gauge shift is included, each local coordinate value preserves the given real linear combination. [`localValue_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L144).

**Theorem · Base mesh moments preserve combinations.** The base moment of combined admissible fields is the same real linear combination of their base moments. [`base_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L158).

**Theorem · Linear combinations of mesh moments.** The full canonical moment vector of combined admissible fields equals the real linear combination of their canonical moment vectors. [`moment_affine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L173).

**Theorem · Linearity and normalization of moments.** The theorem supplies the zero, addition and real-scaling laws for canonical moments together with recovery of the actuator coordinates. [`meshMomentLinear`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshMomentLinear.lean#L191).

### Breakdown.FracCell.MeshRootZero

The canonical root shifts normalize every designated root pressure datum to zero. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Canonical gauge shifts zero the roots.** The theorem proves that the root-shifted value vanishes at every designated gauge root for admissible fields in a valid mesh. [`meshRootZero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRootZero.lean#L11).

### Breakdown.FracCell.MeshRowFar

Polynomial row couplings have no coefficients beyond their degree, so the infinite far row-square expression equals a finite truncation. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Vanishing of lower-power moments.** A triangular polynomial family with the given orthogonality and nonzero leading coefficients is orthogonal to every lower-degree monomial. [`triangular_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L17).

**Theorem · The cell line weight is continuous.** The radial line weight of a cell box is continuous. [`lineWeight_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L53).

**Theorem · Radial basis functions are continuous.** Every radial basis polynomial is continuous. [`radialPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L66).

**Theorem · Height basis functions are continuous.** Every height basis polynomial is continuous. [`heightPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L70).

**Theorem · Radial polynomials kill lower monomials.** The line-weighted pairing of a radial basis polynomial with a lower-degree monomial vanishes for valid bases. [`radial_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L74).

**Theorem · Height polynomials kill lower monomials.** The pairing of a height basis polynomial with a lower-degree monomial vanishes for valid bases. [`height_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L82).

**Theorem · The radial axis has zero planar measure.** Almost every point in the radius-height plane has nonzero radius. [`axis_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L102).

**Theorem · Interior positive radii a.e..** With respect to the cell rectangle measure, almost every point lies in the open rectangle and has nonzero radial coordinate. [`open_rect_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L110).

**Theorem · Row coefficients vanish above degree.** A row coupling agreeing off the axis with a bounded-degree polynomial has zero cell coefficients beyond that degree. [`coef_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L120).

**Theorem · Regroup finite far row sums.** The cutoff-restricted double coefficient sum can be regrouped as the sum of the separate finite mode contributions. [`sum_regroup`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L178).

**Theorem · Replace the infinite row tail by a sum.** The polynomial row-coupling condition makes the far row-square expression equal to its truncation at the specified degree bound. [`rowFarFinite_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshRowFar.lean#L201).

### Breakdown.FracCell.MeshSkeleton

A valid segment split expresses each local coordinate as a finite combination of canonical moments and then supplies the skeleton-slot proposition. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Split rows recover local coordinates.** Under a valid segment split, the weighted list of canonical moments sums to the corresponding local cell coordinate value. [`segSplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L15).

**Theorem · Assemble the mesh skeleton slots.** The segment-split proposition supplies the reconstruction identity between canonical mesh moments and the skeleton's local coordinate slots. [`meshSkeletonSlot_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeleton.lean#L117).

### Breakdown.FracCell.MeshSkeletonPair

Shared skeleton keys identify physical traces across layouts while the canonical pressure gauges align their shifted data. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Predicate · Validity needed for trace comparison.** The structure requires the correct symmetry order, valid side and pressure segments, radial segments away from the axis and valid corner-strip parameters. [`LayoutValid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L20).

**Theorem · Velocity modes agree at a common order.** Two layouts with matching symmetry order give identical velocity-mode functions for the same field. [`velMode_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L33).

**Theorem · Gradient modes agree at a common order.** Two layouts with matching symmetry order give identical gradient-mode functions for the same field. [`gradMode_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L37).

**Theorem · Layouts share second-derivative modes.** Matching layout symmetry orders identify every second-derivative mode function. [`secondMode_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L41).

**Theorem · Layouts share pressure-gradient modes.** Matching layout symmetry orders identify every pressure-gradient mode function. [`pressureGrad_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L45).

**Theorem · Matching gauges identify pressure modes.** Layouts with matching order and pressure gauge give identical gauge-normalized pressure modes. [`pressMode_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L49).

**Theorem · Shared velocity keys give equal data.** Matching velocity skeleton keys in valid layouts yield equal shifted velocity data under the trace-independence hypotheses. [`vel_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L58).

**Theorem · Shared gradient keys give equal data.** Matching gradient skeleton keys in valid layouts yield equal shifted gradient data. [`grad_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L75).

**Theorem · Shared corner keys give equal data.** Matching corner skeleton keys in valid layouts yield equal corner data under the admissibility and corner-independence hypotheses. [`corner_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L93).

**Theorem · Shared stream keys give equal data.** The stream-independence proposition identifies stream entries with the same endpoint key across valid layouts. [`stream_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L113).

**Theorem · Aligned pressure keys give equal data.** Matching pressure keys and matching gauge values at their pressure positions give equal shifted pressure entries. [`pres_case`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L131).

**Theorem · Shared keys identify shifted cell data.** Valid layouts with the same gauge give equal data at a shared nonprivate key when their canonical shifts agree at matching pressure positions. [`shifted_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L186).

**Theorem · Shared keys have the same preset scale.** The preset scaling factor is equal for two layout data entries with the same skeleton key. [`scale_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L201).

**Definition · A common value for each skeleton key.** The definition assigns velocity, gradient, pressure and stream moments to geometric keys, with explicit zero values for corner and private cases. [`keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L213).

**Reader note.** Corner and private cases are assigned zero in this common-key helper; the identification theorem shifted_key explicitly excludes both kinds.

**Theorem · Reconstructed key segments are valid.** Rebuilding a segment from the geometric fields of a valid face segment preserves its validity. [`keySegment_valid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L236).

**Theorem · Velocity data equal the common key value.** The shifted velocity datum of a valid layout equals the corresponding common key value computed in a matching-order reference layout. [`vel_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L240).

**Theorem · Gradient data equal the common key value.** The shifted gradient datum of a valid layout equals the corresponding common key value in the reference layout. [`grad_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L255).

**Theorem · Identify aligned pressure key values.** With gauge values matched to the key's level function, shifted pressure data equal the common pressure-key value. [`pres_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L274).

**Theorem · Stream data equal the common key value.** The stream-independence proposition identifies a layout's stream datum with its common stream-key value. [`stream_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L315).

**Theorem · Identify shifted data through its key.** For a key that is neither private nor a corner, valid layout data and aligned gauge positions identify the shifted datum with its common key value. [`shifted_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L326).

**Definition · Scale pressure keys separately.** The key scale is the selected pressure scale for pressure keys and one for every other key kind. [`keyScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L341).

**Definition · Positive level required for radial keys.** The key condition requires positive radius for radial velocity, gradient and pressure keys and imposes no condition on the other kinds. [`keyLevelPos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L345).

**Theorem · Preset scale depends only on the key.** The layout's preset datum scale equals the scale assigned to its skeleton key. [`scale_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L351).

**Theorem · A segment split preserves key kinds.** A valid segment split excludes private and corner keys, preserves preset scales and keeps zero-mode pressure contributions within zero-mode pressure splits. [`split_kinds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L354).

**Theorem · Extract real or imaginary parts of a sum.** The selected real or imaginary component of a real-weighted complex list sum equals the real-weighted sum of the selected components. [`part_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L389).

**Theorem · Mesh coordinate layouts satisfy validity.** Each coordinate layout supplied by valid mesh data satisfies the trace-comparison validity structure. [`layoutValid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L410).

**Theorem · Canonical side shifts are class values.** The canonical left or right gauge of a cell equals the value of its corresponding node class. [`side_value`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L414).

**Theorem · Sparse row entries equal their list sum.** Evaluating the accumulated sparse row entries equals the weighted sum along the original row list. [`sum_rowEntries`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L418).

**Theorem · Agreement of shifted shared keys.** The mesh compatibility and node-class conditions identify canonical shifted data from different cells with the same eligible skeleton key. [`value_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L427).

**Theorem · Shared coordinates agree locally.** Matching eligible keys and component choices give equal real local coordinate values in their respective cells. [`localValue_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L444).

**Theorem · A pressure datum retains its frequency.** The layout's mode selector applied to a pressure datum returns that datum's Fourier frequency. [`mode_of_pressure`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L459).

**Theorem · Deleted gauge entries have pressure keys.** Every gauge-deleted datum has a skeleton key of zero-frequency pressure type. [`deleted_key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L465).

**Theorem · Deleted gauge entries have zero value.** For valid mesh data, the real part of a canonically shifted gauge-deleted datum vanishes. [`deleted_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L473).

**Theorem · Real parts of zero-frequency slots.** A system skeleton coordinate with zero Fourier mode selects the real component. [`system_part`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L504).

**Theorem · Positive radial levels of valid keys.** Every datum key in a valid layout satisfies the radial-level positivity condition. [`level_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L526).

**Theorem · A common denominator leaves the list sum.** A common real denominator in every weighted list term can be factored out of the entire sum. [`list_div`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonPair.lean#L538).

### Breakdown.FracCell.MeshSkeletonSplit

Additivity of weak strip moments and polynomial test changes validate segment and flux splits, including the zero-stream and deleted-gauge cases. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Split a rectangle integral in height.** An integrable rectangle integral equals the sum over two adjacent height subrectangles when the split point lies between the endpoints. [`prod_split_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L13).

**Theorem · Split a rectangle integral in radius.** An integrable rectangle integral equals the sum over two adjacent radial subrectangles when the split point lies between the endpoints. [`prod_split_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L29).

**Theorem · Enclose an interval in a symmetric one.** Every closed interval lies in the symmetric interval with radius the sum of its endpoint absolute values. [`box_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L45).

**Theorem · Radial strip terms are integrable.** The weak radial pair and continuous test assumptions give integrability of the radial strip term on its defining rectangle. [`radial_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L51).

**Theorem · Expand the weighted height strip term.** The height strip term is the affine combination of the weighted field and weighted derivative, multiplied by its radial test. [`height_term_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L67).

**Theorem · Height strip terms are integrable.** The weak height pair and continuous test assumptions give integrability of the height strip term on its defining rectangle. [`height_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L75).

**Theorem · Orient radial moments as cell integrals.** The radial strip moment equals the integral of its strip term multiplied by the orientation sign. [`rsm_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L96).

**Theorem · Orient height moments as cell integrals.** The height strip moment equals the integral of its weighted strip term multiplied by the orientation sign. [`hsm_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L100).

**Theorem · Radial moments split along their face.** A radial strip moment over a height interval equals the sum of the moments over its two adjacent height pieces. [`rsm_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L109).

**Theorem · Radial moments are additive in the test.** The radial strip moment of a sum of admissible continuous tests equals the sum of their moments. [`rsm_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L113).

**Theorem · Scale real tests in radial moments.** Multiplying the test by a real scalar multiplies its radial strip moment by that scalar. [`rsm_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L125).

**Theorem · Radial moments respect equal tests.** Two tests agreeing on the integration interval give equal radial strip moments. [`rsm_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L134).

**Theorem · Height moments split along their face.** A height strip moment over a radial interval equals the sum over its two adjacent radial pieces. [`hsm_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L147).

**Theorem · Height moments are additive in the test.** The height strip moment of a sum of admissible continuous tests equals the sum of their moments. [`hsm_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L152).

**Theorem · Scale real tests in height moments.** Multiplying the test by a real scalar multiplies its weighted height strip moment by that scalar. [`hsm_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L164).

**Theorem · Height moments respect equal tests.** Two tests agreeing on the integration interval give equal weighted height strip moments. [`hsm_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L173).

**Theorem · Continuity of finite test sums.** A finite list sum of continuous real test functions is continuous. [`list_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L182).

**Theorem · A test functional preserves finite sums.** A functional additive on admissible tests sends a finite list sum to the list sum of its values. [`list_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L190).

**Theorem · Evaluate an abstract segment split.** An additive interval functional that is linear in tests evaluates a valid polynomial segment split as the specified weighted list of child values. [`split_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L205).

**Definition · A common radial-or-height moment.** The definition selects a radial strip moment or a height strip moment, with optional radial weighting and auxiliary level one above the face. [`momJ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L249).

**Theorem · The common moment splits by interval.** The common radial-or-height moment is additive under an admissible division of its face interval. [`momJ_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L260).

**Theorem · Add tests in the common moment.** The common moment of a sum of admissible tests equals the sum of their common moments. [`momJ_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L268).

**Theorem · The common moment preserves test scaling.** Real scaling of a test scales the common radial-or-height moment by the same factor. [`momJ_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L278).

**Theorem · The common moment respects test equality.** Tests agreeing on the face interval give equal common radial-or-height moments. [`momJ_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L284).

**Theorem · Finite monomial tests are continuous.** A finite polynomial test expressed as a monomial sum is continuous. [`poly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L291).

**Theorem · Weak moments respect segment splitting.** The radial-or-height weak moment of a segment test equals the weighted list of child moments specified by a valid segment split. [`split_mom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L294).

**Predicate · A function represented by a polynomial.** The predicate says that a real function agrees everywhere with the evaluation of some real polynomial. [`IsPolyFun`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L312).

**Theorem · Continuity of represented polynomials.** Every real function represented by a polynomial is continuous. [`polyFun_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L314).

**Theorem · A finite monomial sum is polynomial.** A finite coefficient-weighted monomial sum has a polynomial representation. [`polyFun_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L320).

**Theorem · Polynomial representation of finite sums.** A finite list sum of polynomially represented functions also has a polynomial representation. [`polyFun_list`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L324).

**Theorem · Determine a polynomial on an interval.** Two polynomially represented functions agreeing on a nonempty closed interval agree at every real point. [`polyFun_ext`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L336).

**Theorem · Add weighted radial primitives.** The radial weighted integral of a sum of admissible tests equals the sum of their radial weighted integrals. [`rwi_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L348).

**Theorem · Scale weighted radial primitives.** The radial weighted integral of a real-scaled test equals the same scaling of its integral. [`rwi_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L357).

**Definition · The key's pressure gauge correction.** The definition adds the level-dependent gauge correction only at zero frequency, using a face integral radially and weighted endpoint primitives in height. [`presJ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L365).

**Theorem · Gauge corrections split by interval.** The zero-mode pressure gauge correction over a face interval equals the sum of the corrections over its two adjacent pieces. [`presJ_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L369).

**Theorem · Gauge corrections are additive in tests.** The pressure gauge correction of a test sum equals the sum of the corrections. [`presJ_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L381).

**Theorem · Gauge corrections preserve test scaling.** Real scaling of the test scales the pressure gauge correction by the same factor. [`presJ_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L394).

**Theorem · Split pressure moments and gauges.** A pressure moment plus its zero-mode gauge correction respects the polynomial segment split. [`pres_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L406).

**Theorem · Split velocity key values.** For an admissible field, a velocity key value equals the weighted list of its valid child segment-key values. [`vel_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L456).

**Theorem · A height-gradient key is a common moment.** A nonradial gradient key evaluates to the common weighted height moment with the corresponding gradient and second-derivative entries. [`grad_key_false`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L472).

**Theorem · A radial-gradient key is a common moment.** A radial gradient key evaluates to the common weighted radial moment with the corresponding gradient and second-derivative entries. [`grad_key_true`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L479).

**Theorem · Split gradient key values.** For an admissible field, a gradient key value equals the weighted list of its valid child segment-key values. [`grad_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L486).

**Theorem · Split pressure key values.** For an admissible field, the gauge-corrected pressure key value equals the weighted list of its valid child segment-key values. [`pres_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L513).

**Theorem · All segment splits preserve key values.** A valid segment split at the required positive radial level evaluates to the weighted sum of its child key values. [`segmentSplit_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L538).

**Theorem · Expand tests inside a linear functional.** Applying a linear functional to a finite real-weighted test expansion equals the corresponding weighted sum of functional values. [`fin_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L555).

**Definition · Stream key values with boundary zeros.** The helper is zero when radius or height is zero and otherwise uses the common stream-key value. [`streamC`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L572).

**Reader note.** The explicit zero branches are justified by the flux-stream proposition in streamC_eq for nonnegative radius; the branch definition alone does not prove the physical boundary values.

**Theorem · A zero-radius strip moment vanishes.** A height-strip moment over the radial interval from zero to zero is zero. [`hsm_zero_width`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L577).

**Theorem · Identify the stream boundary helper.** For nonnegative radius, the flux-stream proposition identifies the helper with the common stream-key value, including its boundary cases. [`streamC_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L583).

**Theorem · A velocity key is a common moment.** A velocity key evaluates to the unweighted common radial-or-height moment of its polynomial test. [`vel_key_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L610).

**Theorem · Split a velocity key into two intervals.** The polynomial change of basis on a valid face split expresses its velocity key as the finite weighted sum of child-interval velocity keys. [`flux_vel_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L615).

**Theorem · Radial keys as stream differences.** The normalized zero-mode radial velocity key equals the stream-value difference between the lower and upper height endpoints. [`flux_rad_rel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L644).

**Theorem · Height keys as stream differences.** The two test coefficients representing radial weight turn a zero-mode height velocity key combination into the stream difference between the radial endpoints. [`flux_hgt_rel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L671).

**Definition · Select a real or imaginary component.** The selector returns the real part for component zero and the imaginary part for the other component. [`ptOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L737).

**Theorem · Component extraction preserves addition.** The selected real or imaginary part of a sum equals the sum of the selected parts. [`ptOf_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L739).

**Theorem · Subtract extracted components.** The selected real or imaginary part of a difference equals the difference of the selected parts. [`ptOf_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L742).

**Theorem · Scale extracted components.** A real scalar can be moved outside extraction of the real or imaginary component. [`ptOf_ofReal_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L745).

**Theorem · Sum extracted components.** Taking the selected real or imaginary component commutes with finite summation. [`ptOf_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L748).

**Theorem · Real components match stream evaluation.** The selected component of the stream helper equals the stream evaluation applied to the corresponding real component of common key data. [`ptOf_streamC`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L752).

**Definition · Nonnegative lower velocity-key endpoints.** The predicate requires a nonnegative lower face endpoint for velocity keys and imposes no extra condition on other key kinds. [`keyLoNonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L757).

**Theorem · Flux splits preserve real key components.** The flux-stream proposition makes a valid flux split evaluate to the weighted child-key components under the radial-level and lower-endpoint conditions. [`flux_keyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L763).

**Theorem · Eligible key kinds in a flux split.** A valid flux split excludes private and corner keys, assigns unit scale to all keys and excludes zero-mode pressure keys among its children. [`flux_kinds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L800).

**Theorem · Nonnegative lower mesh-velocity bounds.** Keys obtained from a valid mesh layout satisfy the nonnegative lower-endpoint condition needed for flux splits. [`lo_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L816).

**Theorem · Flux-split rows recover local values.** With the stated ownership, component, deleted-gauge and node-alignment conditions, a flux-split row of canonical moments equals the target local coordinate value. [`fluxSplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshSkeletonSplit.lean#L825).

### Breakdown.FracCell.MeshStreamInd

The weak height identity makes strip moments independent of their auxiliary level, giving a well-defined zero-mode stream value. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Add radial weight to a height weak pair.** A height weak pair with constant weight also satisfies the height weak identity with radial weight. [`weightedPair_of_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L14).

**Theorem · Integrate the weighted height-strip term.** The weak-pair assumptions and continuous weights and tests make the height-strip integrand integrable on the specified rectangle. [`term_integrableOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L26).

**Theorem · Moment agreement at opposite levels.** For levels on opposite sides of the selected face, the weak height identity makes the two strip moments equal. [`strip_tent`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L48).

**Theorem · Independence from pairwise crossing.** If every pair of auxiliary levels straddling a fixed level has equal values, any two levels distinct from the fixed level have equal values. [`other_indep`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L89).

**Theorem · Strip independence of the stream moment.** The theorem proves that the zero-mode vertical stream moment is independent of the distinct auxiliary height level. [`streamIndependence_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamInd.lean#L100).

### Breakdown.FracCell.MeshStreamPlane

The stream value vanishes on the symmetry plane, with the zero-radius case separated from the positive-radius weak-trace argument. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The stream vanishes at zero radius.** The stream value at zero radius and zero height is zero for every auxiliary level. [`stream_radius_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamPlane.lean#L16).

**Theorem · Zero stream on the symmetry plane.** The supplied axis and weak-trace propositions imply that the stream value vanishes at height zero for nonnegative radius. [`streamPlane_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshStreamPlane.lean#L23).

### Breakdown.FracCell.MeshTail

Passes from uniform finite polynomial-tail bounds to the infinite weighted coefficient-tail estimate. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Pass a finite bound to infinite sums.** For nonnegative weights and summands, a common bound on every finite index set also bounds the weighted infinite sums. [`weighted_tsum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L18).

**Theorem · Assemble the infinite tail estimate.** The finite-tail proposition implies the infinite weighted tail-majorant proposition. [`tailMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L52).

**Theorem · Bound the complete coefficient tail.** For regular tail families satisfying the prescribed bounds, the weighted infinite output tail is bounded by the input majorant. [`tailMajorant_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L60).

### Breakdown.FracCell.MeshTailAngle

Integrates the pointwise angular-slice tail estimate and evaluates the input energies. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Integrate a finite family.** A finite sum of interval-integrable real functions is interval integrable. [`ii_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L19).

**Theorem · Average the slice tail bound.** The angular-slice bound and input-energy identities imply the averaged angular-tail proposition. [`angleTail_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27).

**Theorem · Bound the angularly averaged tail.** The angular average of the weighted finite polynomial tail is bounded by the input majorant under the cell, regularity, and tail-bound hypotheses. [`angleTail_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L112).

### Breakdown.FracCell.MeshTailCoef

Relates output Fourier coefficients to angular averages of polynomial coefficients. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Bound the synthesized angular field.** A regular tail family has a uniform bound on each synthesized output field over the cell and one angular period. [`angleField_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailCoef.lean#L19).

**Theorem · Continuity of the radial weight.** The cell line weight is a continuous real function. [`lineWeight_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailCoef.lean#L39).

**Theorem · Exchange angular and cell projection.** For regular tail families, polynomial projection of an output mode equals the corresponding Fourier coefficient of the angular field, whose projected angular function lies in L². [`coefMode_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailCoef.lean#L47).

### Breakdown.FracCell.MeshTailEnergy

Uses polynomial and angular orthogonality to evaluate the radial and height input energies exactly. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Energy of an orthonormal expansion.** For a finite orthonormal family with the stated integrability hypotheses, the weighted squared norm of its expansion integrates to the sum of squared coefficients. [`sq_sum_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L17).

**Theorem · Orthogonality of azimuthal modes.** With positive mode spacing, normalized angular integration of one mode times the conjugate of another gives one for equal indices and zero otherwise. [`exp_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L43).

**Theorem · Evaluate polynomial expansion energy.** For an orthonormal polynomial family with the stated integrability, the weighted squared energy of each finite component expansion equals its squared coefficient sum. [`poly_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L82).

**Theorem · Evaluate Fourier expansion energy.** For positive mode spacing, angular averaging of the finite trigonometric expansion energy equals the sum of the squared Fourier coefficients. [`trig_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L99).

**Theorem · Recover input coefficient energies.** The radial and height input energies are angularly integrable and their normalized angular integrals equal the corresponding finite squared coefficient sums. [`inputEnergy_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L120).

### Breakdown.FracCell.MeshTailFinite

Closes the finite tail estimate by combining coefficient interchange with the angular tail bound. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Bound every finite output tail.** For positive mode spacing and regular bounded tail families, every finite weighted output coefficient tail is bounded by the input majorant. [`tailFinite_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailFinite.lean#L17).

### Breakdown.FracCell.MeshTailHeight

Controls the part of the polynomial tail whose height index exceeds the cutoff. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Bound radial projection energy.** For a bounded measurable cell field and a fixed height polynomial, finite squared cell coefficients are bounded by the integrable radial energy of the height projection. [`coef_sq_sum_le_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailHeight.lean#L18).

**Theorem · Bound a height tail on one radius.** At an interior radius with measurable multiplier sections, the weighted height-index tail of the angular field is bounded by the prescribed height constants and input energy. [`height_point`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailHeight.lean#L111).

**Theorem · Control the height-index tail.** The weighted finite coefficient tail above the height cutoff is bounded by the radial integral of the height-input majorant under the stated tail hypotheses. [`heightBranch_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailHeight.lean#L232).

### Breakdown.FracCell.MeshTailModes

Applies finite Fourier Bessel bounds to pass from angular energies to output mode coefficients. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Bound selected Fourier coefficients.** For an L² angular function and positive mode spacing, the squared coefficients at any finite mode set sum to at most its normalized angular energy. [`modeSquareSum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L17).

**Theorem · Convert angular bounds to mode tails.** The coefficient-interchange and angular-tail propositions imply the finite output coefficient-tail proposition. [`tailFinite_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53).

### Breakdown.FracCell.MeshTailRadial

Controls the part of the polynomial tail whose radial index exceeds the cutoff. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Bound height projection energy.** For a bounded measurable cell field and a fixed radial polynomial, finite squared cell coefficients are bounded by the integrable height energy of the weighted radial projection. [`coef_sq_sum_le_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailRadial.lean#L18).

**Theorem · Bound a radial tail on one height.** At an interior height with measurable multiplier sections, the weighted radial-index tail of the angular field is bounded by the prescribed radial constants and input energy. [`radial_point`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailRadial.lean#L115).

**Theorem · Control the radial-index tail.** The weighted finite coefficient tail above the radial cutoff is bounded by the height integral of the radial-input majorant under the stated tail hypotheses. [`radialBranch_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailRadial.lean#L242).

### Breakdown.FracCell.MeshTailSlice

Splits a two-index polynomial tail into radial and height branches at each angle. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Split a two-index tail.** A nonnegative sum outside the square cutoff is bounded by the sum of its radial and height tails over the rectangular index hull. [`far_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L18).

**Theorem · Combine the two tail branches.** The radial-branch and height-branch propositions imply the angular-slice tail estimate. [`angleSlice_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41).

**Theorem · Bound the tail at a fixed angle.** At each angle with measurable multiplier sections, the weighted finite polynomial tail is bounded by the radial and height input-energy majorants. [`angleSlice_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L50).

### Breakdown.FracCell.MeshTailSquares

Supplies finite weighted Bessel and Cauchy–Schwarz estimates used in tail bounds. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Weighted finite Bessel inequality.** For a nonnegative weight and a finite orthonormal real family, the squared complex projection coefficients sum to at most the weighted field energy under the stated integrability assumptions. [`proj_sq_sum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSquares.lean#L17).

**Theorem · Finite Cauchy–Schwarz inequality.** The sum of products of two finite real families is bounded by the product of their Euclidean norms. [`sum_mul_le_sqrt_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSquares.lean#L103).

**Theorem · Reorder four finite sums.** Four finite sums may be reordered to place the two component indices before the two spatial indices. [`swap4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSquares.lean#L108).

**Theorem · Combine weighted component bounds.** Nonnegative component bounds of the form δ²U imply that the weighted energy of their sum is at most the sum of δ times the sum of δU. [`weighted_sum_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSquares.lean#L119).

### Breakdown.FracCell.MeshTailSt

Defines the angular synthesis and the propositions that divide tail control into projection, slice, and energy steps. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · Synthesize the angular output.** The angular output is the finite sum of each multiplier times its associated input function over input families and components. [`TailFamily.angleField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L15).

**Interface · Finite coefficient-tail proposition.** This proposition requires every finite weighted output coefficient tail beyond the square cutoff to be bounded by the input majorant for regular families satisfying the tail bounds and positive mode spacing. [`TailFiniteStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L19).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.tailFinite_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailFinite.lean#L17) ([lean/Breakdown/FracCell/MeshTailFinite.lean:17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailFinite.lean#L17); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.CellAnalysis.MeshTail.tailFinite_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53) ([lean/Breakdown/FracCell/MeshTailModes.lean:53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53); named premises: `AngleTailStatement`, `CoefModeStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.tailMajorant_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L52) ([lean/Breakdown/FracCell/MeshTail.lean:52](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTail.lean#L52); named reference in type).

**Interface · Fourier projection proposition.** This proposition requires output cell coefficients to equal angular Fourier coefficients of projected angular fields and requires those projected fields to lie in L². [`CoefModeStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L27).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.coefMode_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailCoef.lean#L47) ([lean/Breakdown/FracCell/MeshTailCoef.lean:47](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailCoef.lean#L47); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.MeshTail.tailFinite_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53) ([lean/Breakdown/FracCell/MeshTailModes.lean:53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53); named reference in type).

**Interface · Averaged angular-tail proposition.** This proposition bounds the normalized angular integral of every finite weighted polynomial tail by the input majorant under the regularity and tail-bound hypotheses. [`AngleTailStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L36).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.angleTail_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27) ([lean/Breakdown/FracCell/MeshTailAngle.lean:27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27); named premises: `AngleSliceStatement`, `InputEnergyStatement`); [`Breakdown.CellCert.CellAnalysis.angleTail_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L112) ([lean/Breakdown/FracCell/MeshTailAngle.lean:112](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L112); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.MeshTail.tailFinite_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53) ([lean/Breakdown/FracCell/MeshTailModes.lean:53](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailModes.lean#L53); named reference in type).

**Definition · Synthesize a fixed radial coefficient.** The radial input sums the remaining height polynomials and angular modes while holding the radial polynomial index fixed. [`TailFamily.radialInput`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L44).

**Definition · Synthesize a fixed height coefficient.** The height input sums the remaining radial polynomials and angular modes while holding the height polynomial index fixed. [`TailFamily.heightInput`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L49).

**Interface · Angular-slice tail proposition.** This proposition bounds the finite polynomial tail at each angle by the sum of radial and height input-energy majorants when the multiplier sections are measurable. [`AngleSliceStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L54).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.angleSlice_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41) ([lean/Breakdown/FracCell/MeshTailSlice.lean:41](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41); named premises: `HeightBranchStatement`, `RadialBranchStatement`); [`Breakdown.CellCert.CellAnalysis.angleSlice_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L50) ([lean/Breakdown/FracCell/MeshTailSlice.lean:50](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L50); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.angleTail_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27) ([lean/Breakdown/FracCell/MeshTailAngle.lean:27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27); named reference in type).

**Interface · Input energy proposition.** This proposition asserts integrability of the two angular input energies and identifies their normalized averages with the respective squared coefficient sums for positive mode spacing. [`InputEnergyStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L66).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.inputEnergy_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L120) ([lean/Breakdown/FracCell/MeshTailEnergy.lean:120](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailEnergy.lean#L120); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.angleTail_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27) ([lean/Breakdown/FracCell/MeshTailAngle.lean:27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailAngle.lean#L27); named reference in type).

**Interface · Radial-tail proposition.** This proposition bounds the finite tail with radial index above the cutoff by the radial constants times height-integrated radial-input energies. [`RadialBranchStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L81).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.radialBranch_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailRadial.lean#L242) ([lean/Breakdown/FracCell/MeshTailRadial.lean:242](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailRadial.lean#L242); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.angleSlice_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41) ([lean/Breakdown/FracCell/MeshTailSlice.lean:41](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41); named reference in type).

**Interface · Height-tail proposition.** This proposition bounds the finite tail with height index above the cutoff by the height constants times radially weighted height-input energies. [`HeightBranchStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSt.lean#L91).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.heightBranch_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailHeight.lean#L232) ([lean/Breakdown/FracCell/MeshTailHeight.lean:232](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailHeight.lean#L232); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.angleSlice_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41) ([lean/Breakdown/FracCell/MeshTailSlice.lean:41](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/MeshTailSlice.lean#L41); named reference in type).

### Breakdown.FracCell.ModeGradSquare

Transfers global square-integrability of a gradient field to weighted cell integrability of its cylindrical Fourier modes. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Angular integral Cauchy–Schwarz.** For an almost everywhere measurable complex function, the square of its angular norm integral is bounded by $2π$ times its squared-norm integral. [`lint_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L14).

**Theorem · Bound the angular integral norm.** The squared extended norm of a complex angular integral is bounded by $2π$ times the integral of the squared extended norm. [`int_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L31).

**Theorem · Place the cell in the radial half-plane.** For a valid cell, its restricted planar measure is dominated by the measure on positive radii and arbitrary heights. [`hle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L38).

**Theorem · Measurability after angular averaging.** A continuous scalar transform of an almost everywhere measurable spatial field remains almost everywhere strongly measurable after cylindrical angular integration on positive radii. [`meas_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L47).

**Theorem · Measurability of a gradient mode.** Each cylindrical gradient-mode component is almost everywhere strongly measurable on a valid cell when the underlying gradient field is measurable. [`gm_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L57).

**Theorem · Weighted energy of a gradient mode.** Global integrability of the gradient entry squares implies weighted square-integrability of each cylindrical gradient-mode component on a valid cell. [`gm_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L67).

**Theorem · Establish gradient-mode L² control.** Every gradient-mode component of a second-order field is measurable and has integrable squared norm with the cell line weight. [`modeGradSquare`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeGradSquare.lean#L149).

### Breakdown.FracCell.ModeHeightAxis

Combines mollification, Sobolev control, and cylindrical integration to obtain integrability of axial gradient modes up to the radial axis. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Convexity under mollification.** For integer power at least one and an integrable dominating function, the power of the mollified vector norm is bounded by the mollification of the norm power. [`normPow_conv_le_of_dom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L17).

**Theorem · Integrate a finite nonnegative bound.** A finite family of nonnegative functions whose pointwise sum is bounded by an integrable function has summed integrals bounded by that function's integral. [`sum_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L77).

**Theorem · Mollify a column-energy bound.** A pointwise integrable bound on the sum of three column norm squares remains a bound after convolution with a normalized bump. [`conv_sum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L92).

**Theorem · Differentiate a weakly smoothened field.** Convolution of a locally integrable vector field with a normalized bump has coordinate derivatives equal to the convolutions of its specified weak derivative columns. [`mollify_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L106).

**Theorem · Characterize vector L⁶ membership.** For a measurable vector field, membership in L⁶ is equivalent to integrability of the sixth power of its norm. [`memLp_six_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L138).

**Theorem · Control the cutoff derivative error.** A cutoff derivative bounded by K/R gives an L² product bound in terms of the field's exterior L⁶ norm, with the stated dimension-three ball-volume constant. [`cross_tail_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L144).

**Theorem · Vanishing exterior L⁶ tails.** The L⁶ norm of an L⁶ vector field restricted outside balls of radii n plus one tends to zero. [`tail_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L203).

**Theorem · Sobolev control for smooth L⁶ fields.** A smooth L⁶ vector field has L⁶ norm bounded by the stated Sobolev constant times the L² norm of its derivative. [`smooth_six_of_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L234).

**Theorem · Sobolev bound from weak columns.** A compactly supported L² vector field with weak derivative columns dominated in squared sum by an integrable energy has the stated L⁶ bound using three times the square root of that energy integral. [`six_bound_of_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L298).

**Theorem · Ignore the zero-radius boundary.** The measure on a closed finite radial-height rectangle is dominated by the measure on the positive-radius half-plane. [`half_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L378).

**Theorem · Measurability of cylindrical averages.** A continuous scalar transform of a measurable spatial field has a measurable angular average on the positive-radius half-plane. [`kmeas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L387).

**Theorem · Cylindrical integration formula.** For a measurable extended nonnegative spatial function, its global integral equals angular integration over the radial-height half-plane with radial Jacobian. [`half_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L397).

**Theorem · Integrability with the radial Jacobian.** A locally integrable spatial field gives an integrable radially weighted angular average on each finite axis-touching rectangle when the scalar transform is continuous and norm bounded. [`weighted_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L408).

**Theorem · Absorb a linear term into sixth power.** For positive r, every real t satisfies $t≤r^{-1/5}+rt^6$. [`root_power_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L455).

**Theorem · Dominate the angular kernel near zero.** For a norm-bounded scalar transform and positive radius r, its extended norm is at most $r^{-1/5}$ plus r times the sixth power of the vector norm. [`pt_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L475).

**Theorem · Unweighted integrability near the axis.** An L⁶ velocity field has integrable unweighted angular averages on every finite axis-touching rectangle for continuous norm-bounded scalar transforms. [`vel_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L484).

**Theorem · Identify the axial basis vector.** The axial unit vector is the third Cartesian coordinate vector. [`axial_eq_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L549).

**Theorem · L² control of each gradient column.** Measurability and integrable gradient entry squares imply that every Cartesian gradient column lies in L². [`col_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L551).

**Theorem · L² control of each second derivative.** A measurable second derivative field with integrable summed column norm squares has each Cartesian second derivative column in L². [`second_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L562).

**Theorem · Bound a test function derivative.** The derivative norm of a smooth compactly supported scalar test function has a nonnegative global bound. [`test_bounded`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L575).

**Theorem · Differentiate a localized axial column.** For a second-order field, multiplying its axial gradient column by a scalar test function gives the stated weak product rule involving the second derivative. [`cut_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L580).

**Theorem · L⁶ control of the axial column.** A scalar test cutoff of magnitude at most one makes the axial gradient column of a second-order field an L⁶ vector field. [`cut_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L627).

**Theorem · Reduce the axial gradient kernel.** The gradient kernel with axial input equals the velocity kernel applied to the axial column of the linear map. [`kernel_axial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L664).

**Theorem · Integrate axial modes through the axis.** For a second-order field, every axial gradient-mode component is integrable on each finite radial-height rectangle starting at radius zero. [`modeHeightAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightAxis.lean#L678).

### Breakdown.FracCell.ModeHeightLine

Represents radial polynomial projections by an invertible moment matrix and obtains continuous height primitives from weak height identities. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Weighted radial monomial moments.** At a fixed height, the moment vector integrates the field against each conjugate radial monomial using the cell line weight. [`moments`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L14).

**Definition · Weighted monomial Gram matrix.** The moment matrix integrates each pair of radial monomials against the cell line weight. [`momentMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L17).

**Theorem · Continuity of the radial weight.** The cell line weight is continuous on the real line. [`weight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L20).

**Theorem · Nonnegative cell line weight.** The line weight is nonnegative throughout the radial interval of a valid cell. [`weight_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L24).

**Theorem · Positive interior line weight.** The line weight is strictly positive inside the radial interval of a valid cell. [`weight_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L31).

**Theorem · Bound the cell line weight.** On the radial interval of a valid cell, the line weight is at most the upper radius plus one. [`weight_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L38).

**Theorem · Polynomial uniqueness on infinite sets.** If a finite complex polynomial vanishes at every point of an infinite real set, all its coefficients vanish. [`poly_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L45).

**Theorem · Translate projection into moments.** For an integrable weighted radial slice, the monomial orthogonality conditions for a polynomial are equivalent to its coefficients solving the moment-matrix system. [`cond_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L72).

**Theorem · Injectivity of the moment matrix.** For a valid cell, multiplication by the weighted radial monomial Gram matrix is injective. [`momentMatrix_inj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L111).

**Theorem · Invertibility of the moment matrix.** The weighted radial monomial Gram matrix of a valid cell is a unit in the matrix ring. [`momentMatrix_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L179).

**Theorem · Solve the radial moment system.** Multiplying the moment vector by the inverse Gram matrix gives a solution of the radial moment system for a valid cell. [`momentMatrix_inv_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L182).

**Theorem · Explicit radial projection formula.** For an integrable weighted slice, radial projection equals the polynomial whose coefficients are the inverse moment matrix applied to the slice moments. [`projR_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L187).

**Theorem · Product measure for a cell.** The measure restricted to the cell rectangle equals the product of its restricted radial and height measures. [`rect_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L209).

**Theorem · Exchange primitive integration order.** For an integrable complex function and continuous multiplier, integrating the initial-point primitive equals integrating the function against the multiplier's terminal-point primitive. [`primitive_ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L213).

**Theorem · Pair a primitive with a derivative.** For a C¹ real test vanishing at the upper endpoint, integration of a complex primitive against its derivative equals minus the original function paired with the test. [`primitive_ibp_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L262).

**Theorem · Recover a weak primitive.** An integrable function with the stated weak derivative identity agrees almost everywhere with a constant plus the integral of that derivative. [`eq_const_add_primitive`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L273).

**Theorem · Integrability of radial moments.** An integrable cell function has integrable height-dependent radial monomial moments and integrable radial slices at almost every height. [`slice_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L360).

**Theorem · Separate radial moments and height tests.** A cell integral against a radial monomial times a continuous height function equals the height integral of the radial moment times that function. [`rect_integral_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L372).

**Theorem · Interval integral Cauchy–Schwarz.** The squared norm of an integrable complex interval integral is bounded by the interval length times its integrable squared-norm integral. [`sq_norm_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L389).

**Theorem · Bound a radial monomial moment.** The squared weighted radial monomial moment is bounded by $(r₂-r₁)(r₂+1)r₂^{2t}$ times the weighted slice energy under the stated integrability assumptions. [`moment_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L413).

**Theorem · Construct a projected height primitive.** The weighted weak height identity and L² derivative control give a continuous height representative of the radial projection, with projected derivative, almost everywhere agreement, and square-integrability. [`line_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L464).

**Theorem · Build the velocity height representative.** Height-mode integration by parts and the gradient- and velocity-mode square bounds imply continuous height representatives for radial projections of velocity modes with the prescribed projected axial derivatives. [`modeHeightLine_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightLine.lean#L601).

### Breakdown.FracCell.ModeHeightParts

Lifts weak second derivatives through cylindrical matrix kernels and proves cellwise height integration by parts. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Extend the cylindrical frame.** The auxiliary frame uses planar coordinates q to define radial and tangential vectors together with the fixed axial unit vector. [`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L17).

**Theorem · Recover the angular frame.** Evaluating the auxiliary frame at cosine and sine gives the cylindrical orthonormal frame. [`unitAt_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L21).

**Definition · Extend frame component extraction.** The auxiliary row map forms the real linear functional with coefficients given by the chosen auxiliary frame vector. [`rowQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L23).

**Theorem · Extract a cylindrical vector component.** On the unit circle, the auxiliary row map equals the inner product with the corresponding cylindrical frame vector. [`rowQ_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L26).

**Theorem · Smooth auxiliary frame coordinates.** Every Cartesian coordinate of each auxiliary frame vector is smooth in the planar parameters. [`unitAt_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L30).

**Theorem · Smooth auxiliary frame vectors.** Each auxiliary frame vector is a smooth function of the planar parameters. [`unitAt_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L35).

**Theorem · Smooth frame component functionals.** The auxiliary row functional depends smoothly on the planar parameters. [`rowQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L38).

**Definition · Extend matrix entry extraction.** The auxiliary matrix-entry functional applies a linear map to an auxiliary frame vector and extracts its component along another such vector. [`entQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L42).

**Theorem · Smooth matrix entry functionals.** Each auxiliary matrix-entry functional depends smoothly on the planar parameters. [`entQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L45).

**Theorem · Recover a cylindrical matrix entry.** On the unit circle, the auxiliary entry functional equals the corresponding cylindrical-frame matrix coefficient. [`entQ_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L48).

**Theorem · Expand in Cartesian unit vectors.** Every spatial vector equals the sum of its Cartesian coordinates times the corresponding unit vectors. [`vec_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L53).

**Theorem · Recover operator L² membership.** A measurable linear-map field with integrable summed entry squares belongs to L² in the operator norm. [`memLp_of_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L56).

**Theorem · Energy of a second derivative column.** Integrability of all Cartesian second derivative norm squares implies integrability of the entry-square energy of each fixed first-index column. [`col_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L63).

**Theorem · Lift weak derivatives to operator values.** The componentwise weak second derivative identity becomes an equality of integrals valued in continuous linear maps under the stated local integrability assumptions. [`weak_clm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L75).

**Theorem · Scale a weak complex identity.** Multiplying both fields in the given complex integral identity by the same complex constant preserves that identity. [`scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L95).

**Theorem · Weak height derivative of gradient modes.** For smooth compactly supported tests away from the axis, the weak height derivative of a gradient-mode component is the corresponding mode of the axial second derivative. [`weak_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L101).

**Theorem · Smooth interval comparison tests.** Each localized interval comparison test is smooth. [`test_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L122).

**Theorem · Smoothness of the line weight.** The cell line weight is smooth on the real line. [`weight_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L131).

**Theorem · Product measure for a cell.** The measure on the cell rectangle equals the product of its restricted radial and height measures. [`rect_eq'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L138).

**Theorem · Multiply by a continuous cell factor.** Multiplying an integrable cell function by a continuous complex function preserves integrability on the cell rectangle. [`bdd_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L142).

**Theorem · Continuity of a height derivative.** The height derivative of a C¹ complex planar function is continuous. [`hd_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L149).

**Theorem · Integrate an almost everywhere primitive.** A function agreeing almost everywhere with a terminal-point primitive satisfies integration by parts against C¹ complex tests vanishing at both endpoints. [`ibp_line`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L159).

**Theorem · Localize the weak identity to slices.** The planar weak height identity implies a vanishing weighted test integral on almost every interior radial slice for the specified localized height tests. [`line_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L193).

**Theorem · Extend weak height integration by parts.** Weighted integrability and the weak height identity imply the cell integration-by-parts formula for every C¹ complex test vanishing on both height faces. [`parts_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L302).

**Theorem · Integrate a matrix component combination.** A finite complex linear combination of integrable matrix-component fields may be moved outside the cell integral. [`sum_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L378).

**Theorem · Integrate gradient modes by height.** For a second-order field and a C¹ test vanishing on both height faces, the weighted second-derivative mode pairing equals minus the gradient-mode pairing with the test's height derivative. [`modeHeightParts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeHeightParts.lean#L392).

### Breakdown.FracCell.ModeOrthSame

Proves orthogonality of distinct azimuthal frequencies using spatial rotations and cylindrical frame expansions. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Rotation about the vertical axis.** The linear map rotates the first two Cartesian coordinates through the given angle and fixes the third coordinate. [`rotLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L17).

**Theorem · Rotations preserve inner products.** The planar spatial rotation preserves the Euclidean inner product. [`rotLin_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L26).

**Definition · Rotation as an isometric equivalence.** The spatial rotation is packaged as a real linear isometric equivalence. [`rot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L31).

**Theorem · First coordinate after rotation.** The first rotated coordinate is cosine times the original first coordinate minus sine times the second. [`rot0`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L34).

**Theorem · Second coordinate after rotation.** The second rotated coordinate is sine times the original first coordinate plus cosine times the second. [`rot1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L36).

**Theorem · Height is unchanged by rotation.** The third Cartesian coordinate is fixed by rotation about the vertical axis. [`rot2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L38).

**Theorem · Radius is unchanged by rotation.** Rotation about the vertical axis preserves the cylindrical radial coordinate. [`radial_rot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L40).

**Theorem · Rotation preserves cell solids.** A point belongs to a reflected cell solid exactly when its rotated image belongs to that solid. [`mem_cellSolid_rot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L45).

**Theorem · Angular coordinates modulo a turn.** Away from the axis, rotation adds its angle to the cylindrical angular coordinate up to an integer multiple of $2π$. [`angle_rot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L49).

**Theorem · Ignore complete angular turns.** An integer multiple of a full angular turn does not change a sine or cosine mode of natural-number frequency. [`trig_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L95).

**Theorem · Separate sum and difference frequencies.** A product of two real trigonometric modes decomposes into sum- and difference-frequency functions that change sign under a shift by π. [`trig_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L106).

**Theorem · Cancel four shifted mode products.** Four evaluations at the two specified half-period shifts sum to zero for the two antiperiodic frequency functions. [`four_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L135).

**Theorem · The rotation axis has zero volume.** The set where both horizontal Cartesian coordinates vanish has zero three-dimensional volume. [`axis_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L146).

**Theorem · Cancel distinct angular frequencies.** A finite trigonometric expansion with distinct frequencies and rotation-invariant coefficients has zero spatial integral. [`integral_eq_zero_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L156).

**Reader note.** The conclusion is an equality for Lean’s total Bochner integral; this declaration has no separate integrability premise.

**Theorem · Orthonormality of the local frame.** The cylindrical frame vectors have inner product one for equal indices and zero for distinct indices. [`frame_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L200).

**Theorem · Expand a mode field in its frame.** A mode field admits a cylindrical-frame expansion whose scalar coefficients are sums of its two trigonometric modes with rotation-invariant amplitudes. [`field_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L206).

**Theorem · Pair cylindrical vector expansions.** The inner product of two cylindrical-frame expansions is the sum of products of their scalar frame coefficients. [`inner_frame_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L226).

**Theorem · Orthogonality of distinct mode fields.** Mode fields with different azimuthal frequencies have zero integrated Euclidean inner product. [`field_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L231).

**Theorem · Expand a mode gradient in its frame.** A mode gradient admits an expansion in cylindrical rank-one frame operators with trigonometric coefficients and rotation-invariant amplitudes. [`grad_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L243).

**Theorem · Resolve a vector inner product.** Summing products of Cartesian unit-vector components recovers the Euclidean inner product. [`coord_inner_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L265).

**Theorem · Pair two rank-one operators.** The entry inner product of two rank-one operators is the product of the corresponding input-vector and output-vector inner products. [`entryInner_basic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L269).

**Theorem · Expand a bilinear operator pairing.** The entry inner product of two finite real linear combinations expands into the double sum of coefficient products times entry inner products. [`entryInner_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L277).

**Theorem · Orthonormality of frame operators.** Cylindrical rank-one frame operators have entry inner product one for equal index pairs and zero otherwise. [`entryInner_frames`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L288).

**Theorem · Orthogonality of distinct mode gradients.** Mode gradients with different azimuthal frequencies have zero integrated entry inner product. [`grad_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L296).

**Theorem · Separate frequencies on one cell.** For blocks with matching cell geometry and distinct frequencies, their L² mode fields and square-integrable mode gradients are orthogonal. [`modeOrthSame_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeOrthSame.lean#L312).

### Breakdown.FracCell.ModeRadialLine

Builds shrinking smooth interval tests and recovers almost everywhere radial primitives from weak mode identities. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Choose a shrinking smooth bump.** The bump centered at zero has inner radius $1/(k+4)$ and outer radius $2/(k+4)$. [`bumpAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L16).

**Definition · Support radius of the bump.** The test width is $2/(k+4)$. [`width`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L23).

**Definition · Normalized smoothing kernel.** The kernel is the chosen bump normalized to have unit integral with respect to Lebesgue measure. [`kern`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L25).

**Definition · Smooth cumulative step.** The smooth step integrates the normalized kernel from minus one to the supplied point. [`step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L27).

**Definition · Localized interval comparison test.** The test is the difference of two translated smooth steps based at the two comparison points. [`test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L29).

**Lemma · Positive test width.** Each test width is strictly positive. [`width_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L31).

**Lemma · Uniform bound on the test width.** Every test width is at most one half. [`width_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L33).

**Lemma · Shrinking test widths.** The test widths tend to zero as their natural-number index tends to infinity. [`width_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L39).

**Lemma · Fit the bump within any margin.** For every positive margin, all sufficiently large indices have test width smaller than that margin. [`width_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L44).

**Lemma · Nonnegative smoothing kernel.** The normalized kernel is nonnegative at every point. [`kern_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L47).

**Lemma · Continuity of the smoothing kernel.** Each normalized smoothing kernel is continuous. [`kern_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L49).

**Lemma · Integrability of the kernel.** Each normalized smoothing kernel is integrable on the real line. [`kern_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L51).

**Lemma · Unit kernel mass.** The integral of each normalized smoothing kernel is one. [`kern_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L53).

**Lemma · Kernel vanishes outside its width.** The smoothing kernel is zero wherever the absolute coordinate is at least its width. [`kern_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L55).

**Lemma · Bound the smoothing kernel.** Each normalized smoothing kernel has a global absolute-value bound. [`kern_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L63).

**Lemma · Derivative of the cumulative step.** The cumulative step has derivative equal to the normalized kernel at every point. [`step_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L68).

**Lemma · Continuity of the cumulative step.** Each cumulative step is continuous. [`step_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L71).

**Lemma · The step vanishes before its support.** The cumulative step is zero at points no greater than minus its width. [`step_low`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L74).

**Lemma · The step reaches one after support.** The cumulative step equals one at points at least its width. [`step_high`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L87).

**Lemma · Nonnegative cumulative step.** The cumulative step is nonnegative everywhere. [`step_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L100).

**Lemma · The cumulative step is at most one.** The cumulative step is bounded above by one everywhere. [`step_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L105).

**Lemma · Absolute bound on the step.** The absolute value of the cumulative step is at most one. [`abs_step_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L111).

**Lemma · Derivative of an interval test.** The localized interval test has derivative equal to the difference of the two translated kernels. [`test_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L114).

**Lemma · Formula for the interval-test derivative.** The derivative of the interval comparison test is the kernel at the first translated point minus the kernel at the second. [`test_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L120).

**Lemma · Continuous interval-test derivative.** The derivative of each interval comparison test is continuous. [`test_deriv_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L123).

**Lemma · C¹ regularity of interval tests.** Each interval comparison test is continuously differentiable. [`test_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L129).

**Lemma · Continuity of interval tests.** Each interval comparison test is continuous. [`test_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L132).

**Lemma · Bound the interval-test derivative.** The derivative of each interval comparison test has a global absolute-value bound. [`test_deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L136).

**Lemma · Absolute bound on interval tests.** The absolute value of every interval comparison test is at most two. [`abs_test_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L144).

**Lemma · A fixed point is negligible.** Lebesgue almost every real number differs from any prescribed point. [`ae_ne_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L151).

**Lemma · Multiply by a translated kernel.** Multiplying an interval-integrable complex function by a translated smoothing kernel preserves interval integrability. [`integrable_kern_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L155).

**Lemma · Remove a possible left-end singularity.** A translated smooth step supported away from the left endpoint makes a function integrable on the full interval when it is integrable on every right subinterval. [`integrable_step_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L165).

**Definition · Combine smoothed value and derivative.** The averaged value integrates the kernel-weighted original function plus the step-weighted derivative candidate over the interval. [`avgVal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L185).

**Lemma · Continuity of the averaged value.** The averaged value depends continuously on an interior base point when the original function is integrable and the derivative candidate is integrable on right subintervals. [`avgVal_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L188).

**Lemma · Smooth steps select terminal integrals.** At an interior base point, step-weighted integrals converge to the derivative candidate's integral from that point to the right endpoint. [`step_limit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L228).

**Lemma · Recover values by shrinking kernels.** Kernel averages of an interval-integrable function converge almost everywhere to that function extended by zero outside the interval. [`kern_density`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L275).

**Lemma · Recover a radial primitive.** The countable family of localized weak test identities gives a constant whose terminal-point primitive agrees almost everywhere with the original function. [`line_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L298).

**Lemma · Product measure on a rectangle.** The restricted measure on a closed rectangle is the product of the two restricted interval measures. [`rect_measure`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L370).

**Lemma · Almost everywhere integrable slices.** An integrable function on a rectangle has integrable radial slices at almost every height. [`slice_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L375).

**Lemma · Localize vanishing integrals to slices.** If an integrable rectangular field pairs to zero with every continuous height test, its radial integral vanishes at almost every height. [`slice_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L381).

**Lemma · Measurability of the line weight.** The cell line weight is measurable. [`lw_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L407).

**Lemma · A lower bound away from the axis.** At radii at least x′, the cell line weight is at least the minimum of x′ and one. [`lw_ge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L414).

**Lemma · The line weight is nonzero off axis.** At every nonzero radius, the cell line weight is nonzero. [`lw_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L419).

**Lemma · The interval test vanishes on the left.** The interval comparison test vanishes at points lying before both translated kernel supports. [`test_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L424).

**Lemma · The interval test vanishes on the right.** The interval comparison test vanishes at points lying after both translated kernel supports. [`test_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L430).

**Lemma · Integrability of the radial weak test.** An integrable mode and a line-weight-integrable derivative candidate give an integrable radial weak-test expression when both translated tests stay away from the left face. [`integrable_weak_integrand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L436).

**Theorem · Build radial velocity representatives.** The weak radial identity and the gradient- and velocity-mode square bounds yield continuous radial representatives on almost every height slice, with the prescribed gradient-mode derivative and weighted L² bounds. [`modeRadialLine_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L487).

### Breakdown.FracCell.ModeRadialPartsA

Proves radial integration by parts for gradient-mode combinations using weak second derivatives, smoothing, and boundary cutoffs. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Extend the cylindrical frame.** The auxiliary frame uses planar coordinates q to define radial and tangential vectors together with the fixed axial unit vector. [`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L15).

**Theorem · Recover the angular frame.** Evaluating the auxiliary frame at cosine and sine gives the cylindrical orthonormal frame. [`unitAt_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L19).

**Definition · Extend frame component extraction.** The auxiliary row map forms the real linear functional with coefficients given by the chosen auxiliary frame vector. [`rowQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L21).

**Theorem · Extract a cylindrical vector component.** On the unit circle, the auxiliary row map equals the inner product with the corresponding cylindrical frame vector. [`rowQ_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L24).

**Theorem · Smooth auxiliary frame coordinates.** Every Cartesian coordinate of each auxiliary frame vector is smooth in the planar parameters. [`unitAt_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L28).

**Theorem · Smooth auxiliary frame vectors.** Each auxiliary frame vector is a smooth function of the planar parameters. [`unitAt_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L33).

**Theorem · Smooth frame component functionals.** The auxiliary row functional depends smoothly on the planar parameters. [`rowQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L36).

**Definition · Extend matrix entry extraction.** The auxiliary matrix-entry functional applies a linear map to an auxiliary frame vector and extracts its component along another such vector. [`entryQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L40).

**Theorem · Smooth matrix entry functionals.** Each auxiliary matrix-entry functional depends smoothly on the planar parameters. [`entryQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L43).

**Theorem · Recover a cylindrical matrix entry.** On the unit circle, the auxiliary entry functional equals the corresponding cylindrical-frame matrix coefficient. [`entryQ_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L46).

**Theorem · Expand in Cartesian unit vectors.** Every spatial vector equals the sum of its Cartesian coordinates times the corresponding unit vectors. [`vec_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L51).

**Theorem · Bound an operator by its columns.** The operator norm of a linear map from three-dimensional space is at most the sum of the norms of its Cartesian columns. [`norm_le_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L54).

**Theorem · Local integrability of the norm.** The norm of a locally integrable field is locally integrable. [`loc_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L63).

**Theorem · Local integrability from columns.** A measurable operator field is locally integrable if each of its Cartesian columns is locally integrable. [`loc_of_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L67).

**Theorem · Square-integrability of gradient columns.** Each Cartesian column of a measurable gradient field with integrable entry squares lies in L². [`memLp_col`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L77).

**Theorem · Square-integrability of second columns.** Each Cartesian two-index column of a measurable second derivative field lies in L² when the summed column norm squares are integrable. [`memLp_col2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L86).

**Theorem · Local integrability of the gradient.** The gradient field in a second-order field is locally integrable as an operator-valued function. [`locG`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L100).

**Theorem · Local integrability of second columns.** Each first-index Cartesian column of the second derivative field is locally integrable as an operator-valued function. [`locHc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L106).

**Theorem · Local integrability of the Hessian field.** The second derivative in a second-order field is locally integrable as a bilinear-map-valued function. [`locH`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L112).

**Theorem · Weak derivative of the gradient field.** For a second-order field, testing a coordinate derivative against the operator-valued gradient yields minus the test paired with the corresponding second derivative column. [`weakG`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L117).

**Theorem · Scale a weak complex identity.** Multiplying both fields in the given complex integral identity by the same complex constant preserves that identity. [`scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L137).

**Theorem · Weak radial derivative of gradient modes.** For smooth compactly supported planar tests away from the axis, the radial weak derivative of a gradient-mode component is the corresponding radial second-derivative mode. [`weak_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L143).

**Theorem · Integral formula for a radial derivative.** The radial second-derivative mode is the normalized angular integral of the gradient kernel applied to the second derivative's radial column. [`third_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L164).

**Theorem · Weighted integrability of radial modes.** For a second-order field, each radial second-derivative mode is integrable on the cell after multiplication by the cell line weight. [`third_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L175).

**Theorem · Weighted integrability of gradient modes.** Each gradient-mode component of a second-order field is integrable on the cell after multiplication by the line weight. [`grad_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L193).

**Theorem · Transition derivative off its interval.** The derivative of the smooth transition function vanishes strictly outside the unit interval. [`st_deriv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L204).

**Theorem · Bound the transition derivative.** The derivative of the smooth transition function has a nonnegative global absolute-value bound. [`st_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L213).

**Definition · Cut off both radial boundaries.** The radial cutoff multiplies two smooth transition factors that suppress neighborhoods of the left and right endpoints. [`cutR`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L227).

**Theorem · Nonnegative radial cutoff.** The two-sided radial cutoff is nonnegative everywhere. [`cutR_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L229).

**Theorem · The radial cutoff is at most one.** The two-sided radial cutoff is bounded above by one. [`cutR_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L232).

**Theorem · C¹ regularity of the radial cutoff.** The radial cutoff is continuously differentiable for every choice of its parameters. [`cutR_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L235).

**Theorem · Zero cutoff near radial boundaries.** For positive cutoff width, the radial cutoff vanishes within that width of either endpoint and outside those boundaries. [`cutR_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L239).

**Theorem · Unit cutoff in the radial interior.** For positive cutoff width, the radial cutoff equals one at points at least twice that width from both endpoints. [`cutR_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L245).

**Theorem · Remove the cutoff at interior points.** At a fixed interior point, sufficiently small positive cutoff widths give cutoff value one and derivative zero. [`cutR_eventually`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L251).

**Theorem · Differentiate the radial cutoff.** The radial cutoff has the explicit derivative obtained by the product and chain rules for its two smooth transition factors. [`cutR_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L266).

**Theorem · Control a cutoff derivative product.** If a factor vanishes at least linearly toward both endpoints, its product with the radial cutoff derivative is uniformly bounded by $4SM$. [`cutR_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L278).

**Theorem · Derivative of the line weight.** The cell line weight has derivative one for an axis-touching cell and zero otherwise. [`lw_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L323).

**Theorem · C¹ regularity of the line weight.** The cell line weight is continuously differentiable. [`lw_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L329).

**Theorem · Nonnegative weight above the lower face.** For a valid cell, the line weight is nonnegative at every radius at least the lower radius. [`lw_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L335).

**Theorem · Differentiate a radial slice.** The radial slice of a C¹ planar function has derivative equal to its Fréchet derivative applied to the radial coordinate direction. [`line_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L341).

**Theorem · Pass weak identities to boundary tests.** Measurable weighted-integrable fields satisfying the compact-interior radial weak identity obey integration by parts for every real C¹ test vanishing on both radial faces, with an integrable weighted-test derivative term. [`extend_c1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L346).

**Theorem · Bound a compactly supported test.** A continuous compactly supported real planar function has a nonnegative global absolute-value bound. [`bound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L542).

**Theorem · Bound a normalized convolution.** Convolution with a normalized planar bump has absolute value at most three times a global bound for the continuous real input. [`conv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L551).

**Theorem · Extend smooth weak tests to C¹ tests.** Weighted integrability on every valid cell extends the smooth radial weak identity to C¹ compactly supported tests inside a cell. [`c1_of_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L566).

**Theorem · Measurability of radial derivative modes.** The radial second-derivative modes of a second-order field are almost everywhere strongly measurable on a valid cell. [`third_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L706).

**Theorem · Differentiability of the line weight.** The cell line weight is differentiable on the real line. [`lw_diff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L718).

**Theorem · Separate complex weighted derivatives.** The radial derivative of a weighted C¹ complex test is the real-part derivative plus i times the imaginary-part derivative. [`split_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L720).

**Theorem · Real-test radial integration by parts.** For a second-order field and a real C¹ test vanishing on both radial faces, the weighted radial second-derivative pairing equals minus the gradient-mode pairing with the weighted-test derivative, which is integrable. [`real_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L739).

**Theorem · Componentwise radial parts identity.** For a complex C¹ test vanishing on both radial faces, both componentwise pairings are integrable and the weighted radial second-derivative pairing equals minus the gradient-mode weighted-test derivative pairing. [`ab_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L752).

**Theorem · Integrate gradient modes radially.** For second-order fields, every complex linear combination of gradient components satisfies weighted radial integration by parts against C¹ tests vanishing on both radial faces. [`modeRadialParts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsA.lean#L797).
<!-- /passage:front -->

