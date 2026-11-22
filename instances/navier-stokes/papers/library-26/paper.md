
<!-- passage:front -->
# Library guide 26: Breakdown/Torus

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) **26** [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Torus.Advection` to `Breakdown.Torus.KernelBound` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Torus.Advection

Identifies the Fourier coefficients of smooth periodic self-advection with the convolution used in the periodic mild equation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Advection.Internal.

**Compactness of unit cell.** Unit cell is compact, as asserted by `IsCompact cell`. Source: Breakdown.Periodic.Advection.Internal.isCompact_cell in Breakdown.Torus.Advection, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L12).

**Formula for complexification.** Complexification obeys the exact identity `complexify x i = ((x i : ℝ) : ℂ)`. Source: Breakdown.Periodic.Advection.Internal.complexify_apply in Breakdown.Torus.Advection, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L20).

**Continuity of complexification.** Complexification is continuous on the domain specified by `Continuous complexify`. Source: Breakdown.Periodic.Advection.Internal.continuous_complexify in Breakdown.Torus.Advection, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L22).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character k)`. Source: Breakdown.Periodic.Advection.Internal.continuous_character in Breakdown.Torus.Advection, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L26).

**Norm identity for Fourier character.** Fourier character has the norm identity `‖character k x‖ = 1`. Source: Breakdown.Periodic.Advection.Internal.norm_character in Breakdown.Torus.Advection, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L30).

**Addition formula for lattice frequency.** Lattice frequency obeys the addition identity `freq (a + b) = freq a + freq b`. Source: Breakdown.Periodic.Advection.Internal.freq_add in Breakdown.Torus.Advection, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L38).

**Formula for Fourier character.** Fourier character obeys the exact identity `character a x * character b x = character (a + b) x`. Source: Breakdown.Periodic.Advection.Internal.character_mul in Breakdown.Torus.Advection, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L41).

**Scaling formula for complexification.** Complexification obeys the scalar-scaling identity `complexify (∑ i, a i • v i) = ∑ i, ((a i : ℝ) : ℂ) • complexify (v i)`. Source: Breakdown.Periodic.Advection.Internal.complexify_sum_smul in Breakdown.Torus.Advection, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L48).

**Formula for advection.** Advection obeys the exact identity `advectionAt f x = ∑ i, (f x i) • fderiv ℝ f x (unitVector i)`. Source: Breakdown.Periodic.Advection.Internal.advectionAt_eq in Breakdown.Torus.Advection, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L63).

**Smoothness implies C¹ regularity.** With the stated hypotheses, periodic advection has the asserted differentiability order in `ContDiff ℝ 1 f`. Source: Breakdown.Periodic.Advection.Internal.contDiff_one_of_smooth in Breakdown.Torus.Advection, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L69).

**Continuity of partial derivative.** With the stated hypotheses, partial derivative is continuous on the domain specified by `Continuous (fun x => complexify (fderiv ℝ f x (unitVector i)))`. Source: Breakdown.Periodic.Advection.Internal.continuous_partial in Breakdown.Torus.Advection, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L72).

**Sum of coordinate component.** With the stated hypotheses, coordinate component has the exact series sum in `HasSum (fun j => freqTrCoef f (k - j) i • ((2 * π * Complex.I * ((j i : ℤ) : ℂ)) • freqTrCoef f j)) (∫ x in cell, ((f x i : ℝ) : ℂ) • (character k x • complexify (fderiv ℝ f x (unitVector i))))`. Source: Breakdown.Periodic.Advection.Internal.hasSum_component in Breakdown.Torus.Advection, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L76).

**Source namespace:** Breakdown.Periodic.

**Fourier coefficients of advection.** Under the stated assumptions, smooth periodic divergence-free self-advection has the convolution coefficients used by the periodic bilinear kernel. Source: Breakdown.Periodic.coefAdvection in Breakdown.Torus.Advection, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Advection.lean#L127).

### Breakdown.Torus.ApproxClose

Shows that the rescaled periodic cutoff follows finite test-field approximations in the gradient norm, while its scaled L² mass becomes small.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ApproxClose.Internal.

**Cutoff in similarity coordinates.** The rescaled cutoff evaluates the localized velocity at `center + √μ y` and multiplies its value by `√μ`. Source: Breakdown.Periodic.ApproxClose.Internal.simField in Breakdown.Torus.ApproxClose, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L14).

**Dilated profile slice.** The comparison slice dilates the similarity profile at time `similarityTime T t` by `μ / (T - t)`. Source: Breakdown.Periodic.ApproxClose.Internal.profSlice in Breakdown.Torus.ApproxClose, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L17).

**Smooth periodic solenoidal fields.** A good field is smooth, unit-periodic and divergence-free at every point. Source: Breakdown.Periodic.ApproxClose.Internal.IsGood in Breakdown.Torus.ApproxClose, line 20. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L20).

**Symmetry of gradient error energy.** Gradient energy obeys the symmetry identity `gradEnergy (f - g) = gradEnergy (g - f)`. Source: Breakdown.Periodic.ApproxClose.Internal.gradEnergy_sub_comm in Breakdown.Torus.ApproxClose, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L23).

**Small cutoff error at shrinking scales.** For every positive tolerance the cutoff error has small gradient energy and small scaled L² mass uniformly when λμ ≤ T−t ≤ μ and μ is sufficiently small. Source: Breakdown.Periodic.ApproxClose.Internal.cutoffError in Breakdown.Torus.ApproxClose, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L32).

**Derivative of an affine rescaling.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun y : Space => r • f (a + r • y)) y v = (r * r) • fderiv ℝ f (a + r • y) v`. Source: Breakdown.Periodic.ApproxClose.Internal.fderiv_affine_apply in Breakdown.Torus.ApproxClose, line 105. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L105).

**Formula for divergence.** With the stated hypotheses, divergence obeys the exact identity `divergenceAt (fun y : Space => r • f (a + r • y)) y = (r * r) * divergenceAt f (a + r • y)`. Source: Breakdown.Periodic.ApproxClose.Internal.divergence_affine in Breakdown.Torus.ApproxClose, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L116).

**Derivative of an affine rescaling.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun y : Space => r • f (a + r • y)) y = (r * r) • fderiv ℝ f (a + r • y)`. Source: Breakdown.Periodic.ApproxClose.Internal.fderiv_affine in Breakdown.Torus.ApproxClose, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L124).

**Positive dilation preserves decay.** Positive dilation preserves the decay-field conditions. Source: Breakdown.Periodic.ApproxClose.Internal.dilateDecay in Breakdown.Torus.ApproxClose, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L135).

**Support of a difference.** A field that vanishes whenever ‖y‖ > B has topological support contained in the closed ball of radius B. Source: Breakdown.Periodic.ApproxClose.Internal.tsupport_sub_ball in Breakdown.Torus.ApproxClose, line 192. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L192).

**Ball support is compact.** A field whose topological support lies in a closed Euclidean ball has compact support. Source: Breakdown.Periodic.ApproxClose.Internal.hasCompactSupport_of_ball in Breakdown.Torus.ApproxClose, line 199. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L199).

**The zero field has decay.** The zero field satisfies the decay-field conditions. Source: Breakdown.Periodic.ApproxClose.Internal.zero_decayField in Breakdown.Torus.ApproxClose, line 203. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L203).

**Decay is preserved by addition.** The sum of two decay fields is a decay field. Source: Breakdown.Periodic.ApproxClose.Internal.decay_add in Breakdown.Torus.ApproxClose, line 208. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L208).

**Decay is preserved by scaling.** Every real scalar multiple of a decay field is a decay field. Source: Breakdown.Periodic.ApproxClose.Internal.decay_smul in Breakdown.Torus.ApproxClose, line 224. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L224).

**Decay is preserved by subtraction.** The difference of two decay fields is a decay field. Source: Breakdown.Periodic.ApproxClose.Internal.decay_sub in Breakdown.Torus.ApproxClose, line 233. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L233).

**Decay of a finite field sum.** Every finite real-weighted sum of decay fields is a decay field. Source: Breakdown.Periodic.ApproxClose.Internal.decay_sum in Breakdown.Torus.ApproxClose, line 241. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L241).

**Derivative vanishes locally.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ f y = 0`. Source: Breakdown.Periodic.ApproxClose.Internal.eventually_zero_fderiv in Breakdown.Torus.ApproxClose, line 250. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L250).

**Decay from smooth compact support.** A smooth divergence-free field vanishing outside a finite-radius ball satisfies the decay-field conditions. Source: Breakdown.Periodic.ApproxClose.Internal.decay_of_ball in Breakdown.Torus.ApproxClose, line 258. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L258).

**Sum formula for field embedding.** With the stated hypotheses, field embedding obeys the summation identity `Freq.embedX (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Freq.embedX (f i)`. Source: Breakdown.Periodic.ApproxClose.Internal.embed_sum in Breakdown.Torus.ApproxClose, line 287. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L287).

**The zero field is admissible.** Cutoff approximation is smooth, periodic and divergence-free, as asserted by `IsGood (0 : Space → Space)`. Source: Breakdown.Periodic.ApproxClose.Internal.good_zero in Breakdown.Torus.ApproxClose, line 300. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L300).

**Admissible fields add.** With the stated hypotheses, cutoff approximation is smooth, periodic and divergence-free, as asserted by `IsGood (f + g)`. Source: Breakdown.Periodic.ApproxClose.Internal.good_add in Breakdown.Torus.ApproxClose, line 303. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L303).

**Admissible fields scale.** With the stated hypotheses, cutoff approximation is smooth, periodic and divergence-free, as asserted by `IsGood (c • f)`. Source: Breakdown.Periodic.ApproxClose.Internal.good_smul in Breakdown.Torus.ApproxClose, line 308. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L308).

**Embedding a finite weighted field sum.** With the stated hypotheses, periodic Fourier embedding is smooth, periodic and divergence-free, as asserted by `IsGood (∑ i ∈ s, c i • g i) ∧ toV (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • toV (g i)`. Source: Breakdown.Periodic.ApproxClose.Internal.toV_sum in Breakdown.Torus.ApproxClose, line 312. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L312).

**Sum formula for Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the summation identity `toV (f - ∑ i, c i • g i) = toV f - ∑ i, c i • toV (g i)`. Source: Breakdown.Periodic.ApproxClose.Internal.toV_sub_sum in Breakdown.Torus.ApproxClose, line 329. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L329).

**Formula for L² norm.** With the stated hypotheses, L² norm obeys the exact identity `Real.sqrt (∫ y, ‖f y‖ ^ 2) = ‖hf.toLp f‖`. Source: Breakdown.Periodic.ApproxClose.Internal.l2_eq in Breakdown.Torus.ApproxClose, line 339. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L339).

**Bound for L² norm.** With the stated hypotheses, L² norm satisfies the quantitative estimate `Real.sqrt (∫ y, ‖(f + g) y‖ ^ 2) ≤ Real.sqrt (∫ y, ‖f y‖ ^ 2) + Real.sqrt (∫ y, ‖g y‖ ^ 2)`. Source: Breakdown.Periodic.ApproxClose.Internal.l2_add_le in Breakdown.Torus.ApproxClose, line 348. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L348).

**Bound for L² norm.** With the stated hypotheses, L² norm satisfies the quantitative estimate `Real.sqrt (∫ y, ‖(f - g) y‖ ^ 2) ≤ Real.sqrt (∫ y, ‖f y‖ ^ 2) + Real.sqrt (∫ y, ‖g y‖ ^ 2)`. Source: Breakdown.Periodic.ApproxClose.Internal.l2_sub_le in Breakdown.Torus.ApproxClose, line 353. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L353).

**Scaling formula for L² norm.** L² norm obeys the scalar-scaling identity `Real.sqrt (∫ y, ‖(c • f) y‖ ^ 2) = |c| * Real.sqrt (∫ y, ‖f y‖ ^ 2)`. Source: Breakdown.Periodic.ApproxClose.Internal.l2_smul in Breakdown.Torus.ApproxClose, line 358. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L358).

**L² bound for a finite field sum.** A finite weighted sum of L² fields lies in L² and has norm at most the sum of the absolute weights times the individual L² norms. Source: Breakdown.Periodic.ApproxClose.Internal.l2_sum_le in Breakdown.Torus.ApproxClose, line 365. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L365).

**L² control from continuous ball support.** A continuous field vanishing outside a finite-radius ball belongs to L². Source: Breakdown.Periodic.ApproxClose.Internal.memLp_of_ball in Breakdown.Torus.ApproxClose, line 385. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L385).

**Uniform bound for L² norm.** With the stated hypotheses, L² norm admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ φ : Space → Space, IsTestField φ → tsupport φ ⊆ Metric.closedBall 0 b → ∫ y, ‖φ y‖ ^ 2 ≤ K * ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2`. Source: Breakdown.Periodic.ApproxClose.Internal.l2_le_grad in Breakdown.Torus.ApproxClose, line 388. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L388).

**Formula for cutoff approximation.** With the stated hypotheses, cutoff approximation obeys the exact identity `∀ y, B < ‖y‖ → (∑ l, c l • φ l) y = 0`. Source: Breakdown.Periodic.ApproxClose.Internal.sum_vanish in Breakdown.Torus.ApproxClose, line 430. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L430).

**Formula for periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the exact identity `μ ^ (1 / 4 : ℝ) • toV (transplantField μ G) - ∑ l, c l • (μ ^ (1 / 4 : ℝ) • toV (transplantField μ (φ l))) = μ ^ (1 / 4 : ℝ) • toV (transplantField μ (G - ∑ l, c l • φ l))`. Source: Breakdown.Periodic.ApproxClose.Internal.toV_transplant_sub in Breakdown.Torus.ApproxClose, line 435. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L435).

**Total cutoff approximation error.** The squared approximation error is bounded by `(ε + √η)² + 2η + 2μ M₂²` under the gradient, mass and profile bounds in the statement. Source: Breakdown.Periodic.ApproxClose.Internal.pieceBound in Breakdown.Torus.ApproxClose, line 454. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L454).

**Bound for dilation.** With the stated hypotheses, dilation satisfies the estimate `‖Freq.dilX a x - Freq.dilX a₀ x₀‖ ≤ a ^ (1 / 4 : ℝ) * ‖x - x₀‖ + ‖Freq.dilX a x₀ - Freq.dilX a₀ x₀‖`. Source: Breakdown.Periodic.ApproxClose.Internal.dil_split in Breakdown.Torus.ApproxClose, line 509. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L509).

**Continuity of field embedding.** With the stated hypotheses, field embedding is continuous on the domain specified by `Continuous (fun σ => Freq.embedX (W σ))`. Source: Breakdown.Periodic.ApproxClose.Internal.embedContinuous in Breakdown.Torus.ApproxClose, line 518. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L518).

**Continuity of field embedding.** With the stated hypotheses, field embedding is continuous on the domain specified by `Continuous (fun t : Icc (0 : ℝ) L => Freq.dilX (1 - (t : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ))))))`. Source: Breakdown.Periodic.ApproxClose.Internal.profileContinuous in Breakdown.Torus.ApproxClose, line 532. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L532).

**The rescaled cutoff is transplantable.** Under the stated profile and cutoff assumptions, the rescaled cutoff is a decay field supported within radius `1/(8√μ)` and its transplant equals the periodic approximation. Source: Breakdown.Periodic.ApproxClose.Internal.simField_props in Breakdown.Torus.ApproxClose, line 563. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L563).

**Bound for whole-space flow.** With the stated hypotheses, whole-space flow satisfies the quantitative estimate `‖a - ∑ l, A.weight n l x • Freq.embedX (A.field n l)‖ ≤ ε`. Source: Breakdown.Periodic.ApproxClose.Internal.r3_bound in Breakdown.Torus.ApproxClose, line 598. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L598).

**Formula for periodic flow.** With the stated hypotheses, periodic flow obeys the exact identity `(Q - A.torusPiece μ n) x = a - ∑ l, A.weight n l x • ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ (A.field n l)))`. Source: Breakdown.Periodic.ApproxClose.Internal.torus_diff in Breakdown.Torus.ApproxClose, line 606. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L606).

**Formula for cutoff approximation.** Cutoff approximation obeys the exact identity `∀ y, b < ‖y‖ → A.field n l y = 0`. Source: Breakdown.Periodic.ApproxClose.Internal.field_vanish in Breakdown.Torus.ApproxClose, line 613. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxClose.lean#L613).

### Breakdown.Torus.ApproxField

Builds the smooth divergence-free cutoff of the self-similar profile and checks its inner and outer support regions.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ApproxField.Internal.

**Spatial part of the derivative.** The slice derivative restricts the derivative of a space-time function to increments in its spatial variable. Source: Breakdown.Periodic.ApproxField.Internal.sliceFDeriv in Breakdown.Torus.ApproxField, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L16).

**Derivative of parameterized integral.** With the stated hypotheses, parameterized integral has the Fréchet derivative specified by `HasFDerivAt (fun p => ∫ s in (0 : ℝ)..1, F (s, p)) (∫ s in (0 : ℝ)..1, sliceFDeriv F s y) y`. Source: Breakdown.Periodic.ApproxField.Internal.hasFDerivAt_unitIntegral in Breakdown.Torus.ApproxField, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L20).

**Smoothness of a parameter integral.** Integrating a smooth Banach-valued family over the fixed interval [0,1] yields a parameter map of every finite differentiability order. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_unitIntegral_nat in Breakdown.Torus.ApproxField, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L41).

**Smoothness of a parameter integral.** With the stated hypotheses, parameterized integral has the asserted differentiability order in `ContDiff ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, F (s, p))`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_unitIntegral in Breakdown.Torus.ApproxField, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L62).

**Smoothness of cross product.** With the stated hypotheses, cross product has the asserted differentiability order in `ContDiff ℝ ∞ (fun y => cross (u y) (v y))`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_cross_comp in Breakdown.Torus.ApproxField, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L69).

**Formula for cross product.** Cross product obeys the exact identity `cross 0 b = 0`. Source: Breakdown.Periodic.ApproxField.Internal.cross_zero_left in Breakdown.Torus.ApproxField, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L79).

**Smooth clamp of physical time.** The smooth time clamp subtracts `(t - a) * smoothTransition ((t - a) / δ)` from `t`. Source: Breakdown.Periodic.ApproxField.Internal.timeClamp in Breakdown.Torus.ApproxField, line 82. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L82).

**Smoothness of smooth time clamp.** Smooth time clamp has the asserted differentiability order in `ContDiff ℝ ∞ (timeClamp a δ)`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_timeClamp in Breakdown.Torus.ApproxField, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L84).

**Formula for smooth time clamp.** With the stated hypotheses, smooth time clamp obeys the exact identity `timeClamp a δ t = t`. Source: Breakdown.Periodic.ApproxField.Internal.timeClamp_of_le in Breakdown.Torus.ApproxField, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L89).

**Bound for smooth time clamp.** With the stated hypotheses, smooth time clamp satisfies the quantitative estimate `timeClamp a δ t ≤ a + δ`. Source: Breakdown.Periodic.ApproxField.Internal.timeClamp_le in Breakdown.Torus.ApproxField, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L93).

**Smoothness from clamped time curves.** With the stated hypotheses, localized velocity has the asserted differentiability order in `ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Iio T ×ˢ univ)`. Source: Breakdown.Periodic.ApproxField.Internal.contDiffOn_of_clamped in Breakdown.Torus.ApproxField, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L106).

**Smoothness of central cutoff.** Central cutoff has the asserted differentiability order in `ContDiff ℝ ∞ centralCut`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_centralCut in Breakdown.Torus.ApproxField, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L126).

**Smoothness of gradient.** Gradient has the asserted differentiability order in `ContDiff ℝ ∞ (gradientAt centralCut)`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_gradient_centralCut in Breakdown.Torus.ApproxField, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L128).

**Smoothness of vector-potential cutoff.** With the stated hypotheses, vector-potential cutoff has the asserted differentiability order in `ContDiff ℝ ∞ (fun z : ℝ × Space => cutoffField centralCut center (fun x => g (z.1, x)) z.2)`. Source: Breakdown.Periodic.ApproxField.Internal.contDiff_cutoffField_family in Breakdown.Torus.ApproxField, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L133).

**Formula for central cutoff.** With the stated hypotheses, central cutoff obeys the exact identity `centralCut x = 0`. Source: Breakdown.Periodic.ApproxField.Internal.centralCut_outer in Breakdown.Torus.ApproxField, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L150).

**Formula for central cutoff.** With the stated hypotheses, central cutoff obeys the exact identity `centralCut x = 1`. Source: Breakdown.Periodic.ApproxField.Internal.centralCut_inner in Breakdown.Torus.ApproxField, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L153).

**Derivative formula for central cutoff.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ centralCut x = 0`. Source: Breakdown.Periodic.ApproxField.Internal.fderiv_centralCut_outer in Breakdown.Torus.ApproxField, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L156).

**Derivative formula for central cutoff.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ centralCut x = 0`. Source: Breakdown.Periodic.ApproxField.Internal.fderiv_centralCut_inner in Breakdown.Torus.ApproxField, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L163).

**Derivative formula for gradient.** With the stated hypotheses, the derivative calculation gives `gradientAt centralCut x = 0`. Source: Breakdown.Periodic.ApproxField.Internal.gradient_eq_zero_of_fderiv in Breakdown.Torus.ApproxField, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L170).

**Source namespace:** Breakdown.Periodic.

**Properties of the localized flow.** Under the stated assumptions, the cutoff velocity and pressure are smooth before T, the velocity is divergence-free, both vanish outside radius 1/8 and the velocity agrees with the self-similar field inside radius 1/16. Source: Breakdown.Periodic.approxFieldProperties in Breakdown.Torus.ApproxField, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxField.lean#L178).

### Breakdown.Torus.ApproxLinks

Turns the localized profile into periodic time pieces and verifies their continuity and matching at successive time boundaries.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ApproxLinks.Internal.

**Bound for coordinate.** With the stated hypotheses, coordinate satisfies the estimate `|v j - 1 / 2| ≤ 1 / 8`. Source: Breakdown.Periodic.ApproxLinks.Internal.coord_near_of_ne in Breakdown.Torus.ApproxLinks, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L16).

**Formula for periodic wrapping.** With the stated hypotheses, periodic wrapping obeys the exact identity `f (wrap y) = f (y - freq n)`. Source: Breakdown.Periodic.ApproxLinks.Internal.wrap_eq_shift in Breakdown.Torus.ApproxLinks, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L24).

**Formula for periodic wrapping.** With the stated hypotheses, periodic wrapping obeys the exact identity `f (wrap y) = f (y - freq (fun j => round (x j - 1 / 2)))`. Source: Breakdown.Periodic.ApproxLinks.Internal.wrap_eq_near in Breakdown.Torus.ApproxLinks, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L51).

**Formula for localized velocity.** With the stated hypotheses, localized velocity obeys the exact identity `approxField W T t y = 0`. Source: Breakdown.Periodic.ApproxLinks.Internal.approxField_far in Breakdown.Torus.ApproxLinks, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L65).

**Periodicity of periodic approximation.** Periodic approximation is unit-periodic, as expressed by `IsPeriodic (approxPeriodic W T t)`. Source: Breakdown.Periodic.ApproxLinks.Internal.isPeriodic_approxPeriodic in Breakdown.Torus.ApproxLinks, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L71).

**Formula for divergence.** With the stated hypotheses, divergence obeys the exact identity `divergenceAt (approxPeriodic W T t) x = 0`. Source: Breakdown.Periodic.ApproxLinks.Internal.divergence_approxPeriodic in Breakdown.Torus.ApproxLinks, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L75).

**Smoothness of periodic approximation.** With the stated hypotheses, periodic approximation has the asserted differentiability order in `ContDiff ℝ ∞ (fun z : ℝ × Space => approxPeriodic W T (c z.1) z.2)`. Source: Breakdown.Periodic.ApproxLinks.Internal.contDiff_approxPeriodic in Breakdown.Torus.ApproxLinks, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L87).

**Continuity of periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding is continuous on the domain specified by `ContinuousOn (fun s => toV (approxPeriodic W T (c s))) (Ici 0)`. Source: Breakdown.Periodic.ApproxLinks.Internal.continuousOn_toV_approxPeriodic in Breakdown.Torus.ApproxLinks, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L102).

**Formula for piece start time.** Piece start time obeys the exact identity `stepStart T lam (n + 1) = stepStart T lam n + stepScale T lam n * (1 - lam)`. Source: Breakdown.Periodic.ApproxLinks.Internal.stepStart_succ in Breakdown.Torus.ApproxLinks, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L111).

**Continuity of approximate time piece.** With the stated hypotheses, approximate time piece is continuous on the domain specified by `Continuous (fun s : Icc (0 : ℝ) (1 - lam) => (stepScale T lam n) ^ (1 / 4 : ℝ) • toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s)))`. Source: Breakdown.Periodic.ApproxLinks.Internal.continuous_approxPiece in Breakdown.Torus.ApproxLinks, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L116).

**Formula for approximate time piece.** With the stated hypotheses, approximate time piece obeys the exact identity `approxPiece W T lam n s = (stepScale T lam n) ^ (1 / 4 : ℝ) • toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s))`. Source: Breakdown.Periodic.ApproxLinks.Internal.approxPiece_apply in Breakdown.Torus.ApproxLinks, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L147).

**Source namespace:** Breakdown.Periodic.

**Matching localized time pieces.** Under the stated assumptions, the localized time pieces satisfy their evaluation formula and match adjacent endpoints with the factor λ^(1/4). Source: Breakdown.Periodic.approxLinks in Breakdown.Torus.ApproxLinks, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxLinks.lean#L159).

### Breakdown.Torus.ApproxResidual

Reads the localized profile as a forced periodic solution and bounds the Duhamel error on each rescaled time piece.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ApproxResidual.Internal.

**Integer wrapping shift.** The wrapping shift rounds each coordinate relative to the cell center and recombines the resulting integers in the coordinate basis. Source: Breakdown.Periodic.ApproxResidual.Internal.shift in Breakdown.Torus.ApproxResidual, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L15).

**Formula for periodic wrapping.** Periodic wrapping obeys the exact identity `wrap x = x - shift x`. Source: Breakdown.Periodic.ApproxResidual.Internal.wrap_eq_sub_shift in Breakdown.Torus.ApproxResidual, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L17).

**Formula for cell center.** Cell center obeys the exact identity `center j = 1 / 2`. Source: Breakdown.Periodic.ApproxResidual.Internal.center_apply in Breakdown.Torus.ApproxResidual, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L19).

**Formula for integer shift.** Integer shift obeys the exact identity `shift x j = round (x j - 1 / 2)`. Source: Breakdown.Periodic.ApproxResidual.Internal.shift_apply in Breakdown.Torus.ApproxResidual, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L22).

**Bound for coordinate.** Coordinate satisfies the quantitative estimate `|v j - w j| ≤ dist v w`. Source: Breakdown.Periodic.ApproxResidual.Internal.coord_le_dist in Breakdown.Torus.ApproxResidual, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L25).

**Formula for integer rounding.** With the stated hypotheses, integer rounding obeys the exact identity `d = e`. Source: Breakdown.Periodic.ApproxResidual.Internal.round_eq_of_close in Breakdown.Torus.ApproxResidual, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L30).

**Formula for integer shift.** With the stated hypotheses, integer shift obeys the exact identity `shift y = shift x`. Source: Breakdown.Periodic.ApproxResidual.Internal.shift_eq_of_close in Breakdown.Torus.ApproxResidual, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L35).

**Formula for periodic wrapping.** With the stated hypotheses, periodic wrapping obeys the exact identity `f (wrap y) = f (y - shift x)`. Source: Breakdown.Periodic.ApproxResidual.Internal.wrap_local in Breakdown.Torus.ApproxResidual, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L40).

**Wrapping is locally one translation.** For a field supported within radius 1/8 of the cell center, its wrapped version agrees near each point with one fixed integer translate. Source: Breakdown.Periodic.ApproxResidual.Internal.wrap_eventually in Breakdown.Torus.ApproxResidual, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L64).

**Derivative formula for periodic wrapping.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun y => f (wrap y)) x = fderiv ℝ f (wrap x)`. Source: Breakdown.Periodic.ApproxResidual.Internal.fderiv_wrap in Breakdown.Torus.ApproxResidual, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L70).

**Derivative formula for higher derivative.** With the stated hypotheses, the derivative calculation gives `iteratedFDeriv ℝ n (fun y => f (wrap y)) x = iteratedFDeriv ℝ n f (wrap x)`. Source: Breakdown.Periodic.ApproxResidual.Internal.iteratedFDeriv_wrap in Breakdown.Torus.ApproxResidual, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L75).

**Smoothness of periodic wrapping.** With the stated hypotheses, periodic wrapping has the asserted differentiability order in `ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ (z.1, wrap z.2)) (S ×ˢ univ)`. Source: Breakdown.Periodic.ApproxResidual.Internal.contDiffOn_wrap in Breakdown.Torus.ApproxResidual, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L80).

**Continuity of periodic wrapping.** With the stated hypotheses, periodic wrapping is continuous on the domain specified by `ContinuousOn (fun z : ℝ × Space => Φ (z.1, wrap z.2)) (S ×ˢ univ)`. Source: Breakdown.Periodic.ApproxResidual.Internal.continuousOn_wrap in Breakdown.Torus.ApproxResidual, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L94).

**Formula for periodic wrapping.** Periodic wrapping obeys the exact identity `wrap (x + unitVector i) = wrap x`. Source: Breakdown.Periodic.ApproxResidual.Internal.wrap_add_unit in Breakdown.Torus.ApproxResidual, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L108).

**Wrapping produces a periodic field.** Composing any field with the wrapping map gives a unit-periodic field. Source: Breakdown.Periodic.ApproxResidual.Internal.isPeriodic_wrap in Breakdown.Torus.ApproxResidual, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L121).

**Derivative formula for spatial slice.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (f t) v w = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) (0, w)`. Source: Breakdown.Periodic.ApproxResidual.Internal.slice_fderiv_apply in Breakdown.Torus.ApproxResidual, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L125).

**Derivative for localized residual.** With the stated hypotheses, the derivative calculation gives `deriv (fun τ => f τ v) t = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) (1, 0)`. Source: Breakdown.Periodic.ApproxResidual.Internal.time_deriv in Breakdown.Torus.ApproxResidual, line 137. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L137).

**Formula for second spatial derivative.** With the stated hypotheses, second spatial derivative obeys the exact identity `iteratedFDeriv ℝ 2 (f t) v ![e, e] = fderiv ℝ (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (z.1, z.2) (0, e)) (t, v) (0, e)`. Source: Breakdown.Periodic.ApproxResidual.Internal.ssp_eq in Breakdown.Torus.ApproxResidual, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L149).

**Continuity of PDE residual.** With the stated hypotheses, PDE residual is continuous on the domain specified by `ContinuousOn (fun z : ℝ × Space => approxResidual W q T z.1 z.2) (Iio T ×ˢ univ)`. Source: Breakdown.Periodic.ApproxResidual.Internal.continuousOn_residual in Breakdown.Torus.ApproxResidual, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L174).

**The cutoff gives a forced solution.** The localized periodic velocity, wrapped pressure and wrapped residual form a forced periodic solution on every stated slab lying before T, assuming the cutoff and residual interfaces. Source: Breakdown.Periodic.ApproxResidual.Internal.forced_solution in Breakdown.Torus.ApproxResidual, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L204).

**Zero source gives zero forcing.** Heat-regularized forcing has the zero-parameter identity `forceV 0 G = 0`. Source: Breakdown.Periodic.ApproxResidual.Internal.forceV_zero in Breakdown.Torus.ApproxResidual, line 244. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L244).

**L² control from a pointwise bound.** A field bounded pointwise by M ≥ 0 has cell L² norm at most M times the square root of the cell volume. Source: Breakdown.Periodic.ApproxResidual.Internal.sqrt_integral_le in Breakdown.Torus.ApproxResidual, line 251. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L251).

**Bound for heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing satisfies the quantitative estimate `‖∫ r in a..t, forceV (t - r) (F r)‖ ≤ C0 * (M * Real.sqrt (volume.real cell)) * (2 * (t - a) ^ (1 / 2 : ℝ))`. Source: Breakdown.Periodic.ApproxResidual.Internal.force_bound in Breakdown.Torus.ApproxResidual, line 263. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L263).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `P s - (stepFrame hK μ hμ hμ1).G s (extendPiece P 0) - ∫ σ in (0 : ℝ)..s, (stepFrame hK μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ) = μ ^ (1 / 4 : ℝ) • ∫ r in a..a + μ * s, forceV (a + μ * s - r) (F r)`. Source: Breakdown.Periodic.ApproxResidual.Internal.step_identity in Breakdown.Torus.ApproxResidual, line 302. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L302).

**Bound for scaling.** With the stated hypotheses, scaling satisfies the quantitative estimate `(stepScale T lam n) ^ (1 / 4 : ℝ) ≤ θ ^ n * T ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.ApproxResidual.Internal.scale_le in Breakdown.Torus.ApproxResidual, line 349. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L349).

**Bound for localized residual.** With the stated hypotheses, localized residual satisfies the quantitative estimate `(μ * lam) ^ (-(1 / 2 : ℝ)) * (μ * s) ^ (1 / 2 : ℝ) ≤ lam ^ (-(1 / 2 : ℝ))`. Source: Breakdown.Periodic.ApproxResidual.Internal.rate_le in Breakdown.Torus.ApproxResidual, line 356. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxResidual.lean#L356).

### Breakdown.Torus.ApproxSizes

Separates the gradient energy and scaled L² mass of the localized profile to control the initial-data error.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Integrated squared gradient.** The gradient energy integrates the sum of the squared norms of the three coordinate derivatives. Source: Breakdown.Periodic.gradEnergy in Breakdown.Torus.ApproxSizes, line 11. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L11).

**Rescaled localized field.** The rescaled localized field evaluates the cutoff velocity at `center + √μ y` and multiplies it by `√μ`. Source: Breakdown.Periodic.cutAt in Breakdown.Torus.ApproxSizes, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L13).

**Source namespace:** Breakdown.Periodic.ApproxSizes.Internal.

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (approxField W T t)`. Source: Breakdown.Periodic.ApproxSizes.Internal.slice_contDiff in Breakdown.Torus.ApproxSizes, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L20).

**Smoothness of rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field has the asserted differentiability order in `ContDiff ℝ ∞ (cutAt W T t μ)`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_contDiff in Breakdown.Torus.ApproxSizes, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L31).

**Derivative for rescaled cutoff field.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (cutAt W T t μ) y v = (Real.sqrt μ * Real.sqrt μ) • fderiv ℝ (approxField W T t) (center + Real.sqrt μ • y) v`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_cutAt_apply in Breakdown.Torus.ApproxSizes, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L35).

**Formula for rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field obeys the exact identity `divergenceAt (cutAt W T t μ) y = 0`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_div in Breakdown.Torus.ApproxSizes, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L48).

**Support after rescaling.** With the stated hypotheses, rescaled cutoff field satisfies the set inclusion `tsupport (cutAt W T t μ) ⊆ Metric.closedBall 0 (1 / (8 * Real.sqrt μ))`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_tsupport in Breakdown.Torus.ApproxSizes, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L55).

**Formula for transplantation.** With the stated hypotheses, transplantation obeys the exact identity `transplantField μ (cutAt W T t μ) = approxPeriodic W T t`. Source: Breakdown.Periodic.ApproxSizes.Internal.transplant_cutAt in Breakdown.Torus.ApproxSizes, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L72).

**Derivative formula for dilation.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun y => r • f (r • y)) y v = (r * r) • fderiv ℝ f (r • y) v`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_dil_apply in Breakdown.Torus.ApproxSizes, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L78).

**Formula for L² mass.** With the stated hypotheses, L² mass obeys the exact identity `∫ y, ‖r • f (r • y)‖ ^ 2 = r⁻¹ * ∫ y, ‖f y‖ ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.mass_dil in Breakdown.Torus.ApproxSizes, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L104).

**Formula for rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field obeys the exact identity `cutAt W T t μ = fun y => (Real.sqrt μ / Real.sqrt ℓ) • cutAt W T t ℓ ((Real.sqrt μ / Real.sqrt ℓ) • y)`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_dil in Breakdown.Torus.ApproxSizes, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L115).

**Divergence of a difference.** With the stated hypotheses, divergence obeys the exact identity `divergenceAt (f - g) y = 0`. Source: Breakdown.Periodic.ApproxSizes.Internal.div_sub in Breakdown.Torus.ApproxSizes, line 123. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L123).

**Decay of a field difference.** The difference of two decay fields is a decay field. Source: Breakdown.Periodic.ApproxSizes.Internal.decay_sub in Breakdown.Torus.ApproxSizes, line 134. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L134).

**Decay from bounded support.** A smooth divergence-free field supported in a closed ball of nonnegative radius satisfies the decay-field conditions. Source: Breakdown.Periodic.ApproxSizes.Internal.decay_of_support in Breakdown.Torus.ApproxSizes, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L151).

**Decay property of spatial slice.** With the stated hypotheses, spatial slice satisfies the defined decay-field conditions in `IsDecayField (W s)`. Source: Breakdown.Periodic.ApproxSizes.Internal.slice_decay in Breakdown.Torus.ApproxSizes, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L184).

**Uniform bound for gradient energy.** With the stated hypotheses, gradient energy admits the uniform bound stated in `∃ B : ℝ, ∀ s, gradEnergy (W s) ≤ B`. Source: Breakdown.Periodic.ApproxSizes.Internal.gradEnergy_slice_bound in Breakdown.Torus.ApproxSizes, line 191. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L191).

**Norm identity for time piece.** With the stated hypotheses, time piece has the norm identity `‖(μ ^ (1 / 4 : ℝ)) • toV (approxPeriodic W T t)‖ ^ 2 = gradEnergy (cutAt W T t μ) + μ * ∫ y, ‖cutAt W T t μ y‖ ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.norm_sq_piece in Breakdown.Torus.ApproxSizes, line 216. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L216).

**Decay property of rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field satisfies the defined decay-field conditions in `IsDecayField (cutAt W T t μ)`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_decay in Breakdown.Torus.ApproxSizes, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L228).

**Norm identity for field embedding.** With the stated hypotheses, field embedding has the norm identity `‖Freq.embedX f‖ = Real.sqrt (gradEnergy f)`. Source: Breakdown.Periodic.ApproxSizes.Internal.norm_embed in Breakdown.Torus.ApproxSizes, line 236. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L236).

**Norm identity for field embedding.** With the stated hypotheses, field embedding has the norm identity `‖Freq.embedX f - Freq.embedX g‖ = Real.sqrt (gradEnergy (f - g))`. Source: Breakdown.Periodic.ApproxSizes.Internal.norm_embed_sub in Breakdown.Torus.ApproxSizes, line 240. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L240).

**Formula for time piece.** With the stated hypotheses, time piece obeys the exact identity `‖(μ ^ (1 / 4 : ℝ)) • toV (approxPeriodic W T t)‖ ^ 2 = (Real.sqrt μ / Real.sqrt (T - t)) * gradEnergy (cutAt W T t (T - t)) + μ * ((Real.sqrt μ / Real.sqrt (T - t))⁻¹ * ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2)`. Source: Breakdown.Periodic.ApproxSizes.Internal.piece_sq in Breakdown.Torus.ApproxSizes, line 245. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L245).

**Bound for field embedding.** With the stated hypotheses, field embedding satisfies the quantitative estimate `‖Freq.embedX (W (similarityTime T t)) - Freq.embedX (cutAt W T t (T - t))‖ ≤ Real.sqrt ε ∧ gradEnergy (cutAt W T t (T - t)) = ‖Freq.embedX (cutAt W T t (T - t))‖ ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.embed_cut_bounds in Breakdown.Torus.ApproxSizes, line 257. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L257).

**Squared norm of a difference.** The squared distance of two vectors is at most twice the sum of their squared norms. Source: Breakdown.Periodic.ApproxSizes.Internal.sq_norm_sub_le in Breakdown.Torus.ApproxSizes, line 270. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L270).

**Bound for L² mass.** With the stated hypotheses, L² mass satisfies the estimate `T * M ≤ (δ / 2) ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.mass_arith in Breakdown.Torus.ApproxSizes, line 274. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L274).

**Bound for cutoff energy.** With the stated hypotheses, cutoff energy satisfies the estimate `(A + δ / 2) ^ 2 + (δ / 2) ^ 2 ≤ (A + δ) ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.final_arith in Breakdown.Torus.ApproxSizes, line 294. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L294).

**Scaling formula for cross product.** Cross product obeys the scalar-scaling identity `cross (a • u) (b • v) = (a * b) • cross u v`. Source: Breakdown.Periodic.ApproxSizes.Internal.cross_smul_smul in Breakdown.Torus.ApproxSizes, line 299. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L299).

**Formula for rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field obeys the exact identity `cutAt W T t (T - t) y = centralCut (center + Real.sqrt (T - t) • y) • W (similarityTime T t) y + Real.sqrt (T - t) • cross (gradientAt centralCut (center + Real.sqrt (T - t) • y)) (∫ s in (0 : ℝ)..1, s • cross (W (similarityTime T t) (s • y)) y)`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_formula in Breakdown.Torus.ApproxSizes, line 303. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L303).

**Bound for cross product.** Cross product satisfies the quantitative estimate `‖cross a b‖ ≤ ‖a‖ * ‖b‖`. Source: Breakdown.Periodic.ApproxSizes.Internal.norm_cross_le in Breakdown.Torus.ApproxSizes, line 324. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L324).

**The profile bound is nonnegative.** The constant appearing in the similarity-profile conditions is nonnegative. Source: Breakdown.Periodic.ApproxSizes.Internal.profile_const_nonneg in Breakdown.Torus.ApproxSizes, line 337. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L337).

**Uniform bound for central cutoff.** Central cutoff admits the uniform bound stated in `∃ G : ℝ, 0 ≤ G ∧ ∀ x, |centralCut x| ≤ 1 ∧ ‖gradientAt centralCut x‖ ≤ G`. Source: Breakdown.Periodic.ApproxSizes.Internal.centralCut_bounds in Breakdown.Torus.ApproxSizes, line 363. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L363).

**Bound for rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field satisfies the quantitative estimate `‖cutAt W T t (T - t) y‖ ^ 2 ≤ (Iic (1 / (8 * Real.sqrt (T - t)))).indicator (fun r : ℝ => 2 * (C / (1 + r)) ^ 2 + 2 * (T - t) * G ^ 2 * C ^ 2) ‖y‖`. Source: Breakdown.Periodic.ApproxSizes.Internal.cutAt_sq_le in Breakdown.Torus.ApproxSizes, line 385. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L385).

**Radial logarithmic integral bound.** With the stated hypotheses, cutoff energy satisfies the integrability assertion `Integrable (fun y : Space => (Iic ρ).indicator (fun r : ℝ => 2 * (a / (1 + r)) ^ 2 + b) ‖y‖) ∧ ∫ y : Space, (Iic ρ).indicator (fun r : ℝ => 2 * (a / (1 + r)) ^ 2 + b) ‖y‖ ≤ 3 * volume.real (Metric.ball (0 : Space) 1) * ((2 * a ^ 2 + b * ρ ^ 2) * ρ)`. Source: Breakdown.Periodic.ApproxSizes.Internal.radial_bound in Breakdown.Torus.ApproxSizes, line 430. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L430).

**Uniform bound for rescaled cutoff field.** With the stated hypotheses, rescaled cutoff field admits the uniform bound stated in `∃ K : ℝ, ∀ T t : ℝ, 0 < T → t < T → T - t ≤ 1 → ∫ y, ‖cutAt W T t (T - t) y‖ ^ 2 ≤ K / Real.sqrt (T - t)`. Source: Breakdown.Periodic.ApproxSizes.Internal.massBound in Breakdown.Torus.ApproxSizes, line 481. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L481).

**Bound for vector potential.** With the stated hypotheses, vector potential satisfies the estimate `s * (a + b * s * ρ) ≤ 2 * C / ρ`. Source: Breakdown.Periodic.ApproxSizes.Internal.potential_arith in Breakdown.Torus.ApproxSizes, line 505. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L505).

**Derivative formula for difference.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y v = fderiv ℝ (W (similarityTime T t)) y v - ((centralCut (center + Real.sqrt (T - t) • y) • fderiv ℝ (W (similarityTime T t)) y v + fderiv ℝ centralCut (center + Real.sqrt (T - t) • y) (Real.sqrt (T - t) • v) • W (similarityTime T t) y) + Real.sqrt (T - t) • (cross (gradientAt centralCut (center + Real.sqrt (T - t) • y)) ((∫ s in (0 : ℝ)..1, Cutoff.Internal.partialSecond (Cutoff.Internal.potentialIntegrand 0 (W (similarityTime T t))) s y) v) + cross (fderiv ℝ (gradientAt centralCut) (center + Real.sqrt (T - t) • y) (Real.sqrt (T - t) • v)) (homotopyPotential 0 (W (similarityTime T t)) y)))`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_diff_apply in Breakdown.Torus.ApproxSizes, line 556. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L556).

**Bound for the combined derivatives.** Sum of gradient terms satisfies the quantitative estimate `‖g' - ((χ • g' + a • gy) + r • (X + Y))‖ ≤ |1 - χ| * ‖g'‖ + |a| * ‖gy‖ + |r| * (‖X‖ + ‖Y‖)`. Source: Breakdown.Periodic.ApproxSizes.Internal.norm_combo in Breakdown.Torus.ApproxSizes, line 600. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L600).

**Bound for cutoff energy.** With the stated hypotheses, cutoff energy satisfies the estimate `n ≤ C / (1 + ρ) ^ 2 + r ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C)`. Source: Breakdown.Periodic.ApproxSizes.Internal.mid_arith in Breakdown.Torus.ApproxSizes, line 612. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L612).

**Derivative formula for difference.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y = 0`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_diff_inner in Breakdown.Torus.ApproxSizes, line 642. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L642).

**Derivative formula for difference.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y = fderiv ℝ (W (similarityTime T t)) y`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_diff_outer in Breakdown.Torus.ApproxSizes, line 666. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L666).

**Bound for difference.** With the stated hypotheses, difference satisfies the estimate `‖fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y v‖ ≤ C / (1 + ‖y‖) ^ 2 + Real.sqrt (T - t) ^ 2 * (16 * B₁ * C + 32 * G * C + B₂ * C)`. Source: Breakdown.Periodic.ApproxSizes.Internal.fderiv_diff_mid in Breakdown.Torus.ApproxSizes, line 686. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L686).

**Bound for geometric tail.** With the stated hypotheses, geometric tail satisfies the estimate `6 * (C / (1 + ρ) ^ 2) ^ 2 ≤ 24 * C ^ 2 * Real.sqrt r * (1 + ρ) ^ (-(7 / 2 : ℝ))`. Source: Breakdown.Periodic.ApproxSizes.Internal.tail_arith in Breakdown.Torus.ApproxSizes, line 756. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L756).

**Bound for cutoff energy.** With the stated hypotheses, cutoff energy satisfies the quantitative estimate `n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 ≤ 6 * A ^ 2 + 6 * B ^ 2`. Source: Breakdown.Periodic.ApproxSizes.Internal.sq_three_le in Breakdown.Torus.ApproxSizes, line 780. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L780).

**Bound for gradient.** With the stated hypotheses, gradient satisfies the quantitative estimate `∑ i : Fin 3, ‖fderiv ℝ (W (similarityTime T t) - cutAt W T t (T - t)) y (unitVector i)‖ ^ 2 ≤ 24 * C ^ 2 * Real.sqrt (Real.sqrt (T - t)) * (1 + ‖y‖) ^ (-(7 / 2 : ℝ)) + (Iic (1 / (8 * Real.sqrt (T - t)))).indicator (fun ρ : ℝ => 2 * (0 / (1 + ρ)) ^ 2 + 6 * (16 * B₁ * C + 32 * G * C + B₂ * C) ^ 2 * Real.sqrt (T - t) ^ 4) ‖y‖`. Source: Breakdown.Periodic.ApproxSizes.Internal.grad_sum_le in Breakdown.Torus.ApproxSizes, line 788. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L788).

**Bound for cutoff energy.** With the stated hypotheses, cutoff energy satisfies the estimate `a * Real.sqrt (Real.sqrt ℓ) + b * Real.sqrt ℓ ≤ ε`. Source: Breakdown.Periodic.ApproxSizes.Internal.eps_arith in Breakdown.Torus.ApproxSizes, line 837. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L837).

**Source namespace:** Breakdown.Periodic.

**Small-scale initial-data comparison.** Under the stated assumptions, at sufficiently small T the scaled periodic initial-data discrepancy is bounded by the whole-space embedding discrepancy plus any positive tolerance. Source: Breakdown.Periodic.datumClose in Breakdown.Torus.ApproxSizes, line 1010. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ApproxSizes.lean#L1010).

### Breakdown.Torus.Approximants

Approximates the compact profile curve by finite continuous combinations of test fields and propagates them through the profile rotation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.Approximants.

**Finite continuous approximation.** A continuous map on a compact Hausdorff space admits a uniform approximation by a finite weighted sum of points from a dense set, with continuous weights between zero and one. Source: Breakdown.Periodic.Internal.Approximants.exists_finite_approx in Breakdown.Torus.Approximants, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Approximants.lean#L13).

**Rotation preserves the norm.** Finite test-field approximation has the norm identity `‖(⇑e)^[j] y‖ = ‖y‖`. Source: Breakdown.Periodic.Internal.Approximants.iterate_norm in Breakdown.Torus.Approximants, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Approximants.lean#L58).

**Rotation of a weighted field sum.** Finite test-field approximation obeys the exact identity `∑ l, c l • (⇑e)^[j] (y l) - (⇑e)^[j] z = (⇑e)^[j] (∑ l, c l • y l - z)`. Source: Breakdown.Periodic.Internal.Approximants.iterate_combo in Breakdown.Torus.Approximants, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Approximants.lean#L64).

**Rotate a test field repeatedly.** Repeated pushforward by the stated linear isometry preserves the test-field property and the common support ball, and commutes with embedding under the rotation interface. Source: Breakdown.Periodic.Internal.Approximants.rot_iterate in Breakdown.Torus.Approximants, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Approximants.lean#L71).

**Formula for profile.** With the stated hypotheses, profile obeys the exact identity `F.profilePiece w P k (k * j + i) t = (⇑(Freq.rotX R))^[j] (F.profilePiece w P k i t)`. Source: Breakdown.Periodic.Internal.Approximants.profile_rot in Breakdown.Torus.Approximants, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Approximants.lean#L90).

### Breakdown.Torus.Assembly

Combines the periodic approximation, finite-dimensional initial correction and sequence inverse in the construction of periodic blow-up.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**The Fourier realization contract.** The realization contract identifies its heat, bilinear, dilation, rotation, embedding and test-space components with the chosen Fourier constructions. Source: Breakdown.Periodic.IsFreqTrRealization in Breakdown.Torus.Assembly, line 14. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L14).

**Source namespace:** Breakdown.Periodic.Assembly.Internal.

**Addition formula for extended time piece.** Extended time piece obeys the addition identity `extendPiece (f + g) t = extendPiece f t + extendPiece g t`. Source: Breakdown.Periodic.Assembly.Internal.extendPiece_add in Breakdown.Torus.Assembly, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L20).

**Bound for extended time piece.** Extended time piece satisfies the quantitative estimate `‖extendPiece f t‖ ≤ ‖f‖`. Source: Breakdown.Periodic.Assembly.Internal.norm_extendPiece_le in Breakdown.Torus.Assembly, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L27).

**Choose a sufficiently small tolerance.** For the stated positive tolerance δ, a positive ε ≤ 1 can be chosen so that εK ≤ δ. Source: Breakdown.Periodic.Assembly.Internal.exists_small in Breakdown.Torus.Assembly, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L35).

**Uniform control in finite dimension.** Pointwise small-scale bounds for a family of operators become a uniform operator-norm bound on a finite-dimensional domain. Source: Breakdown.Periodic.Assembly.Internal.uniform_of_basis in Breakdown.Torus.Assembly, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L46).

**Addition formula for divergence.** With the stated hypotheses, divergence obeys the addition identity `divergenceAt (f + g) x = divergenceAt f x + divergenceAt g x`. Source: Breakdown.Periodic.Assembly.Internal.divergenceAt_add in Breakdown.Torus.Assembly, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L72).

**Enlarge the common support radius.** An approximant with support radius `b` remains an approximant for any radius `b′ ≥ b`. Source: Breakdown.Periodic.Assembly.Internal.enlargeApprox in Breakdown.Torus.Assembly, line 78. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L78).

**Enlarge the test-lift support radius.** A test-field lift with support radius `b` is reused at any radius `b′ ≥ b`. Source: Breakdown.Periodic.Assembly.Internal.enlargeLift in Breakdown.Torus.Assembly, line 81. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L81).

**Bound for periodic initial-data operator.** With the stated hypotheses, periodic initial-data operator satisfies the quantitative estimate `‖torusSeed hK T lam hT hT1 hl hl1 Jt‖ ≤ ‖Jt‖`. Source: Breakdown.Periodic.Assembly.Internal.norm_torusSeed_le in Breakdown.Torus.Assembly, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L85).

**Formula for periodic flow.** With the stated hypotheses, periodic flow obeys the exact identity `∀ g n, (R g).2 n - (2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n) (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (f n) ((R g).2 n) - (if n = 0 then (stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0) (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt (R g).1) else (lam ^ (1 / 4 : ℝ) / θ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n) (stepScale_le_one hT1 hl hl1 n)).pieceFree (1 - lam) (pieceEnd (1 - lam) ((R g).2 (n - 1)))) = g n`. Source: Breakdown.Periodic.Assembly.Internal.torus_seq_equation in Breakdown.Torus.Assembly, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L100).

**Bound for periodic correction.** With the stated hypotheses, periodic correction satisfies the quantitative estimate `q * (1 + a * 2 * c * d * q) ≤ q * (1 + A * 2 * Cc * D * q)`. Source: Breakdown.Periodic.Assembly.Internal.bound_mono in Breakdown.Torus.Assembly, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L167).

**Bound for periodic correction.** With the stated hypotheses, periodic correction satisfies the estimate `1 + a * x * y ≤ 1 + a * X * Y`. Source: Breakdown.Periodic.Assembly.Internal.mono3 in Breakdown.Torus.Assembly, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Assembly.lean#L178).

### Breakdown.Torus.BaseInverse

Converts the coordinate equations of a right inverse into the continuous-linear-map identity used for the whole-space sequence operator.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.

**Right inverse from coordinate identities.** The coordinate identities for the candidate inverse imply the required continuous-linear-map right-inverse identity. Source: Breakdown.Periodic.Internal.seqChain_comp_eq_id in Breakdown.Torus.BaseInverse, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/BaseInverse.lean#L12).

### Breakdown.Torus.Basic

Checks the heat semigroup and bilinear kernel on the weighted periodic Fourier space, including their coefficient formulas and continuity.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.

**Formula for heat evolution.** Heat evolution obeys the exact identity `((heat t x : V) : Seq) k = heatFactor t k • (x : Seq) k`. Source: Breakdown.Periodic.Internal.heat_apply in Breakdown.Torus.Basic, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L11).

**Formula for bilinear heat kernel.** Bilinear heat kernel obeys the exact identity `((kernel τ u v : V) : Seq) k = kernelSeq τ u v k`. Source: Breakdown.Periodic.Internal.kernel_apply in Breakdown.Torus.Basic, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L14).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < weight k`. Source: Breakdown.Periodic.Internal.weight_pos in Breakdown.Torus.Basic, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L17).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < Real.sqrt (weight k)`. Source: Breakdown.Periodic.Internal.sqrt_weight_pos in Breakdown.Torus.Basic, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L20).

**Nonnegativity of heat multiplier.** Heat multiplier is nonnegative, as stated in `0 ≤ heatFactor t k`. Source: Breakdown.Periodic.Internal.heatFactor_nonneg in Breakdown.Torus.Basic, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L23).

**Multiply heat factors at added times.** With the stated hypotheses, heat multiplier at added times obeys the addition identity `heatFactor (s + t) k = heatFactor s k * heatFactor t k`. Source: Breakdown.Periodic.Internal.heatFactor_add in Breakdown.Torus.Basic, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L26).

**Bound for heat multiplier.** With the stated hypotheses, heat multiplier satisfies the estimate `heatFactor t k ≤ heatFactor s k`. Source: Breakdown.Periodic.Internal.heatFactor_anti in Breakdown.Torus.Basic, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L32).

**Continuity of heat multiplier.** Heat multiplier is continuous on the domain specified by `Continuous fun t => heatFactor t k`. Source: Breakdown.Periodic.Internal.continuous_heatFactor in Breakdown.Torus.Basic, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L38).

**The real value of the square exponent.** Square exponent satisfies the estimate `(0 : ℝ) < (2 : ENNReal).toReal`. Source: Breakdown.Periodic.Internal.two_toReal_pos in Breakdown.Torus.Basic, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L42).

**Norm identity for Fourier sequence.** Fourier sequence has the norm identity `‖a‖ ^ 2 = ∑' k, ‖a k‖ ^ 2`. Source: Breakdown.Periodic.Internal.norm_sq_seq in Breakdown.Torus.Basic, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L44).

**Summability of Fourier evolution.** Periodic Fourier evolution satisfies the series-convergence assertion `Summable fun k => ‖a k‖ ^ 2`. Source: Breakdown.Periodic.Internal.summable_sq in Breakdown.Torus.Basic, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L48).

**Bound for periodic Fourier evolution.** With the stated hypotheses, periodic Fourier evolution satisfies the quantitative estimate `‖a‖ ≤ ‖b‖`. Source: Breakdown.Periodic.Internal.norm_le_of_le in Breakdown.Torus.Basic, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L52).

**Limit of Fourier sequence.** With the stated hypotheses, Fourier sequence has the limit `Tendsto F l (𝓝 G)`. Source: Breakdown.Periodic.Internal.tendsto_seq in Breakdown.Torus.Basic, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L58).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `(freq k) i = (k i : ℝ)`. Source: Breakdown.Periodic.Internal.freq_apply in Breakdown.Torus.Basic, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L84).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.Internal.norm_freq_sq in Breakdown.Torus.Basic, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L87).

**Squared frequency-vector norm.** Frequency-vector norm has the norm identity `‖latVec k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.Internal.norm_latVec_sq in Breakdown.Torus.Basic, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L91).

**Frequency-vector norm.** Frequency-vector norm has the norm identity `‖latVec k‖ = ‖freq k‖`. Source: Breakdown.Periodic.Internal.norm_latVec in Breakdown.Torus.Basic, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L95).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k c = inner ℂ (latVec k) c`. Source: Breakdown.Periodic.Internal.divPairing_eq_inner in Breakdown.Torus.Basic, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L99).

**Bound for divergence pairing.** Divergence pairing satisfies the quantitative estimate `‖divPairing k c‖ ≤ ‖freq k‖ * ‖c‖`. Source: Breakdown.Periodic.Internal.norm_divPairing_le in Breakdown.Torus.Basic, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L103).

**Orthogonal projection contracts.** Divergence pairing satisfies the quantitative estimate `‖(divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k‖ ≤ ‖c‖`. Source: Breakdown.Periodic.Internal.norm_proj_le in Breakdown.Torus.Basic, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L107).

**Bound for Leray projection.** Leray projection satisfies the quantitative estimate `‖divFree k c‖ ≤ 2 * ‖c‖`. Source: Breakdown.Periodic.Internal.norm_divFree_le in Breakdown.Torus.Basic, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L117).

**Norm identity for Sobolev weight.** Sobolev weight has the norm identity `‖(u : Seq) k‖ = Real.sqrt (weight k) * ‖coeff u k‖`. Source: Breakdown.Periodic.Internal.norm_eq_sqrt_weight_mul in Breakdown.Torus.Basic, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L126).

**Bound for Fourier coefficient.** Fourier coefficient satisfies the quantitative estimate `‖coeff u k‖ ≤ ‖(u : Seq) k‖`. Source: Breakdown.Periodic.Internal.norm_coeff_le in Breakdown.Torus.Basic, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L132).

**Bound for lattice frequency.** Lattice frequency satisfies the quantitative estimate `2 * π * ‖freq k‖ * ‖coeff u k‖ ≤ ‖(u : Seq) k‖`. Source: Breakdown.Periodic.Internal.freq_mul_coeff_le in Breakdown.Torus.Basic, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L138).

**Mean squared sequence norm.** The auxiliary advection bound is half the sum of the squared sequence norms of its two inputs. Source: Breakdown.Periodic.Internal.advBound in Breakdown.Torus.Basic, line 147. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L147).

**Symmetry of the advection bound.** Advection bound obeys the symmetry identity `advBound v u = advBound u v`. Source: Breakdown.Periodic.Internal.advBound_comm in Breakdown.Torus.Basic, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L149).

**Nonnegativity of the advection bound.** Advection bound satisfies the quantitative estimate `0 ≤ advBound u v`. Source: Breakdown.Periodic.Internal.advBound_nonneg in Breakdown.Torus.Basic, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L152).

**Bound for advection coefficient.** Advection coefficient satisfies the quantitative estimate `‖advCoef u v k‖ ≤ advBound u v`. Source: Breakdown.Periodic.Internal.norm_advCoef_le in Breakdown.Torus.Basic, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L158).

**Summability of Gaussian weight.** With the stated hypotheses, Gaussian weight satisfies the series-convergence assertion `Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2))`. Source: Breakdown.Periodic.Internal.summable_expSq in Breakdown.Torus.Basic, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L179).

**Summable products over a finite cube.** With the stated hypotheses, finite-dimensional product series satisfies the series-convergence assertion `∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i)`. Source: Breakdown.Periodic.Internal.summable_prod_fin in Breakdown.Torus.Basic, line 191. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L191).

**Summability of lattice frequency.** With the stated hypotheses, lattice frequency satisfies the series-convergence assertion `Summable fun k : Lattice => Real.exp (-(c * ‖freq k‖ ^ 2))`. Source: Breakdown.Periodic.Internal.summable_exp_freq in Breakdown.Torus.Basic, line 200. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L200).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * heatFactor τ k ^ 2 ≤ (1 + 1 / τ) * Real.exp (-((4 * π ^ 2 * τ) * ‖freq k‖ ^ 2))`. Source: Breakdown.Periodic.Internal.weight_heat_le in Breakdown.Torus.Basic, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L205).

**Summability of Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the series-convergence assertion `Summable fun k => weight k * heatFactor τ k ^ 2`. Source: Breakdown.Periodic.Internal.summable_weight_heat in Breakdown.Torus.Basic, line 227. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L227).

**Bound for kernel coefficient.** With the stated hypotheses, kernel coefficient satisfies the quantitative estimate `‖kernelSeq τ u v k‖ ≤ 2 * advBound u v * (Real.sqrt (weight k) * heatFactor τ₁ k)`. Source: Breakdown.Periodic.Internal.norm_kernelSeq_le in Breakdown.Torus.Basic, line 232. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L232).

**Source namespace:** Breakdown.Periodic.

**Heat at time zero is the identity.** Heat evolution has the zero-parameter identity `heat 0 = ContinuousLinearMap.id ℝ V`. Source: Breakdown.Periodic.heat_zero in Breakdown.Torus.Basic, line 261. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L261).

**The heat semigroup law.** With the stated hypotheses, heat semigroup obeys the addition identity `heat (s + t) = (heat s).comp (heat t)`. Source: Breakdown.Periodic.heat_add in Breakdown.Torus.Basic, line 269. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L269).

**Bound for heat evolution.** Heat evolution satisfies the quantitative estimate `‖heat t‖ ≤ 1`. Source: Breakdown.Periodic.norm_heat_le in Breakdown.Torus.Basic, line 277. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L277).

**Continuity of heat evolution.** Heat evolution is continuous on the domain specified by `ContinuousOn (fun t => heat t x) (Ici 0)`. Source: Breakdown.Periodic.heat_continuousOn in Breakdown.Torus.Basic, line 286. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L286).

**Formula for bilinear heat kernel.** Bilinear heat kernel obeys the exact identity `kernel τ u v = kernel τ v u`. Source: Breakdown.Periodic.kernel_symm in Breakdown.Torus.Basic, line 299. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L299).

**Continuity of bilinear heat kernel.** Bilinear heat kernel is continuous on the domain specified by `ContinuousOn (fun τ => kernel τ u v) (Ioi 0)`. Source: Breakdown.Periodic.kernel_continuousOn in Breakdown.Torus.Basic, line 307. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L307).

**Formula for heat evolution.** With the stated hypotheses, heat evolution obeys the exact identity `heat s (kernel τ u v) = kernel (s + τ) u v`. Source: Breakdown.Periodic.heat_kernel in Breakdown.Torus.Basic, line 338. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L338).

**Heat multiplies each coefficient.** The Fourier-coefficient calculation gives `coeff (heat t u) k = heatFactor t k • coeff u k`. Source: Breakdown.Periodic.coeff_heat in Breakdown.Torus.Basic, line 349. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L349).

**Coefficients of the bilinear kernel.** With the stated hypotheses, the Fourier-coefficient calculation gives `coeff (kernel τ u v) k = (-(1 / 2) * heatFactor τ k) • divFree k (advCoef u v k + advCoef v u k)`. Source: Breakdown.Periodic.coeff_kernel in Breakdown.Torus.Basic, line 353. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L353).

**Sum formula for Sobolev weight.** Sobolev weight obeys the summation identity `‖u‖ ^ 2 = ∑' k, weight k * ‖coeff u k‖ ^ 2`. Source: Breakdown.Periodic.norm_sq_eq_tsum in Breakdown.Torus.Basic, line 363. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L363).

**Fourier coefficients determine a field.** With the stated hypotheses, the Fourier-coefficient calculation gives `u = v`. Source: Breakdown.Periodic.coeff_injective in Breakdown.Torus.Basic, line 373. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Basic.lean#L373).

### Breakdown.Torus.ChainR3

Factors each whole-space linearized time-piece interaction through the common shell space.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ChainR3.Internal.

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f σ = f (projIcc 0 L hL σ)`. Source: Breakdown.Periodic.ChainR3.Internal.extendPiece_eq in Breakdown.Torus.ChainR3, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L13).

**Integral equality from the open interval.** For s ≥ 0, two functions agreeing throughout (0,s) have equal interval integrals from zero to s. Source: Breakdown.Periodic.ChainR3.Internal.integral_congr_Ioo in Breakdown.Torus.ChainR3, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L18).

**Composition of diagonal operators.** With the stated hypotheses, diagonal sequence operator obeys the composition identity `(seqOp A).comp (seqOp B) = seqOp fun n => (A n).comp (B n)`. Source: Breakdown.Periodic.ChainR3.Internal.seqOp_comp in Breakdown.Torus.ChainR3, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L24).

**Continuity of extended time piece.** With the stated hypotheses, extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.Periodic.ChainR3.Internal.continuous_extendPiece in Breakdown.Torus.ChainR3, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L39).

**Bound for extended time piece.** With the stated hypotheses, extended time piece satisfies the quantitative estimate `‖extendPiece f σ‖ ≤ ‖f‖`. Source: Breakdown.Periodic.ChainR3.Internal.norm_extendPiece_le in Breakdown.Torus.ChainR3, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L45).

**Bound for whole-space shell interaction.** With the stated hypotheses, whole-space shell interaction satisfies the quantitative estimate `∀ τ, 0 < τ → τ ≤ 1 → ‖lambdaR3 φ hφ b τ‖ ≤ (C * ‖Freq.embedX φ‖) * τ ^ (-(3 / 4 : ℝ))`. Source: Breakdown.Periodic.ChainR3.Internal.lambda_bound in Breakdown.Torus.ChainR3, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L50).

**Continuity of spatial shell interaction.** With the stated hypotheses, whole-space shell interaction is continuous on the domain specified by `ContinuousOn (fun τ => lambdaR3 φ hφ b τ ζ) (Ioi 0)`. Source: Breakdown.Periodic.ChainR3.Internal.lambda_cont in Breakdown.Torus.ChainR3, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L61).

**Formula for time piece.** With the stated hypotheses, time piece obeys the exact identity `(∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ) (A.weight n l)).comp (pieceComp L (restrictR3 b)) = (2 : ℝ) • H.pieceBil L (A.r3Piece n)`. Source: Breakdown.Periodic.ChainR3.Internal.piece_eq in Breakdown.Torus.ChainR3, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L66).

**Formula for restriction.** With the stated hypotheses, restriction obeys the exact identity `(r3Lambda A).comp (r3Restrict L b) = seqOp fun n => (2 : ℝ) • H.pieceBil L (A.r3Piece n)`. Source: Breakdown.Periodic.ChainR3.Internal.lambda_restrict in Breakdown.Torus.ChainR3, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L110).

**Source namespace:** Breakdown.Periodic.

**Factor the whole-space correction.** Under the stated assumptions, the whole-space correction operator factors through propagation, initial-data injection, shell interaction and shell restriction on a positive time piece of length at most one. Source: Breakdown.Periodic.r3ChainEq in Breakdown.Torus.ChainR3, line 144. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainR3.lean#L144).

### Breakdown.Torus.ChainTorus

Factors each periodic linearized time-piece interaction through the same shell space at its shrinking scale.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ChainTorus.Internal.

**Formula for diagonal sequence operator.** With the stated hypotheses, diagonal sequence operator obeys the exact identity `seqOp A = T₀`. Source: Breakdown.Periodic.ChainTorus.Internal.seqOp_eq_of in Breakdown.Torus.ChainTorus, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L17).

**Formula for time-piece extension.** With the stated hypotheses, time-piece extension obeys the exact identity `extendPiece f σ = f (projIcc 0 L hL σ)`. Source: Breakdown.Periodic.ChainTorus.Internal.extend_eq in Breakdown.Torus.ChainTorus, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L26).

**Scalar-weighted time piece.** A weighted time piece multiplies a fixed periodic Fourier vector by a continuous scalar time weight. Source: Breakdown.Periodic.ChainTorus.Internal.weightedPiece in Breakdown.Torus.ChainTorus, line 31. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L31).

**Periodic piece as a weighted sum.** Periodic time piece obeys the summation identity `A.torusPiece μ n = ∑ l, weightedPiece (A.weight n l) ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ (A.field n l)))`. Source: Breakdown.Periodic.ChainTorus.Internal.torusPiece_eq_sum in Breakdown.Torus.ChainTorus, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L34).

**Formula for periodic shell interaction.** With the stated hypotheses, periodic shell interaction obeys the exact identity `lambdaTorus φ hφ b μ τ ζ = -((μ ^ (-(1 / 4 : ℝ))) • heat (μ * τ - μ * σ) (forceV (μ * σ) (fun x => (advectShell φ hφ b ζ : Space → Space) (simCoord μ x))))`. Source: Breakdown.Periodic.ChainTorus.Internal.lambdaTorus_eq_heat in Breakdown.Torus.ChainTorus, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L40).

**Continuity of periodic shell interaction.** With the stated hypotheses, periodic shell interaction is continuous on the domain specified by `ContinuousOn (fun τ => lambdaTorus φ hφ b μ τ ζ) (Ioi 0)`. Source: Breakdown.Periodic.ChainTorus.Internal.lambdaTorus_continuousOn in Breakdown.Torus.ChainTorus, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L48).

**Admissibility of the shell scale.** With the stated hypotheses, the scale and support radius satisfy the shell-geometry constraints in `IsShellScale (stepScale T lam n) b`. Source: Breakdown.Periodic.ChainTorus.Internal.isShellScale_step in Breakdown.Torus.ChainTorus, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L65).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `∀ g n, ((torusLambda A T lam).comp (torusRestrict (1 - lam) b T lam)) g n = ((2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n) (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (A.torusPiece (stepScale T lam n) n)) (g n)`. Source: Breakdown.Periodic.ChainTorus.Internal.chain_apply in Breakdown.Torus.ChainTorus, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L72).

**Source namespace:** Breakdown.Periodic.

**Factor the periodic correction.** Under the stated assumptions, the periodic correction operator factors through propagation, initial-data injection, shell interaction and shell restriction when the support fits inside the shrinking cell. Source: Breakdown.Periodic.torusChainEq in Breakdown.Torus.ChainTorus, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ChainTorus.lean#L157).

### Breakdown.Torus.CoefCalculus

Derives the periodic Fourier rules for first derivatives, the Laplacian and pressure gradients by integration over the unit cell.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CoefCalculus.Internal.

**Formula for coordinate unit vector.** Coordinate unit vector obeys the exact identity `WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) y) = WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) y) + unitVector i`. Source: Breakdown.Periodic.CoefCalculus.Internal.toLp_insertNth_one in Breakdown.Torus.CoefCalculus, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L12).

**Formula for unit cell.** Unit cell obeys the exact identity `cell = (WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹' Icc 0 1`. Source: Breakdown.Periodic.CoefCalculus.Internal.cell_eq_preimage in Breakdown.Torus.CoefCalculus, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L20).

**Zero-parameter formula for integral.** With the stated hypotheses, integral has the zero-parameter identity `∫ x in cell, F' x (unitVector i) = 0`. Source: Breakdown.Periodic.CoefCalculus.Internal.integral_cell_eq_zero in Breakdown.Torus.CoefCalculus, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L24).

**Compactness of unit cell.** Unit cell is compact, as asserted by `IsCompact cell`. Source: Breakdown.Periodic.CoefCalculus.Internal.isCompact_cell in Breakdown.Torus.CoefCalculus, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L75).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k j = k j`. Source: Breakdown.Periodic.CoefCalculus.Internal.freq_apply in Breakdown.Torus.CoefCalculus, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L80).

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ (freq k) (unitVector i) = k i`. Source: Breakdown.Periodic.CoefCalculus.Internal.inner_freq_unitVector in Breakdown.Torus.CoefCalculus, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L83).

**Linear Fourier phase.** The Fourier phase map is `−2πi` times the real pairing with the lattice frequency. Source: Breakdown.Periodic.CoefCalculus.Internal.charL in Breakdown.Torus.CoefCalculus, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L87).

**Formula for Fourier character.** Fourier character obeys the exact identity `character k = fun x => Complex.exp (charL k x)`. Source: Breakdown.Periodic.CoefCalculus.Internal.character_eq in Breakdown.Torus.CoefCalculus, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L90).

**Derivative of Fourier character.** Fourier character has the Fréchet derivative specified by `HasFDerivAt (character k) (character k x • charL k) x`. Source: Breakdown.Periodic.CoefCalculus.Internal.hasFDerivAt_character in Breakdown.Torus.CoefCalculus, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L94).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character k)`. Source: Breakdown.Periodic.CoefCalculus.Internal.continuous_character in Breakdown.Torus.CoefCalculus, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L99).

**Formula for Fourier phase map.** Fourier phase map obeys the exact identity `charL k (unitVector i) = -(2 * π * Complex.I * (k i : ℂ))`. Source: Breakdown.Periodic.CoefCalculus.Internal.charL_unitVector in Breakdown.Torus.CoefCalculus, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L102).

**Formula for Fourier character.** Fourier character obeys the exact identity `character k (x + unitVector i) = character k x`. Source: Breakdown.Periodic.CoefCalculus.Internal.character_add_unitVector in Breakdown.Torus.CoefCalculus, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L106).

**Derivative formula for integral.** With the stated hypotheses, the derivative calculation gives `∫ x in cell, character k x • h' x (unitVector i) = (2 * π * Complex.I * (k i : ℂ)) • ∫ x in cell, character k x • h x`. Source: Breakdown.Periodic.CoefCalculus.Internal.integral_character_smul_deriv in Breakdown.Torus.CoefCalculus, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L116).

**Bounded complexification.** Complexification is packaged as a real continuous linear map from real vectors to complex Fourier coefficients. Source: Breakdown.Periodic.CoefCalculus.Internal.complexifyL in Breakdown.Torus.CoefCalculus, line 153. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L153).

**Formula for bounded complexification.** Bounded complexification obeys the exact identity `complexifyL x = complexify x`. Source: Breakdown.Periodic.CoefCalculus.Internal.complexifyL_apply in Breakdown.Torus.CoefCalculus, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L159).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (fun x => ∑ j, φ j x) k = ∑ j, freqTrCoef (φ j) k`. Source: Breakdown.Periodic.CoefCalculus.Internal.freqTrCoef_sum in Breakdown.Torus.CoefCalculus, line 161. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L161).

**Source namespace:** Breakdown.Periodic.

**Fourier coefficients of derivatives.** Under the stated assumptions, a C¹ periodic coordinate derivative multiplies the original Fourier coefficient by 2πi times that frequency coordinate. Source: Breakdown.Periodic.coefDeriv in Breakdown.Torus.CoefCalculus, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L178).

**Fourier coefficients of the Laplacian.** Under the stated assumptions, the Laplacian of a C² periodic field multiplies each Fourier coefficient by −4π² times the squared frequency norm. Source: Breakdown.Periodic.coefSumSecondPartials in Breakdown.Torus.CoefCalculus, line 187. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L187).

**Fourier coefficients of a gradient.** Under the stated assumptions, the gradient of a C¹ periodic scalar field has Fourier coefficient 2πi times its scalar coefficient and frequency vector. Source: Breakdown.Periodic.coefGradient in Breakdown.Torus.CoefCalculus, line 219. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CoefCalculus.lean#L219).

### Breakdown.Torus.CompareChain

Computes repeated propagation between time pieces as an explicit heat evolution with the required dilation and geometric weight.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareChain.Internal.

**Formula for propagation chain.** Propagation chain obeys the exact identity `shiftChain B m m = ContinuousLinearMap.id ℝ X`. Source: Breakdown.Periodic.CompareChain.Internal.shiftChain_self in Breakdown.Torus.CompareChain, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L12).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `shiftChain B m (n + 1) = (B n).comp (shiftChain B m n)`. Source: Breakdown.Periodic.CompareChain.Internal.shiftChain_succ in Breakdown.Torus.CompareChain, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L18).

**Formula for time-piece endpoint.** With the stated hypotheses, time-piece endpoint obeys the exact identity `pieceEnd L z = z ⟨L, hL, le_rfl⟩`. Source: Breakdown.Periodic.CompareChain.Internal.pieceEnd_apply in Breakdown.Torus.CompareChain, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L24).

**Formula for whole-space propagation step.** With the stated hypotheses, whole-space propagation step obeys the exact identity `r3Step F P k θ n z s = θ⁻¹ • F.G s (F.D (Real.exp (-(P / k))) (pieceEnd (MildFramework.stepLength P k) z))`. Source: Breakdown.Periodic.CompareChain.Internal.r3Step_apply in Breakdown.Torus.CompareChain, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L30).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `∀ (j : ℕ) (s : Icc (0 : ℝ) L), shiftChain B m (m + j + 1) y s = c ^ (j + 1) • Ψ j s (pieceEnd L y)`. Source: Breakdown.Periodic.CompareChain.Internal.chain_apply in Breakdown.Torus.CompareChain, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L39).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `shiftChain (r3Step F P k θ) m (m + j + 1) y s = (θ⁻¹) ^ (j + 1) • F.D (Real.exp (-(P / k)) ^ (j + 1)) (F.G (Real.exp (-(P / k)) ^ (j + 1) * s + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (j + 1)) (pieceEnd (MildFramework.stepLength P k) y))`. Source: Breakdown.Periodic.CompareChain.Internal.r3Chain in Breakdown.Torus.CompareChain, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L59).

**Formula for periodic propagation step.** With the stated hypotheses, periodic propagation step obeys the exact identity `torusStep hK T lam θ hT hT1 hl hl1 n z s = (lam ^ (1 / 4 : ℝ) / θ) • heat (stepScale T lam (n + 1) * s) (pieceEnd (1 - lam) z)`. Source: Breakdown.Periodic.CompareChain.Internal.torusStep_apply in Breakdown.Torus.CompareChain, line 141. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L141).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `shiftChain (torusStep hK T lam θ hT hT1 hl hl1) m (m + j + 1) y s = (lam ^ (1 / 4 : ℝ) / θ) ^ (j + 1) • heat (stepScale T lam m * (lam ^ (j + 1) * s + lam - lam ^ (j + 1))) (pieceEnd (1 - lam) y)`. Source: Breakdown.Periodic.CompareChain.Internal.torusChain in Breakdown.Torus.CompareChain, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L152).

**Source namespace:** Breakdown.Periodic.

**Whole-space chain formula.** Under the stated assumptions, repeated whole-space propagation is an explicit heat evolution followed by dilation and the factor θ raised to the negative number of steps. Source: Breakdown.Periodic.r3ChainFormula in Breakdown.Torus.CompareChain, line 192. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L192).

**Periodic chain formula.** Under the stated assumptions, repeated periodic propagation has the geometric factor (λ^(1/4)/θ)^(j+1) and the specified accumulated heat time. Source: Breakdown.Periodic.torusChainFormula in Breakdown.Torus.CompareChain, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareChain.lean#L197).

### Breakdown.Torus.CompareDilate

Checks how dilation changes transplantation and preserves test fields, then controls shell advection in L³ᐟ².

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareDilate.Internal.

**Derivative formula for shell scaling.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun z => r • f (r • z)) y v = (r * r) • fderiv ℝ f (r • y) v`. Source: Breakdown.Periodic.CompareDilate.Internal.fderiv_dilate in Breakdown.Torus.CompareDilate, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareDilate.lean#L13).

**Source namespace:** Breakdown.Periodic.

**Transplantation under dilation.** Under the stated assumptions, transplanting at scale μ agrees with first dilating by positive c and transplanting at scale μc. Source: Breakdown.Periodic.transplantDilate in Breakdown.Torus.CompareDilate, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareDilate.lean#L23).

**Dilation preserves test fields.** Under the stated assumptions, positive dilation preserves smooth compactly supported solenoidal test fields. Source: Breakdown.Periodic.dilateTest in Breakdown.Torus.CompareDilate, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareDilate.lean#L36).

**Size and support of shell advection.** Under the stated assumptions, shell advection has L³ᐟ² norm bounded by the product of the test-field embedding and shell-data norms and vanishes almost everywhere outside the support ball. Source: Breakdown.Periodic.advectShellBounds in Breakdown.Torus.CompareDilate, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareDilate.lean#L59).

### Breakdown.Torus.CompareEntryR3

Computes each whole-space interaction entry after propagation and restriction to the shell.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareEntryR3.Internal.

**Formula for spatial shell interaction.** With the stated hypotheses, whole-space shell interaction obeys the exact identity `lambdaR3 φ hφ b τ ζ = -(Freq.heatDivFree τ (advectShell φ hφ b ζ))`. Source: Breakdown.Periodic.CompareEntryR3.Internal.lambdaR3_apply in Breakdown.Torus.CompareEntryR3, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L12).

**Bound for spatial shell interaction.** With the stated hypotheses, whole-space shell interaction admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ‖lambdaR3 φ hφ b τ‖ ≤ C * ‖Freq.embedX φ‖ * τ ^ (-(3 / 4 : ℝ))`. Source: Breakdown.Periodic.CompareEntryR3.Internal.lambdaR3_opNorm_le in Breakdown.Torus.CompareEntryR3, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L16).

**Continuity of spatial shell interaction.** With the stated hypotheses, whole-space shell interaction is continuous on the domain specified by `ContinuousOn (fun τ => lambdaR3 φ hφ b τ ζ) (Ioi 0)`. Source: Breakdown.Periodic.CompareEntryR3.Internal.lambdaR3_continuousOn in Breakdown.Torus.CompareEntryR3, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L26).

**Time integrability of integrand.** With the stated hypotheses, integrand is integrable over the time interval in `IntervalIntegrable (fun σ => extendPiece w σ • lambdaR3 φ hφ b (u - σ) (extendPiece ζ σ)) volume 0 u`. Source: Breakdown.Periodic.CompareEntryR3.Internal.integrand_intervalIntegrable in Breakdown.Torus.CompareEntryR3, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L31).

**Map a finite interaction sum.** With the stated hypotheses, extended time piece obeys the summation identity `M (∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ • lambdaR3 (A.field m l) (A.isTest m l) b (u - σ) (extendPiece (ζ m) σ)) = ∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ • M (lambdaR3 (A.field m l) (A.isTest m l) b (u - σ) (extendPiece (ζ m) σ))`. Source: Breakdown.Periodic.CompareEntryR3.Internal.map_lambda_sum in Breakdown.Torus.CompareEntryR3, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L45).

**Formula for time-piece endpoint.** With the stated hypotheses, time-piece endpoint obeys the exact identity `pieceEnd T f = f ⟨T, hT, le_rfl⟩`. Source: Breakdown.Periodic.CompareEntryR3.Internal.pieceEnd_eq in Breakdown.Torus.CompareEntryR3, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L58).

**Formula for propagation chain.** Propagation chain obeys the exact identity `shiftChain B m m = ContinuousLinearMap.id ℝ X`. Source: Breakdown.Periodic.CompareEntryR3.Internal.shiftChain_self in Breakdown.Torus.CompareEntryR3, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L62).

**Propagating one interaction entry.** With the stated hypotheses, extended time piece obeys the exact identity `restrictR3 b (shiftChain (r3Step F P k θ) m (m + i + 1) y s) = (θ⁻¹) ^ (i + 1) • ∑ l, ∫ σ in (0 : ℝ)..MildFramework.stepLength P k, extendPiece (A.weight m l) σ • restrictR3 b (Freq.dilX (Real.exp (-(P / k)) ^ (i + 1)) (-(Freq.heatDivFree (1 - σ - Real.exp (-(P / k)) ^ (i + 1) * (1 - s)) (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ)))))`. Source: Breakdown.Periodic.CompareEntryR3.Internal.succ_entry in Breakdown.Torus.CompareEntryR3, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L67).

**Source namespace:** Breakdown.Periodic.

**Propagated whole-space interaction.** Under the stated assumptions, a propagated whole-space interaction is the explicit rescaled heat integral, integrated to the current time for j = 0 and to L for later entries. Source: Breakdown.Periodic.r3EntryFormula in Breakdown.Torus.CompareEntryR3, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryR3.lean#L130).

### Breakdown.Torus.CompareEntryTorus

Computes the corresponding periodic interaction entry with its heat time and scale factors.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareEntryTorus.Internal.

**Formula for propagation chain.** Propagation chain obeys the exact identity `shiftChain B m m = ContinuousLinearMap.id ℝ X`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.shiftChain_self in Breakdown.Torus.CompareEntryTorus, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L15).

**Integrability of the interaction.** With the stated hypotheses, extended time piece is integrable over the time interval in `IntervalIntegrable (fun σ => extendPiece (A.weight n l) σ • lambdaTorus (A.field n l) (A.isTest n l) b μ (u - σ) (extendPiece ζ σ)) volume 0 u`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.lambda_integrable in Breakdown.Torus.CompareEntryTorus, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L21).

**Formula for heat evolution.** With the stated hypotheses, heat evolution obeys the exact identity `heat (μ * t) (lambdaTorus φ hφ b μ τ ζ) = lambdaTorus φ hφ b μ (t + τ) ζ`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.heat_lambdaTorus in Breakdown.Torus.CompareEntryTorus, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L42).

**Formula for geometric scalar factor.** With the stated hypotheses, geometric scalar factor obeys the exact identity `(lam ^ (1 / 4 : ℝ) / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.scalar_split in Breakdown.Torus.CompareEntryTorus, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L49).

**Formula for periodic shell restriction.** With the stated hypotheses, periodic shell restriction obeys the exact identity `w • ((restrictTorus μ' b).comp (c • heat (μ * t))) (lambdaTorus φ hφ b μ τ ζ) = θ' • (w • restrictTorus μ' b (d • -((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ' (advectShell φ hφ b ζ))))`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.entry_pointwise in Breakdown.Torus.CompareEntryTorus, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L54).

**Formula for time-piece endpoint.** With the stated hypotheses, time-piece endpoint obeys the exact identity `pieceEnd L f = f ⟨L, h, le_rfl⟩`. Source: Breakdown.Periodic.CompareEntryTorus.Internal.pieceEnd_eq in Breakdown.Torus.CompareEntryTorus, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L65).

**Source namespace:** Breakdown.Periodic.

**Propagated periodic interaction.** Under the stated assumptions, a propagated periodic interaction is the explicit geometric-weighted heat integral, integrated to the current time for j = 0 and to L for later entries. Source: Breakdown.Periodic.torusEntryFormula in Breakdown.Torus.CompareEntryTorus, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareEntryTorus.lean#L73).

### Breakdown.Torus.CompareFinal

Combines the interaction comparison and initial-data comparison into smallness of the complete comparison operator.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Small difference of correction chains.** Under the stated assumptions, both the interaction and initial-data comparison chains become small in operator norm as T tends to zero under the stated geometric and finite-dimensional assumptions. Source: Breakdown.Periodic.comparisonSmall_of_parts in Breakdown.Torus.CompareFinal, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFinal.lean#L24).

### Breakdown.Torus.CompareFrame

Compares the shell restrictions in different scales, keeping the L² gradient and L⁶ velocity normalizations.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareFrame.Internal.

**Scaling formula for Lᵖ norm.** With the stated hypotheses, Lᵖ norm obeys the scalar-scaling identity `eLpNorm (fun y => g (s • y)) p volume = ENNReal.ofReal (s ^ 3)⁻¹ ^ (1 / p).toReal * eLpNorm g p volume`. Source: Breakdown.Periodic.CompareFrame.Internal.eLpNorm_comp_smul in Breakdown.Torus.CompareFrame, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L13).

**Norm of an almost-everywhere scaling.** With the stated hypotheses, scaled Lᵖ norm obeys the scalar-scaling identity `‖F‖ = ‖k‖ * ((s ^ 3)⁻¹) ^ (1 / p).toReal * ‖G‖`. Source: Breakdown.Periodic.CompareFrame.Internal.norm_of_ae_comp_smul in Breakdown.Torus.CompareFrame, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L26).

**Subtract two rescaled representatives.** With the stated hypotheses, change of shell scale has the almost-everywhere representation `((A1 - B1 : Lp Space p (volume : Measure Space)) : Space → Space) =ᵐ[volume] fun y => k • ((A2 - B2 : Lp Space p (volume : Measure Space)) : Space → Space) (s • y)`. Source: Breakdown.Periodic.CompareFrame.Internal.sub_ae_comp_smul in Breakdown.Torus.CompareFrame, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L35).

**Equivalent forms of closed ball.** With the stated hypotheses, closed ball has the equivalent characterizations `s • y ∈ Metric.closedBall (0 : Space) (s * b) ↔ y ∈ Metric.closedBall (0 : Space) b`. Source: Breakdown.Periodic.CompareFrame.Internal.mem_closedBall_smul in Breakdown.Torus.CompareFrame, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L48).

**Formula for scaling.** With the stated hypotheses, scaling obeys the exact identity `k0 • (Metric.closedBall (0 : Space) b).indicator f y = k • (Metric.closedBall (0 : Space) (s * b)).indicator g (s • y)`. Source: Breakdown.Periodic.CompareFrame.Internal.indicator_scale in Breakdown.Torus.CompareFrame, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L53).

**Formula for periodic shell restriction.** With the stated hypotheses, periodic shell restriction obeys the exact identity `(restrictTorus μ b z).1 j = Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))))`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictTorus_fst in Breakdown.Torus.CompareFrame, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L63).

**Formula for periodic shell restriction.** With the stated hypotheses, periodic shell restriction obeys the exact identity `(restrictTorus μ b z).2 = Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))))`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictTorus_snd in Breakdown.Torus.CompareFrame, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L70).

**The periodic gradient representative.** With the stated hypotheses, periodic shell restriction has the almost-everywhere representation `((restrictTorus μ b z).1 j : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y)))`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictTorus_fst_ae in Breakdown.Torus.CompareFrame, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L77).

**The periodic velocity representative.** With the stated hypotheses, periodic shell restriction has the almost-everywhere representation `((restrictTorus μ b z).2 : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y)))`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictTorus_snd_ae in Breakdown.Torus.CompareFrame, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L84).

**Formula for whole-space restriction.** Whole-space restriction obeys the exact identity `(restrictR3 b v).1 j = cutLp 2 b (Freq.partialX j v)`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictR3_fst in Breakdown.Torus.CompareFrame, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L91).

**Formula for whole-space restriction.** Whole-space restriction obeys the exact identity `(restrictR3 b v).2 = cutLp 6 b (Freq.velocity v)`. Source: Breakdown.Periodic.CompareFrame.Internal.restrictR3_snd in Breakdown.Torus.CompareFrame, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L94).

**Admissibility of the shell scale.** With the stated hypotheses, the scale and support radius satisfy the shell-geometry constraints in `IsShellScale (μ * c) b`. Source: Breakdown.Periodic.CompareFrame.Internal.shellScale_mul in Breakdown.Torus.CompareFrame, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L97).

**Volume and shell normalization.** With the stated hypotheses, volume scaling factor obeys the exact identity `((Real.sqrt c ^ 3)⁻¹) ^ q = c ^ (-(3 / 2 * q))`. Source: Breakdown.Periodic.CompareFrame.Internal.sqrt_cube_rpow in Breakdown.Torus.CompareFrame, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L106).

**Gradient under a frame change.** With the stated hypotheses, gradient component obeys the exact identity `‖(restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).1 j‖ = c ^ (1 / 4 : ℝ) * ‖(restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).1 j‖`. Source: Breakdown.Periodic.CompareFrame.Internal.grad_component in Breakdown.Torus.CompareFrame, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L114).

**Velocity under a frame change.** With the stated hypotheses, velocity component obeys the exact identity `‖(restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).2‖ = c ^ (1 / 4 : ℝ) * ‖(restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).2‖`. Source: Breakdown.Periodic.CompareFrame.Internal.velocity_component in Breakdown.Torus.CompareFrame, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L164).

**Source namespace:** Breakdown.Periodic.

**Norm under a change of scale.** Under the stated assumptions, rescaling a shell restriction by 0 < c ≤ 1 changes its norm by at most the factor c^(1/4). Source: Breakdown.Periodic.frameChange in Breakdown.Torus.CompareFrame, line 216. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareFrame.lean#L216).

### Breakdown.Torus.CompareHeatDivFree

Proves the time-shift and continuity rules for the whole-space heat evolution followed by the divergence-free projection.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareHeatDivFree.Internal.

**Bound for gradient heat multiplier.** With the stated hypotheses, gradient heat multiplier satisfies the quantitative estimate `‖Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace‖ ≤ 1 + 1 / τ`. Source: Breakdown.Periodic.CompareHeatDivFree.Internal.phiFactor_smul_norm_le in Breakdown.Torus.CompareHeatDivFree, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L16).

**Representative of gradient heat operator.** With the stated hypotheses, gradient heat operator has the almost-everywhere representation `(Freq.fieldOp id (fun ξ => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) f : Space → Freq.CSpace) =ᵐ[volume] fun ξ => Freq.phiFactor τ ξ • (f : Space → Freq.CSpace) ξ`. Source: Breakdown.Periodic.CompareHeatDivFree.Internal.phiOp_ae in Breakdown.Torus.CompareHeatDivFree, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L38).

**Formula for heat multiplier.** With the stated hypotheses, heat multiplier obeys the exact identity `Freq.phiFactor τ ξ * Freq.heatFactor t ξ = Freq.phiFactor (t + τ) ξ`. Source: Breakdown.Periodic.CompareHeatDivFree.Internal.heatFactor_mul_phiFactor in Breakdown.Torus.CompareHeatDivFree, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L47).

**Formula for gradient heat operator.** With the stated hypotheses, gradient heat operator obeys the exact identity `Freq.fieldOp id (fun ξ => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) (Freq.heatL2 t f) = Freq.fieldOp id (fun ξ => Freq.phiFactor (t + τ) ξ • ContinuousLinearMap.id ℝ Freq.CSpace) f`. Source: Breakdown.Periodic.CompareHeatDivFree.Internal.phiOp_heat in Breakdown.Torus.CompareHeatDivFree, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L54).

**Formula for gradient heat operator.** With the stated hypotheses, gradient heat operator obeys the exact identity `Freq.phiX τ (Freq.heatX t ψ) = Freq.phiX (t + τ) ψ`. Source: Breakdown.Periodic.CompareHeatDivFree.Internal.phiX_heat in Breakdown.Torus.CompareHeatDivFree, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L63).

**Source namespace:** Breakdown.Periodic.

**Heat composition after projection.** Under the stated assumptions, free heat evolution for nonnegative time composes with positive-time projected heat flow by adding the two times. Source: Breakdown.Periodic.heatDivFreeShift in Breakdown.Torus.CompareHeatDivFree, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L73).

**Continuity of projected heat flow.** Under the stated assumptions, projected heat flow is strongly continuous for positive elapsed time. Source: Breakdown.Periodic.heatDivFreeContinuous in Breakdown.Torus.CompareHeatDivFree, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareHeatDivFree.lean#L81).

### Breakdown.Torus.CompareInvSeries

Writes the inverse of a contractive sequence shift as a finite sum of propagation chains at each index.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareInvSeries.Internal.

**Formula for resolvent inverse.** With the stated hypotheses, resolvent inverse obeys the exact identity `Ring.inverse (1 - T) y - T (Ring.inverse (1 - T) y) = y`. Source: Breakdown.Periodic.CompareInvSeries.Internal.inverse_fixed in Breakdown.Torus.CompareInvSeries, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareInvSeries.lean#L12).

**Formula for propagation chain.** Propagation chain obeys the exact identity `shiftChain B n n = ContinuousLinearMap.id ℝ X`. Source: Breakdown.Periodic.CompareInvSeries.Internal.shiftChain_self in Breakdown.Torus.CompareInvSeries, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareInvSeries.lean#L19).

**Formula for propagation chain.** With the stated hypotheses, propagation chain obeys the exact identity `shiftChain B m (n + 1) = (B n).comp (shiftChain B m n)`. Source: Breakdown.Periodic.CompareInvSeries.Internal.shiftChain_succ_of_ne in Breakdown.Torus.CompareInvSeries, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareInvSeries.lean#L25).

**Source namespace:** Breakdown.Periodic.

**Entries of the inverse shift.** Under the stated assumptions, the inverse of a sequence shift of norm less than one has entries given by finite sums of propagation chains. Source: Breakdown.Periodic.invSeriesEntry in Breakdown.Torus.CompareInvSeries, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareInvSeries.lean#L34).

**Growth of propagation chains.** Under the stated assumptions, steps uniformly bounded by a nonnegative constant C give a chain bound C^(n−m) whenever m ≤ n. Source: Breakdown.Periodic.shiftChainNorm in Breakdown.Torus.CompareInvSeries, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareInvSeries.lean#L61).

### Breakdown.Torus.CompareLambda

Expands the whole-space and periodic interaction operators into weighted time convolutions.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareLambda.Internal.

**Formula for time convolution.** Time convolution obeys the exact identity `(∑ l ∈ u, T l) ζ s = ∑ l ∈ u, T l ζ s`. Source: Breakdown.Periodic.CompareLambda.Internal.sum_pieceConv_apply in Breakdown.Torus.CompareLambda, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambda.lean#L14).

**Source namespace:** Breakdown.Periodic.

**Whole-space interaction formula.** Under the stated assumptions, on a time piece with 0 < L ≤ 1 the whole-space shell interaction is the prescribed weighted time convolution. Source: Breakdown.Periodic.r3LambdaFormula in Breakdown.Torus.CompareLambda, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambda.lean#L26).

**Periodic interaction formula.** Under the stated assumptions, on a time piece with 0 < L ≤ 1 and valid shell scale the periodic shell interaction is the prescribed weighted time convolution. Source: Breakdown.Periodic.torusLambdaFormula in Breakdown.Torus.CompareLambda, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambda.lean#L52).

### Breakdown.Torus.CompareLambdaAssembly

Turns small errors on a finite window and a geometric tail estimate into an operator-norm comparison.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareLambdaAssembly.Internal.

**Bound for free time piece.** With the stated hypotheses, free time piece satisfies the quantitative estimate `‖H.pieceFree L‖ ≤ 1`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.pieceFree_norm_le in Breakdown.Torus.CompareLambdaAssembly, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L12).

**Bound for time-piece endpoint.** Time-piece endpoint satisfies the quantitative estimate `‖(pieceEnd L : Piece Y L →L[ℝ] Y)‖ ≤ 1`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.pieceEnd_norm_le in Breakdown.Torus.CompareLambdaAssembly, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L22).

**Bound for scaled field.** With the stated hypotheses, scaled field satisfies the quantitative estimate `‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.scaled_step_norm_le in Breakdown.Torus.CompareLambdaAssembly, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L31).

**Formula for periodic flow.** With the stated hypotheses, periodic flow obeys the exact identity `((torusRestrict (1 - lam) b T lam).comp ((Ring.inverse (1 - torusShift hK T lam θ hT hT1 hl hl1)).comp (torusLambda A T lam)) ζ) n s = ∑ m ∈ Finset.range (n + 1), torusEntry hK T lam θ hT hT1 hl hl1 b A ζ m n s`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.torus_apply in Breakdown.Torus.CompareLambdaAssembly, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L37).

**Formula for whole-space flow.** With the stated hypotheses, whole-space flow obeys the exact identity `((r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Lambda A)) ζ) n s = ∑ m ∈ Finset.range (n + 1), r3Entry F P k θ b A ζ m n s`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.r3_apply in Breakdown.Torus.CompareLambdaAssembly, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L67).

**Choose a geometric tail cutoff.** A positive tolerance admits an index beyond which the geometric tail of the propagation comparison is sufficiently small. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.geometric_choice in Breakdown.Torus.CompareLambdaAssembly, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L97).

**Formula for interaction comparison.** Interaction comparison obeys the exact identity `((f - g) ζ) n s = (f ζ) n s - (g ζ) n s`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.sub_entry in Breakdown.Torus.CompareLambdaAssembly, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L115).

**Operator norm from entry bounds.** With the stated hypotheses, operator norm satisfies the quantitative estimate `‖D‖ ≤ δ`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.opNorm_le_of_entries in Breakdown.Torus.CompareLambdaAssembly, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L118).

**Bound for geometric tail.** With the stated hypotheses, geometric tail satisfies the estimate `‖a - b‖ ≤ c * r ^ j * z`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.tail_term in Breakdown.Torus.CompareLambdaAssembly, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L145).

**Bound for finite comparison window.** With the stated hypotheses, finite comparison window satisfies the estimate `‖a - b‖ ≤ c * r ^ j * z`. Source: Breakdown.Periodic.CompareLambdaAssembly.Internal.window_term in Breakdown.Torus.CompareLambdaAssembly, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareLambdaAssembly.lean#L157).

### Breakdown.Torus.CompareSeedAssembly

Compares the initial-data propagators by a finite-dimensional basis argument, a finite window and a geometric tail.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareSeedAssembly.Internal.

**Choose one bound below a finite family.** For positive f and i in the finite index set, the reciprocal of one plus the sum of the reciprocals is at most f(i). Source: Breakdown.Periodic.CompareSeedAssembly.Internal.inv_sum_le in Breakdown.Torus.CompareSeedAssembly, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L13).

**Reduce operator bounds to a basis.** Bounds on the images of a finite-dimensional basis control the operator norm through one common finite constant. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.basis_reduce in Breakdown.Torus.CompareSeedAssembly, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L21).

**Formula for periodic flow.** With the stated hypotheses, periodic flow obeys the exact identity `torusRestrict L b T lam g n s = restrictTorus (stepScale T lam n) b (g n s)`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.torus_slot in Breakdown.Torus.CompareSeedAssembly, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L50).

**Formula for whole-space flow.** With the stated hypotheses, whole-space flow obeys the exact identity `r3Restrict L b g n s = restrictR3 b (g n s)`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.r3_slot in Breakdown.Torus.CompareSeedAssembly, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L60).

**Uniform bound for transplantation.** With the stated hypotheses, transplantation admits the uniform bound stated in `∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, IsShellScale T b → ‖(T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))‖ ≤ M`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.transplant_bound in Breakdown.Torus.CompareSeedAssembly, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L69).

**Bound for initial-data comparison.** With the stated hypotheses, initial-data comparison satisfies the quantitative estimate `Real.sqrt T * b ≤ 1 / 8`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.sqrt_mul_le in Breakdown.Torus.CompareSeedAssembly, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L83).

**Bound for sequence entry.** With the stated hypotheses, sequence entry satisfies the quantitative estimate `‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n • heat (T * (lam ^ n * s + 1 - lam ^ n)) ((T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e)))) - restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) (J e)))‖ ≤ η`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.slot_le_of_freeHeat in Breakdown.Torus.CompareSeedAssembly, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L88).

**Bound for sequence entry.** With the stated hypotheses, sequence entry satisfies the quantitative estimate `‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n • heat (T * (lam ^ n * s + 1 - lam ^ n)) z) - restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) x))‖ ≤ (Ct * M + Cr * ‖x‖) * (lam ^ (1 / 4 : ℝ) / θ) ^ n`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.slot_le_geometric in Breakdown.Torus.CompareSeedAssembly, line 123. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L123).

**Bound for geometric tail.** With the stated hypotheses, geometric tail satisfies the quantitative estimate `K * q ^ n ≤ η`. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.geometric_tail_le in Breakdown.Torus.CompareSeedAssembly, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L155).

**Uniform comparison for a fixed datum.** For a fixed datum in the test-field lift, the initial-data comparison becomes uniformly small over all sequence entries and piece times when T is sufficiently small. Source: Breakdown.Periodic.CompareSeedAssembly.Internal.slot_bound in Breakdown.Torus.CompareSeedAssembly, line 162. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedAssembly.lean#L162).

### Breakdown.Torus.CompareSeedEntry

Computes the propagated initial-data contribution at each time-piece index.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareSeedEntry.Internal.

**Bound for free time piece.** With the stated hypotheses, free time piece satisfies the quantitative estimate `‖H.pieceFree T‖ ≤ 1`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.norm_pieceFree_le in Breakdown.Torus.CompareSeedEntry, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L13).

**Bound for time-piece endpoint.** Time-piece endpoint satisfies the quantitative estimate `‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.norm_pieceEnd_le in Breakdown.Torus.CompareSeedEntry, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L24).

**Formula for initial-data injection.** With the stated hypotheses, initial-data injection obeys the exact identity `seqSeed A e n = if n = 0 then A e else 0`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.seqSeed_apply in Breakdown.Torus.CompareSeedEntry, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L33).

**Formula for sequence shift.** With the stated hypotheses, sequence shift obeys the exact identity `∀ g n, seqShift B g n = if n = 0 then 0 else B (n - 1) (g (n - 1))`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.seqShift_apply in Breakdown.Torus.CompareSeedEntry, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L46).

**Formula for resolvent inverse.** With the stated hypotheses, resolvent inverse obeys the exact identity `(Ring.inverse (1 - seqShift B) (seqSeed A e)) n = shiftChain B 0 n (A e)`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.inverse_seed in Breakdown.Torus.CompareSeedEntry, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L51).

**The initial chain is the identity.** Propagation chain has the zero-parameter identity `shiftChain B 0 0 = ContinuousLinearMap.id ℝ X`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.shiftChain_zero_zero in Breakdown.Torus.CompareSeedEntry, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L63).

**Concatenate propagation chains.** Concatenated propagation obeys the addition identity `shiftChain B 0 (j + 1) = shiftChain B 0 (0 + j + 1)`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.shiftChain_zero_add in Breakdown.Torus.CompareSeedEntry, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L67).

**Formula for time-piece endpoint.** With the stated hypotheses, time-piece endpoint obeys the exact identity `pieceEnd L z = z ⟨L, hL, le_rfl⟩`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.pieceEnd_eval in Breakdown.Torus.CompareSeedEntry, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L71).

**Formula for whole-space flow.** With the stated hypotheses, whole-space flow obeys the exact identity `Freq.dilX μ (Freq.heatX (μ * s + lam - μ) w) = Freq.heatX (s + μ⁻¹ - 1) (Freq.dilX μ x)`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.r3_slot in Breakdown.Torus.CompareSeedEntry, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L77).

**Formula for periodic flow.** With the stated hypotheses, periodic flow obeys the exact identity `heat (T * (μ * s + lam - μ)) (heat (T * (1 - lam)) x) = heat (T * (μ * s + 1 - μ)) x`. Source: Breakdown.Periodic.CompareSeedEntry.Internal.torus_slot in Breakdown.Torus.CompareSeedEntry, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L101).

**Source namespace:** Breakdown.Periodic.

**Whole-space initial-data entries.** Under the stated assumptions, the inverse whole-space shift applied to initial data has the explicit θ⁻ⁿ heat-and-dilation formula at index n. Source: Breakdown.Periodic.r3SeedEntry in Breakdown.Torus.CompareSeedEntry, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L113).

**Periodic initial-data entries.** Under the stated assumptions, the inverse periodic shift applied to initial data has the explicit factor (λ^(1/4)/θ)^n and heat time T(λ^n s+1−λ^n). Source: Breakdown.Periodic.torusSeedEntry in Breakdown.Torus.CompareSeedEntry, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSeedEntry.lean#L157).

### Breakdown.Torus.CompareSplit

Separates a time integral into a regular part and a short endpoint interval with a three-quarter-power singularity.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareSplit.Internal.

**Integrability of the shifted power.** Translated power singularity is integrable over the time interval in `IntervalIntegrable (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) volume 0 u`. Source: Breakdown.Periodic.CompareSplit.Internal.rpow_sub_intervalIntegrable in Breakdown.Torus.CompareSplit, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSplit.lean#L12).

**The terminal singularity is integrable.** Terminal power singularity is integrable over the time interval in `IntervalIntegrable ((Ioi (u - ε)).indicator fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) volume 0 u`. Source: Breakdown.Periodic.CompareSplit.Internal.tail_intervalIntegrable in Breakdown.Torus.CompareSplit, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSplit.lean#L18).

**Bound for terminal power integral.** With the stated hypotheses, terminal power integral satisfies the quantitative estimate `∫ σ in (0 : ℝ)..u, (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ ≤ 4 * ε ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.CompareSplit.Internal.tail_integral_le in Breakdown.Torus.CompareSplit, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSplit.lean#L23).

**Source namespace:** Breakdown.Periodic.

**Split a singular time integral.** Under the stated assumptions, the regular and terminal parts of the time integral admit the bound a u + 4 c ε^(1/4). Source: Breakdown.Periodic.splitIntegralBound in Breakdown.Torus.CompareSplit, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareSplit.lean#L68).

### Breakdown.Torus.CompareStatements

Defines the propagation chains, their entries and the comparison propositions that assemble the periodic localization argument.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Propagation from one index to another.** The propagation chain is the identity when its source and target indices agree, and otherwise successively composes the intervening step operators. Source: Breakdown.Periodic.shiftChain in Breakdown.Torus.CompareStatements, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L10).

**One whole-space propagation step.** A whole-space propagation step takes the previous endpoint, applies the free step evolution and multiplies by `θ⁻¹`. Source: Breakdown.Periodic.r3Step in Breakdown.Torus.CompareStatements, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L15).

**One periodic propagation step.** A periodic propagation step evolves the previous endpoint in the next rescaled heat frame and multiplies by `λ^(1/4) / θ`. Source: Breakdown.Periodic.torusStep in Breakdown.Torus.CompareStatements, line 19. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L19).

**Whole-space interaction entry.** A whole-space entry propagates one interaction contribution from index `m` to `n` and restricts its value to the shell. Source: Breakdown.Periodic.r3Entry in Breakdown.Torus.CompareStatements, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L25).

**Periodic interaction entry.** A periodic entry propagates one interaction contribution to index `n` and restricts it to the shell at that index’s scale. Source: Breakdown.Periodic.torusEntry in Breakdown.Torus.CompareStatements, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L30).

**Entries of the inverse shift.** This proposition requires that the inverse of a sequence shift of norm less than one has entries given by finite sums of propagation chains. Source: Breakdown.Periodic.InvSeriesEntry in Breakdown.Torus.CompareStatements, line 36. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L36).

**Growth of propagation chains.** This proposition requires that steps uniformly bounded by a nonnegative constant C give a chain bound C^(n−m) whenever m ≤ n. Source: Breakdown.Periodic.ShiftChainNorm in Breakdown.Torus.CompareStatements, line 41. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L41).

**Whole-space chain formula.** This proposition requires that repeated whole-space propagation is an explicit heat evolution followed by dilation and the factor θ raised to the negative number of steps. Source: Breakdown.Periodic.R3ChainFormula in Breakdown.Torus.CompareStatements, line 45. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L45).

**Periodic chain formula.** This proposition requires that repeated periodic propagation has the geometric factor (λ^(1/4)/θ)^(j+1) and the specified accumulated heat time. Source: Breakdown.Periodic.TorusChainFormula in Breakdown.Torus.CompareStatements, line 54. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L54).

**Heat composition after projection.** This proposition requires that free heat evolution for nonnegative time composes with positive-time projected heat flow by adding the two times. Source: Breakdown.Periodic.HeatDivFreeShift in Breakdown.Torus.CompareStatements, line 61. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L61).

**Continuity of projected heat flow.** This proposition requires that projected heat flow is strongly continuous for positive elapsed time. Source: Breakdown.Periodic.HeatDivFreeContinuous in Breakdown.Torus.CompareStatements, line 65. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L65).

**Whole-space interaction formula.** This proposition requires that on a time piece with 0 < L ≤ 1 the whole-space shell interaction is the prescribed weighted time convolution. Source: Breakdown.Periodic.R3LambdaFormula in Breakdown.Torus.CompareStatements, line 68. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L68).

**Periodic interaction formula.** This proposition requires that on a time piece with 0 < L ≤ 1 and valid shell scale the periodic shell interaction is the prescribed weighted time convolution. Source: Breakdown.Periodic.TorusLambdaFormula in Breakdown.Torus.CompareStatements, line 73. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L73).

**Propagated whole-space interaction.** This proposition requires that a propagated whole-space interaction is the explicit rescaled heat integral, integrated to the current time for j = 0 and to L for later entries. Source: Breakdown.Periodic.R3EntryFormula in Breakdown.Torus.CompareStatements, line 79. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L79).

**Propagated periodic interaction.** This proposition requires that a propagated periodic interaction is the explicit geometric-weighted heat integral, integrated to the current time for j = 0 and to L for later entries. Source: Breakdown.Periodic.TorusEntryFormula in Breakdown.Torus.CompareStatements, line 90. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L90).

**Norm under a change of scale.** This proposition requires that rescaling a shell restriction by 0 < c ≤ 1 changes its norm by at most the factor c^(1/4). Source: Breakdown.Periodic.FrameChange in Breakdown.Torus.CompareStatements, line 101. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L101).

**Split a singular time integral.** This proposition requires that the regular and terminal parts of the time integral admit the bound a u + 4 c ε^(1/4). Source: Breakdown.Periodic.SplitIntegralBound in Breakdown.Torus.CompareStatements, line 106. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L106).

**Smallness on a finite window.** This proposition requires that for λ^(1/4) < θ < 1 each fixed finite window of whole-space and periodic propagation entries becomes uniformly close as T tends to zero. Source: Breakdown.Periodic.WindowBound in Breakdown.Torus.CompareStatements, line 112. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L112).

**Geometric tail estimate.** This proposition requires that both whole-space and periodic propagation entries admit one uniform bound proportional to (λ^(1/4)/θ)^j. Source: Breakdown.Periodic.TailBound in Breakdown.Torus.CompareStatements, line 124. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L124).

**Whole-space initial-data entries.** This proposition requires that the inverse whole-space shift applied to initial data has the explicit θ⁻ⁿ heat-and-dilation formula at index n. Source: Breakdown.Periodic.R3SeedEntry in Breakdown.Torus.CompareStatements, line 136. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L136).

**Periodic initial-data entries.** This proposition requires that the inverse periodic shift applied to initial data has the explicit factor (λ^(1/4)/θ)^n and heat time T(λ^n s+1−λ^n). Source: Breakdown.Periodic.TorusSeedEntry in Breakdown.Torus.CompareStatements, line 145. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L145).

**Transplantation under dilation.** This proposition requires that transplanting at scale μ agrees with first dilating by positive c and transplanting at scale μc. Source: Breakdown.Periodic.TransplantDilate in Breakdown.Torus.CompareStatements, line 152. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L152).

**Dilation preserves test fields.** This proposition requires that positive dilation preserves smooth compactly supported solenoidal test fields. Source: Breakdown.Periodic.DilateTest in Breakdown.Torus.CompareStatements, line 155. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareStatements.lean#L155).

### Breakdown.Torus.CompareTail

Bounds distant propagation entries by a geometric sequence whose ratio is smaller than one.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareTail.Internal.

**Bound for free time piece.** With the stated hypotheses, free time piece satisfies the quantitative estimate `‖H.pieceFree T‖ ≤ 1`. Source: Breakdown.Periodic.CompareTail.Internal.norm_pieceFree_le in Breakdown.Torus.CompareTail, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L12).

**Bound for time-piece endpoint.** Time-piece endpoint satisfies the quantitative estimate `‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1`. Source: Breakdown.Periodic.CompareTail.Internal.norm_pieceEnd_le in Breakdown.Torus.CompareTail, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L23).

**Bound for dilation.** With the stated hypotheses, dilation satisfies the quantitative estimate `‖F.D μ‖ ≤ μ ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.CompareTail.Internal.norm_dil_le in Breakdown.Torus.CompareTail, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L32).

**Bound for whole-space sequence shift.** With the stated hypotheses, whole-space sequence shift satisfies the quantitative estimate `‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ`. Source: Breakdown.Periodic.CompareTail.Internal.norm_r3Shift_entry in Breakdown.Torus.CompareTail, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L36).

**Bound for periodic sequence shift.** With the stated hypotheses, periodic sequence shift satisfies the quantitative estimate `‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c`. Source: Breakdown.Periodic.CompareTail.Internal.norm_torusShift_entry in Breakdown.Torus.CompareTail, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L52).

**Bound for whole-space piece norm.** With the stated hypotheses, whole-space piece norm satisfies the quantitative estimate `‖A.r3Piece n‖ ≤ (A.terms : ℝ) * (max C 0 * max C 0)`. Source: Breakdown.Periodic.CompareTail.Internal.norm_r3Piece_le in Breakdown.Torus.CompareTail, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L61).

**Bound for periodic shell restriction.** Periodic shell restriction satisfies the quantitative estimate `‖restrictTorus μ b‖ ≤ restrictTorusFun_bound.choose`. Source: Breakdown.Periodic.CompareTail.Internal.norm_restrictTorus_le in Breakdown.Torus.CompareTail, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L77).

**Bound for propagation chain.** With the stated hypotheses, propagation chain satisfies the quantitative estimate `‖R (shiftChain B m (m + j) y s)‖ ≤ CR * c ^ j * ‖y‖`. Source: Breakdown.Periodic.CompareTail.Internal.norm_chain_apply_le in Breakdown.Torus.CompareTail, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L80).

**Source namespace:** Breakdown.Periodic.

**Geometric tail estimate.** Under the stated assumptions, both whole-space and periodic propagation entries admit one uniform bound proportional to (λ^(1/4)/θ)^j. Source: Breakdown.Periodic.tailBound in Breakdown.Torus.CompareTail, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareTail.lean#L97).

### Breakdown.Torus.CompareWindow

Uses heat comparison away from the singular endpoint and an integrable endpoint bound to compare finitely many propagation steps.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.CompareWindow.Internal.

**Integrability from a power bound.** With the stated hypotheses, singular integrand is integrable over the time interval in `IntervalIntegrable f volume 0 u`. Source: Breakdown.Periodic.CompareWindow.Internal.intervalIntegrable_of_singular in Breakdown.Torus.CompareWindow, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L18).

**Continuity after translating time.** With the stated hypotheses, translated operator family is continuous on the domain specified by `ContinuousOn (fun σ => Λ (1 - σ - e) (x σ)) (Ioo 0 u)`. Source: Breakdown.Periodic.CompareWindow.Internal.continuousOn_apply_shift in Breakdown.Torus.CompareWindow, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L30).

**Bound for heat-comparison integrand.** With the stated hypotheses, heat-comparison integrand satisfies the quantitative estimate `‖w • G (Λ τ z)‖ ≤ Cw * M * K * Cx * v ^ (-(3 / 4 : ℝ))`. Source: Breakdown.Periodic.CompareWindow.Internal.norm_term_le in Breakdown.Torus.CompareWindow, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L47).

**Bound for finite comparison window.** With the stated hypotheses, finite comparison window satisfies the estimate `‖(∫ σ in (0 : ℝ)..u, fT σ) - ∫ σ in (0 : ℝ)..u, fR σ‖ ≤ Cw * a₀ * u + 4 * (Cw * (MT * KT + MR * KR) * Cx) * ε ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.CompareWindow.Internal.window_piece in Breakdown.Torus.CompareWindow, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L65).

**Bound for periodic shell restriction.** With the stated hypotheses, periodic shell restriction satisfies the quantitative estimate `‖restrictTorus μ b‖ ≤ C`. Source: Breakdown.Periodic.CompareWindow.Internal.norm_restrictTorus_le in Breakdown.Torus.CompareWindow, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L113).

**Bound for Fourier dilation.** With the stated hypotheses, Fourier dilation satisfies the quantitative estimate `‖Freq.dilX c‖ ≤ 1`. Source: Breakdown.Periodic.CompareWindow.Internal.norm_dilX_le in Breakdown.Torus.CompareWindow, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L117).

**Norm of a scalar identity map.** With the stated hypotheses, scalar identity map satisfies the quantitative estimate `‖(c ^ (1 / 4 : ℝ)) • ContinuousLinearMap.id ℝ V‖ ≤ 1`. Source: Breakdown.Periodic.CompareWindow.Internal.norm_smul_id_le in Breakdown.Torus.CompareWindow, line 123. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L123).

**Bound for finite-window comparison.** With the stated hypotheses, finite-window comparison satisfies the quantitative estimate `ε ^ (1 / 4 : ℝ) ≤ r`. Source: Breakdown.Periodic.CompareWindow.Internal.rpow_quarter_le in Breakdown.Torus.CompareWindow, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L132).

**Bound for finite-window comparison.** With the stated hypotheses, finite-window comparison satisfies the quantitative estimate `Real.sqrt T * b ≤ 1 / 8`. Source: Breakdown.Periodic.CompareWindow.Internal.sqrt_mul_le_of_lt in Breakdown.Torus.CompareWindow, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L140).

**Bound for finite comparison window.** With the stated hypotheses, finite comparison window satisfies the estimate `‖(∫ σ in (0 : ℝ)..u, extendPiece w σ • restrictTorus μn b (c ^ (1 / 4 : ℝ) • (-((μm ^ (-(1 / 4 : ℝ))) • sourceOp μm (1 - σ - e) (advectShell φ hφ b (extendPiece zz σ)))))) - ∫ σ in (0 : ℝ)..u, extendPiece w σ • restrictR3 b (Freq.dilX c (-(Freq.heatDivFree (1 - σ - e) (advectShell φ hφ b (extendPiece zz σ)))))‖ ≤ CA * (δ * (Cad * CA * Cz)) * u + 4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Cz) * ε ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.CompareWindow.Internal.window_term in Breakdown.Torus.CompareWindow, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L147).

**Bound for finite-window comparison.** With the stated hypotheses, finite-window comparison satisfies the estimate `‖(θ⁻¹) ^ j‖ * ((terms : ℝ) * (CA * (δ * (Cad * CA * Z)) + 4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Z) * ε ^ (1 / 4 : ℝ))) ≤ η * Z`. Source: Breakdown.Periodic.CompareWindow.Internal.final_arith in Breakdown.Torus.CompareWindow, line 230. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L230).

**Source namespace:** Breakdown.Periodic.

**Smallness on a finite window.** Under the stated assumptions, for λ^(1/4) < θ < 1 each fixed finite window of whole-space and periodic propagation entries becomes uniformly close as T tends to zero. Source: Breakdown.Periodic.windowBound in Breakdown.Torus.CompareWindow, line 273. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/CompareWindow.lean#L273).

### Breakdown.Torus.Cutoff

Constructs a vector potential by radial integration and uses its curl to localize a divergence-free field.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Cutoff.Internal.

**Zero-parameter formula for cross product.** Cross product has the zero-parameter identity `cross a b 0 = a 1 * b 2 - a 2 * b 1`. Source: Breakdown.Periodic.Cutoff.Internal.cross_apply_zero in Breakdown.Torus.Cutoff, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L12).

**Formula for cross product.** Cross product obeys the exact identity `cross a b 1 = a 2 * b 0 - a 0 * b 2`. Source: Breakdown.Periodic.Cutoff.Internal.cross_apply_one in Breakdown.Torus.Cutoff, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L14).

**Formula for cross product.** Cross product obeys the exact identity `cross a b 2 = a 0 * b 1 - a 1 * b 0`. Source: Breakdown.Periodic.Cutoff.Internal.cross_apply_two in Breakdown.Torus.Cutoff, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L16).

**Formula for coordinate unit vector.** Coordinate unit vector obeys the exact identity `unitVector i j = if j = i then 1 else 0`. Source: Breakdown.Periodic.Cutoff.Internal.unitVector_apply in Breakdown.Torus.Cutoff, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L18).

**Cross product as a bilinear map.** The coordinate cross product is packaged as a real bilinear map. Source: Breakdown.Periodic.Cutoff.Internal.crossLinear in Breakdown.Torus.Cutoff, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L21).

**Bounded bilinear cross product.** The cross product is packaged as a continuous bilinear map on three-dimensional space. Source: Breakdown.Periodic.Cutoff.Internal.crossBilinear in Breakdown.Torus.Cutoff, line 28. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L28).

**Formula for bounded cross product.** Bounded cross product obeys the exact identity `crossBilinear a b = cross a b`. Source: Breakdown.Periodic.Cutoff.Internal.crossBilinear_apply in Breakdown.Torus.Cutoff, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L31).

**Smoothness of cross product.** With the stated hypotheses, cross product has the asserted differentiability order in `ContDiff ℝ n (fun y => cross (u y) (v y))`. Source: Breakdown.Periodic.Cutoff.Internal.contDiff_cross in Breakdown.Torus.Cutoff, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L33).

**Derivative of cross product.** With the stated hypotheses, cross product has the Fréchet derivative specified by `HasFDerivAt (fun y => cross (u y) (v y)) ((crossBilinear (u x)).comp v' + (crossBilinear.comp u').flip (v x)) x`. Source: Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_cross in Breakdown.Torus.Cutoff, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L38).

**Derivative formula for cross product.** The derivative calculation gives `((crossBilinear (u x)).comp v' + (crossBilinear.comp u').flip (v x)) w = cross (u x) (v' w) + cross (u' w) (v x)`. Source: Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_cross_apply in Breakdown.Torus.Cutoff, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L44).

**Formula for coordinate unit vector.** Coordinate unit vector obeys the exact identity `L v c = v 0 * L (unitVector 0) c + v 1 * L (unitVector 1) c + v 2 * L (unitVector 2) c`. Source: Breakdown.Periodic.Cutoff.Internal.apply_expand in Breakdown.Torus.Cutoff, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L48).

**Derivative in the spatial variable.** The spatial partial derivative is the derivative of a space-time map composed with the inclusion of spatial increments. Source: Breakdown.Periodic.Cutoff.Internal.partialSecond in Breakdown.Torus.Cutoff, line 57. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L57).

**Derivative of spatial partial derivative.** With the stated hypotheses, spatial partial derivative has the Fréchet derivative specified by `HasFDerivAt (fun y => F (s, y)) (partialSecond F s x) x`. Source: Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_partialSecond in Breakdown.Torus.Cutoff, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L60).

**Continuity of spatial partial derivative.** With the stated hypotheses, spatial partial derivative is continuous on the domain specified by `Continuous (fun z : ℝ × Space => partialSecond F z.1 z.2)`. Source: Breakdown.Periodic.Cutoff.Internal.continuous_partialSecond in Breakdown.Torus.Cutoff, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L64).

**Derivative of integral.** With the stated hypotheses, integral has the Fréchet derivative specified by `HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) (∫ s in (0 : ℝ)..1, partialSecond F s x) x`. Source: Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_integral_unit in Breakdown.Torus.Cutoff, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L68).

**Smoothness of a radial integral.** Integrating a smooth Banach-valued family along the fixed radial interval [0,1] gives a spatial map of every finite differentiability order. Source: Breakdown.Periodic.Cutoff.Internal.contDiff_integral_unit in Breakdown.Torus.Cutoff, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L86).

**Smoothness of integral.** With the stated hypotheses, integral has the asserted differentiability order in `ContDiff ℝ ∞ (fun y => ∫ s in (0 : ℝ)..1, F (s, y))`. Source: Breakdown.Periodic.Cutoff.Internal.contDiff_integral_unit_infty in Breakdown.Torus.Cutoff, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L107).

**Radial vector-potential integrand.** The vector-potential integrand is `s` times the cross product of the field on the radial segment with the displacement from the base point. Source: Breakdown.Periodic.Cutoff.Internal.potentialIntegrand in Breakdown.Torus.Cutoff, line 112. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L112).

**Radial potential derivative.** The radial derivative combines `s²` times the directional derivative of the field with `2s` times its value. Source: Breakdown.Periodic.Cutoff.Internal.potentialDerivative in Breakdown.Torus.Cutoff, line 115. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L115).

**Smoothness of potential integrand.** With the stated hypotheses, potential integrand has the asserted differentiability order in `ContDiff ℝ ∞ (potentialIntegrand x₀ g)`. Source: Breakdown.Periodic.Cutoff.Internal.contDiff_potentialIntegrand in Breakdown.Torus.Cutoff, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L122).

**Formula for vector potential.** Vector potential obeys the exact identity `homotopyPotential x₀ g = fun y => ∫ s in (0 : ℝ)..1, potentialIntegrand x₀ g (s, y)`. Source: Breakdown.Periodic.Cutoff.Internal.homotopyPotential_eq in Breakdown.Torus.Cutoff, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L128).

**Formula for spatial partial derivative.** With the stated hypotheses, spatial partial derivative obeys the exact identity `partialSecond (potentialIntegrand x₀ g) s x v = s • (cross (g (x₀ + s • (x - x₀))) v + cross (fderiv ℝ g (x₀ + s • (x - x₀)) (s • v)) (x - x₀))`. Source: Breakdown.Periodic.Cutoff.Internal.partialSecond_potential_apply in Breakdown.Torus.Cutoff, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L131).

**Continuity of spatial partial derivative.** With the stated hypotheses, spatial partial derivative is continuous on the domain specified by `Continuous (fun s => partialSecond (potentialIntegrand x₀ g) s x v)`. Source: Breakdown.Periodic.Cutoff.Internal.continuous_partialSecond_potential in Breakdown.Torus.Cutoff, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L145).

**Formula for coordinate derivative.** With the stated hypotheses, coordinate derivative obeys the exact identity `partialAt (homotopyPotential x₀ g) i j x = ∫ s in (0 : ℝ)..1, partialSecond (potentialIntegrand x₀ g) s x (unitVector i) j`. Source: Breakdown.Periodic.Cutoff.Internal.partialAt_potential in Breakdown.Torus.Cutoff, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L151).

**Derivative formula for integral.** With the stated hypotheses, the derivative calculation gives `∫ s in (0 : ℝ)..1, potentialDerivative x₀ x g s = g x`. Source: Breakdown.Periodic.Cutoff.Internal.integral_potentialDerivative in Breakdown.Torus.Cutoff, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L163).

**Formula for vector potential.** With the stated hypotheses, vector potential obeys the exact identity `partialSecond (potentialIntegrand x₀ g) s x (unitVector a) b - partialSecond (potentialIntegrand x₀ g) s x (unitVector b) a = potentialDerivative x₀ x g s c`. Source: Breakdown.Periodic.Cutoff.Internal.potential_pointwise in Breakdown.Torus.Cutoff, line 181. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L181).

**Curl of the homotopy potential.** With the stated hypotheses, vector potential obeys the exact identity `partialAt (homotopyPotential x₀ g) a b x - partialAt (homotopyPotential x₀ g) b a x = g x c`. Source: Breakdown.Periodic.Cutoff.Internal.curl_potential_component in Breakdown.Torus.Cutoff, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L201).

**Smoothness of gradient.** With the stated hypotheses, gradient has the asserted differentiability order in `ContDiff ℝ ∞ (gradientAt χ)`. Source: Breakdown.Periodic.Cutoff.Internal.contDiff_gradientAt in Breakdown.Torus.Cutoff, line 236. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L236).

**Derivative of gradient.** With the stated hypotheses, gradient has the Fréchet derivative specified by `HasFDerivAt (gradientAt χ) (∑ i : Fin 3, (((fderiv ℝ χ x).comp (0 : Space →L[ℝ] Space) + (fderiv ℝ (fderiv ℝ χ) x).flip (unitVector i)).smulRight (unitVector i))) x`. Source: Breakdown.Periodic.Cutoff.Internal.hasFDerivAt_gradientAt in Breakdown.Torus.Cutoff, line 241. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Cutoff.lean#L241).

### Breakdown.Torus.Final

Uses periodic mild uniqueness and a moving-frame reduction to exclude a global smooth solution, then rescales to arbitrary positive viscosity.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Final.Internal.

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (v t)`. Source: Breakdown.Periodic.Final.Internal.contDiff_slice in Breakdown.Torus.Final, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L13).

**Scaling formula for divergence.** Divergence obeys the scalar-scaling identity `divergenceAt (fun y => c • f y) x = c * divergenceAt f x`. Source: Breakdown.Periodic.Final.Internal.divergenceAt_smul in Breakdown.Torus.Final, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L22).

**Formula for gradient.** Gradient obeys the exact identity `gradientAt (fun y => c * p y) x = c • gradientAt p x`. Source: Breakdown.Periodic.Final.Internal.gradientAt_mul in Breakdown.Torus.Final, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L28).

**Scaling formula for advection.** Advection obeys the scalar-scaling identity `advectionAt (fun y => c • f y) x = (c * c) • advectionAt f x`. Source: Breakdown.Periodic.Final.Internal.advectionAt_smul in Breakdown.Torus.Final, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L34).

**Scaling formula for Laplacian.** With the stated hypotheses, Laplacian obeys the scalar-scaling identity `sumSecondPartialsAt (fun y => c • f y) x = c • sumSecondPartialsAt f x`. Source: Breakdown.Periodic.Final.Internal.sumSecondPartialsAt_smul in Breakdown.Torus.Final, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L40).

**Rescale the viscosity parameter.** For positive viscosity ν, scaling velocity by ν⁻¹, pressure by ν⁻² and time by ν⁻¹ converts initial data νu₀ to a viscosity-one solution with initial data u₀. Source: Breakdown.Periodic.Final.Internal.scaled_solution in Breakdown.Torus.Final, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L45).

**Source namespace:** Breakdown.Periodic.

**Periodic breakdown from blow-up.** Periodic mild uniqueness, smooth-to-mild conversion, moving-frame reduction and the periodic blow-up construction together imply the stated periodic breakdown theorem. Source: Breakdown.Periodic.breakdownOnTorus_of_blowup in Breakdown.Torus.Final, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Final.lean#L88).

### Breakdown.Torus.ForceSmoothing

Derives the half-power heat smoothing estimate for continuous periodic forcing from Parseval and coefficient bounds.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ForceSmoothing.Internal.

**One squared velocity component.** The auxiliary field places the square of one real velocity component in the first coordinate. Source: Breakdown.Periodic.ForceSmoothing.Internal.squareField in Breakdown.Torus.ForceSmoothing, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L14).

**Continuity of squared component field.** With the stated hypotheses, squared component field is continuous on the domain specified by `Continuous (squareField F j)`. Source: Breakdown.Periodic.ForceSmoothing.Internal.continuous_squareField in Breakdown.Torus.ForceSmoothing, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L17).

**Periodicity of squared component field.** With the stated hypotheses, squared component field is unit-periodic, as expressed by `IsPeriodic (squareField F j)`. Source: Breakdown.Periodic.ForceSmoothing.Internal.isPeriodic_squareField in Breakdown.Torus.ForceSmoothing, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L22).

**Value at zero for Fourier character.** Fourier character has the zero-parameter identity `character 0 x = 1`. Source: Breakdown.Periodic.ForceSmoothing.Internal.character_zero in Breakdown.Torus.ForceSmoothing, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L27).

**A squared component at zero frequency.** The cell integral of the squared jth velocity component is the first component of the zero Fourier coefficient of the auxiliary squared field. Source: Breakdown.Periodic.ForceSmoothing.Internal.integral_sq_apply in Breakdown.Torus.ForceSmoothing, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L30).

**Sum of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the exact series sum in `HasSum (fun k => ‖(freqTrCoef F k).ofLp j‖ ^ 2) (∫ x in cell, ((F x).ofLp j) ^ 2)`. Source: Breakdown.Periodic.ForceSmoothing.Internal.hasSum_apply_sq in Breakdown.Torus.ForceSmoothing, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L37).

**Sum of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the exact series sum in `HasSum (fun k => ‖freqTrCoef F k‖ ^ 2) (∫ x in cell, ‖F x‖ ^ 2)`. Source: Breakdown.Periodic.ForceSmoothing.Internal.hasSum_sq in Breakdown.Torus.ForceSmoothing, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L55).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * heatFactor τ k ^ 2 ≤ 2 / τ`. Source: Breakdown.Periodic.ForceSmoothing.Internal.weight_heat_le_of_le_one in Breakdown.Torus.ForceSmoothing, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L72).

**Source namespace:** Breakdown.Periodic.

**Smoothing of periodic forcing.** Under the stated assumptions, for 0 < τ ≤ 1 the periodic forcing operator is bounded by Cτ⁻¹ᐟ² times the source L² norm over the unit cell. Source: Breakdown.Periodic.forceSmoothing in Breakdown.Torus.ForceSmoothing, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ForceSmoothing.lean#L88).

### Breakdown.Torus.Forced

Converts a smooth periodic forced PDE into its Fourier-mode Duhamel equation and hence a forced mild solution.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Forced.Internal.

**Closed time slab.** The slab is the product of the closed time interval `[a,b]` with all of space. Source: Breakdown.Periodic.Forced.Internal.slab in Breakdown.Torus.Forced, line 21. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L21).

**Smoothness of forced periodic flow.** With the stated hypotheses, forced periodic flow has the asserted differentiability order in `ContDiff ℝ ∞ (fun y => g (τ, y))`. Source: Breakdown.Periodic.Forced.Internal.sliceContDiff in Breakdown.Torus.Forced, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L23).

**Continuity of forced periodic flow.** With the stated hypotheses, forced periodic flow is continuous on the domain specified by `Continuous fun x => g (τ, x)`. Source: Breakdown.Periodic.Forced.Internal.sliceContinuous in Breakdown.Torus.Forced, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L29).

**Time derivative of time derivative.** With the stated hypotheses, time derivative has the one-variable derivative specified by `HasDerivAt (fun σ => g (σ, x)) (fderivWithin ℝ g (slab a b) (τ, x) (1, 0)) τ`. Source: Breakdown.Periodic.Forced.Internal.timeDeriv in Breakdown.Torus.Forced, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L33).

**Continuity of Fourier coefficient.** With the stated hypotheses, Fourier coefficient is continuous on the domain specified by `ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Icc a b)`. Source: Breakdown.Periodic.Forced.Internal.continuousOn_freqTrCoef_slab in Breakdown.Torus.Forced, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L44).

**Time derivative of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the one-variable derivative specified by `HasDerivAt (fun τ => freqTrCoef (fun x => g (τ, x)) k) (freqTrCoef (fun x => deriv (fun τ => g (τ, x)) t) k) t`. Source: Breakdown.Periodic.Forced.Internal.hasDerivAt_freqTrCoef_slab in Breakdown.Torus.Forced, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L60).

**Cosine time parametrization.** The time parametrization maps `τ` to `a + (b-a)(1-cos τ)/2`. Source: Breakdown.Periodic.Forced.Internal.clampTime in Breakdown.Torus.Forced, line 96. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L96).

**Inverse cosine parametrization.** The inverse time parametrization uses `arccos (1 - 2(t-a)/(b-a))`. Source: Breakdown.Periodic.Forced.Internal.unclampTime in Breakdown.Torus.Forced, line 98. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L98).

**The cosine clock stays in its interval.** When a < b, the cosine time parametrization takes every real input into the closed interval [a,b]. Source: Breakdown.Periodic.Forced.Internal.clampTime_mem in Breakdown.Torus.Forced, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L100).

**Formula for time clamp.** With the stated hypotheses, time clamp obeys the exact identity `clampTime a b (unclampTime a b t) = t`. Source: Breakdown.Periodic.Forced.Internal.clampTime_unclampTime in Breakdown.Torus.Forced, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L107).

**Continuity of periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding is continuous on the domain specified by `ContinuousOn (fun t => toV (u t)) (Icc a b)`. Source: Breakdown.Periodic.Forced.Internal.continuousOn_toV in Breakdown.Torus.Forced, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L117).

**Addition formula for Fourier coefficient.** With the stated hypotheses, Fourier coefficient obeys the addition identity `freqTrCoef (fun x => f x + g x) k = freqTrCoef f k + freqTrCoef g k`. Source: Breakdown.Periodic.Forced.Internal.freqTrCoef_add in Breakdown.Torus.Forced, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L140).

**Time derivative of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the one-variable derivative specified by `HasDerivAt (fun σ => freqTrCoef (u σ) k) ((-(4 * π ^ 2 * ‖freq k‖ ^ 2)) • freqTrCoef (u τ) k - (divFree k (advCoef (toV (u τ)) (toV (u τ)) k) - divFree k (freqTrCoef (F τ) k))) τ`. Source: Breakdown.Periodic.Forced.Internal.mode_deriv in Breakdown.Torus.Forced, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L149).

**Formula for forced periodic flow.** With the stated hypotheses, forced periodic flow obeys the exact identity `c t = Real.exp (-(l * (t - a))) • c a + ∫ s in a..t, (-Real.exp (-(l * (t - s)))) • B s`. Source: Breakdown.Periodic.Forced.Internal.variation_of_constants in Breakdown.Torus.Forced, line 195. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L195).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `coeff (forceV τ G) k = heatFactor τ k • divFree k (freqTrCoef G k)`. Source: Breakdown.Periodic.Forced.Internal.coeff_forceV in Breakdown.Torus.Forced, line 222. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L222).

**Formula for heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing obeys the exact identity `forceV τ G = heat (τ - σ) (forceV σ G)`. Source: Breakdown.Periodic.Forced.Internal.forceV_eq_heat in Breakdown.Torus.Forced, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L228).

**Bound for heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing satisfies the quantitative estimate `‖forceV τ G‖ ≤ (forceSmoothing.choose * τ ^ (-(1 / 2 : ℝ)) + forceSmoothing.choose) * Real.sqrt (∫ x in cell, ‖G x‖ ^ 2)`. Source: Breakdown.Periodic.Forced.Internal.norm_forceV_le in Breakdown.Torus.Forced, line 243. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L243).

**Continuity of heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing is continuous on the domain specified by `ContinuousOn (fun s => forceV (t - s) (F s)) (Ioo a t)`. Source: Breakdown.Periodic.Forced.Internal.continuousOn_force in Breakdown.Torus.Forced, line 263. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L263).

**Integrability of periodic forcing.** With the stated hypotheses, heat-regularized forcing is integrable over the time interval in `IntervalIntegrable (fun s => forceV (t - s) (F s)) volume a t`. Source: Breakdown.Periodic.Forced.Internal.integrable_force in Breakdown.Torus.Forced, line 311. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L311).

**Integrability of bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel is integrable over the time interval in `IntervalIntegrable (fun s => kernel (t - s) (U s) (U s)) volume a t`. Source: Breakdown.Periodic.Forced.Internal.integrable_kernel in Breakdown.Torus.Forced, line 351. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L351).

**Integrability of Fourier coefficient.** With the stated hypotheses, Fourier coefficient is integrable over the time interval in `IntervalIntegrable (fun s => coeff (f s) k) volume a t`. Source: Breakdown.Periodic.Forced.Internal.intervalIntegrable_coeff in Breakdown.Torus.Forced, line 382. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L382).

**Formula for heat multiplier.** With the stated hypotheses, heat multiplier obeys the exact identity `coeff (toV (u t)) k = heatFactor (t - a) k • coeff (toV (u a)) k + (∫ s in a..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k) + ∫ s in a..t, coeff (forceV (t - s) (F s)) k`. Source: Breakdown.Periodic.Forced.Internal.mode_identity in Breakdown.Torus.Forced, line 386. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L386).

**Source namespace:** Breakdown.Periodic.

**From forced PDE to mild flow.** Under the stated assumptions, a smooth forced periodic solution on a nontrivial closed time slab yields the corresponding forced periodic mild solution. Source: Breakdown.Periodic.forcedPeriodicIsMild in Breakdown.Torus.Forced, line 442. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Forced.lean#L442).

### Breakdown.Torus.FreqTrSeries

Reconstructs a smooth periodic solenoidal field from its Fourier coefficients and identifies its weighted sequence representation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.FreqTrSeries.Internal.

**Formula for unit cell.** Unit cell obeys the exact identity `cell = WithLp.toLp 2 '' Icc (0 : Fin 3 → ℝ) 1`. Source: Breakdown.Periodic.FreqTrSeries.Internal.cell_eq_image in Breakdown.Torus.FreqTrSeries, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L12).

**Compactness of unit cell.** Unit cell is compact, as asserted by `IsCompact cell`. Source: Breakdown.Periodic.FreqTrSeries.Internal.isCompact_cell in Breakdown.Torus.FreqTrSeries, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L20).

**Continuity of complexification.** Complexification is continuous on the domain specified by `Continuous complexify`. Source: Breakdown.Periodic.FreqTrSeries.Internal.continuous_complexify in Breakdown.Torus.FreqTrSeries, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L24).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character k)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.continuous_character in Breakdown.Torus.FreqTrSeries, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L29).

**Norm identity for Fourier character.** Fourier character has the norm identity `‖character k x‖ = 1`. Source: Breakdown.Periodic.FreqTrSeries.Internal.norm_character in Breakdown.Torus.FreqTrSeries, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L33).

**Integrability of complexification.** With the stated hypotheses, complexification satisfies the integrability assertion `IntegrableOn (fun x => character k x • complexify (g x)) cell`. Source: Breakdown.Periodic.FreqTrSeries.Internal.integrableOn_coef in Breakdown.Torus.FreqTrSeries, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L36).

**Formula for complexification.** Complexification obeys the exact identity `complexify (a - b) = complexify a - complexify b`. Source: Breakdown.Periodic.FreqTrSeries.Internal.complexify_sub in Breakdown.Torus.FreqTrSeries, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L41).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (fun x => g x - h x) k = freqTrCoef g k - freqTrCoef h k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freqTrCoef_sub in Breakdown.Torus.FreqTrSeries, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L45).

**Bound for Fourier coefficient.** Fourier coefficient satisfies the quantitative estimate `‖freqTrCoef g k‖ ≤ ∫ x in cell, ‖complexify (g x)‖`. Source: Breakdown.Periodic.FreqTrSeries.Internal.norm_freqTrCoef_le in Breakdown.Torus.FreqTrSeries, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L53).

**Coordinate derivative field.** The coordinate derivative field applies the spatial derivative to the chosen coordinate unit vector. Source: Breakdown.Periodic.FreqTrSeries.Internal.partialD in Breakdown.Torus.FreqTrSeries, line 61. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L61).

**Smoothness of coordinate derivative.** With the stated hypotheses, coordinate derivative has the asserted differentiability order in `ContDiff ℝ ∞ (partialD i g)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.contDiff_partialD in Breakdown.Torus.FreqTrSeries, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L63).

**Periodicity of coordinate derivative.** With the stated hypotheses, coordinate derivative is unit-periodic, as expressed by `IsPeriodic (partialD i g)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.isPeriodic_partialD in Breakdown.Torus.FreqTrSeries, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L67).

**Smoothness of Fourier reconstruction.** With the stated hypotheses, periodic Fourier reconstruction has the asserted differentiability order in `ContDiff ℝ 1 g`. Source: Breakdown.Periodic.FreqTrSeries.Internal.contDiff_one in Breakdown.Torus.FreqTrSeries, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L74).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (partialD i g) k = (2 * π * Complex.I * (k i : ℂ)) • freqTrCoef g k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freqTrCoef_partialD in Breakdown.Torus.FreqTrSeries, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L77).

**One minus a coordinate Laplacian.** The auxiliary operator subtracts the second derivative in one coordinate from the field. Source: Breakdown.Periodic.FreqTrSeries.Internal.sspOp in Breakdown.Torus.FreqTrSeries, line 82. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L82).

**Smoothness after a second derivative.** With the stated hypotheses, one minus a second derivative has the asserted differentiability order in `ContDiff ℝ ∞ (sspOp i g)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.contDiff_sspOp in Breakdown.Torus.FreqTrSeries, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L84).

**Periodicity after differentiation.** With the stated hypotheses, one minus a second derivative is unit-periodic, as expressed by `IsPeriodic (sspOp i g)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.isPeriodic_sspOp in Breakdown.Torus.FreqTrSeries, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L88).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (sspOp i g) k = ((1 + 4 * π ^ 2 * (k i : ℝ) ^ 2 : ℝ) : ℂ) • freqTrCoef g k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freqTrCoef_sspOp in Breakdown.Torus.FreqTrSeries, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L94).

**Decay of periodic Fourier coefficients.** A smooth periodic field has a uniform bound on each Fourier-coefficient norm multiplied by the product of its three quadratic coordinate weights. Source: Breakdown.Periodic.FreqTrSeries.Internal.decay in Breakdown.Torus.FreqTrSeries, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L109).

**Summable reciprocal integer weights.** Reciprocal integer weight satisfies the series-convergence assertion `Summable (fun n : ℤ => (1 + 4 * π ^ 2 * (n : ℝ) ^ 2)⁻¹)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.summable_inv_int in Breakdown.Torus.FreqTrSeries, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L120).

**Summability of frequency lattice.** With the stated hypotheses, frequency lattice satisfies the series-convergence assertion `Summable (fun k : Lattice => ∏ i, g (k i))`. Source: Breakdown.Periodic.FreqTrSeries.Internal.summable_prod_of_nonneg in Breakdown.Torus.FreqTrSeries, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L133).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `(freq k).ofLp i = (k i : ℝ)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freq_apply in Breakdown.Torus.FreqTrSeries, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L152).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, (k i : ℝ) ^ 2`. Source: Breakdown.Periodic.FreqTrSeries.Internal.norm_freq_sq in Breakdown.Torus.FreqTrSeries, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L155).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `weight k ≤ ∏ i, (1 + 4 * π ^ 2 * (k i : ℝ) ^ 2)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.weight_le_prod in Breakdown.Torus.FreqTrSeries, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L159).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < weight k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.weight_pos in Breakdown.Torus.FreqTrSeries, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L166).

**Summability of Fourier coefficient.** With the stated hypotheses, Fourier coefficient satisfies the series-convergence assertion `Summable (fun k => ‖freqTrCoef f k‖) ∧ Summable (fun k => weight k * ‖freqTrCoef f k‖ ^ 2)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.summable_bounds in Breakdown.Torus.FreqTrSeries, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L170).

**Sign formula for Fourier character.** Fourier character obeys the sign-change identity `character (-k) x = starRingEnd ℂ (character k x)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.character_neg in Breakdown.Torus.FreqTrSeries, line 199. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L199).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `(freqTrCoef g k).ofLp i = ∫ x in cell, character k x * ((g x).ofLp i : ℂ)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freqTrCoef_apply in Breakdown.Torus.FreqTrSeries, line 208. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L208).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `(freqTrCoef g (-k)).ofLp i = starRingEnd ℂ ((freqTrCoef g k).ofLp i)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freqTrCoef_neg_apply in Breakdown.Torus.FreqTrSeries, line 216. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L216).

**Solenoidality of Fourier coefficients.** With the stated hypotheses, the Fourier-coefficient calculation gives `divPairing k (freqTrCoef f k) = 0`. Source: Breakdown.Periodic.FreqTrSeries.Internal.divPairing_freqTrCoef in Breakdown.Torus.FreqTrSeries, line 223. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L223).

**Sign formula for lattice frequency.** Lattice frequency obeys the sign-change identity `freq (-k) = -freq k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.freq_neg in Breakdown.Torus.FreqTrSeries, line 250. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L250).

**Sign formula for Sobolev weight.** Sobolev weight obeys the sign-change identity `weight (-k) = weight k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.weight_neg in Breakdown.Torus.FreqTrSeries, line 253. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L253).

**Coefficients lie in the field space.** The weighted Fourier coefficients of the stated smooth periodic divergence-free field are square summable and belong to the real solenoidal sequence subspace. Source: Breakdown.Periodic.FreqTrSeries.Internal.mem_fieldSpace in Breakdown.Torus.FreqTrSeries, line 256. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L256).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `coeff (toV f) k = freqTrCoef f k`. Source: Breakdown.Periodic.FreqTrSeries.Internal.coeff_toV in Breakdown.Torus.FreqTrSeries, line 281. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L281).

**Scaling formula for periodic field.** With the stated hypotheses, periodic field obeys the scalar-scaling identity `f (x + (m : ℝ) • unitVector i) = f x`. Source: Breakdown.Periodic.FreqTrSeries.Internal.periodic_int_smul in Breakdown.Torus.FreqTrSeries, line 289. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L289).

**Formula for periodic field.** With the stated hypotheses, periodic field obeys the exact identity `f (x + freq n) = f x`. Source: Breakdown.Periodic.FreqTrSeries.Internal.periodic_freq in Breakdown.Torus.FreqTrSeries, line 306. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L306).

**Quotient into the unit torus.** The quotient map sends each real coordinate to its class in the unit circle. Source: Breakdown.Periodic.FreqTrSeries.Internal.torusMap in Breakdown.Torus.FreqTrSeries, line 311. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L311).

**The torus map is a quotient map.** The coordinatewise quotient from real coordinates to the unit torus is a topological quotient map. Source: Breakdown.Periodic.FreqTrSeries.Internal.isQuotientMap_torusMap in Breakdown.Torus.FreqTrSeries, line 313. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L313).

**Formula for torus quotient map.** With the stated hypotheses, torus quotient map obeys the exact identity `f (WithLp.toLp 2 y) = f (WithLp.toLp 2 y')`. Source: Breakdown.Periodic.FreqTrSeries.Internal.eq_of_torusMap_eq in Breakdown.Torus.FreqTrSeries, line 318. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L318).

**Representatives in the unit cube.** The torus lift chooses the representative of each coordinate in the interval `[0,1)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.torusLift in Breakdown.Torus.FreqTrSeries, line 334. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L334).

**Formula for torus quotient map.** Torus quotient map obeys the exact identity `torusMap (torusLift q) = q`. Source: Breakdown.Periodic.FreqTrSeries.Internal.torusMap_torusLift in Breakdown.Torus.FreqTrSeries, line 336. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L336).

**One component on the quotient torus.** The component function evaluates a periodic field at the chosen torus representative and regards one coordinate as complex. Source: Breakdown.Periodic.FreqTrSeries.Internal.compFun in Breakdown.Torus.FreqTrSeries, line 339. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L339).

**Formula for component on the torus.** With the stated hypotheses, component on the torus obeys the exact identity `compFun f j (torusMap y) = ((f (WithLp.toLp 2 y)).ofLp j : ℂ)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.compFun_torusMap in Breakdown.Torus.FreqTrSeries, line 342. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L342).

**Continuity of component on the torus.** With the stated hypotheses, component on the torus is continuous on the domain specified by `Continuous (compFun f j)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.continuous_compFun in Breakdown.Torus.FreqTrSeries, line 347. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L347).

**Continuous torus component.** A continuous periodic field induces a continuous complex-valued coordinate function on the unit torus. Source: Breakdown.Periodic.FreqTrSeries.Internal.compMap in Breakdown.Torus.FreqTrSeries, line 356. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L356).

**Formula for torus Fourier character.** Torus Fourier character obeys the exact identity `UnitAddTorus.mFourier n (torusMap y) = character (-n) (WithLp.toLp 2 y)`. Source: Breakdown.Periodic.FreqTrSeries.Internal.mFreqTr_torusMap in Breakdown.Torus.FreqTrSeries, line 360. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L360).

**Matching the quotient coefficients.** With the stated hypotheses, the Fourier-coefficient calculation gives `UnitAddTorus.mFourierCoeff (compMap hf hp j) k = (freqTrCoef f k).ofLp j`. Source: Breakdown.Periodic.FreqTrSeries.Internal.mFreqTrCoeff_compMap in Breakdown.Torus.FreqTrSeries, line 375. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L375).

**Sum of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the exact series sum in `HasSum (fun k => character (-k) x • freqTrCoef f k) (complexify (f x))`. Source: Breakdown.Periodic.FreqTrSeries.Internal.hasSum_apply in Breakdown.Torus.FreqTrSeries, line 398. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L398).

**Source namespace:** Breakdown.Periodic.

**Fourier reconstruction contract.** Under the stated assumptions, a smooth periodic divergence-free field has the expected embedding coefficients, absolutely summable Fourier coefficients and pointwise Fourier reconstruction. Source: Breakdown.Periodic.freqTrSeriesSpec in Breakdown.Torus.FreqTrSeries, line 422. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/FreqTrSeries.lean#L422).

### Breakdown.Torus.Glue

Joins successively rescaled periodic mild pieces and checks the integral equation across their endpoints.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Glue.Internal.

**Periodic Duhamel identity.** The periodic Duhamel predicate requires an integrable bilinear term and identifies the final value with free heat evolution plus its time integral. Source: Breakdown.Periodic.Glue.Internal.TorusVarConst in Breakdown.Torus.Glue, line 12. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L12).

**Formula for unit heat framework.** With the stated hypotheses, unit heat framework obeys the exact identity `(stepFrame hK 1 one_pos le_rfl).K = kernel`. Source: Breakdown.Periodic.Glue.Internal.unitFrame_K in Breakdown.Torus.Glue, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L16).

**Formula for unit heat framework.** With the stated hypotheses, unit heat framework obeys the exact identity `(stepFrame hK 1 one_pos le_rfl).G = heat`. Source: Breakdown.Periodic.Glue.Internal.unitFrame_G in Breakdown.Torus.Glue, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L21).

**The unit-frame Duhamel equation.** With the stated hypotheses, unit heat framework has the equivalent characterizations `(stepFrame hK 1 one_pos le_rfl).VarConst u a t ↔ TorusVarConst u a t`. Source: Breakdown.Periodic.Glue.Internal.unitFrame_varConst_iff in Breakdown.Torus.Glue, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L26).

**Duhamel is preserved by agreement.** If two curves agree on [a,t], with a ≤ t, the periodic Duhamel identity for one also holds for the other. Source: Breakdown.Periodic.Glue.Internal.torusVarConst_congr in Breakdown.Torus.Glue, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L31).

**Continuity of extended time piece.** Extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.Periodic.Glue.Internal.extendPiece_cont in Breakdown.Torus.Glue, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L42).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f L = pieceEnd L f`. Source: Breakdown.Periodic.Glue.Internal.extendPiece_right in Breakdown.Torus.Glue, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L47).

**Formula for affine change of variables.** With the stated hypotheses, affine change of variables obeys the exact identity `x + μ * ((y - x) / μ) = y`. Source: Breakdown.Periodic.Glue.Internal.affine_cancel in Breakdown.Torus.Glue, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L51).

**Formula for time-piece index.** With the stated hypotheses, time-piece index obeys the exact identity `stepNumber T lam t = n`. Source: Breakdown.Periodic.Glue.Internal.stepNumber_eq in Breakdown.Torus.Glue, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L55).

**Formula for scaling.** Scaling obeys the exact identity `stepScale T lam (n + 1) = stepScale T lam n * lam`. Source: Breakdown.Periodic.Glue.Internal.scale_succ in Breakdown.Torus.Glue, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L78).

**Formula for piece start time.** Piece start time obeys the exact identity `stepStart T lam (n + 1) = stepStart T lam n + stepScale T lam n * (1 - lam)`. Source: Breakdown.Periodic.Glue.Internal.start_succ in Breakdown.Torus.Glue, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L81).

**Formula for glued flow.** With the stated hypotheses, glued flow obeys the exact identity `gluePieces T lam u (stepStart T lam n + stepScale T lam n * s) = (stepScale T lam n) ^ (-(1 / 4 : ℝ)) • extendPiece (u n) s`. Source: Breakdown.Periodic.Glue.Internal.glue_at in Breakdown.Torus.Glue, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L87).

**Rescale a piecewise Duhamel identity.** A mild solution in the rescaled periodic frame gives the physical periodic Duhamel identity after time dilation by μ and amplitude scaling by μ⁻¹ᐟ⁴. Source: Breakdown.Periodic.Glue.Internal.piece_varConst in Breakdown.Torus.Glue, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L120).

**Continuity of glued flow.** With the stated hypotheses, glued flow is continuous on the domain specified by `ContinuousOn (gluePieces T lam u) (Icc 0 (stepStart T lam n)) ∧ ∀ t ∈ Icc 0 (stepStart T lam n), TorusVarConst (gluePieces T lam u) 0 t`. Source: Breakdown.Periodic.Glue.Internal.glue_upto in Breakdown.Torus.Glue, line 200. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Glue.lean#L200).

### Breakdown.Torus.GlueUnbounded

Evaluates the glued flow at successive starting times and shows that the time scales tend to zero.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.Unbounded.

**Formula for time-piece index.** With the stated hypotheses, time-piece index obeys the exact identity `stepNumber T lam (stepStart T lam n) = n`. Source: Breakdown.Periodic.Internal.Unbounded.stepNumber_stepStart in Breakdown.Torus.GlueUnbounded, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L11).

**Formula for glued physical flow.** With the stated hypotheses, glued physical flow obeys the exact identity `gluePieces T lam u (stepStart T lam n) = (stepScale T lam n) ^ (-(1 / 4 : ℝ)) • u n ⟨0, left_mem_Icc.2 h⟩`. Source: Breakdown.Periodic.Internal.Unbounded.gluePieces_stepStart in Breakdown.Torus.GlueUnbounded, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L21).

**Piece starts precede the final time.** Under the stated positive-time and geometric-ratio assumptions every piece start belongs to [0,T). Source: Breakdown.Periodic.Internal.Unbounded.stepStart_mem in Breakdown.Torus.GlueUnbounded, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L30).

**Limit of piece time scale.** With the stated hypotheses, piece time scale has the limit `Tendsto (fun n : ℕ => stepScale T lam n) atTop (𝓝[>] 0)`. Source: Breakdown.Periodic.Internal.Unbounded.tendsto_stepScale in Breakdown.Torus.GlueUnbounded, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/GlueUnbounded.lean#L39).

### Breakdown.Torus.HeatComparisonAssembly

Converts uniform lattice-sum approximation of the velocity and gradient densities into the shell-norm comparison for forced heat flow.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SourceComparison.Internal.

**Bound for real part.** Real part satisfies the quantitative estimate `‖Freq.realVec z‖ ≤ ‖z‖`. Source: Breakdown.Periodic.SourceComparison.Internal.norm_realVec_le in Breakdown.Torus.HeatComparisonAssembly, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L12).

**Bound for real power.** With the stated hypotheses, real power satisfies the quantitative estimate `W ^ e ≤ max 1 W`. Source: Breakdown.Periodic.SourceComparison.Internal.rpow_le_max in Breakdown.Torus.HeatComparisonAssembly, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L23).

**Bound for coordinate component.** With the stated hypotheses, coordinate component satisfies the quantitative estimate `‖Freq.toLpOrZero p F - u‖ ≤ δ`. Source: Breakdown.Periodic.SourceComparison.Internal.component_norm_le in Breakdown.Torus.HeatComparisonAssembly, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L30).

**Norm for inverse Fourier character.** Inverse Fourier character has the norm identity `‖expChar y ξ‖ = 1`. Source: Breakdown.Periodic.SourceComparison.Internal.norm_expChar in Breakdown.Torus.HeatComparisonAssembly, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L80).

**Continuity of inverse Fourier character.** Inverse Fourier character is continuous on the domain specified by `Continuous fun y => expChar y ξ`. Source: Breakdown.Periodic.SourceComparison.Internal.continuous_expChar in Breakdown.Torus.HeatComparisonAssembly, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L86).

**Continuity of lattice sum.** With the stated hypotheses, lattice sum is continuous on the domain specified by `Continuous fun y => latticeSum h (fun ξ => expChar y ξ • w ξ)`. Source: Breakdown.Periodic.SourceComparison.Internal.continuous_latticeSum in Breakdown.Torus.HeatComparisonAssembly, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L90).

**Formula for forced gradient density.** Forced gradient density obeys the exact identity `gradDensity j τ A y = fun ξ => expChar y ξ • ((2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ)))`. Source: Breakdown.Periodic.SourceComparison.Internal.gradDensity_eq in Breakdown.Torus.HeatComparisonAssembly, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L107).

**Continuity of forced velocity density.** Forced velocity density is continuous on the domain specified by `Continuous fun y => latticeSum h (valueDensity τ A y)`. Source: Breakdown.Periodic.SourceComparison.Internal.continuous_value in Breakdown.Torus.HeatComparisonAssembly, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L113).

**Continuity of gradient.** Gradient is continuous on the domain specified by `Continuous fun y => latticeSum h (gradDensity j τ A y)`. Source: Breakdown.Periodic.SourceComparison.Internal.continuous_grad in Breakdown.Torus.HeatComparisonAssembly, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L117).

**Velocity and gradient densities.** The indexed density family selects the velocity density for `none` and the corresponding gradient density for `some j`. Source: Breakdown.Periodic.SourceComparison.Internal.familyDensity in Breakdown.Torus.HeatComparisonAssembly, line 125. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L125).

**Formula for periodic shell restriction.** Periodic shell restriction obeys the exact identity `restrictTorus μ b z = restrictTorusFun μ b z`. Source: Breakdown.Periodic.SourceComparison.Internal.restrictTorus_apply in Breakdown.Torus.HeatComparisonAssembly, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L129).

**Integrate a fourth-power decay bound.** A Fourier density bounded by `K(1+‖ξ‖)⁻⁴` has integral norm at most K times the integral of that radial decay weight. Source: Breakdown.Periodic.SourceComparison.Internal.integral_bound in Breakdown.Torus.HeatComparisonAssembly, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L131).

**Scaling for periodic shell restriction.** Periodic shell restriction obeys the scalar-scaling identity `restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ (c • A)) - restrictR3 b (Freq.heatDivFree τ (c • A)) = c • (restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A))`. Source: Breakdown.Periodic.SourceComparison.Internal.difference_smul in Breakdown.Torus.HeatComparisonAssembly, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L140).

**Formula for whole-space restriction.** Whole-space restriction obeys the exact identity `restrictR3 b v = (fun j => cutLp 2 b (Freq.partialX j v), cutLp 6 b (Freq.velocity v))`. Source: Breakdown.Periodic.SourceComparison.Internal.restrictR3_apply in Breakdown.Torus.HeatComparisonAssembly, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L153).

**Uniform bound for periodic restriction.** With the stated hypotheses, periodic shell restriction admits the uniform bound stated in `∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ τ ∈ Icc ε ε⁻¹, ∀ A : Freq.L2R, (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) → (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 → ‖restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A)‖ ≤ δ`. Source: Breakdown.Periodic.SourceComparison.Internal.comparison_of_normalized in Breakdown.Torus.HeatComparisonAssembly, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L157).

**Source namespace:** Breakdown.Periodic.

**Periodic forced heat approaches space.** Under the stated assumptions, shrinking-scale periodic projected heat flow converges to whole-space projected heat flow uniformly for elapsed time in [ε,ε⁻¹], with error proportional to the source L³ᐟ² norm. Source: Breakdown.Periodic.heatDivFreeComparison_of in Breakdown.Torus.HeatComparisonAssembly, line 272. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonAssembly.lean#L272).

### Breakdown.Torus.HeatComparisonCoef

Computes Fourier coefficients of transplanted fields by changing variables, including the cell-volume and velocity scale factors.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellCoef.Internal.

**Formula for complexification.** Complexification obeys the exact identity `complexify v = Freq.complexifyVec v`. Source: Breakdown.Periodic.ShellCoef.Internal.complexify_eq_vec in Breakdown.Torus.HeatComparisonCoef, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L12).

**Scaling formula for complexification.** Complexification obeys the scalar-scaling identity `complexify (c • v) = c • complexify v`. Source: Breakdown.Periodic.ShellCoef.Internal.complexify_smul in Breakdown.Torus.HeatComparisonCoef, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L14).

**The central ball lies in the unit cell.** Every point at distance at most 1/4 from the cell center belongs to the unit cell. Source: Breakdown.Periodic.ShellCoef.Internal.mem_cell_of_close in Breakdown.Torus.HeatComparisonCoef, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L18).

**Formula for Fourier character.** Fourier character obeys the exact identity `character k (center + s • y) = character k center * Complex.exp (((-2 * π * inner ℝ y (s • freq k) : ℝ) : ℂ) * Complex.I)`. Source: Breakdown.Periodic.ShellCoef.Internal.character_shift in Breakdown.Torus.HeatComparisonCoef, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L27).

**Fourier change of variables in the cell.** A compact source fitting inside the rescaled cell has Fourier coefficients equal to the source transform at √μk, multiplied by the center phase and cell-volume factor `(√μ)³`. Source: Breakdown.Periodic.ShellCoef.Internal.cell_integral_eq in Breakdown.Torus.HeatComparisonCoef, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L37).

**Formula for cell volume factor.** With the stated hypotheses, cell volume factor obeys the exact identity `(Real.sqrt μ) ^ 3 = μ ^ (3 / 2 : ℝ)`. Source: Breakdown.Periodic.ShellCoef.Internal.sqrt_cube in Breakdown.Torus.HeatComparisonCoef, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L81).

**Formula for inverse volume factor.** With the stated hypotheses, inverse volume factor obeys the exact identity `(Real.sqrt μ)⁻¹ * (Real.sqrt μ) ^ 3 = μ`. Source: Breakdown.Periodic.ShellCoef.Internal.sqrt_inv_cube in Breakdown.Torus.HeatComparisonCoef, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L85).

**Source namespace:** Breakdown.Periodic.

**Fourier coefficients of the source.** Under the stated assumptions, a compact source inside the prescribed cell has coefficients μ^(3/2) times the center phase and its Fourier transform at √μ k. Source: Breakdown.Periodic.sourceCoefFormula in Breakdown.Torus.HeatComparisonCoef, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L95).

**Fourier coefficients of a transplant.** Under the stated assumptions, a transplanted test field inside the prescribed cell has coefficients μ times the center phase and its Fourier transform at √μ k. Source: Breakdown.Periodic.transplantCoefFormula in Breakdown.Torus.HeatComparisonCoef, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonCoef.lean#L100).

### Breakdown.Torus.HeatComparisonDensity

Bounds the forced heat densities and their variation on frequency annuli uniformly for compactly supported normalized sources.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SourceDensity.Internal.

**Bound for complex exponential difference.** Complex exponential difference satisfies the quantitative estimate `‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖ ≤ |a - b|`. Source: Breakdown.Periodic.SourceDensity.Internal.norm_cexp_sub_le in Breakdown.Torus.HeatComparisonDensity, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L12).

**Norm identity for complexification norm.** Complexification norm has the norm identity `‖Freq.complexifyVec z‖ = ‖z‖`. Source: Breakdown.Periodic.SourceDensity.Internal.norm_complexifyVec_eq in Breakdown.Torus.HeatComparisonDensity, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L23).

**Sum formula for inner product.** Inner product obeys the summation identity `(∑ i, ((ξ i : ℝ) : ℂ) * c i) = inner ℂ (Freq.complexifyVec ξ) c`. Source: Breakdown.Periodic.SourceDensity.Internal.inner_eq_sum in Breakdown.Torus.HeatComparisonDensity, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L26).

**Integrability of closed ball.** With the stated hypotheses, closed ball satisfies the integrability assertion `Integrable (⇑A) ∧ ∫ x, ‖A x‖ ≤ (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal`. Source: Breakdown.Periodic.SourceDensity.Internal.l1_bound in Breakdown.Torus.HeatComparisonDensity, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L30).

**Formula for vector Fourier transform.** Vector Fourier transform obeys the exact identity `freqTrVec A ξ = ∫ x, Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I) • Freq.complexifyVec (A x)`. Source: Breakdown.Periodic.SourceDensity.Internal.freqTrVec_eq in Breakdown.Torus.HeatComparisonDensity, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L83).

**The Fourier integrand is measurable.** Complexifying an L² source and multiplying by the forward Fourier character gives an almost-everywhere strongly measurable integrand. Source: Breakdown.Periodic.SourceDensity.Internal.kern_meas in Breakdown.Torus.HeatComparisonDensity, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L88).

**Norm identity for clamped Duhamel kernel.** Clamped Duhamel kernel has the norm identity `‖Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I) • Freq.complexifyVec v‖ = ‖v‖`. Source: Breakdown.Periodic.SourceDensity.Internal.norm_kern in Breakdown.Torus.HeatComparisonDensity, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L95).

**Formula for closed ball.** With the stated hypotheses, closed ball obeys the exact identity `∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) |b'| → A y = 0`. Source: Breakdown.Periodic.SourceDensity.Internal.ae_zero_abs in Breakdown.Torus.HeatComparisonDensity, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L99).

**Bound for vector Fourier transform.** With the stated hypotheses, vector Fourier transform satisfies the quantitative estimate `‖freqTrVec (⇑A) ξ‖ ≤ (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal`. Source: Breakdown.Periodic.SourceDensity.Internal.freqTrVec_bound in Breakdown.Torus.HeatComparisonDensity, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L104).

**Formula for forced Fourier density.** Forced Fourier density obeys the exact identity `|-2 * π * t| = 2 * π * |t|`. Source: Breakdown.Periodic.SourceDensity.Internal.abs_neg_two_pi_mul in Breakdown.Torus.HeatComparisonDensity, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L113).

**Bound for vector Fourier transform.** With the stated hypotheses, vector Fourier transform satisfies the estimate `‖freqTrVec (⇑A) ξ - freqTrVec (⇑A) ξ'‖ ≤ 2 * π * |b'| * (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.freqTrVec_slope in Breakdown.Torus.HeatComparisonDensity, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L117).

**Formula for inverse Fourier character.** Inverse Fourier character obeys the exact identity `expChar y ξ = Complex.exp (↑(2 * π * inner ℝ ξ y) * Complex.I)`. Source: Breakdown.Periodic.SourceDensity.Internal.expChar_eq in Breakdown.Torus.HeatComparisonDensity, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L154).

**Norm for inverse Fourier character.** Inverse Fourier character has the norm identity `‖expChar y ξ‖ = 1`. Source: Breakdown.Periodic.SourceDensity.Internal.norm_expChar in Breakdown.Torus.HeatComparisonDensity, line 161. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L161).

**Bound for inverse Fourier character.** With the stated hypotheses, inverse Fourier character satisfies the estimate `‖expChar y ξ - expChar y ξ'‖ ≤ 2 * π * |b| * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.expChar_slope in Breakdown.Torus.HeatComparisonDensity, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L164).

**Bound for decaying exponential.** With the stated hypotheses, decaying exponential satisfies the quantitative estimate `|Real.exp (-s) - Real.exp (-t)| ≤ |s - t|`. Source: Breakdown.Periodic.SourceDensity.Internal.exp_neg_sub_le in Breakdown.Torus.HeatComparisonDensity, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L179).

**Bound for difference of squared norms.** With the stated hypotheses, difference of squared norms satisfies the quantitative estimate `|‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| ≤ 2 * R * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.sq_norm_sub_le in Breakdown.Torus.HeatComparisonDensity, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L197).

**Nonnegativity of heat multiplier.** Heat multiplier is nonnegative, as stated in `0 ≤ Freq.heatFactor τ ξ`. Source: Breakdown.Periodic.SourceDensity.Internal.heatFactor_nonneg in Breakdown.Torus.HeatComparisonDensity, line 208. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L208).

**Bound for heat multiplier.** Heat multiplier satisfies the quantitative estimate `Freq.heatFactor τ ξ ≤ 1`. Source: Breakdown.Periodic.SourceDensity.Internal.heatFactor_le_one in Breakdown.Torus.HeatComparisonDensity, line 211. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L211).

**Bound for heat multiplier.** With the stated hypotheses, heat multiplier satisfies the estimate `‖Freq.heatFactor τ ξ - Freq.heatFactor τ ξ'‖ ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.heatFactor_slope in Breakdown.Torus.HeatComparisonDensity, line 215. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L215).

**Bound for heat multiplier.** With the stated hypotheses, heat multiplier satisfies the estimate `Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 6 ≤ 8 * (1 + 3 / (4 * π ^ 2 * ε)) ^ 3`. Source: Breakdown.Periodic.SourceDensity.Internal.heatFactor_decay in Breakdown.Torus.HeatComparisonDensity, line 232. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L232).

**Bound for variation bound.** With the stated hypotheses, variation bound satisfies the estimate `‖a • u - a' • u'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d`. Source: Breakdown.Periodic.SourceDensity.Internal.smul_slope in Breakdown.Torus.HeatComparisonDensity, line 272. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L272).

**Bound for inner product.** With the stated hypotheses, inner product satisfies the estimate `‖inner ℂ a c - inner ℂ a' c'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d`. Source: Breakdown.Periodic.SourceDensity.Internal.inner_slope in Breakdown.Torus.HeatComparisonDensity, line 287. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L287).

**Bound for Leray projection.** Leray projection satisfies the quantitative estimate `‖divFreeVec ξ c‖ ≤ 2 * ‖c‖`. Source: Breakdown.Periodic.SourceDensity.Internal.divFreeVec_norm_le in Breakdown.Torus.HeatComparisonDensity, line 302. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L302).

**Formula for Leray projection.** With the stated hypotheses, Leray projection obeys the exact identity `divFreeVec ξ c = c - inner ℂ (Freq.complexifyVec ξ) c • ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ)`. Source: Breakdown.Periodic.SourceDensity.Internal.divFreeVec_eq in Breakdown.Torus.HeatComparisonDensity, line 318. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L318).

**Bound for inverse squared radius.** With the stated hypotheses, inverse squared radius satisfies the estimate `‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) - ((((‖ξ'‖ ^ 2)⁻¹ : ℝ) : ℂ))‖ ≤ 2 * R / (r ^ 2 * r ^ 2) * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.invSq_slope in Breakdown.Torus.HeatComparisonDensity, line 324. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L324).

**Leray projection variation constant.** The projection variation constant combines the Fourier-data bounds with the lower and upper radii of the frequency annulus. Source: Breakdown.Periodic.SourceDensity.Internal.divFreeSlopeConst in Breakdown.Torus.HeatComparisonDensity, line 345. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L345).

**Bound for Leray projection.** With the stated hypotheses, Leray projection satisfies the estimate `‖divFreeVec ξ c - divFreeVec ξ' c'‖ ≤ divFreeSlopeConst r R MF LF * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.SourceDensity.Internal.divFreeVec_slope in Breakdown.Torus.HeatComparisonDensity, line 348. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L348).

**Norm for derivative multiplier norm.** Derivative multiplier norm has the norm identity `‖(2 * π * Complex.I * ((t : ℝ) : ℂ))‖ = 2 * π * |t|`. Source: Breakdown.Periodic.SourceDensity.Internal.norm_two_pi_I_mul in Breakdown.Torus.HeatComparisonDensity, line 384. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L384).

**Source namespace:** Breakdown.Periodic.

**Uniform forced-density decay.** Under the stated assumptions, compact sources with L³ᐟ² norm at most one have uniform fourth-power Fourier-density decay when elapsed time stays in [ε,ε⁻¹]. Source: Breakdown.Periodic.sourceDensityBounds in Breakdown.Torus.HeatComparisonDensity, line 393. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L393).

**Variation of forced Fourier density.** Under the stated assumptions, the normalized forced Fourier densities satisfy uniform Lipschitz bounds on annuli away from zero frequency. Source: Breakdown.Periodic.sourceDensitySlope in Breakdown.Torus.HeatComparisonDensity, line 446. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonDensity.lean#L446).

### Breakdown.Torus.HeatComparisonFreeAssembly

Assembles the lattice-sum comparison for free heat evolution of a compact test field.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.FreeComparison.Internal.

**Bound for real power.** With the stated hypotheses, real power satisfies the quantitative estimate `x ^ q ≤ 1 + x`. Source: Breakdown.Periodic.FreeComparison.Internal.rpow_le_one_add in Breakdown.Torus.HeatComparisonFreeAssembly, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L12).

**Bound for support ball.** With the stated hypotheses, support ball satisfies the quantitative estimate `‖F‖ ≤ c * (volume (Metric.closedBall (0 : Space) b)).toReal ^ (1 / p.toReal)`. Source: Breakdown.Periodic.FreeComparison.Internal.norm_le_of_ae_ball in Breakdown.Torus.HeatComparisonFreeAssembly, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L19).

**Bound for coordinate component.** With the stated hypotheses, coordinate component satisfies the quantitative estimate `‖T - R‖ ≤ c * (1 + (volume (Metric.closedBall (0 : Space) b)).toReal)`. Source: Breakdown.Periodic.FreeComparison.Internal.component_le in Breakdown.Torus.HeatComparisonFreeAssembly, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L32).

**Admissibility of the shell scale.** With the stated hypotheses, the scale and support radius satisfy the shell-geometry constraints in `IsShellScale μ b`. Source: Breakdown.Periodic.FreeComparison.Internal.shellScale_of_lt in Breakdown.Torus.HeatComparisonFreeAssembly, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L47).

**Almost-everywhere form of periodic flow.** With the stated hypotheses, periodic flow has the almost-everywhere representation `((restrictTorus μ b z).1 j : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y)))`. Source: Breakdown.Periodic.FreeComparison.Internal.torus_grad_ae in Breakdown.Torus.HeatComparisonFreeAssembly, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L54).

**Almost-everywhere form of periodic flow.** With the stated hypotheses, periodic flow has the almost-everywhere representation `((restrictTorus μ b z).2 : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y)))`. Source: Breakdown.Periodic.FreeComparison.Internal.torus_value_ae in Breakdown.Torus.HeatComparisonFreeAssembly, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L67).

**Source namespace:** Breakdown.Periodic.

**Periodic free heat approaches space.** Under the stated assumptions, shrinking-scale periodic free heat flow of a transplanted test field converges uniformly on the shell for elapsed time in [0,ε⁻¹]. Source: Breakdown.Periodic.freeHeatComparison_of in Breakdown.Torus.HeatComparisonFreeAssembly, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeAssembly.lean#L83).

### Breakdown.Torus.HeatComparisonFreeDensity

Uses rapid Fourier decay of a test field to control the free heat densities and their variation in frequency.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.FreeDensity.Internal.

**A test transform is a Schwartz field.** The Fourier transform of a smooth compactly supported solenoidal test field is represented by a Schwartz function. Source: Breakdown.Periodic.FreeDensity.Internal.exists_rapid in Breakdown.Torus.HeatComparisonFreeDensity, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L14).

**Fifth-power decay of Schwartz fields.** A Schwartz function admits a nonnegative constant C bounding `(1+‖ξ‖)⁵‖Sξ‖` at every frequency. Source: Breakdown.Periodic.FreeDensity.Internal.rapid_decay in Breakdown.Torus.HeatComparisonFreeDensity, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L24).

**A global slope for a Schwartz field.** A Schwartz function admits a nonnegative global Lipschitz constant. Source: Breakdown.Periodic.FreeDensity.Internal.rapid_slope in Breakdown.Torus.HeatComparisonFreeDensity, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L32).

**Uniform bound for Fourier transform.** With the stated hypotheses, Fourier transform admits the uniform bound stated in `∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ (∀ ξ, (1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖ ≤ C) ∧ (∀ ξ ξ', ‖freqTrVec φ ξ - freqTrVec φ ξ'‖ ≤ L * ‖ξ - ξ'‖)`. Source: Breakdown.Periodic.FreeDensity.Internal.freqTr_bounds in Breakdown.Torus.HeatComparisonFreeDensity, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L42).

**Bound for free Fourier density.** With the stated hypotheses, free Fourier density satisfies the quantitative estimate `‖v‖ ≤ C`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_le_of_pow_five in Breakdown.Torus.HeatComparisonFreeDensity, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L50).

**Norm for inverse Fourier character.** Inverse Fourier character has the norm identity `‖expChar y ξ‖ = 1`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_expChar in Breakdown.Torus.HeatComparisonFreeDensity, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L55).

**Bound for inverse Fourier character.** Inverse Fourier character satisfies the quantitative estimate `‖expChar y ξ - expChar y ξ'‖ ≤ 2 * π * ‖y‖ * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_expChar_sub in Breakdown.Torus.HeatComparisonFreeDensity, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L61).

**Positivity of heat multiplier.** Heat multiplier is strictly positive, as stated in `0 < Freq.heatFactor τ ξ`. Source: Breakdown.Periodic.FreeDensity.Internal.heatFactor_pos in Breakdown.Torus.HeatComparisonFreeDensity, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L76).

**Bound for heat multiplier.** Heat multiplier satisfies the quantitative estimate `Freq.heatFactor τ ξ ≤ 1`. Source: Breakdown.Periodic.FreeDensity.Internal.heatFactor_le_one in Breakdown.Torus.HeatComparisonFreeDensity, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L78).

**Bound for decaying exponential.** With the stated hypotheses, decaying exponential satisfies the quantitative estimate `|Real.exp (-s) - Real.exp (-t)| ≤ |s - t|`. Source: Breakdown.Periodic.FreeDensity.Internal.abs_exp_neg_sub_le in Breakdown.Torus.HeatComparisonFreeDensity, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L84).

**Bound for heat multiplier.** With the stated hypotheses, heat multiplier satisfies the estimate `|Freq.heatFactor τ ξ - Freq.heatFactor τ ξ'| ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.FreeDensity.Internal.heatFactor_sub in Breakdown.Torus.HeatComparisonFreeDensity, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L104).

**Norm identity for coordinate.** Coordinate has the norm identity `‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ = 2 * π * |ξ j|`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_coord_factor in Breakdown.Torus.HeatComparisonFreeDensity, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L127).

**Bound for coordinate.** Coordinate satisfies the quantitative estimate `|ξ j| ≤ ‖ξ‖`. Source: Breakdown.Periodic.FreeDensity.Internal.abs_coord_le in Breakdown.Torus.HeatComparisonFreeDensity, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L132).

**Bound for free Fourier density.** With the stated hypotheses, free Fourier density satisfies the estimate `a ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)`. Source: Breakdown.Periodic.FreeDensity.Internal.le_mul_rpow_of in Breakdown.Torus.HeatComparisonFreeDensity, line 136. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L136).

**Bound for free velocity density.** Free velocity density satisfies the quantitative estimate `‖freeDensity τ φ y ξ‖ ≤ ‖freqTrVec φ ξ‖`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_freeDensity_le in Breakdown.Torus.HeatComparisonFreeDensity, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L143).

**Bound for free gradient density.** Free gradient density satisfies the quantitative estimate `‖freeGradDensity j τ φ y ξ‖ ≤ 2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_freeGradDensity_le in Breakdown.Torus.HeatComparisonFreeDensity, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L151).

**Source namespace:** Breakdown.Periodic.

**Uniform free-density decay.** Under the stated assumptions, a fixed test field has uniform fourth-power decay of its free velocity and gradient densities, including zero elapsed time. Source: Breakdown.Periodic.freeDensityBounds in Breakdown.Torus.HeatComparisonFreeDensity, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L166).

**Source namespace:** Breakdown.Periodic.FreeDensity.Internal.

**Bound for heat evolution.** Heat evolution satisfies the quantitative estimate `‖Freq.heatFactor τ ξ • v‖ ≤ ‖v‖`. Source: Breakdown.Periodic.FreeDensity.Internal.norm_heat_smul_le in Breakdown.Torus.HeatComparisonFreeDensity, line 199. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L199).

**Bound for free velocity density.** With the stated hypotheses, free velocity density satisfies the estimate `‖freeDensity τ φ y ξ - freeDensity τ φ y ξ'‖ ≤ (2 * π * B * C + 4 * π ^ 2 * ε⁻¹ * (2 * R) * C + LF) * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.FreeDensity.Internal.freeDensity_sub in Breakdown.Torus.HeatComparisonFreeDensity, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L204).

**Bound for free gradient density.** With the stated hypotheses, free gradient density satisfies the estimate `‖freeGradDensity j τ φ y ξ - freeGradDensity j τ φ y ξ'‖ ≤ (2 * π * C + 2 * π * R * LD) * ‖ξ - ξ'‖`. Source: Breakdown.Periodic.FreeDensity.Internal.freeGradDensity_sub in Breakdown.Torus.HeatComparisonFreeDensity, line 250. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L250).

**Source namespace:** Breakdown.Periodic.

**Variation of free Fourier density.** Under the stated assumptions, the free velocity and gradient densities of a test field satisfy uniform Lipschitz bounds on frequency annuli. Source: Breakdown.Periodic.freeDensitySlope in Breakdown.Torus.HeatComparisonFreeDensity, line 288. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeDensity.lean#L288).

### Breakdown.Torus.HeatComparisonFreeR3

Identifies the whole-space free heat velocity and gradient with inverse Fourier integrals.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.FreeInverse.Internal.

**Test fields have H¹ regularity.** Every test field satisfies the stated H¹ field condition. Source: Breakdown.Periodic.FreeInverse.Internal.isH1Field_of_test in Breakdown.Torus.HeatComparisonFreeR3, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L18).

**A test field as a Schwartz function.** A smooth compactly supported test field is complexified and packaged as a Schwartz function. Source: Breakdown.Periodic.FreeInverse.Internal.physRapid in Breakdown.Torus.HeatComparisonFreeR3, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L22).

**Formula for vector Fourier transform.** With the stated hypotheses, vector Fourier transform obeys the exact identity `freqTrVec φ ξ = 𝓕 (physRapid hφ) ξ`. Source: Breakdown.Periodic.FreeInverse.Internal.freqTrVec_eq in Breakdown.Torus.HeatComparisonFreeR3, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L26).

**Continuity of heat multiplier.** Heat multiplier is continuous on the domain specified by `Continuous (Freq.heatFactor τ)`. Source: Breakdown.Periodic.FreeInverse.Internal.continuous_heatFactor in Breakdown.Torus.HeatComparisonFreeR3, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L31).

**Bound for heat multiplier.** Heat multiplier satisfies the quantitative estimate `‖Freq.heatFactor τ ξ‖ ≤ 1`. Source: Breakdown.Periodic.FreeInverse.Internal.norm_heatFactor_le in Breakdown.Torus.HeatComparisonFreeR3, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L35).

**Heat-weighted Schwartz data in Lᵖ.** Multiplying a Schwartz field by the source’s heat factor produces an Lᵖ function for every exponent p and every real time parameter. Source: Breakdown.Periodic.FreeInverse.Internal.memLp_heat in Breakdown.Torus.HeatComparisonFreeR3, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L41).

**Formula for inverse Fourier transform.** Inverse Fourier transform obeys the exact identity `𝓕⁻ (fun ξ => Freq.heatFactor τ ξ • T ξ) y = ∫ ξ, expChar y ξ • (Freq.heatFactor τ ξ • T ξ)`. Source: Breakdown.Periodic.FreeInverse.Internal.freqTrInv_heat in Breakdown.Torus.HeatComparisonFreeR3, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L49).

**Physical form of free heat evolution.** With the stated hypotheses, physical representative has the almost-everywhere representation `(toPhys f : Space → Space) =ᵐ[volume] fun y => realVec (∫ ξ, expChar y ξ • (Freq.heatFactor τ ξ • T ξ))`. Source: Breakdown.Periodic.FreeInverse.Internal.toPhys_heat in Breakdown.Torus.HeatComparisonFreeR3, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L60).

**Representative of Fourier representative.** With the stated hypotheses, Fourier representative has the almost-everywhere representation `(freqTrR (Freq.complexify (toLpOrZero 2 φ)) : Space → CSpace) =ᵐ[volume] fun ξ => 𝓕 (physRapid hφ) ξ`. Source: Breakdown.Periodic.FreeInverse.Internal.hat_ae in Breakdown.Torus.HeatComparisonFreeR3, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L76).

**Derivative formula for Fourier transform.** With the stated hypotheses, the derivative calculation gives `𝓕 (∂_{unitVector j} (physRapid hφ)) ξ = (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • 𝓕 (physRapid hφ) ξ`. Source: Breakdown.Periodic.FreeInverse.Internal.freqTr_deriv_eq in Breakdown.Torus.HeatComparisonFreeR3, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L98).

**Source namespace:** Breakdown.Periodic.

**Integral formula for free heat flow.** Under the stated assumptions, whole-space free heat velocity and derivatives agree almost everywhere with the inverse Fourier integrals of their densities. Source: Breakdown.Periodic.r3FreeFormula in Breakdown.Torus.HeatComparisonFreeR3, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonFreeR3.lean#L113).

### Breakdown.Torus.HeatComparisonInverse

Uses Gaussian decay and inverse Fourier compatibility to identify the whole-space forced heat velocity and gradient.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SourceInverse.Internal.

**Integrability of a Gaussian weight.** With the stated hypotheses, Gaussian weight satisfies the integrability assertion `Integrable (fun ξ : Space => Real.exp (-(c * ‖ξ‖ ^ 2)))`. Source: Breakdown.Periodic.SourceInverse.Internal.integrable_expSq in Breakdown.Torus.HeatComparisonInverse, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L17).

**Gaussian decay gives L¹ and L² control.** An almost-everywhere strongly measurable field bounded by a Gaussian with positive decay rate belongs to both L¹ and L². Source: Breakdown.Periodic.SourceInverse.Internal.memLp_of_expSq in Breakdown.Torus.HeatComparisonInverse, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L25).

**Bound for Leray projection.** Leray projection satisfies the quantitative estimate `‖divFreeVec ξ c‖ ≤ 2 * ‖c‖`. Source: Breakdown.Periodic.SourceInverse.Internal.norm_divFreeVec_le in Breakdown.Torus.HeatComparisonInverse, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L41).

**Bound for vector Fourier transform.** Vector Fourier transform satisfies the quantitative estimate `‖freqTrVec A ξ‖ ≤ ∫ x, ‖complexifyVec (A x)‖`. Source: Breakdown.Periodic.SourceInverse.Internal.norm_freqTrVec_le in Breakdown.Torus.HeatComparisonInverse, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L50).

**Formula for heat multiplier.** With the stated hypotheses, heat multiplier obeys the exact identity `Freq.heatFactor τ ξ = Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))`. Source: Breakdown.Periodic.SourceInverse.Internal.heatFactor_eq in Breakdown.Torus.HeatComparisonInverse, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L54).

**Bound for forced heat density.** With the stated hypotheses, forced heat density satisfies the quantitative estimate `‖Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ)‖ ≤ (2 * ∫ x, ‖complexifyVec (A x)‖) * Real.exp (-((4 * π ^ 2 * τ) * ‖ξ‖ ^ 2))`. Source: Breakdown.Periodic.SourceInverse.Internal.norm_source_le in Breakdown.Torus.HeatComparisonInverse, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L59).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `2 * π * t * Real.exp (-((4 * π ^ 2 * τ) * t ^ 2)) ≤ (1 + 2 / τ) * Real.exp (-((2 * π ^ 2 * τ) * t ^ 2))`. Source: Breakdown.Periodic.SourceInverse.Internal.weight_le in Breakdown.Torus.HeatComparisonInverse, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L66).

**Bound for Leray projection.** With the stated hypotheses, Leray projection satisfies the quantitative estimate `‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ))‖ ≤ ((2 * ∫ x, ‖complexifyVec (A x)‖) * (1 + 2 / τ)) * Real.exp (-((2 * π ^ 2 * τ) * ‖ξ‖ ^ 2))`. Source: Breakdown.Periodic.SourceInverse.Internal.norm_gradSource_le in Breakdown.Torus.HeatComparisonInverse, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L87).

**Scaling for derivative multiplier.** Derivative multiplier obeys the scalar-scaling identity `derivSymbol j ξ • ((2 * π * ‖ξ‖) • z) = (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • z`. Source: Breakdown.Periodic.SourceInverse.Internal.derivSymbol_smul in Breakdown.Torus.HeatComparisonInverse, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L111).

**Physical Fourier representative.** With the stated hypotheses, physical representative has the almost-everywhere representation `(toPhys x : Space → Space) =ᵐ[volume] fun y => realVec (∫ ξ, expChar y ξ • F ξ)`. Source: Breakdown.Periodic.SourceInverse.Internal.toPhys_ae in Breakdown.Torus.HeatComparisonInverse, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L122).

**Source namespace:** Breakdown.Periodic.

**Integral formula for forced heat flow.** Under the stated assumptions, whole-space projected heat velocity and derivatives agree almost everywhere with the inverse Fourier integrals of their densities. Source: Breakdown.Periodic.r3ValueFormula_of in Breakdown.Torus.HeatComparisonInverse, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonInverse.lean#L146).

### Breakdown.Torus.HeatComparisonPartition

Proves uniform convergence of lattice sums by separating a compact annulus from small inner and outer tails.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.PartitionSum.Internal.

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `(freq k) i = (k i : ℝ)`. Source: Breakdown.Periodic.PartitionSum.Internal.freq_coord in Breakdown.Torus.HeatComparisonPartition, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L12).

**Bound for lattice cell index.** With the stated hypotheses, lattice cell index satisfies the quantitative estimate `‖ξ - h • freq (latticeIndex h ξ)‖ ≤ 2 * h`. Source: Breakdown.Periodic.PartitionSum.Internal.norm_sub_step_le in Breakdown.Torus.HeatComparisonPartition, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L15).

**Bound for lattice approximation.** With the stated hypotheses, lattice approximation satisfies the quantitative estimate `(1 + ‖ξ'‖) ^ (-4 : ℝ) ≤ 81 * (1 + ‖ξ‖) ^ (-4 : ℝ)`. Source: Breakdown.Periodic.PartitionSum.Internal.decay_le_of_near in Breakdown.Torus.HeatComparisonPartition, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L36).

**Continuity of variation bound.** With the stated hypotheses, variation bound is continuous on the domain specified by `ContinuousOn g {0}ᶜ`. Source: Breakdown.Periodic.PartitionSum.Internal.continuousOn_of_slope in Breakdown.Torus.HeatComparisonPartition, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L56).

**Annular slope bounds imply measurability.** A field with Lipschitz bounds on every annulus away from zero is almost-everywhere strongly measurable on all of space. Source: Breakdown.Periodic.PartitionSum.Internal.aestronglyMeasurable_of_slope in Breakdown.Torus.HeatComparisonPartition, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L80).

**Integrability of lattice approximation.** Lattice approximation satisfies the integrability assertion `Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ (-4 : ℝ))`. Source: Breakdown.Periodic.PartitionSum.Internal.integrable_decay in Breakdown.Torus.HeatComparisonPartition, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L87).

**Exhausting frequency annulus.** The `n`th frequency annulus consists of radii between `(n+1)⁻¹` and `n+1`. Source: Breakdown.Periodic.PartitionSum.Internal.annulus in Breakdown.Torus.HeatComparisonPartition, line 92. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L92).

**Equivalent forms of frequency annulus.** Frequency annulus has the equivalent characterizations `ξ ∈ annulus n ↔ ((n : ℝ) + 1)⁻¹ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (n : ℝ) + 1`. Source: Breakdown.Periodic.PartitionSum.Internal.mem_annulus in Breakdown.Torus.HeatComparisonPartition, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L94).

**Measurability of frequency annulus.** Frequency annulus has the measurability property `MeasurableSet (annulus n)`. Source: Breakdown.Periodic.PartitionSum.Internal.measurableSet_annulus in Breakdown.Torus.HeatComparisonPartition, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L97).

**Uniform bound for geometric tail.** With the stated hypotheses, geometric tail admits the uniform bound stated in `∃ n : ℕ, ∫ ξ in (annulus n)ᶜ, (1 + ‖ξ‖) ^ (-4 : ℝ) ≤ ε`. Source: Breakdown.Periodic.PartitionSum.Internal.exists_tail_le in Breakdown.Torus.HeatComparisonPartition, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L101).

**Bound for lattice approximation.** With the stated hypotheses, lattice approximation satisfies the quantitative estimate `c * (δ / (2 * (c + 1))) ≤ δ / 2`. Source: Breakdown.Periodic.PartitionSum.Internal.mul_div_two_succ_le in Breakdown.Torus.HeatComparisonPartition, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L139).

**Source namespace:** Breakdown.Periodic.

**Uniform lattice approximation.** Under the stated assumptions, uniform fourth-power decay and annular Lipschitz bounds make lattice sums converge uniformly to the corresponding integrals. Source: Breakdown.Periodic.partitionSumBound_of_step in Breakdown.Torus.HeatComparisonPartition, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonPartition.lean#L151).

### Breakdown.Torus.HeatComparisonProj

Matches the finite-dimensional divergence-free projection with the whole-space Fourier projection and its heat multiplier.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.DivFreeProjection.Internal.

**Formula for longitudinal projection.** Longitudinal projection obeys the exact identity `(longitudinal ξ z) j = (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ i, ((ξ i : ℝ) : ℂ) * z i) * ((ξ j : ℝ) : ℂ)`. Source: Breakdown.Periodic.DivFreeProjection.Internal.longitudinal_coord in Breakdown.Torus.HeatComparisonProj, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L16).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFreeVec ξ c = c - longitudinal ξ c`. Source: Breakdown.Periodic.DivFreeProjection.Internal.divFreeVec_eq in Breakdown.Torus.HeatComparisonProj, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L22).

**Sign formula for complex conjugation.** Complex conjugation obeys the sign-change identity `conjVec (longitudinal (-ξ) z) = longitudinal ξ (conjVec z)`. Source: Breakdown.Periodic.DivFreeProjection.Internal.conj_longitudinal_neg in Breakdown.Torus.HeatComparisonProj, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L33).

**Formula for longitudinal projection.** Longitudinal projection obeys the exact identity `longitudinal ξ (z - longitudinal ξ z) = 0`. Source: Breakdown.Periodic.DivFreeProjection.Internal.longitudinal_proj in Breakdown.Torus.HeatComparisonProj, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L44).

**Real and complex inner products agree.** The underlying real inner product of two complex coefficient vectors is the real part of their complex inner product. Source: Breakdown.Periodic.DivFreeProjection.Internal.real_inner_coef in Breakdown.Torus.HeatComparisonProj, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L61).

**Pairing with the longitudinal part.** Longitudinal projection pairing obeys the exact identity `inner ℝ (longitudinal ξ a) b = inner ℝ a (longitudinal ξ b)`. Source: Breakdown.Periodic.DivFreeProjection.Internal.inner_longitudinal in Breakdown.Torus.HeatComparisonProj, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L63).

**Representative of Fourier transform.** With the stated hypotheses, Fourier transform has the almost-everywhere representation `(freqTrR (Freq.complexify A) : Space → CSpace) =ᵐ[volume] freqTrVec (⇑A)`. Source: Breakdown.Periodic.DivFreeProjection.Internal.freqTr_ae in Breakdown.Torus.HeatComparisonProj, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L72).

**Sign formula for heat multiplier.** Heat multiplier obeys the sign-change identity `Freq.heatFactor τ (-ξ) = Freq.heatFactor τ ξ`. Source: Breakdown.Periodic.DivFreeProjection.Internal.heatFactor_neg in Breakdown.Torus.HeatComparisonProj, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L95).

**Sign formula of gradient heat multiplier.** Gradient heat multiplier obeys the sign-change identity `phiFactor τ (-ξ) = phiFactor τ ξ`. Source: Breakdown.Periodic.DivFreeProjection.Internal.phiFactor_neg in Breakdown.Torus.HeatComparisonProj, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L98).

**Bound for heat evolution.** Heat evolution satisfies the quantitative estimate `‖Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1`. Source: Breakdown.Periodic.DivFreeProjection.Internal.norm_heat_smul_le in Breakdown.Torus.HeatComparisonProj, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L101).

**Bound for gradient heat multiplier.** With the stated hypotheses, gradient heat multiplier satisfies the quantitative estimate `‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + 1 / τ`. Source: Breakdown.Periodic.DivFreeProjection.Internal.norm_phi_smul_le in Breakdown.Torus.HeatComparisonProj, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L110).

**Almost-everywhere form of heat evolution.** With the stated hypotheses, heat evolution has the almost-everywhere representation `(fieldOp id (fun ξ => Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace) =ᵐ[volume] fun ξ => Freq.heatFactor τ ξ • f ξ`. Source: Breakdown.Periodic.DivFreeProjection.Internal.heat_ae in Breakdown.Torus.HeatComparisonProj, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L131).

**Gradient multiplier representative.** With the stated hypotheses, gradient heat multiplier has the almost-everywhere representation `(fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • f ξ`. Source: Breakdown.Periodic.DivFreeProjection.Internal.phi_ae in Breakdown.Torus.HeatComparisonProj, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L140).

**Projection gives a real solenoidal field.** Subtracting the longitudinal component of a Fourier field fixed by reflection-conjugation gives an element of the real solenoidal subspace, assuming the field-operator realization. Source: Breakdown.Periodic.DivFreeProjection.Internal.divFree_mem_sig in Breakdown.Torus.HeatComparisonProj, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L149).

**Formula for longitudinal projection.** With the stated hypotheses, longitudinal projection obeys the exact identity `∀ᵐ ξ ∂volume, longitudinal ξ (t ξ) = 0`. Source: Breakdown.Periodic.DivFreeProjection.Internal.ae_longitudinal_of_mem in Breakdown.Torus.HeatComparisonProj, line 171. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L171).

**Source namespace:** Breakdown.Periodic.

**Factor projected heat evolution.** Under the stated assumptions, projected heat flow has the stated half-Laplacian multiplier factorization in Fourier space. Source: Breakdown.Periodic.heatDivFreeFactor in Breakdown.Torus.HeatComparisonProj, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonProj.lean#L182).

### Breakdown.Torus.HeatComparisonSeries

Identifies an absolutely convergent periodic Fourier series with its Lᵖ representative almost everywhere.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.TorusSeriesEval.Internal.

**Norm identity for Fourier summand.** Fourier summand has the norm identity `‖term c k x‖ = ‖c k‖`. Source: Breakdown.Periodic.TorusSeriesEval.Internal.norm_term in Breakdown.Torus.HeatComparisonSeries, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L14).

**Pointwise Fourier series limit.** The pointwise limit is the infinite sum of the Fourier summands. Source: Breakdown.Periodic.TorusSeriesEval.Internal.limitFn in Breakdown.Torus.HeatComparisonSeries, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L17).

**Continuity of Fourier series limit.** With the stated hypotheses, Fourier series limit is continuous on the domain specified by `Continuous (limitFn c)`. Source: Breakdown.Periodic.TorusSeriesEval.Internal.continuous_limitFn in Breakdown.Torus.HeatComparisonSeries, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L19).

**Bound for Fourier series limit.** With the stated hypotheses, Fourier series limit satisfies the quantitative estimate `‖limitFn c x - partialSum c s x‖ ≤ ∑' k, ‖c k‖ - ∑ k ∈ s, ‖c k‖`. Source: Breakdown.Periodic.TorusSeriesEval.Internal.norm_limitFn_sub_le in Breakdown.Torus.HeatComparisonSeries, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L23).

**Sum of Fourier character.** With the stated hypotheses, Fourier character has the exact series sum in `HasSum (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)) ((memLp_of_continuous p (continuous_limitFn c hc)).toLp (limitFn c))`. Source: Breakdown.Periodic.TorusSeriesEval.Internal.hasSum_toLp in Breakdown.Torus.HeatComparisonSeries, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L41).

**Representative of Fourier series.** With the stated hypotheses, periodic Fourier series has the almost-everywhere representation `(torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell] (fun x => ∑' k, character (-k) x • c k)`. Source: Breakdown.Periodic.TorusSeriesEval.Internal.coeFn_torusSeries in Breakdown.Torus.HeatComparisonSeries, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L63).

**Source namespace:** Breakdown.Periodic.

**Pointwise Fourier representatives.** Under the stated assumptions, an absolutely summable coefficient sequence represents its periodic L² and L⁶ Fourier series almost everywhere. Source: Breakdown.Periodic.torusSeriesPointwise in Breakdown.Torus.HeatComparisonSeries, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonSeries.lean#L72).

### Breakdown.Torus.HeatComparisonStatements

Defines the Fourier densities and lattice-sum propositions used to compare periodic and whole-space heat evolution.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Continuous-frequency Leray projection.** At nonzero frequency the projection subtracts the longitudinal component, while at zero frequency it keeps the input vector. Source: Breakdown.Periodic.divFreeVec in Breakdown.Torus.HeatComparisonStatements, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L10).

**Fourier transform of a real field.** The vector Fourier transform applies the Fourier integral to the complexified real field. Source: Breakdown.Periodic.freqTrVec in Breakdown.Torus.HeatComparisonStatements, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L13).

**Inverse Fourier character.** The inverse Fourier character is `exp(2πi⟨ξ,y⟩)`. Source: Breakdown.Periodic.expChar in Breakdown.Torus.HeatComparisonStatements, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L16).

**Forced velocity Fourier density.** The forced velocity density multiplies the projected Fourier transform by the heat factor and the inverse Fourier character. Source: Breakdown.Periodic.valueDensity in Breakdown.Torus.HeatComparisonStatements, line 18. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L18).

**Forced gradient Fourier density.** The `j`th forced gradient density multiplies the velocity density by the derivative factor `2πi ξⱼ`. Source: Breakdown.Periodic.gradDensity in Breakdown.Torus.HeatComparisonStatements, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L21).

**Free velocity Fourier density.** The free velocity density multiplies the Fourier transform of the test field by the heat factor and inverse Fourier character. Source: Breakdown.Periodic.freeDensity in Breakdown.Torus.HeatComparisonStatements, line 24. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L24).

**Free gradient Fourier density.** The `j`th free gradient density multiplies the free velocity density by `2πi ξⱼ`. Source: Breakdown.Periodic.freeGradDensity in Breakdown.Torus.HeatComparisonStatements, line 27. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L27).

**Volume-weighted lattice sum.** The lattice sum multiplies the sum over frequencies `h k` by the cell volume `h³`. Source: Breakdown.Periodic.latticeSum in Breakdown.Torus.HeatComparisonStatements, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L30).

**Index of a lattice cube.** The lattice index takes the floor of each coordinate divided by the mesh size. Source: Breakdown.Periodic.latticeIndex in Breakdown.Torus.HeatComparisonStatements, line 32. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L32).

**Integral of a lattice step function.** This proposition requires that a lattice step function with the stated decay is integrable and its integral equals h³ times its lattice sum for h > 0. Source: Breakdown.Periodic.StepIntegral in Breakdown.Torus.HeatComparisonStatements, line 34. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L34).

**Uniform lattice approximation.** This proposition requires that uniform fourth-power decay and annular Lipschitz bounds make lattice sums converge uniformly to the corresponding integrals. Source: Breakdown.Periodic.PartitionSumBound in Breakdown.Torus.HeatComparisonStatements, line 41. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L41).

**Pointwise Fourier representatives.** This proposition requires that an absolutely summable coefficient sequence represents its periodic L² and L⁶ Fourier series almost everywhere. Source: Breakdown.Periodic.TorusSeriesPointwise in Breakdown.Torus.HeatComparisonStatements, line 49. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L49).

**Fourier coefficients of the source.** This proposition requires that a compact source inside the prescribed cell has coefficients μ^(3/2) times the center phase and its Fourier transform at √μ k. Source: Breakdown.Periodic.SourceCoefFormula in Breakdown.Torus.HeatComparisonStatements, line 54. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L54).

**Fourier coefficients of a transplant.** This proposition requires that a transplanted test field inside the prescribed cell has coefficients μ times the center phase and its Fourier transform at √μ k. Source: Breakdown.Periodic.TransplantCoefFormula in Breakdown.Torus.HeatComparisonStatements, line 60. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L60).

**Lattice series for forced heat flow.** This proposition requires that the shell velocity and gradient of periodic forced heat flow agree almost everywhere with lattice sums at mesh √μ. Source: Breakdown.Periodic.TorusSourceSeries in Breakdown.Torus.HeatComparisonStatements, line 65. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L65).

**Lattice series for free heat flow.** This proposition requires that the shell velocity and gradient of a transplanted free heat flow agree almost everywhere with lattice sums at mesh √μ, including zero elapsed time. Source: Breakdown.Periodic.TorusFreeSeries in Breakdown.Torus.HeatComparisonStatements, line 76. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L76).

**Factor projected heat evolution.** This proposition requires that projected heat flow has the stated half-Laplacian multiplier factorization in Fourier space. Source: Breakdown.Periodic.HeatDivFreeFactor in Breakdown.Torus.HeatComparisonStatements, line 88. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L88).

**Integral formula for forced heat flow.** This proposition requires that whole-space projected heat velocity and derivatives agree almost everywhere with the inverse Fourier integrals of their densities. Source: Breakdown.Periodic.R3ValueFormula in Breakdown.Torus.HeatComparisonStatements, line 95. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L95).

**Integral formula for free heat flow.** This proposition requires that whole-space free heat velocity and derivatives agree almost everywhere with the inverse Fourier integrals of their densities. Source: Breakdown.Periodic.R3FreeFormula in Breakdown.Torus.HeatComparisonStatements, line 103. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L103).

**Uniform forced-density decay.** This proposition requires that compact sources with L³ᐟ² norm at most one have uniform fourth-power Fourier-density decay when elapsed time stays in [ε,ε⁻¹]. Source: Breakdown.Periodic.SourceDensityBounds in Breakdown.Torus.HeatComparisonStatements, line 110. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L110).

**Variation of forced Fourier density.** This proposition requires that the normalized forced Fourier densities satisfy uniform Lipschitz bounds on annuli away from zero frequency. Source: Breakdown.Periodic.SourceDensitySlope in Breakdown.Torus.HeatComparisonStatements, line 117. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L117).

**Uniform free-density decay.** This proposition requires that a fixed test field has uniform fourth-power decay of its free velocity and gradient densities, including zero elapsed time. Source: Breakdown.Periodic.FreeDensityBounds in Breakdown.Torus.HeatComparisonStatements, line 125. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L125).

**Variation of free Fourier density.** This proposition requires that the free velocity and gradient densities of a test field satisfy uniform Lipschitz bounds on frequency annuli. Source: Breakdown.Periodic.FreeDensitySlope in Breakdown.Torus.HeatComparisonStatements, line 131. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStatements.lean#L131).

### Breakdown.Torus.HeatComparisonStep

Computes the measure and integral of lattice step functions and controls their approximation cells.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.StepSum.Internal.

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `(freq k) i = (k i : ℝ)`. Source: Breakdown.Periodic.StepSum.Internal.freq_coord in Breakdown.Torus.HeatComparisonStep, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L12).

**Measurability of lattice cell index.** With the stated hypotheses, lattice cell index has the measurability property `Measurable (latticeIndex h)`. Source: Breakdown.Periodic.StepSum.Internal.measurable_latticeIndex in Breakdown.Torus.HeatComparisonStep, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L15).

**Formula for lattice fiber.** With the stated hypotheses, lattice fiber obeys the exact identity `latticeIndex h ⁻¹' {k} = (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' (pi univ fun i => Ico (h * k i) (h * k i + h))`. Source: Breakdown.Periodic.StepSum.Internal.fibre_eq in Breakdown.Torus.HeatComparisonStep, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L21).

**Formula for lattice fiber.** With the stated hypotheses, lattice fiber obeys the exact identity `volume (latticeIndex h ⁻¹' {k}) = ENNReal.ofReal (h ^ 3)`. Source: Breakdown.Periodic.StepSum.Internal.volume_fibre in Breakdown.Torus.HeatComparisonStep, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L41).

**Formula for lattice cell index.** With the stated hypotheses, lattice cell index obeys the exact identity `(Measure.map (latticeIndex h) volume) {k} = ENNReal.ofReal (h ^ 3)`. Source: Breakdown.Periodic.StepSum.Internal.map_singleton in Breakdown.Torus.HeatComparisonStep, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L49).

**Formula for lattice cell index.** With the stated hypotheses, lattice cell index obeys the exact identity `∫⁻ ξ, c (latticeIndex h ξ) = ENNReal.ofReal (h ^ 3) * ∑' k, c k`. Source: Breakdown.Periodic.StepSum.Internal.lintegral_step in Breakdown.Torus.HeatComparisonStep, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L54).

**Integrability of lattice cell index.** With the stated hypotheses, lattice cell index satisfies the integrability assertion `Integrable (fun ξ => c (latticeIndex h ξ))`. Source: Breakdown.Periodic.StepSum.Internal.integrable_step in Breakdown.Torus.HeatComparisonStep, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L60).

**Integrate a lattice step function.** For h > 0 and absolutely summable cell values, the step-function integral equals h³ times the sum of those values. Source: Breakdown.Periodic.StepSum.Internal.integral_step in Breakdown.Torus.HeatComparisonStep, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L73).

**Bound for lattice cell index.** With the stated hypotheses, lattice cell index satisfies the estimate `‖ξ - h • freq (latticeIndex h ξ)‖ ≤ 2 * h`. Source: Breakdown.Periodic.StepSum.Internal.near_lattice in Breakdown.Torus.HeatComparisonStep, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L83).

**Bound for lattice cell index.** With the stated hypotheses, lattice cell index satisfies the estimate `(1 + ‖h • freq (latticeIndex h ξ)‖) ^ (-4 : ℝ) ≤ (1 + 2 * h) ^ 4 * (1 + ‖ξ‖) ^ (-4 : ℝ)`. Source: Breakdown.Periodic.StepSum.Internal.decay_lattice in Breakdown.Torus.HeatComparisonStep, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L104).

**Summability of frequency lattice.** With the stated hypotheses, frequency lattice satisfies the series-convergence assertion `Summable (fun k : Lattice => (1 + ‖h • freq k‖) ^ (-4 : ℝ))`. Source: Breakdown.Periodic.StepSum.Internal.summable_decay in Breakdown.Torus.HeatComparisonStep, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L126).

**Source namespace:** Breakdown.Periodic.

**Integral of a lattice step function.** Under the stated assumptions, a lattice step function with the stated decay is integrable and its integral equals h³ times its lattice sum for h > 0. Source: Breakdown.Periodic.stepIntegral in Breakdown.Torus.HeatComparisonStep, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonStep.lean#L147).

### Breakdown.Torus.HeatComparisonTorusSide

Rewrites periodic heat series in similarity coordinates as lattice sums of the same densities used on the whole space.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.TorusShellSeries.Internal.

**Formula for cell center.** Cell center obeys the exact identity `center i = 1 / 2`. Source: Breakdown.Periodic.TorusShellSeries.Internal.center_apply in Breakdown.Torus.HeatComparisonTorusSide, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L13).

**The rescaled ball fits inside the cell.** If h > 0 and hb ≤ 1/8, every y in the radius-b ball gives a point `center + h • y` in the unit cell. Source: Breakdown.Periodic.TorusShellSeries.Internal.mem_cell in Breakdown.Torus.HeatComparisonTorusSide, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L16).

**Affine map preserves null sets.** For h ≠ 0, the affine map `y ↦ center + h • y` is quasi measure preserving for Lebesgue measure, so preimages of null sets are null. Source: Breakdown.Periodic.TorusShellSeries.Internal.qmp_affine in Breakdown.Torus.HeatComparisonTorusSide, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L33).

**Equivalent forms of lattice frequency.** Lattice frequency has the equivalent characterizations `freq k = 0 ↔ k = 0`. Source: Breakdown.Periodic.TorusShellSeries.Internal.freq_eq_zero in Breakdown.Torus.HeatComparisonTorusSide, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L38).

**Formula for heat multiplier.** With the stated hypotheses, heat multiplier obeys the exact identity `heatFactor (μ * t) k = Freq.heatFactor t (Real.sqrt μ • freq k)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.heatFactor_eq in Breakdown.Torus.HeatComparisonTorusSide, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L47).

**Formula for Leray projection.** With the stated hypotheses, Leray projection obeys the exact identity `divFree k c = divFreeVec (h • freq k) c`. Source: Breakdown.Periodic.TorusShellSeries.Internal.divFree_eq in Breakdown.Torus.HeatComparisonTorusSide, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L55).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFreeVec ξ (w • c) = w • divFreeVec ξ c`. Source: Breakdown.Periodic.TorusShellSeries.Internal.divFreeVec_csmul in Breakdown.Torus.HeatComparisonTorusSide, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L79).

**Formula for Fourier character.** With the stated hypotheses, Fourier character obeys the exact identity `character (-k) (center + h • y) * character k center = expChar y (h • freq k)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.character_shift in Breakdown.Torus.HeatComparisonTorusSide, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L87).

**Scaling formula for Fourier coefficient.** Fourier coefficient obeys the scalar-scaling identity `coeff (r • u) k = r • coeff u k`. Source: Breakdown.Periodic.TorusShellSeries.Internal.coeff_smul in Breakdown.Torus.HeatComparisonTorusSide, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L96).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `coeff (sourceOp μ τ A) k = heatFactor (μ * τ) k • divFree k (freqTrCoef (fun x => (A : Space → Space) (simCoord μ x)) k)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.coeff_sourceOp in Breakdown.Torus.HeatComparisonTorusSide, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L100).

**Formula for cell volume factor.** With the stated hypotheses, cell volume factor obeys the exact identity `μ ^ (3 / 2 : ℝ) = Real.sqrt μ ^ 3`. Source: Breakdown.Periodic.TorusShellSeries.Internal.rpow_three_halves in Breakdown.Torus.HeatComparisonTorusSide, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L111).

**Formula for quarter-power cancellation.** With the stated hypotheses, quarter-power cancellation obeys the exact identity `μ ^ (1 / 4 : ℝ) * μ ^ (-(1 / 4 : ℝ)) = 1`. Source: Breakdown.Periodic.TorusShellSeries.Internal.rpow_quarter_mul in Breakdown.Torus.HeatComparisonTorusSide, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L115).

**Formula for forced heat series.** With the stated hypotheses, forced heat series obeys the exact identity `character (-k) (center + Real.sqrt μ • y) • ((μ ^ (1 / 4 : ℝ)) • coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) k) = (Real.sqrt μ ^ 3) • valueDensity τ (⇑A) y (Real.sqrt μ • freq k)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.source_value in Breakdown.Torus.HeatComparisonTorusSide, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L119).

**Formula for rescaled pullback.** With the stated hypotheses, rescaled pullback obeys the exact identity `∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)), s • (torusSeries p c : Space → Coef) (center + h • y) = latticeSum h (G y)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.series_pullback in Breakdown.Torus.HeatComparisonTorusSide, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L142).

**Formula for gradient.** With the stated hypotheses, gradient obeys the exact identity `character (-k) (center + h • y) • ((s * h) • ((2 * π * Complex.I * (k j : ℂ)) • c k)) = (h ^ 3) • ((2 * π * Complex.I * (((h • freq k) j : ℝ) : ℂ)) • G y (h • freq k))`. Source: Breakdown.Periodic.TorusShellSeries.Internal.grad_identity in Breakdown.Torus.HeatComparisonTorusSide, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L159).

**Formula for free heat scaling.** With the stated hypotheses, free heat scaling obeys the exact identity `μ ^ (1 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) * μ = Real.sqrt μ ^ 3`. Source: Breakdown.Periodic.TorusShellSeries.Internal.rpow_free in Breakdown.Torus.HeatComparisonTorusSide, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L173).

**Formula for gradient scaling.** With the stated hypotheses, gradient scaling obeys the exact identity `μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * Real.sqrt μ`. Source: Breakdown.Periodic.TorusShellSeries.Internal.rpow_grad in Breakdown.Torus.HeatComparisonTorusSide, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L178).

**Formula for transplanted field.** With the stated hypotheses, transplanted field obeys the exact identity `character (-k) (center + Real.sqrt μ • y) • ((μ ^ (1 / 4 : ℝ)) • coeff ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ))) k) = (Real.sqrt μ ^ 3) • freeDensity τ φ y (Real.sqrt μ • freq k)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.free_value in Breakdown.Torus.HeatComparisonTorusSide, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L182).

**Summability of heat evolution.** With the stated hypotheses, heat evolution satisfies the series-convergence assertion `Summable (heatFactor t)`. Source: Breakdown.Periodic.TorusShellSeries.Internal.summable_heat in Breakdown.Torus.HeatComparisonTorusSide, line 206. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L206).

**Bound for Fourier coefficient.** With the stated hypotheses, Fourier coefficient satisfies the quantitative estimate `‖coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) k‖ ≤ (μ ^ (-(1 / 4 : ℝ)) * (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord μ x))‖)) * heatFactor (μ * τ) k`. Source: Breakdown.Periodic.TorusShellSeries.Internal.norm_coeff_source_le in Breakdown.Torus.HeatComparisonTorusSide, line 212. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L212).

**Summability of gradient.** With the stated hypotheses, gradient satisfies the series-convergence assertion `Summable fun k => ‖gradCoef j z k‖`. Source: Breakdown.Periodic.TorusShellSeries.Internal.summable_grad_of_bound in Breakdown.Torus.HeatComparisonTorusSide, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L228).

**Summability of rescaled Fourier series.** With the stated hypotheses, rescaled Fourier series satisfies the series-convergence assertion `Summable fun k => ‖c k‖`. Source: Breakdown.Periodic.TorusShellSeries.Internal.summable_of_density in Breakdown.Torus.HeatComparisonTorusSide, line 248. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L248).

**Source namespace:** Breakdown.Periodic.

**Lattice series for forced heat flow.** Under the stated assumptions, the shell velocity and gradient of periodic forced heat flow agree almost everywhere with lattice sums at mesh √μ. Source: Breakdown.Periodic.torusSourceSeries_of in Breakdown.Torus.HeatComparisonTorusSide, line 269. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L269).

**Lattice series for free heat flow.** Under the stated assumptions, the shell velocity and gradient of a transplanted free heat flow agree almost everywhere with lattice sums at mesh √μ, including zero elapsed time. Source: Breakdown.Periodic.torusFreeSeries_of in Breakdown.Torus.HeatComparisonTorusSide, line 287. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparisonTorusSide.lean#L287).

### Breakdown.Torus.HeatDivFreeCont

Establishes strong continuity in positive time for the whole-space heat and divergence-free operator.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.HeatDivFreeCont.Internal.

**Gradient heat multiplier on L².** The operator applies the Fourier multiplier `phiFactor τ` to an L² complex field. Source: Breakdown.Periodic.HeatDivFreeCont.Internal.phiOp in Breakdown.Torus.HeatDivFreeCont, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L14).

**Continuity of gradient heat multiplier.** Gradient heat multiplier is continuous on the domain specified by `Continuous (fun τ => phiFactor τ ξ)`. Source: Breakdown.Periodic.HeatDivFreeCont.Internal.continuous_phiFactor_time in Breakdown.Torus.HeatDivFreeCont, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L17).

**Representative of gradient heat operator.** With the stated hypotheses, gradient heat operator has the almost-everywhere representation `(phiOp τ g : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • (g : Space → CSpace) ξ`. Source: Breakdown.Periodic.HeatDivFreeCont.Internal.phiOp_ae in Breakdown.Torus.HeatDivFreeCont, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L21).

**Bound for gradient heat multiplier.** With the stated hypotheses, gradient heat multiplier satisfies the quantitative estimate `(phiFactor τ ξ - phiFactor τ₀ ξ) ^ 2 ≤ 6 / τ₀`. Source: Breakdown.Periodic.HeatDivFreeCont.Internal.sub_sq_phiFactor_le in Breakdown.Torus.HeatDivFreeCont, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L25).

**Continuity of gradient heat operator.** With the stated hypotheses, gradient heat operator is continuous on the domain specified by `ContinuousOn (fun τ => phiOp τ g) (Ioi 0)`. Source: Breakdown.Periodic.HeatDivFreeCont.Internal.phiOp_continuousOn in Breakdown.Torus.HeatDivFreeCont, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L38).

**Source namespace:** Breakdown.Periodic.

**Strong continuity after projection.** Assuming the Fourier field-operator realization, projected heat evolution of every L² source is continuous for positive elapsed time. Source: Breakdown.Periodic.heatDivFree_continuousOn in Breakdown.Torus.HeatDivFreeCont, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatDivFreeCont.lean#L85).

### Breakdown.Torus.InverseAlgebra

Records the two inverse identities for one minus a bounded operator of norm less than one.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.InverseAlgebra.Internal.

**Invert one minus a strict contraction.** A bounded linear operator of norm less than one makes one minus that operator invertible. Source: Breakdown.Periodic.InverseAlgebra.Internal.isUnit_one_sub_clm in Breakdown.Torus.InverseAlgebra, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L13).

**Formula for resolvent inverse.** With the stated hypotheses, resolvent inverse obeys the exact identity `Ring.inverse (1 - T) (x - T x) = x`. Source: Breakdown.Periodic.InverseAlgebra.Internal.inverse_one_sub_apply_sub in Breakdown.Torus.InverseAlgebra, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L25).

**Formula for resolvent inverse.** With the stated hypotheses, resolvent inverse obeys the exact identity `Ring.inverse (1 - T) y - T (Ring.inverse (1 - T) y) = y`. Source: Breakdown.Periodic.InverseAlgebra.Internal.sub_apply_inverse_one_sub in Breakdown.Torus.InverseAlgebra, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L31).

### Breakdown.Torus.InverseDefs

Defines the bounded sequences of time pieces, finite test-field approximants and the restriction, shift and seed operators.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Bounded whole-space time pieces.** The whole-space sequence space is the space of bounded sequences of continuous time pieces valued in the Fourier space `X`. Source: Breakdown.Periodic.R3Seq in Breakdown.Torus.InverseDefs, line 13. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L13).

**Bounded periodic time pieces.** The periodic sequence space is the space of bounded sequences of continuous time pieces valued in `V`. Source: Breakdown.Periodic.TorusSeq in Breakdown.Torus.InverseDefs, line 15. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L15).

**Bounded shell-data time pieces.** The shell sequence space is the space of bounded sequences of continuous shell-data time pieces. Source: Breakdown.Periodic.ShellSeq in Breakdown.Torus.InverseDefs, line 17. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L17).

**Finite test-field approximation data.** An approximant records finitely many smooth solenoidal test fields per time piece, a common support radius, continuous scalar weights and a uniform bound. Source: Breakdown.Periodic.Approximant in Breakdown.Torus.InverseDefs, line 19. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L19).

**Source namespace:** Breakdown.Periodic.Approximant.

**Whole-space approximating time piece.** The whole-space approximating piece sums the embedded test fields with their continuous time weights. Source: Breakdown.Periodic.Approximant.r3Piece in Breakdown.Torus.InverseDefs, line 27. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L27).

**Periodic approximating time piece.** The periodic approximating piece sums the transplanted test fields with their time weights and the factor `μ^(1/4)`. Source: Breakdown.Periodic.Approximant.torusPiece in Breakdown.Torus.InverseDefs, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L30).

**Source namespace:** Breakdown.Periodic.

**Whole-space sequence restriction.** Whole-space sequence restriction applies the shell restriction at every time and every sequence index. Source: Breakdown.Periodic.r3Restrict in Breakdown.Torus.InverseDefs, line 40. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L40).

**Periodic sequence restriction.** Periodic sequence restriction uses the shell restriction at the geometric scale of each sequence index. Source: Breakdown.Periodic.torusRestrict in Breakdown.Torus.InverseDefs, line 42. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L42).

**Whole-space sequence shift.** The whole-space sequence shift propagates the preceding endpoint by the free step and the factor `θ⁻¹`. Source: Breakdown.Periodic.r3Shift in Breakdown.Torus.InverseDefs, line 45. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L45).

**Periodic sequence shift.** The periodic sequence shift propagates the preceding endpoint in the next time scale with factor `λ^(1/4)/θ`. Source: Breakdown.Periodic.torusShift in Breakdown.Torus.InverseDefs, line 49. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L49).

**Whole-space initial-data injection.** The whole-space seed inserts the free evolution of the lifted initial correction into the first time piece. Source: Breakdown.Periodic.r3Seed in Breakdown.Torus.InverseDefs, line 55. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L55).

**Periodic initial-data injection.** The periodic seed inserts the free evolution of the periodic initial correction into the first rescaled time piece. Source: Breakdown.Periodic.torusSeed in Breakdown.Torus.InverseDefs, line 59. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseDefs.lean#L59).

### Breakdown.Torus.KernelBound

Derives the three-quarter-power periodic bilinear kernel estimate from the trilinear bound and a weighted Fourier test sequence.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.KernelEstimate.

**Summability of decaying exponential.** With the stated hypotheses, decaying exponential satisfies the series-convergence assertion `Summable (fun n : ℤ => Real.exp (-(a * (n : ℝ) ^ 2)))`. Source: Breakdown.Periodic.Internal.KernelEstimate.summable_exp_neg_mul_int_sq in Breakdown.Torus.KernelBound, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L12).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k i = (k i : ℝ)`. Source: Breakdown.Periodic.Internal.KernelEstimate.freq_apply in Breakdown.Torus.KernelBound, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L30).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2`. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_freq_sq in Breakdown.Torus.KernelBound, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L33).

**Three integer frequency coordinates.** The lattice equivalence identifies a frequency with the ordered triple of its integer coordinates. Source: Breakdown.Periodic.Internal.KernelEstimate.latticeEquiv in Breakdown.Torus.KernelBound, line 37. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L37).

**Formula for lattice coordinates.** Lattice coordinates obeys the exact identity `latticeEquiv.symm p = ![p.1, p.2.1, p.2.2]`. Source: Breakdown.Periodic.Internal.KernelEstimate.latticeEquiv_symm_apply in Breakdown.Torus.KernelBound, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L45).

**Summability of decaying exponential.** With the stated hypotheses, decaying exponential satisfies the series-convergence assertion `Summable (fun k : Lattice => Real.exp (-(a * ‖freq k‖ ^ 2)))`. Source: Breakdown.Periodic.Internal.KernelEstimate.summable_exp_neg_mul_norm_freq_sq in Breakdown.Torus.KernelBound, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L48).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < weight k`. Source: Breakdown.Periodic.Internal.KernelEstimate.weight_pos in Breakdown.Torus.KernelBound, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L63).

**Nonnegativity of heat multiplier.** Heat multiplier is nonnegative, as stated in `0 ≤ heatFactor τ k`. Source: Breakdown.Periodic.Internal.KernelEstimate.heatFactor_nonneg in Breakdown.Torus.KernelBound, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L67).

**Bound for heat multiplier.** Heat multiplier satisfies the quantitative estimate `heatFactor τ k ≤ 1`. Source: Breakdown.Periodic.Internal.KernelEstimate.heatFactor_le_one in Breakdown.Torus.KernelBound, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L70).

**Summability of heat multiplier.** With the stated hypotheses, heat multiplier satisfies the series-convergence assertion `Summable (heatFactor τ)`. Source: Breakdown.Periodic.Internal.KernelEstimate.summable_heatFactor in Breakdown.Torus.KernelBound, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L73).

**Bound for heat evolution.** With the stated hypotheses, heat evolution satisfies the estimate `τ * (weight k * heatFactor τ k ^ 2) ≤ heatFactor τ k ∧ τ ^ 2 * (weight k ^ 2 * heatFactor τ k ^ 2) ≤ 1`. Source: Breakdown.Periodic.Internal.KernelEstimate.heat_ineq in Breakdown.Torus.KernelBound, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L80).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * heatFactor τ k ^ 2 ≤ heatFactor τ k / τ`. Source: Breakdown.Periodic.Internal.KernelEstimate.weight_heat_le_div in Breakdown.Torus.KernelBound, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L102).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * heatFactor τ k ^ 2 ≤ τ⁻¹`. Source: Breakdown.Periodic.Internal.KernelEstimate.weight_heat_le_inv in Breakdown.Torus.KernelBound, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L107).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k ^ 2 * heatFactor τ k ^ 2 ≤ (τ ^ 2)⁻¹`. Source: Breakdown.Periodic.Internal.KernelEstimate.weight_sq_heat_le_inv in Breakdown.Torus.KernelBound, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L113).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k c = inner ℂ (latVec k) c`. Source: Breakdown.Periodic.Internal.KernelEstimate.divPairing_eq_inner in Breakdown.Torus.KernelBound, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L118).

**Formula for inner product.** Inner product obeys the exact identity `inner ℂ (latVec k) (latVec k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ)`. Source: Breakdown.Periodic.Internal.KernelEstimate.inner_latVec_self in Breakdown.Torus.KernelBound, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L124).

**Nonzero frequencies have positive size.** A nonzero lattice frequency has nonzero squared Euclidean norm. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_freq_sq_ne_zero in Breakdown.Torus.KernelBound, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L130).

**Formula for inner product.** Inner product obeys the exact identity `inner ℂ (divFree k x) x = ((‖divFree k x‖ ^ 2 : ℝ) : ℂ)`. Source: Breakdown.Periodic.Internal.KernelEstimate.inner_divFree_self in Breakdown.Torus.KernelBound, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L138).

**Real scalars act through complex scalars.** Real scalar multiplication of a complex coefficient vector agrees with multiplication by that scalar viewed as a complex number. Source: Breakdown.Periodic.Internal.KernelEstimate.real_smul_coef in Breakdown.Torus.KernelBound, line 162. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L162).

**Formula for inner product.** Inner product obeys the exact identity `inner ℂ ((wt * s) • (s • divFree k (a + a))) a = (((1 / 2) * (wt * ‖s • divFree k (a + a)‖ ^ 2) : ℝ) : ℂ)`. Source: Breakdown.Periodic.Internal.KernelEstimate.inner_term in Breakdown.Torus.KernelBound, line 165. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L165).

**Weighted heat test sequence.** The test sequence multiplies each coefficient by `−weight(k) heatFactor(τ,k)/2`. Source: Breakdown.Periodic.Internal.KernelEstimate.testSeq in Breakdown.Torus.KernelBound, line 183. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L183).

**Norm identity for weighted test sequence.** Weighted test sequence has the norm identity `‖testSeq τ c k‖ = (1 / 2) * weight k * heatFactor τ k * ‖c k‖`. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_testSeq in Breakdown.Torus.KernelBound, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L186).

**Norm identity for weighted test sequence.** Weighted test sequence has the norm identity `‖testSeq τ c k‖ ^ 2 = (1 / 4) * (weight k * heatFactor τ k ^ 2) * (weight k * ‖c k‖ ^ 2)`. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_testSeq_sq in Breakdown.Torus.KernelBound, line 194. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L194).

**Summability of weighted test sequence.** With the stated hypotheses, weighted test sequence satisfies the series-convergence assertion `Summable (fun k => ‖testSeq τ c k‖)`. Source: Breakdown.Periodic.Internal.KernelEstimate.summable_norm_testSeq in Breakdown.Torus.KernelBound, line 199. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L199).

**Bound for weighted test sequence.** With the stated hypotheses, weighted test sequence satisfies the quantitative estimate `‖testSeq τ c k‖ ^ 2 ≤ τ⁻¹ * (weight k * ‖c k‖ ^ 2)`. Source: Breakdown.Periodic.Internal.KernelEstimate.testSeq_sq_le in Breakdown.Torus.KernelBound, line 210. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L210).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * ‖testSeq τ c k‖ ^ 2 ≤ (τ ^ 2)⁻¹ * (weight k * ‖c k‖ ^ 2)`. Source: Breakdown.Periodic.Internal.KernelEstimate.weight_testSeq_sq_le in Breakdown.Torus.KernelBound, line 218. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L218).

**Summability of Sobolev weight.** Sobolev weight satisfies the series-convergence assertion `Summable (fun k => weight k * ‖coeff w k‖ ^ 2)`. Source: Breakdown.Periodic.Internal.KernelEstimate.summable_weight_coeff in Breakdown.Torus.KernelBound, line 231. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L231).

**Formula for three-quarter time exponent.** With the stated hypotheses, three-quarter time exponent obeys the exact identity `(τ⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) * ((τ ^ 2)⁻¹ * N ^ 2) ^ (1 / 4 : ℝ) = τ ^ (-(3 / 4 : ℝ)) * N`. Source: Breakdown.Periodic.Internal.KernelEstimate.rpow_combine in Breakdown.Torus.KernelBound, line 240. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L240).

**Bound for scalar quadratic bound.** With the stated hypotheses, scalar quadratic bound satisfies the quantitative estimate `N ≤ 2 * K`. Source: Breakdown.Periodic.Internal.KernelEstimate.le_two_mul_of_half_sq_le in Breakdown.Torus.KernelBound, line 251. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L251).

**Bound for bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel satisfies the quantitative estimate `‖kernel τ u u‖ ≤ 2 * (C * τ ^ (-(3 / 4 : ℝ))) * ‖u‖ ^ 2`. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_kernel_diag_le in Breakdown.Torus.KernelBound, line 255. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L255).

**Bound for symmetric bilinear norm.** With the stated hypotheses, symmetric bilinear norm satisfies the quantitative estimate `‖K‖ ≤ 2 * D`. Source: Breakdown.Periodic.Internal.KernelEstimate.norm_le_of_diag in Breakdown.Torus.KernelBound, line 315. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/KernelBound.lean#L315).
<!-- /passage:front -->

