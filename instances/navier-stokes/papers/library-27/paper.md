
<!-- passage:front -->
# Library guide 27: Breakdown/Torus, Breakdown/Transfer

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) **27** [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Torus.Lattice` to `Breakdown.Transfer.VarConstIntegral` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.
<!-- /passage:front -->

## Breakdown/Torus

<!-- passage:sec-breakdown-torus -->

### Breakdown.Torus.Lattice

Constructs the real solenoidal weighted Fourier space, its heat evolution and the symmetrized nonlinear kernel.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Integer frequency lattice.** A lattice frequency is a triple of integers. Source: Breakdown.Periodic.Lattice in Breakdown.Torus.Lattice, line 9. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L9).

**Complex vector coefficient space.** A Fourier coefficient is a three-dimensional complex Euclidean vector. Source: Breakdown.Periodic.Coef in Breakdown.Torus.Lattice, line 11. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L11).

**Square-summable Fourier sequences.** The coefficient sequence space consists of square-summable complex vector sequences indexed by the integer lattice. Source: Breakdown.Periodic.Seq in Breakdown.Torus.Lattice, line 13. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L13).

**Real frequency vector.** The real frequency vector is the sum of the integer coordinates multiplied by their coordinate unit vectors. Source: Breakdown.Periodic.freq in Breakdown.Torus.Lattice, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L15).

**Complex frequency vector.** The complex frequency vector regards the three integer coordinates as complex numbers. Source: Breakdown.Periodic.latVec in Breakdown.Torus.Lattice, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L17).

**Periodic heat multiplier.** The periodic heat multiplier is `exp(−4π²|k|² max(t,0))`, so nonpositive time uses the identity multiplier. Source: Breakdown.Periodic.heatFactor in Breakdown.Torus.Lattice, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L21).

**Fourier divergence pairing.** The Fourier divergence pairing sums the products of the lattice coordinates and coefficient components. Source: Breakdown.Periodic.divPairing in Breakdown.Torus.Lattice, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L23).

**Lattice Leray projection.** The lattice projection subtracts the longitudinal component for a nonzero frequency and keeps the zero-frequency coefficient unchanged. Source: Breakdown.Periodic.divFree in Breakdown.Torus.Lattice, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L25).

**Addition formula for divergence pairing.** Divergence pairing obeys the addition identity `divPairing k (c + d) = divPairing k c + divPairing k d`. Source: Breakdown.Periodic.divPairing_add in Breakdown.Torus.Lattice, line 28. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L28).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k (c - d) = divPairing k c - divPairing k d`. Source: Breakdown.Periodic.divPairing_sub in Breakdown.Torus.Lattice, line 32. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L32).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k (z • c) = z * divPairing k c`. Source: Breakdown.Periodic.divPairing_csmul in Breakdown.Torus.Lattice, line 36. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L36).

**Scaling formula for divergence pairing.** Divergence pairing obeys the scalar-scaling identity `divPairing k (r • c) = (r : ℂ) * divPairing k c`. Source: Breakdown.Periodic.divPairing_smul in Breakdown.Torus.Lattice, line 41. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L41).

**Value at zero for divergence pairing.** Divergence pairing has the zero-parameter identity `divPairing k 0 = 0`. Source: Breakdown.Periodic.divPairing_zero in Breakdown.Torus.Lattice, line 45. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L45).

**Sign formula for divergence pairing.** Divergence pairing obeys the sign-change identity `divPairing (-k) c = -divPairing k c`. Source: Breakdown.Periodic.divPairing_neg in Breakdown.Torus.Lattice, line 48. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L48).

**Formula for divergence pairing.** With the stated hypotheses, divergence pairing obeys the exact identity `divPairing k c = starRingEnd ℂ (divPairing k d)`. Source: Breakdown.Periodic.divPairing_of_conj in Breakdown.Torus.Lattice, line 51. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L51).

**Membership in the solenoidal space.** Real solenoidal subspace has the equivalent characterizations `a ∈ fieldSpace ↔ (∀ k i, (a (-k)) i = starRingEnd ℂ ((a k) i)) ∧ ∀ k, divPairing k (a k) = 0`. Source: Breakdown.Periodic.mem_fieldSpace in Breakdown.Torus.Lattice, line 69. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L69).

**Continuity of evaluation.** Evaluation is continuous on the domain specified by `Continuous fun a : Seq => a k`. Source: Breakdown.Periodic.continuous_eval in Breakdown.Torus.Lattice, line 73. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L73).

**Continuity of divergence pairing.** Divergence pairing is continuous on the domain specified by `Continuous (divPairing k)`. Source: Breakdown.Periodic.continuous_divPairing in Breakdown.Torus.Lattice, line 76. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L76).

**Closedness of real solenoidal subspace.** Real solenoidal subspace is closed, as asserted by `IsClosed (fieldSpace : Set Seq)`. Source: Breakdown.Periodic.isClosed_fieldSpace in Breakdown.Torus.Lattice, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L80).

**Completeness of periodic Fourier space.** The real solenoidal periodic Fourier space is a complete normed space. Source: anonymous instance in Breakdown.Torus.Lattice, line 93. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L93).

**Remove the Sobolev weight.** The physical Fourier coefficient divides the stored sequence coefficient by the square root of its Sobolev weight. Source: Breakdown.Periodic.coeff in Breakdown.Torus.Lattice, line 95. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L95).

**Formula for square exponent.** Square exponent obeys the exact identity `(2 : ENNReal).toReal = 2`. Source: Breakdown.Periodic.two_toReal in Breakdown.Torus.Lattice, line 97. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L97).

**Bound for pointwise sequence bound.** With the stated hypotheses, pointwise sequence bound satisfies the quantitative estimate `‖f‖ ≤ C * ‖g‖`. Source: Breakdown.Periodic.norm_le_of_pointwise in Breakdown.Torus.Lattice, line 99. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L99).

**Summability of weighted sequence.** With the stated hypotheses, weighted sequence has the sequence-space membership asserted by `Memℓp (fun k => m k • a k) 2`. Source: Breakdown.Periodic.memℓp_mul in Breakdown.Torus.Lattice, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L112).

**Bounded Fourier multiplier.** A uniformly bounded scalar multiplier acts coordinatewise as a continuous linear map on square-summable sequences. Source: Breakdown.Periodic.mulSeq in Breakdown.Torus.Lattice, line 121. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L121).

**Formula for sequence multiplier.** With the stated hypotheses, sequence multiplier obeys the exact identity `mulSeq m hC hm a k = m k • a k`. Source: Breakdown.Periodic.mulSeq_apply in Breakdown.Torus.Lattice, line 135. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L135).

**Bound for heat multiplier.** Heat multiplier satisfies the quantitative estimate `|heatFactor t k| ≤ 1`. Source: Breakdown.Periodic.abs_heatFactor_le in Breakdown.Torus.Lattice, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L138).

**Sign formula for lattice frequency.** Lattice frequency obeys the sign-change identity `freq (-k) = -freq k`. Source: Breakdown.Periodic.freq_neg in Breakdown.Torus.Lattice, line 143. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L143).

**Sign formula for Sobolev weight.** Sobolev weight obeys the sign-change identity `weight (-k) = weight k`. Source: Breakdown.Periodic.weight_neg in Breakdown.Torus.Lattice, line 146. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L146).

**Sign formula for heat multiplier.** Heat multiplier obeys the sign-change identity `heatFactor t (-k) = heatFactor t k`. Source: Breakdown.Periodic.heatFactor_neg in Breakdown.Torus.Lattice, line 149. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L149).

**Heat preserves the Fourier field space.** Multiplying a periodic field’s weighted sequence by the heat factor preserves the real solenoidal subspace. Source: Breakdown.Periodic.heat_mem in Breakdown.Torus.Lattice, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L152).

**Fourier coefficient of advection.** The advection coefficient sums the frequency pairing of the first velocity with the derivative factor and the second velocity coefficient. Source: Breakdown.Periodic.advCoef in Breakdown.Torus.Lattice, line 164. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L164).

**Symmetrized bilinear heat sequence.** For positive elapsed time the kernel sequence applies the negative one-half heat and Leray factors to the two advection orders, and at nonpositive time it is zero. Source: Breakdown.Periodic.kernelSeq in Breakdown.Torus.Lattice, line 167. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L167).

**Source namespace:** Breakdown.Periodic.Internal.

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k i = k i`. Source: Breakdown.Periodic.Internal.freq_apply in Breakdown.Torus.Lattice, line 174. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L174).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.Internal.norm_freq_sq in Breakdown.Torus.Lattice, line 177. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L177).

**Formula for complex frequency vector.** Complex frequency vector obeys the exact identity `latVec k i = (k i : ℂ)`. Source: Breakdown.Periodic.Internal.latVec_apply in Breakdown.Torus.Lattice, line 181. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L181).

**Norm identity for frequency-vector norm.** Frequency-vector norm has the norm identity `‖latVec k‖ = ‖freq k‖`. Source: Breakdown.Periodic.Internal.norm_latVec in Breakdown.Torus.Lattice, line 183. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L183).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k c = inner ℂ (latVec k) c`. Source: Breakdown.Periodic.Internal.divPairing_eq_inner in Breakdown.Torus.Lattice, line 187. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L187).

**Bound for divergence pairing.** Divergence pairing satisfies the quantitative estimate `‖divPairing k c‖ ≤ ‖freq k‖ * ‖c‖`. Source: Breakdown.Periodic.Internal.norm_divPairing_le in Breakdown.Torus.Lattice, line 190. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L190).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < weight k`. Source: Breakdown.Periodic.Internal.weight_pos in Breakdown.Torus.Lattice, line 194. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L194).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `2 * π * ‖freq k‖ ≤ Real.sqrt (weight k)`. Source: Breakdown.Periodic.Internal.two_pi_le_sqrt in Breakdown.Torus.Lattice, line 198. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L198).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `‖coeff u k‖ = (Real.sqrt (weight k))⁻¹ * ‖(u : Seq) k‖`. Source: Breakdown.Periodic.Internal.norm_coeff in Breakdown.Torus.Lattice, line 204. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L204).

**Bound for Fourier coefficient.** Fourier coefficient satisfies the quantitative estimate `‖coeff u k‖ ≤ ‖(u : Seq) k‖`. Source: Breakdown.Periodic.Internal.norm_coeff_le in Breakdown.Torus.Lattice, line 208. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L208).

**One advection convolution term.** An advection summand multiplies the first coefficient’s divergence pairing by `2πi` and the second coefficient. Source: Breakdown.Periodic.Internal.advTerm in Breakdown.Torus.Lattice, line 217. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L217).

**Coefficients for advection coefficient.** The Fourier-coefficient calculation gives `advCoef u v k = ∑' j, advTerm u v k j`. Source: Breakdown.Periodic.Internal.advCoef_eq in Breakdown.Torus.Lattice, line 220. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L220).

**Bound for advection summand.** Advection summand satisfies the quantitative estimate `‖advTerm u v k j‖ ≤ ‖(u : Seq) (k - j)‖ * ‖(v : Seq) j‖`. Source: Breakdown.Periodic.Internal.norm_advTerm_le in Breakdown.Torus.Lattice, line 222. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L222).

**Summability of weighted Fourier sequence.** Weighted Fourier sequence satisfies the series-convergence assertion `Summable fun j => ‖a j‖ ^ (2 : ℝ)`. Source: Breakdown.Periodic.Internal.summable_sq in Breakdown.Torus.Lattice, line 240. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L240).

**Summability of integer shift.** Integer shift satisfies the series-convergence assertion `Summable fun j => ‖a (k - j)‖ ^ (2 : ℝ)`. Source: Breakdown.Periodic.Internal.summable_sq_shift in Breakdown.Torus.Lattice, line 244. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L244).

**Formula for weighted Fourier sequence.** Weighted Fourier sequence obeys the exact identity `∑' j, ‖a j‖ ^ (2 : ℝ) = ‖a‖ ^ (2 : ℝ)`. Source: Breakdown.Periodic.Internal.tsum_sq in Breakdown.Torus.Lattice, line 247. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L247).

**Summability of weighted Fourier sequence.** Weighted Fourier sequence satisfies the series-convergence assertion `Summable (fun j => ‖a (k - j)‖ * ‖b j‖) ∧ ∑' j, ‖a (k - j)‖ * ‖b j‖ ≤ ‖a‖ * ‖b‖`. Source: Breakdown.Periodic.Internal.lpProd in Breakdown.Torus.Lattice, line 252. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L252).

**Summability of advection summand.** Advection summand satisfies the series-convergence assertion `Summable fun j => ‖advTerm u v k j‖`. Source: Breakdown.Periodic.Internal.summable_norm_advTerm in Breakdown.Torus.Lattice, line 264. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L264).

**Summability of advection summand.** Advection summand satisfies the series-convergence assertion `Summable (advTerm u v k)`. Source: Breakdown.Periodic.Internal.summable_advTerm in Breakdown.Torus.Lattice, line 267. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L267).

**Bound for advection coefficient.** Advection coefficient satisfies the quantitative estimate `‖advCoef u v k‖ ≤ ‖u‖ * ‖v‖`. Source: Breakdown.Periodic.Internal.norm_advCoef_le in Breakdown.Torus.Lattice, line 270. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L270).

**Addition formula for Fourier coefficient.** Fourier coefficient obeys the addition identity `coeff (u + u') k = coeff u k + coeff u' k`. Source: Breakdown.Periodic.Internal.coeff_add in Breakdown.Torus.Lattice, line 278. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L278).

**Scaling formula for Fourier coefficient.** Fourier coefficient obeys the scalar-scaling identity `coeff (r • u) k = r • coeff u k`. Source: Breakdown.Periodic.Internal.coeff_smul in Breakdown.Torus.Lattice, line 281. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L281).

**Coefficients for advection coefficient.** The Fourier-coefficient calculation gives `advCoef (u + u') v k = advCoef u v k + advCoef u' v k`. Source: Breakdown.Periodic.Internal.advCoef_add_left in Breakdown.Torus.Lattice, line 284. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L284).

**Coefficients for advection coefficient.** The Fourier-coefficient calculation gives `advCoef u (v + v') k = advCoef u v k + advCoef u v' k`. Source: Breakdown.Periodic.Internal.advCoef_add_right in Breakdown.Torus.Lattice, line 291. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L291).

**Coefficients for advection coefficient.** The Fourier-coefficient calculation gives `advCoef (r • u) v k = r • advCoef u v k`. Source: Breakdown.Periodic.Internal.advCoef_smul_left in Breakdown.Torus.Lattice, line 298. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L298).

**Coefficients for advection coefficient.** The Fourier-coefficient calculation gives `advCoef u (r • v) k = r • advCoef u v k`. Source: Breakdown.Periodic.Internal.advCoef_smul_right in Breakdown.Torus.Lattice, line 308. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L308).

**Addition formula for Leray projection.** Leray projection obeys the addition identity `divFree k (c + d) = divFree k c + divFree k d`. Source: Breakdown.Periodic.Internal.divFree_add in Breakdown.Torus.Lattice, line 316. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L316).

**Scaling formula for Leray projection.** Leray projection obeys the scalar-scaling identity `divFree k (r • c) = r • divFree k c`. Source: Breakdown.Periodic.Internal.divFree_smul in Breakdown.Torus.Lattice, line 323. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L323).

**Formula for kernel coefficient.** Kernel coefficient obeys the exact identity `kernelSeq τ (u + u') v k = kernelSeq τ u v k + kernelSeq τ u' v k`. Source: Breakdown.Periodic.Internal.kernelSeq_add_left in Breakdown.Torus.Lattice, line 329. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L329).

**Formula for kernel coefficient.** Kernel coefficient obeys the exact identity `kernelSeq τ u (v + v') k = kernelSeq τ u v k + kernelSeq τ u v' k`. Source: Breakdown.Periodic.Internal.kernelSeq_add_right in Breakdown.Torus.Lattice, line 336. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L336).

**Formula for kernel coefficient.** Kernel coefficient obeys the exact identity `kernelSeq τ (r • u) v k = r • kernelSeq τ u v k`. Source: Breakdown.Periodic.Internal.kernelSeq_smul_left in Breakdown.Torus.Lattice, line 343. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L343).

**Formula for kernel coefficient.** Kernel coefficient obeys the exact identity `kernelSeq τ u (r • v) k = r • kernelSeq τ u v k`. Source: Breakdown.Periodic.Internal.kernelSeq_smul_right in Breakdown.Torus.Lattice, line 351. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L351).

**Sum formula for coordinate of a series.** With the stated hypotheses, coordinate of a series obeys the summation identity `(∑' j, f j) i = ∑' j, f j i`. Source: Breakdown.Periodic.Internal.apply_tsum in Breakdown.Torus.Lattice, line 359. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L359).

**Sign formula for Fourier coefficient.** Fourier coefficient obeys the sign-change identity `coeff u (-m) i = starRingEnd ℂ (coeff u m i)`. Source: Breakdown.Periodic.Internal.coeff_neg in Breakdown.Torus.Lattice, line 363. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L363).

**Sign formula for advection coefficient.** Advection coefficient obeys the sign-change identity `advCoef u v (-k) i = starRingEnd ℂ (advCoef u v k i)`. Source: Breakdown.Periodic.Internal.advCoef_neg in Breakdown.Torus.Lattice, line 369. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L369).

**Formula for Leray projection.** With the stated hypotheses, Leray projection obeys the exact identity `divFree (-k) c i = starRingEnd ℂ (divFree k d i)`. Source: Breakdown.Periodic.Internal.divFree_neg_conj in Breakdown.Torus.Lattice, line 382. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L382).

**Nonzero frequencies have positive size.** A nonzero lattice frequency has nonzero squared Euclidean norm. Source: Breakdown.Periodic.Internal.freq_ne_zero in Breakdown.Torus.Lattice, line 393. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L393).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k (latVec k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ)`. Source: Breakdown.Periodic.Internal.divPairing_latVec in Breakdown.Torus.Lattice, line 403. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L403).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k (divFree k c) = 0`. Source: Breakdown.Periodic.Internal.divPairing_divFree in Breakdown.Torus.Lattice, line 408. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L408).

**Bound for Leray projection.** Leray projection satisfies the quantitative estimate `‖divFree k c‖ ≤ 2 * ‖c‖`. Source: Breakdown.Periodic.Internal.norm_divFree_le in Breakdown.Torus.Lattice, line 416. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L416).

**Bound for kernel coefficient.** With the stated hypotheses, kernel coefficient satisfies the quantitative estimate `‖kernelSeq τ u v k‖ ^ 2 ≤ 4 * (‖u‖ * ‖v‖) ^ 2 * (weight k * heatFactor τ k ^ 2)`. Source: Breakdown.Periodic.Internal.norm_kernelSeq_sq in Breakdown.Torus.Lattice, line 434. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L434).

**Absorb a quadratic heat weight.** For τ > 0 and x ≥ 0, the displayed quadratic weight times the squared heat exponential is bounded by `(1+τ⁻¹)` times one heat exponential. Source: Breakdown.Periodic.Internal.real_bound in Breakdown.Torus.Lattice, line 459. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L459).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * heatFactor τ k ^ 2 ≤ (1 + 1 / τ) * heatFactor τ k`. Source: Breakdown.Periodic.Internal.weight_heat_le in Breakdown.Torus.Lattice, line 482. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L482).

**Summability of integer Gaussian weight.** With the stated hypotheses, integer Gaussian weight satisfies the series-convergence assertion `Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2))`. Source: Breakdown.Periodic.Internal.summable_expSq_int in Breakdown.Torus.Lattice, line 488. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L488).

**Summability of finite product series.** With the stated hypotheses, finite-dimensional product series satisfies the series-convergence assertion `∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i)`. Source: Breakdown.Periodic.Internal.summable_prod_fin in Breakdown.Torus.Lattice, line 501. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L501).

**Summability of heat evolution.** With the stated hypotheses, heat evolution satisfies the series-convergence assertion `Summable (heatFactor τ)`. Source: Breakdown.Periodic.Internal.summable_heat in Breakdown.Torus.Lattice, line 510. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L510).

**Summability of Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the series-convergence assertion `Summable fun k => weight k * heatFactor τ k ^ 2`. Source: Breakdown.Periodic.Internal.summable_weight_heat in Breakdown.Torus.Lattice, line 519. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L519).

**Summability of weighted Fourier sequence.** With the stated hypotheses, weighted Fourier sequence has the sequence-space membership asserted by `Memℓp c 2`. Source: Breakdown.Periodic.Internal.memℓp_of_sq_bound in Breakdown.Torus.Lattice, line 523. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L523).

**Bound for sequence norm.** With the stated hypotheses, sequence norm satisfies the quantitative estimate `‖c‖ ≤ Real.sqrt (M * ∑' k, g k)`. Source: Breakdown.Periodic.Internal.norm_le_of_sq_bound in Breakdown.Torus.Lattice, line 530. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L530).

**Source namespace:** Breakdown.Periodic.

**Summability of kernel coefficient.** Kernel coefficient has the sequence-space membership asserted by `Memℓp (kernelSeq τ u v) 2`. Source: Breakdown.Periodic.memℓp_kernelSeq in Breakdown.Torus.Lattice, line 543. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L543).

**The kernel lies in the field space.** The weighted bilinear-kernel sequence belongs to the real solenoidal sequence subspace for every elapsed time and both periodic inputs. Source: Breakdown.Periodic.kernelSeq_mem in Breakdown.Torus.Lattice, line 550. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L550).

**Bilinear heat value in Fourier space.** The kernel value packages the square-summable kernel sequence together with its reality and solenoidal conditions. Source: Breakdown.Periodic.kernelV in Breakdown.Torus.Lattice, line 568. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L568).

**A bilinear bound at each fixed time.** At every fixed elapsed time the periodic kernel value is bounded by a constant times the product of its two input norms. Source: Breakdown.Periodic.kernelV_crude in Breakdown.Torus.Lattice, line 570. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L570).

**Source namespace:** Breakdown.Periodic.Internal.

**Formula for bilinear heat value.** With the stated hypotheses, bilinear heat value obeys the exact identity `x = y`. Source: Breakdown.Periodic.Internal.kernelV_ext in Breakdown.Torus.Lattice, line 591. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L591).

**Formula for bilinear heat value.** Bilinear heat value obeys the exact identity `kernelV τ (u + u') v = kernelV τ u v + kernelV τ u' v`. Source: Breakdown.Periodic.Internal.kernelV_add_left in Breakdown.Torus.Lattice, line 594. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L594).

**Formula for bilinear heat value.** Bilinear heat value obeys the exact identity `kernelV τ (r • u) v = r • kernelV τ u v`. Source: Breakdown.Periodic.Internal.kernelV_smul_left in Breakdown.Torus.Lattice, line 597. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L597).

**Formula for bilinear heat value.** Bilinear heat value obeys the exact identity `kernelV τ u (v + v') = kernelV τ u v + kernelV τ u v'`. Source: Breakdown.Periodic.Internal.kernelV_add_right in Breakdown.Torus.Lattice, line 600. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L600).

**Formula for bilinear heat value.** Bilinear heat value obeys the exact identity `kernelV τ u (r • v) = r • kernelV τ u v`. Source: Breakdown.Periodic.Internal.kernelV_smul_right in Breakdown.Torus.Lattice, line 603. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Lattice.lean#L603).

### Breakdown.Torus.Main

Connects the chosen Fourier realization and the whole-space and periodic shell-interaction estimates to the main assembly.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**The concrete Fourier realization fits.** The chosen Fourier realization satisfies the contract identifying its heat, bilinear, dilation, rotation, embedding and test-space components. Source: Breakdown.Periodic.isFreqTrRealization in Breakdown.Torus.Main, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L48).

**Bound for whole-space interaction.** Under the stated assumptions, the whole-space shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and the shell-data norm. Source: Breakdown.Periodic.r3LambdaBound_holds in Breakdown.Torus.Main, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L57).

**Bound for periodic interaction.** Under the stated assumptions, at a valid shell scale with μτ ≤ 1 the periodic shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and shell-data norm. Source: Breakdown.Periodic.torusLambdaBound_holds in Breakdown.Torus.Main, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L61).

### Breakdown.Torus.Mild

Defines the periodic Duhamel formulation on half-open and closed time intervals.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Mild flow before the endpoint.** The mild-flow predicate requires continuity and the Duhamel identity on the half-open time interval `[a,b)`. Source: Breakdown.Periodic.IsMildOn in Breakdown.Torus.Mild, line 9. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Mild.lean#L9).

**Mild flow including the endpoint.** The closed-interval mild-flow predicate requires continuity and the Duhamel identity on `[a,b]`. Source: Breakdown.Periodic.IsMildOnIcc in Breakdown.Torus.Mild, line 14. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Mild.lean#L14).

### Breakdown.Torus.MovingFrame

Extracts the affine part of a possibly nonperiodic pressure and removes it through a time-dependent change of frame.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.MovingFrame.Internal.

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (f t)`. Source: Breakdown.Periodic.MovingFrame.Internal.slice_contDiff in Breakdown.Torus.MovingFrame, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L14).

**Smoothness of moving-frame pressure.** With the stated hypotheses, moving-frame pressure has the asserted differentiability order in `ContDiffOn ℝ ∞ (fun τ => f τ y) (Ici 0)`. Source: Breakdown.Periodic.MovingFrame.Internal.time_contDiffOn in Breakdown.Torus.MovingFrame, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L20).

**Derivative of space-time map.** With the stated hypotheses, space-time map has the Fréchet derivative specified by `HasFDerivAt (fun z : ℝ × Space => f z.1 z.2) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y)) (t, y)`. Source: Breakdown.Periodic.MovingFrame.Internal.joint_hasFDerivAt in Breakdown.Torus.MovingFrame, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L25).

**Time derivative of moving-frame pressure.** With the stated hypotheses, moving-frame pressure has the one-variable derivative specified by `HasDerivAt (fun τ => f τ y) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y) (1, 0)) t`. Source: Breakdown.Periodic.MovingFrame.Internal.time_hasDerivAt in Breakdown.Torus.MovingFrame, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L33).

**Derivative for moving-frame pressure.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (f t) y = (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)`. Source: Breakdown.Periodic.MovingFrame.Internal.space_fderiv in Breakdown.Torus.MovingFrame, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L40).

**Derivative along a moving path.** With the stated hypotheses, moving-frame trajectory has the one-variable derivative specified by `HasDerivAt (fun τ => f τ (x + h τ)) (deriv (fun τ => f τ (x + h t)) t + fderiv ℝ (f t) (x + h t) v) t`. Source: Breakdown.Periodic.MovingFrame.Internal.along_hasDerivAt in Breakdown.Torus.MovingFrame, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L47).

**Derivative formula for integer shift.** The derivative calculation gives `fderiv ℝ (fun z => f (z + a) + b) x = fderiv ℝ f (x + a)`. Source: Breakdown.Periodic.MovingFrame.Internal.fderiv_shift in Breakdown.Torus.MovingFrame, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L57).

**Derivative formula for higher derivative.** With the stated hypotheses, the derivative calculation gives `iteratedFDeriv ℝ 2 (fun z => f (z + a) + b) x = iteratedFDeriv ℝ 2 f (x + a)`. Source: Breakdown.Periodic.MovingFrame.Internal.iteratedFDeriv_shift in Breakdown.Torus.MovingFrame, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L61).

**Formula for coordinate unit vector.** With the stated hypotheses, coordinate unit vector obeys the exact identity `A = B`. Source: Breakdown.Periodic.MovingFrame.Internal.eq_of_apply_unitVector in Breakdown.Torus.MovingFrame, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L70).

**Formula for gradient.** Gradient obeys the exact identity `gradientAt q x j = fderiv ℝ q x (unitVector j)`. Source: Breakdown.Periodic.MovingFrame.Internal.gradientAt_apply in Breakdown.Torus.MovingFrame, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L76).

**Formula for pressure.** With the stated hypotheses, pressure obeys the exact identity `p t (x + unitVector i) - p t x = p t (unitVector i) - p t 0`. Source: Breakdown.Periodic.MovingFrame.Internal.pressure_shift_pos in Breakdown.Torus.MovingFrame, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L80).

**Formula for moving-frame pressure.** With the stated hypotheses, moving-frame pressure obeys the exact identity `ψ 0 = 0`. Source: Breakdown.Periodic.MovingFrame.Internal.eq_zero_of_pos in Breakdown.Torus.MovingFrame, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L111).

**Formula for pressure.** With the stated hypotheses, pressure obeys the exact identity `p t (x + unitVector i) = p t x + (p t (unitVector i) - p t 0)`. Source: Breakdown.Periodic.MovingFrame.Internal.pressure_shift in Breakdown.Torus.MovingFrame, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L117).

**A smooth primitive from time zero.** A smooth vector-valued curve on nonnegative time has a smooth primitive vanishing at zero whose derivative equals that curve at every positive time. Source: Breakdown.Periodic.MovingFrame.Internal.antideriv in Breakdown.Torus.MovingFrame, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L131).

**Affine part of the pressure.** The affine pressure vector records the pressure increment over one period in each coordinate direction. Source: Breakdown.Periodic.MovingFrame.Internal.linearPart in Breakdown.Torus.MovingFrame, line 144. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L144).

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ (linearPart p t) (unitVector i) = p t (unitVector i) - p t 0`. Source: Breakdown.Periodic.MovingFrame.Internal.inner_linearPart in Breakdown.Torus.MovingFrame, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L147).

**Formula for inner product.** Inner product obeys the exact identity `∑ i, inner ℝ (linearPart p t) (unitVector i) • unitVector i = linearPart p t`. Source: Breakdown.Periodic.MovingFrame.Internal.sum_inner_linearPart in Breakdown.Torus.MovingFrame, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L151).

**Formula for gradient.** With the stated hypotheses, gradient obeys the exact identity `gradientAt (fun z => q (z + a) - inner ℝ w (z + a)) x = gradientAt q (x + a) - ∑ i, inner ℝ w (unitVector i) • unitVector i`. Source: Breakdown.Periodic.MovingFrame.Internal.gradient_shift in Breakdown.Torus.MovingFrame, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L156).

**Formula for moving-frame pressure.** Moving-frame pressure obeys the exact identity `D + -Fg + c + (Fv + Fg) = L - (G - c)`. Source: Breakdown.Periodic.MovingFrame.Internal.combine in Breakdown.Torus.MovingFrame, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/MovingFrame.lean#L166).

### Breakdown.Torus.OpBounds

Controls the sequence operators and their change when the reference time-piece profile is perturbed.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.OpBounds.Internal.

**Bound for diagonal sequence operator.** With the stated hypotheses, diagonal sequence operator satisfies the quantitative estimate `‖A n‖ ≤ ‖T‖`. Source: Breakdown.Periodic.OpBounds.Internal.norm_le_of_seqOp_spec in Breakdown.Torus.OpBounds, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L18).

**Zero for an unbounded operator family.** When the diagonal family has no uniform operator-norm bound, the chosen sequence operator equals zero. Source: Breakdown.Periodic.OpBounds.Internal.seqOp_eq_zero in Breakdown.Torus.OpBounds, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L37).

**Stability of diagonal sequence maps.** A uniform bound C on the differences of two operator families gives the same bound on the difference of their chosen diagonal sequence operators. Source: Breakdown.Periodic.OpBounds.Internal.norm_seqOp_sub_le in Breakdown.Torus.OpBounds, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L43).

**Nonnegativity of kernel constant.** With the stated hypotheses, kernel constant is nonnegative, as stated in `0 ≤ H.CK`. Source: Breakdown.Periodic.OpBounds.Internal.ck_nonneg in Breakdown.Torus.OpBounds, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L77).

**Bound for free time piece.** With the stated hypotheses, free time piece satisfies the quantitative estimate `‖H.pieceFree T‖ ≤ 1`. Source: Breakdown.Periodic.OpBounds.Internal.norm_pieceFree_le in Breakdown.Torus.OpBounds, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L82).

**Bound for time-piece endpoint.** Time-piece endpoint satisfies the quantitative estimate `‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1`. Source: Breakdown.Periodic.OpBounds.Internal.norm_pieceEnd_le in Breakdown.Torus.OpBounds, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L92).

**Bound for bilinear interaction.** With the stated hypotheses, bilinear interaction satisfies the quantitative estimate `‖(2 : ℝ) • H.pieceBil L g - (2 : ℝ) • H.pieceBil L f‖ ≤ 8 * H.CK * L ^ (1 / 4 : ℝ) * M`. Source: Breakdown.Periodic.OpBounds.Internal.norm_bil_sub_le in Breakdown.Torus.OpBounds, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L100).

**Bound for bilinear time-piece integral.** With the stated hypotheses, bilinear time-piece integral satisfies the quantitative estimate `‖seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (g n)) - seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (f n))‖ ≤ 8 * CK * L ^ (1 / 4 : ℝ) * M`. Source: Breakdown.Periodic.OpBounds.Internal.norm_seqBil_sub_le in Breakdown.Torus.OpBounds, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L114).

**Bound for comparison operators.** Comparison operators satisfies the quantitative estimate `‖D.comp (ContinuousLinearMap.snd ℝ E Y)‖ ≤ ‖D‖`. Source: Breakdown.Periodic.OpBounds.Internal.norm_comp_snd_le in Breakdown.Torus.OpBounds, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L127).

**Formula for spatial correction operator.** Whole-space correction operator obeys the exact identity `r3Op F P k θ J f - r3Op F P k θ J g = (seqOp (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (g n)) - seqOp (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (f n))).comp (ContinuousLinearMap.snd ℝ _ _)`. Source: Breakdown.Periodic.OpBounds.Internal.r3Op_sub in Breakdown.Torus.OpBounds, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L135).

**Bound for propagation chain.** With the stated hypotheses, propagation chain satisfies the quantitative estimate `‖((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (f n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞))) - ((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (g n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)))‖ ≤ 8 * CK * L ^ (1 / 4 : ℝ) * M`. Source: Breakdown.Periodic.OpBounds.Internal.norm_chain_sub_le in Breakdown.Torus.OpBounds, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L145).

**Source namespace:** Breakdown.Periodic.

**Stability of correction operators.** Under the stated assumptions, the whole-space and periodic correction operators change by at most 8CKL^(1/4)M when their reference pieces differ uniformly by M. Source: Breakdown.Periodic.opDiffBounds in Breakdown.Torus.OpBounds, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L174).

**Source namespace:** Breakdown.Periodic.OpBounds.Internal.

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f σ = f (projIcc 0 L hL σ)`. Source: Breakdown.Periodic.OpBounds.Internal.extendPiece_eq in Breakdown.Torus.OpBounds, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L197).

**Finite sum of convolution kernels.** The combined kernel applies each of finitely many kernels to its corresponding input component and sums the outputs. Source: Breakdown.Periodic.OpBounds.Internal.combKernel in Breakdown.Torus.OpBounds, line 202. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L202).

**Formula for combined convolution kernel.** Combined convolution kernel obeys the exact identity `combKernel Λ τ y = ∑ l, Λ l τ (y l)`. Source: Breakdown.Periodic.OpBounds.Internal.combKernel_apply in Breakdown.Torus.OpBounds, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L205).

**Bound for combined convolution kernel.** Combined convolution kernel satisfies the quantitative estimate `‖combKernel Λ τ‖ ≤ ∑ l, ‖Λ l τ‖`. Source: Breakdown.Periodic.OpBounds.Internal.norm_combKernel_le in Breakdown.Torus.OpBounds, line 209. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L209).

**Formula for time convolution.** With the stated hypotheses, time convolution obeys the exact identity `(∑ l, pieceConv L (Λ l) (w l)) ζ s = ∫ σ in (0 : ℝ)..s, ∑ l, extendPiece (w l) σ • Λ l (s - σ) (extendPiece ζ σ)`. Source: Breakdown.Periodic.OpBounds.Internal.sum_pieceConv_apply in Breakdown.Torus.OpBounds, line 217. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L217).

**Bound for time convolution.** With the stated hypotheses, time convolution satisfies the quantitative estimate `‖∑ l, pieceConv L (Λ l) (w l)‖ ≤ 4 * B`. Source: Breakdown.Periodic.OpBounds.Internal.norm_sum_pieceConv_le in Breakdown.Torus.OpBounds, line 256. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L256).

**The zero field is a test field.** The zero field is smooth, compactly supported and divergence-free. Source: Breakdown.Periodic.OpBounds.Internal.isTestField_zero in Breakdown.Torus.OpBounds, line 306. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L306).

**Test fields are closed under addition.** The sum of two smooth compactly supported divergence-free fields is again a test field. Source: Breakdown.Periodic.OpBounds.Internal.isTestField_add in Breakdown.Torus.OpBounds, line 310. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L310).

**Test fields are closed under scaling.** Every real scalar multiple of a test field is a test field. Source: Breakdown.Periodic.OpBounds.Internal.isTestField_smul in Breakdown.Torus.OpBounds, line 322. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L322).

**A finite sum remains a test field.** Every finite real-weighted sum of test fields is a test field. Source: Breakdown.Periodic.OpBounds.Internal.isTestField_sum in Breakdown.Torus.OpBounds, line 333. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L333).

**Decay property of test field.** With the stated hypotheses, test field satisfies the defined decay-field conditions in `IsDecayField φ`. Source: Breakdown.Periodic.OpBounds.Internal.isDecayField_of_test in Breakdown.Torus.OpBounds, line 342. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L342).

**Sum formula for field embedding.** With the stated hypotheses, field embedding obeys the summation identity `Freq.embedX (∑ l ∈ s, c l • φ l) = ∑ l ∈ s, c l • Freq.embedX (φ l)`. Source: Breakdown.Periodic.OpBounds.Internal.embedX_sum in Breakdown.Torus.OpBounds, line 362. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L362).

**Cutoff shell-advection integrand.** The cutoff advection integrand combines profile times shell gradient with shell velocity times profile gradient inside the support ball. Source: Breakdown.Periodic.OpBounds.Internal.advInt in Breakdown.Torus.OpBounds, line 376. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L376).

**Formula for shell advection.** With the stated hypotheses, shell advection obeys the exact identity `advectShell φ hφ b ζ = Freq.toLpOrZero 2 (advInt φ b ζ)`. Source: Breakdown.Periodic.OpBounds.Internal.advectShell_eq in Breakdown.Torus.OpBounds, line 381. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L381).

**Lᵖ control of cutoff advection integrand.** With the stated hypotheses, cutoff advection integrand belongs to the Lebesgue space specified by `MemLp (advInt φ b ζ) 2 volume`. Source: Breakdown.Periodic.OpBounds.Internal.memLp_advInt in Breakdown.Torus.OpBounds, line 384. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L384).

**Addition for cutoff advection integrand.** With the stated hypotheses, cutoff advection integrand obeys the addition identity `advInt (f + g) b ζ = advInt f b ζ + advInt g b ζ`. Source: Breakdown.Periodic.OpBounds.Internal.advInt_add in Breakdown.Torus.OpBounds, line 405. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L405).

**Scaling for cutoff advection integrand.** With the stated hypotheses, cutoff advection integrand obeys the scalar-scaling identity `advInt (c • f) b ζ = c • advInt f b ζ`. Source: Breakdown.Periodic.OpBounds.Internal.advInt_smul in Breakdown.Torus.OpBounds, line 420. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L420).

**Addition formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the addition identity `Freq.toLpOrZero 2 (f + g) = Freq.toLpOrZero 2 f + Freq.toLpOrZero 2 g`. Source: Breakdown.Periodic.OpBounds.Internal.toLpOrZero_add in Breakdown.Torus.OpBounds, line 435. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L435).

**Scaling formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the scalar-scaling identity `Freq.toLpOrZero 2 (c • f) = c • Freq.toLpOrZero 2 f`. Source: Breakdown.Periodic.OpBounds.Internal.toLpOrZero_smul in Breakdown.Torus.OpBounds, line 441. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L441).

**Sum formula for shell advection.** With the stated hypotheses, shell advection obeys the summation identity `advectShell (∑ l ∈ s, c l • φ l) (isTestField_sum c φ h s) b ζ = ∑ l ∈ s, c l • advectShell (φ l) (h l) b ζ`. Source: Breakdown.Periodic.OpBounds.Internal.advectShell_sum in Breakdown.Torus.OpBounds, line 447. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L447).

**Sum formula of spatial shell interaction.** With the stated hypotheses, whole-space shell interaction obeys the summation identity `∑ l, c l • lambdaR3 (φ l) (h l) b τ ζ = lambdaR3 (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b τ ζ`. Source: Breakdown.Periodic.OpBounds.Internal.lambdaR3_sum in Breakdown.Torus.OpBounds, line 466. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L466).

**Finite sums of periodic interactions.** With the stated hypotheses, periodic shell interaction obeys the summation identity `∑ l, c l • lambdaTorus (φ l) (h l) b μ τ ζ = lambdaTorus (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b μ τ ζ`. Source: Breakdown.Periodic.OpBounds.Internal.lambdaTorus_sum in Breakdown.Torus.OpBounds, line 474. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L474).

**Bound for dilation.** With the stated hypotheses, dilation satisfies the quantitative estimate `‖F.D μ‖ ≤ μ ^ (1 / 4 : ℝ)`. Source: Breakdown.Periodic.OpBounds.Internal.norm_dil_le in Breakdown.Torus.OpBounds, line 492. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L492).

**Bound for whole-space sequence shift.** With the stated hypotheses, whole-space sequence shift satisfies the quantitative estimate `‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ`. Source: Breakdown.Periodic.OpBounds.Internal.norm_r3Shift_entry in Breakdown.Torus.OpBounds, line 496. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L496).

**Bound for periodic sequence shift.** With the stated hypotheses, periodic sequence shift satisfies the quantitative estimate `‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c`. Source: Breakdown.Periodic.OpBounds.Internal.norm_torusShift_entry in Breakdown.Torus.OpBounds, line 512. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L512).

**Admissibility of the shell scale.** With the stated hypotheses, the scale and support radius satisfy the shell-geometry constraints in `IsShellScale (stepScale T lam n) b`. Source: Breakdown.Periodic.OpBounds.Internal.isShellScale_step in Breakdown.Torus.OpBounds, line 521. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L521).

**Source namespace:** Breakdown.Periodic.

**Bounds for the comparison operators.** Under the stated assumptions, shell interactions and restrictions have the stated uniform operator bounds and the two sequence shifts have the geometric norm bound λ^(1/4)/θ. Source: Breakdown.Periodic.operatorNormBounds in Breakdown.Torus.OpBounds, line 532. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/OpBounds.lean#L532).

### Breakdown.Torus.Residual

Bounds the localized PDE residual on the fixed cutoff annulus, including derivatives of the potential and pressure correction.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Residual.Internal.

**Norm identity for coordinate unit vector.** Coordinate unit vector has the norm identity `‖unitVector i‖ = 1`. Source: Breakdown.Periodic.Residual.Internal.norm_unitVector in Breakdown.Torus.Residual, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L13).

**A four-term triangle inequality.** The norm of `a+b−c+d` is at most the sum of the four vector norms. Source: Breakdown.Periodic.Residual.Internal.norm_four_le in Breakdown.Torus.Residual, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L16).

**Bound for Laplacian.** Laplacian satisfies the quantitative estimate `‖sumSecondPartialsAt f x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 f x‖`. Source: Breakdown.Periodic.Residual.Internal.norm_sumSecondPartialsAt_le in Breakdown.Torus.Residual, line 22. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L22).

**Bound for gradient.** Gradient satisfies the quantitative estimate `‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖`. Source: Breakdown.Periodic.Residual.Internal.norm_gradientAt_le in Breakdown.Torus.Residual, line 35. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L35).

**Finite orders lie below infinity.** Every natural-number derivative order is bounded by the infinite differentiability order. Source: Breakdown.Periodic.Residual.Internal.nat_le_infty in Breakdown.Torus.Residual, line 48. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L48).

**Smoothness of profile.** With the stated hypotheses, profile has the asserted differentiability order in `ContDiff ℝ ∞ (W s)`. Source: Breakdown.Periodic.Residual.Internal.profile_slice in Breakdown.Torus.Residual, line 50. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L50).

**The profile bound is nonnegative.** The constant appearing in the similarity-profile conditions is nonnegative. Source: Breakdown.Periodic.Residual.Internal.profile_const_nonneg in Breakdown.Torus.Residual, line 54. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L54).

**Bound for self-similar velocity.** With the stated hypotheses, self-similar velocity satisfies the estimate `‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖ ≤ ((T - t) ^ (-(1 / 2 : ℝ))) ^ (j + 1) * (C / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist x center) ^ (j + 1))`. Source: Breakdown.Periodic.Residual.Internal.selfSimilar_iteratedFDeriv_sharp in Breakdown.Torus.Residual, line 60. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L60).

**Remove a scaled spatial weight.** The stated scaled decay bound implies `D ρⁿ ≤ C` when the scale is positive and the radius and bound constant are nonnegative. Source: Breakdown.Periodic.Residual.Internal.weighted_le in Breakdown.Torus.Residual, line 101. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L101).

**Bound for self-similar velocity.** With the stated hypotheses, self-similar velocity satisfies the quantitative estimate `‖iteratedFDeriv ℝ j (selfSimilar W T t) x‖ * dist x center ^ (j + 1) ≤ C`. Source: Breakdown.Periodic.Residual.Internal.selfSimilar_iteratedFDeriv_bound in Breakdown.Torus.Residual, line 110. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L110).

**Uniform bound for higher derivative.** With the stated hypotheses, higher derivative admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K`. Source: Breakdown.Periodic.Residual.Internal.bounded_iteratedFDeriv in Breakdown.Torus.Residual, line 118. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L118).

**Smoothness of central cutoff.** Central cutoff has the asserted differentiability order in `ContDiff ℝ ∞ centralCut`. Source: Breakdown.Periodic.Residual.Internal.centralCut_contDiff in Breakdown.Torus.Residual, line 125. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L125).

**The central cutoff has compact support.** The central smooth cutoff has compact support. Source: Breakdown.Periodic.Residual.Internal.centralCut_support in Breakdown.Torus.Residual, line 127. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L127).

**Smoothness of gradient.** With the stated hypotheses, gradient has the asserted differentiability order in `ContDiff ℝ ∞ (gradientAt χ)`. Source: Breakdown.Periodic.Residual.Internal.gradient_contDiff in Breakdown.Torus.Residual, line 129. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L129).

**A compact cutoff has compact gradient.** The gradient of the stated compactly supported smooth scalar function also has compact support. Source: Breakdown.Periodic.Residual.Internal.gradient_support in Breakdown.Torus.Residual, line 135. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L135).

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (f t)`. Source: Breakdown.Periodic.Residual.Internal.slice_of_contDiffOn in Breakdown.Torus.Residual, line 145. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L145).

**Bound for self-similar pressure.** With the stated hypotheses, self-similar pressure satisfies the estimate `‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ ((T - t) ^ (-(1 / 2 : ℝ))) ^ 3 * (C / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist x center) ^ 3)`. Source: Breakdown.Periodic.Residual.Internal.selfSimilarPressure_fderiv_sharp in Breakdown.Torus.Residual, line 152. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L152).

**Bound for self-similar pressure.** With the stated hypotheses, self-similar pressure satisfies the quantitative estimate `‖fderiv ℝ (selfSimilarPressure q T t) x‖ * dist x center ^ 3 ≤ C`. Source: Breakdown.Periodic.Residual.Internal.selfSimilarPressure_fderiv_bound in Breakdown.Torus.Residual, line 198. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L198).

**A segment stays away from the center.** If two displacements have norm at least 1/16 and nonnegative inner product, their translated connecting segment stays at distance at least 1/32 from the center. Source: Breakdown.Periodic.Residual.Internal.segment_far in Breakdown.Torus.Residual, line 205. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L205).

**Bound pressure along an outer segment.** Under the stated cubic spatial-gradient decay and endpoint geometry, the pressure difference is at most `32768 K ‖b−a‖`. Source: Breakdown.Periodic.Residual.Internal.segment_difference in Breakdown.Torus.Residual, line 226. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L226).

**Uniform bound for pressure.** With the stated hypotheses, pressure admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → |selfSimilarPressure q T t x - selfSimilarPressure q T t pressureAnchor| ≤ K`. Source: Breakdown.Periodic.Residual.Internal.pressure_difference_bound in Breakdown.Torus.Residual, line 240. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L240).

**Uniform bound for higher derivative.** With the stated hypotheses, higher derivative admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K`. Source: Breakdown.Periodic.Residual.Internal.bounded_low_derivs in Breakdown.Torus.Residual, line 291. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L291).

**Bound the low-order product expansion.** For derivative order at most two, the binomial product sum of two nonnegative sequences bounded by M is at most `4M²`. Source: Breakdown.Periodic.Residual.Internal.binom_sum_le in Breakdown.Torus.Residual, line 303. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L303).

**Bound for self-similar velocity.** With the stated hypotheses, self-similar velocity satisfies the quantitative estimate `‖iteratedFDeriv ℝ i (selfSimilar W T t) x‖ ≤ 4096 * C`. Source: Breakdown.Periodic.Residual.Internal.selfSimilar_shell_bound in Breakdown.Torus.Residual, line 322. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L322).

**Bound an integral over a unit interval.** A Banach-valued integrand bounded by M on [0,1] has interval-integral norm at most M. Source: Breakdown.Periodic.Residual.Internal.integral_value_le in Breakdown.Torus.Residual, line 333. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L333).

**Bound a differentiated radial integral.** A uniform bound M for the spatial derivatives of a smooth family on [0,1] bounds the derivative of its radial integral by M. Source: Breakdown.Periodic.Residual.Internal.integral_deriv_le in Breakdown.Torus.Residual, line 341. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L341).

**Low derivatives of a translation.** Through order two, the derivative norm of `y ↦ y−c` at x is at most `max ‖x−c‖ 1`. Source: Breakdown.Periodic.Residual.Internal.shift_norm_le in Breakdown.Torus.Residual, line 352. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L352).

**Bound for higher derivative.** With the stated hypotheses, higher derivative satisfies the quantitative estimate `‖iteratedFDeriv ℝ k (fun y => g (c + s • (y - c))) x‖ ≤ ‖iteratedFDeriv ℝ k g (c + s • (x - c))‖ * s ^ k`. Source: Breakdown.Periodic.Residual.Internal.dilate_norm_le in Breakdown.Torus.Residual, line 366. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L366).

**Uniform bound for vector potential.** With the stated hypotheses, vector potential admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (homotopyPotential center (selfSimilar W T t)) x‖ ≤ K`. Source: Breakdown.Periodic.Residual.Internal.potential_bound in Breakdown.Torus.Residual, line 389. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L389).

**Bound for central cutoff.** Central cutoff satisfies the quantitative estimate `‖centralCut x‖ ≤ 1`. Source: Breakdown.Periodic.Residual.Internal.centralCut_norm_le in Breakdown.Torus.Residual, line 507. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L507).

**Bound for self-similar pressure.** With the stated hypotheses, self-similar pressure satisfies the quantitative estimate `‖fderiv ℝ (selfSimilarPressure q T t) x‖ ≤ 4096 * C`. Source: Breakdown.Periodic.Residual.Internal.selfSimilarPressure_shell_bound in Breakdown.Torus.Residual, line 513. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L513).

**Bound for self-similar velocity.** With the stated hypotheses, self-similar velocity satisfies the quantitative estimate `‖deriv (fun τ => selfSimilar W T τ x) t‖ ≤ 4096 * C * (4096 * C) + 6 * (4096 * C)`. Source: Breakdown.Periodic.Residual.Internal.time_selfSimilar_bound in Breakdown.Torus.Residual, line 522. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L522).

**Bound for self-similar velocity.** With the stated hypotheses, self-similar velocity satisfies the estimate `‖deriv (fun τ => selfSimilar W T τ z) t‖ ≤ (C * C + 6 * C) * (((T - t) ^ (-(1 / 2 : ℝ))) ^ 3 / (1 + (T - t) ^ (-(1 / 2 : ℝ)) * dist z center) ^ 3)`. Source: Breakdown.Periodic.Residual.Internal.time_selfSimilar_sharp in Breakdown.Torus.Residual, line 554. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L554).

**Integrate the radial decay kernel.** For a > 0, the integral of `s/(1+as)³` over [0,1] is at most `a⁻²`. Source: Breakdown.Periodic.Residual.Internal.integral_kernel_bound in Breakdown.Torus.Residual, line 596. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L596).

**Time derivative of vector potential.** With the stated hypotheses, vector potential has the one-variable derivative specified by `HasDerivAt (fun τ => homotopyPotential center (selfSimilar W T τ) x) (∫ s in (0 : ℝ)..1, s • cross (deriv (fun τ => selfSimilar W T τ (center + s • (x - center))) t) (x - center)) t`. Source: Breakdown.Periodic.Residual.Internal.potential_time_deriv in Breakdown.Torus.Residual, line 628. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L628).

**Uniform bound for vector potential.** With the stated hypotheses, vector potential admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → DifferentiableAt ℝ (fun τ => homotopyPotential center (selfSimilar W T τ) x) t ∧ ‖deriv (fun τ => homotopyPotential center (selfSimilar W T τ) x) t‖ ≤ K * (T - t) ^ (-(1 / 2 : ℝ))`. Source: Breakdown.Periodic.Residual.Internal.potential_time_bound in Breakdown.Torus.Residual, line 723. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L723).

**Formula for PDE residual.** With the stated hypotheses, PDE residual obeys the exact identity `approxResidual W q T t x = 0`. Source: Breakdown.Periodic.Residual.Internal.residual_zero_outer in Breakdown.Torus.Residual, line 792. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L792).

**Formula for PDE residual.** With the stated hypotheses, PDE residual obeys the exact identity `approxResidual W q T t x = 0`. Source: Breakdown.Periodic.Residual.Internal.residual_zero_inner in Breakdown.Torus.Residual, line 813. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L813).

**Bound for PDE residual.** With the stated hypotheses, PDE residual satisfies the estimate `centralRadius / 4 ≤ dist x center ∧ dist x center ≤ centralRadius / 2`. Source: Breakdown.Periodic.Residual.Internal.residual_support in Breakdown.Torus.Residual, line 840. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L840).

**Bound the localized time derivative.** On the cutoff annulus the time derivative of the localized velocity is bounded by `K(T−t)⁻¹ᐟ²` uniformly for 0 < T ≤ 1 and 0 ≤ t < T, under the profile and self-similar-solution assumptions. Source: Breakdown.Periodic.Residual.Internal.time_term_bound in Breakdown.Torus.Residual, line 850. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L850).

**Uniform bound for higher derivative.** With the stated hypotheses, higher derivative admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ‖approxField W T t x‖ ≤ K ∧ ‖fderiv ℝ (approxField W T t) x‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 (approxField W T t) x‖ ≤ K`. Source: Breakdown.Periodic.Residual.Internal.field_bound in Breakdown.Torus.Residual, line 910. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L910).

**Uniform bound for pressure.** With the stated hypotheses, pressure admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ‖fderiv ℝ (approxPressure q T t) x‖ ≤ K`. Source: Breakdown.Periodic.Residual.Internal.pressure_bound in Breakdown.Torus.Residual, line 962. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L962).

**Uniform bound for cutoff annulus.** With the stated hypotheses, cutoff annulus admits the uniform bound stated in `∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space, centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 → ‖approxResidual W q T t x‖ ≤ K * (T - t) ^ (-(1 / 2 : ℝ))`. Source: Breakdown.Periodic.Residual.Internal.shell_bound in Breakdown.Torus.Residual, line 1008. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L1008).

**Source namespace:** Breakdown.Periodic.

**Support and size of the residual.** Under the stated assumptions, for 0 < T ≤ 1 the localized residual is supported in the annulus of radii 1/16 and 1/8 and is bounded by K(T−t)⁻¹ᐟ². Source: Breakdown.Periodic.approxResidualBound in Breakdown.Torus.Residual, line 1044. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Residual.lean#L1044).

### Breakdown.Torus.SelfSimilar

Checks the derivative and scaling identities that turn a similarity profile into a smooth physical-time solution before the terminal time.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SelfSimilar.Internal.

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (G s)`. Source: Breakdown.Periodic.SelfSimilar.Internal.slice_contDiff in Breakdown.Torus.SelfSimilar, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L12).

**Derivative of scaled field.** With the stated hypotheses, scaled field has the Fréchet derivative specified by `HasFDerivAt (fun z : Space => f (a • (z - c))) ((fderiv ℝ f (a • (x - c))).comp (a • ContinuousLinearMap.id ℝ Space)) x`. Source: Breakdown.Periodic.SelfSimilar.Internal.hasFDerivAt_scaled in Breakdown.Torus.SelfSimilar, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L16).

**Derivative of a rescaled velocity.** Differentiating `x ↦ r f(r(x−center))` multiplies the derivative of f at the rescaled point by r². Source: Breakdown.Periodic.SelfSimilar.Internal.fderiv_scaledField_apply in Breakdown.Torus.SelfSimilar, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L24).

**Derivative of a rescaled pressure.** Differentiating `x ↦ a f(r(x−center))` multiplies the derivative of f at the rescaled point by ar. Source: Breakdown.Periodic.SelfSimilar.Internal.fderiv_scaledPressure_apply in Breakdown.Torus.SelfSimilar, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L34).

**Derivative formula for higher derivative.** With the stated hypotheses, the derivative calculation gives `iteratedFDeriv ℝ 2 (fun z : Space => r • f (r • (z - center))) x (fun i => m i) = (r * r ^ 2) • iteratedFDeriv ℝ 2 f (r • (x - center)) m`. Source: Breakdown.Periodic.SelfSimilar.Internal.iteratedFDeriv_two_scaledField in Breakdown.Torus.SelfSimilar, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L45).

**Formula for divergence.** With the stated hypotheses, divergence obeys the exact identity `divergenceAt (fun z : Space => r • f (r • (z - center))) x = (r * r) * divergenceAt f (r • (x - center))`. Source: Breakdown.Periodic.SelfSimilar.Internal.divergence_scaledField in Breakdown.Torus.SelfSimilar, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L66).

**Formula for advection.** With the stated hypotheses, advection obeys the exact identity `advectionAt (fun z : Space => r • f (r • (z - center))) x = (r * r * r) • advectionAt f (r • (x - center))`. Source: Breakdown.Periodic.SelfSimilar.Internal.advection_scaledField in Breakdown.Torus.SelfSimilar, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L75).

**Formula for Laplacian.** With the stated hypotheses, Laplacian obeys the exact identity `sumSecondPartialsAt (fun z : Space => r • f (r • (z - center))) x = (r * r ^ 2) • sumSecondPartialsAt f (r • (x - center))`. Source: Breakdown.Periodic.SelfSimilar.Internal.sumSecondPartials_scaledField in Breakdown.Torus.SelfSimilar, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L82).

**Formula for gradient.** With the stated hypotheses, gradient obeys the exact identity `gradientAt (fun z : Space => a * f (r • (z - center))) x = (a * r) • gradientAt f (r • (x - center))`. Source: Breakdown.Periodic.SelfSimilar.Internal.gradient_scaledPressure in Breakdown.Torus.SelfSimilar, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L92).

**Smoothness gives differentiability.** With the stated hypotheses, self-similar scaling is differentiable as asserted in `Differentiable ℝ f`. Source: Breakdown.Periodic.SelfSimilar.Internal.differentiable_of_smooth in Breakdown.Torus.SelfSimilar, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L101).

**Formula for similarity scaling factor.** With the stated hypotheses, similarity scaling factor obeys the exact identity `(T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) = (T - t)⁻¹`. Source: Breakdown.Periodic.SelfSimilar.Internal.scaleFactor_mul_self in Breakdown.Torus.SelfSimilar, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L106).

**Time derivative of similarity time.** With the stated hypotheses, similarity time has the one-variable derivative specified by `HasDerivAt (fun τ => similarityTime T τ) (T - t)⁻¹ t`. Source: Breakdown.Periodic.SelfSimilar.Internal.hasDerivAt_similarityTime in Breakdown.Torus.SelfSimilar, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L110).

**Derivative of the similarity factor.** With the stated hypotheses, similarity scaling factor has the one-variable derivative specified by `HasDerivAt (fun τ : ℝ => (T - τ) ^ (-(1 / 2 : ℝ))) ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) t`. Source: Breakdown.Periodic.SelfSimilar.Internal.hasDerivAt_scaleFactor in Breakdown.Torus.SelfSimilar, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L121).

**Derivative formula for time derivative.** With the stated hypotheses, the derivative calculation gives `deriv (fun σ => W σ y) s = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (1, 0)`. Source: Breakdown.Periodic.SelfSimilar.Internal.deriv_time_slice in Breakdown.Torus.SelfSimilar, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L133).

**Derivative formula for spatial slice.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (W s) y v = fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (s, y) (0, v)`. Source: Breakdown.Periodic.SelfSimilar.Internal.fderiv_space_slice in Breakdown.Torus.SelfSimilar, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L140).

**Derivative for self-similar velocity.** With the stated hypotheses, the derivative calculation gives `deriv (fun τ => selfSimilar W T τ x) t = (T - t) ^ (-(1 / 2 : ℝ)) • ((T - t)⁻¹ • deriv (fun σ => W σ ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))) (similarityTime T t) + ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • fderiv ℝ (W (similarityTime T t)) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center)) (x - center)) + ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)))) • W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • (x - center))`. Source: Breakdown.Periodic.SelfSimilar.Internal.deriv_selfSimilar in Breakdown.Torus.SelfSimilar, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L150).

**Smoothness of similarity scaling factor.** With the stated hypotheses, similarity scaling factor has the asserted differentiability order in `ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1) ^ (-(1 / 2 : ℝ))) z`. Source: Breakdown.Periodic.SelfSimilar.Internal.contDiffAt_scaleFactor in Breakdown.Torus.SelfSimilar, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L179).

**Smoothness of similarity time.** With the stated hypotheses, similarity time has the asserted differentiability order in `ContDiffAt ℝ ∞ (fun z : ℝ × Space => similarityTime T z.1) z`. Source: Breakdown.Periodic.SelfSimilar.Internal.contDiffAt_similarityTime in Breakdown.Torus.SelfSimilar, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L183).

**Smooth similarity coordinates before T.** The map `(t,x) ↦ (T−t)⁻¹ᐟ²(x−center)` is smooth at every point with t < T. Source: Breakdown.Periodic.SelfSimilar.Internal.contDiffAt_scaledPoint in Breakdown.Torus.SelfSimilar, line 189. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L189).

**Smoothness of self-similar velocity.** With the stated hypotheses, self-similar velocity has the asserted differentiability order in `ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilar W T z.1 z.2) (Iio T ×ˢ univ)`. Source: Breakdown.Periodic.SelfSimilar.Internal.contDiffOn_selfSimilar in Breakdown.Torus.SelfSimilar, line 193. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L193).

**Smoothness of self-similar pressure.** With the stated hypotheses, self-similar pressure has the asserted differentiability order in `ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilarPressure q T z.1 z.2) (Iio T ×ˢ univ)`. Source: Breakdown.Periodic.SelfSimilar.Internal.contDiffOn_selfSimilarPressure in Breakdown.Torus.SelfSimilar, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L204).

**Source namespace:** Breakdown.Periodic.

**Equation for the self-similar flow.** Under the stated assumptions, the self-similar profile yields a smooth divergence-free velocity and pressure satisfying the viscosity-one equation before time T. Source: Breakdown.Periodic.selfSimilarSolves in Breakdown.Torus.SelfSimilar, line 220. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SelfSimilar.lean#L220).

### Breakdown.Torus.SeqDefs

Defines the sequence and time-convolution operators by their bounded realization contracts, together with the propositions that identify them.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Diagonal operator on bounded sequences.** The diagonal sequence operator chooses a bounded map acting by `A n` at index `n`, and returns zero when such a bounded realization does not exist. Source: Breakdown.Periodic.seqOp in Breakdown.Torus.SeqDefs, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L15).

**Shift on bounded sequences.** The sequence shift chooses a bounded map with zero first entry and `A(n−1)g(n−1)` thereafter, and otherwise returns zero. Source: Breakdown.Periodic.seqShift in Breakdown.Torus.SeqDefs, line 20. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L20).

**Initial-data sequence injection.** The seed operator chooses a bounded map placing the input image at index zero and zero elsewhere, and otherwise returns zero. Source: Breakdown.Periodic.seqSeed in Breakdown.Torus.SeqDefs, line 26. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L26).

**Composition on time pieces.** The composition operator chooses a bounded map applying the spatial operator at every time and otherwise returns zero. Source: Breakdown.Periodic.pieceComp in Breakdown.Torus.SeqDefs, line 31. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L31).

**Weighted time-convolution operator.** The convolution operator chooses a bounded realization of the weighted time integral and otherwise returns zero. Source: Breakdown.Periodic.pieceConv in Breakdown.Torus.SeqDefs, line 35. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L35).

**Sequence-operator contracts.** This proposition requires that uniformly bounded diagonal, shifted and initial-data sequence operators have the specified coordinates and operator-norm bounds. Source: Breakdown.Periodic.SeqOpSpec in Breakdown.Torus.SeqDefs, line 40. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L40).

**Time-piece composition contract.** This proposition requires that for nonnegative interval length a bounded linear map acts pointwise on time pieces with operator norm at most its own norm. Source: Breakdown.Periodic.PieceCompSpec in Breakdown.Torus.SeqDefs, line 49. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L49).

**Time-convolution contract.** This proposition requires that a strongly continuous positive-time operator kernel bounded by Cτ⁻³ᐟ⁴ defines the stated convolution with norm at most 4CL^(1/4)‖w‖ for 0 < L ≤ 1. Source: Breakdown.Periodic.PieceConvSpec in Breakdown.Torus.SeqDefs, line 54. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqDefs.lean#L54).

### Breakdown.Torus.SeqOps

Constructs the bounded sequence and convolution operators and proves their evaluation and norm specifications.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SeqOps.Internal.

**Bound for bounded sequence operators.** With the stated hypotheses, bounded sequence operators satisfies the quantitative estimate `‖A n (g n)‖ ≤ C * ‖g‖`. Source: Breakdown.Periodic.SeqOps.Internal.norm_apply_le in Breakdown.Torus.SeqOps, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L17).

**Coordinatewise sequence action.** A uniformly bounded operator family sends a bounded sequence to the coordinatewise images of its entries. Source: Breakdown.Periodic.SeqOps.Internal.opFun in Breakdown.Torus.SeqOps, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L23).

**Formula for diagonal sequence action.** With the stated hypotheses, diagonal sequence action obeys the exact identity `opFun A hA g n = A n (g n)`. Source: Breakdown.Periodic.SeqOps.Internal.opFun_apply in Breakdown.Torus.SeqOps, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L29).

**Bounded coordinatewise action.** The coordinatewise action of a uniformly bounded operator family is packaged as a continuous linear map. Source: Breakdown.Periodic.SeqOps.Internal.opCLM in Breakdown.Torus.SeqOps, line 32. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L32).

**Bound the shifted sequence entry.** A uniformly C-bounded operator family gives shifted sequence entries of norm at most C times the input supremum norm, including the zero initial entry. Source: Breakdown.Periodic.SeqOps.Internal.shift_le in Breakdown.Torus.SeqOps, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L43).

**Shifted operator action.** The shifted action has zero first entry and applies each operator to the preceding sequence value. Source: Breakdown.Periodic.SeqOps.Internal.shiftFun in Breakdown.Torus.SeqOps, line 51. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L51).

**Formula for shifted sequence action.** With the stated hypotheses, shifted sequence action obeys the exact identity `shiftFun B hB hC g n = if n = 0 then 0 else B (n - 1) (g (n - 1))`. Source: Breakdown.Periodic.SeqOps.Internal.shiftFun_apply in Breakdown.Torus.SeqOps, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L57).

**Bounded shifted action.** The uniformly bounded shifted action is packaged as a continuous linear map. Source: Breakdown.Periodic.SeqOps.Internal.shiftCLM in Breakdown.Torus.SeqOps, line 61. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L61).

**Bound for initial-data injection.** Initial-data injection satisfies the quantitative estimate `‖(if n = 0 then A₀ e else 0)‖ ≤ ‖A₀ e‖`. Source: Breakdown.Periodic.SeqOps.Internal.seed_le in Breakdown.Torus.SeqOps, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L74).

**Sequence supported at index zero.** The seed sequence places the image of the initial datum at index zero and vanishes at every later index. Source: Breakdown.Periodic.SeqOps.Internal.seedFun in Breakdown.Torus.SeqOps, line 81. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L81).

**Formula for initial-data sequence.** Initial-data sequence obeys the exact identity `seedFun A₀ e n = if n = 0 then A₀ e else 0`. Source: Breakdown.Periodic.SeqOps.Internal.seedFun_apply in Breakdown.Torus.SeqOps, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L86).

**Bounded seed injection.** Injection of the initial datum at index zero is packaged as a continuous linear map. Source: Breakdown.Periodic.SeqOps.Internal.seedCLM in Breakdown.Torus.SeqOps, line 89. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L89).

**Addition for time-piece extension.** Time-piece extension obeys the addition identity `extendPiece (f + g) s = extendPiece f s + extendPiece g s`. Source: Breakdown.Periodic.SeqOps.Internal.extend_add in Breakdown.Torus.SeqOps, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L108).

**Scaling formula for time-piece extension.** Time-piece extension obeys the scalar-scaling identity `extendPiece (c • f) s = c • extendPiece f s`. Source: Breakdown.Periodic.SeqOps.Internal.extend_smul in Breakdown.Torus.SeqOps, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L115).

**Continuity of time-piece extension.** Time-piece extension is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.Periodic.SeqOps.Internal.extend_continuous in Breakdown.Torus.SeqOps, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L122).

**Bound for time-piece extension.** Time-piece extension satisfies the quantitative estimate `‖extendPiece f s‖ ≤ ‖f‖`. Source: Breakdown.Periodic.SeqOps.Internal.norm_extend_le in Breakdown.Torus.SeqOps, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L128).

**Limit of bounded sequence operators.** With the stated hypotheses, bounded sequence operators has the limit `Tendsto (fun x => Λ (τ x) (z x)) l (𝓝 (Λ τ₀ z₀))`. Source: Breakdown.Periodic.SeqOps.Internal.tendsto_apply in Breakdown.Torus.SeqOps, line 134. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L134).

**Weighted convolution integrand.** The convolution integrand evaluates the weight and input at `s−r`, then applies the operator kernel at elapsed time `r`. Source: Breakdown.Periodic.SeqOps.Internal.convKernel in Breakdown.Torus.SeqOps, line 151. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L151).

**Continuity of convolution integrand.** With the stated hypotheses, convolution integrand is continuous on the domain specified by `ContinuousOn (convKernel Λ w ζ s) (Ioc 0 1)`. Source: Breakdown.Periodic.SeqOps.Internal.convKernel_continuousOn in Breakdown.Torus.SeqOps, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L157).

**Continuity of convolution integrand.** Convolution integrand is continuous on the domain specified by `Continuous (fun s => convKernel Λ w ζ s r)`. Source: Breakdown.Periodic.SeqOps.Internal.convKernel_continuous_left in Breakdown.Torus.SeqOps, line 176. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L176).

**Bound for convolution integrand.** With the stated hypotheses, convolution integrand satisfies the quantitative estimate `‖convKernel Λ w ζ s r‖ ≤ ‖w‖ * C * ‖ζ‖ * r ^ (-(3 / 4 : ℝ))`. Source: Breakdown.Periodic.SeqOps.Internal.norm_convKernel_le in Breakdown.Torus.SeqOps, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L184).

**Integrability of the singular power.** For c ≥ 0, the scalar majorant `K r⁻³ᐟ⁴` is integrable on (0,c]. Source: Breakdown.Periodic.SeqOps.Internal.bound_integrableOn in Breakdown.Torus.SeqOps, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L197).

**Integrability of convolution integrand.** With the stated hypotheses, convolution integrand is integrable over the time interval in `IntervalIntegrable (convKernel Λ w ζ s) volume 0 c`. Source: Breakdown.Periodic.SeqOps.Internal.convKernel_integrable in Breakdown.Torus.SeqOps, line 202. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L202).

**Integrate the singular time power.** The interval integral of `r⁻³ᐟ⁴` from zero to c equals `4 c^(1/4)` with the source’s real-power convention. Source: Breakdown.Periodic.SeqOps.Internal.integral_rpow_three_quarters in Breakdown.Torus.SeqOps, line 213. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L213).

**Weighted time integral.** The convolution value integrates the weighted kernel from elapsed time zero to the current time. Source: Breakdown.Periodic.SeqOps.Internal.convFun in Breakdown.Torus.SeqOps, line 220. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L220).

**Formula for time convolution.** Time convolution obeys the exact identity `∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ) = convFun Λ w ζ s`. Source: Breakdown.Periodic.SeqOps.Internal.convFun_eq in Breakdown.Torus.SeqOps, line 222. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L222).

**Bound for time convolution.** With the stated hypotheses, time convolution satisfies the quantitative estimate `‖convFun Λ w ζ s‖ ≤ 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖ * ‖ζ‖`. Source: Breakdown.Periodic.SeqOps.Internal.norm_convFun_le in Breakdown.Torus.SeqOps, line 231. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L231).

**Continuity of time convolution.** With the stated hypotheses, time convolution is continuous on the domain specified by `ContinuousOn (convFun Λ w ζ) (Icc 0 L)`. Source: Breakdown.Periodic.SeqOps.Internal.convFun_continuousOn in Breakdown.Torus.SeqOps, line 246. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L246).

**Addition formula for time convolution.** With the stated hypotheses, time convolution obeys the addition identity `convFun Λ w (ζ + ζ') s = convFun Λ w ζ s + convFun Λ w ζ' s`. Source: Breakdown.Periodic.SeqOps.Internal.convFun_add in Breakdown.Torus.SeqOps, line 285. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L285).

**Scaling formula for time convolution.** Time convolution obeys the scalar-scaling identity `convFun Λ w (c • ζ) s = c • convFun Λ w ζ s`. Source: Breakdown.Periodic.SeqOps.Internal.convFun_smul in Breakdown.Torus.SeqOps, line 297. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L297).

**Continuous convolution time piece.** The weighted convolution and its continuity proof are packaged as a continuous time piece. Source: Breakdown.Periodic.SeqOps.Internal.convPiece in Breakdown.Torus.SeqOps, line 306. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L306).

**Bounded time-convolution map.** The convolution is packaged as a continuous linear map with norm bound `4 C L^(1/4) ‖w‖`. Source: Breakdown.Periodic.SeqOps.Internal.convCLM in Breakdown.Torus.SeqOps, line 311. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L311).

**Source namespace:** Breakdown.Periodic.

**Sequence-operator contracts.** Under the stated assumptions, uniformly bounded diagonal, shifted and initial-data sequence operators have the specified coordinates and operator-norm bounds. Source: Breakdown.Periodic.seqOpSpec in Breakdown.Torus.SeqOps, line 335. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L335).

**Time-piece composition contract.** Under the stated assumptions, for nonnegative interval length a bounded linear map acts pointwise on time pieces with operator norm at most its own norm. Source: Breakdown.Periodic.pieceCompSpec in Breakdown.Torus.SeqOps, line 373. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L373).

**Time-convolution contract.** Under the stated assumptions, a strongly continuous positive-time operator kernel bounded by Cτ⁻³ᐟ⁴ defines the stated convolution with norm at most 4CL^(1/4)‖w‖ for 0 < L ≤ 1. Source: Breakdown.Periodic.pieceConvSpec in Breakdown.Torus.SeqOps, line 387. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqOps.lean#L387).

### Breakdown.Torus.SeqPerturbation

Rewrites the correction equation as a contraction on bounded time-piece sequences and obtains a controlled fixed point.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SeqPerturbation.Internal.

**Formula for time-piece extension.** With the stated hypotheses, time-piece extension obeys the exact identity `extendPiece f t = f ⟨t, ht⟩`. Source: Breakdown.Periodic.SeqPerturbation.Internal.extend_eq in Breakdown.Torus.SeqPerturbation, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L15).

**Continuity of time-piece extension.** With the stated hypotheses, time-piece extension is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.Periodic.SeqPerturbation.Internal.extend_continuous in Breakdown.Torus.SeqPerturbation, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L20).

**Scaling formula for time-piece extension.** With the stated hypotheses, time-piece extension obeys the scalar-scaling identity `extendPiece (f + a • g) s = extendPiece f s + a • extendPiece g s`. Source: Breakdown.Periodic.SeqPerturbation.Internal.extend_add_smul in Breakdown.Torus.SeqPerturbation, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L28).

**A piece equation gives a mild solution.** A continuous time piece satisfying the free-plus-quadratic equation extends to a mild solution on [0,T] with the prescribed initial value, assuming the two piece-integral interfaces. Source: Breakdown.Periodic.SeqPerturbation.Internal.mild_of_eq in Breakdown.Torus.SeqPerturbation, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L34).

**Formula for bilinear interaction.** With the stated hypotheses, bilinear interaction obeys the exact identity `H.pieceBil T f g = H.pieceBil T g f`. Source: Breakdown.Periodic.SeqPerturbation.Internal.bil_symm in Breakdown.Torus.SeqPerturbation, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L58).

**Formula for time piece.** With the stated hypotheses, time piece obeys the exact identity `b + t • w = F (b0 + y) + B (b + t • w) (b + t • w)`. Source: Breakdown.Periodic.SeqPerturbation.Internal.piece_identity in Breakdown.Torus.SeqPerturbation, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L65).

**Nonlinear sequence correction.** The correction combines the weighted quadratic term, the inversely weighted residual and the initial-data contribution at index zero. Source: Breakdown.Periodic.SeqPerturbation.Internal.seqNonlin in Breakdown.Torus.SeqPerturbation, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L87).

**Formula of nonlinear sequence correction.** With the stated hypotheses, nonlinear sequence correction obeys the exact identity `seqNonlin H L θ res ξ z n - seqNonlin H L θ res ξ z' n = θ ^ n • (H n).pieceBil L (z n) (z n) - θ ^ n • (H n).pieceBil L (z' n) (z' n)`. Source: Breakdown.Periodic.SeqPerturbation.Internal.seqNonlin_sub in Breakdown.Torus.SeqPerturbation, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L92).

**Bound for nonlinear sequence correction.** With the stated hypotheses, nonlinear sequence correction satisfies the quantitative estimate `x ≤ 2 * A`. Source: Breakdown.Periodic.SeqPerturbation.Internal.quad_le in Breakdown.Torus.SeqPerturbation, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L99).

**A small quadratic fixed point.** The stated quadratic smallness condition `8 q A ≤ 1` yields a fixed point with norm at most `2 A`. Source: Breakdown.Periodic.SeqPerturbation.Internal.exists_fixed in Breakdown.Torus.SeqPerturbation, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SeqPerturbation.lean#L104).

### Breakdown.Torus.ShellDefs

Defines the common shell data, cutoff restrictions, periodic transplantation and the two shell-interaction operators.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Periodize around the cell center.** Wrapping subtracts the rounded integer displacement from the cell center in every coordinate. Source: Breakdown.Periodic.wrap in Breakdown.Torus.ShellDefs, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L16).

**Periodic similarity coordinates.** The periodic similarity coordinate subtracts the cell center after wrapping and divides by `√μ`. Source: Breakdown.Periodic.simCoord in Breakdown.Torus.ShellDefs, line 18. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L18).

**Admissible shell scale.** A shell scale requires `0 < μ ≤ 1`, `0 < b` and `√μ b ≤ 1/8`. Source: Breakdown.Periodic.IsShellScale in Breakdown.Torus.ShellDefs, line 23. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L23).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the exact identity `Freq.toLpOrZero p f = h.toLp f`. Source: Breakdown.Periodic.ShellDefs.Internal.toLpOrZero_eq in Breakdown.Torus.ShellDefs, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L27).

**Addition formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the addition identity `Freq.toLpOrZero p k = Freq.toLpOrZero p f + Freq.toLpOrZero p g`. Source: Breakdown.Periodic.ShellDefs.Internal.toLpOrZero_add in Breakdown.Torus.ShellDefs, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L32).

**Scaling formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the scalar-scaling identity `Freq.toLpOrZero p k = r • Freq.toLpOrZero p f`. Source: Breakdown.Periodic.ShellDefs.Internal.toLpOrZero_smul in Breakdown.Torus.ShellDefs, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L39).

**Bound for Lᵖ representative.** With the stated hypotheses, Lᵖ representative satisfies the quantitative estimate `‖Freq.toLpOrZero p f‖ ≤ B.toReal`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_toLpOrZero_le in Breakdown.Torus.ShellDefs, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L46).

**Ball restriction preserves Lᵖ membership.** Multiplying an Lᵖ function by the indicator of a closed ball preserves Lᵖ membership. Source: Breakdown.Periodic.ShellDefs.Internal.memLp_cut in Breakdown.Torus.ShellDefs, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L55).

**Addition formula for ball restriction.** Ball restriction obeys the addition identity `Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (⇑(f + g) : Space → Space)) = Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f) + Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator g)`. Source: Breakdown.Periodic.ShellDefs.Internal.cut_add in Breakdown.Torus.ShellDefs, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L59).

**Scaling formula for ball restriction.** Ball restriction obeys the scalar-scaling identity `Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (⇑(r • f) : Space → Space)) = r • Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f)`. Source: Breakdown.Periodic.ShellDefs.Internal.cut_smul in Breakdown.Torus.ShellDefs, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L71).

**Bound for ball restriction.** Ball restriction satisfies the quantitative estimate `‖Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f)‖ ≤ 1 * ‖f‖`. Source: Breakdown.Periodic.ShellDefs.Internal.cut_norm_le in Breakdown.Torus.ShellDefs, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L82).

**Source namespace:** Breakdown.Periodic.

**Restriction to a closed ball.** The ball restriction multiplies an Lᵖ representative by the indicator of the closed ball and packages the result as a continuous linear map. Source: Breakdown.Periodic.cutLp in Breakdown.Torus.ShellDefs, line 90. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L90).

**Representative of ball restriction.** Ball restriction has the almost-everywhere representation `(cutLp p b f : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator f`. Source: Breakdown.Periodic.cutLp_apply in Breakdown.Torus.ShellDefs, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L97).

**Whole-space data on the shell.** Whole-space restriction records the three L² derivatives and the L⁶ velocity after cutting them off to the support ball. Source: Breakdown.Periodic.restrictR3 in Breakdown.Torus.ShellDefs, line 103. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L103).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Shell-to-cell coordinate map.** The shell coordinate map sends `y` to `center + √μ y`. Source: Breakdown.Periodic.ShellDefs.Internal.shellMap in Breakdown.Torus.ShellDefs, line 109. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L109).

**Measurability of unit cell.** Unit cell has the measurability property `MeasurableSet cell`. Source: Breakdown.Periodic.ShellDefs.Internal.measurableSet_cell in Breakdown.Torus.ShellDefs, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L111).

**Continuity of shell coordinate map.** Shell coordinate map is continuous on the domain specified by `Continuous (shellMap μ)`. Source: Breakdown.Periodic.ShellDefs.Internal.continuous_shellMap in Breakdown.Torus.ShellDefs, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L114).

**Shell coordinates preserve null sets.** At positive μ the shell coordinate map is quasi measure preserving for Lebesgue measure. Source: Breakdown.Periodic.ShellDefs.Internal.qmp_shellMap in Breakdown.Torus.ShellDefs, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L117).

**Formula for cell center.** Cell center obeys the exact identity `center i = 1 / 2`. Source: Breakdown.Periodic.ShellDefs.Internal.center_apply in Breakdown.Torus.ShellDefs, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L122).

**The shell map stays inside the cell.** At a valid shell scale, the shell coordinate map sends the radius-b ball into the unit cell. Source: Breakdown.Periodic.ShellDefs.Internal.shellMap_mem in Breakdown.Torus.ShellDefs, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L125).

**Pull back almost-everywhere cell facts.** At a valid shell scale, a property holding almost everywhere in the cell also holds almost everywhere on the radius-b ball after the shell coordinate map. Source: Breakdown.Periodic.ShellDefs.Internal.ae_shellMap in Breakdown.Torus.ShellDefs, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L142).

**Formula for scaling.** With the stated hypotheses, scaling obeys the exact identity `|(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| = μ ^ (-(3 / 2 : ℝ))`. Source: Breakdown.Periodic.ShellDefs.Internal.scale_eq in Breakdown.Torus.ShellDefs, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L149).

**Bound for shell coordinate map.** With the stated hypotheses, shell coordinate map satisfies the quantitative estimate `Measure.map (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b)) ≤ ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) • volume.restrict cell`. Source: Breakdown.Periodic.ShellDefs.Internal.map_shellMap_le in Breakdown.Torus.ShellDefs, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L155).

**Bound for real part.** Real part satisfies the quantitative estimate `‖Freq.realVec v‖ ≤ ‖v‖`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_realVec_le in Breakdown.Torus.ShellDefs, line 171. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L171).

**Lᵖ scaling from the cell to the shell.** At a valid shell scale the real-part pullback is measurable and its Lᵖ norm gains at most the factor `|k| μ^(−3/(2p))` relative to the cell norm, for finite p in the source convention. Source: Breakdown.Periodic.ShellDefs.Internal.eLpNorm_shell_le in Breakdown.Torus.ShellDefs, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L179).

**Formula for scaling.** With the stated hypotheses, scaling obeys the exact identity `‖μ ^ a‖ₑ * ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) ^ q = 1`. Source: Breakdown.Periodic.ShellDefs.Internal.scale_cancel in Breakdown.Torus.ShellDefs, line 209. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L209).

**Normalized shell restriction contracts.** At a valid shell scale the ball-restricted real pullback, normalized by `μ^(3/(2p))`, belongs to Lᵖ and has norm at most the original cell Lᵖ norm. Source: Breakdown.Periodic.ShellDefs.Internal.norm_shell_le in Breakdown.Torus.ShellDefs, line 216. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L216).

**Addition formula for cutoff annulus.** With the stated hypotheses, cutoff annulus obeys the addition identity `Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (fun y => μ ^ a • Freq.realVec ((g + g' : Lp Coef p (volume.restrict cell)) (center + Real.sqrt μ • y)))) = Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y)))) + Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (fun y => μ ^ a • Freq.realVec (g' (center + Real.sqrt μ • y))))`. Source: Breakdown.Periodic.ShellDefs.Internal.shell_add in Breakdown.Torus.ShellDefs, line 233. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L233).

**Scaling formula for cutoff annulus.** With the stated hypotheses, cutoff annulus obeys the scalar-scaling identity `Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (fun y => μ ^ a • Freq.realVec ((r • g : Lp Coef p (volume.restrict cell)) (center + Real.sqrt μ • y)))) = r • Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y))))`. Source: Breakdown.Periodic.ShellDefs.Internal.shell_smul in Breakdown.Torus.ShellDefs, line 251. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L251).

**Formula for shell restriction.** Shell restriction obeys the exact identity `(3 / 4 : ℝ) = 3 / 2 * (1 / (2 : ℝ≥0∞)).toReal`. Source: Breakdown.Periodic.ShellDefs.Internal.exp_two in Breakdown.Torus.ShellDefs, line 267. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L267).

**Formula for shell restriction.** Shell restriction obeys the exact identity `(1 / 4 : ℝ) = 3 / 2 * (1 / (6 : ℝ≥0∞)).toReal`. Source: Breakdown.Periodic.ShellDefs.Internal.exp_six in Breakdown.Torus.ShellDefs, line 271. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L271).

**Summability of Sobolev weight.** Sobolev weight satisfies the series-convergence assertion `Summable fun k => weight k * ‖coeff z k‖ ^ 2`. Source: Breakdown.Periodic.ShellDefs.Internal.summable_weight_coeff in Breakdown.Torus.ShellDefs, line 275. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L275).

**Bound for gradient coefficient.** Gradient coefficient satisfies the quantitative estimate `‖gradCoef j z k‖ ^ 2 ≤ weight k * ‖coeff z k‖ ^ 2`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_gradCoef_sq_le in Breakdown.Torus.ShellDefs, line 283. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L283).

**Bound for gradient.** Gradient satisfies the quantitative estimate `‖torusSeries 2 (gradCoef j z)‖ ≤ ‖z‖`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_grad_le in Breakdown.Torus.ShellDefs, line 301. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L301).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `coeff (z + w) = coeff z + coeff w`. Source: Breakdown.Periodic.ShellDefs.Internal.coeff_add' in Breakdown.Torus.ShellDefs, line 308. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L308).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `coeff (r • z) = r • coeff z`. Source: Breakdown.Periodic.ShellDefs.Internal.coeff_smul' in Breakdown.Torus.ShellDefs, line 312. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L312).

**Coefficients for gradient coefficient.** The Fourier-coefficient calculation gives `gradCoef j (z + w) = gradCoef j z + gradCoef j w`. Source: Breakdown.Periodic.ShellDefs.Internal.gradCoef_add' in Breakdown.Torus.ShellDefs, line 317. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L317).

**Coefficients for gradient coefficient.** The Fourier-coefficient calculation gives `gradCoef j (r • z) = r • gradCoef j z`. Source: Breakdown.Periodic.ShellDefs.Internal.gradCoef_smul' in Breakdown.Torus.ShellDefs, line 321. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L321).

**Source namespace:** Breakdown.Periodic.

**Periodic data on the shell.** At an admissible shell scale the restriction pulls back the periodic derivatives with factor `μ^(3/4)` and velocity with factor `μ^(1/4)`, and otherwise returns zero. Source: Breakdown.Periodic.restrictTorusFun in Breakdown.Torus.ShellDefs, line 329. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L329).

**Uniform bound for periodic restriction.** Periodic shell restriction admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ μ b z, ‖restrictTorusFun μ b z‖ ≤ C * ‖z‖`. Source: Breakdown.Periodic.restrictTorusFun_bound in Breakdown.Torus.ShellDefs, line 340. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L340).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Addition for periodic shell restriction.** Periodic shell restriction obeys the addition identity `restrictTorusFun μ b (z + w) = restrictTorusFun μ b z + restrictTorusFun μ b w`. Source: Breakdown.Periodic.ShellDefs.Internal.restrictTorusFun_add in Breakdown.Torus.ShellDefs, line 356. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L356).

**Scaling for periodic shell restriction.** Periodic shell restriction obeys the scalar-scaling identity `restrictTorusFun μ b (r • z) = r • restrictTorusFun μ b z`. Source: Breakdown.Periodic.ShellDefs.Internal.restrictTorusFun_smul in Breakdown.Torus.ShellDefs, line 372. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L372).

**Linearized advection on shell data.** The shell integrand sums profile times perturbation gradient and perturbation velocity times profile gradient over the three coordinates. Source: Breakdown.Periodic.ShellDefs.Internal.advIntegrand in Breakdown.Torus.ShellDefs, line 395. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L395).

**Shell-advection norm constant.** The auxiliary shell constant combines the profile and gradient bounds with the volume factor for passage from L⁶ to L² on the support ball. Source: Breakdown.Periodic.ShellDefs.Internal.advK in Breakdown.Torus.ShellDefs, line 398. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L398).

**The shell-advection bound is finite.** The extended-real shell-advection bound is finite for every real choice of its three parameters. Source: Breakdown.Periodic.ShellDefs.Internal.advK_ne_top in Breakdown.Torus.ShellDefs, line 402. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L402).

**Bound for shell restriction.** With the stated hypotheses, shell restriction satisfies the quantitative estimate `‖a‖ₑ ≤ ‖c‖ₑ`. Source: Breakdown.Periodic.ShellDefs.Internal.enorm_le_of_norm_le in Breakdown.Torus.ShellDefs, line 410. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L410).

**Uniform bound for test field.** With the stated hypotheses, test field admits the uniform bound stated in `∃ M0 M1 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ (∀ y, ‖φ y‖ ≤ M0) ∧ ∀ j y, ‖Freq.partialField φ j y‖ ≤ M1`. Source: Breakdown.Periodic.ShellDefs.Internal.test_bounds in Breakdown.Torus.ShellDefs, line 415. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L415).

**Continuity of shell restriction.** With the stated hypotheses, shell restriction is continuous on the domain specified by `Continuous (Freq.partialField φ j)`. Source: Breakdown.Periodic.ShellDefs.Internal.continuous_partialField in Breakdown.Torus.ShellDefs, line 426. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L426).

**An L² bound for shell advection.** The ball-restricted shell-advection integrand lies in L² and its L² norm is at most the stated shell constant times the shell-data norm. Source: Breakdown.Periodic.ShellDefs.Internal.advect_bound in Breakdown.Torus.ShellDefs, line 430. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L430).

**Shell advection adds almost everywhere.** The shell-advection integrand is additive in its shell-data input almost everywhere. Source: Breakdown.Periodic.ShellDefs.Internal.advIntegrand_add_ae in Breakdown.Torus.ShellDefs, line 489. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L489).

**Shell advection scales almost everywhere.** The shell-advection integrand respects real scalar multiplication of its shell-data input almost everywhere. Source: Breakdown.Periodic.ShellDefs.Internal.advIntegrand_smul_ae in Breakdown.Torus.ShellDefs, line 504. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L504).

**Source namespace:** Breakdown.Periodic.

**Shell advection as an L² field.** The shell-advection value cuts the linearized advection integrand off to the support ball and takes its L² representative. Source: Breakdown.Periodic.advectShellFun in Breakdown.Torus.ShellDefs, line 520. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L520).

**Uniform bound for shell advection value.** With the stated hypotheses, shell advection value admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ ζ, ‖advectShellFun φ b ζ‖ ≤ C * ‖ζ‖`. Source: Breakdown.Periodic.advectShellFun_bound in Breakdown.Torus.ShellDefs, line 526. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L526).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Addition for shell advection value.** With the stated hypotheses, shell advection value obeys the addition identity `advectShellFun φ b (ζ + ζ') = advectShellFun φ b ζ + advectShellFun φ b ζ'`. Source: Breakdown.Periodic.ShellDefs.Internal.advectShellFun_add in Breakdown.Torus.ShellDefs, line 536. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L536).

**Scaling for shell advection value.** With the stated hypotheses, shell advection value obeys the scalar-scaling identity `advectShellFun φ b (r • ζ) = r • advectShellFun φ b ζ`. Source: Breakdown.Periodic.ShellDefs.Internal.advectShellFun_smul in Breakdown.Torus.ShellDefs, line 548. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L548).

**Source namespace:** Breakdown.Periodic.

**Bounded shell-advection map.** For a test field, shell advection is packaged as a bounded linear map from shell data into real L² fields. Source: Breakdown.Periodic.advectShell in Breakdown.Torus.ShellDefs, line 559. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L559).

**Whole-space shell interaction.** The whole-space shell interaction is the negative projected heat evolution of the shell-advection field. Source: Breakdown.Periodic.lambdaR3 in Breakdown.Torus.ShellDefs, line 566. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L566).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Affine similarity coordinates.** The affine similarity coordinate is `(x−center)/√μ` before periodic wrapping. Source: Breakdown.Periodic.ShellDefs.Internal.simLin in Breakdown.Torus.ShellDefs, line 571. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L571).

**Similarity change-of-volume factor.** The similarity volume factor is the absolute reciprocal determinant of the spatial similarity map. Source: Breakdown.Periodic.ShellDefs.Internal.simConst in Breakdown.Torus.ShellDefs, line 573. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L573).

**Similarity L¹ comparison constant.** The similarity integral constant combines the square-root Jacobian factor with the finite-cell L²-to-L¹ factor. Source: Breakdown.Periodic.ShellDefs.Internal.simK in Breakdown.Torus.ShellDefs, line 575. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L575).

**The similarity bound is nonnegative.** Similarity integral bound is nonnegative, as stated in `0 ≤ simK μ`. Source: Breakdown.Periodic.ShellDefs.Internal.simK_nonneg in Breakdown.Torus.ShellDefs, line 579. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L579).

**Continuity of affine similarity map.** Affine similarity map is continuous on the domain specified by `Continuous (simLin μ)`. Source: Breakdown.Periodic.ShellDefs.Internal.continuous_simLin in Breakdown.Torus.ShellDefs, line 581. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L581).

**Similarity maps preserve null sets.** At positive μ the affine similarity map is quasi measure preserving for Lebesgue measure. Source: Breakdown.Periodic.ShellDefs.Internal.qmp_simLin in Breakdown.Torus.ShellDefs, line 585. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L585).

**Formula for coordinate.** Coordinate obeys the exact identity `volume {x : Space | x i = 1} = 0`. Source: Breakdown.Periodic.ShellDefs.Internal.volume_coord_eq_one in Breakdown.Torus.ShellDefs, line 589. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L589).

**Similarity coordinates are affine.** On almost every point of the unit cell, the periodic similarity coordinates equal the affine similarity coordinates. Source: Breakdown.Periodic.ShellDefs.Internal.simCoord_ae in Breakdown.Torus.ShellDefs, line 602. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L602).

**Bound for affine similarity map.** With the stated hypotheses, affine similarity map satisfies the quantitative estimate `Measure.map (simLin μ) (volume.restrict cell) ≤ simConst μ • volume`. Source: Breakdown.Periodic.ShellDefs.Internal.map_simLin_le in Breakdown.Torus.ShellDefs, line 618. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L618).

**An L² bound for similarity pullback.** For μ > 0, the pulled-back source is measurable on the cell and has L² norm bounded by the square root of the volume-comparison constant times its whole-space L² norm. Source: Breakdown.Periodic.ShellDefs.Internal.eLpNorm_simCoord_le in Breakdown.Torus.ShellDefs, line 629. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L629).

**Norm identity for complexification.** Complexification has the norm identity `‖complexify v‖ = ‖v‖`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_complexify' in Breakdown.Torus.ShellDefs, line 647. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L647).

**The unit cell has finite volume.** The Lebesgue measure of the unit cell is finite. Source: Breakdown.Periodic.ShellDefs.Internal.finite_cell in Breakdown.Torus.ShellDefs, line 653. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L653).

**L² control after similarity pullback.** For μ > 0, pulling an L² source back by periodic similarity coordinates gives an L² field on the unit cell. Source: Breakdown.Periodic.ShellDefs.Internal.memLp_sim in Breakdown.Torus.ShellDefs, line 655. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L655).

**An L¹ bound for the pulled-back source.** At positive μ, the cell integral of the pulled-back source norm is at most the similarity constant times its whole-space L² norm. Source: Breakdown.Periodic.ShellDefs.Internal.integral_simCoord_le in Breakdown.Torus.ShellDefs, line 662. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L662).

**Bound for heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing satisfies the quantitative estimate `‖forceV s F‖ ≤ 2 * Real.sqrt (∑' k, weight k * heatFactor s k ^ 2) * ∫ x in cell, ‖complexify (F x)‖`. Source: Breakdown.Periodic.ShellDefs.Internal.norm_forceV_le in Breakdown.Torus.ShellDefs, line 688. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L688).

**The forcing map sends zero to zero.** With the stated hypotheses, heat-regularized forcing has the zero-parameter identity `forceV s F = 0`. Source: Breakdown.Periodic.ShellDefs.Internal.forceV_eq_zero in Breakdown.Torus.ShellDefs, line 716. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L716).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFree k (c + d) = divFree k c + divFree k d`. Source: Breakdown.Periodic.ShellDefs.Internal.divFree_add' in Breakdown.Torus.ShellDefs, line 722. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L722).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFree k (r • c) = r • divFree k c`. Source: Breakdown.Periodic.ShellDefs.Internal.divFree_smul' in Breakdown.Torus.ShellDefs, line 731. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L731).

**Coefficients of heat-regularized forcing.** With the stated hypotheses, the Fourier-coefficient calculation gives `forceV s F = forceV s G + forceV s H`. Source: Breakdown.Periodic.ShellDefs.Internal.forceV_add_of_coef in Breakdown.Torus.ShellDefs, line 737. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L737).

**Coefficients of heat-regularized forcing.** With the stated hypotheses, the Fourier-coefficient calculation gives `forceV s F = r • forceV s G`. Source: Breakdown.Periodic.ShellDefs.Internal.forceV_smul_of_coef in Breakdown.Torus.ShellDefs, line 749. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L749).

**Formula for complexification.** Complexification obeys the exact identity `complexify (a + b) = complexify a + complexify b`. Source: Breakdown.Periodic.ShellDefs.Internal.complexify_add' in Breakdown.Torus.ShellDefs, line 760. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L760).

**Formula for complexification.** Complexification obeys the exact identity `complexify (r • a) = r • complexify a`. Source: Breakdown.Periodic.ShellDefs.Internal.complexify_smul' in Breakdown.Torus.ShellDefs, line 764. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L764).

**Integrability of complexification.** With the stated hypotheses, complexification satisfies the integrability assertion `IntegrableOn (fun x => complexify ((A : Space → Space) (simCoord μ x))) cell`. Source: Breakdown.Periodic.ShellDefs.Internal.integrableOn_sim in Breakdown.Torus.ShellDefs, line 768. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L768).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef F k = freqTrCoef G k + freqTrCoef H k`. Source: Breakdown.Periodic.ShellDefs.Internal.freqTrCoef_add_ae in Breakdown.Torus.ShellDefs, line 775. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L775).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef F k = r • freqTrCoef G k`. Source: Breakdown.Periodic.ShellDefs.Internal.freqTrCoef_smul_ae in Breakdown.Torus.ShellDefs, line 786. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L786).

**Similarity pullbacks preserve addition.** For μ > 0, pulling the sum of two L² sources into the cell agrees almost everywhere with the sum of their pullbacks. Source: Breakdown.Periodic.ShellDefs.Internal.sim_add_ae in Breakdown.Torus.ShellDefs, line 794. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L794).

**Similarity pullbacks preserve scaling.** For μ > 0, pulling a real scalar multiple of an L² source into the cell agrees almost everywhere with that scalar multiple of the pullback. Source: Breakdown.Periodic.ShellDefs.Internal.sim_smul_ae in Breakdown.Torus.ShellDefs, line 801. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L801).

**Source namespace:** Breakdown.Periodic.

**Rescaled periodic forcing value.** For positive `μ` the source value applies periodic heat forcing at time `μτ` to the source in similarity coordinates, and otherwise returns zero. Source: Breakdown.Periodic.sourceFun in Breakdown.Torus.ShellDefs, line 810. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L810).

**Uniform bound for rescaled forcing value.** Rescaled forcing value admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ A, ‖sourceFun μ τ A‖ ≤ C * ‖A‖`. Source: Breakdown.Periodic.sourceFun_bound in Breakdown.Torus.ShellDefs, line 814. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L814).

**Source namespace:** Breakdown.Periodic.ShellDefs.Internal.

**Addition for rescaled forcing value.** Rescaled forcing value obeys the addition identity `sourceFun μ τ (A + B) = sourceFun μ τ A + sourceFun μ τ B`. Source: Breakdown.Periodic.ShellDefs.Internal.sourceFun_add in Breakdown.Torus.ShellDefs, line 829. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L829).

**Scaling for rescaled forcing value.** Rescaled forcing value obeys the scalar-scaling identity `sourceFun μ τ (r • A) = r • sourceFun μ τ A`. Source: Breakdown.Periodic.ShellDefs.Internal.sourceFun_smul in Breakdown.Torus.ShellDefs, line 838. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L838).

**Source namespace:** Breakdown.Periodic.

**Bounded rescaled forcing operator.** The rescaled periodic source value is packaged as a continuous linear map from real L² fields to periodic Fourier space. Source: Breakdown.Periodic.sourceOp in Breakdown.Torus.ShellDefs, line 844. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L844).

**Periodic shell interaction.** The periodic shell interaction is the negative rescaled source operator applied to shell advection, with factor `μ^(−1/4)`. Source: Breakdown.Periodic.lambdaTorus in Breakdown.Torus.ShellDefs, line 851. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellDefs.lean#L851).

### Breakdown.Torus.ShellR3

Factors whole-space advection through shell data and derives its three-quarter-power heat estimate.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.ShellR3.

**Bound for ball restriction.** Ball restriction satisfies the quantitative estimate `‖cutLp p b‖ ≤ 1`. Source: Breakdown.Periodic.Internal.ShellR3.cutLp_norm_le in Breakdown.Torus.ShellR3, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L14).

**Formula for whole-space restriction.** Whole-space restriction obeys the exact identity `restrictR3 b v = (fun j => cutLp 2 b (Freq.partialX j v), cutLp 6 b (Freq.velocity v))`. Source: Breakdown.Periodic.Internal.ShellR3.restrictR3_apply in Breakdown.Torus.ShellR3, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L19).

**Bound for whole-space shell interaction.** With the stated hypotheses, whole-space shell interaction satisfies the quantitative estimate `‖Freq.partialX j v‖ ≤ ‖v‖`. Source: Breakdown.Periodic.Internal.ShellR3.partialX_norm_le in Breakdown.Torus.ShellR3, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L22).

**Formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the exact identity `Freq.toLpOrZero p f = Freq.toLpOrZero p g`. Source: Breakdown.Periodic.Internal.ShellR3.toLpOrZero_congr in Breakdown.Torus.ShellR3, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L30).

**Bound for Lᵖ representative.** Lᵖ representative satisfies the quantitative estimate `∀ᵐ y ∂volume, ‖(Freq.toLpOrZero p f : Space → F) y‖ ≤ ‖f y‖`. Source: Breakdown.Periodic.Internal.ShellR3.toLpOrZero_norm_le in Breakdown.Torus.ShellR3, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L40).

**Formula for shell advection.** With the stated hypotheses, shell advection obeys the exact identity `advectShell φ hφ b (restrictR3 b v) = Freq.advectTest φ v`. Source: Breakdown.Periodic.Internal.ShellR3.advectShell_restrict in Breakdown.Torus.ShellR3, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L52).

**Real exponents give a Hölder triple.** Positive real exponents satisfying `1/p + 1/q = 1/r` give the corresponding extended-real Hölder triple. Source: Breakdown.Periodic.Internal.ShellR3.lpProdTriple_of_real in Breakdown.Torus.ShellR3, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L79).

**Bound for Lᵖ norm.** With the stated hypotheses, Lᵖ norm satisfies the quantitative estimate `∫⁻ y, ENNReal.ofReal (‖f y‖ * ‖g y‖ * ‖h y‖) ≤ eLpNorm f 6 volume * eLpNorm g 2 volume * (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ)`. Source: Breakdown.Periodic.Internal.ShellR3.lintegral_three_le in Breakdown.Torus.ShellR3, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L85).

**A three-factor Hölder estimate.** The stated L⁶, L² and interpolated L²/L⁶ bounds control the integral of three norms by `ab√(cd)`. Source: Breakdown.Periodic.Internal.ShellR3.lintegral_three_le_real in Breakdown.Torus.ShellR3, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L152).

**Formula for Lᵖ norm.** Lᵖ norm obeys the exact identity `eLpNorm u p volume = ENNReal.ofReal ‖u‖`. Source: Breakdown.Periodic.Internal.ShellR3.eLpNorm_Lp in Breakdown.Torus.ShellR3, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L168).

**Bound for Lᵖ norm.** With the stated hypotheses, Lᵖ norm satisfies the quantitative estimate `eLpNorm u p volume ≤ ENNReal.ofReal r`. Source: Breakdown.Periodic.Internal.ShellR3.eLpNorm_Lp_le in Breakdown.Torus.ShellR3, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L172).

**Formula for product.** With the stated hypotheses, product obeys the exact identity `Real.sqrt ((K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s)) = K * τ ^ (-(3 / 4 : ℝ)) * s`. Source: Breakdown.Periodic.Internal.ShellR3.sqrt_phi_product in Breakdown.Torus.ShellR3, line 177. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L177).

**Bound for inner product.** With the stated hypotheses, inner product satisfies the quantitative estimate `ENNReal.ofReal ‖inner ℝ a u‖ ≤ ∑ j : Fin 3, (ENNReal.ofReal (‖p‖ * ‖z₁ j‖ * ‖u‖) + ENNReal.ofReal (‖z₂‖ * ‖q j‖ * ‖u‖))`. Source: Breakdown.Periodic.Internal.ShellR3.pointwise_inner_le in Breakdown.Torus.ShellR3, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L186).

**Bound for whole-space shell interaction.** With the stated hypotheses, whole-space shell interaction satisfies the quantitative estimate `∫⁻ y, ∑ j : Fin 3, (a j y + c j y) ≤ 3 * (α + γ)`. Source: Breakdown.Periodic.Internal.ShellR3.lintegral_sum_le in Breakdown.Torus.ShellR3, line 215. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L215).

**Bound the integrated shell pairing.** The stated pointwise three-component decomposition and L²/L⁶ bounds imply the pairing bound `3(αβ√(cd)+βγ√(cd))`. Source: Breakdown.Periodic.Internal.ShellR3.integral_bound_of_parts in Breakdown.Torus.ShellR3, line 227. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L227).

**Uniform bound for inner product.** With the stated hypotheses, inner product admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData, ∀ ψ : Freq.X, inner ℝ (Freq.heatDivFree τ (advectShell φ hφ b ζ)) ψ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖ * ‖ψ‖`. Source: Breakdown.Periodic.Internal.ShellR3.inner_heatDivFree_le in Breakdown.Torus.ShellR3, line 268. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L268).

**Source namespace:** Breakdown.Periodic.

**Bound for whole-space interaction.** Under the stated assumptions, the whole-space shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and the shell-data norm. Source: Breakdown.Periodic.r3LambdaBound in Breakdown.Torus.ShellR3, line 373. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellR3.lean#L373).

### Breakdown.Torus.ShellTorus

Factors periodic advection through shell data and proves the corresponding scale-uniform heat estimate.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellTorus.Internal.

**Coefficients for advection coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `advCoef ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) z k + advCoef z ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) k = μ⁻¹ • freqTrCoef (fun x => (advectShell φ hφ b (restrictTorus μ b z) : Space → Space) (simCoord μ x)) k`. Source: Breakdown.Periodic.ShellTorus.Internal.advCoef_transplant in Breakdown.Torus.ShellTorus, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorus.lean#L14).

**Smoothing of a compact shell source.** At a valid shell scale with 0 < μτ ≤ 1, a source supported in the radius-b ball obeys the bound `‖sourceOp μ τ A‖ ≤ C μ^(1/4) τ⁻³ᐟ⁴ ‖A‖₃ᐟ₂` with one nonnegative constant C. Source: Breakdown.Periodic.ShellTorus.Internal.sourceOp_threeHalves in Breakdown.Torus.ShellTorus, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorus.lean#L33).

**Formula for scaling.** With the stated hypotheses, scaling obeys the exact identity `μ ^ (3 / 4 : ℝ) * μ⁻¹ = μ ^ (-(1 / 4 : ℝ))`. Source: Breakdown.Periodic.ShellTorus.Internal.rpow_scale in Breakdown.Torus.ShellTorus, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorus.lean#L72).

**Source namespace:** Breakdown.Periodic.

**Bound for periodic interaction.** Under the stated assumptions, at a valid shell scale with μτ ≤ 1 the periodic shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and shell-data norm. Source: Breakdown.Periodic.torusLambdaBound in Breakdown.Torus.ShellTorus, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorus.lean#L94).

### Breakdown.Torus.ShellTorusBase

Identifies the periodic physical fields and their products, then prepares the dual forcing estimate under transplantation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellTorus.Internal.

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `coeff (r • u) k = r • coeff u k`. Source: Breakdown.Periodic.ShellTorus.Internal.coeff_smul_real in Breakdown.Torus.ShellTorusBase, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L12).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `coeff (-u) k = -coeff u k`. Source: Breakdown.Periodic.ShellTorus.Internal.coeff_neg_vec in Breakdown.Torus.ShellTorusBase, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L16).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFree k (r • c) = r • divFree k c`. Source: Breakdown.Periodic.ShellTorus.Internal.divFree_smul_real in Breakdown.Torus.ShellTorusBase, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L20).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `coeff (forceV s F) k = heatFactor s k • divFree k (freqTrCoef F k)`. Source: Breakdown.Periodic.ShellTorus.Internal.coeff_forceV in Breakdown.Torus.ShellTorusBase, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L29).

**Formula for rescaled source operator.** With the stated hypotheses, rescaled source operator obeys the exact identity `sourceOp μ τ A = forceV (μ * τ) (fun x => (A : Space → Space) (simCoord μ x))`. Source: Breakdown.Periodic.ShellTorus.Internal.sourceOp_apply in Breakdown.Torus.ShellTorusBase, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L34).

**Formula for periodic shell interaction.** With the stated hypotheses, periodic shell interaction obeys the exact identity `lambdaTorus φ hφ b μ τ ζ = -((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ (advectShell φ hφ b ζ))`. Source: Breakdown.Periodic.ShellTorus.Internal.lambdaTorus_apply in Breakdown.Torus.ShellTorusBase, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L39).

**Velocity from the periodic L⁶ series.** The physical velocity field is the real part of the L⁶ Fourier-series representative. Source: Breakdown.Periodic.ShellTorus.Internal.zField in Breakdown.Torus.ShellTorusBase, line 42. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L42).

**Gradient from the periodic L² series.** The physical gradient component is the real part of the L² series of differentiated Fourier coefficients. Source: Breakdown.Periodic.ShellTorus.Internal.gField in Breakdown.Torus.ShellTorusBase, line 44. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L44).

**Symmetric linearized advection field.** The product field sums the smooth field times the periodic gradient and periodic velocity times the smooth field’s derivative. Source: Breakdown.Periodic.ShellTorus.Internal.productField in Breakdown.Torus.ShellTorusBase, line 46. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L46).

**Formula for coordinate.** Coordinate obeys the exact identity `volume {x : Space | x i = a} = 0`. Source: Breakdown.Periodic.ShellTorus.Internal.volume_coord_eq in Breakdown.Torus.ShellTorusBase, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L49).

**Formula for cell center.** Cell center obeys the exact identity `center i = 1 / 2`. Source: Breakdown.Periodic.ShellTorus.Internal.center_coord in Breakdown.Torus.ShellTorusBase, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L56).

**Formula for periodic wrapping.** With the stated hypotheses, periodic wrapping obeys the exact identity `wrap x = x`. Source: Breakdown.Periodic.ShellTorus.Internal.wrap_eq_self in Breakdown.Torus.ShellTorusBase, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L59).

**Formula for periodic wrapping.** Periodic wrapping obeys the exact identity `∀ᵐ x ∂(volume.restrict cell), wrap x = x`. Source: Breakdown.Periodic.ShellTorus.Internal.ae_wrap_eq in Breakdown.Torus.ShellTorusBase, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L65).

**Similarity coordinates after wrapping.** Almost everywhere in the unit cell, similarity coordinates equal `μ⁻¹ᐟ²(x−center)`. Source: Breakdown.Periodic.ShellTorus.Internal.ae_simCoord_eq in Breakdown.Torus.ShellTorusBase, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L72).

**Formula for divergence.** Divergence obeys the exact identity `divergenceAt (fun y => c • f y) x = c * divergenceAt f x`. Source: Breakdown.Periodic.ShellTorus.Internal.divergenceAt_scale in Breakdown.Torus.ShellTorusBase, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L77).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `freqTrCoef (fun x => r • F x) k = r • freqTrCoef F k`. Source: Breakdown.Periodic.ShellTorus.Internal.freqTrCoef_scale in Breakdown.Torus.ShellTorusBase, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L83).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef F k = freqTrCoef G k`. Source: Breakdown.Periodic.ShellTorus.Internal.freqTrCoef_congr in Breakdown.Torus.ShellTorusBase, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L94).

**Value at zero for shell advection.** With the stated hypotheses, shell advection has the zero-parameter identity `∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (advectShell φ hφ b ζ : Space → Space) y = 0`. Source: Breakdown.Periodic.ShellTorus.Internal.advectShell_ae_zero in Breakdown.Torus.ShellTorusBase, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L99).

**Decay property of test field.** With the stated hypotheses, test field satisfies the defined decay-field conditions in `IsDecayField φ`. Source: Breakdown.Periodic.ShellTorus.Internal.isDecay_of_test in Breakdown.Torus.ShellTorusBase, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L110).

**The L⁶ and L² product exponent.** The Hölder exponents 6 and 2 combine to give exponent 3/2 for the product. Source: Breakdown.Periodic.ShellTorus.Internal.lpProdSixTwo in Breakdown.Torus.ShellTorusBase, line 130. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L130).

**Bound for periodic physical field.** Periodic physical field satisfies the quantitative estimate `(1 : ℝ≥0∞) ≤ 3 / 2`. Source: Breakdown.Periodic.ShellTorus.Internal.one_le_threeHalves in Breakdown.Torus.ShellTorusBase, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L140).

**Bound for Lᵖ norm.** With the stated hypotheses, Lᵖ norm satisfies the quantitative estimate `eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume ≤ eLpNorm (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y + (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) (3 / 2) volume`. Source: Breakdown.Periodic.ShellTorus.Internal.eLpNorm_advectShell_le in Breakdown.Torus.ShellTorusBase, line 144. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L144).

**Formula for Lᵖ norm.** Lᵖ norm obeys the exact identity `eLpNorm (f : Space → Space) p volume = ENNReal.ofReal ‖f‖`. Source: Breakdown.Periodic.ShellTorus.Internal.eLpNorm_Lp_eq in Breakdown.Torus.ShellTorusBase, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L156).

**The shell product lies in L³ᐟ².** The L³ᐟ² norm of shell advection is bounded by one nonnegative constant times the test-field embedding norm and the shell-data norm. Source: Breakdown.Periodic.ShellTorus.Internal.advectShell_threeHalves in Breakdown.Torus.ShellTorusBase, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L160).

**Weighted heat test field.** The heat test field takes the real part of the Fourier series with coefficients multiplied by the Sobolev weight and heat factor. Source: Breakdown.Periodic.ShellTorus.Internal.phiField in Breakdown.Torus.ShellTorusBase, line 275. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L275).

**Norm identity for complexification.** Complexification has the norm identity `‖complexify a‖ = ‖a‖`. Source: Breakdown.Periodic.ShellTorus.Internal.norm_complexify in Breakdown.Torus.ShellTorusBase, line 278. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L278).

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ a (Freq.realVec v) = RCLike.re (inner ℂ (complexify a) v)`. Source: Breakdown.Periodic.ShellTorus.Internal.inner_realVec in Breakdown.Torus.ShellTorusBase, line 281. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L281).

**Formula for real part.** Real part obeys the exact identity `RCLike.re (inner ℂ (divFree k c) c) = ‖divFree k c‖ ^ 2`. Source: Breakdown.Periodic.ShellTorus.Internal.re_inner_divFree in Breakdown.Torus.ShellTorusBase, line 285. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L285).

**Norm for heat-regularized forcing.** With the stated hypotheses, heat-regularized forcing has the norm identity `‖forceV s F‖ ^ 2 = ∫ x in cell, inner ℝ (F x) (phiField s (forceV s F) x)`. Source: Breakdown.Periodic.ShellTorus.Internal.norm_sq_forceV in Breakdown.Torus.ShellTorusBase, line 302. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L302).

**The L³ᐟ² and L³ pairing exponent.** The Hölder exponents 3/2 and 3 combine to give an integrable product. Source: Breakdown.Periodic.ShellTorus.Internal.lpProdThreeHalvesThree in Breakdown.Torus.ShellTorusBase, line 392. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L392).

**Bound for periodic physical field.** Periodic physical field satisfies the quantitative estimate `(3 / 2 : ℝ≥0∞) ≤ 2`. Source: Breakdown.Periodic.ShellTorus.Internal.threeHalves_le_two in Breakdown.Torus.ShellTorusBase, line 402. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L402).

**Compact L² sources also lie in L³ᐟ².** An L² source supported almost everywhere in a finite-radius ball has finite L³ᐟ² norm. Source: Breakdown.Periodic.ShellTorus.Internal.eLpNorm_threeHalves_ne_top in Breakdown.Torus.ShellTorusBase, line 406. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L406).

**Integrability of pairing.** With the stated hypotheses, pairing satisfies the integrability assertion `IntegrableOn (fun x => (A : Space → Space) (simCoord μ x)) cell ∧ |∫ x in cell, inner ℝ ((A : Space → Space) (simCoord μ x)) (G x)| ≤ μ * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal * (eLpNorm G 3 (volume.restrict cell)).toReal`. Source: Breakdown.Periodic.ShellTorus.Internal.pairing_transplant in Breakdown.Torus.ShellTorusBase, line 428. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusBase.lean#L428).

### Breakdown.Torus.ShellTorusPhi

Estimates the weighted heat test field in L³ by interpolating its L² and L⁶ bounds.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellTorus.Internal.

**Weighted heat-test coefficient.** The heat-test coefficient multiplies the field coefficient by the Sobolev weight and the heat multiplier. Source: Breakdown.Periodic.ShellTorus.Internal.shellCoef in Breakdown.Torus.ShellTorusPhi, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L14).

**Bound for weighted heat field.** With the stated hypotheses, weighted heat field satisfies the quantitative estimate `(1 + y) * Real.exp (-(y * s)) ≤ 1 + 1 / s`. Source: Breakdown.Periodic.ShellTorus.Internal.exp_mul_bound in Breakdown.Torus.ShellTorusPhi, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L16).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `0 ≤ weight k * heatFactor s k ∧ weight k * heatFactor s k ≤ 2 / s`. Source: Breakdown.Periodic.ShellTorus.Internal.weight_heat_bound in Breakdown.Torus.ShellTorusPhi, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L30).

**Weighted heat coefficients.** The norm of a weighted heat-test coefficient is exactly its Sobolev weight times its heat factor times the original physical-coefficient norm. Source: Breakdown.Periodic.ShellTorus.Internal.norm_shellCoef in Breakdown.Torus.ShellTorusPhi, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L44).

**Summability of weighted heat coefficient.** With the stated hypotheses, weighted heat coefficient satisfies the series-convergence assertion `Summable fun k => ‖shellCoef s ψ k‖`. Source: Breakdown.Periodic.ShellTorus.Internal.summable_norm_shellCoef in Breakdown.Torus.ShellTorusPhi, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L49).

**Bound for weighted heat coefficient.** With the stated hypotheses, weighted heat coefficient satisfies the quantitative estimate `‖shellCoef s ψ k‖ ^ 2 ≤ 2 / s * (weight k * ‖coeff ψ k‖ ^ 2)`. Source: Breakdown.Periodic.ShellTorus.Internal.sq_norm_shellCoef_le in Breakdown.Torus.ShellTorusPhi, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L58).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * ‖shellCoef s ψ k‖ ^ 2 ≤ (2 / s) ^ 2 * (weight k * ‖coeff ψ k‖ ^ 2)`. Source: Breakdown.Periodic.ShellTorus.Internal.weight_sq_norm_shellCoef_le in Breakdown.Torus.ShellTorusPhi, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L76).

**A bounded Fourier summand.** A Fourier summand is packaged as a bounded continuous function with bound equal to the coefficient norm. Source: Breakdown.Periodic.ShellTorus.Internal.termBounded in Breakdown.Torus.ShellTorusPhi, line 86. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L86).

**Bound for bounded Fourier summand.** Bounded Fourier summand satisfies the quantitative estimate `‖termBounded c k‖ ≤ ‖c k‖`. Source: Breakdown.Periodic.ShellTorus.Internal.norm_termBounded_le in Breakdown.Torus.ShellTorusPhi, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L90).

**Representative of Fourier series.** With the stated hypotheses, periodic Fourier series has the almost-everywhere representation `(torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell] fun x => ∑' k, character (-k) x • c k`. Source: Breakdown.Periodic.ShellTorus.Internal.torusSeries_ae_eq in Breakdown.Torus.ShellTorusPhi, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L95).

**Formula for weighted heat field.** Weighted heat field obeys the exact identity `(4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2`. Source: Breakdown.Periodic.ShellTorus.Internal.four_mul_half in Breakdown.Torus.ShellTorusPhi, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L113).

**Formula for weighted heat field.** Weighted heat field obeys the exact identity `(12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6`. Source: Breakdown.Periodic.ShellTorus.Internal.twelve_mul_half in Breakdown.Torus.ShellTorusPhi, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L118).

**The L⁴ and L¹² product exponent.** The Hölder exponents 4 and 12 combine to give exponent 3 for the product. Source: Breakdown.Periodic.ShellTorus.Internal.lpProdFourTwelve in Breakdown.Torus.ShellTorusPhi, line 123. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L123).

**Bound for Lᵖ norm.** With the stated hypotheses, Lᵖ norm satisfies the quantitative estimate `eLpNorm f 3 μ ≤ eLpNorm f 2 μ ^ (1 / 2 : ℝ) * eLpNorm f 6 μ ^ (1 / 2 : ℝ)`. Source: Breakdown.Periodic.ShellTorus.Internal.eLpNorm_three_le in Breakdown.Torus.ShellTorusPhi, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L132).

**Bound for Lᵖ norm.** With the stated hypotheses, Lᵖ norm satisfies the quantitative estimate `eLpNorm (phiField s ψ) p (volume.restrict cell) ≤ ENNReal.ofReal ‖torusSeries p (shellCoef s ψ)‖`. Source: Breakdown.Periodic.ShellTorus.Internal.eLpNorm_phi_le in Breakdown.Torus.ShellTorusPhi, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L147).

**Bound for periodic Fourier series.** With the stated hypotheses, periodic Fourier series satisfies the quantitative estimate `‖torusSeries 2 (shellCoef s ψ)‖ ^ 2 ≤ 2 / s * ‖ψ‖ ^ 2`. Source: Breakdown.Periodic.ShellTorus.Internal.torusSeries_two_le in Breakdown.Torus.ShellTorusPhi, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L156).

**Bound for periodic Fourier series.** With the stated hypotheses, periodic Fourier series satisfies the quantitative estimate `‖torusSeries 6 (shellCoef s ψ)‖ ≤ C * (2 / s * ‖ψ‖)`. Source: Breakdown.Periodic.ShellTorus.Internal.torusSeries_six_le in Breakdown.Torus.ShellTorusPhi, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L164).

**Uniform weighted heat-field bound.** The periodic Sobolev interface gives `‖phiField s ψ‖₃ ≤ C s⁻³ᐟ⁴ ‖ψ‖` for 0 < s ≤ 1, with one nonnegative constant C. Source: Breakdown.Periodic.ShellTorus.Internal.phiField_bound in Breakdown.Torus.ShellTorusPhi, line 181. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusPhi.lean#L181).

### Breakdown.Torus.ShellTorusProduct

Matches the symmetric Fourier advection convolution with the physical product field.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellTorus.Internal.

**Finite measure of the unit cell.** Lebesgue measure restricted to the unit cell is a finite measure. Source: Breakdown.Periodic.ShellTorus.Internal.finiteCellMeasure in Breakdown.Torus.ShellTorusProduct, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L14).

**Formula for Fourier character.** Fourier character obeys the exact identity `character (k - m) x = character k x * character (-m) x`. Source: Breakdown.Periodic.ShellTorus.Internal.character_sub_eq in Breakdown.Torus.ShellTorusProduct, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L17).

**Orthogonality of Fourier characters.** The cell integral of the product of the k-character and the negative j-character is one when j = k and zero otherwise. Source: Breakdown.Periodic.ShellTorus.Internal.integral_character_mul in Breakdown.Torus.ShellTorusProduct, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L21).

**Uniform bound for integral.** With the stated hypotheses, integral admits the uniform bound stated in `∃ K : NNReal, ∀ g : Lp Coef p (volume.restrict cell), ∫ x in cell, ‖(g : Space → Coef) x‖ ≤ K * ‖g‖`. Source: Breakdown.Periodic.ShellTorus.Internal.integral_norm_le_Lp in Breakdown.Torus.ShellTorusProduct, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L30).

**Recover one Fourier-series coefficient.** Integrating a summable periodic Lᵖ Fourier series against the forward k-character recovers its kth coefficient for finite p ≥ 1. Source: Breakdown.Periodic.ShellTorus.Internal.integral_character_torusSeries in Breakdown.Torus.ShellTorusProduct, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L56).

**Conjugate symmetry gives a real field.** A summable periodic series whose coefficients obey reflection-conjugation symmetry is real-valued almost everywhere in the cell. Source: Breakdown.Periodic.ShellTorus.Internal.real_torusSeries in Breakdown.Torus.ShellTorusProduct, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L107).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `coeff z (-k) i = starRingEnd ℂ (coeff z k i)`. Source: Breakdown.Periodic.ShellTorus.Internal.coeff_neg_apply in Breakdown.Torus.ShellTorusProduct, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L143).

**Coefficients for gradient coefficient.** The Fourier-coefficient calculation gives `gradCoef j z (-k) i = starRingEnd ℂ (gradCoef j z k i)`. Source: Breakdown.Periodic.ShellTorus.Internal.gradCoef_neg_apply in Breakdown.Torus.ShellTorusProduct, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L149).

**Sum of Fourier character.** With the stated hypotheses, Fourier character has the exact series sum in `HasSum (fun l => β l • ∫ x in cell, character (k - l) x • H x) (∫ x in cell, g x • (character k x • H x))`. Source: Breakdown.Periodic.ShellTorus.Internal.hasSum_scalar_series in Breakdown.Torus.ShellTorusProduct, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L155).

**Sum of Fourier character.** With the stated hypotheses, Fourier character has the exact series sum in `HasSum (fun l => (∫ x in cell, character (k - l) x * h x) • β l) (∫ x in cell, h x • (character k x • g x))`. Source: Breakdown.Periodic.ShellTorus.Internal.hasSum_vector_series in Breakdown.Torus.ShellTorusProduct, line 181. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L181).

**Formula for complexification.** Complexification obeys the exact identity `complexify (∑ j, F j) = ∑ j, complexify (F j)`. Source: Breakdown.Periodic.ShellTorus.Internal.complexify_finsum in Breakdown.Torus.ShellTorusProduct, line 210. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L210).

**Scaling formula for complexification.** Complexification obeys the scalar-scaling identity `complexify (r • v + s • w) = (r : ℂ) • complexify v + (s : ℂ) • complexify w`. Source: Breakdown.Periodic.ShellTorus.Internal.complexify_add_smul in Breakdown.Torus.ShellTorusProduct, line 213. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L213).

**Coefficients for advection coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `advCoef a z k + advCoef z a k = freqTrCoef (productField f z) k`. Source: Breakdown.Periodic.ShellTorus.Internal.advCoef_product in Breakdown.Torus.ShellTorusProduct, line 219. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusProduct.lean#L219).

### Breakdown.Torus.ShellTorusTransplant

Checks the almost-everywhere product and derivative formulas under periodic transplantation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ShellTorus.Internal.

**Cell boundaries have zero volume.** Almost every point of the closed unit cell has all three coordinates strictly between zero and one. Source: Breakdown.Periodic.ShellTorus.Internal.ae_mem_open_cell in Breakdown.Torus.ShellTorusTransplant, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L12).

**Similarity coordinates in the cell.** At every point whose coordinates lie strictly between zero and one, periodic similarity coordinates equal `μ⁻¹ᐟ²(x−center)`. Source: Breakdown.Periodic.ShellTorus.Internal.simCoord_open_cell in Breakdown.Torus.ShellTorusTransplant, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L21).

**Derivative formula for transplantation.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun x' => μ ^ (1 / 4 : ℝ) • transplantField μ φ x') x v = (μ ^ (1 / 4 : ℝ) * ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹)) • fderiv ℝ φ ((Real.sqrt μ)⁻¹ • (x - center)) v`. Source: Breakdown.Periodic.ShellTorus.Internal.fderiv_transplant_open_cell in Breakdown.Torus.ShellTorusTransplant, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L25).

**The inverse affine scale preserves nulls.** For μ > 0, subtracting the cell center and scaling by μ⁻¹ᐟ² gives a quasi measure preserving map for Lebesgue measure. Source: Breakdown.Periodic.ShellTorus.Internal.qmp_simAffine in Breakdown.Torus.ShellTorusTransplant, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L50).

**Formula for shell advection.** With the stated hypotheses, shell advection obeys the exact identity `∀ᵐ y ∂volume, (advectShell φ hφ b (restrictTorus μ b z) : Space → Space) y = (Metric.closedBall (0 : Space) b).indicator (fun y => ∑ j : Fin 3, (φ y j • (μ ^ (3 / 4 : ℝ) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))) + (μ ^ (1 / 4 : ℝ) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))) j • Freq.partialField φ j y)) y`. Source: Breakdown.Periodic.ShellTorus.Internal.advectShell_restrict_ae in Breakdown.Torus.ShellTorusTransplant, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L55).

**Representative of linear advection field.** With the stated hypotheses, linearized advection field has the almost-everywhere representation `productField (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) z =ᵐ[volume.restrict cell] fun x => μ⁻¹ • (advectShell φ hφ b (restrictTorus μ b z) : Space → Space) (simCoord μ x)`. Source: Breakdown.Periodic.ShellTorus.Internal.productField_transplant in Breakdown.Torus.ShellTorusTransplant, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ShellTorusTransplant.lean#L108).

### Breakdown.Torus.SourceCont

Proves positive-time continuity of the periodic forcing map and the rescaled source operator.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.SourceCont.Internal.

**Formula for heat-regularized forcing.** Heat-regularized forcing obeys the exact identity `((forceV s F : V) : Seq) k = forceSeq s F k`. Source: Breakdown.Periodic.SourceCont.Internal.forceV_apply in Breakdown.Torus.SourceCont, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SourceCont.lean#L12).

**Bound for forcing coefficients.** With the stated hypotheses, forcing coefficients satisfies the quantitative estimate `‖forceSeq s F k‖ ≤ 2 * (∫ x in cell, ‖complexify (F x)‖) * (Real.sqrt (weight k) * heatFactor s₁ k)`. Source: Breakdown.Periodic.SourceCont.Internal.norm_forceSeq_le_of_le in Breakdown.Torus.SourceCont, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SourceCont.lean#L15).

**Continuity of heat-regularized forcing.** Heat-regularized forcing is continuous on the domain specified by `ContinuousOn (fun s => forceV s F) (Ioi 0)`. Source: Breakdown.Periodic.SourceCont.Internal.forceV_continuousOn in Breakdown.Torus.SourceCont, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SourceCont.lean#L29).

**Source namespace:** Breakdown.Periodic.

**Continuity of rescaled source operator.** With the stated hypotheses, rescaled source operator is continuous on the domain specified by `ContinuousOn (fun τ => sourceOp μ τ A) (Ioi 0)`. Source: Breakdown.Periodic.sourceOp_continuousOn in Breakdown.Torus.SourceCont, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/SourceCont.lean#L59).

### Breakdown.Torus.StatementsAnalysis

States periodic mild uniqueness and the trilinear Fourier estimate needed for the sharp kernel bound.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Uniqueness of periodic mild flow.** This proposition requires that periodic mild solutions on half-open and closed intervals with the same initial value agree on the half-open interval. Source: Breakdown.Periodic.MildUniqueness in Breakdown.Torus.StatementsAnalysis, line 12. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsAnalysis.lean#L12).

**Periodic trilinear estimate.** This proposition requires that the periodic advection pairing is bounded by the two input norms times the quarter powers of the unweighted and weighted squared test norms. Source: Breakdown.Periodic.TrilinearBound in Breakdown.Torus.StatementsAnalysis, line 15. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsAnalysis.lean#L15).

### Breakdown.Torus.StatementsApprox

Defines the cutoff geometry, similarity variables, localized pressure and PDE residual.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Central localization radius.** The central localization radius is `1/4`. Source: Breakdown.Periodic.centralRadius in Breakdown.Torus.StatementsApprox, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L13).

**Bump for the localization annulus.** The central bump has inner radius `1/16` and outer radius `1/8` about the cell center. Source: Breakdown.Periodic.centralBump in Breakdown.Torus.StatementsApprox, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L15).

**Central cutoff function.** The central cutoff is the value of the chosen smooth central bump. Source: Breakdown.Periodic.centralCut in Breakdown.Torus.StatementsApprox, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L21).

**Logarithmic similarity time.** The similarity time is `−log((T−t)/T)`. Source: Breakdown.Periodic.similarityTime in Breakdown.Torus.StatementsApprox, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L23).

**Velocity in physical variables.** The physical self-similar velocity evaluates the profile at logarithmic time and spatial scale `(T−t)^(−1/2)`, with the same factor on its value. Source: Breakdown.Periodic.selfSimilar in Breakdown.Torus.StatementsApprox, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L25).

**Pressure in physical variables.** The physical self-similar pressure evaluates the profile pressure in similarity variables and multiplies by `(T−t)⁻¹`. Source: Breakdown.Periodic.selfSimilarPressure in Breakdown.Torus.StatementsApprox, line 28. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L28).

**Reference point for pressure.** The pressure reference point is displaced from the cell center by three-eighths of the central radius in the first coordinate. Source: Breakdown.Periodic.pressureAnchor in Breakdown.Torus.StatementsApprox, line 31. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L31).

**Localized pressure difference.** The localized pressure multiplies the central cutoff by the difference between the physical pressure and its value at the reference point. Source: Breakdown.Periodic.approxPressure in Breakdown.Torus.StatementsApprox, line 36. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L36).

**Residual of the localized PDE.** The residual is the time derivative plus advection minus the Laplacian plus the gradient of the localized pressure. Source: Breakdown.Periodic.approxResidual in Breakdown.Torus.StatementsApprox, line 39. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L39).

**Equation for the self-similar flow.** This proposition requires that the self-similar profile yields a smooth divergence-free velocity and pressure satisfying the viscosity-one equation before time T. Source: Breakdown.Periodic.SelfSimilarSolves in Breakdown.Torus.StatementsApprox, line 43. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L43).

**Support and size of the residual.** This proposition requires that for 0 < T ≤ 1 the localized residual is supported in the annulus of radii 1/16 and 1/8 and is bounded by K(T−t)⁻¹ᐟ². Source: Breakdown.Periodic.ApproxResidualBound in Breakdown.Torus.StatementsApprox, line 59. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApprox.lean#L59).

### Breakdown.Torus.StatementsApproxSteps

States the matching of localized time pieces and the comparison of their first datum with a transplanted test field.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Localized profile on one time piece.** The approximate piece restricts the periodic localized velocity to the affine time window and multiplies by the fourth root of its time scale. Source: Breakdown.Periodic.approxPiece in Breakdown.Torus.StatementsApproxSteps, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L13).

**Matching localized time pieces.** This proposition requires that the localized time pieces satisfy their evaluation formula and match adjacent endpoints with the factor λ^(1/4). Source: Breakdown.Periodic.ApproxLinks in Breakdown.Torus.StatementsApproxSteps, line 17. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L17).

**Small-scale initial-data comparison.** This proposition requires that at sufficiently small T the scaled periodic initial-data discrepancy is bounded by the whole-space embedding discrepancy plus any positive tolerance. Source: Breakdown.Periodic.DatumClose in Breakdown.Torus.StatementsApproxSteps, line 50. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L50).

**Additivity of periodic embedding.** This proposition requires that the periodic Fourier embedding is additive on smooth periodic divergence-free fields. Source: Breakdown.Periodic.ToVAdd in Breakdown.Torus.StatementsApproxSteps, line 57. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsApproxSteps.lean#L57).

### Breakdown.Torus.StatementsCoeff

States the periodic Fourier differentiation, reconstruction, advection and time-continuity interfaces.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Fourier coefficients of derivatives.** This proposition requires that a C¹ periodic coordinate derivative multiplies the original Fourier coefficient by 2πi times that frequency coordinate. Source: Breakdown.Periodic.CoefDeriv in Breakdown.Torus.StatementsCoeff, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L10).

**Fourier coefficients of the Laplacian.** This proposition requires that the Laplacian of a C² periodic field multiplies each Fourier coefficient by −4π² times the squared frequency norm. Source: Breakdown.Periodic.CoefSumSecondPartials in Breakdown.Torus.StatementsCoeff, line 15. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L15).

**Fourier coefficients of a gradient.** This proposition requires that the gradient of a C¹ periodic scalar field has Fourier coefficient 2πi times its scalar coefficient and frequency vector. Source: Breakdown.Periodic.CoefGradient in Breakdown.Torus.StatementsCoeff, line 19. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L19).

**Fourier reconstruction contract.** This proposition requires that a smooth periodic divergence-free field has the expected embedding coefficients, absolutely summable Fourier coefficients and pointwise Fourier reconstruction. Source: Breakdown.Periodic.FreqTrSeriesSpec in Breakdown.Torus.StatementsCoeff, line 23. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L23).

**Fourier coefficients of advection.** This proposition requires that smooth periodic divergence-free self-advection has the convolution coefficients used by the periodic bilinear kernel. Source: Breakdown.Periodic.CoefAdvection in Breakdown.Torus.StatementsCoeff, line 28. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L28).

**Time differentiation of coefficients.** This proposition requires that a smooth family of periodic fields has Fourier coefficients continuous up to time zero and differentiable by differentiating the field at positive times. Source: Breakdown.Periodic.CoefTimeDeriv in Breakdown.Torus.StatementsCoeff, line 32. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L32).

**Continuity of periodic embedding.** This proposition requires that the periodic Fourier embedding of a smooth divergence-free periodic family is continuous for nonnegative time. Source: Breakdown.Periodic.ToVContinuous in Breakdown.Torus.StatementsCoeff, line 39. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCoeff.lean#L39).

### Breakdown.Torus.StatementsCutoff

Defines coordinate curl and states the vector-potential and solenoidal-cutoff interfaces.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Three-dimensional cross product.** The cross product uses the ordinary three-coordinate cross product in the Euclidean-space representation. Source: Breakdown.Periodic.cross in Breakdown.Torus.StatementsCutoff, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L10).

**A coordinate partial derivative.** The coordinate partial is component `j` of the field derivative in direction `i`. Source: Breakdown.Periodic.partialAt in Breakdown.Torus.StatementsCutoff, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L12).

**Curl in three coordinates.** The curl collects the three antisymmetric coordinate differences of first derivatives. Source: Breakdown.Periodic.curlAt in Breakdown.Torus.StatementsCutoff, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L14).

**A vector potential for solenoidal flow.** This proposition requires that the radial homotopy construction gives a smooth vector potential whose curl is the original smooth divergence-free field. Source: Breakdown.Periodic.HomotopyCurl in Breakdown.Torus.StatementsCutoff, line 21. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L21).

**Divergence-free spatial cutoff.** This proposition requires that cutting off the vector potential of a smooth divergence-free field and taking its curl gives a smooth divergence-free field. Source: Breakdown.Periodic.CutoffDivergenceFree in Breakdown.Torus.StatementsCutoff, line 28. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsCutoff.lean#L28).

### Breakdown.Torus.StatementsForce

Constructs the heat-regularized forcing field and states the forced periodic-to-mild and smoothing interfaces.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Fourier sequence of heat forcing.** For positive elapsed time the forcing sequence applies the square-root Sobolev weight, heat multiplier and Leray projection to the source coefficients, and otherwise vanishes. Source: Breakdown.Periodic.forceSeq in Breakdown.Torus.StatementsForce, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L12).

**Source namespace:** Breakdown.Periodic.Force.Internal.

**Formula for Fourier character.** Fourier character obeys the exact identity `character (-k) x * character k x = 1`. Source: Breakdown.Periodic.Force.Internal.character_neg_mul in Breakdown.Torus.StatementsForce, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L17).

**Integrability of Fourier character.** With the stated hypotheses, Fourier character satisfies the integrability assertion `IntegrableOn (fun x => character k x • G x) cell`. Source: Breakdown.Periodic.Force.Internal.integrableOn_character_smul in Breakdown.Torus.StatementsForce, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L21).

**Take a coordinate through an integral.** Each coordinate of the cell integral of an integrable complex vector field equals the cell integral of that coordinate. Source: Breakdown.Periodic.Force.Internal.integral_apply in Breakdown.Torus.StatementsForce, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L28).

**Coefficients for Fourier coefficient.** The Fourier-coefficient calculation gives `(freqTrCoef F (-k)).ofLp i = starRingEnd ℂ ((freqTrCoef F k).ofLp i)`. Source: Breakdown.Periodic.Force.Internal.freqTrCoef_neg_apply in Breakdown.Torus.StatementsForce, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L35).

**Nonzero frequencies give nonzero vectors.** A nonzero lattice frequency has a nonzero complex frequency vector. Source: Breakdown.Periodic.Force.Internal.latVec_ne_zero in Breakdown.Torus.StatementsForce, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L58).

**Formula for divergence pairing.** Divergence pairing obeys the exact identity `divPairing k (divFree k c) = 0`. Source: Breakdown.Periodic.Force.Internal.divPairing_divFree in Breakdown.Torus.StatementsForce, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L65).

**Scaling formula for divergence pairing.** Divergence pairing obeys the scalar-scaling identity `divPairing k (r • c) = r * divPairing k c`. Source: Breakdown.Periodic.Force.Internal.divPairing_real_smul in Breakdown.Torus.StatementsForce, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L78).

**Sign formula for heat multiplier.** Heat multiplier obeys the sign-change identity `heatFactor t (-k) = heatFactor t k`. Source: Breakdown.Periodic.Force.Internal.heatFactor_neg in Breakdown.Torus.StatementsForce, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L84).

**Formula for Leray projection.** With the stated hypotheses, Leray projection obeys the exact identity `(divFree (-k) d).ofLp i = starRingEnd ℂ ((divFree k c).ofLp i)`. Source: Breakdown.Periodic.Force.Internal.divFree_neg_apply in Breakdown.Torus.StatementsForce, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L87).

**Bound for forcing coefficients.** With the stated hypotheses, forcing coefficients satisfies the quantitative estimate `‖forceSeq τ F k‖ ≤ Real.sqrt (weight k) * heatFactor τ k * (2 * ‖freqTrCoef F k‖)`. Source: Breakdown.Periodic.Force.Internal.norm_forceSeq_le in Breakdown.Torus.StatementsForce, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L99).

**Bound for forcing coefficients.** With the stated hypotheses, forcing coefficients satisfies the quantitative estimate `‖forceSeq τ F k‖ ^ 2 ≤ 4 * ‖freqTrCoef F k‖ ^ 2 * (weight k * heatFactor τ k ^ 2)`. Source: Breakdown.Periodic.Force.Internal.sq_norm_forceSeq_le in Breakdown.Torus.StatementsForce, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L107).

**Source namespace:** Breakdown.Periodic.

**Forcing coefficients are square summable.** For every elapsed time and source field, the heat-forcing coefficients form a square-summable sequence. Source: Breakdown.Periodic.memℓp_forceSeq in Breakdown.Torus.StatementsForce, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L119).

**Forcing lies in the Fourier field space.** The heat-regularized forcing sequence belongs to the real solenoidal sequence subspace for every elapsed time and source field. Source: Breakdown.Periodic.forceSeq_mem in Breakdown.Torus.StatementsForce, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L135).

**Heat forcing in periodic space.** The forcing sequence and its square-summability, reality and solenoidal proofs are packaged as an element of periodic Fourier space. Source: Breakdown.Periodic.forceV in Breakdown.Torus.StatementsForce, line 151. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L151).

**Forced periodic mild solution.** A forced mild solution is continuous on the closed interval, has the two required time integrals and satisfies the forced Duhamel identity. Source: Breakdown.Periodic.IsForcedMildOnIcc in Breakdown.Torus.StatementsForce, line 153. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L153).

**Smooth forced periodic solution.** A forced periodic solution consists of smooth periodic velocity and pressure, a continuous periodic force, divergence-free velocity and the forced PDE on the open time interval. Source: Breakdown.Periodic.IsForcedPeriodicSolution in Breakdown.Torus.StatementsForce, line 160. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L160).

**From forced PDE to mild flow.** This proposition requires that a smooth forced periodic solution on a nontrivial closed time slab yields the corresponding forced periodic mild solution. Source: Breakdown.Periodic.ForcedPeriodicIsMild in Breakdown.Torus.StatementsForce, line 170. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L170).

**Smoothing of periodic forcing.** This proposition requires that for 0 < τ ≤ 1 the periodic forcing operator is bounded by Cτ⁻¹ᐟ² times the source L² norm over the unit cell. Source: Breakdown.Periodic.ForceSmoothing in Breakdown.Torus.StatementsForce, line 174. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsForce.lean#L174).

### Breakdown.Torus.StatementsInverse

States perturbation bounds for the sequence operators and the finite-dimensional test-field lifting interfaces.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Stability of correction operators.** This proposition requires that the whole-space and periodic correction operators change by at most 8CKL^(1/4)M when their reference pieces differ uniformly by M. Source: Breakdown.Periodic.OpDiffBounds in Breakdown.Torus.StatementsInverse, line 35. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L35).

**Physical representatives of test data.** A test lift records a linear family of test fields with common compact support whose Fourier embeddings equal the prescribed finite-dimensional map. Source: Breakdown.Periodic.TestLift in Breakdown.Torus.StatementsInverse, line 61. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L61).

**Lift finite-dimensional test data.** This proposition requires that a finite-dimensional map with range in the span of test fields has a test-field lift with one common positive support radius. Source: Breakdown.Periodic.TestLiftExists in Breakdown.Torus.StatementsInverse, line 67. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L67).

**Lift test data to the periodic space.** This proposition requires that a finite-dimensional test lift at a valid shell scale induces the linear periodic lift μ^(1/4) times the Fourier embedding of its transplant. Source: Breakdown.Periodic.TorusLiftExists in Breakdown.Torus.StatementsInverse, line 71. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsInverse.lean#L71).

### Breakdown.Torus.StatementsShell

States recovery of smooth fields from periodic series and the whole-space and periodic shell-interaction bounds.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Smooth Fourier representatives.** This proposition requires that the periodic velocity and its derivatives agree almost everywhere with the smooth field and its complexified derivatives in the required L² and L⁶ spaces. Source: Breakdown.Periodic.TorusSeriesSmooth in Breakdown.Torus.StatementsShell, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L10).

**Bound for whole-space interaction.** This proposition requires that the whole-space shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and the shell-data norm. Source: Breakdown.Periodic.R3LambdaBound in Breakdown.Torus.StatementsShell, line 24. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L24).

**Bound for periodic interaction.** This proposition requires that at a valid shell scale with μτ ≤ 1 the periodic shell interaction is bounded by Cτ⁻³ᐟ⁴ times the embedded test-field norm and shell-data norm. Source: Breakdown.Periodic.TorusLambdaBound in Breakdown.Torus.StatementsShell, line 34. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsShell.lean#L34).

### Breakdown.Torus.StatementsSmooth

Defines unit-periodicity, the unit cell and the Fourier coefficient conventions for real vector fields.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Unit-periodic spatial field.** A periodic field is invariant under translation by each of the three coordinate unit vectors. Source: Breakdown.Periodic.IsPeriodic in Breakdown.Torus.StatementsSmooth, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L10).

**Closed unit cube.** The periodic integration cell consists of the points whose three coordinates lie in `[0,1]`. Source: Breakdown.Periodic.cell in Breakdown.Torus.StatementsSmooth, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L12).

**Real vectors as complex coefficients.** Complexification regards each real coordinate as a complex coordinate. Source: Breakdown.Periodic.complexify in Breakdown.Torus.StatementsSmooth, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L14).

**Forward Fourier character.** The forward Fourier character is `exp(−2πi⟨k,x⟩)`. Source: Breakdown.Periodic.character in Breakdown.Torus.StatementsSmooth, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L16).

**Vector Fourier coefficient.** The vector coefficient integrates the forward Fourier character times the complexified field over the unit cell. Source: Breakdown.Periodic.freqTrCoef in Breakdown.Torus.StatementsSmooth, line 19. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L19).

**Scalar Fourier coefficient.** The scalar coefficient integrates the forward Fourier character times the scalar field over the unit cell. Source: Breakdown.Periodic.scalarCoef in Breakdown.Torus.StatementsSmooth, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L22).

**Sobolev-weighted Fourier coefficient.** The weighted coefficient multiplies the physical Fourier coefficient by the square root of its Sobolev weight. Source: Breakdown.Periodic.weightedCoef in Breakdown.Torus.StatementsSmooth, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSmooth.lean#L25).

### Breakdown.Torus.StatementsSteps

Records bounds on the geometric time scales and defines which time piece contains a physical time.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**Positivity of piece time scale.** With the stated hypotheses, piece time scale is strictly positive, as stated in `0 < stepScale T lam n`. Source: Breakdown.Periodic.stepScale_pos in Breakdown.Torus.StatementsSteps, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L63).

**Bound for piece time scale.** With the stated hypotheses, piece time scale satisfies the quantitative estimate `stepScale T lam n ≤ 1`. Source: Breakdown.Periodic.stepScale_le_one in Breakdown.Torus.StatementsSteps, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L66).

**Index of the geometric time window.** The time-window index is the natural-number floor of `log((T−t)/T) / log λ`. Source: Breakdown.Periodic.stepNumber in Breakdown.Torus.StatementsSteps, line 72. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/StatementsSteps.lean#L72).

### Breakdown.Torus.TestLift

Lifts a finite-dimensional space of test data to physical test fields with a common support radius and then to periodic Fourier space.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.TestLift.

**Differentiability of test field.** With the stated hypotheses, test field is differentiable as asserted in `DifferentiableAt ℝ φ y`. Source: Breakdown.Periodic.Internal.TestLift.diffAt_of_test in Breakdown.Torus.TestLift, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L13).

**Test fields are closed under addition.** The sum of two test fields is again a smooth compactly supported divergence-free test field. Source: Breakdown.Periodic.Internal.TestLift.isTest_add in Breakdown.Torus.TestLift, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L17).

**Test fields are closed under scaling.** Every real scalar multiple of a test field is a test field. Source: Breakdown.Periodic.Internal.TestLift.isTest_smul in Breakdown.Torus.TestLift, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L27).

**The zero field is a test field.** The zero field is smooth, compactly supported and divergence-free. Source: Breakdown.Periodic.Internal.TestLift.isTest_zero in Breakdown.Torus.TestLift, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L36).

**Decay property of test-field combination.** With the stated hypotheses, test-field combination satisfies the defined decay-field conditions in `IsDecayField φ`. Source: Breakdown.Periodic.Internal.TestLift.isDecay_of_isTest in Breakdown.Torus.TestLift, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L41).

**Finite combinations are test fields.** Every finite real-weighted sum of test fields is a test field. Source: Breakdown.Periodic.Internal.TestLift.isTest_sum_smul in Breakdown.Torus.TestLift, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L74).

**Support of a finite test-field sum.** If each field in the stated finite family has topological support in K, then the weighted finite sum also has topological support in K. Source: Breakdown.Periodic.Internal.TestLift.tsupport_sum_smul_subset in Breakdown.Torus.TestLift, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L91).

**Addition formula for transplanted field.** Transplanted field obeys the addition identity `transplantField μ (f + g) = transplantField μ f + transplantField μ g`. Source: Breakdown.Periodic.Internal.TestLift.transplantField_add in Breakdown.Torus.TestLift, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L101).

**Scaling formula for transplanted field.** Transplanted field obeys the scalar-scaling identity `transplantField μ (c • f) = c • transplantField μ f`. Source: Breakdown.Periodic.Internal.TestLift.transplantField_smul in Breakdown.Torus.TestLift, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L106).

**Scaling formula for complexification.** Complexification obeys the scalar-scaling identity `complexify (c • v) = c • complexify v`. Source: Breakdown.Periodic.Internal.TestLift.complexify_smul in Breakdown.Torus.TestLift, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L112).

**Scaling formula for Fourier coefficient.** Fourier coefficient obeys the scalar-scaling identity `freqTrCoef (c • f) k = c • freqTrCoef f k`. Source: Breakdown.Periodic.Internal.TestLift.freqTrCoef_smul in Breakdown.Torus.TestLift, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L116).

**Scaling for weighted Fourier coefficient.** Weighted Fourier coefficient obeys the scalar-scaling identity `weightedCoef (c • f) = c • weightedCoef f`. Source: Breakdown.Periodic.Internal.TestLift.weightedCoef_smul in Breakdown.Torus.TestLift, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L125).

**Formula for periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the exact identity `((toV f : Seq) : Lattice → Coef) = weightedCoef f`. Source: Breakdown.Periodic.Internal.TestLift.toV_coe in Breakdown.Torus.TestLift, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L131).

**Invalid Fourier data embed as zero.** If the weighted coefficients do not satisfy the square-summable solenoidal realization condition, the chosen periodic embedding returns zero. Source: Breakdown.Periodic.Internal.TestLift.toV_of_not in Breakdown.Torus.TestLift, line 137. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L137).

**Formula for periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the exact identity `(∃ hm : Memℓp (weightedCoef g) 2, (⟨weightedCoef g, hm⟩ : Seq) ∈ fieldSpace) ∧ toV g = a • toV f`. Source: Breakdown.Periodic.Internal.TestLift.toV_smul_of_eq in Breakdown.Torus.TestLift, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L143).

**Scaling for periodic Fourier embedding.** Periodic Fourier embedding obeys the scalar-scaling identity `toV (c • f) = c • toV f`. Source: Breakdown.Periodic.Internal.TestLift.toV_smul in Breakdown.Torus.TestLift, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L160).

**Source namespace:** Breakdown.Periodic.

**Lift finite-dimensional test data.** Under the stated assumptions, a finite-dimensional map with range in the span of test fields has a test-field lift with one common positive support radius. Source: Breakdown.Periodic.testLiftExists in Breakdown.Torus.TestLift, line 181. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L181).

**Lift test data to the periodic space.** Under the stated assumptions, a finite-dimensional test lift at a valid shell scale induces the linear periodic lift μ^(1/4) times the Fourier embedding of its transplant. Source: Breakdown.Periodic.torusLiftExists in Breakdown.Torus.TestLift, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TestLift.lean#L204).

### Breakdown.Torus.TimeCoef

Proves time differentiation of periodic Fourier coefficients and continuity of the weighted sequence representation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.TimeCoef.Internal.

**Nonnegative time half-space.** The half-space is the product of nonnegative time with all spatial points. Source: Breakdown.Periodic.TimeCoef.Internal.halfSpace in Breakdown.Torus.TimeCoef, line 12. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L12).

**Derivatives on the time half-space.** The nonnegative-time space-time half-space has the unique-derivative property used for differentiating smooth families at its boundary. Source: Breakdown.Periodic.TimeCoef.Internal.uniqueDiffOn_halfSpace in Breakdown.Torus.TimeCoef, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L14).

**Bound for time-dependent Fourier data.** Time-dependent Fourier coefficients satisfies the quantitative estimate `(∞ : WithTop ℕ∞) + 1 ≤ ∞`. Source: Breakdown.Periodic.TimeCoef.Internal.infty_add_one_le in Breakdown.Torus.TimeCoef, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L17).

**Compactness of unit cell.** Unit cell is compact, as asserted by `IsCompact cell`. Source: Breakdown.Periodic.TimeCoef.Internal.isCompact_cell in Breakdown.Torus.TimeCoef, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L20).

**Measurability of unit cell.** Unit cell has the measurability property `MeasurableSet cell`. Source: Breakdown.Periodic.TimeCoef.Internal.measurableSet_cell in Breakdown.Torus.TimeCoef, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L28).

**Finite measure of the unit cell.** Lebesgue measure restricted to the closed unit cell is a finite measure. Source: anonymous instance in Breakdown.Torus.TimeCoef, line 30. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L30).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character k)`. Source: Breakdown.Periodic.TimeCoef.Internal.continuous_character in Breakdown.Torus.TimeCoef, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L33).

**Norm identity for Fourier character.** Fourier character has the norm identity `‖character k x‖ = 1`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_character in Breakdown.Torus.TimeCoef, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L37).

**Norm identity for complexification.** Complexification has the norm identity `‖complexify y‖ = ‖y‖`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_complexify in Breakdown.Torus.TimeCoef, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L40).

**Bounded complexification.** Complexification is packaged as a real continuous linear map from real vectors to complex Fourier coefficients. Source: Breakdown.Periodic.TimeCoef.Internal.complexifyL in Breakdown.Torus.TimeCoef, line 43. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L43).

**Formula for bounded complexification.** Bounded complexification obeys the exact identity `complexifyL y = complexify y`. Source: Breakdown.Periodic.TimeCoef.Internal.complexifyL_apply in Breakdown.Torus.TimeCoef, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L49).

**Time derivative of complexification.** With the stated hypotheses, complexification has the one-variable derivative specified by `HasDerivAt (fun σ => complexify (f σ)) (complexify f') τ`. Source: Breakdown.Periodic.TimeCoef.Internal.hasDerivAt_complexify in Breakdown.Torus.TimeCoef, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L51).

**Continuity of integrand.** With the stated hypotheses, integrand is continuous on the domain specified by `Continuous fun x => character k x • complexify (f x)`. Source: Breakdown.Periodic.TimeCoef.Internal.continuous_integrand in Breakdown.Torus.TimeCoef, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L55).

**Bound for Fourier coefficient.** With the stated hypotheses, Fourier coefficient satisfies the quantitative estimate `‖freqTrCoef f k‖ ≤ C * volume.real cell`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_freqTrCoef_le in Breakdown.Torus.TimeCoef, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L59).

**Continuity of spatial slice.** With the stated hypotheses, spatial slice is continuous on the domain specified by `Continuous fun x => h (τ, x)`. Source: Breakdown.Periodic.TimeCoef.Internal.continuous_slice in Breakdown.Torus.TimeCoef, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L66).

**Derivative of spatial slice.** With the stated hypotheses, spatial slice has the Fréchet derivative specified by `HasFDerivAt (fun y => g (τ, y)) ((fderivWithin ℝ g halfSpace (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x`. Source: Breakdown.Periodic.TimeCoef.Internal.hasFDerivAt_slice in Breakdown.Torus.TimeCoef, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L70).

**Derivative formula for spatial slice.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (fun y => g (τ, y)) x v = fderivWithin ℝ g halfSpace (τ, x) (0, v)`. Source: Breakdown.Periodic.TimeCoef.Internal.fderiv_slice_apply in Breakdown.Torus.TimeCoef, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L80).

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (fun y => g (τ, y))`. Source: Breakdown.Periodic.TimeCoef.Internal.contDiff_slice in Breakdown.Torus.TimeCoef, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L86).

**Time derivative of relative derivative.** With the stated hypotheses, relative derivative has the one-variable derivative specified by `HasDerivAt (fun σ => g (σ, x)) (fderivWithin ℝ g halfSpace (τ, x) (1, 0)) τ`. Source: Breakdown.Periodic.TimeCoef.Internal.hasDerivAt_time in Breakdown.Torus.TimeCoef, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L92).

**Spatial derivative on the half-space.** The partial operator evaluates the derivative within the nonnegative-time half-space on a purely spatial increment. Source: Breakdown.Periodic.TimeCoef.Internal.partialOp in Breakdown.Torus.TimeCoef, line 104. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L104).

**Smoothness of spatial slice derivative.** With the stated hypotheses, spatial slice derivative has the asserted differentiability order in `ContDiffOn ℝ ∞ (partialOp v h) halfSpace`. Source: Breakdown.Periodic.TimeCoef.Internal.contDiffOn_partialOp in Breakdown.Torus.TimeCoef, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L107).

**Differentiation preserves periodicity.** Every fixed-direction spatial derivative of a periodic field is periodic in the source’s total-derivative convention. Source: Breakdown.Periodic.TimeCoef.Internal.isPeriodic_fderiv in Breakdown.Torus.TimeCoef, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L111).

**Formula for spatial slice.** With the stated hypotheses, spatial slice obeys the exact identity `(fun x => partialOp v h (τ, x)) = fun x => fderiv ℝ (fun y => h (τ, y)) x v`. Source: Breakdown.Periodic.TimeCoef.Internal.slice_partialOp in Breakdown.Torus.TimeCoef, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L118).

**Smooth family of periodic slices.** The slice predicate requires a smooth space-time family whose spatial slices are periodic for every nonnegative time. Source: Breakdown.Periodic.TimeCoef.Internal.SmoothPeriodicSlices in Breakdown.Torus.TimeCoef, line 123. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L123).

**Spatial differentiation keeps the class.** A spatial directional derivative of a smooth family of periodic slices is again a smooth family of periodic slices. Source: Breakdown.Periodic.TimeCoef.Internal.smoothPeriodicSlices_partialOp in Breakdown.Torus.TimeCoef, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L126).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (fun x => partialOp (unitVector i) h (τ, x)) k = (2 * π * Complex.I * (k i : ℂ)) • freqTrCoef (fun x => h (τ, x)) k`. Source: Breakdown.Periodic.TimeCoef.Internal.freqTrCoef_partialOp in Breakdown.Torus.TimeCoef, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L132).

**Repeated spatial differentiation.** Every iterate of a fixed spatial directional derivative preserves the smooth-periodic-slice class. Source: Breakdown.Periodic.TimeCoef.Internal.smoothPeriodicSlices_iterate in Breakdown.Torus.TimeCoef, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L139).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (fun x => (partialOp (unitVector i))^[n] h (τ, x)) k = (2 * π * Complex.I * (k i : ℂ)) ^ n • freqTrCoef (fun x => h (τ, x)) k`. Source: Breakdown.Periodic.TimeCoef.Internal.freqTrCoef_iterate in Breakdown.Torus.TimeCoef, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L147).

**Uniform bound for Fourier coefficient.** With the stated hypotheses, Fourier coefficient admits the uniform bound stated in `∃ C, ∀ τ ∈ Icc 0 T, ∀ k, ‖freqTrCoef (fun x => h (τ, x)) k‖ ≤ C`. Source: Breakdown.Periodic.TimeCoef.Internal.exists_bound_freqTrCoef in Breakdown.Torus.TimeCoef, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L157).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_freq_sq in Breakdown.Torus.TimeCoef, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L164).

**Norm for derivative multiplier norm.** Derivative multiplier norm has the norm identity `‖(2 * π * Complex.I * (n : ℂ))‖ = 2 * π * |(n : ℝ)|`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_two_pi_I_mul in Breakdown.Torus.TimeCoef, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L169).

**Product frequency-decay weight.** The decay weight is the product of `(1+kᵢ²)⁻¹` over the three integer coordinates. Source: Breakdown.Periodic.TimeCoef.Internal.decayBound in Breakdown.Torus.TimeCoef, line 172. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L172).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `weight k ^ 2 ≤ 6 * (1 + ∑ i, (2 * π * |(k i : ℝ)|) ^ 4)`. Source: Breakdown.Periodic.TimeCoef.Internal.weight_sq_le in Breakdown.Torus.TimeCoef, line 175. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L175).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `1 ≤ weight k`. Source: Breakdown.Periodic.TimeCoef.Internal.one_le_weight in Breakdown.Torus.TimeCoef, line 193. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L193).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `(1 + ((k 0 : ℝ)) ^ 2) * ((1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2)) ≤ weight k ^ 3`. Source: Breakdown.Periodic.TimeCoef.Internal.prod_le_weight_cube in Breakdown.Torus.TimeCoef, line 198. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L198).

**Bound for Sobolev weight.** With the stated hypotheses, Sobolev weight satisfies the quantitative estimate `weight k * ‖c‖ ^ 2 ≤ 36 * A ^ 2 * decayBound k`. Source: Breakdown.Periodic.TimeCoef.Internal.weight_mul_sq_le in Breakdown.Torus.TimeCoef, line 214. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L214).

**Uniform Fourier decay on a time slab.** A smooth family of periodic slices has one constant controlling its weighted squared Fourier coefficients by the fixed summable decay weight throughout [0,T]. Source: Breakdown.Periodic.TimeCoef.Internal.exists_decay in Breakdown.Torus.TimeCoef, line 238. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L238).

**Summable reciprocal quadratic weights.** The integer sequence given by the reciprocal of one plus the squared integer is summable. Source: Breakdown.Periodic.TimeCoef.Internal.summable_inv_one_add_sq in Breakdown.Torus.TimeCoef, line 252. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L252).

**Three integer frequency coordinates.** The lattice equivalence identifies a frequency with the ordered triple of its integer coordinates. Source: Breakdown.Periodic.TimeCoef.Internal.tripleEquiv in Breakdown.Torus.TimeCoef, line 259. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L259).

**Summability of summable frequency weight.** Summable frequency weight satisfies the series-convergence assertion `Summable decayBound`. Source: Breakdown.Periodic.TimeCoef.Internal.summable_decayBound in Breakdown.Torus.TimeCoef, line 265. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L265).

**A relative time neighborhood.** The interval in the statement is a neighborhood within the nonnegative time half-line, including the vacuous relative-neighborhood case when the base point lies outside that half-line. Source: Breakdown.Periodic.TimeCoef.Internal.Icc_mem_nhdsWithin_Ici_zero in Breakdown.Torus.TimeCoef, line 271. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L271).

**Continuity of Fourier coefficient.** With the stated hypotheses, Fourier coefficient is continuous on the domain specified by `ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Icc 0 T)`. Source: Breakdown.Periodic.TimeCoef.Internal.continuousOn_freqTrCoef_Icc in Breakdown.Torus.TimeCoef, line 275. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L275).

**Continuity of Fourier coefficient.** With the stated hypotheses, Fourier coefficient is continuous on the domain specified by `ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Ici 0)`. Source: Breakdown.Periodic.TimeCoef.Internal.continuousOn_freqTrCoef in Breakdown.Torus.TimeCoef, line 291. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L291).

**Time derivative of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the one-variable derivative specified by `HasDerivAt (fun τ => freqTrCoef (fun x => g (τ, x)) k) (freqTrCoef (fun x => deriv (fun τ => g (τ, x)) t) k) t`. Source: Breakdown.Periodic.TimeCoef.Internal.hasDerivAt_freqTrCoef in Breakdown.Torus.TimeCoef, line 297. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L297).

**Norm identity for Fourier sequence.** Fourier sequence has the norm identity `‖a‖ ^ 2 = ∑' k, ‖a k‖ ^ 2`. Source: Breakdown.Periodic.TimeCoef.Internal.seq_norm_sq in Breakdown.Torus.TimeCoef, line 331. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L331).

**Formula for periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the exact identity `((toV f : V) : Seq) k = Real.sqrt (weight k) • freqTrCoef f k`. Source: Breakdown.Periodic.TimeCoef.Internal.toV_apply in Breakdown.Torus.TimeCoef, line 335. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L335).

**Scaling formula for Sobolev weight.** Sobolev weight obeys the scalar-scaling identity `‖Real.sqrt (weight k) • c‖ ^ 2 = weight k * ‖c‖ ^ 2`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_sq_sqrt_weight_smul in Breakdown.Torus.TimeCoef, line 343. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L343).

**Bound for time-dependent Fourier data.** Time-dependent Fourier coefficients satisfies the quantitative estimate `‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. Source: Breakdown.Periodic.TimeCoef.Internal.norm_sub_sq_le in Breakdown.Torus.TimeCoef, line 348. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L348).

**Source namespace:** Breakdown.Periodic.

**Time differentiation of coefficients.** Under the stated assumptions, a smooth family of periodic fields has Fourier coefficients continuous up to time zero and differentiable by differentiating the field at positive times. Source: Breakdown.Periodic.coefTimeDeriv in Breakdown.Torus.TimeCoef, line 358. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L358).

**Continuity of periodic embedding.** Under the stated assumptions, the periodic Fourier embedding of a smooth divergence-free periodic family is continuous for nonnegative time. Source: Breakdown.Periodic.toVContinuous in Breakdown.Torus.TimeCoef, line 364. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TimeCoef.lean#L364).

### Breakdown.Torus.ToVLinear

Checks addition and scalar multiplication for the map from smooth periodic solenoidal fields into Fourier space.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.ToVLinear.Internal.

**Addition formula for complexification.** Complexification obeys the addition identity `complexify (a + b) = complexify a + complexify b`. Source: Breakdown.Periodic.ToVLinear.Internal.complexify_add in Breakdown.Torus.ToVLinear, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L15).

**Scaling formula for complexification.** Complexification obeys the scalar-scaling identity `complexify (c • a) = c • complexify a`. Source: Breakdown.Periodic.ToVLinear.Internal.complexify_smul in Breakdown.Torus.ToVLinear, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L19).

**Addition formula for Fourier coefficient.** With the stated hypotheses, Fourier coefficient obeys the addition identity `freqTrCoef (f + g) k = freqTrCoef f k + freqTrCoef g k`. Source: Breakdown.Periodic.ToVLinear.Internal.freqTrCoef_add in Breakdown.Torus.ToVLinear, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L23).

**Scaling formula for Fourier coefficient.** Fourier coefficient obeys the scalar-scaling identity `freqTrCoef (c • f) k = c • freqTrCoef f k`. Source: Breakdown.Periodic.ToVLinear.Internal.freqTrCoef_smul in Breakdown.Torus.ToVLinear, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L32).

**Addition formula for Fourier coefficient.** Fourier coefficient obeys the addition identity `coeff (u + v) k = coeff u k + coeff v k`. Source: Breakdown.Periodic.ToVLinear.Internal.coeff_add in Breakdown.Torus.ToVLinear, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L40).

**Scaling formula for Fourier coefficient.** Fourier coefficient obeys the scalar-scaling identity `coeff (c • u) k = c • coeff u k`. Source: Breakdown.Periodic.ToVLinear.Internal.coeff_smul in Breakdown.Torus.ToVLinear, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L43).

**Sums preserve periodicity.** The sum of two unit-periodic spatial fields is unit-periodic. Source: Breakdown.Periodic.ToVLinear.Internal.isPeriodic_add in Breakdown.Torus.ToVLinear, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L46).

**Scalar multiples preserve periodicity.** Every real scalar multiple of a unit-periodic spatial field is unit-periodic. Source: Breakdown.Periodic.ToVLinear.Internal.isPeriodic_smul in Breakdown.Torus.ToVLinear, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L51).

**Addition formula for divergence.** With the stated hypotheses, divergence obeys the addition identity `divergenceAt (f + g) x = divergenceAt f x + divergenceAt g x`. Source: Breakdown.Periodic.ToVLinear.Internal.divergenceAt_add in Breakdown.Torus.ToVLinear, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L55).

**Scaling formula for divergence.** Divergence obeys the scalar-scaling identity `divergenceAt (c • f) x = c * divergenceAt f x`. Source: Breakdown.Periodic.ToVLinear.Internal.divergenceAt_smul in Breakdown.Torus.ToVLinear, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L60).

**Source namespace:** Breakdown.Periodic.

**Scaling for periodic Fourier embedding.** With the stated hypotheses, periodic Fourier embedding obeys the scalar-scaling identity `toV (c • f) = c • toV f`. Source: Breakdown.Periodic.toV_smul in Breakdown.Torus.ToVLinear, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L68).

**Additivity of periodic embedding.** Under the stated assumptions, the periodic Fourier embedding is additive on smooth periodic divergence-free fields. Source: Breakdown.Periodic.toVAdd in Breakdown.Torus.ToVLinear, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/ToVLinear.lean#L76).

### Breakdown.Torus.TorusSeries

Constructs periodic Fourier series as L² or L⁶ sums and establishes their norm and linearity estimates.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.

**The admissible L⁶ exponent.** The L⁶ exponent satisfies the lower bound of one required by the periodic series construction. Source: Breakdown.Periodic.factOneLeSixLattice in Breakdown.Torus.TorusSeries, line 13. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L13).

**Choose an Lᵖ representative.** The construction returns the Lᵖ class when the function belongs to Lᵖ and returns zero otherwise. Source: Breakdown.Periodic.lpOrZero in Breakdown.Torus.TorusSeries, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L16).

**Periodic Fourier series in Lᵖ.** The periodic series is the infinite Lᵖ sum of the inverse Fourier characters multiplied by their coefficients. Source: Breakdown.Periodic.torusSeries in Breakdown.Torus.TorusSeries, line 19. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L19).

**Fourier coefficient of a derivative.** The gradient coefficient multiplies the field coefficient by `2πi kⱼ`. Source: Breakdown.Periodic.gradCoef in Breakdown.Torus.TorusSeries, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L22).

**Source namespace:** Breakdown.Periodic.TorusSeries.Internal.

**Finite measure of the unit cell.** Lebesgue measure restricted to the unit cell is a finite measure. Source: Breakdown.Periodic.TorusSeries.Internal.finite_cell in Breakdown.Torus.TorusSeries, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L26).

**Continuous cell fields lie in every Lᵖ.** A continuous complex vector field belongs to every Lᵖ space on the compact unit cell, including the infinite exponent. Source: Breakdown.Periodic.TorusSeries.Internal.memLp_of_continuous in Breakdown.Torus.TorusSeries, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L29).

**One Fourier-series term.** One Fourier-series term is the inverse Fourier character multiplied by its coefficient. Source: Breakdown.Periodic.TorusSeries.Internal.term in Breakdown.Torus.TorusSeries, line 36. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L36).

**Continuity of Fourier summand.** Fourier summand is continuous on the domain specified by `Continuous (term c k)`. Source: Breakdown.Periodic.TorusSeries.Internal.continuous_term in Breakdown.Torus.TorusSeries, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L38).

**Formula for Lᵖ representative.** Lᵖ representative obeys the exact identity `lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k) = (memLp_of_continuous p (continuous_term c k)).toLp (term c k)`. Source: Breakdown.Periodic.TorusSeries.Internal.lpOrZero_term in Breakdown.Torus.TorusSeries, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L41).

**Finite Fourier-series sum.** A partial sum adds the Fourier terms over the specified finite set of lattice frequencies. Source: Breakdown.Periodic.TorusSeries.Internal.partialSum in Breakdown.Torus.TorusSeries, line 50. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L50).

**Continuity of finite Fourier sum.** Finite Fourier sum is continuous on the domain specified by `Continuous (partialSum c s)`. Source: Breakdown.Periodic.TorusSeries.Internal.continuous_partialSum in Breakdown.Torus.TorusSeries, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L53).

**Formula for Lᵖ representative.** Lᵖ representative obeys the exact identity `∑ k ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k) = (memLp_of_continuous p (continuous_partialSum c s)).toLp (partialSum c s)`. Source: Breakdown.Periodic.TorusSeries.Internal.sum_lpOrZero in Breakdown.Torus.TorusSeries, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L58).

**Sum formula for Lᵖ representative.** With the stated hypotheses, Lᵖ representative obeys the summation identity `‖∑ k ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)‖ = (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ p.toReal) ^ p.toReal⁻¹`. Source: Breakdown.Periodic.TorusSeries.Internal.norm_sum_lpOrZero in Breakdown.Torus.TorusSeries, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L70).

**Sum formula for Fourier character.** Fourier character obeys the summation identity `‖∑ k ∈ s, lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • c k)‖ = √(∑ k ∈ s, ‖c k‖ ^ 2)`. Source: Breakdown.Periodic.TorusSeries.Internal.norm_sum_two in Breakdown.Torus.TorusSeries, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L79).

**Bound for Fourier character.** With the stated hypotheses, Fourier character satisfies the quantitative estimate `‖∑ k ∈ s, lpOrZero 6 (volume.restrict cell) (fun x => character (-k) x • c k)‖ ≤ C * √(∑ k ∈ s, weight k * ‖c k‖ ^ 2)`. Source: Breakdown.Periodic.TorusSeries.Internal.norm_sum_six_le in Breakdown.Torus.TorusSeries, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L86).

**Summability of periodic Fourier series.** With the stated hypotheses, periodic Fourier series satisfies the series-convergence assertion `Summable L`. Source: Breakdown.Periodic.TorusSeries.Internal.summable_of_bound in Breakdown.Torus.TorusSeries, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L95).

**Bound for periodic Fourier series.** With the stated hypotheses, periodic Fourier series satisfies the quantitative estimate `‖∑' k, L k‖ ≤ C * √(∑' k, g k)`. Source: Breakdown.Periodic.TorusSeries.Internal.norm_tsum_le_of_bound in Breakdown.Torus.TorusSeries, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L117).

**Summability of Fourier character.** With the stated hypotheses, Fourier character satisfies the series-convergence assertion `Summable (fun k => lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • c k))`. Source: Breakdown.Periodic.TorusSeries.Internal.summable_two in Breakdown.Torus.TorusSeries, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L124).

**Summability of Fourier character.** With the stated hypotheses, Fourier character satisfies the series-convergence assertion `Summable (fun k => lpOrZero 6 (volume.restrict cell) (fun x => character (-k) x • c k))`. Source: Breakdown.Periodic.TorusSeries.Internal.summable_six in Breakdown.Torus.TorusSeries, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L129).

**Summability of Fourier coefficient.** Fourier coefficient satisfies the series-convergence assertion `Summable fun k => ‖coeff z k‖ ^ 2`. Source: Breakdown.Periodic.TorusSeries.Internal.summable_coeff_sq in Breakdown.Torus.TorusSeries, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L135).

**Bound for gradient coefficient.** Gradient coefficient satisfies the quantitative estimate `‖gradCoef j z k‖ ^ 2 ≤ weight k * ‖coeff z k‖ ^ 2`. Source: Breakdown.Periodic.TorusSeries.Internal.norm_gradCoef_sq_le in Breakdown.Torus.TorusSeries, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L140).

**Source namespace:** Breakdown.Periodic.

**Summability of periodic Fourier series.** With the stated hypotheses, periodic Fourier series satisfies the series-convergence assertion `Summable (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • coeff z k))`. Source: Breakdown.Periodic.summable_torusSeries in Breakdown.Torus.TorusSeries, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L160).

**Summability of periodic Fourier series.** Periodic Fourier series satisfies the series-convergence assertion `Summable (fun k => lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • gradCoef j z k))`. Source: Breakdown.Periodic.summable_torusSeries_grad in Breakdown.Torus.TorusSeries, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L166).

**Norm for periodic Fourier series.** With the stated hypotheses, periodic Fourier series has the norm identity `‖torusSeries 2 c‖ ^ 2 = ∑' k, ‖c k‖ ^ 2`. Source: Breakdown.Periodic.torusSeries_norm_sq in Breakdown.Torus.TorusSeries, line 171. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L171).

**Addition for periodic Fourier series.** With the stated hypotheses, periodic Fourier series obeys the addition identity `torusSeries p (c + d) = torusSeries p c + torusSeries p d`. Source: Breakdown.Periodic.torusSeries_add in Breakdown.Torus.TorusSeries, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L183).

**Scaling for periodic Fourier series.** Periodic Fourier series obeys the scalar-scaling identity `torusSeries p (r • c) = r • torusSeries p c`. Source: Breakdown.Periodic.torusSeries_smul in Breakdown.Torus.TorusSeries, line 194. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L194).

**Uniform bound for Fourier series.** Periodic Fourier series admits the uniform bound stated in `∃ C : ℝ, 0 ≤ C ∧ ∀ z : V, ‖torusSeries 6 (coeff z)‖ ≤ C * ‖z‖`. Source: Breakdown.Periodic.torusSeries_six_bound in Breakdown.Torus.TorusSeries, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeries.lean#L205).

### Breakdown.Torus.TorusSeriesSmooth

Identifies the Lᵖ series representatives of a smooth field and its first spatial derivatives.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.TorusSeriesSmooth.Internal.

**Finite measure of the unit cell.** Lebesgue measure restricted to the closed unit cell is a finite measure. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.finiteCell in Breakdown.Torus.TorusSeriesSmooth, line 14. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L14).

**Continuity of Fourier summand.** Fourier summand is continuous on the domain specified by `Continuous (fun x => character (-k) x • c)`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.continuous_term in Breakdown.Torus.TorusSeriesSmooth, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L17).

**Norm identity for Fourier summand.** Fourier summand has the norm identity `‖character (-k) x • c‖ = ‖c‖`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.norm_term in Breakdown.Torus.TorusSeriesSmooth, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L20).

**A bounded Fourier-series term.** One Fourier term is packaged as a bounded continuous function with bound equal to the coefficient norm. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.termBCF in Breakdown.Torus.TorusSeriesSmooth, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L23).

**Bound for bounded Fourier summand.** Bounded Fourier summand satisfies the quantitative estimate `‖termBCF c k‖ ≤ ‖c‖`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.norm_termBCF_le in Breakdown.Torus.TorusSeriesSmooth, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L27).

**Formula for Lᵖ representative.** Lᵖ representative obeys the exact identity `lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c) = BoundedContinuousFunction.toLp (E := Coef) p (volume.restrict cell) ℝ (termBCF c k)`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.lpOrZero_term in Breakdown.Torus.TorusSeriesSmooth, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L30).

**Representative of Fourier series.** With the stated hypotheses, periodic Fourier series has the almost-everywhere representation `(torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell] (fun x => complexify (g x))`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.series_ae in Breakdown.Torus.TorusSeriesSmooth, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L41).

**Representative of Fourier transform.** With the stated hypotheses, Fourier transform has the almost-everywhere representation `(torusSeries p (freqTrCoef f) : Space → Coef) =ᵐ[volume.restrict cell] (fun x => complexify (f x))`. Source: Breakdown.Periodic.TorusSeriesSmooth.Internal.freqTr_ae in Breakdown.Torus.TorusSeriesSmooth, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L63).

**Source namespace:** Breakdown.Periodic.

**Smooth Fourier representatives.** Under the stated assumptions, the periodic velocity and its derivatives agree almost everywhere with the smooth field and its complexified derivatives in the required L² and L⁶ spaces. Source: Breakdown.Periodic.torusSeriesSmooth in Breakdown.Torus.TorusSeriesSmooth, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TorusSeriesSmooth.lean#L73).

### Breakdown.Torus.Transplant

Localizes a compact field inside the unit cell, periodizes it and computes its L² and gradient energies after rescaling.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Transplant.Internal.

**Affine rescaling before periodization.** The transplanted profile evaluates the field at `(y−center)/√μ` and multiplies it by `μ^(−1/2)`. Source: Breakdown.Periodic.Transplant.Internal.profile in Breakdown.Torus.Transplant, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L15).

**Formula for cell center.** Cell center obeys the exact identity `center j = 1 / 2`. Source: Breakdown.Periodic.Transplant.Internal.center_apply in Breakdown.Torus.Transplant, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L18).

**Formula for coordinate unit vector.** Coordinate unit vector obeys the exact identity `unitVector i j = if j = i then 1 else 0`. Source: Breakdown.Periodic.Transplant.Internal.unitVector_apply in Breakdown.Torus.Transplant, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L21).

**Formula for periodic wrapping.** Periodic wrapping obeys the exact identity `wrap x j = x j - round (x j - 1 / 2)`. Source: Breakdown.Periodic.Transplant.Internal.wrap_apply in Breakdown.Torus.Transplant, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L24).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `(freq n) j = (n j : ℝ)`. Source: Breakdown.Periodic.Transplant.Internal.freq_apply' in Breakdown.Torus.Transplant, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L27).

**Formula for transplanted test field.** With the stated hypotheses, transplanted test field obeys the exact identity `d = e`. Source: Breakdown.Periodic.Transplant.Internal.int_eq_of_abs_lt in Breakdown.Torus.Transplant, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L30).

**Bound for transplanted test field.** Transplanted test field satisfies the quantitative estimate `|v j| ≤ ‖v‖`. Source: Breakdown.Periodic.Transplant.Internal.abs_apply_le in Breakdown.Torus.Transplant, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L35).

**Support stays near the center.** At a valid shell scale, a point whose inverse-rescaled position lies in the test-field support differs from 1/2 by at most 1/8 in each coordinate. Source: Breakdown.Periodic.Transplant.Internal.coord_near_tsupport in Breakdown.Torus.Transplant, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L41).

**Bound for coordinate.** With the stated hypotheses, coordinate satisfies the estimate `|v j - 1 / 2| ≤ 1 / 8`. Source: Breakdown.Periodic.Transplant.Internal.coord_near in Breakdown.Torus.Transplant, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L53).

**Formula for transplantation.** With the stated hypotheses, transplantation obeys the exact identity `transplantField μ g y = profile μ g (y - freq n)`. Source: Breakdown.Periodic.Transplant.Internal.transplant_eq in Breakdown.Torus.Transplant, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L57).

**Smoothness of profile.** With the stated hypotheses, profile has the asserted differentiability order in `ContDiff ℝ ∞ (profile μ g)`. Source: Breakdown.Periodic.Transplant.Internal.contDiff_profile in Breakdown.Torus.Transplant, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L86).

**Derivative of profile.** With the stated hypotheses, profile has the Fréchet derivative specified by `HasFDerivAt (profile μ g) ((Real.sqrt μ)⁻¹ • ((fderiv ℝ g ((Real.sqrt μ)⁻¹ • (y - center))).comp ((Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ Space))) y`. Source: Breakdown.Periodic.Transplant.Internal.hasFDerivAt_profile in Breakdown.Torus.Transplant, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L89).

**Derivative formula for profile.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (profile μ g) y v = ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹) • fderiv ℝ g ((Real.sqrt μ)⁻¹ • (y - center)) v`. Source: Breakdown.Periodic.Transplant.Internal.fderiv_profile_apply in Breakdown.Torus.Transplant, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L97).

**Formula for divergence.** With the stated hypotheses, divergence obeys the exact identity `∑ i : Fin 3, (fderiv ℝ (profile μ g) y (unitVector i)) i = 0`. Source: Breakdown.Periodic.Transplant.Internal.divergence_profile in Breakdown.Torus.Transplant, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L103).

**A transplant is locally one translate.** At a valid shell scale, the periodic transplant agrees near each point with the rescaled profile shifted by the integer vector selected at that point. Source: Breakdown.Periodic.Transplant.Internal.transplant_eventually in Breakdown.Torus.Transplant, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L109).

**Formula for periodic wrapping.** Periodic wrapping obeys the exact identity `wrap (x + unitVector i) = wrap x`. Source: Breakdown.Periodic.Transplant.Internal.wrap_add_unitVector in Breakdown.Torus.Transplant, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L122).

**Sum of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the exact series sum in `HasSum (fun k => ‖freqTrCoef G k‖ ^ 2) (∫ x in cell, ‖G x‖ ^ 2)`. Source: Breakdown.Periodic.Transplant.Internal.hasSum_sq_freqTrCoef in Breakdown.Torus.Transplant, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L167).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2`. Source: Breakdown.Periodic.Transplant.Internal.norm_freq_sq' in Breakdown.Torus.Transplant, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L205).

**Sum of Sobolev weight.** With the stated hypotheses, Sobolev weight has the exact series sum in `HasSum (fun k => weight k * ‖freqTrCoef F k‖ ^ 2) ((∫ x in cell, ‖F x‖ ^ 2) + ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ F x (unitVector i)‖ ^ 2)`. Source: Breakdown.Periodic.Transplant.Internal.hasSum_weight in Breakdown.Torus.Transplant, line 209. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L209).

**The periodic H¹ norm formula.** For the stated smooth periodic divergence-free field the squared periodic Fourier norm equals its cell L² mass plus the sum of the cell L² masses of its three coordinate derivatives. Source: Breakdown.Periodic.Transplant.Internal.norm_toV_sq in Breakdown.Torus.Transplant, line 230. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L230).

**The Jacobian of the transplant scale.** The stated integral change of variables for `x ↦ μ⁻¹ᐟ²(x−center)` contributes the volume factor `(√μ)³`. Source: Breakdown.Periodic.Transplant.Internal.integral_rescale in Breakdown.Torus.Transplant, line 237. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L237).

**Leaving the cell moves a coordinate.** A point outside the unit cell has at least one coordinate at distance greater than 1/2 from the cell-center coordinate. Source: Breakdown.Periodic.Transplant.Internal.coord_far in Breakdown.Torus.Transplant, line 244. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L244).

**Formula for profile.** With the stated hypotheses, profile obeys the exact identity `profile μ g x = 0`. Source: Breakdown.Periodic.Transplant.Internal.profile_off in Breakdown.Torus.Transplant, line 254. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L254).

**Derivative formula for profile.** With the stated hypotheses, the derivative calculation gives `fderiv ℝ (profile μ g) x v = 0`. Source: Breakdown.Periodic.Transplant.Internal.fderiv_profile_off in Breakdown.Torus.Transplant, line 260. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L260).

**Value at zero for lattice frequency.** Lattice frequency has the zero-parameter identity `freq 0 = 0`. Source: Breakdown.Periodic.Transplant.Internal.freq_zero in Breakdown.Torus.Transplant, line 271. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L271).

**The transplant matches inside the cell.** At a valid shell scale, the periodic transplant agrees locally with the rescaled profile around every point in the closed unit cell. Source: Breakdown.Periodic.Transplant.Internal.eventually_cell in Breakdown.Torus.Transplant, line 273. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L273).

**Measurability of unit cell.** Unit cell has the measurability property `MeasurableSet cell`. Source: Breakdown.Periodic.Transplant.Internal.measurableSet_cell in Breakdown.Torus.Transplant, line 286. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L286).

**Mass under transplantation.** The cell L² mass of a valid transplanted test field is its whole-space L² mass multiplied by `√μ`. Source: Breakdown.Periodic.Transplant.Internal.integral_value in Breakdown.Torus.Transplant, line 289. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L289).

**Gradient energy under transplantation.** The cell gradient energy of a valid transplanted test field is its whole-space gradient energy multiplied by `μ⁻¹ᐟ²`. Source: Breakdown.Periodic.Transplant.Internal.integral_deriv in Breakdown.Torus.Transplant, line 301. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Transplant.lean#L301).

### Breakdown.Torus.TrigHs

Derives the periodic Sobolev estimate for trigonometric polynomials by applying a whole-space cutoff.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.TrigHs.Internal.

**A coordinate cube.** The coordinate box consists of points whose three coordinates all lie in `[a,b]`. Source: Breakdown.Periodic.TrigHs.Internal.box in Breakdown.Torus.TrigHs, line 11. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L11).

**Finite trigonometric polynomial.** The trigonometric polynomial is the sum of inverse Fourier characters times their vector coefficients over a finite frequency set. Source: Breakdown.Periodic.TrigHs.Internal.trig in Breakdown.Torus.TrigHs, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L13).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k i = k i`. Source: Breakdown.Periodic.TrigHs.Internal.freq_apply in Breakdown.Torus.TrigHs, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L16).

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i`. Source: Breakdown.Periodic.TrigHs.Internal.inner_freq in Breakdown.Torus.TrigHs, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L19).

**Sign formula for Fourier character.** Fourier character obeys the sign-change identity `character (-k) x = Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ))`. Source: Breakdown.Periodic.TrigHs.Internal.character_neg in Breakdown.Torus.TrigHs, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L22).

**Formula for Fourier character.** Fourier character obeys the exact identity `character (-k) x = ∏ i, Complex.exp (2 * π * Complex.I * (((k i : ℝ) * x i : ℝ) : ℂ))`. Source: Breakdown.Periodic.TrigHs.Internal.character_neg_eq_prod in Breakdown.Torus.TrigHs, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L27).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character (-k))`. Source: Breakdown.Periodic.TrigHs.Internal.continuous_character_neg in Breakdown.Torus.TrigHs, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L34).

**Formula for coordinate box.** Coordinate box obeys the exact identity `box a b = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' (Set.univ.pi fun _ => Icc a b)`. Source: Breakdown.Periodic.TrigHs.Internal.box_eq in Breakdown.Torus.TrigHs, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L40).

**Compactness of coordinate box.** Coordinate box is compact, as asserted by `IsCompact (box a b)`. Source: Breakdown.Periodic.TrigHs.Internal.isCompact_box in Breakdown.Torus.TrigHs, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L46).

**Separate a coordinate product integral.** The integral of a product of three separate coordinate functions over a coordinate box equals the product of their one-dimensional integrals. Source: Breakdown.Periodic.TrigHs.Internal.setIntegral_box_prod in Breakdown.Torus.TrigHs, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L57).

**Integrate a character over whole periods.** A scalar Fourier character integrated over an interval of natural-number length L gives L at zero integer frequency and zero at every nonzero integer frequency. Source: Breakdown.Periodic.TrigHs.Internal.integral_exp_Icc in Breakdown.Torus.TrigHs, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L64).

**Character integrals on integer cubes.** A lattice Fourier character integrates to the cube volume at zero frequency and to zero at nonzero frequency on a cube of natural-number side length. Source: Breakdown.Periodic.TrigHs.Internal.setIntegral_box_character in Breakdown.Torus.TrigHs, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L89).

**Formula for complex conjugation.** Complex conjugation obeys the exact identity `(starRingEnd ℂ) (character (-j) x) * character (-k) x = character (-(k - j)) x`. Source: Breakdown.Periodic.TrigHs.Internal.conj_character_mul in Breakdown.Torus.TrigHs, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L103).

**Coefficient formula for inner product.** The Fourier-coefficient calculation gives `inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ)`. Source: Breakdown.Periodic.TrigHs.Internal.inner_self_coef in Breakdown.Torus.TrigHs, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L114).

**Integrability of Fourier character.** Fourier character satisfies the integrability assertion `IntegrableOn (character (-n)) (box a b)`. Source: Breakdown.Periodic.TrigHs.Internal.integrableOn_character in Breakdown.Torus.TrigHs, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L118).

**Parseval on an integer-sided cube.** The squared L² norm of a finite trigonometric polynomial on a cube of natural-number side length L is L³ times the sum of the squared coefficient norms. Source: Breakdown.Periodic.TrigHs.Internal.integral_norm_sq_trig in Breakdown.Torus.TrigHs, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L121).

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ (freq k) (unitVector i) = k i`. Source: Breakdown.Periodic.TrigHs.Internal.inner_freq_unitVector in Breakdown.Torus.TrigHs, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L146).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.TrigHs.Internal.norm_freq_sq in Breakdown.Torus.TrigHs, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L150).

**Derivative of Fourier character.** Fourier character has the Fréchet derivative specified by `HasFDerivAt (character (-k)) (Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) • ((2 * π * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ (freq k))))) x`. Source: Breakdown.Periodic.TrigHs.Internal.hasFDerivAt_character_neg in Breakdown.Torus.TrigHs, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L154).

**Formula for trigonometric polynomial.** Trigonometric polynomial obeys the exact identity `trig s c = fun x => ∑ k ∈ s, Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) • c k`. Source: Breakdown.Periodic.TrigHs.Internal.trig_eq in Breakdown.Torus.TrigHs, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L167).

**Smoothness of trigonometric polynomial.** Trigonometric polynomial has the asserted differentiability order in `ContDiff ℝ 1 (trig s c)`. Source: Breakdown.Periodic.TrigHs.Internal.contDiff_trig in Breakdown.Torus.TrigHs, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L172).

**Derivative for trigonometric polynomial.** The derivative calculation gives `fderiv ℝ (trig s c) x (unitVector i) = trig s (fun k => (2 * π * Complex.I * (k i : ℂ)) • c k) x`. Source: Breakdown.Periodic.TrigHs.Internal.fderiv_trig_apply in Breakdown.Torus.TrigHs, line 180. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L180).

**Sum formula for coordinate unit vector.** Coordinate unit vector obeys the summation identity `v = ∑ i, v i • unitVector i`. Source: Breakdown.Periodic.TrigHs.Internal.eq_sum_unitVector in Breakdown.Torus.TrigHs, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L197).

**Norm identity for coordinate unit vector.** Coordinate unit vector has the norm identity `‖unitVector i‖ = 1`. Source: Breakdown.Periodic.TrigHs.Internal.norm_unitVector in Breakdown.Torus.TrigHs, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L201).

**Bound for operator norm.** Operator norm satisfies the quantitative estimate `‖T‖ ≤ ∑ i, ‖T (unitVector i)‖`. Source: Breakdown.Periodic.TrigHs.Internal.opNorm_le_sum in Breakdown.Torus.TrigHs, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L204).

**A uniform norm bound inside the cell.** Every point of the unit cell has Euclidean norm at most three. Source: Breakdown.Periodic.TrigHs.Internal.norm_le_of_mem_cell in Breakdown.Torus.TrigHs, line 216. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L216).

**A norm ball fits inside a coordinate box.** Every point of norm at most four lies in the coordinate box from −4 to 4. Source: Breakdown.Periodic.TrigHs.Internal.mem_box_of_norm_le in Breakdown.Torus.TrigHs, line 225. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L225).

**Cutoff for the periodic Sobolev bound.** The auxiliary Sobolev cutoff equals one on the ball of radius three and vanishes beyond radius four. Source: Breakdown.Periodic.TrigHs.Internal.cutoff in Breakdown.Torus.TrigHs, line 232. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L232).

**Bound for smooth cutoff.** With the stated hypotheses, smooth cutoff satisfies the quantitative estimate `‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖ ^ 2 ≤ (6 + 18 * M ^ 2) * (‖trig s c x‖ ^ 2 + ∑ i, ‖trig s (fun k => (2 * π * Complex.I * (k i : ℂ)) • c k) x‖ ^ 2)`. Source: Breakdown.Periodic.TrigHs.Internal.norm_fderiv_cutoff_sq_le in Breakdown.Torus.TrigHs, line 234. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L234).

**Gradient energy after a smooth cutoff.** A cutoff with derivative norm at most M gives gradient energy at most `(6+18M²)8³` times the weighted squared coefficient sum of the trigonometric polynomial. Source: Breakdown.Periodic.TrigHs.Internal.integral_fderiv_cutoff_sq_le in Breakdown.Torus.TrigHs, line 280. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L280).

**The Sobolev cutoff preserves cell values.** The sixth-power cell integral of a trigonometric polynomial equals that of the polynomial multiplied by the chosen cutoff. Source: Breakdown.Periodic.TrigHs.Internal.setIntegral_cell_eq in Breakdown.Torus.TrigHs, line 322. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/TrigHs.lean#L322).

### Breakdown.Torus.Trilinear

Proves the advection trilinear estimate first for finite Fourier sums and then passes to the full series.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Trilinear.Internal.

**Formula for inner product.** Inner product obeys the exact identity `inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i`. Source: Breakdown.Periodic.Trilinear.Internal.inner_freq in Breakdown.Torus.Trilinear, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L12).

**Formula for Fourier character.** Fourier character obeys the exact identity `character n x = ∏ i, Complex.exp (-(2 * π * Complex.I * (((n i : ℝ) * x i : ℝ) : ℂ)))`. Source: Breakdown.Periodic.Trilinear.Internal.character_eq_prod in Breakdown.Torus.Trilinear, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L15).

**Addition formula for Fourier character.** Fourier character obeys the addition identity `character (a + b) x = character a x * character b x`. Source: Breakdown.Periodic.Trilinear.Internal.character_add in Breakdown.Torus.Trilinear, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L20).

**Formula for complex conjugation.** Complex conjugation obeys the exact identity `starRingEnd ℂ (character a x) = character (-a) x`. Source: Breakdown.Periodic.Trilinear.Internal.conj_character in Breakdown.Torus.Trilinear, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L27).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character n)`. Source: Breakdown.Periodic.Trilinear.Internal.continuous_character in Breakdown.Torus.Trilinear, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L33).

**Formula for unit cell.** Unit cell obeys the exact identity `cell = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin 3 => Icc (0 : ℝ) 1)`. Source: Breakdown.Periodic.Trilinear.Internal.cell_eq in Breakdown.Torus.Trilinear, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L37).

**Compactness of unit cell.** Unit cell is compact, as asserted by `IsCompact cell`. Source: Breakdown.Periodic.Trilinear.Internal.isCompact_cell in Breakdown.Torus.Trilinear, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L41).

**Continuous fields integrate on the cell.** Every continuous normed-group-valued field is integrable over the compact unit cell in the source’s Bochner-integral convention. Source: Breakdown.Periodic.Trilinear.Internal.integrableOn_cell in Breakdown.Torus.Trilinear, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L53).

**One-period character orthogonality.** The scalar Fourier character has integral one at zero integer frequency and zero otherwise over [0,1]. Source: Breakdown.Periodic.Trilinear.Internal.integral_Icc_char in Breakdown.Torus.Trilinear, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L57).

**The zero mode is the cell average.** The integral of a lattice Fourier character over the unit cell is one for the zero lattice vector and zero for every other lattice vector. Source: Breakdown.Periodic.Trilinear.Internal.integral_character in Breakdown.Torus.Trilinear, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L80).

**Formula for inner product.** Inner product obeys the exact identity `inner ℂ (character (-a) x • c) (character (-b) x • d) = character (a - b) x * inner ℂ c d`. Source: Breakdown.Periodic.Trilinear.Internal.inner_smul_character in Breakdown.Torus.Trilinear, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L99).

**Sum formula for integral.** Integral obeys the summation identity `∫ x in cell, inner ℂ (∑ k ∈ s, character (-k) x • a k) (∑ p ∈ t, character (-σ p) x • b p) = ∑ k ∈ s, ∑ p ∈ t, if k = σ p then inner ℂ (a k) (b p) else 0`. Source: Breakdown.Periodic.Trilinear.Internal.integral_inner_sums in Breakdown.Torus.Trilinear, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L104).

**Sum formula for integral.** Integral obeys the summation identity `∫ x in cell, ‖∑ k ∈ s, character (-k) x • a k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2`. Source: Breakdown.Periodic.Trilinear.Internal.integral_norm_sq_sum in Breakdown.Torus.Trilinear, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L120).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k i = k i`. Source: Breakdown.Periodic.Trilinear.Internal.freq_apply in Breakdown.Torus.Trilinear, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L139).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.Trilinear.Internal.norm_freq_sq in Breakdown.Torus.Trilinear, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L142).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ = √(∑ i, ((k i : ℝ)) ^ 2)`. Source: Breakdown.Periodic.Trilinear.Internal.norm_freq_eq in Breakdown.Torus.Trilinear, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L146).

**Bound for divergence pairing.** Divergence pairing satisfies the quantitative estimate `‖divPairing j c‖ ≤ ‖freq j‖ * ‖c‖`. Source: Breakdown.Periodic.Trilinear.Internal.norm_divPairing_le in Breakdown.Torus.Trilinear, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L149).

**Positivity of Sobolev weight.** Sobolev weight is strictly positive, as stated in `0 < weight k`. Source: Breakdown.Periodic.Trilinear.Internal.weight_pos in Breakdown.Torus.Trilinear, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L160).

**Bound for Sobolev weight.** Sobolev weight satisfies the quantitative estimate `1 ≤ weight k`. Source: Breakdown.Periodic.Trilinear.Internal.one_le_weight in Breakdown.Torus.Trilinear, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L164).

**Bound for lattice frequency.** Lattice frequency satisfies the quantitative estimate `4 * π ^ 2 * ‖freq k‖ ^ 2 ≤ weight k`. Source: Breakdown.Periodic.Trilinear.Internal.freq_le_weight in Breakdown.Torus.Trilinear, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L169).

**Coefficient formula for Sobolev weight.** The Fourier-coefficient calculation gives `weight k * ‖coeff u k‖ ^ 2 = ‖(u : Seq) k‖ ^ 2`. Source: Breakdown.Periodic.Trilinear.Internal.weight_mul_norm_coeff_sq in Breakdown.Torus.Trilinear, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L173).

**Sum of Sobolev weight.** Sobolev weight has the exact series sum in `HasSum (fun k => weight k * ‖coeff u k‖ ^ 2) (‖u‖ ^ 2)`. Source: Breakdown.Periodic.Trilinear.Internal.hasSum_weight_coeff in Breakdown.Torus.Trilinear, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L179).

**One advection convolution term.** An advection summand multiplies the first coefficient’s divergence pairing by `2πi` and the second coefficient. Source: Breakdown.Periodic.Trilinear.Internal.advTerm in Breakdown.Torus.Trilinear, line 189. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L189).

**Differentiated Fourier coefficient.** The differentiated coefficient multiplies the original coefficient by `2πi` times the selected lattice coordinate. Source: Breakdown.Periodic.Trilinear.Internal.derivCoef in Breakdown.Torus.Trilinear, line 192. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L192).

**Bound for advection summand.** Advection summand satisfies the quantitative estimate `‖advTerm cu cv p‖ ≤ ‖cu p.1‖ * (2 * π * ‖freq p.2‖ * ‖cv p.2‖)`. Source: Breakdown.Periodic.Trilinear.Internal.norm_advTerm_le in Breakdown.Torus.Trilinear, line 195. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L195).

**Derivative of differentiated coefficient.** The derivative calculation gives `∑ i, ‖derivCoef cv i j‖ ^ 2 = 4 * π ^ 2 * ‖freq j‖ ^ 2 * ‖cv j‖ ^ 2`. Source: Breakdown.Periodic.Trilinear.Internal.norm_derivCoef_sq in Breakdown.Torus.Trilinear, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L205).

**Derivative formula for Fourier character.** The derivative calculation gives `∑ i, (∑ m ∈ s, character (-m) x • cu m) i • ∑ j ∈ s, character (-j) x • derivCoef cv i j = ∑ p ∈ s ×ˢ s, character (-(p.1 + p.2)) x • advTerm cu cv p`. Source: Breakdown.Periodic.Trilinear.Internal.sum_smul_deriv in Breakdown.Torus.Trilinear, line 214. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L214).

**Finite trigonometric polynomial.** The trigonometric polynomial is the sum of inverse Fourier characters times their vector coefficients over a finite frequency set. Source: Breakdown.Periodic.Trilinear.Internal.trig in Breakdown.Torus.Trilinear, line 231. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L231).

**Continuity of trigonometric polynomial.** Trigonometric polynomial is continuous on the domain specified by `Continuous (trig s c)`. Source: Breakdown.Periodic.Trilinear.Internal.continuous_trig in Breakdown.Torus.Trilinear, line 234. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L234).

**Bound for periodic trilinear pairing.** Periodic trilinear pairing satisfies the quantitative estimate `‖∑ i, U i • D i‖ ≤ ‖U‖ * √(∑ i, ‖D i‖ ^ 2)`. Source: Breakdown.Periodic.Trilinear.Internal.norm_sum_smul_le in Breakdown.Torus.Trilinear, line 237. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L237).

**Bound for periodic trilinear pairing.** With the stated hypotheses, periodic trilinear pairing satisfies the estimate `∫ x in cell, P x * (Q x * G x) ≤ (∫ x in cell, P x ^ 2) ^ (1 / 4 : ℝ) * (∫ x in cell, P x ^ (6 : ℝ)) ^ (1 / 12 : ℝ) * (∫ x in cell, Q x ^ (6 : ℝ)) ^ (1 / 6 : ℝ) * (∫ x in cell, G x ^ 2) ^ (1 / 2 : ℝ)`. Source: Breakdown.Periodic.Trilinear.Internal.lpProd_four in Breakdown.Torus.Trilinear, line 245. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L245).

**Derivative formula for integral.** The derivative calculation gives `∫ x in cell, √(∑ i, ‖trig s (derivCoef cv i) x‖ ^ 2) ^ 2 = ∑ j ∈ s, 4 * π ^ 2 * ‖freq j‖ ^ 2 * ‖cv j‖ ^ 2`. Source: Breakdown.Periodic.Trilinear.Internal.integral_sq_deriv in Breakdown.Torus.Trilinear, line 324. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L324).

**A finite trilinear Fourier estimate.** The assumed finite Fourier Sobolev bound gives the displayed trilinear convolution estimate in terms of unweighted, weighted and derivative-weighted coefficient sums. Source: Breakdown.Periodic.Trilinear.Internal.finite_est in Breakdown.Torus.Trilinear, line 335. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L335).

**Reindex by total frequency.** The frequency-pair equivalence sends `(j,k)` to `(j+k,k)`. Source: Breakdown.Periodic.Trilinear.Internal.shiftEquiv in Breakdown.Torus.Trilinear, line 395. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L395).

**Reindex by frequency difference.** The frequency-pair equivalence sends `(j,k)` to `(j,j−k)` and is its own inverse. Source: Breakdown.Periodic.Trilinear.Internal.diffEquiv in Breakdown.Torus.Trilinear, line 401. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L401).

**Sum of advection coefficient.** With the stated hypotheses, advection coefficient has the exact series sum in `HasSum (fun p : Lattice × Lattice => inner ℂ (φ (p.1 + p.2)) (advTerm (coeff u) (coeff v) p)) (∑' k, inner ℂ (φ k) (advCoef u v k))`. Source: Breakdown.Periodic.Trilinear.Internal.hasSum_pairs in Breakdown.Torus.Trilinear, line 407. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L407).

**Limit of frequency lattice.** Frequency lattice has the limit `Tendsto (fun s : Finset Lattice => (s ×ˢ s).filter (fun p => p.1 + p.2 ∈ s)) atTop atTop`. Source: Breakdown.Periodic.Trilinear.Internal.tendsto_pairs in Breakdown.Torus.Trilinear, line 469. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L469).

**Formula for periodic trilinear pairing.** With the stated hypotheses, periodic trilinear pairing obeys the exact identity `(x ^ 2) ^ (1 / 2 : ℝ) = x`. Source: Breakdown.Periodic.Trilinear.Internal.sq_rpow_half in Breakdown.Torus.Trilinear, line 480. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L480).

**Source namespace:** Breakdown.Periodic.

**Derive the periodic trilinear bound.** The periodic Sobolev estimate supplies the trilinear advection bound used in mild uniqueness. Source: Breakdown.Periodic.trilinearBound in Breakdown.Torus.Trilinear, line 487. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Trilinear.lean#L487).

### Breakdown.Torus.Unique

Proves periodic mild uniqueness by contracting the difference on short intervals and continuing across adjacent blocks.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Unique.Internal.

**Formula for bilinear heat kernel.** Bilinear heat kernel obeys the exact identity `kernel τ x x - kernel τ y y = kernel τ (x - y) (x + y)`. Source: Breakdown.Periodic.Unique.Internal.kernel_sq_sub_sq in Breakdown.Torus.Unique, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L12).

**Integrate a shifted singular power.** The integral of `(t−s)⁻³ᐟ⁴` from t₀ to t equals `4(t−t₀)^(1/4)` in the source’s real-power convention. Source: Breakdown.Periodic.Unique.Internal.integral_sub_rpow in Breakdown.Torus.Unique, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L18).

**Integrability of a shifted power kernel.** The shifted singular power `(t−s)⁻³ᐟ⁴` is interval-integrable between t₀ and t. Source: Breakdown.Periodic.Unique.Internal.intervalIntegrable_sub_rpow in Breakdown.Torus.Unique, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L26).

**Quarter-power kernel integral bound.** On a time interval of length at most one, the stated kernel and input bounds give integral norm at most `4 C M S (t−t₀)^(1/4)`. Source: Breakdown.Periodic.Unique.Internal.norm_integral_kernel_le in Breakdown.Torus.Unique, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L32).

**Bound for periodic mild uniqueness.** With the stated hypotheses, periodic mild uniqueness satisfies the quantitative estimate `x ^ (1 / 4 : ℝ) ≤ ε`. Source: Breakdown.Periodic.Unique.Internal.rpow_quarter_le in Breakdown.Torus.Unique, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L57).

**Bound for periodic mild uniqueness.** With the stated hypotheses, periodic mild uniqueness satisfies the estimate `‖w r‖ ≤ S / 2`. Source: Breakdown.Periodic.Unique.Internal.local_contraction in Breakdown.Torus.Unique, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L63).

**Formula for time block.** With the stated hypotheses, time block obeys the exact identity `∀ r ∈ Icc t₀ t₂, w r = 0`. Source: Breakdown.Periodic.Unique.Internal.zero_on_block in Breakdown.Torus.Unique, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L96).

**Formula for periodic mild uniqueness.** With the stated hypotheses, periodic mild uniqueness obeys the exact identity `∀ t ∈ Icc a c, w t = 0`. Source: Breakdown.Periodic.Unique.Internal.zero_of_blocks in Breakdown.Torus.Unique, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L107).

**Integrability of bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel is integrable over the time interval in `IntervalIntegrable (fun s => kernel (t - s) (u s - v s) (u s + v s)) volume a t ∧ u t - v t = ∫ s in a..t, kernel (t - s) (u s - v s) (u s + v s)`. Source: Breakdown.Periodic.Unique.Internal.mild_difference_eq in Breakdown.Torus.Unique, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L132).

**Source namespace:** Breakdown.Periodic.

**Uniqueness of periodic mild flow.** Under the stated assumptions, periodic mild solutions on half-open and closed intervals with the same initial value agree on the half-open interval. Source: Breakdown.Periodic.mildUniqueness in Breakdown.Torus.Unique, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Unique.lean#L150).

### Breakdown.Torus.VarConst

Projects a smooth periodic solution onto Fourier modes and reconstructs the unforced Duhamel equation.

Reading context: Section 6; Lemmas 6.1–6.3.

**Source namespace:** Breakdown.Periodic.Internal.Mild.

**Bounded coefficient evaluation.** Evaluation at a fixed lattice frequency is packaged as a continuous linear map on square-summable sequences. Source: Breakdown.Periodic.Internal.Mild.evalSeq in Breakdown.Torus.VarConst, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L14).

**Bounded physical-coefficient map.** The physical-coefficient map restricts sequence evaluation to the solenoidal subspace and divides by the square root of the Sobolev weight. Source: Breakdown.Periodic.Internal.Mild.coeffL in Breakdown.Torus.VarConst, line 24. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L24).

**Coefficients for bounded coefficient map.** The Fourier-coefficient calculation gives `coeffL k u = coeff u k`. Source: Breakdown.Periodic.Internal.Mild.coeffL_apply in Breakdown.Torus.VarConst, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L27).

**Addition formula for divergence pairing.** Divergence pairing obeys the addition identity `divPairing k (a + b) = divPairing k a + divPairing k b`. Source: Breakdown.Periodic.Internal.Mild.divPairing_add in Breakdown.Torus.VarConst, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L29).

**Scaling formula for divergence pairing.** Divergence pairing obeys the scalar-scaling identity `divPairing k (z • a) = z * divPairing k a`. Source: Breakdown.Periodic.Internal.Mild.divPairing_smul in Breakdown.Torus.VarConst, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L33).

**Scaling formula for divergence pairing.** Divergence pairing obeys the scalar-scaling identity `divPairing k (r • a) = r * divPairing k a`. Source: Breakdown.Periodic.Internal.Mild.divPairing_real_smul in Breakdown.Torus.VarConst, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L38).

**Leray projection as a linear map.** The lattice Leray projection is packaged as a complex linear map. Source: Breakdown.Periodic.Internal.Mild.divFreeLin in Breakdown.Torus.VarConst, line 43. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L43).

**Leray projection as a bounded map.** The complex-linear Leray projection is packaged as a continuous linear map. Source: Breakdown.Periodic.Internal.Mild.divFreeL in Breakdown.Torus.VarConst, line 57. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L57).

**Formula for bounded Leray projection.** Bounded Leray projection obeys the exact identity `divFreeL k c = divFree k c`. Source: Breakdown.Periodic.Internal.Mild.divFreeL_apply in Breakdown.Torus.VarConst, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L59).

**Addition formula for Leray projection.** Leray projection obeys the addition identity `divFree k (a + b) = divFree k a + divFree k b`. Source: Breakdown.Periodic.Internal.Mild.divFree_add in Breakdown.Torus.VarConst, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L61).

**Formula for Leray projection.** With the stated hypotheses, Leray projection obeys the exact identity `divFree k c = c`. Source: Breakdown.Periodic.Internal.Mild.divFree_of_div in Breakdown.Torus.VarConst, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L64).

**Formula for lattice frequency.** Lattice frequency obeys the exact identity `freq k i = k i`. Source: Breakdown.Periodic.Internal.Mild.freq_apply in Breakdown.Torus.VarConst, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L68).

**Norm identity for lattice frequency.** Lattice frequency has the norm identity `‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2`. Source: Breakdown.Periodic.Internal.Mild.norm_freq_sq in Breakdown.Torus.VarConst, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L71).

**Formula for Leray projection.** Leray projection obeys the exact identity `divFree k (latVec k) = 0`. Source: Breakdown.Periodic.Internal.Mild.divFree_latVec in Breakdown.Torus.VarConst, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L75).

**Coefficient formula for Leray projection.** The Fourier-coefficient calculation gives `divFree k (coeff a k) = coeff a k`. Source: Breakdown.Periodic.Internal.Mild.divFree_coeff in Breakdown.Torus.VarConst, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L94).

**Formula for heat evolution.** Heat evolution obeys the exact identity `heat t = heat (max t 0)`. Source: Breakdown.Periodic.Internal.Mild.heat_max in Breakdown.Torus.VarConst, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L100).

**Continuity of heat evolution.** Heat evolution is continuous on the domain specified by `Continuous (fun t => heat t x)`. Source: Breakdown.Periodic.Internal.Mild.heat_apply_continuous in Breakdown.Torus.VarConst, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L107).

**Limit of heat evolution.** With the stated hypotheses, heat evolution has the limit `Tendsto (fun a => heat (σ a) (w a)) l (𝓝 (heat σ₀ w₀))`. Source: Breakdown.Periodic.Internal.Mild.heat_tendsto in Breakdown.Torus.VarConst, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L113).

**Formula for bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel obeys the exact identity `kernel τ x y = heat (τ - σ) (kernel σ x y)`. Source: Breakdown.Periodic.Internal.Mild.kernel_eq_heat in Breakdown.Torus.VarConst, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L128).

**Limit of bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel has the limit `Tendsto (fun a => kernel (τ a) (x a) (y a)) l (𝓝 (kernel τ₀ x₀ y₀))`. Source: Breakdown.Periodic.Internal.Mild.kernel_tendsto in Breakdown.Torus.VarConst, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L132).

**Bound for bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel satisfies the estimate `‖kernel τ‖ ≤ ‖kernel σ‖`. Source: Breakdown.Periodic.Internal.Mild.kernel_opNorm_anti in Breakdown.Torus.VarConst, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L146).

**Uniform bound for bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel admits the uniform bound stated in `∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ x y : V, ‖kernel τ x y‖ ≤ (C * τ ^ (-(3 / 4 : ℝ)) + C) * ‖x‖ * ‖y‖`. Source: Breakdown.Periodic.Internal.Mild.kernel_norm_le in Breakdown.Torus.VarConst, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L154).

**Integrability of bilinear heat kernel.** With the stated hypotheses, bilinear heat kernel is integrable over the time interval in `IntervalIntegrable (fun s => kernel (t - s) (U s) (U s)) volume 0 t`. Source: Breakdown.Periodic.Internal.Mild.integrable_kernel in Breakdown.Torus.VarConst, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L170).

**Smoothness of spatial slice.** With the stated hypotheses, spatial slice has the asserted differentiability order in `ContDiff ℝ ∞ (f t)`. Source: Breakdown.Periodic.Internal.Mild.contDiff_slice in Breakdown.Torus.VarConst, line 200. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L200).

**Formula for divergence.** With the stated hypotheses, divergence obeys the exact identity `divergenceAt (u t) x = 0`. Source: Breakdown.Periodic.Internal.Mild.divergence_nonneg in Breakdown.Torus.VarConst, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L205).

**The unit cell fits in a radius-two ball.** The closed unit cell is contained in the closed Euclidean ball of radius two centered at zero. Source: Breakdown.Periodic.Internal.Mild.cell_subset in Breakdown.Torus.VarConst, line 241. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L241).

**Continuity of Fourier character.** Fourier character is continuous on the domain specified by `Continuous (character k)`. Source: Breakdown.Periodic.Internal.Mild.continuous_character in Breakdown.Torus.VarConst, line 254. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L254).

**Continuity of complexification.** Complexification is continuous on the domain specified by `Continuous complexify`. Source: Breakdown.Periodic.Internal.Mild.continuous_complexify in Breakdown.Torus.VarConst, line 259. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L259).

**Formula for complexification.** Complexification obeys the exact identity `complexify (a - b) = complexify a - complexify b`. Source: Breakdown.Periodic.Internal.Mild.complexify_sub in Breakdown.Torus.VarConst, line 264. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L264).

**Integrability of a Fourier coefficient.** A continuous field multiplied by a Fourier character has an integrable complexification over the unit cell. Source: Breakdown.Periodic.Internal.Mild.integrableOn_cell in Breakdown.Torus.VarConst, line 268. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L268).

**Coefficients for Fourier coefficient.** With the stated hypotheses, the Fourier-coefficient calculation gives `freqTrCoef (fun x => f x - g x) k = freqTrCoef f k - freqTrCoef g k`. Source: Breakdown.Periodic.Internal.Mild.freqTrCoef_sub in Breakdown.Torus.VarConst, line 273. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L273).

**Continuity of Laplacian.** With the stated hypotheses, Laplacian is continuous on the domain specified by `Continuous (sumSecondPartialsAt f)`. Source: Breakdown.Periodic.Internal.Mild.continuous_sumSecondPartialsAt in Breakdown.Torus.VarConst, line 281. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L281).

**Continuity of gradient.** With the stated hypotheses, gradient is continuous on the domain specified by `Continuous (gradientAt g)`. Source: Breakdown.Periodic.Internal.Mild.continuous_gradientAt in Breakdown.Torus.VarConst, line 287. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L287).

**Continuity of advection.** With the stated hypotheses, advection is continuous on the domain specified by `Continuous (advectionAt f)`. Source: Breakdown.Periodic.Internal.Mild.continuous_advectionAt in Breakdown.Torus.VarConst, line 293. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L293).

**Time derivative of Fourier coefficient.** With the stated hypotheses, Fourier coefficient has the one-variable derivative specified by `HasDerivAt (fun σ => freqTrCoef (u σ) k) ((-(4 * π ^ 2 * ‖freq k‖ ^ 2)) • freqTrCoef (u τ) k - divFree k (advCoef (toV (u τ)) (toV (u τ)) k)) τ`. Source: Breakdown.Periodic.Internal.Mild.mode_deriv in Breakdown.Torus.VarConst, line 298. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L298).

**Formula for periodic Duhamel formula.** With the stated hypotheses, periodic Duhamel formula obeys the exact identity `c t = Real.exp (-(l * t)) • c 0 + ∫ s in (0 : ℝ)..t, (-Real.exp (-(l * (t - s)))) • B s`. Source: Breakdown.Periodic.Internal.Mild.variation_of_constants in Breakdown.Torus.VarConst, line 339. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L339).

**Formula for heat multiplier.** With the stated hypotheses, heat multiplier obeys the exact identity `coeff (toV (u t)) k = heatFactor t k • coeff (toV (u 0)) k + ∫ s in (0 : ℝ)..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k`. Source: Breakdown.Periodic.Internal.Mild.mode_identity in Breakdown.Torus.VarConst, line 366. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L366).

**Source namespace:** Breakdown.Periodic.

**Smooth periodic flow is mild.** Under the stated assumptions, a global smooth viscosity-one solution with periodic velocity and pressure gives a periodic mild solution on every finite closed time interval. Source: Breakdown.Periodic.smoothPeriodicIsMild in Breakdown.Torus.VarConst, line 411. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/VarConst.lean#L411).
<!-- /passage:sec-breakdown-torus -->

## Breakdown/Transfer

<!-- passage:sec-breakdown-transfer -->

### Breakdown.Transfer.CompactPiece

Approximates continuous time pieces by finite combinations of scalar time weights and vectors from a dense set.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.CompactPieceInternal.

**Dense elementary continuous time pieces.** If S is dense in X, the span of continuous scalar time weights times vectors from S is dense in the space of continuous time pieces. Source: Breakdown.CompactPieceInternal.dense_span_smul in Breakdown.Transfer.CompactPiece, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/CompactPiece.lean#L13).

### Breakdown.Transfer.CompactSimple

Prepares continuity and extension facts for compactness of the time-piece interaction on simple inputs.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.CompactSimpleInternal.

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f s = f (projIcc 0 T hT s)`. Source: Breakdown.CompactSimpleInternal.extendPiece_eq in Breakdown.Transfer.CompactSimple, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/CompactSimple.lean#L13).

**Bound for extended time piece.** Extended time piece satisfies the quantitative estimate `‖extendPiece f s‖ ≤ ‖f‖`. Source: Breakdown.CompactSimpleInternal.norm_extendPiece_le in Breakdown.Transfer.CompactSimple, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/CompactSimple.lean#L18).

**Continuity of extended time piece.** Extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.CompactSimpleInternal.continuous_extendPiece in Breakdown.Transfer.CompactSimple, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/CompactSimple.lean#L25).

**Continuity of free evolution.** With the stated hypotheses, free evolution is continuous on the domain specified by `ContinuousOn (fun p : ℝ × X => H.G p.1 p.2) (Ici 0 ×ˢ univ)`. Source: Breakdown.CompactSimpleInternal.continuousOn_G_apply in Breakdown.Transfer.CompactSimple, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/CompactSimple.lean#L35).

### Breakdown.Transfer.DiscreteDichotomy

Constructs the inverse on the unstable spectral range and controls the stable and unstable parts of the discrete correction.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.DiscreteDichotomyInternal.

**Formula for spectral projection.** With the stated hypotheses, spectral projection obeys the exact identity `Pu (Pu x) = Pu x`. Source: Breakdown.DiscreteDichotomyInternal.idem_apply in Breakdown.Transfer.DiscreteDichotomy, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L13).

**A commuting projection acts pointwise.** If the projection and evolution operator commute, applying the projection after one evolution step equals evolving the projected vector. Source: Breakdown.DiscreteDichotomyInternal.comm_apply in Breakdown.Transfer.DiscreteDichotomy, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L17).

**The projection commutes with every power.** If the projection and evolution operator commute, they also commute after every natural-number power of the evolution operator. Source: Breakdown.DiscreteDichotomyInternal.comm_pow_apply in Breakdown.Transfer.DiscreteDichotomy, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L21).

**Growth implies injectivity on the range.** The stated lower growth estimate makes M injective on vectors fixed by the projection. Source: Breakdown.DiscreteDichotomyInternal.eq_of_range in Breakdown.Transfer.DiscreteDichotomy, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L28).

**Choose a preimage in the unstable range.** Surjectivity of M on the idempotent projection range gives a vector w in that range satisfying `Mw = Pu z` for every z. Source: Breakdown.DiscreteDichotomyInternal.exists_pre in Breakdown.Transfer.DiscreteDichotomy, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L35).

**A right inverse on the unstable range.** The stated lower growth bound and surjectivity on the projection range yield a bounded linear map N whose image lies in that range and satisfies MN = Pu. Source: Breakdown.DiscreteDichotomyInternal.exists_inverse in Breakdown.Transfer.DiscreteDichotomy, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L44).

**Formula for powers in the unstable range.** Powers in the unstable range obeys the exact identity `Pu ((N ^ (j + 1)) z) = (N ^ (j + 1)) z`. Source: Breakdown.DiscreteDichotomyInternal.range_pow in Breakdown.Transfer.DiscreteDichotomy, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L74).

**Formula for left inverse.** Left inverse obeys the exact identity `Pu ((M ^ j) ((N ^ j) z)) = Pu z`. Source: Breakdown.DiscreteDichotomyInternal.left_inverse_pow in Breakdown.Transfer.DiscreteDichotomy, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L78).

**Bound for discrete spectral dichotomy.** With the stated hypotheses, discrete spectral dichotomy satisfies the quantitative estimate `‖(N ^ (j + 1)) z‖ ≤ K * r₂⁻¹ ^ (j + 1) * ‖Pu z‖`. Source: Breakdown.DiscreteDichotomyInternal.norm_pow_le in Breakdown.Transfer.DiscreteDichotomy, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L86).

**Shift one term of the unstable tail.** Applying M to the next weighted inverse iterate gives Θ times the current weighted inverse iterate under the section’s inverse identities. Source: Breakdown.DiscreteDichotomyInternal.shift_term in Breakdown.Transfer.DiscreteDichotomy, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L93).

**Bound for summand bound.** With the stated hypotheses, summand bound satisfies the quantitative estimate `‖Θ ^ j • (N ^ (j + 1)) (f j)‖ ≤ A * r₂⁻¹ * R * (Θ / r₂) ^ j`. Source: Breakdown.DiscreteDichotomyInternal.term_le in Breakdown.Transfer.DiscreteDichotomy, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L108).

**Addition formula for unstable tail sum.** With the stated hypotheses, unstable tail sum obeys the addition identity `tailSum N Θ (fun j => f j + g j) = tailSum N Θ f + tailSum N Θ g`. Source: Breakdown.DiscreteDichotomyInternal.tailSum_add in Breakdown.Transfer.DiscreteDichotomy, line 134. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L134).

**Scaling formula for unstable tail sum.** Unstable tail sum obeys the scalar-scaling identity `tailSum N Θ (fun j => t • f j) = t • tailSum N Θ f`. Source: Breakdown.DiscreteDichotomyInternal.tailSum_smul in Breakdown.Transfer.DiscreteDichotomy, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L139).

**The tail correction lies in the range.** The unstable tail sum of a uniformly bounded forcing sequence is fixed by the unstable projection. Source: Breakdown.DiscreteDichotomyInternal.range_tailSum in Breakdown.Transfer.DiscreteDichotomy, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L148).

**Bound for discrete spectral dichotomy.** With the stated hypotheses, discrete spectral dichotomy satisfies the quantitative estimate `‖((Θ⁻¹ • M) ^ k) (v - Pu v)‖ ≤ K * (r₁ / Θ) ^ k * ‖v‖`. Source: Breakdown.DiscreteDichotomyInternal.norm_pow_quot_le in Breakdown.Transfer.DiscreteDichotomy, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/DiscreteDichotomy.lean#L184).

### Breakdown.Transfer.Exports

Exports the completed scaling and similarity-to-physical-time implications used in the transfer theorem.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Scaling of abstract mild solutions.** Under the stated assumptions, for positive μ and nonnegative T a mild solution on [0,μT] rescales by the framework dilation to a mild solution on [0,T]. Source: Breakdown.scale in Breakdown.Transfer.Exports, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L37).

**From similarity time to physical time.** Under the stated assumptions, a continuous similarity-time solution of the abstract Duhamel equation yields a self-similar mild solution on [0,1). Source: Breakdown.orbitPhysical in Breakdown.Transfer.Exports, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L39).

### Breakdown.Transfer.Glue

Joins an infinite family of rescaled mild pieces using the logarithmic interval index and endpoint matching.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.GlueInternal.

**Bound for time-piece index.** With the stated hypotheses, time-piece index satisfies the estimate `μ ^ (MildFramework.stepIndex μ t + 1) < 1 - t ∧ 1 - t ≤ μ ^ MildFramework.stepIndex μ t`. Source: Breakdown.GlueInternal.index_spec in Breakdown.Transfer.Glue, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L14).

**Formula for time-piece index.** With the stated hypotheses, time-piece index obeys the exact identity `MildFramework.stepIndex μ t = n`. Source: Breakdown.GlueInternal.index_eq in Breakdown.Transfer.Glue, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L33).

**One piece in physical time.** The scaled piece uses inverse geometric dilation and the affine physical-time coordinate for its index. Source: Breakdown.GlueInternal.scaledPiece in Breakdown.Transfer.Glue, line 47. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L47).

**Continuity of extended time piece.** Extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.GlueInternal.extendPiece_continuous in Breakdown.Transfer.Glue, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L50).

**Continuity of rescaled time piece.** Rescaled time piece is continuous on the domain specified by `Continuous (scaledPiece F μ u n)`. Source: Breakdown.GlueInternal.scaledPiece_continuous in Breakdown.Transfer.Glue, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L59).

**The glued flow agrees with each piece.** When adjacent endpoints match after dilation, the glued flow agrees with the rescaled nth piece on the full closed nth physical-time interval. Source: Breakdown.GlueInternal.glue_eq in Breakdown.Transfer.Glue, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L64).

**Agreement preserves the Duhamel identity.** If two curves agree on [a,t], with a ≤ t, the abstract Duhamel identity for one also holds for the other. Source: Breakdown.GlueInternal.varConst_congr in Breakdown.Transfer.Glue, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L92).

**Each rescaled piece satisfies Duhamel.** Assuming the scaling and time-shift interfaces, the nth physical-time rescaling of a mild piece satisfies the Duhamel identity from its piece start to every point in its interval. Source: Breakdown.GlueInternal.piece_varConst in Breakdown.Transfer.Glue, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L106).

**Continuity of glued flow.** With the stated hypotheses, glued flow is continuous on the domain specified by `ContinuousOn (F.gluePieces μ u) (Icc 0 (1 - μ ^ n)) ∧ ∀ t ∈ Icc 0 (1 - μ ^ n), F.toHeatBilinear.VarConst (F.gluePieces μ u) 0 t`. Source: Breakdown.GlueInternal.glue_upto in Breakdown.Transfer.Glue, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L126).

**Source namespace:** Breakdown.

**Glue rescaled mild time pieces.** Under the stated assumptions, mild time pieces matching after dilation glue to a mild solution on [0,1) with the specified identity between physical and piecewise similarity scales. Source: Breakdown.glue_of in Breakdown.Transfer.Glue, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Glue.lean#L167).

### Breakdown.Transfer.Main

Provides elementary time-piece identities used when assembling the compact initial-data correction.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.TransferAssemblyInternal.

**Addition formula for extended time piece.** Extended time piece obeys the addition identity `extendPiece (f + g) t = extendPiece f t + extendPiece g t`. Source: Breakdown.TransferAssemblyInternal.extendPiece_add in Breakdown.Transfer.Main, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Main.lean#L16).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f t = f ⟨t, ht⟩`. Source: Breakdown.TransferAssemblyInternal.extendPiece_of_mem in Breakdown.Transfer.Main, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Main.lean#L23).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f T = pieceEnd T f`. Source: Breakdown.TransferAssemblyInternal.extendPiece_end in Breakdown.Transfer.Main, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Main.lean#L29).

**Bound for extended time piece.** Extended time piece satisfies the quantitative estimate `‖extendPiece f t‖ ≤ ‖f‖`. Source: Breakdown.TransferAssemblyInternal.norm_extendPiece_le in Breakdown.Transfer.Main, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Main.lean#L34).

**Formula for abstract time piece.** Abstract time piece obeys the exact identity `a + b - a = b`. Source: Breakdown.TransferAssemblyInternal.add_sub_left_eq in Breakdown.Transfer.Main, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Main.lean#L40).

### Breakdown.Transfer.Monodromy

Builds the period map from time-piece propagators and shows that its departure from the reference evolution is compact.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Rotation on continuous time pieces.** The lifted rotation applies the same linear isometry to a time piece at every time. Source: Breakdown.liftPiece in Breakdown.Transfer.Monodromy, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L12).

**Formula for rotation on time pieces.** Rotation on time pieces obeys the exact identity `liftPiece T e f t = e (f t)`. Source: Breakdown.liftPiece_apply in Breakdown.Transfer.Monodromy, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L15).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece (liftPiece T e f) s = e (extendPiece f s)`. Source: Breakdown.extendPiece_liftPiece in Breakdown.Transfer.Monodromy, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L18).

**Formula for time-piece endpoint.** With the stated hypotheses, time-piece endpoint obeys the exact identity `pieceEnd T f = f ⟨T, hT, le_rfl⟩`. Source: Breakdown.pieceEnd_apply in Breakdown.Transfer.Monodromy, line 24. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L24).

**Formula for rotation on time pieces.** Rotation on time pieces obeys the exact identity `liftPiece T e * liftPiece T e.symm = 1`. Source: Breakdown.liftPiece_mul_symm in Breakdown.Transfer.Monodromy, line 30. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L30).

**Formula for rotation on time pieces.** Rotation on time pieces obeys the exact identity `liftPiece T e.symm * liftPiece T e = 1`. Source: Breakdown.liftPiece_symm_mul in Breakdown.Transfer.Monodromy, line 35. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L35).

**Inverse norm under a quarter bound.** In the stated normed ring, an invertible `1−x` with ‖x‖ ≤ 1/4 has inverse norm at most 4/3. Source: Breakdown.norm_inverse_one_sub_le in Breakdown.Transfer.Monodromy, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L40).

**A right inverse identifies the inverse.** If c is invertible and cb = 1, the chosen ring inverse of c equals b. Source: Breakdown.inverse_eq_of_mul_eq_one in Breakdown.Transfer.Monodromy, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L52).

**Inversion respects conjugation.** Conjugating an invertible element by mutually inverse u and v conjugates its inverse by the same u and v. Source: Breakdown.inverse_conj in Breakdown.Transfer.Monodromy, line 57. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L57).

**Products preserve a compact difference.** If each step differs compactly from a fixed bounded operator T₀, then every finite step product differs compactly from the corresponding power of T₀. Source: Breakdown.iterProd_sub_pow_compact in Breakdown.Transfer.Monodromy, line 65. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L65).

**Control one full orbit period.** Under the stated assumptions, step operators of norm at most 1/4 have inverse norm at most 4/3, rotational covariance and a monodromy operator that differs compactly from a free operator of norm at most exp(−P/4). Source: Breakdown.monodromy_of in Breakdown.Transfer.Monodromy, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Monodromy.lean#L81).

### Breakdown.Transfer.OrbitNorm

Uses rotational recurrence to make the orbit norm periodic and rules out decay compatible with a bounded physical continuation.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.OrbitNormInternal.

**The orbit norm is periodic.** The norm of an orbit with rotational period P is an ordinary P-periodic real-valued function. Source: Breakdown.OrbitNormInternal.norm_periodic in Breakdown.Transfer.OrbitNorm, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L14).

**Norm identity for orbit norm.** With the stated hypotheses, orbit norm has the norm identity `‖w (s + n * P)‖ = ‖w s‖`. Source: Breakdown.OrbitNormInternal.norm_add_nat_mul in Breakdown.Transfer.OrbitNorm, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L19).

**Decay forced by a bounded physical flow.** A physical flow bounded by B forces the corresponding similarity orbit to obey `‖w(s′+σ)‖ ≤ exp(−σ)^(1/4) B` for every σ ≥ 0. Source: Breakdown.OrbitNormInternal.decay in Breakdown.Transfer.OrbitNorm, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L23).

**Exponential decay eventually halves.** For every P > 0, some natural-number multiple nP makes `2 exp(−nP)^(1/4) < 1`. Source: Breakdown.OrbitNormInternal.exp_quarter_small in Breakdown.Transfer.OrbitNorm, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L40).

### Breakdown.Transfer.OrbitPhysical

Converts the similarity-time integral equation into the physical mild equation on the interval before blow-up.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.OrbitPhysicalInternal.

**Reciprocal dilation cancels dilation.** For positive μ, dilating first by μ and then by μ⁻¹ returns the original vector. Source: Breakdown.OrbitPhysicalInternal.D_inv_apply in Breakdown.Transfer.OrbitPhysical, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitPhysical.lean#L14).

**Continuity of self-similar velocity.** With the stated hypotheses, self-similar velocity is continuous on the domain specified by `ContinuousOn (F.selfSimilar w s₀) (Ico 0 1)`. Source: Breakdown.OrbitPhysicalInternal.selfSimilar_continuousOn in Breakdown.Transfer.OrbitPhysical, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitPhysical.lean#L19).

**Formula for self-similar velocity.** With the stated hypotheses, self-similar velocity obeys the exact identity `F.selfSimilar w s₀ t = F.G (t - 0) (F.selfSimilar w s₀ 0) + ∫ r in (0 : ℝ)..t, F.K (t - r) (F.selfSimilar w s₀ r) (F.selfSimilar w s₀ r)`. Source: Breakdown.OrbitPhysicalInternal.selfSimilar_eq in Breakdown.Transfer.OrbitPhysical, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitPhysical.lean#L57).

**Source namespace:** Breakdown.

**From similarity time to physical time.** Under the stated assumptions, a continuous similarity-time solution of the abstract Duhamel equation yields a self-similar mild solution on [0,1). Source: Breakdown.orbitPhysical_of in Breakdown.Transfer.OrbitPhysical, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitPhysical.lean#L150).

### Breakdown.Transfer.PeriodicInverse

Solves the periodically conjugated discrete recurrence by reducing complete blocks to the spectral dichotomy.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.PeriodicInverseInternal.

**Forced discrete recurrence.** The recurrence starts at the prescribed value and advances by `θ⁻¹` times the current operator image plus the forcing. Source: Breakdown.PeriodicInverseInternal.nseq in Breakdown.Transfer.PeriodicInverse, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L13).

**Initial value of the forced recurrence.** Discrete forced recurrence has the zero-parameter identity `nseq M θ c x 0 = x`. Source: Breakdown.PeriodicInverseInternal.nseq_zero in Breakdown.Transfer.PeriodicInverse, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L17).

**Formula for discrete forced recurrence.** Discrete forced recurrence obeys the exact identity `nseq M θ c x (n + 1) = θ⁻¹ • (M n (nseq M θ c x n) + c n)`. Source: Breakdown.PeriodicInverseInternal.nseq_succ in Breakdown.Transfer.PeriodicInverse, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L20).

**Addition for discrete forced recurrence.** Discrete forced recurrence obeys the addition identity `nseq M θ (fun t => c t + c' t) (x + x') n = nseq M θ c x n + nseq M θ c' x' n`. Source: Breakdown.PeriodicInverseInternal.nseq_add in Breakdown.Transfer.PeriodicInverse, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L23).

**Scaling for discrete forced recurrence.** Discrete forced recurrence obeys the scalar-scaling identity `nseq M θ (fun t => a • c t) (a • x) n = a • nseq M θ c x n`. Source: Breakdown.PeriodicInverseInternal.nseq_smul in Breakdown.Transfer.PeriodicInverse, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L32).

**Formula for discrete forced recurrence.** Discrete forced recurrence obeys the exact identity `nseq M θ (fun _ => 0) x n = (θ ^ n)⁻¹ • iterProd M n x`. Source: Breakdown.PeriodicInverseInternal.nseq_homog in Breakdown.Transfer.PeriodicInverse, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L39).

**Bound for discrete forced recurrence.** With the stated hypotheses, discrete forced recurrence satisfies the quantitative estimate `‖nseq M θ c x n‖ ≤ L ^ n * (‖x‖ + n * Bc)`. Source: Breakdown.PeriodicInverseInternal.nseq_norm_le in Breakdown.Transfer.PeriodicInverse, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L48).

**Iterate rotational covariance.** Rotational covariance after k steps iterates to covariance after jk steps under the jth power of the rotation. Source: Breakdown.PeriodicInverseInternal.conj_pow in Breakdown.Transfer.PeriodicInverse, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L74).

**Formula for discrete forced recurrence.** With the stated hypotheses, discrete forced recurrence obeys the exact identity `(σ ^ j) (nseq M θ c x (k * j + i)) = nseq M θ (fun t => (σ ^ j) (c (k * j + t))) ((σ ^ j) (nseq M θ c x (k * j))) i`. Source: Breakdown.PeriodicInverseInternal.nseq_block in Breakdown.Transfer.PeriodicInverse, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L83).

**Formula for time block.** With the stated hypotheses, time block obeys the exact identity `orbitSeq ((σ.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd M k) (θ ^ k) (fun j => (θ ^ k) • σ (nseq M θ (fun t => (σ ^ j) (c (k * j + t))) 0 k)) x j = (σ ^ j) (nseq M θ c x (k * j))`. Source: Breakdown.PeriodicInverseInternal.block_orbit in Breakdown.Transfer.PeriodicInverse, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L92).

**Source namespace:** Breakdown.

**Invert the periodic recurrence.** Under the stated assumptions, the stated spectral dichotomy and rotational recurrence assumptions yield a bounded right inverse with its initial correction in the unstable range. Source: Breakdown.periodicInverse_of in Breakdown.Transfer.PeriodicInverse, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PeriodicInverse.lean#L114).

### Breakdown.Transfer.PieceOperator

Realizes free heat evolution and the Duhamel integral as bounded linear and bilinear maps on continuous time pieces.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.PieceOperatorInternal.

**Addition formula for extended time piece.** Extended time piece obeys the addition identity `extendPiece (f + g) s = extendPiece f s + extendPiece g s`. Source: Breakdown.PieceOperatorInternal.extendPiece_add in Breakdown.Transfer.PieceOperator, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L13).

**Scaling formula for extended time piece.** Extended time piece obeys the scalar-scaling identity `extendPiece (c • f) s = c • extendPiece f s`. Source: Breakdown.PieceOperatorInternal.extendPiece_smul in Breakdown.Transfer.PieceOperator, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L20).

**Continuity of extended time piece.** Extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.PieceOperatorInternal.extendPiece_continuous in Breakdown.Transfer.PieceOperator, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L27).

**Bound for extended time piece.** Extended time piece satisfies the quantitative estimate `‖extendPiece f s‖ ≤ ‖f‖`. Source: Breakdown.PieceOperatorInternal.norm_extendPiece_le in Breakdown.Transfer.PieceOperator, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L33).

**Nonnegativity of kernel constant.** With the stated hypotheses, kernel constant is nonnegative, as stated in `0 ≤ H.CK`. Source: Breakdown.PieceOperatorInternal.CK_nonneg in Breakdown.Transfer.PieceOperator, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L39).

**Kernel control after unit time.** At elapsed times at least one, the abstract bilinear kernel is bounded by CK times the two input norms. Source: Breakdown.PieceOperatorInternal.norm_K_far in Breakdown.Transfer.PieceOperator, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L44).

**Duhamel control for extended pieces.** The abstract integral interface gives integrability, the quarter-power short-time norm bound and continuity of the Duhamel integral of two extended time pieces. Source: Breakdown.PieceOperatorInternal.varConst_piece in Breakdown.Transfer.PieceOperator, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L60).

**A bound for any finite time piece.** The abstract integral interface bounds the time-piece Duhamel integral by `(4+T) CK ‖f‖ ‖g‖` at every time in [0,T]. Source: Breakdown.PieceOperatorInternal.norm_integral_le in Breakdown.Transfer.PieceOperator, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L73).

**Continuous Duhamel time piece.** The Duhamel integral of two extended pieces is packaged as a continuous time piece. Source: Breakdown.PieceOperatorInternal.integralPiece in Breakdown.Transfer.PieceOperator, line 120. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L120).

**Time integrability of time piece.** With the stated hypotheses, time piece is integrable over the time interval in `IntervalIntegrable (fun s => H.K (t - s) (extendPiece f s) (extendPiece g s)) volume 0 t`. Source: Breakdown.PieceOperatorInternal.integrable_piece in Breakdown.Transfer.PieceOperator, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L125).

**Formula for Duhamel time piece.** With the stated hypotheses, Duhamel time piece obeys the exact identity `integralPiece h1 H hT (f + f') g = integralPiece h1 H hT f g + integralPiece h1 H hT f' g`. Source: Breakdown.PieceOperatorInternal.integralPiece_add_left in Breakdown.Transfer.PieceOperator, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L130).

**Formula for Duhamel time piece.** With the stated hypotheses, Duhamel time piece obeys the exact identity `integralPiece h1 H hT f (g + g') = integralPiece h1 H hT f g + integralPiece h1 H hT f g'`. Source: Breakdown.PieceOperatorInternal.integralPiece_add_right in Breakdown.Transfer.PieceOperator, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L139).

**Formula for Duhamel time piece.** With the stated hypotheses, Duhamel time piece obeys the exact identity `integralPiece h1 H hT (c • f) g = c • integralPiece h1 H hT f g`. Source: Breakdown.PieceOperatorInternal.integralPiece_smul_left in Breakdown.Transfer.PieceOperator, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L148).

**Formula for Duhamel time piece.** With the stated hypotheses, Duhamel time piece obeys the exact identity `integralPiece h1 H hT f (c • g) = c • integralPiece h1 H hT f g`. Source: Breakdown.PieceOperatorInternal.integralPiece_smul_right in Breakdown.Transfer.PieceOperator, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L156).

**Bounded Duhamel bilinear map.** The Duhamel time-piece integral is packaged as a bounded bilinear map with bound `(4+T) CK`. Source: Breakdown.PieceOperatorInternal.integralBil in Breakdown.Transfer.PieceOperator, line 164. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L164).

**Continuous free-evolution piece.** The free evolution of the initial datum is restricted to the chosen closed time interval. Source: Breakdown.PieceOperatorInternal.freePiece in Breakdown.Transfer.PieceOperator, line 175. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L175).

**Linear free-evolution map.** The free time-piece construction is packaged as a linear map of its initial datum. Source: Breakdown.PieceOperatorInternal.freeLin in Breakdown.Transfer.PieceOperator, line 178. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L178).

**Bound for free evolution.** With the stated hypotheses, free evolution satisfies the quantitative estimate `‖H.G t x‖ ≤ ‖x‖`. Source: Breakdown.PieceOperatorInternal.norm_G_apply_le in Breakdown.Transfer.PieceOperator, line 187. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L187).

**Bounded free-evolution map.** The free time-piece construction is packaged as a continuous linear map of norm at most one. Source: Breakdown.PieceOperatorInternal.freeCLM in Breakdown.Transfer.PieceOperator, line 191. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L191).

**Source namespace:** Breakdown.

**Free and bilinear piece operators.** Under the stated assumptions, the chosen piece operators realize the free evolution and Duhamel integral, with free norm at most one and bilinear norm at most 4CKT^(1/4) for 0 < T ≤ 1. Source: Breakdown.pieceOperator_of in Breakdown.Transfer.PieceOperator, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PieceOperator.lean#L201).

### Breakdown.Transfer.PiecePerturbation

Obtains the local perturbation equation from the bounded time-piece operators.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.PiecePerturbationInternal.

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece f t = f ⟨t, ht⟩`. Source: Breakdown.PiecePerturbationInternal.extendPiece_eq in Breakdown.Transfer.PiecePerturbation, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PiecePerturbation.lean#L13).

**Addition formula for extended time piece.** Extended time piece obeys the addition identity `extendPiece (f + g) = extendPiece f + extendPiece g`. Source: Breakdown.PiecePerturbationInternal.extendPiece_add in Breakdown.Transfer.PiecePerturbation, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PiecePerturbation.lean#L18).

**Continuity of extended time piece.** Extended time piece is continuous on the domain specified by `Continuous (extendPiece f)`. Source: Breakdown.PiecePerturbationInternal.continuous_extendPiece in Breakdown.Transfer.PiecePerturbation, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PiecePerturbation.lean#L26).

**Bound for extended time piece.** With the stated hypotheses, extended time piece satisfies the quantitative estimate `‖extendPiece f t‖ ≤ ‖f‖`. Source: Breakdown.PiecePerturbationInternal.norm_extendPiece_le in Breakdown.Transfer.PiecePerturbation, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PiecePerturbation.lean#L41).

**Source namespace:** Breakdown.

**Add a nonlinear correction piece.** Under the stated assumptions, a solution of the quadratic perturbation equation around a mild reference piece gives the required initial correction and a new mild solution. Source: Breakdown.piecePerturbation_of in Breakdown.Transfer.PiecePerturbation, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/PiecePerturbation.lean#L49).

### Breakdown.Transfer.ProfilePiece

Cuts the similarity orbit into physical mild pieces of length one minus the period dilation factor.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.ProfilePiece.Internal.

**Positivity of time-piece length.** With the stated hypotheses, time-piece length is strictly positive, as stated in `0 < MildFramework.stepLength P k`. Source: Breakdown.ProfilePiece.Internal.stepLength_pos in Breakdown.Transfer.ProfilePiece, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L13).

**Bound for time-piece length.** Time-piece length satisfies the quantitative estimate `MildFramework.stepLength P k < 1`. Source: Breakdown.ProfilePiece.Internal.stepLength_lt_one in Breakdown.Transfer.ProfilePiece, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L21).

**Formula for time-to-terminal factor.** Time-to-terminal factor obeys the exact identity `1 - MildFramework.stepLength P k = Real.exp (-(P / k))`. Source: Breakdown.ProfilePiece.Internal.one_sub_stepLength in Breakdown.Transfer.ProfilePiece, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L25).

**Formula for profile time piece.** With the stated hypotheses, profile time piece obeys the exact identity `toPiece T f t = f t`. Source: Breakdown.ProfilePiece.Internal.toPiece_apply in Breakdown.Transfer.ProfilePiece, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L29).

**Formula for profile time piece.** With the stated hypotheses, profile time piece obeys the exact identity `F.profilePiece w P k m t = F.selfSimilar w (m * (P / k)) t`. Source: Breakdown.ProfilePiece.Internal.profilePiece_apply in Breakdown.Transfer.ProfilePiece, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L36).

**Formula for extended time piece.** With the stated hypotheses, extended time piece obeys the exact identity `extendPiece (F.profilePiece w P k m) t = F.selfSimilar w (m * (P / k)) t`. Source: Breakdown.ProfilePiece.Internal.extendPiece_profilePiece in Breakdown.Transfer.ProfilePiece, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L46).

**Source namespace:** Breakdown.

**Orbit pieces and boundary matching.** Under the stated assumptions, each profile piece is a mild self-similar flow with matching dilated endpoints, rotation after k steps and norm bounded by exp(P/(4k)) times the orbit bound. Source: Breakdown.profilePiece_of in Breakdown.Transfer.ProfilePiece, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/ProfilePiece.lean#L58).

### Breakdown.Transfer.Restrict

Derives restriction, concatenation and time-translation rules for the Duhamel identity.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Propagate an earlier Duhamel identity.** For a ≤ m ≤ t, applying free evolution from m to t to a Duhamel identity on [a,m] shifts its kernel times to t−s and preserves integrability. Source: Breakdown.varConst_free_step in Breakdown.Transfer.Restrict, line 11. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L11).

**Restart the Duhamel identity.** Under the stated assumptions, for a ≤ m ≤ t the Duhamel identities from a to m and from a to t imply the identity from m to t. Source: Breakdown.restrict_of in Breakdown.Transfer.Restrict, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L38).

**Concatenate Duhamel identities.** Under the stated assumptions, for a ≤ m ≤ t a continuous curve satisfying the Duhamel identities from a to m and from m to t also satisfies the identity from a to t. Source: Breakdown.concat_of in Breakdown.Transfer.Restrict, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L46).

**Translate a Duhamel identity.** Under the stated assumptions, the abstract Duhamel identity is invariant under translating both the curve and its initial and final times. Source: Breakdown.shift in Breakdown.Transfer.Restrict, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Restrict.lean#L48).

### Breakdown.Transfer.Scale

Checks dilation covariance of the Duhamel integral and preserves mildness under positive scaling.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**The bilinear kernel respects scaling.** Positive dilation of the bilinear kernel at scaled elapsed time introduces the factor μ required to match the kernel of the dilated inputs. Source: Breakdown.scaled_kernel_eq in Breakdown.Transfer.Scale, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Scale.lean#L10).

**Scaling of abstract mild solutions.** Under the stated assumptions, for positive μ and nonnegative T a mild solution on [0,μT] rescales by the framework dilation to a mild solution on [0,T]. Source: Breakdown.scale_of in Breakdown.Transfer.Scale, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Scale.lean#L17).

### Breakdown.Transfer.SmallData

Applies a quadratic contraction estimate to produce a local mild solution from sufficiently small data.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.SmallData.Internal.

**Formula for bilinear interaction.** Bilinear interaction obeys the exact identity `B v v - B w w = B (v - w) v + B w (v - w)`. Source: Breakdown.SmallData.Internal.bil_sub in Breakdown.Transfer.SmallData, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/SmallData.lean#L11).

**Bound for bilinear interaction.** With the stated hypotheses, bilinear interaction satisfies the quantitative estimate `‖B v v - B w w‖ ≤ 2 * ‖B‖ * r * ‖v - w‖`. Source: Breakdown.SmallData.Internal.bil_norm_sub in Breakdown.Transfer.SmallData, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/SmallData.lean#L17).

**Small-data quadratic solvability.** The stated smallness bound for the bilinear map and datum gives a solution of the quadratic fixed-point equation with the claimed norm control. Source: Breakdown.SmallData.Internal.fixed_point in Breakdown.Transfer.SmallData, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/SmallData.lean#L30).

**Source namespace:** Breakdown.

**Small data on a unit interval.** Under the stated assumptions, sufficiently small initial data produce an abstract mild solution on [0,1] with norm at most twice the initial norm. Source: Breakdown.smallData_of in Breakdown.Transfer.SmallData, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/SmallData.lean#L67).

### Breakdown.Transfer.StatementsDefs

Defines the abstract Duhamel equation and the extension, restriction and endpoint operations on time pieces.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.MildFramework.

**Forget the dilation structure.** The heat-bilinear structure keeps the framework’s heat and bilinear evolution data and their bounds. Source: Breakdown.MildFramework.toHeatBilinear in Breakdown.Transfer.StatementsDefs, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L22).

**Source namespace:** Breakdown.HeatBilinear.

**Abstract Duhamel identity.** The abstract Duhamel predicate requires integrability and identifies the final value with free evolution plus the nonlinear time integral. Source: Breakdown.HeatBilinear.VarConst in Breakdown.Transfer.StatementsDefs, line 44. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L44).

**Mild flow before the endpoint.** The mild-flow predicate requires continuity and the Duhamel identity on the half-open time interval `[a,b)`. Source: Breakdown.HeatBilinear.IsMildOn in Breakdown.Transfer.StatementsDefs, line 48. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L48).

**Mild flow including the endpoint.** The closed-interval mild-flow predicate requires continuity and the Duhamel identity on `[a,b]`. Source: Breakdown.HeatBilinear.IsMildOnIcc in Breakdown.Transfer.StatementsDefs, line 53. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L53).

**Compactness on a dense test set.** The compact-kernel predicate requires a dense set of first inputs for which the positive-time kernel is a compact operator. Source: Breakdown.HeatBilinear.HasCompactKernel in Breakdown.Transfer.StatementsDefs, line 58. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L58).

**Source namespace:** Breakdown.

**Extend by endpoint values.** For a nonnegative interval length a time piece is extended using the nearest endpoint outside its interval, and for negative length the extension is zero. Source: Breakdown.extendPiece in Breakdown.Transfer.StatementsDefs, line 65. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L65).

**Restrict a curve to a time piece.** A curve is restricted to the closed interval when that restriction is continuous, and otherwise the construction returns the zero piece. Source: Breakdown.toPiece in Breakdown.Transfer.StatementsDefs, line 69. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L69).

**Evaluate a time-piece endpoint.** Endpoint evaluation returns the value at the right endpoint for nonnegative interval length and is the zero map for negative length. Source: Breakdown.pieceEnd in Breakdown.Transfer.StatementsDefs, line 72. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L72).

**Source namespace:** Breakdown.HeatBilinear.

**Choose the free-evolution operator.** The free time-piece operator chooses a bounded realization of the heat trajectory and otherwise returns zero. Source: Breakdown.HeatBilinear.pieceFree in Breakdown.Transfer.StatementsDefs, line 86. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L86).

**Source namespace:** Breakdown.MildFramework.

**Abstract and framework mild flow.** Half-open mild equation has the equivalent characterizations `F.IsMildOn u a b ↔ F.toHeatBilinear.IsMildOn u a b`. Source: Breakdown.MildFramework.isMildOn_iff in Breakdown.Transfer.StatementsDefs, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L126).

**Abstract and framework closed mild flow.** Closed mild equation has the equivalent characterizations `F.IsMildOnIcc u a b ↔ F.toHeatBilinear.IsMildOnIcc u a b`. Source: Breakdown.MildFramework.isMildOnIcc_iff in Breakdown.Transfer.StatementsDefs, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L129).

**Compactness on a dense test set.** Under the stated assumptions, positive-time bilinear kernels are compact operators for first inputs in a dense set. Source: Breakdown.MildFramework.hasCompactKernel in Breakdown.Transfer.StatementsDefs, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L132).

**Index before the terminal time.** The abstract time-piece index is the natural-number floor of `log(1−t) / log μ`. Source: Breakdown.MildFramework.stepIndex in Breakdown.Transfer.StatementsDefs, line 134. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsDefs.lean#L134).

### Breakdown.Transfer.StatementsFrame

States the positive-scaling and similarity-to-physical-time interfaces of the abstract framework.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Scaling of abstract mild solutions.** This proposition requires that for positive μ and nonnegative T a mild solution on [0,μT] rescales by the framework dilation to a mild solution on [0,T]. Source: Breakdown.ScaleStatement in Breakdown.Transfer.StatementsFrame, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L10).

**From similarity time to physical time.** This proposition requires that a continuous similarity-time solution of the abstract Duhamel equation yields a self-similar mild solution on [0,1). Source: Breakdown.OrbitPhysicalStatement in Breakdown.Transfer.StatementsFrame, line 15. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L15).

### Breakdown.Transfer.StatementsLocal

States concatenation and time translation for the abstract Duhamel identity.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Concatenate Duhamel identities.** This proposition requires that for a ≤ m ≤ t a continuous curve satisfying the Duhamel identities from a to m and from m to t also satisfies the identity from a to t. Source: Breakdown.ConcatStatement in Breakdown.Transfer.StatementsLocal, line 32. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L32).

**Translate a Duhamel identity.** This proposition requires that the abstract Duhamel identity is invariant under translating both the curve and its initial and final times. Source: Breakdown.ShiftStatement in Breakdown.Transfer.StatementsLocal, line 37. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsLocal.lean#L37).

### Breakdown.Transfer.StepData

Assembles monodromy, the spectral dichotomy, a finite-dimensional section and periodic inversion into correction data.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Finite correction and sequence inverse.** Under the stated assumptions, the orbit supplies arbitrarily short steps, a rate between the dilation rate and one, a finite-dimensional correction space and a bounded right inverse of the linear recurrence. Source: Breakdown.stepData_of in Breakdown.Transfer.StepData, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StepData.lean#L48).

### Breakdown.Transfer.Unique

Proves abstract mild uniqueness by a uniform short-time contraction and interval continuation.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.

**Nonnegativity of kernel constant.** With the stated hypotheses, kernel constant is nonnegative, as stated in `0 ≤ H.CK`. Source: Breakdown.heatBilinear_ck_nonneg in Breakdown.Transfer.Unique, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Unique.lean#L11).

**Choose a uniqueness time step.** A sufficiently short positive time step makes the singular-kernel contraction factor `8 CK δ^(1/4) M` at most one half. Source: Breakdown.exists_contraction_length in Breakdown.Transfer.Unique, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Unique.lean#L16).

**Extend equality by a short time step.** Under the stated uniform bounds and half-contraction condition, equality through m extends through `min(m+δ,T)`. Source: Breakdown.eq_on_next_interval in Breakdown.Transfer.Unique, line 39. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Unique.lean#L39).

**The Duhamel identity gives uniqueness.** Two continuous curves satisfying the abstract Duhamel identity throughout [a,T] and sharing their initial value agree throughout that interval, assuming integral control and restart. Source: Breakdown.eq_on_Icc_of_varConst in Breakdown.Transfer.Unique, line 100. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Unique.lean#L100).

**Uniqueness of abstract mild flow.** Under the stated assumptions, abstract mild solutions with the same initial value agree on both half-open and closed time intervals. Source: Breakdown.unique_of in Breakdown.Transfer.Unique, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Unique.lean#L139).

### Breakdown.Transfer.VarConstIntegral

Establishes integrability, continuity and the quarter-power norm estimate for the abstract Duhamel integral.

Reading context: Propositions 2.1 and 4.3; Lemmas 4.6–4.8.

**Source namespace:** Breakdown.VarConstIntegralInternal.

**Nonnegativity of kernel constant.** Kernel constant is nonnegative, as stated in `0 ≤ H.CK`. Source: Breakdown.VarConstIntegralInternal.ck_nonneg in Breakdown.Transfer.VarConstIntegral, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L13).

**The kernel norm decreases after one.** At elapsed time at least one, the abstract bilinear-kernel norm is at most its norm at time one. Source: Breakdown.VarConstIntegralInternal.norm_K_le_one in Breakdown.Transfer.VarConstIntegral, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L18).

**A kernel bound for all positive times.** For every positive elapsed time τ, the abstract kernel norm is bounded by `CK(τ⁻³ᐟ⁴+1)`. Source: Breakdown.VarConstIntegralInternal.norm_K_le in Breakdown.Transfer.VarConstIntegral, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L28).

**Limit of bilinear kernel.** With the stated hypotheses, bilinear kernel has the limit `Tendsto (fun x => H.K (τ x) (w x) (z x)) l (𝓝 (H.K τ₀ x₀ y₀))`. Source: Breakdown.VarConstIntegralInternal.tendsto_K in Breakdown.Transfer.VarConstIntegral, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L40).

**Continuity of bilinear kernel.** With the stated hypotheses, bilinear kernel is continuous on the domain specified by `ContinuousOn (fun x => H.K (τ x) (w x) (z x)) S`. Source: Breakdown.VarConstIntegralInternal.continuousOn_K in Breakdown.Transfer.VarConstIntegral, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L76).

**Clamping stays in the interval.** When a ≤ b, the value `max a (min b s)` belongs to [a,b] for every real s. Source: Breakdown.VarConstIntegralInternal.clamp_mem in Breakdown.Transfer.VarConstIntegral, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L81).

**Formula for interval clamp.** With the stated hypotheses, interval clamp obeys the exact identity `max a (min b s) = s`. Source: Breakdown.VarConstIntegralInternal.clamp_eq in Breakdown.Transfer.VarConstIntegral, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L84).

**Continuity of interval clamp.** With the stated hypotheses, interval clamp is continuous on the domain specified by `Continuous (fun s => u (max a (min b s)))`. Source: Breakdown.VarConstIntegralInternal.continuous_clamp in Breakdown.Transfer.VarConstIntegral, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L87).

**Duhamel kernel with clamped inputs.** The auxiliary kernel evaluates both input curves at the clamped time `t−r` and applies the bilinear kernel at elapsed time `r`. Source: Breakdown.VarConstIntegralInternal.kern in Breakdown.Transfer.VarConstIntegral, line 91. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L91).

**Continuity of clamped Duhamel kernel.** With the stated hypotheses, clamped Duhamel kernel is continuous on the domain specified by `ContinuousOn (kern H a b u v t) (Ioi 0)`. Source: Breakdown.VarConstIntegralInternal.kern_continuousOn in Breakdown.Transfer.VarConstIntegral, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L94).

**Continuity of clamped Duhamel kernel.** With the stated hypotheses, clamped Duhamel kernel is continuous on the domain specified by `Continuous (fun t => kern H a b u v t r)`. Source: Breakdown.VarConstIntegralInternal.kern_continuous_left in Breakdown.Transfer.VarConstIntegral, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L100).

**Bound for clamped Duhamel kernel.** With the stated hypotheses, clamped Duhamel kernel satisfies the quantitative estimate `‖kern H a b u v t r‖ ≤ H.CK * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N`. Source: Breakdown.VarConstIntegralInternal.norm_kern_le in Breakdown.Transfer.VarConstIntegral, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L106).

**Bound for clamped Duhamel kernel.** With the stated hypotheses, clamped Duhamel kernel satisfies the quantitative estimate `‖kern H a b u v t r‖ ≤ H.CK * M * N * r ^ (-(3 / 4 : ℝ))`. Source: Breakdown.VarConstIntegralInternal.norm_kern_le_small in Breakdown.Transfer.VarConstIntegral, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L118).

**The singular majorant is integrable.** For c ≥ 0, the majorant `C (r⁻³ᐟ⁴+1) M N` is integrable on the half-open interval (0,c]. Source: Breakdown.VarConstIntegralInternal.bound_integrableOn in Breakdown.Transfer.VarConstIntegral, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L131).

**Integrability of the clamped kernel.** With the stated hypotheses, clamped Duhamel kernel is integrable over the time interval in `IntervalIntegrable (kern H a b u v t) volume 0 c`. Source: Breakdown.VarConstIntegralInternal.kern_intervalIntegrable in Breakdown.Transfer.VarConstIntegral, line 137. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L137).

**Reverse the Duhamel time variable.** For t in [a,b], substituting elapsed time r = t−s rewrites the Duhamel integral as the integral of the clamped kernel from zero to t−a. Source: Breakdown.VarConstIntegralInternal.integral_eq_kern in Breakdown.Transfer.VarConstIntegral, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L147).

**Integrate the singular time power.** The interval integral of `r⁻³ᐟ⁴` from zero to c equals `4 c^(1/4)` with the source’s real-power convention. Source: Breakdown.VarConstIntegralInternal.integral_rpow_three_quarters in Breakdown.Transfer.VarConstIntegral, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/VarConstIntegral.lean#L158).
<!-- /passage:sec-breakdown-transfer -->

