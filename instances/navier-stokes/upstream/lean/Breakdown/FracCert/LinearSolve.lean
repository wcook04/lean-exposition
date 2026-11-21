import Breakdown.FracCert.LinearSolveCore

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace LinearSolveInternal

theorem gradient_neg {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq, hQ2, hm, hw⟩ := hQ
  refine ⟨fun y => -q y, ?_, ?_, hm.neg, ?_⟩
  · simpa only [neg_sq] using hq
  · simpa only [norm_neg] using hQ2
  · intro φ hφ j
    have h := hw φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg, neg_neg]
    linarith

theorem l2Norm_ae_zero {F : Space → Space} (h : ∀ᵐ y ∂volume, F y = 0) : l2Norm F = 0 := by
  unfold l2Norm
  rw [integral_eq_zero_of_ae (h.mono fun y hy => by simp [hy])]
  simp

theorem l2Pair_ae_zero {F : Space → Space} (E : Space → Space) (h : ∀ᵐ y ∂volume, F y = 0) :
    l2Pair F E = 0 := by
  unfold l2Pair
  exact integral_eq_zero_of_ae (h.mono fun y hy => by simp [hy])

theorem sub_ae_zero {F Q : Space → Space} (hF : ∀ᵐ y ∂volume, F y = Q y) :
    ∀ᵐ y ∂volume, F y + -Q y = 0 :=
  hF.mono fun y hy => by rw [hy, add_neg_cancel]

theorem projectedNorm_zero {F Q : Space → Space} (hQ : IsGradientField Q)
    (hF : ∀ᵐ y ∂volume, F y = Q y) : projectedNorm F = 0 := by
  unfold projectedNorm
  have hz := sub_ae_zero hF
  have h0 : (0 : ℝ) ∈ {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => F y + Q y) 2 volume ∧
      r = l2Norm (fun y => F y + Q y)} := by
    refine ⟨fun y => -Q y, gradient_neg hQ, ?_, ?_⟩
    · show MemLp (fun y => F y + -Q y) 2 volume
      exact (MemLp.zero : MemLp (0 : Space → Space) 2 volume).ae_eq
        (hz.mono fun y hy => by simp only [Pi.zero_apply]; exact hy.symm)
    · show 0 = l2Norm (fun y => F y + -Q y)
      exact (l2Norm_ae_zero hz).symm
  have hlb : ∀ r ∈ {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => F y + Q y) 2 volume ∧
      r = l2Norm (fun y => F y + Q y)}, 0 ≤ r := by
    rintro r ⟨Q', -, -, hr⟩
    rw [hr]
    exact Real.sqrt_nonneg _
  exact le_antisymm (csInf_le ⟨0, hlb⟩ h0) (le_csInf ⟨0, h0⟩ hlb)

theorem rowSeminorm_zero {N : ℕ} (e : Fin N → Space → Space) (τw : Fin N → ℝ) {F Q : Space → Space}
    (hQ : IsGradientField Q) (hF : ∀ᵐ y ∂volume, F y = Q y) : rowSeminorm e τw F = 0 := by
  unfold rowSeminorm
  have hz := sub_ae_zero hF
  have h0 : (0 : ℝ) ∈ {r | ∃ Q, IsGradientField Q ∧ r = rowSize e τw (fun y => F y + Q y)} := by
    refine ⟨fun y => -Q y, gradient_neg hQ, ?_⟩
    show 0 = rowSize e τw (fun y => F y + -Q y)
    unfold rowSize
    simp only [l2Pair_ae_zero _ hz]
    simp
  have hlb : ∀ r ∈ {r | ∃ Q, IsGradientField Q ∧ r = rowSize e τw (fun y => F y + Q y)}, 0 ≤ r := by
    rintro r ⟨Q', -, hr⟩
    rw [hr]
    exact Real.sqrt_nonneg _
  exact le_antisymm (csInf_le ⟨0, hlb⟩ h0) (le_csInf ⟨0, h0⟩ hlb)

theorem clm_eq_zero {L : Space →L[ℝ] Space} (h : ∀ j, L (unitVector j) = 0) : L = 0 := by
  have h' : ∀ j, L (EuclideanSpace.single j 1) = 0 := h
  ext1 x
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, h']

theorem entrySq_nonneg (L : Space →L[ℝ] Space) : 0 ≤ entrySq L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem eq_zero_of_entrySq {L : Space →L[ℝ] Space} (h : entrySq L = 0) : L = 0 := by
  apply clm_eq_zero
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖L (unitVector i)‖)).mp h j
    (Finset.mem_univ _)
  simpa using hj

end LinearSolveInternal

open LinearSolveInternal

theorem linearKernel (h1 : AprioriBoundStatement) (hI : InverseSquareBoundStatement) :
    LinearKernelStatement := by
  intro α hα1 hα2 k N d hd p hp v G H P hst κ hQex hpin
  obtain ⟨Q, hQ, hff⟩ := hQex
  have hb := h1 α hα1 hα2 d hd p hp v G H P hst κ
  have hpins : vecNorm (d.pins G) = 0 := by
    unfold vecNorm
    simp [hpin]
  rw [projectedNorm_zero hQ hff, FracCertData.rowsModGrad, rowSeminorm_zero d.row d.rowWeight hQ hff,
    hpins] at hb
  have hb0 : d.boundFn 0 (Real.sqrt (0 ^ 2 + d.pinWeight * 0 ^ 2)) 0 = 0 := by
    simp [FracCertData.boundFn, boundConst]
  rw [hb0] at hb
  have hs : weightedEnergy d.weight G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 ≤ 0 := by
    have h' : d.size G H κ = 0 := le_antisymm hb (Real.sqrt_nonneg _)
    exact Real.sqrt_eq_zero'.mp h'
  have hst2 := hst.second
  have hwpos : ∀ y, 0 < d.weight y := fun y => hd.weightMin_pos.trans_le (hd.weight_lower y)
  have hT : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => by positivity
  have hW : 0 ≤ ∫ y, d.weight y * entrySq (G y) :=
    integral_nonneg fun y => mul_nonneg (hwpos y).le (entrySq_nonneg _)
  have hK : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hμ : 0 < d.multiplierScale ^ 2 := by have := hd.multiplierScale_pos; positivity
  unfold weightedEnergy at hs
  have hW0 : ∫ y, d.weight y * entrySq (G y) = 0 := by nlinarith
  have hK0 : ∑ i, κ i ^ 2 = 0 := le_antisymm (by nlinarith) hK
  have hκ : κ = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (κ i))).mp hK0 i
      (Finset.mem_univ _)
    simpa using hi
  have hint : Integrable (fun y => d.weight y * entrySq (G y)) :=
    hst2.gradient_two.bdd_mul (c := d.weightMax) hd.weight_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (hwpos y)]
        exact hd.weight_upper y)
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun y => mul_nonneg (hwpos y).le (entrySq_nonneg _)) hint).mp hW0
  have hG0 : ∀ᵐ y ∂volume, G y = 0 := hae.mono fun y hy => by
    have hy' : d.weight y * entrySq (G y) = 0 := hy
    rcases mul_eq_zero.mp hy' with h | h
    · exact absurd h (hwpos y).ne'
    · exact eq_zero_of_entrySq h
  have hE0 : ∫ y, entrySq (G y) = 0 :=
    integral_eq_zero_of_ae (hG0.mono fun y hy => by simp [hy, entrySq])
  obtain ⟨hIi, hIle⟩ := hI v G hst2.measurable_velocity hst2.velocity_six hst2.gradient_two
    hst2.weak_gradient
  rw [hE0, mul_zero] at hIle
  have hae2 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hIi).mp
    (le_antisymm hIle (integral_nonneg fun y => by positivity))
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  have hv0 : ∀ᵐ y ∂volume, v y = 0 := by
    filter_upwards [hae2, hne] with y hy hy0
    have hy' : ‖v y‖ ^ 2 / ‖y‖ ^ 2 = 0 := hy
    simpa [hy0] using hy'
  have hP0 : ∀ᵐ y ∂volume, P y = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hst.power.1.locallyIntegrable (by norm_num))
    intro g hg hgs
    by_cases hgi : Integrable (fun y => g y • P y)
    · set X := ∫ y, g y • P y with hX
      have key : ∫ y, inner ℝ (P y) (g y • X) = 0 := by
        rw [hst.power.2 (fun y => g y • X) ⟨hg.smul contDiff_const, hgs.smul_right⟩]
        exact integral_eq_zero_of_ae (hv0.mono fun y hy => by simp [hy])
      have hXX : inner ℝ X X = 0 := by
        rw [hX, ← integral_inner hgi, ← hX]
        simpa [real_inner_smul_left, real_inner_smul_right, real_inner_comm] using key
      exact inner_self_eq_zero.mp hXX
    · exact integral_undef hgi
  have hs0 : ∀ i : Fin 3, EuclideanSpace.single i (0 : ℝ) = 0 := fun i => by
    ext j
    simp
  refine ⟨?_, hκ⟩
  filter_upwards [hv0, hG0, hP0] with y hv hG hP
  simp [driftField, hv, hG, hP, axialTurn, hs0]

theorem linearSolve (h1 : AprioriBoundStatement) (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement)
    (h4 : FreeBoundsStatement) (h5 : ProfileProductCompactStatement) (h6 : SolenoidalSplitStatement)
    (h7 : SecondOrderLinearStatement) (h8 : LinearStateClosedStatement)
    (h9 : GradientOrthogonalStatement) (h10 : InverseSquareBoundStatement) (h11 : ProductClassStatement)
    (h12 : WeakPowerDifferenceStatement) : LinearSolveStatement :=
  LinearSolveCore.linearSolve_of_kernel' h2 h3 h4 h5 h6 h7 h9 h11 h10 h12 (linearKernel h1 h10)

end SteadyCert

end Breakdown
