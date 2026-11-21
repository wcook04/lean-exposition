import Breakdown.FracCert.StHeld

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldNonzeroInternal

theorem partsIdentity {W : Space → Space} (hW : ContDiff ℝ 1 W) {φ : Space → ℝ} (hφ : IsTestScalar φ)
    (j : Fin 3) :
    ∫ y, (fderiv ℝ φ y (unitVector j)) • W y = -∫ y, φ y • fderiv ℝ W y (unitVector j) := by
  have hφc : ContDiff ℝ 1 φ := hφ.1.of_le (mod_cast le_top)
  have h1 : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h2 : Continuous (fun y => fderiv ℝ W y (unitVector j)) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs1 : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) _
  have hi1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • W y) :=
    (h1.smul hW.continuous).integrable_of_hasCompactSupport hs1.smul_right
  have hi2 : Integrable (fun y => φ y • fderiv ℝ W y (unitVector j)) :=
    (hφc.continuous.smul h2).integrable_of_hasCompactSupport hφ.2.smul_right
  have hi3 : Integrable (fun y => φ y • W y) :=
    (hφc.continuous.smul hW.continuous).integrable_of_hasCompactSupport hφ.2.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (v := unitVector j)
    hi1 hi2 hi3 (fun x _ => hφc.differentiable one_ne_zero x) (fun x _ => hW.differentiable one_ne_zero x)
  rw [h, neg_neg]

theorem entrySq_nonneg (G : Space →L[ℝ] Space) : 0 ≤ entrySq G := by
  unfold entrySq
  positivity

theorem gradient_ae_eq {W u : Space → Space} (hW : ContDiff ℝ 1 W) {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hweak : IsWeakGradientOf u G) (hu : ∀ᵐ y ∂volume, W y + u y = 0) :
    ∀ᵐ y ∂volume, entrySq (G y) = entrySq (fderiv ℝ W y) := by
  have key : ∀ j : Fin 3, ∀ᵐ y ∂volume, G y (unitVector j) = -fderiv ℝ W y (unitVector j) := by
    intro j
    have hmeas : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hG
    have hL2 : MemLp (fun y => G y (unitVector j)) 2 volume := by
      rw [memLp_two_iff_integrable_sq_norm hmeas]
      refine hG2.mono' (hmeas.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      unfold entrySq
      exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    have hloc1 : LocallyIntegrable (fun y => G y (unitVector j)) volume :=
      hL2.locallyIntegrable (by norm_num)
    have hcont : Continuous (fun y => -fderiv ℝ W y (unitVector j)) :=
      ((hW.continuous_fderiv one_ne_zero).clm_apply continuous_const).neg
    refine ae_eq_of_integral_contDiff_smul_eq hloc1 hcont.locallyIntegrable (fun φ hφd hφs => ?_)
    have h1 := hweak φ ⟨hφd, hφs⟩ j
    have h2 := partsIdentity hW ⟨hφd, hφs⟩ j
    have h3 : ∫ y, fderiv ℝ φ y (unitVector j) • u y = -∫ y, fderiv ℝ φ y (unitVector j) • W y := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hu] with y hy
      have hy' : u y = -W y := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy)
      rw [hy', smul_neg]
    have h4 : ∫ y, φ y • -fderiv ℝ W y (unitVector j) = -∫ y, φ y • fderiv ℝ W y (unitVector j) := by
      simp_rw [smul_neg]
      exact integral_neg _
    rw [h4, ← h2]
    exact neg_inj.mp (h1.symm.trans h3)
  filter_upwards [ae_all_iff.mpr key] with y hy
  unfold entrySq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy i, norm_neg]

end HeldNonzeroInternal

open HeldNonzeroInternal in
theorem heldNonzero : HeldNonzeroStatement := by
  intro α _ _ k N d hd p hp u G H P κ hsol hsize hzero
  have hst := hsol.state.second
  have hae := gradient_ae_eq (hd.profile_smooth p hp) hst.measurable_gradient hst.gradient_two
    hst.weak_gradient hzero
  have heq : ∫ y, entrySq (d.gradProfile p y) = ∫ y, entrySq (G y) :=
    (integral_congr_ae hae).symm
  have hwm := hd.weightMin_pos
  have hint : Integrable (fun y => d.weight y * entrySq (G y)) := by
    refine (hst.gradient_two.const_mul d.weightMax).mono'
      (hd.weight_measurable.aestronglyMeasurable.mul hst.gradient_two.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := entrySq_nonneg (G y)
    have hw0 : 0 ≤ d.weight y := hwm.le.trans (hd.weight_lower y)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 h0)]
    exact mul_le_mul_of_nonneg_right (hd.weight_upper y) h0
  have hlow : d.weightMin * ∫ y, entrySq (G y) ≤ ∫ y, d.weight y * entrySq (G y) := by
    rw [← integral_const_mul]
    exact integral_mono (hst.gradient_two.const_mul _) hint fun y =>
      mul_le_mul_of_nonneg_right (hd.weight_lower y) (entrySq_nonneg (G y))
  have htr : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => by positivity
  have hen : d.weightMin * ∫ y, entrySq (G y) ≤ d.energy G H := by
    show _ ≤ (∫ y, ‖secondTrace (H y)‖ ^ 2) + ∫ y, d.weight y * entrySq (G y)
    linarith
  have hsz : Real.sqrt (d.energy G H) ≤ d.size G H κ := by
    show Real.sqrt (d.energy G H) ≤ Real.sqrt (d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2)
    have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by positivity
    exact Real.sqrt_le_sqrt (by linarith)
  have hnt := hd.nontrivial p hp
  rw [heq] at hnt
  have hsw : 0 < Real.sqrt d.weightMin := Real.sqrt_pos.mpr hwm
  have hkey : Real.sqrt (∫ y, entrySq (G y)) * Real.sqrt d.weightMin ≤ d.heldRadius := by
    rw [← Real.sqrt_mul' _ hwm.le, mul_comm (∫ y, entrySq (G y))]
    exact (Real.sqrt_le_sqrt hen).trans (hsz.trans hsize)
  have hfin : Real.sqrt (∫ y, entrySq (G y)) ≤ d.heldRadius / Real.sqrt d.weightMin :=
    (le_div_iff₀ hsw).mpr hkey
  linarith

end SteadyCert

end Breakdown
