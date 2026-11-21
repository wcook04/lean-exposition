import Breakdown.Frac.StOperator

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

theorem secondOrderRemainder_comp_smul (v : Space → Space) (hv : ContDiff ℝ 2 v) (l : ℝ) (y z : Space) :
    secondOrderRemainder (fun x => v (l • x)) y z = secondOrderRemainder v (l • y) (l • z) := by
  have hd : DifferentiableAt ℝ v (l • y) := hv.differentiable (by norm_num) _
  have h1 : fderiv ℝ (fun x => v (l • x)) y =
      (fderiv ℝ v (l • y)).comp (l • ContinuousLinearMap.id ℝ Space) := by
    have hs : HasFDerivAt (fun x : Space => l • x) (l • ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).const_smul l
    exact (hd.hasFDerivAt.comp y hs).fderiv
  have h2 : iteratedFDeriv ℝ 2 (fun x => v (l • x)) y = l ^ 2 • iteratedFDeriv ℝ 2 v (l • y) := by
    rw [iteratedFDeriv_comp_const_smul (i := 2) l hv]
  have h3 : (![l • z, l • z] : Fin 2 → Space) = fun i => l • (![z, z] : Fin 2 → Space) i := by
    ext i : 1
    fin_cases i <;> rfl
  unfold secondOrderRemainder
  rw [h1, h2, h3, ContinuousMultilinearMap.map_smul_univ]
  simp [smul_add, pow_two, mul_smul]

theorem fractionalPowerAt_comp_smul (α : ℝ) (v : Space → Space) (hv : ContDiff ℝ 2 v) (l : ℝ) (hl : 0 < l)
    (y : Space) :
    fractionalPowerAt α (fun x => v (l • x)) y = l ^ (2 * α) • fractionalPowerAt α v (l • y) := by
  unfold fractionalPowerAt
  obtain ⟨G, hG⟩ : ∃ G : Space → Space,
      G = fun u : Space => ‖u‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v (l • y) u := ⟨_, rfl⟩
  have hpt : (fun z : Space =>
      ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (fun x => v (l • x)) y z) =
        fun z => l ^ (3 + 2 * α) • G (l • z) := by
    funext z
    rw [secondOrderRemainder_comp_smul v hv l y z, hG]
    beta_reduce
    rw [norm_smul, Real.norm_of_nonneg hl.le, Real.mul_rpow hl.le (norm_nonneg _), smul_smul,
      ← mul_assoc, ← Real.rpow_add hl]
    simp
  rw [hpt, integral_smul, Measure.integral_comp_smul (μ := volume) (f := G) (R := l), ← hG]
  simp only [smul_smul]
  congr 1
  have hfin : Module.finrank ℝ Space = 3 := by simp
  have h3 : l ^ (3 + 2 * α) = l ^ (3 : ℕ) * l ^ (2 * α) := by
    rw [Real.rpow_add hl, ← Real.rpow_natCast]
    norm_num
  rw [hfin, h3, abs_of_pos (by positivity)]
  have : l ^ (3 : ℕ) ≠ 0 := by positivity
  field_simp

theorem fractionalPowerAt_const_smul (α : ℝ) (v : Space → Space) (hv : ContDiff ℝ 2 v) (c : ℝ) (y : Space) :
    fractionalPowerAt α (fun x => c • v x) y = c • fractionalPowerAt α v y := by
  unfold fractionalPowerAt
  have hrem : ∀ z : Space,
      secondOrderRemainder (fun x => c • v x) y z = c • secondOrderRemainder v y z := by
    intro z
    have hd : DifferentiableAt ℝ v y := hv.differentiable (by norm_num) y
    unfold secondOrderRemainder
    have hs : HasFDerivAt (fun x => c • v x) (c • fderiv ℝ v y) y := hd.hasFDerivAt.const_smul c
    rw [hs.fderiv, iteratedFDeriv_const_smul_apply' (i := 2) hv.contDiffAt]
    simp only [smul_apply, smul_sub]
    rw [smul_comm (1 / 2 : ℝ) c]
  simp_rw [hrem, smul_comm _ c]
  rw [integral_smul, smul_comm]

theorem secondOrderRemainder_comp_isometry (v : Space → Space) (hv : ContDiff ℝ 2 v) (R : Space ≃ₗᵢ[ℝ] Space)
    (y z : Space) :
    secondOrderRemainder (fun x => R (v (R.symm x))) y z =
      R (secondOrderRemainder v (R.symm y) (R.symm z)) := by
  have hf : (fun x => R (v (R.symm x))) =
      (R.toContinuousLinearEquiv : Space →L[ℝ] Space) ∘
        (v ∘ (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space)) := rfl
  have hd : DifferentiableAt ℝ v (R.symm y) := hv.differentiable (by norm_num) _
  have h1 : fderiv ℝ (fun x => R (v (R.symm x))) y z = R (fderiv ℝ v (R.symm y) (R.symm z)) := by
    have hs : HasFDerivAt (fun x => R (v (R.symm x)))
        ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp ((fderiv ℝ v (R.symm y)).comp
          (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
      R.toContinuousLinearEquiv.hasFDerivAt.comp y
        (hd.hasFDerivAt.comp y R.symm.toContinuousLinearEquiv.hasFDerivAt)
    rw [hs.fderiv]
    rfl
  have h2 : iteratedFDeriv ℝ 2 (fun x => R (v (R.symm x))) y ![z, z] =
      R (iteratedFDeriv ℝ 2 v (R.symm y) ![R.symm z, R.symm z]) := by
    rw [hf, ContinuousLinearMap.iteratedFDeriv_comp_left _
      ((hv.comp (ContinuousLinearMap.contDiff _)).contDiffAt) le_rfl,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ hv _ le_rfl]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have e : (fun i => R.symm ((![z, z] : Fin 2 → Space) i)) = ![R.symm z, R.symm z] := by
      funext i
      fin_cases i <;> rfl
    show R ((iteratedFDeriv ℝ 2 v (R.symm y)) fun i => R.symm ((![z, z] : Fin 2 → Space) i)) = _
    rw [e]
  unfold secondOrderRemainder
  rw [h1, h2]
  simp [map_sub, map_smul]

theorem fractionalPowerAt_comp_isometry (α : ℝ) (v : Space → Space) (hv : ContDiff ℝ 2 v) (R : Space ≃ₗᵢ[ℝ] Space)
    (y : Space) :
    fractionalPowerAt α (fun x => R (v (R.symm x))) y = R (fractionalPowerAt α v (R.symm y)) := by
  unfold fractionalPowerAt
  obtain ⟨G, hG⟩ : ∃ G : Space → Space,
      G = fun u : Space => ‖u‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v (R.symm y) u := ⟨_, rfl⟩
  have hpt : (fun z : Space =>
      ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (fun x => R (v (R.symm x))) y z) =
        fun z => R (G (R.symm z)) := by
    funext z
    rw [secondOrderRemainder_comp_isometry v hv R y z, hG]
    simp [map_smul]
  have hc : ∀ φ : Space → Space, ∫ z, R (φ z) = R (∫ z, φ z) :=
    fun φ => R.toLinearIsometry.integral_comp_comm φ
  rw [hpt, hc, (R.symm.measurePreserving).integral_comp R.symm.toHomeomorph.measurableEmbedding,
    ← hG, map_smul]

theorem fractionalPowerAt_comp_add (α : ℝ) (v : Space → Space) (c y : Space) :
    fractionalPowerAt α (fun x => v (x + c)) y = fractionalPowerAt α v (y + c) := by
  unfold fractionalPowerAt secondOrderRemainder
  rw [fderiv_comp_add_right, iteratedFDeriv_comp_add_right]
  simp only [add_right_comm y]

end FracInternal

open FracInternal in
theorem covariance : CovarianceStatement := fun α v hv =>
  ⟨fun l hl y => fractionalPowerAt_comp_smul α v hv l hl y, fun c y => fractionalPowerAt_const_smul α v hv c y,
    fun R y => fractionalPowerAt_comp_isometry α v hv R y, fun c y => fractionalPowerAt_comp_add α v c y⟩

theorem additivity : AdditivityStatement := by
  intro α v w x hv hw hdv hdw hcv hcw
  unfold fractionalPowerAt
  have hrem : ∀ z : Space,
      secondOrderRemainder (v + w) x z = secondOrderRemainder v x z + secondOrderRemainder w x z := by
    intro z
    unfold secondOrderRemainder
    rw [fderiv_add hdv hdw, iteratedFDeriv_add_apply (i := 2) hcv hcw]
    simp only [Pi.add_apply, add_apply, smul_add]
    abel
  simp_rw [hrem, smul_add]
  rw [integral_add hv hw, smul_add]

end Breakdown
