import Breakdown.Uniqueness.EnergyDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem ibp_hasCompactSupport_of_vanish {F : Type*} [NormedAddCommGroup F] {φ : Space → ℝ}
    {f : Space → F} (hφc : HasCompactSupport φ) (h : ∀ x, x ∉ tsupport φ → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro hφc h

private theorem ibp_integrable_of_vanish {F : Type*} [NormedAddCommGroup F] {φ : Space → ℝ}
    {f : Space → F} (hφc : HasCompactSupport φ) (hf : Continuous f)
    (h : ∀ x, x ∉ tsupport φ → f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (ibp_hasCompactSupport_of_vanish hφc h)

private theorem ibp_iteratedFDeriv_out {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} {x : Space} (n : ℕ) (hx : x ∉ tsupport f) : iteratedFDeriv ℝ n f x = 0 := by
  by_contra h
  exact hx (support_iteratedFDeriv_subset n h)

private theorem ibp_integral_fderiv_eq_zero {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (a : Space) : ∫ x, fderiv ℝ h x a = 0 := by
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℝ)) (g := h) (v := a) ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · simp
  · simp only [one_mul]
    exact ((hh.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L a) (by simp))
  · simpa using hh.continuous.integrable_of_hasCompactSupport hc
  · intro x _
    exact differentiableAt_const _
  · intro x _
    exact (hh.differentiable (by simp)) x

private theorem ibp_contDiff_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) (e : Space) : ContDiff ℝ ∞ (fun y => fderiv ℝ f y e) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem ibp_fderiv_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) (x e : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y e) x e = iteratedFDeriv ℝ 2 f x ![e, e] := by
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x) (differentiableAt_const e)]
  simp

private theorem ibp_sum_coord (y : Space) : ∑ i, y i • unitVector i = y := by
  simpa [unitVector] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y

private def sspFlux (φ : Space → ℝ) (w : Space → Space) (i : Fin 3) (y : Space) : ℝ :=
  φ y * inner ℝ (w y) (fderiv ℝ w y (unitVector i)) - 1 / 2 * (‖w y‖ ^ 2 * fderiv ℝ φ y (unitVector i))

private theorem ibp_sspFlux_smooth {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (i : Fin 3) : ContDiff ℝ ∞ (sspFlux φ w i) :=
  (hφ.mul (hw.inner ℝ (ibp_contDiff_fderiv_apply hw _))).sub
    (contDiff_const.mul ((hw.norm_sq ℝ).mul (ibp_contDiff_fderiv_apply hφ _)))

private theorem ibp_sspFlux_deriv {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (i : Fin 3) (x : Space) :
    fderiv ℝ (sspFlux φ w i) x (unitVector i)
      = φ x * ‖fderiv ℝ w x (unitVector i)‖ ^ 2
        + φ x * inner ℝ (w x) (iteratedFDeriv ℝ 2 w x ![unitVector i, unitVector i])
        - 1 / 2 * (‖w x‖ ^ 2 * iteratedFDeriv ℝ 2 φ x ![unitVector i, unitVector i]) := by
  have hφ' := (hφ.differentiable (by simp) x).hasFDerivAt
  have hw' := (hw.differentiable (by simp) x).hasFDerivAt
  have hA' := ((ibp_contDiff_fderiv_apply hw (unitVector i)).differentiable (by simp) x).hasFDerivAt
  have hB' := ((ibp_contDiff_fderiv_apply hφ (unitVector i)).differentiable (by simp) x).hasFDerivAt
  have H : HasFDerivAt (sspFlux φ w i) _ x :=
    (hφ'.mul (hw'.inner ℝ hA')).sub ((hw'.norm_sq.mul hB').const_mul (1 / 2 : ℝ))
  rw [H.fderiv, ← ibp_fderiv_fderiv_apply hw, ← ibp_fderiv_fderiv_apply hφ]
  simp [fderivInnerCLM_apply]
  ring

private theorem ibp_ssp_pointwise {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space) :
    ∑ i, fderiv ℝ (sspFlux φ w i) x (unitVector i)
      = φ x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2 + φ x * inner ℝ (w x) (sumSecondPartialsAt w x)
        - 1 / 2 * (‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials φ x) := by
  simp only [ibp_sspFlux_deriv hφ hw, sumSecondPartialsAt, FundSol.scalarSumSecondPartials, FundSol.secondPartial,
    inner_sum, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem ibp_continuous_sumSecondPartialsAt {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    Continuous (sumSecondPartialsAt w) := by
  have e : sumSecondPartialsAt w = fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (unitVector i)) x (unitVector i) := by
    funext x
    simp [sumSecondPartialsAt, ibp_fderiv_fderiv_apply hw]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((ibp_contDiff_fderiv_apply hw _).continuous_fderiv (by simp)).clm_apply continuous_const

private theorem ibp_continuous_scalarSumSecondPartials {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (FundSol.scalarSumSecondPartials φ) := by
  have e : FundSol.scalarSumSecondPartials φ = fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (unitVector i)) x (unitVector i) := by
    funext x
    simp [FundSol.scalarSumSecondPartials, FundSol.secondPartial, ibp_fderiv_fderiv_apply hφ]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((ibp_contDiff_fderiv_apply hφ _).continuous_fderiv (by simp)).clm_apply continuous_const

private theorem ibp_integral_sum_fderiv_eq_zero {h : Fin 3 → Space → ℝ}
    (hs : ∀ i, ContDiff ℝ ∞ (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    ∫ x, ∑ i, fderiv ℝ (h i) x (unitVector i) = 0 := by
  have hint : ∀ i, Integrable (fun x => fderiv ℝ (h i) x (unitVector i)) := fun i =>
    (((hs i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (((hc i).fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) (by simp))
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp [ibp_integral_fderiv_eq_zero (hs _) (hc _)]

theorem integral_mul_inner_sumSecondPartialsAt {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w) :
    ∫ x, φ x * inner ℝ (w x) (sumSecondPartialsAt w x) =
      -(∫ x, φ x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2)
        + (1 / 2) * ∫ x, ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials φ x := by
  have hsum := ibp_integral_sum_fderiv_eq_zero (h := sspFlux φ w) (ibp_sspFlux_smooth hφ hw)
    (fun i => ibp_hasCompactSupport_of_vanish hφc (fun x hx => by
      simp [sspFlux, image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx]))
  simp only [ibp_ssp_pointwise hφ hw] at hsum
  have hP : Integrable (fun x => φ x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2) :=
    ibp_integrable_of_vanish hφc (hφ.continuous.mul (continuous_finsetSum _ fun i _ =>
      ((ibp_contDiff_fderiv_apply hw _).continuous.norm.pow 2)))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hQ : Integrable (fun x => φ x * inner ℝ (w x) (sumSecondPartialsAt w x)) :=
    ibp_integrable_of_vanish hφc (hφ.continuous.mul (hw.continuous.inner (ibp_continuous_sumSecondPartialsAt hw)))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hR : Integrable (fun x => ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials φ x) :=
    ibp_integrable_of_vanish hφc ((hw.continuous.norm.pow 2).mul (ibp_continuous_scalarSumSecondPartials hφ))
      (fun x hx => by
        simp [FundSol.scalarSumSecondPartials, FundSol.secondPartial, ibp_iteratedFDeriv_out 2 hx])
  have hPQ : Integrable (fun x => φ x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2
      + φ x * inner ℝ (w x) (sumSecondPartialsAt w x)) := hP.add hQ
  rw [integral_sub hPQ (hR.const_mul _), integral_add hP hQ, integral_const_mul] at hsum
  linarith

private def transFlux (φ : Space → ℝ) (w v : Space → Space) (i : Fin 3) (y : Space) : ℝ :=
  φ y * ‖w y‖ ^ 2 * v y i

private theorem ibp_transFlux_smooth {φ : Space → ℝ} {w v : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    ContDiff ℝ ∞ (transFlux φ w v i) :=
  (hφ.mul (hw.norm_sq ℝ)).mul (by exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hv)

private theorem ibp_transFlux_deriv {φ : Space → ℝ} {w v : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) (i : Fin 3) (x e : Space) :
    fderiv ℝ (transFlux φ w v i) x e
      = φ x * ‖w x‖ ^ 2 * (fderiv ℝ v x e) i
        + v x i * (φ x * (2 * inner ℝ (w x) (fderiv ℝ w x e)) + ‖w x‖ ^ 2 * fderiv ℝ φ x e) := by
  have hφ' := (hφ.differentiable (by simp) x).hasFDerivAt
  have hw' := (hw.differentiable (by simp) x).hasFDerivAt
  have hv' := (hv.differentiable (by simp) x).hasFDerivAt
  have hvi : HasFDerivAt (fun y => v y i) ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ v x)) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x hv'
  have H : HasFDerivAt (transFlux φ w v i) _ x := (hφ'.mul hw'.norm_sq).mul hvi
  rw [H.fderiv]
  simp
  ring

private theorem ibp_trans_pointwise {φ : Space → ℝ} {w v : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) (x : Space) :
    ∑ i, fderiv ℝ (transFlux φ w v i) x (unitVector i)
      = φ x * ‖w x‖ ^ 2 * divergenceAt v x
        + (2 * (φ x * inner ℝ (w x) (fderiv ℝ w x (v x)))
          + ‖w x‖ ^ 2 * inner ℝ (v x) (gradientAt φ x)) := by
  have e1 : fderiv ℝ w x (v x) = ∑ i, v x i • fderiv ℝ w x (unitVector i) := by
    conv_lhs => rw [← ibp_sum_coord (v x)]
    simp [map_sum, map_smul]
  have e2 : inner ℝ (v x) (gradientAt φ x) = ∑ i, v x i * fderiv ℝ φ x (unitVector i) := by
    simp only [gradientAt, inner_sum, inner_smul_right, unitVector, EuclideanSpace.inner_single_right]
    exact Finset.sum_congr rfl fun i _ => by simp; ring
  rw [e1, e2, divergenceAt, inner_sum]
  simp only [inner_smul_right, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [ibp_transFlux_deriv hφ hw hv]; ring

theorem integral_mul_inner_fderiv_transport {φ : Space → ℝ} {v w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ x, divergenceAt v x = 0) (hw : ContDiff ℝ ∞ w) :
    ∫ x, φ x * inner ℝ (w x) (fderiv ℝ w x (v x)) =
      -(1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (v x) (gradientAt φ x) := by
  have hsum := ibp_integral_sum_fderiv_eq_zero (h := transFlux φ w v) (ibp_transFlux_smooth hφ hw hv)
    (fun i => ibp_hasCompactSupport_of_vanish hφc (fun x hx => by
      simp [transFlux, image_eq_zero_of_notMem_tsupport hx]))
  simp only [ibp_trans_pointwise hφ hw hv, hdiv, mul_zero, zero_add] at hsum
  have hP : Integrable (fun x => φ x * inner ℝ (w x) (fderiv ℝ w x (v x))) :=
    ibp_integrable_of_vanish hφc (hφ.continuous.mul (hw.continuous.inner
      ((hw.continuous_fderiv (by simp)).clm_apply hv.continuous)))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hG : Continuous (gradientAt φ) := continuous_finsetSum _ fun i _ =>
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hR : Integrable (fun x => ‖w x‖ ^ 2 * inner ℝ (v x) (gradientAt φ x)) :=
    ibp_integrable_of_vanish hφc ((hw.continuous.norm.pow 2).mul (hv.continuous.inner hG))
      (fun x hx => by simp [gradientAt, fderiv_of_notMem_tsupport ℝ hx])
  have hP2 : Integrable (fun x => 2 * (φ x * inner ℝ (w x) (fderiv ℝ w x (v x)))) := hP.const_mul _
  rw [integral_add hP2 hR, integral_const_mul] at hsum
  linarith

end Breakdown
