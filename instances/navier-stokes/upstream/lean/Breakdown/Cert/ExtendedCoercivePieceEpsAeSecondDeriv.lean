import Breakdown.Cert.ExtendedCoercivePieceEpsSlope
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Measurable

open scoped ContDiff NNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakGradientSlope

variable {u : Space → Space} {g : Space → (Space →L[ℝ] Space)} {C : ℝ≥0}

theorem coord_slopeBound (hu : LipschitzWith C u) (k : Fin 3) : LipschitzWith C (fun y => u y k) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := PiLp.norm_apply_le (u x - u y) k
  rw [Real.dist_eq]
  rw [PiLp.sub_apply, Real.norm_eq_abs] at h
  exact h.trans (by rw [← dist_eq_norm]; exact hu.dist_le_mul x y)

theorem column_locallyIntegrable (hg : IsWeakGradient u g) (i : Fin 3) :
    LocallyIntegrable (fun x => g x (unitVector i)) := by
  refine hg.2.1.mono ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
    hg.2.1.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  refine (ContinuousLinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  have h1 : ‖unitVector i‖ = 1 := by simp [unitVector]
  rw [h1, mul_one]

theorem integral_lineDeriv_coord (hu : LipschitzWith C u) (hg : IsWeakGradient u g) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (i k : Fin 3) :
    ∫ x, φ x • lineDeriv ℝ (fun y => u y k) x (unitVector i) = ∫ x, φ x • g x (unitVector i) k := by
  obtain ⟨Cφ, hCφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφs hφ (by simp)
  have e1 := (coord_slopeBound hu k).integral_lineDeriv_mul_eq (μ := volume) hCφ hφs (unitVector i)
  have hφd : ∀ x, lineDeriv ℝ φ x (-unitVector i) = -(fderiv ℝ φ x (unitVector i)) := fun x => by
    rw [(hφ.differentiable (by simp) x).lineDeriv_eq_fderiv, map_neg]
  have hw := hg.2.2 φ ⟨hφ, hφs⟩ i
  have hsd : HasCompactSupport (fun x => fderiv ℝ φ x (unitVector i)) := by
    refine (hφs.fderiv (𝕜 := ℝ)).mono fun x hx => ?_
    contrapose! hx
    rw [Function.notMem_support] at hx ⊢
    simp [hx]
  have I1 : Integrable (fun x => φ x • g x (unitVector i)) :=
    (column_locallyIntegrable hg i).integrable_smul_left_of_hasCompactSupport hφ.continuous hφs
  have I2 : Integrable (fun x => fderiv ℝ φ x (unitVector i) • u x) :=
    hg.1.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) hsd
  have hk := congrArg (EuclideanSpace.proj k : Space →L[ℝ] ℝ) hw
  rw [← ContinuousLinearMap.integral_comp_comm _ I1, map_neg,
    ← ContinuousLinearMap.integral_comp_comm _ I2] at hk
  have hk2 : ∫ x, φ x * g x (unitVector i) k = -∫ x, fderiv ℝ φ x (unitVector i) * u x k := by
    simpa using hk
  simp only [smul_eq_mul]
  rw [hk2]
  calc ∫ x, φ x * lineDeriv ℝ (fun y => u y k) x (unitVector i)
      = ∫ x, lineDeriv ℝ (fun y => u y k) x (unitVector i) * φ x := by simp_rw [mul_comm]
    _ = ∫ x, lineDeriv ℝ φ x (-unitVector i) * u x k := e1
    _ = -∫ x, fderiv ℝ φ x (unitVector i) * u x k := by
        rw [← integral_neg]
        simp_rw [hφd, neg_mul]

theorem ae_hasFDerivAt_of_weakGradient (hu : LipschitzWith C u) (hg : IsWeakGradient u g) :
    ∀ᵐ x, HasFDerivAt u (g x) x := by
  have hcoord : ∀ i k : Fin 3, ∀ᵐ x,
      lineDeriv ℝ (fun y => u y k) x (unitVector i) = g x (unitVector i) k := by
    intro i k
    refine ae_eq_of_integral_contDiff_smul_eq ?_ ?_ fun φ hφ hφs =>
      integral_lineDeriv_coord hu hg φ hφ hφs i k
    · refine (locallyIntegrable_const ((C : ℝ) * ‖unitVector i‖)).mono
        (measurable_lineDeriv (coord_slopeBound hu k).continuous).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      refine (norm_lineDeriv_le_of_lipschitz ℝ (coord_slopeBound hu k)).trans (le_of_eq ?_)
      exact (Real.norm_of_nonneg (mul_nonneg C.2 (norm_nonneg _))).symm
    · refine (column_locallyIntegrable hg i).mono
        ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
          (column_locallyIntegrable hg i).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      exact PiLp.norm_apply_le _ k
  filter_upwards [hu.ae_differentiableAt, ae_all_iff.2 fun i => ae_all_iff.2 fun k => hcoord i k]
    with x hd hc
  have e : fderiv ℝ u x = g x := by
    refine ContinuousLinearMap.coe_injective
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => ?_)
    ext k
    have hf : HasFDerivAt (fun y => u y k) ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ u x)) x :=
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt
    have hk : lineDeriv ℝ (fun y => u y k) x (unitVector i) = fderiv ℝ u x (unitVector i) k := by
      rw [hf.differentiableAt.lineDeriv_eq_fderiv, hf.fderiv]
      simp
    have hci := hc i k
    simp only [EuclideanSpace.basisFun_toBasis, ContinuousLinearMap.coe_coe]
    have hb : (PiLp.basisFun 2 ℝ (Fin 3)) i = unitVector i := by
      ext j
      simp [unitVector]
    rw [hb, ← hci, hk]
  rw [← e]
  exact hd.hasFDerivAt

theorem ae_hasFDerivAt_fderiv {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) : ∀ᵐ y, HasFDerivAt (fderiv ℝ (W σ)) (HW σ y) y := by
  have hcol : ∀ j : Fin 3, ∀ᵐ y, HasFDerivAt (fun x => fderiv ℝ (W σ) x (unitVector j))
      ((HW σ y).flip (unitVector j)) y := fun j =>
    ae_hasFDerivAt_of_weakGradient (column_slopeBound hW σ j) (hW.secondDeriv_weak σ j)
  filter_upwards [(fderiv_slopeBound hW σ).ae_differentiableAt, ae_all_iff.2 hcol] with y hd hc
  have e : fderiv ℝ (fderiv ℝ (W σ)) y = HW σ y := by
    ext w : 1
    refine ContinuousLinearMap.coe_injective ((PiLp.basisFun 2 ℝ (Fin 3)).ext fun j => ?_)
    have hb : (PiLp.basisFun 2 ℝ (Fin 3)) j = unitVector j := by
      ext l
      simp [unitVector]
    have h1 : HasFDerivAt (fun x => fderiv ℝ (W σ) x (unitVector j))
        ((ContinuousLinearMap.apply ℝ Space (unitVector j)).comp (fderiv ℝ (fderiv ℝ (W σ)) y)) y :=
      (ContinuousLinearMap.apply ℝ Space (unitVector j)).hasFDerivAt.comp y hd.hasFDerivAt
    have h2 := congrArg (fun L : Space →L[ℝ] Space => L w) ((hc j).unique h1)
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply] at h2
    simp only [ContinuousLinearMap.coe_coe, hb]
    exact h2.symm
  rw [← e]
  exact hd.hasFDerivAt

theorem ae_secondDerivField_eq {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) : ∀ᵐ y, secondDerivField W σ y = HW σ y := by
  filter_upwards [ae_hasFDerivAt_fderiv hW σ] with y hy
  exact hy.fderiv

end Internal.WeakGradientSlope

end CoerciveWeak

end Breakdown
