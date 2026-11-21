import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.WeakInX

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem fderiv_spaceScale {f : Space → Space} (hf : Differentiable ℝ f) (b : ℝ)
    (y v : Space) : fderiv ℝ (spaceScale b f) y v = b • fderiv ℝ f (b • y) v := by
  have h : HasFDerivAt (fun z : Space => f (b • z))
      ((fderiv ℝ f (b • y)).comp (b • ContinuousLinearMap.id ℝ Space)) y :=
    (hf (b • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul b)
  rw [show spaceScale b f = fun z : Space => f (b • z) from rfl, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, map_smul]

private theorem contDiff_spaceScale {f : Space → Space} (hf : ContDiff ℝ ∞ f) (b : ℝ) :
    ContDiff ℝ ∞ (spaceScale b f) :=
  hf.comp (contDiff_id.const_smul b)

private theorem partialField_spaceScale {f : Space → Space} (hf : Differentiable ℝ f) (b : ℝ)
    (j : Fin 3) : partialField (spaceScale b f) j = b • spaceScale b (partialField f j) := by
  funext y
  simp only [partialField, fderiv_spaceScale hf, Pi.smul_apply, spaceScale]

private theorem partialField_smul {g : Space → Space} (hg : Differentiable ℝ g) (b : ℝ)
    (j : Fin 3) : partialField (b • g) j = b • partialField g j := by
  funext y
  have e : (b • g) = fun z => b • g z := rfl
  have hd : fderiv ℝ (fun z => b • g z) y = b • fderiv ℝ g y :=
    ((hg y).hasFDerivAt.const_smul b).fderiv
  simp only [partialField, e, hd, Pi.smul_apply, FunLike.coe_smul]

private theorem negSsp_spaceScale {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (b : ℝ) :
    negSsp (spaceScale b φ) = b ^ 2 • spaceScale b (negSsp φ) := by
  have hd : ∀ {g : Space → Space}, ContDiff ℝ ∞ g → Differentiable ℝ g :=
    fun hg => hg.differentiable (by simp)
  have hP : ∀ j, ContDiff ℝ ∞ (partialField φ j) := Internal.WeakInX.smooth_partial hφ
  have inner_step : ∀ j, partialField (partialField (spaceScale b φ) j) j =
      (b * b) • spaceScale b (partialField (partialField φ j) j) := by
    intro j
    rw [partialField_spaceScale (hd hφ), partialField_smul (hd (contDiff_spaceScale (hP j) b)),
      partialField_spaceScale (hd (hP j)), smul_smul]
  rw [Internal.WeakInX.negSsp_eq (contDiff_spaceScale hφ b), Internal.WeakInX.negSsp_eq hφ]
  funext y
  simp only [inner_step, Pi.smul_apply, spaceScale, Finset.smul_sum, smul_neg, pow_two]

private theorem isTestField_spaceScale {φ : Space → Space} (hφ : IsTestField φ) {b : ℝ}
    (hb : b ≠ 0) : IsTestField (spaceScale b φ) := by
  refine ⟨contDiff_spaceScale hφ.1 b, hφ.2.1.comp_smul hb, fun y => ?_⟩
  have hdf : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have h0 := hφ.2.2 (b • y)
  simp only [divergenceAt] at h0 ⊢
  simp only [fderiv_spaceScale hdf, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, h0,
    mul_zero]

theorem pairingDilate_holds : PairingDilate := by
  intro hP μ hμ x φ hφ
  have hs0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hb : (Real.sqrt μ)⁻¹ ≠ 0 := inv_ne_zero hs0.ne'
  rw [hP _ _ hφ, hP _ _ (isTestField_spaceScale hφ hb), negSsp_spaceScale hφ.1]
  have e1 : ∫ y, inner ℝ ((velocity (dilX μ x) : Space → Space) y) (negSsp φ y) =
      Real.sqrt μ * ∫ y, inner ℝ ((velocity x : Space → Space) (Real.sqrt μ • y)) (negSsp φ y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ((velocityCov_holds.2 μ hμ x).mono fun y hy => ?_)
    simp only [hy, dilateField, real_inner_smul_left]
  have h := Measure.integral_comp_smul (μ := (volume : Measure Space))
    (fun z => inner ℝ ((velocity x : Space → Space) z)
      (((Real.sqrt μ)⁻¹ ^ 2 • spaceScale (Real.sqrt μ)⁻¹ (negSsp φ)) z)) (Real.sqrt μ)
  have h2 : ∫ y, inner ℝ ((velocity x : Space → Space) (Real.sqrt μ • y))
      (((Real.sqrt μ)⁻¹ ^ 2 • spaceScale (Real.sqrt μ)⁻¹ (negSsp φ)) (Real.sqrt μ • y)) =
      (Real.sqrt μ)⁻¹ ^ 2 *
        ∫ y, inner ℝ ((velocity x : Space → Space) (Real.sqrt μ • y)) (negSsp φ y) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [Pi.smul_apply, spaceScale, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul,
      real_inner_smul_right]
  rw [h2, finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul] at h
  have h3 : ∫ z, inner ℝ ((velocity x : Space → Space) z)
      (((Real.sqrt μ)⁻¹ ^ 2 • spaceScale (Real.sqrt μ)⁻¹ (negSsp φ)) z) =
      Real.sqrt μ ^ 3 * ((Real.sqrt μ)⁻¹ ^ 2 *
        ∫ y, inner ℝ ((velocity x : Space → Space) (Real.sqrt μ • y)) (negSsp φ y)) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [e1, h3]
  field_simp

end Breakdown.WeakProfile
