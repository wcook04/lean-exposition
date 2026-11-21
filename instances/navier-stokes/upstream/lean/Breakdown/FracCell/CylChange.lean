import Breakdown.FracCell.StCylModeWeak
import Breakdown.FracCell.CylIntegral

open scoped ContDiff
open MeasureTheory Real Set

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert CellAnalysis Breakdown.CellCert.Spectral.Internal.CylIntegral

theorem cylChange : CylChangeStatement := by
  intro h hh
  set g : (ℝ × ℝ) × ℝ → ℂ := fun w => h (toSpace w) with hg_def
  have hg : Integrable g := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hh
  have hchange : ∫ w, g w = ∫ x in cylMap.target, (x.1.1 : ℂ) * g (cylMap.symm x) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set image_ae,
      integral_image_eq_integral_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
        (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g]
    refine setIntegral_congr_fun cylMap.open_target.measurableSet fun x hx => ?_
    simp only [abs_det_eq hx, Complex.real_smul]
  have hH : IntegrableOn (fun x : (ℝ × ℝ) × ℝ => (x.1.1 : ℂ) * g (cylMap.symm x)) cylMap.target := by
    have h1 : IntegrableOn g (cylMap.symm '' cylMap.target) :=
      (integrableOn_univ.mpr hg).congr_set_ae image_ae
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
        (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g] at h1
    refine h1.congr_fun (fun x hx => ?_) cylMap.open_target.measurableSet
    simp only [abs_det_eq hx, Complex.real_smul]
  set H : (ℝ × ℝ) × ℝ → ℂ := fun x => (x.1.1 : ℂ) * g (cylMap.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapEquiv) ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π) := by
    rw [← swapEquiv_preimage]
    exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  calc ∫ y, h y = ∫ w, g w := (toSpace_mp.integral_comp' h).symm
    _ = ∫ x in cylMap.target, H x := hchange
    _ = ∫ x in swapEquiv ⁻¹' cylMap.target, H (swapEquiv x) :=
        (swapEquiv_mp.setIntegral_preimage_emb swapEquiv.measurableEmbedding H _).symm
    _ = ∫ x in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π, (H ∘ swapEquiv) x := by
        rw [swapEquiv_preimage]; rfl
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∫ θ in Ioo (-π) π, (H ∘ swapEquiv) (q, θ) :=
        setIntegral_prod _ hHσ
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          (q.1 : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), h (cylPoint q.1 θ q.2) := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun q _ => ?_
        have hper : Function.Periodic (fun θ => h (cylPoint q.1 θ q.2)) (2 * π) := fun θ => by
          simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
        have hsh := hper.intervalIntegral_add_eq 0 (-π)
        rw [zero_add, show -π + 2 * π = π by ring] at hsh
        rw [hsh, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo,
          ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        obtain ⟨r, z⟩ := q
        simp only [Function.comp_apply, swapEquiv_apply, hH_def, hg_def]
        rw [show cylPoint r θ z = toSpace ((r * Real.cos θ, r * Real.sin θ), z) from (toSpace_apply r θ z).symm]
        rfl

end Breakdown.CellCert.CellFormula
