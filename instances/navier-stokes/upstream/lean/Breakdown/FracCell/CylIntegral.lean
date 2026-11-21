import Breakdown.FracCell.SpectralBlocksMode
import Mathlib

open MeasureTheory Real Set

noncomputable section

namespace Breakdown.CellCert.Spectral

namespace Internal.CylIntegral

scoped instance : Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

def toSpace : (ℝ × ℝ) × ℝ ≃ᵐ Space :=
  ((MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm).trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem toSpace_mp : MeasurePreserving toSpace volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm.comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      (((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm).comp
        Measure.measurePreserving_swap))

theorem toSpace_apply (r θ z : ℝ) :
    toSpace ((r * Real.cos θ, r * Real.sin θ), z) = cylPoint r θ z := by
  ext i
  fin_cases i <;> simp [cylPoint] <;> rfl

def cylMap : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ) :=
  polarCoord.prod (OpenPartialHomeomorph.refl ℝ)

def cylDeriv (x : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ →L[ℝ] (ℝ × ℝ) × ℝ :=
  (fderivPolarCoordSymm x.1).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem hasDeriv (x : (ℝ × ℝ) × ℝ) : HasFDerivAt cylMap.symm (cylDeriv x) x :=
  (hasFDerivAt_polarCoord_symm x.1).prodMap x (hasFDerivAt_id x.2)

theorem det_cylDeriv (x : (ℝ × ℝ) × ℝ) : (cylDeriv x).det = x.1.1 := by
  have : (cylDeriv x).toLinearMap =
      LinearMap.prodMap (fderivPolarCoordSymm x.1).toLinearMap LinearMap.id := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_prodMap, LinearMap.det_id, mul_one,
    ← ContinuousLinearMap.det, det_fderivPolarCoordSymm]

theorem cylMap_target : cylMap.target = polarCoord.target ×ˢ (univ : Set ℝ) := rfl

theorem image_ae : cylMap.symm '' cylMap.target =ᵐ[volume] (univ : Set ((ℝ × ℝ) × ℝ)) := by
  rw [← Set.univ_prod_univ, cylMap.symm_image_target_eq_source]
  exact Measure.set_prod_ae_eq polarCoord_source_ae_eq_univ .rfl

theorem abs_det_eq {x : (ℝ × ℝ) × ℝ} (hx : x ∈ cylMap.target) : |(cylDeriv x).det| = x.1.1 := by
  rw [det_cylDeriv]
  exact abs_of_pos hx.1.1

theorem change (g : (ℝ × ℝ) × ℝ → ℝ) :
    ∫ w, g w = ∫ x in cylMap.target, x.1.1 * g (cylMap.symm x) := by
  rw [← setIntegral_univ, ← setIntegral_congr_set image_ae,
    integral_image_eq_integral_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g]
  refine setIntegral_congr_fun cylMap.open_target.measurableSet fun x hx => ?_
  simp only [smul_eq_mul, abs_det_eq hx]

theorem change_integrable {g : (ℝ × ℝ) × ℝ → ℝ} (hg : Integrable g) :
    IntegrableOn (fun x => x.1.1 * g (cylMap.symm x)) cylMap.target := by
  have h1 : IntegrableOn g (cylMap.symm '' cylMap.target) :=
    (integrableOn_univ.mpr hg).congr_set_ae image_ae
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g] at h1
  refine h1.congr_fun (fun x hx => ?_) cylMap.open_target.measurableSet
  simp only [smul_eq_mul, abs_det_eq hx]

def swapEquiv : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)).trans
    MeasurableEquiv.prodAssoc.symm

theorem swapEquiv_mp : MeasurePreserving swapEquiv volume volume :=
  (measurePreserving_prodAssoc volume volume volume).symm.comp
    (((MeasurePreserving.id volume).prod Measure.measurePreserving_swap).comp
      (measurePreserving_prodAssoc volume volume volume))

theorem swapEquiv_apply (r z θ : ℝ) : swapEquiv ((r, z), θ) = ((r, θ), z) := rfl

theorem swapEquiv_preimage :
    swapEquiv ⁻¹' cylMap.target = (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π := by
  ext ⟨⟨r, z⟩, θ⟩
  simp [swapEquiv_apply, cylMap_target, polarCoord_target]

end Internal.CylIntegral

open Internal.CylIntegral in
theorem cylIntegral : CylStatement := by
  intro f hf
  set g : (ℝ × ℝ) × ℝ → ℝ := fun w => f (toSpace w) with hg_def
  have hg : Integrable g := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hf
  have hH := change_integrable hg
  set H : (ℝ × ℝ) × ℝ → ℝ := fun x => x.1.1 * g (cylMap.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapEquiv) ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π) := by
    rw [← swapEquiv_preimage]
    exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  calc ∫ y, f y = ∫ w, g w := (toSpace_mp.integral_comp' f).symm
    _ = ∫ x in cylMap.target, H x := change g
    _ = ∫ x in swapEquiv ⁻¹' cylMap.target, H (swapEquiv x) :=
        (swapEquiv_mp.setIntegral_preimage_emb swapEquiv.measurableEmbedding H _).symm
    _ = ∫ x in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π, (H ∘ swapEquiv) x := by
        rw [swapEquiv_preimage]; rfl
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∫ θ in Ioo (-π) π, (H ∘ swapEquiv) (q, θ) :=
        setIntegral_prod _ hHσ
    _ = ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          q.1 * ∫ θ in (-Real.pi)..Real.pi, f (cylPoint q.1 θ q.2) := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun q _ => ?_
        rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo,
          ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        obtain ⟨r, z⟩ := q
        simp only [Function.comp_apply, swapEquiv_apply, hH_def, hg_def]
        rw [← toSpace_apply]
        rfl

end Breakdown.CellCert.Spectral
