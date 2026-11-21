import Breakdown.Cert.StConclusion
import Mathlib

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Internal.Rescale

def timeScale (c : ℝ) (hc : c ≠ 0) : ℝ × Space ≃ₜ ℝ × Space :=
  (Homeomorph.mulLeft₀ c hc).prodCongr (Homeomorph.refl Space)

theorem timeScale_apply (c : ℝ) (hc : c ≠ 0) (z : ℝ × Space) :
    timeScale c hc z = (c * z.1, z.2) := rfl

theorem measurableEmbedding_timeScale (c : ℝ) (hc : c ≠ 0) :
    MeasurableEmbedding (fun z : ℝ × Space => (c * z.1, z.2)) :=
  (timeScale c hc).toMeasurableEquiv.measurableEmbedding

theorem map_timeScale (c : ℝ) (hc : c ≠ 0) :
    Measure.map (fun z : ℝ × Space => (c * z.1, z.2)) volume
      = ENNReal.ofReal |c⁻¹| • (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  have h : (fun z : ℝ × Space => (c * z.1, z.2)) = Prod.map (c * ·) id := rfl
  rw [h, ← Measure.map_prod_map _ _ (measurable_const_mul c) measurable_id,
    Real.map_volume_mul_left hc, Measure.map_id, Measure.prod_smul_left]

theorem quasiMeasurePreserving_timeScale (c : ℝ) (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun z : ℝ × Space => (c * z.1, z.2)) volume volume :=
  ⟨(measurableEmbedding_timeScale c hc).measurable, by
    rw [map_timeScale c hc]; exact Measure.smul_absolutelyContinuous⟩

theorem quasiMeasurePreserving_mul (c : ℝ) (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun s : ℝ => c * s) volume volume :=
  ⟨measurable_const_mul c, by
    rw [Real.map_volume_mul_left hc]; exact Measure.smul_absolutelyContinuous⟩

theorem integrable_timeScale_iff (c : ℝ) (hc : c ≠ 0) (f : ℝ × Space → ℝ) :
    Integrable (fun z : ℝ × Space => f (c * z.1, z.2)) ↔ Integrable f := by
  have h := (measurableEmbedding_timeScale c hc).integrable_map_iff (g := f) (μ := volume)
  rw [map_timeScale c hc, integrable_smul_measure (by simp [hc]) ENNReal.ofReal_ne_top] at h
  exact h.symm

theorem integral_timeScale (c : ℝ) (hc : c ≠ 0) (f : ℝ × Space → ℝ) :
    ∫ z : ℝ × Space, f (c * z.1, z.2) = |c⁻¹| * ∫ z, f z := by
  rw [← (measurableEmbedding_timeScale c hc).integral_map, map_timeScale c hc,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem setLIntegral_Icc_inv_mul {P : ℝ} (hP : 0 < P) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Icc 0 P, F (P⁻¹ * s) = ENNReal.ofReal P * ∫⁻ σ in Set.Icc 0 1, F σ := by
  have hP0 : P⁻¹ ≠ 0 := inv_ne_zero hP.ne'
  have he : MeasurableEmbedding (fun s : ℝ => P⁻¹ * s) :=
    (Homeomorph.mulLeft₀ P⁻¹ hP0).toMeasurableEquiv.measurableEmbedding
  have hpre : (fun s : ℝ => P⁻¹ * s) ⁻¹' Set.Icc 0 1 = Set.Icc 0 P := by
    rw [Set.preimage_const_mul_Icc₀ _ _ (inv_pos.2 hP)]
    simp
  rw [← hpre, ← he.lintegral_map, ← he.restrict_map, Real.map_volume_mul_left hP0,
    Measure.restrict_smul, lintegral_smul_measure, inv_inv, abs_of_pos hP, smul_eq_mul]

theorem weakSimilarityIntegrand_eq {P : ℝ} (hP : P ≠ 0) (W : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (φ : ℝ → Space → Space) (z : ℝ × Space) :
    weakSimilarityIntegrand (fun s y => W (P⁻¹ * s) y) (fun s y => G (P⁻¹ * s) y) φ z
      = sigmaSimilarityIntegrand P W G (fun σ y => φ (P * σ) y) (P⁻¹ * z.1, z.2) := by
  have hs : P * (P⁻¹ * z.1) = z.1 := by field_simp
  have hd : deriv (fun σ => φ (P * σ) z.2) (P⁻¹ * z.1) = P • deriv (fun t => φ t z.2) z.1 := by
    have h := deriv_comp_mul_left P (fun t => φ t z.2) (P⁻¹ * z.1)
    rw [hs] at h
    exact h
  have hφ : (fun y => φ (P * (P⁻¹ * z.1)) y) = φ z.1 := by rw [hs]
  simp only [weakSimilarityIntegrand, sigmaSimilarityIntegrand, hd, hφ, inner_smul_right]
  field_simp

theorem isSpaceTimeTestField_comp {P : ℝ} (hP : P ≠ 0) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) : IsSpaceTimeTestField (fun σ y => φ (P * σ) y) := by
  refine ⟨?_, ?_, fun s y => hφ.2.2 (P * s) y⟩
  · exact hφ.1.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)
  · exact hφ.2.1.comp_homeomorph (timeScale P hP)

end Internal.Rescale

open Internal.Rescale in
theorem weakPeriodicSimilarityProfileExists_of_sigma {P C : ℝ} {W : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsSigmaProfile P W G H C) : WeakPeriodicSimilarityProfileExists := by
  have hP := h.period_pos
  have hP0 : P ≠ 0 := hP.ne'
  have hPi : P⁻¹ ≠ 0 := inv_ne_zero hP0
  refine ⟨fun s y => W (P⁻¹ * s) y, fun s y => G (P⁻¹ * s) y, fun s y => H (P⁻¹ * s) y, P,
    LinearIsometryEquiv.refl ℝ Space, C, hP, ?_, ?_, ?_, ?_, fun s => h.weak_gradient _,
    ?_, fun s => h.divergence_free _, fun s => h.sixth_power _, fun s => h.gradient_bound _,
    ?_, ?_, ?_⟩
  · exact h.measurable_velocity.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · exact h.measurable_gradient.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · exact h.measurable_secondDeriv.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · intro s y
    have hs : P⁻¹ * (s + P) = P⁻¹ * s + 1 := by rw [mul_add, inv_mul_cancel₀ hP0]
    simp only [hs, h.periodic]
    rfl
  · exact (quasiMeasurePreserving_mul _ hPi).ae h.weak_secondDeriv
  · rw [setLIntegral_Icc_inv_mul hP (fun σ => ∫⁻ y, ENNReal.ofReal (‖H σ y‖ ^ 2))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.secondDeriv_finite
  · intro φ hφ
    have hψ := h.weak_equation _ (isSpaceTimeTestField_comp hP0 hφ)
    have hfun : weakSimilarityIntegrand (fun s y => W (P⁻¹ * s) y) (fun s y => G (P⁻¹ * s) y) φ
        = fun z => sigmaSimilarityIntegrand P W G (fun σ y => φ (P * σ) y) (P⁻¹ * z.1, z.2) :=
      funext (weakSimilarityIntegrand_eq hP0 W G φ)
    rw [hfun, integrable_timeScale_iff _ hPi, integral_timeScale _ hPi, hψ.2, mul_zero]
    exact ⟨hψ.1, rfl⟩
  · intro hW
    apply h.nonzero
    filter_upwards [(quasiMeasurePreserving_timeScale P hP0).ae hW] with z hz
    simpa [inv_mul_cancel_left₀ hP0] using hz

end Breakdown
