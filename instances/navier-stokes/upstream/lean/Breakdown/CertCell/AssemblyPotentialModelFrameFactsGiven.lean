import Breakdown.CertCell.AssemblyPotentialModelFrame
import Breakdown.Cert.CoerciveSmoothMuWave

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal Coercive.RotationInternal


theorem ae_first_ne : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬a.1 ≠ 0} = {0} ×ˢ Set.univ := by
    ext a
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem ae_second_ne : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬a.2 ≠ 0} = Set.univ ×ˢ {0} := by
    ext a
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem rect_ac_halfPlane (K : CellBox) (hK : IsCellBox K) :
    volume.restrict K.rect ≪ volume.restrict halfPlane := by
  refine Measure.absolutelyContinuous_of_le (Measure.restrict_mono_ae ?_)
  filter_upwards [ae_first_ne, ae_second_ne] with p h1 h2 hp
  obtain ⟨⟨hr1, _⟩, hz1, _⟩ := hp
  exact ⟨lt_of_le_of_ne (hK.r_order.1.trans hr1) (Ne.symm h1), lt_of_le_of_ne (hK.z_order.1.trans hz1) (Ne.symm h2)⟩

private theorem phase_neg_conj (β : ℤ × ℤ) (τ φ : ℝ) : phase (-β) τ φ = (starRingEnd ℂ) (phase β τ φ) := by
  simp only [phase, waveArg]
  exact Coercive.Internal.MuSmooth.phase_neg β τ φ

private theorem modeSecondDeriv_neg_conj (β : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ)
    (y : Space) (x : Fin 3 × Fin 3 × Fin 3) : modeSecondDeriv (-β) H σ y x = (starRingEnd ℂ) (modeSecondDeriv β H σ y x) := by
  unfold modeSecondDeriv
  exact Coercive.Internal.MuSmooth.modeAverage_neg _ _ _

private theorem decay_nonneg {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) : 0 ≤ B := by
  have h := (hW.decay 0 0).1
  rw [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem givenExpansion : GivenExpansionStatement := by
  intro S W HW B hE hW K hK
  have hB := decay_nonneg hW
  have hgper : IsTimePeriodic (gradField W) := by
    intro σ y
    have e : W (σ + 1) = W σ := funext (hW.periodic σ)
    simp only [gradField, e]
  have hcont := continuous_gradField hW.smooth
  refine ⟨fun y τ φ a b => ?_, ?_⟩
  · have hint : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
        axialRot (-θ.2) (gradField W (τ + θ.1) (axialRot θ.2 (axialRot φ y)) (axialRot θ.2 (unitVector x.2))) x.1)
        boxMeasure := by
      intro τ φ x
      have hc : Continuous (fun θ : ℝ × ℝ => gradField W (τ + θ.1) (axialRot θ.2 (axialRot φ y))) := by
        refine hcont.comp (f := fun θ : ℝ × ℝ => ((τ + θ.1, axialRot θ.2 (axialRot φ y)) : ℝ × Space)) ?_
        unfold axialRot
        fun_prop
      have h := integrable_shift_grad _ hc.aestronglyMeasurable B (fun θ => ?_) (0, 0) x
      · simpa only [add_zero] using h
      · refine (hW.decay _ _).2.1.trans (div_le_self hB (one_le_pow₀ ?_))
        linarith [norm_nonneg (axialRot θ.2 (axialRot φ y))]
    rw [frameGrad_expansion hE hgper y hint τ φ a b]
    refine Coercive.Internal.MuSmooth.re_sum_sym S hE.symmetric _ fun β => ?_
    rw [map_mul, phase_neg_conj, Coercive.Internal.MuSmooth.modeGrad_neg]
  · have hae := (ae_aestronglyMeasurable_orbit (u := fun z : ℝ × Space => HW z.1 z.2)
      hW.secondDeriv_measurable)
    filter_upwards [rect_ac_halfPlane K hK hae] with p hp τ φ a b c
    have hint : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
        axialRot (-θ.2) (HW (τ + θ.1) (axialRot θ.2 (axialRot φ (planePoint p))) (axialRot θ.2 (unitVector x.2.1))
          (axialRot θ.2 (unitVector x.2.2))) x.1) boxMeasure := by
      intro τ φ x
      have h := integrable_shift_secondDeriv (fun θ : ℝ × ℝ => HW θ.1 (axialRot θ.2 (planePoint p))) hp B
        (fun θ => ?_) (τ, φ) x
      · refine h.congr (Filter.Eventually.of_forall fun θ => ?_)
        simp only [axialRot_add]
        rw [add_comm θ.1 τ]
      · refine (hW.decay _ _).2.2.trans (div_le_self hB (one_le_pow₀ ?_))
        linarith [norm_nonneg (axialRot θ.2 (planePoint p))]
    rw [frameSecondDeriv_expansion hE hW.secondDeriv_periodic (planePoint p) hint τ φ a b c]
    refine Coercive.Internal.MuSmooth.re_sum_sym S hE.symmetric _ fun β => ?_
    rw [map_mul, phase_neg_conj, modeSecondDeriv_neg_conj]

end Internal
end Assembly
end CertCell
end Breakdown
