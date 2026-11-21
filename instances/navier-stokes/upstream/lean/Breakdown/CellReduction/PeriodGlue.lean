import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    ENNReal.ofReal |∫ x, g x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |g x| ∂μ := by
  have h := norm_integral_le_lintegral_norm (μ := μ) g
  simp only [Real.norm_eq_abs] at h
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_toReal_le

theorem ofReal_abs_integral_inner_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F M : α → Space) :
    ENNReal.ofReal |∫ x, inner ℝ (F x) (M x) ∂μ| ≤ ∫⁻ x, ENNReal.ofReal (‖F x‖ * ‖M x‖) ∂μ := by
  refine (ofReal_abs_integral_le μ _).trans (lintegral_mono fun x => ?_)
  exact ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)

theorem lintegral_ofReal_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) :
    ∫⁻ x, ENNReal.ofReal (φ x ^ 2) ∂μ = eLpNorm φ 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := φ) (p := 2) two_ne_zero
  have h2 : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : ((2 : NNReal) : ℝ≥0∞) = 2 := by norm_num
  rw [h3] at h
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, h]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_of_nonneg (hφ x), ENNReal.ofReal_pow (hφ x), ← ENNReal.rpow_natCast]
  norm_num

theorem le_ofReal_of_sq_le {x : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : x ^ 2 ≤ ENNReal.ofReal (r ^ 2)) :
    x ≤ ENNReal.ofReal r := by
  rw [ENNReal.ofReal_pow hr] at h
  exact not_lt.mp fun hlt => absurd h (not_le.mpr (ENNReal.pow_lt_pow_left two_ne_zero hlt))

end Internal

open Internal

theorem periodSumBound : PeriodSumBoundHolds := by
  intro n F f c E hE hc hmeas hf hF hFle hbound
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμdef
  have hμ : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμdef, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  set φ : Fin n → ℝ × Space → ℝ := fun a z => f a z.1 z.2 with hφdef
  have hφm : ∀ a, AEMeasurable (φ a) μ := fun a => by rw [hμ]; exact (hmeas a).restrict
  set S : ℝ × Space → ℝ := fun z => ∑ a, φ a z with hSdef
  have hS0 : ∀ z, 0 ≤ S z := fun z => Finset.sum_nonneg fun a _ => hf a z.1 z.2
  have hSm : AEMeasurable S μ := Finset.aemeasurable_fun_sum Finset.univ (fun a _ => hφm a)
  have step1 : periodLIntegral (fun σ y => F σ y ^ 2) ≤
      periodLIntegral (fun σ y => (∑ a, f a σ y) ^ 2) := by
    refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (hF σ y) (hFle σ y) 2
  have step2 : periodLIntegral (fun σ y => (∑ a, f a σ y) ^ 2) =
      ∫⁻ z, ENNReal.ofReal (S z ^ 2) ∂μ := by
    rw [hμdef, lintegral_prod _ ((hSm.pow_const 2).ennreal_ofReal)]
    rfl
  have step3 : ∫⁻ z, ENNReal.ofReal (S z ^ 2) ∂μ = eLpNorm S 2 μ ^ 2 :=
    lintegral_ofReal_sq_eq μ S hS0
  have hSeq : S = ∑ a, φ a := by
    funext z
    simp [hSdef, Finset.sum_apply]
  have step4 : eLpNorm S 2 μ ≤ ∑ a, eLpNorm (φ a) 2 μ := by
    rw [hSeq]
    exact eLpNorm_sum_le (fun a _ => (hφm a).aestronglyMeasurable) (by norm_num)
  have step5 : ∀ a, eLpNorm (φ a) 2 μ ≤ ENNReal.ofReal (c a * Real.sqrt E) := by
    intro a
    refine le_ofReal_of_sq_le (mul_nonneg (hc a) (Real.sqrt_nonneg E)) ?_
    rw [← lintegral_ofReal_sq_eq μ (φ a) (fun z => hf a z.1 z.2), mul_pow, Real.sq_sqrt hE]
    refine le_trans ?_ (hbound a)
    exact lintegral_prod_le (fun z => ENNReal.ofReal (φ a z ^ 2))
  have step6 : ∑ a, eLpNorm (φ a) 2 μ ≤ ENNReal.ofReal ((∑ a, c a) * Real.sqrt E) := by
    rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
      (fun a _ => mul_nonneg (hc a) (Real.sqrt_nonneg E))]
    exact Finset.sum_le_sum fun a _ => step5 a
  have hsum0 : 0 ≤ (∑ a, c a) * Real.sqrt E :=
    mul_nonneg (Finset.sum_nonneg fun a _ => hc a) (Real.sqrt_nonneg E)
  calc periodLIntegral (fun σ y => F σ y ^ 2)
      ≤ periodLIntegral (fun σ y => (∑ a, f a σ y) ^ 2) := step1
    _ = eLpNorm S 2 μ ^ 2 := by rw [step2, step3]
    _ ≤ ENNReal.ofReal ((∑ a, c a) * Real.sqrt E) ^ 2 := by
        gcongr
        exact step4.trans step6
    _ = ENNReal.ofReal ((∑ a, c a) ^ 2 * E) := by
        rw [← ENNReal.ofReal_pow hsum0, mul_pow, Real.sq_sqrt hE]

theorem periodPairingBound : PeriodPairingBoundHolds := by
  intro F M B hB h
  have hin : ∀ σ, ENNReal.ofReal |∫ y, inner ℝ (F σ y) (M σ y)| ≤
      ∫⁻ y, ENNReal.ofReal (‖F σ y‖ * ‖M σ y‖) := fun σ =>
    ofReal_abs_integral_inner_le volume (F σ) (M σ)
  have hout := ofReal_abs_integral_le (volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun σ => ∫ y, inner ℝ (F σ y) (M σ y))
  have htot : ENNReal.ofReal |periodPairing F M| ≤ ENNReal.ofReal B :=
    hout.trans ((lintegral_mono fun σ => hin σ).trans h)
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp htot

theorem stationaryPairingBound : StationaryPairingBoundHolds := by
  intro F M B hB h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp ((ofReal_abs_integral_inner_le volume F M).trans h)

theorem sliceIntegrate : SliceIntegrateHolds := by
  intro f h c hc hae
  unfold periodLIntegral
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal (h σ y) :=
        lintegral_mono_ae (ae_restrict_of_ae hae)
    _ = ENNReal.ofReal c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (h σ y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem periodGlue : PeriodGlueHolds :=
  ⟨periodSumBound, periodPairingBound, stationaryPairingBound, sliceIntegrate⟩

end CertReduction

end Breakdown
