import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem scaleFactor_sq_eq (w₀ : ℝ) :
    supBoundFactor w₀ ^ 2 = 1 / (4 * Real.pi * Real.sqrt w₀) := by
  have hpos : 0 ≤ 2 * Real.pi * (2 * Real.sqrt w₀) := by positivity
  unfold supBoundFactor
  rw [div_pow, one_pow, Real.sq_sqrt hpos]
  ring

theorem product_le_scaleFactor_sq (w₀ a b : ℝ) (hw : 0 < w₀) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / (2 * Real.pi)) * Real.sqrt a * Real.sqrt b ≤ supBoundFactor w₀ ^ 2 * (b + w₀ * a) := by
  rw [scaleFactor_sq_eq]
  have hs : Real.sqrt w₀ ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc (1 / (2 * Real.pi)) * Real.sqrt a * Real.sqrt b
        = 1 / (4 * Real.pi * Real.sqrt w₀) * (2 * (Real.sqrt w₀ * Real.sqrt a) * Real.sqrt b) := by
          field_simp
          ring
    _ ≤ 1 / (4 * Real.pi * Real.sqrt w₀) * (Real.sqrt b ^ 2 + (Real.sqrt w₀ * Real.sqrt a) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt w₀ * Real.sqrt a)]
    _ = 1 / (4 * Real.pi * Real.sqrt w₀) * (b + w₀ * a) := by
          rw [Real.sq_sqrt hb, mul_pow, Real.sq_sqrt hw.le, Real.sq_sqrt ha]

theorem columnSquareSum_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end Internal

theorem sliceEnergySup_of (h1 : SliceSupNormHolds) (h2 : PerturbationSliceHolds) :
    SliceEnergySupHolds := by
  intro Γ P w₀ v G H g hw hp
  filter_upwards [h2 Γ P v G H g hp] with σ hσ
  obtain ⟨hg, hh, h6, hG, hH⟩ := hσ
  filter_upwards [h1 (v σ) (G σ) (H σ) hg hh h6 hG hH] with y hy
  exact hy.trans (Internal.product_le_scaleFactor_sq w₀ _ _ hw
    (integral_nonneg fun _ => Internal.columnSquareSum_nonneg' _)
    (integral_nonneg fun _ => sq_nonneg _))

theorem profileEnergySup_of (h1 : SliceSupNormHolds) : ProfileEnergySupHolds := by
  intro Γ w₀ w G H hw hp
  filter_upwards [h1 w G H hp.weak_gradient hp.weak_secondDeriv hp.sixth_power hp.gradient_finite
    hp.sumSecondPartials_finite] with y hy
  refine hy.trans (le_of_le_of_eq (Internal.product_le_scaleFactor_sq w₀ _ _ hw
    (integral_nonneg fun _ => Internal.columnSquareSum_nonneg' _)
    (integral_nonneg fun _ => sq_nonneg _)) ?_)
  unfold stationaryEnergy
  rw [integral_const_mul]

theorem periodGradientEnergy : PeriodGradientEnergyHolds := by
  intro w₀ G H hw hfin
  have hle : ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul hw.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := sq_nonneg ‖secondDerivTrace (H σ y)‖
    linarith
  unfold weightedEnergy
  calc w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal
        = (ENNReal.ofReal w₀ * periodLIntegral (fun σ y => matSq (G σ y))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw.le]
    _ ≤ (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y))).toReal :=
          ENNReal.toReal_mono hfin.ne hle

theorem energyBounds_of (h1 : SliceSupNormHolds) (h2 : PerturbationSliceHolds) :
    EnergyBoundsHolds :=
  ⟨sliceEnergySup_of h1 h2, profileEnergySup_of h1, periodGradientEnergy⟩

end CertReduction

end Breakdown
