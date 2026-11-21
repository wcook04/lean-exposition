import Breakdown.Torus.StatementsForce

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ForceSmoothing.Internal

open FreqTrSeries.Internal

def squareField (F : Space → Space) (j : Fin 3) (x : Space) : Space :=
  (((F x).ofLp j) ^ 2) • unitVector 0

theorem continuous_squareField {F : Space → Space} (hF : Continuous F) (j : Fin 3) :
    Continuous (squareField F j) := by
  unfold squareField
  exact (((PiLp.continuous_apply 2 _ j).comp hF).pow 2).smul continuous_const

theorem isPeriodic_squareField {F : Space → Space} (hp : IsPeriodic F) (j : Fin 3) :
    IsPeriodic (squareField F j) := by
  intro i x
  simp only [squareField, hp i x]

theorem character_zero (x : Space) : character 0 x = 1 := by
  simp [character, freq]

theorem integral_sq_apply {F : Space → Space} (hF : Continuous F) (j : Fin 3) :
    (((∫ x in cell, ((F x).ofLp j) ^ 2 : ℝ)) : ℂ) = (freqTrCoef (squareField F j) 0).ofLp 0 := by
  rw [freqTrCoef_apply (continuous_squareField hF j), ← integral_complex_ofReal]
  congr 1
  funext x
  simp [squareField, character_zero, unitVector]

theorem hasSum_apply_sq {F : Space → Space} (hF : Continuous F) (hp : IsPeriodic F) (j : Fin 3) :
    HasSum (fun k => ‖(freqTrCoef F k).ofLp j‖ ^ 2) (∫ x in cell, ((F x).ofLp j) ^ 2) := by
  have : IsFiniteMeasure (Measure.pi fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    inferInstance
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin 3)
    (ContinuousMap.toLp 2 _ ℂ (compMap hF hp j))
  simp only [UnitAddTorus.mFourierCoeff_toLp, mFreqTrCoeff_compMap] at h
  convert h using 1
  apply Complex.ofReal_injective
  rw [integral_sq_apply hF j, ← mFreqTrCoeff_compMap (continuous_squareField hF j)
    (isPeriodic_squareField hp j) 0 0, ← integral_complex_ofReal, UnitAddTorus.mFourierCoeff]
  refine integral_congr_ae ?_
  refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) _ (compMap hF hp j)).mono fun t ht => ?_
  simp only
  rw [ht, neg_zero, UnitAddTorus.mFourier_zero]
  change (1 : ℂ) • compFun (squareField F j) 0 t = ((‖compFun F j t‖ ^ 2 : ℝ) : ℂ)
  simp [compFun, squareField, Complex.norm_real, sq_abs, unitVector]

theorem hasSum_sq {F : Space → Space} (hF : Continuous F) (hp : IsPeriodic F) :
    HasSum (fun k => ‖freqTrCoef F k‖ ^ 2) (∫ x in cell, ‖F x‖ ^ 2) := by
  have h := hasSum_sum (s := Finset.univ) fun j _ => hasSum_apply_sq hF hp j
  have e1 : (fun k => ‖freqTrCoef F k‖ ^ 2) = fun k => ∑ j, ‖(freqTrCoef F k).ofLp j‖ ^ 2 := by
    funext k
    exact EuclideanSpace.norm_sq_eq _
  have e2 : ∫ x in cell, ‖F x‖ ^ 2 = ∑ j, ∫ x in cell, ((F x).ofLp j) ^ 2 := by
    rw [← integral_finsetSum]
    · congr 1
      funext x
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    · intro j _
      exact (((PiLp.continuous_apply 2 _ j).comp hF).pow 2).continuousOn.integrableOn_compact isCompact_cell
  rw [e1, e2]
  exact h

theorem weight_heat_le_of_le_one {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k * heatFactor τ k ^ 2 ≤ 2 / τ := by
  refine (Breakdown.Periodic.Internal.weight_heat_le hτ k).trans ?_
  have hE : Real.exp (-((4 * π ^ 2 * τ) * ‖freq k‖ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  have h1 : 1 ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith
  calc (1 + 1 / τ) * Real.exp (-((4 * π ^ 2 * τ) * ‖freq k‖ ^ 2)) ≤ (1 + 1 / τ) * 1 :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 / τ := by
        rw [mul_one, div_eq_mul_one_div 2 τ]
        linarith

end ForceSmoothing.Internal

open ForceSmoothing.Internal in
theorem forceSmoothing : ForceSmoothing := by
  refine ⟨3, by norm_num, fun τ hτ hτ1 F hF hp => ?_⟩
  set I := ∫ x in cell, ‖F x‖ ^ 2
  have hS := hasSum_sq hF hp
  have hI : 0 ≤ I := hS.nonneg fun k => sq_nonneg _
  have hsq : ((forceV τ F : V) : Seq) = ⟨forceSeq τ F, memℓp_forceSeq τ F⟩ := rfl
  have hnorm : ‖forceV τ F‖ = ‖((forceV τ F : V) : Seq)‖ := rfl
  have htp : (τ ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    norm_num
    rw [Real.rpow_neg_one, inv_eq_one_div]
  have hB : 0 ≤ 3 * τ ^ (-(1 / 2 : ℝ)) * Real.sqrt I := by positivity
  have hle : ‖((forceV τ F : V) : Seq)‖ ^ 2 ≤ (3 * τ ^ (-(1 / 2 : ℝ)) * Real.sqrt I) ^ 2 := by
    rw [Breakdown.Periodic.Internal.norm_sq_seq, mul_pow, mul_pow, htp, Real.sq_sqrt hI]
    have hb : ∀ k, ‖((forceV τ F : V) : Seq) k‖ ^ 2 ≤ 8 / τ * ‖freqTrCoef F k‖ ^ 2 := by
      intro k
      rw [hsq]
      change ‖forceSeq τ F k‖ ^ 2 ≤ _
      refine (Force.Internal.sq_norm_forceSeq_le hτ F k).trans ?_
      have hw := weight_heat_le_of_le_one hτ hτ1 k
      have hc : 0 ≤ ‖freqTrCoef F k‖ ^ 2 := sq_nonneg _
      calc 4 * ‖freqTrCoef F k‖ ^ 2 * (weight k * heatFactor τ k ^ 2)
          ≤ 4 * ‖freqTrCoef F k‖ ^ 2 * (2 / τ) := by gcongr
        _ = 8 / τ * ‖freqTrCoef F k‖ ^ 2 := by ring
    calc ∑' k, ‖((forceV τ F : V) : Seq) k‖ ^ 2 ≤ ∑' k, 8 / τ * ‖freqTrCoef F k‖ ^ 2 :=
          Summable.tsum_le_tsum hb (Breakdown.Periodic.Internal.summable_sq _) (hS.summable.mul_left _)
      _ = 8 / τ * I := by rw [tsum_mul_left, hS.tsum_eq]
      _ ≤ 3 ^ 2 * (1 / τ) * I := by
          have : 8 / τ ≤ 3 ^ 2 * (1 / τ) := by
            rw [div_eq_mul_one_div 8 τ]
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_right this hI
  rw [hnorm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp hle

end Breakdown.Periodic
