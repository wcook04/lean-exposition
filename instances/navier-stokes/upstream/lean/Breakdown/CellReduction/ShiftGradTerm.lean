import Breakdown.CellReduction.ReductionStatements

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

private theorem shiftGrad_lintegral_mul_le {f g : Space → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hf2 : (∫⁻ y, ENNReal.ofReal (f y ^ 2)) ≤ ENNReal.ofReal (K ^ 2))
    (hg2 : (∫⁻ y, ENNReal.ofReal (g y ^ 2)) ≤ ENNReal.ofReal (L ^ 2)) :
    (∫⁻ y, ENNReal.ofReal (f y * g y)) ≤ ENNReal.ofReal (K * L) := by
  have hprod := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hf.ennreal_ofReal hg.ennreal_ofReal
  have hsq : ∀ {u : Space → ℝ}, (∀ y, 0 ≤ u y) →
      (∫⁻ y, ENNReal.ofReal (u y) ^ (2 : ℝ)) = ∫⁻ y, ENNReal.ofReal (u y ^ 2) := by
    intro u hu
    refine lintegral_congr (fun y => ?_)
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hu y)]
  have hroot : ∀ {M : ℝ}, 0 ≤ M → ENNReal.ofReal (M ^ 2) ^ ((1 : ℝ) / 2) = ENNReal.ofReal M := by
    intro M hM
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hM]
  rw [hsq hf0, hsq hg0] at hprod
  calc (∫⁻ y, ENNReal.ofReal (f y * g y))
      = ∫⁻ y, ((fun y => ENNReal.ofReal (f y)) * (fun y => ENNReal.ofReal (g y))) y := by
        refine lintegral_congr (fun y => ?_)
        simp only [Pi.mul_apply]
        exact ENNReal.ofReal_mul (hf0 y)
    _ ≤ _ := hprod
    _ ≤ ENNReal.ofReal (K ^ 2) ^ ((1 : ℝ) / 2) * ENNReal.ofReal (L ^ 2) ^ ((1 : ℝ) / 2) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hf2 (by norm_num))
          (ENNReal.rpow_le_rpow hg2 (by norm_num))
    _ = ENNReal.ofReal (K * L) := by
        rw [hroot hK, hroot hL, ENNReal.ofReal_mul hK]

private theorem shiftGrad_product_le_energy {a b w₀ : ℝ} (hw : 0 < w₀) :
    a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀) := by
  have hs : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  have hsq : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt w₀ * a - b)]

private theorem shiftGrad_columnSquareSum_continuous :
    Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  fun_prop

private theorem shiftGrad_columnSquareSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end Internal

open Internal in
theorem shiftGradTerm_of (h3 : EnergyBoundsHolds) (h4 : CubicWeightProductHolds) :
    ShiftGradTermHolds := by
  intro Γ w₀ n cubic w D G H hw₀ hn hp hD hb
  have hGm : AEStronglyMeasurable G volume := hp.weak_gradient.2.1.aestronglyMeasurable
  have hwm : AEStronglyMeasurable w volume := hp.weak_gradient.1.aestronglyMeasurable
  have htr : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume := by
    have h : (fun y => secondDerivTrace (H y)) =
        fun y => ∑ j : Fin 3, (H y).flip (unitVector j) (unitVector j) := by
      funext y
      simp [secondDerivTrace, ContinuousLinearMap.flip_apply]
    rw [h]
    exact Finset.aestronglyMeasurable_fun_sum (f := fun j y => (H y).flip (unitVector j) (unitVector j))
      Finset.univ (fun j _ =>
        (hp.weak_secondDeriv j).2.1.aestronglyMeasurable.apply_continuousLinearMap (unitVector j))
  have hDw : AEStronglyMeasurable (fun y => D y (w y)) volume :=
    (ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)).aestronglyMeasurable_comp₂
      hD.aestronglyMeasurable hwm
  have hcolumn : AEStronglyMeasurable (fun y => matSq (G y)) volume :=
    shiftGrad_columnSquareSum_continuous.comp_aestronglyMeasurable hGm
  have hI1 : (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) =
      ENNReal.ofReal (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun y => sq_nonneg _))
      (htr.norm.pow 2), ENNReal.ofReal_toReal hp.sumSecondPartials_finite.ne]
  have hI2 : (∫⁻ y, ENNReal.ofReal (matSq (G y))) = ENNReal.ofReal (∫ y, matSq (G y)) := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => shiftGrad_columnSquareSum_nonneg (G y))) hcolumn,
      ENNReal.ofReal_toReal hp.gradient_finite.ne]
  have hI1n : 0 ≤ ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 := integral_nonneg (fun y => sq_nonneg _)
  have hI2n : 0 ≤ ∫ y, matSq (G y) := integral_nonneg (fun y => shiftGrad_columnSquareSum_nonneg (G y))
  have hE : stationaryEnergy (fun _ => w₀) G H =
      (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) + w₀ * ∫ y, matSq (G y) := by
    simp only [stationaryEnergy]
    rw [integral_const_mul]
  set I1 := ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 with hI1def
  set I2 := ∫ y, matSq (G y) with hI2def
  set E := stationaryEnergy (fun _ => w₀) G H with hEdef
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hI1E : I1 ≤ E := by rw [hE]; nlinarith
  have hpt : ∀ y, ‖D y (w y)‖ ^ 2 ≤ ‖D y‖ ^ 2 * ‖w y‖ ^ 2 := by
    intro y
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((D y).le_opNorm (w y)) 2
  have hL2 : (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) ≤
      ENNReal.ofReal (Real.sqrt I1 ^ 2) := by
    rw [hI1, Real.sq_sqrt hI1n]
  have key : ∀ K : ℝ, 0 ≤ K →
      (∫⁻ y, ENNReal.ofReal (‖D y (w y)‖ ^ 2)) ≤ ENNReal.ofReal (K ^ 2) →
      K * Real.sqrt I1 ≤ shiftGradCoeff w₀ cubic * n * E →
      (∫⁻ y, ENNReal.ofReal (‖D y (w y)‖ * ‖secondDerivTrace (H y)‖)) ≤
        ENNReal.ofReal (shiftGradCoeff w₀ cubic * n * E) := by
    intro K hK hX hKL
    exact (shiftGrad_lintegral_mul_le hDw.norm.aemeasurable htr.norm.aemeasurable
      (fun y => norm_nonneg _) (fun y => norm_nonneg _) hK (Real.sqrt_nonneg _) hX hL2).trans
      (ENNReal.ofReal_le_ofReal hKL)
  cases cubic with
  | false =>
    simp only [PieceGradBound, Bool.false_eq_true, ↓reduceIte] at hb
    have hag : 0 ≤ supBoundFactor w₀ := by unfold supBoundFactor; positivity
    have hsup := h3.2.1 Γ w₀ w G H hw₀ hp
    refine key (supBoundFactor w₀ * Real.sqrt E * n) (by positivity) ?_ ?_
    · calc (∫⁻ y, ENNReal.ofReal (‖D y (w y)‖ ^ 2))
          ≤ ∫⁻ y, ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) * ENNReal.ofReal (‖D y‖ ^ 2) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hsup] with y hy
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ((hpt y).trans ?_)
            rw [mul_comm (supBoundFactor w₀ ^ 2 * E)]
            exact mul_le_mul_of_nonneg_left hy (sq_nonneg _)
        _ = ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) * ∫⁻ y, ENNReal.ofReal (‖D y‖ ^ 2) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (supBoundFactor w₀ ^ 2 * E) * ENNReal.ofReal (n ^ 2) := by
            gcongr
        _ = ENNReal.ofReal ((supBoundFactor w₀ * Real.sqrt E * n) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
    · simp only [shiftGradCoeff, Bool.false_eq_true, ↓reduceIte]
      have hs : Real.sqrt I1 ≤ Real.sqrt E := Real.sqrt_le_sqrt hI1E
      calc supBoundFactor w₀ * Real.sqrt E * n * Real.sqrt I1
          = supBoundFactor w₀ * n * Real.sqrt E * Real.sqrt I1 := by ring
        _ ≤ supBoundFactor w₀ * n * Real.sqrt E * Real.sqrt E :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = supBoundFactor w₀ * n * E := by
            rw [mul_assoc (supBoundFactor w₀ * n), Real.mul_self_sqrt hE0]
  | true =>
    simp only [PieceGradBound, ↓reduceIte] at hb
    have hcw := h4 w G (fun y => ‖D y‖) hp.weak_gradient hp.sixth_power hp.gradient_finite
      hD.aestronglyMeasurable.norm
    simp only [abs_norm] at hcw
    have hn3 : (n ^ 3) ^ ((2 : ℝ) / 3) = n ^ 2 := by
      rw [← Real.rpow_natCast n 3, ← Real.rpow_mul hn]
      norm_num
    have hs3 : (0 : ℝ) < Real.sqrt 3 := by positivity
    refine key (2 / Real.sqrt 3 * n * Real.sqrt I2) (by positivity) ?_ ?_
    · calc (∫⁻ y, ENNReal.ofReal (‖D y (w y)‖ ^ 2))
          ≤ ∫⁻ y, ENNReal.ofReal (‖D y‖ ^ 2 * ‖w y‖ ^ 2) :=
            lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hpt y))
        _ ≤ _ := hcw
        _ ≤ ENNReal.ofReal (4 / 3) * ENNReal.ofReal (n ^ 3) ^ ((2 : ℝ) / 3) *
              ENNReal.ofReal I2 := by
            rw [hI2]
            gcongr
        _ = ENNReal.ofReal ((2 / Real.sqrt 3 * n * Real.sqrt I2) ^ 2) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), hn3,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sq_sqrt hI2n]
            ring
    · simp only [shiftGradCoeff, ↓reduceIte]
      have hab := shiftGrad_product_le_energy (a := Real.sqrt I2) (b := Real.sqrt I1) hw₀
      rw [Real.sq_sqrt hI1n, Real.sq_sqrt hI2n, ← hE] at hab
      have hc : 0 ≤ 2 / Real.sqrt 3 * n := by positivity
      calc 2 / Real.sqrt 3 * n * Real.sqrt I2 * Real.sqrt I1
          = 2 / Real.sqrt 3 * n * (Real.sqrt I2 * Real.sqrt I1) := by ring
        _ ≤ 2 / Real.sqrt 3 * n * (E / (2 * Real.sqrt w₀)) := mul_le_mul_of_nonneg_left hab hc
        _ = 2 / Real.sqrt 3 / (2 * Real.sqrt w₀) * n * E := by ring

end CertReduction

end Breakdown
