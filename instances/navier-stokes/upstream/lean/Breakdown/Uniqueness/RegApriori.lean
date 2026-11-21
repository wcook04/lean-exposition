import Breakdown.Uniqueness.RegAprioriAuxEnergy
import Breakdown.Uniqueness.RegAprioriAuxCont
import Breakdown.Uniqueness.RegAprioriAuxMild
import Breakdown.Uniqueness.RegAprioriAuxIntegralIneq

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma rpow_quarter_pow_four (x : ℝ≥0∞) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

private lemma rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem hsNormSq_apriori (m : ℕ) (hm : 3 ≤ m) (M T B₀ : ℝ) : ∃ B : ℝ, ∀ T' ∈ Icc 0 T,
    ∀ F : ℝ → Space → CSpace, IsHsCurve m F 0 T' → IsVarConstSymbol F 0 T' →
      (∀ t ∈ Icc 0 T', IsSolenoidalSymbol (F t)) → hsNormSq m (F 0) ≤ ENNReal.ofReal B₀ →
      (∀ t ∈ Icc 0 T', homNormSq 1 (F t) ≤ ENNReal.ofReal M) →
      ∀ t ∈ Icc 0 T', hsNormSq m (F t) ≤ ENNReal.ofReal B := by
  obtain ⟨K, hK⟩ := lintegral_homNormSq_two_le m hm M T
  obtain ⟨Ca, hCa⟩ := freqL1Norm_le_supBound
  obtain ⟨C, hC⟩ := hsNormSq_sqrt_mild_le m hm
  obtain ⟨B, hB⟩ := iterIntegral_bound (max B₀ 0 ^ (1 / 2 : ℝ)) C
    (max Ca 0 ^ 4 * max M 0 * max K 0) T
  refine ⟨max B 0 ^ 2, ?_⟩
  intro T' hT' F hF hD hS h0 h1 t ht
  have hm2 : 2 ≤ m := by omega
  have hfin : ∀ s ∈ Icc 0 T', hsNormSq m (F s) ≠ ⊤ := fun s hs => (hF.1 s hs).2.ne
  have hwfin : ∀ s ∈ Icc 0 T', freqL1Norm (F s) ≠ ⊤ := fun s hs =>
    (freqL1Norm_lt_top_of_hsNormSq hm2 (hF.1 s hs).2).ne
  set n : ℝ → ℝ := fun s => (hsNormSq m (F s)).toReal ^ (1 / 2 : ℝ) with hn
  set w : ℝ → ℝ := fun s => (freqL1Norm (F s)).toReal with hw
  have hn_eq : ∀ s ∈ Icc 0 T', ENNReal.ofReal (n s) = hsNormSq m (F s) ^ (1 / 2 : ℝ) := by
    intro s hs
    simp only [hn, ENNReal.toReal_rpow]
    exact ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hfin s hs))
  have hw_eq : ∀ s ∈ Icc 0 T', ENNReal.ofReal (w s) = freqL1Norm (F s) := fun s hs =>
    ENNReal.ofReal_toReal (hwfin s hs)
  have hn_cont : ContinuousOn n (Icc 0 T') :=
    (continuousOn_hsNormSq_toReal hF).rpow_const (fun _ _ => Or.inr (by norm_num))
  have hw_cont : ContinuousOn w (Icc 0 T') := continuousOn_freqL1Norm_toReal hm2 hF
  have hn0 : ∀ s ∈ Icc 0 T', 0 ≤ n s := fun s _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hw0 : ∀ s ∈ Icc 0 T', 0 ≤ w s := fun s _ => ENNReal.toReal_nonneg
  have hW4 : ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4) ≤
      ENNReal.ofReal (max Ca 0 ^ 4 * max M 0 * max K 0) := by
    calc ∫⁻ s in Icc 0 T', ENNReal.ofReal (w s ^ 4)
        ≤ ∫⁻ s in Icc 0 T', ENNReal.ofReal (max Ca 0 ^ 4 * max M 0) * homNormSq 2 (F s) := by
          refine setLIntegral_mono' measurableSet_Icc (fun s hs => ?_)
          rw [ENNReal.ofReal_pow (hw0 s hs), hw_eq s hs]
          have hA := hCa (F s)
          have hM : homNormSq 1 (F s) ≤ ENNReal.ofReal (max M 0) :=
            (h1 s hs).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          have hCa' : ENNReal.ofReal Ca ≤ ENNReal.ofReal (max Ca 0) :=
            ENNReal.ofReal_le_ofReal (le_max_left _ _)
          calc freqL1Norm (F s) ^ 4
              ≤ (ENNReal.ofReal Ca * homNormSq 1 (F s) ^ (1 / 4 : ℝ) *
                  homNormSq 2 (F s) ^ (1 / 4 : ℝ)) ^ 4 := by gcongr
            _ = ENNReal.ofReal Ca ^ 4 * homNormSq 1 (F s) * homNormSq 2 (F s) := by
                rw [mul_pow, mul_pow, rpow_quarter_pow_four, rpow_quarter_pow_four]
            _ ≤ ENNReal.ofReal (max Ca 0) ^ 4 * ENNReal.ofReal (max M 0) * homNormSq 2 (F s) := by
                gcongr
            _ = ENNReal.ofReal (max Ca 0 ^ 4 * max M 0) * homNormSq 2 (F s) := by
                rw [ENNReal.ofReal_mul (pow_nonneg (le_max_right _ _) _),
                  ENNReal.ofReal_pow (le_max_right _ _)]
      _ = ENNReal.ofReal (max Ca 0 ^ 4 * max M 0) * ∫⁻ s in Icc 0 T', homNormSq 2 (F s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (max Ca 0 ^ 4 * max M 0) * ENNReal.ofReal (max K 0) := by
          gcongr
          exact (hK T' hT' F hF hD hS h1).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (max Ca 0 ^ 4 * max M 0 * max K 0) :=
          (ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (le_max_right _ _) _)
            (le_max_right _ _))).symm
  have hmild : ∀ t ∈ Icc 0 T', ENNReal.ofReal (n t) ≤ ENNReal.ofReal (max B₀ 0 ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (w s) * ENNReal.ofReal (n s) := by
    intro t ht
    have h0' : hsNormSq m (F 0) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (max B₀ 0 ^ (1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by norm_num)]
      exact ENNReal.rpow_le_rpow (h0.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        (by norm_num)
    have hint : ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (w s) * ENNReal.ofReal (n s) = ∫⁻ s in Ioo 0 t,
          ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) * freqL1Norm (F s) *
            hsNormSq m (F s) ^ (1 / 2 : ℝ) := by
      refine setLIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
      have hs' : s ∈ Icc 0 T' := ⟨hs.1.le, hs.2.le.trans ht.2⟩
      rw [hw_eq s hs', hn_eq s hs']
    rw [hn_eq t ht, hint]
    exact (hC T' F hF hD hS t ht).trans (add_le_add h0' le_rfl)
  have hnt := hB T' hT' n w hn_cont hw_cont hn0 hw0 hW4 hmild t ht
  calc hsNormSq m (F t) = ENNReal.ofReal (n t) ^ 2 := by rw [hn_eq t ht, rpow_half_sq]
    _ ≤ ENNReal.ofReal (max B 0) ^ 2 := by
        gcongr
        exact hnt.trans (le_max_left _ _)
    _ = ENNReal.ofReal (max B 0 ^ 2) := (ENNReal.ofReal_pow (le_max_right _ _) 2).symm

end Breakdown.SmoothFlow
