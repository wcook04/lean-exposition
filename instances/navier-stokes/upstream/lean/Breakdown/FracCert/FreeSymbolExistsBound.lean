import Breakdown.FracCert.FreeSymbolExistsSmooth
import Breakdown.FracCert.FreeSymbolExistsBasic

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolBoundInternal

theorem far_zero {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ∃ R : ℝ, 0 < R ∧ ∀ (j : ℕ) (ξ : Space), R < ‖ξ‖ → iteratedFDeriv ℝ j (freeSolution α a s) ξ = 0 := by
  obtain ⟨R0, hR0⟩ := FreeSymbolExistsInternal.support_zero (a := a) hα hs
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun j ξ hξ => ?_⟩
  have hopen : IsOpen {η : Space | max R0 1 < ‖η‖} := isOpen_lt continuous_const continuous_norm
  have hev : freeSolution α a s =ᶠ[nhds ξ] fun _ => 0 :=
    Filter.eventually_of_mem (hopen.mem_nhds hξ) fun η hη =>
      hR0 η (lt_of_le_of_lt (le_max_left _ _) hη)
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
  simp

theorem deriv_continuousOn {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) (j : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ j (freeSolution α a s)) {ξ | ξ ≠ 0} := by
  have hopen : IsOpen {ξ : Space | ξ ≠ 0} := isOpen_ne
  have h := (FreeSymbolSmoothInternal.solution_smooth hα a hs).continuousOn_iteratedFDerivWithin
    (m := j) (by exact_mod_cast le_top) hopen.uniqueDiffOn
  exact h.congr fun ξ hξ => (iteratedFDerivWithin_of_isOpen j hopen hξ).symm

end FreeSymbolBoundInternal

open FreeSymbolBoundInternal in
theorem freeSolutionBound_of (h : FreeSolutionSmallBoundStatement) : FreeSolutionBoundStatement := by
  intro α hα1 hα2 a s hs j
  have hα : 0 < α := by linarith
  obtain ⟨ρ, hρ, C1, hC1⟩ := h α hα1 hα2 a s hs j
  obtain ⟨R, hR, hfar⟩ := far_zero (a := a) hα hs
  set K : Set Space := Metric.closedBall 0 R ∩ {ξ | ρ ≤ ‖ξ‖} with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hKsub : K ⊆ {ξ | ξ ≠ 0} := fun ξ hξ h0 => by
    have h2 : ρ ≤ ‖ξ‖ := hξ.2
    rw [h0, norm_zero] at h2
    linarith
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((deriv_continuousOn (a := a) hα hs j).mono hKsub)
  set e : ℝ := 2 * α - 4 - (j : ℝ) with he
  have he0 : e ≤ 0 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hRe : 0 < R ^ e := Real.rpow_pos_of_pos hR e
  refine ⟨max (max C1 0) (max M 0 / R ^ e), fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hpow : 0 < ‖ξ‖ ^ e := Real.rpow_pos_of_pos hn e
  by_cases h1 : ‖ξ‖ < ρ
  · calc ‖iteratedFDeriv ℝ j (freeSolution α a s) ξ‖ ≤ C1 * ‖ξ‖ ^ e := hC1 ξ hξ h1
      _ ≤ max (max C1 0) (max M 0 / R ^ e) * ‖ξ‖ ^ e :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hpow.le
  · by_cases h2 : R < ‖ξ‖
    · rw [hfar j ξ h2, norm_zero]
      exact mul_nonneg (le_trans (le_max_right _ _) (le_max_left _ _)) hpow.le
    · have hmem : ξ ∈ K := ⟨by simpa using not_lt.1 h2, not_lt.1 h1⟩
      have hb := hM ξ hmem
      have hcmp : R ^ e ≤ ‖ξ‖ ^ e := Real.rpow_le_rpow_of_nonpos hn (not_lt.1 h2) he0
      calc ‖iteratedFDeriv ℝ j (freeSolution α a s) ξ‖ ≤ max M 0 := le_trans hb (le_max_left _ _)
        _ = max M 0 / R ^ e * R ^ e := by field_simp
        _ ≤ max M 0 / R ^ e * ‖ξ‖ ^ e :=
          mul_le_mul_of_nonneg_left hcmp (div_nonneg (le_max_right _ _) hRe.le)
        _ ≤ max (max C1 0) (max M 0 / R ^ e) * ‖ξ‖ ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

end SteadyCert

end Breakdown
