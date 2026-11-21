import Breakdown.FracCert.FreeSymbolExistsEquation

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def FreeCoreBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    ∀ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ ξ : Space, ξ ≠ 0 → ‖ξ‖ < ρ →
      ‖iteratedFDeriv ℝ j (FreeSymbolEquationInternal.hbase α a s) ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4 - (j : ℝ))

def FreeExpBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ j : ℕ, ∃ C : ℝ, ∀ ξ : Space, ξ ≠ 0 → ‖ξ‖ ≤ 1 →
    ‖iteratedFDeriv ℝ j (fun η => Real.exp (freqPow (2 * α) η)) ξ‖ ≤ C * ‖ξ‖ ^ (-(j : ℝ))

namespace FreeSymbolSmallInternal

open FreeSymbolSmoothInternal FreeSymbolEquationInternal

theorem small_of (hc : FreeCoreBoundStatement) (he : FreeExpBoundStatement) : FreeSolutionSmallBoundStatement := by
  intro α hα1 hα2 a s hs j
  have hα : 0 < α := by linarith
  choose ρf hρf Cf hCf using hc α hα1 hα2 a s hs
  choose Bf hBf using he α hα1 hα2
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, by simp⟩
  set ρ : ℝ := min 1 ((Finset.range (j + 1)).inf' hne ρf) with hρ
  have hρpos : 0 < ρ := lt_min one_pos ((Finset.lt_inf'_iff hne).2 fun i _ => hρf i)
  refine ⟨ρ, hρpos, ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |Bf i| * |Cf (j - i)|, fun ξ hξ hξρ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hle1 : ‖ξ‖ ≤ 1 := le_trans hξρ.le (min_le_left _ _)
  have hlt : ∀ i ∈ Finset.range (j + 1), ‖ξ‖ < ρf i := fun i hi =>
    lt_of_lt_of_le hξρ (le_trans (min_le_right _ _) (Finset.inf'_le _ hi))
  set U : Set Space := {η | η ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  have hE : ContDiffOn ℝ ∞ (fun η => Real.exp (freqPow (2 * α) η)) U := fun η hη =>
    ((Real.contDiff_exp.contDiffAt).comp η (pow_smoothAt (2 * α) hη)).contDiffWithinAt
  have hC : ContDiffOn ℝ ∞ (hbase α a s) U := fun η hη => (core_contDiffAt hα hs hη).contDiffWithinAt
  have hw : freeSolution α a s = fun η => Real.exp (freqPow (2 * α) η) • hbase α a s η :=
    funext (solution_eq hα a s)
  have hL := norm_iteratedFDerivWithin_smul_le hE hC hUo.uniqueDiffOn (hξ : ξ ∈ U) (n := j) (by exact_mod_cast le_top)
  rw [← hw, iteratedFDerivWithin_of_isOpen j hUo hξ] at hL
  refine le_trans hL ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [iteratedFDerivWithin_of_isOpen i hUo hξ, iteratedFDerivWithin_of_isOpen (j - i) hUo hξ]
  have h1 := hBf i ξ hξ hle1
  have h2 := hCf (j - i) ξ hξ (hlt _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.sub_le j i))))
  have hp1 : 0 ≤ ‖ξ‖ ^ (-(i : ℝ)) := (Real.rpow_pos_of_pos hn _).le
  have hp2 : 0 ≤ ‖ξ‖ ^ (2 * α - 4 - ((j - i : ℕ) : ℝ)) := (Real.rpow_pos_of_pos hn _).le
  have hpow : ‖ξ‖ ^ (-(i : ℝ)) * ‖ξ‖ ^ (2 * α - 4 - ((j - i : ℕ) : ℝ)) = ‖ξ‖ ^ (2 * α - 4 - (j : ℝ)) := by
    rw [← Real.rpow_add hn, Nat.cast_sub hij]
    congr 1
    ring
  have hb1 : ‖iteratedFDeriv ℝ i (fun η => Real.exp (freqPow (2 * α) η)) ξ‖ ≤ |Bf i| * ‖ξ‖ ^ (-(i : ℝ)) :=
    le_trans h1 (mul_le_mul_of_nonneg_right (le_abs_self _) hp1)
  have hb2 : ‖iteratedFDeriv ℝ (j - i) (hbase α a s) ξ‖ ≤ |Cf (j - i)| * ‖ξ‖ ^ (2 * α - 4 - ((j - i : ℕ) : ℝ)) :=
    le_trans h2 (mul_le_mul_of_nonneg_right (le_abs_self _) hp2)
  have hch : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
  calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η => Real.exp (freqPow (2 * α) η)) ξ‖ *
        ‖iteratedFDeriv ℝ (j - i) (hbase α a s) ξ‖
      ≤ (j.choose i : ℝ) * (|Bf i| * ‖ξ‖ ^ (-(i : ℝ))) *
          (|Cf (j - i)| * ‖ξ‖ ^ (2 * α - 4 - ((j - i : ℕ) : ℝ))) := by
        gcongr
    _ = (j.choose i : ℝ) * |Bf i| * |Cf (j - i)| *
          (‖ξ‖ ^ (-(i : ℝ)) * ‖ξ‖ ^ (2 * α - 4 - ((j - i : ℕ) : ℝ))) := by ring
    _ = (j.choose i : ℝ) * |Bf i| * |Cf (j - i)| * ‖ξ‖ ^ (2 * α - 4 - (j : ℝ)) := by rw [hpow]

end FreeSymbolSmallInternal

theorem freeSolutionSmallBound_of (hc : FreeCoreBoundStatement) (he : FreeExpBoundStatement) :
    FreeSolutionSmallBoundStatement :=
  FreeSymbolSmallInternal.small_of hc he

end SteadyCert

end Breakdown
