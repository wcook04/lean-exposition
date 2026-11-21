import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegUniqueAux3

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

private lemma continuous_powerHeatFactor (α t : ℝ) (ξ : Space) :
    Continuous (fun s : ℝ => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ)) := by
  unfold powerHeatSymbol
  fun_prop

private lemma powerHeatSymbol_mul (α t b s : ℝ) (ξ : Space) :
    ((powerHeatSymbol α (t - b) ξ : ℝ) : ℂ) * ((powerHeatSymbol α (b - s) ξ : ℝ) : ℂ) =
      ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  simp only [powerHeatSymbol, ← Real.exp_add]
  congr 1
  ring

private theorem isPowerMildSymbol_concat {α : ℝ} {F G : ℝ → Space → CSpace} {a b c : ℝ}
    (hab : a ≤ b) (_hbc : b ≤ c) (hF3 : IsHsCurve 3 F a b) (hG3 : IsHsCurve 3 G b c)
    (hF : IsPowerMildSymbol α F a b) (hG : IsPowerMildSymbol α G b c) (hFG : G b = F b) :
    IsPowerMildSymbol α (fun t => if t ≤ b then F t else G t) a c := by
  have hHG : ∀ s ∈ Icc b c, (if s ≤ b then F s else G s) = G s := by
    intro s hs
    by_cases h : s ≤ b
    · rw [if_pos h, le_antisymm h hs.1, hFG]
    · rw [if_neg h]
  intro t ht ξ
  simp only [if_pos hab]
  by_cases htb : t ≤ b
  · rw [if_pos htb, hF t ⟨ht.1, htb⟩ ξ]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [if_pos (hs.2.trans htb)]
  · have hbt : b ≤ t := (not_le.1 htb).le
    have hI1 : IntervalIntegrable (fun s => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      refine (((continuous_powerHeatFactor α t ξ).continuousOn).smul
        (continuousOn_nonlinSymbol hF3 ξ)).congr fun s hs => ?_
      simp only [if_pos hs.2]
      rfl
    have hI2 : IntervalIntegrable (fun s => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ) volume b t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hbt]
      refine ((((continuous_powerHeatFactor α t ξ).continuousOn).smul
        (continuousOn_nonlinSymbol hG3 ξ)).mono (Icc_subset_Icc le_rfl ht.2)).congr
        fun s hs => ?_
      simp only [hHG s ⟨hs.1, hs.2.trans ht.2⟩]
      rfl
    have e1 : ∫ s in a..b, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ =
        ∫ s in a..b, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hab] at hs
      simp only [if_pos hs.2]
    have e2 : ∫ s in b..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ =
        ∫ s in b..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hbt] at hs
      simp only [hHG s ⟨hs.1, hs.2.trans ht.2⟩]
    have e3 : ((powerHeatSymbol α (t - b) ξ : ℝ) : ℂ) •
        ∫ s in a..b, ((powerHeatSymbol α (b - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ =
        ∫ s in a..b, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      rw [← intervalIntegral.integral_smul]
      congr 1
      funext s
      rw [smul_smul, powerHeatSymbol_mul]
    rw [if_neg htb, hG t ⟨hbt, ht.2⟩ ξ, hFG, hF b ⟨hab, le_rfl⟩ ξ,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, e1, e2, smul_add, smul_smul,
      powerHeatSymbol_mul, e3, add_assoc]

private theorem isPowerMildSymbol_restrict {α : ℝ} {F : ℝ → Space → CSpace} {a b b' : ℝ}
    (hb : b' ≤ b) (hF : IsPowerMildSymbol α F a b) : IsPowerMildSymbol α F a b' :=
  fun t ht ξ => hF t ⟨ht.1, ht.2.trans hb⟩ ξ

end PowerInternal

theorem powerConcat (α : ℝ) (_hα : 1 < α) : PowerConcatStatement α :=
  ⟨fun _ _ _ _ _ hab hbc hF3 hG3 hF hG hFG =>
      PowerInternal.isPowerMildSymbol_concat hab hbc hF3 hG3 hF hG hFG,
    fun _ _ _ _ hb hF => PowerInternal.isPowerMildSymbol_restrict hb hF⟩

end Breakdown.SmoothFlow
