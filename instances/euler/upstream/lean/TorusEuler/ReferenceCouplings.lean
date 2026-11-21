import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace TorusEuler

/-- The reference coupling numerator identities in the proof of Lemma 2.5. -/
theorem referenceCouplingNumerators (ε τ x s e Y : ℝ)
    (hx : x = ε * τ ^ 2 / 2)
    (hs : (1 + x ^ 2) * s ^ 2 = 1)
    (hY : Y = s * (1 + e) - ε * τ * x * s ^ 2 / 2) :
    (x + ε + 2 * ε * τ * Y = x - ε + 2 * ε * s ^ 2 + 2 * ε * τ * s * (1 + e)) ∧
    (-1 + ε * x + 2 * (1 + x ^ 2) * Y ^ 2 + 2 * ε * τ * x * Y =
      1 + 4 * e + 2 * e ^ 2 + ε * x * s ^ 2) := by
  have hτ : (ε * τ) ^ 2 = 2 * ε * x := by
    linear_combination -2 * ε * hx
  have hs' : x ^ 2 * s ^ 2 = 1 - s ^ 2 := by
    linear_combination hs
  constructor
  · rw [hY]
    linear_combination -(x * s ^ 2) * hτ - 2 * ε * hs'
  · let p := s * (1 + e)
    let q := ε * τ * x * s ^ 2 / 2
    change Y = p - q at hY
    have hp : (1 + x ^ 2) * p ^ 2 = (1 + e) ^ 2 := by
      dsimp [p]
      linear_combination (1 + e) ^ 2 * hs
    have hq : (1 + x ^ 2) * q ^ 2 = ε * x ^ 3 * s ^ 2 / 2 := by
      dsimp [q]
      linear_combination ((ε * τ) ^ 2 * x ^ 2 * s ^ 2 / 4) * hs +
        (x ^ 2 * s ^ 2 / 4) * hτ
    have hcross : 2 * ε * τ * x = 4 * (1 + x ^ 2) * q := by
      dsimp [q]
      linear_combination -2 * ε * τ * x * hs
    calc
      -1 + ε * x + 2 * (1 + x ^ 2) * Y ^ 2 + 2 * ε * τ * x * Y =
          -1 + ε * x + 2 * ((1 + x ^ 2) * p ^ 2 - (1 + x ^ 2) * q ^ 2) := by
            rw [hY, hcross]
            ring
      _ = 1 + 4 * e + 2 * e ^ 2 + ε * x * s ^ 2 := by
            rw [hp, hq]
            linear_combination -ε * x * hs'

end TorusEuler
