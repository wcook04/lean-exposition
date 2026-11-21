import PCP.Complexity.LangSpace
import PCP.Complexity.Machine

/-!
# Budget arithmetic for structured compilation

The source charge bounds every state visited by a loop and its number of body
calls. Static sequencing takes the maximum of polynomial degrees; a counted
loop increases the degree by one. These lemmas concern the explicit source cost
and are used with actual machine traces, not as replacement runtime certificates.
-/

namespace PCP.Lang.Compiler

variable {R Q : ℕ}

/-- Forgetting charges turns the source iterator into ordinary function iteration. -/
theorem iterate_state (f : State R Q → State R Q × ℕ) (c n : ℕ) (st : State R Q) :
    (iterate f c n st).1 = (fun s => (f s).1)^[n] st := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => exact (ih (f st).1).trans (Function.iterate_succ_apply _ _ _).symm

/-- Every counted call pays at least one when the loop's counter charge is positive. -/
theorem iterations_le_cost (f : State R Q → State R Q × ℕ) (c : ℕ) (hc : 1 ≤ c)
    (n : ℕ) (st : State R Q) : n ≤ (iterate f c n st).2 := by
  induction n generalizing st with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have h := ih (f st).1
      simp only [iterate] at *
      omega

/-- A larger positive base and a larger exponent both enlarge a natural polynomial budget. -/
theorem power_budget_mono (B N k d : ℕ) (hB : B ≤ N) (hN : 1 ≤ N) (hk : k ≤ d) :
    B ^ k ≤ N ^ d :=
  (Nat.pow_le_pow_left hB k).trans (Nat.pow_le_pow_right hN hk)

/-- Three physical call/return transitions fit inside the static sequencing coefficient. -/
theorem sequence_budget (a b k l B c d : ℕ) :
    a * (B + c + 1) ^ k + b * (B + c + d + 1) ^ l + 3 ≤
      (a + b + 4) * (B + (c + d + 1) + 1) ^ max k l := by
  let N := B + (c + d + 1) + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have h1 := power_budget_mono (B + c + 1) N k (max k l) (by dsimp [N]; omega)
    hN (Nat.le_max_left _ _)
  have h2 := power_budget_mono (B + c + d + 1) N l (max k l) (by dsimp [N]; omega)
    hN (Nat.le_max_right _ _)
  have hpos : 1 ≤ N ^ max k l := one_le_pow₀ hN
  have ha := Nat.mul_le_mul_left a h1
  have hb := Nat.mul_le_mul_left b h2
  change _ ≤ (a + b + 4) * N ^ max k l
  nlinarith

/-- Either selected branch fits the shared coefficient, including its two control transitions. -/
theorem branch_budget (a b k l B c overhead : ℕ) (hOverhead : 1 ≤ overhead) :
    a * (B + c + 1) ^ k + 2 ≤
      (a + b + 4) * (B + (c + overhead) + 1) ^ max k l := by
  let N := B + (c + overhead) + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have h1 := power_budget_mono (B + c + 1) N k (max k l)
    (by dsimp [N]; omega) hN (Nat.le_max_left _ _)
  have hpos : 1 ≤ N ^ max k l := one_le_pow₀ hN
  have ha := Nat.mul_le_mul_left a h1
  change _ ≤ (a + b + 4) * N ^ max k l
  nlinarith

/-- Capturing one counter, executing all iterations, and returning costs one extra degree. -/
theorem loop_budget (a k N n width : ℕ) (hN : 1 ≤ N) (hn : n ≤ N)
    (hw : width ≤ N) :
    2 * width + n * ((a + 34) * N ^ k) + 1 + 3 ≤ (a + 128) * N ^ (k + 1) := by
  have hp : 1 ≤ N ^ k := one_le_pow₀ hN
  have hn' := Nat.mul_le_mul_right ((a + 34) * N ^ k) hn
  rw [pow_succ]
  nlinarith

end PCP.Lang.Compiler
