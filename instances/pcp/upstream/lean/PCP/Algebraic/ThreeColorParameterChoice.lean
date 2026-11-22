/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorParameters
import Mathlib.Data.Nat.Find

/-!
# Choosing the three-color verifier's dimension from the graph size

The least `a ≥ 2` with `clog 2 N ≤ a*2^a` gives a grid large enough for `N`
vertices. Its volume `a*2^a` is at most four times `max 8 (clog 2 N)`.
All existence and minimality claims are proved, including graph sizes zero and
one. This certifies a mathematical parameter choice, not its running time.
-/

namespace PCP.Algebraic.ThreeColorParameterChoice

private theorem exists_exponent (N : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ Nat.clog 2 N ≤ a * 2 ^ a := by
  refine ⟨max 2 (Nat.clog 2 N), le_max_left _ _, ?_⟩
  exact (le_max_right _ _).trans
    (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))

/-- The least admissible exponent; the witness is proved for every input size. -/
def exponent (N : ℕ) : ℕ := Nat.find (exists_exponent N)

theorem exponent_ge_two (N : ℕ) : 2 ≤ exponent N := (Nat.find_spec (exists_exponent N)).1

/-- The logarithmic parameter volume controlling later resource exponents. -/
def volume (N : ℕ) : ℕ := exponent N * 2 ^ exponent N

theorem le_volume (N : ℕ) : Nat.clog 2 N ≤ volume N :=
  (Nat.find_spec (exists_exponent N)).2

/-- Minimality is retained as a usable interface for every competing exponent. -/
theorem exponent_le {N a : ℕ} (ha : 2 ≤ a) (hN : Nat.clog 2 N ≤ a * 2 ^ a) :
    exponent N ≤ a := Nat.find_min' (exists_exponent N) ⟨ha, hN⟩

/-- Below the selected exponent, an admissible predecessor cannot hold the input. -/
theorem predecessor_volume_lt {N : ℕ} (ha : 2 < exponent N) :
    (exponent N - 1) * 2 ^ (exponent N - 1) < Nat.clog 2 N := by
  have h := Nat.find_min (exists_exponent N)
    (show exponent N - 1 < exponent N by omega)
  have ha' : 2 ≤ exponent N - 1 := by omega
  exact Nat.lt_of_not_ge (fun hN => h ⟨ha', hN⟩)

/-- The chosen grid has room for every vertex, not merely for the logarithm of its count. -/
theorem size_le_grid_capacity (N : ℕ) :
    N ≤ (ThreeColorParameters.grid (exponent N)).card ^
      ThreeColorParameters.size (exponent N) := by
  rw [ThreeColorParameters.grid_capacity]
  exact (Nat.le_pow_clog (by decide) N).trans
    (Nat.pow_le_pow_right (by decide) (le_volume N))

/-- The minimal exponent loses at most a factor four compared with the requested logarithm. -/
theorem volume_le (N : ℕ) : volume N ≤ 4 * max 8 (Nat.clog 2 N) := by
  by_cases ha : exponent N = 2
  · have h := le_max_left 8 (Nat.clog 2 N)
    simp only [volume, ha]
    omega
  · have hge := exponent_ge_two N
    have hprev := predecessor_volume_lt (by omega : 2 < exponent N)
    have he : exponent N = (exponent N - 1) + 1 := by omega
    have hp : 2 ^ exponent N = 2 ^ (exponent N - 1) * 2 := by
      conv_lhs => rw [he]
      rw [pow_succ]
    have hstep : volume N ≤ 4 * ((exponent N - 1) * 2 ^ (exponent N - 1)) := by
      unfold volume
      rw [hp]
      have hc : exponent N * 2 ≤ 4 * (exponent N - 1) := by omega
      have hm := Nat.mul_le_mul_right (2 ^ (exponent N - 1)) hc
      nlinarith
    exact hstep.trans (Nat.mul_le_mul_left 4
      (hprev.le.trans (le_max_right _ _)))

/-- An alternative simple affine bound in the ceiling logarithm. -/
theorem volume_le_log_add_one (N : ℕ) : volume N ≤ 32 * (Nat.clog 2 N + 1) := by
  apply (volume_le N).trans
  have h : max 8 (Nat.clog 2 N) ≤ 8 * (Nat.clog 2 N + 1) := by omega
  omega

/-- Both chosen dimension and inner base are bounded by the parameter volume. -/
theorem size_le_volume (N : ℕ) : ThreeColorParameters.size (exponent N) ≤ volume N := by
  exact Nat.le_mul_of_pos_left _ (by have h := exponent_ge_two N; omega)

/-- The field construction is available at the chosen exponent for every graph size. -/
theorem choice_spec (N : ℕ) :
    2 ≤ exponent N ∧
      N ≤ (ThreeColorParameters.grid (exponent N)).card ^
        ThreeColorParameters.size (exponent N) ∧
      volume N ≤ 4 * max 8 (Nat.clog 2 N) :=
  ⟨exponent_ge_two N, size_le_grid_capacity N, volume_le N⟩

end PCP.Algebraic.ThreeColorParameterChoice
