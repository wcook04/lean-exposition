/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.BooleanClauseLang
import PCP.Complexity.LangComposition

/-!
# One executable Boolean-constraint to graph reduction

The bounded truth-table clause compiler and graph matrix emitter compose into
one concrete program. Its exact output is the graph bitstring used by the
three-color verifier, and its charged cost is polynomial at every fixed arity.
-/

namespace PCP.Reduction.BooleanGraphLang

open PCP.Lang

variable {v c k : ℕ}

def formula (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) :=
  ThreeSATNumericClauses.indexed (FiniteBooleanEncoding.indexedClauses R s)

def encode (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) : List Bool :=
  Algebraic.ThreeColorEncoding.encode (ThreeColorNumericAdjacency.indexedGraph (formula R s))

def program (k : ℕ) : Prog :=
  (BooleanClauseLang.program k).compose ThreeColorMatrixLang.program

/-- Exact output identity for the actual composed graph constructor. -/
theorem program_run (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) :
    (program k).run (BooleanClauseSource.source R s) = (encode R s).map Bool.toNat := by
  rw [program, Prog.run_compose, BooleanClauseLang.program_run_source,
    ThreeColorMatrixSource.program_run]
  rfl

/-- Colorability of the emitted graph is exactly feasibility of the Boolean local constraints. -/
theorem decode_colorable_iff (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
    (s : Fin c → Fin k → Fin v) :
    (Algebraic.ThreeColorEncoding.graph (encode R s)).Colorable 3 ↔
      ∃ a : Fin v → Bool, FiniteBooleanConstraints.LocalHolds R s a :=
  (ThreeSATNumericClauses.decoded_colorable_iff (FiniteBooleanEncoding.indexedClauses R s)).trans
    (FiniteBooleanEncoding.indexedClauses_satisfiable_iff R s)

theorem bitList_size_le (l : List Bool) : listSize (l.map Bool.toNat) ≤ 2 * l.length := by
  induction l with
  | nil => simp [listSize]
  | cons b l ih => cases b <;> simp_all [listSize] <;> omega

theorem matrix_output_size {v c : ℕ}
    (Q : Fin c → Fin 3 → NAEThreeColor.Literal (Fin v)) :
    listSize (ThreeColorMatrixLang.program.run (ThreeColorMatrixSource.source Q)) ≤
      26 * (v + c + 1) ^ 2 := by
  rw [ThreeColorMatrixSource.program_run]
  have h := bitList_size_le
    (Algebraic.ThreeColorEncoding.encode (ThreeColorNumericAdjacency.indexedGraph Q))
  rw [Algebraic.ThreeColorEncoding.length_encode] at h
  have hn : 3 + 2 * v + 3 * c ≤ 3 * (v + c + 1) := by omega
  have hsq := Nat.pow_le_pow_left hn 2
  nlinarith

/-- Fixed-arity Boolean constraints are reduced by one polynomial-cost concrete program. -/
theorem program_cost (k : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
      (s : Fin c → Fin k → Fin v),
      (program k).cost (BooleanClauseSource.source R s) ≤ C * (v + c + 1) ^ 6 := by
  obtain ⟨A, ha⟩ := BooleanClauseLang.program_cost_source k
  obtain ⟨B, hb⟩ := ThreeColorMatrixSource.program_cost
  let H := 2 ^ k * (k + 1) + 3 * (2 ^ k * (3 * k + 2)) + 1
  refine ⟨A + B * H ^ 6 + 36 * H ^ 2 + 5, fun v c R s => ?_⟩
  let V := v + c * 2 ^ k * (k + 1)
  let C := c * 2 ^ k * (3 * k + 2)
  let M := v + c + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hcount : V + C + C * 2 + 1 ≤ H * M := by
    have heq : V + C + C * 2 + 1 + c = v + c * H + 1 := by dsimp [V, C, H]; ring
    have hv := Nat.mul_le_mul_right (v + 1) hH
    calc
      _ ≤ v + c * H + 1 := by omega
      _ ≤ H * (v + 1) + c * H := by omega
      _ = _ := by dsimp [M]; ring
  have hsq := Nat.pow_le_pow_left hcount 2
  have hsix := Nat.pow_le_pow_left hcount 6
  have hsmall : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by decide)
  have hsource := ThreeColorMatrixSource.source_size_le (formula R s)
  have houtput := matrix_output_size (formula R s)
  have hfirst := ha v c R s
  have hsecond := hb (V + C) (C * 2) (formula R s)
  have hsbound : listSize (ThreeColorMatrixSource.source (formula R s)) ≤ 10 * H ^ 2 * M ^ 6 := by
    have hp := Nat.mul_le_mul_left (10 * H ^ 2) hsmall
    change _ ≤ 10 * (V + C + C * 2 + 1) ^ 2 at hsource
    nlinarith only [hsource, hsq, hp]
  have hobound : listSize
      (ThreeColorMatrixLang.program.run (ThreeColorMatrixSource.source (formula R s))) ≤
      26 * H ^ 2 * M ^ 6 := by
    have hp := Nat.mul_le_mul_left (26 * H ^ 2) hsmall
    change _ ≤ 26 * (V + C + C * 2 + 1) ^ 2 at houtput
    nlinarith only [houtput, hsq, hp]
  have hsecond' : ThreeColorMatrixLang.program.cost
      (ThreeColorMatrixSource.source (formula R s)) ≤ B * H ^ 6 * M ^ 6 := by
    have hp := Nat.mul_le_mul_left B hsix
    nlinarith only [hsecond, hp]
  have hone : 1 ≤ M ^ 6 := one_le_pow₀ hM
  rw [program, Prog.cost_compose, BooleanClauseLang.program_run_source]
  change (BooleanClauseLang.program k).cost (BooleanClauseSource.source R s) +
    ThreeColorMatrixLang.program.cost (ThreeColorMatrixSource.source (formula R s)) +
    listSize (ThreeColorMatrixSource.source (formula R s)) +
    listSize (ThreeColorMatrixLang.program.run (ThreeColorMatrixSource.source (formula R s))) + 5 ≤
      (A + B * H ^ 6 + 36 * H ^ 2 + 5) * M ^ 6
  change _ ≤ A * M ^ 6 at hfirst
  nlinarith only [hfirst, hsecond', hsbound, hobound, hone]


/-- The operational graph output has quadratic bit size at each fixed local arity. -/
theorem output_size (k : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → FiniteBooleanConstraints.Pattern k → Bool)
      (s : Fin c → Fin k → Fin v),
      listSize ((program k).run (BooleanClauseSource.source R s)) ≤ C * (v + c + 1) ^ 2 := by
  let H := 2 ^ k * (k + 1) + 3 * (2 ^ k * (3 * k + 2)) + 1
  refine ⟨26 * H ^ 2, fun v c R s => ?_⟩
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hcount : v + c * 2 ^ k * (k + 1) + c * 2 ^ k * (3 * k + 2) +
      c * 2 ^ k * (3 * k + 2) * 2 + 1 ≤ H * (v + c + 1) := by
    have heq : v + c * 2 ^ k * (k + 1) + c * 2 ^ k * (3 * k + 2) +
        c * 2 ^ k * (3 * k + 2) * 2 + 1 + c = v + c * H + 1 := by dsimp [H]; ring
    have hv := Nat.mul_le_mul_right (v + 1) hH
    calc
      _ ≤ v + c * H + 1 := by omega
      _ ≤ H * (v + 1) + c * H := by omega
      _ = _ := by ring
  rw [program, Prog.run_compose, BooleanClauseLang.program_run_source]
  calc
    _ ≤ 26 * (v + c * 2 ^ k * (k + 1) + c * 2 ^ k * (3 * k + 2) +
        c * 2 ^ k * (3 * k + 2) * 2 + 1) ^ 2 := matrix_output_size (formula R s)
    _ ≤ 26 * (H * (v + c + 1)) ^ 2 :=
      Nat.mul_le_mul_left 26 (Nat.pow_le_pow_left hcount 2)
    _ = _ := by ring

end PCP.Reduction.BooleanGraphLang
