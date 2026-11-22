/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteDomainLang
import PCP.Reduction.BooleanGraphLang

/-!
# Executable finite-domain constraint to graph reduction

One concrete language program performs one-hot expansion, Boolean lookup-clause
construction, NAE splitting, and adjacency-matrix emission. Every stage has exact
semantics and a proved polynomial charged cost, with alphabet and arity fixed.
-/

namespace PCP.Reduction.FiniteDomainGraphLang

open PCP.Lang FiniteDomainConstraints

variable {v c a d : ℕ}

def encode (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v) : List Bool :=
  BooleanGraphLang.encode (FiniteDomainLang.booleanRelation R) (FiniteDomainLang.booleanScope s)

def program (a d : ℕ) : Prog :=
  (FiniteDomainLang.program a d).compose (BooleanGraphLang.program (arity a d))

/-- Exact output of the entire finite-domain graph construction program. -/
theorem program_run (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v) :
    (program a d).run (FiniteDomainSource.source R s) = (encode R s).map Bool.toNat := by
  rw [program, Prog.run_compose, FiniteDomainLang.program_run_source, BooleanGraphLang.program_run]
  rfl

theorem decode_colorable_iff (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) :
    (Algebraic.ThreeColorEncoding.graph (encode R s)).Colorable 3 ↔
      ∃ x : Fin v → Fin a, Holds R s x :=
  (BooleanGraphLang.decode_colorable_iff _ _).trans
    (FiniteDomainEncoding.indexed_satisfiable_iff (Equiv.refl _) (Equiv.refl _) R s)

private theorem expandedCount_le (a v c : ℕ) :
    (v + 1) * a + (c + v) + 1 ≤ (a + 2) * (v + c + 1) := by nlinarith

/-- The actual output, measured as stored natural bits, is polynomially bounded. -/
theorem output_size (a d : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v),
      listSize ((program a d).run (FiniteDomainSource.source R s)) ≤ C * (v + c + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := BooleanGraphLang.output_size (arity a d)
  refine ⟨C * (a + 2) ^ 2, fun v c R s => ?_⟩
  rw [program, Prog.run_compose, FiniteDomainLang.program_run_source]
  calc
    _ ≤ C * ((v + 1) * a + (c + v) + 1) ^ 2 := hC _ _ _ _
    _ ≤ C * ((a + 2) * (v + c + 1)) ^ 2 :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (expandedCount_le a v c) 2)
    _ = _ := by ring

/-- A uniform polynomial charged-cost bound, with no assumed relation-evaluation algorithm. -/
theorem program_cost (a d : ℕ) : ∃ C : ℕ,
    ∀ (v c : ℕ) (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v),
      (program a d).cost (FiniteDomainSource.source R s) ≤ C * (v + c + 1) ^ 6 := by
  obtain ⟨A, hA⟩ := FiniteDomainLang.program_cost_source a d
  obtain ⟨B, hB⟩ := BooleanGraphLang.program_cost (arity a d)
  obtain ⟨D, hD⟩ := BooleanGraphLang.output_size (arity a d)
  let W := BooleanClauseSource.width (arity a d) + 4
  refine ⟨A + B * (a + 2) ^ 6 + (W + D) * (a + 2) ^ 2 + 5, fun v c R s => ?_⟩
  let M := v + c + 1
  let Rb := FiniteDomainLang.booleanRelation (v := v) R
  let sb := FiniteDomainLang.booleanScope (a := a) s
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hsmall : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by decide)
  have hcount := expandedCount_le a v c
  have hsix := Nat.pow_le_pow_left hcount 6
  have htwo := Nat.pow_le_pow_left hcount 2
  have hfirst := hA v c R s
  have hsecond := hB ((v + 1) * a) (c + v) Rb sb
  have hsource := BooleanClauseLang.source_size_le Rb sb
  have houtput := hD ((v + 1) * a) (c + v) Rb sb
  have hsecond' : (BooleanGraphLang.program (arity a d)).cost
      (BooleanClauseSource.source Rb sb) ≤ B * (a + 2) ^ 6 * M ^ 6 := by
    have hp := Nat.mul_le_mul_left B hsix
    dsimp [M]
    nlinarith only [hsecond, hp]
  have hsource' : listSize (BooleanClauseSource.source Rb sb) ≤ W * (a + 2) ^ 2 * M ^ 6 := by
    have h1 := Nat.mul_le_mul_left W htwo
    have h2 := Nat.mul_le_mul_left (W * (a + 2) ^ 2) hsmall
    change _ ≤ W * ((v + 1) * a + (c + v) + 1) ^ 2 at hsource
    dsimp [M] at h2 ⊢
    nlinarith only [hsource, h1, h2]
  have houtput' : listSize ((BooleanGraphLang.program (arity a d)).run
      (BooleanClauseSource.source Rb sb)) ≤ D * (a + 2) ^ 2 * M ^ 6 := by
    have h1 := Nat.mul_le_mul_left D htwo
    have h2 := Nat.mul_le_mul_left (D * (a + 2) ^ 2) hsmall
    dsimp [M] at h2 ⊢
    nlinarith only [houtput, h1, h2]
  have hone : 1 ≤ M ^ 6 := one_le_pow₀ hM
  rw [program, Prog.cost_compose, FiniteDomainLang.program_run_source]
  change (FiniteDomainLang.program a d).cost (FiniteDomainSource.source R s) +
    (BooleanGraphLang.program (arity a d)).cost (BooleanClauseSource.source Rb sb) +
    listSize (BooleanClauseSource.source Rb sb) +
    listSize ((BooleanGraphLang.program (arity a d)).run (BooleanClauseSource.source Rb sb)) + 5 ≤
      (A + B * (a + 2) ^ 6 + (W + D) * (a + 2) ^ 2 + 5) * M ^ 6
  change _ ≤ A * M ^ 6 at hfirst
  nlinarith only [hfirst, hsecond', hsource', houtput', hone]

end PCP.Reduction.FiniteDomainGraphLang
