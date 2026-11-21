import PCP.Complexity.StackSimulationTime
import PCP.Complexity.BoundedEval

/-!
# Finite stack machines simulated by finite tape machines

This specializes the quantitative compiler extracted in `StackSimulationTime` to an
arbitrary finitely supported source program, rather than only Boolean stack programs.
The source and target traces are exact. The target starts on mathlib's marked, reversed
multitrack encoding; this theorem does not claim a canonical binary input/output interface.
-/

namespace PCP.Machine.TMTime

open Turing
open scoped BigOperators

/-- The local trace convention agrees with the one used by `TM2OutputsInTime`. -/
theorem exec_eq_iterate {α : Type*} (step : α → Option α) (t : ℕ) (a : α) :
    exec step t a = (Function.swap Bind.bind step)^[t] (some a) := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [exec, Function.iterate_succ_apply]
    change (step a).bind (exec step t) = (Function.swap Bind.bind step)^[t] (step a)
    cases h : step a with
    | none =>
      exact (iterate_bind_none (step := step) t).symm
    | some b => exact ih b

section Generic

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] [Inhabited Λ] [Inhabited σ] [Finite σ]

/-- Every supported stack program has one finite-control TM0 simulator with quadratic
overhead. Its halted tape is exactly the tape related to the source's final stacks. -/
theorem finite_compilation (M : Λ → TM2.Stmt Γ Λ σ) (F : Finset Λ)
    (hF : TM2.Supports M F) :
    ∃ (m : ℕ) (G : TM0.Machine (TM2to1.Γ' K Γ) (Fin (m + 1))) (C : ℕ), 0 < C ∧
      ∀ (k : K) (w : List (Γ k)) (b : TM2.Cfg Γ Λ σ) (t : ℕ),
        exec (TM2.step M) t (TM2.init k w) = some b → TM2.step M b = none →
        ∃ u ≤ C * (w.length + t + 3) ^ 2,
          ∃ a : TM0.Cfg (TM2to1.Γ' K Γ) (Fin (m + 1)),
            exec (TM0.step G) u (TM0.init (TM2to1.trInit k w)) = some a ∧
            TM0.step G a = none ∧
            ∃ b' : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ,
              TM2to1.TrCfg b b' ∧ a.Tape = b'.Tape := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let N := TM2to1.tr M
  let H := TM2to1.trSupp M F
  have hH : TM1.Supports N H := TM2to1.tr_supports M hF
  let S := TM1to0.trStmts N H
  have hs : TM0.Supports (TM1to0.tr N) (S : Set (TM1to0.Λ' N)) :=
    TM1to0.tr_supports N hH
  obtain ⟨m, G, hG⟩ := FiniteStates.finite_machine (TM1to0.tr N) S hs
  let A := 1 + ∑ l ∈ F, (StackToOne.stackWeight (M l) + 1)
  let B := 1 + ∑ l ∈ H, OneToZero.weight (N l)
  have hA : 1 ≤ A := by simp [A]
  have hB : 1 ≤ B := by simp [B]
  have hAbound : ∀ l ∈ F, StackToOne.stackWeight (M l) + 1 ≤ A := by
    intro l hl
    exact (Finset.single_le_sum (f := fun l => StackToOne.stackWeight (M l) + 1)
      (fun _ _ => Nat.zero_le _) hl).trans
      (Nat.le_add_left _ _)
  have hBbound : ∀ l ∈ H, OneToZero.weight (N l) ≤ B := by
    intro l hl
    exact (Finset.single_le_sum (f := fun l => OneToZero.weight (N l))
      (fun _ _ => Nat.zero_le _) hl).trans
      (Nat.le_add_left _ _)
  refine ⟨m, G, 10 * B * (A + 1) ^ 2, by positivity, ?_⟩
  intro k w b t hr hh
  have hlen : ∀ j, ((TM2.init k w : TM2.Cfg Γ Λ σ).stk j).length ≤ w.length := by
    intro j
    by_cases hj : j = k
    · subst j
      simp [TM2.init]
    · simp [TM2.init, hj]
  obtain ⟨u, b', hu, htr, hx⟩ := StackToOne.execution_time M F hF A hAbound
    t (TM2.init k w) b (TM1.init (TM2to1.trInit k w)) w.length
    (Finset.some_mem_insertNone.mpr hF.1) hlen (TM2to1.trCfg_init k w) hr
  have hhalt : TM1.step N b' = none := StackToOne.halts M b b' htr hh
  obtain ⟨u', hu', hx'⟩ := OneToZero.execution_time N H hH B hBbound u
    (TM1.init (TM2to1.trInit k w)) b' (Finset.some_mem_insertNone.mpr hH.1) hx
  have hi : TM1to0.trCfg N (TM1.init (TM2to1.trInit k w)) =
      TM0.init (TM2to1.trInit k w) := rfl
  rw [hi] at hx'
  obtain ⟨a, ha, hhalt', htape⟩ := hG (TM2to1.trInit k w) u'
    (TM1to0.trCfg N b') hx' (OneToZero.halts N b' hhalt)
  refine ⟨u', ?_, a, ha, hhalt', b', htr, htape⟩
  have ht : t ≤ w.length + t + 3 := by omega
  have hsweep : w.length + A * t ≤ (A + 1) * (w.length + t + 3) := by
    nlinarith only [Nat.zero_le (A * w.length), Nat.zero_le A]
  have hsweep' : 2 * (w.length + A * t) + 4 ≤
      4 * (A + 1) * (w.length + t + 3) := by
    nlinarith only [hsweep, hA, Nat.zero_le w.length, Nat.zero_le t]
  calc
    u' ≤ B * u := hu'
    _ ≤ B * (A * t * (2 * (w.length + A * t) + 4)) := Nat.mul_le_mul_left _ hu
    _ ≤ B * (A * (w.length + t + 3) *
        (4 * (A + 1) * (w.length + t + 3))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hsweep')
    _ ≤ 10 * B * (A + 1) ^ 2 * (w.length + t + 3) ^ 2 := by
      nlinarith [Nat.zero_le (B * (w.length + t + 3) ^ 2)]

end Generic

end PCP.Machine.TMTime
