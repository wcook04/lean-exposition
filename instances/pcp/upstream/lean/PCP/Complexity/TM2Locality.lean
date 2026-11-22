/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.Bounds
import PCP.Complexity.BoundedEval

/-!
# Constant-window locality of an actual `FinTM2` transition

One counted `TM2` step executes a finite statement tree. The tree can inspect or
modify only a bounded prefix of each stack. This module proves the exact split:
execute the statement on those prefixes, then append each untouched input suffix
to its corresponding output stack. The bound depends only on the fixed machine.

This is a local transition lemma for the computation-tableau construction. It
avoids a truth table over entire space-bounded configurations. The finite constraints
for the prefix lookup and the suffix alignment are built in `TableauConstraints` and
`NPCellConstraints`.
-/

namespace PCP.Machine.TM2Locality

open Turing Turing.TM2

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Reattach the uninspected suffix of every stack. -/
def appendStacks (P T : (k : K) → List (Γ k)) : (k : K) → List (Γ k) :=
  fun k => P k ++ T k

def appendCfg (c : Cfg Γ Λ σ) (T : (k : K) → List (Γ k)) : Cfg Γ Λ σ :=
  ⟨c.l, c.var, appendStacks c.stk T⟩

/-- A short prefix is permitted precisely when there is no hidden suffix to inspect. -/
def Enough (n : ℕ) (P T : (k : K) → List (Γ k)) : Prop :=
  ∀ k, n ≤ (P k).length ∨ T k = []

theorem enough_mono {m n : ℕ} {P T : (k : K) → List (Γ k)}
    (h : Enough n P T) (hm : m ≤ n) : Enough m P T := by
  intro k
  exact (h k).imp (hm.trans) id

private theorem head_append {α : Type} (P T : List α)
    (h : 1 ≤ P.length ∨ T = []) : (P ++ T).head? = P.head? := by
  rcases h with h | rfl
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · simp

private theorem tail_append {α : Type} (P T : List α)
    (h : 1 ≤ P.length ∨ T = []) : (P ++ T).tail = P.tail ++ T := by
  rcases h with h | rfl
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · simp

variable [DecidableEq K]

private theorem push_append (P T : (k : K) → List (Γ k)) (k : K) (a : Γ k) :
    Function.update (appendStacks P T) k (a :: appendStacks P T k) =
      appendStacks (Function.update P k (a :: P k)) T := by
  funext j
  by_cases h : j = k
  · subst j
    simp [appendStacks]
  · simp [appendStacks, Function.update_of_ne h]

private theorem pop_append (P T : (k : K) → List (Γ k)) (k : K)
    (h : 1 ≤ (P k).length ∨ T k = []) :
    Function.update (appendStacks P T) k (appendStacks P T k).tail =
      appendStacks (Function.update P k (P k).tail) T := by
  funext j
  by_cases hj : j = k
  · subst j
    simp only [Function.update_self, appendStacks]
    exact tail_append _ _ h
  · simp [appendStacks, Function.update_of_ne hj]

private theorem enough_push {n : ℕ} {P T : (k : K) → List (Γ k)}
    (h : Enough n P T) (k : K) (a : Γ k) :
    Enough n (Function.update P k (a :: P k)) T := by
  intro j
  by_cases hj : j = k
  · subst j
    rw [Function.update_self]
    exact (h k).imp (fun hk => by simpa using Nat.le_succ_of_le hk) id
  · rw [Function.update_of_ne hj]
    exact h j

private theorem enough_pop {n : ℕ} {P T : (k : K) → List (Γ k)}
    (h : Enough (n + 1) P T) (k : K) :
    Enough n (Function.update P k (P k).tail) T := by
  intro j
  by_cases hj : j = k
  · subst j
    rw [Function.update_self]
    rcases h k with hk | hk
    · left
      rw [List.length_tail]
      omega
    · exact Or.inr hk
  · rw [Function.update_of_ne hj]
    exact (h j).imp (fun hj => by omega) id

/-- An untouched suffix survives an entire counted statement execution exactly. -/
theorem stepAux_append : ∀ (q : Stmt Γ Λ σ) (v : σ) (P T : (k : K) → List (Γ k)),
    Enough (opBound q) P T →
    stepAux q v (appendStacks P T) = appendCfg (stepAux q v P) T
  | .push k f q, v, P, T, h => by
      simp only [stepAux]
      rw [push_append]
      exact stepAux_append q v _ T
        (enough_push (enough_mono h (by simp [opBound])) k (f v))
  | .peek k f q, v, P, T, h => by
      simp only [stepAux]
      rw [show (appendStacks P T k).head? = (P k).head? from
        head_append _ _ (enough_mono h (by simp [opBound]) k)]
      exact stepAux_append q _ P T (enough_mono h (by simp [opBound]))
  | .pop k f q, v, P, T, h => by
      simp only [stepAux]
      have hk := enough_mono h (by simp [opBound] : 1 ≤ opBound (.pop k f q)) k
      rw [show (appendStacks P T k).head? = (P k).head? from head_append _ _ hk,
        pop_append P T k hk]
      exact stepAux_append q _ _ T (enough_pop (by simpa [opBound, Nat.add_comm] using h) k)
  | .load f q, v, P, T, h => by
      exact stepAux_append q _ P T (enough_mono h (by simp [opBound]))
  | .branch f q₁ q₂, v, P, T, h => by
      cases hf : f v with
      | false =>
          simp only [stepAux, hf, Bool.cond_false]
          exact stepAux_append q₂ v P T (enough_mono h (by simp only [opBound]; omega))
      | true =>
          simp only [stepAux, hf, Bool.cond_true]
          exact stepAux_append q₁ v P T (enough_mono h (by simp only [opBound]; omega))
  | .goto f, v, P, T, _ => rfl
  | .halt, v, P, T, _ => rfl

/-- Splitting every stack at a sufficient fixed window isolates the whole transition. -/
theorem stepAux_take_drop (q : Stmt Γ Λ σ) (v : σ) (S : (k : K) → List (Γ k))
    (B : ℕ) (hB : opBound q ≤ B) :
    stepAux q v S =
      appendCfg (stepAux q v (fun k => (S k).take B)) (fun k => (S k).drop B) := by
  have h : Enough (opBound q) (fun k => (S k).take B) (fun k => (S k).drop B) := by
    intro k
    by_cases hk : B ≤ (S k).length
    · left
      simpa only [List.length_take, Nat.min_eq_left hk] using hB
    · right
      exact List.drop_eq_nil_of_le (by omega)
  have heq : appendStacks (fun k => (S k).take B) (fun k => (S k).drop B) = S :=
    funext (fun k => List.take_append_drop B (S k))
  have hstep := stepAux_append q v (fun k => (S k).take B) (fun k => (S k).drop B) h
  rw [heq] at hstep
  exact hstep

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- One inspection-window constant, computed from the finite program syntax. -/
def machineWindow (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l : tm.Λ => opBound (tm.m l)

theorem opBound_le_machineWindow (tm : FinTM2) (l : tm.Λ) :
    opBound (tm.m l) ≤ machineWindow tm :=
  Finset.le_sup (f := fun l : tm.Λ => opBound (tm.m l)) (Finset.mem_univ l)

/-- The actual machine transition is a fixed prefix computation and unchanged suffixes. -/
theorem step_split (tm : FinTM2) (c : tm.Cfg) (l : tm.Λ) (hl : c.l = some l) :
    tm.step c = some (appendCfg
      (stepAux (tm.m l) c.var (fun k => (c.stk k).take (machineWindow tm)))
      (fun k => (c.stk k).drop (machineWindow tm))) := by
  cases c with
  | mk cl cv cs =>
    change cl = some l at hl
    simp only [FinTM2.step, TM2.step, hl]
    exact congrArg some (stepAux_take_drop _ _ _ _ (opBound_le_machineWindow tm l))

/-- Keep just the inspected prefix on every stack. -/
def prefixCfg (tm : FinTM2) (B : ℕ) (c : tm.Cfg) : tm.Cfg :=
  ⟨c.l, c.var, fun k => (c.stk k).take B⟩

/-- The same fixed window also covers the terminal-preserving tableau transition. -/
theorem keepStep_split (tm : FinTM2) (c : tm.Cfg) :
    keepStep tm.step c =
      appendCfg (keepStep tm.step (prefixCfg tm (machineWindow tm) c))
        (fun k => (c.stk k).drop (machineWindow tm)) := by
  cases c with
  | mk cl cv cs =>
    cases cl with
    | none =>
      change (⟨none, cv, cs⟩ : tm.Cfg) =
        ⟨none, cv, fun k => (cs k).take (machineWindow tm) ++
          (cs k).drop (machineWindow tm)⟩
      apply congrArg (fun S => (⟨none, cv, S⟩ : tm.Cfg))
      funext k
      exact (List.take_append_drop _ _).symm
    | some l =>
      simp only [keepStep, FinTM2.step, TM2.step, Option.getD_some, prefixCfg]
      exact stepAux_take_drop _ _ _ _ (opBound_le_machineWindow tm l)

end PCP.Machine.TM2Locality
