/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Tactic

/-!
# Quantitative compilation of finite Turing machines

Adapted from Complexitylib at commit `add0aca8ee0d71e68969f2cb45cf91554a50f787`,
which attributes the original proofs to OpenAI's `math` revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache 2.0).
Only generic transition-count lemmas are extracted; no complexity class is redefined.
The namespace and imports are adapted to the pinned mathlib installation.
-/

namespace PCP.Machine.TMTime
open Turing

/-- Execute a partial transition function for exactly the specified number of steps. -/
def exec {α : Type*} (step : α → Option α) : ℕ → α → Option α
  | 0,a => some a
  | t+1,a => (step a).bind (exec step t)

@[simp] lemma exec_zero {α : Type*} (step : α → Option α) (a : α) : exec step 0 a = some a := rfl

lemma exec_add {α : Type*} (step : α → Option α) (s t : ℕ) (a : α) :
    exec step (s+t) a = (exec step s a).bind (exec step t) := by
  induction s generalizing a with
  | zero => simp [exec]
  | succ s ih =>
    simp only [Nat.succ_add,exec,ih,Option.bind_assoc]

lemma exec_trans {α : Type*} {step : α → Option α} {s t : ℕ} {a b c : α}
    (h : exec step s a = some b) (h' : exec step t b = some c) :
    exec step (s+t) a = some c := by rw [exec_add,h,Option.bind_some,h']

lemma exec_positive_congr {α : Type*} {step : α → Option α} {t : ℕ} (ht : 0 < t)
    {a b : α} (h : step a = step b) : exec step t a = exec step t b := by
  cases t with
  | zero => omega
  | succ t => simp only [exec,h]

namespace OneToZero
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Syntactic statement bound, fixed once the finite machine is fixed. -/
def weight : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .write _ q | .load _ q => weight q+1
  | .branch _ q r => max (weight q) (weight r)+1
  | .goto _ | .halt => 1

lemma weight_pos.{v_1, v_2, v_3} {Γ : Type v_1} {Λ : Type v_2}
  {σ : Type v_3} (q : Turing.TM1.Stmt Γ Λ σ) :
  0 < PCP.Machine.TMTime.OneToZero.weight q := by cases q <;> simp [weight]

/-- Each TM1 macro-step takes at most its statement size in real TM0 steps.
Load and branch are absorbed into the next primitive step by Mathlib's compiler. -/
theorem statement_time (M : Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ t, 0<t ∧ t ≤ weight q ∧
      exec (TM0.step (TM1to0.tr M)) t ⟨(some q,v),T⟩ =
        some (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.move d)
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | write f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.write (f T.head v))
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | load f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih (f T.head v) T
    refine ⟨t,ht,by simp only [weight]; omega,?_⟩
    rw [exec_positive_congr ht (by rfl : TM0.step (TM1to0.tr M)
      ⟨(some (.load f q),v),T⟩ = TM0.step (TM1to0.tr M) ⟨(some q,f T.head v),T⟩)]
    exact he
  | branch f q r ihq ihr =>
    cases hh : f T.head v with
    | false =>
      obtain ⟨t,ht,hb,he⟩ := ihr v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,
        Bool.cond_false] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some r,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
    | true =>
      obtain ⟨t,ht,hb,he⟩ := ihq v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,Bool.cond_true] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
  | goto f =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]

/-- Linear transition overhead for a finitely supported TM1 program. -/
theorem execution_time (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hs : TM1.Supports M S) (C : ℕ) (hC : ∀ l ∈ S, weight (M l) ≤ C)
    (t : ℕ) (a b : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S)
    (hr : exec (TM1.step M) t a = some b) :
    ∃ u ≤ C*t, exec (TM0.step (TM1to0.tr M)) u (TM1to0.trCfg M a) =
      some (TM1to0.trCfg M b) := by
  induction t generalizing a with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0, by omega, rfl⟩
  | succ t ih =>
    obtain ⟨l,v,T⟩ := a
    cases l with
    | none => simp [exec,TM1.step] at hr
    | some l =>
      have hl : l ∈ S := Finset.some_mem_insertNone.mp ha
      have hnext : (TM1.stepAux (M l) v T).l ∈ Finset.insertNone S :=
        TM1.step_supports M hs (by rfl) ha
      change exec (TM1.step M) t (TM1.stepAux (M l) v T) = some b at hr
      obtain ⟨u,hu,he⟩ := ih _ hnext hr
      obtain ⟨v',_,hv',hv⟩ := statement_time M (M l) v T
      refine ⟨v'+u,?_,exec_trans hv he⟩
      have := hC l hl
      nlinarith

@[simp] theorem halts (M : Λ → TM1.Stmt Γ Λ σ) (a : TM1.Cfg Γ Λ σ)
    (h : TM1.step M a = none) : TM0.step (TM1to0.tr M) (TM1to0.trCfg M a) = none := by
  rcases a with ⟨l,v,T⟩
  cases l <;> simp_all [TM1.step,TM1to0.trCfg,TM0.step,TM1to0.tr]

end OneToZero
end PCP.Machine.TMTime

