/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticExpressionLang
import PCP.Complexity.LangLookup

/-!
# Arithmetic assignments and indexed reads in one register file

These routines share a fixed source-register prefix, preserve the source list,
and restore the expression stack. An indexed read uses the bounded stored-list
lookup routine: even an out-of-range binary index performs bounded work.
-/

namespace PCP.Lang.ArithmeticLookup

open ArithmeticExpression

variable {n : ℕ}

def inputs (st : State (n + 4) 3) (i : Fin n) : ℕ := st.regs (i.castAdd 4)

def expr (t : Term n) : Stmt (n + 4) 3 :=
  (scalar t).rename Fin.castSucc Fin.castSucc

theorem expr_spec (t : Term n) (st : State (n + 4) 3) :
    ((expr t).run st).1.regs ((leftReg n).castSucc) = t.eval (inputs st) ∧
    (∀ i, inputs ((expr t).run st).1 i = inputs st i) ∧
    ((expr t).run st).1.lists 0 = st.lists 0 ∧
    ((expr t).run st).1.lists 1 = st.lists 1 := by
  have h := congrArg Prod.fst ((scalar t).run_rename Fin.castSucc Fin.castSucc
    (Fin.castSucc_injective _) (Fin.castSucc_injective _) st)
  have hreg := congrArg (fun s : State (n + 3) 2 => s.regs (leftReg n)) h
  have h0 := congrArg (fun s : State (n + 3) 2 => s.lists 0) h
  have h1 := congrArg (fun s : State (n + 3) 2 => s.lists 1) h
  refine ⟨hreg.trans (scalar_spec t _).1, ?_, h0.trans (scalar_preserves_source t _),
    h1.trans (scalar_spec t _).2⟩
  intro i
  have hi := congrArg (fun s : State (n + 3) 2 => s.regs (i.castAdd 3)) h
  exact hi.trans (scalar_preserves_input t i _)

def assign (dest : Fin n) (t : Term n) : Stmt (n + 4) 3 :=
  .seq (expr t) (.assign (dest.castAdd 4) (.var ((leftReg n).castSucc)))

theorem assign_spec (dest : Fin n) (t : Term n) (st : State (n + 4) 3) :
    inputs ((assign dest t).run st).1 = Function.update (inputs st) dest (t.eval (inputs st)) ∧
    ((assign dest t).run st).1.lists 0 = st.lists 0 ∧
    ((assign dest t).run st).1.lists 1 = st.lists 1 := by
  obtain ⟨he, hi, h0, h1⟩ := expr_spec t st
  refine ⟨?_, ?_, ?_⟩
  · funext i
    by_cases hd : i = dest
    · subst i
      simp [inputs, assign, run_seq_fst, run_assign_fst, Expr.eval, he]
    · have hc : i.castAdd 4 ≠ dest.castAdd 4 := by
        simpa only [ne_eq, Fin.ext_iff, Fin.val_castAdd] using hd
      simpa [inputs, assign, run_seq_fst, run_assign_fst, Function.update, hd, hc]
        using hi i
  · simpa [assign, run_seq_fst, run_assign_fst] using h0
  · simpa [assign, run_seq_fst, run_assign_fst] using h1

/-- Scratch index, destination, flag, and length, respectively. -/
def lookupRegs (dest : Fin n) : Fin 4 → Fin (n + 4) :=
  ![⟨n, by omega⟩, dest.castAdd 4, ⟨n + 2, by omega⟩, ⟨n + 3, by omega⟩]

def lookupLists : Fin 2 → Fin 3 := ![0, 2]

theorem lookupRegs_injective (dest : Fin n) : Function.Injective (lookupRegs dest) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [lookupRegs, Fin.ext_iff]
  all_goals omega

theorem lookupLists_injective : Function.Injective lookupLists := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [lookupLists]

theorem lookupRegs_outside (dest i : Fin n) (hi : i ≠ dest) :
    ∀ j, lookupRegs dest j ≠ i.castAdd 4 := by
  intro j hj
  have hv := congrArg Fin.val hj
  have hne : i.val ≠ dest.val := fun he => hi (Fin.ext he)
  fin_cases j <;> simp [lookupRegs] at hv <;> omega


def lookup (dest : Fin n) (t : Term n) : Stmt (n + 4) 3 :=
  .seq (expr t) (Lookup.lookup.rename (lookupRegs dest) lookupLists)

/-- The indexed read stores exactly the zero-padded list value and preserves both caller lists. -/
theorem lookup_spec (dest : Fin n) (t : Term n) (st : State (n + 4) 3) :
    inputs ((lookup dest t).run st).1 =
      Function.update (inputs st) dest ((st.lists 0).getD (t.eval (inputs st)) 0) ∧
    ((lookup dest t).run st).1.lists 0 = st.lists 0 ∧
    ((lookup dest t).run st).1.lists 1 = st.lists 1 := by
  let se := ((expr t).run st).1
  obtain ⟨he, hi, h0, h1⟩ := expr_spec t st
  have h := congrArg Prod.fst (Lookup.lookup.run_rename (lookupRegs dest) lookupLists
    (lookupRegs_injective dest) lookupLists_injective se)
  have hv := congrArg (fun s : State 4 2 => s.regs 1) h
  have hs := congrArg (fun s : State 4 2 => s.lists 0) h
  simp only [State.restrict_regs, State.restrict_lists] at hv hs
  refine ⟨?_, ?_, ?_⟩
  · funext i
    by_cases hd : i = dest
    · subst i
      rw [Lookup.lookup_run] at hv
      simpa [inputs, lookup, run_seq_fst, lookupRegs, lookupLists, se, ← he, h0, leftReg]
        using hv
    · have hf := Lookup.lookup.run_rename_reg_outside (lookupRegs dest) lookupLists
        (i.castAdd 4) (lookupRegs_outside dest i hd) se
      simpa [inputs, lookup, run_seq_fst, Function.update, hd, se] using hf.trans (hi i)
  · rw [Lookup.lookup_preserves_source] at hs
    simpa [lookup, run_seq_fst, lookupLists, se, h0] using hs
  · have hf := Lookup.lookup.run_rename_list_outside (lookupRegs dest) lookupLists 1
        (by intro j; fin_cases j <;> decide) se
    simpa [lookup, run_seq_fst, se] using hf.trans h1

/-- Fixed finite sequences of arithmetic assignments and bounded source reads. -/
inductive Code (n : ℕ)
  | assign : Fin n → Term n → Code n
  | lookup : Fin n → Term n → Code n
  | seq : Code n → Code n → Code n

def Code.eval (input : List ℕ) : Code n → (Fin n → ℕ) → (Fin n → ℕ)
  | .assign dest t, r => Function.update r dest (t.eval r)
  | .lookup dest t, r => Function.update r dest (input.getD (t.eval r) 0)
  | .seq a b, r => b.eval input (a.eval input r)

def Code.compile : Code n → Stmt (n + 4) 3
  | .assign dest t => ArithmeticLookup.assign dest t
  | .lookup dest t => ArithmeticLookup.lookup dest t
  | .seq a b => .seq a.compile b.compile

theorem Code.spec (p : Code n) (st : State (n + 4) 3) :
    inputs (p.compile.run st).1 = p.eval (st.lists 0) (inputs st) ∧
    (p.compile.run st).1.lists 0 = st.lists 0 ∧
    (p.compile.run st).1.lists 1 = st.lists 1 := by
  induction p generalizing st with
  | assign dest t => exact assign_spec dest t st
  | lookup dest t => exact lookup_spec dest t st
  | seq a b iha ihb =>
      obtain ⟨ha, h0a, h1a⟩ := iha st
      obtain ⟨hb, h0b, h1b⟩ := ihb (a.compile.run st).1
      simp only [Code.compile, run_seq_fst, Code.eval]
      exact ⟨hb.trans (by rw [h0a, ha]), h0b.trans h0a, h1b.trans h1a⟩

end PCP.Lang.ArithmeticLookup

namespace PCP.Lang.ArithmeticExpression

/-- Substitute source-register names without changing arithmetic syntax. -/
def Term.rename {n m : ℕ} (f : Fin n → Fin m) : Term n → Term m
  | .const a => .const a
  | .input i => .input (f i)
  | .bin o a b => .bin o (a.rename f) (b.rename f)
  | .cond c a b => .cond (c.rename f) (a.rename f) (b.rename f)

@[simp] theorem Term.eval_rename {n m : ℕ} (f : Fin n → Fin m) (t : Term n) (r : Fin m → ℕ) :
    (t.rename f).eval r = t.eval (r ∘ f) := by
  induction t <;> simp_all [Term.rename, Term.eval, Function.comp_def]

end PCP.Lang.ArithmeticExpression
