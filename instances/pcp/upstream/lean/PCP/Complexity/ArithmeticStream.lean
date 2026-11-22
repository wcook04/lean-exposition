/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticParallel
import PCP.Complexity.ArithmeticLookupLang

/-!
# Streaming arithmetic state machines in the counted-loop language

A fixed vector of arithmetic expressions updates a numeric configuration for
each input symbol. The concrete program consumes exactly the input length;
there is no unbounded search and no time-bound function to evaluate.
-/

namespace PCP.Lang.ArithmeticStream

open ArithmeticExpression

variable {n : ℕ}

def inputRegs (st : State (n + 1 + 3) 2) : Fin n → ℕ :=
  fun i => st.regs (i.castSucc.castAdd 3)

def withSymbol (r : Fin n → ℕ) (a : ℕ) : Fin (n + 1) → ℕ := Fin.lastCases a r

def next (ts : Fin n → Term (n + 1)) (r : Fin n → ℕ) (a : ℕ) : Fin n → ℕ :=
  fun i => (ts i).eval (withSymbol r a)

def fullTerms (ts : Fin n → Term (n + 1)) : Fin (n + 1) → Term (n + 1) :=
  Fin.lastCases (.const 0) ts

def step (ts : Fin n → Term (n + 1)) : Stmt (n + 1 + 3) 2 :=
  .seq (.pop 0 ((Fin.last n).castAdd 3) (flagReg (n + 1))) (parallel (fullTerms ts))

private theorem input_ne_flag (i : Fin (n + 1)) :
    i.castAdd 3 ≠ flagReg (n + 1) := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, flagReg]
  omega

theorem step_spec (ts : Fin n → Term (n + 1)) (st : State (n + 1 + 3) 2)
    (a : ℕ) (xs : List ℕ) (hs : st.lists 0 = a :: xs) :
    inputRegs ((step ts).run st).1 = next ts (inputRegs st) a ∧
    ((step ts).run st).1.lists 0 = xs ∧
    ((step ts).run st).1.lists 1 = st.lists 1 ∧
    ((step ts).run st).1.regs ((Fin.last n).castAdd 3) = 0 := by
  let sp := ((Stmt.pop 0 ((Fin.last n).castAdd 3) (flagReg (n + 1))).run st).1
  have hp : (fun i : Fin (n + 1) => sp.regs (i.castAdd 3)) =
      withSymbol (inputRegs st) a := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [sp, Stmt.run, hs, withSymbol, input_ne_flag]
    · have hj : j.castSucc.castAdd 3 ≠ (Fin.last n).castAdd 3 := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_castSucc, Fin.val_last]
        omega
      simp [sp, Stmt.run, hs, withSymbol, inputRegs, input_ne_flag, hj]
  obtain ⟨hr, hl⟩ := parallel_spec (fullTerms ts) sp
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    simpa [step, run_seq_fst, inputRegs, next, fullTerms, hp, sp] using hr i.castSucc
  · change ((parallel (fullTerms ts)).run sp).1.lists 0 = _
    rw [hl]
    simp [sp, Stmt.run, hs]
  · change ((parallel (fullTerms ts)).run sp).1.lists 1 = _
    rw [hl]
    simp [sp, Stmt.run, hs]
  · simpa [step, run_seq_fst, fullTerms, Term.eval, sp] using hr (Fin.last n)

theorem iterate_spec (ts : Fin n → Term (n + 1)) (xs tail : List ℕ)
    (c : ℕ) (st : State (n + 1 + 3) 2) (hs : st.lists 0 = xs ++ tail) :
    inputRegs (iterate (step ts).run c xs.length st).1 =
      xs.foldl (next ts) (inputRegs st) ∧
    (iterate (step ts).run c xs.length st).1.lists 0 = tail ∧
    (iterate (step ts).run c xs.length st).1.lists 1 = st.lists 1 := by
  induction xs generalizing st with
  | nil => simp_all [iterate]
  | cons a xs ih =>
      obtain ⟨hr, h0, h1, _⟩ := step_spec ts st a (xs ++ tail) (by simpa using hs)
      obtain ⟨hi, hi0, hi1⟩ := ih ((step ts).run st).1 h0
      refine ⟨?_, hi0, hi1.trans h1⟩
      simpa only [List.length_cons, iterate_succ_fst, List.foldl_cons, hr] using hi

def initializeRegs (r : Fin n → ℕ) : Stmt (n + 1 + 3) 2 :=
  parallel (fun i => Term.const (withSymbol r 0 i))

theorem initializeRegs_spec (r : Fin n → ℕ) (st : State (n + 1 + 3) 2) :
    inputRegs ((initializeRegs r).run st).1 = r ∧
    ((initializeRegs r).run st).1.lists = st.lists := by
  obtain ⟨hr, hl⟩ := parallel_spec (fun i => Term.const (withSymbol r 0 i)) st
  refine ⟨?_, hl⟩
  funext i
  simpa [initializeRegs, inputRegs, withSymbol, Term.eval] using hr i.castSucc

def finish (verdict : Term n) : Stmt (n + 1 + 3) 2 :=
  .seq (scalar (verdict.rename Fin.castSucc)) (.push 1 (leftReg (n + 1)))

theorem finish_spec (verdict : Term n) (st : State (n + 1 + 3) 2) :
    ((finish verdict).run st).1.lists 1 =
      verdict.eval (inputRegs st) :: st.lists 1 := by
  obtain ⟨hr, hl⟩ := scalar_spec (verdict.rename Fin.castSucc) st
  simp only [finish, run_seq_fst, run_push_fst, setList_lists, Function.update_self, hr, hl,
    Term.eval_rename]
  rfl

def program (r : Fin n → ℕ) (ts : Fin n → Term (n + 1)) (verdict : Term n) : Prog where
  R := n + 1 + 3
  Q := 2
  hQ := le_rfl
  body := .seq (initializeRegs r) (.seq (.len 0 (leftReg (n + 1)))
    (.seq (.loop (leftReg (n + 1)) (step ts)) (finish verdict)))

/-- The compiled stream program has exactly the specified finite-fold semantics. -/
theorem program_run (r : Fin n → ℕ) (ts : Fin n → Term (n + 1))
    (verdict : Term n) (xs : List ℕ) :
    (program r ts verdict).run xs = [verdict.eval (xs.foldl (next ts) r)] := by
  let p := program r ts verdict
  let si := ((initializeRegs r).run (p.init xs)).1
  let sl := ((Stmt.len 0 (leftReg (n + 1))).run si).1
  obtain ⟨hi, hl⟩ := initializeRegs_spec r (p.init xs)
  have hsi : si.lists = (p.init xs).lists := hl
  have h0 : sl.lists 0 = xs := by
    change si.lists 0 = xs
    rw [hsi]
    simp [Prog.init, Prog.inL, p, program]
  have h1 : sl.lists 1 = [] := by
    change si.lists 1 = []
    rw [hsi]
    simp [Prog.init, Prog.inL, p, program]
  have hr : inputRegs sl = r := by
    funext i
    have hn : i.castSucc.castAdd 3 ≠ leftReg (n + 1) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_castSucc, leftReg]
      omega
    have hh := congrFun hi i
    simpa [sl, run_len_fst, inputRegs, Function.update, hn, si] using hh
  have hc : sl.regs (leftReg (n + 1)) = xs.length := by
    simp only [sl, run_len_fst, setReg_regs, Function.update_self]
    exact congrArg List.length h0
  have hit := iterate_spec ts xs [] (Nat.size xs.length + 1) sl (by simpa using h0)
  change ((finish verdict).run ((Stmt.loop (leftReg (n + 1)) (step ts)).run sl).1).1.lists 1 = _
  rw [finish_spec, run_loop_fst, hc, hit.1, hr, hit.2.2, h1]

end PCP.Lang.ArithmeticStream
