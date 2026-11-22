/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ArithmeticStream

/-! # Charged polynomial cost of arithmetic streaming programs -/

namespace PCP.Lang.ArithmeticStream

open ArithmeticExpression

variable {n : ℕ}

def updateConstant (ts : Fin n → Term (n + 1)) : ℕ :=
  (parallel (fullTerms ts)).C *
    ((parallel (fullTerms ts)).width + (parallel (fullTerms ts)).csize + 1) + 2

theorem step_cost (ts : Fin n → Term (n + 1)) (st : State (n + 1 + 3) 2)
    (a : ℕ) (xs : List ℕ) (W : ℕ) (hs : st.lists 0 = a :: xs)
    (hr : ∀ i, Nat.size (inputRegs st i) ≤ W) (ha : Nat.size a ≤ W)
    (hl : listSize (st.lists 1) ≤ W) :
    ((step ts).run st).2 ≤ updateConstant ts * (W + 1) := by
  let sp := ((Stmt.pop 0 ((Fin.last n).castAdd 3) (flagReg (n + 1))).run st).1
  have hp : ∀ i : Fin (n + 1), Nat.size (sp.regs (i.castAdd 3)) ≤ W := by
    intro i
    have hf : i.castAdd 3 ≠ flagReg (n + 1) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, flagReg]
      omega
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hlast : (Fin.last n).castAdd 3 ≠ flagReg (n + 1) := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_last, flagReg]
        omega
      simpa [sp, Stmt.run, hs, Function.update, hlast] using ha
    · have hj : j.castSucc.castAdd 3 ≠ (Fin.last n).castAdd 3 := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_castSucc, Fin.val_last]
        omega
      have hf' : j.castSucc.castAdd 3 ≠ flagReg (n + 1) := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_castSucc, flagReg]
        omega
      simpa [sp, Stmt.run, hs, inputRegs, Function.update, hj, hf'] using hr j
  have hpL : listSize (sp.lists 1) ≤ W := by simpa [sp, Stmt.run, hs] using hl
  have hc := parallel_cost (fullTerms ts) sp W hp hpL
  have hpop : ((Stmt.pop 0 ((Fin.last n).castAdd 3) (flagReg (n + 1))).run st).2 =
      Nat.size a + 1 := by simp [Stmt.run, hs]
  rw [step, run_seq_snd, hpop]
  dsimp only [updateConstant]
  change Nat.size a + 1 + ((parallel (fullTerms ts)).run sp).2 + 1 ≤ _
  nlinarith

theorem step_last (ts : Fin n → Term (n + 1)) (st : State (n + 1 + 3) 2) :
    ((step ts).run st).1.regs ((Fin.last n).castAdd 3) = 0 := by
  simpa [step, run_seq_fst, fullTerms, Term.eval] using
    (parallel_spec (fullTerms ts)
      ((Stmt.pop 0 ((Fin.last n).castAdd 3) (flagReg (n + 1))).run st).1).1 (Fin.last n)

theorem iterate_last (ts : Fin n → Term (n + 1)) (st : State (n + 1 + 3) 2)
    (c N : ℕ) (h : st.regs ((Fin.last n).castAdd 3) = 0) :
    (iterate (step ts).run c N st).1.regs ((Fin.last n).castAdd 3) = 0 :=
  iterate_frame _ _ (fun s => s.regs ((Fin.last n).castAdd 3) = 0)
    (fun s _ => step_last ts s) N st h

/-- The bound follows the actual finite prefixes, with no assumption about
configurations that the input stream never reaches. -/
theorem iterate_cost (ts : Fin n → Term (n + 1)) (xs tail : List ℕ)
    (c W : ℕ) (st : State (n + 1 + 3) 2) (hs : st.lists 0 = xs ++ tail)
    (hl : listSize (st.lists 1) ≤ W)
    (ha : ∀ a ∈ xs, Nat.size a ≤ W)
    (hr : ∀ ys zs, xs = ys ++ zs → ∀ i,
      Nat.size (ys.foldl (next ts) (inputRegs st) i) ≤ W) :
    (iterate (step ts).run c xs.length st).2 ≤
      xs.length * (c + updateConstant ts * (W + 1)) := by
  induction xs generalizing st with
  | nil => simp [iterate]
  | cons a xs ih =>
      obtain ⟨hn, h0, h1, _⟩ := step_spec ts st a (xs ++ tail) (by simpa using hs)
      have hb := step_cost ts st a (xs ++ tail) W (by simpa using hs)
        (by simpa using hr [] (a :: xs) rfl) (ha a (by simp)) hl
      have hi := ih ((step ts).run st).1 h0 (by simpa [h1] using hl)
        (fun b hb => ha b (by simp [hb])) (by
          intro ys zs hsplit i
          have h := hr (a :: ys) zs (by simp [hsplit]) i
          simpa [List.foldl_cons, hn] using h)
      simp only [List.length_cons, iterate, Nat.succ_mul]
      omega

def finishConstant (verdict : Term n) : ℕ :=
  2 * ((scalar (verdict.rename Fin.castSucc)).C *
    ((scalar (verdict.rename Fin.castSucc)).width +
      (scalar (verdict.rename Fin.castSucc)).csize + 1)) + 2

theorem finish_cost (verdict : Term n) (st : State (n + 1 + 3) 2) (W : ℕ)
    (hr : ∀ i : Fin (n + 1), Nat.size (st.regs (i.castAdd 3)) ≤ W) :
    ((finish verdict).run st).2 ≤ finishConstant verdict * (W + 1) := by
  let t := verdict.rename Fin.castSucc
  have hc := scalar_cost_inputs t st W hr
  have hv := eval_size_le t (fun i => st.regs (i.castAdd 3)) W hr
  rw [finish, run_seq_snd, run_push_snd, (scalar_spec t st).1]
  dsimp only [finishConstant, t] at *
  nlinarith

def initialConstant (r : Fin n → ℕ) : ℕ :=
  (initializeRegs r).C * ((initializeRegs r).width + (initializeRegs r).csize + 1)

def programConstant (r : Fin n → ℕ) (ts : Fin n → Term (n + 1))
    (verdict : Term n) : ℕ :=
  initialConstant r + updateConstant ts + finishConstant verdict + 10

/-- A linear bit-size bound on reachable configurations gives quadratic charged
cost for the actual input-consuming program. -/
theorem program_cost (r : Fin n → ℕ) (ts : Fin n → Term (n + 1))
    (verdict : Term n) (xs : List ℕ) (W : ℕ)
    (hx : listSize xs ≤ W)
    (hr : ∀ ys zs, xs = ys ++ zs → ∀ i,
      Nat.size (ys.foldl (next ts) r i) ≤ W) :
    (program r ts verdict).cost xs ≤ programConstant r ts verdict * (W + 1) ^ 2 := by
  let p := program r ts verdict
  let si := ((initializeRegs r).run (p.init xs)).1
  let sl := ((Stmt.len 0 (leftReg (n + 1))).run si).1
  let sf := ((Stmt.loop (leftReg (n + 1)) (step ts)).run sl).1
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
  have hin : inputRegs sl = r := by
    funext i
    have hn : i.castSucc.castAdd 3 ≠ leftReg (n + 1) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_castSucc, leftReg]
      omega
    simpa [sl, run_len_fst, inputRegs, Function.update, hn, si] using congrFun hi i
  have hc : sl.regs (leftReg (n + 1)) = xs.length := by
    simp only [sl, run_len_fst, setReg_regs, Function.update_self]
    exact congrArg List.length h0
  have hlast : sl.regs ((Fin.last n).castAdd 3) = 0 := by
    have h := (parallel_spec (fun i => Term.const (withSymbol r 0 i)) (p.init xs)).1
      (Fin.last n)
    have hn : (Fin.last n).castAdd 3 ≠ leftReg (n + 1) := by
      simp [ne_eq, Fin.ext_iff, leftReg]
    simpa [sl, run_len_fst, Function.update, hn, si, initializeRegs, withSymbol, Term.eval]
      using h
  have hsfinal : inputRegs sf = xs.foldl (next ts) r ∧ sf.lists 1 = [] ∧
      sf.regs ((Fin.last n).castAdd 3) = 0 := by
    have ht := iterate_spec ts xs [] (Nat.size xs.length + 1) sl (by simpa using h0)
    have htlast := iterate_last ts sl (Nat.size xs.length + 1) xs.length hlast
    simp only [sf, run_loop_fst, hc]
    exact ⟨ht.1.trans (by rw [hin]), ht.2.2.trans h1, htlast⟩
  have hic : ((initializeRegs r).run (p.init xs)).2 ≤ initialConstant r := by
    have h := parallel_cost (fun i => Term.const (withSymbol r 0 i)) (p.init xs) 0
      (by intro i; simp [Prog.init])
      (by simp [Prog.init, Prog.inL, p, program, listSize])
    simpa [initializeRegs, initialConstant] using h
  have hlen : ((Stmt.len 0 (leftReg (n + 1))).run si).2 =
      listSize xs + Nat.size xs.length + 1 := by
    rw [run_len_snd]
    change listSize (sl.lists 0) + Nat.size (sl.lists 0).length + 1 = _
    rw [h0]
  have hit := iterate_cost ts xs [] (Nat.size xs.length + 1) W sl (by simpa using h0)
    (by simp [h1, listSize]) (fun a ha => (size_le_listSize ha).trans hx)
    (by simpa [hin] using hr)
  have hloop : ((Stmt.loop (leftReg (n + 1)) (step ts)).run sl).2 ≤
      xs.length * (Nat.size xs.length + 1 + updateConstant ts * (W + 1)) +
        Nat.size xs.length + 1 := by
    rw [run_loop_snd, hc]
    omega
  have hfin := finish_cost verdict sf W (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hsfinal.2.2]
    · have h := hr xs [] (by simp) j
      simpa [← hsfinal.1, inputRegs] using h)
  have hn : xs.length ≤ W := (length_le_listSize xs).trans hx
  have hsize : Nat.size xs.length ≤ W := (size_le_self _).trans hn
  change ((initializeRegs r).run (p.init xs)).2 +
    (((Stmt.len 0 (leftReg (n + 1))).run si).2 +
      (((Stmt.loop (leftReg (n + 1)) (step ts)).run sl).2 +
        ((finish verdict).run sf).2 + 1) + 1) + 1 ≤ _
  rw [hlen]
  dsimp only [programConstant]
  have hm := Nat.mul_le_mul hn
    (show Nat.size xs.length + 1 + updateConstant ts * (W + 1) ≤
      W + 1 + updateConstant ts * (W + 1) by omega)
  have hsquare : W * (W + 1) ≤ (W + 1) ^ 2 := by nlinarith
  have hlinear : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hinit' : initialConstant r ≤ initialConstant r * (W + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left (initialConstant r)
      (show 1 ≤ (W + 1) ^ 2 by nlinarith)
    simpa using h
  have hfin' := Nat.mul_le_mul_left (finishConstant verdict) hlinear
  have hloop' : W * (W + 1 + updateConstant ts * (W + 1)) ≤
      (updateConstant ts + 1) * (W + 1) ^ 2 := by
    calc _ = (updateConstant ts + 1) * (W * (W + 1)) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ hsquare
  nlinarith

end PCP.Lang.ArithmeticStream
