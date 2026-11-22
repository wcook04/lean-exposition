import PCP.Complexity.LangCost
import PCP.Complexity.LangSpace
import PCP.Algebraic.ThreeColorEncoding
import Mathlib.Tactic

/-!
# Reading the unary public graph header

The program counts the leading one bits and retains the entire original input.
It is defined on every natural-number list, including missing delimiters.
-/

namespace PCP.Lang.GraphHeader

def body : Stmt 6 2 :=
  .ite 2 (.seq (.pop 1 4 5) (.seq (.assign 5 (.eq 4 3))
    (.ite 5 (.assign 1 (.add 1 3)) (.assign 2 (.const 0))))) .skip

def setup : Stmt 6 2 :=
  .seq (.copy 0 1) (.seq (.len 0 0) (.seq (.assign 1 (.const 0))
    (.seq (.assign 2 (.const 1)) (.assign 3 (.const 1)))))

def program : Stmt 6 2 := .seq setup (.loop 0 body)

def count (xs : List ℕ) : ℕ := (xs.takeWhile (· == 1)).length

theorem body_inactive (st : State 6 2) (ha : st.regs 2 = 0) :
    (body.run st).1 = st := by simp [body, Stmt.run, ha]

theorem iterate_inactive (c n : ℕ) (st : State 6 2) (ha : st.regs 2 = 0) :
    (iterate body.run c n st).1 = st := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_fst, body_inactive st ha, ih]

theorem body_one (xs : List ℕ) (st : State 6 2)
    (hl : st.lists 1 = 1 :: xs) (ha : st.regs 2 = 1) (h1 : st.regs 3 = 1) :
    (body.run st).1.lists 1 = xs ∧ (body.run st).1.regs 1 = st.regs 1 + 1 ∧
      (body.run st).1.regs 2 = 1 ∧ (body.run st).1.regs 3 = 1 := by
  simp [body, Stmt.run, Expr.eval, Function.update, hl, ha, h1]

theorem body_other (v : ℕ) (xs : List ℕ) (st : State 6 2)
    (hl : st.lists 1 = v :: xs) (ha : st.regs 2 = 1) (h1 : st.regs 3 = 1) (hv : v ≠ 1) :
    (body.run st).1.regs 1 = st.regs 1 ∧ (body.run st).1.regs 2 = 0 := by
  simp [body, Stmt.run, Expr.eval, Function.update, hl, ha, h1, hv]

/-- The counted scan also handles an all-one word without a delimiter. -/
theorem iterate_count (xs : List ℕ) (c : ℕ) (st : State 6 2)
    (hl : st.lists 1 = xs) (ha : st.regs 2 = 1) (h1 : st.regs 3 = 1) :
    (iterate body.run c xs.length st).1.regs 1 = st.regs 1 + count xs := by
  induction xs generalizing st with
  | nil => simp [iterate, count]
  | cons v xs ih =>
    by_cases hv : v = 1
    · subst v
      have hb := body_one xs st hl ha h1
      rw [List.length_cons, iterate_succ_fst, ih _ hb.1 hb.2.2.1 hb.2.2.2, hb.2.1]
      simp [count, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hb := body_other v xs st hl ha h1 hv
      rw [List.length_cons, iterate_succ_fst, iterate_inactive _ _ _ hb.2, hb.1]
      simp [count, hv]

/-- Numeric header parsing preserves the original stored public input. -/
theorem program_run (st : State 6 2) :
    (program.run st).1.regs 1 = count (st.lists 0) ∧
      (program.run st).1.lists 0 = st.lists 0 := by
  let s := (setup.run st).1
  have hl : s.lists 1 = st.lists 0 := by simp [s, setup, Stmt.run]
  have ha : s.regs 2 = 1 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have h1 : s.regs 3 = 1 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hlen : s.regs 0 = (st.lists 0).length := by
    simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hz : s.regs 1 = 0 := by simp [s, setup, Stmt.run, Expr.eval, Function.update]
  have hout := iterate_count (st.lists 0) (Nat.size (st.lists 0).length + 1) s hl ha h1
  constructor
  · simp only [program, run_seq_fst, run_loop_fst]
    change (iterate body.run (Nat.size (s.regs 0) + 1) (s.regs 0) s).1.regs 1 = _
    rw [hlen]
    simpa only [hz, zero_add] using hout
  · exact run_lists_frame program 0 (by decide) st

theorem count_bits (xs : List Bool) : count (xs.map Bool.toNat) =
    PCP.Algebraic.ThreeColorEncoding.vertexCount xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b
    · simp [count, PCP.Algebraic.ThreeColorEncoding.vertexCount]
    · simpa [count, PCP.Algebraic.ThreeColorEncoding.vertexCount] using ih

/-- The result is the exact vertex count used by the graph decoder. -/
theorem program_bits (xs : List Bool) (st : State 6 2) (hl : st.lists 0 = xs.map Bool.toNat) :
    (program.run st).1.regs 1 = PCP.Algebraic.ThreeColorEncoding.vertexCount xs := by
  rw [(program_run st).1, hl, count_bits]

/-- The accumulator and unread suffix jointly fit in the initial input length. -/
def Bounded (B : ℕ) (st : State 6 2) : Prop :=
  st.regs 2 ≤ 1 ∧ st.regs 3 = 1 ∧ st.regs 1 + (st.lists 1).length ≤ B ∧
    ∀ v ∈ st.lists 1, v ≤ 1

theorem body_bounded_cost (B : ℕ) (st : State 6 2) (hb : Bounded B st) :
    Bounded B (body.run st).1 ∧ (body.run st).2 ≤ 2 * B + 30 := by
  by_cases hz : st.regs 2 = 0
  · simp only [body, Stmt.run, hz, ne_eq, not_true_eq_false, ite_false,
      Nat.size_zero, add_zero]
    exact ⟨hb, by omega⟩
  · have ha : st.regs 2 = 1 := by have := hb.1; omega
    cases hl : st.lists 1 with
    | nil =>
      have hacc := hb.2.2.1
      simp only [hl, List.length_nil, add_zero] at hacc
      simp [Bounded, body, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
        Function.update, ha, hl, hb.2.1, hacc]
    | cons v vs =>
      have hv : v ≤ 1 := hb.2.2.2 v (by simp [hl])
      have hvs : ∀ w ∈ vs, w ≤ 1 := fun w hw => hb.2.2.2 w (by simp [hl, hw])
      have hacc : st.regs 1 + vs.length + 1 ≤ B := by
        have := hb.2.2.1
        simpa only [hl, List.length_cons, Nat.add_assoc] using this
      have hs : Nat.size (st.regs 1) ≤ B := (size_le_self _).trans (by omega)
      have hs' : Nat.size (st.regs 1 + 1) ≤ B := (size_le_self _).trans (by omega)
      have hv' : v = 0 ∨ v = 1 := by omega
      rcases hv' with rfl | rfl
      · simpa [Bounded, body, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
          Function.update, ha, hl, hb.2.1] using
          And.intro (show st.regs 1 + vs.length ≤ B by omega) hvs
      · simp only [Bounded, body, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
          Function.update, ha, hl, hb.2.1, setReg_regs, setReg_lists, setList_regs,
          setList_lists, Fin.reduceEq, dite_false, dite_true, ne_eq, one_ne_zero,
          not_false_eq_true, ite_true, Nat.size_one, Nat.size_zero, le_refl,
          true_and]
        exact ⟨⟨by omega, hvs⟩, by omega⟩

/-- Charged running time is quadratic in the size of the stored binary graph. -/
theorem program_cost (st : State 6 2) (hb : ∀ v ∈ st.lists 0, v ≤ 1) :
    (program.run st).2 ≤ 100 * (listSize (st.lists 0) + 1) ^ 2 := by
  let B := listSize (st.lists 0)
  let n := (st.lists 0).length
  let s := (setup.run st).1
  have hn : n ≤ B := length_le_listSize _
  have hs : Nat.size n ≤ B := (size_le_self _).trans hn
  have hsb : Bounded B s := by
    simpa [Bounded, s, setup, Stmt.run, Expr.eval, Function.update] using And.intro hn hb
  have hsn : s.regs 0 = n := by simp [s, setup, Stmt.run, Expr.eval, Function.update, n]
  have hit := iterate_cost_le body.run (Nat.size n + 1) (2 * B + 30) (Bounded B)
    (fun u hu => (body_bounded_cost B u hu).1)
    (fun u hu => (body_bounded_cost B u hu).2) n s hsb
  have hloop : ((Stmt.loop 0 body).run s).2 ≤ B * (3 * B + 31) + B + 1 := by
    rw [run_loop_snd, hsn]
    have hm := Nat.mul_le_mul hn (show Nat.size n + 1 + (2 * B + 30) ≤ 3 * B + 31 by omega)
    omega
  have hsetup : (setup.run st).2 ≤ 3 * B + 20 := by
    simp only [setup, run_seq_snd, run_copy_snd, run_copy_fst, run_len_snd,
      run_len_fst, run_assign_fst, Expr.eval]
    simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    change B + 1 + (B + Nat.size n + 1 + (1 + (3 + 3 + 1) + 1) + 1) + 1 ≤ _
    omega
  simp only [program, run_seq_snd]
  change (setup.run st).2 + ((Stmt.loop 0 body).run s).2 + 1 ≤ 100 * (B + 1) ^ 2
  nlinarith

end PCP.Lang.GraphHeader
