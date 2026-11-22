import PCP.Complexity.LangSplitFirst
import Mathlib.Tactic

/-!
# Charged cost of the first-word separator scan
-/

namespace PCP.Lang.SplitFirst

/-- All public symbol codes fit in two bits; the activity flag is a bit. -/
def Bounded (st : State 5 2) : Prop :=
  st.regs 3 ≤ 1 ∧ st.regs 4 = 2 ∧ ∀ v ∈ st.lists 0, v ≤ 2

/-- Every pass has constant source cost and retains the scan's bounded values. -/
theorem body_bounded_cost (st : State 5 2) (h : Bounded st) :
    Bounded (body.run st).1 ∧ (body.run st).2 ≤ 20 := by
  by_cases hz : st.regs 3 = 0
  · simpa [body, Stmt.run, hz] using h
  · have ha : st.regs 3 = 1 := by have := h.1; omega
    cases hl : st.lists 0 with
    | nil => simp [Bounded, body, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
        Function.update, ha, hl, h.2.1, show Nat.size 2 = 2 from rfl]
    | cons v vs =>
      have hv : v ≤ 2 := h.2.2 v (by simp [hl])
      have hvs : ∀ w ∈ vs, w ≤ 2 := fun w hw => h.2.2 w (by simp [hl, hw])
      have hsize : Nat.size v ≤ 2 := (size_le_self _).trans hv
      by_cases heq : v = 2
      · simpa [Bounded, body, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
          Function.update, ha, hl, h.2.1, heq, show Nat.size 2 = 2 from rfl] using hvs
      · simp only [Bounded, body, Fin.isValue, Stmt.run, ha, ne_eq, one_ne_zero,
          not_false_eq_true, ite_true, hl, Expr.eval, setReg_regs, Function.update,
          Fin.reduceEq, dite_false, dite_true, setList_regs, h.2.1, heq, Expr.cost,
          Expr.readSize, show Nat.size 2 = 2 from rfl, Nat.size_zero, add_zero,
          not_true_eq_false, ite_false, setReg_lists, setList_lists, Nat.size_one,
          le_refl, zero_ne_one, true_and, Order.add_one_le_iff]
        exact ⟨hvs, by omega⟩

/-- The complete splitter has quadratic cost in its stored input size. -/
theorem program_cost (st : State 5 2)
    (hb : ∀ v ∈ st.lists 0, v ≤ 2) (he : st.lists 1 = []) :
    (program.run st).2 ≤ 100 * (listSize (st.lists 0) + 1) ^ 2 := by
  let B := listSize (st.lists 0)
  let n := (st.lists 0).length
  let s := (setup.run st).1
  have hn : n ≤ B := length_le_listSize _
  have hsize : Nat.size n ≤ B := (size_le_self _).trans hn
  have hs0 : s.regs 0 = n := by simp [s, setup, Stmt.run, Expr.eval, Function.update, n]
  have hsb : Bounded s := by
    simpa [Bounded, s, setup, Stmt.run, Expr.eval, Function.update] using hb
  have hss : s.Sized (B + 2) := by
    constructor
    · intro r
      fin_cases r
      · simpa [s, setup, Stmt.run, Expr.eval, Function.update, n] using
          hsize.trans (show B ≤ B + 2 by omega)
      all_goals simp [s, setup, Stmt.run, Expr.eval, Function.update,
        show Nat.size 2 = 2 from rfl]
    · intro L
      fin_cases L
      · change listSize (st.lists 0) ≤ B + 2
        omega
      · simp [s, setup, Stmt.run, he, listSize]
  have hit := iterate_cost_le body.run (Nat.size n + 1) 20 Bounded
    (fun u hu => (body_bounded_cost u hu).1)
    (fun u hu => (body_bounded_cost u hu).2) n s hsb
  have hloop : ((Stmt.loop 0 body).run s).2 ≤ B * (B + 21) + B + 1 := by
    rw [run_loop_snd, hs0]
    have hm := Nat.mul_le_mul hn (show Nat.size n + 1 + 20 ≤ B + 21 by omega)
    omega
  have hspace := (Stmt.run_sized (.loop 0 body) s (B + 2) hss).2 1
  have hsetup : (setup.run st).2 ≤ 2 * B + 15 := by
    simp only [setup, run_seq_snd, run_len_snd, run_len_fst, run_assign_fst, Expr.eval]
    simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    change B + Nat.size n + 1 + (1 + (1 + (3 + 5 + 1) + 1) + 1) + 1 ≤ _
    omega
  simp only [program, run_seq_snd, run_rev_snd]
  change (setup.run st).2 + (((Stmt.loop 0 body).run s).2 +
    (listSize (((Stmt.loop 0 body).run s).1.lists 1) + 1) + 1) + 1 ≤ _
  change _ ≤ 100 * (B + 1) ^ 2
  nlinarith

end PCP.Lang.SplitFirst
