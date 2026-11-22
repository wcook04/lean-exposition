/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanMaskEnumerationCost

/-!
# Stored support containment

The loop compares successive low bits of two numeric masks. Width and inputs
are preserved, and a zero-or-one flag records squarefree support containment.
-/

namespace PCP.Lang.BooleanMaskSubset

open PCP.Algebraic BooleanLoops

/-- Containment of the low fixed-width characteristic words. -/
def Contains (t a b : ℕ) : Prop :=
  ∀ i : Fin t, a / 2 ^ i.val % 2 ≤ b / 2 ^ i.val % 2

instance (t a b : ℕ) : Decidable (Contains t a b) :=
  inferInstanceAs (Decidable (∀ i : Fin t, a / 2 ^ i.val % 2 ≤ b / 2 ^ i.val % 2))

theorem contains_succ (t a b : ℕ) :
    Contains (t + 1) a b ↔ a % 2 ≤ b % 2 ∧ Contains t (a / 2) (b / 2) := by
  simp [Contains, Fin.forall_fin_succ, pow_succ', Nat.div_div_eq_div_mul]

theorem truth_contains_succ (t a b : ℕ) :
    truth (Contains (t + 1) a b) =
      truth (a % 2 ≤ b % 2) * truth (Contains t (a / 2) (b / 2)) := by
  simp only [truth, contains_succ]
  split_ifs <;> simp_all

def body : Stmt 10 1 :=
  .seq (.assign 6 (.mod 4 8)) (.seq (.assign 7 (.mod 5 8))
    (.seq (.assign 6 (.lt 7 6)) (.seq (.assign 6 (.sub 9 6))
      (.seq (.assign 3 (.mul 3 6)) (.seq (.assign 4 (.div 4 8))
        (.assign 5 (.div 5 8)))))))

theorem body_step (st : State 10 1) (h8 : st.regs 8 = 2) (h9 : st.regs 9 = 1) :
    (body.run st).1.regs 3 = st.regs 3 * truth (st.regs 4 % 2 ≤ st.regs 5 % 2) ∧
      (body.run st).1.regs 4 = st.regs 4 / 2 ∧
      (body.run st).1.regs 5 = st.regs 5 / 2 ∧
      (body.run st).1.regs 8 = 2 ∧ (body.run st).1.regs 9 = 1 := by
  by_cases h : st.regs 5 % 2 < st.regs 4 % 2
  · have hn : ¬ st.regs 4 % 2 ≤ st.regs 5 % 2 := by omega
    simp [body, Stmt.run, Expr.eval, Function.update, h8, h9, h, truth, hn]
  · have hn : st.regs 4 % 2 ≤ st.regs 5 % 2 := by omega
    simp [body, Stmt.run, Expr.eval, Function.update, h8, h9, h, truth, hn]

theorem iterate_result (c n : ℕ) (st : State 10 1)
    (h8 : st.regs 8 = 2) (h9 : st.regs 9 = 1) :
    (iterate body.run c n st).1.regs 3 =
      st.regs 3 * truth (Contains n (st.regs 4) (st.regs 5)) := by
  induction n generalizing st with
  | zero => simp [iterate, truth, Contains]
  | succ n ih =>
    obtain ⟨h3, h4, h5, ht, ho⟩ := body_step st h8 h9
    rw [iterate_succ_fst, ih _ ht ho, h3, h4, h5, truth_contains_succ, Nat.mul_assoc]

/-- Width `0` and masks `1`, `2` are preserved; result flag is `3`. -/
def subset : Stmt 10 1 :=
  .seq (.assign 4 (.var 1)) (.seq (.assign 5 (.var 2))
    (.seq (.assign 3 (.const 1)) (.seq (.assign 8 (.const 2))
      (.seq (.assign 9 (.const 1)) (.loop 0 body)))))

theorem subset_run (st : State 10 1) :
    (subset.run st).1.regs 3 = truth (Contains (st.regs 0) (st.regs 1) (st.regs 2)) := by
  simp only [subset, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  rw [iterate_result _ _ _ (by simp [Function.update]) (by simp)]
  simp [Function.update]

/-- The fixed-width numeric test is precisely semantic finite-set containment. -/
theorem contains_iff (t : ℕ) (a b : Fin (2 ^ t)) :
    Contains t a.val b.val ↔ (BooleanCoefficientIndex.subsetCodeEquiv t).symm a ⊆
      (BooleanCoefficientIndex.subsetCodeEquiv t).symm b := by
  have hbit (x y : Fin 2) : x.val ≤ y.val ↔ (x = 1 → y = 1) := by
    fin_cases x <;> fin_cases y <;> decide
  change (∀ i : Fin t, ((@finFunctionFinEquiv 2 t).symm a i).val ≤
    ((@finFunctionFinEquiv 2 t).symm b i).val) ↔
    BooleanCoefficientIndex.unmask ((@finFunctionFinEquiv 2 t).symm a) ⊆
      BooleanCoefficientIndex.unmask ((@finFunctionFinEquiv 2 t).symm b)
  simp only [BooleanCoefficientIndex.unmask, Finset.subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and, hbit]

/-- A fixed syntax-dependent stage constant, independent of masks and width. -/
def passConstant : ℕ := body.C * (body.width + body.csize + 1)

theorem body_cost (st : State 10 1) (b : ℕ)
    (h8 : st.regs 8 = 2) (h9 : st.regs 9 = 1) (h3 : st.regs 3 ≤ 1)
    (h4 : Nat.size (st.regs 4) ≤ b) (h5 : Nat.size (st.regs 5) ≤ b) :
    (body.run st).2 ≤ passConstant * (b + 3) := by
  apply loopFree_cost_le body (by decide) st (b + 2)
  · intro x hx
    have hu : body.uses = [4, 8, 5, 8, 9, 3, 4, 8, 5, 8] := rfl
    rw [hu] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | exact h4.trans (by omega)
    | exact h5.trans (by omega)
    | exact (size_le_one_of_le_one h3).trans (by omega)
    | rw [h8]; exact (show Nat.size 2 = 2 from rfl).le.trans (by omega)
    | rw [h9]; exact (show Nat.size 1 = 1 from rfl).le.trans (by omega)
  · simp [body, Stmt.lUses]

/-- Support containment has polynomial cost in width and the two binary input sizes. -/
theorem subset_cost (st : State 10 1) :
    (subset.run st).2 ≤ (passConstant + 30) *
      (st.regs 0 + Nat.size (st.regs 1) + Nat.size (st.regs 2) + 3) ^ 2 := by
  let t := st.regs 0
  let b := Nat.size (st.regs 1) + Nat.size (st.regs 2)
  let s := setReg (setReg (setReg (setReg (setReg st 4 (st.regs 1))
    5 (st.regs 2)) 3 1) 8 2) 9 1
  have hit := iterate_cost_le body.run (Nat.size t + 1) (passConstant * (b + 3))
    (fun u => u.regs 8 = 2 ∧ u.regs 9 = 1 ∧ u.regs 3 ≤ 1 ∧
      Nat.size (u.regs 4) ≤ b ∧ Nat.size (u.regs 5) ≤ b)
    (by
      intro u hu
      obtain ⟨h3, h4, h5, ht, ho⟩ := body_step u hu.1 hu.2.1
      refine ⟨ht, ho, ?_, ?_, ?_⟩
      · rw [h3]
        have hb := truth_lt_two (u.regs 4 % 2 ≤ u.regs 5 % 2)
        nlinarith [hu.2.2.1]
      · rw [h4]; exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hu.2.2.2.1
      · rw [h5]; exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hu.2.2.2.2)
    (fun u hu => body_cost u b hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2) t s
    (by simp [s, b, Function.update])
  have hsz : Nat.size t ≤ t := size_le_self _
  have hit' : (iterate body.run (Nat.size t + 1) t s).2 ≤
      t * (t + 1 + passConstant * (b + 3)) :=
    hit.trans (Nat.mul_le_mul_left _ (by omega))
  simp only [subset, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd,
    setReg_regs, Function.update, Fin.reduceEq, dite_false]
  change (Expr.var 1).cost st.regs + ((Expr.var 2).cost (setReg st 4 (st.regs 1)).regs +
    ((Expr.const 1).cost _ + ((Expr.const 2).cost _ + ((Expr.const 1).cost _ +
      ((iterate body.run (Nat.size t + 1) t s).2 + Nat.size t + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, Nat.size_one, show Nat.size 2 = 2 from rfl]
  have hb : Nat.size (st.regs 1) + Nat.size (st.regs 2) = b := rfl
  change _ ≤ (passConstant + 30) * (t + Nat.size (st.regs 1) + Nat.size (st.regs 2) + 3) ^ 2
  rw [Nat.add_assoc t, hb]
  nlinarith [Nat.zero_le (passConstant * t ^ 2), Nat.zero_le (passConstant * b ^ 2),
    Nat.zero_le (t ^ 2), Nat.zero_le (b ^ 2)]

end PCP.Lang.BooleanMaskSubset
