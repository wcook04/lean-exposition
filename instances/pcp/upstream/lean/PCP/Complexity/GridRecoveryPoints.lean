import PCP.Complexity.GridRecoveryCost
import PCP.Algebraic.FieldQueryArithmetic

/-!
# Both materialized certificate points of the derived grid test

The first point appends zero coordinates. The second appends the actual
coordinatewise grid-vanishing products. Both use the production sum-domain order.
-/

namespace PCP.Lang.GridRecovery

open PCP.Algebraic BinaryFieldCode

variable {t : ℕ} [NeZero t]

def assemble : Stmt 41 17 := .seq (.copy 7 15) (.seq (.assign 40 (.const 0))
  (.seq (.len 12 39) (.seq (.loop 39 (.push 15 40))
    (.seq (.copy 12 13) (.seq (.rev 13) (.seq (.revApp 13 15) (.revApp 13 16)))))))

def points : Stmt 41 17 := .seq program assemble

theorem iterate_push {R Q : ℕ} (r : Fin R) (L : Fin Q) (c n : ℕ) (st : State R Q) :
    (iterate (Stmt.push L r).run c n st).1 =
      setList st L (List.replicate n (st.regs r) ++ st.lists L) := by
  induction n generalizing st with
  | zero =>
      cases st
      simp [iterate, setList]
  | succ n ih =>
      rw [iterate_succ_fst, ih]
      simp only [run_push_fst, setList_regs, setList_lists, Function.update_self,
        List.replicate_succ', List.append_assoc, List.singleton_append]
      cases st
      simp [setList, Function.update_idem]

theorem assemble_run (st : State 41 17) (he : st.lists 7 = []) :
    (assemble.run st).1.lists 15 = st.lists 12 ++ List.replicate (st.lists 12).length 0 ∧
    (assemble.run st).1.lists 16 = st.lists 12 ++ st.lists 16 ∧
    (assemble.run st).1.lists 12 = st.lists 12 := by
  simp [assemble, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    run_len_fst, run_loop_fst, iterate_push, run_rev_fst, run_revApp_fst,
    Function.update, he]

theorem assemble_context (h : ℕ) (st : State 41 17) (hc : Context t h st) :
    Context t h (assemble.run st).1 := by
  have h23 := run_regs_frame assemble 23 (by decide) st
  have h31 := run_regs_frame assemble 31 (by decide) st
  have h3 := run_lists_frame assemble 3 (by decide) st
  have h7 := run_lists_frame assemble 7 (by decide) st
  exact ⟨h23.trans hc.1, h31.trans hc.2.1, h3.trans hc.2.2.1, h7.trans hc.2.2.2⟩

theorem points_run (h : ℕ) (hh : h ≤ 2 ^ t)
    (xs : List (BinaryMaterializedField.Element t)) (st : State 41 17)
    (hc : Context t h st) (hx : st.lists 12 = codes xs) :
    (points.run st).1.lists 15 = codes xs ++ List.replicate xs.length 0 ∧
    (points.run st).1.lists 16 = codes xs ++ values h xs ∧
    Context t h (points.run st).1 ∧ (points.run st).1.lists 12 = st.lists 12 := by
  have hr := program_run h hh xs st hc hx
  have ha := assemble_run (program.run st).1 hr.2.1.2.2.2
  have hctx := assemble_context h (program.run st).1 hr.2.1
  simp only [points, run_seq_fst]
  refine ⟨?_, ?_, hctx, ha.2.2.trans hr.2.2⟩
  · simpa only [hr.2.2, hx, codes, List.length_map] using ha.1
  · simpa only [hr.2.2, hx, hr.1] using ha.2.1

omit [NeZero t] in
theorem sum_codes {F : Type*} {q n : ℕ} (eF : F ≃ Fin q) (x y : Fin n → F) :
    List.ofFn (fun i => (eF (Sum.elim x y (finSumFinEquiv.symm i))).val) =
      List.ofFn (fun i => (eF (x i)).val) ++ List.ofFn (fun i => (eF (y i)).val) := by
  rw [List.ofFn_add]
  simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
  congr 1
  apply congrArg List.ofFn
  funext i
  change (eF (Sum.elim x y (finSumFinEquiv.symm (i.castAdd n)))).val = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem points_zero_recovery {n : ℕ} (h : ℕ) (hh : h ≤ 2 ^ t)
    (x : Fin n → BinaryMaterializedField.Element t) (st : State 41 17)
    (hc : Context t h st)
    (hx : st.lists 12 = List.ofFn (fun i => (fieldEquiv t (x i)).val)) :
    (points.run st).1.lists 15 = List.ofFn (fun i =>
      (fieldEquiv t (BinaryZeroOnGrid.zeroPoint x (finSumFinEquiv.symm i))).val) ∧
    (points.run st).1.lists 16 = List.ofFn (fun i =>
      (fieldEquiv t (FieldQueryArithmetic.recoveryPoint
        (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) x (finSumFinEquiv.symm i))).val) := by
  have hr := points_run h hh (List.ofFn x) st hc
    (by simpa only [codes, List.map_ofFn, Function.comp_def] using hx)
  constructor
  · rw [hr.1, BinaryZeroOnGrid.zeroPoint, sum_codes]
    simp only [codes, List.map_ofFn, Function.comp_def, List.length_ofFn]
    rw [show (fieldEquiv t (0 : BinaryMaterializedField.Element t)).val = 0 by
      exact FieldExpression.code_zero, List.ofFn_const]
  · rw [hr.2.1, FieldQueryArithmetic.recoveryPoint, sum_codes]
    simp only [codes, values, List.map_ofFn, Function.comp_def, GridFactor.value_eq_alphabet _ h hh]

end PCP.Lang.GridRecovery
