import PCP.Complexity.QueryHistoryLang
import PCP.Complexity.LangRenaming
import PCP.Algebraic.ComputableHadamardTest
import PCP.Algebraic.BinarySeedPadding

/-!
# The difference branch's actual answer-history verdict

Three independent calls to the certified history reader retain first-occurrence
precedence even on repeated addresses and inconsistent hypothetical answers.
The final bit is exactly the characteristic-two difference residual test.
-/

namespace PCP.Lang.DifferenceVerdict

open PCP.Algebraic

def history : Stmt 14 4 := QueryHistory.program.rename (Fin.castAdd 6) id

def readAt (src : Fin 14) : Stmt 14 4 := .seq (.assign 0 (.var src)) history

def accumulate (src : Fin 14) : Stmt 14 4 := .seq (readAt src) (.assign 11 (.add 11 2))

def finish : Stmt 14 4 := .seq (.assign 12 (.const 2)) (.seq (.assign 11 (.mod 11 12))
  (.seq (.assign 13 (.const 0)) (.assign 13 (.eq 11 13))))

def program : Stmt 14 4 := .seq (.assign 11 (.const 0))
  (.seq (accumulate 8) (.seq (accumulate 9) (.seq (accumulate 10) finish)))

def Context (qs bs : List ℕ) (x y z : ℕ) (st : State 14 4) : Prop :=
  st.lists 0 = qs ∧ st.lists 1 = bs ∧ st.regs 8 = x ∧ st.regs 9 = y ∧ st.regs 10 = z

theorem history_result (st : State 14 4) :
    ((history.run st).1.restrict (Fin.castAdd 6) id, (history.run st).2) =
      QueryHistory.program.run (st.restrict (Fin.castAdd 6) id) := by
  unfold history
  exact Stmt.run_rename _ _ _ (Fin.castAdd_injective 8 6) Function.injective_id st

theorem readAt_run (src : Fin 14) (st : State 14 4) :
    ((readAt src).run st).1.regs 2 = QueryHistory.read (st.lists 0) (st.lists 1) (st.regs src) ∧
    ((readAt src).run st).1.lists 0 = st.lists 0 ∧
    ((readAt src).run st).1.lists 1 = st.lists 1 := by
  let s := setReg st 0 (st.regs src)
  have h := QueryHistory.program_run (s.restrict (Fin.castAdd 6) id)
  rw [← history_result s] at h
  simp only [State.restrict_regs, State.restrict_lists,
    show (0 : Fin 8).castAdd 6 = (0 : Fin 14) from rfl,
    show (2 : Fin 8).castAdd 6 = (2 : Fin 14) from rfl, id_eq] at h
  simpa [readAt, run_seq_fst, run_assign_fst, Expr.eval, s] using ⟨h.1, h.2.1, h.2.2.1⟩

theorem readAt_reg (src i : Fin 14) (hi : 8 ≤ i.val) (st : State 14 4) :
    ((readAt src).run st).1.regs i = st.regs i := by
  have h := QueryHistory.program.run_rename_reg_outside (Fin.castAdd 6) id i
    (by intro j hj; have := congrArg Fin.val hj; simp only [Fin.val_castAdd] at this; omega)
    (setReg st 0 (st.regs src))
  simp only [readAt, run_seq_fst, run_assign_fst, Expr.eval]
  have hi0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  simpa only [history, setReg_regs, Function.update_of_ne hi0] using h

theorem readAt_context (src : Fin 14) (qs bs : List ℕ) (x y z : ℕ)
    (st : State 14 4) (hc : Context qs bs x y z st) :
    Context qs bs x y z ((readAt src).run st).1 := by
  have h := readAt_run src st
  exact ⟨h.2.1.trans hc.1, h.2.2.trans hc.2.1,
    (readAt_reg src 8 (by decide) st).trans hc.2.2.1,
    (readAt_reg src 9 (by decide) st).trans hc.2.2.2.1,
    (readAt_reg src 10 (by decide) st).trans hc.2.2.2.2⟩

theorem accumulate_run (src : Fin 14) (st : State 14 4) :
    ((accumulate src).run st).1.regs 11 = st.regs 11 +
      QueryHistory.read (st.lists 0) (st.lists 1) (st.regs src) := by
  simp only [accumulate, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self, (readAt_run src st).1, readAt_reg src 11 (by decide) st]

theorem accumulate_context (src : Fin 14) (qs bs : List ℕ) (x y z : ℕ)
    (st : State 14 4) (hc : Context qs bs x y z st) :
    Context qs bs x y z ((accumulate src).run st).1 := by
  have h := readAt_context src qs bs x y z st hc
  simpa [Context, accumulate, run_seq_fst, run_assign_fst, Function.update] using h

theorem finish_run (st : State 14 4) :
    (finish.run st).1.regs 13 = (decide (st.regs 11 % 2 = 0)).toNat := by
  simp [finish, Stmt.run, Expr.eval, Function.update]
  split_ifs with h <;> simp [h]

/-- The actual program computes the parity of the three history reads. -/
theorem program_run (qs bs : List ℕ) (x y z : ℕ) (st : State 14 4)
    (hc : Context qs bs x y z st) :
    (program.run st).1.regs 13 = (decide
      ((QueryHistory.read qs bs x + QueryHistory.read qs bs y +
        QueryHistory.read qs bs z) % 2 = 0)).toNat := by
  let s := setReg st 11 0
  have hsc : Context qs bs x y z s := by simpa [Context, s, Function.update] using hc
  have hu11 := accumulate_run 8 s
  have huc := accumulate_context 8 qs bs x y z s hsc
  have hs11 : s.regs 11 = 0 := rfl
  rw [hs11, hsc.1, hsc.2.1, hsc.2.2.1, Nat.zero_add] at hu11
  generalize hu : ((accumulate 8).run s).1 = u at *
  have hv11 := accumulate_run 9 u
  have hvc := accumulate_context 9 qs bs x y z u huc
  rw [hu11, huc.1, huc.2.1, huc.2.2.2.1] at hv11
  generalize hv : ((accumulate 9).run u).1 = v at *
  have hw11 := accumulate_run 10 v
  rw [hv11, hvc.1, hvc.2.1, hvc.2.2.2.2] at hw11
  simp only [program, run_seq_fst, run_assign_fst, Expr.eval]
  dsimp only [s] at hu
  rw [hu, hv, finish_run, hw11]

/-- The physical history bit interpretation used by the production verifier. -/
def check (qs : List ℕ) (bs : List Bool) (x y z : ℕ) : Bool :=
  decide (BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs x) -
    (BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs y) -
      BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs z)) = 0)

/-- This includes missing answers, duplicate addresses, and every inconsistent bit history. -/
theorem program_check (qs : List ℕ) (bs : List Bool) (x y z : ℕ) (st : State 14 4)
    (hc : Context qs (bs.map Bool.toNat) x y z st) :
    (program.run st).1.regs 13 = (check qs bs x y z).toNat := by
  rw [program_run qs (bs.map Bool.toNat) x y z st hc]
  simp only [QueryHistory.read_bool, check]
  cases QueryTree.answersOracle qs bs x <;> cases QueryTree.answersOracle qs bs y <;>
    cases QueryTree.answersOracle qs bs z <;> decide

/-- Direct identification with the named difference branch, at any physical address embedding. -/
theorem program_difference_check {F σ : Type*} {t r : ℕ} (hr : 1 ≤ r)
    (index : BinaryDifferenceConsistency.Query F σ t r → ℕ)
    (a b : σ → F) (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (st : State 14 4)
    (hc : Context qs (bs.map Bool.toNat)
      (index (.inr (Sum.elim a b, BooleanCoefficientArithmetic.homogeneousIndex hr w)))
      (index (.inl (a, BooleanCoefficientArithmetic.homogeneousIndex hr w)))
      (index (.inl (b, BooleanCoefficientArithmetic.homogeneousIndex hr w))) st) :
    (program.run st).1.regs 13 = (decide (ComputableBinaryDifferenceConsistency.check hr
      (fun x label => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs
        (index (.inl (x, label)))))
      (fun x label => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs
        (index (.inr (x, label))))) a b w = 0)).toNat :=
  program_check qs bs _ _ _ st hc

end PCP.Lang.DifferenceVerdict
