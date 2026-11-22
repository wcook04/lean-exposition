import PCP.Complexity.InterpolationBranchPoint
import PCP.Complexity.InterpolationBranchLabel

/-!
# Scratch values retained between interpolation-branch arithmetic stages
-/

namespace PCP.Lang.InterpolationBranch

theorem pointPrepare_reg (src i : Fin 100) (hi : 80 ≤ i.val) (st : State 100 40) :
    ((pointPrepare src).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [pointPrepare, Stmt.regWrites, List.nil_append, List.mem_append,
    List.mem_singleton]
  rintro (rfl | rfl | rfl) <;> norm_num at hi

theorem pointStep_reg (src i : Fin 100) (hi : 80 ≤ i.val) (h95 : i ≠ 95)
    (st : State 100 40) : ((pointStep src).run st).1.regs i = st.regs i := by
  simp only [pointStep, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_of_ne h95]
  rw [show (pointCall.run ((pointPrepare src).run st).1).1.regs i =
      ((pointPrepare src).run st).1.regs i from call_reg _ _ _ _ i hi]
  exact pointPrepare_reg src i hi st

theorem labelOutput_reg (i : Fin 100) (hi : 80 ≤ i.val) (h94 : i ≠ 94)
    (st : State 100 40) : (labelOutput.run st).1.regs i = st.regs i := by
  simp only [labelOutput, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_of_ne h94]
  exact call_reg _ _ _ st i hi

theorem plainLabel_reg (i : Fin 100) (hi : 80 ≤ i.val) (h94 : i ≠ 94)
    (st : State 100 40) : (plainLabel.run st).1.regs i = st.regs i :=
  labelOutput_reg i hi h94 _

theorem scalePrepare_reg (i : Fin 100) (hi : 80 ≤ i.val) (st : State 100 40) :
    (scalePrepare.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [scalePrepare, Stmt.regWrites, List.nil_append, List.mem_append,
    List.mem_singleton]
  rintro (rfl | rfl) <;> norm_num at hi

theorem scaledLabel_reg (i : Fin 100) (hi : 80 ≤ i.val) (h94 : i ≠ 94)
    (st : State 100 40) : (scaledLabel.run st).1.regs i = st.regs i := by
  simp only [scaledLabel, run_seq_fst, run_copy_fst, labelOutput_reg i hi h94, setList_regs]
  rw [show (scaleCall.run (scalePrepare.run st).1).1.regs i =
      (scalePrepare.run st).1.regs i from call_reg _ _ _ _ i hi]
  exact scalePrepare_reg i hi st

theorem labelOutput_queries (st : State 100 40) :
    (labelOutput.run st).1.lists 20 = st.lists 20 := by
  have hr := call_result (by decide) (by decide) StandardCorrection.label st
  have h := run_lists_frame StandardCorrection.label 20 (by decide)
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← hr] at h
  exact h

theorem plainLabel_queries (st : State 100 40) :
    (plainLabel.run st).1.lists 20 = st.lists 20 := by
  rw [plainLabel, run_seq_fst, labelOutput_queries]
  rfl

theorem scaledLabel_queries (st : State 100 40) :
    (scaledLabel.run st).1.lists 20 = st.lists 20 := by
  simp only [scaledLabel, run_seq_fst, run_copy_fst, labelOutput_queries,
    setList_lists, Function.update_of_ne (by decide : (20 : Fin 40) ≠ 17)]
  rw [show (scaleCall.run (scalePrepare.run st).1).1.lists 20 =
      (scalePrepare.run st).1.lists 20 from call_list _ _ _ _ 20 (by decide)]
  exact run_lists_frame scalePrepare 20 (by decide) st

end PCP.Lang.InterpolationBranch
