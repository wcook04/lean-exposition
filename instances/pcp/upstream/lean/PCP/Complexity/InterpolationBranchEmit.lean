import PCP.Complexity.InterpolationBranchState

/-!
# Emitting an actual physical query from the interpolation branch
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def emitPrepare : Stmt 100 40 := .seq (.copy 7 21)
  (.seq (.assign 50 (.var 83)) (.seq (.assign 51 (.var 84))
  (.seq (.assign 52 (.var 85)) (.seq (.assign 53 (.var 86))
  (.seq (.assign 54 (.var 87)) (.seq (.assign 55 (.var 88))
  (.seq (.assign 56 (.var 89)) (.seq (.assign 57 (.var 90))
  (.seq (.assign 58 (.var 91)) (.seq (.assign 59 (.var 95)) (.assign 60 (.var 94))))))))))))

def emitCall : Stmt 100 40 := call (by decide) (by decide) StandardCorrection.emit

def emitStep : Stmt 100 40 := .seq emitPrepare emitCall

def address (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (label : Coefficients t 1) : ℕ :=
  (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) (site.query x label)).val

theorem emitPrepare_frame (st : State 100 40) : Frame st (emitPrepare.run st).1 := by
  apply frame_of_writes
  · intro i hi
    simp only [emitPrepare, Stmt.regWrites, List.nil_append, List.mem_append,
      List.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro L hL
    simp only [emitPrepare, Stmt.listWrites, List.append_nil, List.mem_singleton] at hL
    subst L
    decide

theorem emitPrepare_context (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (x : Point t m) (label : Coefficients t 1) (st : State 100 40)
    (hc : Context a z u v w site st)
    (hx : st.regs 95 = (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).val)
    (hw : st.regs 94 = (BooleanCoefficientIndex.coefficientEquiv t 1 label).val) :
    StandardCorrection.AddressContext (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) site x label
      ((emitPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := hc.address i
    fin_cases i <;> simpa [emitPrepare, Stmt.run, Expr.eval, Function.update, State.restrict,
      StandardCorrection.addressRegs, prefixPort] using h
  · simpa [emitPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hx
  · simpa [emitPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hw

omit [NeZero t] in
theorem emitCall_run (site : StandardCorrection.Site (Field t) n)
    (x : Point t m) (label : Coefficients t 1) (st : State 100 40)
    (hc : StandardCorrection.AddressContext (fieldEquiv t)
      (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
      site x label (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))) :
    (emitCall.run st).1.lists 20 = address site x label :: st.lists 20 ∧
    Frame st (emitCall.run st).1 := by
  have hr := call_result (by decide) (by decide) StandardCorrection.emit st
  have hp := (StandardCorrection.emit_run (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
    site x label _ hc).1
  have hm := QueryAddress.emit.run_rename_list_outside
    StandardCorrection.addressRegs StandardCorrection.addressLists 3
    (by intro j; fin_cases j <;> decide)
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  have he := QueryAddress.emit.run_rename_list_outside
    StandardCorrection.addressRegs StandardCorrection.addressLists 7
    (by intro j; fin_cases j <;> decide)
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  change (StandardCorrection.emit.run (st.restrict (Fin.castLE (by decide))
    (Fin.castLE (by decide)))).1.lists 3 = _ at hm
  change (StandardCorrection.emit.run (st.restrict (Fin.castLE (by decide))
    (Fin.castLE (by decide)))).1.lists 7 = _ at he
  rw [← hr] at hp hm he
  exact ⟨hp, fun i hi _ => call_reg _ _ _ st i hi,
    fun L hL => call_list _ _ _ st L (by omega), hm, he⟩

theorem emitStep_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (x : Point t m) (label : Coefficients t 1) (st : State 100 40)
    (hc : Context a z u v w site st)
    (hx : st.regs 95 = (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).val)
    (hw : st.regs 94 = (BooleanCoefficientIndex.coefficientEquiv t 1 label).val) :
    (emitStep.run st).1.lists 20 = address site x label :: st.lists 20 ∧
    Frame st (emitStep.run st).1 := by
  have hv := emitPrepare_context a z u v w site x label st hc hx hw
  have hq := run_lists_frame emitPrepare 20 (by decide) st
  have hf := emitPrepare_frame st
  have hp := emitCall_run site x label (emitPrepare.run st).1 hv
  exact ⟨hp.1.trans (congrArg (address site x label :: ·) hq), hf.trans hp.2⟩

end PCP.Lang.InterpolationBranch
