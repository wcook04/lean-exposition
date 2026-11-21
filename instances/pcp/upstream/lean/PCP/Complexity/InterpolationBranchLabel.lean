import PCP.Complexity.InterpolationBranchState

/-!
# Plain and weighted homogeneous labels of the interpolation branch
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BooleanCoefficientArithmetic

variable {t n m : ℕ} [NeZero t]

def labelCall : Stmt 100 40 := call (by decide) (by decide) StandardCorrection.label

def labelOutput : Stmt 100 40 := .seq labelCall (.assign 94 (.var 60))

def plainLabel : Stmt 100 40 := .seq (.copy 34 17) labelOutput

def scalePrepare : Stmt 100 40 := .seq (.copy 34 17)
  (.seq (.assign 20 (.var 80)) (.assign 24 (.var 92)))

def scaleCall : Stmt 100 40 := call (by decide) (by decide) BinaryLabelScale.scale

def scaledLabel : Stmt 100 40 := .seq scalePrepare
  (.seq scaleCall (.seq (.copy 16 17) labelOutput))

omit [NeZero t] in
theorem labelCall_run (w : Fin t → ZMod 2) (st : State 100 40)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (labelCall.run st).1.regs 60 =
      (BooleanCoefficientIndex.coefficientEquiv t 1 (homogeneousIndex (le_refl 1) w)).val ∧
    Frame st (labelCall.run st).1 := by
  have hr := call_result (by decide) (by decide) StandardCorrection.label st
  have hp := StandardCorrection.label_run w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) hw
  have h3 := run_lists_frame StandardCorrection.label 3 (by decide)
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  have h7 := run_lists_frame StandardCorrection.label 7 (by decide)
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← hr] at hp h3 h7
  exact ⟨hp, fun i hi _ => call_reg _ _ _ st i hi,
    fun L hL => call_list _ _ _ st L (by omega), h3, h7⟩

omit [NeZero t] in
theorem labelOutput_run (w : Fin t → ZMod 2) (st : State 100 40)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (labelOutput.run st).1.regs 94 =
      (BooleanCoefficientIndex.coefficientEquiv t 1 (homogeneousIndex (le_refl 1) w)).val ∧
    Frame st (labelOutput.run st).1 := by
  have h := labelCall_run w st hw
  exact ⟨h.1, h.2.trans (Frame.assign _ 94 (by decide) _)⟩

theorem plainLabel_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (plainLabel.run st).1.regs 94 =
      (BooleanCoefficientIndex.coefficientEquiv t 1 (homogeneousIndex (le_refl 1) w)).val ∧
    Frame st (plainLabel.run st).1 := by
  have h := labelOutput_run w (setList st 17 (st.lists 34)) (by simpa using hc.label)
  exact ⟨h.1, (Frame.copy st 34 17 (by decide) (by decide) (by decide)).trans h.2⟩

theorem scalePrepare_frame (st : State 100 40) : Frame st (scalePrepare.run st).1 := by
  exact (Frame.copy st 34 17 (by decide) (by decide) (by decide)).trans
    ((Frame.assign _ 20 (by decide) _).trans (Frame.assign _ 24 (by decide) _))

theorem scaleCall_run (α : Field t) (w : Fin t → ZMod 2) (st : State 100 40)
    (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t α).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (scaleCall.run st).1.lists 16 = List.ofFn (fun i =>
      (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) α w i).val) ∧
    Frame st (scaleCall.run st).1 := by
  have hr := call_result (by decide) (by decide) BinaryLabelScale.scale st
  have hp := BinaryLabelScale.scale_run α w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht ha hm he hw
  have hf := BinaryLabelScale.scale_frame
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← hr] at hp hf
  exact ⟨hp, fun i hi _ => call_reg _ _ _ st i hi,
    fun L hL => call_list _ _ _ st L (by omega), hf.2.2.1, hf.2.2.2.1⟩

theorem scaledLabel_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs 92 = (fieldEquiv t α).val) :
    (scaledLabel.run st).1.regs 94 = (BooleanCoefficientIndex.coefficientEquiv t 1
      (homogeneousIndex (le_refl 1)
        (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) α w))).val ∧
    Frame st (scaledLabel.run st).1 := by
  let s := (scalePrepare.run st).1
  have ht : s.regs 20 = t := by
    simpa [s, scalePrepare, Stmt.run, Expr.eval, Function.update] using hc.width
  have ha' : s.regs 24 = (fieldEquiv t α).val := by
    simpa [s, scalePrepare, Stmt.run, Expr.eval, Function.update] using ha
  have hm : s.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) := by
    simpa [s, scalePrepare, Stmt.run, Expr.eval, Function.update] using hc.modulus
  have he : s.lists 7 = [] := by
    simpa [s, scalePrepare, Stmt.run, Expr.eval, Function.update] using hc.empty
  have hw : s.lists 17 = List.ofFn (fun i => (w i).val) := by
    simpa [s, scalePrepare, Stmt.run, Expr.eval, Function.update] using hc.label
  have hscale := scaleCall_run α w s ht ha' hm he hw
  generalize hu : (scaleCall.run s).1 = out at *
  have hlabel := labelOutput_run
    (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) α w)
    (setList out 17 (out.lists 16)) (by simpa using hscale.1)
  simp only [scaledLabel, run_seq_fst, run_copy_fst]
  change (labelOutput.run (setList (scaleCall.run s).1 17
    ((scaleCall.run s).1.lists 16))).1.regs 94 = _ ∧ _
  rw [hu]
  exact ⟨hlabel.1, (scalePrepare_frame st).trans (hscale.2.trans
    ((Frame.copy out 16 17 (by decide) (by decide) (by decide)).trans hlabel.2))⟩

end PCP.Lang.InterpolationBranch
