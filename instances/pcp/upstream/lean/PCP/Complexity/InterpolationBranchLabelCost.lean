import PCP.Complexity.InterpolationBranchLabel

/-!
# Costs of plain and weighted homogeneous query labels
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BooleanCoefficientArithmetic

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] labelCall labelOutput scaleCall scalePrepare

omit [NeZero t] in
theorem coordinateBits_size (w : Fin t → ZMod 2) :
    listSize (List.ofFn (fun i => (w i).val)) ≤ 2*t := by
  simp only [listSize, List.map_ofFn, Fin.sum_ofFn, Function.comp_apply]
  calc
    _ ≤ ∑ _i : Fin t, 2 := Finset.sum_le_sum fun i _ => by
      have h : Nat.size (w i).val ≤ 1 := Nat.size_le.mpr (ZMod.val_lt _)
      omega
    _ = _ := by simp [Nat.mul_comm]

omit [NeZero t] in
theorem labelIndex_size (w : BinaryPolynomialSpace.Coefficients t 1) :
    Nat.size (BooleanCoefficientIndex.coefficientEquiv t 1 w).val ≤ t+1 := by
  apply Nat.size_le.mpr
  simpa [BooleanCoefficientIndex.dimension_one, Nat.add_comm] using
    (BooleanCoefficientIndex.coefficientEquiv t 1 w).isLt

omit [NeZero t] in
theorem labelCall_cost (w : Fin t → ZMod 2) (st : State 100 40)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (labelCall.run st).2 ≤ (WordCodec.passConstant*3+30)*(t+2)^2 := by
  have hp := StandardCorrection.label_cost w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) hw
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) StandardCorrection.label st)] at hp
  simpa only [labelCall, Prod.snd] using hp

omit [NeZero t] in
theorem labelOutput_cost (w : Fin t → ZMod 2) (st : State 100 40)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (labelOutput.run st).2 ≤ (WordCodec.passConstant*3+35)*(t+2)^2 := by
  have hp := labelCall_cost w st hw
  have hout := (labelCall_run w st hw).1
  have hs : Nat.size ((labelCall.run st).1.regs 60) ≤ t+1 := by
    rw [hout]; exact labelIndex_size _
  rw [labelOutput, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  nlinarith only [hp, hs]

theorem plainLabel_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (plainLabel.run st).2 ≤ (WordCodec.passConstant*3+40)*(t+2)^2 := by
  have hp := labelOutput_cost w (setList st 17 (st.lists 34)) (by simpa using hc.label)
  have hs : listSize (st.lists 34) ≤ 2*t := by rw [hc.label]; exact coordinateBits_size w
  rw [plainLabel, run_seq_snd, run_copy_snd, run_copy_fst]
  nlinarith only [hp, hs]

theorem scalePrepare_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs 92 = (fieldEquiv t α).val) :
    (scalePrepare.run st).2 ≤ 6*t+5 := by
  have hs : listSize (st.lists 34) ≤ 2*t := by rw [hc.label]; exact coordinateBits_size w
  have ht := size_le_self t
  have hα : Nat.size (fieldEquiv t α).val ≤ t := Nat.size_le.mpr (fieldEquiv t α).isLt
  simp only [scalePrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setList_regs,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, hc.width, ha]
  omega

theorem scaleCall_cost (α : Field t) (w : Fin t → ZMod 2) (st : State 100 40)
    (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t α).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (scaleCall.run st).2 ≤ (BinaryLabelScale.kernelConstant+700000)*(2^t+4)^7 := by
  have hp := BinaryLabelScale.scale_cost α w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht ha hm he hw
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) BinaryLabelScale.scale st)] at hp
  simpa only [scaleCall, Prod.snd] using hp

/-- Cost includes the genuine transpose-of-multiplication computation of the weighted label. -/
theorem scaledLabel_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs 92 = (fieldEquiv t α).val) :
    (scaledLabel.run st).2 ≤
      (BinaryLabelScale.kernelConstant+WordCodec.passConstant*3+700100)*(2^t+4)^7 := by
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
  have hp := scalePrepare_cost a z u v w site α st hc ha
  have hscale := scaleCall_cost α w s ht ha' hm he hw
  have hout := (scaleCall_run α w s ht ha' hm he hw).1
  have hlabel := labelOutput_cost
    (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) α w)
    (setList (scaleCall.run s).1 17 ((scaleCall.run s).1.lists 16)) (by simpa using hout)
  have hcopy : listSize ((scaleCall.run s).1.lists 16) ≤ 2*t := by
    rw [hout]; exact coordinateBits_size _
  have htq : t+2 ≤ 2^t+4 := by have : t < 2^t := Nat.lt_two_pow_self; omega
  have h27 : (t+2)^2 ≤ (2^t+4)^7 :=
    (Nat.pow_le_pow_left htq 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hlin : t+2 ≤ (2^t+4)^7 :=
    htq.trans (Nat.le_self_pow (by decide) _)
  have hlabel' := hlabel.trans (Nat.mul_le_mul_left _ h27)
  rw [scaledLabel, run_seq_snd, run_seq_snd, run_seq_snd, run_copy_snd, run_copy_fst]
  change (scalePrepare.run st).2+((scaleCall.run s).2+
    (listSize ((scaleCall.run s).1.lists 16)+1+
      (labelOutput.run
        (setList (scaleCall.run s).1 17 ((scaleCall.run s).1.lists 16))).2+1)+1)+1 ≤ _
  nlinarith only [hp, hscale, hcopy, hlabel', hlin]

end PCP.Lang.InterpolationBranch
