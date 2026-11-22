import PCP.Complexity.InterpolationBranchPoint

/-!
# Cost of materializing an interpolation query point
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] pointCall pointPrepare

omit [NeZero t] in
theorem innerIndex_size (x : Point t m) :
    Nat.size (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).val ≤ t*(4*m) := by
  apply Nat.size_le.mpr
  simpa only [← pow_mul] using (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).isLt

theorem pointPrepare_cost (src : Fin 100) (hs : 80 ≤ src.val)
    (a : Fin 5 → Field t) (z : Field t) (u v : Point t m) (w : Fin t → ZMod 2)
    (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs src = (fieldEquiv t α).val) :
    ((pointPrepare src).run st).2 ≤ 10*(t+4*m+2)^2 := by
  have hu : listSize (st.lists 32) ≤ (4*m)*(t+1) := by
    rw [hc.left]; exact StandardCorrection.fieldCodes_size _
  have hv : listSize (st.lists 33) ≤ (4*m)*(t+1) := by
    rw [hc.right]; exact StandardCorrection.fieldCodes_size _
  have ht := size_le_self t
  have hα : Nat.size (fieldEquiv t α).val ≤ t := Nat.size_le.mpr (fieldEquiv t α).isLt
  have h43 : src ≠ 43 := by intro h; subst src; norm_num at hs
  have h45 : src ≠ 45 := by intro h; subst src; norm_num at hs
  simp only [pointPrepare, Stmt.run,
    Expr.cost, Expr.readSize, Expr.eval, setList_regs, setList_lists, setReg_regs,
    Function.update, h43, h45,
    Fin.reduceEq, dite_false, hc.width, hc.card, ha, Nat.size_pow]
  nlinarith only [hu, hv, ht, hα, Nat.zero_le (t^2), Nat.zero_le (m^2)]

theorem pointCall_cost (u v : Point t m) (α : Field t) (st : State 100 40)
    (hc : StandardCorrection.AffineContext (StandardCorrection.vector u)
      (StandardCorrection.vector v)
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (ha : st.regs 26 = (fieldEquiv t α).val) :
    (pointCall.run st).2 ≤ (RadixCodec.passConstant+101000025)*(t+4*m+2)^5 := by
  have hp := StandardCorrection.scalarPoint_cost α _ _ _ hc ha
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    StandardCorrection.scalarPoint st)] at hp
  simpa only [pointCall, Prod.snd] using hp

/-- The affine vector, little-endian point code, and output copy all have polynomial cost. -/
theorem pointStep_cost (src : Fin 100) (hs : 80 ≤ src.val)
    (a : Fin 5 → Field t) (z : Field t) (u v : Point t m) (w : Fin t → ZMod 2)
    (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs src = (fieldEquiv t α).val) :
    ((pointStep src).run st).2 ≤ (RadixCodec.passConstant+101000100)*(t+4*m+2)^5 := by
  have hp := pointPrepare_cost src hs a z u v w site α st hc ha
  have hctx := pointPrepare_context src hs a z u v w site α st hc ha
  have hc' := pointCall_cost u v α _ hctx.1 hctx.2
  have hout := (pointCall_run u v α _ hctx.1 hctx.2).1
  have hsize : Nat.size ((pointCall.run ((pointPrepare src).run st).1).1.regs 59) ≤ t*(4*m) := by
    rw [hout]; exact innerIndex_size _
  have h25 : (t+4*m+2)^2 ≤ (t+4*m+2)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  rw [pointStep, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  nlinarith only [hp, hc', hsize, h25, Nat.zero_le (t^2), Nat.zero_le (m^2)]

end PCP.Lang.InterpolationBranch
