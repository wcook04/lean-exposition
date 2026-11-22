import PCP.Complexity.InterpolationBranchWeight

/-!
# Cost of loading and evaluating an interpolation weight
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] weightCall weightPrepare weightSave

theorem weightPrepare_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (weightPrepare.run st).2 ≤ 9*t+12 := by
  have hn : listSize (st.lists 35) ≤ 5*(t+1) := by
    rw [hc.nodes]; exact StandardCorrection.fieldCodes_size a
  have ht := size_le_self t
  have hz : Nat.size (fieldEquiv t z).val ≤ t := Nat.size_le.mpr (fieldEquiv t z).isLt
  simp only [weightPrepare, Stmt.run,
    Expr.cost, Expr.readSize, Expr.eval, setList_regs, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.width, hc.param]
  omega

theorem weightCall_cost (a : Fin 5 → Field t) (z : Field t) (i : Fin 5)
    (st : State 100 40) (hc : InterpolationWeightLoad.Context a z
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))) :
    ((weightCall i).run st).2 ≤ InterpolationWeightLoad.constant*(t+1)^4 := by
  have hp := InterpolationWeightLoad.program_cost a z i _ hc
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    (InterpolationWeightLoad.program i) st)] at hp
  simpa only [weightCall, Prod.snd] using hp

theorem weightSave_cost (a : Fin 5 → Field t) (z : Field t) (i : Fin 5)
    (st : State 100 40)
    (hw : st.regs 32 = (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val)
    (hn : st.regs (i.castAdd 95) = (fieldEquiv t (a i)).val) :
    ((weightSave i).run st).2 ≤ 4*t+3 := by
  have hi : i.castAdd 95 ≠ (92 : Fin 100) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hw' : Nat.size (st.regs 32) ≤ t := by
    rw [hw]; exact Nat.size_le.mpr (fieldEquiv t _).isLt
  have hn' : Nat.size (st.regs (i.castAdd 95)) ≤ t := by
    rw [hn]; exact Nat.size_le.mpr (fieldEquiv t _).isLt
  simp only [weightSave, Stmt.run, Expr.cost, Expr.readSize,
    Expr.eval, setReg_regs, Function.update_of_ne hi]
  omega

/-- Fixed-degree weight computation includes copying nodes and saving both field codes. -/
theorem weightStep_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (i : Fin 5) (st : State 100 40) (hc : Context a z u v w site st) :
    ((weightStep i).run st).2 ≤ (InterpolationWeightLoad.constant+30)*(t+1)^4 := by
  have hp := weightPrepare_cost a z u v w site st hc
  have hc' := weightPrepare_context a z u v w site st hc
  have hw := weightCall_cost a z i (weightPrepare.run st).1 hc'
  have hs := weightCall_run a z i (weightPrepare.run st).1 hc'
  have hsave := weightSave_cost a z i _ hs.1 hs.2.1
  have hl : t+1 ≤ (t+1)^4 := Nat.le_self_pow (by decide) _
  rw [weightStep, run_seq_snd, run_seq_snd]
  nlinarith only [hp, hw, hsave, hl]

end PCP.Lang.InterpolationBranch
