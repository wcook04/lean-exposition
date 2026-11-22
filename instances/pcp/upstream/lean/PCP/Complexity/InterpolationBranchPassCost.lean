import PCP.Complexity.InterpolationBranchPass
import PCP.Complexity.InterpolationBranchWeightCost
import PCP.Complexity.InterpolationBranchPointCost
import PCP.Complexity.InterpolationBranchLabelCost
import PCP.Complexity.InterpolationBranchEmitCost

/-!
# Cost of all interpolation query passes
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BooleanCoefficientArithmetic BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] pointStep plainLabel scaledLabel emitStep weightStep nodeEmit

def ReadBound (site : StandardCorrection.Site (Field t) n)
    (x : Point t m) (label : Coefficients t 1) (W : ℕ) : Prop :=
  (∀ i : Fin 11, Nat.size (QueryAddress.inputs (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
      (site.query x label) i) ≤ W) ∧ Nat.size (address site x label) ≤ W

/-- Widths of actual payloads and addresses, including nodes whose zero weight omits the read. -/
def QueryBound (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (W : ℕ) : Prop :=
  ReadBound site (PolynomialLine.point u v z) (homogeneousIndex (le_refl 1) w) W ∧
  ∀ i : Fin 5, ReadBound site (PolynomialLine.point u v (a i))
    (homogeneousIndex (le_refl 1) (FieldQueryArithmetic.scaleLabel
      (BinaryMaterializedField.coordinates t) (FieldQueryArithmetic.interpolationWeight a z i) w)) W

def pointCostConstant : ℕ := RadixCodec.passConstant+101000100
def labelCostConstant : ℕ := BinaryLabelScale.kernelConstant+WordCodec.passConstant*3+700100
def emitCostConstant : ℕ := QueryAddress.program.C *
  (QueryAddress.program.width+QueryAddress.program.csize+1)+30

def queryBudget (t m W : ℕ) : ℕ := pointCostConstant*(t+4*m+2)^5+
  labelCostConstant*(2^t+4)^7+emitCostConstant*(W+1)+2

def nodeBudget (t m W : ℕ) : ℕ :=
  (InterpolationWeightLoad.constant+30)*(t+1)^4+queryBudget t m W+t+3

theorem plainLabel_cost_wide (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    (plainLabel.run st).2 ≤ labelCostConstant*(2^t+4)^7 := by
  have hp := plainLabel_cost a z u v w site st hc
  have ht : t+2 ≤ 2^t+4 := by have : t < 2^t := Nat.lt_two_pow_self; omega
  have hpow : (t+2)^2 ≤ (2^t+4)^7 :=
    (Nat.pow_le_pow_left ht 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  exact hp.trans (Nat.mul_le_mul (by unfold labelCostConstant; omega) hpow)

theorem firstQuery_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (W : ℕ)
    (st : State 100 40) (hc : Context a z u v w site st)
    (hb : QueryBound a z u v w site W) :
    (firstQuery.run st).2 ≤ queryBudget t m W := by
  have hp := pointStep_run 82 (by decide) a z u v w site z st hc hc.param
  have hpc := pointStep_cost 82 (by decide) a z u v w site z st hc hc.param
  generalize hs : ((pointStep 82).run st).1 = s at *
  have hsc := hc.of_frame hp.2
  have hl := plainLabel_run a z u v w site s hsc
  have hlc := plainLabel_cost_wide a z u v w site s hsc
  have hlp := plainLabel_reg 95 (by decide) (by decide) s
  generalize hout : (plainLabel.run s).1 = out at *
  have he := emitStep_cost a z u v w site (PolynomialLine.point u v z)
    (homogeneousIndex (le_refl 1) w) out (hsc.of_frame hl.2) (hlp.trans hp.1) hl.1 W hb.1.1 hb.1.2
  rw [firstQuery, run_seq_snd, run_seq_snd, hs, hout]
  change _ ≤ pointCostConstant*(t+4*m+2)^5+
    labelCostConstant*(2^t+4)^7+emitCostConstant*(W+1)+2
  change (pointStep 82 |>.run st).2 ≤ pointCostConstant*(t+4*m+2)^5 at hpc
  change (emitStep.run out).2 ≤ emitCostConstant*(W+1) at he
  omega

theorem nodeEmit_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5) (W : ℕ)
    (st : State 100 40) (hc : Context a z u v w site st)
    (hw : st.regs 92 = (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val)
    (hn : st.regs 93 = (fieldEquiv t (a i)).val) (hb : QueryBound a z u v w site W) :
    (nodeEmit.run st).2 ≤ queryBudget t m W := by
  have hp := pointStep_run 93 (by decide) a z u v w site (a i) st hc hn
  have hpc := pointStep_cost 93 (by decide) a z u v w site (a i) st hc hn
  have hpw := pointStep_reg 93 92 (by decide) (by decide) st
  generalize hs : ((pointStep 93).run st).1 = s at *
  have hsc := hc.of_frame hp.2
  have hl := scaledLabel_run a z u v w site
    (FieldQueryArithmetic.interpolationWeight a z i) s hsc (hpw.trans hw)
  have hlc := scaledLabel_cost a z u v w site
    (FieldQueryArithmetic.interpolationWeight a z i) s hsc (hpw.trans hw)
  have hlp := scaledLabel_reg 95 (by decide) (by decide) s
  generalize hout : (scaledLabel.run s).1 = out at *
  have he := emitStep_cost a z u v w site (PolynomialLine.point u v (a i))
    (homogeneousIndex (le_refl 1) (FieldQueryArithmetic.scaleLabel
      (BinaryMaterializedField.coordinates t) (FieldQueryArithmetic.interpolationWeight a z i) w))
    out (hsc.of_frame hl.2) (hlp.trans hp.1) hl.1 W (hb.2 i).1 (hb.2 i).2
  rw [nodeEmit, run_seq_snd, run_seq_snd, hs, hout]
  change _ ≤ pointCostConstant*(t+4*m+2)^5+
    labelCostConstant*(2^t+4)^7+emitCostConstant*(W+1)+2
  change (pointStep 93 |>.run st).2 ≤ pointCostConstant*(t+4*m+2)^5 at hpc
  change (scaledLabel.run s).2 ≤ labelCostConstant*(2^t+4)^7 at hlc
  change (emitStep.run out).2 ≤ emitCostConstant*(W+1) at he
  omega

theorem nodeStep_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n) (i : Fin 5) (W : ℕ)
    (st : State 100 40) (hc : Context a z u v w site st)
    (hb : QueryBound a z u v w site W) :
    ((nodeStep i).run st).2 ≤ nodeBudget t m W := by
  have hw := weightStep_run a z u v w site i st hc
  have hwc := weightStep_cost a z u v w site i st hc
  generalize hs : ((weightStep i).run st).1 = s at *
  have hsc := hc.of_frame hw.2.2
  have hn := nodeEmit_cost a z u v w site i W s hsc hw.1 hw.2.1 hb
  have hsize : Nat.size (s.regs 92) ≤ t := by
    rw [hw.1]; exact Nat.size_le.mpr (fieldEquiv t _).isLt
  rw [nodeStep, run_seq_snd, hs]
  change _ ≤ (InterpolationWeightLoad.constant+30)*(t+1)^4+queryBudget t m W+t+3
  simp only [Stmt.run]
  split_ifs <;> omega

end PCP.Lang.InterpolationBranch
