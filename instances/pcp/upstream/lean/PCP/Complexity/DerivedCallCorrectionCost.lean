/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedCallResources
import PCP.Complexity.NumericCorrectionCost

/-! # Charged cost of both complete numeric certificate calls -/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace
variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] correctionCall NumericCorrection.program

theorem optional_sizes (x : Option (ZMod 2)) :
    Nat.size (present x) ≤ 1 ∧ Nat.size (answer x) ≤ 1 := by
  cases x with
  | none => simp [present, answer]
  | some x =>
      constructor
      · change Nat.size 1 ≤ 1
        decide
      · exact Nat.size_le.mpr (ZMod.val_lt x)

theorem saveCorrection_cost (left : Bool) (V : ℕ) (st : State 300 112)
    (hp : Nat.size (st.regs 146) ≤ 1) (ha : Nat.size (st.regs 147) ≤ 1)
    (hq : listSize (st.lists 49) ≤ V) :
    ((saveCorrection left).run st).2 ≤ 2*V+11 := by
  cases left <;>
    simp only [saveCorrection, presentPort, answerPort, Bool.false_eq_true, ↓reduceIte,
      Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_lists, setReg_regs,
      Function.update_of_ne (by decide : (147 : Fin 300) ≠ 273),
      Function.update_of_ne (by decide : (147 : Fin 300) ≠ 271),
      setList_lists, Function.update_self, listSize_reverse] <;> omega

def correctionCost (k : Certificate) (left : Bool) (t n m W : ℕ)
    (qs : List ℕ) (bs : List Bool) : ℕ :=
  fixedConstant (prepareCorrection left)*(W+1) + NumericCorrection.programCost k t n m W qs bs +
    42*(QueryAddress.width t n m 4+1)+13

set_option maxRecDepth 8192 in
theorem correction_cost (left : Bool) (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (a b : k.Point t n) (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (weight : OuterBranch.Field t) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st)
    (hb : SourceBound W st) :
    ((correction k left).run st).2 ≤ correctionCost k left t n m W qs bs := by
  have hprep := prepareCorrection_cost left W st hb
  have hp := prepareCorrection_run left k nodes ζ a b w mask weight loc first second qs bs st hc
  have hbound := prepareCorrection_bound left W st hb
  have hcall := NumericCorrection.program_cost k nodes ζ (if left then a else b) w
    (if left then first else second) qs bs W
    (view (by decide) (by decide) ((prepareCorrection left).run st).1) hp.1 hp.2 hbound
  have hout := NumericCorrection.program_run k nodes ζ (if left then a else b) w
    (if left then first else second) qs bs
    (view (by decide) (by decide) ((prepareCorrection left).run st).1) hp.1 hp.2
  rw [← call_result (by decide) (by decide) (NumericCorrection.program k)] at hcall hout
  rw [show call (by decide) (by decide) (NumericCorrection.program k) = correctionCall k by
    unfold correctionCall; rfl] at hcall hout
  generalize hu : ((correctionCall k).run ((prepareCorrection left).run st).1).1 = u at *
  have hv : u.regs 146 = present (callValue k nodes ζ (if left then a else b)
      w (if left then first else second) qs bs) := hout.1
  have ha : u.regs 147 = answer (callValue k nodes ζ (if left then a else b)
      w (if left then first else second) qs bs) := hout.2.1
  have hq : u.lists 49 =
      (callQueries k nodes ζ (if left then a else b) w
        (if left then first else second)).reverse := hout.2.2
  have hpresent : Nat.size (u.regs 146) ≤ 1 := by
    rw [hv]
    exact (optional_sizes _).1
  have hanswer : Nat.size (u.regs 147) ≤ 1 := by
    rw [ha]
    exact (optional_sizes _).2
  have hqueries : listSize (u.lists 49) ≤ 21*(QueryAddress.width t n m 4+1) := by
    rw [hq, listSize_reverse]
    exact callQueries_size k nodes ζ (if left then a else b) w (if left then first else second)
  have hsave := saveCorrection_cost left _ u hpresent hanswer hqueries
  simp only [correction, run_seq_snd, hu]
  unfold correctionCost
  omega

end PCP.Lang.DerivedCall
