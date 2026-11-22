import PCP.Complexity.StandardCorrectionQueries
import PCP.Complexity.StandardCorrectionWeightCost

/-!
# Charged cost of the standard-correction query generator
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace BooleanCoefficientArithmetic
  BooleanCoefficientIndex

variable {t n m : ℕ} [NeZero t]

/-- Numeric payload and physical address widths, stated on the actual five semantic queries. -/
def QueryBound (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ) : Prop :=
  ∀ j < 5,
    (∀ i : Fin 11, Nat.size (QueryAddress.inputs (fieldEquiv t) (labelEquiv t 1)
      (labelEquiv t 3) (s.query (PolynomialLine.point u v (ζ^(j+1)))
        (queryLabel ζ w j)) i) ≤ W) ∧
    Nat.size (queryCode s ζ u v w j) ≤ W

def pointConstant : ℕ := RadixCodec.passConstant + 141000025

def addressConstant : ℕ := QueryAddress.program.C *
  (QueryAddress.program.width + QueryAddress.program.csize + 1) + 2

def passBudget (t d W : ℕ) : ℕ := weightConstant*(2^t+4)^7 +
  pointConstant * (t+d+4)^5 + addressConstant*(W+1)+12

attribute [local irreducible] point emit weightedLabel

theorem pass_cost (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j W : ℕ) (hj : j < 5)
    (st : State 80 26) (hc : Context s ζ u v w st)
    (hb : QueryBound s ζ u v w W) (hs : listSize (st.lists 21) ≤ W) :
    ((pass j).run st).2 ≤ passBudget t (4*m) W := by
  let a := setReg st 46 (j+1)
  let i : Fin 5 := ⟨j % 5, Nat.mod_lt _ (by decide)⟩
  have hac := assign_context s ζ u v w j st hc
  have hwc := weighted_context s ζ u v w i a hac
  have hwcost := weightedLabel_cost ζ (vector u) (vector v) i w a hac.1 hac.2.2
  have hwl := weightedLabel_run ζ (vector u) (vector v) i w a hac.1 hac.2.2
  have hwe : ((weightedLabel i).run a).1.regs 46 = j+1 :=
    (weightedLabel_reg i a 46 (by decide) (by decide) (by decide)).trans (by simp [a])
  have hw21 := weightedLabel_list i a 21 (by decide) (by decide)
  generalize hsb : ((weightedLabel i).run a).1 = b at *
  have hp := point_cost ζ (vector u) (vector v) (j+1) (by omega) b hwc.1 hwe
  have hv := point_address s ζ u v w j hj b hwc hwe hwl
  have hview := address_view (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) s
    (PolynomialLine.point u v (ζ^(j+1))) (queryLabel ζ w j) _ hv
  have he := emit_cost (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) s
    (PolynomialLine.point u v (ζ^(j+1))) (queryLabel ζ w j) _ hv W
    (fun k => by rw [← State.restrict_regs, hview k]; exact (hb j hj).1 k)
    (by rw [point_lists_outside b 21 (by decide), hw21]; exact hs) (hb j hj).2
  have hjb : Nat.size (j+1) ≤ 3 := Nat.size_le.mpr (by norm_num; omega)
  simp only [pass, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.const (j+1)).cost st.regs + (((weightedLabel i).run a).2+
    ((point.run ((weightedLabel i).run a).1).2 +
      (emit.run (point.run ((weightedLabel i).run a).1).1).2+1)+1)+1 ≤ _
  rw [hsb]
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  change _ ≤ weightConstant*(2^t+4)^7 +
    pointConstant * (t+4*m+4)^5 + addressConstant*(W+1)+12
  change (point.run b).2 ≤ pointConstant * (t+4*m+4)^5 at hp
  change (emit.run (point.run b).1).2 ≤ addressConstant*(W+1) at he
  omega

theorem passes_cost (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j k W : ℕ) (hjk : j + k ≤ 5)
    (st : State 80 26) (hc : Context s ζ u v w st)
    (hb : QueryBound s ζ u v w W) (hs : listSize (st.lists 21) ≤ W) :
    ((passes j k).run st).2 ≤ k*(passBudget t (4*m) W+1)+1 := by
  induction k generalizing j st with
  | zero => simp [passes, Stmt.run]
  | succ k ih =>
      have hc' := (pass_run s ζ u v w j (by omega) st hc).2
      have hs' : listSize (((pass j).run st).1.lists 21) ≤ W := by
        rw [pass_list j st 21 (by decide) (by decide)]; exact hs
      have hi := ih (j+1) (by omega) ((pass j).run st).1 hc' hs'
      have hp := pass_cost s ζ u v w j W (by omega) st hc hb hs
      rw [passes, run_seq_snd]
      nlinarith only [hi, hp]

end PCP.Lang.StandardCorrection
