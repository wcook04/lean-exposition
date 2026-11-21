import PCP.Complexity.OuterBranchRead
import PCP.Complexity.OuterBranchPointLabelCost
import PCP.Complexity.OuterBranchResources

/-!
# Cost of the actual outer primary homogeneous read
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] QueryAddress.emit QueryHistory.program
  callPrimaryAddress callPrimaryHistory loadPrimaryAddress outerPoint outerLabel
  emitPrimary readPrimary

def PrimaryBound (k : Kind) (x : Point k t n) (p : Coefficients t k.degree) (W : ℕ) : Prop :=
  (∀ i : Fin 11, Nat.size (QueryAddress.inputs (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
      ((k.primary (m := m) x).query p) i) ≤ W) ∧
  Nat.size (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p)).val ≤ W

omit [NeZero t] in
theorem PrimaryBound.point {k : Kind} {x : Point k t n} {p : Coefficients t k.degree} {W : ℕ}
    (hb : PrimaryBound (m := m) k x p W) : Nat.size (k.pointCode (fieldEquiv t) x) ≤ W := by
  have h := hb.1 7
  rw [HadamardRow.Location.inputs_eq, Kind.primary_payload] at h
  exact h

omit [NeZero t] in
theorem PrimaryBound.label {k : Kind} {x : Point k t n} {p : Coefficients t k.degree} {W : ℕ}
    (hb : PrimaryBound (m := m) k x p W) : Nat.size (HadamardLabel.code p) ≤ W := by
  have h := hb.1 10
  rw [HadamardRow.Location.inputs_eq] at h
  exact h

set_option maxRecDepth 1024 in
-- The fixed address loader has thirteen assignments and copies.
theorem loadPrimaryAddress_cost (W : ℕ) (st : State 180 80) (hb : StoredBound W st)
    (hp : Nat.size (st.regs 145) ≤ W) (hl : Nat.size (st.regs 146) ≤ W) :
    (loadPrimaryAddress.run st).2 ≤ loaderConstant loadPrimaryAddress *
      (W+listSize (st.lists 49)+1) := by
  apply loopFree_cost_le loadPrimaryAddress (by unfold loadPrimaryAddress; decide)
    st (W+listSize (st.lists 49))
  · intro i hi
    have huse : ∀ j ∈ loadPrimaryAddress.uses,
        (120 ≤ j.val ∧ j.val < 139) ∨ j = 145 ∨ j = 146 := by
      unfold loadPrimaryAddress; decide
    rcases huse i hi with h | rfl | rfl
    · have := hb.regs i h.1 h.2
      omega
    · omega
    · omega
  · intro i hi
    have huse : ∀ j ∈ loadPrimaryAddress.lUses, j = 41 ∨ j = 49 := by
      unfold loadPrimaryAddress; decide
    rcases huse i hi with rfl | rfl
    · have := hb.lists 41 (by decide) (by decide) (by decide)
      omega
    · omega

theorem emitPrimary_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st)
    (x : Point k t n) (p : Coefficients t k.degree)
    (hx : st.regs 145 = k.pointCode (fieldEquiv t) x)
    (hp : st.regs 146 = HadamardLabel.code p) (hb : PrimaryBound (m := m) k x p W) :
    (emitPrimary.run st).2 ≤ loaderConstant loadPrimaryAddress *
      (W+listSize (st.lists 49)+1) + StandardCorrection.addressConstant*(W+1) +
      listSize (st.lists 49)+3*W+6 := by
  have hl := loadPrimaryAddress_cost W st hs (by rw [hx]; exact hb.point)
    (by rw [hp]; exact hb.label)
  have hv := loadPrimaryAddress_view k a ζ s qs bs st hc x p hx hp
  have he : (loadPrimaryAddress.run st).1.lists 1 = [] := by
    simpa [loadPrimaryAddress, Stmt.run, Function.update] using hc.empty
  have hcost := QueryAddress.emit_cost (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
    ((k.primary (m := m) x).query p) _ hv W
    (fun i => by rw [hv i]; exact hb.1 i)
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 2 ≤ 80) (1 : Fin 2) = (1 : Fin 80) from rfl,
      he, show listSize [] = 0 from rfl] using Nat.zero_le W) hb.2
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) QueryAddress.emit
    (loadPrimaryAddress.run st).1)] at hcost
  have hcall : (callPrimaryAddress.run (loadPrimaryAddress.run st).1).2 ≤
      StandardCorrection.addressConstant*(W+1) := by
    simpa only [callPrimaryAddress, Prod.snd, StandardCorrection.addressConstant] using hcost
  have hout := emitPrimary_run k a ζ s qs bs st hc x p hx hp
  simp only [emitPrimary, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    setReg_regs, setReg_lists, setList_regs, setList_lists, Function.update_self] at hout
  have haddr : Nat.size ((callPrimaryAddress.run (loadPrimaryAddress.run st).1).1.regs 11) ≤ W := by
    rw [hout.1]; exact hb.2
  have hlist : listSize ((callPrimaryAddress.run (loadPrimaryAddress.run st).1).1.lists 0) ≤
      W+1+listSize (st.lists 49) := by
    rw [hout.2.1]
    simpa only [listSize, List.map_cons, List.sum_cons] using
      Nat.add_le_add_right (Nat.add_le_add_right hb.2 1) (listSize (st.lists 49))
  rw [emitPrimary, run_seq_snd, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setList_regs]
  omega

theorem readPrimary_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : Nat.size (st.regs 147) ≤ W) :
    (readPrimary.run st).2 ≤ (QueryHistory.passConstant+40)*
      (listSize (st.lists 47)+listSize (st.lists 48)+W+2)^2 := by
  have hp := QueryHistory.program_cost ((loadPrimaryHistory.run st).1.restrict
    (Fin.castLE (by decide : 8 ≤ 180)) (Fin.castLE (by decide : 4 ≤ 80)))
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) QueryHistory.program
    (loadPrimaryHistory.run st).1)] at hp
  have hcall : (callPrimaryHistory.run (loadPrimaryHistory.run st).1).2 ≤
      (QueryHistory.passConstant+20)*
        (listSize (st.lists 47)+listSize (st.lists 48)+Nat.size (st.regs 147)+2)^2 := by
    simpa only [callPrimaryHistory, Prod.snd, State.restrict_lists, State.restrict_regs,
      loadPrimaryHistory, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
      setList_lists, setReg_lists, setList_regs, setReg_regs, Function.update,
      show Fin.castLE (by decide : 4 ≤ 80) (0 : Fin 4) = (0 : Fin 80) from rfl,
      show Fin.castLE (by decide : 4 ≤ 80) (1 : Fin 4) = (1 : Fin 80) from rfl,
      show Fin.castLE (by decide : 8 ≤ 180) (0 : Fin 8) = (0 : Fin 180) from rfl,
      Fin.reduceEq, dite_true, dite_false] using hp
  have hcall' := hcall.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by omega : listSize (st.lists 47)+listSize (st.lists 48)+Nat.size (st.regs 147)+2 ≤
      listSize (st.lists 47)+listSize (st.lists 48)+W+2) 2))
  have hload : (loadPrimaryHistory.run st).2 ≤
      listSize (st.lists 47)+listSize (st.lists 48)+2*W+5 := by
    simp only [loadPrimaryHistory, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
      setList_regs, setList_lists, Function.update, Fin.reduceEq, dite_false]
    omega
  have hout := (readPrimary_run k a ζ s qs bs st hc).1
  simp only [readPrimary, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self] at hout
  have hsize : Nat.size ((callPrimaryHistory.run (loadPrimaryHistory.run st).1).1.regs 2) ≤ 1 := by
    rw [hout]
    cases QueryTree.answersOracle qs bs (st.regs 147) <;> decide
  have hpow : listSize (st.lists 47)+listSize (st.lists 48)+W+2 ≤
      (listSize (st.lists 47)+listSize (st.lists 48)+W+2)^2 := Nat.le_pow (by decide)
  rw [readPrimary, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  nlinarith only [hcall', hload, hsize, hpow]

/-- Every stage, including physical history lookup, is included in the charged bound. -/
theorem primaryReadAt_cost (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st)
    (ha : st.regs src = (fieldEquiv t α).val)
    (hb : PrimaryBound (m := m) k (PolynomialLine.point s.1.1 s.1.2 α)
      (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) W) :
    ((primaryReadAt src).run st).2 ≤
      (RadixCodec.passConstant+101000100)*(t+k.dimension n+2)^5 +
      (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)*(2^t+7)^8 +
      loaderConstant loadPrimaryAddress*(W+listSize (st.lists 49)+1) +
      StandardCorrection.addressConstant*(W+1)+listSize (st.lists 49)+3*W+6 +
      (QueryHistory.passConstant+40)*
        (listSize (st.lists 47)+listSize (st.lists 48)+W+2)^2 + 3 := by
  have hp := outerPoint_run src hsrc k a ζ α s qs bs st hc ha
  have hpc := outerPoint_cost src hsrc k a ζ α s qs bs st hc ha
  have hpa := outerPoint_queries src st
  generalize hP : ((outerPoint src).run st).1 = p at *
  have hcp := hc.of_frame hp.2
  have hsp := hs.of_frame hp.2
  have hl := outerLabel_run k a ζ s qs bs p hcp
  have hlc := outerLabel_cost k a ζ s qs bs p hcp
  have hla := outerLabel_queries p
  have hlp := (outerLabel_reg 145 (by decide) (by decide) p).trans hp.1
  generalize hL : (outerLabel.run p).1 = l at *
  have hcl := hcp.of_frame hl.2
  have hsl := hsp.of_frame hl.2
  have he := emitPrimary_run k a ζ s qs bs l hcl
    (PolynomialLine.point s.1.1 s.1.2 α)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) hlp hl.1
  have hec := emitPrimary_cost k a ζ s qs bs W l hcl hsl
    (PolynomialLine.point s.1.1 s.1.2 α)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) hlp hl.1 hb
  rw [hla, hpa] at hec
  generalize hE : (emitPrimary.run l).1 = e at *
  have hr := readPrimary_cost k a ζ s qs bs W e (hcl.of_frame he.2.2)
    (by rw [he.1]; exact hb.2)
  have hf := hp.2.trans (hl.2.trans he.2.2)
  rw [hf.lists 47 (by decide) (by decide) (by decide),
    hf.lists 48 (by decide) (by decide) (by decide)] at hr
  simp only [primaryReadAt, run_seq_snd, hP, hL, hE]
  omega

end PCP.Lang.OuterBranch
