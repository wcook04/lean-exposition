import PCP.Complexity.OuterBranchPointLabel

/-!
# The physical primary homogeneous read of an outer line check

The affine point, homogeneous coefficient code and proof address are all computed.
History lookup retains earliest-match precedence, including hypothetical histories.
-/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def loadPrimaryAddress : Stmt 180 80 :=
  .seq (.copy 49 0) (.seq (.copy 41 1)
  (.seq (.assign 0 (.var 129)) (.seq (.assign 1 (.var 130))
  (.seq (.assign 2 (.var 131)) (.seq (.assign 3 (.var 132))
  (.seq (.assign 4 (.var 133)) (.seq (.assign 5 (.var 134))
  (.seq (.assign 6 (.var 135)) (.seq (.assign 7 (.var 145))
  (.seq (.assign 8 (.const 0)) (.seq (.assign 9 (.const 0))
    (.assign 10 (.var 146)))))))))))))

def callPrimaryAddress : Stmt 180 80 := call (by decide) (by decide) QueryAddress.emit

def emitPrimary : Stmt 180 80 := .seq loadPrimaryAddress
  (.seq callPrimaryAddress (.seq (.copy 0 49) (.assign 147 (.var 11))))

def loadPrimaryHistory : Stmt 180 80 :=
  .seq (.copy 47 0) (.seq (.copy 48 1) (.assign 0 (.var 147)))

def callPrimaryHistory : Stmt 180 80 := call (by decide) (by decide) QueryHistory.program

def readPrimary : Stmt 180 80 :=
  .seq loadPrimaryHistory (.seq callPrimaryHistory (.assign 143 (.var 2)))

def primaryReadAt (src : Fin 180) : Stmt 180 80 :=
  .seq (outerPoint src) (.seq outerLabel (.seq emitPrimary readPrimary))

def primaryRead : Stmt 180 80 := primaryReadAt 125

attribute [local irreducible] QueryAddress.emit QueryHistory.program
  callPrimaryAddress callPrimaryHistory loadPrimaryAddress
  outerPoint outerLabel emitPrimary readPrimary

theorem loadPrimaryAddress_frame (st : State 180 80) :
    Frame st (loadPrimaryAddress.run st).1 :=
  frame_of_writes _ (by unfold loadPrimaryAddress; decide)
    (by unfold loadPrimaryAddress; decide) _

theorem loadPrimaryAddress_view (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (x : Point k t n) (p : Coefficients t k.degree)
    (hx : st.regs 145 = k.pointCode (fieldEquiv t) x)
    (hp : st.regs 146 = HadamardLabel.code p) :
    QueryAddress.View (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p)
      ((loadPrimaryAddress.run st).1.restrict (Fin.castLE (by decide))
        (Fin.castLE (by decide))) := by
  intro i
  rw [HadamardRow.Location.inputs_eq, Kind.primary_payload]
  fin_cases i <;> simp [loadPrimaryAddress, Stmt.run, Expr.eval, State.restrict,
    Function.update, hc.tag, hc.vertices, hc.pairs, hc.proper, hc.inner,
    hc.affineLabels, hc.cubicLabels, hx, hp] <;> rfl

theorem emitPrimary_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (x : Point k t n) (p : Coefficients t k.degree)
    (hx : st.regs 145 = k.pointCode (fieldEquiv t) x)
    (hp : st.regs 146 = HadamardLabel.code p) :
    (emitPrimary.run st).1.regs 147 =
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p)).val ∧
    (emitPrimary.run st).1.lists 49 =
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p)).val ::
          st.lists 49 ∧ Frame st (emitPrimary.run st).1 := by
  have hv := loadPrimaryAddress_view k a ζ s qs bs st hc x p hx hp
  have hs := QueryAddress.emit_run (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p) _ hv
  have ha : (QueryAddress.emit.run
      ((loadPrimaryAddress.run st).1.restrict (Fin.castLE (by decide : 14 ≤ 180))
        (Fin.castLE (by decide : 2 ≤ 80)))).1.regs 11 =
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p)).val := by
    simpa only [QueryAddress.emit, run_seq_fst, run_push_fst, setList_regs] using
      QueryAddress.program_run_state (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) x).query p) _ hv
  have hr := call_result (by decide) (by decide) QueryAddress.emit (loadPrimaryAddress.run st).1
  rw [← hr] at hs ha
  have hf := call_frame (by decide) (by decide) QueryAddress.emit (loadPrimaryAddress.run st).1
  have ht := frame_of_writes (.seq (.copy 0 49) (.assign 147 (.var 11)))
    (by decide) (by decide) (callPrimaryAddress.run (loadPrimaryAddress.run st).1).1
  have h0 : (loadPrimaryAddress.run st).1.lists 0 = st.lists 49 := by
    simp [loadPrimaryAddress, Stmt.run, Function.update]
  simp only [State.restrict_regs, State.restrict_lists] at ha hs
  simp only [emitPrimary, callPrimaryAddress, run_seq_fst, run_copy_fst, run_assign_fst,
    Expr.eval, setList_regs, setReg_regs, setReg_lists, setList_lists, Function.update_self]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [
      show Fin.castLE (by decide : 14 ≤ 180) (11 : Fin 14) = (11 : Fin 180) from rfl] using ha
  · simpa only [h0, State.restrict_lists,
      show Fin.castLE (by decide : 2 ≤ 80) (0 : Fin 2) = (0 : Fin 80) from rfl] using hs.1
  · simpa only [callPrimaryAddress, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
      setList_regs] using (loadPrimaryAddress_frame st).trans
      (hf.trans (by simpa only [callPrimaryAddress, run_seq_fst, run_copy_fst,
        run_assign_fst, Expr.eval, setList_regs] using ht))

theorem readPrimary_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (readPrimary.run st).1.regs 143 = (QueryTree.answersOracle qs bs (st.regs 147)).toNat ∧
      (readPrimary.run st).1.lists 49 = st.lists 49 ∧ Frame st (readPrimary.run st).1 := by
  have hq : (loadPrimaryHistory.run st).1.lists 0 = qs := by
    simpa [loadPrimaryHistory, Stmt.run, Function.update] using hc.history
  have hb : (loadPrimaryHistory.run st).1.lists 1 = bs.map Bool.toNat := by
    simpa [loadPrimaryHistory, Stmt.run, Function.update] using hc.answers
  have ha : (loadPrimaryHistory.run st).1.regs 0 = st.regs 147 := by
    simp [loadPrimaryHistory, Stmt.run, Expr.eval, Function.update]
  have hp := QueryHistory.program_answersOracle
    ((loadPrimaryHistory.run st).1.restrict (Fin.castLE (by decide : 8 ≤ 180))
      (Fin.castLE (by decide : 4 ≤ 80))) bs
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 4 ≤ 80) (1 : Fin 4) = (1 : Fin 80) from rfl] using hb)
  have hr := call_result (by decide) (by decide) QueryHistory.program (loadPrimaryHistory.run st).1
  rw [← hr] at hp
  have hl := frame_of_writes loadPrimaryHistory (by decide) (by decide) st
  have hf := call_frame (by decide) (by decide) QueryHistory.program (loadPrimaryHistory.run st).1
  have ht := frame_of_writes (.assign 143 (.var 2)) (by decide) (by decide)
    (callPrimaryHistory.run (loadPrimaryHistory.run st).1).1
  have h49 := call_list (by decide) (by decide) QueryHistory.program
    (loadPrimaryHistory.run st).1 49 (by decide)
  have hl49 := run_lists_frame loadPrimaryHistory 49 (by decide) st
  simp only [State.restrict_regs, State.restrict_lists] at hp
  simp only [readPrimary, callPrimaryHistory, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, setReg_lists, Function.update_self]
  refine ⟨?_, h49.trans hl49, ?_⟩
  · simpa only [show Fin.castLE (by decide : 8 ≤ 180) (2 : Fin 8) = (2 : Fin 180) from rfl,
      show Fin.castLE (by decide : 8 ≤ 180) (0 : Fin 8) = (0 : Fin 180) from rfl,
      show Fin.castLE (by decide : 4 ≤ 80) (0 : Fin 4) = (0 : Fin 80) from rfl, hq, ha] using hp
  · simpa only [callPrimaryHistory, run_assign_fst, Expr.eval] using
      hl.trans (hf.trans (by simpa only [callPrimaryHistory, run_assign_fst, Expr.eval] using ht))

theorem emitPrimary_reg (i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 147)
    (st : State 180 80) : (emitPrimary.run st).1.regs i = st.regs i := by
  have hl : i ∉ loadPrimaryAddress.regWrites := by
    intro hm
    have hb : ∀ j ∈ loadPrimaryAddress.regWrites, j.val < 120 := by
      unfold loadPrimaryAddress; decide
    have := hb i hm
    omega
  have hf := call_reg (by decide) (by decide) QueryAddress.emit
    (loadPrimaryAddress.run st).1 i hi
  simp only [emitPrimary, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    setReg_regs, setList_regs, Function.update_of_ne hj]
  simpa only [callPrimaryAddress] using hf.trans (run_regs_frame _ _ hl st)

theorem readPrimary_reg (i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 143)
    (st : State 180 80) : (readPrimary.run st).1.regs i = st.regs i := by
  have hl : i ∉ loadPrimaryHistory.regWrites := by
    intro hm
    have hb : ∀ j ∈ loadPrimaryHistory.regWrites, j.val < 120 := by decide
    have := hb i hm
    omega
  have hf := call_reg (by decide) (by decide) QueryHistory.program
    (loadPrimaryHistory.run st).1 i hi
  simp only [readPrimary, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne hj]
  simpa only [callPrimaryHistory] using hf.trans (run_regs_frame _ _ hl st)

/-- Exact primary homogeneous answer and the one appended physical query. -/
theorem primaryReadAt_run (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((primaryReadAt src).run st).1.regs 143 =
      (primaryOracle (m := m) k qs bs (PolynomialLine.point s.1.1 s.1.2 α)
        (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2)).val ∧
    ((primaryReadAt src).run st).1.lists 49 =
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3)
        ((k.primary (m := m) (PolynomialLine.point s.1.1 s.1.2 α)).query
          (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2))).val ::
        st.lists 49 ∧ Frame st ((primaryReadAt src).run st).1 := by
  have hp := outerPoint_run src hsrc k a ζ α s qs bs st hc ha
  have hpa := outerPoint_queries src st
  generalize hP : ((outerPoint src).run st).1 = p at *
  have hcp := hc.of_frame hp.2
  have hl := outerLabel_run k a ζ s qs bs p hcp
  have hla := outerLabel_queries p
  have hlp := (outerLabel_reg 145 (by decide) (by decide) p).trans hp.1
  generalize hL : (outerLabel.run p).1 = l at *
  have hcl := hcp.of_frame hl.2
  have he := emitPrimary_run k a ζ s qs bs l hcl
    (PolynomialLine.point s.1.1 s.1.2 α)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) hlp hl.1
  generalize hE : (emitPrimary.run l).1 = e at *
  have hr := readPrimary_run k a ζ s qs bs e (hcl.of_frame he.2.2)
  simp only [primaryReadAt, run_seq_fst, hP, hL, hE]
  refine ⟨?_, ?_, hp.2.trans (hl.2.trans (he.2.2.trans hr.2.2))⟩
  · rw [hr.1, he.1]
    unfold primaryOracle
    cases QueryTree.answersOracle qs bs _ <;> rfl
  · rw [hr.2.1, he.2.1, hla, hpa]

/-- Standard caller entry point, at the sample's stored outer parameter. -/
theorem primaryRead_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (primaryRead.run st).1.regs 143 =
      (primaryOracle (m := m) k qs bs (PolynomialLine.point s.1.1 s.1.2 s.2.1)
        (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2)).val ∧
    (primaryRead.run st).1.lists 49 =
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3)
        ((k.primary (m := m) (PolynomialLine.point s.1.1 s.1.2 s.2.1)).query
          (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2))).val ::
        st.lists 49 ∧ Frame st (primaryRead.run st).1 :=
  primaryReadAt_run 125 (by decide) k a ζ s.2.1 s qs bs st hc hc.param

/-- The previously computed primary, inner and correction results remain available. -/
theorem primaryReadAt_reg (src i : Fin 180) (hi : 120 ≤ i.val)
    (h143 : i ≠ 143) (h145 : i ≠ 145) (h146 : i ≠ 146) (h147 : i ≠ 147)
    (st : State 180 80) : ((primaryReadAt src).run st).1.regs i = st.regs i := by
  simp only [primaryReadAt, run_seq_fst]
  exact (readPrimary_reg i hi h143 _).trans ((emitPrimary_reg i hi h147 _).trans
    ((outerLabel_reg i hi h146 _).trans (outerPoint_reg src i hi h145 st)))

theorem primaryRead_reg (i : Fin 180) (hi : 120 ≤ i.val)
    (h143 : i ≠ 143) (h145 : i ≠ 145) (h146 : i ≠ 146) (h147 : i ≠ 147)
    (st : State 180 80) : (primaryRead.run st).1.regs i = st.regs i :=
  primaryReadAt_reg 125 i hi h143 h145 h146 h147 st

end PCP.Lang.OuterBranch
