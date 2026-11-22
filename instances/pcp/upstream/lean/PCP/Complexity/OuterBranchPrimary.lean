import PCP.Complexity.OuterBranchState

/-!
# Primary Hadamard check of the outer encoded-line branch
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def loadPrimary : Stmt 180 80 :=
  .seq (.copy 41 7)
    (.seq (.copy 41 27)
    (.seq (.copy 47 30)
    (.seq (.copy 48 31)
    (.seq (.copy 50 20)
    (.seq (.copy 51 21)
    (.seq (.copy 52 22)
    (.seq (.copy 53 23)
    (.seq (.assign 20 (.var 120))
    (.seq (.assign 56 (.var 121))
    (.seq (.assign 80 (.var 129))
    (.seq (.assign 81 (.var 130))
    (.seq (.assign 82 (.var 131))
    (.seq (.assign 83 (.var 132))
    (.seq (.assign 84 (.var 133))
    (.seq (.assign 85 (.var 134))
    (.seq (.assign 86 (.var 135))
    (.seq (.assign 87 (.var 136))
    (.seq (.assign 88 (.const 0)) ((.assign 89 (.const 0)))))))))))))))))))))

def callHadamard : Stmt 180 80 := call (by decide) (by decide) HadamardRow.branch

def primaryHadamard : Stmt 180 80 := .seq loadPrimary (.seq callHadamard
  (.seq (.assign 140 (.var 63)) (.revApp 26 49)))

attribute [local irreducible] callHadamard loadPrimary HadamardRow.branch

omit [NeZero t] in
theorem Kind.primary_payload (k : Kind) (eF : Field t ≃ Fin (2 ^ t))
    (x : Point k t n) :
    (k.primary (m := m) x).payload (t := t) eF =
      ![k.tag, (2^t)^n, (2^t)^(n+n), (2^t)^((n+n)+(n+n)), (2^t)^(4*m),
        2^BooleanCoefficientIndex.dimension t 1, 2^BooleanCoefficientIndex.dimension t 3,
        k.pointCode eF x, 0, 0] := by
  cases k <;> funext i <;> fin_cases i <;> rfl

set_option maxRecDepth 1024 in
-- The fixed input-loader AST contains twenty sequential assignments and copies.
theorem loadPrimary_frame (st : State 180 80) : Frame st (loadPrimary.run st).1 :=
  frame_of_writes loadPrimary (by unfold loadPrimary; decide) (by unfold loadPrimary; decide) st

theorem loadPrimary_sources (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    HadamardRow.Sources (primarySeed s)
      ((loadPrimary.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  simp [loadPrimary, HadamardRow.Sources, HadamardRow.Context, HadamardRow.rowRegs,
    Stmt.run, Expr.eval, Function.update, State.restrict, hc.width, hc.degree, hc.empty,
    hc.primaryBase, hc.primaryAuxiliary, hc.primaryLinear, hc.primaryFactors]

theorem loadPrimary_payload (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    HadamardRow.Payload ((k.primary (m := m) s.1.1).payload (t := t) (fieldEquiv t))
      ((loadPrimary.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  rw [Kind.primary_payload]
  intro i
  fin_cases i <;> simp [loadPrimary, Stmt.run, Expr.eval, Function.update, State.restrict,
    HadamardRow.payloadReg, hc.tag, hc.vertices, hc.pairs, hc.proper, hc.inner,
    hc.affineLabels, hc.cubicLabels, hc.leftCode]

def primaryOracle (k : Kind) (qs : List ℕ) (bs : List Bool)
    (x : Point k t n) (label : Coefficients t k.degree) : ZMod 2 :=
  (QueryTree.answersOracle qs bs (ThreeColorQueryIndex.equiv (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
      ((k.primary (m := m) x).query label)).val).toNat

def primaryQueries (k : Kind) (s : Sample k t n m) : List ℕ :=
  (ComputableHadamardTest.queries k.degree_pos (primarySeed s)).map (fun label =>
    (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) ((k.primary (m := m) s.1.1).query label)).val)

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
-- The two nested state embeddings retain the exact physical row implementation.
theorem primaryHadamard_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (primaryHadamard.run st).1.regs 140 =
      (ComputableHadamardTest.test k.degree_pos (primaryOracle (m := m) k qs bs s.1.1)
        (primarySeed s)).toNat ∧
    (primaryHadamard.run st).1.lists 49 = (primaryQueries k s).reverse ++ st.lists 49 ∧
    Frame st (primaryHadamard.run st).1 := by
  have hsrc := loadPrimary_sources k a ζ s qs bs st hc
  have hpay := loadPrimary_payload k a ζ s qs bs st hc
  have hq : (loadPrimary.run st).1.lists 30 = qs := by
    simpa [loadPrimary, Stmt.run, Function.update] using hc.history
  have hb : (loadPrimary.run st).1.lists 31 = bs.map Bool.toNat := by
    simpa [loadPrimary, Stmt.run, Function.update] using hc.answers
  have hr := call_result (by decide) (by decide) HadamardRow.branch (loadPrimary.run st).1
  have hp := HadamardRow.branch_location (fieldEquiv t) (k.primary s.1.1) k.degree_pos
    (primarySeed s) qs bs _ hsrc hpay hq hb
  rw [← hr] at hp
  have hpf := loadPrimary_frame st
  have hcf := call_frame (by decide) (by decide) HadamardRow.branch (loadPrimary.run st).1
  have h49 := call_list (by decide) (by decide) HadamardRow.branch
    (loadPrimary.run st).1 49 (by decide)
  have hload49 := run_lists_frame loadPrimary 49 (by unfold loadPrimary; decide) st
  have htail : Frame (callHadamard.run (loadPrimary.run st).1).1
      ((Stmt.seq (.assign 140 (.var 63)) (.revApp 26 49)).run
        (callHadamard.run (loadPrimary.run st).1).1).1 :=
    frame_of_writes _ (by decide) (by decide) _
  simp only [callHadamard, State.restrict_lists, State.restrict_regs] at hp htail ⊢
  simp only [primaryHadamard, callHadamard, run_seq_fst, run_assign_fst, run_revApp_fst, Expr.eval,
    setReg_regs, setReg_lists, setList_regs, setList_lists, Function.update_self]
  exact ⟨hp.2, congrArg₂ (· ++ ·) (congrArg List.reverse hp.1) (h49.trans hload49),
    hpf.trans (hcf.trans htail)⟩

end PCP.Lang.OuterBranch
