import PCP.Complexity.OuterBranchStandard
import PCP.Complexity.InnerBranchLang

/-!
# The actual selected inner low-degree check of an outer branch

Both candidate contexts are materialized from the protected outer sample. The
stored seed coin selects the Hadamard or the interpolation program.
-/

-- These fixed loaders have twenty assignments each.
set_option maxRecDepth 2048

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def loadInnerHad : Stmt 180 80 :=
  .seq (.copy 41 7)
    (.seq (.copy 47 36)
    (.seq (.copy 48 37)
    (.seq (.copy 55 20)
    (.seq (.copy 56 21)
    (.seq (.copy 57 22)
    (.seq (.copy 58 23)
    (.seq (.assign 20 (.var 120))
    (.seq (.assign 56 (.const 1))
    (.seq (.assign 100 (.var 126))
    (.seq (.assign 110 (.const 4))
    (.seq (.assign 110 (.add 110 129))
    (.seq (.assign 111 (.var 130))
    (.seq (.assign 112 (.var 131))
    (.seq (.assign 113 (.var 132))
    (.seq (.assign 114 (.var 133))
    (.seq (.assign 115 (.var 134))
    (.seq (.assign 116 (.var 135))
    (.seq (.assign 117 (.var 136))
    (.seq (.assign 118 (.var 137)) (.assign 119 (.var 138)))))))))))))))))))))

def loadInnerInterpolation : Stmt 180 80 :=
  .seq (.copy 40 3)
    (.seq (.copy 41 7)
    (.seq (.copy 59 32)
    (.seq (.copy 60 33)
    (.seq (.copy 61 34)
    (.seq (.copy 46 35)
    (.seq (.assign 80 (.var 120))
    (.seq (.assign 81 (.var 123))
    (.seq (.assign 82 (.const 0))
    (.seq (.assign 83 (.const 4))
    (.seq (.assign 83 (.add 83 129))
    (.seq (.assign 84 (.var 130))
    (.seq (.assign 85 (.var 131))
    (.seq (.assign 86 (.var 132))
    (.seq (.assign 87 (.var 133))
    (.seq (.assign 88 (.var 134))
    (.seq (.assign 89 (.var 135))
    (.seq (.assign 90 (.var 136)) (.assign 91 (.var 137)))))))))))))))))))

def loadInner : Stmt 180 80 := .seq loadInnerHad loadInnerInterpolation

def callInner : Stmt 180 80 := call (by decide) (by decide) InnerBranch.program

def selectedInner : Stmt 180 80 := .seq loadInner
  (.seq callInner (.seq (.assign 141 (.var 101)) (.revApp 38 49)))

attribute [local irreducible] InnerBranch.program loadInnerHad loadInnerInterpolation
  loadInner callInner

omit [NeZero t] in
theorem Kind.inner_payload (k : Kind) (s : Sample k t n m) :
    (InnerBranch.location (k.line s.1) (innerHadPoint s)).payload (t := t) (fieldEquiv t) =
      ![4+k.tag, (2^t)^n, (2^t)^(n+n), (2^t)^((n+n)+(n+n)), (2^t)^(4*m),
        2^BooleanCoefficientIndex.dimension t 1, 2^BooleanCoefficientIndex.dimension t 3,
        k.pointCode (fieldEquiv t) s.1.1, k.pointCode (fieldEquiv t) s.1.2,
        (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).val] := by
  cases k <;> funext i <;> fin_cases i <;> rfl

theorem loadInner_frame (st : State 180 80) : Frame st (loadInner.run st).1 := by
  rw [loadInner, run_seq_fst]
  exact (frame_of_writes loadInnerHad (by unfold loadInnerHad; decide)
    (by unfold loadInnerHad; decide) st).trans
    (frame_of_writes loadInnerInterpolation (by unfold loadInnerInterpolation; decide)
      (by unfold loadInnerInterpolation; decide) _)

theorem loadInner_hadamard (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    HadamardRow.Sources (innerHadSeed s)
      (((loadInner.run st).1.restrict (Fin.castLE (by decide : 120 ≤ 180))
        (Fin.castLE (by decide : 40 ≤ 80))).restrict InnerBranch.hadRegs InnerBranch.hadLists) := by
  simp [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Expr.eval, Function.update,
    State.restrict, InnerBranch.hadRegs, InnerBranch.hadLists, HadamardRow.Sources,
    HadamardRow.Context, HadamardRow.rowRegs, hc.width, hc.empty,
    hc.innerBase, hc.innerAuxiliary, hc.innerLinear, hc.innerFactors]

theorem loadInner_payload (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    HadamardRow.Payload
      ((InnerBranch.location (k.line s.1) (innerHadPoint s)).payload (t := t) (fieldEquiv t))
      (((loadInner.run st).1.restrict (Fin.castLE (by decide : 120 ≤ 180))
        (Fin.castLE (by decide : 40 ≤ 80))).restrict InnerBranch.hadRegs InnerBranch.hadLists) := by
  rw [Kind.inner_payload]
  intro i
  fin_cases i <;> simp [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Expr.eval,
    Function.update, State.restrict, InnerBranch.hadRegs, InnerBranch.hadLists,
    HadamardRow.payloadReg, hc.tag, hc.vertices, hc.pairs, hc.proper, hc.inner,
    hc.affineLabels, hc.cubicLabels, hc.leftCode, hc.rightCode, hc.innerHadCode]

theorem loadInner_interpolation (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    InterpolationBranch.Context a 0
      (interpolationSeed s).1.1.1 (interpolationSeed s).1.1.2 (interpolationSeed s).2 (k.line s.1)
      (((loadInner.run st).1.restrict (Fin.castLE (by decide : 120 ≤ 180))
        (Fin.castLE (by decide : 40 ≤ 80))).restrict InnerBranch.interpRegs id) := by
  have hzero : BinaryFieldCode.code ((0 : Field t).coefficients) = 0 :=
    FieldExpression.code_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (solve | simp [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Expr.eval,
    Function.update, State.restrict, InnerBranch.interpRegs, hc.width, hc.card, hc.interpParam,
    hc.modulus, hc.empty, hc.interpLeft, hc.interpRight, hc.interpLabel, hc.nodes, hzero])
  intro i
  rw [Kind.line_prefix]
  fin_cases i <;> simp [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Expr.eval,
    Function.update, State.restrict, InnerBranch.interpRegs, InterpolationBranch.prefixPort,
    hc.tag, hc.vertices, hc.pairs, hc.proper, hc.inner, hc.affineLabels, hc.cubicLabels,
    hc.leftCode, hc.rightCode]

theorem loadInner_context (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    InnerBranch.Context a (k.line s.1) (innerSeed s)
      ((loadInner.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, loadInner_hadamard k a ζ s qs bs st hc,
    loadInner_payload k a ζ s qs bs st hc, loadInner_interpolation k a ζ s qs bs st hc⟩
  simpa [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Expr.eval,
    Function.update, State.restrict] using hc.coin

theorem selectedInner_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (selectedInner.run st).1.regs 141 =
      (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs).toNat ∧
    (selectedInner.run st).1.lists 49 =
      (InnerBranch.queries a (k.line s.1) (innerSeed s)).reverse ++ st.lists 49 ∧
      Frame st (selectedInner.run st).1 := by
  have hi := loadInner_context k a ζ s qs bs st hc
  have hq : (loadInner.run st).1.lists 36 = qs := by
    simpa [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Function.update]
      using hc.history
  have hb : (loadInner.run st).1.lists 37 = bs.map Bool.toNat := by
    simpa [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Function.update]
      using hc.answers
  have hp := InnerBranch.program_run a (k.line s.1) (innerSeed s) qs bs _ hi hq hb
  have hr := call_result (by decide) (by decide) InnerBranch.program (loadInner.run st).1
  rw [← hr] at hp
  have hf := call_frame (by decide) (by decide) InnerBranch.program (loadInner.run st).1
  have h49 := call_list (by decide) (by decide) InnerBranch.program
    (loadInner.run st).1 49 (by decide)
  have hl49 : (loadInner.run st).1.lists 49 = st.lists 49 := by
    simp [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Function.update]
  have ht := frame_of_writes (.seq (.assign 141 (.var 101)) (.revApp 38 49))
    (by decide) (by decide) (callInner.run (loadInner.run st).1).1
  simp only [selectedInner, callInner, run_seq_fst, run_assign_fst, run_revApp_fst,
    Expr.eval, setReg_regs, setReg_lists, setList_lists, setList_regs, Function.update_self]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 120 ≤ 180) (101 : Fin 120) = (101 : Fin 180) from rfl]
      using hp.2
  · simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 40 ≤ 80) (38 : Fin 40) = (38 : Fin 80) from rfl] using
      congrArg₂ (· ++ ·) (congrArg List.reverse hp.1) (h49.trans hl49)
  · simpa only [callInner, run_seq_fst, run_assign_fst, run_revApp_fst, Expr.eval,
      setReg_lists] using (loadInner_frame st).trans
      (hf.trans (by simpa only [callInner, run_seq_fst, run_assign_fst, run_revApp_fst,
        Expr.eval, setReg_lists] using ht))

/-- Selected inner checks retain all saved outer results, including primary read143. -/
theorem selectedInner_reg (i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 141)
    (st : State 180 80) : (selectedInner.run st).1.regs i = st.regs i := by
  have hl : i ∉ loadInner.regWrites := by
    intro hm
    have hb : ∀ j ∈ loadInner.regWrites, j.val < 120 := by
      unfold loadInner loadInnerHad loadInnerInterpolation; decide
    have := hb i hm
    omega
  have hf := call_reg (by decide) (by decide) InnerBranch.program (loadInner.run st).1 i hi
  simp only [selectedInner, run_seq_fst, run_assign_fst, run_revApp_fst, Expr.eval,
    setList_regs, setReg_regs, Function.update_of_ne hj]
  simpa only [callInner] using hf.trans (run_regs_frame _ _ hl st)

end PCP.Lang.OuterBranch
