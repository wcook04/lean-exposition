import PCP.Complexity.LocalCorrectionVerdict
import PCP.Complexity.OuterBranchRead
import PCP.Complexity.OuterBranchInner

/-!
# Actual weighted correction from the shared physical branch stages

The primary read, selected inner test and both standard corrections are executed
in the existing protected outer layout. The optional result occupies registers
146 and 147, and every query is prepended to the reversed accumulator in list49.
-/

-- The fixed verdict uses six ports in a 180-register state.
set_option maxRecDepth 1024

namespace PCP.Lang.LocalCorrection

open PCP.Algebraic OuterBranch BinaryFieldCode

variable {t n m : ℕ} [NeZero t] [NeZero m]

def finishRegs : Fin 6 → Fin 180 := ![141, 143, 145, 142, 146, 147]

def finish : Stmt 180 80 := verdict.rename finishRegs Fin.elim0

def saveAndZero : Stmt 180 80 := .seq (.assign 145 (.var 142)) (.assign 139 (.const 0))

def program : Stmt 180 80 := .seq primaryRead (.seq selectedInner
  (.seq (standardAt 125) (.seq saveAndZero (.seq (standardAt 139) finish))))

theorem finish_result (st : State 180 80) :
    ((finish.run st).1.restrict finishRegs Fin.elim0, (finish.run st).2) =
      verdict.run (st.restrict finishRegs Fin.elim0) :=
  verdict.run_rename _ _ (by decide) (by intro i; exact Fin.elim0 i) st

theorem finish_run (ok : Bool) (observed checked recovered : ZMod 2)
    (st : State 180 80) (h0 : st.regs 141 = ok.toNat) (h1 : st.regs 143 = observed.val)
    (h2 : st.regs 145 = checked.val) (h3 : st.regs 142 = recovered.val) :
    (finish.run st).1.regs 146 = present (decision ok observed checked recovered) ∧
    (finish.run st).1.regs 147 = answer (decision ok observed checked recovered) := by
  have h := verdict_run ok observed checked recovered
    (st.restrict finishRegs Fin.elim0) h0 h1 h2 h3
  rw [← finish_result] at h
  exact h

theorem finish_frame (st : State 180 80) : OuterBranch.Frame st (finish.run st).1 :=
  frame_of_writes _ (by decide) (by decide) st

theorem saveAndZero_frame (st : State 180 80) :
    OuterBranch.Frame st (saveAndZero.run st).1 :=
  frame_of_writes _ (by decide) (by decide) st

def observed (k : Kind) (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) : ZMod 2 :=
  primaryOracle (m := m) k qs bs (PolynomialLine.point s.1.1 s.1.2 s.2.1)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2)

def corrected (k : Kind) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) : ZMod 2 :=
  ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
    ((k.line s.1).oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
      (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs)
    (SetMultilinear.evaluationPoint m 4 α) s.2.2.1.1 s.2.2.1.2

def result (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) : Option (ZMod 2) :=
  decision (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs)
    (observed k s qs bs) (corrected k ζ s.2.1 s qs bs) (corrected k ζ 0 s qs bs)

def queryCode (q : ThreeColorVerifier.Query (Field t) n m 4 t) : ℕ :=
  (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
    (BooleanCoefficientIndex.coefficientEquiv t 3) q).val

def queries (k : Kind) (a : Fin 5 → Field t) (ζ : Field t) (s : Sample k t n m) : List ℕ :=
  queryCode ((k.primary (m := m) (PolynomialLine.point s.1.1 s.1.2 s.2.1)).query
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2)) ::
  (InnerBranch.queries a (k.line s.1) (innerSeed s) ++
    ((k.line s.1).queries ζ (BinaryMaterializedField.coordinates t) (SetMultilinear.evaluationPoint m 4 s.2.1)
      s.2.2.1.1 s.2.2.1.2).map queryCode ++
    ((k.line s.1).queries ζ (BinaryMaterializedField.coordinates t) (SetMultilinear.evaluationPoint m 4 0)
      s.2.2.1.1 s.2.2.1.2).map queryCode)

attribute [local irreducible] primaryRead selectedInner standardAt finish

theorem program_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (program.run st).1.regs 146 = present (result k a ζ s qs bs) ∧
    (program.run st).1.regs 147 = answer (result k a ζ s qs bs) ∧
    (program.run st).1.lists 49 = (queries k a ζ s).reverse ++ st.lists 49 ∧
    OuterBranch.Frame st (program.run st).1 := by
  have hP := primaryRead_run k a ζ s qs bs st hc
  generalize hps : (primaryRead.run st).1 = p at *
  have hI := selectedInner_run k a ζ s qs bs p (hc.of_frame hP.2.2)
  have hPI := (selectedInner_reg 143 (by decide) (by decide) p).trans hP.1
  generalize his : (selectedInner.run p).1 = i at *
  have hci := (hc.of_frame hP.2.2).of_frame hI.2.2
  have hZ := standardAt_run 125 (by decide) k a ζ s.2.1 s qs bs i hci hci.param
  have hPZ := (standardAt_reg 125 143 (by decide) (by decide) i).trans hPI
  have hIZ := (standardAt_reg 125 141 (by decide) (by decide) i).trans hI.1
  generalize hzs : ((standardAt 125).run i).1 = z at *
  have hcz := hci.of_frame hZ.2.2
  have hcz' := hcz.of_frame (saveAndZero_frame z)
  have h145 : (saveAndZero.run z).1.regs 145 = (corrected k ζ s.2.1 s qs bs).val := by
    simpa [saveAndZero, Stmt.run, Expr.eval, Function.update, corrected] using hZ.1
  have h139 : (saveAndZero.run z).1.regs 139 = (fieldEquiv t (0 : Field t)).val := by
    change 0 = (fieldEquiv t (0 : Field t)).val
    exact (FieldExpression.code_zero (t := t)).symm
  have h141 : (saveAndZero.run z).1.regs 141 =
      (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs).toNat := by
    simpa [saveAndZero, Stmt.run, Function.update] using hIZ
  have h143 : (saveAndZero.run z).1.regs 143 = (observed k s qs bs).val := by
    simpa [saveAndZero, Stmt.run, Function.update, observed] using hPZ
  generalize hss : (saveAndZero.run z).1 = saved at *
  have hO := standardAt_run 139 (by decide) k a ζ 0 s qs bs saved hcz' h139
  have hf0 := (standardAt_reg 139 141 (by decide) (by decide) saved).trans h141
  have hf1 := (standardAt_reg 139 143 (by decide) (by decide) saved).trans h143
  have hf2 := (standardAt_reg 139 145 (by decide) (by decide) saved).trans h145
  generalize hos : ((standardAt 139).run saved).1 = o at *
  have hf := finish_run _ _ _ _ o hf0 hf1 hf2 hO.1
  have hfl := run_lists_frame finish 49 (by unfold finish; decide) o
  have hsl : saved.lists 49 = z.lists 49 := by
    rw [← hss]; rfl
  have hsf : OuterBranch.Frame z saved := by rw [← hss]; exact saveAndZero_frame z
  simp only [program, run_seq_fst, hps, his, hzs, hss, hos]
  refine ⟨hf.1, hf.2, ?_, hP.2.2.trans (hI.2.2.trans
    (hZ.2.2.trans (hsf.trans (hO.2.2.trans (finish_frame o)))))⟩
  rw [hfl, hO.2.1, hsl, hZ.2.1, hI.2.1, hP.2.1]
  simp only [queries, queryCode, List.reverse_cons, List.reverse_append,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

end PCP.Lang.LocalCorrection
