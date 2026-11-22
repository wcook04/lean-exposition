import PCP.Complexity.OuterBranchState

/-!
# Standard correction at an arbitrary stored outer-line parameter

The four-block power sampler is computed before the five actual correction
queries. The parameter may be the outer sample or a separately stored zero.
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t] [NeZero m]

def evaluationPrepare (src : Fin 180) : Stmt 180 80 :=
  .seq (.copy 40 5)
    (.seq (.copy 41 9)
    (.seq (.copy 41 1)
    (.seq (.assign 24 (.var 120))
    (.seq (.assign 28 (.var src)) ((.assign 46 (.var 122)))))))

def evaluationCall : Stmt 180 80 := call (by decide) (by decide) EvaluationPoint.program

def evaluationAt (src : Fin 180) : Stmt 180 80 := .seq (evaluationPrepare src) evaluationCall

def loadStandard : Stmt 180 80 :=
  .seq (.copy 40 3)
    (.seq (.copy 41 7)
    (.seq (.copy 1 12)
    (.seq (.copy 44 13)
    (.seq (.copy 45 17)
    (.seq (.copy 47 22)
    (.seq (.copy 48 23)
    (.seq (.copy 49 20)
    (.seq (.copy 41 21)
    (.seq (.assign 43 (.var 120))
    (.seq (.assign 44 (.var 124))
    (.seq (.assign 45 (.var 123))
    (.seq (.assign 50 (.const 4))
    (.seq (.assign 50 (.add 50 129))
    (.seq (.assign 51 (.var 130))
    (.seq (.assign 52 (.var 131))
    (.seq (.assign 53 (.var 132))
    (.seq (.assign 54 (.var 133))
    (.seq (.assign 55 (.var 134))
    (.seq (.assign 56 (.var 135))
    (.seq (.assign 57 (.var 136)) ((.assign 58 (.var 137)))))))))))))))))))))))

def callStandard : Stmt 180 80 := call (by decide) (by decide) StandardCorrection.program

def standardAt (src : Fin 180) : Stmt 180 80 := .seq (evaluationAt src)
  (.seq loadStandard (.seq callStandard (.seq (.copy 20 49) (.assign 142 (.var 48)))))

attribute [local irreducible] evaluationCall evaluationAt loadStandard callStandard
  EvaluationPoint.program

theorem evaluationPrepare_frame (src : Fin 180) (st : State 180 80) :
    Frame st ((evaluationPrepare src).run st).1 :=
  frame_of_writes _ (by simp [evaluationPrepare, Stmt.regWrites])
    (by simp [evaluationPrepare, Stmt.listWrites]) st

theorem evaluationAt_run (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((evaluationAt src).run st).1.lists 1 = List.ofFn (fun i : Fin (4*m) =>
      (fieldEquiv t (StandardCorrection.vector (SetMultilinear.evaluationPoint m 4 α) i)).val) ∧
    Frame st ((evaluationAt src).run st).1 := by
  have h24 : src ≠ 24 := by intro h; subst src; norm_num at hsrc
  have hv : EvaluationPoint.View m α (((evaluationPrepare src).run st).1.restrict
      (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    simp [evaluationPrepare, EvaluationPoint.View, Stmt.run, Expr.eval, Function.update,
      State.restrict, hc.width, hc.base, hc.modulus, hc.empty, h24, ha]
  have he : ((evaluationPrepare src).run st).1.lists 1 = [] := by
    simp [evaluationPrepare, Stmt.run, Function.update, hc.empty]
  have hp := EvaluationPoint.program_evaluationPoint m α _ hv he
  have hr := call_result (by decide) (by decide) EvaluationPoint.program
    ((evaluationPrepare src).run st).1
  rw [← hr] at hp
  rw [evaluationAt, run_seq_fst]
  refine ⟨?_, (evaluationPrepare_frame src st).trans ?_⟩
  · simpa only [evaluationCall, State.restrict_lists, StandardCorrection.vector,
      Function.comp_apply,
      show Fin.castLE (by decide : 13 ≤ 80) (1 : Fin 13) = (1 : Fin 80) from rfl] using hp
  · simpa only [evaluationCall] using
      call_frame (by decide) (by decide) EvaluationPoint.program ((evaluationPrepare src).run st).1

set_option maxRecDepth 1024 in
-- The loader fixes twenty-two concrete input locations.
theorem loadStandard_frame (st : State 180 80) : Frame st (loadStandard.run st).1 :=
  frame_of_writes _ (by unfold loadStandard; decide) (by unfold loadStandard; decide) st

omit [NeZero t] [NeZero m] in
theorem Kind.line_prefix (k : Kind) (s : Sample k t n m) :
    (k.line s.1).prefix (fieldEquiv t) (2^BooleanCoefficientIndex.dimension t 1)
      (2^BooleanCoefficientIndex.dimension t 3) m =
      ![4+k.tag, (2^t)^n, (2^t)^(n+n), (2^t)^((n+n)+(n+n)), (2^t)^(4*m),
        2^BooleanCoefficientIndex.dimension t 1, 2^BooleanCoefficientIndex.dimension t 3,
        k.pointCode (fieldEquiv t) s.1.1, k.pointCode (fieldEquiv t) s.1.2] := by
  cases k <;> rfl

omit [NeZero m] in
theorem loadStandard_input (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st)
    (he : st.lists 1 = List.ofFn (fun i : Fin (4*m) =>
      (fieldEquiv t (StandardCorrection.vector (SetMultilinear.evaluationPoint m 4 α) i)).val)) :
    StandardCorrection.Input (k.line s.1) ζ (SetMultilinear.evaluationPoint m 4 α)
      s.2.2.1.1 s.2.2.1.2
      ((loadStandard.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [loadStandard, StandardCorrection.PointContext, Stmt.run, Expr.eval,
      Function.update, State.restrict, hc.width, hc.root, hc.card, hc.modulus, hc.empty,
      he, hc.direction]
  · rw [Kind.line_prefix]
    intro i
    fin_cases i <;> simp [loadStandard, StandardCorrection.addressRegs,
      Stmt.run, Expr.eval, Function.update, State.restrict, hc.tag, hc.vertices, hc.pairs,
      hc.proper, hc.inner, hc.affineLabels, hc.cubicLabels, hc.leftCode, hc.rightCode]
  · simpa [loadStandard, Stmt.run, Function.update, State.restrict] using hc.label

theorem evaluationAt_queries (src : Fin 180) (st : State 180 80) :
    ((evaluationAt src).run st).1.lists 49 = st.lists 49 := by
  rw [evaluationAt, run_seq_fst]
  have h := call_list (by decide) (by decide) EvaluationPoint.program
    ((evaluationPrepare src).run st).1 49 (by decide)
  have hp := run_lists_frame (evaluationPrepare src) 49
    (by simp [evaluationPrepare, Stmt.listWrites]) st
  simpa only [evaluationCall] using h.trans hp

theorem call_output_reg {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40)
    (p : Stmt R Q) (st : State 180 80) (i : Fin R) :
    ((call hR hQ p).run st).1.regs (Fin.castLE (hR.trans (by decide)) i) =
      (p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
        (Fin.castLE (hQ.trans (by decide))))).1.regs i :=
  congrArg (fun v : State R Q × ℕ => v.1.regs i) (call_result hR hQ p st)

theorem call_output_list {R Q : ℕ} (hR : R ≤ 120) (hQ : Q ≤ 40)
    (p : Stmt R Q) (st : State 180 80) (i : Fin Q) :
    ((call hR hQ p).run st).1.lists (Fin.castLE (hQ.trans (by decide)) i) =
      (p.run (st.restrict (Fin.castLE (hR.trans (by decide)))
        (Fin.castLE (hQ.trans (by decide))))).1.lists i :=
  congrArg (fun v : State R Q × ℕ => v.1.lists i) (call_result hR hQ p st)

theorem call80_reg48_result (p : Stmt 80 26) (st : State 180 80) :
    ((call (by decide) (by decide) p).run st).1.regs 48 =
      (p.run (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))).1.regs 48 :=
  call_output_reg (by decide) (by decide) p st 48

theorem call80_list20_result (p : Stmt 80 26) (st : State 180 80) :
    ((call (by decide) (by decide) p).run st).1.lists 20 =
      (p.run (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))).1.lists 20 :=
  call_output_list (by decide) (by decide) p st 20


theorem callStandard_reg_result (st : State 180 80) :
    (callStandard.run st).1.regs 48 =
      (StandardCorrection.program.run (st.restrict
        (Fin.castLE (by decide)) (Fin.castLE (by decide)))).1.regs 48 := by
  rw [callStandard]
  exact call80_reg48_result StandardCorrection.program st


theorem callStandard_list_result (st : State 180 80) :
    (callStandard.run st).1.lists 20 =
      (StandardCorrection.program.run (st.restrict
        (Fin.castLE (by decide)) (Fin.castLE (by decide)))).1.lists 20 := by
  rw [callStandard]
  exact call80_list20_result StandardCorrection.program st


omit [NeZero m] in
theorem callStandard_run (k : Kind) (ζ : Field t) (u v : BinaryLocalCorrection.InnerPoint (Field t) m 4)
    (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (uv : (k.Coordinates n → Field t) × (k.Coordinates n → Field t))
    (st : State 180 80)
    (hi : StandardCorrection.Input (k.line uv) ζ u v w
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (hq : st.lists 22 = qs) (hb : st.lists 23 = bs.map Bool.toNat) :
    (callStandard.run st).1.regs 48 =
      (ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
        ((k.line uv).oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
          (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs) u v w).val ∧
    (callStandard.run st).1.lists 20 =
      (((k.line uv).queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
        (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
          (BooleanCoefficientIndex.coefficientEquiv t 3) q).val)).reverse ++ st.lists 20 := by
  have hp := StandardCorrection.program_run (k.line uv) ζ u v w qs bs _ hi hq hb
  have h48 := (callStandard_reg_result st).trans hp.1
  have h20 := (callStandard_list_result st).trans hp.2
  exact ⟨h48, h20⟩


set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
-- The concrete sampler and corrector are composed through their certified state restrictions.
theorem standardAt_run (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((standardAt src).run st).1.regs 142 =
      (ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
        ((k.line s.1).oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
          (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs)
        (SetMultilinear.evaluationPoint m 4 α) s.2.2.1.1 s.2.2.1.2).val ∧
    ((standardAt src).run st).1.lists 49 =
      (((k.line s.1).queries ζ (BinaryMaterializedField.coordinates t) (SetMultilinear.evaluationPoint m 4 α)
        s.2.2.1.1 s.2.2.1.2).map (fun q =>
          (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
            (BooleanCoefficientIndex.coefficientEquiv t 3) q).val)).reverse ++ st.lists 49 ∧
    Frame st ((standardAt src).run st).1 := by
  have he := evaluationAt_run src hsrc k a ζ α s qs bs st hc ha
  have heq := evaluationAt_queries src st
  generalize hEv : ((evaluationAt src).run st).1 = ev at *
  have hev := hc.of_frame he.2
  have hi := loadStandard_input k a ζ α s qs bs ev hev he.1
  have hq : (loadStandard.run ev).1.lists 22 = qs := by
    simpa [loadStandard, Stmt.run, Function.update] using hev.history
  have hb : (loadStandard.run ev).1.lists 23 = bs.map Bool.toNat := by
    simpa [loadStandard, Stmt.run, Function.update] using hev.answers
  have hacc : (loadStandard.run ev).1.lists 20 = st.lists 49 := by
    simpa [loadStandard, Stmt.run, Function.update] using heq
  have hlf := loadStandard_frame ev
  generalize hLoad : (loadStandard.run ev).1 = loaded at *
  have hp := callStandard_run k ζ (SetMultilinear.evaluationPoint m 4 α)
    s.2.2.1.1 s.2.2.1.2 qs bs s.1 loaded hi hq hb
  have h48 := hp.1
  have h20 := hp.2
  have hcf : Frame loaded (callStandard.run loaded).1 := by
    simpa only [callStandard] using call_frame (by decide) (by decide)
      StandardCorrection.program loaded
  generalize hCall : (callStandard.run loaded).1 = out at *
  have htail : Frame out
      ((Stmt.seq (.copy 20 49) (.assign 142 (.var 48))).run out).1 :=
    frame_of_writes _ (by decide) (by decide) _
  have hframe : Frame st ((standardAt src).run st).1 := by
    rw [standardAt, run_seq_fst, hEv, run_seq_fst, hLoad, run_seq_fst, hCall]
    exact he.2.trans (hlf.trans (hcf.trans htail))
  refine ⟨?_, ?_, hframe⟩
  · rw [standardAt, run_seq_fst, hEv, run_seq_fst, hLoad, run_seq_fst, hCall]
    exact h48
  · rw [standardAt, run_seq_fst, hEv, run_seq_fst, hLoad, run_seq_fst, hCall]
    exact h20.trans (congrArg (_ ++ ·) hacc)

theorem evaluationAt_reg (src i : Fin 180) (hi : 120 ≤ i.val) (st : State 180 80) :
    ((evaluationAt src).run st).1.regs i = st.regs i := by
  have hc := call_reg (by decide) (by decide) EvaluationPoint.program
    ((evaluationPrepare src).run st).1 i hi
  have hp : i ∉ (evaluationPrepare src).regWrites := by
    intro hm
    have h : ∀ j ∈ (evaluationPrepare src).regWrites, j.val < 120 := by
      simp [evaluationPrepare, Stmt.regWrites]
    have := h i hm
    omega
  rw [evaluationAt, run_seq_fst]
  simpa only [evaluationCall] using hc.trans (run_regs_frame (evaluationPrepare src) i hp st)

set_option maxRecDepth 1024 in
-- The write list is the fixed twenty-two-instruction loader.
theorem loadStandard_reg (i : Fin 180) (hi : 120 ≤ i.val) (st : State 180 80) :
    (loadStandard.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  intro hm
  have h : ∀ j ∈ loadStandard.regWrites, j.val < 120 := by unfold loadStandard; decide
  have := h i hm
  omega

theorem callStandard_reg (i : Fin 180) (hi : 120 ≤ i.val) (st : State 180 80) :
    (callStandard.run st).1.regs i = st.regs i := by
  rw [callStandard]
  exact call_reg (by decide) (by decide) StandardCorrection.program st i hi

theorem standardTail_reg (i : Fin 180) (hj : i ≠ 142) (st : State 180 80) :
    ((Stmt.seq (.copy 20 49) (.assign 142 (.var 48))).run st).1.regs i = st.regs i := by
  simp only [run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    setReg_regs, setList_regs, Function.update_of_ne hj]

/-- Previously saved check results are retained by every correction call. -/
theorem standardAt_reg (src i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 142)
    (st : State 180 80) : ((standardAt src).run st).1.regs i = st.regs i := by
  rw [standardAt, run_seq_fst, run_seq_fst, run_seq_fst, standardTail_reg i hj,
    callStandard_reg i hi, loadStandard_reg i hi, evaluationAt_reg src i hi]

end PCP.Lang.OuterBranch
