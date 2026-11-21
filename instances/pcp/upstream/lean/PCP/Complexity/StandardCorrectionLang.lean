import PCP.Complexity.StandardCorrectionQueries
import PCP.Complexity.LangHistoryParityOracle
import Mathlib.Tactic.IrreducibleDef

/-!
# Executable standard local correction with physical answer-history reads

The routine emits exactly five addresses and returns the parity of their actual
first-occurrence history answers. Its query accumulator uses reversed order,
matching the surrounding verifier protocol.
-/

namespace PCP.Lang.StandardCorrection


open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace BooleanCoefficientArithmetic
  BooleanCoefficientIndex

variable {t n m : ℕ} [NeZero t]

def parityRegs : Fin 12 → Fin 80 := ![61, 64, 68, 65, 66, 67, 69, 70, 48, 71, 72, 73]
def parityLists : Fin 6 → Fin 26 := ![22, 23, 24, 25, 20, 18]

theorem parityRegs_injective : Function.Injective parityRegs := by decide
theorem parityLists_injective : Function.Injective parityLists := by decide

def readParity : Stmt 80 26 := HistoryParity.parity.rename parityRegs parityLists

def prepare : Stmt 80 26 := .seq (.copy 20 19) (.seq (.copy 7 20) label)

def generate : Stmt 80 26 := .seq prepare (passes 0 5)

def restore : Stmt 80 26 := .seq (.rev 20) (.seq (.revApp 20 19) (.copy 19 20))

-- Keep the large weighted-query syntax behind a checked equation. This prevents
-- kernel conversion in callers from executing the complete register program.
irreducible_def program : Stmt 80 26 := .seq generate (.seq readParity restore)

attribute [local irreducible] point pass passes prepare generate readParity restore label emit

def Input (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) : Prop :=
  PointContext ζ (vector u) (vector v) st ∧
  (∀ i : Fin 9, st.regs (addressRegs (i.castAdd 5)) =
    s.prefix (fieldEquiv t) (2 ^ dimension t 1) (2 ^ dimension t 3) m i) ∧
  st.lists 17 = List.ofFn (fun i => (w i).val)

theorem label_reg (st : State 80 26) (i : Fin 80)
    (hi : i ∉ [60, 71, 72, 73, 74, 75]) : (label.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [List.mem_cons, not_or] at hi
  simp [label, homogeneous, decodeLabel, Stmt.regWrites, Stmt.regWrites_rename,
    homogeneousRegs, labelRegs, WordCodec.decode, WordCodec.body, WordCodec.setup,
    BooleanAffineList.homogeneous, hi]

theorem label_list (st : State 80 26) (i : Fin 26) (hi : i ≠ 18) :
    (label.run st).1.lists i = st.lists i := by
  apply run_lists_frame
  simpa [label, homogeneous, decodeLabel, Stmt.listWrites, Stmt.listWrites_rename,
    homogeneousLists, labelLists, WordCodec.decode, WordCodec.body, WordCodec.setup,
    BooleanAffineList.homogeneous] using hi

theorem prepare_run (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) (hi : Input s ζ u v w st) :
    Context s ζ u v w (prepare.run st).1 ∧
      (prepare.run st).1.lists 20 = [] ∧ (prepare.run st).1.lists 19 = st.lists 20 := by
  let a := setList (setList st 19 (st.lists 20)) 20 (st.lists 7)
  have ha : (prepare.run st).1 = (label.run a).1 := by
    rw [prepare, run_seq_fst, run_seq_fst, run_copy_fst, run_copy_fst]
    rfl
  have h17 : a.lists 17 = List.ofFn (fun i => (w i).val) := by
    simpa [a, Function.update] using hi.2.2
  rw [ha]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, (label_list a 17 (by decide)).trans h17⟩, ?_, ?_⟩
  · exact (label_reg a 43 (by decide)).trans hi.1.1
  · exact (label_reg a 44 (by decide)).trans hi.1.2.1
  · exact (label_reg a 45 (by decide)).trans hi.1.2.2.1
  · simpa [a, Function.update] using (label_list a 3 (by decide)).trans hi.1.2.2.2.1
  · simpa [a, Function.update] using (label_list a 7 (by decide)).trans hi.1.2.2.2.2.1
  · simpa [a, Function.update] using (label_list a 12 (by decide)).trans hi.1.2.2.2.2.2.1
  · simpa [a, Function.update] using (label_list a 13 (by decide)).trans hi.1.2.2.2.2.2.2
  · intro i
    exact (label_reg a _ (by fin_cases i <;> decide)).trans (hi.2.1 i)
  · simpa [a, Function.update, hi.1.2.2.2.2.1] using label_list a 20 (by decide)
  · simpa [a, Function.update] using label_list a 19 (by decide)

theorem prepare_list (st : State 80 26) (i : Fin 26) (hi : i ∉ [18, 19, 20]) :
    (prepare.run st).1.lists i = st.lists i := by
  have h18 : i ≠ 18 := by simpa using fun h => hi (by simp [h])
  have h19 : i ≠ 19 := by simpa using fun h => hi (by simp [h])
  have h20 : i ≠ 20 := by simpa using fun h => hi (by simp [h])
  rw [prepare, run_seq_fst, run_seq_fst, label_list _ i h18]
  simp [Stmt.run, Function.update, h19, h20]

theorem generate_run (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) (hi : Input s ζ u v w st) :
    (generate.run st).1.lists 20 = ((s.queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1)
        (labelEquiv t 3) q).val)).reverse ∧
    Context s ζ u v w (generate.run st).1 ∧
    (generate.run st).1.lists 19 = st.lists 20 := by
  have hp := prepare_run s ζ u v w st hi
  have hg := passes_run s ζ u v w 0 5 (by decide) (prepare.run st).1 hp.1
  rw [hp.2.1, List.append_nil, codes_eq] at hg
  rw [generate, run_seq_fst]
  exact ⟨hg.1, hg.2, (passes_list 0 5 (prepare.run st).1 19
    (by decide) (by decide)).trans hp.2.2⟩

theorem generate_list (st : State 80 26) (i : Fin 26)
    (hi : 17 ≤ i.val) (hj : i ∉ [18, 19, 20, 24, 25]) :
    (generate.run st).1.lists i = st.lists i := by
  have hp : i ∉ ([18, 20, 24, 25] : List (Fin 26)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; tauto
  have hprep : i ∉ ([18, 19, 20] : List (Fin 26)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; tauto
  rw [generate, run_seq_fst, passes_list _ _ _ i hi hp, prepare_list _ i hprep]

theorem readParity_result (st : State 80 26) :
    ((readParity.run st).1.restrict parityRegs parityLists, (readParity.run st).2) =
      HistoryParity.parity.run (st.restrict parityRegs parityLists) :=
  by
    unfold readParity
    exact Stmt.run_rename _ _ _ parityRegs_injective parityLists_injective st

theorem readParity_frame (st : State 80 26) :
    (readParity.run st).1.lists 20 = st.lists 20 ∧
    (readParity.run st).1.lists 22 = st.lists 22 ∧
    (readParity.run st).1.lists 23 = st.lists 23 ∧
    (readParity.run st).1.lists 19 = st.lists 19 := by
  have hr := readParity_result st
  have hp := HistoryParity.parity_run (st.restrict parityRegs parityLists)
  rw [← hr] at hp
  refine ⟨hp.2.2.2, hp.2.1, hp.2.2.1, ?_⟩
  unfold readParity
  apply Stmt.run_rename_list_outside
  intro i hi
  fin_cases i <;> simp [parityLists] at hi

theorem restore_run (st : State 80 26) :
    (restore.run st).1.lists 20 = st.lists 20 ++ st.lists 19 ∧
      (restore.run st).1.regs 48 = st.regs 48 := by
  simp [restore, Stmt.run, Function.update]

theorem query_sum (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool) :
    (((s.queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) q).val)).map
        (fun a => BinarySeedPadding.boolEquiv (QueryTree.answersOracle qs bs a))).sum =
      ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
        (s.oracle (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) qs bs) u v w := by
  rw [Site.queries_ofFn]
  simp only [List.map_ofFn, Fin.sum_ofFn, ComputableBinaryStandardLocalCorrection.correct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  unfold Site.oracle
  cases QueryTree.answersOracle qs bs
    (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3)
      (s.query (PolynomialLine.point u v (ζ^(i.val+1)))
        (homogeneousIndex (le_refl 1)
          (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
            (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0 i)
              w)))).val <;> rfl

/-- Exact correction answer and five actual queries, for every possibly incomplete history. -/
theorem program_run (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (st : State 80 26) (hi : Input s ζ u v w st)
    (hq : st.lists 22 = qs) (hb : st.lists 23 = bs.map Bool.toNat) :
    (program.run st).1.regs 48 =
      (ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
        (s.oracle (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) qs bs) u v w).val ∧
    (program.run st).1.lists 20 = ((s.queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) q).val)).reverse
        ++ st.lists 20 := by
  have hg := generate_run s ζ u v w st hi
  have hq' := (generate_list st 22 (by decide) (by decide)).trans hq
  have hb' := (generate_list st 23 (by decide) (by decide)).trans hb
  have hp := HistoryParity.parity_oracle qs _ bs
    ((generate.run st).1.restrict parityRegs parityLists) hq' hb' hg.1
  rw [← readParity_result] at hp
  simp only [List.map_reverse, List.sum_reverse, query_sum] at hp
  have hf := readParity_frame (generate.run st).1
  have hr := restore_run (readParity.run (generate.run st).1).1
  rw [program_def, run_seq_fst, run_seq_fst]
  refine ⟨hr.2.trans hp, ?_⟩
  exact hr.1.trans (congrArg₂ (· ++ ·) (hf.1.trans hg.1) (hf.2.2.2.trans hg.2.2))

theorem program_history (st : State 80 26) :
    (program.run st).1.lists 22 = st.lists 22 ∧
    (program.run st).1.lists 23 = st.lists 23 := by
  have hp := readParity_frame (generate.run st).1
  rw [program_def, run_seq_fst, run_seq_fst]
  constructor
  · exact (run_lists_frame restore 22 (by unfold restore; decide) _).trans
      (hp.2.1.trans (generate_list st 22 (by decide) (by decide)))
  · exact (run_lists_frame restore 23 (by unfold restore; decide) _).trans
      (hp.2.2.1.trans (generate_list st 23 (by decide) (by decide)))

end PCP.Lang.StandardCorrection
