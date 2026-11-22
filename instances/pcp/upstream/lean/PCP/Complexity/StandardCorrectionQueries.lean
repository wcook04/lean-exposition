import PCP.Complexity.StandardCorrectionWeight
import PCP.Complexity.StandardCorrectionAddressLang

/-!
# The five concrete physical queries of standard local correction
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace BooleanCoefficientArithmetic
  BooleanCoefficientIndex

variable {t n m : ℕ} [NeZero t]

abbrev labelEquiv (t r : ℕ) := BooleanCoefficientIndex.coefficientEquiv t r

/-- Fixed physical site together with the immutable arithmetic inputs and shared label. -/
def Context (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) : Prop :=
  PointContext ζ (vector u) (vector v) st ∧
  (∀ i : Fin 9, st.regs (addressRegs (i.castAdd 5)) =
    s.prefix (fieldEquiv t) (2 ^ dimension t 1) (2 ^ dimension t 3) m i) ∧
  st.lists 17 = List.ofFn fun i => (w i).val

def queryLabel (ζ : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2) (j : ℕ) :=
  homogeneousIndex (le_refl 1)
    (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
      (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0
        ⟨j % 5, Nat.mod_lt _ (by decide)⟩) w)

@[simp] theorem queryLabel_coe (ζ : BinaryMaterializedField.Element t)
    (w : Fin t → ZMod 2) (i : Fin 5) :
    queryLabel ζ w i.val = homogeneousIndex (le_refl 1)
      (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
        (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0 i) w) := by
  simp [queryLabel, Nat.mod_eq_of_lt i.isLt]

def queryCode (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j : ℕ) : ℕ :=
  (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3)
    (s.query (PolynomialLine.point u v (ζ^(j+1))) (queryLabel ζ w j))).val

def pass (j : ℕ) : Stmt 80 26 :=
  .seq (.assign 46 (.const (j+1)))
    (.seq (weightedLabel ⟨j % 5, Nat.mod_lt _ (by decide)⟩) (.seq point emit))

def passes (j : ℕ) : ℕ → Stmt 80 26
  | 0 => .skip
  | k+1 => .seq (pass j) (passes (j+1) k)

theorem emit_reg (st : State 80 26) (i : Fin 80) (hi : i ∉ [61, 62, 63]) :
    (emit.run st).1.regs i = st.regs i := by
  by_cases hin : ∃ j : Fin 11, addressRegs (j.castAdd 3) = i
  · obtain ⟨j, rfl⟩ := hin
    exact (emit_frame st).1 j
  · apply Stmt.run_rename_reg_outside
    intro j hj
    have hlt : j.val < 11 := by
      by_contra hn
      have hj' : j = 11 ∨ j = 12 ∨ j = 13 := by omega
      rcases hj' with rfl | rfl | rfl <;> simp_all [addressRegs]
    exact hin ⟨⟨j.val, hlt⟩, hj⟩

theorem emit_list (st : State 80 26) (i : Fin 26) (hi : i ≠ 20) :
    (emit.run st).1.lists i = st.lists i := by
  by_cases h21 : i = 21
  · subst i; exact (emit_frame st).2
  · apply Stmt.run_rename_list_outside
    intro j hj
    fin_cases j <;> simp_all [addressLists]

theorem emit_context (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (st : State 80 26) (hc : Context s ζ u v w st) :
    Context s ζ u v w (emit.run st).1 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (emit_reg st 43 (by decide)).trans hc.1.1
  · exact (emit_reg st 44 (by decide)).trans hc.1.2.1
  · exact (emit_reg st 45 (by decide)).trans hc.1.2.2.1
  · exact (emit_list st 3 (by decide)).trans hc.1.2.2.2.1
  · exact (emit_list st 7 (by decide)).trans hc.1.2.2.2.2.1
  · exact (emit_list st 12 (by decide)).trans hc.1.2.2.2.2.2.1
  · exact (emit_list st 13 (by decide)).trans hc.1.2.2.2.2.2.2
  · intro i
    exact ((emit_frame st).1 (i.castAdd 2)).trans (hc.2.1 i)
  · exact (emit_list st 17 (by decide)).trans hc.2.2

attribute [local irreducible] point emit weightedLabel weightScale weightLabelLoad weightEncode

theorem weighted_context (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j : Fin 5) (st : State 80 26) (hc : Context s ζ u v w st) :
    Context s ζ u v w ((weightedLabel j).run st).1 := by
  refine ⟨weightedLabel_context ζ (vector u) (vector v) j st hc.1, ?_, ?_⟩
  · intro i
    exact (weightedLabel_reg j st _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)).trans (hc.2.1 i)
  · exact (weightedLabel_list j st 17 (by decide) (by decide)).trans hc.2.2

theorem point_address (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j : ℕ) (hj : j < 5)
    (st : State 80 26) (hc : Context s ζ u v w st) (he : st.regs 46 = j + 1)
    (hl : st.regs 60 = (labelEquiv t 1 (queryLabel ζ w j)).val) :
    AddressContext (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) s
      (PolynomialLine.point u v (ζ^(j+1))) (queryLabel ζ w j) (point.run st).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (point_reg st _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)).trans (hc.2.1 i)
  · simpa only [← vector_point, vector_index] using
      point_run ζ (vector u) (vector v) (j+1) (by omega) st hc.1 he
  · exact (point_reg st 60 (by decide) (by decide)).trans hl

theorem assign_context (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j : ℕ) (st : State 80 26) (hc : Context s ζ u v w st) :
    Context s ζ u v w (setReg st 46 (j+1)) := by
  refine ⟨?_, ?_, hc.2.2⟩
  · simpa [PointContext, Function.update] using hc.1
  · intro i
    have he : addressRegs (i.castAdd 5) ≠ 46 := by fin_cases i <;> decide
    simpa [Function.update, he] using hc.2.1 i

theorem pass_run (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j : ℕ) (hj : j < 5)
    (st : State 80 26) (hc : Context s ζ u v w st) :
    (pass j |>.run st).1.lists 20 = queryCode s ζ u v w j :: st.lists 20 ∧
      Context s ζ u v w (pass j |>.run st).1 := by
  let a := setReg st 46 (j+1)
  let i : Fin 5 := ⟨j % 5, Nat.mod_lt _ (by decide)⟩
  have hac := assign_context s ζ u v w j st hc
  have hwc := weighted_context s ζ u v w i a hac
  have hwl := weightedLabel_run ζ (vector u) (vector v) i w a hac.1 hac.2.2
  have hwe : ((weightedLabel i).run a).1.regs 46 = j+1 :=
    (weightedLabel_reg i a 46 (by decide) (by decide) (by decide)).trans (by simp [a])
  have hw20 := weightedLabel_list i a 20 (by decide) (by decide)
  generalize hs : ((weightedLabel i).run a).1 = b at *
  have hpc := point_context ζ (vector u) (vector v) (j+1) (by omega) b hwc.1 hwe
  have hpref (k : Fin 9) := (point_reg b (addressRegs (k.castAdd 5))
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)).trans (hwc.2.1 k)
  have hw : (point.run b).1.lists 17 = List.ofFn fun k => (w k).val :=
    (point_lists_outside b 17 (by decide)).trans hwc.2.2
  have hadd := point_address s ζ u v w j hj b hwc hwe hwl
  have he := emit_run (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) s
    (PolynomialLine.point u v (ζ^(j+1))) (queryLabel ζ w j) _ hadd
  have hctx := emit_context s ζ u v w _ ⟨hpc, hpref, hw⟩
  have h20 := (point_lists_outside b 20 (by decide)).trans hw20
  simp only [pass, run_seq_fst, run_assign_fst, Expr.eval]
  change (emit.run (point.run ((weightedLabel i).run a).1).1).1.lists 20 = _ ∧ _
  rw [hs]
  exact ⟨he.1.trans (congrArg (queryCode s ζ u v w j :: ·) h20), hctx⟩

theorem passes_run (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) (j k : ℕ) (hjk : j + k ≤ 5)
    (st : State 80 26) (hc : Context s ζ u v w st) :
    ((passes j k).run st).1.lists 20 =
      ((List.range' j k).map (queryCode s ζ u v w)).reverse ++ st.lists 20 ∧
    Context s ζ u v w ((passes j k).run st).1 := by
  induction k generalizing j st with
  | zero => simp [passes, Stmt.run, hc]
  | succ k ih =>
      have hp := pass_run s ζ u v w j (by omega) st hc
      have hh := ih (j+1) (by omega) (pass j |>.run st).1 hp.2
      rw [passes, run_seq_fst]
      refine ⟨?_, hh.2⟩
      rw [hh.1, hp.1]
      simp [List.range'_succ, List.reverse_cons, List.append_assoc]

theorem pass_list (j : ℕ) (st : State 80 26) (i : Fin 26)
    (hi : 17 ≤ i.val) (hj : i ∉ [18, 20, 24, 25]) :
    ((pass j).run st).1.lists i = st.lists i := by
  have h20 : i ≠ 20 := fun h => hj (by simp [h])
  have hw : i ∉ ([14, 15, 16, 18, 24, 25] : List (Fin 26)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at * <;> tauto
  rw [pass, run_seq_fst, run_seq_fst, run_seq_fst, emit_list _ i h20,
    point_lists_outside _ i hi, weightedLabel_list _ _ i (by omega) hw]
  rfl

theorem passes_list (j k : ℕ) (st : State 80 26) (i : Fin 26)
    (hi : 17 ≤ i.val) (hj : i ∉ [18, 20, 24, 25]) :
    ((passes j k).run st).1.lists i = st.lists i := by
  induction k generalizing j st with
  | zero => rfl
  | succ k ih => rw [passes, run_seq_fst, ih, pass_list _ _ i hi hj]

theorem codes_eq (s : Site (BinaryMaterializedField.Element t) n)
    (ζ : BinaryMaterializedField.Element t)
    (u v : BinaryLocalCorrection.InnerPoint (BinaryMaterializedField.Element t) m 4)
    (w : Fin t → ZMod 2) :
    (List.range' 0 5).map (queryCode s ζ u v w) =
      (s.queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
        (ThreeColorQueryIndex.equiv (fieldEquiv t) (labelEquiv t 1) (labelEquiv t 3) q).val) := by
  rw [Site.queries_ofFn, List.map_ofFn]
  simp only [List.ofFn_succ, List.ofFn_zero, List.range'_succ, List.range'_zero,
    List.map_cons, List.map_nil]
  rfl

end PCP.Lang.StandardCorrection
