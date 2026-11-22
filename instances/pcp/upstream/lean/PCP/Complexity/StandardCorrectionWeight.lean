import PCP.Complexity.GeneratorWeightLang
import PCP.Complexity.StandardCorrectionAddressLang
import PCP.Complexity.StandardCorrectionFrame
import PCP.Complexity.BinaryLabelScaleCost

/-! # Computing the weighted homogeneous label of each correction query -/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode FieldExpression BinaryPolynomialSpace

variable {t d : ℕ} [NeZero t]

def weightCall (i : Fin 5) : Stmt 80 26 :=
  (generatorWeight 4 i).rename (Fin.castLE (by decide)) (Fin.castLE (by decide))

def weightLabelLoad (i : Fin 5) : Stmt 80 26 := .seq (.assign 0 (.var 44))
  (.seq (.assign 21 (.var 43)) (weightCall i))

theorem weightCall_result (i : Fin 5) (st : State 80 26) :
    (((weightCall i).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      ((weightCall i).run st).2) = (generatorWeight 4 i).run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  Stmt.run_rename _ _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem weightLabelLoad_run (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (i : Fin 5)
    (st : State 80 26) (hc : PointContext ζ u v st) :
    ((weightLabelLoad i).run st).1.regs 27 =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight
        (GeneratorLowDegreeTest.nodes 4 ζ) 0 i)).val ∧
    ((weightLabelLoad i).run st).1.lists 3 = st.lists 3 ∧
    ((weightLabelLoad i).run st).1.lists 7 = st.lists 7 := by
  let s := setReg (setReg st 0 (st.regs 44)) 21 (st.regs 43)
  have hv : View t (fun _ : Fin 1 => ζ)
      (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    refine ⟨?_, ?_, hc.2.2.2.1, hc.2.2.2.2.1⟩
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa [s, Function.update] using hc.2.1
    · simpa [s, Function.update, slot] using hc.1
  have hp := generatorWeight_run ζ i _ hv
  have hr := weightCall_result i s
  have h27 := congrArg (fun p : State 37 12 × ℕ => p.1.regs 27) hr
  have h3 := congrArg (fun p : State 37 12 × ℕ => p.1.lists 3) hr
  have h7 := congrArg (fun p : State 37 12 × ℕ => p.1.lists 7) hr
  simp only [weightLabelLoad, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  exact ⟨h27.trans hp.1, (h3.trans hp.2.2.2.1).trans hc.2.2.2.1.symm,
    (h7.trans hp.2.2.2.2).trans hc.2.2.2.2.1.symm⟩

theorem weightLabelLoad_reg (j : Fin 5) (st : State 80 26) (i : Fin 80)
    (hi : 37 ≤ i.val) : ((weightLabelLoad j).run st).1.regs i = st.regs i := by
  simp only [weightLabelLoad, run_seq_fst, run_assign_fst, Expr.eval, weightCall]
  rw [Stmt.run_rename_reg_outside (generatorWeight 4 j)
    (Fin.castLE (by decide)) (Fin.castLE (by decide)) i (by
      intro k hk; have := congrArg Fin.val hk; simp only [Fin.val_castLE] at this; omega)]
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h21 : i ≠ 21 := by intro h; subst i; norm_num at hi
  simp [Function.update, h0, h21]

theorem weightLabelLoad_list (j : Fin 5) (st : State 80 26) (i : Fin 26)
    (hi : 12 ≤ i.val) : ((weightLabelLoad j).run st).1.lists i = st.lists i := by
  simp only [weightLabelLoad, run_seq_fst, run_assign_fst, Expr.eval, weightCall]
  rw [Stmt.run_rename_list_outside (generatorWeight 4 j)
    (Fin.castLE (by decide)) (Fin.castLE (by decide)) i (by
      intro k hk; have := congrArg Fin.val hk; simp only [Fin.val_castLE] at this; omega)]
  rfl

def weightScaleRegs (i : Fin 54) : Fin 80 :=
  if h : i.val < 42 then ⟨i.val, by omega⟩ else ⟨i.val+26, by omega⟩

def weightScaleLists (i : Fin 18) : Fin 26 :=
  if i = 12 then 24 else if i = 13 then 25 else i.castLE (by decide)

theorem weightScaleRegs_injective : Function.Injective weightScaleRegs := by decide
theorem weightScaleLists_injective : Function.Injective weightScaleLists := by decide

def weightScale : Stmt 80 26 :=
  BinaryLabelScale.scale.rename weightScaleRegs weightScaleLists

def weightScalePrepare : Stmt 80 26 := .seq (.assign 24 (.var 27)) (.assign 20 (.var 43))

def weightEncode : Stmt 80 26 := label.rename id (Equiv.swap 16 17)

def weightedLabel (i : Fin 5) : Stmt 80 26 := .seq (weightLabelLoad i)
  (.seq weightScalePrepare (.seq weightScale weightEncode))

theorem weightScale_run (a : BinaryMaterializedField.Element t) (w : Fin t → ZMod 2)
    (st : State 80 26) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hw : st.lists 17 = List.ofFn fun i => (w i).val) :
    (weightScale.run st).1.lists 16 = List.ofFn fun i =>
      (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) a w i).val := by
  have hr := BinaryLabelScale.scale.run_rename weightScaleRegs weightScaleLists
    weightScaleRegs_injective weightScaleLists_injective st
  exact (congrArg (fun p : State 54 18 × ℕ => p.1.lists 16) hr).trans
    (BinaryLabelScale.scale_run a w _ ht ha hm he hw)

theorem weightEncode_run (w : Fin t → ZMod 2) (st : State 80 26)
    (hw : st.lists 16 = List.ofFn fun i => (w i).val) :
    (weightEncode.run st).1.regs 60 =
      (BooleanCoefficientIndex.coefficientEquiv t 1
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) w)).val := by
  have hr := label.run_rename id (Equiv.swap 16 17) Function.injective_id
    (Equiv.swap 16 17).injective st
  exact (congrArg (fun p : State 80 26 × ℕ => p.1.regs 60) hr).trans
    (label_run w _ hw)

theorem weightedLabel_run (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (i : Fin 5) (w : Fin t → ZMod 2)
    (st : State 80 26) (hc : PointContext ζ u v st)
    (hw : st.lists 17 = List.ofFn fun j => (w j).val) :
    ((weightedLabel i).run st).1.regs 60 =
      (BooleanCoefficientIndex.coefficientEquiv t 1
        (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1)
          (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t)
            (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0 i) w))).val := by
  have hload := weightLabelLoad_run ζ u v i st hc
  have ht := weightLabelLoad_reg i st 43 (by decide)
  have hw' := weightLabelLoad_list i st 17 (by decide)
  simp only [weightedLabel, run_seq_fst]
  generalize hs : ((weightLabelLoad i).run st).1 = s at *
  let a := setReg (setReg s 24 (s.regs 27)) 20 (s.regs 43)
  have hscale := weightScale_run
    (FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0 i) w a
    (by simpa [a] using ht.trans hc.1) (by simpa [a, Function.update] using hload.1)
    (by simpa [a] using hload.2.1.trans hc.2.2.2.1)
    (by simpa [a] using hload.2.2.trans hc.2.2.2.2.1)
    (by simpa [a] using hw'.trans hw)
  simp only [weightScalePrepare, run_seq_fst, run_assign_fst, Expr.eval]
  exact weightEncode_run _ _ hscale



theorem weightScale_reg (st : State 80 26) (i : Fin 80)
    (hlo : 42 ≤ i.val) (hhi : i.val < 68) :
    (weightScale.run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have he := congrArg Fin.val hj
  simp only [weightScaleRegs] at he
  split_ifs at he <;> simp only [Fin.val_mk] at he <;> omega

theorem weightScale_list (st : State 80 26) (i : Fin 26)
    (hlo : 12 ≤ i.val) (hi : i ∉ [14, 15, 16, 24, 25]) :
    (weightScale.run st).1.lists i = st.lists i := by
  by_cases h17 : i = 17
  · subst i
    have hr := BinaryLabelScale.scale.run_rename weightScaleRegs weightScaleLists
      weightScaleRegs_injective weightScaleLists_injective st
    exact (congrArg (fun p : State 54 18 × ℕ => p.1.lists 17) hr).trans
      (BinaryLabelScale.scale_frame _).2.2.2.2
  · apply Stmt.run_rename_list_outside
    intro j hj
    have he := congrArg Fin.val hj
    fin_cases j <;> simp_all [weightScaleLists, Fin.ext_iff] <;> omega

theorem weightScale_modulus (st : State 80 26) :
    (weightScale.run st).1.lists 3 = st.lists 3 ∧
    (weightScale.run st).1.lists 7 = st.lists 7 := by
  have hr := BinaryLabelScale.scale.run_rename weightScaleRegs weightScaleLists
    weightScaleRegs_injective weightScaleLists_injective st
  have hf := BinaryLabelScale.scale_frame (st.restrict weightScaleRegs weightScaleLists)
  exact ⟨(congrArg (fun p : State 54 18 × ℕ => p.1.lists 3) hr).trans hf.2.2.1,
    (congrArg (fun p : State 54 18 × ℕ => p.1.lists 7) hr).trans hf.2.2.2.1⟩

theorem weightEncode_reg (st : State 80 26) (i : Fin 80)
    (hi : i ∉ [60, 71, 72, 73, 74, 75]) :
    (weightEncode.run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [List.mem_cons, not_or] at hi
  simp [weightEncode, label, homogeneous, decodeLabel, Stmt.regWrites, Stmt.regWrites_rename,
    homogeneousRegs, labelRegs, WordCodec.decode, WordCodec.body, WordCodec.setup,
    BooleanAffineList.homogeneous, hi]

theorem weightEncode_list (st : State 80 26) (i : Fin 26) (hi : i ≠ 18) :
    (weightEncode.run st).1.lists i = st.lists i := by
  apply run_lists_frame
  simpa [weightEncode, label, homogeneous, decodeLabel, Stmt.listWrites, Stmt.listWrites_rename,
    homogeneousLists, labelLists, WordCodec.decode, WordCodec.body, WordCodec.setup,
    BooleanAffineList.homogeneous, Equiv.swap_apply_def] using hi

theorem weightedLabel_reg (j : Fin 5) (st : State 80 26) (i : Fin 80)
    (hlo : 42 ≤ i.val) (hhi : i.val < 68) (hi : i ≠ 60) :
    ((weightedLabel j).run st).1.regs i = st.regs i := by
  have henc : i ∉ ([60, 71, 72, 73, 74, 75] : List (Fin 80)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *
  have h20 : i ≠ 20 := by intro h; subst i; norm_num at hlo
  have h24 : i ≠ 24 := by intro h; subst i; norm_num at hlo
  simp only [weightedLabel, run_seq_fst, weightEncode_reg _ i henc,
    weightScale_reg _ i hlo hhi, weightScalePrepare, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne h20, Function.update_of_ne h24]
  exact weightLabelLoad_reg j st i (by omega)

theorem weightedLabel_list (j : Fin 5) (st : State 80 26) (i : Fin 26)
    (hlo : 12 ≤ i.val) (hi : i ∉ [14, 15, 16, 18, 24, 25]) :
    ((weightedLabel j).run st).1.lists i = st.lists i := by
  have h18 : i ≠ 18 := fun h => hi (by simp [h])
  have hs : i ∉ ([14, 15, 16, 24, 25] : List (Fin 26)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    tauto
  simp only [weightedLabel, run_seq_fst, weightEncode_list _ i h18,
    weightScale_list _ i hlo hs, weightScalePrepare, run_assign_fst, Expr.eval, setReg_lists]
  exact weightLabelLoad_list j st i hlo

attribute [local irreducible] weightCall weightLabelLoad weightScale weightScalePrepare weightEncode

-- Keep the arithmetic programs opaque while checking the preserved context.
theorem weightedLabel_context (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (j : Fin 5)
    (st : State 80 26) (hc : PointContext ζ u v st) :
    PointContext ζ u v ((weightedLabel j).run st).1 := by
  have hload := weightLabelLoad_run ζ u v j st hc
  refine ⟨(weightedLabel_reg j st 43 (by decide) (by decide) (by decide)).trans hc.1,
    (weightedLabel_reg j st 44 (by decide) (by decide) (by decide)).trans hc.2.1,
    (weightedLabel_reg j st 45 (by decide) (by decide) (by decide)).trans hc.2.2.1,
    ?_, ?_,
    (weightedLabel_list j st 12 (by decide) (by decide)).trans hc.2.2.2.2.2.1,
    (weightedLabel_list j st 13 (by decide) (by decide)).trans hc.2.2.2.2.2.2⟩
  · simp only [weightedLabel, run_seq_fst, weightEncode_list _ 3 (by decide),
      (weightScale_modulus _).1, weightScalePrepare, run_assign_fst, Expr.eval, setReg_lists]
    exact hload.2.1.trans hc.2.2.2.1
  · simp only [weightedLabel, run_seq_fst, weightEncode_list _ 7 (by decide),
      (weightScale_modulus _).2, weightScalePrepare, run_assign_fst, Expr.eval, setReg_lists]
    exact hload.2.2.trans hc.2.2.2.2.1

end PCP.Lang.StandardCorrection
