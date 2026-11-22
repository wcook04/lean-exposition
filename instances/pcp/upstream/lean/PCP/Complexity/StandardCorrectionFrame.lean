import PCP.Complexity.StandardCorrectionPointLang

/-!
# Preserved inputs of the standard correction point routine
-/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode

variable {t d : ℕ} [NeZero t]

theorem powerCall_reg (st : State 80 26) (i : Fin 80) (hi : 42 ≤ i.val) :
    (powerCall.run st).1.regs i = st.regs i := by
  have h20 : i ≠ 20 := by intro he; subst i; norm_num at hi
  have h24 : i ≠ 24 := by intro he; subst i; norm_num at hi
  have h36 : i ≠ 36 := by intro he; subst i; norm_num at hi
  have h37 : i ≠ 37 := by intro he; subst i; norm_num at hi
  simp only [powerCall, run_seq_fst, run_assign_fst, Expr.eval]
  rw [power_reg_outside _ i hi]
  simp [Function.update, h20, h24, h36, h37]

theorem affine_reg_outside (st : State 80 26) (i : Fin 80) (hi : 41 ≤ i.val) :
    (affine.run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have he := congrArg Fin.val hj
  simp only [Fin.val_castLE] at he
  omega

theorem affine_list_outside (st : State 80 26) (i : Fin 26) (hi : 17 ≤ i.val) :
    (affine.run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  have he := congrArg Fin.val hj
  simp only [Fin.val_castLE] at he
  omega

theorem affineCall_reg (st : State 80 26) (i : Fin 80) (hi : 41 ≤ i.val) :
    (affineCall.run st).1.regs i = st.regs i := by
  have h2 : i ≠ 2 := by intro he; subst i; norm_num at hi
  have h23 : i ≠ 23 := by intro he; subst i; norm_num at hi
  simp only [affineCall, run_seq_fst, run_assign_fst, Expr.eval]
  rw [affine_reg_outside _ i hi]
  simp [Function.update, h2, h23]

theorem radix_reg (st : State 80 26) (i : Fin 80)
    (hi : i ∉ [59, 64, 65, 66, 67]) : (radix.run st).1.regs i = st.regs i := by
  by_cases h45 : i = 45
  · subst i
    have hr := RadixCodec.encode.run_rename radixRegs radixLists radixRegs_injective
      (Function.injective_of_subsingleton _) st
    exact (congrArg (fun p : State 6 1 × ℕ => p.1.regs 0) hr).trans
      (RadixCodec.encode_run (st.restrict radixRegs radixLists)).1
  · apply Stmt.run_rename_reg_outside
    intro j hj
    fin_cases j <;> simp_all [radixRegs]

theorem point_reg (st : State 80 26) (i : Fin 80) (hi : 42 ≤ i.val)
    (hj : i ∉ [59, 64, 65, 66, 67]) : (point.run st).1.regs i = st.regs i := by
  rw [point, run_seq_fst, run_seq_fst, radix_reg _ i hj,
    affineCall_reg _ i (by omega), powerCall_reg _ i hi]

theorem scalarPoint_reg (st : State 80 26) (i : Fin 80) (hi : 41 ≤ i.val)
    (hj : i ∉ [59, 64, 65, 66, 67]) : (scalarPoint.run st).1.regs i = st.regs i := by
  rw [scalarPoint, run_seq_fst, radix_reg _ i hj, affineCall_reg _ i hi]

theorem radix_list (st : State 80 26) (i : Fin 26) (hi : i ≠ 16) :
    (radix.run st).1.lists i = st.lists i := by
  apply Stmt.run_rename_list_outside
  intro j hj
  exact hi hj.symm

theorem point_lists_outside (st : State 80 26) (i : Fin 26) (hi : 17 ≤ i.val) :
    (point.run st).1.lists i = st.lists i := by
  have hi16 : i ≠ 16 := by intro he; subst i; norm_num at hi
  rw [point, run_seq_fst, run_seq_fst,
    radix_list _ i hi16]
  simp only [affineCall, run_seq_fst, run_assign_fst, Expr.eval]
  rw [affine_list_outside _ i hi]
  simp only [setReg_lists, powerCall, run_seq_fst, run_assign_fst, Expr.eval]
  rw [power_list_outside _ i (by omega)]
  rfl

theorem scalarPoint_lists_outside (st : State 80 26) (i : Fin 26) (hi : 17 ≤ i.val) :
    (scalarPoint.run st).1.lists i = st.lists i := by
  have hi16 : i ≠ 16 := by intro he; subst i; norm_num at hi
  rw [scalarPoint, run_seq_fst,
    radix_list _ i hi16]
  simp only [affineCall, run_seq_fst, run_assign_fst, Expr.eval]
  rw [affine_list_outside _ i hi]
  rfl

theorem affineCall_context_core (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    AffineContext u v (affineCall.run st).1 := by
  let s := setReg (setReg st 2 (st.regs 26)) 23 (st.regs 43)
  have hr := affine_result s
  have hp := AffineVector.program_run a (List.ofFn (fun i => (u i, v i)))
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨by simpa [s, Function.update] using ha,
      by simpa [s] using hc.1, hc.2.2.1, hc.2.2.2.1⟩
    (by simpa [s, AffineVector.leftCodes, Function.comp_def] using hc.2.2.2.2.1)
    (by simpa [s, AffineVector.rightCodes, Function.comp_def] using hc.2.2.2.2.2)
  rw [← hr] at hp
  have hm : (affineCall.run st).1.lists 3 =
      BinaryField.encode (BinaryWordMaterialization.modulus t) := hp.2.1.2.2.1
  have he : (affineCall.run st).1.lists 7 = [] := hp.2.1.2.2.2
  have hu : (affineCall.run st).1.lists 12 = st.lists 12 := hp.2.2.1
  have hv : (affineCall.run st).1.lists 13 = st.lists 13 := hp.2.2.2
  exact ⟨(affineCall_reg st 43 (by decide)).trans hc.1,
    (affineCall_reg st 45 (by decide)).trans hc.2.1, hm, he,
    hu.trans hc.2.2.2.2.1, hv.trans hc.2.2.2.2.2⟩

theorem radix_context (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st) :
    AffineContext u v (radix.run st).1 := by
  exact ⟨(radix_reg st 43 (by decide)).trans hc.1,
    (radix_reg st 45 (by decide)).trans hc.2.1,
    (radix_list st 3 (by decide)).trans hc.2.2.1,
    (radix_list st 7 (by decide)).trans hc.2.2.2.1,
    (radix_list st 12 (by decide)).trans hc.2.2.2.2.1,
    (radix_list st 13 (by decide)).trans hc.2.2.2.2.2⟩

theorem scalarPoint_context (a : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t)
    (st : State 80 26) (hc : AffineContext u v st)
    (ha : st.regs 26 = (fieldEquiv t a).val) :
    AffineContext u v (scalarPoint.run st).1 :=
  radix_context u v _ (affineCall_context_core a u v st hc ha)

theorem point_context (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (k : ℕ) (hk : k ≤ 5)
    (st : State 80 26) (hc : PointContext ζ u v st) (he : st.regs 46 = k) :
    PointContext ζ u v (point.run st).1 := by
  have hp := powerCall_context ζ u v st hc
  have hs : AffineContext u v (powerCall.run st).1 :=
    ⟨hp.1, hp.2.2.1, hp.2.2.2⟩
  have hf := scalarPoint_context (ζ^k) u v (powerCall.run st).1 hs
    (powerCall_run ζ u v k hk st hc he)
  exact ⟨hf.1, (point_reg st 44 (by decide) (by decide)).trans hc.2.1,
    hf.2.1, hf.2.2⟩

end PCP.Lang.StandardCorrection
