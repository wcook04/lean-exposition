import PCP.Complexity.GridEdgeLang

/-!
# Charged cost of one public edge interpolation pass
-/

namespace PCP.Lang.GridEdge

open PCP.Algebraic BinaryFieldCode

variable {t h n : ℕ} [NeZero t]

omit [NeZero t] in
theorem add_result (st : State 70 20) :
    (((add.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))),
      (add.run st).2) = (binary .add).run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) :=
  (binary .add).run_rename _ _ (Fin.castLE_injective _) (Fin.castLE_injective _) st

theorem addCall_cost (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (a b : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (ha : st.regs 50 = (fieldEquiv t a).val)
    (hb : st.regs 40 = (fieldEquiv t b).val) :
    (addCall.run st).2 ≤ 21000000 * (t + 1) ^ 4 := by
  let s := setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 50)) 25 (st.regs 40)
  have hr := add_result s
  have hp := binary_cost .add (Nat.pos_of_ne_zero (NeZero.ne t))
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (fieldEquiv t a) (fieldEquiv t b)
    (by simpa [s, Function.update] using hc.1)
    (by simpa [s, Function.update] using ha)
    (by simpa [s] using hb) hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1
  rw [← congrArg Prod.snd hr] at hp
  have hout := binary_run_field .add
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) a b
    (by simpa [s, Function.update] using hc.1)
    (by simpa [s, Function.update] using ha)
    (by simpa [s] using hb) hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1
  have ho := (congrArg (fun p : State 36 11 × ℕ => p.1.regs 26) hr).trans hout
  simp only [State.restrict_regs,
    show Fin.castLE (by decide : 36 ≤ 70) (26 : Fin 36) = (26 : Fin 70) from rfl,
    Op.fieldEval] at ho
  have hsa : Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt
  have hsb : Nat.size (fieldEquiv t b).val ≤ t := Nat.size_le.mpr (fieldEquiv t b).isLt
  have hso : Nat.size (fieldEquiv t (a + b)).val ≤ t := Nat.size_le.mpr (fieldEquiv t (a+b)).isLt
  have hst := size_le_self t
  have hlin : t + 1 ≤ (t + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)
  simp only [addCall, run_seq_snd, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false]
  dsimp only [s] at hp ho
  generalize hu : add.run
    (setReg (setReg (setReg st 20 (st.regs 44)) 24 (st.regs 50)) 25 (st.regs 40)) = u at *
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_false, hc.1, ha, hb, ho]
  omega

theorem tensor_cost (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (j : Fin (h ^ (n + n))) (st : State 70 20) (hc : Context t h n x z st)
    (hj : st.lists 13 = List.ofFn
      (fun i : Fin (n + n) => ((finFunctionFinEquiv.symm j) i).val)) :
    (tensor.run st).2 ≤ 200000000 * (n + n + h + t + 1) ^ 6 := by
  rw [tensor, Stmt.run_rename_cost _ _ _ (Fin.castLE_injective _) (Fin.castLE_injective _)]
  have hp := GridTensor.program_cost (GridTensor.coordinates hh (gridPoint hh j) z) hh
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    ⟨hc.1, hc.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1⟩
    (by simpa [GridTensor.pointCodes, GridTensor.coordinates, Function.comp_def] using
      hc.2.2.2.2.2.2.2.2.2.1)
    (by
      simp only [GridTensor.nodeCodes, GridTensor.coordinates, List.map_ofFn,
        Function.comp_def, gridPoint_codes]
      exact hj)
  simpa only [GridTensor.coordinates, List.length_ofFn] using hp

theorem digitCall_cost (x : List Bool) (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (st : State 70 20) (hc : Context t h n x z st) (W : ℕ)
    (hd : n + n ≤ W) (hb : h ≤ W) (hj : st.regs 51 ≤ W) :
    (digitCall.run st).2 ≤ (81 * (MixedRadixDecode.passConstant + 20) + 20) * (W + 1) ^ 4 := by
  let s := setList (setList
    (setReg (setReg (setReg st 64 (st.regs 51)) 65 (st.regs 54)) 66 (st.regs 45))
    17 (st.lists 7)) 13 (st.lists 7)
  have he := hc.2.2.2.2.2.2.2.2.1
  have hcost := UniformRadix.program_cost (s.restrict digitRegs digitLists)
    (by simpa [s, digitLists, Function.update] using he)
    (by simpa [s, digitLists, Function.update] using he)
  rw [← Stmt.run_rename_cost UniformRadix.program digitRegs digitLists
    digitRegs_injective digitLists_injective s] at hcost
  change (digits.run s).2 ≤ _ at hcost
  have hs0 : (s.restrict digitRegs digitLists).regs 0 = st.regs 51 := by
    simp [s, digitRegs, Function.update]
  have hs1 : (s.restrict digitRegs digitLists).regs 1 = n + n := by
    simpa [s, digitRegs, Function.update] using hc.2.2.2.2.1
  have hs2 : (s.restrict digitRegs digitLists).regs 2 = h := by
    simpa [s, digitRegs, Function.update] using hc.2.1
  rw [hs0, hs1, hs2] at hcost
  have hsj := (size_le_self (st.regs 51)).trans hj
  have hsh := (size_le_self h).trans hb
  have hsd := (size_le_self (n+n)).trans hd
  have hpow : (n + n + Nat.size h + Nat.size (st.regs 51) + 2) ^ 4 ≤
      81 * (W + 1) ^ 4 := by
    calc
      _ ≤ (3 * (W + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = _ := by ring
  have hcost' := hcost.trans (Nat.mul_le_mul_left _ hpow)
  have hlin : W + 1 ≤ (W + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ W + 1) (by decide : 1 ≤ 4)
  simp only [digitCall, run_seq_snd, run_assign_fst, run_copy_snd, run_copy_fst, Expr.eval]
  change (Expr.var 51).cost st.regs + ((Expr.var 54).cost _ +
    ((Expr.var 45).cost _ + (listSize (st.lists 7) + 1 +
      (listSize (st.lists 7) + 1 + (digits.run s).2 + 1) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.2.2.2.2.1, hc.2.1, he, listSize, List.map_nil, List.sum_nil]
  nlinarith

/-- The arithmetic graph lookup has one fixed uniform polynomial cost. -/
theorem reader_cost : ∃ C : ℕ, ∀ (st : State 70 20) (W : ℕ),
    (∀ i ∈ [51, 53, 55], Nat.size (st.regs i) ≤ W) → listSize (st.lists 16) ≤ W →
      (reader.run st).2 ≤ C * (W + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := GraphAdjacency.program_cost
  refine ⟨C, ?_⟩
  intro st W hregs hl
  rw [reader, Stmt.run_rename_cost _ _ _ readerRegs_injective readerLists_injective]
  apply hC _ W
  · intro i
    fin_cases i <;> exact hregs _ (by simp [readerRegs])
  · exact hl

/-- One conditional update has a field-width polynomial cost. -/
theorem accumulate_cost (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t)
    (a b : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (ha : st.regs 50 = (fieldEquiv t a).val)
    (hb : st.regs 40 = (fieldEquiv t b).val) (hf : st.regs 57 ≤ 1) :
    (accumulate.run st).2 ≤ 21000000 * (t + 1) ^ 4 + 3 := by
  have hs := (size_le_self (st.regs 57)).trans hf
  have hp := addCall_cost x z a b st hc ha hb
  by_cases hz : st.regs 57 ≠ 0
  · simp only [accumulate, Stmt.run, ite_eq_left hz]
    omega
  · simp only [accumulate, Stmt.run, ite_eq_right hz]
    omega

/-- All source magnitudes used by one pass are bounded; scratch registers are unrestricted. -/
def Budget (t h n : ℕ) (x : List Bool) (W : ℕ) : Prop :=
  t ≤ W ∧ h ≤ W ∧ n + n ≤ W ∧ h ^ (n+n) ≤ W ∧ h ^ n ≤ W ∧
    ThreeColorEncoding.vertexCount x ≤ W ∧ listSize (x.map Bool.toNat) ≤ W

set_option maxHeartbeats 800000 in
-- Four renamed arithmetic traces and their source bounds are combined in one theorem.
/-- The complete arithmetic pass has a fixed degree-six charged bound. -/
theorem kernel_cost_of_reader_bound (C : ℕ)
    (hC : ∀ (st : State 70 20) (W : ℕ),
      (∀ i ∈ [51, 53, 55], Nat.size (st.regs i) ≤ W) → listSize (st.lists 16) ≤ W →
        (reader.run st).2 ≤ C * (W + 1) ^ 2)
    (hh : h ≤ 2 ^ t) (x : List Bool)
    (z : Fin (n + n) → BinaryMaterializedField.Element t) (j : Fin (h ^ (n + n)))
    (a : BinaryMaterializedField.Element t) (st : State 70 20)
    (hc : Context t h n x z st) (hj : st.regs 51 = j.val)
    (ha : st.regs 50 = (fieldEquiv t a).val) (W : ℕ) (hw : Budget t h n x W) :
    (kernel.run st).2 ≤
      (C + 81 * (MixedRadixDecode.passConstant + 20) + 145822000030) * (W + 1) ^ 6 := by
  have hsj : st.regs 51 ≤ W := by rw [hj]; exact j.isLt.le.trans hw.2.2.2.1
  have hr := hC st W (by
    intro i hi
    rcases (by simpa using hi : i = 51 ∨ i = 53 ∨ i = 55) with rfl | rfl | rfl
    · exact (size_le_self _).trans hsj
    · rw [hc.2.2.2.1]; exact (size_le_self _).trans hw.2.2.2.2.2.1
    · rw [hc.2.2.2.2.2.1]; exact (size_le_self _).trans hw.2.2.2.2.1)
    (by rw [hc.2.2.2.2.2.2.2.2.2.2]; exact hw.2.2.2.2.2.2)
  have hsc := context_readOnly reader_readOnly x z st hc
  have hsj' := (reader_counter st).trans hj
  have hs50 := run_regs_frame reader 50
    (by unfold reader GraphAdjacency.program GraphAdjacency.code; decide) st
  have hflag := reader_run x z st hc
  simp only [kernel, run_seq_snd]
  generalize hs : (reader.run st).1 = s at *
  have hdc := digitCall_cost x z s hsc W hw.2.2.1 hw.2.1
    (by rw [hsj']; exact j.isLt.le.trans hw.2.2.2.1)
  have huc := context_readOnly digitCall_readOnly x z s hsc
  have hnodes := digitCall_run x z j s hsc hsj'
  have hu50 := run_regs_frame digitCall 50 (by decide) s
  have hu57 := run_regs_frame digitCall 57 (by decide) s
  generalize hu : (digitCall.run s).1 = u at *
  have htc := tensor_cost hh x z j u huc hnodes
  have hvc := context_readOnly tensor_readOnly x z u huc
  have hvalue := tensor_run hh x z j u huc hnodes
  have hv50 := run_regs_frame tensor 50 (by decide) u
  have hv57 := run_regs_frame tensor 57 (by decide) u
  generalize hv : (tensor.run u).1 = v at *
  have hacc : v.regs 50 = (fieldEquiv t a).val := hv50.trans (hu50.trans (hs50.trans ha))
  have hf : v.regs 57 ≤ 1 := by
    rw [hv57, hu57, hflag]
    split <;> omega
  have hac := accumulate_cost x z a _ v hvc hacc hvalue hf
  have h24 : (W + 1) ^ 2 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h46 : (W + 1) ^ 4 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (W + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have ht4 : (t + 1) ^ 4 ≤ (W + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by have := hw.1; omega) 4).trans h46
  have htp : (n + n + h + t + 1) ^ 6 ≤ 729 * (W + 1) ^ 6 := by
    calc
      _ ≤ (3 * (W + 1)) ^ 6 := Nat.pow_le_pow_left
        (by have := hw.1; have := hw.2.1; have := hw.2.2.1; omega) 6
      _ = _ := by ring
  have hr' := hr.trans (Nat.mul_le_mul_left C h24)
  have hd' := hdc.trans (Nat.mul_le_mul_left _ h46)
  have ht' := htc.trans (Nat.mul_le_mul_left 200000000 htp)
  have ha' := hac.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 21000000 ht4) 3)
  nlinarith only [hr', hd', ht', ha', hpos]

end PCP.Lang.GridEdge
