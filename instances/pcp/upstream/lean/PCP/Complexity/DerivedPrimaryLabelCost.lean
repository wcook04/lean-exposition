import PCP.Complexity.DerivedPrimaryLabels
import PCP.Complexity.InterpolationBranchLabelCost

/-! # Polynomial charged cost of the two actual derived-primary coefficient labels -/

namespace PCP.Lang.DerivedPrimary

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode

variable {t : ℕ} [NeZero t]

attribute [local irreducible] homogeneous BooleanLabelConstructors.homogeneous
  BinaryCubicQueryLang.query affine translate maskQuery masked decode

theorem prepare_cost (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask : Coefficients t 3) (st : State 100 32) (hc : Context w v mask st) :
    (prepare.run st).2 ≤ 6*t+20 := by
  have hm : listSize (st.lists 22) ≤ 2*t := by
    rw [hc.modulus]; exact InterpolationBranch.coordinateBits_size _
  have hv : listSize (st.lists 20) ≤ 2*t := by
    rw [hc.word]; exact InterpolationBranch.coordinateBits_size _
  have ht := size_le_self t
  simp only [prepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setList_lists, Function.update,
    Fin.reduceEq, dite_false, hc.width, hc.empty, show listSize [] = 0 from rfl]
  norm_num
  omega

theorem affine_cost (w : BinaryMaterializedField.Element t) (v : Fin t → ZMod 2)
    (mask : Coefficients t 3) (st : State 100 32) (hc : Context w v mask st) :
    (affine.run st).2 ≤ (BooleanLabelTransform.queryConstant+300)*(2^t+7)^8 := by
  have hp := BooleanLabelConstructors.homogeneous_cost (r := 1) v
    ((prepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.width])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.empty])
    (by simp [prepare, Stmt.run, Expr.eval, Function.update, State.restrict, hc.word])
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    BooleanLabelConstructors.homogeneous (prepare.run st).1)] at hp
  have hpc : (homogeneous.run (prepare.run st).1).2 ≤
      (BooleanLabelTransform.queryConstant+200)*(2^t+Nat.size 1+5)^8 := by
    simpa only [homogeneous, Prod.snd] using hp
  have hp' := hpc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by norm_num) 8 : (2^t+Nat.size 1+5)^8 ≤ (2^t+7)^8))
  have hprep := prepare_cost w v mask st hc
  have hpow : 2^t+7 ≤ (2^t+7)^8 := Nat.le_pow (by decide)
  have ht : t < 2^t := Nat.lt_two_pow_self
  rw [affine, run_seq_snd]
  nlinarith only [hp', hprep, hpow, ht]

theorem translatePrepare_cost (w : BinaryMaterializedField.Element t) (L : Coefficients t 1)
    (st : State 100 32) (ht : st.regs 98 = t) (hw : st.regs 99 = (fieldEquiv t w).val)
    (hm : st.lists 22 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 23 = []) (hL : st.lists 5 = encode L) :
    (translatePrepare.run st).2 ≤ 6*t+2*2^t+20 := by
  have hm' : listSize (st.lists 22) ≤ 2*t := by
    rw [hm]; exact InterpolationBranch.coordinateBits_size _
  have hL' : listSize (st.lists 5) ≤ 2*2^t := by rw [hL]; exact HadamardLabel.encode_size _
  have hw' : Nat.size (fieldEquiv t w).val ≤ t := Nat.size_le.mpr (fieldEquiv t w).isLt
  have ht' := size_le_self t
  simp only [translatePrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setList_lists, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, ht, hw, he, show listSize [] = 0 from rfl]
  omega

theorem translate_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 100 32) (ht : st.regs 98 = t)
    (hw : st.regs 99 = (fieldEquiv t w).val)
    (hm : st.lists 22 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 23 = []) (hL : st.lists 5 = encode L) :
    ((translate weighted).run st).2 ≤ (BinaryCubicQueryLang.queryConstant+100)*(2^t+7)^8 := by
  have hp := BinaryCubicQueryLang.query_cost weighted w L
    ((translatePrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using ht)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hw)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hm)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
    (by simpa [translatePrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hL)
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    (BinaryCubicQueryLang.query weighted) (translatePrepare.run st).1)] at hp
  have hp' := hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by omega : 2^t+5 ≤ 2^t+7) 8))
  have hprep := translatePrepare_cost w L st ht hw hm he hL
  have hpow : 2^t+7 ≤ (2^t+7)^8 := Nat.le_pow (by decide)
  have htt : t < 2^t := Nat.lt_two_pow_self
  rw [translate, run_seq_snd]
  change _ + ((call (by decide) (by decide) (BinaryCubicQueryLang.query weighted)).run
    (translatePrepare.run st).1).2 + 1 ≤ _
  nlinarith only [hp', hprep, hpow, htt]

omit [NeZero t] in
theorem maskQuery_cost (p mask : Coefficients t 3) (st : State 100 32)
    (hp : st.lists 5 = encode p) (hm : st.lists 21 = encode mask) (he : st.lists 7 = []) :
    (maskQuery.run st).2 ≤ 100*(2^t+7)^8 := by
  have ha := BooleanLabelAddition.add_cost p mask
    ((maskPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using hp)
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using hm)
    (by simpa [maskPrepare, Stmt.run, Function.update, State.restrict] using he)
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    BooleanLabelAddition.add (maskPrepare.run st).1)] at ha
  have hd := BooleanCoefficientTransform.masks_length_le t 3
  rw [BooleanMask.masks_length] at hd
  have hp2 : (BooleanCoefficientIndex.dimension t 3+1)^2 ≤ (2^t+7)^8 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have ha' := ha.trans (Nat.mul_le_mul_left 60 hp2)
  have hs1 : listSize (st.lists 5) ≤ 2*2^t := by rw [hp]; exact HadamardLabel.encode_size _
  have hs2 : listSize (st.lists 21) ≤ 2*2^t := by rw [hm]; exact HadamardLabel.encode_size _
  have hprep : (maskPrepare.run st).2 = listSize (st.lists 5)+listSize (st.lists 21)+3 := by
    simp [maskPrepare, Stmt.run, Function.update, Nat.add_assoc]
    omega
  have hpow : 2^t+7 ≤ (2^t+7)^8 := Nat.le_pow (by decide)
  rw [maskQuery, run_seq_snd, hprep]
  nlinarith only [ha', hs1, hs2, hpow]

omit [NeZero t] in
theorem decode_cost {r : ℕ} (p : Coefficients t r) (st : State 100 32)
    (hp : st.lists 0 = encode p) :
    (decode.run st).2 ≤ (WordCodec.passConstant*3+20)*(2^t+1)^2 := by
  have hc := WordCodec.decode_cost
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by change BinaryField.Bits (st.lists 0); rw [hp]; exact encode_bits p)
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) WordCodec.decode st)] at hc
  have hd := BooleanCoefficientTransform.masks_length_le t r
  rw [BooleanMask.masks_length] at hd
  have h : (decode.run st).2 ≤ (WordCodec.passConstant*3+20)*
      (BooleanCoefficientIndex.dimension t r+1)^2 := by
    simpa only [decode, Prod.snd, State.restrict_lists,
      show Fin.castLE (by decide : 1 ≤ 32) (0 : Fin 1) = (0 : Fin 32) from rfl,
      hp, encode_length] using hc
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

omit [NeZero t] in
theorem loadCode_cost {r : ℕ} (src : Fin 32) (dst : Fin 100)
    (p : Coefficients t r) (st : State 100 32) (hp : st.lists src = encode p) :
    ((loadCode src dst).run st).2 ≤ (WordCodec.passConstant*3+40)*(2^t+1)^2 := by
  have hc := decode_cost p (setList st 0 (st.lists src)) (by simpa using hp)
  have ho := decode_run p (setList st 0 (st.lists src)) (by simpa using hp)
  have hs : listSize (st.lists src) ≤ 2*2^t := by rw [hp]; exact HadamardLabel.encode_size _
  have hb := HadamardLabel.code_size p
  simp only [loadCode, Stmt.run,
    Expr.cost, Expr.readSize, Expr.eval, ho]
  nlinarith only [hc, hs, hb, Nat.zero_le ((2^t)^2)]

omit [NeZero t] in
theorem serialize_cost (p mask : Coefficients t 3) (st : State 100 32)
    (hp : st.lists 1 = encode p) (hm : st.lists 21 = encode mask) (he : st.lists 23 = []) :
    (serialize.run st).2 ≤ (WordCodec.passConstant*6+100)*(2^t+7)^8 := by
  have hc1 := loadCode_cost 1 96 p st hp
  have h1 := loadCode_run 1 96 p st hp
  have hm1 := (run_lists_frame (loadCode 1 96) 21 
    
    (by unfold loadCode decode call; decide) st).trans hm
  have he1 := (run_lists_frame (loadCode 1 96) 23 
    
    (by unfold loadCode decode call; decide) st).trans he
  generalize hs : ((loadCode 1 96).run st).1 = s at *
  have hc2 := loadCode_cost 21 97 mask s hm1
  have h2 := loadCode_run 21 97 mask s hm1
  have h1' := (run_regs_frame (loadCode 21 97) 96 
    (by unfold loadCode decode call; decide) s).trans h1
  have he2 := (run_lists_frame (loadCode 21 97) 23 
    (by unfold loadCode decode call; decide) s).trans he1
  have hpb := HadamardLabel.code_size p
  have hmb := HadamardLabel.code_size mask
  have hpow : (2^t+1)^2 ≤ (2^t+7)^8 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hp1 := hc1.trans (Nat.mul_le_mul_left _ hpow)
  have hp2 := hc2.trans (Nat.mul_le_mul_left _ hpow)
  have hlo : 2^t+7 ≤ (2^t+7)^8 := Nat.le_pow (by decide)
  simp only [serialize, run_seq_snd, hs]
  generalize hu : ((loadCode 21 97).run s).1 = u at *
  simp only [run_copy_snd, run_copy_fst, run_push_snd, run_push_fst,
    setList_regs, h1', h2, he2, show listSize [] = 0 from rfl]
  nlinarith only [hp1, hp2, hpb, hmb, hlo]

def labelsConstant : ℕ := BooleanLabelTransform.queryConstant +
  BinaryCubicQueryLang.queryConstant + WordCodec.passConstant*6 + 1000

private theorem assemble_cost (p₁ p₂ p₃ p₄ : Stmt 100 32)
    (P₀ P₁ P₂ P₃ : State 100 32 → Prop) (A B C D : ℕ)
    (h₁ : ∀ st, P₀ st → P₁ (p₁.run st).1 ∧ (p₁.run st).2 ≤ A)
    (h₂ : ∀ st, P₁ st → P₂ (p₂.run st).1 ∧ (p₂.run st).2 ≤ B)
    (h₃ : ∀ st, P₂ st → P₃ (p₃.run st).1 ∧ (p₃.run st).2 ≤ C)
    (h₄ : ∀ st, P₃ st → (p₄.run st).2 ≤ D)
    (st : State 100 32) (h : P₀ st) :
    ((Stmt.seq (.seq p₁ (.seq p₂ p₃)) p₄).run st).2 ≤ A+B+C+D+3 := by
  have hA := h₁ st h
  have hB := h₂ (p₁.run st).1 hA.1
  have hC := h₃ (p₂.run (p₁.run st).1).1 hB.1
  have hD := h₄ (p₃.run (p₂.run (p₁.run st).1).1).1 hC.1
  simp only [run_seq_snd, run_seq_fst]
  omega

theorem labels_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (v : Fin t → ZMod 2) (mask : Coefficients t 3) (st : State 100 32)
    (hc : Context w v mask st) :
    ((labels weighted).run st).2 ≤ labelsConstant*(2^t+7)^8 := by
  let L := BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) v
  let p := BinaryCubicQueryLang.translated weighted w L
  let N := (2^t+7)^8
  have h := assemble_cost affine (translate weighted) maskQuery serialize
    (Context w v mask)
    (fun st => Context w v mask st ∧ st.lists 5 = encode L)
    (fun st => Context w v mask st ∧ st.lists 5 = encode p ∧ st.lists 7 = [])
    (fun st => Context w v mask st ∧ st.lists 1 = encode (p+mask))
    ((BooleanLabelTransform.queryConstant+300)*N)
    ((BinaryCubicQueryLang.queryConstant+100)*N) (100*N)
    ((WordCodec.passConstant*6+100)*N)
    (fun st hc => by
      have h := affine_run w v mask st hc
      exact ⟨⟨hc.of_frame h.2, h.1⟩, affine_cost w v mask st hc⟩)
    (fun st hc => by
      have h := translate_run weighted w L st hc.1.width hc.1.weight
        hc.1.modulus hc.1.empty hc.2
      exact ⟨⟨hc.1.of_frame h.2.2, h.1, h.2.1⟩,
        translate_cost weighted w L st hc.1.width hc.1.weight
          hc.1.modulus hc.1.empty hc.2⟩)
    (fun st hc => by
      have h := maskQuery_run p mask st hc.2.1 hc.1.mask hc.2.2
      exact ⟨⟨hc.1.of_frame h.2, h.1⟩, maskQuery_cost p mask st hc.2.1 hc.1.mask hc.2.2⟩)
    (fun st hc => serialize_cost (p+mask) mask st hc.2 hc.1.mask hc.1.empty) st hc
  have hlo : 1 ≤ N := Nat.one_le_pow _ _ (Nat.succ_pos (2^t+6))
  rw [labels, masked]
  change _ ≤ labelsConstant*N
  unfold labelsConstant
  nlinarith only [h, hlo]

end PCP.Lang.DerivedPrimary
