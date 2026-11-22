import PCP.Complexity.StandardCorrectionWeight

/-! # Charged cost of the generator constraint's weighted correction labels -/

namespace PCP.Lang.StandardCorrection

open PCP.Algebraic BinaryFieldCode FieldExpression BinaryPolynomialSpace

variable {t d : ℕ} [NeZero t]

attribute [local irreducible] weightCall weightLabelLoad weightScale weightScalePrepare
  weightEncode weightedLabel

def weightTermBound : ℕ := ∑ i : Fin 5, ((generatorWeightTerm 4 i).weight + 12)

def weightConstant : ℕ := weightTermBound + BinaryLabelScale.kernelConstant +
  WordCodec.passConstant * 3 + 700100

theorem weightLabelLoad_cost (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (i : Fin 5)
    (st : State 80 26) (hc : PointContext ζ u v st) :
    ((weightLabelLoad i).run st).2 ≤ weightTermBound * (t+1)^4 := by
  let s := setReg (setReg st 0 (st.regs 44)) 21 (st.regs 43)
  have hv : View t (fun _ : Fin 1 => ζ)
      (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    refine ⟨?_, ?_, hc.2.2.2.1, hc.2.2.2.2.1⟩
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa [s, Function.update] using hc.2.1
    · simpa [s, Function.update, slot] using hc.1
  have hp := generatorWeight_cost ζ i _ hv
  rw [← congrArg Prod.snd (weightCall_result i s)] at hp
  have hi : (generatorWeightTerm 4 i).weight + 12 ≤ weightTermBound := by
    unfold weightTermBound
    exact Finset.single_le_sum (f := fun j : Fin 5 => (generatorWeightTerm 4 j).weight + 12)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hζ : Nat.size (st.regs 44) ≤ t := by rw [hc.2.1]; exact Nat.size_le.mpr (Fin.isLt _)
  have ht : Nat.size (st.regs 43) ≤ t := by rw [hc.1]; exact size_le_self t
  have hlow : t+1 ≤ (t+1)^4 := Nat.le_pow (by decide)
  have hmul := Nat.mul_le_mul_right ((t+1)^4) hi
  simp only [weightLabelLoad, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 44).cost st.regs +
    ((Expr.var 43).cost (setReg st 0 (st.regs 44)).regs + ((weightCall i).run s).2+1)+1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs,
    Function.update_of_ne (by decide : (43 : Fin 80) ≠ 0)]
  dsimp only [Prod.snd] at hp
  nlinarith only [hp, hζ, ht, hlow, hmul]

theorem weightedLabel_cost (ζ : BinaryMaterializedField.Element t)
    (u v : Fin d → BinaryMaterializedField.Element t) (i : Fin 5) (w : Fin t → ZMod 2)
    (st : State 80 26) (hc : PointContext ζ u v st)
    (hw : st.lists 17 = List.ofFn fun j => (w j).val) :
    ((weightedLabel i).run st).2 ≤ weightConstant * (2^t+4)^7 := by
  have hload := weightLabelLoad_run ζ u v i st hc
  have hloadc := weightLabelLoad_cost ζ u v i st hc
  have ht := (weightLabelLoad_reg i st 43 (by decide)).trans hc.1
  have hw' := (weightLabelLoad_list i st 17 (by decide)).trans hw
  generalize hs : ((weightLabelLoad i).run st).1 = s at *
  let a := FieldQueryArithmetic.interpolationWeight (GeneratorLowDegreeTest.nodes 4 ζ) 0 i
  have ha : s.regs 27 = (fieldEquiv t a).val := hload.1
  let b := (weightScalePrepare.run s).1
  have hb20 : b.regs 20 = t := by simp [b, weightScalePrepare, Stmt.run, Expr.eval, ht]
  have hb24 : b.regs 24 = (fieldEquiv t a).val := by
    simp [b, weightScalePrepare, Stmt.run, Expr.eval, Function.update, ha]
  have hb3 : b.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) := by
    simpa [b, weightScalePrepare, Stmt.run] using hload.2.1.trans hc.2.2.2.1
  have hb7 : b.lists 7 = [] := by
    simpa [b, weightScalePrepare, Stmt.run] using hload.2.2.trans hc.2.2.2.2.1
  have hb17 : b.lists 17 = List.ofFn fun j => (w j).val := by
    simpa [b, weightScalePrepare, Stmt.run] using hw'
  have hscale := BinaryLabelScale.scale_cost a w (b.restrict weightScaleRegs weightScaleLists)
    hb20 hb24 hb3 hb7 hb17
  rw [← Stmt.run_rename_cost _ _ _ weightScaleRegs_injective weightScaleLists_injective b]
    at hscale
  rw [← weightScale] at hscale
  have hout := weightScale_run a w b hb20 hb24 hb3 hb7 hb17
  have henc := label_cost (FieldQueryArithmetic.scaleLabel (BinaryMaterializedField.coordinates t) a w)
    ((weightScale.run b).1.restrict id (Equiv.swap 16 17)) hout
  rw [← Stmt.run_rename_cost _ _ _ Function.injective_id (Equiv.swap 16 17).injective
    (weightScale.run b).1] at henc
  rw [← weightEncode] at henc
  have haSize : Nat.size (s.regs 27) ≤ t := by rw [ha]; exact Nat.size_le.mpr (Fin.isLt _)
  have htSize : Nat.size (s.regs 43) ≤ t := by rw [ht]; exact size_le_self t
  have hprep : (weightScalePrepare.run s).2 ≤ 4*t+3 := by
    simp only [weightScalePrepare, Stmt.run, Expr.cost, Expr.readSize,
      Expr.eval, setReg_regs, Function.update_of_ne (by decide : (43 : Fin 80) ≠ 24)]
    omega
  let Q := 2^t+4
  have htq : t+2 ≤ Q := by dsimp [Q]; have := Nat.lt_two_pow_self (n := t); omega
  have h4 : (t+1)^4 ≤ Q^7 := (Nat.pow_le_pow_left (by omega) 4).trans
    (Nat.pow_le_pow_right (by dsimp [Q]; omega) (by decide))
  have h2 : (t+2)^2 ≤ Q^7 := (Nat.pow_le_pow_left htq 2).trans
    (Nat.pow_le_pow_right (by dsimp [Q]; omega) (by decide))
  have hlow : t+2 ≤ Q^7 := htq.trans (Nat.le_pow (by decide))
  have hload' := hloadc.trans (Nat.mul_le_mul_left _ h4)
  have henc' := henc.trans (Nat.mul_le_mul_left _ h2)
  simp only [weightedLabel, run_seq_snd, hs]
  change ((weightLabelLoad i).run st).2 + ((weightScalePrepare.run s).2 +
    ((weightScale.run b).2 + (weightEncode.run (weightScale.run b).1).2+1)+1)+1 ≤ _
  change _ ≤ weightConstant * Q^7
  change (weightScale.run b).2 ≤ (BinaryLabelScale.kernelConstant+700000)*Q^7 at hscale
  unfold weightConstant
  nlinarith only [hload', henc', hscale, hprep, hlow]

end PCP.Lang.StandardCorrection
