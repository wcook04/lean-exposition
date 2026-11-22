import PCP.Complexity.OuterBranchPointLabel

/-!
# Polynomial cost of the outer affine point and homogeneous label
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] callOuterPoint callOuterLabel
  StandardCorrection.scalarPoint HadamardHomogeneousCode.program

omit [NeZero t] in
theorem Kind.pointCode_size (k : Kind) (x : Point k t n) :
    Nat.size (k.pointCode (fieldEquiv t) x) ≤ t * k.dimension n := by
  apply Nat.size_le.mpr
  simpa only [Kind.pointCode, ← pow_mul] using
    (finFunctionFinEquiv (fieldEquiv t ∘ k.vector x)).isLt

theorem loadOuterPoint_cost (src : Fin 180) (_hs : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((loadOuterPoint src).run st).2 ≤ 12 * (t + k.dimension n + 2)^2 := by
  have hu : listSize (st.lists 42) ≤ k.dimension n * (t+1) := by
    rw [hc.left]; exact StandardCorrection.fieldCodes_size _
  have hv : listSize (st.lists 43) ≤ k.dimension n * (t+1) := by
    rw [hc.right]; exact StandardCorrection.fieldCodes_size _
  have hm : listSize (st.lists 40) ≤ 2*t := by
    rw [hc.modulus]
    exact InterpolationBranch.coordinateBits_size _
  have ht := size_le_self t
  have hα : Nat.size (fieldEquiv t α).val ≤ t := Nat.size_le.mpr (fieldEquiv t α).isLt
  simp only [loadOuterPoint, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setList_lists, setReg_regs, Function.update,
    Fin.reduceEq, dite_false, hc.width, hc.card, hc.empty, ha, Nat.size_pow,
    show listSize [] = 0 from rfl]
  nlinarith only [hu, hv, hm, ht, hα, Nat.zero_le (t^2), Nat.zero_le ((k.dimension n)^2)]

theorem callOuterPoint_cost (k : Kind) (u v : Point k t n) (α : Field t)
    (st : State 180 80)
    (hc : StandardCorrection.AffineContext (k.vector u) (k.vector v)
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (ha : st.regs 26 = (fieldEquiv t α).val) :
    (callOuterPoint.run st).2 ≤
      (RadixCodec.passConstant+101000025) * (t+k.dimension n+2)^5 := by
  have hp := StandardCorrection.scalarPoint_cost α _ _ _ hc ha
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    StandardCorrection.scalarPoint st)] at hp
  simpa only [callOuterPoint, Prod.snd] using hp

theorem outerPoint_cost (src : Fin 180) (hs : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((outerPoint src).run st).2 ≤
      (RadixCodec.passConstant+101000100) * (t+k.dimension n+2)^5 := by
  have hp := loadOuterPoint_cost src hs k a ζ α s qs bs st hc ha
  have hi := loadOuterPoint_input src k a ζ s qs bs st hc
  have hα : ((loadOuterPoint src).run st).1.regs 26 = (fieldEquiv t α).val := by
    simpa [loadOuterPoint, Stmt.run, Expr.eval, Function.update] using ha
  have hcall := callOuterPoint_cost k s.1.1 s.1.2 α _ hi hα
  have hout := (outerPoint_run src hs k a ζ α s qs bs st hc ha).1
  simp only [outerPoint, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self] at hout
  have hsize : Nat.size
      ((callOuterPoint.run ((loadOuterPoint src).run st).1).1.regs 59) ≤ t*k.dimension n := by
    rw [hout]; exact k.pointCode_size _
  have h25 : (t+k.dimension n+2)^2 ≤ (t+k.dimension n+2)^5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  rw [outerPoint, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  nlinarith only [hp, hcall, hsize, h25, Nat.zero_le (t^2), Nat.zero_le ((k.dimension n)^2)]

theorem loadOuterLabel_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (loadOuterLabel.run st).2 ≤ 5*t+15 := by
  have hw : listSize (st.lists 45) ≤ 2*t := by
    rw [hc.label]; exact InterpolationBranch.coordinateBits_size _
  have ht := size_le_self t
  have hd : Nat.size k.degree ≤ 2 := by cases k <;> decide
  simp only [loadOuterLabel, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setList_lists, setReg_regs, Function.update, Fin.reduceEq, dite_false,
    hc.width, hc.degree, hc.empty, show listSize [] = 0 from rfl]
  omega

theorem outerLabel_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (outerLabel.run st).2 ≤
      (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)*(2^t+7)^8 := by
  have ht : (loadOuterLabel.run st).1.regs 20 = t := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.width
  have hd : (loadOuterLabel.run st).1.regs 56 = k.degree := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.degree
  have he : (loadOuterLabel.run st).1.lists 7 = [] := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.empty
  have hw : (loadOuterLabel.run st).1.lists 17 = List.ofFn (fun i => (s.2.2.1.2 i).val) := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.label
  have hp := HadamardHomogeneousCode.program_cost k.degree_pos s.2.2.1.2
    ((loadOuterLabel.run st).1.restrict (Fin.castLE (by decide : 80 ≤ 180))
      (Fin.castLE (by decide : 32 ≤ 80)))
    (by simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 80 ≤ 180) (20 : Fin 80) = (20 : Fin 180) from rfl] using ht)
    (by simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 80 ≤ 180) (56 : Fin 80) = (56 : Fin 180) from rfl] using hd)
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 32 ≤ 80) (7 : Fin 32) = (7 : Fin 80) from rfl] using he)
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 32 ≤ 80) (17 : Fin 32) = (17 : Fin 80) from rfl] using hw)
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    HadamardHomogeneousCode.program (loadOuterLabel.run st).1)] at hp
  have hpc : (callOuterLabel.run (loadOuterLabel.run st).1).2 ≤
      (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+300)*
        (2^t+Nat.size k.degree+5)^8 := by
    simpa only [callOuterLabel, Prod.snd] using hp
  have hr := (outerLabel_run k a ζ s qs bs st hc).1
  simp only [outerLabel, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self] at hr
  have hout : Nat.size ((callOuterLabel.run (loadOuterLabel.run st).1).1.regs 1) ≤ 2^t := by
    rw [hr]; exact HadamardLabel.code_size _
  have hdsize : Nat.size k.degree ≤ 2 := by cases k <;> decide
  have hp' := hpc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by omega : 2^t+Nat.size k.degree+5 ≤ 2^t+7) 8))
  have hl := loadOuterLabel_cost k a ζ s qs bs st hc
  have hpow : 2^t+7 ≤ (2^t+7)^8 := Nat.le_pow (by decide)
  have htq : t < 2^t := Nat.lt_two_pow_self
  rw [outerLabel, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  nlinarith only [hp', hl, hout, hpow, htq]

end PCP.Lang.OuterBranch
