import PCP.Complexity.InterpolationBranchEmit

/-!
# Charged construction of interpolation-branch physical query addresses
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] emitCall emitPrepare

theorem emitPrepare_cost (st : State 100 40) (W : ℕ) (he : st.lists 7 = [])
    (hb : ∀ i ∈ ([83, 84, 85, 86, 87, 88, 89, 90, 91, 95, 94] : List (Fin 100)),
      Nat.size (st.regs i) ≤ W) :
    (emitPrepare.run st).2 ≤ 22*W+24 := by
  have h83 := hb 83 (by simp)
  have h84 := hb 84 (by simp)
  have h85 := hb 85 (by simp)
  have h86 := hb 86 (by simp)
  have h87 := hb 87 (by simp)
  have h88 := hb 88 (by simp)
  have h89 := hb 89 (by simp)
  have h90 := hb 90 (by simp)
  have h91 := hb 91 (by simp)
  have h95 := hb 95 (by simp)
  have h94 := hb 94 (by simp)
  simp only [emitPrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setReg_regs, Function.update, Fin.reduceEq, dite_false, he, listSize,
    List.map_nil, List.sum_nil]
  omega

/-- The bound covers the actual address expression and the preparation of all eleven inputs. -/
theorem emitStep_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (x : Point t m) (label : Coefficients t 1) (st : State 100 40)
    (hc : Context a z u v w site st)
    (hx : st.regs 95 = (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 x).val)
    (hw : st.regs 94 = (BooleanCoefficientIndex.coefficientEquiv t 1 label).val)
    (W : ℕ)
    (hb : ∀ i : Fin 11, Nat.size (QueryAddress.inputs (fieldEquiv t)
      (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
        (site.query x label) i) ≤ W)
    (ha : Nat.size (address site x label) ≤ W) :
    (emitStep.run st).2 ≤
      (QueryAddress.program.C*
        (QueryAddress.program.width+QueryAddress.program.csize+1)+30)*(W+1) := by
  have hpref (i : Fin 9) : Nat.size (st.regs (prefixPort i)) ≤ W := by
    rw [hc.address i]
    simpa only [StandardCorrection.Site.inputs_prefix] using hb (i.castAdd 2)
  have h95 : Nat.size (st.regs 95) ≤ W := by
    rw [hx]
    simpa only [StandardCorrection.Site.inputs_inner] using hb 9
  have h94 : Nat.size (st.regs 94) ≤ W := by
    rw [hw]
    simpa only [StandardCorrection.Site.inputs_label] using hb 10
  have hp := emitPrepare_cost st W hc.empty (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpref 0
    · exact hpref 1
    · exact hpref 2
    · exact hpref 3
    · exact hpref 4
    · exact hpref 5
    · exact hpref 6
    · exact hpref 7
    · exact hpref 8
    · exact h95
    · exact h94)
  have hv := emitPrepare_context a z u v w site x label st hc hx hw
  have hview := StandardCorrection.address_view (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
    site x label _ hv
  have hscratch : ((emitPrepare.run st).1.restrict
      (Fin.castLE (by decide : 80 ≤ 100)) (Fin.castLE (by decide : 26 ≤ 40))).lists 21 = [] := by
    simp [emitPrepare, Stmt.run, Function.update, hc.empty, State.restrict]
  have he := StandardCorrection.emit_cost (fieldEquiv t)
    (BooleanCoefficientIndex.coefficientEquiv t 1) (BooleanCoefficientIndex.coefficientEquiv t 3)
    site x label _ hv W
    (fun i => by rw [← State.restrict_regs, hview i]; exact hb i)
    (by rw [hscratch]; exact Nat.zero_le _) ha
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    StandardCorrection.emit (emitPrepare.run st).1)] at he
  have he' : (emitCall.run (emitPrepare.run st).1).2 ≤
      (QueryAddress.program.C*
        (QueryAddress.program.width+QueryAddress.program.csize+1)+2)*(W+1) := by
    simpa only [emitCall, Prod.snd] using he
  rw [emitStep, run_seq_snd]
  nlinarith only [hp, he']

end PCP.Lang.InterpolationBranch
