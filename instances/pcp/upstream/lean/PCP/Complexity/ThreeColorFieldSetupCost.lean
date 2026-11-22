import PCP.Complexity.ThreeColorFieldSetup

/-!
# Charged cost of constructing the production field and roots
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameters

theorem buildField_cost (a : ℕ) (st : State 50 15)
    (ht : st.regs 20 = binaryDimension a) (he : st.lists 7 = []) :
    (buildField.run st).2 ≤ 7000000 * (2 ^ binaryDimension a + 1) ^ 7 := by
  rw [buildField, fieldCall_cost]
  exact BinaryRootSearch.buildModulus_cost (binaryDimension a)
    (by rw [binaryDimension_eq]; omega) _ ht he

theorem rootStep_cost (a : ℕ) (full : Bool) (st : State 50 15)
    (h : FieldContext a st) :
    ((rootStep full).run st).2 ≤ 400000000 * (2 ^ binaryDimension a + 4) ^ 6 := by
  have hs := BinaryRootSearch.searchRoot_cost full (st.restrict fieldRegs fieldLists)
    h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [← fieldCall_cost] at hs
  have hr := BinaryRootSearch.searchRoot_run (fieldIndex a) full
    (st.restrict fieldRegs fieldLists) h.1 h.2.1 h.2.2.1 h.2.2.2
  have hp := congrArg (fun u : State 36 11 => u.regs 35)
    (fieldCall_state (BinaryRootSearch.searchRoot full) st)
  change ((fieldCall (BinaryRootSearch.searchRoot full)).run st).1.regs 35 = _ at hp
  have ho := hp.trans hr
  have hsize : Nat.size (((fieldCall (BinaryRootSearch.searchRoot full)).run st).1.regs 35) ≤
      binaryDimension a := by
    rw [ho]
    exact Nat.size_le.mpr (Fin.isLt _)
  have htq : binaryDimension a ≤ 2 ^ binaryDimension a := (Nat.lt_two_pow_self).le
  simp only [rootStep, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
  let q := 2 ^ binaryDimension a
  change _ ≤ 400000000 * (q + 4) ^ 6
  change ((fieldCall (BinaryRootSearch.searchRoot full)).run st).2 ≤
    300000000 * (q + 4) ^ 6 at hs
  have hpow : q + 4 ≤ (q + 4) ^ 6 := le_self_pow₀ (by omega) (by decide)
  change binaryDimension a ≤ q at htq
  nlinarith

/-- Both searches and the modulus constructor are charged in full. -/
theorem roots_cost (a : ℕ) (st : State 50 15)
    (ht : st.regs 20 = binaryDimension a) (he : st.lists 7 = []) :
    (roots.run st).2 ≤ 1000000000 * (2 ^ binaryDimension a + 4) ^ 7 := by
  have hb := buildField_run a st ht he
  have hbc := buildField_cost a st ht he
  generalize hu : (buildField.run st).1 = u at *
  let s := setReg u 47 (u.regs 28)
  have hs : FieldContext a s := by simpa [FieldContext, s, Function.update] using hb
  have hsc := rootStep_cost a false s hs
  have hcctx := rootStep_context a false s hs
  generalize hv : ((rootStep false).run s).1 = v at *
  have hfc := rootStep_cost a true v hcctx
  have hsize : Nat.size (u.regs 28) ≤ 2 ^ binaryDimension a := by
    rw [hb.2.1]
    exact size_le_self _
  let q := 2 ^ binaryDimension a
  have hb' : (buildField.run st).2 ≤ 7000000 * (q + 4) ^ 7 :=
    hbc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [q]; omega) 7))
  have hpow : (q + 4) ^ 6 ≤ (q + 4) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hc' := hsc.trans (Nat.mul_le_mul_left _ hpow)
  have hf' := hfc.trans (Nat.mul_le_mul_left _ hpow)
  have hq : q + 4 ≤ (q + 4) ^ 7 := le_self_pow₀ (by omega) (by decide)
  simp only [roots, run_seq_snd, run_assign_fst, Expr.eval, hu]
  change (buildField.run st).2 + ((Expr.var 28).cost u.regs +
    (((rootStep false).run s).2 +
      ((rootStep true).run ((rootStep false).run s).1).2 + 1) + 1) + 1 ≤ _
  rw [hv]
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  change _ ≤ 1000000000 * (q + 4) ^ 7
  change Nat.size (u.regs 28) ≤ q at hsize
  nlinarith

end PCP.Lang.ThreeColorContext
