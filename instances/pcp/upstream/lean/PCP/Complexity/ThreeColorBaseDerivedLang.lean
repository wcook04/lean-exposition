import PCP.Complexity.ThreeColorBaseDerivedLoad

/-! # Running either complete numeric derived-grid branch inside the production workspace -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorFullFieldSampling
  LocalCorrection DerivedGrid ThreeColorBaseSetup

def finish (k : Certificate) : Stmt 400 128 :=
  .seq (.assign (resultPort k) (.var 275)) (.revApp 113 124)

def program (k : Certificate) : Stmt 400 128 := .seq (load k) (.seq (branch k) (finish k))

attribute [local irreducible] branch NumericDerived.program

theorem branch_run (k : Certificate) (N : ℕ) (bits : List Bool) (x : List Bool)
    (qs : List ℕ) (bs : List Bool) (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) (hx : st.lists 100 = x.map Bool.toNat)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    let a := exponent N
    let s := sample k N bits hv
    let w := DerivedSeed.weight k (size a) (size_le_fieldCode a) x s
    let H := FiniteAlphabetIndex.alphabet (BinaryFieldCode.fieldEquiv (binaryDimension a))
      (size_le_fieldCode a)
    ((branch k).run ((load k).run st).1).1.regs 275 =
      (decision k (nodes a) (generator a) H w s qs bs).toNat ∧
    ((branch k).run ((load k).run st).1).1.lists 113 =
      queries k (nodes a) (generator a) H w s := by
  have h := NumericDerived.program_run k (nodes (exponent N)) (generator (exponent N))
    (size (exponent N)) (size_le_fieldCode (exponent N)) x (sample k N bits hv) qs bs
    (view ((load k).run st).1) (load_input k N bits st hd hs hv)
    (load_public k N x qs bs st hd hc hx hq hb)
  rw [← branch_result] at h
  exact h

theorem program_run (k : Certificate) (N : ℕ) (bits : List Bool) (x : List Bool)
    (qs : List ℕ) (bs : List Bool) (st : State 400 128) (hd : Data N st)
    (hc : ThreeColorBaseCardinal.Cardinal (binaryDimension (exponent N))
      (size (exponent N)) st) (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hv : Valid (ThreeColorBaseSeed.sample N bits)) (hx : st.lists 100 = x.map Bool.toNat)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    let a := exponent N
    let s := sample k N bits hv
    let w := DerivedSeed.weight k (size a) (size_le_fieldCode a) x s
    let H := FiniteAlphabetIndex.alphabet (BinaryFieldCode.fieldEquiv (binaryDimension a))
      (size_le_fieldCode a)
    ((program k).run st).1.regs (resultPort k) =
      (decision k (nodes a) (generator a) H w s qs bs).toNat ∧
    ((program k).run st).1.lists 124 =
      (queries k (nodes a) (generator a) H w s).reverse ++ st.lists 124 := by
  have h := branch_run k N bits x qs bs st hd hc hs hv hx hq hb
  have h124 := (branch_list k ((load k).run st).1 124 (by decide)).trans
    (load_list k st 124 (by decide))
  generalize hu : ((branch k).run ((load k).run st).1).1 = u at *
  simp [program, hu, finish, Stmt.run, Expr.eval, Function.update, h.1, h.2, h124]

theorem program_reg (k : Certificate) (st : State 400 128) (i : Fin 400)
    (hi : 300 ≤ i.val) (hne : i ≠ resultPort k) (hwork : i ≠ 310) :
    ((program k).run st).1.regs i = st.regs i := by
  simp only [program, run_seq_fst]
  rw [run_regs_frame (finish k) i (by simp [finish, Stmt.regWrites, hne])]
  rw [branch_reg k _ i hi]
  exact load_reg k st i hi hwork

theorem program_metadata (k : Certificate) (st : State 400 128) (i : Fin 400)
    (hi : 320 ≤ i.val) : ((program k).run st).1.regs i = st.regs i :=
  program_reg k st i (by omega) (by cases k <;> simp only [resultPort] <;> omega) (by omega)

theorem program_list (k : Certificate) (st : State 400 128) (L : Fin 128)
    (hL : 115 ≤ L.val ∨ (100 ≤ L.val ∧ L.val < 103)) (hne : L ≠ 124) :
    ((program k).run st).1.lists L = st.lists L := by
  simp only [program, run_seq_fst]
  rw [run_lists_frame (finish k) L (by simp [finish, Stmt.listWrites, hne])]
  rw [branch_list k _ L hL]
  exact load_list k st L hL

end PCP.Lang.ThreeColorBaseDerived
