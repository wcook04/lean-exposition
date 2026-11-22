/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchLang

/-! # Shared-history preservation by the complete inner selector -/

namespace PCP.Lang.InnerBranch

open PCP.Algebraic InterpolationBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] InterpolationBranch.queries InterpolationBranch.program interpCall

theorem hadCall_list (st : State 120 40) (L : Fin 40) (hL : 32 ≤ L.val) :
    (hadCall.run st).1.lists L = st.lists L := by
  apply HadamardRow.branch.run_rename_list_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [hadLists, Fin.val_castLE] at this
  omega

theorem hadamard_list (st : State 120 40) (L : Fin 40)
    (hL : 32 ≤ L.val) (h38 : L ≠ 38) :
    (hadamard.run st).1.lists L = st.lists L := by
  simp only [hadamard, run_seq_fst, run_copy_fst, run_assign_fst, setReg_lists,
    setList_lists, Function.update_of_ne h38, hadCall_list _ L hL]
  have h30 : L ≠ 30 := by intro h; subst L; omega
  have h31 : L ≠ 31 := by intro h; subst L; omega
  have h27 : L ≠ 27 := by intro h; subst L; omega
  simp only [prepareHad, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_of_ne h30, Function.update_of_ne h31, Function.update_of_ne h27]

theorem interpCall_list (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 120 40)
    (hc : InterpolationBranch.Context a z u v w site (st.restrict interpRegs id))
    (L : Fin 40) (hL : 32 ≤ L.val) :
    (interpCall.run st).1.lists L = st.lists L := by
  have hq := (InterpolationBranch.queries_run a z u v w site
    (st.restrict interpRegs id) hc).2.lists L hL
  have hw : ∀ L : Fin 40, 32 ≤ L.val → L ∉ InterpolationBranch.verdict.listWrites := by
    decide
  have h : (InterpolationBranch.program.run (st.restrict interpRegs id)).1.lists L =
      st.lists L := by
    rw [InterpolationBranch.program, run_seq_fst,
      run_lists_frame InterpolationBranch.verdict L (hw L hL)]
    exact hq
  rw [← interpCall_result] at h
  exact h

theorem interpolate_list (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 120 40)
    (hc : InterpolationBranch.Context a z u v w site (st.restrict interpRegs id))
    (L : Fin 40) (hL : 32 ≤ L.val) (h38 : L ≠ 38) :
    (interpolate.run st).1.lists L = st.lists L := by
  simp only [interpolate, run_seq_fst, run_copy_fst, run_assign_fst, setReg_lists,
    setList_lists, Function.update_of_ne h38]
  exact interpCall_list a z u v w site st hc L hL

theorem program_list (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (st : State 120 40) (hc : Context a site s st)
    (L : Fin 40) (hL : 32 ≤ L.val) (h38 : L ≠ 38) :
    (program.run st).1.lists L = st.lists L := by
  simp only [program, run_ite_fst]
  split_ifs
  · exact interpolate_list a _ _ _ _ site st hc.interpolation L hL h38
  · exact hadamard_list st L hL h38

theorem program_history (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (st : State 120 40) (hc : Context a site s st) :
    (program.run st).1.lists 36 = st.lists 36 ∧
      (program.run st).1.lists 37 = st.lists 37 :=
  ⟨program_list a site s st hc 36 (by decide) (by decide),
    program_list a site s st hc 37 (by decide) (by decide)⟩

end PCP.Lang.InnerBranch
