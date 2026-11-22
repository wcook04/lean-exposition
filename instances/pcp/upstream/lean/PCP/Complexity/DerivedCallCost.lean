/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedCallPrimaryCost
import PCP.Complexity.DerivedCallCorrectionCost

/-! # Complete polynomial charged cost of the actual derived-grid call -/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace
variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] primary correction

theorem finish_cost (p : ZMod 2) (a b : Option (ZMod 2)) (st : State 300 112)
    (h0 : st.regs 270 = p.val) (h1 : st.regs 271 = present a)
    (h2 : st.regs 272 = answer a) (h3 : st.regs 273 = present b)
    (h4 : st.regs 274 = answer b) :
    (finish.run st).2 ≤ 1000000+listSize (st.lists 110)+2 := by
  have h := DerivedGrid.verdict_cost p a b (st.restrict verdictRegs Fin.elim0) h0 h1 h2 h3 h4
  rw [← DerivedGrid.verdict.run_rename verdictRegs Fin.elim0 (by decide)
    (fun i => Fin.elim0 i) st] at h
  have hl := Stmt.run_rename_list_outside DerivedGrid.verdict verdictRegs Fin.elim0
    (110 : Fin 112) (fun i => Fin.elim0 i) st
  simp only [finish, run_seq_snd, run_rev_snd, hl]
  omega

def programCost (k : Certificate) (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  primaryCost t n m W qs bs + correctionCost k true t n m W qs bs +
    correctionCost k false t n m W qs bs + 1000000+44*(QueryAddress.width t n m 4+1)+5

set_option maxRecDepth 8192 in
/-- Every callback and history operation is executed, with actual stored source sizes charged. -/
theorem program_cost (weighted : Bool) (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (a b : k.Point t n) (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (weight : OuterBranch.Field t) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st)
    (hbound : SourceBound W st) :
    ((program weighted k).run st).2 ≤ programCost k t n m W qs bs := by
  have hp := primary_run weighted k nodes ζ a b w mask weight loc first second qs bs st hc
  have hpc := primary_cost weighted k nodes ζ a b w mask weight loc first second qs bs W st
    hc hbound
  have hcu := hc.of_frame hp.2.2
  have hbu := hbound.of_frame hp.2.2
  generalize hu : ((primary weighted).run st).1 = u at *
  have ha := correction_run true k nodes ζ a b w mask weight loc first second qs bs u hcu
  have hac := correction_cost true k nodes ζ a b w mask weight loc first second qs bs W u hcu hbu
  have hap := (correction_reg k true u 270 (by decide) (by decide) (by decide)).trans hp.1
  have hcv := hcu.of_frame ha.2.2.2
  have hbv := hbu.of_frame ha.2.2.2
  generalize hv : ((correction k true).run u).1 = v at *
  have hb := correction_run false k nodes ζ a b w mask weight loc first second qs bs v hcv
  have hbc := correction_cost false k nodes ζ a b w mask weight loc first second qs bs W v hcv hbv
  have hbp := (correction_reg k false v 270 (by decide) (by decide) (by decide)).trans hap
  have hbap := (correction_reg k false v 271 (by decide) (by decide) (by decide)).trans ha.1
  have hbaa := (correction_reg k false v 272 (by decide) (by decide) (by decide)).trans ha.2.1
  generalize hz : ((correction k false).run v).1 = z at *
  have hfinish := finish_cost _ _ _ z hbp hbap hbaa hb.1 hb.2.1
  have htrace : listSize (z.lists 110) ≤ 44*(QueryAddress.width t n m 4+1) := by
    have hpq := primaryQueries_size weighted weight w mask loc
    have haq := callQueries_size k nodes ζ a w first
    have hbq := callQueries_size k nodes ζ b w second
    rw [hb.2.2.1, listSize_append, listSize_reverse, ha.2.2.1, listSize_append,
      listSize_reverse, hp.2.1, listSize_reverse]
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    omega
  simp only [program, run_seq_snd, hu, hv, hz]
  unfold programCost
  omega

end PCP.Lang.DerivedCall
