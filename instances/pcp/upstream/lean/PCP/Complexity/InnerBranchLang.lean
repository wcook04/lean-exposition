/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchHadamard

/-!
# The complete inner Hadamard/interpolation selector

Both the query trace and the verdict coincide with the original named callback
on an arbitrary shared answer history, including repeated and missing addresses.
-/

-- The two existing arithmetic branches have deeply nested finite syntax.
set_option maxRecDepth 4096

namespace PCP.Lang.InnerBranch

open PCP.Algebraic BinaryPolynomialSpace InterpolationBranch

variable {t n m : ℕ} [NeZero t]

theorem interpolate_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (qs : List ℕ) (bs : List Bool) (st : State 120 40)
    (hc : InterpolationBranch.Context a z u v w site (st.restrict interpRegs id))
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat) :
    (interpolate.run st).1.lists 38 = queryCodes a z u v w site ∧
      (interpolate.run st).1.regs 101 = (check a z u v w site qs bs).toNat := by
  have h := InterpolationBranch.program_run a z u v w site qs bs
    (st.restrict interpRegs id) hc hq hb
  rw [← interpCall_result] at h
  simp only [interpolate, run_seq_fst]
  generalize hout : (interpCall.run st).1 = out at *
  change out.lists 20 = _ ∧ out.regs 11 = _ at h
  simpa only [run_copy_fst, run_assign_fst, Expr.eval, setList_regs,
    setReg_lists, setList_lists, setReg_regs, Function.update_self] using h

def queries (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) : List ℕ :=
  (ComputableBinaryLowDegreeTest.queries (le_refl 1) (BinaryMaterializedField.coordinates t)
    a s).map (fun p => address site p.1 p.2)

def verdict (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (qs : List ℕ) (bs : List Bool) : Bool :=
  ComputableBinaryLowDegreeTest.test (le_refl 1) (BinaryMaterializedField.coordinates t)
    a (oracle site qs bs) s

/-- Exact realization of the actual inner callback, without a callback premise. -/
theorem program_run (a : Fin 5 → Field t) (site : StandardCorrection.Site (Field t) n)
    (s : Seed t m) (qs : List ℕ) (bs : List Bool) (st : State 120 40)
    (hc : Context a site s st) (hq : st.lists 36 = qs)
    (hb : st.lists 37 = bs.map Bool.toNat) :
    (program.run st).1.lists 38 = queries a site s ∧
      (program.run st).1.regs 101 = (verdict a site s qs bs).toNat := by
  cases hcoin : s.1 with
  | false =>
      have hz : st.regs 100 = 0 := hc.coin.trans (congrArg Bool.toNat hcoin)
      have h := hadamard_run site s.2.1.1 s.2.1.2 qs bs st hc.hadamard hc.payload hq hb
      simpa only [program, run_ite_fst, hz, ne_eq, not_true_eq_false, ↓reduceIte,
        queries, verdict, ComputableBinaryLowDegreeTest.queries,
        ComputableBinaryLowDegreeTest.test, hcoin, Bool.false_eq_true,
        List.map_map, Function.comp_def] using h
  | true =>
      have hz : st.regs 100 = 1 := hc.coin.trans (congrArg Bool.toNat hcoin)
      have h := interpolate_run a 0 s.2.2.1.1.1 s.2.2.1.1.2 s.2.2.2
        site qs bs st hc.interpolation hq hb
      simpa only [program, run_ite_fst, hz, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte,
        queries, verdict, queryCodes, check, ComputableBinaryLowDegreeTest.queries,
        ComputableBinaryLowDegreeTest.test, ComputableBinaryLowDegreeTest.interpolationTest,
        hcoin] using h

end PCP.Lang.InnerBranch
