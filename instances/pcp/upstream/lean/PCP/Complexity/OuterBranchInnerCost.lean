import PCP.Complexity.OuterBranchInner
import PCP.Complexity.OuterBranchResources
import PCP.Complexity.InnerBranchCost

/-! # Charged cost of the selected inner callback inside an outer branch -/

-- Both fixed input-loader ASTs have twenty sequential assignments and copies.
set_option maxRecDepth 2048

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] callInner loadInner InnerBranch.program

def loadInnerConstant : ℕ := loaderConstant loadInner

theorem loadInner_cost (W : ℕ) (st : State 180 80) (hb : StoredBound W st) :
    (loadInner.run st).2 ≤ loadInnerConstant * (W + 1) := by
  apply loader_cost loadInner
    (by unfold loadInner loadInnerHad loadInnerInterpolation; decide)
    (by unfold loadInner loadInnerHad loadInnerInterpolation; decide)
    (by unfold loadInner loadInnerHad loadInnerInterpolation; decide) W st hb

theorem innerQueries_size (k : Kind) (a : Fin 5 → Field t) (s : Sample k t n m) (W : ℕ)
    (hb : InnerBranch.Bounds a (k.line s.1) (innerSeed s) W) :
    listSize (InnerBranch.queries a (k.line s.1) (innerSeed s)) ≤ 6 * (W + 1) := by
  cases h : (innerSeed s).1 with
  | false =>
      have hs := InnerBranch.hadCodes_size (k.line s.1) (innerHadPoint s)
        (innerHadSeed s) W hb.hadamard
      simpa only [InnerBranch.queries, ComputableBinaryLowDegreeTest.queries, h,
        Bool.false_eq_true, ↓reduceIte, List.map_map, Function.comp_def] using hs
  | true =>
      have hs := InterpolationBranch.queryCodes_size a 0
        (interpolationSeed s).1.1.1 (interpolationSeed s).1.1.2 (interpolationSeed s).2
        (k.line s.1) W hb.interpolation
      simpa only [InnerBranch.queries, ComputableBinaryLowDegreeTest.queries, h,
        ↓reduceIte, InterpolationBranch.queryCodes] using hs

theorem selectedInner_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st)
    (hb : InnerBranch.Bounds a (k.line s.1) (innerSeed s) W) :
    (selectedInner.run st).2 ≤ loadInnerConstant * (W + 1) +
      InnerBranch.costConstant * (t + 4 * m + 2 ^ t + 3 * W + 10) ^ 9 +
        6 * (W + 1) + 10 := by
  have hl := loadInner_cost W st hs
  have hi := loadInner_context k a ζ s qs bs st hc
  have hq : (loadInner.run st).1.lists 36 = qs := by
    simpa [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Function.update]
      using hc.history
  have hbs : (loadInner.run st).1.lists 37 = bs.map Bool.toNat := by
    simpa [loadInner, loadInnerHad, loadInnerInterpolation, Stmt.run, Function.update]
      using hc.answers
  have hcost := InnerBranch.program_cost a (k.line s.1) (innerSeed s) qs bs W _ hi hq hbs hb
  have hsem := InnerBranch.program_run a (k.line s.1) (innerSeed s) qs bs _ hi hq hbs
  have hqs : listSize qs ≤ W := hc.history ▸ hs.lists 47 (by decide) (by decide) (by decide)
  have hans : listSize (bs.map Bool.toNat) ≤ W :=
    hc.answers ▸ hs.lists 48 (by decide) (by decide) (by decide)
  have hbase : InnerBranch.budget t m W
      ((loadInner.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ≤
      t + 4 * m + 2 ^ t + 3 * W + 10 := by
    change t + 4 * m + 2 ^ t + W + listSize ((loadInner.run st).1.lists 36) +
      listSize ((loadInner.run st).1.lists 37) + 10 ≤ _
    rw [hq, hbs]
    omega
  have hcost' := hcost.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 9))
  have hr := call_result (by decide) (by decide) InnerBranch.program (loadInner.run st).1
  rw [← hr] at hcost' hsem
  rw [show call _ _ InnerBranch.program = callInner from by unfold callInner; rfl] at hcost'
  have hsize := innerQueries_size k a s W hb
  have hflag := InnerBranch.bool_size (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs)
  simp only [selectedInner, run_seq_snd]
  generalize hu : (loadInner.run st).1 = u at *
  rw [show call _ _ InnerBranch.program = callInner from by
    unfold callInner; rfl] at hsem
  generalize hv : (callInner.run u).1 = v at *
  change v.lists 38 = InnerBranch.queries a (k.line s.1) (innerSeed s) ∧
    v.regs 101 = (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs).toNat at hsem
  simp only [run_assign_fst, run_revApp_snd, setReg_lists]
  change (loadInner.run st).2 + ((callInner.run u).2 +
    (Nat.size (v.regs 101) + Nat.size (v.regs 101) + 1 +
      (listSize (v.lists 38) + 1) + 1) + 1) + 1 ≤ _
  rw [hsem.1, hsem.2]
  omega

end PCP.Lang.OuterBranch
