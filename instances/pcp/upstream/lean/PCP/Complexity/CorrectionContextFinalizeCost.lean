/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionContextResources

/-! # Charging final correction copies by their semantic output sizes -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection
variable {t n m : ℕ} [NeZero t]

-- The fixed loader has 39 copies and uses the full register layout.
set_option maxRecDepth 4096

set_option maxHeartbeats 1000000 in
-- Normalize each copied source through the 39-stage fixed loader.
/-- Every read is copied to a protected output; unused scratch 54 is irrelevant. -/
theorem finalize_cost_of_output (k : Certificate) (W : ℕ) (st : State 220 96)
    (hb : OuterBranch.StoredBound W
      (setList (outerState ((finalize k).run st).1) 54 [])) :
    ((finalize k).run st).2 ≤ fixedConstant (finalize k) * (W + 1) := by
  apply loopFree_cost_le (finalize k) (by cases k <;> decide) st W
  · intro i hi
    have he : i = 200 ∨ i = 201 ∨ i = 208 ∨ i = 218 ∨ i = 206 ∨ i = 100 ∨ i = 104 ∨ i = 202 ∨
        i = 212 ∨ i = 213 ∨ i = 214 ∨ i = 215 ∨ i = 216 ∨ i = 217 ∨ i = 219 ∨ i = 207 ∨
        i = 119 := by
      simp [finalize, Stmt.uses, Expr.uses] at hi
      tauto
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 120 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 122 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 123 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 124 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 125 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 126 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 127 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 128 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 130 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 131 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 132 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 133 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 134 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 135 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 136 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 137 (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Expr.eval,
        Function.update] using hb.regs 138 (by decide) (by decide)
  · intro L hL
    have he : L = 85 ∨ L = 80 ∨ L = 83 ∨ L = 81 ∨ L = 82 ∨ L = 84 ∨ L = 86 ∨ L = 87 ∨ L = 88 ∨
        L = 20 ∨ L = 21 ∨ L = 22 ∨ L = 23 ∨ L = 32 ∨ L = 33 ∨ L = 34 := by
      simp [finalize, Stmt.lUses] at hL
      tauto
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 40 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 41 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 42 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 43 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 44 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 45 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 46 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 47 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 48 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 50 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 51 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 52 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 53 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 59 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 60 (by decide) (by decide) (by decide)
    · simpa [setList, outerState, State.restrict, finalize, Stmt.run, Function.update]
        using hb.lists 61 (by decide) (by decide) (by decide)

/-- Semantic arrays supply a polynomial bound without charging arbitrary scratch. -/
theorem finalize_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hc : OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState ((finalize k).run st).1)) :
    ((finalize k).run st).2 ≤
      fixedConstant (finalize k) * (OuterBranch.storedWidth t n m qs bs [] + 1) := by
  have hclear := hc.set_scratch54 k.outer nodes ζ (k.sample a w s) qs bs _ []
  have hb := hclear.storedBound k.outer nodes ζ (k.sample a w s) qs bs _
  simp only [setList, Function.update_self] at hb
  exact finalize_cost_of_output k _ st hb

end PCP.Lang.CorrectionContext
