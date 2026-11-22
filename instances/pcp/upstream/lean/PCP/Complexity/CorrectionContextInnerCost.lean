/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionContextResources

/-! # Charged cost of the inner-seed stage of correction loading -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection
variable {t n m : ℕ} [NeZero t]

-- Fixed payload copying uses the full register layout.
set_option maxRecDepth 4096

attribute [local irreducible] inner InnerSeed.program

theorem prepareInner_cost (k : Certificate) (W : ℕ) (st : State 220 96)
    (hb : LoadedBound W st) :
    ((prepareInner k).run st).2 ≤ fixedConstant (prepareInner k) * (W + 1) := by
  apply loaded_cost (prepareInner k) (by cases k <;> decide)
    (by cases k <;> decide) (by cases k <;> decide) W st hb

theorem prepareInner_bound (k : Certificate) (W : ℕ) (st : State 220 96)
    (hb : LoadedBound W st) :
    InnerSeed.SourceBound (W + 3) (innerState ((prepareInner k).run st).1) := by
  constructor
  · intro i hi hu
    have he : i = 120 ∨ i = 121 ∨ i = 122 ∨ i = 123 ∨ i = 124 ∨ i = 125 ∨
        i = 126 ∨ i = 127 ∨ i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 200 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 201 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 208 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · have htag : Nat.size (k.outer.tag + 4) ≤ W + 3 := by
        cases k <;> change 3 ≤ W + 3 <;> omega
      simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using htag
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 212 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 213 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 214 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 215 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 216 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 217 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 219 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 207 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using (hb.regs 204 (by decide) (by decide) (by decide) (by decide)).trans
          (Nat.le_add_right W 3)
  · intro L hL hu
    have he : L = 40 ∨ L = 41 ∨ L = 42 := by omega
    rcases he with rfl | rfl | rfl
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update]
        using (hb.lists 85 (by decide) (by decide)).trans (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update]
        using (hb.lists 80 (by decide) (by decide)).trans (Nat.le_add_right W 3)
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update]
        using (hb.lists 86 (by decide) (by decide)).trans (Nat.le_add_right W 3)

def innerCost (k : Certificate) (t m W : ℕ) : ℕ :=
  fixedConstant (prepareInner k) * (W + 1) +
    InnerSeed.costConstant * (InnerSeed.budget t m (W + 3)) ^ 5 + 1

theorem materializeInner_cost (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st)
    (hb : LoadedBound W st) :
    ((materializeInner k).run st).2 ≤ innerCost k t m W := by
  have hc := prepareInner_cost k W st hb
  have hs := prepareInner_run k nodes ζ a w s qs bs st hp hl
  have hbound := prepareInner_bound k W st hb
  have hi := InnerSeed.program_cost nodes (k.outer.line (a,s.1)) s.2.2.2 (W+3)
    (innerState ((prepareInner k).run st).1) hs.1 hbound hs.2
  rw [← inner_result] at hi
  simp only [materializeInner, run_seq_snd]
  unfold innerCost
  omega

end PCP.Lang.CorrectionContext
