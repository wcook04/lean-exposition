/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedCallLang
import PCP.Complexity.CorrectionContextResources

/-! # Actual protected-source and trace sizes for complete derived calls -/

namespace PCP.Lang.DerivedCall

-- Fixed loader membership proofs range over the 300-register layout.
set_option maxRecDepth 4096

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace

structure SourceBound (W : ℕ) (st : State 300 112) : Prop where
  regs : ∀ i : Fin 300, (240 ≤ i.val ∧ i.val < 256) ∨ (260 ≤ i.val ∧ i.val < 270) →
    Nat.size (st.regs i) ≤ W
  lists : ∀ L : Fin 112, 100 ≤ L.val → L.val < 109 → listSize (st.lists L) ≤ W

theorem SourceBound.of_frame {W : ℕ} {st out : State 300 112}
    (hb : SourceBound W st) (hf : Frame st out) : SourceBound W out :=
  ⟨fun i hi => by rw [hf.regs i (by omega) (by omega)]; exact hb.regs i hi,
    fun L hL hu => by rw [hf.lists L hL hu]; exact hb.lists L hL hu⟩

def fixedConstant (p : Stmt 300 112) : ℕ := p.C*(p.width+p.csize+1)

theorem fixed_cost (p : Stmt 300 112) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, (240 ≤ i.val ∧ i.val < 256) ∨ (260 ≤ i.val ∧ i.val < 270))
    (hl : ∀ L ∈ p.lUses, 100 ≤ L.val ∧ L.val < 109)
    (W : ℕ) (st : State 300 112) (hb : SourceBound W st) :
    (p.run st).2 ≤ fixedConstant p*(W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi)
  · intro L hL
    exact hb.lists L (hl L hL).1 (hl L hL).2

theorem preparePrimary_cost (W : ℕ) (st : State 300 112) (hb : SourceBound W st) :
    (preparePrimary.run st).2 ≤ fixedConstant preparePrimary*(W+1) :=
  fixed_cost preparePrimary (by decide) (by decide) (by decide) W st hb

theorem prepareCorrection_cost (left : Bool) (W : ℕ) (st : State 300 112)
    (hb : SourceBound W st) :
    ((prepareCorrection left).run st).2 ≤ fixedConstant (prepareCorrection left)*(W+1) :=
  fixed_cost (prepareCorrection left) (by cases left <;> decide)
    (by cases left <;> decide) (by cases left <;> decide) W st hb

-- Copying the 20 fixed fields requires normalization through the full layout.
set_option maxRecDepth 4096 in
theorem prepareCorrection_bound (left : Bool) (W : ℕ) (st : State 300 112)
    (hb : SourceBound W st) :
    CorrectionContext.SourceBound W
      (view (by decide) (by decide) ((prepareCorrection left).run st).1) := by
  constructor
  · intro i
    fin_cases i
    · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
        Stmt.run, Expr.eval, Function.update] using hb.regs 240 (by decide)
    · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
        Stmt.run, Expr.eval, Function.update] using hb.regs 241 (by decide)
    · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
        Stmt.run, Expr.eval, Function.update] using hb.regs 242 (by decide)
    · cases left
      · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
          Stmt.run, Expr.eval, Function.update] using hb.regs 249 (by decide)
      · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
          Stmt.run, Expr.eval, Function.update] using hb.regs 248 (by decide)
    · simpa [CorrectionSeed.inputPort, view, State.restrict, prepareCorrection,
        Stmt.run, Expr.eval, Function.update] using hb.regs 243 (by decide)
  · constructor
    · intro i hi
      have he : i = 212 ∨ i = 213 ∨ i = 214 ∨ i = 215 ∨ i = 216 ∨ i = 217 ∨
          i = 218 ∨ i = 219 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 250 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 251 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 252 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 253 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 254 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 255 (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
          using hb.regs 244 (by decide)
      · cases left
        · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
            using hb.regs 247 (by decide)
        · simpa [view, State.restrict, prepareCorrection, Stmt.run, Expr.eval, Function.update]
            using hb.regs 246 (by decide)
    · intro L hL hu
      have he : L = 83 ∨ L = 84 ∨ L = 85 ∨ L = 86 ∨ L = 87 ∨ L = 88 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · cases left
        · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
            using hb.lists 104 (by decide) (by decide)
        · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
            using hb.lists 103 (by decide) (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
          using hb.lists 105 (by decide) (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
          using hb.lists 101 (by decide) (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
          using hb.lists 102 (by decide) (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
          using hb.lists 107 (by decide) (by decide)
      · simpa [view, State.restrict, prepareCorrection, Stmt.run, Function.update]
          using hb.lists 108 (by decide) (by decide)

variable {t n m : ℕ} [NeZero t]

theorem primaryQueries_size (weighted : Bool) (weight : OuterBranch.Field t)
    (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3) :
    listSize (primaryQueries weighted weight w mask loc) ≤ 2*(QueryAddress.width t n m 4+1) := by
  have h0 := QueryAddress.address_size (fieldEquiv t)
    (loc.query (primaryLabel weighted weight w+mask))
  have h1 := QueryAddress.address_size (fieldEquiv t) (loc.query mask)
  change Nat.size (queryCode (loc.query (primaryLabel weighted weight w+mask))) ≤
    QueryAddress.width t n m 4 at h0
  change Nat.size (queryCode (loc.query mask)) ≤ QueryAddress.width t n m 4 at h1
  change Nat.size (queryCode (loc.query (primaryLabel weighted weight w+mask)))+1+
    (Nat.size (queryCode (loc.query mask))+1+0) ≤ _
  omega

theorem callQueries_size (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) :
    listSize (callQueries k nodes ζ a w s) ≤ 21*(QueryAddress.width t n m 4+1) := by
  have hlen : (callQueries k nodes ζ a w s).length ≤ 21 := by
    simp only [callQueries, List.length_map, ComputableBinaryLocalCorrection.queries_eq]
    exact BinaryLocalCorrection.queries_length_le _ _ _ _ _ _ _ _ _
  have hbound : ∀ z ∈ callQueries k nodes ζ a w s,
      Nat.size z ≤ QueryAddress.width t n m 4 := by
    intro z hz
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz
    exact QueryAddress.address_size (fieldEquiv t) (k.physical a q)
  exact (HadamardRow.listSize_bounded _ _ hbound).trans
    (Nat.mul_le_mul_right _ hlen)

end PCP.Lang.DerivedCall
