/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedCallResources

/-! # Complete charged cost of the masked primary stage -/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic BinaryFieldCode LocalCorrection BinaryPolynomialSpace
variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] DerivedPrimary.program primaryCall DerivedPrimary.programConstant

def primaryCost (t n m W : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  fixedConstant preparePrimary*(W+1) + DerivedPrimary.programConstant*
    (2^t+QueryAddress.width t n m 4+listSize qs+listSize (bs.map Bool.toNat)+10)^8 +
    2*(QueryAddress.width t n m 4+1)+9

theorem savePrimary_cost (V : ℕ) (st : State 300 112)
    (hv : Nat.size (st.regs 8) ≤ 1) (he : st.lists 100 = [])
    (hq : listSize (st.lists 26) ≤ V) : (savePrimary.run st).2 ≤ V+7 := by
  simp only [savePrimary, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, setReg_lists,
    he, show listSize ([] : List ℕ) = 0 from rfl, setList_lists,
    Function.update_of_ne (by decide : (26 : Fin 112) ≠ 110)]
  omega

theorem primary_cost (weighted : Bool) (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (a b : k.Point t n) (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (weight : OuterBranch.Field t) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st)
    (hb : SourceBound W st) :
    ((primary weighted).run st).2 ≤ primaryCost t n m W qs bs := by
  have hprep := preparePrimary_cost W st hb
  have hp := preparePrimary_run k nodes ζ a b w mask weight loc first second qs bs st hc
  have hs : listSize ((view (by decide) (by decide) (preparePrimary.run st).1 :
      State 100 32).lists 27) ≤ QueryAddress.width t n m 4 := by
    simp [view, State.restrict, preparePrimary, Stmt.run, Function.update, hc.empty, listSize]
  have hcall := DerivedPrimary.program_cost weighted weight w mask (loc.payload (fieldEquiv t))
    (QueryAddress.width t n m 4) (view (by decide) (by decide) (preparePrimary.run st).1)
    hp.1 hp.2.1 (BranchQueryBounds.payload loc le_rfl) hs (by
      intro p _
      rw [loc.address_eq]
      exact QueryAddress.address_size (fieldEquiv t) (loc.query p))
  have hout := DerivedPrimary.program_location weighted weight w mask loc qs bs
    (view (by decide) (by decide) (preparePrimary.run st).1) hp.1 hp.2.1
    (by simpa [view, State.restrict] using hp.2.2.1)
    (by simpa [view, State.restrict] using hp.2.2.2)
  rw [← call_result (by decide) (by decide) (DerivedPrimary.program weighted)] at hcall hout
  have he := (call_list (by decide) (by decide) (DerivedPrimary.program weighted)
    (preparePrimary.run st).1 100 (by decide)).trans
      ((preparePrimary_frame st).lists 100 (by decide) (by decide) |>.trans hc.empty)
  rw [show call (by decide) (by decide) (DerivedPrimary.program weighted) = primaryCall weighted by
    unfold primaryCall; rfl] at hcall hout he
  change ((primaryCall weighted).run (preparePrimary.run st).1).2 ≤
    DerivedPrimary.programConstant*(2^t+QueryAddress.width t n m 4+
      listSize ((preparePrimary.run st).1.lists 30)+
      listSize ((preparePrimary.run st).1.lists 31)+10)^8 at hcall
  rw [hp.2.2.1, hp.2.2.2] at hcall
  have hvalue : ((primaryCall weighted).run (preparePrimary.run st).1).1.regs 8 =
      (primaryBit weighted weight w mask loc qs bs).val := hout.2
  have hqueries : ((primaryCall weighted).run (preparePrimary.run st).1).1.lists 26 =
      primaryQueries weighted weight w mask loc := hout.1
  have hval : Nat.size (((primaryCall weighted).run (preparePrimary.run st).1).1.regs 8) ≤ 1 := by
    rw [hvalue]
    exact Nat.size_le.mpr (ZMod.val_lt _)
  have htrace : listSize (((primaryCall weighted).run (preparePrimary.run st).1).1.lists 26) ≤
      2*(QueryAddress.width t n m 4+1) := by
    rw [hqueries]
    exact primaryQueries_size weighted weight w mask loc
  have hsave := savePrimary_cost _ _ hval he htrace
  simp only [primary, run_seq_snd]
  unfold primaryCost
  omega

end PCP.Lang.DerivedCall
