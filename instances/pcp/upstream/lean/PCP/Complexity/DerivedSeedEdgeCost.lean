/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedResources
import PCP.Complexity.GridEdgeCost
import PCP.Complexity.OuterBranchPointLabelCost

/-! # Charged cost of the public edge weight in a derived-grid branch -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode
open LocalCorrection DerivedGrid

attribute [local irreducible] edgeCall GridEdge.program

def edgeCost (C d t h n : ℕ) (x : List Bool) : ℕ :=
  C*(GridEdge.budget t h n x+1)^7+d*(t+1)+6*t+2*h+2*n+
    listSize (x.map Bool.toNat)+25

/-- The constant is supplied by the already proved concrete edge program bound. -/
theorem edge_cost : ∃ C : ℕ, ∀ (t n m : ℕ) [NeZero t] (k : Certificate) (h : ℕ) (_hh : h ≤ 2 ^ t)
    (x : List Bool) (s : DerivedGrid.Sample k t n m) (st : State 300 112),
    st.regs 240 = t → st.regs 279 = h → st.regs 280 = n →
    st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t) →
    st.lists 100 = [] →
    st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val) →
    st.lists 111 = x.map Bool.toNat →
    ((edge k).run st).2 ≤ edgeCost C (baseDimension k n) t h n x := by
  obtain ⟨C, hC⟩ := GridEdge.program_cost
  refine ⟨C, ?_⟩
  intro t n m _ k h hh x s st ht hh' hn hmod he hz hx
  cases k with
  | valid =>
    simp only [edge, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, edgeCost, Nat.size_zero]
    omega
  | proper =>
    have hi : GridEdge.Input t h n x s.1
        (DerivedCall.view (by decide) (by decide) (edgePrepare.run st).1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using ht
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hh'
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hn
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hmod
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using he
      · calc _ = st.lists 109 := by
                simp [edgePrepare, Stmt.run, Expr.eval, Function.update,
                  DerivedCall.view, State.restrict]
             _ = _ := hz
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hx
    have hc := hC t h n hh x s.1 _ hi
    have hr := GridEdge.program_run hh x s.1 _ hi
    rw [← DerivedCall.call_result (by decide) (by decide) GridEdge.program] at hc hr
    rw [show DerivedCall.call (by decide) (by decide) GridEdge.program = edgeCall by
      unfold edgeCall; rfl] at hc hr
    change (edgeCall.run (edgePrepare.run st).1).1.regs 50 = _ at hr
    have hsize : Nat.size ((edgeCall.run (edgePrepare.run st).1).1.regs 50) ≤ t := by
      rw [hr]
      exact Nat.size_le.mpr (fieldEquiv t _).isLt
    have hsm := BinaryField.listSize_bits
      (BinaryField.encode_bits (BinaryWordMaterialization.modulus t))
    simp only [BinaryField.encode_length] at hsm
    have hsz : listSize (List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) ≤
        (n+n)*(t+1) := StandardCorrection.fieldCodes_size s.1
    have hst := size_le_self t
    have hsh := size_le_self h
    have hsn := size_le_self n
    have hp : (edgePrepare.run st).2 ≤
        (n+n)*(t+1)+4*t+2*h+2*n+listSize (x.map Bool.toNat)+19 := by
      simp only [edgePrepare, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
        setReg_regs, setReg_lists, setList_lists, Function.update, Fin.reduceEq, dite_false,
        ht, hh', hn, hmod, he, hz, hx, show listSize ([] : List ℕ) = 0 from rfl]
      omega
    simp only [edge, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    simp only [edgeCost, baseDimension]
    omega

end PCP.Lang.DerivedSeed
