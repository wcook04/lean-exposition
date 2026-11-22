/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedResources
import PCP.Complexity.GridRecoveryPointsCost
import PCP.Complexity.OuterBranchPointLabelCost

/-! # Charged costs of derived-grid recovery points and their numeric codes -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode
open LocalCorrection DerivedGrid
variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] pointsCall encodeCall GridRecovery.points RadixCodec.encode

def pointsCost (d t h : ℕ) : ℕ :=
  100001000*(h+t+d+1)^6+5*d*(t+1)+4*t+2*h+20

theorem points_cost (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t)
    (s : DerivedGrid.Sample k t n m) (st : State 300 112)
    (ht : st.regs 240 = t) (hh' : st.regs 279 = h)
    (hm : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 100 = [])
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) :
    (points.run st).2 ≤ pointsCost (baseDimension k n) t h := by
  have hc : GridRecovery.Context t h
      (DerivedCall.view (by decide) (by decide) (pointsPrepare.run st).1) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [DerivedCall.view, State.restrict, pointsPrepare, Stmt.run, Expr.eval,
        Function.update, ht, hh', hm, he]
  have hp : (DerivedCall.view (by decide) (by decide) (pointsPrepare.run st).1 :
      State 41 17).lists 12 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val) := by
    simpa [DerivedCall.view, State.restrict, pointsPrepare, Stmt.run, Expr.eval,
      Function.update] using hx
  have hcost := GridRecovery.points_cost h hh (List.ofFn s.1) _ hc
    (by simpa only [GridRecovery.codes, List.map_ofFn, Function.comp_def] using hp)
  have hout := GridRecovery.points_zero_recovery h hh s.1 _ hc hp
  rw [← DerivedCall.call_result (by decide) (by decide) GridRecovery.points] at hcost hout
  rw [show DerivedCall.call (by decide) (by decide) GridRecovery.points = pointsCall by
    unfold pointsCall; rfl] at hcost hout
  change (pointsCall.run (pointsPrepare.run st).1).1.lists 15 = _ ∧
    (pointsCall.run (pointsPrepare.run st).1).1.lists 16 = _ at hout
  have hsa := StandardCorrection.fieldCodes_size
    (fun i => BinaryZeroOnGrid.zeroPoint s.1 (finSumFinEquiv.symm i))
  have hsb := StandardCorrection.fieldCodes_size
    (fun i => FieldQueryArithmetic.recoveryPoint
      (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s.1 (finSumFinEquiv.symm i))
  have hsx := StandardCorrection.fieldCodes_size s.1
  have hsm := BinaryField.listSize_bits
    (BinaryField.encode_bits (BinaryWordMaterialization.modulus t))
  simp only [BinaryField.encode_length] at hsm
  have hst := size_le_self t
  have hsh := size_le_self h
  have hprep : (pointsPrepare.run st).2 ≤
      baseDimension k n*(t+1)+4*t+2*h+13 := by
    simp only [pointsPrepare, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
      setReg_regs, setReg_lists, setList_lists, Function.update, Fin.reduceEq, dite_false,
      ht, hh', hm, he, hx, show listSize ([] : List ℕ) = 0 from rfl]
    omega
  simp only [List.length_ofFn] at hcost
  simp only [points, run_seq_snd, run_copy_snd, run_copy_fst, setList_lists,
    Function.update_of_ne (by decide : (16 : Fin 112) ≠ 103), hout.1, hout.2]
  unfold pointsCost
  nlinarith only [hcost, hprep, hsa, hsb]

def encodeCost (d t : ℕ) : ℕ :=
  (RadixCodec.passConstant+20)*(d*(t+1)+(d+1)*(t+2)+2)^2+
    d*(t+1)+2*(t+1)+2*t*d+6

omit [NeZero t] in
theorem encode_cost (k : Certificate) (p : k.Point t n) (src : Fin 112) (dst : Fin 300)
    (st : State 300 112) (hb : st.regs 243 = 2 ^ t)
    (hx : st.lists src = List.ofFn (fun i => (fieldEquiv t (k.outer.vector p i)).val)) :
    ((encode src dst).run st).2 ≤ encodeCost (k.outer.dimension n) t := by
  have hr : (DerivedCall.view (by decide) (by decide) ((encodePrepare src).run st).1 :
      State 6 1).regs 0 = 2 ^ t := by
    simp [DerivedCall.view, State.restrict, encodePrepare, Stmt.run, Expr.eval,
      Function.update, hb]
  have hl : (DerivedCall.view (by decide) (by decide) ((encodePrepare src).run st).1 :
      State 6 1).lists 0 = List.ofFn (fun i => (fieldEquiv t (k.outer.vector p i)).val) := by
    simp [DerivedCall.view, State.restrict, encodePrepare, Stmt.run, Function.update, hx]
  have hc := RadixCodec.encode_cost
    (DerivedCall.view (by decide) (by decide) ((encodePrepare src).run st).1)
    (by rw [hr, hl]; intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact (fieldEquiv t (k.outer.vector p i)).isLt)
  rw [hr, hl] at hc
  rw [← DerivedCall.call_result (by decide) (by decide) RadixCodec.encode] at hc
  rw [show DerivedCall.call (by decide) (by decide) RadixCodec.encode = encodeCall by
    unfold encodeCall; rfl] at hc
  have hs := StandardCorrection.fieldCodes_size (k.outer.vector p)
  have hw : RadixCodec.workBound (2 ^ t)
      (List.ofFn (fun i => (fieldEquiv t (k.outer.vector p i)).val))+1 ≤
      k.outer.dimension n*(t+1)+(k.outer.dimension n+1)*(t+2)+2 := by
    simp only [RadixCodec.workBound, List.length_ofFn, Nat.size_pow]
    nlinarith only [hs]
  have hc' := hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2))
  have ho := encode_run k p src dst st hb hx
  simp only [encode, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self] at ho
  have hsize := k.outer.pointCode_size p
  have hp : ((encodePrepare src).run st).2 ≤ k.outer.dimension n*(t+1)+2*(t+1)+3 := by
    simp only [encodePrepare, Stmt.run, Expr.eval, Expr.cost, Expr.readSize,
      setList_regs, hx, hb, Nat.size_pow, Nat.add_assoc]
    omega
  simp only [encode, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, ho]
  unfold encodeCost
  nlinarith only [hc', hp, hsize]

end PCP.Lang.DerivedSeed
