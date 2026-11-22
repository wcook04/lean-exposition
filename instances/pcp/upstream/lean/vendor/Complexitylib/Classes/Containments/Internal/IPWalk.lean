/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPStep
public import Complexitylib.Classes.Containments.Internal.IPGameTree

/-!
# The walk runs on the protocol's tree

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.IPSem` builds a machine that walks an abstract tree,
parametric in a single test — *does this coin string make the verifier accept below these rounds*.
This file supplies that test from a protocol and checks that the tree the machine walks is the
protocol's own.

## Main definitions

- `Complexity.Protocol.walkParams` — the parameters the walk runs on

## Main results

- `Complexity.Protocol.treeVal_eq_gvalR` — the abstract tree is the protocol's game tree
- `Complexity.Protocol.treeVal_le_two_pow` — its values fit in the coin space
- `Complexity.Protocol.ipStep_iterate_walk` — the encoded orbit is the abstract one
-/

@[expose] public section

namespace Complexity

namespace Protocol

open Classical in
/-- The parameters the walk runs on: the message bound, the coin width, and the leaf test. -/
noncomputable def walkParams (prot : Protocol) (x : List Bool) : IPM.Params where
  m := prot.msgLen x.length
  t := prot.coins x.length
  ok := fun ps s =>
    decide (prot.replay x s ps [] = true ∧
      pair (pair x s) (false :: (encBodyR ps ++ [true])) ∈ prot.verdict)

open Classical in
/-- **The abstract tree is the protocol's game tree.** -/
theorem treeVal_eq_gvalR (prot : Protocol) (x : List Bool) :
    ∀ (n : ℕ) (ps : List (List Bool × List Bool)),
      IPM.treeVal (prot.walkParams x) n ps = prot.gvalR x (prot.coins x.length) n ps := by
  classical
  intro n
  induction n with
  | zero =>
      intro ps
      rw [IPM.treeVal_zero, gvalR_zero_enum]
      refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
      show ((prot.walkParams x).ok ps (IPM.coinOf (prot.walkParams x) k) = true) ↔ _
      rw [walkParams, IPM.coinOf, IPM.zeroCoin]
      simp
  | succ n ih =>
      intro ps
      rw [IPM.treeVal, gvalR_succ_enum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sup_congr rfl fun j _ => ?_
      rw [ih, IPM.msgOf, IPM.msgOf]

open Classical in
theorem treeVal_le_two_pow (prot : Protocol) (x : List Bool) (n : ℕ)
    (ps : List (List Bool × List Bool)) :
    IPM.treeVal (prot.walkParams x) n ps ≤ 2 ^ (prot.walkParams x).t := by
  rw [treeVal_eq_gvalR]
  exact gvalR_le_two_pow prot x _ n ps

/-! ## The walk decides membership -/

open Classical in
/-- The verdict the walk finishes with is membership. -/
theorem cmpBit_eq_true_iff {L : Language} (prot : Protocol) (x : List Bool)
    (hcomp : ∀ y ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen y.length) ∧
      2 / 3 ≤ eventProb (prot.acceptEvent S y))
    (hsound : ∀ y ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen y.length) →
      eventProb (prot.acceptEvent S y) ≤ 1 / 3)
    (w : List Bool) (hwlen : w.length = (prot.walkParams x).t + 1)
    (hwval : binValLE w = IPM.treeVal (prot.walkParams x) (prot.rounds x.length) []) :
    IPM.cmpBit (prot.walkParams x) w = true ↔ x ∈ L := by
  classical
  have hlen : (false :: w).length = (twoPowBits (prot.walkParams x).t).length := by
    rw [List.length_cons, hwlen, twoPowBits_length]
  have h1 : IPM.cmpBit (prot.walkParams x) w = true
      ↔ ltFlag (twoPowBits (prot.walkParams x).t) (false :: w) = [true] := by
    rw [IPM.cmpBit, ltFlag_eq _ _ hlen]
    simp
  rw [h1, ← two_pow_lt_two_mul_iff (prot.walkParams x).t w hwlen, hwval, treeVal_eq_gvalR,
    gvalR_root]
  exact (Protocol.mem_iff_gval prot x hcomp hsound).symm

open Classical in
/-- **The walk decides membership.** From a single fresh frame of `rounds(|x|)` levels the machine
keeps its flag down, raises it on the next step, and one step later the flag *is* the membership
bit. -/
theorem walk_decides {L : Language} (prot : Protocol)
    (hcomp : ∀ y ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen y.length) ∧
      2 / 3 ≤ eventProb (prot.acceptEvent S y))
    (hsound : ∀ y ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen y.length) →
      eventProb (prot.acceptEvent S y) ≤ 1 / 3)
    (x : List Bool) (lvl : List Bool) (hlvl : lvl.length = prot.rounds x.length) :
    ∃ T ≤ IPM.runBound (prot.walkParams x) (prot.rounds x.length),
      (∀ j ≤ T, ((IPM.step (prot.walkParams x))^[j]
          ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] lvl]⟩).done = false) ∧
      ((IPM.step (prot.walkParams x))^[T + 1]
          ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] lvl]⟩).done = true ∧
      ((((IPM.step (prot.walkParams x))^[T + 2]
          ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] lvl]⟩).done = true)
        ↔ x ∈ L) := by
  classical
  obtain ⟨T, w, hT, hwlen, hwval, hdd, h1, h2⟩ :=
    IPM.run_top (prot.walkParams x) (treeVal_le_two_pow prot x) lvl
  rw [hlvl] at hT hwval
  refine ⟨T, hT, hdd, ?_, ?_⟩
  · rw [h1]
  · rw [h2]
    exact cmpBit_eq_true_iff prot x hcomp hsound w hwlen hwval

/-- **The encoded orbit is the abstract one.** -/
theorem ipStep_iterate_walk (prot : Protocol) (x : List Bool) (mr cr : List Bool)
    (hm : mr.length = (prot.walkParams x).m) (hc : cr.length = (prot.walkParams x).t)
    (okf : List Bool → List Bool → List Bool)
    (lvl : List Bool)
    (hokf : ∀ (f : IPM.Frm) (fs : List IPM.Frm), IPM.BodyOk (f :: fs) →
      (f :: fs).length ≤ lvl.length + 1 → ∀ u : List Bool,
      okf (IPM.encStk (f :: fs)) u = [(prot.walkParams x).ok (IPM.roundsOf fs) u])
    (j : ℕ) :
    (IPM.ipStep mr cr okf)^[j]
        (IPM.encSst ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] lvl]⟩)
      = IPM.encSst ((IPM.step (prot.walkParams x))^[j]
          ⟨false, false, none, [IPM.freshFrm (prot.walkParams x) [] lvl]⟩) :=
  IPM.ipStep_iterate (prot.walkParams x) mr cr hm hc okf (lvl.length + 1) hokf j _
    (IPM.encOk_start (prot.walkParams x) lvl)

end Protocol

end Complexity
