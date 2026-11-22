/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CodeStep

/-!
# Reading the verdict cell out of a record

⚠️ Unreviewed by Bolton

Acceptance is a property of cell `1` of the output tape, but a code stores each
tape split at its head, so where cell `1` sits depends on the head. Driving the
head back to cell `0` first puts it in a fixed place: the encoding's right
half-block is then the whole tape in order, two bits per cell, so cell `1` is
bits `2` and `3`.

That is the same rewind the completeness direction of Cobham's theorem uses to
read a simulated machine's output, `Cobham.rewindFn`, run here as a loop of its
own.

## Main definitions

- `Complexity.outPair` — the output tape's two blocks, read out of a record
- `Complexity.rewindStepP` — one rewind step, on the packed state
- `Complexity.rewindCode` — a whole rewind

## Main results

- `Complexity.outPair_cfgCode` — the two blocks are the output tape's code
- `Complexity.rewindCode_pairCode` — a long enough rewind parks the head
- `Complexity.rewindStepP_mem_FP`, `Complexity.rewindCodeFn_mem_FP` — both are
  polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The output tape inside a record -/

/-- Block `3` is the output tape's left half. -/
theorem blockAt_cfgCode_outputLeft {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (c : Cfg k Q) :
    blockAt (blockRuler W) (Cobham.cfgCode W c) 3
      = padTo (blockRuler W) (leftCode c.output) := by
  rw [blockAt_cfgCode W c 3 (by rw [cfgBlocks_length]; omega)]
  rfl

/-- Block `4` is the output tape's right half. -/
theorem blockAt_cfgCode_outputRight {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (c : Cfg k Q) :
    blockAt (blockRuler W) (Cobham.cfgCode W c) 4
      = padTo (blockRuler W) (rightCode c.output W) := by
  rw [blockAt_cfgCode W c 4 (by rw [cfgBlocks_length]; omega)]
  rfl

/-- The output tape's code, read out of a record. -/
def outPair (R u : List Bool) : List Bool := blockAt R u 3 ++ blockAt R u 4

theorem outPairFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => outPair (a z) (b z)) ∈ FP :=
  Cobham.appendFn_mem_FP (blockAtFn_mem_FP ha hb 3) (blockAtFn_mem_FP ha hb 4)

/-- **The two blocks are the output tape's code.** -/
theorem outPair_cfgCode {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ) (c : Cfg k Q) :
    outPair (blockRuler W) (Cobham.cfgCode W c) = pairCode W c.output := by
  rw [outPair, blockAt_cfgCode_outputLeft, blockAt_cfgCode_outputRight, pairCode]

/-! ## The rewind loop -/

/-- One rewind step, on the packed state `pair R z`. -/
def rewindStepP (z : List Bool) : List Bool :=
  pair (pairFst z) (rewindFn (pairFst z) (pairSnd z))

theorem rewindStepP_pack (R z : List Bool) :
    rewindStepP (pair R z) = pair R (rewindFn R z) := by
  rw [rewindStepP, pairFst_pair, pairSnd_pair]

theorem rewindStepP_iterate (R z : List Bool) (n : ℕ) :
    rewindStepP^[n] (pair R z) = pair R ((rewindFn R)^[n] z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, rewindStepP_pack, ih, Function.iterate_succ_apply]

/-- A whole rewind: one step per bit of the ruler. -/
def rewindCode (R ruler z : List Bool) : List Bool :=
  pairSnd (rewindStepP^[ruler.length] (pair R z))

theorem rewindCode_eq (R ruler z : List Bool) :
    rewindCode R ruler z = (rewindFn R)^[ruler.length] z := by
  rw [rewindCode, rewindStepP_iterate, pairSnd_pair]

/-- **A long enough rewind parks the head at cell `0`.** -/
theorem rewindCode_pairCode (W : ℕ) (t : Tape) (hinv : t.StartInvariant)
    (hW : t.head ≤ W) (ruler : List Bool) (hlen : W ≤ ruler.length) :
    rewindCode (blockRuler W) ruler (pairCode W t)
      = pairCode W { head := 0, cells := t.cells } := by
  rw [rewindCode_eq, iterate_rewindFn t hinv hW ruler.length,
    rewound t (le_trans hW hlen)]

/-! ## Both are polynomial-time -/

theorem rewindFnFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => rewindFn (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := rewindFn) (Cobham.rewindFn_mem (Cobham.proj 0) (Cobham.proj 1)) ha hb

theorem rewindStepP_mem_FP : rewindStepP ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : (fun z => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : (fun z => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  exact Cobham.pairFn_mem_FP hfst (rewindFnFn_mem_FP hfst hsnd)

/-- **The rewind is polynomial-time.** -/
theorem rewindCodeFn_mem_FP {Rf rulerf zf : List Bool → List Bool} (hR : Rf ∈ FP)
    (hruler : rulerf ∈ FP) (hz : zf ∈ FP)
    (hlen : ∀ w, (zf w).length ≤ 2 * (Rf w).length) :
    (fun w => rewindCode (Rf w) (rulerf w) (zf w)) ∈ FP := by
  have hinit : (fun w => pair (Rf w) (zf w)) ∈ FP := Cobham.pairFn_mem_FP hR hz
  have hwidth : (fun w => pair (Rf w) (wideRuler 2 (Rf w))) ∈ FP :=
    Cobham.pairFn_mem_FP hR (wideRulerFn_mem_FP hR 2)
  have hbound : ∀ w, ∀ n ≤ (rulerf w).length,
      (rewindStepP^[n] (pair (Rf w) (zf w))).length
        ≤ (pair (Rf w) (wideRuler 2 (Rf w))).length := by
    intro w n _
    rw [rewindStepP_iterate, pair_length, pair_length, wideRuler_length]
    have := Cobham.iterate_rewindFn_length_le (Rf w) (zf w) (hlen w) n
    omega
  have h := Cobham.iterate_mem_FP rewindStepP_mem_FP hinit hruler hwidth hbound
  have h2 := mem_FP_comp h Cobham.sndBlock_mem_FP
  refine mem_FP_of_eq h2 fun w => ?_
  rw [Function.comp_apply, rewindCode]

end Complexity
