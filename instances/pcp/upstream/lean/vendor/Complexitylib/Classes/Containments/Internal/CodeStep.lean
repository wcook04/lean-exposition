/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BlockSearch
public import Complexitylib.Classes.Containments.Internal.BoundedReach

/-!
# What the encoded step does to a reachable configuration

⚠️ Unreviewed by Bolton

`Cobham.stepFn` tracks a machine's step only on configurations that respect the
encoding's window: every head inside it, every tape carrying its left-end
marker. This file collects those side conditions into `Complexity.CodeInv`,
shows that every configuration of a space-bounded machine's configuration graph
satisfies it, and reads off what `Complexity.nstepFn` computes there.

## Main definitions

- `Complexity.CodeInv` — the encoding's side conditions on a configuration

## Main results

- `Complexity.cfgCode_length` — a code is exactly `2(k+2)+1` blocks wide
- `Complexity.nstepFn_code`, `Complexity.nstepFn_code_halted` — the encoded
  successor is the code of the successor
- `Complexity.codeInv_of_reachesCfg` — the graph stays inside the window
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The width of a code -/

/-- The number of blocks in a code: one for the state and two per tape. -/
def codeBlocks (k : ℕ) : ℕ := 2 * (k + 2) + 1

private theorem length_flatten_const {α : Type} (bs : List (List α)) (w : ℕ)
    (h : ∀ b ∈ bs, b.length = w) : bs.flatten.length = bs.length * w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.flatten_cons, List.length_append, h b (List.mem_cons_self),
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc)), List.length_cons, Nat.succ_mul]
      omega

/-- **A code is exactly `2(k+2)+1` blocks wide.** -/
@[simp] theorem cfgCode_length {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (c : Cfg k Q) :
    (Cobham.cfgCode W c).length = codeBlocks k * (blockRuler W).length := by
  rw [Cobham.cfgCode, length_flatten_const _ _ (cfgBlocks_width W c), cfgBlocks_length, codeBlocks]

/-- A code is unchanged by the width normalisation. -/
theorem fitCode_cfgCode {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ) (c : Cfg k Q) :
    fitCode (codeBlocks k) (blockRuler W) (Cobham.cfgCode W c) = Cobham.cfgCode W c :=
  fitCode_of_length _ _ _ (cfgCode_length W c)

/-! ## The window conditions -/

/-- The side conditions under which the encoded step tracks the real one. -/
structure CodeInv {Q : Type} (W : ℕ) (c : Cfg k Q) : Prop where
  /-- Every tape carries its left-end marker. -/
  start : ∀ t ∈ cfgTapes c, t.StartInvariant
  /-- Every head is inside the encoded window. -/
  head : ∀ t ∈ cfgTapes c, t.head ≤ W

/-- **The encoded successor is the code of the successor.** -/
theorem nstepFn_code (tm : NTM k) (b : Bool) (W : ℕ) (c : Cfg k tm.Q)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hinv : CodeInv W c)
    (hne : c.state ≠ tm.qhalt) :
    nstepFn tm b (blockRuler W) (Cobham.cfgCode W c) = Cobham.cfgCode W (tm.stepCfg b c) := by
  rw [nstepFn]
  refine stepFn_eq (tm.branchTM b) (c := c) (NTM.branchTM_step tm b hne) hq hinv.head
    (hinv.start _ (by simp [cfgTapes])) (fun i => hinv.start _ ?_)
    (stepActs_forall₂ (tm.branchTM b) c hinv.start hinv.head)
  rw [cfgTapes]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

/-- A halted configuration is a fixed point of the encoded step. -/
theorem nstepFn_code_halted (tm : NTM k) (b : Bool) (W : ℕ) (c : Cfg k tm.Q)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hinv : CodeInv W c)
    (hhalt : c.state = tm.qhalt) :
    nstepFn tm b (blockRuler W) (Cobham.cfgCode W c) = Cobham.cfgCode W c := by
  rw [nstepFn]
  exact stepFn_halted (tm.branchTM b) (c := c) hhalt hq hinv.head

/-! ## The graph stays inside the window -/

/-- Every configuration of the graph carries its left-end markers. -/
theorem startInvariant_of_reachesCfg (tm : NTM k) (x : List Bool) {c : Cfg k tm.Q}
    (h : tm.ReachesCfg (tm.initCfg x) c) :
    c.input.StartInvariant ∧ (∀ i, (c.work i).StartInvariant) ∧
      c.output.StartInvariant := by
  induction h with
  | refl =>
      exact ⟨Tape.StartInvariant.init_ofBool x, fun _ => Tape.StartInvariant.init_nil,
        Tape.StartInvariant.init_nil⟩
  | tail _ hstep ih =>
      obtain ⟨b, hb⟩ := (NTM.succ_iff tm _ _).mp hstep
      exact TM.step_startInvariant (tm.branchTM b) hb ih.1 ih.2.1 ih.2.2

/-- **The graph stays inside the encoded window.** -/
theorem codeInv_of_reachesCfg (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c : Cfg k tm.Q}
    (h : tm.ReachesCfg (tm.initCfg x) c) (W : ℕ)
    (hW : x.length + S x.length + 1 ≤ W) : CodeInv W c := by
  obtain ⟨hin, hwork, hout⟩ := startInvariant_of_reachesCfg tm x h
  have hsp := NTM.withinDecisionSpace_of_reachesCfg hdec x h
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;>
    · rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | rfl | ⟨i, rfl⟩
      · first
          | exact hin
          | (have := hsp.1.2; omega)
      · first
          | exact hout
          | (have := hsp.2; omega)
      · first
          | exact hwork i
          | (have := hsp.1.1 i; omega)

end Complexity
