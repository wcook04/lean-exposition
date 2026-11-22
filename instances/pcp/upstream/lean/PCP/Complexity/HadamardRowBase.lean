/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowSpec

/-!
# The six initial Hadamard row queries

The concrete stages produce the base, auxiliary, additive, constant, and linear
queries in the semantic order. Only the later factor iterations remain separate.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def unitLabel (t r : ℕ) : Coefficients t r := BooleanCoefficientArithmetic.constant 1

def linearLabel (hr : 1 ≤ r) (s : TestRandomness t r) : Coefficients t r :=
  BooleanCoefficientArithmetic.embed hr s.linear

def constantPart : Stmt 80 32 :=
  .seq (.assign 51 (.const 1)) (.seq HadamardLabel.constant (emitSum 5 20))

theorem constantPart_stable : Stable constantPart := by decide

theorem constantPart_run (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    (constantPart.run st).1.lists 24 = code (unitLabel t r + s.base) :: st.lists 24 := by
  let u := setReg st 51 1
  have hl := HadamardLabel.constant_run (t := t) (r := r) 1 u
    (by simpa [u, Function.update] using hc.1)
    (by simpa [u, Function.update] using hc.2.1) (by rfl) hc.2.2.1
  have hu7 := run_lists_frame HadamardLabel.constant 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.constant 20 (by decide) u
  have hu24 := run_lists_frame HadamardLabel.constant 24 (by decide) u
  dsimp only [u] at hl hu7 hu20 hu24
  simp only [constantPart, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hv : (HadamardLabel.constant.run (setReg st 51 1)).1 = v at *
  have hh := emitSum_run 5 20 (by decide) (unitLabel t r) s.base v hl
    (hu20.trans hc.2.2.2.1) (hu7.trans hc.2.2.1)
  rw [hu24] at hh
  exact hh

def linearPrepare : Stmt 80 32 :=
  .seq (.copy 22 13) (.seq (.assign 54 (.const 1))
    (.seq HadamardLabel.embed (.copy 5 26)))

theorem linearPrepare_stable : Stable linearPrepare := by decide

theorem linearPrepare_run (hr : 1 ≤ r) (s : TestRandomness t r)
    (st : State 80 32) (hc : Context s st) :
    (linearPrepare.run st).1.lists 26 = encode (linearLabel hr s) := by
  let u := setReg (setList st 13 (st.lists 22)) 54 1
  have hl := HadamardLabel.embed_run hr s.linear u
    (by simpa [u, Function.update] using hc.1) (by simp [u])
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1)
  dsimp only [u] at hl
  simp only [linearPrepare, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval]
  generalize hv : (HadamardLabel.embed.run
    (setReg (setList st 13 (st.lists 22)) 54 1)).1 = v at *
  simp only [setList_lists, Function.update_self]
  exact hl

def linearPart : Stmt 80 32 :=
  .seq linearPrepare (.seq (emitSum 26 20) (emit 26))

theorem linearPart_stable : Stable linearPart := by decide

theorem linearPart_run (hr : 1 ≤ r) (s : TestRandomness t r)
    (st : State 80 32) (hc : Context s st) :
    (linearPart.run st).1.lists 24 = code (linearLabel hr s) ::
      code (linearLabel hr s + s.base) :: st.lists 24 := by
  have hl := linearPrepare_run hr s st hc
  have hctx := context_frame linearPrepare linearPrepare_stable s st hc
  have h24 := run_lists_frame linearPrepare 24 (by decide) st
  simp only [linearPart, run_seq_fst]
  generalize hs : (linearPrepare.run st).1 = u at *
  have hsum := emitSum_run 26 20 (by decide) (linearLabel hr s) s.base u hl
    hctx.2.2.2.1 hctx.2.2.1
  have h26 := run_lists_frame (emitSum 26 20) 26 (by decide) u
  generalize hu : ((emitSum 26 20).run u).1 = v at *
  rw [emit_run 26 (linearLabel hr s) v (h26.trans hl), hsum, h24]

/-- A single allowance uniformly covers each of the five initial query-producing stages. -/
def baseStepConstant : ℕ :=
  BooleanLabelTransform.queryConstant + 6 * WordCodec.passConstant + 2000

def baseSize (t r : ℕ) : ℕ := 2 ^ t + Nat.size r + 5

theorem constantPart_cost (s : TestRandomness t r) (st : State 80 32) (hc : Context s st) :
    (constantPart.run st).2 ≤ baseStepConstant * baseSize t r ^ 8 := by
  let u := setReg st 51 1
  have hcost := HadamardLabel.constant_cost (t := t) (r := r) 1 u
    (by simpa [u, Function.update] using hc.1)
    (by simpa [u, Function.update] using hc.2.1) (by rfl) hc.2.2.1
  have hl := HadamardLabel.constant_run (t := t) (r := r) 1 u
    (by simpa [u, Function.update] using hc.1)
    (by simpa [u, Function.update] using hc.2.1) (by rfl) hc.2.2.1
  have hu7 := run_lists_frame HadamardLabel.constant 7 (by decide) u
  have hu20 := run_lists_frame HadamardLabel.constant 20 (by decide) u
  dsimp only [u] at hcost hl hu7 hu20
  simp only [constantPart, run_seq_snd, run_assign_fst, Expr.eval]
  generalize hv : (HadamardLabel.constant.run (setReg st 51 1)).1 = v at *
  have hsum := emitSum_cost 5 20 (by decide) (unitLabel t r) s.base v hl
    (hu20.trans hc.2.2.2.1) (hu7.trans hc.2.2.1)
  change (Expr.const 1).cost st.regs + ((HadamardLabel.constant.run (setReg st 51 1)).2 +
    ((emitSum 5 20).run v).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_one]
  have h8 : (2 ^ t + Nat.size r + 3) ^ 8 ≤ baseSize t r ^ 8 :=
    Nat.pow_le_pow_left (by dsimp only [baseSize]; omega) _
  have h2 : (2 ^ t + 1) ^ 2 ≤ baseSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by change 2 ^ t + 1 ≤ 2 ^ t + Nat.size r + 5; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hc' := hcost.trans (Nat.mul_le_mul_left _ h8)
  have hs' := hsum.trans (Nat.mul_le_mul_left _ h2)
  have hpos : 1 ≤ baseSize t r ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  unfold baseStepConstant
  nlinarith only [hc', hs', hpos, Nat.zero_le WordCodec.passConstant]

theorem linearPrepare_cost (hr : 1 ≤ r) (s : TestRandomness t r)
    (st : State 80 32) (hc : Context s st) :
    (linearPrepare.run st).2 ≤ (BooleanLabelTransform.queryConstant + 200) *
      baseSize t r ^ 8 := by
  let u := setReg (setList st 13 (st.lists 22)) 54 1
  have hcost := HadamardLabel.embed_cost s.linear u
    (by simpa [u, Function.update] using hc.1) (by simp [u])
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1)
  have hl := HadamardLabel.embed_run hr s.linear u
    (by simpa [u, Function.update] using hc.1) (by simp [u])
    (by simpa [u, Function.update] using hc.2.1)
    (by simpa [u, Function.update] using hc.2.2.1)
    (by simpa [u] using hc.2.2.2.2.2.1)
  dsimp only [u] at hcost hl
  simp only [linearPrepare, run_seq_snd, run_copy_snd, run_copy_fst,
    run_assign_fst, Expr.eval]
  generalize hv : (HadamardLabel.embed.run
    (setReg (setList st 13 (st.lists 22)) 54 1)).1 = v at *
  change (listSize (st.lists 22) + 1) + ((Expr.const 1).cost _ +
    ((HadamardLabel.embed.run (setReg (setList st 13 (st.lists 22)) 54 1)).2 +
      (listSize (v.lists 5) + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_one, hl, hc.2.2.2.2.2.1]
  have hleft := HadamardLabel.encode_size s.linear
  have hright := HadamardLabel.encode_size (linearLabel hr s)
  change listSize (encode (BooleanCoefficientArithmetic.embed hr s.linear)) ≤ 2 * 2 ^ t at hright
  have hb : 2 ^ t + Nat.size 1 + Nat.size 1 + Nat.size r + 3 = baseSize t r := by
    simp only [Nat.size_one, baseSize]
    omega
  rw [hb] at hcost
  have hlow : 2 ^ t + 5 ≤ baseSize t r ^ 8 :=
    (by dsimp only [baseSize]; omega : 2 ^ t + 5 ≤ baseSize t r).trans
      (Nat.le_pow (by decide))
  rw [hc.2.2.2.2.2.1] at hcost
  nlinarith only [hcost, hleft, hright, hlow]

theorem linearPart_cost (hr : 1 ≤ r) (s : TestRandomness t r)
    (st : State 80 32) (hc : Context s st) :
    (linearPart.run st).2 ≤ baseStepConstant * baseSize t r ^ 8 := by
  have hprep := linearPrepare_cost hr s st hc
  have hl := linearPrepare_run hr s st hc
  have hctx := context_frame linearPrepare linearPrepare_stable s st hc
  simp only [linearPart, run_seq_snd]
  generalize hs : (linearPrepare.run st).1 = u at *
  have hsum := emitSum_cost 26 20 (by decide) (linearLabel hr s) s.base u hl
    hctx.2.2.2.1 hctx.2.2.1
  have h26 := run_lists_frame (emitSum 26 20) 26 (by decide) u
  generalize hu : ((emitSum 26 20).run u).1 = v at *
  have hemit := emit_cost 26 (linearLabel hr s) v (h26.trans hl)
  have h2 : (2 ^ t + 1) ^ 2 ≤ baseSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by change 2 ^ t + 1 ≤ 2 ^ t + Nat.size r + 5; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hs' := hsum.trans (Nat.mul_le_mul_left _ h2)
  have he' := hemit.trans (Nat.mul_le_mul_left _ h2)
  have hpos : 1 ≤ baseSize t r ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  unfold baseStepConstant
  nlinarith only [hprep, hs', he', hpos]

/-- The initial six query labels, before any factor checks. -/
def prefixQueries (hr : 1 ≤ r) (s : TestRandomness t r) : List ℕ :=
  [code s.base, code s.auxiliary, code (s.base + s.auxiliary),
    code (unitLabel t r + s.base), code (linearLabel hr s + s.base), code (linearLabel hr s)]

def initialQueries : Stmt 80 32 :=
  .seq (emit 20) (.seq (emit 21) (.seq (emitSum 20 21) (.seq constantPart linearPart)))

theorem small_bound (t r : ℕ) :
    (WordCodec.passConstant * 3 + 101) * (2 ^ t + 1) ^ 2 ≤
      baseStepConstant * baseSize t r ^ 8 := by
  have h2 : (2 ^ t + 1) ^ 2 ≤ baseSize t r ^ 8 :=
    (Nat.pow_le_pow_left (by change 2 ^ t + 1 ≤ 2 ^ t + Nat.size r + 5; omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  apply (Nat.mul_le_mul_left _ h2).trans
  apply Nat.mul_le_mul_right
  unfold baseStepConstant
  omega

theorem prefix_spec (hr : 1 ≤ r) (s : TestRandomness t r) :
    Spec s initialQueries (prefixQueries hr s) ((5 * baseStepConstant + 4) * baseSize t r ^ 8) := by
  let C := baseStepConstant * baseSize t r ^ 8
  have hemit : (WordCodec.passConstant * 3 + 30) * (2 ^ t + 1) ^ 2 ≤ C :=
    (Nat.mul_le_mul_right _ (by omega)).trans (small_bound t r)
  have hbase := (emit_spec s 20 s.base (fun _ hc => hc.2.2.2.1) (by decide)).mono hemit
  have haux := (emit_spec s 21 s.auxiliary (fun _ hc => hc.2.2.2.2.1) (by decide)).mono hemit
  have hsum := (emitSum_spec s 20 21 (by decide) s.base s.auxiliary
    (fun _ hc => hc.2.2.2.1) (fun _ hc => hc.2.2.2.2.1) (by decide)).mono (small_bound t r)
  have hunit : Spec s constantPart [code (unitLabel t r + s.base)] C :=
    ⟨fun st hc => context_frame _ constantPart_stable s st hc,
      fun st hc => by simpa using constantPart_run s st hc, constantPart_cost s⟩
  have hlin : Spec s linearPart
      [code (linearLabel hr s + s.base), code (linearLabel hr s)] C :=
    ⟨fun st hc => context_frame _ linearPart_stable s st hc,
      fun st hc => by simpa using linearPart_run hr s st hc, linearPart_cost hr s⟩
  have hh := hbase.seq (haux.seq (hsum.seq (hunit.seq hlin)))
  apply hh.mono
  have hpos : 1 ≤ baseSize t r ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  dsimp [C]
  nlinarith only [hpos]

end PCP.Lang.HadamardRow
