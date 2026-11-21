/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialFactorCost
import PCP.Complexity.LangBooleanLoops

/-!
# Scanning all factor masks with stored numeric counters

At a fixed factor degree `d`, each number below `2^t` encodes both factors:
its low `d` bits are the first mask and the remaining bits are the second.
Thus one counted loop enumerates every monic factor pair exactly once.
-/

namespace PCP.Lang.BinaryPolynomialMaskScan

open PCP.Algebraic BinaryPolynomialCoefficient BinaryPolynomialFactor BooleanLoops

def factorEmbedding : Fin 24 → Fin 32 := Fin.castLE (by decide)
def factor32 : Stmt 32 2 := matchProduct.rename factorEmbedding id

set_option maxHeartbeats 800000 in
-- The register transport traverses the complete nested coefficient program.
theorem factor32_run (st : State 32 2) :
    (factor32.run st).1.regs 22 = truth (MatchesPrefix (st.regs 20) (st.regs 21)
      (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) (st.regs 20 + 1)) := by
  have h := congrArg (fun z : State 24 2 × ℕ => z.1.regs 22)
    (matchProduct.run_rename factorEmbedding id (Fin.castLE_injective _)
      Function.injective_id st)
  exact h.trans (matches_run _)

def maskPrepare : Stmt 32 2 :=
  .seq (.assign 10 (.mod 25 29)) (.assign 11 (.div 25 29))

def maskTail : Stmt 32 2 :=
  .seq (.assign 3 (.sub 30 22))
    (.seq (.assign 27 (.mul 27 3)) (.assign 25 (.add 25 30)))

def maskBody : Stmt 32 2 := .seq maskPrepare (.seq factor32 maskTail)

def NoFactor (t code d e width i : ℕ) : Prop :=
  ¬ MatchesPrefix t code d e (i % width) (i / width) (t + 1)

instance (t code d e width i : ℕ) : Decidable (NoFactor t code d e width i) :=
  inferInstanceAs (Decidable (¬ MatchesPrefix t code d e (i % width) (i / width) (t + 1)))

def Context (t code d e q width : ℕ) (st : State 32 2) : Prop :=
  st.regs 20 = t ∧ st.regs 21 = code ∧ st.regs 8 = d ∧ st.regs 9 = e ∧
    st.regs 28 = q ∧ st.regs 29 = width ∧ st.regs 30 = 1

theorem maskBody_step (st : State 32 2) (h30 : st.regs 30 = 1) :
    (maskBody.run st).1.regs 27 = st.regs 27 * truth
      (NoFactor (st.regs 20) (st.regs 21) (st.regs 8) (st.regs 9)
        (st.regs 29) (st.regs 25)) ∧
      (maskBody.run st).1.regs 25 = st.regs 25 + 1 := by
  let p := setReg (setReg st 10 (st.regs 25 % st.regs 29)) 11
    (st.regs 25 / st.regs 29)
  have hp : (maskPrepare.run st).1 = p := rfl
  have hs22 := factor32_run p
  have hs25 := run_regs_frame factor32 25 (by decide) p
  have hs27 := run_regs_frame factor32 27 (by decide) p
  have hs30 := run_regs_frame factor32 30 (by decide) p
  simp only [maskBody, run_seq_fst, hp]
  generalize hs : (factor32.run p).1 = s at *
  simp only [p, setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    h30] at hs22 hs25 hs27 hs30
  simp only [maskTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    hs22, hs25, hs27, hs30]
  unfold NoFactor truth
  split_ifs <;> simp_all

theorem maskBody_frame (st : State 32 2) (r : Fin 32)
    (hr : r ∈ ([20, 21, 8, 9, 28, 29, 30] : List (Fin 32))) :
    (maskBody.run st).1.regs r = st.regs r := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem maskBody_context (t code d e q width : ℕ) (st : State 32 2)
    (h : Context t code d e q width st) : Context t code d e q width (maskBody.run st).1 := by
  unfold Context at h ⊢
  rw [maskBody_frame st 20 (by decide), maskBody_frame st 21 (by decide),
    maskBody_frame st 8 (by decide), maskBody_frame st 9 (by decide),
    maskBody_frame st 28 (by decide), maskBody_frame st 29 (by decide),
    maskBody_frame st 30 (by decide)]
  exact h

/-- Multiply the incoming flag by the universal no-factor test at one degree. -/
def maskScan : Stmt 32 2 := .seq (.assign 25 (.const 0)) (.loop 28 maskBody)

theorem maskScan_run (t code d e q width : ℕ) (st : State 32 2)
    (h : Context t code d e q width st) :
    (maskScan.run st).1.regs 27 =
      st.regs 27 * truth (AllBelow (NoFactor t code d e width) q) := by
  let s := setReg st 25 0
  have hi : Context t code d e q width s := by
    simpa [Context, s, Function.update] using h
  have hit := iterate_all maskBody.run (Nat.size q + 1) q 25 27
    (Context t code d e q width) (NoFactor t code d e width)
    (by
      intro n u _ hu hn
      obtain ⟨hf, hj⟩ := maskBody_step u hu.2.2.2.2.2.2
      refine ⟨maskBody_context _ _ _ _ _ _ u hu, hj.trans (by rw [hn]), ?_⟩
      simpa only [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1,
        hu.2.2.2.2.2.1, hn] using hf) s hi (by simp [s])
  simp only [maskScan, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst]
  simpa only [s, setReg_regs, Function.update_of_ne (by decide : (28 : Fin 32) ≠ 25),
    Function.update_of_ne (by decide : (27 : Fin 32) ≠ 25), h.2.2.2.2.1] using hit.2.2

/-- The numeric pair enumeration agrees with the semantic finite factor test. -/
theorem allBelow_noFactor_iff (t : ℕ) (code : Fin (2 ^ t)) (d : ℕ) (hd : d ≤ t) :
    AllBelow (NoFactor t code.val d (t - d) (2 ^ d)) (2 ^ t) ↔
      ∀ j : Fin (2 ^ d), ∀ k : Fin (2 ^ (t - d)),
        ¬ BinaryIrreduciblePolynomial.ProductMatches t code d j k := by
  have hpow : 2 ^ t = 2 ^ d * 2 ^ (t - d) := by rw [← pow_add, Nat.add_sub_of_le hd]
  constructor
  · intro h j k
    have hn : j.val + 2 ^ d * k.val < 2 ^ t := by
      rw [hpow]
      have hmul := Nat.mul_le_mul_left (2 ^ d) k.isLt
      nlinarith [j.isLt]
    have hh := h (j.val + 2 ^ d * k.val) (Finset.mem_range.mpr hn)
    have hmod : (j.val + 2 ^ d * k.val) % 2 ^ d = j.val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
    have hdiv : (j.val + 2 ^ d * k.val) / 2 ^ d = k.val := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt j.isLt]
      omega
    simpa only [NoFactor, hmod, hdiv, matchesPrefix_iff] using hh
  · intro h n hn
    have hn' : n < 2 ^ t := Finset.mem_range.mp hn
    have hj : n % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
    have hk : n / 2 ^ d < 2 ^ (t - d) := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      simpa only [Nat.mul_comm] using hpow ▸ hn'
    exact (matchesPrefix_iff t code d ⟨_, hj⟩ ⟨_, hk⟩).not.mpr (h _ _)

end PCP.Lang.BinaryPolynomialMaskScan
