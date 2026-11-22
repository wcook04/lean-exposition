/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryFieldLang
import PCP.Complexity.LangRenaming

/-!
# Numeric polynomial coefficients in the counted-loop language

The coefficient routine reads a degree, a numeric lower-coefficient mask, and an
index. It agrees exactly with the finite irreducible-polynomial search semantics
and has a proved charged cost bound. Out-of-range indices return before the loop.
The stored finite convolution program also has exact operational semantics; its
cost and the outer irreducible-polynomial search are developed separately.
-/

namespace PCP.Lang.BinaryPolynomialCoefficient

open PCP.Algebraic

def value (d code k : ℕ) : ℕ :=
  if k < d then code / 2 ^ k % 2 else if k = d then 1 else 0

theorem coefficient_value (d : ℕ) (code : Fin (2 ^ d)) (k : ℕ) :
    (BinaryIrreduciblePolynomial.coefficient d code k).val = value d code.val k := by
  by_cases hk : k < d
  · simp only [BinaryIrreduciblePolynomial.coefficient, hk, dite_eq_left, value, ite_eq_left]
    rfl
  · by_cases hkd : k = d
    · simp [BinaryIrreduciblePolynomial.coefficient, hkd, value,
        show (1 : ZMod 2).val = 1 from rfl]
    · simp [BinaryIrreduciblePolynomial.coefficient, hk, hkd, value]

def powerBody : Stmt 8 2 := .assign 5 (.mul 5 6)

theorem powerBody_run (st : State 8 2) :
    (powerBody.run st).1.regs 5 = st.regs 5 * st.regs 6 := by
  simp [powerBody, Stmt.run, Expr.eval]

theorem power_iterate (n c : ℕ) (st : State 8 2) (h2 : st.regs 6 = 2) :
    (iterate powerBody.run c n st).1.regs 5 = st.regs 5 * 2 ^ n := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate_succ_fst, ih _ (by simpa [powerBody, Stmt.run, Function.update] using h2)]
    rw [powerBody_run, h2, pow_succ]
    ring

/-- Extract a lower coefficient using a bounded power-of-two divisor. -/
def lower : Stmt 8 2 :=
  .seq (.assign 5 (.const 1)) (.seq (.assign 6 (.const 2))
    (.seq (.loop 2 powerBody) (.seq (.assign 3 (.div 1 5)) (.assign 3 (.mod 3 6)))))

/-- Degree, numeric mask and requested exponent are in registers 0, 1, 2.
The coefficient is returned in register 3. Large out-of-range exponents do not enter the loop. -/
def coefficient : Stmt 8 2 :=
  .seq (.assign 4 (.lt 2 0)) (.ite 4 lower (.assign 3 (.eq 2 0)))

theorem coefficient_run (st : State 8 2) :
    (coefficient.run st).1.regs 3 = value (st.regs 0) (st.regs 1) (st.regs 2) := by
  let s := setReg st 4 (if st.regs 2 < st.regs 0 then 1 else 0)
  have hs0 : s.regs 0 = st.regs 0 := by simp [s, Function.update]
  have hs1 : s.regs 1 = st.regs 1 := by simp [s, Function.update]
  have hs2 : s.regs 2 = st.regs 2 := by simp [s, Function.update]
  have hs4 : s.regs 4 = if st.regs 2 < st.regs 0 then 1 else 0 := by simp [s]
  change ((Stmt.ite 4 _ _).run s).1.regs 3 = _
  rw [run_ite_fst, hs4]
  by_cases hk : st.regs 2 < st.regs 0
  · simp only [hk, ite_eq_left]
    let u := setReg (setReg s 5 1) 6 2
    have h2 : u.regs 2 = st.regs 2 := by simp [u, Function.update, hs2]
    have h1 : u.regs 1 = st.regs 1 := by simp [u, Function.update, hs1]
    have h6 : u.regs 6 = 2 := by simp [u]
    have h5 : u.regs 5 = 1 := by simp [u, Function.update]
    let z := (iterate powerBody.run (Nat.size (st.regs 2) + 1) (st.regs 2) u).1
    have hz5 : z.regs 5 = 2 ^ st.regs 2 := by
      simpa only [h5, one_mul] using power_iterate (st.regs 2) _ u h6
    have hz1 : z.regs 1 = st.regs 1 :=
      (iterate_frame powerBody.run _ (fun z => z.regs 1 = st.regs 1)
        (fun z hz => (run_regs_frame powerBody 1 (by decide) z).trans hz) _ u h1)
    have hz6 : z.regs 6 = 2 :=
      (iterate_frame powerBody.run _ (fun z => z.regs 6 = 2)
        (fun z hz => (run_regs_frame powerBody 6 (by decide) z).trans hz) _ u h6)
    simp only [lower, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst]
    change (setReg (setReg z 3 (z.regs 1 / z.regs 5)) 3
      ((setReg z 3 (z.regs 1 / z.regs 5)).regs 3 %
        (setReg z 3 (z.regs 1 / z.regs 5)).regs 6)).regs 3 = _
    simp [Function.update, hz1, hz5, hz6, value, hk]
  · simp [hk, Stmt.run, Expr.eval, Function.update, value, s]


theorem powerBody_cost (st : State 8 2) (Q : ℕ) (h5 : st.regs 5 ≤ Q)
    (h6 : st.regs 6 = 2) (hprod : st.regs 5 * 2 ≤ Q) :
    (powerBody.run st).2 ≤ 2 * Q + 3 := by
  have hs5 : Nat.size (st.regs 5) ≤ Q := (size_le_self _).trans h5
  have hsprod : Nat.size (st.regs 5 * 2) ≤ Q := (size_le_self _).trans hprod
  simpa [powerBody, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, h6,
    show Nat.size 2 = 2 by decide] using
    (show Nat.size (st.regs 5) + 2 + Nat.size (st.regs 5 * 2) + 1 ≤ 2 * Q + 3 by omega)

theorem power_iterate_cost (k d c : ℕ) (st : State 8 2) (hkd : k ≤ d)
    (h5 : st.regs 5 = 1) (h6 : st.regs 6 = 2) :
    (iterate powerBody.run c k st).2 ≤ k * (c + 2 * 2 ^ d + 3) := by
  have h := iterate_cost_idx powerBody.run c (2 * 2 ^ d + 3) k
    (fun j s => s.regs 5 = 2 ^ j ∧ s.regs 6 = 2)
    (by
      intro j s hj hs
      refine ⟨?_, ?_⟩
      · simp [powerBody, Stmt.run, Expr.eval, Function.update, hs.1, hs.2, pow_succ]
      · refine powerBody_cost s (2 ^ d) ?_ hs.2 ?_
        · rw [hs.1]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        · rw [hs.1, ← pow_succ]
          exact Nat.pow_le_pow_right (by decide) (by omega)) st
    (by simpa using And.intro h5 h6)
  simpa [Nat.add_assoc] using h


theorem lower_cost (st : State 8 2) (d : ℕ) (hk : st.regs 2 ≤ d)
    (hcode : st.regs 1 < 2 ^ d) : (lower.run st).2 ≤ 20 * (2 ^ d + 1) ^ 2 := by
  let Q := 2 ^ d
  let k := st.regs 2
  let u := setReg (setReg st 5 1) 6 2
  have hu2 : u.regs 2 = k := by simp [u, k, Function.update]
  have hu1 : u.regs 1 = st.regs 1 := by simp [u, Function.update]
  have hu6 : u.regs 6 = 2 := by simp [u]
  have hu5 : u.regs 5 = 1 := by simp [u, Function.update]
  let z := (iterate powerBody.run (Nat.size k + 1) k u).1
  have hz5 : z.regs 5 = 2 ^ k := by
    simpa only [hu5, one_mul] using power_iterate k _ u hu6
  have hz1 : z.regs 1 = st.regs 1 :=
    iterate_frame powerBody.run _ (fun z => z.regs 1 = st.regs 1)
      (fun z hz => (run_regs_frame powerBody 1 (by decide) z).trans hz) _ u hu1
  have hz6 : z.regs 6 = 2 :=
    iterate_frame powerBody.run _ (fun z => z.regs 6 = 2)
      (fun z hz => (run_regs_frame powerBody 6 (by decide) z).trans hz) _ u hu6
  have hloop := power_iterate_cost k d (Nat.size k + 1) u hk hu5 hu6
  have hd : d ≤ Q := (Nat.lt_two_pow_self (n := d)).le
  have hkQ : k ≤ Q := hk.trans hd
  have hsk : Nat.size k ≤ Q := (size_le_self _).trans hkQ
  have hsCode : Nat.size (st.regs 1) ≤ Q := (size_le_self _).trans hcode.le
  have hsPow : Nat.size (2 ^ k) ≤ Q := (size_le_self _).trans
    (Nat.pow_le_pow_right (by decide) hk)
  have hsDiv : Nat.size (st.regs 1 / 2 ^ k) ≤ Q := (size_le_self _).trans
    ((Nat.div_le_self _ _).trans hcode.le)
  have hsMod : Nat.size ((st.regs 1 / 2 ^ k) % 2) ≤ 1 := size_le_one_of_le_one (by omega)
  simp only [lower, run_seq_snd, run_assign_fst, Expr.eval, run_loop_snd, run_loop_fst]
  change (Expr.const 1).cost st.regs + ((Expr.const 2).cost _ +
    ((iterate powerBody.run (Nat.size k + 1) k u).2 + Nat.size k + 1 +
      ((Expr.div 1 5).cost z.regs +
        (Expr.mod 3 6).cost (setReg z 3 (z.regs 1 / z.regs 5)).regs + 1) + 1) + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setReg_regs, Function.update_self,
    Function.update_of_ne (by decide : (6 : Fin 8) ≠ 3), hz1, hz5, hz6,
    show Nat.size 1 = 1 from rfl, show Nat.size 2 = 2 by decide]
  have hmul : k * (Nat.size k + 1 + 2 * Q + 3) ≤ Q * (3 * Q + 4) :=
    Nat.mul_le_mul hkQ (by omega)
  have hQ : 1 ≤ Q := by
    have hp : 0 < Q := by dsimp [Q]; positivity
    omega
  have hl : (iterate powerBody.run (Nat.size k + 1) k u).2 ≤ Q * (3 * Q + 4) :=
    hloop.trans hmul
  change _ ≤ 20 * (Q + 1) ^ 2
  nlinarith


/-- The coefficient routine is polynomial in the field cardinality and index bit length;
out-of-range binary indices never control a loop. -/
theorem coefficient_cost (st : State 8 2) (hcode : st.regs 1 < 2 ^ st.regs 0) :
    (coefficient.run st).2 ≤ 30 * (2 ^ st.regs 0 + Nat.size (st.regs 2) + 1) ^ 2 := by
  let Q := 2 ^ st.regs 0
  let K := Nat.size (st.regs 2)
  let s := setReg st 4 (if st.regs 2 < st.regs 0 then 1 else 0)
  have hs0 : s.regs 0 = st.regs 0 := by simp [s, Function.update]
  have hs1 : s.regs 1 = st.regs 1 := by simp [s, Function.update]
  have hs2 : s.regs 2 = st.regs 2 := by simp [s, Function.update]
  have hs4 : s.regs 4 = if st.regs 2 < st.regs 0 then 1 else 0 := by simp [s]
  have hd : Nat.size (st.regs 0) ≤ Q :=
    (size_le_self _).trans (Nat.lt_two_pow_self (n := st.regs 0)).le
  have hflag : Nat.size (s.regs 4) ≤ 1 := by
    rw [hs4]
    split_ifs <;> decide
  have hguard : (Expr.lt 2 0).cost st.regs ≤ K + Q + 2 := by
    unfold Expr.cost Expr.readSize Expr.eval
    have hs := hflag
    rw [hs4] at hs
    change K + Nat.size (st.regs 0) + Nat.size (if st.regs 2 < st.regs 0 then 1 else 0) + 1 ≤ _
    omega
  have hbranch : (if s.regs 4 ≠ 0 then (lower.run s).2
      else ((Stmt.assign 3 (.eq 2 0)).run s).2) ≤ 20 * (Q + K + 1) ^ 2 := by
    by_cases hk : st.regs 2 < st.regs 0
    · have hl := lower_cost s (st.regs 0) (by simpa only [hs2] using hk.le)
        (by simpa only [hs1] using hcode)
      rw [hs4, ite_eq_left hk]
      exact hl.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    · rw [hs4, ite_eq_right hk]
      simp only [ne_eq, not_true_eq_false, ite_false]
      change (Expr.eq 2 0).cost s.regs ≤ _
      have heqsz : Nat.size (if s.regs 2 = s.regs 0 then 1 else 0) ≤ 1 := by
        split_ifs <;> decide
      simp only [Expr.cost, Expr.readSize, Expr.eval]
      rw [hs2, hs0] at heqsz ⊢
      change K + Nat.size (st.regs 0) + Nat.size (if st.regs 2 = st.regs 0 then 1 else 0) + 1 ≤ _
      nlinarith
  rw [coefficient, run_seq_snd, run_assign_fst, run_ite_snd]
  change (Expr.lt 2 0).cost st.regs +
    ((if s.regs 4 ≠ 0 then (lower.run s).2 else ((Stmt.assign 3 (.eq 2 0)).run s).2) +
      Nat.size (s.regs 4) + 1) + 1 ≤ _
  change _ ≤ 30 * (Q + K + 1) ^ 2
  nlinarith


/-- Natural coefficient convolution, reduced modulo two. -/
def convolution (d e j k n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range (n + 1), value d j i * value e k (n - i)) % 2

def regEmbedding : Fin 8 → Fin 20 := Fin.castLE (by decide)

theorem regEmbedding_injective : Function.Injective regEmbedding := Fin.castLE_injective _

def coefficient20 : Stmt 20 2 := coefficient.rename regEmbedding id

theorem coefficient20_run (st : State 20 2) :
    (coefficient20.run st).1.regs 3 = value (st.regs 0) (st.regs 1) (st.regs 2) := by
  have h := congrArg (fun z : State 8 2 × ℕ => z.1.regs 3)
    (coefficient.run_rename regEmbedding id regEmbedding_injective Function.injective_id st)
  exact h.trans (coefficient_run _)

def leftCoefficient : Stmt 20 2 :=
  .seq (.assign 0 (.var 8)) (.seq (.assign 1 (.var 10))
    (.seq (.assign 2 (.var 14)) (.seq coefficient20 (.assign 17 (.var 3)))))

def rightCoefficient : Stmt 20 2 :=
  .seq (.assign 0 (.var 9)) (.seq (.assign 1 (.var 11))
    (.seq (.assign 2 (.sub 12 14)) coefficient20))

theorem leftCoefficient_run (st : State 20 2) :
    (leftCoefficient.run st).1.regs 17 = value (st.regs 8) (st.regs 10) (st.regs 14) := by
  simp only [leftCoefficient, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  rw [coefficient20_run]
  simp [Function.update]

theorem rightCoefficient_run (st : State 20 2) :
    (rightCoefficient.run st).1.regs 3 =
      value (st.regs 9) (st.regs 11) (st.regs 12 - st.regs 14) := by
  simp only [rightCoefficient, run_seq_fst, run_assign_fst, Expr.eval]
  rw [coefficient20_run]
  simp [Function.update]

def convolutionTail : Stmt 20 2 :=
  .seq (.assign 3 (.mul 17 3)) (.seq (.assign 13 (.add 13 3))
    (.seq (.assign 13 (.mod 13 16)) (.assign 14 (.add 14 15))))

def convolutionBody : Stmt 20 2 :=
  .seq leftCoefficient (.seq rightCoefficient convolutionTail)

theorem convolutionBody_step (st : State 20 2) (h1 : st.regs 15 = 1) (h2 : st.regs 16 = 2) :
    (convolutionBody.run st).1.regs 13 =
      (st.regs 13 + value (st.regs 8) (st.regs 10) (st.regs 14) *
        value (st.regs 9) (st.regs 11) (st.regs 12 - st.regs 14)) % 2 ∧
    (convolutionBody.run st).1.regs 14 = st.regs 14 + 1 := by
  let s := (leftCoefficient.run st).1
  let u := (rightCoefficient.run s).1
  have hs17 : s.regs 17 = value (st.regs 8) (st.regs 10) (st.regs 14) := leftCoefficient_run st
  have hu3 : u.regs 3 = value (st.regs 9) (st.regs 11) (st.regs 12 - st.regs 14) := by
    rw [rightCoefficient_run]
    rw [run_regs_frame leftCoefficient 9 (by decide),
      run_regs_frame leftCoefficient 11 (by decide),
      run_regs_frame leftCoefficient 12 (by decide),
      run_regs_frame leftCoefficient 14 (by decide)]
  have hu17 : u.regs 17 = value (st.regs 8) (st.regs 10) (st.regs 14) :=
    (run_regs_frame rightCoefficient 17 (by decide) s).trans hs17
  have hu13 : u.regs 13 = st.regs 13 := (run_regs_frame rightCoefficient 13 (by decide) s).trans
    (run_regs_frame leftCoefficient 13 (by decide) st)
  have hu14 : u.regs 14 = st.regs 14 := (run_regs_frame rightCoefficient 14 (by decide) s).trans
    (run_regs_frame leftCoefficient 14 (by decide) st)
  have hu15 : u.regs 15 = 1 := (run_regs_frame rightCoefficient 15 (by decide) s).trans
    ((run_regs_frame leftCoefficient 15 (by decide) st).trans h1)
  have hu16 : u.regs 16 = 2 := (run_regs_frame rightCoefficient 16 (by decide) s).trans
    ((run_regs_frame leftCoefficient 16 (by decide) st).trans h2)
  dsimp only [u, s] at hu3 hu17 hu13 hu14 hu15 hu16
  simp only [convolutionBody, convolutionTail, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update, Fin.reduceEq, dite_true, dite_false, hu3, hu17, hu13, hu14, hu15, hu16,
    and_self]


def ConvolutionInv (d e j k n z : ℕ) (st : State 20 2) : Prop :=
  st.regs 8 = d ∧ st.regs 9 = e ∧ st.regs 10 = j ∧ st.regs 11 = k ∧ st.regs 12 = n ∧
  st.regs 14 = z ∧ st.regs 15 = 1 ∧ st.regs 16 = 2 ∧
  st.regs 13 = (∑ i ∈ Finset.range z, value d j i * value e k (n - i)) % 2

theorem convolutionBody_inv (d e j k n z : ℕ) (st : State 20 2)
    (h : ConvolutionInv d e j k n z st) :
    ConvolutionInv d e j k n (z + 1) (convolutionBody.run st).1 := by
  obtain ⟨h8, h9, h10, h11, h12, h14, h15, h16, h13⟩ := h
  obtain ⟨hz13, hz14⟩ := convolutionBody_step st h15 h16
  refine ⟨(run_regs_frame convolutionBody 8 (by decide) st).trans h8,
    (run_regs_frame convolutionBody 9 (by decide) st).trans h9,
    (run_regs_frame convolutionBody 10 (by decide) st).trans h10,
    (run_regs_frame convolutionBody 11 (by decide) st).trans h11,
    (run_regs_frame convolutionBody 12 (by decide) st).trans h12,
    hz14.trans (by rw [h14]),
    (run_regs_frame convolutionBody 15 (by decide) st).trans h15,
    (run_regs_frame convolutionBody 16 (by decide) st).trans h16, ?_⟩
  rw [hz13, h8, h9, h10, h11, h12, h14, h13, Finset.sum_range_succ]
  omega

def convolutionProgram : Stmt 20 2 :=
  .seq (.assign 13 (.const 0)) (.seq (.assign 14 (.const 0))
    (.seq (.assign 15 (.const 1)) (.seq (.assign 16 (.const 2))
      (.seq (.assign 18 (.add 12 15)) (.loop 18 convolutionBody)))))

theorem convolution_run (st : State 20 2) :
    (convolutionProgram.run st).1.regs 13 =
      convolution (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) (st.regs 12) := by
  let n := st.regs 12
  let s := setReg (setReg (setReg (setReg (setReg st 13 0) 14 0) 15 1) 16 2) 18 (n + 1)
  have hinit : ConvolutionInv (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) n 0 s := by
    simp [ConvolutionInv, s, n, Function.update]
  have h := iterate_inv convolutionBody.run (Nat.size (n + 1) + 1) (n + 1)
    (ConvolutionInv (st.regs 8) (st.regs 9) (st.regs 10) (st.regs 11) n)
    (fun z u _ hu => convolutionBody_inv _ _ _ _ _ z u hu) s hinit
  have hfinal := h.2.2.2.2.2.2.2.2
  simp only [convolutionProgram, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update_self]
  simp only [Function.update, Fin.reduceEq, dite_true, dite_false]
  exact hfinal

theorem convolution_value (d e : ℕ) (j : Fin (2 ^ d)) (k : Fin (2 ^ e)) (n : ℕ) :
    convolution d e j.val k.val n =
      (∑ ab ∈ Finset.antidiagonal n,
        BinaryIrreduciblePolynomial.coefficient d j ab.1 *
          BinaryIrreduciblePolynomial.coefficient e k ab.2).val := by
  have hcast : (convolution d e j.val k.val n : ZMod 2) =
      ∑ i ∈ Finset.range (n + 1), BinaryIrreduciblePolynomial.coefficient d j i *
        BinaryIrreduciblePolynomial.coefficient e k (n - i) := by
    simp only [convolution, ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul]
    simp_rw [← coefficient_value d j, ← coefficient_value e k]
    simp
  have hval := congrArg ZMod.val hcast
  simp only [ZMod.val_natCast, convolution, Nat.mod_mod] at hval
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact hval

end PCP.Lang.BinaryPolynomialCoefficient
