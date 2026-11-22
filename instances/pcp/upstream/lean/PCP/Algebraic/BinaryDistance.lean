/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialDistance
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.ZMod.Basic

/-!
# Distance of binary multilinear polynomials

The binary branch of Theorem 2.5: a nonzero multilinear polynomial of total degree
at most `d` is nonzero on at least a `2⁻ᵈ` fraction of the Boolean cube.

The proof inducts on the number of variables. If the first variable does not occur,
each nonzero evaluation of the constant coefficient has two extensions. Otherwise,
each nonzero evaluation of the linear coefficient has at least one nonzero extension,
and that coefficient has strictly smaller total degree.
-/

namespace PCP.Algebraic

open Finset MvPolynomial

/-- Every variable has individual degree at most one. This is a property of a formal polynomial. -/
def IsMultilinear {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

theorem IsMultilinear.sub {σ R : Type*} [CommRing R] {p q : MvPolynomial σ R}
    (hp : IsMultilinear p) (hq : IsMultilinear q) : IsMultilinear (p - q) := by
  intro i
  exact (degreeOf_sub_le i p q).trans (max_le (hp i) (hq i))

variable {m d : ℕ}

/-- Dropping a variable preserves multilinearity in every coefficient. -/
theorem IsMultilinear.coeff_finSuccEquiv {R : Type*} [CommSemiring R]
    {p : MvPolynomial (Fin (m + 1)) R} (hp : IsMultilinear p) (k : ℕ) :
    IsMultilinear ((finSuccEquiv R m p).coeff k) := by
  intro i
  exact (degreeOf_coeff_finSuccEquiv p i k).trans (hp i.succ)

private theorem nonzero_count_of_degreeOf_zero (p : MvPolynomial (Fin (m + 1)) (ZMod 2))
    (h : p.degreeOf 0 = 0) :
    #{x | eval x p ≠ 0} = 2 * #{x | eval x ((finSuccEquiv (ZMod 2) m p).coeff 0) ≠ 0} := by
  have heval (x : Fin (m + 1) → ZMod 2) :
      eval x p = eval (Fin.tail x) ((finSuccEquiv (ZMod 2) m p).coeff 0) := by
    conv_lhs => rw [← Fin.cons_self_tail x, eval_eq_eval_mv_eval']
    rw [Polynomial.eq_C_of_natDegree_eq_zero ((natDegree_finSuccEquiv p).trans h)]
    simp
  simp_rw [heval]
  simpa [Fin.tail_def] using
    card_consEquiv_filter_piFinset (fun _ : Fin (m + 1) => (univ : Finset (ZMod 2)))
    (fun x => eval x ((finSuccEquiv (ZMod 2) m p).coeff 0) ≠ 0)

private theorem nonzero_count_coeff_one_le (p : MvPolynomial (Fin (m + 1)) (ZMod 2))
    (h : p.degreeOf 0 ≤ 1) :
    #{x | eval x ((finSuccEquiv (ZMod 2) m p).coeff 1) ≠ 0} ≤ #{x | eval x p ≠ 0} := by
  let q := (finSuccEquiv (ZMod 2) m p).coeff 1
  let r := (finSuccEquiv (ZMod 2) m p).coeff 0
  have heval (a : ZMod 2) (x : Fin m → ZMod 2) :
      eval (Fin.cons a x) p = eval x q * a + eval x r := by
    rw [eval_eq_eval_mv_eval', Polynomial.eq_X_add_C_of_natDegree_le_one
      ((natDegree_finSuccEquiv p).trans_le h)]
    simp [q, r]
  let extend (x : Fin m → ZMod 2) : Fin (m + 1) → ZMod 2 :=
    Fin.cons (if eval x r = 0 then 1 else 0) x
  apply card_le_card_of_injOn extend
  · intro x hx
    have hxq : eval x q ≠ 0 := (mem_filter.mp hx).2
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    dsimp only [extend]
    rw [heval]
    by_cases hxr : eval x r = 0 <;> simp [hxr, hxq]
  · intro x _ y _ hxy
    simpa [extend] using congrArg Fin.tail hxy

/-- A division-free form of the binary minimum-weight bound. -/
theorem two_pow_le_nonzero_count_mul (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : IsMultilinear p) (hne : p ≠ 0) :
    2 ^ m ≤ #{x | eval x p ≠ 0} * 2 ^ p.totalDegree := by
  induction m with
  | zero =>
      rw [p.eq_C_of_isEmpty] at *
      simp [C_ne_zero.mp hne]
  | succ m ih =>
      let p' := finSuccEquiv (ZMod 2) m p
      let k := p'.natDegree
      let q := p'.coeff k
      have hp' : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hne
      have hq : q ≠ 0 := by
        change p'.leadingCoeff ≠ 0
        exact Polynomial.leadingCoeff_ne_zero.mpr hp'
      have hqdeg : q.totalDegree + k ≤ p.totalDegree :=
        totalDegree_coeff_finSuccEquiv_add_le p k hq
      have hqmulti : IsMultilinear q := hp.coeff_finSuccEquiv k
      have hind := ih q hqmulti hq
      have hk : k ≤ 1 := (natDegree_finSuccEquiv p).trans_le (hp 0)
      have hpower : 2 ^ (q.totalDegree + k) ≤ 2 ^ p.totalDegree :=
        Nat.pow_le_pow_right (by decide) hqdeg
      have hdouble := Nat.mul_le_mul_left 2 hind
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with hk | hk
      · have hz : p.degreeOf 0 = 0 := (natDegree_finSuccEquiv p).symm.trans hk
        have hcount := nonzero_count_of_degreeOf_zero p hz
        have hcount' : #{x | eval x p ≠ 0} = 2 * #{x | eval x q ≠ 0} := by
          simpa only [q, hk, p'] using hcount
        rw [hk, Nat.add_zero] at hpower
        calc
          2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
          _ ≤ 2 * (#{x | eval x q ≠ 0} * 2 ^ q.totalDegree) := hdouble
          _ = #{x | eval x p ≠ 0} * 2 ^ q.totalDegree := by rw [hcount', mul_assoc]
          _ ≤ #{x | eval x p ≠ 0} * 2 ^ p.totalDegree := Nat.mul_le_mul_left _ hpower
      · have hcount := nonzero_count_coeff_one_le p (hp 0)
        have hcount' : #{x | eval x q ≠ 0} ≤ #{x | eval x p ≠ 0} := by
          simpa only [q, hk, p'] using hcount
        rw [hk] at hpower
        calc
          2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
          _ ≤ 2 * (#{x | eval x q ≠ 0} * 2 ^ q.totalDegree) := hdouble
          _ = #{x | eval x q ≠ 0} * 2 ^ (q.totalDegree + 1) := by rw [pow_succ]; ac_rfl
          _ ≤ #{x | eval x p ≠ 0} * 2 ^ p.totalDegree := Nat.mul_le_mul hcount' hpower

/-- Theorem 2.5 (binary branch), with rational probability normalization. -/
theorem binary_eval_distance_zero_ge (p : MvPolynomial (Fin m) (ZMod 2))
    (hmulti : IsMultilinear p) (hdeg : p.totalDegree ≤ d) (hne : p ≠ 0) :
    (1 : ℚ) / 2 ^ d ≤ relativeDistance (fun x => eval x p) 0 := by
  have hcount : (2 : ℚ) ^ m ≤ (#{x | eval x p ≠ 0} : ℚ) * 2 ^ d := by
    exact_mod_cast (two_pow_le_nonzero_count_mul p hmulti hne).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hdeg))
  change (1 : ℚ) / 2 ^ d ≤ (#{x | eval x p ≠ 0} : ℚ) / Fintype.card (Fin m → ZMod 2)
  rw [Fintype.card_pi_const, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hcount

/-- Distinct binary multilinear polynomials of degree at most `d` have distance at least `2⁻ᵈ`. -/
theorem binary_eval_distance_ge (p q : MvPolynomial (Fin m) (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (hpdeg : p.totalDegree ≤ d) (hqdeg : q.totalDegree ≤ d) (hne : p ≠ q) :
    (1 : ℚ) / 2 ^ d ≤ relativeDistance (fun x => eval x p) (fun x => eval x q) := by
  have h := binary_eval_distance_zero_ge (p - q) (hp.sub hq)
    ((totalDegree_sub p q).trans (max_le hpdeg hqdeg)) (sub_ne_zero.mpr hne)
  simpa [relativeDistance, hammingDist, eval_sub, sub_ne_zero] using h

/-- Multilinear formal polynomials over `𝔽₂` are determined by their evaluation functions. -/
theorem binary_eval_injective :
    Set.InjOn (fun p : MvPolynomial (Fin m) (ZMod 2) => fun x => eval x p)
      {p | IsMultilinear p} := by
  intro p hp q hq heval
  dsimp only at heval
  by_contra hne
  have h := binary_eval_distance_ge p q hp hq (Nat.le_max_left _ _) (Nat.le_max_right _ _) hne
  rw [heval, relativeDistance_self] at h
  have hpos : (0 : ℚ) < 1 / 2 ^ max p.totalDegree q.totalDegree := by positivity
  linarith

/-- The unique-decoding radius for binary multilinear polynomials is strictly below `2⁻⁽ᵈ⁺¹⁾`. -/
theorem eq_of_binary_eval_close (p q : MvPolynomial (Fin m) (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (hpdeg : p.totalDegree ≤ d) (hqdeg : q.totalDegree ≤ d)
    {w : (Fin m → ZMod 2) → ZMod 2} {ε : ℚ}
    (hradius : 2 * ε < (1 : ℚ) / 2 ^ d)
    (hwp : relativeDistance w (fun x => eval x p) ≤ ε)
    (hwq : relativeDistance w (fun x => eval x q) ≤ ε) : p = q := by
  by_contra hne
  have hlow := binary_eval_distance_ge p q hp hq hpdeg hqdeg hne
  have htriangle := relativeDistance_triangle (fun x => eval x p) w (fun x => eval x q)
  rw [relativeDistance_comm (fun x => eval x p) w] at htriangle
  linarith

end PCP.Algebraic
