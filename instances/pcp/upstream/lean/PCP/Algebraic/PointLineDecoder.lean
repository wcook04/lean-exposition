/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineTest
import PCP.Algebraic.UnivariateDistance
import Mathlib.Data.Nat.Find

/-!
# Nearest polynomial decoding of parametrized lines

Every word on a finite field has a best approximating polynomial of any given
degree bound. Existence follows by minimizing the natural-number disagreement
count, with the zero polynomial supplying a candidate. Applying this choice on
each parametrized line produces a lines table with minimum rejection among all
degree-bounded lines tables.

The root bound gives uniqueness below half the polynomial distance, and ensures
that a line decoder agrees with a known global polynomial whenever their line
error is below that radius. No assumption asserts the existence of a decoder,
and the classical construction makes no efficiency claim.
-/

namespace PCP.Algebraic.PointLineTest

open Finset PolynomialLine

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F] {c : ℕ}

/-- Distinct degree-bounded univariate polynomials have the usual root-count distance. -/
theorem univariate_distance_ge (p q : Polynomial F)
    (hp : p.natDegree ≤ c) (hq : q.natDegree ≤ c) (hne : p ≠ q) :
    1 - (c : ℚ) / Fintype.card F ≤ relativeDistance p.eval q.eval := by
  have h := UnivariateDistance.eval_distance_zero_ge (p - q)
    (Polynomial.natDegree_sub_le p q |>.trans (max_le hp hq)) (sub_ne_zero.mpr hne)
  simpa only [relativeDistance, hammingDist, Polynomial.eval_sub, Pi.zero_apply,
    sub_ne_zero] using h

/-- Two degree-bounded polynomials cannot both be within a strict half-distance radius. -/
theorem eq_of_univariate_close (p q : Polynomial F)
    (hp : p.natDegree ≤ c) (hq : q.natDegree ≤ c) {w : F → F} {ε : ℚ}
    (hradius : 2 * ε < 1 - (c : ℚ) / Fintype.card F)
    (hwp : relativeDistance w p.eval ≤ ε) (hwq : relativeDistance w q.eval ≤ ε) : p = q := by
  by_contra hne
  have hlow := univariate_distance_ge p q hp hq hne
  have htriangle := relativeDistance_triangle p.eval w q.eval
  rw [relativeDistance_comm p.eval w] at htriangle
  linarith

/-- A minimum exists because error counts are natural numbers and zero is an admissible codeword. -/
theorem exists_bestApproximation (c : ℕ) (w : F → F) :
    ∃ p : Polynomial F, p.natDegree ≤ c ∧
      ∀ q : Polynomial F, q.natDegree ≤ c → relativeDistance w p.eval ≤
        relativeDistance w q.eval := by
  classical
  let S : ℕ → Prop := fun n =>
    ∃ p : Polynomial F, p.natDegree ≤ c ∧ hammingDist w p.eval = n
  have hex : ∃ n, S n := ⟨_, 0, by simp, rfl⟩
  obtain ⟨p, hp, hcount⟩ := Nat.find_spec hex
  refine ⟨p, hp, fun q hq => ?_⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  rw [hcount]
  exact Nat.find_min' hex ⟨q, hq, rfl⟩

/-- A chosen nearest formal polynomial. Ties are resolved by classical choice. -/
noncomputable def bestApproximation (c : ℕ) (w : F → F) :
    {p : Polynomial F // p.natDegree ≤ c} :=
  ⟨(exists_bestApproximation c w).choose, (exists_bestApproximation c w).choose_spec.1⟩

/-- The chosen polynomial minimizes normalized disagreement with the given word. -/
theorem bestApproximation_min (c : ℕ) (w : F → F) (q : Polynomial F)
    (hq : q.natDegree ≤ c) :
    relativeDistance w (bestApproximation c w).val.eval ≤ relativeDistance w q.eval :=
  (exists_bestApproximation c w).choose_spec.2 q hq

/-- Any codeword inside the strict half-distance radius is the chosen nearest polynomial. -/
theorem bestApproximation_eq_of_close (c : ℕ) (w : F → F) (p : Polynomial F)
    (hp : p.natDegree ≤ c) {ε : ℚ}
    (hradius : 2 * ε < 1 - (c : ℚ) / Fintype.card F)
    (hwp : relativeDistance w p.eval ≤ ε) : (bestApproximation c w).val = p :=
  eq_of_univariate_close _ p (bestApproximation c w).property hp hradius
    ((bestApproximation_min c w p hp).trans hwp) hwp

/-- Nearest bounded-degree decoding applied separately to every parametrized line. -/
noncomputable def decodedTable (c : ℕ) (f : (σ → F) → F) : LineTable F σ c :=
  fun uv => bestApproximation c (fun t => f (point uv.1 uv.2 t))

/-- The decoded row has no more error than any degree-bounded candidate on that line. -/
theorem decodedTable_lineError_le (c : ℕ) (f : (σ → F) → F) (u v : σ → F)
    (q : Polynomial F) (hq : q.natDegree ≤ c) :
    relativeDistance (fun t => f (point u v t)) (decodedTable c f (u, v)).val.eval ≤
      relativeDistance (fun t => f (point u v t)) q.eval :=
  bestApproximation_min c _ q hq

/-- Below half-distance error on a line, decoding recovers the global polynomial's restriction. -/
theorem decodedTable_eq_restrict_of_close (f : (σ → F) → F) (u v : σ → F)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) {ε : ℚ}
    (hradius : 2 * ε < 1 - (c : ℚ) / Fintype.card F)
    (hclose : relativeDistance (fun t => f (point u v t))
      (fun t => MvPolynomial.eval (point u v t) P) ≤ ε) :
    (decodedTable c f (u, v)).val = restrict u v P := by
  apply bestApproximation_eq_of_close c _ _
    (natDegree_restrict_le_of_totalDegree_le u v P hP) hradius
  simpa only [eval_restrict] using hclose

variable [Fintype σ] [DecidableEq σ]

/-- Choosing a nearest polynomial on every line never increases the actual rejection probability. -/
theorem rejectionRate_decodedTable_le (c : ℕ) (f : (σ → F) → F)
    (table : LineTable F σ c) : rejectionRate f (decodedTable c f) ≤ rejectionRate f table := by
  rw [rejectionRate_eq_relativeDistance, rejectionRate_eq_relativeDistance]
  rw [relativeDistance_prod, relativeDistance_prod]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro uv _
  exact decodedTable_lineError_le c f uv.1 uv.2 (table uv).val (table uv).property

end PCP.Algebraic.PointLineTest
