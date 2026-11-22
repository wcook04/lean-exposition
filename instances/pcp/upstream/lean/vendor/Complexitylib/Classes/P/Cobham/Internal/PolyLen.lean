/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.Algebra
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial lengths inside the algebra

A computation in Cobham's algebra measures sizes by string lengths, so a
polynomial time or space bound has to be available as a *string of that
length*. `smash` multiplies lengths and concatenation adds them, so Horner's
scheme builds, for any polynomial with natural coefficients, a member of the
algebra whose output has exactly the polynomial's value as its length.

## Main definitions

- `Cobham.hornerEval` — Horner evaluation of a coefficient list
- `Cobham.lenOfCoeffs` — the string realizing that value as its length
- `Cobham.polyLen` — the same for a `Polynomial ℕ`

## Main results

- `Cobham.lenOfCoeffs_mem`, `Cobham.polyLen_mem` — both are in the algebra
- `Cobham.polyLen_length` — `polyLen q s` has length exactly `q.eval |s|`
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-- Horner evaluation of a coefficient list, lowest coefficient first. -/
def hornerEval : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, n => a + n * hornerEval as n

/-- The string whose length is the Horner value of the coefficient list at
`|s|`: constants contribute blocks of that many bits, and each multiplication
by `|s|` is one `smash`. -/
def lenOfCoeffs : List ℕ → List Bool → List Bool
  | [], _ => []
  | a :: as, s => List.replicate a false ++ Complexity.smash s (lenOfCoeffs as s)

@[simp] theorem lenOfCoeffs_length (as : List ℕ) (s : List Bool) :
    (lenOfCoeffs as s).length = hornerEval as s.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      rw [lenOfCoeffs, hornerEval, List.length_append, List.length_replicate,
        smash_length, ih]

/-- **The Horner string is in the algebra.** -/
theorem lenOfCoeffs_mem {n : ℕ} (as : List ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => lenOfCoeffs as (g v) := by
  induction as with
  | nil => exact (Cobham.const []).of_eq fun _ => rfl
  | cons a as ih =>
      exact (appendFn (Cobham.const (List.replicate a false))
        (comp₂ Cobham.smash hg ih)).of_eq fun _ => by simp [lenOfCoeffs]

/-- Horner evaluation of a truncated coefficient sequence is the truncated
power sum. -/
theorem hornerEval_map_range (f : ℕ → ℕ) (d n : ℕ) :
    hornerEval ((List.range d).map f) n = ∑ i ∈ Finset.range d, f i * n ^ i := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerEval,
        ih (f ∘ Nat.succ), Finset.sum_range_succ' (fun i => f i * n ^ i) d]
      simp only [Function.comp_apply, pow_zero, mul_one]
      have hmul : n * ∑ i ∈ Finset.range d, f (i + 1) * n ^ i
          = ∑ i ∈ Finset.range d, f (i + 1) * n ^ (i + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hmul]
      omega

/-- The string realizing a polynomial's value as its length. -/
noncomputable def polyLen (q : Polynomial ℕ) (s : List Bool) : List Bool :=
  lenOfCoeffs ((List.range (q.natDegree + 1)).map q.coeff) s

/-- **The polynomial's value is the string's length.** -/
@[simp] theorem polyLen_length (q : Polynomial ℕ) (s : List Bool) :
    (polyLen q s).length = q.eval s.length := by
  rw [polyLen, lenOfCoeffs_length, hornerEval_map_range, Polynomial.eval_eq_sum_range]

/-- **The polynomial-length string is in the algebra.** -/
theorem polyLen_mem {n : ℕ} (q : Polynomial ℕ)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => polyLen q (g v) :=
  lenOfCoeffs_mem _ hg

end Cobham

end Complexity
