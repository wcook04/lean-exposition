module

public import QuarticQuery.Forrelation.Circuit

/-!
# Magnitudes in the ideal integer computation

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

The bounds below concern ideal integer sums. `Forrelation.Enc` in the existing
Boolean circuit records residues modulo a power of two. These lemmas must not
be described as a proof that every stored register of that implementation has
been related to an ideal intermediate value without wraparound.
-/

public section

namespace QuarticQuery.Paper

open Finset
open QuarticQuery.Forrelation

/-- Ledger: claim-circuit-size. Supporting elementary bound: a sum of `a`
integers of absolute value at most `B` has absolute value at most `a * B`. -/
theorem construction_abs_sum_range_le (a : ℕ) (v : ℕ → ℤ) (B : ℤ)
    (hv : ∀ j, j < a → |v j| ≤ B) :
    |∑ j ∈ range a, v j| ≤ (a : ℤ) * B := by
  revert hv
  induction a with
  | zero =>
    intro hv
    simp only [range_zero, sum_empty, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ a ih =>
    intro hv
    have hprev : |∑ j ∈ range a, v j| ≤ (a : ℤ) * B :=
      ih (fun j hj => hv j (by omega))
    rw [sum_range_succ]
    calc
      |(∑ j ∈ range a, v j) + v a| ≤ |∑ j ∈ range a, v j| + |v a| :=
        abs_add_le _ _
      _ ≤ (a : ℤ) * B + B := add_le_add hprev (hv a (by omega))
      _ = ((a + 1 : ℕ) : ℤ) * B := by push_cast; ring

/-- Ledger: def-walsh-sign. Verbatim sign magnitude used in the integer walk. -/
theorem construction_abs_walshN (n i j : ℕ) : |walshN n i j| = 1 := by
  rcases walshN_eq_one_or n i j with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- Ledger: claim-circuit-size. The ideal Walsh walk after `l` transforms is
bounded by `m^l`, where `m = 2^n`. This explicit bound supplies the paper's
polynomial-magnitude assertion; it does not assert anything about a modular
register's decoded signed value. -/
theorem construction_walkN_bound (n l : ℕ) (σ : ℕ → ℕ → ℤ)
    (hσ : ∀ h i, |σ h i| ≤ 1) (i : ℕ) :
    |walkN n l σ i| ≤ ((2 ^ n : ℕ) : ℤ) ^ l := by
  induction l generalizing σ i with
  | zero => simpa only [walkN, pow_zero] using hσ 0 i
  | succ l ih =>
    have hsum :
        |∑ j ∈ range (2 ^ n),
          walshN n i j * walkN n l (fun h => σ (h + 1)) j| ≤
          ((2 ^ n : ℕ) : ℤ) * ((2 ^ n : ℕ) : ℤ) ^ l := by
      apply construction_abs_sum_range_le
      intro j hj
      rw [abs_mul, construction_abs_walshN, one_mul]
      exact ih (σ := fun h => σ (h + 1)) (i := j) (fun h a => hσ (h + 1) a)
    rw [walkN, abs_mul]
    calc
      |σ 0 i| * |∑ j ∈ range (2 ^ n),
          walshN n i j * walkN n l (fun h => σ (h + 1)) j| ≤
          1 * |∑ j ∈ range (2 ^ n),
            walshN n i j * walkN n l (fun h => σ (h + 1)) j| :=
        mul_le_mul_of_nonneg_right (hσ 0 i) (abs_nonneg _)
      _ ≤ ((2 ^ n : ℕ) : ℤ) * ((2 ^ n : ℕ) : ℤ) ^ l := by
        simpa only [one_mul] using hsum
      _ = ((2 ^ n : ℕ) : ℤ) ^ (l + 1) := by rw [pow_succ]; ring

/-- Ledger: claim-circuit-size. Every prefix of the final signed sum is bounded
by its number of terms times `m^l`. The endpoint with `a = m` is at most
`m^(l+1)`, and a prefix with `a ≤ m` has the same upper bound. -/
theorem construction_walkN_prefix_bound (n l a : ℕ) (σ : ℕ → ℕ → ℤ)
    (hσ : ∀ h i, |σ h i| ≤ 1) :
    |∑ j ∈ range a, walkN n l σ j| ≤ (a : ℤ) * ((2 ^ n : ℕ) : ℤ) ^ l := by
  apply construction_abs_sum_range_le
  intro j hj
  exact construction_walkN_bound n l σ hσ j

/-- Ledger: claim-circuit-size. A partial butterfly block of size `2^q` has
absolute value at most `2^q B` if its input coordinates have magnitude at most
`B`. Offsets allow any recursive subblock of the transform. -/
theorem construction_butterfly_block_bound (q i offset : ℕ)
    (v : ℕ → ℤ) (B : ℤ)
    (hv : ∀ j, j < 2 ^ q → |v (offset + j)| ≤ B) :
    |∑ j ∈ range (2 ^ q), walshN q i j * v (offset + j)| ≤
      ((2 ^ q : ℕ) : ℤ) * B := by
  apply construction_abs_sum_range_le
  intro j hj
  rw [abs_mul, construction_abs_walshN, one_mul]
  exact hv j hj

end QuarticQuery.Paper
