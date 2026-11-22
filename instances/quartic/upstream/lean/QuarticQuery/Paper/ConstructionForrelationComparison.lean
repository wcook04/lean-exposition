module

public import QuarticQuery.Paper.ConstructionForrelationDefinitions

/-!
# The numerical comparison in the proof of Lemma 2.1(i)

Compiled as part of the `QuarticQuery` library target.
This file proves only the numerical comparison with `L`. It makes no assertion
that the precise logarithmic factor in Bansal--Sinha's published lower bound
has a complete proof. The source already proves the required fixed-`k`
complexity bound independently in `ForrelationLower.Main`.
-/

public section

namespace QuarticQuery.Paper

/-- Ledger: claim-bs-to-L. Auxiliary arithmetic statement: an affine
denominator to a power at most one is eventually smaller than a positive
multiple of `(2t)^2`. The unfloored comparison is stated explicitly. -/
theorem construction_affine_comparison {k : ℕ} (hk : 2 ≤ k)
    {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      ∀ Λ : ℝ, 1 ≤ Λ → Λ ≤ A + B * t →
        (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 <
          c * ((mValue t : ℝ) / Λ) ^ (1 - 1 / (k : ℝ)) := by
  refine ⟨⌈(A + B) / (4 * c)⌉₊ + 1, by omega, fun t ht Λ hΛ1 hΛ => ?_⟩
  have ha1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) < t := by linarith
  have hm : (0 : ℝ) < (mValue t : ℝ) := by
    have : 0 < mValue t := by simp only [mValue]; positivity
    exact_mod_cast this
  have hMpos : 0 < (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) :=
    Real.rpow_pos_of_pos hm _
  have hΛpos : 0 < Λ := by linarith
  have hpow : Λ ^ (1 - 1 / (k : ℝ)) ≤ Λ := by
    calc
      Λ ^ (1 - 1 / (k : ℝ)) ≤ Λ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hΛ1 ha1
      _ = Λ := Real.rpow_one Λ
  have hΛa : 0 < Λ ^ (1 - 1 / (k : ℝ)) := Real.rpow_pos_of_pos hΛpos _
  have hdiv : ((mValue t : ℝ) / Λ) ^ (1 - 1 / (k : ℝ)) =
      (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ ^ (1 - 1 / (k : ℝ)) :=
    Real.div_rpow hm.le hΛpos.le _
  have hT : (A + B) / (4 * c) < t := by
    have hceil := Nat.le_ceil ((A + B) / (4 * c))
    have hcast : ((⌈(A + B) / (4 * c)⌉₊ + 1 : ℕ) : ℝ) ≤ t := by
      exact_mod_cast ht
    push_cast at hcast
    linarith
  have hAB : A + B < t * (4 * c) := (div_lt_iff₀ (by positivity)).1 hT
  have hAt : A ≤ A * t := by nlinarith
  have hΛlt : Λ < c * (2 * (t : ℝ)) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hAB ht0]
  have hgt : 1 < c * (2 * (t : ℝ)) ^ 2 / Λ := (one_lt_div hΛpos).2 hΛlt
  have e : c * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ) =
      ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2) *
        (c * (2 * (t : ℝ)) ^ 2 / Λ) := by
    field_simp [hΛpos.ne', ht0.ne'] <;> ring
  have hsmall : (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 <
      c * ((mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) / Λ) := by
    rw [e]
    exact lt_mul_of_one_lt_right (div_pos hMpos (by positivity)) hgt
  rw [hdiv]
  exact hsmall.trans_le
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hMpos.le hΛa hpow) hc.le)

/-- Ledger: claim-bs-to-L. Stronger explicit floor-removal component:
the nonnegative floor is at most the unfloored quantity. -/
theorem construction_L_le_unfloored (k t : ℕ) :
    (Lvalue k t : ℝ) ≤ (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) /
      (Real.logb 2 (mValue t : ℝ)) ^ 2 := by
  rw [Lvalue, Real.rpow_eq_pow]
  exact Nat.floor_le
    (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))

/-- Ledger: claim-bs-to-L. Stronger chain with the unfloored middle term,
`c > 0` explicit and logarithms in the paper's base-two convention. -/
theorem construction_bs_comparison_chain (k : ℕ) (hk : 2 ≤ k)
    (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (Lvalue k t : ℝ) ≤ (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) /
        (Real.logb 2 (mValue t : ℝ)) ^ 2 ∧
      (mValue t : ℝ) ^ (1 - 1 / (k : ℝ)) /
          (Real.logb 2 (mValue t : ℝ)) ^ 2 <
        c * (k : ℝ) ^ (-29 : ℤ) *
          ((mValue t : ℝ) / Real.logb 2 ((k : ℝ) * (mValue t : ℝ))) ^
            (1 - 1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hc' : 0 < c * (k : ℝ) ^ (-29 : ℤ) := mul_pos hc (zpow_pos hk0 _)
  have hlk : 0 ≤ Real.logb 2 (k : ℝ) := Real.logb_nonneg one_lt_two hk1
  obtain ⟨t₀, ht₀1, ht₀⟩ := construction_affine_comparison hk hc' hlk
    (zero_le_two : (0 : ℝ) ≤ 2)
  refine ⟨t₀, fun t ht => ⟨construction_L_le_unfloored k t, ?_⟩⟩
  rw [Forrelation.logb_mValue]
  apply ht₀ t ht
  all_goals
    have hm : (0 : ℝ) < (mValue t : ℝ) := by
      have : 0 < mValue t := by simp only [mValue]; positivity
      exact_mod_cast this
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    rw [Real.logb_mul hk0.ne' hm.ne', Forrelation.logb_mValue] <;> linarith

/-- Ledger: claim-bs-to-L. Verbatim corrected numerical comparison,
independent of any theorem asserting a randomized-query lower bound. -/
theorem construction_claim_bs_to_L (k : ℕ) (hk : 2 ≤ k)
    (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (Lvalue k t : ℝ) < c * (k : ℝ) ^ (-29 : ℤ) *
        ((mValue t : ℝ) / Real.logb 2 ((k : ℝ) * (mValue t : ℝ))) ^
          (1 - 1 / (k : ℝ)) := by
  obtain ⟨t₀, ht₀⟩ := construction_bs_comparison_chain k hk c hc
  exact ⟨t₀, fun t ht => (ht₀ t ht).1.trans_lt (ht₀ t ht).2⟩

end QuarticQuery.Paper
