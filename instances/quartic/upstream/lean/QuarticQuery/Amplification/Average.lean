module

public import QuarticQuery.Statement

/-!
# Equation (9): the averaged success probability

The sum of `sin²((2ℓ+1)θ)` over `ℓ < M` is a telescoping sum. Adapted from Troy
Lee's `Quantum/Amplitude/TrigSum.lean`, not imported. The exact error term is
`1/(4M|sin 2θ|)`; the preprint's `1/(2M|sin 2θ|)` is weaker and also proved.
-/

@[expose] public section

namespace QuarticQuery.Amplification

open Finset

/-- Ledger: eq-9. The telescoping identity in multiplied form. -/
theorem sin_two_mul_sum_sin_sq (θ : ℝ) (M : ℕ) :
    Real.sin (2 * θ) * ∑ ℓ ∈ range M, Real.sin ((2 * ℓ + 1) * θ) ^ 2
      = M * Real.sin (2 * θ) / 2 - Real.sin (4 * M * θ) / 4 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, mul_add, ih]
    have hx : (4 * ((M + 1 : ℕ) : ℝ) * θ) = (2 * (2 * M + 1) * θ) + 2 * θ := by
      push_cast; ring
    have hy : (4 * (M : ℝ) * θ) = (2 * (2 * M + 1) * θ) - 2 * θ := by ring
    have hsq : Real.sin ((2 * M + 1) * θ) ^ 2
        = (1 - Real.cos (2 * (2 * M + 1) * θ)) / 2 := by
      have := Real.cos_sq' ((2 * M + 1) * θ)
      have h2 := Real.cos_two_mul ((2 * M + 1) * θ)
      rw [show 2 * ((2 * (M : ℝ) + 1) * θ) = 2 * (2 * M + 1) * θ by ring] at h2
      linarith
    rw [hx, hy, Real.sin_add, Real.sin_sub, hsq]
    push_cast
    ring

/-- Ledger: eq-9. The exact average. -/
theorem average_sin_sq {θ : ℝ} {M : ℕ} (hM : M ≠ 0) (hs : Real.sin (2 * θ) ≠ 0) :
    (1 / (M : ℝ)) * ∑ ℓ ∈ range M, Real.sin ((2 * ℓ + 1) * θ) ^ 2
      = 1 / 2 - Real.sin (4 * M * θ) / (4 * M * Real.sin (2 * θ)) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have h := sin_two_mul_sum_sin_sq θ M
  have hsum : ∑ ℓ ∈ range M, Real.sin ((2 * ℓ + 1) * θ) ^ 2 =
      (M * Real.sin (2 * θ) / 2 - Real.sin (4 * M * θ) / 4) / Real.sin (2 * θ) := by
    rw [eq_div_iff hs, mul_comm, h]
  rw [hsum]
  field_simp

/-- Ledger: eq-9. The first inequality of (9). -/
theorem average_sin_sq_ge {θ : ℝ} {M : ℕ} (hM : M ≠ 0) (hs : Real.sin (2 * θ) ≠ 0) :
    1 / 2 - 1 / (2 * M * |Real.sin (2 * θ)|) ≤
      (1 / (M : ℝ)) * ∑ ℓ ∈ range M, Real.sin ((2 * ℓ + 1) * θ) ^ 2 := by
  rw [average_sin_sq hM hs]
  have hM' : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have ha : 0 < |Real.sin (2 * θ)| := abs_pos.mpr hs
  have hb : Real.sin (4 * M * θ) / (4 * M * Real.sin (2 * θ)) ≤
      1 / (2 * M * |Real.sin (2 * θ)|) := by
    calc Real.sin (4 * M * θ) / (4 * M * Real.sin (2 * θ))
        ≤ |Real.sin (4 * M * θ) / (4 * M * Real.sin (2 * θ))| := le_abs_self _
      _ = |Real.sin (4 * M * θ)| / (4 * M * |Real.sin (2 * θ)|) := by
          rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * M)]
      _ ≤ 1 / (4 * M * |Real.sin (2 * θ)|) := by
          gcongr
          exact Real.abs_sin_le_one _
      _ ≤ 1 / (2 * M * |Real.sin (2 * θ)|) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [mul_pos hM' ha]
  linarith

/-- Ledger: eq-9. The second inequality of (9), for `γ ≤ sin² 2θ`-sized angles and
`M ≥ 10/√γ`. -/
theorem average_sin_sq_ge_nine_twentieths {θ γ : ℝ} {M : ℕ} (hγ : 0 < γ)
    (hM : 10 / Real.sqrt γ ≤ M) (hs : Real.sqrt γ ≤ Real.sin (2 * θ)) :
    (9 / 20 : ℝ) ≤ (1 / (M : ℝ)) * ∑ ℓ ∈ range M, Real.sin ((2 * ℓ + 1) * θ) ^ 2 := by
  have hr : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hs0 : 0 < Real.sin (2 * θ) := hr.trans_le hs
  have hMpos : (0 : ℝ) < M := (div_pos (by norm_num) hr).trans_le hM
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hMpos
  have h := average_sin_sq_ge hM0 hs0.ne'
  rw [abs_of_pos hs0] at h
  have h10 : 10 ≤ (M : ℝ) * Real.sqrt γ := by
    rwa [div_le_iff₀ hr] at hM
  have hprod : 10 ≤ (M : ℝ) * Real.sin (2 * θ) :=
    h10.trans (mul_le_mul_of_nonneg_left hs hMpos.le)
  have hb : 1 / (2 * (M : ℝ) * Real.sin (2 * θ)) ≤ 1 / 20 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  linarith

end QuarticQuery.Amplification
