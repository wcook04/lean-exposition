module

public import QuarticQuery.Results.Unconditional

/-!
# The exact tail and exponent displays in Sections 4 and 5

Compiled as part of the `QuarticQuery` library target.
Target: `leanprover/lean4:v4.36.0-rc2`, Mathlib
`69552756cd8a2d2d48763cf7279fd814d6a1224d`.

The declarations in this file do not import `Paper.Section4`.
The asymptotic logarithms are base two, as in the preprint. The threshold for
the randomized lower bound may depend on the fixed integer `k`.
-/

public section

namespace QuarticQuery.Paper

open Filter

/-- Ledger: claim-tail. The exact real exponent of the independent-answer
probability, with `m = 4^t` and `r = 40t`. -/
theorem classical_twoThirds_exact (t : ℕ) :
    ((2 : ℝ) / 3) ^ (40 * t) =
      (mValue t : ℝ) ^ (-20 * Real.logb 2 ((3 : ℝ) / 2)) := by
  have hm : 0 < (mValue t : ℝ) := by rw [mValue_cast]; positivity
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hlog : Real.log (mValue t : ℝ) = 2 * (t : ℝ) * Real.log 2 := by
    have h : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
    rw [h, Real.log_pow]
    push_cast
    ring
  have hlog23 : Real.log ((2 : ℝ) / 3) = -Real.log ((3 : ℝ) / 2) := by
    rw [show ((2 : ℝ) / 3) = (((3 : ℝ) / 2)⁻¹) by norm_num, Real.log_inv]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
    Real.rpow_def_of_pos hm, hlog, hlog23, Real.logb]
  congr 1
  push_cast
  field_simp [hl2] <;> ring

/-- Ledger: claim-tail. The paper's exponent is strictly negative. In fact it
is less than `-8`, since `(3/2)^2 > 2`. -/
theorem classical_tail_exponent_neg :
    2 - 20 * Real.logb 2 ((3 : ℝ) / 2) < 0 := by
  have h : (1 : ℝ) < 2 * Real.logb 2 ((3 : ℝ) / 2) := by
    calc
      (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one one_lt_two).symm
      _ < Real.logb 2 (((3 : ℝ) / 2) ^ (2 : ℕ)) :=
        Real.logb_lt_logb one_lt_two (by norm_num) (by norm_num)
      _ = 2 * Real.logb 2 ((3 : ℝ) / 2) := by
        simpa using Real.logb_pow (2 : ℝ) ((3 : ℝ) / 2) 2
  linarith

/-- Ledger: claim-tail. An exact geometric-sequence expression for the
power appearing in the paper's upper envelope. -/
theorem classical_tail_envelope_eq (t : ℕ) :
    (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2)) =
      ((16 : ℝ) * ((2 : ℝ) / 3) ^ 40) ^ t := by
  have hm : 0 < (mValue t : ℝ) := by rw [mValue_cast]; positivity
  have hm2 : (mValue t : ℝ) ^ 2 = (16 : ℝ) ^ t := by
    rw [mValue_cast, ← pow_mul, Nat.mul_comm t 2, pow_mul]
    norm_num
  calc
    (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2)) =
        (mValue t : ℝ) ^ (2 : ℝ) *
          (mValue t : ℝ) ^ (-20 * Real.logb 2 ((3 : ℝ) / 2)) := by
      rw [← Real.rpow_add hm]
      congr 1
      ring
    _ = (mValue t : ℝ) ^ 2 * ((2 : ℝ) / 3) ^ (40 * t) := by
      rw [Real.rpow_two, ← classical_twoThirds_exact t]
    _ = ((16 : ℝ) * ((2 : ℝ) / 3) ^ 40) ^ t := by
      rw [hm2, pow_mul, ← mul_pow]

/-- Ledger: claim-tail. The exact finite inequality displayed by the preprint.
The budget premise follows from `L ≤ m` and `G ≤ mL/100`. -/
theorem classical_tail_le (t : ℕ) {G : ℝ}
    (hG : G ≤ (mValue t : ℝ) ^ 2 / 100) :
    G * ((2 : ℝ) / 3) ^ (40 * t) ≤
      (1 / 100 : ℝ) *
        (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2)) := by
  have hm : 0 < (mValue t : ℝ) := by rw [mValue_cast]; positivity
  calc
    G * ((2 : ℝ) / 3) ^ (40 * t) ≤
        ((mValue t : ℝ) ^ 2 / 100) * ((2 : ℝ) / 3) ^ (40 * t) :=
      mul_le_mul_of_nonneg_right hG (by positivity)
    _ = (1 / 100 : ℝ) *
        (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2)) := by
      rw [classical_twoThirds_exact t]
      rw [show 2 - 20 * Real.logb 2 ((3 : ℝ) / 2) =
        (2 : ℝ) + (-20 * Real.logb 2 ((3 : ℝ) / 2)) by ring,
        Real.rpow_add hm, Real.rpow_two]
      ring

/-- Ledger: claim-tail. The upper envelope with the paper's exact exponent
tends to zero; no weakened exponent is substituted. -/
theorem classical_tail_envelope_tendsto :
    Tendsto (fun t : ℕ => (1 / 100 : ℝ) *
      (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2))) atTop (nhds 0) := by
  have h : Tendsto (fun t : ℕ => ((16 : ℝ) * ((2 : ℝ) / 3) ^ 40) ^ t)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  simpa only [classical_tail_envelope_eq, mul_zero] using h.const_mul (1 / 100 : ℝ)

/-- Ledger: claim-tail. The guessed-address contribution itself is `o(1)`
for any nonnegative budget sequence satisfying the paper's bound. -/
theorem classical_tail_tendsto {G : ℕ → ℝ}
    (hG0 : ∀ t, 0 ≤ G t)
    (hG : ∀ t, G t ≤ (mValue t : ℝ) ^ 2 / 100) :
    Tendsto (fun t : ℕ => G t * ((2 : ℝ) / 3) ^ (40 * t)) atTop (nhds 0) := by
  exact squeeze_zero (fun t => mul_nonneg (hG0 t) (by positivity))
    (fun t => classical_tail_le t (hG t)) classical_tail_envelope_tendsto

/-- Ledger: claim-tail. The actual floored budget obeys the elementary square
bound. At `t = 0`, its value is zero by the total real-division convention. -/
theorem classical_Gvalue_le_square (k t : ℕ) (hk : 1 ≤ k) :
    (Gvalue (mValue t) (Lvalue k t) : ℝ) ≤ (mValue t : ℝ) ^ 2 / 100 := by
  by_cases ht : t = 0
  · subst t
    norm_num [Gvalue, Lvalue, mValue]
  · have hLm : (Lvalue k t : ℝ) ≤ (mValue t : ℝ) := by
      exact_mod_cast Lvalue_le_mValue hk (show 1 ≤ t by omega)
    have hG : (Gvalue (mValue t) (Lvalue k t) : ℝ) ≤
        (mValue t : ℝ) * (Lvalue k t : ℝ) / 100 := by
      simpa [Gvalue] using
        (Nat.cast_div_le (α := ℝ) (m := mValue t * Lvalue k t) (n := 100))
    have hm0 : (0 : ℝ) ≤ mValue t := Nat.cast_nonneg _
    calc
      (Gvalue (mValue t) (Lvalue k t) : ℝ) ≤
          (mValue t : ℝ) * (Lvalue k t : ℝ) / 100 := hG
      _ ≤ (mValue t : ℝ) * (mValue t : ℝ) / 100 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLm hm0) (by norm_num)
      _ = (mValue t : ℝ) ^ 2 / 100 := by ring

/-- Ledger: claim-tail. Both clauses of the paper's tail statement at the
actual `L` and `G`; the bound and the zero limit are unconditional. -/
theorem classical_tail_parameters (k : ℕ) (hk : 1 ≤ k) :
    (∀ t : ℕ,
      (Gvalue (mValue t) (Lvalue k t) : ℝ) * ((2 : ℝ) / 3) ^ (40 * t) ≤
        (1 / 100 : ℝ) *
          (mValue t : ℝ) ^ (2 - 20 * Real.logb 2 ((3 : ℝ) / 2))) ∧
    Tendsto (fun t : ℕ =>
      (Gvalue (mValue t) (Lvalue k t) : ℝ) * ((2 : ℝ) / 3) ^ (40 * t))
      atTop (nhds 0) := by
  refine ⟨fun t => classical_tail_le t (classical_Gvalue_le_square k t hk), ?_⟩
  exact classical_tail_tendsto (fun t => Nat.cast_nonneg _)
    (fun t => classical_Gvalue_le_square k t hk)

/-- Ledger: claim-numeric. All three numerical component bounds and their sum,
including the strict separation of the numerical constant from `1/3`.
The underlying finite estimate is valid even at `t = 0` if its premises hold. -/
theorem classical_numeric_components {t : ℕ} {L G : ℝ}
    (hL1 : 1 ≤ L) (hLm : L ≤ (mValue t : ℝ))
    (hG : G ≤ (mValue t : ℝ) * L / 100) :
    4 * G / (mValue t : ℝ) ^ 2 ≤ 4 / 100 ∧
    G / ((mValue t : ℝ) * L) ≤ 1 / 100 ∧
    G * ((2 : ℝ) / 3) ^ (40 * t) ≤ 1 / 100 ∧
    4 * G / (mValue t : ℝ) ^ 2 + G / ((mValue t : ℝ) * L) +
      G * ((2 : ℝ) / 3) ^ (40 * t) ≤ 6 / 100 ∧
    (6 / 100 : ℝ) < 1 / 3 := by
  set m : ℝ := (mValue t : ℝ)
  have hm1 : 1 ≤ m := hL1.trans hLm
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have h1 : 4 * G / m ^ 2 ≤ 4 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : G / (m * L) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have htail : ((2 : ℝ) / 3) ^ (40 * t) ≤ (m ^ 10)⁻¹ := twoThirds_pow_le t
  have h3 : G * ((2 : ℝ) / 3) ^ (40 * t) ≤ 1 / 100 := by
    have hGm : G ≤ m ^ 2 / 100 := by nlinarith
    have hm210 : m ^ 2 ≤ m ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
    calc
      G * ((2 : ℝ) / 3) ^ (40 * t) ≤ m ^ 2 / 100 * ((2 : ℝ) / 3) ^ (40 * t) :=
        mul_le_mul_of_nonneg_right hGm (by positivity)
      _ ≤ m ^ 2 / 100 * (m ^ 10)⁻¹ :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ m ^ 10 / 100 * (m ^ 10)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 100 := by field_simp
  exact ⟨h1, h2, h3, by linarith, by norm_num⟩

/-- Ledger: cor-R-omega. The lower bound with the paper's base-two logarithm,
all quantifiers explicit, and constant `1/400`. The circuit is arbitrary subject
to realizing the fixed promise problem, so the threshold is independent of it. -/
theorem classical_cor_R_omega_log2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) →
        (1 / 400 : ℝ) * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
          Real.logb 2 (mValue t : ℝ) ^ 2 ≤
            (R (totalise (Fkm k t C)) : ℝ) := by
  obtain ⟨t₀, ht₀⟩ := ForrelationLower.bansalSinhaLower k hk
  refine ⟨max t₀ 8, fun t ht C hC => ?_⟩
  have ht8 : 8 ≤ t := le_trans (le_max_right _ _) ht
  have hLR := ht₀ t (le_trans (le_max_left _ _) ht)
  have h := rpow_le_of_Gvalue_lt hk ht8 (Gvalue_lt_R_Fkm hk ht8 C hC hLR)
  rw [logb_mValue, mValue_cast]
  exact h

/-- Ledger: cor-R-omega. The same estimate expressed with natural logarithms.
Only the displayed multiplicative constant changes. -/
theorem classical_cor_R_omega_log (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∀ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) →
        c * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
          Real.log (mValue t : ℝ) ^ 2 ≤
            (R (totalise (Fkm k t C)) : ℝ) := by
  obtain ⟨t₀, ht₀⟩ := classical_cor_R_omega_log2 k hk
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨Real.log 2 ^ 2 / 400, by positivity, max t₀ 1, fun t ht C hC => ?_⟩
  have h := ht₀ t (le_trans (le_max_left _ _) ht) C hC
  have ht0 : (0 : ℝ) < t := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) ht))
  have hlog : Real.log (mValue t : ℝ) = 2 * (t : ℝ) * Real.log 2 := by
    have hm : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
    rw [hm, Real.log_pow]
    push_cast
    ring
  have heq : Real.log 2 ^ 2 / 400 * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
      Real.log (mValue t : ℝ) ^ 2 =
      (1 / 400 : ℝ) * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
        Real.logb 2 (mValue t : ℝ) ^ 2 := by
    rw [hlog, logb_mValue]
    field_simp [hl2.ne', ht0.ne'] <;> ring
  rw [heq]
  exact h

/-- Ledger: claim-exponent-ratio. The finite quotient calculation, isolated
from the existence of the function family. The constant is explicit. -/
theorem classical_ratio_arithmetic {c C s α r q m W : ℝ} (b : ℕ)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hα : 0 ≤ α) (hm : 1 ≤ m) (hW : 1 ≤ W)
    (hq : 0 ≤ q)
    (hQ : q ≤ C * m ^ ((1 : ℝ) / 2) * W ^ b)
    (hR : c * m ^ s / W ^ 2 ≤ r) :
    c / (1 + C) ^ α * m ^ (s - α / 2) / W ^ (2 + α * (b : ℝ)) ≤
      r / (1 + q) ^ α := by
  have hm0 : 0 < m := by linarith
  have hW0 : 0 < W := by linarith
  have hC1 : 0 < 1 + C := by linarith
  have hq1 : 0 < 1 + q := by linarith
  have hA : 1 ≤ m ^ ((1 : ℝ) / 2) * W ^ b :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hm (by norm_num)) (one_le_pow₀ hW)
  have hbase : 1 + q ≤ (1 + C) * (m ^ ((1 : ℝ) / 2) * W ^ b) := by
    nlinarith
  have hpow : (1 + q) ^ α ≤
      (1 + C) ^ α * m ^ (α / 2) * W ^ ((b : ℝ) * α) := by
    calc
      (1 + q) ^ α ≤ ((1 + C) * (m ^ ((1 : ℝ) / 2) * W ^ b)) ^ α :=
        Real.rpow_le_rpow hq1.le hbase hα
      _ = (1 + C) ^ α * m ^ (α / 2) * W ^ ((b : ℝ) * α) := by
        rw [Real.mul_rpow hC1.le (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hm0.le,
          ← Real.rpow_natCast W b, ← Real.rpow_mul hW0.le]
        rw [show ((1 : ℝ) / 2) * α = α / 2 by ring]
        ring
  have hCpow : (1 + C) ^ α ≠ 0 := (Real.rpow_pos_of_pos hC1 α).ne'
  have hmpow : m ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hm0 _).ne'
  have hWpow : W ^ ((b : ℝ) * α) ≠ 0 := (Real.rpow_pos_of_pos hW0 _).ne'
  have heq : c / (1 + C) ^ α * m ^ (s - α / 2) / W ^ (2 + α * (b : ℝ)) =
      (c * m ^ s / W ^ 2) /
        ((1 + C) ^ α * m ^ (α / 2) * W ^ ((b : ℝ) * α)) := by
    rw [Real.rpow_sub hm0, Real.rpow_add hW0, Real.rpow_two,
      mul_comm α (b : ℝ)]
    field_simp [hCpow, hmpow, hWpow, hW0.ne'] <;> ring
  calc
    c / (1 + C) ^ α * m ^ (s - α / 2) / W ^ (2 + α * (b : ℝ)) =
        (c * m ^ s / W ^ 2) /
          ((1 + C) ^ α * m ^ (α / 2) * W ^ ((b : ℝ) * α)) := heq
    _ ≤ (c * m ^ s / W ^ 2) / (1 + q) ^ α :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hq1 _) hpow
    _ ≤ r / (1 + q) ^ α :=
      div_le_div_of_nonneg_right hR (Real.rpow_nonneg hq1.le _)

/-- Ledger: claim-exponent-ratio. A positive power of `m = 4^t` divided by
any fixed real power of `log₂ m` tends to infinity. -/
theorem classical_power_log_tendsto {d δ e : ℝ} (hd : 0 < d) (hδ : 0 < δ) :
    Tendsto (fun t : ℕ => d * (mValue t : ℝ) ^ δ /
      Real.logb 2 (mValue t : ℝ) ^ e) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro B
  have hD : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hK : 0 < max B 1 / d := div_pos hD hd
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((eventually_poly_lt_exp (max B 1 / d) e (2 * δ) hK (by linarith)).and
      (eventually_ge_atTop 1))
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hkey, ht1⟩ := hT t ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht1)
  have hWpow : 0 < (2 * (t : ℝ)) ^ e :=
    Real.rpow_pos_of_pos (by positivity) e
  have hmexp : (mValue t : ℝ) ^ δ = (2 : ℝ) ^ ((2 * δ) * (t : ℝ)) := by
    have hm : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    congr 1
    push_cast
    ring
  have hscaled : max B 1 * (2 * (t : ℝ)) ^ e <
      d * (2 : ℝ) ^ ((2 * δ) * (t : ℝ)) := by
    calc
      max B 1 * (2 * (t : ℝ)) ^ e =
          d * ((max B 1 / d) * (2 * (t : ℝ)) ^ e) := by
        field_simp [hd.ne'] <;> ring
      _ < d * (2 : ℝ) ^ ((2 * δ) * (t : ℝ)) :=
        mul_lt_mul_of_pos_left hkey hd
  rw [logb_mValue, hmexp]
  apply (le_div_iff₀ hWpow).2
  exact (mul_le_mul_of_nonneg_right (le_max_left B 1) hWpow.le).trans hscaled.le

/-- Ledger: claim-exponent-ratio. The quotient version of the already-proved
eventual strict comparison. The sequence index is `t`; all parameters are fixed. -/
theorem classical_ratio_tendsto {c C s α : ℝ} (b : ℕ) {Rt Qt : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 < C) (hα : 0 ≤ α) (hs : α / 2 < s)
    (hQ0 : ∀ t, 0 ≤ Qt t)
    (hQ : ∀ᶠ t : ℕ in atTop, Qt t ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b)
    (hR : ∀ᶠ t : ℕ in atTop, c * ((4 : ℝ) ^ t) ^ s / (2 * (t : ℝ)) ^ 2 ≤ Rt t) :
    Tendsto (fun t : ℕ => Rt t / (1 + Qt t) ^ α) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro B
  have hD : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (eventually_gt_rpow b hc hC hD hα hs hQ0 hQ hR)
  refine ⟨T, fun t ht => ?_⟩
  have hden : 0 < (1 + Qt t) ^ α :=
    Real.rpow_pos_of_pos (by have := hQ0 t; linarith) α
  exact (le_max_left B 1).trans ((lt_div_iff₀ hden).2 (hT t ht)).le

/-- Ledger: claim-exponent-ratio. The explicit lower envelope, its divergence,
and divergence of the ratio, for arbitrary sequences obeying the family bounds.
The next declaration instantiates this with the actual `Fkm` family. -/
theorem classical_exponent_ratio {k : ℕ} {c C α : ℝ} (b : ℕ) {Rt Qt : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 < C) (hα : 0 ≤ α)
    (hs : α / 2 < 2 - 1 / (k : ℝ))
    (hQ0 : ∀ t, 0 ≤ Qt t)
    (hQ : ∀ᶠ t : ℕ in atTop, Qt t ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b)
    (hR : ∀ᶠ t : ℕ in atTop,
      c * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤ Rt t) :
    (∀ᶠ t : ℕ in atTop,
      c / (1 + C) ^ α * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ) - α / 2) /
        Real.logb 2 (mValue t : ℝ) ^ (2 + α * (b : ℝ)) ≤ Rt t / (1 + Qt t) ^ α) ∧
    Tendsto (fun t : ℕ =>
      c / (1 + C) ^ α * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ) - α / 2) /
        Real.logb 2 (mValue t : ℝ) ^ (2 + α * (b : ℝ))) atTop atTop ∧
    Tendsto (fun t : ℕ => Rt t / (1 + Qt t) ^ α) atTop atTop := by
  refine ⟨?_, classical_power_log_tendsto (by positivity) (by linarith),
    classical_ratio_tendsto b hc hC hα hs hQ0 hQ hR⟩
  filter_upwards [hQ, hR, eventually_ge_atTop 1] with t hQt hRt ht1
  have ht1r : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hm1 : (1 : ℝ) ≤ (mValue t : ℝ) := by
    rw [mValue_cast]
    exact one_le_pow₀ (by norm_num)
  have hW1 : (1 : ℝ) ≤ 2 * (t : ℝ) := by linarith
  have hroot : (mValue t : ℝ) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ t := by
    rw [mValue_cast, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      ← pow_mul, pow_mul', ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  have hQt' : Qt t ≤ C * (mValue t : ℝ) ^ ((1 : ℝ) / 2) * (2 * (t : ℝ)) ^ b := by
    rw [hroot]
    exact hQt
  have hRt' : c * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
      (2 * (t : ℝ)) ^ 2 ≤ Rt t := by
    simpa only [mValue_cast] using hRt
  simpa only [logb_mValue] using
    classical_ratio_arithmetic b hc.le hC.le hα hm1 hW1 (hQ0 t) hQt' hRt'

/-- Ledger: claim-exponent-ratio. The paper's ratio display for its actual
canonical circuit family, with `k = l + 1`, `b_k = 6`, an explicit positive
constant, and both limits. `l` and `α` are chosen before `t` tends to infinity. -/
theorem classical_Fkm_ratio (l : ℕ) (hk : 2 ≤ l + 1) {α : ℝ}
    (hα : 0 ≤ α) (hs : α / 2 < 2 - 1 / ((l + 1 : ℕ) : ℝ)) :
    ∃ d : ℝ, 0 < d ∧
      (∀ᶠ t : ℕ in atTop,
        d * (mValue t : ℝ) ^ (2 - 1 / ((l + 1 : ℕ) : ℝ) - α / 2) /
          Real.logb 2 (mValue t : ℝ) ^ (2 + α * 6) ≤
            (R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) /
              (1 + (Q (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ)) ^ α) ∧
      Tendsto (fun t : ℕ =>
        d * (mValue t : ℝ) ^ (2 - 1 / ((l + 1 : ℕ) : ℝ) - α / 2) /
          Real.logb 2 (mValue t : ℝ) ^ (2 + α * 6)) atTop atTop ∧
      Tendsto (fun t : ℕ =>
        (R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) /
          (1 + (Q (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ)) ^ α)
        atTop atTop := by
  have hC : (0 : ℝ) < Upper.budgetConst (l + 1) := by
    exact_mod_cast Upper.budgetConst_pos (l + 1)
  have hQ : ∀ᶠ t : ℕ in atTop,
      (Q (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) ≤
        (Upper.budgetConst (l + 1) : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ 6 := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact Upper.Q_Fkm_le l t ht
  obtain ⟨t₀, ht₀⟩ := classical_cor_R_omega_log2 (l + 1) hk
  have hR : ∀ᶠ t : ℕ in atTop,
      (1 / 400 : ℝ) * ((4 : ℝ) ^ t) ^ (2 - 1 / ((l + 1 : ℕ) : ℝ)) /
        (2 * (t : ℝ)) ^ 2 ≤
          (R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) := by
    filter_upwards [eventually_ge_atTop t₀] with t ht
    have h := ht₀ t ht (Forrelation.forrCircuit l t) (Forrelation.forrCircuit_realises l t)
    rw [logb_mValue, mValue_cast] at h
    exact h
  refine ⟨(1 / 400 : ℝ) / (1 + (Upper.budgetConst (l + 1) : ℝ)) ^ α,
    by positivity, ?_⟩
  simpa only [Nat.cast_ofNat] using
    classical_exponent_ratio (k := l + 1)
      (Rt := fun t => (R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ))
      (Qt := fun t => (Q (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ))
      6 (by norm_num : (0 : ℝ) < 1 / 400)
      hC hα hs (fun t => Nat.cast_nonneg _) hQ hR

end QuarticQuery.Paper
