import TorusEuler.InductionBudget
import TorusEuler.InductionScales

/-! The scalar absorption of the comparison error in item 2 of the proof of Theorem 7.1. -/

namespace TorusEuler

open Filter

private theorem eventually_scaled_log_pow_le_rpow (n : ℕ) {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) :
    ∀ᶠ μ : ℝ in atTop, C * (Real.log μ) ^ n ≤ μ ^ α := by
  have h := ((isLittleO_log_rpow_rpow_atTop (n : ℝ) hα).const_mul_left C).eventuallyLE
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with μ hμ hμ₁
  rw [Real.rpow_natCast, Real.norm_of_nonneg (mul_nonneg hC
    (pow_nonneg (Real.log_nonneg hμ₁) _)), Real.norm_of_nonneg (Real.rpow_nonneg
      (zero_le_one.trans hμ₁) _)] at hμ
  exact hμ

/-- The gain bound (1.15) absorbs any finite family of fixed polynomial
losses in positive powers of the base frequency, with a common threshold. -/
theorem exists_uniform_log_gain_budget {ι : Type*} [Finite ι]
    (C : ι → ℝ) (p : ι → ℕ) (a : ι → ℝ) (hC : ∀ k, 0 ≤ C k) (ha : ∀ k, 0 < a k) :
    ∃ N₀ : ℝ, 1 < N₀ ∧
      ∀ μ ≥ N₀, ∀ L, 0 ≤ L → L ≤ (Real.log μ) ^ 2 → ∀ k, C k * L ^ p k ≤ μ ^ a k := by
  have h : ∀ᶠ μ : ℝ in atTop, ∀ k, C k * (Real.log μ) ^ (2 * p k) ≤ μ ^ a k :=
    eventually_all.mpr fun k => eventually_scaled_log_pow_le_rpow (2 * p k) (hC k) (ha k)
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  refine ⟨max 2 R, (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _), ?_⟩
  intro μ hμ L hL hLog k
  calc
    C k * L ^ p k ≤ C k * ((Real.log μ) ^ 2) ^ p k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLog _) (hC k)
    _ = C k * (Real.log μ) ^ (2 * p k) := by rw [pow_mul]
    _ ≤ μ ^ a k := hR μ ((le_max_right _ _).trans hμ) k

/-- Item 2 of the proof of Theorem 7.1 uses the gradient estimates (7.6)
one frequency step behind the parent, then expresses them at the parent scale. -/
theorem induction_older_gradient_scales {old μ B Bt : ℝ} {b q : ℕ}
    (hb : 1 ≤ b) (hold : 1 ≤ old) (hμ : μ = old ^ frequencyExponent b q)
    (hB : B ≤ old ^ 9) (hBt : Bt ≤ old ^ 18) :
    B ≤ μ ^ (1 / 32 : ℝ) ∧ Bt ≤ μ ^ (1 / 16 : ℝ) := by
  have hK : 320 ≤ frequencyExponent b q := by
    change 320 * 1 * 1 ≤ 320 * b * (q + 1)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 320 hb) (Nat.succ_pos _)
  have hK' : (320 : ℝ) ≤ frequencyExponent b q := by exact_mod_cast hK
  have hpow (n : ℕ) (a : ℝ) (ha : (n : ℝ) ≤ (frequencyExponent b q : ℝ) * a) :
      old ^ n ≤ μ ^ a := by
    rw [hμ, ← Real.rpow_natCast old n, ← Real.rpow_natCast old (frequencyExponent b q),
      ← Real.rpow_mul (zero_le_one.trans hold)]
    exact Real.rpow_le_rpow_of_exponent_le hold ha
  exact ⟨hB.trans (hpow 9 _ (by push_cast; linarith)),
    hBt.trans (hpow 18 _ (by push_cast; linarith))⟩

/-- Substitution of the preceding gradient and residual bounds into (6.6)
gives the three decay powers used in item 2 of the proof of Theorem 7.1.
`B`, `Bt`, and `E` are upper bounds for the three supremum norms. -/
theorem induction_comparison_error_budget {μ ν r L LNext B Bt E δ A c : ℝ}
    (hμ : 1 ≤ μ) (hν : 1 ≤ ν) (hc : 0 < c) (hr : c * μ ^ (1 / 8 : ℝ) ≤ r)
    (hL : 0 < L) (hLNext : 0 ≤ LNext) (hA : 0 ≤ A) (hB₀ : 0 ≤ B)
    (hB : B ≤ μ ^ (1 / 32 : ℝ)) (hBt : Bt ≤ μ ^ (1 / 16 : ℝ))
    (hE : E ≤ μ ^ (-1 / 4 : ℝ))
    (hδ : δ ≤ A * (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (B ^ 2 + Bt) /
      (ν * couplingRatioOfGain L) + B / r + E / ν)) :
    δ ≤ A * (5 + c⁻¹) *
      (L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ) + μ ^ (-3 / 32 : ℝ) + μ ^ (-1 / 4 : ℝ)) := by
  have hμ₀ : 0 < μ := zero_lt_one.trans_le hμ
  have hν₀ : 0 < ν := zero_lt_one.trans_le hν
  have hr₀ : 0 < r := (mul_pos hc (Real.rpow_pos_of_pos hμ₀ _)).trans_le hr
  have hε : 0 < couplingRatioOfGain L := inv_pos.mpr (pow_pos hL _)
  have hSquare : (μ ^ (1 / 32 : ℝ)) ^ (2 : ℕ) = μ ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ₀.le]
    norm_num
  have hDeriv : B ^ 2 + Bt ≤ 2 * μ ^ (1 / 16 : ℝ) := by
    have h := (pow_le_pow_left₀ hB₀ hB 2)
    rw [hSquare] at h
    linarith
  have hDenom : (couplingRatioOfGain L) ≤ ν * couplingRatioOfGain L :=
    le_mul_of_one_le_left hε.le hν
  have h₁ : 2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (B ^ 2 + Bt) /
       (ν * couplingRatioOfGain L) ≤ 4 * (L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ)) := by
    calc
      _ ≤ (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (2 * μ ^ (1 / 16 : ℝ))) /
          (ν * couplingRatioOfGain L) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDeriv (by positivity)) (by positivity)
      _ ≤ (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (2 * μ ^ (1 / 16 : ℝ))) /
          couplingRatioOfGain L :=
        div_le_div_of_nonneg_left (by positivity) hε hDenom
      _ = _ := by
        have hPowers : μ ^ (-1 / 8 : ℝ) * μ ^ (1 / 16 : ℝ) = μ ^ (-1 / 16 : ℝ) := by
          rw [← Real.rpow_add hμ₀]
          norm_num
        rw [couplingRatioOfGain, div_inv_eq_mul, ← hPowers]
        ring
  have h₂ : B / r ≤ c⁻¹ * μ ^ (-3 / 32 : ℝ) := by
    calc
      _ ≤ (μ ^ (1 / 32 : ℝ)) / r := div_le_div_of_nonneg_right hB hr₀.le
      _ ≤ (μ ^ (1 / 32 : ℝ)) / (c * μ ^ (1 / 8 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hr
      _ = _ := by
        rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg hμ₀.le]
        rw [mul_left_comm, ← Real.rpow_add hμ₀]
        norm_num
  have h₃ : E / ν ≤ μ ^ (-1 / 4 : ℝ) :=
    (div_le_div_of_nonneg_right hE hν₀.le).trans (div_le_self (by positivity) hν)
  have hC4 : 4 ≤ 5 + c⁻¹ := by linarith [inv_nonneg.mpr hc.le]
  have hC1 : 1 ≤ 5 + c⁻¹ := by linarith [inv_nonneg.mpr hc.le]
  have hCr : c⁻¹ ≤ 5 + c⁻¹ := by linarith
  calc
    δ ≤ A * (4 * (L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ)) +
        c⁻¹ * μ ^ (-3 / 32 : ℝ) + μ ^ (-1 / 4 : ℝ)) :=
      hδ.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hA)
    _ ≤ A * ((5 + c⁻¹) * (L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ)) +
        (5 + c⁻¹) * μ ^ (-3 / 32 : ℝ) + (5 + c⁻¹) * μ ^ (-1 / 4 : ℝ)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) hA
      · exact mul_le_mul_of_nonneg_right hC4 (by positivity)
      · exact mul_le_mul_of_nonneg_right hCr (by positivity)
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1
          (Real.rpow_nonneg hμ₀.le (-1 / 4 : ℝ))
    _ = _ := by ring

/-- For the two successive gains of item 2 in Theorem 7.1, the bounds on the
normalized window and the error imply both smallness inequalities (2.5)
uniformly above one base frequency. -/
theorem exists_induction_amplification_smallness (C₀ : ℕ) (C_T C_δ : ℝ)
    (hCT : 0 ≤ C_T) (hCδ : 0 ≤ C_δ) :
    ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ μ ≥ N₀, ∀ L LNext T δ : ℝ,
      Real.log μ ≤ L → L ≤ LNext → LNext ≤ (Real.log μ) ^ 2 →
      0 ≤ T → T ≤ C_T * LNext ^ 4 → 0 ≤ δ →
      δ ≤ C_δ * (L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ) +
        μ ^ (-3 / 32 : ℝ) + μ ^ (-1 / 4 : ℝ)) →
      (C₀ : ℝ) * couplingRatioOfGain L ≤ 1 ∧
        (C₀ : ℝ) * T ^ C₀ * δ ≤ couplingRatioOfGain L := by
  let p := 4 * C₀ + 7
  let A : ℝ := 3 * (C₀ : ℝ) * C_T ^ C₀ * C_δ
  obtain ⟨N, hN, hBudget⟩ := exists_uniform_log_gain_budget
    (ι := Unit) (fun _ => A) (fun _ => p) (fun _ => 1 / 16)
    (fun _ => by dsimp [A]; positivity) (fun _ => by norm_num)
  let top := max N (Real.exp (1 + (C₀ : ℝ)))
  refine ⟨top, hN.trans_le (le_max_left _ _), ?_⟩
  intro μ hμ L LNext T δ hLogL hLLNext hLNextLog hT₀ hT hδ₀ hδ
  have hμ₁ : 1 ≤ μ := hN.le.trans ((le_max_left _ _).trans hμ)
  have hμ₀ : 0 < μ := zero_lt_one.trans_le hμ₁
  have hLog : 1 + (C₀ : ℝ) ≤ Real.log μ := by
    have h := Real.log_le_log (Real.exp_pos (1 + (C₀ : ℝ)))
      (show Real.exp (1 + (C₀ : ℝ)) ≤ μ from (le_max_right _ _).trans hμ)
    rwa [Real.log_exp] at h
  have hL₁ : 1 ≤ L := by linarith
  have hL₀ : 0 < L := zero_lt_one.trans_le hL₁
  have hLNext₁ : 1 ≤ LNext := hL₁.trans hLLNext
  have hLNext₀ : 0 ≤ LNext := zero_le_one.trans hLNext₁
  have hLsq : L ^ 2 ≤ LNext ^ 2 := pow_le_pow_left₀ hL₀.le hLLNext 2
  have hLNext5 : 1 ≤ LNext ^ (5 : ℕ) := one_le_pow₀ hLNext₁
  have hInv : μ ^ (-1 / 16 : ℝ) ≤ LNext ^ 5 * μ ^ (-1 / 16 : ℝ) :=
    le_mul_of_one_le_left (by positivity) hLNext5
  have hmain : L ^ 2 * LNext ^ 3 * μ ^ (-1 / 16 : ℝ) ≤
      LNext ^ 5 * μ ^ (-1 / 16 : ℝ) := by
    rw [show LNext ^ (5 : ℕ) = LNext ^ 2 * LNext ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLsq (by positivity))
      (by positivity)
  have hsecond : μ ^ (-3 / 32 : ℝ) ≤ LNext ^ 5 * μ ^ (-1 / 16 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hμ₁
      (by norm_num : (-3 / 32 : ℝ) ≤ -1 / 16)).trans hInv
  have hthird : μ ^ (-1 / 4 : ℝ) ≤ LNext ^ 5 * μ ^ (-1 / 16 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hμ₁
      (by norm_num : (-1 / 4 : ℝ) ≤ -1 / 16)).trans hInv
  have hδ' : δ ≤ 3 * C_δ * (LNext ^ 5 * μ ^ (-1 / 16 : ℝ)) := by
    exact hδ.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain hsecond) hthird) hCδ).trans_eq
      (by ring))
  have hTPow : T ^ C₀ ≤ (C_T * LNext ^ 4) ^ C₀ := pow_le_pow_left₀ hT₀ hT _
  have hProd : (C₀ : ℝ) * T ^ C₀ * δ * L ^ 2 ≤ 1 := by
    calc
      _ ≤ (C₀ : ℝ) * ((C_T * LNext ^ 4) ^ C₀) *
          (3 * C_δ * (LNext ^ 5 * μ ^ (-1 / 16 : ℝ))) * LNext ^ 2 := by
        gcongr
      _ = A * LNext ^ p * μ ^ (-1 / 16 : ℝ) := by
        have hP : LNext ^ p = LNext ^ (4 * C₀) * LNext ^ 5 * LNext ^ 2 := by
          dsimp [p]
          rw [show 4 * C₀ + 7 = (4 * C₀ + 5) + 2 by omega, pow_add, pow_add]
        rw [hP, mul_pow, ← pow_mul]
        unfold A
        ring
      _ ≤ μ ^ (1 / 16 : ℝ) * μ ^ (-1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (hBudget μ ((le_max_left _ _).trans hμ) LNext hLNext₀ hLNextLog ()) (by positivity)
      _ = 1 := by rw [← Real.rpow_add hμ₀]; norm_num
  unfold couplingRatioOfGain
  constructor
  · rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos hL₀)).mpr
    have hLsq₁ : L ≤ L ^ 2 := by rw [pow_two]; exact le_mul_of_one_le_right hL₀.le hL₁
    linarith
  · rw [← one_div]
    exact (le_div_iff₀ (sq_pos_of_pos hL₀)).mpr hProd

/-- Bounds for the length of the normalized comparison window
`2 * r * μ^(-1/8) * LNext^3` used in item 2 of Theorem 7.1. -/
theorem induction_normalized_comparison_window {μ r L LNext c C : ℝ}
    (hμ : 0 < μ) (hC : 0 ≤ C) (hLNext : 0 ≤ LNext) (hL : L ≤ LNext)
    (hrLo : c * μ ^ (1 / 8 : ℝ) ≤ r) (hrHi : r ≤ C * μ ^ (1 / 8 : ℝ) * L) :
    let halfTime := μ ^ (-1 / 8 : ℝ) * LNext ^ 3
    2 * c * LNext ^ 3 ≤ 2 * r * halfTime ∧ 2 * r * halfTime ≤ (2 * C) * LNext ^ 4 := by
  let halfTime := μ ^ (-1 / 8 : ℝ) * LNext ^ 3
  have hhalf : 0 ≤ halfTime := by unfold halfTime; positivity
  have hPowers : μ ^ (1 / 8 : ℝ) * μ ^ (-1 / 8 : ℝ) = 1 := by
    rw [← Real.rpow_add hμ]
    norm_num
  have hCancel : μ ^ (1 / 8 : ℝ) * halfTime = LNext ^ 3 := by
    unfold halfTime
    rw [← mul_assoc, hPowers, one_mul]
  constructor
  · calc
      2 * c * LNext ^ 3 = 2 * (c * μ ^ (1 / 8 : ℝ)) * halfTime := by
        rw [show 2 * (c * μ ^ (1 / 8 : ℝ)) * halfTime =
          (2 * c) * (μ ^ (1 / 8 : ℝ) * halfTime) by ring, hCancel]
      _ ≤ 2 * r * halfTime :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrLo (by norm_num)) hhalf
  · calc
      2 * r * halfTime ≤ 2 * (C * μ ^ (1 / 8 : ℝ) * L) * halfTime :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrHi (by norm_num)) hhalf
      _ = (2 * C) * (L * LNext ^ 3) := by
        rw [show 2 * (C * μ ^ (1 / 8 : ℝ) * L) * halfTime =
          (2 * C) * (L * (μ ^ (1 / 8 : ℝ) * halfTime)) by ring, hCancel]
      _ ≤ _ := by
        rw [pow_succ LNext 3, mul_comm (LNext ^ 3) LNext]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (by positivity)) (by positivity)

/-- The estimates on the older gradient, the preceding strength through
its comparison rate, the residual and the gains give (2.5) on the actual
normalized interval of item 2 in Theorem 7.1. The last hypothesis is the
physical-frame error estimate (6.6). -/
theorem exists_induction_amplification_step_comparison (C₀ : ℕ) (A c C : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ N₀ : ℝ, 1 < N₀ ∧
      ∀ {old μ ν r L LNext B Bt E δ : ℝ} {b q : ℕ},
        N₀ ≤ μ → 1 ≤ b → 1 ≤ old → μ = old ^ frequencyExponent b q →
        1 ≤ ν → c * μ ^ (1 / 8 : ℝ) ≤ r → r ≤ C * μ ^ (1 / 8 : ℝ) * L →
        Real.log μ ≤ L → L ≤ LNext → LNext ≤ (Real.log μ) ^ 2 →
        0 ≤ B → B ≤ old ^ 9 → Bt ≤ old ^ 18 → E ≤ μ ^ (-1 / 4 : ℝ) → 0 ≤ δ →
        let halfTime := μ ^ (-1 / 8 : ℝ) * LNext ^ 3
        let T := 2 * r * halfTime
        let ε := couplingRatioOfGain L
        δ ≤ A * (2 * halfTime * (B ^ 2 + Bt) / (ν * ε) + B / r + E / ν) →
        2 ≤ T ∧ (C₀ : ℝ) * ε ≤ 1 ∧ (C₀ : ℝ) * T ^ C₀ * δ ≤ ε := by
  obtain ⟨N, hN, hSmall⟩ :=
    exists_induction_amplification_smallness C₀ (2 * C) (A * (5 + c⁻¹)) (by positivity) (by positivity)
  let top := max N (Real.exp (1 + c⁻¹))
  refine ⟨top, hN.trans_le (le_max_left _ _), ?_⟩
  intro old μ ν r L LNext B Bt E δ b q htop hb hold hRec hν hrLo hrHi
    hLogL hLLNext hLNextLog hB₀ hB hBt hE hδ₀ halfTime T ε hδ
  have hLarge : N ≤ μ := (le_max_left _ _).trans htop
  have hμ : 1 ≤ μ := hN.le.trans hLarge
  have hLog : 1 + c⁻¹ ≤ Real.log μ := by
    have h := Real.log_le_log (Real.exp_pos (1 + c⁻¹))
      (show Real.exp (1 + c⁻¹) ≤ μ from (le_max_right _ _).trans htop)
    rwa [Real.log_exp] at h
  have hL : 0 < L := by linarith [inv_nonneg.mpr hc.le]
  have hLNext₁ : 1 ≤ LNext := by linarith [inv_nonneg.mpr hc.le]
  have hLNext₀ := zero_le_one.trans hLNext₁
  have hInv : c⁻¹ ≤ LNext ^ (3 : ℕ) := (show c⁻¹ ≤ LNext by linarith).trans
    (le_self_pow₀ hLNext₁ (by decide))
  have hClock : 2 ≤ 2 * c * LNext ^ (3 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hInv hc.le
    rw [mul_inv_cancel₀ hc.ne'] at h
    linarith
  obtain ⟨hTLo, hTHi⟩ := induction_normalized_comparison_window (zero_lt_one.trans_le hμ) hC
    hLNext₀ hLLNext hrLo hrHi
  have hT₂ : 2 ≤ T := hClock.trans hTLo
  obtain ⟨hBG, hBtG⟩ := induction_older_gradient_scales hb hold hRec hB hBt
  have hError := induction_comparison_error_budget hμ hν hc hrLo hL hLNext₀ hA hB₀ hBG hBtG hE hδ
  exact ⟨hT₂, hSmall μ hLarge L LNext T δ hLogL hLLNext hLNextLog
    ((by norm_num : (0 : ℝ) ≤ 2).trans hT₂) hTHi hδ₀ hError⟩

end TorusEuler
