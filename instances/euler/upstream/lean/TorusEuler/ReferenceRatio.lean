import TorusEuler.ReferenceCouplings
import TorusEuler.ReferenceLateBounds

open Set

namespace TorusEuler.ReferenceRiccati

noncomputable section

/-- The reference value of the first coupling divided by the parent coupling. -/
def referenceNu (ε τ : ℝ) (Y : ℝ → ℝ) : ℝ :=
  (x ε τ + ε + 2 * ε * τ * Y τ) * s ε τ

/-- The reference value of the second coupling divided by the parent coupling. -/
def referenceEta (ε τ : ℝ) (Y : ℝ → ℝ) : ℝ :=
  (-1 + ε * x ε τ + 2 * (1 + x ε τ ^ 2) * (Y τ) ^ 2
    + 2 * ε * τ * x ε τ * Y τ) * s ε τ

private theorem reference_coupling_forms {ε τ : ℝ} {Y e : ℝ → ℝ}
    (hform : Y = referenceY ε e) :
    referenceNu ε τ Y =
      (x ε τ - ε + 2 * ε * s ε τ ^ 2 + 2 * ε * τ * s ε τ * (1 + e τ)) * s ε τ ∧
    referenceEta ε τ Y / s ε τ =
      1 + 4 * e τ + 2 * (e τ) ^ 2 + ε * x ε τ * s ε τ ^ 2 := by
  have hY : Y τ = s ε τ * (1 + e τ) - ε * τ * x ε τ * s ε τ ^ 2 / 2 := by
    rw [hform, referenceY, damping]
    ring
  obtain ⟨hν, hη⟩ := referenceCouplingNumerators ε τ (x ε τ) (s ε τ) (e τ) (Y τ)
    rfl (by linear_combination s_sq_mul ε τ) hY
  constructor
  · exact congrArg (fun v => v * s ε τ) hν
  · unfold referenceEta
    rw [mul_div_cancel_right₀ _ (s_pos ε τ).ne', hη]

/-- The early reference coupling is at least epsilon throughout the range used in Lemma 2.5. -/
theorem referenceNu_early_lower {ε τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ Real.sqrt 2 / ε)
    (hform : Y = referenceY ε e) (he : 0 ≤ e τ) :
    ε ≤ referenceNu ε τ Y := by
  have hxs := x_nonneg hε.le τ
  have hs := s_pos ε τ
  have hτ₂ : ε * τ ≤ 2 := by
    have h := (le_div_iff₀ hε).mp hτ
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      apply (Real.sqrt_le_left (by norm_num)).mpr
      norm_num
    rw [mul_comm] at h
    exact h.trans hsqrt
  have hY : 0 < Y τ := by
    rw [hform]
    exact referenceY_pos hε.le hτ₂ he
  have hpoly : ε ^ 2 * (1 + x ε τ ^ 2) ≤ (x ε τ + ε) ^ 2 := by
    have hεsq : ε ^ 2 ≤ 1 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hεsq) (sq_nonneg (x ε τ)), mul_nonneg hxs hε.le]
  have hsq : ε ^ 2 ≤ ((x ε τ + ε) * s ε τ) ^ 2 := by
    calc
      _ = s ε τ ^ 2 * (ε ^ 2 * (1 + x ε τ ^ 2)) := by
        linear_combination -(ε ^ 2) * s_sq_mul ε τ
      _ ≤ s ε τ ^ 2 * (x ε τ + ε) ^ 2 := mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ (x ε τ + ε) * s ε τ :=
      (sq_le_sq₀ hε.le (mul_nonneg (add_nonneg hxs hε.le) hs.le)).mp hsq
    _ ≤ referenceNu ε τ Y := by
      unfold referenceNu
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hs.le

private theorem late_clock_bounds {ε τ : ℝ} (hε : 0 < ε)
    (hτ : Real.sqrt 2 / ε ≤ τ) : 0 < τ ∧ 1 / ε ≤ x ε τ ∧ 1 ≤ ε * τ := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    exact Real.one_le_sqrt.mpr (by norm_num)
  have ht₀ : 0 < τ := (by positivity : 0 < Real.sqrt 2 / ε).trans_le hτ
  have ht : Real.sqrt 2 ≤ ε * τ := by rw [mul_comm]; exact (div_le_iff₀ hε).mp hτ
  refine ⟨ht₀, ?_, hsqrt.trans ht⟩
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg 2) ht 2
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  rw [div_le_iff₀ hε, x]
  nlinarith

/-- Explicit versions of the two late reference coupling estimates in Lemma 2.5. -/
theorem reference_couplings_late_bound {ε τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hτ : Real.sqrt 2 / ε ≤ τ)
    (hform : Y = referenceY ε e) (he : e τ ∈ Icc 0 (ε / 8)) :
    |referenceNu ε τ Y - 1| ≤ 7 * ε ^ 2 ∧
      |referenceEta ε τ Y / s ε τ - 1| ≤ 2 * ε := by
  obtain ⟨ht₀, hxlow, ht₁⟩ := late_clock_bounds hε hτ
  have hx₀ : 0 < x ε τ := (by positivity : 0 < 1 / ε).trans_le hxlow
  have hs := s_pos ε τ
  have hscale : s ε τ ≤ ε := by
    apply (s_le_inv_x hx₀).trans
    simpa only [one_div, inv_inv] using inv_anti₀ (by positivity : 0 < 1 / ε) hxlow
  have hxs₀ : 0 ≤ x ε τ * s ε τ := mul_nonneg hx₀.le hs.le
  have hxs₁ : x ε τ * s ε τ ≤ 1 := (x_mul_s_lt_one ε τ).le
  have hxs_lower : 1 - ε ^ 2 ≤ x ε τ * s ε τ := by
    have hs_sq := pow_le_pow_left₀ hs.le hscale 2
    nlinarith [s_sq_mul ε τ, mul_nonneg hxs₀ (sub_nonneg.mpr hxs₁)]
  have ht_scale : ε * τ * s ε τ ≤ 2 * ε := by
    calc
      _ ≤ ε * τ * (x ε τ)⁻¹ :=
        mul_le_mul_of_nonneg_left (s_le_inv_x hx₀) (mul_pos hε ht₀).le
      _ = 2 / τ := by unfold x; field_simp
      _ ≤ _ := (div_le_iff₀ ht₀).mpr (by nlinarith)
  have hscale_sq := mul_le_mul_of_nonneg_left hscale hε.le
  have he₀ : 0 ≤ e τ := he.1
  have he₁ : e τ ≤ ε / 8 := he.2
  obtain ⟨hν, hη⟩ := reference_coupling_forms (τ := τ) hform
  constructor
  · rw [hν, abs_le]
    have hprod₀ : 0 ≤ ε * τ * s ε τ * (1 + e τ) * s ε τ := by positivity
    have hprod₁ : ε * τ * s ε τ * (1 + e τ) * s ε τ ≤ (2 * ε) * (9 / 8) * ε := by
      exact mul_le_mul (mul_le_mul ht_scale (by linarith) (by positivity) (by positivity))
        hscale hs.le (by positivity)
    have hcube : ε * s ε τ ^ 2 * s ε τ ≤ ε ^ 2 := by
      have hs₂ : s ε τ ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ hs.le (s_le_one ε τ) 2
      calc
        _ ≤ ε * 1 * s ε τ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs₂ hε.le) hs.le
        _ ≤ _ := by nlinarith
    have hcube₀ : 0 ≤ ε * s ε τ ^ 2 * s ε τ := by positivity
    constructor <;> nlinarith
  · rw [hη, abs_le]
    have hforce : ε * x ε τ * s ε τ ^ 2 ≤ ε ^ 2 := by
      calc
        _ = (x ε τ * s ε τ) * (ε * s ε τ) := by ring
        _ ≤ _ := by simpa [pow_two] using
          (mul_le_mul hxs₁ hscale_sq (mul_nonneg hε.le hs.le) (by norm_num : (0 : ℝ) ≤ 1))
    have he2 := pow_le_pow_left₀ he₀ he₁ 2
    have hε2 : ε ^ 2 ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]
    have hf₀ : 0 ≤ ε * x ε τ * s ε τ ^ 2 := by positivity
    constructor <;> nlinarith [sq_nonneg (e τ)]

private theorem ratio_error_bound {u v dU dV : ℝ} (hu : 0 < u)
    (hU : |u - 1| ≤ dU) (hV : |v - 1| ≤ dV) :
    |v / u - 1| ≤ (dV + dU) / u := by
  have heq : v / u - 1 = ((v - 1) - (u - 1)) / u := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hu]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hV hU)) hu.le

private theorem seven_sq_le_eps {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 16) :
    7 * ε ^ 2 ≤ 7 * ε / 16 := by
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]

/-- The late reference coupling ratio from Lemma 2.5 is within a relative
error of four epsilon from the clock factor. -/
theorem reference_couplingRatio_late_bound {ε τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 16) (hτ : Real.sqrt 2 / ε ≤ τ)
    (hform : Y = referenceY ε e) (he : e τ ∈ Icc 0 (ε / 8)) :
    ε ≤ referenceNu ε τ Y ∧
      |(referenceEta ε τ Y / referenceNu ε τ Y) / s ε τ - 1| ≤ 4 * ε := by
  obtain ⟨hν, hη⟩ := reference_couplings_late_bound hε (by linarith) hτ hform he
  have hν' : |referenceNu ε τ Y - 1| ≤ ε := hν.trans ((seven_sq_le_eps hε hε₁).trans (by linarith))
  have hνlower : 3 / 4 ≤ referenceNu ε τ Y := by linarith [(abs_le.mp hν').1]
  have hpos : 0 < referenceNu ε τ Y := by linarith
  refine ⟨by linarith, ?_⟩
  have heq : (referenceEta ε τ Y / referenceNu ε τ Y) / s ε τ =
      (referenceEta ε τ Y / s ε τ) / referenceNu ε τ Y := by ring
  rw [heq]
  calc
    _ ≤ (2 * ε + ε) / referenceNu ε τ Y := ratio_error_bound hpos hν' hη
    _ ≤ _ := (div_le_iff₀ hpos).mpr (by
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hνlower)])

theorem inv_sq_window_le_s {ε T τ : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hT : 2 ≤ T) (hτ : τ ∈ Icc 0 T) : (T ^ 2)⁻¹ ≤ s ε τ := by
  have hT₀ : 0 ≤ T := by linarith
  have hx₀ : 0 ≤ x ε τ := x_nonneg hε τ
  have hx : x ε τ ≤ T ^ 2 / 2 := by
    have hτsq := pow_le_pow_left₀ hτ.1 hτ.2 2
    have hετsq := mul_le_mul_of_nonneg_right hε₁ (sq_nonneg τ)
    unfold x
    linarith
  have hsquare := pow_le_pow_left₀ hx₀ hx 2
  have hTsq : 4 ≤ T ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT 2
    norm_num at h
    exact h
  have hTfour := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hTsq 2
  unfold s
  apply inv_anti₀ (by positivity)
  apply (Real.sqrt_le_left (sq_nonneg T)).mpr
  nlinarith

/-- The finite-window smallness in (2.5) absorbs a polynomial comparison
constant and two additional powers of the window length. -/
theorem coupling_error_of_polynomial_smallness {C T δ ε : ℝ} {p C₀ : ℕ}
    (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hp : p + 2 ≤ C₀) (hC₀ : 8 * C ≤ C₀)
    (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) :
    C * T ^ p * δ ≤ ε / (8 * T ^ 2) := by
  have hT₁ : 1 ≤ T := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 8 * T ^ 2)).mpr
  calc
    _ = (8 * C) * T ^ (p + 2) * δ := by rw [pow_add]; ring
    _ ≤ (C₀ : ℝ) * T ^ C₀ * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ
      exact mul_le_mul hC₀ (pow_le_pow_right₀ hT₁ hp) (by positivity) (by positivity)
    _ ≤ ε := hsmall

/-- Perturbative transfer of the reference bounds to the actual normalized
couplings in (2.10), using the common quantitative error from Lemma 2.5. -/
theorem actual_couplings_of_reference_error {ε T : ℝ} {Y e ν η : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 16) (hT : 2 ≤ T)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hνerr : ∀ t ∈ Icc 0 T, |ν t - referenceNu ε t Y| ≤ ε / (8 * T ^ 2))
    (hηerr : ∀ t ∈ Icc 0 T, |η t - referenceEta ε t Y| ≤ ε / (8 * T ^ 2)) :
    (∀ t ∈ Icc 0 T, ε / 2 ≤ ν t) ∧
      (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
        |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2) := by
  have hT₁ : 1 ≤ T := by linarith
  have hTsq : 1 ≤ T ^ 2 := by simpa using pow_le_pow_left₀ zero_le_one hT₁ 2
  have herror : ε / (8 * T ^ 2) ≤ ε / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * T ^ 2)).mpr
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hTsq)]
  have hlate (t : ℝ) (ht : t ∈ Icc 0 T) (htlate : Real.sqrt 2 / ε ≤ t) :
      |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2 := by
    obtain ⟨hν, hη⟩ := reference_couplings_late_bound hε (by linarith) htlate hform (he ht.1)
    have hν' : |ν t - 1| ≤ ε := by
      have hsum := (abs_sub_le (ν t) (referenceNu ε t Y) (1 : ℝ)).trans
        (add_le_add ((hνerr t ht).trans herror) hν)
      exact hsum.trans (by linarith [seven_sq_le_eps hε hε₁])
    have hscaled_err : |η t / s ε t - referenceEta ε t Y / s ε t| ≤ ε / 8 := by
      rw [← sub_div, abs_div, abs_of_pos (s_pos ε t), div_le_iff₀ (s_pos ε t)]
      calc
        _ ≤ ε / (8 * T ^ 2) := hηerr t ht
        _ = (ε / 8) * (T ^ 2)⁻¹ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (inv_sq_window_le_s hε.le (by linarith) hT ht) (by positivity)
    have hη' : |η t / s ε t - 1| ≤ 3 * ε := by
      exact ((abs_sub_le _ (referenceEta ε t Y / s ε t) _).trans
        (add_le_add hscaled_err hη)).trans (by linarith)
    have hνpos : 0 < ν t := by linarith [(abs_le.mp hν').1]
    refine ⟨hν', ?_⟩
    have heq : (η t / ν t) / s ε t = (η t / s ε t) / ν t := by ring
    rw [heq]
    calc
      _ ≤ (3 * ε + ε) / ν t := ratio_error_bound hνpos hν' hη'
      _ ≤ _ := (div_le_iff₀ hνpos).mpr (by linarith [(abs_le.mp hν').1])
  refine ⟨?_, hlate⟩
  intro t ht
  rcases le_or_gt (Real.sqrt 2 / ε) t with htlate | htearly
  · linarith [(abs_le.mp (hlate t ht htlate).1).1]
  · have hν := referenceNu_early_lower hε (by linarith) ht.1 htearly.le hform (he ht.1).1
    have herr := (hνerr t ht).trans herror
    linarith [(abs_le.mp herr).1]

/-- The coupling conclusions of Lemma 2.5 from a supplied polynomial
comparison bound, with the smallness hypothesis of (2.5). -/
theorem actual_couplings_of_polynomial_error {C ε T δ : ℝ} {p C₀ : ℕ} {Y e ν η : ℝ → ℝ}
    (hε : 0 < ε) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hC₀ : (16 : ℝ) ≤ C₀) (hp : p + 2 ≤ C₀) (hC : 8 * C ≤ C₀)
    (hsmallε : (C₀ : ℝ) * ε ≤ 1) (hsmallδ : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hνerr : ∀ t ∈ Icc 0 T, |ν t - referenceNu ε t Y| ≤ C * T ^ p * δ)
    (hηerr : ∀ t ∈ Icc 0 T, |η t - referenceEta ε t Y| ≤ C * T ^ p * δ) :
    (∀ t ∈ Icc 0 T, ε / 2 ≤ ν t) ∧
      (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
        |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2) := by
  have hε₁ : ε ≤ 1 / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hC₀ hε.le]
  have hbound := coupling_error_of_polynomial_smallness hT hδ hp hC hsmallδ
  exact actual_couplings_of_reference_error hε hε₁ hT hform he
    (fun t ht => (hνerr t ht).trans hbound) (fun t ht => (hηerr t ht).trans hbound)

/-- The coupling ratio window used at each putative crossing in Proposition 2.6. -/
theorem couplingRatio_clock_bounds {ε t ρ : ℝ} (hx : 1 ≤ x ε t)
    (hratio : |ρ / s ε t - 1| ≤ 1 / 2) :
    1 / (4 * x ε t) ≤ ρ ∧ ρ ≤ 3 / (2 * x ε t) := by
  have hs := s_pos ε t
  obtain ⟨hrl, hru⟩ := abs_le.mp hratio
  have hlo : s ε t / 2 ≤ ρ := by
    have h : 1 / 2 ≤ ρ / s ε t := by linarith
    linarith [(le_div_iff₀ hs).mp h]
  have hhi : ρ ≤ 3 * s ε t / 2 := by
    have h : ρ / s ε t ≤ 3 / 2 := by linarith
    linarith [(div_le_iff₀ hs).mp h]
  constructor
  · calc
      _ = ((2 * x ε t)⁻¹) / 2 := by ring
      _ ≤ s ε t / 2 := div_le_div_of_nonneg_right (inv_two_mul_x_le_s hx) (by norm_num)
      _ ≤ _ := hlo
  · calc
      _ ≤ 3 * s ε t / 2 := hhi
      _ ≤ 3 * (x ε t)⁻¹ / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (s_le_inv_x (zero_lt_one.trans_le hx)) (by norm_num))
          (by norm_num)
      _ = _ := by ring

end

end TorusEuler.ReferenceRiccati
