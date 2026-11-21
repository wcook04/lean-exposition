import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Copies of the coupling conclusions of Lemma 2.7 with `Y > 0` taken from Lemma 2.5

In the early range `ετ ≤ √2` of the proof of Lemma 2.7, the text uses `Y > 0` "by
Lemma 2.5" (`sections/03_amplification.tex:842-843`). The library carrier of the
conclusions, `GrowingCoupling.coupling_conclusions_of_polynomial_budget`, reaches
`ReferenceRiccati.referenceNu_early_lower`, which derives `Y > 0` from the form (2.13) by
`ReferenceRiccati.referenceY_pos`, a step of the proof of Lemma 2.5 (`:511-512`). The
copies below take `Y > 0` on `[0, √2/ε]` as a hypothesis `hpos`, which the proof of
Lemma 2.7 supplies from the sign clause of `Statement.lemma_2_5`; nothing else changes.

| Library (namespace `TorusEuler`) | Copy (namespace `TorusEuler.Paper.Lib.S2b`) |
| --- | --- |
| `ReferenceRiccati.ratio_error_bound` (private) | `ratio_error_bound` (verbatim) |
| `ReferenceRiccati.seven_sq_le_eps` (private) | `seven_sq_le_eps` (verbatim) |
| `ReferenceRiccati.referenceNu_early_lower` | `referenceNu_lower_of_pos` |
| `ReferenceRiccati.actual_couplings_of_reference_error` | `actual_couplings_of_reference_error_of_pos` |
| `ReferenceRiccati.actual_couplings_of_polynomial_error` | `actual_couplings_of_polynomial_error_of_pos` |
| `GrowingCoupling.coupling_conclusions_of_polynomial_budget` | `coupling_conclusions_of_polynomial_budget_of_pos` |

The file also holds the polynomial budget `coupling_budget` of the proof of Lemma 2.7
(new glue). Namespace `TorusEuler.Paper.Lib.S2b`.
-/

open Set

namespace TorusEuler.Paper.Lib.S2b

open ReferenceRiccati

noncomputable section

/-- The polynomial budget `κ = C_κ T^q δ` of the proof of Lemma 2.7, with
`C_κ = |C₄| + |C₆| + 23` and `q = p₄ + p₆ + 3`, dominates the error of `ζ` from (2.10),
the `S⁻²` terms (`S⁻² ≤ 2δ`) and the error of `q = α₁/α₂` from (2.17) together with
the coefficient errors `21T³δ`, and is at most `1/2` under (2.7). -/
theorem coupling_budget {C4 C6 T δ ε : ℝ} {p4 p6 C₀ : ℕ} (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hq : p4 + p6 + 3 ≤ C₀) (hC₀ : 2 * (|C4| + |C6| + 23) ≤ (C₀ : ℝ))
    (hsmall : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε) (hε : ε ≤ 1) :
    let κ := (|C4| + |C6| + 23) * T ^ (p4 + p6 + 3) * δ
    0 ≤ κ ∧ |C4| * T ^ p4 * δ ≤ κ ∧ 2 * δ ≤ κ ∧
      |C6| * T ^ p6 * δ + 21 * T ^ 3 * δ ≤ κ ∧ κ ≤ 1 / 2 := by
  intro κ
  have hT₁ : 1 ≤ T := by linarith
  set q := p4 + p6 + 3 with hqdef
  have hpow {m : ℕ} (hm : m ≤ q) : T ^ m ≤ T ^ q := pow_le_pow_right₀ hT₁ hm
  have hq1 : 1 ≤ T ^ q := one_le_pow₀ hT₁
  have hA := abs_nonneg C4
  have hB := abs_nonneg C6
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨hκ0, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul (show |C4| ≤ |C4| + |C6| + 23 by linarith) (hpow (m := p4) (by omega))
      (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this hδ
  · nlinarith [mul_le_mul_of_nonneg_right hq1 hδ]
  · have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpow (m := p6) (by omega)) hB) hδ
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpow (m := 3) (by omega)) (by norm_num : (0 : ℝ) ≤ 21)) hδ
    have h3 : 0 ≤ (|C4| + 2) * T ^ q * δ := by positivity
    have : κ = |C6| * T ^ q * δ + 21 * T ^ q * δ + (|C4| + 2) * T ^ q * δ := by
      simp only [κ, ← hqdef]; ring
    linarith
  · exact absorb hT hδ (by positivity) (by omega) hC₀ hsmall hε

/-- Copy of the private `ReferenceRiccati.ratio_error_bound`. -/
theorem ratio_error_bound {u v dU dV : ℝ} (hu : 0 < u)
    (hU : |u - 1| ≤ dU) (hV : |v - 1| ≤ dV) :
    |v / u - 1| ≤ (dV + dU) / u := by
  have heq : v / u - 1 = ((v - 1) - (u - 1)) / u := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hu]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hV hU)) hu.le

/-- Copy of the private `ReferenceRiccati.seven_sq_le_eps`. -/
theorem seven_sq_le_eps {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 16) :
    7 * ε ^ 2 ≤ 7 * ε / 16 := by
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]

/-- Copy of `ReferenceRiccati.referenceNu_early_lower` with `Y τ > 0` as the hypothesis
`hY` (the library derives it for `ετ ≤ 2` from the form (2.13) by `referenceY_pos`, a step
of the proof of Lemma 2.5): where `Y > 0`, the reference value (2.22) of `ν₊/ν` is at
least `sin φ + ε cos φ ≥ ε` (`sections/03_amplification.tex:842-844`). -/
theorem referenceNu_lower_of_pos {ε τ : ℝ} {Y : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hτ₀ : 0 ≤ τ) (hY : 0 < Y τ) :
    ε ≤ referenceNu ε τ Y := by
  have hxs := x_nonneg hε.le τ
  have hs := s_pos ε τ
  have hpoly : ε ^ 2 * (1 + x ε τ ^ 2) ≤ (x ε τ + ε) ^ 2 := by
    have hεsq : ε ^ 2 ≤ 1 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hεsq) (sq_nonneg (x ε τ)), mul_nonneg hxs hε.le]
  have hsq : ε ^ 2 ≤ ((x ε τ + ε) * s ε τ) ^ 2 := by
    calc
      _ = s ε τ ^ 2 * (ε ^ 2 * (1 + x ε τ ^ 2)) := by
        linear_combination -(ε ^ 2) * s_sq_mul ε τ
      _ ≤ s ε τ ^ 2 * (x ε τ + ε) ^ 2 := mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
      _ = _ := by ring
  have hterm : 0 ≤ 2 * ε * τ * Y τ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε.le) hτ₀) hY.le
  calc
    _ ≤ (x ε τ + ε) * s ε τ :=
      (sq_le_sq₀ hε.le (mul_nonneg (add_nonneg hxs hε.le) hs.le)).mp hsq
    _ ≤ referenceNu ε τ Y := by
      unfold referenceNu
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hterm) hs.le

/-- Copy of `ReferenceRiccati.actual_couplings_of_reference_error` with `Y > 0` on
`[0, √2/ε]` as the hypothesis `hpos` (in place of the library's `referenceY_pos` step):
the conclusions `ν₊/ν ≥ ε/2` and, for `τ ≥ √2/ε`, `|ν₊/ν - 1| ≤ ε` and
`|(η₊/ν₊)/cos φ - 1| ≤ 1/2` from the reference values (2.22) and errors at most
`ε/(8T²)` (`sections/03_amplification.tex:832-871`). -/
theorem actual_couplings_of_reference_error_of_pos {ε T : ℝ} {Y e ν η : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 16) (hT : 2 ≤ T)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hpos : ∀ t ∈ Icc 0 (Real.sqrt 2 / ε), 0 < Y t)
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
  · have hν := referenceNu_lower_of_pos hε (by linarith) ht.1 (hpos t ⟨ht.1, htearly.le⟩)
    have herr := (hνerr t ht).trans herror
    linarith [(abs_le.mp herr).1]

/-- Copy of `ReferenceRiccati.actual_couplings_of_polynomial_error` with the hypothesis
`hpos` of `actual_couplings_of_reference_error_of_pos`. -/
theorem actual_couplings_of_polynomial_error_of_pos {C ε T δ : ℝ} {p C₀ : ℕ}
    {Y e ν η : ℝ → ℝ}
    (hε : 0 < ε) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hC₀ : (16 : ℝ) ≤ C₀) (hp : p + 2 ≤ C₀) (hC : 8 * C ≤ C₀)
    (hsmallε : (C₀ : ℝ) * ε ≤ 1) (hsmallδ : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hpos : ∀ t ∈ Icc 0 (Real.sqrt 2 / ε), 0 < Y t)
    (hνerr : ∀ t ∈ Icc 0 T, |ν t - referenceNu ε t Y| ≤ C * T ^ p * δ)
    (hηerr : ∀ t ∈ Icc 0 T, |η t - referenceEta ε t Y| ≤ C * T ^ p * δ) :
    (∀ t ∈ Icc 0 T, ε / 2 ≤ ν t) ∧
      (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
        |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2) := by
  have hε₁ : ε ≤ 1 / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hC₀ hε.le]
  have hbound := coupling_error_of_polynomial_smallness hT hδ hp hC hsmallδ
  exact actual_couplings_of_reference_error_of_pos hε hε₁ hT hform he hpos
    (fun t ht => (hνerr t ht).trans hbound) (fun t ht => (hηerr t ht).trans hbound)

/-- Copy of `GrowingCoupling.coupling_conclusions_of_polynomial_budget` with the hypothesis
`hpos` of `actual_couplings_of_reference_error_of_pos`: the conclusions of Lemma 2.7 from
errors `256T⁸κ + 2δ` of the normalized couplings, with `κ ≤ CT^pδ`
(`sections/03_amplification.tex:844-871`). -/
theorem coupling_conclusions_of_polynomial_budget_of_pos {C ε T δ κ : ℝ} {p C₀ : ℕ}
    {Y e ν η : ℝ → ℝ} (hε : 0 < ε) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hC₀ : (16 : ℝ) ≤ C₀) (hp : p + 10 ≤ C₀) (hC : 8 * (256 * C + 2) ≤ C₀)
    (hsmallε : (C₀ : ℝ) * ε ≤ 1) (hsmallδ : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hpos : ∀ t ∈ Icc 0 (Real.sqrt 2 / ε), 0 < Y t)
    (hκ : κ ≤ C * T ^ p * δ)
    (herr : ∀ t ∈ Icc 0 T, |ν t - referenceNu ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ ∧
      |η t - referenceEta ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ) :
    (∀ t ∈ Icc 0 T, ε / 2 ≤ ν t) ∧ (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
      |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2) := by
  have hT₁ : 1 ≤ T := by linarith
  have hpow : 1 ≤ T ^ (p + 8) := one_le_pow₀ hT₁
  have hbudget : 256 * T ^ 8 * κ + 2 * δ ≤ (256 * C + 2) * T ^ (p + 8) * δ := by
    calc
      _ ≤ 256 * T ^ 8 * (C * T ^ p * δ) + 2 * (T ^ (p + 8) * δ) :=
        add_le_add (mul_le_mul_of_nonneg_left hκ (by positivity))
          (by nlinarith only [mul_le_mul_of_nonneg_right hpow hδ])
      _ = _ := by rw [pow_add]; ring
  exact actual_couplings_of_polynomial_error_of_pos
    (C := 256 * C + 2) (p := p + 8) hε hT hδ hC₀ (by simpa only [Nat.add_assoc] using hp)
    hC hsmallε hsmallδ hform he hpos (fun t ht => (herr t ht).1.trans hbudget)
    (fun t ht => (herr t ht).2.trans hbudget)

end

end TorusEuler.Paper.Lib.S2b
