import TorusEuler.MovingAmplitudeCoefficients

/-! Reciprocal bounds for the amplitude coordinates in Lemma 2.3. -/

namespace TorusEuler.MovingAmplitude

private theorem abs_inv_sub_inv_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| = |a - b| / (a * b) := by
  rw [show a⁻¹ - b⁻¹ = (b - a) / (a * b) by field_simp,
    abs_div, abs_sub_comm b a, abs_of_pos (mul_pos ha hb)]

/-- On the domain of Lemma 2.3, both reciprocals are bounded and their
differences from the reference values are controlled by the coordinate error. -/
theorem amplitude_denominator_bounds {X Q Z x S M d : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hd : d ≤ 1 / 2)
    (hX : |X| ≤ M) (hx : |x| ≤ M) (hQ : |Q| ≤ M)
    (hclose : |X - x| + |Z - 1| ≤ d) :
    let m := normFactor X Q Z S
    1 / 2 ≤ Z ∧ 1 / 4 ≤ m ∧ Z⁻¹ ≤ 2 ∧ m⁻¹ ≤ 4 ∧
      |Z⁻¹ - 1| ≤ 2 * d ∧ |m⁻¹ - (1 + x ^ 2)⁻¹| ≤ 4 * (3 * M * d + M ^ 2 / S) := by
  let m := normFactor X Q Z S
  have hM₀ : 0 ≤ M := by linarith
  have hS₀ : 0 < S := by linarith
  have hZclose : |Z - 1| ≤ d := by linarith [abs_nonneg (X - x)]
  obtain ⟨hZlo, hZhi⟩ := abs_le.mp (hZclose.trans hd)
  have hZ : 1 / 2 ≤ Z := by linarith
  have hZ₀ : 0 < Z := by linarith
  have hm : 1 / 4 ≤ m := by
    have hZsq := (sq_le_sq₀ (by norm_num : 0 ≤ (1 : ℝ) / 2) hZ₀.le).mpr hZ
    unfold m normFactor
    linarith [sq_nonneg X, div_nonneg (sq_nonneg Q) (sq_nonneg S)]
  have hm₀ : 0 < m := by linarith
  have h1x : 0 < 1 + x ^ 2 := by positivity
  have hXsq : |X ^ 2 - x ^ 2| ≤ (3 * M) * |X - x| := by
    rw [show X ^ 2 - x ^ 2 = (X + x) * (X - x) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right ((abs_add_le X x).trans (by linarith)) (abs_nonneg _)
  have hZsq : |Z ^ 2 - 1| ≤ (3 * M) * |Z - 1| := by
    rw [show Z ^ 2 - 1 = (Z + 1) * (Z - 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < Z + 1)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hQsq : |Q ^ 2 / S ^ 2| ≤ M ^ 2 / S := by
    have hq := (sq_le_sq₀ (abs_nonneg Q) hM₀).mpr hQ
    rw [sq_abs] at hq
    rw [abs_of_nonneg (by positivity)]
    calc
      Q ^ 2 / S ^ 2 ≤ M ^ 2 / S ^ 2 := div_le_div_of_nonneg_right hq (sq_nonneg S)
      _ ≤ M ^ 2 / S :=
        div_le_div_of_nonneg_left (sq_nonneg M) hS₀ (by nlinarith)
  have hmdiff : |m - (1 + x ^ 2)| ≤ 3 * M * d + M ^ 2 / S := by
    rw [show m - (1 + x ^ 2) = (X ^ 2 - x ^ 2) + (Z ^ 2 - 1) + Q ^ 2 / S ^ 2 by
      unfold m normFactor
      ring]
    calc
      _ ≤ |X ^ 2 - x ^ 2| + |Z ^ 2 - 1| + |Q ^ 2 / S ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * M * |X - x| + 3 * M * |Z - 1| + M ^ 2 / S :=
        add_le_add (add_le_add hXsq hZsq) hQsq
      _ ≤ _ := by
        rw [← mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left hclose (by positivity)) le_rfl
  have hZinv : Z⁻¹ ≤ 2 := by
    simpa using (inv_le_inv₀ hZ₀ (show 0 < (1 : ℝ) / 2 by norm_num)).mpr hZ
  have hminv : m⁻¹ ≤ 4 := by
    simpa using (inv_le_inv₀ hm₀ (show 0 < (1 : ℝ) / 4 by norm_num)).mpr hm
  refine ⟨hZ, hm, hZinv, hminv, ?_, ?_⟩
  · calc
      |Z⁻¹ - 1| = |Z - 1| / Z := by simpa using abs_inv_sub_inv_eq hZ₀ zero_lt_one
      _ ≤ 2 * d := by
        rw [div_eq_mul_inv, mul_comm 2]
        exact mul_le_mul hZclose hZinv (inv_nonneg.mpr hZ₀.le) ((abs_nonneg _).trans hZclose)
  · rw [abs_inv_sub_inv_eq hm₀ h1x, div_eq_mul_inv, mul_inv]
    have h1xinv : (1 + x ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ h1x]
      linarith [sq_nonneg x]
    have hbound : m⁻¹ * (1 + x ^ 2)⁻¹ ≤ 4 :=
      (mul_le_mul hminv h1xinv (inv_nonneg.mpr h1x.le) (by norm_num)).trans_eq (mul_one _)
    calc
      _ ≤ (3 * M * d + M ^ 2 / S) * 4 :=
        mul_le_mul hmdiff hbound (by positivity) ((abs_nonneg _).trans hmdiff)
      _ = _ := mul_comm _ _

private theorem wave_coordinate_window_bounds {X Q Z ε τ T d : ℝ}
    (hT : 2 ≤ T) (hτ₀ : 0 ≤ τ) (hτT : τ ≤ T)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hd : d ≤ 1 / 2)
    (hclose : |X - ReferenceRiccati.x ε τ| + |Q + ε * τ| + |Z - 1| ≤ d) :
    |X| ≤ T ^ 2 ∧ |Q| ≤ T ^ 2 ∧ |Z| ≤ 3 / 2 ∧
      |ReferenceRiccati.x ε τ| ≤ T ^ 2 ∧ |-(ε * τ)| ≤ T := by
  let x := ReferenceRiccati.x ε τ
  change |X - x| + |Q + ε * τ| + |Z - 1| ≤ d at hclose
  have hx₀ : 0 ≤ x := ReferenceRiccati.x_nonneg hε₀ τ
  have hx : x ≤ T ^ 2 / 2 := by
    have hsquares := (sq_le_sq₀ hτ₀ (hτ₀.trans hτT)).mpr hτT
    unfold x ReferenceRiccati.x
    linarith [mul_le_mul_of_nonneg_right hε₁ (sq_nonneg τ)]
  have hXd : |X - x| ≤ 1 / 2 := by
    linarith [abs_nonneg (Q + ε * τ), abs_nonneg (Z - 1)]
  have hX : |X| ≤ T ^ 2 := by
    calc
      |X| = |(X - x) + x| := by rw [sub_add_cancel]
      _ ≤ |X - x| + |x| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hx₀]; nlinarith
  have hQd : |Q + ε * τ| ≤ 1 / 2 := by
    linarith [abs_nonneg (X - x), abs_nonneg (Z - 1)]
  have hQ : |Q| ≤ T ^ 2 := by
    calc
      |Q| = |(Q + ε * τ) - ε * τ| := by rw [add_sub_cancel_right]
      _ ≤ |Q + ε * τ| + |ε * τ| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (mul_nonneg hε₀ hτ₀)]
        nlinarith [mul_le_mul_of_nonneg_right hε₁ hτ₀]
  refine ⟨hX, hQ, ?_, ?_, ?_⟩
  · have hZd : |Z - 1| ≤ 1 / 2 := by
      linarith [abs_nonneg (X - x), abs_nonneg (Q + ε * τ)]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hZd
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [abs_of_nonneg hx₀]
    linarith [sq_nonneg T]
  · rw [abs_neg, abs_of_nonneg (mul_nonneg hε₀ hτ₀)]
    exact (mul_le_mul_of_nonneg_right hε₁ hτ₀).trans_eq (one_mul τ) |>.trans hτT

/-- The corresponding polynomial bounds on the normalized time window. The
coordinate error `d` can be taken from the wave-vector comparison. -/
theorem amplitude_denominator_bounds_on_window {X Q Z S ε τ T d δ : ℝ}
    (hT : 2 ≤ T) (hτ₀ : 0 ≤ τ) (hτT : τ ≤ T)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hS : 1 ≤ S) (hSinv : S⁻¹ ≤ 2 * δ)
    (hd : d ≤ 1 / 2)
    (hclose : |X - ReferenceRiccati.x ε τ| + |Q + ε * τ| + |Z - 1| ≤ d) :
    let m := normFactor X Q Z S
    1 / 2 ≤ Z ∧ 1 / 4 ≤ m ∧ Z⁻¹ ≤ 2 ∧ m⁻¹ ≤ 4 ∧ |Z⁻¹ - 1| ≤ 2 * d ∧
      |m⁻¹ - ReferenceRiccati.s ε τ ^ 2| ≤ 4 * (3 * T ^ 2 * d + 2 * T ^ 4 * δ) := by
  let x := ReferenceRiccati.x ε τ
  obtain ⟨hX, hQ, _, hxabs, _⟩ := wave_coordinate_window_bounds hT hτ₀ hτT hε₀ hε₁ hd hclose
  have hcloseXZ : |X - x| + |Z - 1| ≤ d := by
    change |X - x| + |Q + ε * τ| + |Z - 1| ≤ d at hclose
    linarith [abs_nonneg (Q + ε * τ)]
  obtain ⟨hZ, hm, hZinv, hminv, hZdiff, hmdiff⟩ :=
    amplitude_denominator_bounds (by nlinarith : 1 ≤ T ^ 2) hS hd hX hxabs hQ hcloseXZ
  refine ⟨hZ, hm, hZinv, hminv, hZdiff, ?_⟩
  have hs : ReferenceRiccati.s ε τ ^ 2 = (1 + x ^ 2)⁻¹ := by
    rw [ReferenceRiccati.s, inv_pow, Real.sq_sqrt (by positivity)]
  rw [hs]
  refine hmdiff.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num))
  calc
    (T ^ 2) ^ 2 / S = T ^ 4 * S⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ T ^ 4 * (2 * δ) := mul_le_mul_of_nonneg_left hSinv (by positivity)
    _ = 2 * T ^ 4 * δ := by ring

/-- The six wave scalars in the amplitude polynomials satisfy a single size
bound and a single comparison bound on the time window of Lemma 2.3. -/
theorem amplitude_wave_scalar_box {X Q Z S ε τ T δ : ℝ}
    (hT : 2 ≤ T) (hτ₀ : 0 ≤ τ) (hτT : τ ≤ T)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hS : 1 ≤ S) (hSinv : S⁻¹ ≤ 2 * δ)
    (hδ : 0 ≤ δ) (hsmall : 120 * δ * T ^ 6 ≤ 1 / 2)
    (hclose : |X - ReferenceRiccati.x ε τ| + |Q + ε * τ| + |Z - 1| ≤ 120 * δ * T ^ 6) :
    let actual : Fin 6 → ℝ := ![X, Q, Z, S⁻¹, Z⁻¹, (normFactor X Q Z S)⁻¹]
    let reference : Fin 6 → ℝ :=
      ![ReferenceRiccati.x ε τ, -ε * τ, 1, 0, 1, ReferenceRiccati.s ε τ ^ 2]
    1 / 2 ≤ Z ∧ (∀ i, |actual i| ≤ 4 * T ^ 2) ∧ (∀ i, |reference i| ≤ 4 * T ^ 2) ∧
      ∀ i, |actual i - reference i| ≤ 1448 * T ^ 8 * δ := by
  let d := 120 * δ * T ^ 6
  obtain ⟨hX, hQ, hZabs, hx, hq⟩ :=
    wave_coordinate_window_bounds hT hτ₀ hτT hε₀ hε₁ hsmall hclose
  obtain ⟨hZ, hm, hZinv, hminv, hZdiff, hmdiff⟩ :=
    amplitude_denominator_bounds_on_window hT hτ₀ hτT hε₀ hε₁ hS hSinv hsmall hclose
  have hT₁ : 1 ≤ T := by linarith
  have hscale : 4 ≤ 4 * T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hS₀ : 0 < S := by linarith
  have hs₀ := (ReferenceRiccati.s_pos ε τ).le
  have hs := (sq_le_sq₀ hs₀ zero_le_one).mpr (ReferenceRiccati.s_le_one ε τ)
  have hT48 : T ^ 4 ≤ T ^ 8 := pow_le_pow_right₀ hT₁ (by decide)
  have hT68 : T ^ 6 ≤ T ^ 8 := pow_le_pow_right₀ hT₁ (by decide)
  have hmerror : |(normFactor X Q Z S)⁻¹ - ReferenceRiccati.s ε τ ^ 2| ≤
      1448 * T ^ 8 * δ :=
    hmdiff.trans (by nlinarith only [mul_le_mul_of_nonneg_right hT48 hδ])
  have hderror : 2 * d ≤ 1448 * T ^ 8 * δ := by
    dsimp only [d]
    nlinarith only [mul_le_mul_of_nonneg_right hT68 hδ,
      show 0 ≤ T ^ 8 * δ by positivity]
  have hSerror : 2 * δ ≤ 1448 * T ^ 8 * δ := by
    have hpow : 1 ≤ T ^ 8 := one_le_pow₀ hT₁
    nlinarith only [mul_le_mul_of_nonneg_right hpow hδ, hδ]
  have hZinv₀ : 0 ≤ Z⁻¹ := inv_nonneg.mpr (by linarith)
  have hminv₀ : 0 ≤ (normFactor X Q Z S)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨hZ, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change |X| ≤ 4 * T ^ 2
      linarith [sq_nonneg T]
    · change |Q| ≤ 4 * T ^ 2
      linarith [sq_nonneg T]
    · change |Z| ≤ 4 * T ^ 2
      linarith
    · change |S⁻¹| ≤ 4 * T ^ 2
      rw [abs_of_nonneg (inv_nonneg.mpr hS₀.le)]
      exact ((inv_le_one₀ hS₀).mpr hS).trans (by linarith)
    · change |Z⁻¹| ≤ 4 * T ^ 2
      rw [abs_of_nonneg hZinv₀]
      linarith
    · change |(normFactor X Q Z S)⁻¹| ≤ 4 * T ^ 2
      rw [abs_of_nonneg hminv₀]
      linarith
  · intro i
    fin_cases i
    · change |ReferenceRiccati.x ε τ| ≤ 4 * T ^ 2
      linarith [sq_nonneg T]
    · change |-ε * τ| ≤ 4 * T ^ 2
      rw [neg_mul]
      nlinarith [sq_nonneg (T - 1)]
    · change |(1 : ℝ)| ≤ 4 * T ^ 2
      rw [abs_one]
      linarith
    · change |(0 : ℝ)| ≤ 4 * T ^ 2
      rw [abs_zero]
      linarith
    · change |(1 : ℝ)| ≤ 4 * T ^ 2
      rw [abs_one]
      linarith
    · change |ReferenceRiccati.s ε τ ^ 2| ≤ 4 * T ^ 2
      rw [abs_of_nonneg (sq_nonneg _)]
      linarith
  · intro i
    have hd_le : d ≤ 1448 * T ^ 8 * δ := by
      have hd₀ : 0 ≤ d := by unfold d; positivity
      linarith
    fin_cases i
    · change |X - ReferenceRiccati.x ε τ| ≤ 1448 * T ^ 8 * δ
      exact (show |X - ReferenceRiccati.x ε τ| ≤ d by
        linarith [abs_nonneg (Q + ε * τ), abs_nonneg (Z - 1)]).trans hd_le
    · change |Q - (-ε * τ)| ≤ 1448 * T ^ 8 * δ
      rw [neg_mul, sub_neg_eq_add]
      exact (show |Q + ε * τ| ≤ d by
        linarith [abs_nonneg (X - ReferenceRiccati.x ε τ), abs_nonneg (Z - 1)]).trans hd_le
    · change |Z - 1| ≤ 1448 * T ^ 8 * δ
      exact (show |Z - 1| ≤ d by
        linarith [abs_nonneg (X - ReferenceRiccati.x ε τ), abs_nonneg (Q + ε * τ)]).trans hd_le
    · change |S⁻¹ - 0| ≤ 1448 * T ^ 8 * δ
      rw [sub_zero, abs_of_nonneg (inv_nonneg.mpr hS₀.le)]
      exact hSinv.trans hSerror
    · exact hZdiff.trans hderror
    · exact hmerror

end TorusEuler.MovingAmplitude
