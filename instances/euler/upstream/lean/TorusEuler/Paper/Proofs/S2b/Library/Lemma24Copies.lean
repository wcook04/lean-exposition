import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Copies of the library carriers of Lemma 2.4, with the frame equations as hypotheses

The library proof of the wave-vector comparison of Lemma 2.4,
`MovingWaveVector.moving_waveVector_polynomial_error` (ledger content of row 2.4), and the
strength estimate `MovingWaveVector.strengthRatio_bound` call
`hasDerivWithinAt_movingFrame` (ledger content of row 2.2, the frame equations (2.2)) and
`orthonormal_movingFrame` (in its dependency closure). The copies below take the
orthonormality of the frame, the frame equations `E₁', E₂', E₃'` and `(log σ_p)' = B₃₃` as
hypotheses, which the proof of Lemma 2.4 supplies from `Statement.lemma_2_2`. Everything
else is unchanged; the private helpers of `MovingCoordinateWaveVector.lean` they need
(`abs_le_of_deriv_abs_le`, the residuals `residualX/Q/Z`, `abs_threeProducts_bound`,
`abs_div_le_self_of_one_le`, `residual_bounds`) are copied verbatim.
Namespace `TorusEuler.Paper.Lib.S2b`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open MovingWaveVector

noncomputable section

/-- Copy of the private `MovingWaveVector.abs_le_of_deriv_abs_le`: a function vanishing at
`0` with derivative bounded by `M` on `[0, T]` is bounded by `MT`. -/
theorem abs_le_of_deriv_abs_le {f f' : ℝ → ℝ} {T M τ : ℝ}
    (ht : τ ∈ Icc 0 T) (h₀ : f 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, |f' t| ≤ M) : |f τ| ≤ M * T := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 h0T)
  have h := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ht) h0T ht
  rw [h₀, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hM)

/-- Copy of `MovingWaveVector.strengthRatio_bound` with the equation `(log σ_p)' = B₃₃`
of (2.2) and the orthonormality of the frame as hypotheses `hlog`, `he` (in the library
they come from `hasDerivWithinAt_movingFrame` and `orthonormal_movingFrame`):
`|σ_p/σ - 1| ≤ 2Tδ` (`sections/03_amplification.tex:302-309`). -/
theorem strengthRatio_bound_of_log {kp ap : ℝ → Space} {B : ℝ → Space →L[ℝ] Space}
    {T δ : ℝ} (hsmall : T * δ ≤ 1)
    (hp : ∀ t ∈ Icc 0 T, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0)
    (he : ∀ t ∈ Icc 0 T, Orthonormal ℝ (frame kp ap t))
    (hlog : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => Real.log (‖kp u‖ * ‖ap u‖))
      (entry (frame kp ap t) (B t) 2 2) (Icc 0 T) t)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, |strengthRatio kp ap t - 1| ≤ 2 * T * δ := by
  let F (t : ℝ) := Real.log (‖kp t‖ * ‖ap t‖) - Real.log (‖kp 0‖ * ‖ap 0‖)
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt F (entry (frame kp ap t) (B t) 2 2) (Icc 0 T) t :=
    (hlog t ht).sub_const _
  intro t ht
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hF₀ : F 0 = 0 := sub_self _
  have hbound := abs_le_of_deriv_abs_le ht hF₀ hF (fun u hu =>
    (coefficient_abs_le_norm (he u hu) (B u) 2 2).trans (hB u hu))
  have hId : Real.exp (F t) = strengthRatio kp ap t := by
    dsimp [F, strengthRatio]
    rw [Real.exp_sub, Real.exp_log (mul_pos (norm_pos_iff.mpr (hp t ht).1)
      (norm_pos_iff.mpr (hp t ht).2.1)), Real.exp_log (mul_pos
      (norm_pos_iff.mpr (hp 0 h0T).1) (norm_pos_iff.mpr (hp 0 h0T).2.1))]
  rw [← hId]
  exact (Real.abs_exp_sub_one_le (hbound.trans (by linarith))).trans (by linarith)

/-- Copy of the private `MovingWaveVector.residualX`. -/
def residualX (b d : Fin 3 → Fin 3 → ℝ) (S σratio x q z : ℝ) : ℝ :=
  (-b 0 0 - d 0 0) * x + (1 - σratio - (b 1 0 + b 0 1 + d 1 0) / S) * q +
    (-(b 2 0 + b 0 2 + d 2 0)) * z

/-- Copy of the private `MovingWaveVector.residualQ`. -/
def residualQ (b d : Fin 3 → Fin 3 → ℝ) (ε S x q z : ℝ) : ℝ :=
  (-(S * d 0 1)) * x + (-b 1 1 - d 1 1) * q + (ε - 2 * S * b 2 1 - S * d 2 1) * z

/-- Copy of the private `MovingWaveVector.residualZ`. -/
def residualZ (b d : Fin 3 → Fin 3 → ℝ) (S x q z : ℝ) : ℝ :=
  (-d 0 2) * x + (-(b 1 2 - b 2 1 + d 1 2) / S) * q + (-b 2 2 - d 2 2) * z

/-- Copy of the private `MovingWaveVector.abs_threeProducts_bound`. -/
theorem abs_threeProducts_bound {a b c x q z M : ℝ}
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) :
    |a * x + b * q + c * z| ≤ M * (|x| + |q| + |z|) := by
  calc
    _ ≤ |a * x + b * q| + |c * z| := abs_add_le _ _
    _ ≤ |a * x| + |b * q| + |c * z| := add_le_add (abs_add_le _ _) le_rfl
    _ = |a| * |x| + |b| * |q| + |c| * |z| := by simp only [abs_mul]
    _ ≤ M * |x| + M * |q| + M * |z| := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
      (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

/-- Copy of the private `MovingWaveVector.abs_div_le_self_of_one_le`. -/
theorem abs_div_le_self_of_one_le {a S : ℝ} (hS : 1 ≤ S) : |a / S| ≤ |a| := by
  rw [abs_div, abs_of_nonneg (zero_le_one.trans hS)]
  exact div_le_self (abs_nonneg _) hS

/-- Copy of the private `MovingWaveVector.residual_bounds`. -/
theorem residual_bounds {b d : Fin 3 → Fin 3 → ℝ}
    {ε T δ S σratio x q z : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hS : 1 ≤ S)
    (hb : ∀ i j, |b i j| ≤ δ) (hd : ∀ i j, |d i j| ≤ δ)
    (hdS : ∀ i j, |S * d i j| ≤ δ) (hσ : |σratio - 1| ≤ 2 * T * δ)
    (hε : |2 * S * b 2 1 - ε| ≤ δ) :
    let L := (5 * T * δ) * (|x| + |q| + |z|)
    |residualX b d S σratio x q z| ≤ L ∧
    |residualQ b d ε S x q z| ≤ L ∧
    |residualZ b d S x q z| ≤ L := by
  dsimp only
  have hTδ : δ ≤ T * δ := by simpa using mul_le_mul_of_nonneg_right hT hδ
  have hbbd (i j i' j' m n : Fin 3) : |b i j + b i' j' + d m n| ≤ 3 * δ := by
    have h := (abs_add_le (b i j + b i' j') (d m n)).trans
      (add_le_add ((abs_add_le (b i j) (b i' j')).trans (add_le_add (hb i j) (hb i' j'))) (hd m n))
    linarith
  have hbndNeg (i j : Fin 3) : |-b i j - d i j| ≤ 5 * T * δ := by
    have h := (abs_sub (-b i j) (d i j)).trans (add_le_add (by simpa using hb i j) (hd i j))
    linarith
  constructor
  · apply abs_threeProducts_bound (hbndNeg 0 0)
    · have hdiff : |1 - σratio| ≤ 2 * T * δ := by simpa only [abs_sub_comm] using hσ
      have hdiv := (abs_div_le_self_of_one_le (a := b 1 0 + b 0 1 + d 1 0) hS).trans
        (hbbd 1 0 0 1 1 0)
      have hc := (abs_sub (1 - σratio) ((b 1 0 + b 0 1 + d 1 0) / S)).trans
        (add_le_add hdiff hdiv)
      linarith
    · rw [abs_neg]
      linarith [hbbd 2 0 0 2 2 0]
  constructor
  · refine abs_threeProducts_bound ?_ (hbndNeg 1 1) ?_
    · rw [abs_neg]
      linarith [hdS 0 1]
    · have heps : |ε - 2 * S * b 2 1| ≤ δ := by simpa only [abs_sub_comm] using hε
      have hc := (abs_sub (ε - 2 * S * b 2 1) (S * d 2 1)).trans
        (add_le_add heps (hdS 2 1))
      linarith
  · refine abs_threeProducts_bound ?_ ?_ (hbndNeg 2 2)
    · rw [abs_neg]
      linarith [hd 0 2]
    · have h₀ := (abs_add_le (b 1 2 - b 2 1) (d 1 2)).trans
        (add_le_add ((abs_sub (b 1 2) (b 2 1)).trans (add_le_add (hb 1 2) (hb 2 1))) (hd 1 2))
      have h := (abs_div_le_self_of_one_le (a := -(b 1 2 - b 2 1 + d 1 2)) hS).trans
        (by simpa only [abs_neg] using h₀)
      linarith

/-- Copy of `MovingWaveVector.moving_waveVector_polynomial_error` (content of Lemma 2.4)
with the orthonormality of the frame and the frame equations (2.2) of the preceding wave
as hypotheses `he, hE₁, hE₂, hE₃, hlog` (in the library they come from
`orthonormal_movingFrame` and from `hasDerivWithinAt_movingFrame` through
`moving_waveVector_derivatives` and `strengthRatio_bound`): the scaled components of the
wave vector satisfy `|X - x| + |Q + ετ| + |Z - 1| ≤ 120δT⁶ ≤ 1/2` on `[0, T]`
(`sections/03_amplification.tex:311-357`). -/
theorem waveVector_polynomial_error_of_frame {kp ap k : ℝ → Space}
    {B E : ℝ → Space →L[ℝ] Space} {ε T δ scale S : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hscale : scale ≠ 0) (hS : 1 ≤ S) (hsmall : 240 * δ * T ^ 6 ≤ 1)
    (hp : ∀ t ∈ Icc 0 T, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0)
    (he : ∀ t ∈ Icc 0 T, Orthonormal ℝ (frame kp ap t))
    (hE₁ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => frame kp ap u 0)
      ((-entry (frame kp ap t) (B t) 0 1) • frame kp ap t 1 -
        entry (frame kp ap t) (B t) 0 2 • frame kp ap t 2) (Icc 0 T) t)
    (hE₂ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => frame kp ap u 1)
      (entry (frame kp ap t) (B t) 0 1 • frame kp ap t 0 -
        entry (frame kp ap t) (B t) 2 1 • frame kp ap t 2) (Icc 0 T) t)
    (hE₃ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => frame kp ap u 2)
      (entry (frame kp ap t) (B t) 0 2 • frame kp ap t 0 +
        entry (frame kp ap t) (B t) 2 1 • frame kp ap t 1) (Icc 0 T) t)
    (hlog : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => Real.log (‖kp u‖ * ‖ap u‖))
      (entry (frame kp ap t) (B t) 2 2) (Icc 0 T) t)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k
      (-((strain (frame kp ap t) (B t) (E t) S (strengthRatio kp ap t)).adjoint (k t))) (Icc 0 T) t)
    (hk₀ : k 0 = scale • frame kp ap 0 2)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ δ)
    (hE : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ δ / S)
    (hCoupling : ∀ t ∈ Icc 0 T,
      |2 * S * entry (frame kp ap t) (B t) 2 1 - ε| ≤ δ) :
    ∀ t ∈ Icc 0 T,
      let e := frame kp ap
      |X e k scale t - ReferenceRiccati.x ε t| + |Q e k scale S t + ε * t| +
        |Z e k scale t - 1| ≤ 120 * δ * T ^ 6 ∧ 120 * δ * T ^ 6 ≤ 1 / 2 := by
  let e := frame kp ap
  let x := X e k scale
  let q := Q e k scale S
  let z := Z e k scale
  let b (t : ℝ) := entry (e t) (B t)
  let d (t : ℝ) := entry (e t) (E t)
  let rX (t : ℝ) := residualX (b t) (d t) S (strengthRatio kp ap t) (x t) (q t) (z t)
  let rQ (t : ℝ) := residualQ (b t) (d t) ε S (x t) (q t) (z t)
  let rZ (t : ℝ) := residualZ (b t) (d t) S (x t) (q t) (z t)
  have hT₀ : 0 ≤ T := by linarith
  have hT₁ : 1 ≤ T := by linarith
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have hTδ : T * δ ≤ 1 := by
    have hp : T ^ 1 ≤ T ^ 6 := pow_le_pow_right₀ hT₁ (by decide)
    rw [pow_one] at hp
    nlinarith [mul_le_mul_of_nonneg_right hp hδ]
  have hσ := strengthRatio_bound_of_log hTδ hp he hlog hB
  obtain ⟨hx₀, hq₀, hz₀⟩ := coordinate_initial_values (he 0 ⟨le_rfl, hT₀⟩) hscale hk₀
  have hDerivative (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt x (-q t + rX t) (Icc 0 T) t ∧
      HasDerivWithinAt q (-ε * z t + rQ t) (Icc 0 T) t ∧
      HasDerivWithinAt z (rZ t) (Icc 0 T) t := by
    obtain ⟨h₁, h₂, h₃⟩ := normalized_waveVector_derivatives (he t ht) hscale hS₀.ne'
      (hE₁ t ht) (hE₂ t ht) (hE₃ t ht) (hk t ht)
    refine ⟨h₁.congr_deriv ?_, h₂.congr_deriv ?_, h₃.congr_deriv ?_⟩ <;>
      dsimp [rX, rQ, rZ, residualX, residualQ, residualZ, b, d, x, q, z, e] <;> ring
  have hResidual (t : ℝ) (ht : t ∈ Icc 0 T) :
      let L := (5 * T * δ) * (|x t| + |q t| + |z t|)
      |rX t| ≤ L ∧ |rQ t| ≤ L ∧ |rZ t| ≤ L := by
    have hb₀ (i j : Fin 3) : |b t i j| ≤ δ :=
      (coefficient_abs_le_norm (he t ht) (B t) i j).trans (hB t ht)
    have hd₀ (i j : Fin 3) : |d t i j| ≤ δ / S :=
      (coefficient_abs_le_norm (he t ht) (E t) i j).trans (hE t ht)
    have hdS (i j : Fin 3) : |S * d t i j| ≤ δ := by
      rw [abs_mul, abs_of_nonneg hS₀.le]
      calc
        _ ≤ S * (δ / S) := mul_le_mul_of_nonneg_left (hd₀ i j) hS₀.le
        _ = δ := by field_simp
    exact residual_bounds hδ hT₁ hS hb₀
      (fun i j => (hd₀ i j).trans (div_le_self hδ hS)) hdS (hσ t ht) (hCoupling t ht)
  have hDsmall : 12 * (5 * T * δ) * T ^ 3 ≤ 1 := by
    have hp : T ^ 4 ≤ T ^ 6 := pow_le_pow_right₀ hT₁ (by decide)
    nlinarith [mul_le_mul_of_nonneg_left hp hδ]
  have hpoly := polynomial_waveVector_error hε₀ hε₁ hT (by positivity) hDsmall hx₀ hq₀ hz₀
    (fun t ht => (hDerivative t ht).1) (fun t ht => (hDerivative t ht).2.1)
    (fun t ht => (hDerivative t ht).2.2) hResidual
  intro t ht
  exact ⟨(hpoly t ht).trans_eq (by ring), by linarith⟩

end

end TorusEuler.Paper.Lib.S2b
