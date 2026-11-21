import Breakdown.FracCell.StSpectral

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

private lemma rpow_neg_half_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

private lemma rpow_scaled (lam h : ℝ) (hl : 0 < lam) (hh : 0 < h) :
    (lam * h ^ 2) ^ (-(1 / 2 : ℝ)) = h⁻¹ * lam ^ (-(1 / 2 : ℝ)) := by
  rw [rpow_neg_half_eq _ (by positivity), rpow_neg_half_eq _ hl.le, Real.sqrt_mul hl.le,
    Real.sqrt_sq hh.le, mul_inv, mul_comm]

private lemma rpow_quarter (lam h : ℝ) (hl : 0 < lam) (hh : 0 < h) :
    (lam * h ^ 2 / 4) ^ (-(1 / 2 : ℝ)) = 2 / h * lam ^ (-(1 / 2 : ℝ)) := by
  have e : lam * h ^ 2 / 4 = lam * (h / 2) ^ 2 := by ring
  rw [e, rpow_scaled lam (h / 2) hl (by positivity)]
  congr 1
  field_simp

private lemma inv_le_cross (Λ lam : ℝ) (hΛ : 0 < Λ) (hl : Λ ≤ lam) :
    lam⁻¹ ≤ Λ ^ (-(1 / 2 : ℝ)) * lam ^ (-(1 / 2 : ℝ)) := by
  have hl0 : 0 < lam := lt_of_lt_of_le hΛ hl
  rw [rpow_neg_half_eq _ hΛ.le, rpow_neg_half_eq _ hl0.le]
  have ht : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hl0
  have hw : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hΛ
  have hwt : Real.sqrt Λ ≤ Real.sqrt lam := Real.sqrt_le_sqrt hl
  have e : lam⁻¹ = (Real.sqrt lam)⁻¹ * (Real.sqrt lam)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hl0.le]
  rw [e]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hw hwt) (inv_nonneg.mpr ht.le)

private lemma intervalClosed_quarter (q : ℕ) (lam h : ℝ) (hl : 0 < lam) (hh : 0 < h) :
    intervalClosed q (lam * h ^ 2 / 4)
      = 8 / Real.sqrt 3 * ((q : ℝ) + 1) ^ 2 / h * lam ^ (-(1 / 2 : ℝ))
        + 2 * ((q : ℝ) + 1) ^ 4 / h ^ 2 * lam⁻¹ := by
  unfold intervalClosed
  rw [rpow_quarter lam h hl hh]
  ring

private lemma axisClosed_scaled (q : ℕ) (M lam h : ℝ) (hl : 0 < lam) (hh : 0 < h) :
    axisClosed q M (lam * h ^ 2)
      = 8 * Real.sqrt 6 / 3 * ((q : ℝ) + 1) ^ 2 / h * lam ^ (-(1 / 2 : ℝ))
        + 2 * M / h ^ 2 * lam⁻¹ := by
  unfold axisClosed
  rw [rpow_scaled lam h hl hh]
  ring

private lemma gradient_nonneg (q : ℕ) (M : ℝ) (hM : AxisGradientBound q M) : 0 ≤ M := by
  have h := hM 0 (by norm_num) 1 (by simp) (by intro h; simp at h)
  have e : (∫ r in (0 : ℝ)..1, (1 : ℝ[X]).eval r ^ 2 * r) = 1 / 2 := by
    simp [integral_id]
  have e0 : (∫ r in (0 : ℝ)..1, ((derivative (1 : ℝ[X])).eval r ^ 2
      + ((0 : ℕ) : ℝ) ^ 2 * (1 : ℝ[X]).eval r ^ 2 / r ^ 2) * r) = 0 := by
    simp
  rw [e, e0] at h
  linarith

private lemma ratio_le (lam x : ℝ) (hl : 0 < lam) (hx : 0 ≤ x) : ratioFn lam x ≤ x * lam⁻¹ := by
  unfold ratioFn
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hx hl (le_add_of_nonneg_right hx)

private lemma off_axis_bound (sd : SpectralData) (g : CellBlock) (Λ lam : ℝ) (hΛ : 0 < Λ)
    (hl : Λ ≤ lam) (hr : g.innerRadius < g.outerRadius) (hz : g.lowerHeight < g.upperHeight)
    (h1 : 0 < g.innerRadius) :
    min 1 (g.outerRadius / g.innerRadius
      * (sd.intervalUpper g.degree (lam * (g.outerRadius - g.innerRadius) ^ 2 / 4)
        + sd.intervalUpper g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4)
        + ratioFn lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2)))
    ≤ g.outerRadius / g.innerRadius
      * (8 / Real.sqrt 3 * (g.degree + 1 : ℝ) ^ 2
          * (1 / (g.outerRadius - g.innerRadius) + 1 / (g.upperHeight - g.lowerHeight))
        + Λ ^ (-(1 / 2 : ℝ)) * (2 * (g.degree + 1 : ℝ) ^ 4
            * (1 / (g.outerRadius - g.innerRadius) ^ 2 + 1 / (g.upperHeight - g.lowerHeight) ^ 2)
          + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2)) * lam ^ (-(1 / 2 : ℝ)) := by
  have hl0 : 0 < lam := lt_of_lt_of_le hΛ hl
  have hR : 0 < g.outerRadius / g.innerRadius := div_pos (by linarith) h1
  have hrp : 0 < g.outerRadius - g.innerRadius := sub_pos.mpr hr
  have hzp : 0 < g.upperHeight - g.lowerHeight := sub_pos.mpr hz
  have iu : ∀ μ, sd.intervalUpper g.degree μ ≤ intervalClosed g.degree μ := fun μ => min_le_right _ _
  have a1 := iu (lam * (g.outerRadius - g.innerRadius) ^ 2 / 4)
  rw [intervalClosed_quarter _ _ _ hl0 hrp] at a1
  have a2 := iu (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4)
  rw [intervalClosed_quarter _ _ _ hl0 hzp] at a2
  have a3 := ratio_le lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2) hl0 (by positivity)
  have hc := inv_le_cross Λ lam hΛ hl
  have hB : 0 ≤ 2 * (g.degree + 1 : ℝ) ^ 4
      * (1 / (g.outerRadius - g.innerRadius) ^ 2 + 1 / (g.upperHeight - g.lowerHeight) ^ 2)
      + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hc hB
  have key : sd.intervalUpper g.degree (lam * (g.outerRadius - g.innerRadius) ^ 2 / 4)
        + sd.intervalUpper g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4)
        + ratioFn lam ((g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2)
      ≤ (8 / Real.sqrt 3 * (g.degree + 1 : ℝ) ^ 2
          * (1 / (g.outerRadius - g.innerRadius) + 1 / (g.upperHeight - g.lowerHeight))
        + Λ ^ (-(1 / 2 : ℝ)) * (2 * (g.degree + 1 : ℝ) ^ 4
            * (1 / (g.outerRadius - g.innerRadius) ^ 2 + 1 / (g.upperHeight - g.lowerHeight) ^ 2)
          + (g.mode + 1 : ℝ) ^ 2 / g.innerRadius ^ 2)) * lam ^ (-(1 / 2 : ℝ)) := by
    linear_combination a1 + a2 + a3 + hm
  calc _ ≤ _ := min_le_right _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left key hR.le
    _ = _ := by ring

private lemma on_axis_bound (sd : SpectralData) (g : CellBlock) (Λ lam : ℝ) (hΛ : 0 < Λ)
    (hl : Λ ≤ lam) (hr : g.innerRadius < g.outerRadius) (hz : g.lowerHeight < g.upperHeight)
    (h24 : 24 ≤ Λ * (g.outerRadius - g.innerRadius) ^ 2) (hM : 0 ≤ sd.axisGradient g.degree) :
    min 1 (sd.axisUpper g.degree (lam * (g.outerRadius - g.innerRadius) ^ 2)
      + sd.intervalUpper g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4))
    ≤ ((g.degree + 1 : ℝ) ^ 2 * (8 * Real.sqrt 6 / 3 / (g.outerRadius - g.innerRadius)
        + 8 / Real.sqrt 3 / (g.upperHeight - g.lowerHeight))
      + Λ ^ (-(1 / 2 : ℝ)) * (2 * sd.axisGradient g.degree / (g.outerRadius - g.innerRadius) ^ 2
        + 2 * (g.degree + 1 : ℝ) ^ 4 / (g.upperHeight - g.lowerHeight) ^ 2)) * lam ^ (-(1 / 2 : ℝ)) := by
  have hl0 : 0 < lam := lt_of_lt_of_le hΛ hl
  have hrp : 0 < g.outerRadius - g.innerRadius := sub_pos.mpr hr
  have hzp : 0 < g.upperHeight - g.lowerHeight := sub_pos.mpr hz
  have hμ : 24 ≤ lam * (g.outerRadius - g.innerRadius) ^ 2 :=
    h24.trans (mul_le_mul_of_nonneg_right hl (sq_nonneg _))
  have a1 : sd.axisUpper g.degree (lam * (g.outerRadius - g.innerRadius) ^ 2)
      ≤ axisClosed g.degree (sd.axisGradient g.degree) (lam * (g.outerRadius - g.innerRadius) ^ 2) := by
    unfold SpectralData.axisUpper
    rw [if_pos hμ]
    exact min_le_right _ _
  rw [axisClosed_scaled _ _ _ _ hl0 hrp] at a1
  have a2 : sd.intervalUpper g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4)
      ≤ intervalClosed g.degree (lam * (g.upperHeight - g.lowerHeight) ^ 2 / 4) := min_le_right _ _
  rw [intervalClosed_quarter _ _ _ hl0 hzp] at a2
  have hc := inv_le_cross Λ lam hΛ hl
  have hB : 0 ≤ 2 * sd.axisGradient g.degree / (g.outerRadius - g.innerRadius) ^ 2
        + 2 * (g.degree + 1 : ℝ) ^ 4 / (g.upperHeight - g.lowerHeight) ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hc hB
  refine (min_le_right _ _).trans ?_
  linear_combination a1 + a2 + hm

theorem tail_holds : TailStatement := by
  intro k N c sd hsd a lam hlam
  have hΛ := hsd.cutoff_pos
  obtain ⟨hr, hz, -, -⟩ := hsd.block_geometry a
  cases hb : (sd.block (c.blockIndex a)).onAxis with
  | false =>
    have h1 := hsd.off_axis a hb
    simp only [SpectralData.blockSpectral, SpectralData.tailFormula, hb, Bool.false_eq_true,
      if_false]
    exact off_axis_bound sd _ _ _ hΛ hlam hr hz h1
  | true =>
    obtain ⟨-, -, h24⟩ := hsd.on_axis a hb
    simp only [SpectralData.blockSpectral, SpectralData.tailFormula, hb, if_true]
    exact on_axis_bound sd _ _ _ hΛ hlam hr hz h24 (gradient_nonneg _ _ (hsd.axis_gradient a hb))

end Spectral

end CellCert

end Breakdown
