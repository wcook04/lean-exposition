import Mathlib

open Real

noncomputable section

namespace Breakdown

theorem le_half_weighted {y w t : ℝ} (_hy : 0 ≤ y) (hw : 0 < w) (ht : 0 < t) :
    y ≤ (t * (w * y ^ 2) + (t * w)⁻¹) / 2 := by
  have ha : 0 < t * w := mul_pos ht hw
  have e : t * (w * y ^ 2) + (t * w)⁻¹ - 2 * y = ((t * w) * y - 1) ^ 2 / (t * w) := by
    field_simp
    ring
  have h0 : 0 ≤ ((t * w) * y - 1) ^ 2 / (t * w) := div_nonneg (sq_nonneg _) ha.le
  linarith

private theorem sq_le_of_forall_t {X P Q : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 < Q)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * P + t⁻¹ * Q) / 2) : X ^ 2 ≤ P * Q := by
  refine le_of_not_gt fun hc => ?_
  have hXp : 0 < X := by
    rcases hX.lt_or_eq with h1 | h1
    · exact h1
    · subst h1
      nlinarith [mul_nonneg hP hQ.le]
  rcases hP.lt_or_eq with hP1 | hP1
  · have ht : 0 < X / P := div_pos hXp hP1
    have h2 := h (X / P) ht
    have e1 : X / P * P = X := by field_simp
    have e2 : (X / P)⁻¹ * Q = P * Q / X := by
      rw [inv_div]
      field_simp
    rw [e1, e2] at h2
    have h3 : P * Q / X < X := by
      rw [div_lt_iff₀ hXp]
      nlinarith
    linarith
  · subst hP1
    have ht : 0 < Q / X := div_pos hQ hXp
    have h2 := h (Q / X) ht
    have e2 : (Q / X)⁻¹ * Q = X := by
      rw [inv_div]
      field_simp
    rw [e2] at h2
    linarith

private theorem key_bound {X I J : ℝ} (hX : 0 ≤ X) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : ∀ l : ℝ, 0 < l → ∀ t : ℝ, 0 < t → X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2)
    (l : ℝ) (hl : 0 < l) : X ^ 2 ≤ (l * I + J / l) * (1 / (4 * π)) :=
  sq_le_of_forall_t hX (add_nonneg (mul_nonneg hl.le hI) (div_nonneg hJ hl.le))
    (by positivity) (h l hl)

theorem sq_le_of_forall_scale {X I J : ℝ} (hX : 0 ≤ X) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : ∀ l : ℝ, 0 < l → ∀ t : ℝ, 0 < t → X ≤ (t * (l * I + J / l) + t⁻¹ * (1 / (4 * π))) / 2) :
    X ^ 2 ≤ (1 / (2 * π)) * Real.sqrt I * Real.sqrt J := by
  have hk := key_bound hX hI hJ h
  have hpi : 0 < π := Real.pi_pos
  rcases hI.lt_or_eq with hI1 | hI1
  · rcases hJ.lt_or_eq with hJ1 | hJ1
    · have sI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hI1
      have sJ : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJ1
      have h2 := hk (Real.sqrt J / Real.sqrt I) (div_pos sJ sI)
      have eI : Real.sqrt I ^ 2 = I := Real.sq_sqrt hI
      have eJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ
      have e : ∀ a b : ℝ, 0 < a → 0 < b →
          (b / a * a ^ 2 + b ^ 2 / (b / a)) * (1 / (4 * π)) = (1 / (2 * π)) * a * b := by
        intro a b ha hb
        field_simp
        ring
      have e2 := e _ _ sI sJ
      rw [eI, eJ] at e2
      rw [e2] at h2
      exact h2
    · subst hJ1
      refine le_of_not_gt fun hc => ?_
      have hX2 : 0 < X ^ 2 := lt_of_le_of_lt (by positivity) hc
      have hX0 : X ≠ 0 := fun h0 => by simp [h0] at hX2
      have hl : 0 < 2 * π * X ^ 2 / (I + 1) := by positivity
      have h2 := hk _ hl
      have e : (2 * π * X ^ 2 / (I + 1) * I + 0 / (2 * π * X ^ 2 / (I + 1))) * (1 / (4 * π)) =
          X ^ 2 * (I / (2 * (I + 1))) := by
        field_simp
        ring
      rw [e] at h2
      have h3 : I / (2 * (I + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      nlinarith
  · subst hI1
    refine le_of_not_gt fun hc => ?_
    have hX2 : 0 < X ^ 2 := lt_of_le_of_lt (by positivity) hc
    have hX0 : X ≠ 0 := fun h0 => by simp [h0] at hX2
    have hl : 0 < (J + 1) / (4 * π * X ^ 2) := by positivity
    have h2 := hk _ hl
    have e : ((J + 1) / (4 * π * X ^ 2) * 0 + J / ((J + 1) / (4 * π * X ^ 2))) * (1 / (4 * π)) =
        X ^ 2 * (J / (J + 1)) := by
      field_simp
      ring
    rw [e] at h2
    have h3 : J / (J + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith

theorem sqrt_radial_weight (l : ℝ) (hl : 0 < l) :
    2 * π ^ 2 / Real.sqrt ((l * (4 * π ^ 2)) * (l⁻¹ * (16 * π ^ 4))) = 1 / (4 * π) := by
  have hpi : 0 < π := Real.pi_pos
  have e : (l * (4 * π ^ 2)) * (l⁻¹ * (16 * π ^ 4)) = (8 * π ^ 3) ^ 2 := by
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp
  ring

end Breakdown
