import TorusEuler.ReferenceLateBounds
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace TorusEuler.AmplificationCrossing

open ReferenceRiccati (x s x_bounds_of_turning_time s_le_inv_x inv_two_mul_x_le_s)

noncomputable section

/-- The right endpoint of the crossing interval in Proposition 2.6. -/
def crossingHorizon (ε next : ℝ) : ℝ := 2 / Real.sqrt (ε * next)

theorem eight_div_le_crossingHorizon {ε next : ℝ} (hε : 0 < ε) (hn : 0 < next)
    (hsmall : next ≤ ε / 32) : 8 / ε ≤ crossingHorizon ε next := by
  have hprod : 0 < ε * next := mul_pos hε hn
  have hsqrt : 0 < Real.sqrt (ε * next) := Real.sqrt_pos.2 hprod
  have hsquare : ε * next ≤ (ε / 4) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall hε.le
    nlinarith [sq_nonneg ε]
  have hroot : Real.sqrt (ε * next) ≤ ε / 4 := by
    calc
      Real.sqrt (ε * next) ≤ Real.sqrt ((ε / 4) ^ 2) := Real.sqrt_le_sqrt hsquare
      _ = ε / 4 := Real.sqrt_sq (by positivity)
  unfold crossingHorizon
  apply (div_le_div_iff₀ hε hsqrt).2
  linarith

theorem x_crossingHorizon {ε next : ℝ} (hε : 0 < ε) (hn : 0 < next) :
    x ε (crossingHorizon ε next) = 2 / next := by
  have hprod : 0 < ε * next := mul_pos hε hn
  rw [x, crossingHorizon, div_pow, Real.sq_sqrt hprod.le]
  field_simp

/-- The existence and location estimates for the crossing in Proposition 2.6.
The hypotheses supply the continuous physical coupling ratio and its two late bounds. -/
theorem exists_crossing_and_x_bounds {ε next τm T : ℝ} {ρ : ℝ → ℝ}
    (hε : 0 < ε) (hn : 0 < next) (hsmall : next ≤ ε / 32)
    (hτm : τm ∈ Icc (2 / ε) (3 / ε)) (hT : crossingHorizon ε next ≤ T)
    (hρ : ContinuousOn ρ (Icc τm T))
    (hbounds : ∀ τ ∈ Icc τm T, 1 / (4 * x ε τ) ≤ ρ τ ∧ ρ τ ≤ 3 / (2 * x ε τ)) :
    (∃ τ ∈ Ioo τm (crossingHorizon ε next), ρ τ = next) ∧
      ∀ τ ∈ Icc τm T, ρ τ = next → 1 / (4 * next) ≤ x ε τ ∧ x ε τ ≤ 3 / (2 * next) := by
  let b := crossingHorizon ε next
  have hmb : τm < b := hτm.2.trans_lt <|
    (div_lt_div_of_pos_right (by norm_num : (3 : ℝ) < 8) hε).trans_le
      (eight_div_le_crossingHorizon hε hn hsmall)
  have hx (τ : ℝ) (hτ : τm ≤ τ) : 0 < x ε τ := by
    have hτ₀ : 0 < τ := (div_pos (by norm_num : (0 : ℝ) < 2) hε).trans_le (hτm.1.trans hτ)
    unfold x
    positivity
  have hm : next < ρ τm := by
    have hm_bound := (hbounds τm ⟨le_rfl, hmb.le.trans hT⟩).1
    apply lt_of_lt_of_le _ hm_bound
    have hxm := (x_bounds_of_turning_time hε hτm).2
    have hmul : next * (4 * x ε τm) ≤ (ε / 32) * (4 * (9 / (2 * ε))) :=
      mul_le_mul hsmall (mul_le_mul_of_nonneg_left hxm (by norm_num))
        (mul_nonneg (by norm_num) (hx τm le_rfl).le)
        (div_nonneg hε.le (by norm_num))
    have hcancel : (ε / 32) * (4 * (9 / (2 * ε))) = 9 / 16 := by field_simp; norm_num
    rw [lt_div_iff₀ (mul_pos (by norm_num) (hx τm le_rfl))]
    rw [hcancel] at hmul
    linarith
  have hb : ρ b < next := by
    apply lt_of_le_of_lt (hbounds b ⟨hmb.le, hT⟩).2
    change 3 / (2 * x ε (crossingHorizon ε next)) < next
    rw [x_crossingHorizon hε hn, div_lt_iff₀ (by positivity)]
    have hcancel : next * (2 * (2 / next)) = 4 := by field_simp; norm_num
    rw [hcancel]
    norm_num
  constructor
  · obtain ⟨τ, hτ, hroot⟩ := intermediate_value_Icc' hmb.le
      (hρ.mono (Icc_subset_Icc_right hT)) (show next ∈ Icc (ρ b) (ρ τm) from ⟨hb.le, hm.le⟩)
    exact ⟨τ, ⟨hτ.1.lt_of_ne (by intro heq; subst τ; exact hm.ne hroot.symm),
      hτ.2.lt_of_ne (by intro heq; subst τ; exact hb.ne hroot)⟩, hroot⟩
  · intro τ hτ hcross
    obtain ⟨hl, hu⟩ := hbounds τ hτ
    rw [hcross, div_le_iff₀ (mul_pos (by norm_num) (hx τ hτ.1))] at hl
    rw [hcross, le_div_iff₀ (mul_pos (by norm_num) (hx τ hτ.1))] at hu
    constructor
    · rw [div_le_iff₀ (by positivity)]
      convert hl using 1; ring
    · rw [le_div_iff₀ (by positivity)]
      convert hu using 1; ring

/-- The late bounds of Lemma 2.5 imply the crossing in Proposition 2.6. -/
theorem exists_crossing_of_couplingRatio {ε next τm T : ℝ} {ρ : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hn : 0 < next) (hsmall : next ≤ ε / 32)
    (hτm : τm ∈ Icc (2 / ε) (3 / ε)) (hT : crossingHorizon ε next ≤ T)
    (hρ : ContinuousOn ρ (Icc τm T))
    (hcomp : ∀ τ ∈ Icc (Real.sqrt 2 / ε) T, s ε τ / 2 ≤ ρ τ ∧ ρ τ ≤ 3 / 2 * s ε τ) :
    (∃ τ ∈ Ioo τm (crossingHorizon ε next), ρ τ = next) ∧
      ∀ τ ∈ Icc τm T, ρ τ = next → 1 / (4 * next) ≤ x ε τ ∧ x ε τ ≤ 3 / (2 * next) := by
  apply exists_crossing_and_x_bounds hε hn hsmall hτm hT hρ
  intro τ hτ
  have hstart : 0 ≤ τm := (by positivity : 0 ≤ 2 / ε).trans hτm.1
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hτ' : τ ∈ Icc (Real.sqrt 2 / ε) T :=
    ⟨(div_le_div_of_nonneg_right hsqrt hε.le).trans (hτm.1.trans hτ.1), hτ.2⟩
  have h1m : 1 ≤ x ε τm := by
    apply le_trans _ (x_bounds_of_turning_time hε hτm).1
    rw [le_div_iff₀ hε]
    linarith
  have h1 : 1 ≤ x ε τ := h1m.trans (by
    unfold x
    gcongr
    exact hτ.1)
  have hx : 0 < x ε τ := zero_lt_one.trans_le h1
  obtain ⟨hl, hu⟩ := hcomp τ hτ'
  constructor
  · apply le_trans _ hl
    have h := div_le_div_of_nonneg_right (inv_two_mul_x_le_s h1) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1
    field_simp
    norm_num
  · apply hu.trans
    have h := mul_le_mul_of_nonneg_left (s_le_inv_x hx) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    convert h using 1
    field_simp

end
end TorusEuler.AmplificationCrossing
