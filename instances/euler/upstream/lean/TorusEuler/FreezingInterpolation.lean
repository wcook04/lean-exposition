import TorusEuler.TorusFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory Set
open scoped ENNReal

namespace TorusEuler

local notation "Labels" => UnitAddTorus (Fin 3)

/-- Exact ball mass for the product metric and normalized Haar measure on the unit torus. -/
theorem unitTorusMeasure_closedBall (a : Labels) {r : ℝ} (hr : 0 ≤ r) :
    unitTorusMeasure (Metric.closedBall a r) = ENNReal.ofReal ((min 1 (2 * r)) ^ 3) := by
  have hc (x : UnitAddCircle) :
      AddCircle.haarAddCircle (Metric.closedBall x r) = ENNReal.ofReal (min 1 (2 * r)) := by
    have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
    rw [← hvol]
    exact AddCircle.volume_closedBall 1 r
  rw [unitTorusMeasure, Measure.pi_closedBall _ _ hr]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (le_min (by norm_num) (by positivity))]

/-- The interpolation step in Appendix A, with the product metric on the unit torus.
The real square root of the squared norm integral is the spatial `L²` norm. -/
theorem unitTorus_sup_le_holderHalf_add_l2 {E : Type*} [NormedAddCommGroup E]
    (v : C(Labels, E)) {ε H : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hH : 0 ≤ H)
    (hholder : ∀ a b, ‖v a - v b‖ ≤ H * Real.sqrt (dist a b)) :
    ‖v‖ ≤ ε * H + ε⁻¹ ^ 3 * Real.sqrt (∫ b, ‖v b‖ ^ 2 ∂unitTorusMeasure) := by
  rw [ContinuousMap.norm_le_of_nonempty]
  intro a
  let S := Metric.closedBall a (ε ^ 2)
  let m := max 0 (‖v a‖ - ε * H)
  have hm : 0 ≤ m := le_max_left _ _
  have hSmeas : MeasurableSet S := measurableSet_closedBall
  have hball : ε ^ 6 ≤ unitTorusMeasure.real S := by
    have hmin : ε ^ 2 ≤ min 1 (2 * ε ^ 2) :=
      le_min (by simpa only [one_pow] using pow_le_pow_left₀ hε.le hε1 2)
        (by linarith only [sq_nonneg ε])
    have hpow := pow_le_pow_left₀ (sq_nonneg ε) hmin 3
    rw [measureReal_def, unitTorusMeasure_closedBall a (sq_nonneg ε),
      ENNReal.toReal_ofReal (by positivity)]
    simpa only [← pow_mul] using hpow
  have hg : Integrable (fun b => ‖v b‖ ^ 2) unitTorusMeasure := by
    rw [← integrableOn_univ]
    exact (v.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have hpoint (b : Labels) (hb : b ∈ S) : m ≤ ‖v b‖ := by
    have hdist : dist a b ≤ ε ^ 2 := (dist_comm b a) ▸ (Metric.mem_closedBall.mp hb)
    have hsqrt : Real.sqrt (dist a b) ≤ ε := by
      simpa only [Real.sqrt_sq hε.le] using Real.sqrt_le_sqrt hdist
    have hf := (hholder a b).trans (mul_le_mul_of_nonneg_left hsqrt hH)
    apply max_le (norm_nonneg _)
    have htri := norm_sub_norm_le (v a) (v b)
    linarith
  have hbound : (m * ε ^ 3) ^ 2 ≤ ∫ b, ‖v b‖ ^ 2 ∂unitTorusMeasure := by
    calc
      (m * ε ^ 3) ^ 2 = ε ^ 6 * m ^ 2 := by ring
      _ ≤ unitTorusMeasure.real S * m ^ 2 := mul_le_mul_of_nonneg_right hball (sq_nonneg _)
      _ = ∫ _ in S, m ^ 2 ∂unitTorusMeasure := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ b in S, ‖v b‖ ^ 2 ∂unitTorusMeasure := by
        apply integral_mono_ae (integrable_const _) hg.integrableOn
        filter_upwards [ae_restrict_mem hSmeas] with b hb
        exact pow_le_pow_left₀ hm (hpoint b hb) 2
      _ ≤ ∫ b, ‖v b‖ ^ 2 ∂unitTorusMeasure :=
        setIntegral_le_integral hg (ae_of_all _ fun _ => sq_nonneg _)
  have hnorm : m ≤ Real.sqrt (∫ b, ‖v b‖ ^ 2 ∂unitTorusMeasure) / ε ^ 3 :=
    (le_div_iff₀ (pow_pos hε 3)).mpr (Real.le_sqrt_of_sq_le hbound)
  have hsub : ‖v a‖ - ε * H ≤ m := le_max_right _ _
  rw [inv_pow, ← div_eq_inv_mul]
  linarith

/-- A localized coefficient has a small supremum and a radius-independent
Lipschitz bound. Together these give a half-Hölder seminorm of order `√r`. -/
theorem localizedCoefficient_holderHalf {X E : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : X) (χ : X → ℝ) (B : X → E)
    {r C L : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hsupp : ∀ x, 2 * r < dist x a → χ x = 0)
    (hχlip : ∀ x y, ‖χ x - χ y‖ ≤ C / r * dist x y)
    (hBlip : ∀ x y, ‖B x - B y‖ ≤ L * dist x y) :
    let f := fun x => χ x • (B a - B x)
    (∀ x, ‖f x‖ ≤ 2 * r * L) ∧
      (∀ x y, ‖f x - f y‖ ≤ (1 + 2 * C) * L * dist x y) ∧
      (∀ x y, ‖f x - f y‖ ≤ max 4 (1 + 2 * C) * L * Real.sqrt r * Real.sqrt (dist x y)) := by
  let f := fun x => χ x • (B a - B x)
  change (∀ x, ‖f x‖ ≤ 2 * r * L) ∧
    (∀ x y, ‖f x - f y‖ ≤ (1 + 2 * C) * L * dist x y) ∧
    (∀ x y, ‖f x - f y‖ ≤ max 4 (1 + 2 * C) * L * Real.sqrt r * Real.sqrt (dist x y))
  have hχnorm (x : X) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hχ x).1]
    exact (hχ x).2
  have hnear (x : X) (hx : dist x a ≤ 2 * r) : ‖B a - B x‖ ≤ L * (2 * r) := by
    rw [dist_comm x a] at hx
    exact (hBlip a x).trans (mul_le_mul_of_nonneg_left hx hL)
  have hsup (x : X) : ‖f x‖ ≤ 2 * r * L := by
    by_cases hx : dist x a ≤ 2 * r
    · calc
        ‖f x‖ = ‖χ x‖ * ‖B a - B x‖ := norm_smul _ _
        _ ≤ 1 * (L * (2 * r)) := mul_le_mul (hχnorm _) (hnear x hx) (norm_nonneg _) zero_le_one
        _ = 2 * r * L := by ring
    · simp only [f, hsupp x (lt_of_not_ge hx), zero_smul, norm_zero]
      positivity
  have hlipNear (x y : X) (hx : dist x a ≤ 2 * r) :
      ‖f x - f y‖ ≤ (1 + 2 * C) * L * dist x y := by
    have hsplit : f x - f y = (χ x - χ y) • (B a - B x) + χ y • (B y - B x) := by
      simp only [f, sub_smul, smul_sub]
      abel
    have hdy : ‖B y - B x‖ ≤ L * dist x y := by
      rw [dist_comm x y]
      exact hBlip y x
    rw [hsplit]
    calc
      _ ≤ ‖χ x - χ y‖ * ‖B a - B x‖ + ‖χ y‖ * ‖B y - B x‖ := by
        simpa only [norm_smul] using norm_add_le ((χ x - χ y) • (B a - B x)) (χ y • (B y - B x))
      _ ≤ (C / r * dist x y) * (L * (2 * r)) + 1 * (L * dist x y) :=
        add_le_add
          (mul_le_mul (hχlip x y) (hnear x hx) (norm_nonneg _) (by positivity))
          (mul_le_mul (hχnorm _) hdy (norm_nonneg _) zero_le_one)
      _ = (1 + 2 * C) * L * dist x y := by
        field_simp [hr.ne']
        ring
  have hlip (x y : X) : ‖f x - f y‖ ≤ (1 + 2 * C) * L * dist x y := by
    by_cases hx : dist x a ≤ 2 * r
    · exact hlipNear x y hx
    by_cases hy : dist y a ≤ 2 * r
    · rw [norm_sub_rev, dist_comm x y]
      exact hlipNear y x hy
    · simp only [f, hsupp x (lt_of_not_ge hx), hsupp y (lt_of_not_ge hy), zero_smul,
        sub_zero, norm_zero]
      positivity
  refine ⟨hsup, hlip, fun x y => ?_⟩
  let d := dist x y
  have hd : 0 ≤ d := dist_nonneg
  have hcoef : 0 ≤ max 4 (1 + 2 * C) * L :=
    mul_nonneg (zero_le_four.trans (le_max_left _ _)) hL
  have ht : ‖f x - f y‖ ≤ 4 * r * L := by
    linarith only [(norm_sub_le (f x) (f y)).trans (add_le_add (hsup x) (hsup y))]
  change ‖f x - f y‖ ≤ max 4 (1 + 2 * C) * L * Real.sqrt r * Real.sqrt d
  rw [mul_assoc (max 4 (1 + 2 * C) * L)]
  by_cases hsmall : d ≤ r
  · have hd' : d ≤ Real.sqrt r * Real.sqrt d := by
      conv_lhs => rw [← Real.sq_sqrt hd, pow_two]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsmall) (Real.sqrt_nonneg _)
    have hmono : (1 + 2 * C) * L ≤ max 4 (1 + 2 * C) * L :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hL
    exact (hlip x y).trans (mul_le_mul hmono hd' hd hcoef)
  · have hr' : r ≤ Real.sqrt r * Real.sqrt d := by
      conv_lhs => rw [← Real.sq_sqrt hr.le, pow_two]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hsmall)))
        (Real.sqrt_nonneg _)
    calc
      ‖f x - f y‖ ≤ 4 * r * L := ht
      _ = (4 * L) * r := by ring
      _ ≤ (max 4 (1 + 2 * C) * L) * (Real.sqrt r * Real.sqrt d) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hL) hr' hr.le hcoef

end TorusEuler
