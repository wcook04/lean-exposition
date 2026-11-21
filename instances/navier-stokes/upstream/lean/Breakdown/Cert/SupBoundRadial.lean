import Mathlib
import Breakdown.Defs

open MeasureTheory Real Set Filter Topology

noncomputable section

namespace Breakdown

namespace Internal.SupBoundRadial

theorem sqrt_scale_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < Real.sqrt (b / a) :=
  Real.sqrt_pos.mpr (div_pos hb ha)

theorem mul_sqrt_scale {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  have e : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

theorem hasDerivAt_prim {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s => arctan (Real.sqrt (b / a) * s) / (a * Real.sqrt (b / a)))
      (a + b * r ^ 2)⁻¹ r := by
  have hc := sqrt_scale_pos ha hb
  have hc2 : Real.sqrt (b / a) ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
  have h := (((hasDerivAt_id r).const_mul (Real.sqrt (b / a))).arctan).div_const
    (a * Real.sqrt (b / a))
  refine h.congr_deriv ?_
  simp only [id, mul_one, mul_pow, hc2]
  field_simp

theorem tendsto_prim {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun s => arctan (Real.sqrt (b / a) * s) / (a * Real.sqrt (b / a))) atTop
      (𝓝 ((π / 2) / (a * Real.sqrt (b / a)))) := by
  have hc := sqrt_scale_pos ha hb
  have ht : Tendsto (fun s => arctan (Real.sqrt (b / a) * s)) atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp (tendsto_id.const_mul_atTop hc)
  exact ht.div_const _

theorem integrableOn_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => (a + b * r ^ 2)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_prim ha hb r)
    (fun r _ => by positivity) (tendsto_prim ha hb)

theorem integral_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ r in Ioi (0 : ℝ), (a + b * r ^ 2)⁻¹ = π / (2 * Real.sqrt (a * b)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => hasDerivAt_prim ha hb r)
    (integrableOn_Ioi ha hb) (tendsto_prim ha hb)]
  rw [mul_sqrt_scale ha hb]
  simp only [mul_zero, arctan_zero, zero_div, sub_zero]
  ring

theorem radial_eqOn {a b : ℝ} :
    EqOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • (a * y ^ 2 + b * y ^ 4)⁻¹)
      (fun y => (a + b * y ^ 2)⁻¹) (Ioi 0) := by
  intro y hy
  have hy : 0 < y := hy
  have hy2 : y ^ 2 ≠ 0 := by positivity
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have e : a * y ^ 2 + b * y ^ 4 = y ^ 2 * (a + b * y ^ 2) := by ring
  rw [e, mul_inv, ← mul_assoc, show (3 - 1 : ℕ) = 2 from rfl, mul_inv_cancel₀ hy2, one_mul]

theorem volume_real_ball_one : (volume : Measure Space).real (Metric.ball 0 1) = π * 4 / 3 := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

end Internal.SupBoundRadial

open Internal.SupBoundRadial

theorem integrable_inv_radial {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun ξ : Space => (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun y : ℝ => (a * y ^ 2 + b * y ^ 4)⁻¹)).mpr
    ((integrableOn_congr_fun radial_eqOn measurableSet_Ioi).mpr (integrableOn_Ioi ha hb))
  exact h

theorem integral_inv_radial {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ ξ : Space, (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹ = 2 * π ^ 2 / Real.sqrt (a * b) := by
  have h := integral_fun_norm_addHaar (volume : Measure Space)
    (fun y : ℝ => (a * y ^ 2 + b * y ^ 4)⁻¹)
  rw [h, setIntegral_congr_fun measurableSet_Ioi radial_eqOn, integral_Ioi ha hb,
    volume_real_ball_one]
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  field_simp
  ring

end Breakdown
