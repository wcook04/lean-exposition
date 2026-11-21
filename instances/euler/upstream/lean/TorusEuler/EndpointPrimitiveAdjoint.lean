import TorusEuler.EndpointDensity
import TorusEuler.EndpointPrimitive
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E]

private theorem absolutelyContinuousOnInterval_norm {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ, hδ, fun intervals hIntervals hlen => ?_⟩
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => dist_norm_norm_le _ _) ?_
  simpa only [dist_eq_norm] using hbound intervals hIntervals hlen

variable [InnerProductSpace ℝ E]

private theorem absolutelyContinuousOnInterval_inner {f g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => ⟪f t, g t⟫_ℝ) a b := by
  have hf' := absolutelyContinuousOnInterval_norm hf
  have hg' := absolutelyContinuousOnInterval_norm hg
  have hsum := absolutelyContinuousOnInterval_norm (hf.add hg)
  have h := (((hsum.fun_mul hsum).fun_sub (hf'.fun_mul hf')).fun_sub
    (hg'.fun_mul hg')).const_mul (1 / 2 : ℝ)
  convert h using 1
  ext t
  simp only [Pi.add_apply, ← pow_two, norm_add_sq_real]
  ring

variable [CompleteSpace E]

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)

/-- Integration by parts for the time primitives of two square-integrable paths. -/
theorem endpointPrimitiveLp_inner_add_inner_eq (T : ℝ) (hT : 0 ≤ T)
    (u v : Lp E 2 (timeMeasure T)) :
    ⟪endpointPrimitiveLp hT u, v⟫_ℝ + ⟪u, endpointPrimitiveLp hT v⟫_ℝ =
      ⟪endpointIntegral T u, endpointIntegral T v⟫_ℝ := by
  let Ju := endpointPrimitiveLp hT u
  let Jv := endpointPrimitiveLp hT v
  have hu := intervalIntegrable_velocity_of_memLp hT (Lp.memLp u)
  have hv := intervalIntegrable_velocity_of_memLp hT (Lp.memLp v)
  have hAC := absolutelyContinuousOnInterval_inner
    (absolutelyContinuousOnInterval_endpointPrimitive hT hu)
    (absolutelyContinuousOnInterval_endpointPrimitive hT hv)
  rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner Ju v)
    (L2.integrable_inner u Jv)]
  rw [← intervalIntegral.integral_of_le hT]
  have hterminal (w : Lp E 2 (timeMeasure T)) :
      endpointPrimitive w T = endpointIntegral T w := by
    rw [endpointPrimitive, intervalIntegral.integral_of_le hT, endpointIntegral_apply]
  rw [← hterminal u, ← hterminal v]
  have h := hAC.integral_deriv_eq_sub
  rw [endpointPrimitive_zero, endpointPrimitive_zero, inner_zero_left, sub_zero] at h
  rw [← h]
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  filter_upwards [endpointPrimitiveLp_apply_ae hT u, endpointPrimitiveLp_apply_ae hT v,
    ae_hasDerivAt_endpointPrimitive hT hu, ae_hasDerivAt_endpointPrimitive hT hv]
    with t hJu hJv hdu hdv
  rw [hJu, hJv]
  exact (hdu.inner ℝ hdv).deriv.symm

/-- The time primitive is skew under pairing against a zero-time-mean test path. -/
theorem endpointPrimitiveLp_inner_eq_neg_inner {T : ℝ} (hT : 0 ≤ T)
    (u v : Lp E 2 (timeMeasure T)) (hv : endpointIntegral T v = 0) :
    ⟪endpointPrimitiveLp hT u, v⟫_ℝ = -⟪u, endpointPrimitiveLp hT v⟫_ℝ := by
  have h := endpointPrimitiveLp_inner_add_inner_eq T hT u v
  rw [hv, inner_zero_right] at h
  exact eq_neg_of_add_eq_zero_left h

end TorusEuler
