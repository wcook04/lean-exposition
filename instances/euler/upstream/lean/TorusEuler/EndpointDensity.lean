import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)

private theorem norm_timeIntegral_le {T : ℝ} (v : Lp E 2 (timeMeasure T)) :
    ‖∫ t, v t ∂timeMeasure T‖ ≤ (timeMeasure T).real univ ^ (1 / 2 : ℝ) * ‖v‖ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable v)
  rw [eLpNorm_one_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    show 1 / (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  have hfinite : eLpNorm v 2 (timeMeasure T) * (timeMeasure T) univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top v)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top _ _)).ne
  calc
    ‖∫ t, v t ∂timeMeasure T‖ ≤ (∫⁻ t, ‖v t‖ₑ ∂timeMeasure T).toReal := by
      simpa only [ofReal_norm] using norm_integral_le_lintegral_norm v
    _ ≤ (eLpNorm v 2 (timeMeasure T) * (timeMeasure T) univ ^ (1 / 2 : ℝ)).toReal :=
      ENNReal.toReal_mono hfinite h
    _ = _ := by rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, measureReal_def, mul_comm]

/-- Time integration on the fixed-label velocity space. -/
noncomputable def endpointIntegral (T : ℝ) : Lp E 2 (timeMeasure T) →L[ℝ] E := by
  let L : Lp E 2 (timeMeasure T) →ₗ[ℝ] E :=
    { toFun := fun v => ∫ t, v t ∂timeMeasure T
      map_add' := fun v w => by
        change (∫ t, (v + w) t ∂timeMeasure T) = _
        rw [integral_congr_ae (Lp.coeFn_add v w)]
        exact integral_add ((Lp.memLp v).integrable (by norm_num))
          ((Lp.memLp w).integrable (by norm_num))
      map_smul' := fun c v => by
        change (∫ t, (c • v) t ∂timeMeasure T) = _
        rw [integral_congr_ae (Lp.coeFn_smul c v)]
        exact integral_smul c (⇑v) }
  exact L.mkContinuous ((timeMeasure T).real univ ^ (1 / 2 : ℝ)) norm_timeIntegral_le

@[simp] theorem endpointIntegral_apply (T : ℝ) (v : Lp E 2 (timeMeasure T)) :
    endpointIntegral T v = ∫ t, v t ∂timeMeasure T := rfl

private theorem timeMeasure_real_univ {T : ℝ} (hT : 0 ≤ T) :
    (timeMeasure T).real univ = T := by
  rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def, Real.volume_real_Ioc_of_le hT,
    sub_zero]

/-- The time integration bound from the finite-measure `L²` to `L¹` inclusion. -/
theorem norm_endpointIntegral_le {T : ℝ} (hT : 0 ≤ T) (v : Lp E 2 (timeMeasure T)) :
    ‖endpointIntegral T v‖ ≤ Real.sqrt T * ‖v‖ := by
  simpa only [endpointIntegral_apply, timeMeasure_real_univ hT, Real.sqrt_eq_rpow] using
    norm_timeIntegral_le v

/-- Subtract the constant path with value equal to the time average on `[0, T]`. -/
noncomputable def endpointSubtractMean (T : ℝ) :
    Lp E 2 (timeMeasure T) →L[ℝ] Lp E 2 (timeMeasure T) :=
  ContinuousLinearMap.id ℝ _ - (Lp.constL 2 (timeMeasure T) ℝ).comp (T⁻¹ • endpointIntegral T)

theorem endpointSubtractMean_apply (T : ℝ) (v : Lp E 2 (timeMeasure T)) :
    endpointSubtractMean T v = v - Lp.const 2 (timeMeasure T) (T⁻¹ • endpointIntegral T v) := by
  rfl

/-- Subtracting the time average is bounded uniformly in the interval length. -/
theorem norm_endpointSubtractMean_le {T : ℝ} (hT : 0 < T) (v : Lp E 2 (timeMeasure T)) :
    ‖endpointSubtractMean T v‖ ≤ 2 * ‖v‖ := by
  have hconst : ‖Lp.const 2 (timeMeasure T) (T⁻¹ • endpointIntegral T v)‖ ≤ ‖v‖ := by
    rw [Lp.norm_const' _ _ _ (by norm_num) (by norm_num), norm_smul, timeMeasure_real_univ hT.le,
      ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    calc
      _ ≤ T⁻¹ * (Real.sqrt T * ‖v‖) * Real.sqrt T :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_endpointIntegral_le hT.le v) (inv_nonneg.mpr hT.le))
          (Real.sqrt_nonneg T)
      _ = (T⁻¹ * Real.sqrt T ^ 2) * ‖v‖ := by ring
      _ = ‖v‖ := by rw [Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne', one_mul]
  rw [endpointSubtractMean_apply, two_mul]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hconst)

variable [CompleteSpace E]

theorem endpointIntegral_subtractMean {T : ℝ} (hT : 0 < T) (v : Lp E 2 (timeMeasure T)) :
    endpointIntegral T (endpointSubtractMean T v) = 0 := by
  rw [endpointSubtractMean_apply, map_sub]
  have hconst (c : E) : endpointIntegral T (Lp.const 2 (timeMeasure T) c) = T • c := by
    rw [endpointIntegral_apply, integral_congr_ae (Lp.coeFn_const 2 (timeMeasure T) c)]
    simp [Function.const, integral_const, timeMeasure_real_univ hT.le]
  rw [hconst, smul_smul, mul_inv_cancel₀ hT.ne', one_smul, sub_self]

/-- Smooth, zero-integral velocities are dense in the kernel of time integration. -/
theorem closure_smooth_meanZero_L2 {T : ℝ} (hT : 0 < T) :
    closure {v : Lp E 2 (timeMeasure T) | ∃ g : ℝ → E, v =ᵐ[timeMeasure T] g ∧
      ContDiff ℝ ∞ g ∧ (∫ t, g t ∂timeMeasure T) = 0} =
      ((endpointIntegral (E := E) T).ker : Set (Lp E 2 (timeMeasure T))) := by
  apply le_antisymm
  · apply closure_minimal _ (endpointIntegral (E := E) T).isClosed_ker
    rintro v ⟨g, hvg, _, hg⟩
    change endpointIntegral T v = 0
    simpa only [endpointIntegral_apply, integral_congr_ae hvg] using hg
  · let S := {v : Lp E 2 (timeMeasure T) | ∃ g : ℝ → E, v =ᵐ[timeMeasure T] g ∧
        HasCompactSupport g ∧ ContDiff ℝ ∞ g}
    have hS : Dense S := Lp.dense_hasCompactSupport_contDiff (by norm_num)
    intro v hv
    have hv0 : endpointIntegral T v = 0 := hv
    have hfix : endpointSubtractMean T v = v := by simp [endpointSubtractMean_apply, hv0]
    have hclosure := mem_closure_image (endpointSubtractMean (E := E) T).continuous.continuousAt (hS v)
    rw [← hfix]
    apply closure_mono _ hclosure
    rintro u ⟨w, ⟨g, hwg, _, hg⟩, rfl⟩
    let c := T⁻¹ • endpointIntegral T w
    have hw : endpointSubtractMean T w =ᵐ[timeMeasure T] (fun t => g t - c) := by
      rw [endpointSubtractMean_apply]
      exact (Lp.coeFn_sub _ _).trans (hwg.sub (Lp.coeFn_const 2 (timeMeasure T) c))
    refine ⟨fun t => g t - c, hw, hg.sub contDiff_const, ?_⟩
    rw [← integral_congr_ae hw, ← endpointIntegral_apply]
    exact endpointIntegral_subtractMean hT w

/-- A mean-zero square-integrable velocity admits arbitrarily close smooth mean-zero
approximants on the time interval. -/
theorem exists_smooth_meanZero_L2_approx {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hv0 : (∫ t in (0 : ℝ)..T, v t) = 0) :
    ∃ w : ℝ → E, ContDiff ℝ ∞ w ∧ MemLp w 2 (timeMeasure T) ∧
      (∫ t in (0 : ℝ)..T, w t) = 0 ∧ eLpNorm (v - w) 2 (timeMeasure T) < ENNReal.ofReal ε := by
  rw [intervalIntegral.integral_of_le hT.le] at hv0
  have hcl : hv.toLp v ∈ closure {u : Lp E 2 (timeMeasure T) | ∃ g : ℝ → E,
      u =ᵐ[timeMeasure T] g ∧ ContDiff ℝ ∞ g ∧ (∫ t, g t ∂timeMeasure T) = 0} := by
    rw [closure_smooth_meanZero_L2 hT]
    change endpointIntegral T (hv.toLp v) = 0
    rw [endpointIntegral_apply, integral_congr_ae hv.coeFn_toLp, hv0]
  obtain ⟨u, ⟨w, huw, hwd, hw0⟩, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  have hw : MemLp w 2 (timeMeasure T) := (Lp.memLp u).ae_eq huw
  refine ⟨w, hwd, hw, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_of_le hT.le] using hw0
  · rw [← Lp.edist_toLp_toLp v w hv hw, Lp.edist_dist]
    have hwLp : hw.toLp w = u := Lp.ext (hw.coeFn_toLp.trans huw.symm)
    rw [hwLp]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hdist

end TorusEuler
