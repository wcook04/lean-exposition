import TorusEuler.EndpointPrimitive
import TorusEuler.TorusFourier
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set

namespace TorusEuler

local notation "timeVolume" T => volume.restrict (Ioc (0 : ℝ) T)

section Product

variable {A E : Type*} [MeasurableSpace A]
variable {ν : Measure A} [SFinite ν] {T : ℝ}

/-- Equality almost everywhere on the product implies equality on almost every time slice. -/
theorem ae_endpointTimeSlice_congr {v w : ℝ × A → E} (h : v =ᵐ[(timeVolume T).prod ν] w) :
    ∀ᵐ a ∂ν, (fun t => v (t, a)) =ᵐ[timeVolume T] (fun t => w (t, a)) :=
  Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp h)

variable [NormedAddCommGroup E]

/-- A square-integrable joint velocity is square integrable in time for almost every label. -/
theorem ae_memLp_endpointTimeSlice {v : ℝ × A → E} (hv : MemLp v 2 ((timeVolume T).prod ν)) :
    ∀ᵐ a ∂ν, MemLp (fun t => v (t, a)) 2 (timeVolume T) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  filter_upwards [hv.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with a hmeas hint
  exact (memLp_two_iff_integrable_sq_norm hmeas).mpr hint

variable [NormedSpace ℝ E]

/-- Integration in time sends joint `L²` velocities to square-integrable label fields. -/
theorem memLp_endpointTimeIntegral (hT : 0 ≤ T) {v : ℝ × A → E}
    (hv : MemLp v 2 ((timeVolume T).prod ν)) :
    MemLp (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) 2 ν := by
  have hmeas : AEStronglyMeasurable (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) ν :=
    hv.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hsq := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr
    ((hsq.integral_prod_right.const_mul T).mono' (hmeas.norm.pow 2) ?_)
  filter_upwards [ae_memLp_endpointTimeSlice hv] with a ha
  simpa only [Real.norm_of_nonneg (sq_nonneg _), intervalIntegral.integral_of_le hT, sub_zero] using
    norm_sq_intervalIntegral_le_of_memLp hT ha

private noncomputable def endpointTimeIntegralValue (hT : 0 ≤ T)
    (v : Lp E 2 ((timeVolume T).prod ν)) : Lp E 2 ν :=
  (memLp_endpointTimeIntegral hT (Lp.memLp v)).toLp (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a))

private theorem endpointTimeIntegralValue_apply_ae (hT : 0 ≤ T)
    (v : Lp E 2 ((timeVolume T).prod ν)) :
    (endpointTimeIntegralValue hT v : A → E) =ᵐ[ν] (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) :=
  (memLp_endpointTimeIntegral hT (Lp.memLp v)).coeFn_toLp

private noncomputable def endpointTimeIntegralLinear (hT : 0 ≤ T) :
    Lp E 2 ((timeVolume T).prod ν) →ₗ[ℝ] Lp E 2 ν where
  toFun := endpointTimeIntegralValue hT
  map_add' v w := by
    apply Lp.ext
    filter_upwards [endpointTimeIntegralValue_apply_ae hT (v + w),
      endpointTimeIntegralValue_apply_ae hT v, endpointTimeIntegralValue_apply_ae hT w,
      Lp.coeFn_add (endpointTimeIntegralValue hT v) (endpointTimeIntegralValue hT w),
      ae_endpointTimeSlice_congr (Lp.coeFn_add v w), ae_memLp_endpointTimeSlice (Lp.memLp v),
      ae_memLp_endpointTimeSlice (Lp.memLp w)] with a hsum hv hw hadd hslice hvl hwl
    rw [hsum, hadd, Pi.add_apply, hv, hw, integral_congr_ae hslice]
    exact integral_add (hvl.integrable one_le_two) (hwl.integrable one_le_two)
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [endpointTimeIntegralValue_apply_ae hT (c • v),
      endpointTimeIntegralValue_apply_ae hT v,
      Lp.coeFn_smul c (endpointTimeIntegralValue hT v),
      ae_endpointTimeSlice_congr (Lp.coeFn_smul c v)] with a hsmul hv hsmul' hslice
    rw [hsmul, RingHom.id_apply, hsmul', Pi.smul_apply, hv, integral_congr_ae hslice]
    exact integral_smul c (fun t => v (t, a))

omit [NormedSpace ℝ E] in
private theorem norm_sq_Lp_two_eq_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, (Lp.memLp v).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

private theorem endpointTimeIntegralLinear_bound (hT : 0 ≤ T)
    (v : Lp E 2 ((timeVolume T).prod ν)) :
    ‖endpointTimeIntegralLinear hT v‖ ≤ Real.sqrt T * ‖v‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt hT, norm_sq_Lp_two_eq_integral, norm_sq_Lp_two_eq_integral]
  change (∫ a, ‖endpointTimeIntegralValue hT v a‖ ^ 2 ∂ν) ≤ _
  rw [integral_congr_ae ((endpointTimeIntegralValue_apply_ae hT v).mono fun a ha =>
    congrArg (fun x : E => ‖x‖ ^ 2) ha)]
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hmean := memLp_endpointTimeIntegral hT (Lp.memLp v)
  rw [integral_prod_symm _ hsq, ← integral_const_mul]
  apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hmean.aestronglyMeasurable).mp hmean)
    (hsq.integral_prod_right.const_mul T)
  filter_upwards [ae_memLp_endpointTimeSlice (Lp.memLp v)] with a ha
  simpa only [intervalIntegral.integral_of_le hT, sub_zero] using
    norm_sq_intervalIntegral_le_of_memLp hT ha

/-- The bounded partial time integral on the product `L²` space. -/
noncomputable def endpointTimeIntegral (ν : Measure A) [SFinite ν] {T : ℝ} (hT : 0 ≤ T) :
    Lp E 2 ((timeVolume T).prod ν) →L[ℝ] Lp E 2 ν :=
  (endpointTimeIntegralLinear hT).mkContinuous (Real.sqrt T) (endpointTimeIntegralLinear_bound hT)

theorem norm_endpointTimeIntegral_le (ν : Measure A) [SFinite ν] (hT : 0 ≤ T) :
    ‖endpointTimeIntegral (E := E) ν hT‖ ≤ Real.sqrt T :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem endpointTimeIntegral_apply_ae (hT : 0 ≤ T) (v : Lp E 2 ((timeVolume T).prod ν)) :
    (endpointTimeIntegral ν hT v : A → E) =ᵐ[ν] (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) :=
  endpointTimeIntegralValue_apply_ae hT v

theorem endpointTimeIntegral_toLp_apply_ae (hT : 0 ≤ T) {v : ℝ × A → E}
    (hv : MemLp v 2 ((timeVolume T).prod ν)) :
    (endpointTimeIntegral ν hT (hv.toLp v) : A → E) =ᵐ[ν] (fun a => ∫ t in Ioc (0 : ℝ) T, v (t, a)) := by
  filter_upwards [endpointTimeIntegral_apply_ae hT (hv.toLp v),
    ae_endpointTimeSlice_congr hv.coeFn_toLp] with a hvalue hae
  exact hvalue.trans (integral_congr_ae hae)

/-- The kernel of partial time integration consists of paths whose time integral
vanishes for almost every label. -/
theorem endpointTimeIntegral_eq_zero_iff (hT : 0 ≤ T) (v : Lp E 2 ((timeVolume T).prod ν)) :
    endpointTimeIntegral ν hT v = 0 ↔
      ∀ᵐ a ∂ν, (∫ t in Ioc (0 : ℝ) T, v (t, a)) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact ⟨(endpointTimeIntegral_apply_ae hT v).symm.trans, (endpointTimeIntegral_apply_ae hT v).trans⟩

end Product

/-- Time integration of a joint time–torus velocity, with values in spatial `L²`. -/
noncomputable def endpointTorusTimeIntegral {T : ℝ} (hT : 0 ≤ T) :
    Lp Vec3 2 ((timeVolume T).prod unitTorusMeasure) →L[ℝ] Lp Vec3 2 unitTorusMeasure :=
  endpointTimeIntegral unitTorusMeasure hT

theorem norm_endpointTorusTimeIntegral_le {T : ℝ} (hT : 0 ≤ T) :
    ‖endpointTorusTimeIntegral hT‖ ≤ Real.sqrt T :=
  norm_endpointTimeIntegral_le unitTorusMeasure hT

theorem endpointTorusTimeIntegral_apply_ae {T : ℝ} (hT : 0 ≤ T)
    (v : Lp Vec3 2 ((timeVolume T).prod unitTorusMeasure)) :
    (endpointTorusTimeIntegral hT v : UnitAddTorus (Fin 3) → Vec3) =ᵐ[unitTorusMeasure]
      fun a => ∫ t in (0 : ℝ)..T, v (t, a) := by
  simpa only [endpointTorusTimeIntegral, intervalIntegral.integral_of_le hT] using
    endpointTimeIntegral_apply_ae hT v

theorem endpointTorusTimeIntegral_eq_zero_iff {T : ℝ} (hT : 0 ≤ T)
    (v : Lp Vec3 2 ((timeVolume T).prod unitTorusMeasure)) :
    endpointTorusTimeIntegral hT v = 0 ↔
      ∀ᵐ a ∂unitTorusMeasure, (∫ t in (0 : ℝ)..T, v (t, a)) = 0 := by
  simpa only [endpointTorusTimeIntegral, intervalIntegral.integral_of_le hT] using
    endpointTimeIntegral_eq_zero_iff hT v

end TorusEuler
