import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open Filter MeasureTheory Set

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E]

theorem intervalIntegrable_velocity_of_memLp {a b : ℝ} {v : ℝ → E} (hab : a ≤ b)
    (hv : MemLp v 2 (volume.restrict (Ioc a b))) : IntervalIntegrable v volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hv.integrable one_le_two)

theorem intervalIntegrable_sq_velocity_of_memLp {a b : ℝ} {v : ℝ → E} (hab : a ≤ b)
    (hv : MemLp v 2 (volume.restrict (Ioc a b))) :
    IntervalIntegrable (fun s => ‖v s‖ ^ 2) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv)

variable [NormedSpace ℝ E]

/-- The displacement obtained by integrating the label velocity from the initial time. -/
noncomputable def endpointPrimitive (v : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, v s

@[simp] theorem endpointPrimitive_zero (v : ℝ → E) : endpointPrimitive v 0 = 0 :=
  intervalIntegral.integral_same

theorem endpointPrimitive_terminal {T : ℝ} {v : ℝ → E}
    (hmean : (∫ s in (0 : ℝ)..T, v s) = 0) : endpointPrimitive v T = 0 :=
  hmean

theorem endpointPrimitive_sub_velocity {T : ℝ} {v w : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T) (hw : IntervalIntegrable w volume 0 T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    endpointPrimitive (v - w) t = endpointPrimitive v t - endpointPrimitive w t := by
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  exact intervalIntegral.integral_sub (hv.mono_set hsub) (hw.mono_set hsub)

theorem endpointPrimitive_congr_ae {T : ℝ} {v w : ℝ → E}
    (hvw : v =ᵐ[volume.restrict (Ioc 0 T)] w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    endpointPrimitive v t = endpointPrimitive w t := by
  have hsub : Ioc 0 t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
  simpa only [endpointPrimitive, intervalIntegral.integral_of_le ht.1] using
    integral_congr_ae (hvw.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))

/-- The primitive of an integrable velocity is continuous up to both endpoints. -/
theorem continuousOn_endpointPrimitive {T : ℝ} {v : ℝ → E} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T) :
    ContinuousOn (endpointPrimitive v) (Icc 0 T) := by
  change ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Icc 0 T)
  simpa only [uIcc_of_le hT] using
    intervalIntegral.continuousOn_primitive_interval' hv left_mem_uIcc

/-- For a continuous velocity the derivative identity holds at every time. -/
theorem hasDerivAt_endpointPrimitive [CompleteSpace E] {v : ℝ → E} (hv : Continuous v) (t : ℝ) :
    HasDerivAt (endpointPrimitive v) (v t) t :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

/-- The velocity is the derivative of its primitive almost everywhere in time. -/
theorem ae_hasDerivAt_endpointPrimitive [CompleteSpace E] {T : ℝ} {v : ℝ → E} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), HasDerivAt (endpointPrimitive v) (v t) t := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hv.ae_hasDerivAt_integral] with t ht hIoc
  exact ht (by rw [uIcc_of_le hT]; exact Ioc_subset_Icc_self hIoc) 0 left_mem_uIcc

/-- A primitive on a bounded time interval is square integrable. -/
theorem memLp_endpointPrimitive {T : ℝ} {v : ℝ → E} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T) :
    MemLp (endpointPrimitive v) 2 (volume.restrict (Ioc 0 T)) := by
  have hcont := continuousOn_endpointPrimitive hT hv
  refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact ((hcont.norm.pow 2).intervalIntegrable_of_Icc hT).1

theorem endpointPrimitive_sub_eq_intervalIntegral {T : ℝ} {v : ℝ → E} {a b : ℝ}
    (hv : IntervalIntegrable v volume 0 T) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    endpointPrimitive v b - endpointPrimitive v a = ∫ s in a..b, v s := by
  have hv0a : IntervalIntegrable v volume 0 a := by
    refine hv.mono_set ?_
    rw [uIcc_of_le ha.1, uIcc_of_le (ha.1.trans ha.2)]
    exact Icc_subset_Icc le_rfl ha.2
  have hvab : IntervalIntegrable v volume a b := by
    refine hv.mono_set ?_
    rw [uIcc_of_le (ha.1.trans ha.2)]
    exact uIcc_subset_Icc ha hb
  exact sub_eq_of_eq_add' (intervalIntegral.integral_add_adjacent_intervals hv0a hvab).symm

/-- The primitive of an interval-integrable velocity is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_endpointPrimitive {T : ℝ} {v : ℝ → E} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T) :
    AbsolutelyContinuousOnInterval (endpointPrimitive v) 0 T := by
  rw [absolutelyContinuousOnInterval_iff]
  have hnorm : AbsolutelyContinuousOnInterval (endpointPrimitive fun t => ‖v t‖) 0 T :=
    hv.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  rw [absolutelyContinuousOnInterval_iff] at hnorm
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hnorm ε hε
  refine ⟨δ, hδ, fun intervals hIntervals hlen => ?_⟩
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i hi => ?_) (hbound intervals hIntervals hlen)
  obtain ⟨ha, hb⟩ := hIntervals.1 i hi
  rw [uIcc_of_le hT] at ha hb
  rw [dist_eq_norm, endpointPrimitive_sub_eq_intervalIntegral hv hb ha, Real.dist_eq,
    endpointPrimitive_sub_eq_intervalIntegral hv.norm hb ha]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- For mean-zero velocities the endpoint primitive is also the negative terminal integral. -/
theorem endpointPrimitive_eq_neg_terminal_integral {T : ℝ} {v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T) (hmean : (∫ s in (0 : ℝ)..T, v s) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    endpointPrimitive v t = -(∫ s in t..T, v s) := by
  have h := endpointPrimitive_sub_eq_intervalIntegral hv ht ⟨ht.1.trans ht.2, le_rfl⟩
  rw [endpointPrimitive_terminal hmean, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The squared norm of an interval integral is bounded by the interval length
times the squared `L²` norm of the integrand. -/
theorem norm_sq_intervalIntegral_le_of_memLp {a b : ℝ} {v : ℝ → E} (hab : a ≤ b)
    (hv : MemLp v 2 (volume.restrict (Ioc a b))) :
    ‖∫ s in a..b, v s‖ ^ 2 ≤ (b - a) * ∫ s in a..b, ‖v s‖ ^ 2 := by
  let μ := volume.restrict (Ioc a b)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := fun _ => (1 : ℝ)) (g := fun s => ‖v s‖) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => zero_le_one) (ae_of_all _ fun s => norm_nonneg (v s))
    (by simpa only [ENNReal.ofReal_ofNat] using (memLp_const (μ := μ) (p := 2) (1 : ℝ)))
    (by simpa only [ENNReal.ofReal_ofNat] using hv.norm)
  simp only [one_mul, Real.rpow_two, one_pow, ← Real.sqrt_eq_rpow] at hholder
  have hlength : (∫ _ : ℝ, (1 : ℝ) ∂μ) = b - a := by
    rw [show (∫ _ : ℝ, (1 : ℝ) ∂μ) = (∫ _ in a..b, (1 : ℝ)) from
      (intervalIntegral.integral_of_le hab).symm]
    simp [intervalIntegral.integral_const]
  rw [hlength, ← Real.sqrt_mul (sub_nonneg.mpr hab)] at hholder
  calc
    ‖∫ s in a..b, v s‖ ^ 2 ≤ (∫ s in a..b, ‖v s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := v) hab) 2
    _ ≤ (b - a) * ∫ s in a..b, ‖v s‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (integral_nonneg fun s => norm_nonneg (v s)) hholder 2
      rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hab)
        (integral_nonneg fun s => sq_nonneg ‖v s‖))] at hsq
      simpa only [intervalIntegral.integral_of_le hab] using hsq

private theorem norm_sq_intervalIntegral_le_on {T a b : ℝ} {v : ℝ → E}
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    ‖∫ s in a..b, v s‖ ^ 2 ≤ (b - a) * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 := by
  have hv' : MemLp v 2 (volume.restrict (Ioc a b)) :=
    hv.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc ha hb) le_rfl)
  calc
    ‖∫ s in a..b, v s‖ ^ 2 ≤ (b - a) * ∫ s in a..b, ‖v s‖ ^ 2 :=
      norm_sq_intervalIntegral_le_of_memLp hab hv'
    _ ≤ (b - a) * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval ha hab hb
        (ae_of_all _ fun s => sq_nonneg ‖v s‖)
        (intervalIntegrable_sq_velocity_of_memLp (ha.trans (hab.trans hb)) hv))
        (sub_nonneg.mpr hab)

/-- The squared increment of the primitive is bounded by the elapsed time times
the total squared `L²` norm of the velocity. -/
theorem norm_sq_endpointPrimitive_increment_le {T a b : ℝ} {v : ℝ → E}
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T)
    (hab : a ≤ b) :
    ‖endpointPrimitive v b - endpointPrimitive v a‖ ^ 2 ≤
      (b - a) * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 := by
  rw [endpointPrimitive_sub_eq_intervalIntegral
    (intervalIntegrable_velocity_of_memLp (ha.1.trans ha.2) hv) ha hb]
  exact norm_sq_intervalIntegral_le_on hv ha.1 hab hb.2

/-- An `L²` estimate for the difference of the primitives of two velocities at every time. -/
theorem norm_sq_endpointPrimitive_sub_velocity_le {T : ℝ} {v w : ℝ → E}
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) (hw : MemLp w 2 (volume.restrict (Ioc 0 T)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖endpointPrimitive v t - endpointPrimitive w t‖ ^ 2 ≤
      t * ∫ s in (0 : ℝ)..T, ‖v s - w s‖ ^ 2 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  rw [← endpointPrimitive_sub_velocity
    (intervalIntegrable_velocity_of_memLp hT hv) (intervalIntegrable_velocity_of_memLp hT hw) ht]
  simpa only [endpointPrimitive_zero, sub_zero, Pi.sub_apply] using
    norm_sq_endpointPrimitive_increment_le (hv.sub hw) ⟨le_rfl, hT⟩ ht ht.1

/-- The pointwise inequality in (4.5) for primitives of mean-zero `L²` velocities. -/
theorem endpointPrimitive_terminal_poincare_pointwise {T : ℝ} {v : ℝ → E}
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T)))
    (hmean : (∫ s in (0 : ℝ)..T, v s) = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖endpointPrimitive v t‖ ^ 2 ≤ (T - t) * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 := by
  simpa only [endpointPrimitive_terminal hmean, zero_sub, norm_neg] using
    norm_sq_endpointPrimitive_increment_le hv ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2

/-- The integrated inequality in (4.5) for primitives of mean-zero `L²` velocities. -/
theorem endpointPrimitive_terminal_poincare_integral {T : ℝ} {v : ℝ → E}
    (hT : 0 ≤ T) (hv : MemLp v 2 (volume.restrict (Ioc 0 T)))
    (hmean : (∫ s in (0 : ℝ)..T, v s) = 0) :
    (∫ t in (0 : ℝ)..T, ‖endpointPrimitive v t‖ ^ 2) ≤
      (T ^ 2 / 2) * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 := by
  let energy := ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2
  have hcont := continuousOn_endpointPrimitive hT (intervalIntegrable_velocity_of_memLp hT hv)
  have hbound_cont : Continuous (fun t => (T - t) * energy) :=
    (continuous_const.sub continuous_id).mul continuous_const
  calc
    (∫ t in (0 : ℝ)..T, ‖endpointPrimitive v t‖ ^ 2) ≤ ∫ t in (0 : ℝ)..T, (T - t) * energy :=
      intervalIntegral.integral_mono_on hT ((hcont.norm.pow 2).intervalIntegrable_of_Icc hT)
        (hbound_cont.intervalIntegrable 0 T)
        (fun t ht => endpointPrimitive_terminal_poincare_pointwise hv hmean ht)
    _ = (T ^ 2 / 2) * energy := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_const, integral_id]
      simp only [sub_zero, smul_eq_mul, zero_pow (by decide : 2 ≠ 0)]
      ring

private theorem integral_endpointPrimitive_norm_sq_le {T : ℝ} {v : ℝ → E}
    (hT : 0 ≤ T) (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) :
    (∫ t in (0 : ℝ)..T, ‖endpointPrimitive v t‖ ^ 2) ≤
      T ^ 2 * ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2 := by
  let energy := ∫ s in (0 : ℝ)..T, ‖v s‖ ^ 2
  have henergy : 0 ≤ energy :=
    intervalIntegral.integral_nonneg_of_forall hT (fun s => sq_nonneg ‖v s‖)
  have hcont := continuousOn_endpointPrimitive hT (intervalIntegrable_velocity_of_memLp hT hv)
  calc
    (∫ t in (0 : ℝ)..T, ‖endpointPrimitive v t‖ ^ 2) ≤ ∫ _ in (0 : ℝ)..T, T * energy := by
      apply intervalIntegral.integral_mono_on hT ((hcont.norm.pow 2).intervalIntegrable_of_Icc hT)
        (continuous_const.intervalIntegrable _ _)
      intro t ht
      have hpoint : ‖endpointPrimitive v t‖ ^ 2 ≤ t * energy := by
        simpa only [endpointPrimitive_zero, sub_zero] using
          norm_sq_endpointPrimitive_increment_le hv ⟨le_rfl, hT⟩ ht ht.1
      exact hpoint.trans (mul_le_mul_of_nonneg_right ht.2 henergy)
    _ = T ^ 2 * energy := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul, sq, mul_assoc]

omit [NormedSpace ℝ E] in
private theorem lp_two_norm_sq_eq_intervalIntegral {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (volume.restrict (Ioc 0 T))) :
    ‖v‖ ^ 2 = ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2 := by
  rw [Lp.norm_def, (Lp.memLp v).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  rw [intervalIntegral.integral_of_le hT]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

private noncomputable def endpointPrimitiveLpValue {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (volume.restrict (Ioc 0 T))) : Lp E 2 (volume.restrict (Ioc 0 T)) :=
  (memLp_endpointPrimitive hT
    (intervalIntegrable_velocity_of_memLp hT (Lp.memLp v))).toLp (endpointPrimitive v)

private theorem endpointPrimitiveLpValue_apply_ae {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (volume.restrict (Ioc 0 T))) :
    (endpointPrimitiveLpValue hT v : ℝ → E) =ᵐ[volume.restrict (Ioc 0 T)] endpointPrimitive v :=
  (memLp_endpointPrimitive hT
    (intervalIntegrable_velocity_of_memLp hT (Lp.memLp v))).coeFn_toLp

private noncomputable def endpointPrimitiveLpLinear {T : ℝ} (hT : 0 ≤ T) :
    Lp E 2 (volume.restrict (Ioc 0 T)) →ₗ[ℝ] Lp E 2 (volume.restrict (Ioc 0 T)) where
  toFun := endpointPrimitiveLpValue hT
  map_add' v w := by
    apply Lp.ext
    filter_upwards [endpointPrimitiveLpValue_apply_ae hT (v + w),
      endpointPrimitiveLpValue_apply_ae hT v, endpointPrimitiveLpValue_apply_ae hT w,
      Lp.coeFn_add (endpointPrimitiveLpValue hT v) (endpointPrimitiveLpValue hT w),
      ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))]
      with t hsum hv hw hLpAdd ht
    rw [hsum, hLpAdd, Pi.add_apply, hv, hw]
    have hvs : IntervalIntegrable v volume 0 t :=
      intervalIntegrable_velocity_of_memLp ht.1.le
        ((Lp.memLp v).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl))
    have hws : IntervalIntegrable w volume 0 t :=
      intervalIntegrable_velocity_of_memLp ht.1.le
        ((Lp.memLp w).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl))
    exact (endpointPrimitive_congr_ae (Lp.coeFn_add v w) (Ioc_subset_Icc_self ht)).trans
      (intervalIntegral.integral_add hvs hws)
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [endpointPrimitiveLpValue_apply_ae hT (c • v),
      endpointPrimitiveLpValue_apply_ae hT v, Lp.coeFn_smul c (endpointPrimitiveLpValue hT v),
      ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))]
      with t hs hv hLpSmul ht
    rw [hs, RingHom.id_apply, hLpSmul, Pi.smul_apply, hv]
    exact (endpointPrimitive_congr_ae (Lp.coeFn_smul c v) (Ioc_subset_Icc_self ht)).trans
      (intervalIntegral.integral_smul c v)

private theorem endpointPrimitiveLpLinear_bound {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (volume.restrict (Ioc 0 T))) :
    ‖endpointPrimitiveLpLinear hT v‖ ≤ T * ‖v‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hT (norm_nonneg _))
  rw [mul_pow, lp_two_norm_sq_eq_intervalIntegral hT, lp_two_norm_sq_eq_intervalIntegral hT]
  rw [intervalIntegral.integral_of_le hT]
  have hae := endpointPrimitiveLpValue_apply_ae hT v
  change (∫ t in Ioc 0 T, ‖endpointPrimitiveLpValue hT v t‖ ^ 2) ≤ _
  rw [integral_congr_ae (hae.mono fun t ht => congrArg (fun x : E => ‖x‖ ^ 2) ht)]
  simpa only [intervalIntegral.integral_of_le hT] using
    integral_endpointPrimitive_norm_sq_le hT (Lp.memLp v)

/-- The bounded integration operator on the label velocity space. -/
noncomputable def endpointPrimitiveLp {T : ℝ} (hT : 0 ≤ T) :
    Lp E 2 (volume.restrict (Ioc 0 T)) →L[ℝ] Lp E 2 (volume.restrict (Ioc 0 T)) :=
  (endpointPrimitiveLpLinear hT).mkContinuous T (endpointPrimitiveLpLinear_bound hT)

theorem norm_endpointPrimitiveLp_le {T : ℝ} (hT : 0 ≤ T) :
    ‖endpointPrimitiveLp (E := E) hT‖ ≤ T :=
  LinearMap.mkContinuous_norm_le _ hT _

theorem endpointPrimitiveLp_apply_ae {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (volume.restrict (Ioc 0 T))) :
    (endpointPrimitiveLp hT v : ℝ → E) =ᵐ[volume.restrict (Ioc 0 T)] endpointPrimitive v :=
  endpointPrimitiveLpValue_apply_ae hT v

theorem endpointPrimitiveLp_toLp_apply_ae {T : ℝ} (hT : 0 ≤ T) {v : ℝ → E}
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) :
    (endpointPrimitiveLp hT (hv.toLp v) : ℝ → E) =ᵐ[volume.restrict (Ioc 0 T)]
      endpointPrimitive v :=
  (endpointPrimitiveLp_apply_ae hT (hv.toLp v)).trans <|
    (ae_restrict_mem measurableSet_Ioc).mono fun _ ht =>
      endpointPrimitive_congr_ae hv.coeFn_toLp (Ioc_subset_Icc_self ht)

end TorusEuler
