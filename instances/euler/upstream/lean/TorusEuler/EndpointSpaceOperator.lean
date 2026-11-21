import TorusEuler.EndpointMeanFubini
import TorusEuler.EndpointL2Multiplier
import TorusEuler.EndpointPrimitiveAdjoint
import TorusEuler.EndpointSpace
import TorusEuler.ProjectedHilbertInverse

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

variable {A E : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ν : Measure A) [SFinite ν]

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "ProductL2(" T ")" => Lp E 2 (Measure.prod (timeMeasure T) ν)

/-- The primitive obtained by integrating along the time coordinate at a fixed label. -/
noncomputable def endpointProductPrimitiveRep {T : ℝ} (v : ProductL2(T)) (q : ℝ × A) : E :=
  ∫ s in Ioc (0 : ℝ) q.1, v (s, q.2) ∂timeMeasure T

omit [SFinite ν] in
theorem endpointProductPrimitiveRep_eq {T : ℝ} (v : ProductL2(T)) (q : ℝ × A)
    (hq : q.1 ∈ Icc 0 T) :
    endpointProductPrimitiveRep ν v q = endpointPrimitive (fun s => v (s, q.2)) q.1 := by
  rw [endpointProductPrimitiveRep, endpointPrimitive, intervalIntegral.integral_of_le hq.1,
    Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hq.2)]

omit [SFinite ν] in
private theorem stronglyMeasurable_endpointProductPrimitiveRep {T : ℝ} (v : ProductL2(T)) :
    StronglyMeasurable (endpointProductPrimitiveRep ν v) := by
  let f : (ℝ × A) × ℝ → E := fun x => v (x.2, x.1.2)
  let s : Set ((ℝ × A) × ℝ) := {x | x.2 ∈ Ioc (0 : ℝ) x.1.1}
  have hs : MeasurableSet s := by
    change MeasurableSet ({x : (ℝ × A) × ℝ | 0 < x.2} ∩ {x : (ℝ × A) × ℝ | x.2 ≤ x.1.1})
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hf : StronglyMeasurable f :=
    (Lp.stronglyMeasurable v).comp_measurable
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have h := (hf.indicator hs).integral_prod_right' (ν := timeMeasure T)
  convert h using 1
  ext q
  rw [endpointProductPrimitiveRep, ← integral_indicator measurableSet_Ioc]
  rfl

omit [SFinite ν] in
private theorem ae_mem_productTimeInterval (T : ℝ) :
    ∀ᵐ q ∂(timeMeasure T).prod ν, q.1 ∈ Ioc 0 T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)

private theorem endpointProductPrimitiveRep_sq_le {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    ∀ᵐ q ∂(timeMeasure T).prod ν, ‖endpointProductPrimitiveRep ν v q‖ ^ 2 ≤
      T * ∫ s in Ioc (0 : ℝ) T, ‖v (s, q.2)‖ ^ 2 := by
  have hLp := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae (ae_memLp_endpointTimeSlice (Lp.memLp v))
  filter_upwards [ae_mem_productTimeInterval ν T, hLp] with q hq hv
  rw [endpointProductPrimitiveRep_eq ν v q (Ioc_subset_Icc_self hq)]
  have h := norm_sq_endpointPrimitive_increment_le hv (a := 0) (b := q.1)
    ⟨le_rfl, hT⟩ (Ioc_subset_Icc_self hq) hq.1.le
  rw [endpointPrimitive_zero, sub_zero, sub_zero, intervalIntegral.integral_of_le hT] at h
  exact h.trans (mul_le_mul_of_nonneg_right hq.2 (integral_nonneg fun _ => sq_nonneg _))

omit [InnerProductSpace ℝ E] in
private theorem integrable_sq_endpointProductPrimitiveRep_bound {T : ℝ} (v : ProductL2(T)) :
    Integrable (fun q => T * ∫ s in Ioc (0 : ℝ) T, ‖v (s, q.2)‖ ^ 2) ((timeMeasure T).prod ν) := by
  have hsq : Integrable (fun q => ‖v q‖ ^ 2) ((timeMeasure T).prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  exact (hsq.integral_prod_right.const_mul T).comp_snd (timeMeasure T)


private theorem memLp_endpointProductPrimitiveRep {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    MemLp (endpointProductPrimitiveRep ν v) 2 ((timeMeasure T).prod ν) := by
  have hm : AEStronglyMeasurable (endpointProductPrimitiveRep ν v) ((timeMeasure T).prod ν) :=
    (stronglyMeasurable_endpointProductPrimitiveRep ν v).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact (integrable_sq_endpointProductPrimitiveRep_bound ν v).mono
    (hm.norm.pow 2)
    ((endpointProductPrimitiveRep_sq_le ν hT v).mono fun _ h => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact h.trans (le_abs_self _))

private noncomputable def endpointProductPrimitiveValue {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    ProductL2(T) :=
  (memLp_endpointProductPrimitiveRep ν hT v).toLp (endpointProductPrimitiveRep ν v)

private theorem endpointProductPrimitiveValue_apply_ae {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    (endpointProductPrimitiveValue ν hT v : ℝ × A → E) =ᵐ[(timeMeasure T).prod ν]
      endpointProductPrimitiveRep ν v :=
  (memLp_endpointProductPrimitiveRep ν hT v).coeFn_toLp

private noncomputable def endpointProductPrimitiveLinear {T : ℝ} (hT : 0 ≤ T) :
    ProductL2(T) →ₗ[ℝ] ProductL2(T) where
  toFun := endpointProductPrimitiveValue ν hT
  map_add' v w := by
    apply Lp.ext
    have h := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae (ae_endpointTimeSlice_congr (Lp.coeFn_add v w))
    have hv := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae (ae_memLp_endpointTimeSlice (Lp.memLp v))
    have hw := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae (ae_memLp_endpointTimeSlice (Lp.memLp w))
    filter_upwards [endpointProductPrimitiveValue_apply_ae ν hT (v + w),
      endpointProductPrimitiveValue_apply_ae ν hT v, endpointProductPrimitiveValue_apply_ae ν hT w,
      Lp.coeFn_add (endpointProductPrimitiveValue ν hT v) (endpointProductPrimitiveValue ν hT w),
      h, hv, hw] with q hsum hvq hwq hadd hs hvLp hwLp
    rw [hsum, hadd, Pi.add_apply, hvq, hwq]
    simp only [endpointProductPrimitiveRep]
    have hr := hs.filter_mono (ae_mono (Measure.restrict_le_self (s := Ioc (0 : ℝ) q.1)))
    rw [integral_congr_ae hr]
    exact integral_add (hvLp.integrable one_le_two).restrict (hwLp.integrable one_le_two).restrict
  map_smul' c v := by
    apply Lp.ext
    have h := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae (ae_endpointTimeSlice_congr (Lp.coeFn_smul c v))
    filter_upwards [endpointProductPrimitiveValue_apply_ae ν hT (c • v),
      endpointProductPrimitiveValue_apply_ae ν hT v,
      Lp.coeFn_smul c (endpointProductPrimitiveValue ν hT v), h] with q hsmul hvq hlp hs
    rw [hsmul, RingHom.id_apply, hlp, Pi.smul_apply, hvq]
    simp only [endpointProductPrimitiveRep]
    have hr := hs.filter_mono (ae_mono (Measure.restrict_le_self (s := Ioc (0 : ℝ) q.1)))
    rw [integral_congr_ae hr]
    exact integral_smul c _

private theorem timeMeasure_real_univ_productPrimitive {T : ℝ} (hT : 0 ≤ T) :
    (timeMeasure T).real univ = T := by
  rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def, Real.volume_real_Ioc_of_le hT,
    sub_zero]

private theorem lp_two_sq_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem endpointProductPrimitiveLinear_bound {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    ‖endpointProductPrimitiveLinear ν hT v‖ ≤ T * ‖v‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg hT (norm_nonneg _))
  rw [mul_pow, lp_two_sq_eq_integral, lp_two_sq_eq_integral]
  change (∫ q, ‖endpointProductPrimitiveValue ν hT v q‖ ^ 2 ∂(timeMeasure T).prod ν) ≤ _
  have hae := endpointProductPrimitiveValue_apply_ae ν hT v
  rw [integral_congr_ae (hae.mono fun _ h => congrArg (fun z : E => ‖z‖ ^ 2) h)]
  have hsq : Integrable (fun q => ‖v q‖ ^ 2) ((timeMeasure T).prod ν) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  calc
    _ ≤ ∫ q : ℝ × A, T * (∫ s, ‖v (s, q.2)‖ ^ 2 ∂timeMeasure T) ∂(timeMeasure T).prod ν :=
      integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm
          (stronglyMeasurable_endpointProductPrimitiveRep ν v).aestronglyMeasurable).mp
          (memLp_endpointProductPrimitiveRep ν hT v))
        (integrable_sq_endpointProductPrimitiveRep_bound ν v)
        (endpointProductPrimitiveRep_sq_le ν hT v)
    _ = _ := by
      rw [integral_fun_snd (fun a => T * ∫ s, ‖v (s, a)‖ ^ 2 ∂timeMeasure T),
        timeMeasure_real_univ_productPrimitive hT, integral_const_mul,
        ← integral_prod_symm _ hsq, smul_eq_mul, sq, mul_assoc]

/-- The joint (L²) primitive integrates in time and leaves the label fixed. -/
noncomputable def endpointProductPrimitive {T : ℝ} (hT : 0 ≤ T) : ProductL2(T) →L[ℝ] ProductL2(T) :=
  (endpointProductPrimitiveLinear ν hT).mkContinuous T (endpointProductPrimitiveLinear_bound ν hT)

theorem norm_endpointProductPrimitive_le {T : ℝ} (hT : 0 ≤ T) :
    ‖endpointProductPrimitive (E := E) ν hT‖ ≤ T :=
  LinearMap.mkContinuous_norm_le _ hT _

theorem endpointProductPrimitive_apply_ae {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    (endpointProductPrimitive ν hT v : ℝ × A → E) =ᵐ[(timeMeasure T).prod ν]
      fun q => endpointPrimitive (fun s => v (s, q.2)) q.1 :=
  (endpointProductPrimitiveValue_apply_ae ν hT v).trans <|
    (ae_mem_productTimeInterval ν T).mono fun q hq =>
      endpointProductPrimitiveRep_eq ν v q (Ioc_subset_Icc_self hq)

/-- On almost every time slice, the joint primitive agrees with the one-label continuous
linear primitive on the square-integrable restriction of the velocity. -/
theorem endpointProductPrimitive_ae_timeSlice {T : ℝ} (hT : 0 ≤ T) (v : ProductL2(T)) :
    ∀ᵐ a ∂ν, ∃ hv : MemLp (fun s => v (s, a)) 2 (timeMeasure T),
      (fun t => endpointProductPrimitive ν hT v (t, a)) =ᵐ[timeMeasure T]
        (endpointPrimitiveLp hT (hv.toLp (fun s => v (s, a))) : ℝ → E) := by
  filter_upwards [ae_endpointTimeSlice_congr (endpointProductPrimitive_apply_ae ν hT v),
    ae_memLp_endpointTimeSlice (Lp.memLp v)] with a ha hmem
  exact ⟨hmem, ha.trans (endpointPrimitiveLp_toLp_apply_ae hT hmem).symm⟩

/-- The ambient space-time endpoint operator from Appendix A is multiplication by
`K` minus the time primitive of the multiplication by `Ω`. -/
noncomputable def endpointProductOperator {T : ℝ} (hT : 0 ≤ T)
    (K Ω : ℝ × A → E →L[ℝ] E)
    (hK : AEStronglyMeasurable K ((timeMeasure T).prod ν))
    (hΩ : AEStronglyMeasurable Ω ((timeMeasure T).prod ν))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖Ω q‖ ≤ CΩ) :
    ProductL2(T) →L[ℝ] ProductL2(T) :=
  endpointL2Multiplier K hK bK -
    (endpointProductPrimitive ν hT).comp (endpointL2Multiplier Ω hΩ bΩ)

theorem endpointProductOperator_apply_ae {T : ℝ} (hT : 0 ≤ T)
    (K Ω : ℝ × A → E →L[ℝ] E)
    (hK : AEStronglyMeasurable K ((timeMeasure T).prod ν))
    (hΩ : AEStronglyMeasurable Ω ((timeMeasure T).prod ν))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖Ω q‖ ≤ CΩ) (v : ProductL2(T)) :
    (endpointProductOperator ν hT K Ω hK hΩ bK bΩ v : ℝ × A → E) =ᵐ[(timeMeasure T).prod ν]
      fun q => K q (v q) - endpointPrimitive (fun t => Ω (t, q.2) (v (t, q.2))) q.1 := by
  let x := endpointL2Multiplier K hK bK v
  let y := endpointL2Multiplier Ω hΩ bΩ v
  have hsl := (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := ν)).ae
    (ae_endpointTimeSlice_congr (endpointL2Multiplier_apply_ae Ω hΩ bΩ v))
  have h := Lp.coeFn_sub x (endpointProductPrimitive ν hT y)
  change (x - endpointProductPrimitive ν hT y : ProductL2(T)) =ᵐ[(timeMeasure T).prod ν] _
  filter_upwards [h, hsl, endpointL2Multiplier_apply_ae K hK bK v,
    endpointProductPrimitive_apply_ae ν hT y, ae_mem_productTimeInterval ν T]
    with q hsub hs hx hy hq
  rw [hsub, Pi.sub_apply, hx, hy, endpointPrimitive_congr_ae hs (Ioc_subset_Icc_self hq)]

/-- Integrating a time-slice inequality gives the corresponding product Hilbert inequality. -/
theorem endpointProduct_inner_lower_bound_of_ae_slice {T c : ℝ} (v w : ProductL2(T))
    (h : ∀ᵐ a ∂ν, c * (∫ t, ‖v (t, a)‖ ^ 2 ∂timeMeasure T) ≤
      ∫ t, ⟪w (t, a), v (t, a)⟫_ℝ ∂timeMeasure T) :
    c * ‖v‖ ^ 2 ≤ ⟪w, v⟫_ℝ := by
  have hs := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hi := L2.integrable_inner (𝕜 := ℝ) w v
  rw [lp_two_sq_eq_integral, L2.inner_def, integral_prod_symm _ hs, integral_prod_symm _ hi,
    ← integral_const_mul]
  exact integral_mono_ae (hs.integral_prod_right.const_mul c) hi.integral_prod_right h

/-- Coercivity of the endpoint quadratic form on time slices yields coercivity in the
space-time Hilbert space with the same constant. -/
theorem endpointProductOperator_coercive_of_ae_slice {T c : ℝ} (hT : 0 ≤ T)
    (K Ω : ℝ × A → E →L[ℝ] E)
    (hK : AEStronglyMeasurable K ((timeMeasure T).prod ν))
    (hΩ : AEStronglyMeasurable Ω ((timeMeasure T).prod ν))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂(timeMeasure T).prod ν, ‖Ω q‖ ≤ CΩ) (v : ProductL2(T))
    (hslice : ∀ᵐ a ∂ν, c * (∫ t, ‖v (t, a)‖ ^ 2 ∂timeMeasure T) ≤
      ∫ t, ⟪K (t, a) (v (t, a)) - endpointPrimitive (fun s => Ω (s, a) (v (s, a))) t,
        v (t, a)⟫_ℝ ∂timeMeasure T) :
    c * ‖v‖ ^ 2 ≤ ⟪endpointProductOperator ν hT K Ω hK hΩ bK bΩ v, v⟫_ℝ := by
  apply endpointProduct_inner_lower_bound_of_ae_slice ν
  have h := ae_endpointTimeSlice_congr (endpointProductOperator_apply_ae ν hT K Ω hK hΩ bK bΩ v)
  filter_upwards [hslice, h] with a ha hslice
  rw [integral_congr_ae (hslice.mono fun t ht => congrArg (fun x => ⟪x, v (t, a)⟫_ℝ) ht)]
  exact ha

private theorem integrable_inner_of_memLp_pair {T : ℝ} {u v : ℝ → E}
    (hu : MemLp u 2 (timeMeasure T)) (hv : MemLp v 2 (timeMeasure T)) :
    Integrable (fun t => ⟪u t, v t⟫_ℝ) (timeMeasure T) :=
  (L2.integrable_inner (hu.toLp u) (hv.toLp v)).congr <| by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with t htu htv
    rw [htu, htv]

variable [CompleteSpace E]

private theorem integral_endpointPrimitive_inner_eq_neg {T : ℝ} (hT : 0 ≤ T)
    {u v : ℝ → E} (hu : MemLp u 2 (timeMeasure T)) (hv : MemLp v 2 (timeMeasure T))
    (hmean : (∫ t, v t ∂timeMeasure T) = 0) :
    (∫ t, ⟪endpointPrimitive u t, v t⟫_ℝ ∂timeMeasure T) =
      -(∫ t, ⟪u t, endpointPrimitive v t⟫_ℝ ∂timeMeasure T) := by
  have hmean' : endpointIntegral T (hv.toLp v) = 0 := by
    rw [endpointIntegral_apply, integral_congr_ae hv.coeFn_toLp, hmean]
  have h := endpointPrimitiveLp_inner_eq_neg_inner hT (hu.toLp u) (hv.toLp v) hmean'
  rw [L2.inner_def, L2.inner_def] at h
  have hl : (∫ t, ⟪endpointPrimitiveLp hT (hu.toLp u) t, hv.toLp v t⟫_ℝ ∂timeMeasure T) =
      ∫ t, ⟪endpointPrimitive u t, v t⟫_ℝ ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [endpointPrimitiveLp_toLp_apply_ae hT hu, hv.coeFn_toLp] with t htu htv
    rw [htu, htv]
  have hr : (∫ t, ⟪hu.toLp u t, endpointPrimitiveLp hT (hv.toLp v) t⟫_ℝ ∂timeMeasure T) =
      ∫ t, ⟪u t, endpointPrimitive v t⟫_ℝ ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, endpointPrimitiveLp_toLp_apply_ae hT hv] with t htu htv
    rw [htu, htv]
  exact hl.symm.trans (h.trans (congrArg Neg.neg hr))

private theorem integral_endpointProductOperator_slice_eq {T : ℝ} (hT : 0 ≤ T)
    {v w k : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (hk : MemLp k 2 (timeMeasure T)) (hmean : (∫ t, v t ∂timeMeasure T) = 0) :
    (∫ t, ⟪k t - endpointPrimitive w t, v t⟫_ℝ ∂timeMeasure T) =
      ∫ t, ⟪k t, v t⟫_ℝ + ⟪w t, endpointPrimitive v t⟫_ℝ ∂timeMeasure T := by
  have hJw := memLp_endpointPrimitive hT (intervalIntegrable_velocity_of_memLp hT hw)
  have hJv := memLp_endpointPrimitive hT (intervalIntegrable_velocity_of_memLp hT hv)
  have hkv := integrable_inner_of_memLp_pair hk hv
  simp_rw [inner_sub_left]
  rw [integral_sub hkv (integrable_inner_of_memLp_pair hJw hv),
    integral_add hkv (integrable_inner_of_memLp_pair hw hJv),
    integral_endpointPrimitive_inner_eq_neg hT hw hv hmean, sub_neg_eq_add]

/-- The projected space-time endpoint equation has a unique weak `L²` solution
under the integrated time-slice coercivity hypothesis of Appendix A.
The spatial Hölder estimates are a separate regularity step. -/
theorem exists_endpointTorusL2Solution {T c : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (K Ω : ℝ × UnitAddTorus (Fin 3) → Vec3 →L[ℝ] Vec3)
    (hK : AEStronglyMeasurable K (endpointTorusMeasure T))
    (hΩ : AEStronglyMeasurable Ω (endpointTorusMeasure T))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂endpointTorusMeasure T, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂endpointTorusMeasure T, ‖Ω q‖ ≤ CΩ)
    (hcoercive : ∀ᵐ a ∂unitTorusMeasure, ∀ v : ℝ → Vec3,
      MemLp v 2 (timeMeasure T) → (∫ t, v t ∂timeMeasure T) = 0 →
      c * (∫ t, ‖v t‖ ^ 2 ∂timeMeasure T) ≤
        ∫ t, ⟪K (t, a) (v t), v t⟫_ℝ + ⟪Ω (t, a) (v t), endpointPrimitive v t⟫_ℝ
          ∂timeMeasure T)
    (f : EndpointTorusL2 T) :
    let B := endpointProductOperator unitTorusMeasure hT K Ω hK hΩ bK bΩ
    ∃ v : endpointTorusSpace T,
      (∀ w : endpointTorusSpace T, ⟪B (v : EndpointTorusL2 T), (w : EndpointTorusL2 T)⟫_ℝ =
        ⟪f, (w : EndpointTorusL2 T)⟫_ℝ) ∧ ‖v‖ ≤ ‖f‖ / c ∧
      ∀ u : endpointTorusSpace T,
        (∀ w : endpointTorusSpace T, ⟪B (u : EndpointTorusL2 T), (w : EndpointTorusL2 T)⟫_ℝ =
          ⟪f, (w : EndpointTorusL2 T)⟫_ℝ) → u = v := by
  dsimp only
  refine exists_projectedHilbertSolution (endpointTorusSpace T) (isClosed_endpointTorusSpace T)
    _ hc (fun v => ?_) f
  let u : EndpointTorusL2 T := v
  have hu := Lp.memLp u
  have hu0 := ((mem_endpointTorusSpace_iff_slices T u).mp v.property).1
  apply endpointProductOperator_coercive_of_ae_slice unitTorusMeasure hT K Ω hK hΩ bK bΩ u
  filter_upwards [hcoercive, ae_memLp_endpointTimeSlice hu, hu0,
    ae_memLp_endpointTimeSlice (memLp_endpointL2Mul K hK bK hu),
    ae_memLp_endpointTimeSlice (memLp_endpointL2Mul Ω hΩ bΩ hu)]
    with a hcoerc hua hu0a hKa hΩa
  exact (hcoerc (fun t => u (t, a)) hua hu0a).trans_eq
    (integral_endpointProductOperator_slice_eq hT hua hΩa hKa hu0a).symm

end TorusEuler
