import TorusEuler.EndpointDensity
import TorusEuler.EndpointL2Multiplier
import TorusEuler.EndpointPrimitive
import TorusEuler.HalfHolderSpace
import TorusEuler.ProjectedHilbertInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Time recovery for the projected endpoint equation in Appendix A. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped InnerProductSpace Topology

namespace TorusEuler

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)

section PrimitiveEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem timeL2_norm_sq_eq_integral {T : ℝ} (hT : 0 ≤ T)
    (v : Lp E 2 (timeMeasure T)) : ‖v‖ ^ 2 = ∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2 := by
  rw [Lp.norm_def, (Lp.memLp v).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  rw [intervalIntegral.integral_of_le hT]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

private theorem norm_endpointPrimitive_increment_le {T : ℝ} (v : Lp E 2 (timeMeasure T))
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    ‖endpointPrimitive v t - endpointPrimitive v s‖ ≤ Real.sqrt (t - s) * ‖v‖ := by
  have h := norm_sq_endpointPrimitive_increment_le (Lp.memLp v) hs ht hst
  rw [← timeL2_norm_sq_eq_integral (hs.1.trans hs.2) v] at h
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rwa [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hst)]

/-- Integrating from time zero to a fixed time defines a continuous linear evaluation
of an `L²` path. -/
noncomputable def endpointPrimitiveEvaluation {T : ℝ} (t : Icc (0 : ℝ) T) :
    Lp E 2 (timeMeasure T) →L[ℝ] E := by
  let J : Lp E 2 (timeMeasure T) →ₗ[ℝ] E :=
    { toFun := fun v => endpointPrimitive v t
      map_add' := fun v w => by
        have hv := (Lp.memLp v).mono_measure (Measure.restrict_mono
          (Ioc_subset_Ioc_right t.property.2) le_rfl)
        have hw := (Lp.memLp w).mono_measure (Measure.restrict_mono
          (Ioc_subset_Ioc_right t.property.2) le_rfl)
        exact (endpointPrimitive_congr_ae (Lp.coeFn_add v w) t.property).trans
          (intervalIntegral.integral_add (intervalIntegrable_velocity_of_memLp t.property.1 hv)
            (intervalIntegrable_velocity_of_memLp t.property.1 hw))
      map_smul' := fun c v =>
        (endpointPrimitive_congr_ae (Lp.coeFn_smul c v) t.property).trans
          (intervalIntegral.integral_smul c (⇑v)) }
  exact J.mkContinuous (Real.sqrt (t : ℝ)) fun v => by
    simpa only [J, LinearMap.coe_mk, AddHom.coe_mk, endpointPrimitive_zero, sub_zero] using
      norm_endpointPrimitive_increment_le v ⟨le_rfl, t.property.1.trans t.property.2⟩
        t.property t.property.1

@[simp] theorem endpointPrimitiveEvaluation_apply {T : ℝ} (t : Icc (0 : ℝ) T)
    (v : Lp E 2 (timeMeasure T)) : endpointPrimitiveEvaluation t v = endpointPrimitive v t := rfl

theorem norm_endpointPrimitiveEvaluation_le {T : ℝ} (t : Icc (0 : ℝ) T) :
    ‖endpointPrimitiveEvaluation (E := E) t‖ ≤ Real.sqrt (t : ℝ) := by
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  simpa only [endpointPrimitiveEvaluation_apply, endpointPrimitive_zero, sub_zero] using
    norm_endpointPrimitive_increment_le v ⟨le_rfl, t.property.1.trans t.property.2⟩
      t.property t.property.1

/-- Cauchy–Schwarz gives a half-power time modulus in operator norm for primitive evaluation. -/
theorem norm_endpointPrimitiveEvaluation_sub_le {T : ℝ} (s t : Icc (0 : ℝ) T) :
    ‖endpointPrimitiveEvaluation (E := E) t - endpointPrimitiveEvaluation s‖ ≤
      Real.sqrt |(t : ℝ) - s| := by
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  rw [sub_apply, endpointPrimitiveEvaluation_apply, endpointPrimitiveEvaluation_apply]
  rcases le_total (s : ℝ) t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact norm_endpointPrimitive_increment_le v s.property t.property h
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact norm_endpointPrimitive_increment_le v t.property s.property h

theorem continuous_endpointPrimitiveEvaluation (T : ℝ) :
    Continuous (endpointPrimitiveEvaluation (E := E) (T := T)) := by
  refine continuous_iff_continuousAt.mpr fun s => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_endpointPrimitiveEvaluation_sub_le s t) ?_
  have h : Continuous (fun t : Icc (0 : ℝ) T => Real.sqrt |(t : ℝ) - s|) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.sub continuous_const).abs
  simpa only [sub_self, abs_zero, Real.sqrt_zero] using h.continuousAt (x := s).tendsto

/-- For a fixed label, evaluating the primitive of the multiplier `Ωv` gives
the ordinary integral of the coefficient applied to the time-dependent velocity. -/
theorem endpointPrimitiveEvaluation_l2Multiplier_apply {T : ℝ} (t : Icc (0 : ℝ) T)
    (Ω : ℝ → E →L[ℝ] E) (hΩ : AEStronglyMeasurable Ω (timeMeasure T)) {C : ℝ}
    (hC : ∀ᵐ r ∂timeMeasure T, ‖Ω r‖ ≤ C) (v : Lp E 2 (timeMeasure T)) :
    endpointPrimitiveEvaluation t (endpointL2Multiplier Ω hΩ hC v) =
      ∫ r in (0 : ℝ)..t, Ω r (v r) :=
  endpointPrimitive_congr_ae (endpointL2Multiplier_apply_ae Ω hΩ hC v) t.property

/-- Applying primitive evaluation to a field of time paths preserves spatial difference
bounds, with the half-power time gain. The same formula applies after dividing by a
spatial Hölder weight. -/
theorem norm_endpointMixedPrimitive_spatial_increment_le {A : Type*} {T : ℝ}
    (w : A → Lp E 2 (timeMeasure T)) (s t : Icc (0 : ℝ) T) (a b : A) :
    ‖(endpointPrimitiveEvaluation t (w a) - endpointPrimitiveEvaluation s (w a)) -
      (endpointPrimitiveEvaluation t (w b) - endpointPrimitiveEvaluation s (w b))‖ ≤
      Real.sqrt |(t : ℝ) - s| * ‖w a - w b‖ := by
  let D := endpointPrimitiveEvaluation (E := E) t - endpointPrimitiveEvaluation s
  calc
    _ = ‖D (w a - w b)‖ := by rw [map_sub]; rfl
    _ ≤ _ := (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (norm_endpointPrimitiveEvaluation_sub_le s t) (norm_nonneg _))

variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Postcomposition by primitive evaluation turns a mixed-space path into a continuous
time path in the spatial Banach space. `post` is the bounded postcomposition map. -/
theorem continuous_endpointMixedPrimitive {T : ℝ}
    (post : (Lp E 2 (timeMeasure T) →L[ℝ] E) →L[ℝ] (X →L[ℝ] B)) (w : X) :
    Continuous (fun t : Icc (0 : ℝ) T => post (endpointPrimitiveEvaluation t) w) :=
  (post.continuous.comp (continuous_endpointPrimitiveEvaluation T)).clm_apply continuous_const

/-- The time increment bound in the spatial norm, applied in Appendix A to `Ωv`. -/
theorem norm_endpointMixedPrimitive_sub_le {T : ℝ}
    (post : (Lp E 2 (timeMeasure T) →L[ℝ] E) →L[ℝ] (X →L[ℝ] B)) (w : X)
    (s t : Icc (0 : ℝ) T) :
    ‖post (endpointPrimitiveEvaluation t) w - post (endpointPrimitiveEvaluation s) w‖ ≤
      ‖post‖ * Real.sqrt |(t : ℝ) - s| * ‖w‖ := by
  rw [← sub_apply, ← map_sub]
  exact ((post (endpointPrimitiveEvaluation t - endpointPrimitiveEvaluation s)).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right
      ((post.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_endpointPrimitiveEvaluation_sub_le s t) (norm_nonneg _))) (norm_nonneg _))

/-- A real-parameter representative of the mixed-space primitive is continuous on the
closed time interval, with the uniform bound used in the instantaneous equation. -/
theorem endpointMixedPrimitive_continuousOn_and_bound {T : ℝ}
    (post : (Lp E 2 (timeMeasure T) →L[ℝ] E) →L[ℝ] (X →L[ℝ] B)) (w : X)
    {JΩ : ℝ → B} (hJΩ : ∀ t : Icc (0 : ℝ) T, JΩ t = post (endpointPrimitiveEvaluation t) w) :
    ContinuousOn JΩ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, ‖JΩ t‖ ≤ ‖post‖ * Real.sqrt T * ‖w‖ := by
  constructor
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_endpointMixedPrimitive post w).congr (fun t => (hJΩ t).symm)
  · intro t ht
    rw [hJΩ ⟨t, ht⟩]
    exact ((post (endpointPrimitiveEvaluation ⟨t, ht⟩)).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right ((post.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((norm_endpointPrimitiveEvaluation_le ⟨t, ht⟩).trans
          (Real.sqrt_le_sqrt ht.2)) (norm_nonneg _))) (norm_nonneg _))

/-- The primitive of a spatial half-Hölder field of time paths is continuous
in the spatial norm, with the half-power time modulus used in (A.9). -/
theorem continuous_and_norm_sub_le_endpointHalfHolderPrimitive {A : Type*} [MetricSpace A]
    {T : ℝ} (w : HalfHolder A (Lp E 2 (timeMeasure T))) :
    let Jw (t : Icc (0 : ℝ) T) : HalfHolder A E :=
      HalfHolder.map (endpointPrimitiveEvaluation t) w
    Continuous Jw ∧ ∀ s t : Icc (0 : ℝ) T,
      ‖Jw t - Jw s‖ ≤ Real.sqrt |(t : ℝ) - s| * ‖w‖ := by
  let post : (Lp E 2 (timeMeasure T) →L[ℝ] E) →L[ℝ]
      (HalfHolder A (Lp E 2 (timeMeasure T)) →L[ℝ] HalfHolder A E) := HalfHolder.postcomp
  refine ⟨continuous_endpointMixedPrimitive post w, fun s t => ?_⟩
  let D : Lp E 2 (timeMeasure T) →L[ℝ] E :=
    endpointPrimitiveEvaluation t - endpointPrimitiveEvaluation s
  have hD : HalfHolder.map D w = HalfHolder.map (endpointPrimitiveEvaluation t) w -
      HalfHolder.map (endpointPrimitiveEvaluation s) w := by
    apply HalfHolder.ext
    intro a
    rw [map_sub, HalfHolder.eval_map, HalfHolder.eval_map, HalfHolder.eval_map]
    rfl
  change ‖HalfHolder.map (endpointPrimitiveEvaluation t) w -
    HalfHolder.map (endpointPrimitiveEvaluation s) w‖ ≤ _
  rw [← hD]
  exact ((HalfHolder.map D).le_opNorm w).trans (mul_le_mul_of_nonneg_right
    ((HalfHolder.norm_map_le (X := A) D).trans (norm_endpointPrimitiveEvaluation_sub_le s t))
    (norm_nonneg _))

end PrimitiveEvaluation

section InstantRecovery

variable {X B Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Subtracting the time mean removes exactly the constant component of the projected
weak equation. -/
theorem endpointProjectedWeak_eq_mean {T : ℝ} {w : Lp Y 2 (timeMeasure T)}
    (h : endpointSubtractMean T w = 0) :
    ∀ᵐ t ∂timeMeasure T, w t = T⁻¹ • endpointIntegral T w := by
  rw [endpointSubtractMean_apply, sub_eq_zero] at h
  filter_upwards [Lp.coeFn_const 2 (timeMeasure T) (T⁻¹ • endpointIntegral T w)] with t ht
  exact (congrArg (fun v : Lp Y 2 (timeMeasure T) => v t) h).trans ht

/-- The weak fixed-time equation `cc:holder:eq:instant` uses the sign of the time
primitive in `Bv = Kv - J(Ωv)`. The maps `K` and `P` act on the weak spatial space. -/
theorem endpointWeakInstant_of_subtractMean_eq_zero {T : ℝ}
    {w : Lp Y 2 (timeMeasure T)} {K : ℝ → B →L[ℝ] B} {P : B →L[ℝ] Y}
    {v JΩ L : ℝ → B} (h : endpointSubtractMean T w = 0)
    (hw : ∀ᵐ t ∂timeMeasure T, w t = P (K t (v t) - JΩ t + L t)) :
    ∀ᵐ t ∂timeMeasure T,
      P (K t (v t)) = T⁻¹ • endpointIntegral T w + P (JΩ t) - P (L t) := by
  filter_upwards [endpointProjectedWeak_eq_mean h, hw] with t hc hwt
  rw [hwt, map_add, map_sub] at hc
  rw [← hc]
  abel

/-- Continuity of the fixed-time inverse in operator norm, for a continuous family of
isomorphisms of the spatial Banach space. -/
theorem continuousOn_endpointFixedInverse [CompleteSpace X] {I : Set ℝ}
    {S : ℝ → X ≃L[ℝ] X}
    (hS : ContinuousOn (fun t => (S t : X →L[ℝ] X)) I) :
    ContinuousOn (fun t => ((S t).symm : X →L[ℝ] X)) I := by
  have h (t : ℝ) : Ring.inverse ((S t : X →L[ℝ] X)) = ((S t).symm : X →L[ℝ] X) :=
    Ring.inverse_unit (S t).toUnit
  intro t ht
  have hi : ContinuousAt (Ring.inverse : (X →L[ℝ] X) → (X →L[ℝ] X)) (S t : X →L[ℝ] X) :=
    NormedRing.inverse_continuousAt (S t).toUnit
  have hcont := hi.comp_continuousWithinAt (f := fun r => (S r : X →L[ℝ] X)) (hS t ht)
  exact hcont.congr (fun r _ => (h r).symm) (h t).symm

/-- The fixed-time projected Hilbert operator is injective by spatial ellipticity. -/
theorem endpointProjectedHilbertOperator_injective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (K : H →L[ℝ] H) {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ v : V, κ * ‖v‖ ^ 2 ≤ ⟪K (v : H), (v : H)⟫_ℝ) :
    Function.Injective (projectedHilbertOperator V hV K) := by
  intro x y hxy
  apply (projectedHilbertEquiv V hV K hκ hK).injective
  simpa only [projectedHilbertEquiv_apply] using hxy

/-- Apply the fixed-time inverse to the continuous right side. Its value agrees
almost everywhere with the incoming weak solution by weak elliptic injectivity. -/
theorem exists_endpointContinuousRepresentative {T : ℝ} {S : ℝ → X ≃L[ℝ] X}
    {Sweak : ℝ → Y →L[ℝ] Y} (emb : X →L[ℝ] Y) (P : B →L[ℝ] X)
    (c : X) {JΩ L : ℝ → B} {w : ℝ → Y} {M CJ CL : ℝ}
    (hInv : ContinuousOn (fun t => ((S t).symm : X →L[ℝ] X)) (Icc 0 T))
    (hJ : ContinuousOn JΩ (Icc 0 T)) (hL : ContinuousOn L (Icc 0 T))
    (hM : 0 ≤ M) (hBound : ∀ t ∈ Icc 0 T, ‖((S t).symm : X →L[ℝ] X)‖ ≤ M)
    (hJBound : ∀ t ∈ Icc 0 T, ‖JΩ t‖ ≤ CJ) (hLBound : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ CL)
    (hCompat : ∀ t ∈ Icc 0 T, ∀ v, Sweak t (emb v) = emb (S t v))
    (hWeakInjective : ∀ t ∈ Icc 0 T, Function.Injective (Sweak t))
    (hWeak : ∀ᵐ t ∂timeMeasure T, Sweak t (w t) = emb (c + P (JΩ t) - P (L t))) :
    ∃ v : ℝ → X, ContinuousOn v (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, S t (v t) = c + P (JΩ t) - P (L t)) ∧
      ((fun t => emb (v t)) =ᵐ[timeMeasure T] w) ∧
      ∀ t ∈ Icc 0 T, ‖v t‖ ≤ M * (‖c‖ + ‖P‖ * (CJ + CL)) := by
  let g (t : ℝ) := c + P (JΩ t) - P (L t)
  let v (t : ℝ) := (S t).symm (g t)
  have hg : ContinuousOn g (Icc 0 T) :=
    (continuousOn_const.add (P.continuous.comp_continuousOn hJ)).sub
      (P.continuous.comp_continuousOn hL)
  have hv : ∀ t, S t (v t) = g t := fun t => (S t).apply_symm_apply (g t)
  refine ⟨v, hInv.clm_apply hg, fun t _ => hv t, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc, hWeak] with t ht hw
    have htc := Ioc_subset_Icc_self ht
    exact hWeakInjective t htc ((hCompat t htc (v t)).trans ((congrArg emb (hv t)).trans hw.symm))
  · intro t ht
    have hgBound : ‖g t‖ ≤ ‖c‖ + ‖P‖ * (CJ + CL) := by
      calc
        ‖g t‖ ≤ (‖c‖ + ‖P (JΩ t)‖) + ‖P (L t)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (‖c‖ + ‖P‖ * CJ) + ‖P‖ * CL :=
          add_le_add (add_le_add le_rfl ((P.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hJBound t ht) (norm_nonneg _))))
            ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hLBound t ht) (norm_nonneg _)))
        _ = _ := by rw [mul_add, add_assoc]
    exact (((S t).symm : X →L[ℝ] X).le_opNorm (g t)).trans
      ((mul_le_mul_of_nonneg_right (hBound t ht) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hgBound hM))

/-- Taking the time primitive of the recovered velocity preserves the zero endpoint
condition and gives the recovered velocity as its derivative at every time. -/
theorem endpointRecoveredPrimitive_hasDerivWithinAt_and_zero_endpoints [CompleteSpace X]
    [CompleteSpace Y] {T : ℝ} (hT : 0 ≤ T) {v : ℝ → X} {w : ℝ → Y}
    (emb : X →L[ℝ] Y) (hEmb : Function.Injective emb) (hv : ContinuousOn v (Icc 0 T))
    (hRep : (fun t => emb (v t)) =ᵐ[timeMeasure T] w)
    (hMean : (∫ t in (0 : ℝ)..T, w t) = 0) :
    endpointPrimitive v 0 = 0 ∧ endpointPrimitive v T = 0 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive v) (v t) (Icc 0 T) t := by
  have hvInt := hv.intervalIntegrable_of_Icc (μ := volume) hT
  have hMean' : endpointPrimitive (fun t => emb (v t)) T = endpointPrimitive w T :=
    endpointPrimitive_congr_ae hRep ⟨hT, le_rfl⟩
  have hComm := emb.intervalIntegral_comp_comm hvInt
  have hZero : endpointPrimitive v T = 0 := by
    apply hEmb
    rw [map_zero]
    exact hComm.symm.trans (hMean'.trans hMean)
  refine ⟨endpointPrimitive_zero v, hZero, fun t ht => ?_⟩
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hInt : IntervalIntegrable v volume 0 t :=
    (hv.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  exact intervalIntegral.integral_hasDerivWithinAt_right hInt
    (hv.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hv t ht)

end InstantRecovery

end TorusEuler
