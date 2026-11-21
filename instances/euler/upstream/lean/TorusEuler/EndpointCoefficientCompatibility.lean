import TorusEuler.EndpointRecoverTime
import TorusEuler.EndpointSpaceCompatibility
import TorusEuler.EndpointSpaceOperator

/-! Multiplication and time integration compatibility in Appendix A.2. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

section Pointwise

variable {X E F : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem halfHolder_eval_bounds {K : HalfHolder X E} :
    (∀ x, ‖HalfHolder.eval x K‖ ≤ ‖K‖) ∧
      ∀ x y, ‖HalfHolder.eval x K - HalfHolder.eval y K‖ ≤ ‖K‖ * Real.sqrt (dist x y) :=
  (HalfHolder.norm_le_iff (norm_nonneg K)).mp le_rfl

private theorem halfHolder_coefficient_value_bound
    (K : HalfHolder X (E →L[ℝ] F)) (v : HalfHolder X E) (x : X) :
    ‖HalfHolder.eval x K (HalfHolder.eval x v)‖ ≤ 2 * ‖K‖ * ‖v‖ := by
  calc
    ‖HalfHolder.eval x K (HalfHolder.eval x v)‖ ≤ ‖HalfHolder.eval x K‖ * ‖HalfHolder.eval x v‖ :=
      (HalfHolder.eval x K).le_opNorm _
    _ ≤ ‖K‖ * ‖v‖ := mul_le_mul ((halfHolder_eval_bounds (K := K)).1 x)
      ((halfHolder_eval_bounds (K := v)).1 x) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg K) (norm_nonneg v)]

private theorem halfHolder_coefficient_increment_bound
    (K : HalfHolder X (E →L[ℝ] F)) (v : HalfHolder X E) (x y : X) :
    ‖HalfHolder.eval x K (HalfHolder.eval x v) -
      HalfHolder.eval y K (HalfHolder.eval y v)‖ ≤
      (2 * ‖K‖ * ‖v‖) * Real.sqrt (dist x y) := by
  let A := HalfHolder.eval x K
  let B := HalfHolder.eval y K
  let u := HalfHolder.eval x v
  let w := HalfHolder.eval y v
  let d := Real.sqrt (dist x y)
  have hA : ‖A‖ ≤ ‖K‖ := halfHolder_eval_bounds.1 x
  have hab : ‖A - B‖ ≤ ‖K‖ * d := halfHolder_eval_bounds.2 x y
  have hw : ‖w‖ ≤ ‖v‖ := halfHolder_eval_bounds.1 y
  have huv : ‖u - w‖ ≤ ‖v‖ * d := halfHolder_eval_bounds.2 x y
  change ‖A u - B w‖ ≤ (2 * ‖K‖ * ‖v‖) * d
  calc
    ‖A u - B w‖ = ‖A (u - w) + (A - B) w‖ := by
      rw [map_sub, _root_.sub_apply]
      abel_nf
    _ ≤ ‖A (u - w)‖ + ‖(A - B) w‖ := norm_add_le _ _
    _ ≤ ‖K‖ * (‖v‖ * d) + (‖K‖ * d) * ‖v‖ := by
      exact add_le_add ((A.le_opNorm _).trans (mul_le_mul hA huv (norm_nonneg _) (norm_nonneg _)))
        (((A - B).le_opNorm _).trans (mul_le_mul hab hw (norm_nonneg _) (by positivity)))
    _ = _ := by ring

private noncomputable def halfHolder_coefficientApply
    (K : HalfHolder X (E →L[ℝ] F)) (v : HalfHolder X E) : HalfHolder X F :=
  HalfHolder.ofBound
    ⟨fun x => HalfHolder.eval x K (HalfHolder.eval x v), K.val.1.continuous.clm_apply v.val.1.continuous⟩
    (halfHolder_coefficient_value_bound K v) (halfHolder_coefficient_increment_bound K v)

@[simp] private theorem halfHolder_eval_coefficientApply
    (K : HalfHolder X (E →L[ℝ] F)) (v : HalfHolder X E) (x : X) :
    HalfHolder.eval x (halfHolder_coefficientApply K v) =
      HalfHolder.eval x K (HalfHolder.eval x v) := rfl

/-- A half-Hölder field of bounded linear maps acts boundedly on half-Hölder fields. -/
noncomputable def HalfHolder.coefficientMul (K : HalfHolder X (E →L[ℝ] F)) :
    HalfHolder X E →L[ℝ] HalfHolder X F := by
  let L : HalfHolder X E →ₗ[ℝ] HalfHolder X F :=
    { toFun := halfHolder_coefficientApply K
      map_add' := fun u v => HalfHolder.ext fun x => by simp only [map_add, halfHolder_eval_coefficientApply]
      map_smul' := fun c v => HalfHolder.ext fun x => by
        simp only [map_smul, RingHom.id_apply, halfHolder_eval_coefficientApply] }
  have hb (v : HalfHolder X E) : ‖L v‖ ≤ 2 * ‖K‖ * ‖v‖ := by
    apply (HalfHolder.norm_le_iff (by positivity)).mpr
    change (∀ x, ‖HalfHolder.eval x (L v)‖ ≤ _) ∧
      ∀ x y, ‖HalfHolder.eval x (L v) - HalfHolder.eval y (L v)‖ ≤ _
    exact ⟨halfHolder_coefficient_value_bound K v, halfHolder_coefficient_increment_bound K v⟩
  exact L.mkContinuous (2 * ‖K‖) hb

@[simp] theorem HalfHolder.eval_coefficientMul (K : HalfHolder X (E →L[ℝ] F)) (v : HalfHolder X E)
    (x : X) : HalfHolder.eval x (K.coefficientMul v) = HalfHolder.eval x K (HalfHolder.eval x v) :=
  rfl

theorem HalfHolder.norm_coefficientMul_le (K : HalfHolder X (E →L[ℝ] F)) :
    ‖K.coefficientMul‖ ≤ 2 * ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (HalfHolder.norm_le_iff (by positivity)).mpr
  change (∀ x, ‖HalfHolder.eval x (K.coefficientMul v)‖ ≤ _) ∧
    ∀ x y, ‖HalfHolder.eval x (K.coefficientMul v) - HalfHolder.eval y (K.coefficientMul v)‖ ≤ _
  simpa only [HalfHolder.eval_coefficientMul] using
    And.intro (halfHolder_coefficient_value_bound K v) (halfHolder_coefficient_increment_bound K v)

theorem HalfHolder.coefficientMul_sub (K L : HalfHolder X (E →L[ℝ] F)) :
    (K - L).coefficientMul = K.coefficientMul - L.coefficientMul := by
  apply ContinuousLinearMap.ext
  intro v
  apply HalfHolder.ext
  intro x
  simp only [_root_.sub_apply, map_sub, HalfHolder.eval_coefficientMul]

theorem HalfHolder.lipschitzWith_coefficientMul :
    LipschitzWith 2 (fun K : HalfHolder X (E →L[ℝ] F) => K.coefficientMul) := by
  refine LipschitzWith.of_dist_le_mul fun K L => ?_
  rw [dist_eq_norm, dist_eq_norm, ← HalfHolder.coefficientMul_sub]
  exact HalfHolder.norm_coefficientMul_le (K - L)

end Pointwise

local notation "A" => UnitAddTorus (Fin 3)
local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "timeVolume" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Vtime(" T ")" => Lp Vec3 2 (timeVolume T)

private theorem endpointHalfHolderCoefficient_aestronglyMeasurable (K : K½) :
    AEStronglyMeasurable (fun a => HalfHolder.eval a K) unitTorusMeasure :=
  K.val.1.continuous.aestronglyMeasurable

private theorem endpointHalfHolderCoefficient_ae_bound (K : K½) :
    ∀ᵐ a ∂unitTorusMeasure, ‖HalfHolder.eval a K‖ ≤ ‖K‖ :=
  ae_of_all _ (halfHolder_eval_bounds (K := K)).1

/-- The ambient weak coefficient operator associated to a spatial half-Hölder
operator field. -/
noncomputable def endpointWeakCoefficient (K : K½) : H →L[ℝ] H :=
  endpointL2Multiplier (fun a => HalfHolder.eval a K)
    (endpointHalfHolderCoefficient_aestronglyMeasurable K)
    (endpointHalfHolderCoefficient_ae_bound K)

theorem endpointWeakCoefficient_apply_ae (K : K½) (v : H) :
    (fun a => endpointWeakCoefficient K v a) =ᵐ[unitTorusMeasure]
      fun a => HalfHolder.eval a K (v a) :=
  endpointL2Multiplier_apply_ae _ (endpointHalfHolderCoefficient_aestronglyMeasurable K)
    (endpointHalfHolderCoefficient_ae_bound K) v

/-- Pointwise ellipticity of the kinetic coefficient implies ellipticity
of its weak multiplication operator with the same constant. -/
theorem endpointWeakCoefficient_coercive (K : K½) {κ : ℝ}
    (hK : ∀ a (z : Vec3), κ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a K z, z⟫_ℝ) (v : H) :
    κ * ‖v‖ ^ 2 ≤ ⟪endpointWeakCoefficient K v, v⟫_ℝ := by
  have hh := L2.integrable_inner (𝕜 := ℝ) v v
  have hw := L2.integrable_inner (𝕜 := ℝ) (endpointWeakCoefficient K v) v
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae (hh.const_mul κ) hw
  filter_upwards [endpointWeakCoefficient_apply_ae K v] with a ha
  rw [ha, real_inner_self_eq_norm_sq]
  exact hK a (v a)

/-- The projected weak fixed-time equation is invertible under the pointwise
ellipticity hypothesis on the kinetic coefficient. -/
noncomputable def endpointWeakCoefficientEquiv (K : K½) {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ a (z : Vec3), κ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a K z, z⟫_ℝ) :
    endpointSpatialSolenoidal ≃L[ℝ] endpointSpatialSolenoidal :=
  projectedHilbertEquiv endpointSpatialSolenoidal isClosed_endpointSpatialSolenoidal
    (endpointWeakCoefficient K) hκ
    fun v => endpointWeakCoefficient_coercive K hK (v : H)

theorem endpointWeakCoefficientEquiv_apply (K : K½) {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ a (z : Vec3), κ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a K z, z⟫_ℝ)
    (v : endpointSpatialSolenoidal) :
    endpointWeakCoefficientEquiv K hκ hK v =
      projectedHilbertOperator endpointSpatialSolenoidal isClosed_endpointSpatialSolenoidal
        (endpointWeakCoefficient K) v :=
  projectedHilbertEquiv_apply _ _ _ _ _ _

/-- Pointwise multiplication commutes with the embedding into spatial Haar L². -/
theorem endpointHalfHolderToL2_coefficientMul (K : K½) (v : C½) :
    endpointHalfHolderToL2 (K.coefficientMul v) =
      endpointWeakCoefficient K (endpointHalfHolderToL2 v) := by
  apply Lp.ext
  filter_upwards [endpointHalfHolderToL2_apply_ae (K.coefficientMul v),
    endpointHalfHolderToL2_apply_ae v, endpointWeakCoefficient_apply_ae K (endpointHalfHolderToL2 v)]
    with a hmul hv hweak
  rw [hmul, hweak, hv, HalfHolder.eval_coefficientMul]

/-- If the spatial projection agrees on strong fields, so do the resulting
projected fixed-time coefficient equations. -/
theorem endpointCompressedCoefficient_compat
    (K : K½) (P : C½ →L[ℝ] endpointHalfHolderSolenoidal)
    (Pweak : H →L[ℝ] endpointSpatialSolenoidal)
    (hP : ∀ v, Pweak (endpointHalfHolderToL2 v) = endpointSolenoidalEmbedding (P v))
    (v : endpointHalfHolderSolenoidal) :
    Pweak (endpointWeakCoefficient K ((endpointSolenoidalEmbedding v : endpointSpatialSolenoidal) : H)) =
      endpointSolenoidalEmbedding (P (K.coefficientMul (v : C½))) := by
  change Pweak (endpointWeakCoefficient K (endpointHalfHolderToL2 (v : C½))) = _
  rw [← endpointHalfHolderToL2_coefficientMul]
  exact hP _

/-- When a mixed field represents the time paths of a joint field, their
primitives agree as spatial representatives at each time on the closed slab. -/
theorem endpointMixedPrimitive_apply_ae {T : ℝ}
    (w : HalfHolder A (Vtime(T))) (v : EndpointTorusL2 T)
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun s => HalfHolder.eval a w s) =ᵐ[timeVolume T] fun s => v (s, a))
    (t : Icc (0 : ℝ) T) :
    (endpointHalfHolderToL2 (HalfHolder.map (endpointPrimitiveEvaluation t) w) : A → Vec3)
      =ᵐ[unitTorusMeasure] fun a => endpointPrimitive (fun s => v (s, a)) t := by
  filter_upwards [endpointHalfHolderToL2_apply_ae
    (HalfHolder.map (endpointPrimitiveEvaluation t) w), hw] with a ha hwa
  rw [ha, HalfHolder.eval_map, endpointPrimitiveEvaluation_apply]
  exact endpointPrimitive_congr_ae hwa t.property

/-- The terminal value of the strong primitive is the time integral of the
joint field in the weak spatial space. -/
theorem endpointMixedPrimitive_terminal_eq_timeIntegral {T : ℝ} (hT : 0 ≤ T)
    (w : HalfHolder A (Vtime(T))) (v : EndpointTorusL2 T)
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun s => HalfHolder.eval a w s) =ᵐ[timeVolume T] fun s => v (s, a)) :
    endpointHalfHolderToL2
      (HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT, le_rfl⟩) w) =
        endpointTorusTimeIntegral hT v := by
  apply Lp.ext
  exact (endpointMixedPrimitive_apply_ae w v hw ⟨T, hT, le_rfl⟩).trans
    (endpointTorusTimeIntegral_apply_ae hT v).symm

/-- On almost every time slice the joint L² primitive agrees with the primitive
of the corresponding mixed half-Hölder field. -/
theorem endpointMixedPrimitive_eq_spatialSlice {T : ℝ} (hT : 0 ≤ T)
    (w : HalfHolder A (Vtime(T))) (v : EndpointTorusL2 T)
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun s => HalfHolder.eval a w s) =ᵐ[timeVolume T] fun s => v (s, a)) :
    ∀ᵐ t ∂timeVolume T, ∃ ht : t ∈ Icc (0 : ℝ) T,
      endpointHalfHolderToL2 (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) w) =
      endpointSpatialSlice (endpointProductPrimitive unitTorusMeasure hT v) t := by
  let Jv : EndpointTorusL2 T := endpointProductPrimitive unitTorusMeasure hT v
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc,
    endpointSpatialSlice_apply_ae Jv, Measure.ae_ae_of_ae_prod
      (endpointProductPrimitive_apply_ae unitTorusMeasure hT v)] with t ht hs hj
  have hja : (fun a => Jv (t, a)) =ᵐ[unitTorusMeasure]
      fun a => endpointPrimitive (fun s => v (s, a)) t := hj
  refine ⟨Ioc_subset_Icc_self ht, Lp.ext ?_⟩
  exact (endpointMixedPrimitive_apply_ae w v hw ⟨t, Ioc_subset_Icc_self ht⟩).trans
    (hja.symm.trans hs.symm)

/-! The pointwise identification for mixed multiplication is independent of
the construction and regularity of the label-to-operator map. -/

/-- A mixed coefficient calculus agrees with joint multiplication whenever
its action on each time path agrees almost everywhere with the joint coefficient. -/
theorem endpointMixedCoefficientMul_represents {T : ℝ}
    (Ω : HalfHolder A (Vtime(T) →L[ℝ] Vtime(T)))
    (ω : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hω : AEStronglyMeasurable ω (endpointTorusMeasure T)) {Cω : ℝ}
    (bω : ∀ᵐ q ∂endpointTorusMeasure T, ‖ω q‖ ≤ Cω)
    (hΩ : ∀ᵐ a ∂unitTorusMeasure, ∀ f : Vtime(T),
      (fun t => HalfHolder.eval a Ω f t) =ᵐ[timeVolume T] fun t => ω (t, a) (f t))
    (w : HalfHolder A (Vtime(T))) (v : EndpointTorusL2 T)
    (hw : ∀ᵐ a ∂unitTorusMeasure,
      (fun s => HalfHolder.eval a w s) =ᵐ[timeVolume T] fun s => v (s, a)) :
    ∀ᵐ a ∂unitTorusMeasure,
      (fun t => HalfHolder.eval a (Ω.coefficientMul w) t) =ᵐ[timeVolume T]
        fun t => endpointL2Multiplier ω hω bω v (t, a) := by
  have hjoint := ae_endpointTimeSlice_congr (endpointL2Multiplier_apply_ae ω hω bω v)
  filter_upwards [hΩ, hw, hjoint] with a ha hwa hja
  filter_upwards [ha (HalfHolder.eval a w), hwa, hja] with t ht hwt hjt
  rw [HalfHolder.eval_coefficientMul, ht, hwt, hjt]

end TorusEuler
