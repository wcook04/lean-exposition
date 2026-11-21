import TorusEuler.EndpointMixedOperators
import TorusEuler.EndpointMixedProjection
import TorusEuler.EndpointWeakInstantaneous

/-! Strong and weak forms of the projected endpoint equation in Appendix A.2. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

local notation "A" => UnitAddTorus (Fin 3)
local notation "ν" => unitTorusMeasure
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "H" => Lp Vec3 2 ν
local notation "Vt(" T ")" => Lp Vec3 2 (μt T)
local notation "W(" T ")" => HalfHolder A (Vt(T))
local notation "Op(" T ")" => HalfHolder A (Vt(T) →L[ℝ] Vt(T))
local notation "C½" => HalfHolder A Vec3

/-- The mixed coefficient and its joint product multiplier agree when their
actions on time paths agree at almost every label. -/
theorem endpointMixedToJoint_mul_of_action {T : ℝ}
    (C : ℝ × A → Vec3 →L[ℝ] Vec3) (hC : AEStronglyMeasurable C (endpointTorusMeasure T))
    {M : ℝ} (bC : ∀ᵐ q ∂endpointTorusMeasure T, ‖C q‖ ≤ M) (Cmix : Op(T))
    (hCm : ∀ᵐ a ∂ν, ∀ f : Vt(T), (fun t => HalfHolder.eval a Cmix f t)
      =ᵐ[μt T] fun t => C (t, a) (f t)) (v : W(T)) :
    endpointMixedToJoint T (Cmix.coefficientMul v) =
      endpointL2Multiplier C hC bC (endpointMixedToJoint T v) := by
  have h := endpointMixedCoefficientMul_represents Cmix C hC bC hCm v
    (endpointMixedToJoint T v) (endpointMixedToJoint_apply_ae v)
  apply endpointJoint_eq_of_slices
  filter_upwards [endpointMixedToJoint_apply_ae (Cmix.coefficientMul v), h] with a ha hb
  exact ha.symm.trans hb

/-- In mixed coordinates the ambient coefficient of (A.9) is (K-JOmega). -/
noncomputable def endpointMixedProductOperator {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : Op(T)) : W(T) →L[ℝ] W(T) :=
  Kmix.coefficientMul - (endpointMixedIntegration hT).comp Ωmix.coefficientMul

theorem endpointMixedToJoint_productOperator {T : ℝ} (hT : 0 ≤ T)
    (K Ω : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hK : AEStronglyMeasurable K (endpointTorusMeasure T))
    (hΩ : AEStronglyMeasurable Ω (endpointTorusMeasure T))
    {CK CΩ : ℝ}
    (bK : ∀ᵐ q ∂endpointTorusMeasure T, ‖K q‖ ≤ CK)
    (bΩ : ∀ᵐ q ∂endpointTorusMeasure T, ‖Ω q‖ ≤ CΩ)
    (Kmix Ωmix : Op(T))
    (hKm : ∀ᵐ a ∂ν, ∀ f : Vt(T), (fun t => HalfHolder.eval a Kmix f t)
      =ᵐ[μt T] fun t => K (t, a) (f t))
    (hΩm : ∀ᵐ a ∂ν, ∀ f : Vt(T), (fun t => HalfHolder.eval a Ωmix f t)
      =ᵐ[μt T] fun t => Ω (t, a) (f t)) (v : W(T)) :
    endpointMixedToJoint T (endpointMixedProductOperator hT Kmix Ωmix v) =
      endpointProductOperator ν hT K Ω hK hΩ bK bΩ (endpointMixedToJoint T v) := by
  rw [endpointMixedProductOperator, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub, endpointMixedToJoint_integration,
    endpointMixedToJoint_mul_of_action K hK bK Kmix hKm,
    endpointMixedToJoint_mul_of_action Ω hΩ bΩ Ωmix hΩm]
  rfl

private theorem endpointMixedProjection_commutes {T : ℝ} (hT : 0 < T)
    (P : W(T) →L[ℝ] W(T))
    (hP : ∀ (w : W(T)) (k : Fin 3 → ℤ) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (P w) ∂ν) =
        angularTimeLeray T (realFourierFrequency k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂ν))
    (w : W(T)) :
    endpointMixedToJoint T (P w) = endpointJointConstraintProjection T (endpointMixedToJoint T w) :=
  endpointMixedToJoint_eq_projection_of_fourierCoeff hT w (P w) (hP w)

/-- A mixed projected solution is a joint weak solution when the strong
projection has the combined Fourier symbol and the ambient operators agree.
The residual has the sign (Bv+L), so the weak right side is (-L). -/
theorem endpointMixedProjectedSolve_to_product {T : ℝ} (hT : 0 < T)
    (P : W(T) →L[ℝ] W(T))
    (hP : ∀ (w : W(T)) (k : Fin 3 → ℤ) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (P w) ∂ν) =
        angularTimeLeray T (realFourierFrequency k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂ν))
    (Bmix : W(T) →L[ℝ] W(T)) (B : EndpointTorusL2 T →L[ℝ] EndpointTorusL2 T)
    (hB : ∀ f, endpointMixedToJoint T (Bmix f) = B (endpointMixedToJoint T f))
    (v L : W(T)) (hv : P v = v) (hr : P (Bmix v + L) = 0) :
    ∃ u : endpointTorusSpace T, (u : EndpointTorusL2 T) = endpointMixedToJoint T v ∧
      ∀ z : endpointTorusSpace T,
        ⟪B (u : EndpointTorusL2 T), (z : EndpointTorusL2 T)⟫_ℝ =
          ⟪-(endpointMixedToJoint T L), (z : EndpointTorusL2 T)⟫_ℝ := by
  let jv := endpointMixedToJoint T v
  let jL := endpointMixedToJoint T L
  have hvp := endpointMixedProjection_commutes hT P hP v
  rw [hv] at hvp
  have hjv : jv ∈ endpointTorusSpace T := by
    rw [← range_endpointJointConstraintProjection]
    exact ⟨jv, hvp.symm⟩
  have hres := endpointMixedProjection_commutes hT P hP (Bmix v + L)
  rw [hr, map_zero, map_add, hB] at hres
  refine ⟨⟨jv, hjv⟩, rfl, fun z => ?_⟩
  let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
  have hz : endpointJointConstraintProjection T (z : EndpointTorusL2 T) = z :=
    Submodule.starProjection_eq_self_iff.mpr z.property
  have horth : ⟪B jv + jL, (z : EndpointTorusL2 T)⟫_ℝ = 0 := by
    calc
      _ = ⟪B jv + jL, endpointJointConstraintProjection T (z : EndpointTorusL2 T)⟫_ℝ := by rw [hz]
      _ = ⟪endpointJointConstraintProjection T (B jv + jL), (z : EndpointTorusL2 T)⟫_ℝ :=
        ((endpointTorusSpace T).inner_starProjection_left_eq_right _ _).symm
      _ = _ := by rw [← hres, inner_zero_left]
  rw [inner_add_left] at horth
  change ⟪B jv, (z : EndpointTorusL2 T)⟫_ℝ = ⟪-jL, (z : EndpointTorusL2 T)⟫_ℝ
  rw [inner_neg_left]
  exact eq_neg_of_add_eq_zero_left horth

/-- The concrete mixed solve for the labelwise coefficient (K-JOmega)
supplies the weak joint equation with right side (-L). -/
theorem endpointMixedCoefficientSolve_to_product {T CK CΩ : ℝ} (hT : 0 < T)
    (K Ω : ℝ × A → Vec3 →L[ℝ] Vec3)
    (hK : AEStronglyMeasurable K (endpointTorusMeasure T))
    (hΩ : AEStronglyMeasurable Ω (endpointTorusMeasure T))
    (hKt : ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (μt T))
    (hΩt : ∀ a, AEStronglyMeasurable (fun t => Ω (t, a)) (μt T))
    (hCK : 0 ≤ CK) (hCΩ : 0 ≤ CΩ)
    (bK : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖K (t, a)‖ ≤ CK)
    (bΩ : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖Ω (t, a)‖ ≤ CΩ)
    (dK : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ CK * Real.sqrt (dist a b))
    (dΩ : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖Ω (t, a) - Ω (t, b)‖ ≤ CΩ * Real.sqrt (dist a b))
    (P : W(T) →L[ℝ] W(T))
    (hP : ∀ (w : W(T)) (k : Fin 3 → ℤ) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (P w) ∂ν) =
        angularTimeLeray T (realFourierFrequency k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a w ∂ν))
    (v L : W(T)) (hv : P v = v) :
    let Kmix := endpointMixedCoefficient K hKt bK dK hCK
    let Ωmix := endpointMixedCoefficient Ω hΩt bΩ dΩ hCΩ
    P (endpointMixedProductOperator hT.le Kmix Ωmix v + L) = 0 →
      ∃ u : endpointTorusSpace T, (u : EndpointTorusL2 T) = endpointMixedToJoint T v ∧
        ∀ z : endpointTorusSpace T,
          ⟪endpointProductOperator ν hT.le K Ω hK hΩ
              (endpointJointCoefficient_ae_bound K bK) (endpointJointCoefficient_ae_bound Ω bΩ)
              (u : EndpointTorusL2 T), (z : EndpointTorusL2 T)⟫_ℝ =
          ⟪-(endpointMixedToJoint T L), (z : EndpointTorusL2 T)⟫_ℝ := by
  intro Kmix Ωmix hr
  exact endpointMixedProjectedSolve_to_product hT P hP (endpointMixedProductOperator hT.le Kmix Ωmix)
    (endpointProductOperator ν hT.le K Ω hK hΩ
      (endpointJointCoefficient_ae_bound K bK) (endpointJointCoefficient_ae_bound Ω bΩ))
    (endpointMixedToJoint_productOperator hT.le K Ω hK hΩ
      (endpointJointCoefficient_ae_bound K bK) (endpointJointCoefficient_ae_bound Ω bΩ) Kmix Ωmix
      (ae_of_all _ (endpointMixedCoefficient_apply_ae K hKt bK dK hCK))
      (ae_of_all _ (endpointMixedCoefficient_apply_ae Ω hΩt bΩ dΩ hCΩ))) v L hv hr

/-- The time-averaged projected residual agrees with the embedding of its
spatial half-Hölder representative. -/
theorem endpointMixedResidual_projectedMean_compat {T : ℝ} (hT : 0 ≤ T)
    (P : C½ →L[ℝ] endpointHalfHolderSolenoidal)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    (r : W(T)) :
    endpointWeakSpatialProjection (T⁻¹ • endpointTorusTimeIntegral hT (endpointMixedToJoint T r)) =
      endpointSolenoidalEmbedding
        (P (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT, le_rfl⟩) r)) := by
  rw [← endpointMixedToJoint_terminal hT r, ← map_smul, hP]

/-- The projected mixed primitive agrees with the weak primitive in (A.9)
at almost every time in the slab. -/
theorem endpointMixedProjectedPrimitive_compat {T : ℝ} (hT : 0 ≤ T)
    (P : C½ →L[ℝ] endpointHalfHolderSolenoidal)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    (w : W(T)) :
    ∀ᵐ t ∂μt T, ∃ ht : t ∈ Icc (0 : ℝ) T,
      endpointWeakSpatialProjection
        (endpointSpatialSlice (endpointProductPrimitive ν hT (endpointMixedToJoint T w)) t) =
          endpointSolenoidalEmbedding (P (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) w)) := by
  filter_upwards [endpointMixedPrimitive_eq_spatialSlice hT w (endpointMixedToJoint T w)
    (endpointMixedToJoint_apply_ae w)] with t ht
  obtain ⟨ht, heq⟩ := ht
  refine ⟨ht, ?_⟩
  rw [← heq, hP]

end TorusEuler
