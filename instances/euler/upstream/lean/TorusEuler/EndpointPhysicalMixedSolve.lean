import TorusEuler.EndpointConcreteInverses
import TorusEuler.EndpointMixedConcreteOperator
import TorusEuler.EndpointMixedProjectionUniform

/-! The physical mixed half-Hölder solve in Appendix A before instantaneous recovery. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "Mixed(" T ")" => HalfHolder A (Path(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(T) →L[ℝ] Path(T))
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "Slab(" T ")" => (Set.prod (Icc (0 : ℝ) T) (univ : Set A))

/-- The exact projected mixed equation for the kinetic and vorticity coefficients
gives the physical weak equation on the embedded constrained space. -/
theorem endpointPhysicalMixedSolution_weak {T : ℝ} (hT : 0 < T)
    (F M : ℝ × A → Coefficient) (cF : ContinuousOn F Slab(T)) (cM : ContinuousOn M Slab(T))
    (Kmix Ωmix : MixedCoefficient(T))
    (hK : ∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Kmix w t) =ᵐ[TimeMeasure(T)]
      fun t => kineticForm (F (t, a)) (w t))
    (hΩ : ∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Ωmix w t) =ᵐ[TimeMeasure(T)]
      fun t => vorticityForm (F (t, a)) (M (t, a)) (w t))
    (v f : Mixed(T)) (hv : endpointStrongMixedLeray T v = v)
    (heq : endpointStrongMixedLeray T (endpointMixedProductOperator hT.le Kmix Ωmix v + f) = 0) :
    ∃ u : endpointTorusSpace T, (u : EndpointTorusL2 T) = endpointMixedToJoint T v ∧
      ∀ z : endpointTorusSpace T,
        ⟪endpointTorusFlowOperator hT.le F M cF cM (u : EndpointTorusL2 T),
          (z : EndpointTorusL2 T)⟫_ℝ = ⟪-(endpointMixedToJoint T f), (z : EndpointTorusL2 T)⟫_ℝ :=
  endpointMixedProjectedSolve_to_product hT (endpointStrongMixedLeray T)
    (endpointStrongMixedLeray_realCoefficient T) (endpointMixedProductOperator hT.le Kmix Ωmix)
    (endpointTorusFlowOperator hT.le F M cF cM)
    (endpointMixedToJoint_productOperator_eq_torusFlowOperator hT.le F M cF cM Kmix Ωmix
      (ae_of_all _ hK) (ae_of_all _ hΩ)) v f hv heq

set_option maxHeartbeats 1800000 in
/-- The physical mixed solve has a polynomial norm bound with one prefactor for all
positive slab durations at most one. -/
theorem exists_endpointPhysicalMixedSolve_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ} (hT : 0 < T) (_hT₁ : T ≤ 1) {D L S F₁ M₁ : ℝ},
      1 ≤ D → 0 ≤ L → 0 ≤ S → 0 ≤ F₁ → 0 ≤ M₁ →
      ∀ (F G M Mt : ℝ × A → Coefficient)
        (cF : ContinuousOn F Slab(T)) (cM : ContinuousOn M Slab(T)),
      (∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => F (r, a))
        ((M (t, a)).comp (F (t, a))) (Icc 0 T) t) →
      (∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) (Icc 0 T) t) →
      (∀ a, ContinuousOn (fun t => Mt (t, a)) (Icc 0 T)) →
      (∀ q ∈ Slab(T), (G q).comp (F q) = ContinuousLinearMap.id ℝ Vec3) →
      (∀ q ∈ Slab(T), ‖G q‖ ≤ D) →
      (∀ q ∈ Slab(T), ‖F q‖ ≤ S) →
      (∀ q ∈ Slab(T), ‖M q‖ ≤ L) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖F (t, a) - F (t, b)‖ ≤ F₁ * dist a b) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖M (t, a) - M (t, b)‖ ≤ M₁ * dist a b) →
      (∀ q ∈ Slab(T), ∀ x : Vec3, ⟪endpointHessian (M q) (Mt q) x, x⟫_ℝ ≤ ‖x‖ ^ 2) →
      ∀ f : Mixed(T),
      ∃ (Kmix Ωmix : MixedCoefficient(T)) (v : Mixed(T)) (u : endpointTorusSpace T),
        (∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Kmix w t) =ᵐ[TimeMeasure(T)]
          fun t => kineticForm (F (t, a)) (w t)) ∧
        (∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Ωmix w t) =ᵐ[TimeMeasure(T)]
          fun t => vorticityForm (F (t, a)) (M (t, a)) (w t)) ∧
        endpointStrongMixedLeray T v = v ∧
        endpointStrongMixedLeray T (endpointMixedProductOperator hT.le Kmix Ωmix v + f) = 0 ∧
        (∀ a, endpointIntegral T (HalfHolder.eval a v) = 0) ∧
        (u : EndpointTorusL2 T) = endpointMixedToJoint T v ∧
        (∀ z : endpointTorusSpace T,
          ⟪endpointTorusFlowOperator hT.le F M cF cM (u : EndpointTorusL2 T),
            (z : EndpointTorusL2 T)⟫_ℝ = ⟪-(endpointMixedToJoint T f), (z : EndpointTorusL2 T)⟫_ℝ) ∧
        let Q := 4 + 2 * D ^ 2 * (1 + L) ^ 2 + (S ^ 2 + T * (2 * S ^ 2 * L)) +
          (2 * S * F₁ + T * (4 * S * F₁ * L + 2 * S ^ 2 * M₁))
        ‖v‖ ≤ C * Q ^ 145 * ‖endpointStrongMixedLeray T f‖ ∧
        ‖v‖ ≤ C * Q ^ 145 * ‖f‖ := by
  obtain ⟨C₀, hC₀, hSolve⟩ := exists_endpointStrongMixedSolve_uniform
  obtain ⟨Cproj, _, hProjection⟩ := exists_norm_endpointStrongMixedLeray_le
  let C := C₀ * max 1 Cproj
  have hmax : 1 ≤ max 1 Cproj := le_max_left _ _
  have hC : 0 ≤ C := mul_nonneg hC₀ (zero_le_one.trans hmax)
  have hC₀C : C₀ ≤ C := le_mul_of_one_le_right hC₀ hmax
  refine ⟨C, hC, ?_⟩
  intro T hT hT₁ D L S F₁ M₁ hD hL hS hF₁ hM₁ F G M Mt cF cM hF hM hMt hGF hGbound hFbound hMbound
    hFlip hMlip hupper f
  let P := endpointStrongMixedLeray T
  have hP : ‖P‖ ≤ max 1 Cproj := (hProjection T hT).trans (le_max_right _ _)
  obtain ⟨Kmix, Ωmix, hK, hΩ, hBsup, hBlip, hBcoercive⟩ :=
    exists_endpointMixedPhysicalCoefficients hT hT₁ hD hL hS hF₁ hM₁ F G M Mt cF cM
      hF hM hMt hGF hGbound hFbound hMbound hFlip hMlip hupper
  let B := endpointMixedPathCoefficient hT.le Kmix Ωmix
  let μ := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  let L_B := 2 * S * F₁ + T * (4 * S * F₁ * L + 2 * S ^ 2 * M₁)
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hL_B : 0 ≤ L_B := by dsimp [L_B]; positivity
  obtain ⟨v, hv, hProjected, hEstimate⟩ := hSolve hT B (μ := μ) (L := L_B) hμ hL_B hBlip hBcoercive f
  have hProjected' : P (endpointMixedProductOperator hT.le Kmix Ωmix v + f) = 0 := by
    rw [← endpointMixedPathCoefficient_coefficientMul hT.le Kmix Ωmix]
    exact hProjected
  have hMean (a : A) : endpointIntegral T (HalfHolder.eval a v) = 0 := by
    rw [← hv]
    exact endpointStrongMixedLeray_timeIntegral_eq_zero hT v a
  obtain ⟨u, hu, hWeak⟩ :=
    endpointPhysicalMixedSolution_weak hT F M cF cM Kmix Ωmix hK hΩ v f hv hProjected'
  refine ⟨Kmix, Ωmix, v, u, hK, hΩ, hv, hProjected', hMean, hu, hWeak, ?_⟩
  let Q := 4 + 2 * D ^ 2 * (1 + L) ^ 2 + (S ^ 2 + T * (2 * S ^ 2 * L)) + L_B
  change ‖v‖ ≤ C * Q ^ 145 * ‖P f‖ ∧ ‖v‖ ≤ C * Q ^ 145 * ‖f‖
  have hbase : 4 + μ⁻¹ + ‖B.val.1‖ + L_B ≤ Q := by
    dsimp only [Q, μ]
    rw [one_div, inv_inv]
    exact add_le_add (add_le_add le_rfl hBsup) le_rfl
  have hpow : (4 + μ⁻¹ + ‖B.val.1‖ + L_B) ^ 145 ≤ Q ^ 145 :=
    pow_le_pow_left₀ (by positivity) hbase 145
  have hnorm : ‖v‖ ≤ C₀ * Q ^ 145 * ‖P f‖ :=
    hEstimate.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC₀) (norm_nonneg _))
  refine ⟨hnorm.trans ?_, hnorm.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C (by positivity)) (norm_nonneg _)
  · calc
      _ ≤ C₀ * Q ^ 145 * (max 1 Cproj * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((P.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hP (norm_nonneg _))) (by positivity)
      _ = _ := by dsimp only [C]; ac_rfl

set_option maxHeartbeats 1800000 in
/-- The physical mixed solve on a fixed slab. -/
theorem exists_endpointPhysicalMixedSolve {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D L S F₁ M₁ : ℝ},
      1 ≤ D → 0 ≤ L → 0 ≤ S → 0 ≤ F₁ → 0 ≤ M₁ →
      ∀ (F G M Mt : ℝ × A → Coefficient)
        (cF : ContinuousOn F Slab(T)) (cM : ContinuousOn M Slab(T)),
      (∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => F (r, a))
        ((M (t, a)).comp (F (t, a))) (Icc 0 T) t) →
      (∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) (Icc 0 T) t) →
      (∀ a, ContinuousOn (fun t => Mt (t, a)) (Icc 0 T)) →
      (∀ q ∈ Slab(T), (G q).comp (F q) = ContinuousLinearMap.id ℝ Vec3) →
      (∀ q ∈ Slab(T), ‖G q‖ ≤ D) →
      (∀ q ∈ Slab(T), ‖F q‖ ≤ S) →
      (∀ q ∈ Slab(T), ‖M q‖ ≤ L) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖F (t, a) - F (t, b)‖ ≤ F₁ * dist a b) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖M (t, a) - M (t, b)‖ ≤ M₁ * dist a b) →
      (∀ q ∈ Slab(T), ∀ x : Vec3, ⟪endpointHessian (M q) (Mt q) x, x⟫_ℝ ≤ ‖x‖ ^ 2) →
      ∀ f : Mixed(T),
      ∃ (Kmix Ωmix : MixedCoefficient(T)) (v : Mixed(T)) (u : endpointTorusSpace T),
        (∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Kmix w t) =ᵐ[TimeMeasure(T)]
          fun t => kineticForm (F (t, a)) (w t)) ∧
        (∀ (a : A) (w : Path(T)), (fun t => HalfHolder.eval a Ωmix w t) =ᵐ[TimeMeasure(T)]
          fun t => vorticityForm (F (t, a)) (M (t, a)) (w t)) ∧
        endpointStrongMixedLeray T v = v ∧
        endpointStrongMixedLeray T (endpointMixedProductOperator hT.le Kmix Ωmix v + f) = 0 ∧
        (∀ a, endpointIntegral T (HalfHolder.eval a v) = 0) ∧
        (u : EndpointTorusL2 T) = endpointMixedToJoint T v ∧
        (∀ z : endpointTorusSpace T,
          ⟪endpointTorusFlowOperator hT.le F M cF cM (u : EndpointTorusL2 T),
            (z : EndpointTorusL2 T)⟫_ℝ = ⟪-(endpointMixedToJoint T f), (z : EndpointTorusL2 T)⟫_ℝ) ∧
        let Q := 4 + 2 * D ^ 2 * (1 + L) ^ 2 + (S ^ 2 + T * (2 * S ^ 2 * L)) +
          (2 * S * F₁ + T * (4 * S * F₁ * L + 2 * S ^ 2 * M₁))
        ‖v‖ ≤ C * Q ^ 145 * ‖endpointStrongMixedLeray T f‖ ∧
        ‖v‖ ≤ C * Q ^ 145 * ‖f‖ := by
  obtain ⟨C, hC, hSolve⟩ := exists_endpointPhysicalMixedSolve_uniform
  exact ⟨C, hC, hSolve (T := T) hT hT₁⟩

end

end TorusEuler
