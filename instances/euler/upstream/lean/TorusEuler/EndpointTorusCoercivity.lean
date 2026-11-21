import TorusEuler.EndpointKinetic
import TorusEuler.EndpointL2Coercivity
import TorusEuler.EndpointSpaceOperator

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "Slab(" T ")" => (Set.prod (Icc (0 : ℝ) T) (univ : Set Labels))
local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)

private theorem isCompact_endpointSlab (T : ℝ) : IsCompact (Slab(T)) :=
  isCompact_Icc.prod isCompact_univ

private theorem ae_mem_endpointSlab (T : ℝ) :
    ∀ᵐ q ∂endpointTorusMeasure T, q ∈ Slab(T) := by
  have h : ∀ᵐ q ∂endpointTorusMeasure T, q.1 ∈ Ioc (0 : ℝ) T :=
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure T) (ν := unitTorusMeasure)).ae
      (ae_restrict_mem measurableSet_Ioc)
  exact h.mono fun q hq => ⟨Ioc_subset_Icc_self hq, mem_univ q.2⟩

private theorem endpointCoefficient_aestronglyMeasurable {T : ℝ}
    {A : ℝ × Labels → Coefficient} (hA : ContinuousOn A (Slab(T))) :
    AEStronglyMeasurable A (endpointTorusMeasure T) := by
  have h := hA.aestronglyMeasurable_of_isCompact (μ := endpointTorusMeasure T)
    (isCompact_endpointSlab T) (measurableSet_Icc.prod MeasurableSet.univ)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_endpointSlab T)] at h

private theorem endpointCoefficient_bounded {T : ℝ}
    {A : ℝ × Labels → Coefficient} (hA : ContinuousOn A (Slab(T))) :
    ∃ C : ℝ, ∀ᵐ q ∂endpointTorusMeasure T, ‖A q‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_endpointSlab T).exists_bound_of_continuousOn hA
  exact ⟨C, (ae_mem_endpointSlab T).mono hC⟩

private theorem continuousOn_endpointKinetic {T : ℝ} {F : ℝ × Labels → Coefficient}
    (hF : ContinuousOn F (Slab(T))) : ContinuousOn (fun q => kineticForm (F q)) (Slab(T)) := by
  have hAdj : Continuous (fun A : Coefficient => A.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  exact (hAdj.comp_continuousOn hF).clm_comp hF

private theorem continuousOn_endpointVorticity {T : ℝ} {F M : ℝ × Labels → Coefficient}
    (hF : ContinuousOn F (Slab(T))) (hM : ContinuousOn M (Slab(T))) :
    ContinuousOn (fun q => vorticityForm (F q) (M q)) (Slab(T)) := by
  have hAdj : Continuous (fun A : Coefficient => A.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  exact (hAdj.comp_continuousOn hF).clm_comp
    (((hAdj.comp_continuousOn hM).sub hM).clm_comp hF)

/-- The space-time operator from (4.9) with the kinetic and vorticity coefficients
from (4.1). Continuity on the compact slab gives the required measurable bounds. -/
noncomputable def endpointTorusFlowOperator {T : ℝ} (hT : 0 ≤ T)
    (F M : ℝ × Labels → Coefficient)
    (cF : ContinuousOn F (Slab(T))) (cM : ContinuousOn M (Slab(T))) :
    EndpointTorusL2 T →L[ℝ] EndpointTorusL2 T :=
  endpointProductOperator unitTorusMeasure hT
    (fun q => kineticForm (F q)) (fun q => vorticityForm (F q) (M q))
    (endpointCoefficient_aestronglyMeasurable (continuousOn_endpointKinetic cF))
    (endpointCoefficient_aestronglyMeasurable (continuousOn_endpointVorticity cF cM))
    (endpointCoefficient_bounded (continuousOn_endpointKinetic cF)).choose_spec
    (endpointCoefficient_bounded (continuousOn_endpointVorticity cF cM)).choose_spec

theorem endpointTorusFlowOperator_apply_ae {T : ℝ} (hT : 0 ≤ T)
    (F M : ℝ × Labels → Coefficient)
    (cF : ContinuousOn F (Slab(T))) (cM : ContinuousOn M (Slab(T))) (v : EndpointTorusL2 T) :
    (endpointTorusFlowOperator hT F M cF cM v : ℝ × Labels → Vec3) =ᵐ[endpointTorusMeasure T]
      fun q => kineticForm (F q) (v q) -
        endpointPrimitive (fun t => vorticityForm (F (t, q.2)) (M (t, q.2)) (v (t, q.2))) q.1 :=
  endpointProductOperator_apply_ae unitTorusMeasure hT _ _ _ _ _ _ v

/-- The weak space-time inverse from Theorem 4.2 under the deformation and Hessian
hypotheses in (4.1)–(4.8). In (4.9) the ambient right-hand side is the negative of
the supplied source. The spatial Hölder estimates require the Appendix A regularity argument. -/
theorem exists_endpointTorusFlowL2Solution {T D L : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (F G M Mt : ℝ × Labels → Coefficient)
    (cF : ContinuousOn F (Slab(T))) (cM : ContinuousOn M (Slab(T)))
    (hF : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => F (r, a))
      ((M (t, a)).comp (F (t, a))) (Icc 0 T) t)
    (hM : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) (Icc 0 T) t)
    (hMt : ∀ a, ContinuousOn (fun t => Mt (t, a)) (Icc 0 T))
    (hGF : ∀ q ∈ Slab(T), (G q).comp (F q) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ q ∈ Slab(T), ‖G q‖ ≤ D) (hMbound : ∀ q ∈ Slab(T), ‖M q‖ ≤ L)
    (hupper : ∀ q ∈ Slab(T), ∀ x : Vec3, ⟪endpointHessian (M q) (Mt q) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (f : EndpointTorusL2 T) :
    let B := endpointTorusFlowOperator hT.le F M cF cM
    let c : ℝ := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
    ∃ v : endpointTorusSpace T,
      (∀ w : endpointTorusSpace T, ⟪B (v : EndpointTorusL2 T), (w : EndpointTorusL2 T)⟫_ℝ =
        ⟪f, (w : EndpointTorusL2 T)⟫_ℝ) ∧ ‖v‖ ≤ ‖f‖ / c ∧
      ∀ u : endpointTorusSpace T,
        (∀ w : endpointTorusSpace T, ⟪B (u : EndpointTorusL2 T), (w : EndpointTorusL2 T)⟫_ℝ =
          ⟪f, (w : EndpointTorusL2 T)⟫_ℝ) → u = v := by
  dsimp only [endpointTorusFlowOperator]
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  refine exists_endpointTorusL2Solution hT.le (by positivity) _ _ _ _ _ _ ?_ f
  apply ae_of_all
  intro a v hv hmean
  have hcFa : ContinuousOn (fun t => F (t, a)) (Icc 0 T) :=
    cF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ a⟩)
  have hcMa : ContinuousOn (fun t => M (t, a)) (Icc 0 T) :=
    cM.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ a⟩)
  have hv0 : endpointIntegral T (hv.toLp v) = 0 := by
    rw [endpointIntegral_apply, integral_congr_ae hv.coeFn_toLp, hmean]
  have hb := endpointL2Energy_coercive hT hT1 hD hL hcFa hcMa (hF a) (hM a) (hMt a)
    (fun t ht => hGF (t, a) ⟨ht, mem_univ a⟩)
    (fun t ht => hGbound (t, a) ⟨ht, mem_univ a⟩)
    (fun t ht => hMbound (t, a) ⟨ht, mem_univ a⟩)
    (fun t ht => hupper (t, a) ⟨ht, mem_univ a⟩) (hv.toLp v) hv0
  have hnorm : ‖hv.toLp v‖ ^ 2 = ∫ t, ‖v t‖ ^ 2 ∂timeMeasure T := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (hv.coeFn_toLp.mono fun t ht => by
      change ⟪hv.toLp v t, hv.toLp v t⟫_ℝ = ‖v t‖ ^ 2
      rw [ht, real_inner_self_eq_norm_sq])
  rw [hnorm, endpointL2Energy_eq_integral hT.le hcFa hcMa hv.coeFn_toLp,
    intervalIntegral.integral_of_le hT.le] at hb
  exact hb

end TorusEuler
