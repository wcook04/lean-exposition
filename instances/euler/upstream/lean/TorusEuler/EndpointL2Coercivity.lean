import TorusEuler.EndpointCoercivity
import TorusEuler.EndpointDensity
import TorusEuler.EndpointL2Multiplier
import TorusEuler.EndpointPrimitive

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "TimeL2" T => Lp E 2 (timeMeasure T)

omit [CompleteSpace E] in
private theorem continuousOn_aebound {T : ℝ} {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousOn A (Icc 0 T)) :
    ∃ C : ℝ, ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  exact ⟨C, (ae_restrict_mem measurableSet_Ioc).mono
    (fun t ht => hC t (Ioc_subset_Icc_self ht))⟩

/-- Multiplication by an operator field continuous on the closed time interval. -/
noncomputable def endpointTimeMultiplier {T : ℝ} (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc 0 T)) : (TimeL2 T) →L[ℝ] (TimeL2 T) :=
  endpointL2Multiplier A
    (hA.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self)
    (Classical.choose_spec (continuousOn_aebound hA))

omit [CompleteSpace E] in
theorem endpointTimeMultiplier_apply_ae {T : ℝ} (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc 0 T)) (v : TimeL2 T) :
    ⇑(endpointTimeMultiplier A hA v) =ᵐ[timeMeasure T] fun t => A t (v t) :=
  endpointL2Multiplier_apply_ae _ _ _ _

/-- The skew coefficient in (4.1). -/
noncomputable def endpointSkew (F M : E →L[ℝ] E) : E →L[ℝ] E :=
  F.adjoint.comp ((M.adjoint - M).comp F)

theorem continuousOn_endpointSkew {T : ℝ} {F M : ℝ → E →L[ℝ] E}
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T)) :
    ContinuousOn (fun t => endpointSkew (F t) (M t)) (Icc 0 T) := by
  have hAdj : Continuous (fun A : E →L[ℝ] E => A.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  exact (hAdj.comp_continuousOn cF).clm_comp
    (((hAdj.comp_continuousOn cM).sub cM).clm_comp cF)

/-- The bounded quadratic form from (4.7), on the fixed-label velocity space. -/
noncomputable def endpointL2Energy {T : ℝ} (hT : 0 ≤ T) (F M : ℝ → E →L[ℝ] E)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T)) (v : TimeL2 T) : ℝ :=
  ‖endpointTimeMultiplier F cF v‖ ^ 2 +
    ⟪endpointTimeMultiplier (fun t => endpointSkew (F t) (M t))
      (continuousOn_endpointSkew cF cM) v, endpointPrimitiveLp hT v⟫_ℝ

theorem continuous_endpointL2Energy {T : ℝ} (hT : 0 ≤ T) (F M : ℝ → E →L[ℝ] E)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T)) :
    Continuous (endpointL2Energy hT F M cF cM) :=
  ((endpointTimeMultiplier F cF).continuous.norm.pow 2).add
    ((endpointTimeMultiplier (fun t => endpointSkew (F t) (M t))
      (continuousOn_endpointSkew cF cM)).continuous.inner (endpointPrimitiveLp hT).continuous)

/-- The L² quadratic form agrees with the integral on any representative and its primitive. -/
theorem endpointL2Energy_eq_integral {T : ℝ} (hT : 0 ≤ T)
    {F M : ℝ → E →L[ℝ] E} (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    {v : TimeL2 T} {g : ℝ → E} (hg : v =ᵐ[timeMeasure T] g) :
    endpointL2Energy hT F M cF cM v =
      ∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (endpointPrimitive g t) (g t) := by
  let w := endpointTimeMultiplier F cF v
  let y := endpointTimeMultiplier (fun t => endpointSkew (F t) (M t))
    (continuousOn_endpointSkew cF cM) v
  let z := endpointPrimitiveLp hT v
  change ‖w‖ ^ 2 + ⟪y, z⟫_ℝ = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_add
    (L2.integrable_inner w w) (L2.integrable_inner y z), intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  filter_upwards [endpointTimeMultiplier_apply_ae F cF v,
    endpointTimeMultiplier_apply_ae (fun t => endpointSkew (F t) (M t))
      (continuousOn_endpointSkew cF cM) v,
    endpointPrimitiveLp_apply_ae hT v, hg, ae_restrict_mem measurableSet_Ioc] with t hw hy hz hvg ht
  have hz' := endpointPrimitive_congr_ae hg (Ioc_subset_Icc_self ht)
  change ⟪w t, w t⟫_ℝ + ⟪y t, z t⟫_ℝ = _
  change w t = F t (v t) at hw
  change y t = endpointSkew (F t) (M t) (v t) at hy
  change z t = endpointPrimitive v t at hz
  rw [hw, hy, hz, hz', hvg]
  simp only [endpointLabelEnergy, endpointSkew, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- Fixed-label coercivity on all zero-mean velocities, with the coefficient in Theorem 4.2.
    The displacement is the absolutely continuous primitive with L² derivative. -/
theorem endpointL2Energy_coercive {T D L : ℝ} {F G M Mt : ℝ → E →L[ℝ] E}
    (hT : 0 < T) (hT1 : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T))
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ E)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D) (hMbound : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : E, ⟪endpointHessian (M t) (Mt t) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (v : TimeL2 T) (hv : endpointIntegral T v = 0) :
    (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖v‖ ^ 2 ≤ endpointL2Energy hT.le F M cF cM v := by
  let c : ℝ := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  let good : Set (TimeL2 T) := {w | c * ‖w‖ ^ 2 ≤ endpointL2Energy hT.le F M cF cM w}
  have hgood : IsClosed good :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (continuous_endpointL2Energy hT.le F M cF cM)
  have hsmooth : {w : TimeL2 T | ∃ g : ℝ → E, w =ᵐ[timeMeasure T] g ∧
      ContDiff ℝ ∞ g ∧ (∫ t, g t ∂timeMeasure T) = 0} ⊆ good := by
    rintro w ⟨g, hwg, hg, hmean⟩
    have hz : ∀ t ∈ Icc 0 T,
        HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t :=
      fun t _ => (hasDerivAt_endpointPrimitive hg.continuous t).hasDerivWithinAt
    have hzT : endpointPrimitive g T = 0 := by
      simpa only [endpointPrimitive, intervalIntegral.integral_of_le hT.le] using hmean
    have hnorm : ‖w‖ ^ 2 = ∫ t in (0 : ℝ)..T, ‖g t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, intervalIntegral.integral_of_le hT.le]
      exact integral_congr_ae (hwg.mono fun t ht => by
        change ⟪w t, w t⟫_ℝ = ‖g t‖ ^ 2
        rw [ht, real_inner_self_eq_norm_sq])
    change c * ‖w‖ ^ 2 ≤ endpointL2Energy hT.le F M cF cM w
    rw [hnorm, endpointL2Energy_eq_integral hT.le cF cM hwg]
    exact endpointLabelEnergy_coercive_velocity hT.le hT1 hD hL hF hM hz hMt
      hg.continuous.continuousOn (by simp [endpointPrimitive]) hzT hGF hGbound hMbound hupper
  have hsubset := closure_minimal hsmooth hgood
  rw [closure_smooth_meanZero_L2 hT] at hsubset
  exact hsubset hv

end TorusEuler
