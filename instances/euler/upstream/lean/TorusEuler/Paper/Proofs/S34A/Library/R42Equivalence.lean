import TorusEuler.Paper.S34A.Statements
import TorusEuler.EndpointL2Coercivity
import TorusEuler.EndpointNorm

/-! Glue for the proof of **Theorem 4.2** (package S34A): the velocity bound (4.6)
`∫_I |z_t|² ≤ D_-² (1 + ‖M‖_∞)² ∫_I |ξ_t|²` (sections/06b_mean_inverse.tex:59–76) for
square-integrable velocities `z_t` of zero mean, by density from the `C¹` case
`integral_endpointLabelVelocity_norm_sq_le`. No numbered result is used. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "TimeL2" T => Lp E 2 (timeMeasure T)

/-- (4.6) for velocities `v ∈ L²(I)` of zero mean (sections/06b_mean_inverse.tex:59–76):
with `z = ∫_0^t v`, `ξ = F z` and `ξ_t = M ξ + F v` (4.4),
`∫_I |v|² ≤ D² (1 + L)² ∫_I |ξ_t|²`, where `G F = Id`, `|G| ≤ D`, `|M| ≤ L`, `F' = M F`.
The TeX states it on `H¹₀`; the `C¹` case is `integral_endpointLabelVelocity_norm_sq_le`,
and both sides are continuous in `v ∈ L²`. -/
theorem integral_norm_sq_le_displacement {T D L : ℝ} {F G M : ℝ → E →L[ℝ] E}
    (hT : 0 < T) (hT1 : T ≤ 1) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (cM : ContinuousOn M (Icc 0 T))
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ E)
    (hG : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D) (hM : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (v : TimeL2 T) (hv : endpointIntegral T v = 0) :
    ‖v‖ ^ 2 ≤ D ^ 2 * (1 + L) ^ 2 * ∫ t in (0 : ℝ)..T,
      ‖endpointDisplacementDerivative (F t) (M t) (endpointPrimitive v t) (v t)‖ ^ 2 := by
  have cF : ContinuousOn F (Icc 0 T) := fun t ht => (hF t ht).continuousWithinAt
  let A := endpointTimeMultiplier F cF
  let B := endpointTimeMultiplier M cM
  let X := A.comp (endpointPrimitiveLp hT.le)
  let Dop : (TimeL2 T) →L[ℝ] (TimeL2 T) := B.comp X + A
  have hX (w : TimeL2 T) : (X w : ℝ → E) =ᵐ[timeMeasure T]
      fun t => F t (endpointPrimitive w t) := by
    filter_upwards [endpointTimeMultiplier_apply_ae F cF (endpointPrimitiveLp hT.le w),
      endpointPrimitiveLp_apply_ae hT.le w] with t h1 h2
    change A (endpointPrimitiveLp hT.le w) t = _ at h1
    change A (endpointPrimitiveLp hT.le w) t = _
    rw [h1, h2]
  have hDf (w : TimeL2 T) : (Dop w : ℝ → E) =ᵐ[timeMeasure T] fun t =>
      endpointDisplacementDerivative (F t) (M t) (endpointPrimitive w t) (w t) := by
    filter_upwards [Lp.coeFn_add (B (X w)) (A w), endpointTimeMultiplier_apply_ae M cM (X w),
      endpointTimeMultiplier_apply_ae F cF w, hX w] with t hadd h1 h2 hx
    change B (X w) t = _ at h1
    change A w t = _ at h2
    change (B (X w) + A w) t = _
    rw [hadd, Pi.add_apply, h1, h2, hx]
    rfl
  have hDnorm (w : TimeL2 T) {g : ℝ → E} (hg : w =ᵐ[timeMeasure T] g) :
      ‖Dop w‖ ^ 2 = ∫ t in (0 : ℝ)..T,
        ‖endpointDisplacementDerivative (F t) (M t) (endpointPrimitive g t) (g t)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, intervalIntegral.integral_of_le hT.le]
    apply integral_congr_ae
    filter_upwards [hDf w, hg, ae_restrict_mem measurableSet_Ioc] with t hd he ht
    change ⟪Dop w t, Dop w t⟫_ℝ = _
    rw [hd, endpointPrimitive_congr_ae hg (Ioc_subset_Icc_self ht), he,
      real_inner_self_eq_norm_sq]
  let c : ℝ := D ^ 2 * (1 + L) ^ 2
  let good : Set (TimeL2 T) := {w | ‖w‖ ^ 2 ≤ c * ‖Dop w‖ ^ 2}
  have hgood : IsClosed good :=
    isClosed_le (continuous_norm.pow 2) (continuous_const.mul (Dop.continuous.norm.pow 2))
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
    change ‖w‖ ^ 2 ≤ c * ‖Dop w‖ ^ 2
    rw [hnorm, hDnorm w hwg]
    exact integral_endpointLabelVelocity_norm_sq_le hT.le hT1 hD hL hF hz cM
      hg.continuous.continuousOn hzT hGF hG hM
  have hsubset := closure_minimal hsmooth hgood
  rw [closure_smooth_meanZero_L2 hT] at hsubset
  have h := hsubset hv
  change ‖v‖ ^ 2 ≤ c * ‖Dop v‖ ^ 2 at h
  rwa [hDnorm v EventuallyEq.rfl] at h

end TorusEuler.Paper.Lib.S34A
