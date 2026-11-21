import TorusEuler.HierarchyParentGeometry
import TorusEuler.HierarchyPhysicalGraph

/-! Solenoidality of the physical mean profile in the hierarchy. -/

open Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {hT : 0 < T}

/-- The incompressible label displacement velocity has zero total profile divergence after the coframe transform. -/
theorem ParentGeometry.meanResult_divergence_eq_zero
    (d : ParentGeometry hT U X k)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    {S : HierarchyTwistedProfile T k Vec3}
    (out : MeanResult hT d.inverse d.strain d.covector S d.mean) :
    HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
      out.output.B.val.val = 0 := by
  have hFlow := hX.contDiffOn_forwardLabelFlow hT hU hper
  apply HierarchySmoothProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hp : ContDiffOn ℝ ∞ (fun b : Vec3 => (t, b)) univ :=
    contDiffOn_const.prodMk contDiffOn_id
  have hsub : MapsTo (fun b : Vec3 => (t, b)) univ (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    fun b _ => ⟨ht, mem_univ b⟩
  have hXt : ContDiff ℝ ∞ (X 0 t) := contDiffOn_univ.mp (hFlow.comp hp hsub)
  have hv : ContDiff ℝ ∞ (out.velocity t) := contDiffOn_univ.mp (out.velocity_smooth.comp hp hsub)
  have hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (d.mean.deformation (t, toUnitTorus b)).toLinearMap = 1 :=
    Eventually.of_forall fun b => by
      rw [d.deformation_value t ht b]
      exact hX.det_labelDerivative hT (hU.of_le (by simp)) hper hdiv h0 ht b
  have hphase : (fun r => out.output.B.val.val.val (t, a, r)) =
      fun _ => d.mean.deformation (t, toUnitTorus a) (out.velocity t a) :=
    funext (out.mean_velocity t ht a)
  have hfast : deriv (fun r => out.output.B.val.val.val (t, a, r)) s = 0 := by
    rw [hphase]
    simp
  have hslow : LinearMap.trace ℝ Vec3
      (((fderiv ℝ (fun b => out.output.B.val.val.val (t, b, s)) a).comp
        (d.mean.inverse (t, toUnitTorus a))).toLinearMap) = 0 :=
    trace_endpointPhysicalMean_eq_zero_of_volumePreserving
      (X := X 0 t) ((hXt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt)
      (d.deformation_value t ht) (d.mean.inverse_left (toUnitTorus a) t ht) hdet
      ((hv.differentiable (by simp)) a) (out.velocity_divergence t ht a)
      (fun b => out.mean_velocity t ht b s)
  change (HierarchySmoothProfile.profileLabelDivergence hT d.inverse.val.val out.output.B.val.val).val (t, a, s) +
    (HierarchySmoothProfile.profilePhaseDivergence hT d.covector.val.val out.output.B.val.val).val (t, a, s) = 0
  rw [HierarchySmoothProfile.profileLabelDivergence_apply hT _ _ ht,
    HierarchySmoothProfile.profilePhaseDivergence_apply hT _ _ ht, d.mean.inverse_value _ hx,
    hslow, hfast, inner_zero_right, add_zero]

/-- The selected physical mean solver supplies the zero-divergence hypothesis of the graph construction. -/
theorem ParentGeometry.physicalSolvers_mean_divergence_eq_zero
    (d : ParentGeometry hT U X k)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0) (hT₁ : T ≤ 1)
    (S : HierarchyTwistedProfile T k Vec3)
    (hS : (twistedHierarchyOperators hT d.inverse d.strain d.covector).average S = S) :
    HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
      ((physicalSolvers hT hT₁ d.inverse d.strain d.covector d.mean d.oscillation).solveMean S hS).val.B.val.val = 0 :=
  d.meanResult_divergence_eq_zero hX hU hper hdiv
    (solveMean hT hT₁ d.inverse d.strain d.covector d.mean S hS)

end

end TorusEuler.HierarchyTwistedProfile
