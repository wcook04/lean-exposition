import TorusEuler.TerminalScheduledParentCoefficients
import TorusEuler.TerminalCoefficientTimeNorms
import TorusEuler.HierarchyTwistedSlowSourceBounds

/-! Exact coefficient and old residual caps for the scheduled mixed recurrence. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

set_option maxHeartbeats 1400000 in
/-- A scaled row of the inverse coframe has the same derivative slope as
the coframe, with the expected single inverse label width. -/
theorem scaledCoframeRowProfile_unweighted_timeJetSeminorm_le
    {f : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {ell h D A : ℝ}
    {q p : ℕ} {C : ℕ → ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hell : 0 ≤ ell) (hD : 0 ≤ D) (hA : 0 ≤ A) (hScale : ell * D ^ p ≤ 1)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (hVal : ∀ x ∈ hierarchyProfileSlab T, G.val.val.val x = f x.1 x.2.1)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hRaw : TerminalMixedJetBound 0 T q p D A C f)
    (hC : ∀ n, 0 ≤ C n) (n : ℕ) (i : Fin 3) :
    timeJetSeminorm hT q (unweightedSeminorm False ell h n hT) (scaledCoframeRowProfile ell G i) ≤
      terminalLabelTimeSeminormCost C q n * (ell⁻¹ * A) := by
  let Q : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj i
  let L : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] ℝ) := ell⁻¹ • compL ℝ Vec3 Vec3 ℝ Q
  have hInv : 0 ≤ ell⁻¹ := inv_nonneg.mpr hell
  have hQ : ‖Q‖ ≤ 1 := Q.opNorm_le_bound zero_le_one fun y => by
    change ‖y i‖ ≤ 1 * ‖y‖
    rw [one_mul]
    exact PiLp.norm_apply_le y i
  have hL : ‖L‖ ≤ ell⁻¹ := L.opNorm_le_bound hInv fun B => by
    change ‖ell⁻¹ • Q.comp B‖ ≤ ell⁻¹ * ‖B‖
    rw [norm_smul, Real.norm_of_nonneg hInv]
    apply mul_le_mul_of_nonneg_left _ hInv
    calc
      _ ≤ ‖Q‖ * ‖B‖ := Q.opNorm_comp_le B
      _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg B)
      _ = _ := one_mul _
  let g (t : ℝ) (x : Vec3) := L (f t x)
  have hg : TerminalMixedJetBound 0 T q p D (ell⁻¹ * A) C g := by
    have h := hRaw.apply_clm hT hf L
    intro j hj m t ht x
    refine (h j hj m t ht x).trans ?_
    calc
      _ ≤ (ell⁻¹ * C m) * A * D ^ (p * m) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (hC m)) hA)
          (pow_nonneg hD _)
      _ = _ := by ring
  have hRow (z : HierarchyProfilePoint) (hz : z ∈ hierarchyProfileSlab T) :
      (scaledCoframeRowProfile ell G i).val.val.val z = g z.1 z.2.1 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [scaledCoframeRowProfile_apply ell G i hz, hVal z hz]
    rfl
  exact unweighted_timeJetSeminorm_le_of_labelMixedJetBound hT hT₁ hell hD
    (mul_nonneg hInv hA) hScale _ hRow hg hC n

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile

noncomputable section

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (j q E : ℕ)

set_option maxHeartbeats 2500000 in
/-- The selected actual stage supplies the slow row, fast phase coefficient
and transported old residual used in the mixed hierarchy. The old residual
only uses time orders through `q`. -/
theorem scheduledTimeSourceCoefficientBounds {C : ℕ → ℝ} (hC : ∀ m, 0 ≤ C m)
    (hRadius : 16 ≤ c.radiusExponent) (raw : c.ScheduledParentCoefficientTimeBounds j q E C) :
    let d := (c.selectedStep j).selected
    let D := P.frequency (j + 1) ^ (9 : ℕ)
    let freq := P.frequency (j + 2)
    let U : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E],
      ℕ → ℕ → Seminorm ℝ (HierarchyTwistedProfile (c.construction.slab (j+2)) d.carrier E) :=
      fun r n => timeJetSeminorm d.time_pos r (unweightedSeminorm False d.radius d.width n d.time_pos)
    ∀ m, (∀ i : Fin 3, U (q+1) m (scaledCoframeRowProfile d.radius d.parent.geometry.inverse i) ≤
        terminalLabelTimeSeminormCost C (q+1) m * D ^ (c.radiusExponent + E)) ∧
      U (q+1) m (scaledPhaseCoefficientProfile d.width d.parent.geometry.covector) ≤
        terminalLabelTimeSeminormCost C (q+1) m * D ^ E * freq ^ (3 / 2 : ℝ) ∧
      U q m d.approximation.parentResidual ≤
        terminalLabelTimeSeminormCost C q m * D ^ E * freq ^ (-5 / 2 : ℝ) := by
  intro d D freq U m
  let tip := c.construction.tip j
  let geom := d.parent.geometry
  have hD : 1 ≤ D := one_le_two.trans d.parent_scale_ge_two
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hf : 0 < freq := zero_lt_one.trans_le d.child_frequency_ge_one
  have hS : d.radius * D ^ (16 : ℕ) ≤ 1 := d.radius_mul_parent_power hRadius
  have hell : 0 ≤ d.radius := d.regularity.envelope_pos.le
  have hA : 0 ≤ D ^ E := pow_nonneg hD₀ _
  have hUf (t : ℝ) (_ : t ∈ Icc 0 (c.construction.slab (j+2))) :
      SpatiallyPeriodic (tip.parent.velocity t) := tip.parent.periodic_velocity t
  let f (t : ℝ) (x : Vec3) := fderiv ℝ (tip.parent.flow t 0) (tip.parent.flow 0 t x)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry f)
      (Icc 0 (c.construction.slab (j+2)) ×ˢ (univ : Set Vec3)) :=
    d.parent.deformationOn.flow.contDiffOn_inverseLabelDerivative d.time_pos d.parent.smooth_velocity hUf
  have hG (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab (c.construction.slab (j+2))) :
      geom.inverse.val.val.val x = f x.1 x.2.1 := geom.inverse_value x hx
  constructor
  · intro i
    have h := scaledCoframeRowProfile_unweighted_timeJetSeminorm_le (h := d.width) d.time_pos d.time_le_one
      hell hD₀ hA hS geom.inverse hG hF raw.inverse hC m i
    have hradius : d.radius⁻¹ = D ^ c.radiusExponent := d.radius_inv
    rw [hradius, ← pow_add] at h
    exact h
  constructor
  · let κ₀ (t : ℝ) (x : Vec3) := labelWaveVector tip.parent.flow 0 x d.carrier t
    have hκ (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab (c.construction.slab (j+2))) :
        geom.covector.val.val.val x = κ₀ x.1 x.2.1 := geom.covector_value x hx
    exact scaledPhaseCoefficientProfile_unweighted_timeJetSeminorm_le d.time_pos d.time_le_one
      hell hD₀ hA hS hf rfl geom.covector hκ raw.covector hC m
  · have hResEq : d.approximation.parentResidual = d.parent.residualProfile := by
      apply HierarchyTwistedProfile.ext
      intro x hx
      rw [d.approximation.parentResidual_value x hx, d.parent.residualProfile_value x hx,
        d.parent.momentum_same x.1 hx.1]
    rw [hResEq]
    have h := d.parent.residualProfile_unweighted_timeJetSeminorm_le (h := d.width) d.time_le_one hell hD₀
      (mul_nonneg hA (Real.rpow_nonneg hf.le _)) hS raw.residual hC m
    rw [show (-(5 / 2 : ℝ)) = (-5 / 2 : ℝ) by ring] at h
    rw [mul_assoc]
    exact h

end

end TorusEuler.ScheduledEulerConstruction
