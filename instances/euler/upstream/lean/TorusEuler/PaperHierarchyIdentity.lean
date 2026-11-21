import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchyTwistedSourceCancellation

/-! The profile identity of Proposition 5.4 in the frozen paper. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "I" => Icc 0 T
local notation "J" => Set.prod I (univ : Set Vec3)

set_option maxHeartbeats 2800000 in
/-- Proposition 5.4 (cc:uf:hier:prop:identity) for the physical twisted
profiles. Smoothness is encoded by the profile types at every level. -/
theorem paper_hierarchy_identity
    (b : PhysicalApproximationData d p P) (hP : 2 ≤ P)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0)
    {t₀ : ℝ} {S : Set Vec3} (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S) :
    let A := b.operators;
    let u := b.profiles;
    let W := u.velocity P;
    let pressure := u.pressure P;
    let R := A.remainder u P;
    let inactive := hierarchyInactiveRegion T t₀ S;
    let force : ℕ → VP := (fun i =>
      let H := A.sourceBeforeMean u P b.leading.completionSwitch i;
      -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u));
    W = (∑ i ∈ Finset.Icc 1 P, u.Z i) + u.C P ∧
    W = ∑ i ∈ Finset.Icc 1 P, (u.V i + u.C i + u.B i) ∧
    pressure = ∑ i ∈ Finset.Icc 1 P, (u.p i + u.q i) ∧ u.q 1 = 0 ∧
    HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val W.val.val = 0 ∧
    A.material W + A.labelAdv W W + A.phaseAdv W W + A.labelGrad pressure +
      A.phaseGrad pressure + b.parentResidual = R +
        (b.leading.leadingSwitch + b.leading.completionSwitch) ∧
    W - A.average W = ∑ i ∈ Finset.Icc 1 P, (u.V i + u.C i) ∧
    EqOn (W - A.average W).val.val.val 0 inactive ∧
    (∀ i, A.average (u.V i) = 0 ∧ A.average (u.C i) = 0) ∧
    (∀ i, EqOn (u.V i).val.val.val 0 inactive ∧ EqOn (u.C i).val.val.val 0 inactive ∧
      EqOn (u.p i).val.val.val 0 inactive) ∧
    (∀ i ∈ Finset.Icc 2 P, EqOn (force i).val.val.val 0 inactive) ∧
    u.V (P + 1) = 0 ∧ u.B (P + 1) = 0 ∧ u.Y (P + 1) = u.C P ∧ u.Z (P + 1) = u.C P ∧
    R = A.material (u.C P) + A.labelGrad (u.p P) +
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.Z ij.1) (u.Z ij.2)) +
      (∑ ij ∈ hierarchyTailPairs P 1, A.phaseAdv (u.Z ij.1) (u.Y ij.2)) ∧
    (∀ t ∈ I, ∀ x ∉ S, ∀ s s', R.val.val.val (t,x,s) = R.val.val.val (t,x,s')) ∧
    ContDiffOn ℝ ∞ W.val.val.val (hierarchyProfileSlab T) ∧
    ContDiffOn ℝ ∞ pressure.val.val.val (hierarchyProfileSlab T) ∧
    ContDiffOn ℝ ∞ R.val.val.val (hierarchyProfileSlab T) := by
  intro A u W pressure R inactive force
  have hP₁ : 1 ≤ P := by omega
  have hzero i (hi : i = 0 ∨ P < i) :=
    b.solvers.construct_eq_zero_of_index hP₁ hi b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  have hC₀ : u.C 0 = 0 := (hzero 0 (Or.inl rfl)).2.1
  have hVlast : u.V (P + 1) = 0 := (hzero (P + 1) (Or.inr (Nat.lt_succ_self _))).1
  have hBlast : u.B (P + 1) = 0 := (hzero (P + 1) (Or.inr (Nat.lt_succ_self _))).2.2.1
  have hYlast : u.Y (P + 1) = u.C P := by simp [HierarchyProfiles.Y, hVlast]
  have hZlast : u.Z (P + 1) = u.C P := by simp [HierarchyProfiles.Z, hYlast, hBlast]
  have hq₁ : u.q 1 = 0 :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).2.2.2
  have hMomentum := b.solvers.construct_momentum hP b.leading.leadingSwitch b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output b.leading.momentum
  have hOsc : W - A.average W = ∑ i ∈ Finset.Icc 1 P, (u.V i + u.C i) :=
    b.solvers.construct_velocity_sub_average P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  obtain ⟨hSupport,hForce,hTail⟩ := physicalConstruct_support_and_tail_on_inactive (τ := t₀) hT
    b.time_le_one hS d.inverse d.strain d.covector d.mean d.oscillation hP₁
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hInactive.velocity hInactive.pressure hInactive.completionSwitch
  have hWosc : EqOn (W - A.average W).val.val.val 0 inactive := by
    intro z hz
    change (u.velocity P - A.average (u.velocity P)).val.val.val z = 0
    rw [hOsc]
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_add, Pi.add_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hv : (u.V i).val.val.val z = 0 := (hSupport i).1 hz
    have hc : (u.C i).val.val.val z = 0 := (hSupport i).2.1 hz
    rw [hv, hc, add_zero]
  obtain ⟨hSurj, hChart⟩ := d.inverseGraph_values hX hU hper
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hCdiv (o : HierarchyTransverseOutput A) :
      HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
        (o.V + b.solvers.complete o.V).val.val = 0 :=
    profileTotalDivergence_completedOutput_eq_zero hT d.inverse d.strain d.covector
      d.oscillation.covector_independent d.oscillation.covector_ne_zero o
      (fun t ht => contDiffOn_univ.mp ((hA.of_le (by simp)).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨ht, mem_univ x⟩))) hSurj
      (fun t ht x s => (hChart t ht x s).1) (fun t ht x s => (hChart t ht x s).2)
  let forget : VP →ₗ[ℝ] HierarchySmoothProfile T Vec3 :=
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype.comp
      (hierarchyTwistedProfileSubmodule T k Vec3).subtype
  let D := (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val).comp forget
  have hWdiv : HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
      W.val.val = 0 :=
    b.solvers.construct_divergence_eq_zero P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output D hCdiv
      (d.physicalSolvers_mean_divergence_eq_zero hX hU hper hdiv b.time_le_one)
  have hPhaseData (i : ℕ) : A.average (u.V i) = 0 ∧ A.average (u.C i) = 0 ∧
      ∀ v, A.phaseAdv (u.V i) v = 0 :=
    b.solvers.construct_oscillatory_phase_data P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output i
  have hav i : A.average (u.V i) = 0 ∧ A.average (u.C i) = 0 :=
    ⟨(hPhaseData i).1, (hPhaseData i).2.1⟩
  have hphase i v : A.phaseAdv (u.V i) v = 0 := (hPhaseData i).2.2 v
  have hRformula : R = A.material (u.C P) + A.labelGrad (u.p P) +
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.Z ij.1) (u.Z ij.2)) +
      (∑ ij ∈ hierarchyTailPairs P 1, A.phaseAdv (u.Z ij.1) (u.Y ij.2)) := by
    unfold R HierarchyOperators.remainder
    congr 1
    refine Finset.sum_congr rfl fun ij _ => ?_
    change A.phaseAdv (u.C (ij.1 - 1)) (u.Y ij.2) + A.phaseAdv (u.B ij.1) (u.Y ij.2) = _
    rw [show u.Z ij.1 = u.V ij.1 + u.C (ij.1 - 1) + u.B ij.1 from rfl]
    simp only [map_add, LinearMap.add_apply, hphase, zero_add]
  let meanTail := ∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)
  have hmeanAvg i : A.average (u.B i) = u.B i :=
    b.solvers.construct_average_B P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output i
  have hmeanTail : A.average meanTail = meanTail := by
    dsimp only [meanTail]
    rw [map_sum]
    exact Finset.sum_congr rfl fun ij _ =>
      average_labelAdv_independent_independent hT d.inverse d.strain d.covector
        (u.B ij.1) (u.B ij.2) d.mean.inverse_independent (hmeanAvg _) (hmeanAvg _)
  have hRind (t : ℝ) (ht : t ∈ I) (x : Vec3) (hx : x ∉ S) (s s' : ℝ) :
      R.val.val.val (t,x,s) = R.val.val.val (t,x,s') := by
    have hsub (a : ℝ) : (t,x,a) ∈ inactive := ⟨⟨ht,mem_univ _⟩, Or.inr hx⟩
    have hAvg (a : ℝ) : meanTail.val.val.val (t,x,a) =
        phaseMean (fun q => meanTail.val.val.val (t,x,q)) :=
      (congrArg (fun z : VP => z.val.val.val (t,x,a)) hmeanTail).symm.trans
        (average_apply_phaseMean hT d.inverse d.strain d.covector _ ht x a)
    exact (hTail (hsub s)).trans ((hAvg s).trans ((hAvg s').symm.trans (hTail (hsub s')).symm))
  exact ⟨u.velocity_eq_sum_Z_add_completion hP₁ hC₀, rfl, rfl, hq₁, hWdiv, hMomentum, hOsc, hWosc,
    hav, hSupport, hForce, hVlast, hBlast, hYlast, hZlast, hRformula, hRind,
    HierarchySmoothProfile.smooth W.val.val, HierarchySmoothProfile.smooth pressure.val.val,
    HierarchySmoothProfile.smooth R.val.val⟩

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
