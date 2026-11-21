import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchyTwistedSourceCancellation

/-! Pressure normalization and source cancellation for the actual selected expansion. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)

/-- Every retained oscillatory pressure has zero phase mean, including the
prescribed pressure at level one. -/
theorem selected_pressure_phaseMean_zero (b : PhysicalApproximationData d p P)
    (hLeading : ∀ t ∈ I, ∀ a, phaseMean (fun s => b.leading.output.p.val.val.val (t,a,s)) = 0)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P) (t : ℝ) (ht : t ∈ I) (a : Vec3) :
    phaseMean (fun s => (b.profiles.p i).val.val.val (t,a,s)) = 0 := by
  by_cases h : i = 1
  · subst i
    have hq : b.profiles.p 1 = b.leading.output.p :=
      (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
        b.parentResidual_average b.leading.output).2.1
    rw [hq]
    exact hLeading t ht a
  · obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hi
    have hi' : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, hr⟩
    obtain ⟨hf, _, hq⟩ := b.solvers.construct_transverse_selected hi' b.leading.completionSwitch
      b.parentResidual b.parentResidual_average b.leading.output
    change b.profiles.p i = _ at hq
    rw [hq]
    exact (solveTransverse hT d.inverse d.strain d.covector d.oscillation _ hf).pressure_mean t ht a

theorem parentStrain_phaseIndependent : HierarchyPeriodicProfile.PhaseIndependent d.strain.val.val := by
  intro x hx s
  exact (d.strain_value (x.1,x.2.1,s) ⟨hx.1,mem_univ _⟩).trans (d.strain_value x hx).symm

/-- The phase-centered linear relay of the actual selected expansion. -/
theorem average_selectedRelay_eq_zero (b : PhysicalApproximationData d p P)
    (hLeading : ∀ t ∈ I, ∀ a, phaseMean (fun s => b.leading.output.p.val.val.val (t,a,s)) = 0)
    (hSwitch : b.operators.average b.leading.completionSwitch = 0)
    {i : ℕ} (hi : i ∈ Finset.Icc 2 P) :
    b.operators.average (b.operators.relayAtLevel b.profiles b.leading.completionSwitch i) = 0 := by
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hi
  have hiprev : i - 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hC : b.profiles.C (i-1) = b.solvers.complete (b.profiles.V (i-1)) :=
    b.solvers.construct_completion hiprev b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  have hCmean : b.operators.average (b.profiles.C (i-1)) = 0 := by
    rw [hC]
    exact average_complete hT d.inverse d.strain d.covector d.mean.inverse_independent
      d.oscillation.covector_independent d.oscillation.covector_ne_zero _
  exact average_relayAtLevel_eq_zero hT d.inverse d.strain d.covector d.mean.inverse_independent
    (parentStrain_phaseIndependent (d := d)) b.profiles b.leading.completionSwitch i hCmean
    (b.selected_pressure_phaseMean_zero hLeading hiprev) hSwitch

set_option maxHeartbeats 1500000 in
/-- Apply the three-term mean-source cancellation to the actual parent
chart and selected profiles. -/
theorem average_selectedSourceBeforeMean_eq (b : PhysicalApproximationData d p P)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hLeading : ∀ t ∈ I, ∀ a, phaseMean (fun s => b.leading.output.p.val.val.val (t,a,s)) = 0)
    (hSwitch : b.operators.average b.leading.completionSwitch = 0)
    (hP : 1 ≤ P) {i : ℕ} (hi : i ≤ P) :
    b.operators.average (b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch i) =
      ∑ ij ∈ hierarchyLevelPairs P 0 i,
        (b.operators.average (b.operators.labelAdv (b.profiles.Y ij.1) (b.profiles.Y ij.2)) +
          b.operators.average (slowLabelDivergenceProduct hT d.inverse (b.profiles.V ij.1) (b.profiles.Y ij.2)) +
          b.operators.labelAdv (b.profiles.B ij.1) (b.profiles.B ij.2)) := by
  obtain ⟨hsurj,hgraph⟩ := d.inverseGraph_values hX hU hper
  have hAreg := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hA (t : ℝ) (ht : t ∈ I) : ContDiff ℝ 2 (X t 0) := by
    have hProj : ContDiff ℝ ∞ (fun x : Vec3 => (t,x)) := contDiff_const.prodMk contDiff_id
    exact ((hAreg.comp_contDiff hProj (fun x => ⟨ht,mem_univ x⟩)).of_le (by simp))
  exact average_construct_sourceBeforeMean_eq_slowProducts hT d.inverse d.strain d.covector
    d.mean.inverse_independent (parentStrain_phaseIndependent (d := d)) d.oscillation.covector_independent
    d.oscillation.covector_ne_zero hA hsurj (fun t ht x s => (hgraph t ht x s).1)
    (fun t ht x => (hgraph t ht x 0).2) b.solvers (fun _ => rfl) hP hi
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output hLeading
    (fun f hf => (solveTransverse hT d.inverse d.strain d.covector d.oscillation f hf).pressure_mean) hSwitch

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
