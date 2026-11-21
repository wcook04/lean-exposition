import TorusEuler.HierarchySelectedSourceIdentities
import TorusEuler.HierarchyTwistedRelayCoefficientBudget
import TorusEuler.HierarchyTwistedSelectedRelay

/-! The linear recurrence terms of the actual selected finite expansion. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The leading equation and its completion give the exact linear relay
normalizations at the first correction. -/
structure LeadingRelayData (b : PhysicalApproximationData d p P) : Prop where
  pressure_mean : ∀ t ∈ I, ∀ a, phaseMean (fun s => b.leading.output.p.val.val.val (t,a,s)) = 0
  activation_mean : b.operators.average b.leading.leadingSwitch = 0
  activation_transverse : ∀ t ∈ I, ∀ a s,
    ⟪d.covector.val.val.val (t,a,0), b.leading.leadingSwitch.val.val.val (t,a,s)⟫_ℝ = 0
  completion_switch : b.leading.completionSwitch = b.solvers.complete b.leading.leadingSwitch

theorem LeadingRelayData.completion_mean {b : PhysicalApproximationData d p P} (w : LeadingRelayData b) :
    b.operators.average b.leading.completionSwitch = 0 := by
  rw [w.completion_switch]
  exact b.solvers.average_complete _ w.activation_mean

/-- The coefficient-only factor of the exact curl estimate at finite order. -/
def completionOrderConstant (n : ℕ) : ℝ :=
  6 * (hierarchyAdmissibleWords (Fin 4) n).card *
    (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)

set_option maxHeartbeats 2000000 in
/-- The exact selected completion row and relay row from one common
normalized coefficient bound on the active interval. -/
theorem selectedLinearEstimates (b : PhysicalApproximationData d p P) (lead : LeadingRelayData b)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {freq K L : ℝ} (hf : 0 < freq)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hcoeff : WaveRelayCoefficientBudget ℓ h n K
      (fun (t : Icc t₀ T) a => d.inverse.val.val.val (t,a,0))
      (fun (t : Icc t₀ T) a => d.strain.val.val.val (t,a,0))
      (fun (t : Icc t₀ T) a => freq⁻¹ • d.covector.val.val.val (t,a,0)))
    (hCompleteCap : completionOrderConstant n * K ^ 2 ≤ L)
    (hRelayCap : waveRelayOrderConstant n * K ^ 2 ≤ L) :
    let W : ℕ → Seminorm ℝ VP := fun j => amplitudeSeminorm False ℓ h j hT ht₀ htT γ hγ hpos
    let s := actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
      freq hf.le ℓ h hT ht₀ htT γ hγ hpos
    (∀ v, b.operators.average v = 0 → W n (b.solvers.complete v) ≤ L * freq⁻¹ * W (n+1) v) ∧
    (∀ i ∈ Finset.Icc 2 P, W n (b.operators.relayAtLevel b.profiles b.leading.completionSwitch i) ≤
      L * (freq⁻¹ * (s.osc (n+1) (i-1) + s.oscSource (n+1) (i-1)))) := by
  intro W s
  obtain ⟨B,hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos
  have hGeom := transportedWaveRelay_coefficient_timeEquations hT hX (hU.of_le (by simp)) hper
    d.inverse d.strain d.covector (fun t ht a => d.inverse_value (t,a,0) ⟨ht,mem_univ _⟩)
    (fun t ht a => d.strain_value (t,a,0) ⟨ht,mem_univ _⟩)
    (fun t ht a => d.covector_value (t,a,0) ⟨ht,mem_univ _⟩)
  constructor
  · intro v hv
    have h := boundedWeightSeminorm_complete_le hT d.inverse d.covector v d.mean.inverse_independent
      d.oscillation.covector_independent d.oscillation.covector_ne_zero hv (Icc_subset_Icc_left ht₀)
      (fun t => (γ t)⁻¹) hB ℓ h hℓ n hf hcoeff.curl hcoeff.potential
    change W n (b.solvers.complete v) ≤ completionOrderConstant n * K ^ 2 * freq⁻¹ * W (n+1) v at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCompleteCap (inv_nonneg.mpr hf.le))
      (apply_nonneg _ _))
  · intro i hi
    have h := construct_amplitudeSeminorm_relayAtLevel_le hT d.inverse d.strain d.covector
      d.mean.inverse_independent (parentStrain_phaseIndependent (d := d)) d.oscillation.covector_independent
      d.oscillation.covector_ne_zero hGeom.1 hGeom.2 b.solvers (fun _ => rfl) hi
      b.leading.completionSwitch b.parentResidual b.leading.leadingSwitch b.parentResidual_average b.leading.output
      b.leading.momentum lead.completion_switch lead.activation_mean lead.activation_transverse lead.pressure_mean
      (fun f hf' => (solveTransverse hT d.inverse d.strain d.covector d.oscillation f hf').pressure_mean)
      ℓ h hℓ n hf ht₀ htT γ hγ hpos hcoeff
    change W n _ ≤ waveRelayOrderConstant n * K ^ 2 * freq⁻¹ *
      (s.osc (n+1) (i-1) + s.oscSource (n+1) (i-1)) at h
    rw [mul_assoc (waveRelayOrderConstant n * K ^ 2)] at h
    exact h.trans (mul_le_mul_of_nonneg_right hRelayCap (mul_nonneg (inv_nonneg.mpr hf.le)
      (add_nonneg (s.nonneg _ _).2.2.1 (s.nonneg _ _).1)))

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
