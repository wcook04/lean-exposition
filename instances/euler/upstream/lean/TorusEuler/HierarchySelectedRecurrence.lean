import TorusEuler.HierarchyPhysicalSourceTerms
import TorusEuler.HierarchySelectedLinearEstimates

/-! The measured recurrence of the actual closed-slab finite construction. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "Q²(" n ")" => hierarchyQuadraticConstant (Fin 4) n ^ (2 : ℕ)

set_option maxHeartbeats 3500000 in
/-- The exact selected physical profiles satisfy the weighted recurrence
once the primitive bounds have been estimated at the required orders. -/
theorem selectedNormRecurrence (b : PhysicalApproximationData d p P) (lead : LeadingRelayData b)
    {H : ℕ} (hP : 1 ≤ P) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {S : Set Vec3} (hS : IsClosed S)
    (inactive : b.leading.Inactive t₀ S)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (hh : h ≠ 0) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1) {freq L K : ℝ}
    (hf : 0 < freq) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (rowCap relayCap : ℕ → ℝ)
    (hrow : ∀ n, n + 1 ≤ H → ∀ i : Fin 3,
      unweightedSeminorm False ℓ h n hT (scaledCoframeRowProfile ℓ d.inverse i) ≤ rowCap n)
    (hRowCap : ∀ n, n + 1 ≤ H → 2 * (3 * Q²(n) * rowCap n) ≤ K * L)
    (hFastCap : ∀ n, n + 1 ≤ H →
      (2 * Q²(n)) * unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h d.covector) ≤
        K * L * freq ^ (3 / 2 : ℝ))
    (hCoeff : ∀ n, n + 1 ≤ H → WaveRelayCoefficientBudget ℓ h n (relayCap n)
      (fun (t : Icc t₀ T) a => d.inverse.val.val.val (t,a,0))
      (fun (t : Icc t₀ T) a => d.strain.val.val.val (t,a,0))
      (fun (t : Icc t₀ T) a => freq⁻¹ • d.covector.val.val.val (t,a,0)))
    (hCompleteCap : ∀ n, n + 1 ≤ H → completionOrderConstant n * relayCap n ^ 2 ≤ K * L)
    (hRelayCap : ∀ n, n + 1 ≤ H → waveRelayOrderConstant n * relayCap n ^ 2 ≤ K * L) :
    let U₀ : ℕ → Seminorm ℝ VP := fun n => unweightedSeminorm False ℓ h n hT
    let W : ℕ → Seminorm ℝ VP := fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
    let pressureNorm : ℕ → Seminorm ℝ SP := fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
    let s := actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
      freq hf.le ℓ h hT ht₀ htT γ hγ hpos
    (∀ n, n + 1 ≤ H → U₀ n b.parentResidual ≤ K * freq ^ hierarchyMeanExponent 2) →
    (∀ n ≤ H, W n b.leading.output.V + freq * pressureNorm n b.leading.output.p ≤
      K * L * freq ^ hierarchyOscExponent 1) →
    (∀ n, n+1 ≤ H → ∀ f hf', U₀ n (b.solvers.solveMean f hf').val.B ≤ K * L * U₀ (n+1) f) →
    (∀ n ≤ H, ∀ i ∈ Finset.Icc 2 P, s.osc n i ≤ K * L * s.oscSource n i) →
    HierarchyNormRecurrence s freq L K P H := by
  intro U₀ W pressureNorm s hResidual hSeed hMean hOsc
  obtain ⟨hSup, _, _⟩ := physicalConstruct_support_and_tail_on_inactive hT b.time_le_one hS
    d.inverse d.strain d.covector d.mean d.oscillation hP b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output inactive.velocity inactive.pressure inactive.completionSwitch
  have hVzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (hl : t < t₀) (x : Vec3 × ℝ) :
      (b.profiles.V i).val.val.val (t,x) = 0 :=
    (hSup i).1 (x := (t,x)) ⟨⟨ht,mem_univ _⟩, Or.inl hl⟩
  have hCzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (hl : t < t₀) (x : Vec3 × ℝ) :
      (b.profiles.C i).val.val.val (t,x) = 0 :=
    (hSup i).2.1 (x := (t,x)) ⟨⟨ht,mem_univ _⟩, Or.inl hl⟩
  have hLin (n : ℕ) (hn : n+1 ≤ H) := b.selectedLinearEstimates lead hX hU hper ℓ h hℓ n hf
    ht₀ htT γ hγ hpos (hCoeff n hn) (hCompleteCap n hn) (hRelayCap n hn)
  have hTerms := actualMeasuredLevels_sourceTermBounds hT d.inverse d.strain d.covector b.profiles P H
    b.leading.completionSwitch b.parentResidual hf.le ℓ h hℓ hh ht₀ htT γ hγ hpos hγle d.mean.inverse_independent
    hVzero hCzero rowCap hrow hRowCap hFastCap
    (b.solvers.construct_average_B P b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output)
    (fun i hi => b.average_selectedSourceBeforeMean_eq hX hU hper lead.pressure_mean lead.completion_mean hP
      (Finset.mem_Icc.mp hi).2)
    (fun i hi => b.average_selectedRelay_eq_zero lead.pressure_mean lead.completion_mean hi)
    hResidual (fun n hn => by simpa only [Real.rpow_neg_one] using (hLin n hn).2)
  refine b.solvers.construct_normRecurrence_from_terms hP b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output hf.le hL hK U₀ W pressureNorm
    (fun i j => slowLabelDivergenceProduct hT d.inverse (b.profiles.V i) (b.profiles.Y j))
    hSeed hMean ?_ hOsc hTerms
  intro n hn v hv
  have h := (hLin n hn).1 v hv
  simpa only [Real.rpow_neg_one] using h

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
