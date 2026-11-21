import TorusEuler.PaperGenericWaveSwitch
import TorusEuler.PaperGenericSwitchWeighted
import TorusEuler.PaperHierarchyDepthGeneral
import TorusEuler.PaperTruncatedHierarchySeed

/-! The finite hierarchy for every smooth activation in the paper. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open HierarchyTwistedProfile HierarchyTwistedProfile.PhysicalApproximationData LocalizedAmplitude

set_option maxHeartbeats 4500000 in
/-- Theorem 5.6 for the localized seed of a prescribed central wave and every
smooth cutoff on the parent slab, including the constant first-wave cutoff.
The seed is shared by all cutoffs and retained depths. -/
theorem exists_paper_hierarchy_depth_of_cutoff :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∃ Clevel Ctotal : ℕ → ℕ → ℝ,
        (∀ n i, 0 ≤ Clevel n i) ∧ (∀ n i, 0 ≤ Ctotal n i) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
          {T t₀ D freq : ℝ} {hT : 0 < T}
          {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          (hOdd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) →
          (∀ t ∈ Icc 0 T, Function.Odd (momentumResidual (Icc 0 T) U p t)) →
          ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t)) →
          0 ≤ t₀ → t₀ < T →
          ∀ (a : ℕ), a₀ ≤ a →
          let ℓ := (D ^ a)⁻¹;
          let h := freq ^ (-1 / 2 : ℝ);
          let L := D ^ (2 * a + b₀);
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
          let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x);
          let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t;
          ‖κ t₀ 0‖ = freq →
          (hCenter : CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D) →
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          let hγ : ContinuousOn γ (Icc t₀ T) :=
            (HasDerivWithinAt.continuousOn hCenter.amplitude).norm.const_mul _;
          let hpos (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
            mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le data.frequency_ge_one) _)
              (norm_pos_iff.mpr (hCenter.nonzero t ht).2.1);
          ∃ (Cseed : ℝ) (w : SeedOn M κ center t₀ T ℓ D Cseed)
            (reg : w.HierarchyRegularity 0 h)
            (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)),
            ∀ (χ : PaperWaveCutoff t₀ T) {depth : ℕ}, 2 ≤ depth →
            ∃ b : PhysicalApproximationData d p depth,
              b.leading = PhysicalLeadingInput.ofPaperCutoff d w reg χ data.flow data.velocity_smooth
                data.velocity_periodic hOdd hAmp ∧
              ∀ n : ℕ,
              let s := actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
                freq (zero_le_one.trans data.frequency_ge_one)
                ℓ h hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos
              let F := b.profiles.velocity depth
              let N := unweightedSeminorm False ℓ h n hT
              let W := amplitudeSeminorm False ℓ h n hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos
              (∀ i ∈ Finset.Icc 1 depth,
                s.osc n i + s.oscSource n i ≤ Clevel n i * L ^ 6 * freq ^ hierarchyOscExponent i ∧
                s.mean n i + s.meanSource n i ≤ Clevel n i * L ^ 6 * freq ^ hierarchyMeanExponent i ∧
                s.completion n i ≤ Clevel n i * L ^ 6 * freq ^ hierarchyCompletionExponent i) ∧
              W (F - b.operators.average F) ≤ Ctotal n depth * L ^ 6 * freq ^ (-5 / 4 : ℝ) ∧
              N (∑ i ∈ Finset.Icc 2 depth, b.profiles.B i) +
                  N (∑ i ∈ Finset.Icc 2 depth, b.paperMeanSource i) ≤
                Ctotal n depth * L ^ 6 * freq ^ (-5 / 2 : ℝ) ∧
              N (b.operators.remainder b.profiles depth) ≤ Ctotal n depth * freq ^ hierarchyOscExponent (depth + 1) ∧
              (∀ i ∈ Finset.Icc 1 depth, HierarchyLevelBound s freq L (Ctotal n depth) n i) := by
  obtain ⟨V, hV, hVelocity⟩ := exists_velocityJetBounds
  obtain ⟨aNorm, haNorm, hNorm⟩ := exists_parent_seed_genericSwitch_ampSeminorm_le V hV
  choose seedCost hCost hSeedBound using hNorm
  obtain ⟨aBounds, b₀, _, hb₀, hBounds⟩ := exists_paper_hierarchy_depth
  obtain ⟨Clevel, Ctotal, hClevel, hCtotal, hMain⟩ := hBounds seedCost hCost
  obtain ⟨aSeed, _, hSeed⟩ := exists_localizedSeed
  let a₀ := max aSeed (max aNorm aBounds)
  refine ⟨a₀, b₀, ?_, hb₀, Clevel, Ctotal, hClevel, hCtotal, ?_⟩
  · exact haNorm.trans ((le_max_left aNorm aBounds).trans (le_max_right aSeed _))
  intro U X p T t₀ D freq hT k center d data hOdd hOddRes hp hpper ht₀ htT
    a ha ℓ h L γ M κ hCarrier hCenter hγle hsmall hγ hpos
  have haSeed : aSeed ≤ a := (le_max_left aSeed _).trans ha
  have haNorm' : aNorm ≤ a := ((le_max_left aNorm aBounds).trans (le_max_right aSeed _)).trans ha
  have haBounds : aBounds ≤ a := ((le_max_right aNorm aBounds).trans (le_max_right aSeed _)).trans ha
  obtain ⟨Cseed, w, reg, hAmp⟩ := hSeed (r := 0) data hOdd ht₀ htT le_rfl a haSeed hCarrier hCenter
  refine ⟨Cseed, w, reg, hAmp, ?_⟩
  intro χ depth hDepth
  have hD := one_le_two.trans data.scale_ge_two
  have hDpos := zero_lt_one.trans_le hD
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hRadius : ℓ ≤ (D ^ aNorm)⁻¹ :=
    inv_anti₀ (pow_pos hDpos _) (pow_le_pow_right₀ hD haNorm')
  have hVel := hVelocity data
  let leading := PhysicalLeadingInput.ofPaperCutoff d w reg χ data.flow data.velocity_smooth
    data.velocity_periodic hOdd hAmp
  obtain ⟨b, hLeading⟩ := exists_physicalApproximationData d data.time_le_one data.flow
    data.velocity_smooth hp data.velocity_periodic hpper hOdd hOddRes leading depth
  have hInactive : b.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) := by
    rw [hLeading]
    exact PhysicalLeadingInput.ofPaperCutoff_inactive d w reg χ data.flow data.velocity_smooth
      data.velocity_periodic hOdd hAmp (isClosed_tsupport _) (subset_tsupport _)
  have hRelay : b.LeadingRelayData :=
    PhysicalLeadingInput.ofPaperCutoff_relay d w reg χ data.flow data.velocity_smooth
      data.velocity_periodic hOdd hAmp b hLeading
  have hLeadNorm (m : ℕ) :
      amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos b.leading.output.V +
        freq * amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos b.leading.output.p ≤
          seedCost m * D ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1 := by
    have hVC (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (hx : x ∈ centeredCell) (s : ℝ) :=
      SeedOn.genericLeading_cell_eval reg k χ ⟨ht₀.trans ht.1, ht.2⟩ hx s
    have hPC (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (hx : x ∈ centeredCell) (s : ℝ) :=
      SeedOn.genericPressure_cell_eval reg k χ ⟨ht₀.trans ht.1, ht.2⟩ hx s
    have hNorm := hSeedBound m data.time_le_one data.scale_ge_two hℓ hRadius data.frequency_ge_one
      hCarrier data.flow data.velocity_smooth data.velocity_periodic data.deformation_le
      data.inverse_deformation_le hVel hCenter w reg χ.value
      (SeedOn.genericLeading reg k χ) (SeedOn.genericPressure reg k χ)
      (fun t ht => χ.abs_le_one ⟨ht₀.trans ht.1, ht.2⟩) hVC hPC
    rw [hLeading]
    change amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos (SeedOn.genericLeading reg k χ) +
      freq * amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos (SeedOn.genericPressure reg k χ) ≤ _
    have he : hierarchyOscExponent 1 = -5 / 4 := by norm_num [hierarchyOscExponent]
    simpa only [he] using hNorm
  exact ⟨b, hLeading, fun n => hMain data a haBounds n hDepth b hRelay
    ht₀ htT hCarrier hCenter hInactive hγ hpos hγle hLeadNorm hsmall⟩

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
