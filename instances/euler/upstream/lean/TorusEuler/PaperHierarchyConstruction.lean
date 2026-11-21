import TorusEuler.PaperHierarchyDepthGeneral
import TorusEuler.PaperTruncatedHierarchySeed

/-! The finite hierarchy from the prescribed central wave in Theorem 5.6. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open LocalizedAmplitude
open PhysicalApproximationData

/-- Theorem 5.6 constructs the actual hierarchy from a truncated parent and
its prescribed central wave. At each depth one selected expansion works
at every order, with constants uniform in the parent and carrier. -/
theorem exists_paper_hierarchy_depth_from_center :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∃ Clevel Ctotal : ℕ → ℕ → ℝ,
        (∀ n i, 0 ≤ Clevel n i) ∧ (∀ n i, 0 ≤ Ctotal n i) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
          {T t₀ D freq r : ℝ} {hT : 0 < T}
          {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          (hOdd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) →
          (∀ t ∈ Icc 0 T, Function.Odd (momentumResidual (Icc 0 T) U p t)) →
          ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t)) →
          0 ≤ t₀ → t₀ < T → 0 ≤ r →
          ∀ (a : ℕ), a₀ ≤ a → ∀ {depth : ℕ}, 2 ≤ depth →
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
            (reg : w.HierarchyRegularity r h)
            (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
            (b : PhysicalApproximationData d p depth),
            b.leading = PhysicalLeadingInput.ofLaterWave d w reg data.flow data.velocity_smooth
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
  obtain ⟨aSeed, _, hSeed⟩ := exists_localizedSeed
  obtain ⟨aDepth, b₀, haDepth, hb₀, Clevel, Ctotal, hClevel, hCtotal, hDepthBounds⟩ :=
    exists_paper_hierarchy_depth_of_later_wave
  refine ⟨max aSeed aDepth, b₀, haDepth.trans (le_max_right _ _), hb₀,
    Clevel, Ctotal, hClevel, hCtotal, ?_⟩
  intro U X p T t₀ D freq r hT k center d data hOdd hOddRes hp hpper ht₀ htT hr
    a ha depth hDepth ℓ h L γ M κ hCarrier hCenter hγle hsmall hγ hpos
  obtain ⟨Cseed, w, reg, hAmp⟩ :=
    hSeed data hOdd ht₀ htT hr a ((le_max_left _ _).trans ha) hCarrier hCenter
  obtain ⟨b, hLeading, hLevels⟩ := hDepthBounds data hOdd hOddRes hp hpper
    a ((le_max_right _ _).trans ha) hDepth hCarrier hCenter w reg hAmp hγle hsmall
  exact ⟨Cseed, w, reg, hAmp, b, hLeading, hLevels⟩

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
