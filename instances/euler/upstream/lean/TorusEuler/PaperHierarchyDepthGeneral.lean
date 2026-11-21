import TorusEuler.PaperHierarchyDepth
import TorusEuler.PaperTruncatedHierarchyBounds
import TorusEuler.ParentSeedJetBudgets
import TorusEuler.HierarchyTwistedLeadingSwitch

/-! Theorem 5.6 for any physical truncated parent satisfying the §5 hypotheses. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open HierarchyTwistedProfile
open HierarchyTwistedProfile.PhysicalApproximationData

set_option maxHeartbeats 9000000 in
/-- Theorem 5.6 (cc:uf:hier:thm:depth) on the selected physical expansion.
One power of the parent scale controls every retained level and every
order of the two sums. No parent factor remains in the remainder estimate.
The level constants depend on the order and level, even when the same
profiles are constructed at a larger depth. -/
theorem exists_paper_hierarchy_depth :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∀ seedCost : ℕ → ℝ, (∀ m, 0 ≤ seedCost m) →
      ∃ Clevel Ctotal : ℕ → ℕ → ℝ,
        (∀ n i, 0 ≤ Clevel n i) ∧ (∀ n i, 0 ≤ Ctotal n i) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T t₀ D freq : ℝ}
          {hT : 0 < T} {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          ∀ (a : ℕ), a₀ ≤ a → ∀ (n : ℕ) {depth : ℕ}, 2 ≤ depth →
          ∀ (b : PhysicalApproximationData d p depth)
            (_lead : LeadingRelayData b) (ht₀ : 0 ≤ t₀) (htT : t₀ < T),
          let ℓ := (D ^ a)⁻¹
          let h := freq ^ (-1 / 2 : ℝ)
          let L := D ^ (2 * a + b₀)
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
          ‖labelWaveVector X 0 0 k t₀‖ = freq →
          LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
            (fun t => labelWaveVector X 0 0 k t) center t₀ T D →
          b.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t),
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          (∀ m,
            amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos b.leading.output.V +
              freq * amplitudeSeminorm False ℓ h m hT ht₀ htT.le γ hγ hpos b.leading.output.p ≤
            seedCost m * D ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1) →
          L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          let s := actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
            freq (zero_le_one.trans data.frequency_ge_one)
            ℓ h hT ht₀ htT.le γ hγ hpos
          let F := b.profiles.velocity depth
          let N := unweightedSeminorm False ℓ h n hT
          let W := amplitudeSeminorm False ℓ h n hT ht₀ htT.le γ hγ hpos
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
  obtain ⟨a₀, b₀, ha₀, hb₀, chooseK⟩ := exists_profileBounds_at_order
  refine ⟨a₀, b₀, ha₀, hb₀, fun seedCost hSeedCost => ?_⟩
  obtain ⟨K, hK, hAnalysis⟩ := chooseK seedCost hSeedCost
  let A (n p : ℕ) := hierarchyLevelConstant p (K (n + 1 + 3 * p)) p
  let Clevel (n i : ℕ) := 2 * hierarchyLevelConstant i (K (n + 3 * i)) i
  let Ctotal (n p : ℕ) := max (paperHierarchySumCost p (A n p))
    (paperHierarchyTailCost p (K (n + 1 + 3 * p)) (A n p))
  have hKA (n : ℕ) : 0 ≤ K n := zero_le_one.trans (hK n)
  have hA (n p : ℕ) : 0 ≤ A n p :=
    zero_le_one.trans (hierarchyLevelConstant_one_le (hKA _) _)
  have hCl (n i : ℕ) : 0 ≤ Clevel n i :=
    mul_nonneg zero_le_two (zero_le_one.trans (hierarchyLevelConstant_one_le (hKA _) _))
  have hCt (n p : ℕ) : 0 ≤ Ctotal n p :=
    (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (hA n p)).trans (le_max_left _ _)
  refine ⟨Clevel, Ctotal, hCl, hCt, ?_⟩
  intro U X p T t₀ D freq hT k center d data a ha n depth hDepth b lead ht₀ htT
    ℓ h L γ hFreqValue hCenter hInactive hγ hpos hγle hSeed hs s F N W
  have hf := data.frequency_ge_one
  have hL : 1 ≤ L := one_le_pow₀ (one_le_two.trans data.scale_ge_two)
  have hExp (u : ℝ) : 0 ≤ freq ^ u := Real.rpow_nonneg (zero_le_one.trans hf) u
  have hL₆ : 0 ≤ L ^ (6 : ℕ) := pow_nonneg (zero_le_one.trans hL) 6
  have hRec (H : ℕ) := hAnalysis data a ha H hDepth b lead ht₀ htT
    hFreqValue hCenter hInactive hγ hpos hγle (fun m _ => hSeed m) hs
  have hLevels (i : ℕ) (hi : i ∈ Finset.Icc 1 depth) :
      HierarchyLevelBound s freq L (A n depth) n i :=
    hierarchy_level_bounds_through_depth (m := n + 1)
      (hRec (n + 1 + 3 * depth)).1 hf hL (hK _) hs n (Nat.le_succ _) i hi
  have hSum := b.paper_hierarchy_sums (by omega : 1 ≤ depth) n hf hL (hA n depth)
    ht₀ htT.le γ hγ hpos hLevels
  refine ⟨fun i hi => ?_, hSum.1.trans ?_, hSum.2.trans ?_, ?_, fun i hi => ?_⟩
  · exact (hRec (n + 3 * i)).1.paper_level_bounds hf hL (hK _) hs hi le_rfl
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL₆) (hExp _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL₆) (hExp _)
  · exact ((hRec (n + 1 + 3 * depth)).2 n le_rfl).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hExp _))
  · have hCard : 1 ≤ ((Finset.Icc 1 depth).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hCost := le_mul_of_one_le_left (hA n depth) (show 1 ≤ 2 * ((Finset.Icc 1 depth).card : ℝ) by linarith)
    exact (hLevels i hi).mono hf hL (hCost.trans (le_max_left _ _))



open LocalizedAmplitude

set_option maxHeartbeats 4500000 in
/-- The actual switched later wave satisfies Theorem 5.6. The seed norm,
the two centered switch identities and the parent residual are supplied
by their physical constructions. -/
theorem exists_paper_hierarchy_depth_of_later_wave :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∃ Clevel Ctotal : ℕ → ℕ → ℝ,
        (∀ n i, 0 ≤ Clevel n i) ∧ (∀ n i, 0 ≤ Ctotal n i) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
          {T t₀ D freq Cseed r : ℝ} {hT : 0 < T}
          {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          (hOdd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) →
          (∀ t ∈ Icc 0 T, Function.Odd (momentumResidual (Icc 0 T) U p t)) →
          ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t)) →
          ∀ (a : ℕ), a₀ ≤ a → ∀ {depth : ℕ}, 2 ≤ depth →
          let ℓ := (D ^ a)⁻¹;
          let h := freq ^ (-1 / 2 : ℝ);
          let L := D ^ (2 * a + b₀);
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
          let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x);
          let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t;
          ‖κ t₀ 0‖ = freq →
          (hCenter : CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D) →
          ∀ (w : SeedOn M κ center t₀ T ℓ D Cseed) (reg : w.HierarchyRegularity r h)
            (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)),
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          let hγ : ContinuousOn γ (Icc t₀ T) :=
            (HasDerivWithinAt.continuousOn hCenter.amplitude).norm.const_mul _;
          let hpos (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
            mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le data.frequency_ge_one) _)
              (norm_pos_iff.mpr (hCenter.nonzero t ht).2.1);
          ∃ b : PhysicalApproximationData d p depth,
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
  obtain ⟨V, hV, hVelocity⟩ := exists_velocityJetBounds
  obtain ⟨aSeed, haSeed, hSeed⟩ := exists_parent_seed_twistedLeading_ampSeminorm_le V hV
  choose seedCost hCost hSeedBound using hSeed
  obtain ⟨aBounds, b₀, _, hb₀, hBounds⟩ := exists_paper_hierarchy_depth
  obtain ⟨Clevel, Ctotal, hClevel, hCtotal, hMain⟩ := hBounds seedCost hCost
  refine ⟨max aSeed aBounds, b₀, haSeed.trans (le_max_left _ _), hb₀,
    Clevel, Ctotal, hClevel, hCtotal, ?_⟩
  intro U X p T t₀ D freq Cseed r hT k center d data hOdd hOddRes hp hpper a ha depth hDepth
    ℓ h L γ M κ hCarrier hCenter w reg hAmp hγle hsmall hγ hpos
  have hD := one_le_two.trans data.scale_ge_two
  have hD₀ := zero_lt_one.trans_le hD
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hD₀ _)
  have hRadius : ℓ ≤ (D ^ aSeed)⁻¹ :=
    inv_anti₀ (pow_pos hD₀ _) (pow_le_pow_right₀ hD ((le_max_left _ _).trans ha))
  have hVel := hVelocity data
  let leading := PhysicalLeadingInput.ofLaterWave d w reg data.flow data.velocity_smooth
    data.velocity_periodic hOdd hAmp
  obtain ⟨b, hLeading⟩ := exists_physicalApproximationData d data.time_le_one data.flow
    data.velocity_smooth hp data.velocity_periodic hpper hOdd hOddRes leading depth
  have hInactive : b.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) := by
    rw [hLeading]
    exact PhysicalLeadingInput.ofLaterWave_inactive d w reg data.flow data.velocity_smooth
      data.velocity_periodic hOdd hAmp (isClosed_tsupport _) (subset_tsupport _)
  have hRelay : b.LeadingRelayData := by
    constructor
    · intro t ht x
      rw [hLeading]
      exact w.twistedPressure_phaseMean_zero reg k ht x
    · change profilePhaseAverage hT b.leading.leadingSwitch = 0
      rw [hLeading]
      exact w.twistedLeadingSwitch_average_zero reg k
    · intro t ht x s
      rw [hLeading]
      have hw := w.twistedLeadingSwitch_transverse reg d.covector d.covector_value (t,x,s)
        ⟨ht, mem_univ _⟩
      have he := d.oscillation.covector_independent (t,x,0) ⟨ht,mem_univ _⟩ s
      change d.covector.val.val.val (t,x,s) = d.covector.val.val.val (t,x,0) at he
      rw [he] at hw
      exact hw
    · rw [hLeading]
      rfl
  have hLeadNorm (m : ℕ) :
      amplitudeSeminorm False ℓ h m hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos b.leading.output.V +
        freq * amplitudeSeminorm False ℓ h m hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos
          b.leading.output.p ≤ seedCost m * D ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1 := by
    have hNorm := hSeedBound m data.time_le_one data.scale_ge_two hℓ hRadius data.frequency_ge_one
      hCarrier data.flow data.velocity_smooth data.velocity_periodic data.deformation_le
      data.inverse_deformation_le hVel hCenter w reg
    rw [hLeading]
    change amplitudeSeminorm False ℓ h m hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos
        (SeedOn.twistedLeading reg k) +
      freq * amplitudeSeminorm False ℓ h m hT reg.nonneg_start reg.start_lt_end.le γ hγ hpos
        (SeedOn.twistedPressure reg k) ≤ _
    have he : hierarchyOscExponent 1 = -5 / 4 := by norm_num [hierarchyOscExponent]
    simpa only [he] using hNorm
  exact ⟨b, hLeading, fun n => hMain data a ((le_max_right _ _).trans ha) n hDepth b hRelay
    reg.nonneg_start reg.start_lt_end hCarrier hCenter hInactive hγ hpos hγle hLeadNorm hsmall⟩

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
