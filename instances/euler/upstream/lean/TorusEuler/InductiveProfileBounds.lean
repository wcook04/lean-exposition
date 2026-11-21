import TorusEuler.HierarchySelectedRecurrence
import TorusEuler.HierarchySelectedDepthTail
import TorusEuler.HierarchyStageCoefficientCaps
import TorusEuler.HierarchyNormalizedTransverseBudget
import TorusEuler.InductiveStageMeanBounds
import TorusEuler.HierarchyParentResidualNorm
import TorusEuler.HierarchyFiniteOrderBudget

/-! Uniform bounds for the actual selected profile hierarchy on an inductive slab. -/

open Set
open scoped ContDiff

namespace TorusEuler.InductiveEulerStage.OnSlab

open HierarchyTwistedProfile
open HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

private theorem orderedParentPower_le {D A B : ℝ} {q r : ℕ}
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hAB : A ≤ B) (hqr : q ≤ r) :
    A * D ^ q ≤ B * D ^ r :=
  mul_le_mul hAB (pow_le_pow_right₀ hD hqr) (pow_nonneg (zero_le_one.trans hD) _) (hA.trans hAB)

private theorem actual_parentResidual_eq
    {P : InductiveEulerParameters} {j : ℕ} {activation T : ℝ}
    {parent : InductiveEulerStage P j activation} {hT : 0 < T} {k : Vec3}
    (d : parent.OnSlab hT k) {depth : ℕ}
    (cfg : PhysicalApproximationData d.geometry parent.pressure depth) :
    cfg.parentResidual = d.residualProfile := by
  apply HierarchyTwistedProfile.ext
  intro z hz
  rw [cfg.parentResidual_value z hz, d.residualProfile_value z hz, d.momentum_same z.1 hz.1]

set_option maxHeartbeats 8000000 in
/-- One absolute parent loss and one monotone order budget control the
selected physical recurrence, its retained levels, and the order-two tail.
The first and later leading waves enter through their actual seed estimate
and their exact activation relay identities. -/
theorem exists_inductiveProfileBounds :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∀ seedCost : ℕ → ℝ, (∀ m, 0 ≤ seedCost m) →
      ∃ K : ℕ → ℝ, (∀ H, 1 ≤ K H) ∧ Monotone K ∧
        ∀ {P : InductiveEulerParameters} {j : ℕ} {activation T t₀ : ℝ}
          {parent : InductiveEulerStage P j activation} {hT : 0 < T}
          {k : Vec3} {κ center : ℝ → Vec3}
          (d : parent.OnSlab hT k) (hBase : 1 ≤ P.frequency 0) (_hParent : 2 ≤ P.frequency j)
          (a : ℕ), a₀ ≤ a → ∀ (m : ℕ) {depth : ℕ}, 2 ≤ depth →
          ∀ (cfg : PhysicalApproximationData d.geometry parent.pressure depth)
            (_lead : LeadingRelayData cfg) (ht₀ : 0 ≤ t₀) (htT : t₀ < T),
          let D := P.frequency j ^ (9 : ℕ)
          let freq := P.frequency (j + 1)
          let ℓ := (D ^ a)⁻¹
          let h := freq ^ (-1 / 2 : ℝ)
          let L := D ^ (2 * a + b₀)
          let H := max m 3 + 3 * depth
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
          ‖κ t₀‖ = freq →
          k = (fderiv ℝ (parent.flow 0 t₀) (0 : Vec3)).adjoint (κ t₀) →
          LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (parent.velocity t) 0) κ center t₀ T D →
          cfg.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t),
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          (∀ r ≤ H,
            amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.V +
              freq * amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.p ≤
            seedCost r * D ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1) →
          L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          let s := actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch
            cfg.parentResidual freq
            (zero_le_one.trans (hBase.trans ((frequencySchedule_frequency_mono P.exponentParameter
              P.order P.frequency P.exponentParameter_ge hBase P.frequency_step) (Nat.zero_le (j + 1)))))
            ℓ h hT ht₀ htT.le γ hγ hpos
          let C := hierarchyLevelConstant depth (K H) depth
          HierarchyNormRecurrence s freq L (K H) depth H ∧
            (∀ r ≤ max m 3, ∀ i ∈ Finset.Icc 1 depth, HierarchyLevelBound s freq L C r i) ∧
            unweightedSeminorm False ℓ h 2 hT (cfg.operators.remainder cfg.profiles depth) ≤
              2 * K H * (C + 1) ^ 2 *
                (1 + ((hierarchyTailPairs depth 0).card : ℝ) + 2 * ((hierarchyTailPairs depth 1).card : ℝ)) *
                  freq ^ hierarchyOscExponent (depth + 1) := by
  obtain ⟨aT, CT, haT, hCT, hTrans⟩ := exists_normalizedPhysicalTransverseSolveBudget_of_stage
  obtain ⟨pM, aM, CM, hCM, hMean⟩ := exists_onSlab_meanSeminormBound
  obtain ⟨CR, hCR, hResidual⟩ := exists_residualProfile_unweightedSeminorm_bound
  obtain ⟨CC, hCC, hCaps⟩ := exists_stageCoefficientCaps
  obtain ⟨CL, hCL, hRelay⟩ := exists_stageRelayCoefficientBudgets
  let a₀ := max aT aM
  let b₀ := pM + 32
  refine ⟨a₀, b₀, haT.trans (le_max_left _ _), by dsimp [b₀]; omega, ?_⟩
  intro seedCost hSeedCost
  let completionCost (r : ℕ) := completionOrderConstant r * (2 * CL r) ^ 2
  let relayCost (r : ℕ) := waveRelayOrderConstant r * (2 * CL r) ^ 2
  let orderCost (r : ℕ) :=
    CT r + CM r + CR r + stageSourceCoefficientCost CC r + completionCost r + relayCost r + seedCost r
  let K (H : ℕ) := 1 + ∑ r ∈ Finset.range (H + 1), orderCost r
  have hCompletionCost (r : ℕ) : 0 ≤ completionCost r := by
    dsimp [completionCost, completionOrderConstant]
    positivity
  have hRelayCost (r : ℕ) : 0 ≤ relayCost r := by
    dsimp [relayCost, waveRelayOrderConstant]
    positivity
  have hOrderCost (r : ℕ) : 0 ≤ orderCost r :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hCT r) (hCM r))
      (hCR r)) (stageSourceCoefficientCost_nonneg CC hCC r)) (hCompletionCost r)) (hRelayCost r)) (hSeedCost r)
  have hK (H : ℕ) : 1 ≤ K H := le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => hOrderCost r)
  refine ⟨K, hK, ?_, ?_⟩
  · intro H H' hHH'
    exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.succ_le_succ hHH')) (fun r _ _ => hOrderCost r))
  intro P j activation T t₀ parent hT k κ center d hBase hParent a ha m depth hDepth cfg lead ht₀ htT
    D freq ℓ h L H γ hFreqValue hLaunch hCenter inactive hγ hpos hγle hSeed hsmall s C
  have haT' : aT ≤ a := (le_max_left _ _).trans ha
  have haM' : aM ≤ a := (le_max_right _ _).trans ha
  have ha₃₀ : 30 ≤ a := haT.trans haT'
  have hParent₁ : 1 ≤ P.frequency j := by linarith
  have hf : 1 ≤ freq := hBase.trans
    ((frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency P.exponentParameter_ge
      hBase P.frequency_step) (Nat.zero_le (j + 1)))
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  have hD : 1 ≤ D := one_le_pow₀ hParent₁
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hL : 1 ≤ L := one_le_pow₀ hD
  have hSquareExp : (15 + a) * 2 ≤ 2 * a + b₀ := by
    change (15 + a) * 2 ≤ 2 * a + (pM + 32)
    omega
  have hMeanExp : pM + 2 + 2 * a ≤ 2 * a + b₀ := by
    change pM + 2 + 2 * a ≤ 2 * a + (pM + 32)
    omega
  have hOscExp : 20 ≤ 2 * a + b₀ := by
    change 20 ≤ 2 * a + (pM + 32)
    omega
  have hH (r : ℕ) (hr : r ≤ H) :
      CT r ≤ K H ∧ CM r ≤ K H ∧ CR r ≤ K H ∧ stageSourceCoefficientCost CC r ≤ K H ∧
        completionCost r ≤ K H ∧ relayCost r ≤ K H ∧ seedCost r ≤ K H := by
    have ht : orderCost r ≤ K H :=
      (Finset.single_le_sum (fun i _ => hOrderCost i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))).trans
        (le_add_of_nonneg_left zero_le_one)
    have h₁ := hCT r
    have h₂ := hCM r
    have h₃ := hCR r
    have h₄ := stageSourceCoefficientCost_nonneg CC hCC r
    have h₅ := hCompletionCost r
    have h₆ := hRelayCost r
    have h₇ := hSeedCost r
    dsimp only [orderCost] at ht
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have ht₀T : t₀ ∈ Icc 0 T := ⟨ht₀, htT.le⟩
  have hCarrier : ‖labelWaveVector parent.flow 0 0 k t₀‖ = freq := by
    rw [← d.centerCovector_eq_labelWaveVector ht₀T hLaunch hCenter.covector ⟨le_rfl, htT.le⟩, hFreqValue]
  let caps := hCaps d cfg.time_le_one hParent₁ hfpos ht₀T hCarrier a (by omega)
  let rowCap (r : ℕ) := stageCoefficientOrderConstant CC r * D ^ (a + 1)
  let relayCap (r : ℕ) := 2 * CL r * D ^ (15 + a)
  have hRow (r : ℕ) (i : Fin 3) := caps.rowCap r i
  have hSource (r : ℕ) (hr : r ≤ H) :=
    caps.sourceCaps hD hfpos.le (by omega : 7 ≤ a)
      (b := 2 * a + b₀) (by dsimp [b₀]; omega) hCC r (hH r hr).2.2.2.1
  have hCoefficient (r : ℕ) := hRelay d cfg.time_le_one hParent₁ hfpos ht₀T hCarrier a
    (by omega : 16 ≤ a) (Icc_subset_Icc_left ht₀) r
  have hComplete (r : ℕ) (hr : r ≤ H) : completionOrderConstant r * relayCap r ^ 2 ≤ K H * L := by
    calc
      _ = completionCost r * D ^ ((15 + a) * 2) := by
        dsimp only [relayCap]
        rw [mul_pow, ← pow_mul]
        simp only [completionCost, mul_assoc]
      _ ≤ _ := orderedParentPower_le hD (hCompletionCost r) (hH r hr).2.2.2.2.1
        hSquareExp
  have hRelayCap (r : ℕ) (hr : r ≤ H) : waveRelayOrderConstant r * relayCap r ^ 2 ≤ K H * L := by
    calc
      _ = relayCost r * D ^ ((15 + a) * 2) := by
        dsimp only [relayCap]
        rw [mul_pow, ← pow_mul]
        simp only [relayCost, mul_assoc]
      _ ≤ _ := orderedParentPower_le hD (hRelayCost r) (hH r hr).2.2.2.2.2.1
        hSquareExp
  have hRes (r : ℕ) (hr : r ≤ H) :
      unweightedSeminorm False ℓ h r hT cfg.parentResidual ≤ K H * freq ^ hierarchyMeanExponent 2 := by
    rw [actual_parentResidual_eq d cfg]
    have hscale : ℓ * D ^ (6 : ℕ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide : 6 ≤ 7)) caps.label_pos.le).trans
        caps.label_scale
    have hq := hResidual d hBase cfg.time_le_one caps.label_pos.le (h := h) hscale r
    have he : hierarchyMeanExponent 2 = -5 / 2 := by norm_num [hierarchyMeanExponent]
    rw [he]
    exact hq.trans (mul_le_mul_of_nonneg_right (hH r hr).2.2.1 (Real.rpow_nonneg hfpos.le _))
  have hSeed' (r : ℕ) (hr : r ≤ H) :
      amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.V +
        freq * amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.p ≤
      K H * L * freq ^ hierarchyOscExponent 1 :=
    (hSeed r hr).trans (mul_le_mul_of_nonneg_right
      (orderedParentPower_le hD (hSeedCost r) (hH r hr).2.2.2.2.2.2 hOscExp)
      (Real.rpow_nonneg hfpos.le _))
  have hSolveMean (r : ℕ) (hr : r ≤ H) (F : HierarchyTwistedProfile T k Vec3)
      (hF : cfg.operators.average F = F) :
      unweightedSeminorm False ℓ h r hT (cfg.solvers.solveMean F hF).val.B ≤
        K H * L * unweightedSeminorm False ℓ h (r + 1) hT F := by
    have hv := hMean d cfg.time_le_one hParent a haM' h r F hF
    have he : P.frequency j ^ (9 * (pM + 2 + 2 * a)) = D ^ (pM + 2 + 2 * a) :=
      pow_mul (P.frequency j) 9 (pM + 2 + 2 * a)
    have hWidth : (P.frequency j ^ (9 * a))⁻¹ = ℓ :=
      congrArg (fun x : ℝ => x⁻¹) (pow_mul (P.frequency j) 9 a)
    change unweightedSeminorm False (P.frequency j ^ (9 * a))⁻¹ h r hT
        (cfg.solvers.solveMean F hF).val.B ≤
      CM r * P.frequency j ^ (9 * (pM + 2 + 2 * a)) *
        unweightedSeminorm False (P.frequency j ^ (9 * a))⁻¹ h (r + 1) hT F at hv
    rw [he, hWidth] at hv
    exact hv.trans (mul_le_mul_of_nonneg_right
      (orderedParentPower_le hD (hCM r) (hH r hr).2.1 hMeanExp) (apply_nonneg _ _))
  have hDepth₁ : 1 ≤ depth := by omega
  have hRadius : ℓ ≤ (D ^ aT)⁻¹ :=
    inv_anti₀ (pow_pos hDpos _) (pow_le_pow_right₀ hD haT')
  have hTransverse := hTrans (h := h) d hParent ht₀ htT caps.label_pos hRadius hfpos hFreqValue hLaunch
    hCenter cfg hDepth₁ inactive hγ hpos
  have hSolveOsc (r : ℕ) (hr : r ≤ H) (i : ℕ) (hi : i ∈ Finset.Icc 2 depth) :
      s.osc r i ≤ K H * L * s.oscSource r i :=
    (hTransverse r i hi).trans (mul_le_mul_of_nonneg_right
      (orderedParentPower_le hD (hCT r) (hH r hr).1 hOscExp)
      (s.nonneg r i).1)
  have hEnvelope := isClosed_tsupport (periodizeCentered (radialEnvelope ℓ))
  have hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (parent.velocity t) := fun t _ => parent.periodic_velocity t
  have hrec : HierarchyNormRecurrence s freq L (K H) depth H :=
    cfg.selectedNormRecurrence lead hDepth₁ d.deformationOn.flow d.smooth_velocity hper ht₀ htT.le
      hEnvelope inactive ℓ h caps.label_pos.ne' caps.phase_pos.ne' γ hγ hpos hγle hfpos
      (zero_le_one.trans hL) (zero_le_one.trans (hK H)) rowCap relayCap
      (fun r _ i => hRow r i)
      (fun r hr => (hSource r (Nat.le_of_succ_le hr)).1)
      (fun r hr => (hSource r (Nat.le_of_succ_le hr)).2)
      (fun r _ => hCoefficient r)
      (fun r hr => hComplete r (Nat.le_of_succ_le hr))
      (fun r hr => hRelayCap r (Nat.le_of_succ_le hr))
      (fun r hr => hRes r (Nat.le_of_succ_le hr)) hSeed'
      (fun r hr => hSolveMean r (Nat.le_of_succ_le hr)) hSolveOsc
  have hlevels := hierarchy_level_bounds_through_depth (m := max m 3) hrec hf hL (hK H) hsmall
  have hH₂ : 2 ≤ H := by dsimp [H]; omega
  have hRowCap₂ : 3 * hierarchyQuadraticConstant (Fin 4) 2 ^ 2 * rowCap 2 ≤ K H * L := by
    have hnonneg : 0 ≤ rowCap 2 := (apply_nonneg _ _).trans (hRow 2 0)
    exact (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans (hSource 2 hH₂).1
  have hFastCap₂ : hierarchyQuadraticConstant (Fin 4) 2 ^ 2 *
      unweightedSeminorm False ℓ h 2 hT (scaledPhaseCoefficientProfile h d.geometry.covector) ≤
      K H * L * freq ^ (3 / 2 : ℝ) := by
    refine (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans ?_
    simpa only [mul_assoc] using (hSource 2 hH₂).2
  have hC : 0 ≤ C :=
    zero_le_one.trans (hierarchyLevelConstant_one_le (P := depth) (zero_le_one.trans (hK H)) depth)
  refine ⟨hrec, hlevels, ?_⟩
  exact cfg.unweightedSeminorm_remainder_le hDepth d.deformationOn.flow (d.smooth_velocity.of_le (by simp))
    hper ℓ h caps.label_pos.ne' caps.phase_pos.ne' 2 hf hL (zero_le_one.trans (hK H)) hC
    hsmall ht₀ htT.le γ hγ hpos hγle hEnvelope inactive (hRow 2) hRowCap₂ hFastCap₂
    (hCoefficient 2) (hRelayCap 2 hH₂) (hlevels 3 (le_max_right _ _))

end

end TorusEuler.InductiveEulerStage.OnSlab
