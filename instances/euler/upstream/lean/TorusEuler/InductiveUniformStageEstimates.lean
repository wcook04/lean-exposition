import TorusEuler.InductiveScheduledConstruction
import TorusEuler.InductiveMeasuredStageReadout
import TorusEuler.InductiveProfileBounds
import TorusEuler.InductiveStagePressureBounds
import TorusEuler.InductiveStageResidualBounds
import TorusEuler.FirstWavePrimaryPressureBound

/-! The same quantitative estimates and cutoff used at every selected stage. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler

open HierarchyTwistedProfile InductiveEulerParameters InductiveEulerStage
open HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

/-- The remaining wave-specific estimates have fixed costs and parent
powers before the common stage schedule is chosen. -/
structure LaterPrimaryCosts where
  radiusFloor : ℕ
  pressureCost : ℝ
  pressurePower : ℕ → ℕ
  activationCost : ℝ
  pressure_nonneg : 0 ≤ pressureCost
  activation_nonneg : 0 ≤ activationCost
  pressure : ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
    {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), radiusFloor ≤ a →
    ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (d.approximation.leadingPressure t)) x v⟫_ℝ ≤
        (pressureCost * (P.frequency (n + 1) ^ (9 : ℕ)) ^ (pressurePower a) *
          P.frequency (n + 2) ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2
  activation : ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
    {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), radiusFloor ≤ a →
    ∀ t ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation), PhaseJetBound 2
      (d.centerWeight t * (activationCost * (P.frequency (n + 1) ^ (9 : ℕ)) ^ (a + 27) *
        P.frequency (n + 2) ^ (-5 / 4 : ℝ)))
      (scaledPhaseProfile d.radius d.width (activationPrimary (h := d.width) d.seed d.parent.geometry.inverse t))

set_option maxHeartbeats 5500000 in
/-- Choose the shared costs from the analytic estimates, and use the exact
first and later leading inputs to produce the two physical constructors. -/
theorem uniformPhysicalEstimates_of_laterPrimaryCosts (primary : LaterPrimaryCosts) : UniformPhysicalEstimates Unit := by
  intro strength Cenv aMin hStrength _
  obtain ⟨Nswitch, hNswitch, hSwitch⟩ := InductiveEulerTip.SelectedLaterInput.exists_centerWeight_switch_bound
    strength hStrength
  obtain ⟨seedFirst, hSeedFirst, hFirst⟩ := InductiveFirstWaveSelection.exists_leadingSeedCost
  obtain ⟨Aseed, seedLater, _, _, hLater⟩ := InductiveEulerTip.SelectedLaterInput.exists_leadingSeedCost
  obtain ⟨Cfirst, hCfirst, hFirstPressure⟩ := InductiveFirstWaveSelection.exists_leading_pressure_hessian_bound
  obtain ⟨aRec, bRec, haRec, _, hProfileSelect⟩ := OnSlab.exists_inductiveProfileBounds
  let a := max aRec (max aMin (max Aseed primary.radiusFloor))
  let r := 2 * a + bRec
  let eLead := max (2 * a) (primary.pressurePower a)
  let eRes := scheduledResidualParentExponent a (a + 27)
  let eVel := max a 1 + 1 + 6 * r
  let ePressure := stagePressureExponent a r eLead
  let power := max eVel (max eRes ePressure)
  let seedCost m := max (seedFirst m) (seedLater m)
  have hSeedCost m : 0 ≤ seedCost m := (hSeedFirst m).trans (le_max_left _ _)
  have haA : aRec ≤ a := le_max_left _ _
  have haMin : aMin ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have haSeed : Aseed ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have haPrimary : primary.radiusFloor ≤ a := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have ha₇ : 7 ≤ a := (by decide : 7 ≤ 30).trans (haRec.trans haA)
  obtain ⟨K, hK, _, hProfile⟩ := hProfileSelect seedCost hSeedCost
  have hK₀ (m : ℕ) : 0 ≤ K m := zero_le_one.trans (hK m)
  obtain ⟨coefficient, hCoefficient, hCaps⟩ := exists_stageCoefficientCaps
  obtain ⟨bernstein, _, hBernsteinBounds⟩ := exists_velocity_bernstein_bounds_through_depth
  obtain ⟨Kgeom, Kparent, hKgeom, hKparent, hPressureCaps⟩ := exists_stagePressureGeometryCaps
  obtain ⟨Ccutoff, Kcutoff, hCcutoff, hKcutoff, hCutoff⟩ := exists_inductiveCutoffBudget
  let Clead := max Cfirst primary.pressureCost
  have hClead : 0 ≤ Clead := hCfirst.trans (le_max_left _ _)
  let Clevel depth := scheduledVelocityLevelConstant K depth
  have hLevel₀ (depth : ℕ) : 0 ≤ Clevel depth :=
    zero_le_one.trans (hierarchyLevelConstant_one_le (hK₀ _) depth)
  let velCost depth := scheduledVelocityStepCost coefficient K depth
  let jetCost depth := 1 + 40 * profileFlowJetConstant coefficient depth (Clevel depth)
  let resCost depth := scheduledResidualStepCost coefficient K primary.activationCost depth
  let presCost depth := stagePressureCost depth Kgeom Kparent (Clevel depth) Clead
  let cost : StepCosts Unit :=
    { analytic := fun _ _ depth => scheduledVelocityParentCost bernstein depth
      cutoffTail := Kcutoff
      step := fun depth => velCost depth + jetCost depth + resCost depth + presCost depth
      mean := scheduledVelocityMeanCost coefficient K }
  have hVelNonneg depth : 0 ≤ velCost depth :=
    (scheduledVelocityCosts_nonneg hCoefficient hK₀ depth).1
  have hJetOne depth : 1 ≤ jetCost depth := by
    have hb := one_le_profileFlowJetConstant coefficient hCoefficient depth (hLevel₀ depth)
    dsimp [jetCost]
    linarith only [hb]
  have hResNonneg depth : 0 ≤ resCost depth := scheduledResidualStepCost_nonneg hK₀ primary.activation_nonneg depth
  have hPresNonneg depth : 0 ≤ presCost depth :=
    stagePressureCost_nonneg depth (zero_le_one.trans hKgeom) hKparent (hLevel₀ depth) hClead
  have hMajorizes depth : 1 ≤ cost.step depth ∧ velCost depth ≤ cost.step depth ∧
      jetCost depth ≤ cost.step depth ∧ resCost depth ≤ cost.step depth ∧ presCost depth ≤ cost.step depth := by
    dsimp only [cost]
    have hv := hVelNonneg depth
    have hj := hJetOne depth
    have hr := hResNonneg depth
    have hp := hPresNonneg depth
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have common {P : InductiveEulerParameters} {i : ℕ} {oldActivation activation : ℝ}
      {parent : InductiveEulerStage P i oldActivation} {k : Vec3} {hT : 0 < P.slab (i + 1) activation}
      {d : parent.OnSlab hT k} {b : PhysicalApproximationData d.geometry parent.pressure (P.stepDepth i)}
      (s : SelectedPhysicalStageSeed d b a seedCost) (properties : PhysicalApproximationProperties b)
      (hBase : 1 ≤ P.frequency 0)
      (num : P.StepNumericalBudget i a (profileFlowJetPower r) r power Ccutoff cost)
      (hLead : ∀ t ∈ Icc 0 (P.slab (i + 1) activation), ∀ x v : Vec3,
        ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
          (Clead * (P.frequency i ^ (9 : ℕ)) ^ eLead * P.frequency (i + 1) ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
      (hResidual : ∀
        (caps : StageCoefficientCaps d a (P.frequency i ^ (9 : ℕ))
          (((P.frequency i ^ (9 : ℕ)) ^ a)⁻¹) (P.frequency (i + 1) ^ (-1 / 2 : ℝ))
          (P.frequency (i + 1)) coefficient),
        unweightedSeminorm False (((P.frequency i ^ (9 : ℕ)) ^ a)⁻¹)
          (P.frequency (i + 1) ^ (-1 / 2 : ℝ)) 2 hT (b.operators.remainder b.profiles (P.stepDepth i)) ≤
          scheduledResidualTailCost K (P.stepDepth i) *
            P.frequency (i + 1) ^ hierarchyOscExponent (P.stepDepth i + 1) →
        ∀ t ∈ Icc 0 (P.slab (i + 1) activation),
          spatialHolderHalfNorm 1 (b.residual t) ≤ P.frequency (i + 2) ^ (-7 / 2 : ℝ)) :
      ∃ stage : ScheduledPhysicalStage parent b properties a, stage.symbol = dyadicMultiplierCutoff := by
    let depth := P.stepDepth i
    have hμ := one_le_two.trans num.parent_ge_two
    have hf := one_le_two.trans num.child_ge_two
    have hDepth : 2 ≤ depth := (le_max_left _ _).trans num.order_le_depth
    have hOrder : 3 ≤ depth + 1 := by omega
    have ht : activation ∈ Icc 0 (P.slab (i + 1) activation) := ⟨s.activation_nonneg, s.activation_lt.le⟩
    have cap := hCaps d b.time_le_one hμ (zero_lt_one.trans_le hf) ht s.label_covector_norm a ha₇
    have capP := hPressureCaps d b.time_le_one hμ (zero_lt_one.trans_le hf) ht s.label_covector_norm a ha₇
    obtain ⟨_, hLevelsRaw, hTailRaw⟩ := hProfile d hBase num.parent_ge_two a haA (depth + 1) hDepth
      b s.relay s.activation_nonneg s.activation_lt s.covector_norm s.carrier_eq s.center_wave
      s.leading_inactive s.weight_continuous s.weight_pos s.weight_le_one
      (fun j _ => s.seed_le j) num.recurrence_small
    have hLevels : ∀ m ≤ depth + 1, ∀ j ∈ Finset.Icc 1 depth,
        HierarchyLevelBound (s.measured (zero_le_two.trans num.child_ge_two))
          (P.frequency (i + 1)) ((P.frequency i ^ (9 : ℕ)) ^ r) (Clevel depth) m j := by
      simpa only [max_eq_left hOrder, Clevel, scheduledVelocityLevelConstant] using hLevelsRaw
    have hTailEq := scheduledResidualTailCost_eq_of_profileBounds K hDepth
    rw [hTailEq] at hTailRaw
    have hPress := potential_hessian_upper_of_actualStageLevels d b properties
      (by omega : 1 ≤ depth) capP hμ hf (hLevel₀ depth) hClead (isClosed_tsupport _)
      s.leading_inactive s.activation_nonneg s.activation_lt.le s.gamma s.weight_continuous
      s.weight_pos s.weight_le_one (fun m hm j hj =>
        hLevels m ((Finset.mem_Icc.mp hm).2.trans (by omega))
          j (Finset.mem_Icc.mpr ⟨(by decide : 1 ≤ 2).trans (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩))
      hLead ((le_max_right eRes ePressure).trans ((le_max_right eVel _).trans num.absolute_exponent))
      (hMajorizes depth).2.2.2.2
    have hCut := hCutoff b properties hDepth (one_le_pow₀ hf : 1 ≤ P.frequency (i + 1) ^ (5 : ℕ))
    exact s.exists_scheduledPhysicalStage_of_levels properties num hCoefficient hK cap
      (hBernsteinBounds parent hμ depth) ()
      (le_abs_self _) (hMajorizes depth).2.1 le_rfl (le_max_left _ _) (hMajorizes depth).2.2.1
      hLevels (hKcutoff _) hCcutoff hCut (hResidual cap hTailRaw)
      (fun t ht x v => by rw [← b.potential_eq properties ht]; exact hPress t ht x v)
  refine ⟨a, profileFlowJetPower r, r, power, Ccutoff, Nswitch, cost, haMin,
    fun depth => (hMajorizes depth).1, ?_, ?_⟩
  · intro P hN _ num d
    have hBase := hNswitch.le.trans hN
    have hD : 1 ≤ P.frequency 0 ^ (9 : ℕ) := one_le_pow₀ hBase
    let s : SelectedPhysicalStageSeed (activation := 0) d.onSlab d.approximation a seedCost :=
      { center := d.origin.amplitude
        covector := d.origin.covector
        activation_nonneg := le_rfl
        activation_lt := d.time_pos
        covector_norm := d.launch_covector_length
        carrier_eq := d.carrier_eq_at_activation
        carrier_le := by
          rw [d.launch_covector_norm]
          exact le_mul_of_one_le_left d.frequency_pos.le hD
        center_wave := d.centerWaveOn
        weight_continuous := d.gamma_continuous
        weight_pos := d.gamma_pos
        weight_le_one := d.gamma_le_one
        leading_inactive := d.leading_inactive
        relay := d.leadingRelayData
        seed_le := fun m => (hFirst d m).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (Real.rpow_nonneg d.frequency_pos.le _)) }
    refine common s d.properties hBase num ?_ ?_
    · intro t ht x v
      refine (hFirstPressure P a d t ht x v).trans ?_
      have hPower := pow_le_pow_right₀ hD (le_max_left (2 * a) (primary.pressurePower a))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left Cfirst primary.pressureCost) hPower (by positivity) hClead)
        (Real.rpow_nonneg d.frequency_pos.le _)) (sq_nonneg _)
    · intro caps hTail t ht
      exact (OnSlab.residual_of_scheduledZeroSwitch d.onSlab d.approximation num caps
        hCoefficient hK₀ primary.activation_nonneg (hMajorizes _).2.2.2.1
        ((le_max_left eRes ePressure).trans (le_max_right eVel _))
        hTail d.leadingSwitch_eq_zero d.completionSwitch_eq_zero t ht).2
  · intro P n hLife tip _ hN hStrengthP num d
    have hBase := hNswitch.le.trans hN
    have hD : 1 ≤ P.frequency (n + 1) ^ (9 : ℕ) := one_le_two.trans d.parent_scale_ge_two
    have hf : 0 ≤ P.frequency (n + 2) := zero_le_one.trans d.child_frequency_ge_one
    let s : SelectedPhysicalStageSeed d.parent d.approximation a seedCost :=
      { center := d.selection.crossing.amplitude
        covector := d.selection.crossing.waveVector
        activation_nonneg := tip.next_activation_nonnegative
        activation_lt := d.regularity.start_lt_end
        covector_norm := d.launch_covector_norm
        carrier_eq := d.carrier_eq_launch_pullback
        carrier_le := d.carrier_bound
        center_wave := d.centerWaveOn
        weight_continuous := d.centerWeight_continuous
        weight_pos := d.centerWeight_pos
        weight_le_one := d.centerWeight_le_one
        leading_inactive := d.leading_inactive
        relay := d.leadingRelayData
        seed_le := fun m => (hLater d haSeed m).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (Real.rpow_nonneg hf _)) }
    refine common s d.properties hBase num ?_ ?_
    · intro t ht x v
      refine (primary.pressure d haPrimary t ht x v).trans ?_
      have hPower := pow_le_pow_right₀ hD (le_max_right (2 * a) (primary.pressurePower a))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_right Cfirst primary.pressureCost) hPower (by positivity) hClead)
        (Real.rpow_nonneg hf _)) (sq_nonneg _)
    · intro caps hTail t ht
      exact (OnSlab.residual_of_scheduledLaterSwitch d.parent d.approximation num caps
        hCoefficient hK₀ primary.activation_nonneg (hMajorizes _).2.2.2.1
        ((le_max_left eRes ePressure).trans (le_max_right eVel _)) hTail
        d.seed d.regularity d.seed_even rfl (primary.activation d haPrimary)
        (fun u _ => hSwitch d hN hStrengthP u) t ht).2

end

/-- The selected first and later estimates prove the main theorem on the basic schedule. -/
theorem theorem11_of_laterPrimaryCosts (primary : LaterPrimaryCosts) : Theorem11 :=
  theorem11_of_uniformPhysicalEstimates (uniformPhysicalEstimates_of_laterPrimaryCosts primary)

end TorusEuler
