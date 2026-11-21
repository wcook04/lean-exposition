import TorusEuler.InductiveLaterWaveSelection
import TorusEuler.ScheduledPhysicalStage
import TorusEuler.HierarchyCenterWeight
import TorusEuler.HierarchySelectedLinearEstimates
import TorusEuler.HierarchyInductiveTransverseBudget
import TorusEuler.InductiveWaveSwitchBound
import TorusEuler.ParentSeedJetBudgets

/-! Closing the later stage using the measured bounds on its selected physical hierarchy. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.InductiveEulerTip.SelectedLaterInput

noncomputable section

open MovingWaveVector HierarchyTwistedProfile LocalizedAmplitude

variable {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
  {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a)

local notation "T₊" => P.slab (n + 2) tip.nextActivation
local notation "λ₊" => P.frequency (n + 2)

local notation "A₊" => Icc tip.nextActivation T₊

include d in
theorem child_frequency_ge_one : 1 ≤ λ₊ := by
  rw [P.frequency_step (n + 1)]
  exact one_le_pow₀ (one_le_two.trans d.parent_frequency_ge_two)

include d in
theorem launch_time_mem : tip.nextActivation ∈ Icc 0 T₊ :=
  ⟨tip.next_activation_nonnegative, d.regularity.start_lt_end.le⟩

/-- The selected center covector starts with the exact scheduled frequency. -/
theorem launch_covector_norm : ‖d.selection.crossing.waveVector tip.nextActivation‖ = λ₊ :=
  (d.selection.crossing.launch_geometry (zero_lt_one.trans_le d.child_frequency_ge_one)).2.1

/-- The carrier is the activation covector pulled back to the parent labels. -/
theorem carrier_eq_launch_pullback :
    d.carrier = (fderiv ℝ (tip.parent.flow 0 tip.nextActivation) (0 : Vec3)).adjoint
      (d.selection.crossing.waveVector tip.nextActivation) := rfl

/-- The same selected pair satisfies the center equations on the active slab. -/
theorem centerWaveOn : CenterWaveOn (fun t => fderiv ℝ (tip.parent.velocity t) 0)
    d.selection.crossing.waveVector d.selection.crossing.amplitude tip.nextActivation T₊
    (P.frequency (n + 1) ^ 9) := d.selection.center

/-- In label coordinates the central wave uses the actual transported covector of the same carrier. -/
theorem centerWaveOn_labels :
    CenterWaveOn (fun t => fderiv ℝ (tip.parent.velocity t) (tip.parent.flow 0 t 0))
      (fun t => labelWaveVector tip.parent.flow 0 0 d.carrier t)
      d.selection.crossing.amplitude tip.nextActivation T₊ (P.frequency (n + 1) ^ 9) :=
  d.parent.centerWaveOn_labelWaveVector d.launch_time_mem d.carrier_eq_launch_pullback d.centerWaveOn

/-- The transported covector also has the scheduled norm in the initial center label. -/
theorem label_launch_covector_norm : ‖labelWaveVector tip.parent.flow 0 0 d.carrier tip.nextActivation‖ = λ₊ := by
  rw [d.carrier_transport (show tip.nextActivation ∈ A₊ from ⟨le_rfl, d.launch_time_mem.2⟩),
    d.launch_covector_norm]

/-- The weight of the selected later wave in the measured hierarchy. -/
def centerWeight (t : ℝ) : ℝ := λ₊ ^ (3 / 4 : ℝ) * ‖d.selection.crossing.amplitude t‖

/-- The exact center amplitude obeys the prescribed peak on the active slab. -/
theorem center_amplitude_le_peak (t : ℝ) (ht : t ∈ A₊) :
    ‖d.selection.crossing.amplitude t‖ ≤ λ₊ ^ (-(3 / 4) : ℝ) := by
  have hSlab : d.window.physical.activeSlab d.selection.window = A₊ := by
    rw [PhysicalAmplification.activeSlab, d.selection.clock_eq]
  have hBound := d.selection.crossing.peak.2 ⟨t, hSlab.symm ▸ ht, rfl⟩
  simpa only [neg_div] using hBound

/-- The actual selected peak makes the central weight positive and at most one,
with a continuous derivative throughout the active slab. -/
theorem centerWeight_properties :
    ContinuousOn d.centerWeight A₊ ∧ (∀ t ∈ A₊, 0 < d.centerWeight t ∧ d.centerWeight t ≤ 1) ∧
      ∃ dg : ℝ → ℝ, ContinuousOn dg A₊ ∧ ∀ t ∈ A₊, HasDerivWithinAt d.centerWeight (dg t) A₊ t := by
  have hJoint := contDiffOn_spatialDerivative_of_joint_contDiff (n := 0)
    (uniqueDiffOn_Icc d.time_pos) (d.parent.smooth_velocity.of_le (by simp))
  have hM : ContinuousOn (fun t => fderiv ℝ (tip.parent.velocity t) (0 : Vec3)) A₊ :=
    hJoint.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun t ht => ⟨⟨tip.next_activation_nonnegative.trans ht.1,ht.2⟩,mem_univ _⟩)
  exact d.selection.center.normalizedWeight (zero_lt_one.trans_le d.child_frequency_ge_one)
    hM d.center_amplitude_le_peak

theorem centerWeight_continuous : ContinuousOn d.centerWeight A₊ := d.centerWeight_properties.1

theorem centerWeight_pos (t : ℝ) (ht : t ∈ A₊) : 0 < d.centerWeight t :=
  (d.centerWeight_properties.2.1 t ht).1

theorem centerWeight_le_one (t : ℝ) (ht : t ∈ A₊) : d.centerWeight t ≤ 1 :=
  (d.centerWeight_properties.2.1 t ht).2

/-- Normalization and completion identities for the actual level-one relay. -/
theorem leadingRelayData : PhysicalApproximationData.LeadingRelayData d.approximation := by
  refine ⟨d.leading_pressure_phaseMean, d.leadingSwitch_average, ?_, d.completionSwitch_eq_complete⟩
  intro t ht x s
  have hw := d.leadingSwitch_transverse (t,x,s) ⟨ht, mem_univ _⟩
  rw [d.parent.geometry.oscillation.covector_independent (t,x,0) ⟨ht, mem_univ _⟩ s] at hw
  exact hw

/-- After selecting a common initial threshold, the scheduled switch
estimate holds with the exact normalized center weight used by the norms. -/
theorem exists_centerWeight_switch_bound (Cstrength : ℝ) (hCstrength : 2 ≤ Cstrength) :
    ∃ N : ℝ, 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a),
        N ≤ P.frequency 0 → P.strengthConstant = Cstrength →
        ∀ t, |deriv (waveSwitch tip.nextActivation d.window.physical.rate) t| * d.centerWeight t ≤
          P.frequency (n + 1) * P.frequency (n + 3) ^ (-4 : ℝ) := by
  obtain ⟨N, hN, hBound⟩ := exists_inductiveEulerTip_scheduled_switch_bound Cstrength hCstrength
  refine ⟨N, hN, ?_⟩
  intro P n tip Cenv a d hBase hStrength t
  have h := hBound tip hBase hStrength d.window d.selection t
  have hWeight : 0 ≤ d.centerWeight t :=
    mul_nonneg (Real.rpow_nonneg (by
      rw [P.frequency_step (n + 1)]
      exact pow_nonneg (zero_le_two.trans d.parent_frequency_ge_two) _) _) (norm_nonneg _)
  change |deriv (waveSwitch tip.nextActivation d.window.physical.rate) t| * |d.centerWeight t| ≤ _ at h
  rwa [abs_of_nonneg hWeight] at h


/-- A common radius exponent meets every smaller inverse-power requirement. -/
theorem radius_le_inverse_power {j : ℕ} (hj : j ≤ a) :
    d.radius ≤ ((P.frequency (n + 1) ^ (9 : ℕ)) ^ j)⁻¹ := by
  have hD := one_le_two.trans d.parent_scale_ge_two
  exact inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) _) (pow_le_pow_right₀ hD hj)

set_option maxHeartbeats 900000 in
/-- The exact later seed has the level-one weighted norm used by the common
recurrence, at every fixed order and one common radius exponent. -/
theorem exists_leadingSeedCost :
    ∃ (A : ℕ) (cost : ℕ → ℝ), 30 ≤ A ∧ (∀ m, 0 ≤ cost m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), A ≤ a → ∀ m : ℕ,
        let h₀ := tip.next_activation_nonnegative
        let hT := d.regularity.start_lt_end.le
        let V := amplitudeSeminorm False d.radius d.width m d.time_pos h₀ hT
          d.centerWeight d.centerWeight_continuous d.centerWeight_pos d.leading.output.V
        let p := amplitudeSeminorm False d.radius d.width m d.time_pos h₀ hT
          d.centerWeight d.centerWeight_continuous d.centerWeight_pos d.leading.output.p
        V + P.frequency (n + 2) * p ≤ cost m * (P.frequency (n + 1) ^ (9 : ℕ)) ^ (20 : ℕ) *
          P.frequency (n + 2) ^ hierarchyOscExponent 1 := by
  obtain ⟨W, hW, hJets⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨A, hA, hSeedAll⟩ := exists_parent_seed_twistedLeading_ampSeminorm_le W hW
  choose cost hCost hSeed using hSeedAll
  refine ⟨A, cost, hA, hCost, ?_⟩
  intro P n tip Cenv a d ha m
  let T := P.slab (n + 2) tip.nextActivation
  let D := P.frequency (n + 1) ^ (9 : ℕ)
  have hParentOne : 1 ≤ P.frequency (n + 1) := one_le_two.trans d.parent_frequency_ge_two
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) : ‖fderiv ℝ (tip.parent.flow 0 t) x‖ ≤ D :=
    ((d.parent.deformationOn.bounds t ht).2.1 x).2.trans d.parent_frequency_le_scale
  have hG (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖fderiv ℝ (tip.parent.flow t 0) (tip.parent.flow 0 t x)‖ ≤ D :=
    ((d.parent.deformationOn.bounds t ht).2.2 (tip.parent.flow 0 t x)).2.trans d.parent_frequency_le_scale
  have hBound := hSeed m d.time_le_one d.parent_scale_ge_two d.regularity.envelope_pos (d.radius_le_inverse_power ha)
    d.child_frequency_ge_one d.label_launch_covector_norm d.parent.deformationOn.flow
    d.parent.smooth_velocity (fun t _ => tip.parent.periodic_velocity t) hF hG
    (fun q j hj hq t ht x => hJets tip.parent hParentOne q j hj hq t (d.parent.subset ht) x)
    d.centerWaveOn_labels d.seed d.regularity
  have hExponent : hierarchyOscExponent 1 = (-5 / 4 : ℝ) := by norm_num [hierarchyOscExponent]
  rw [hExponent]
  exact hBound

/-- The scheduled central remainder bound controls the operator error
of the actual approximate velocity at the rate required by T4. -/
theorem norm_centralError_le {Cstep : ℝ}
    (hStep : Cstep ≤ λ₊ ^ (1 / 32 : ℝ)) {t : ℝ}
    (hCenter : ‖fderiv ℝ (d.approximation.oscillationRemainder t) 0‖ +
      ‖fderiv ℝ (d.approximation.meanCorrection t) 0‖ ≤ Cstep * λ₊ ^ (-5 / 12 : ℝ)) :
    ‖d.centralError t‖ ≤ λ₊ ^ (-1 / 3 : ℝ) := by
  have hf := d.child_frequency_ge_one
  calc
    ‖d.centralError t‖ ≤ ‖fderiv ℝ (d.approximation.oscillationRemainder t) 0‖ +
        ‖fderiv ℝ (d.approximation.meanCorrection t) 0‖ := norm_add_le _ _
    _ ≤ Cstep * λ₊ ^ (-5 / 12 : ℝ) := hCenter
    _ ≤ λ₊ ^ (1 / 12 : ℝ) * λ₊ ^ (-5 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right (hStep.trans (Real.rpow_le_rpow_of_exponent_le hf (by norm_num))) (by positivity)
    _ = λ₊ ^ (-1 / 3 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hf)]
      norm_num

/-- The selected later wave, measured hierarchy, and actual Fourier cutoff
supply the next certified step of the same prefix. -/
theorem exists_inductiveEulerStep {hLife : P.LifetimeBounds}
    (prior : InductiveEulerPrefix P hLife n tip)
    (stage : ScheduledPhysicalStage tip.parent d.approximation d.properties a)
    (hLarge : Real.exp 4 ≤ P.frequency 0) (hStrength : 18 * Real.exp 3 ≤ P.strengthConstant) :
    ∃ step : InductiveEulerStep tip,
      step.child.velocity = stage.cutoff.velocity ∧ step.child.pressure = stage.cutoff.pressure ∧
      step.wave.oscillation = d.approximation.oscillation :=
  exists_inductiveEulerStep_of_actualHierarchy prior d.window d.selection d.approximation d.properties
    stage.cutoff stage.cutoffBounds stage.bounds hLarge hStrength stage.cutoff_nonneg stage.tail_nonneg
    stage.tail_le_parent stage.mean_le_parent stage.step_le_child stage.cutoff_le_next
    stage.parent_le_scale stage.radius_pos stage.jet_nonneg stage.radius_inv rfl stage.carrier_le
    stage.flow_exponent stage.flow_constant stage.jets d.oscillation_vanishes d.oscillation_support
    d.centralError (fun t ht => ⟨d.gradient_split t ht,
      d.norm_centralError_le stage.step_le_child (stage.center t ht)⟩)

end

end TorusEuler.InductiveEulerTip.SelectedLaterInput
