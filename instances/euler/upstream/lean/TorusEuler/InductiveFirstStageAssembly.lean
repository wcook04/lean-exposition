import TorusEuler.FirstWaveDerivativeBudgets
import TorusEuler.HierarchyCenterWeight
import TorusEuler.HierarchySelectedLinearEstimates
import TorusEuler.InductiveFirstWaveSelection
import TorusEuler.ScheduledPhysicalStage

/-! The initial physical wave and its normalized weight on the full first slab. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.InductiveFirstWaveSelection

open HierarchyTwistedProfile LocalizedAmplitude

noncomputable section

variable {P : InductiveEulerParameters} {a : ℕ} (d : InductiveFirstWaveSelection P a)

local notation "T" => P.slab 1 0
local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "parentScale" => P.frequency 0 ^ (9 : ℕ)

/-- The center solution uses the actual stationary parent's central gradient. -/
theorem centerWaveOn : CenterWaveOn (fun t => fderiv ℝ (d.parent.velocity t) 0)
    d.origin.covector d.origin.amplitude 0 T parentScale := by
  have hBase : 2 ≤ P.frequency 0 := (by norm_num : (2 : ℝ) ≤ 4).trans d.frequency_base_ge_four
  have hD : 2 ≤ parentScale := hBase.trans (le_self_pow₀ (one_le_two.trans hBase) (by decide : (9 : ℕ) ≠ 0))
  refine (firstWave_centerWaveOn d.origin d.frequency_pos d.tilt_small d.shear_small hD).congr_gradient ?_
  intro t _
  simp only [d.parent_velocity, stationaryShearGradient_origin]

theorem launch_covector_length : ‖d.origin.covector 0‖ = P.frequency 1 := by
  rw [d.launch_covector_initial, d.launch_covector_norm]

/-- The carrier equals the pullback of the actual central covector at activation. -/
theorem carrier_eq_at_activation :
    firstWaveLaunchCovector (P.frequency 1) =
      (fderiv ℝ (d.parent.flow 0 0) (0 : Vec3)).adjoint (d.origin.covector 0) := by
  have hFlow : d.parent.flow 0 0 = id := by
    funext x
    simp only [d.parent_flow, sub_self, stationaryShearFlow, zero_smul, add_zero, id_eq]
  rw [hFlow, fderiv_id, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    d.launch_covector_initial]

/-- The prescribed peak normalization fixes the first hierarchy's time weight. -/
def gamma (t : ℝ) : ℝ := P.frequency 1 ^ (3 / 4 : ℝ) * ‖d.origin.amplitude t‖

theorem gamma_continuous : ContinuousOn d.gamma I :=
  (HasDerivWithinAt.continuousOn d.origin.amplitude_equation).norm.const_mul _

theorem gamma_pos (t : ℝ) (ht : t ∈ I) : 0 < d.gamma t :=
  mul_pos (Real.rpow_pos_of_pos d.frequency_pos _)
    (norm_pos_iff.mpr (d.origin.transverse t ht).2.1)

theorem gamma_le_one (t : ℝ) (ht : t ∈ I) : d.gamma t ≤ 1 := by
  unfold gamma
  calc
    _ ≤ P.frequency 1 ^ (3 / 4 : ℝ) * P.frequency 1 ^ (-(3 / 4) : ℝ) :=
      mul_le_mul_of_nonneg_left (d.origin.norm_le_peak t ht) (Real.rpow_nonneg d.frequency_pos.le _)
    _ = 1 := by rw [← Real.rpow_add d.frequency_pos, add_neg_cancel, Real.rpow_zero]

theorem gamma_initial_lower : (1 / 2 : ℝ) ≤ d.gamma 0 := by
  have hStrength := (d.origin.initial_strength d.frequency_pos d.shear_small).1
  rw [d.launch_covector_initial, d.launch_covector_norm] at hStrength
  have hFreq : P.frequency 1 ^ (1 / 4 : ℝ) * P.frequency 1 ^ (3 / 4 : ℝ) =
      P.frequency 1 := by
    rw [← Real.rpow_add d.frequency_pos]
    norm_num
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos d.frequency_pos (1 / 4 : ℝ))).mp
  calc
    _ = P.frequency 1 ^ (1 / 4 : ℝ) / 2 := by ring
    _ ≤ P.frequency 1 * ‖d.origin.amplitude 0‖ := hStrength
    _ = _ := by rw [gamma, ← mul_assoc, hFreq]

theorem gamma_attains_one : ∃ t ∈ I, d.gamma t = 1 := by
  obtain ⟨t, ht, hPeak⟩ := d.origin.attains_peak
  refine ⟨t, ht, ?_⟩
  rw [gamma, hPeak, ← Real.rpow_add d.frequency_pos, add_neg_cancel, Real.rpow_zero]

/-- The weight has a continuous derivative on the closed first slab. -/
theorem gamma_hasContinuousDerivative : ∃ dγ : ℝ → ℝ,
    ContinuousOn dγ I ∧ ∀ t ∈ I, HasDerivWithinAt d.gamma (dγ t) I t := by
  have hGrad : ContinuousOn (fun t => fderiv ℝ (d.parent.velocity t) 0) I := by
    simp only [d.parent_velocity, stationaryShearGradient_origin]
    exact continuousOn_const
  exact (d.centerWaveOn.normalizedWeight d.frequency_pos hGrad d.origin.norm_le_peak).2.2

/-- The leading solution has the pressure and forcing normalizations needed
by the linear relay. Its two switches are zero because activation is at zero. -/
theorem leadingRelayData : PhysicalApproximationData.LeadingRelayData d.approximation := by
  refine ⟨d.leading_pressure_phaseMean_zero, ?_, ?_, d.completionSwitch_eq_selected⟩
  · change d.approximation.operators.average d.leading.leadingSwitch = 0
    rw [d.leadingSwitch_eq_zero, map_zero]
  · intro t _ x z
    change ⟪d.onSlab.geometry.covector.val.val.val (t, x, 0),
      d.leading.leadingSwitch.val.val.val (t, x, z)⟫_ℝ = 0
    rw [d.leadingSwitch_eq_zero]
    exact inner_zero_right _

/-- The actual leading velocity and pressure obey (5.25) at the common
envelope radius, phase width, and time weight. -/
theorem exists_leading_ampSeminorm_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : InductiveEulerParameters} {a : ℕ} (s : InductiveFirstWaveSelection P a),
      let V := amplitudeSeminorm False (radius P a) (width P) m s.time_pos le_rfl s.time_pos.le
        s.gamma s.gamma_continuous s.gamma_pos s.leading.output.V
      let p := amplitudeSeminorm False (radius P a) (width P) m s.time_pos le_rfl s.time_pos.le
        s.gamma s.gamma_continuous s.gamma_pos s.leading.output.p
      V + P.frequency 1 * p ≤ C * P.frequency 1 ^ (-5 / 4 : ℝ) := by
  obtain ⟨C, hC, hLeading⟩ := exists_firstWaveHierarchyLeading_ampSeminorm_le m
  refine ⟨C, hC, ?_⟩
  intro P a s
  exact hLeading s.origin s.tilt_small s.time_pos s.time_le_one s.frequency_ge_one
    s.radius_pos s.radius_cell

/-- The first seed budget has the form used by the common selected recurrence. -/
theorem exists_leadingSeedCost :
    ∃ cost : ℕ → ℝ, (∀ m, 0 ≤ cost m) ∧
      ∀ {P : InductiveEulerParameters} {a : ℕ} (s : InductiveFirstWaveSelection P a) (m : ℕ),
        let V := amplitudeSeminorm False (radius P a) (width P) m s.time_pos le_rfl s.time_pos.le
          s.gamma s.gamma_continuous s.gamma_pos s.leading.output.V
        let p := amplitudeSeminorm False (radius P a) (width P) m s.time_pos le_rfl s.time_pos.le
          s.gamma s.gamma_continuous s.gamma_pos s.leading.output.p
        V + P.frequency 1 * p ≤ cost m * (P.frequency 0 ^ (9 : ℕ)) ^ (20 : ℕ) *
          P.frequency 1 ^ hierarchyOscExponent 1 := by
  choose cost hCost hBound using exists_leading_ampSeminorm_bound
  refine ⟨cost, hCost, ?_⟩
  intro P a s m
  have hBase : 1 ≤ P.frequency 0 := (by norm_num : (1 : ℝ) ≤ 4).trans s.frequency_base_ge_four
  have hD : 1 ≤ (P.frequency 0 ^ (9 : ℕ)) ^ (20 : ℕ) := one_le_pow₀ (one_le_pow₀ hBase)
  have hExp : hierarchyOscExponent 1 = (-5 / 4 : ℝ) := by norm_num [hierarchyOscExponent]
  rw [hExp]
  exact (hBound m s).trans (mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (hCost m) hD) (Real.rpow_nonneg s.frequency_pos.le _))

/-- The actual higher oscillations are differentiable at the origin on the
full first slab, including the initial endpoint. -/
theorem oscillationRemainder_differentiableAt (t : ℝ) (ht : t ∈ I) :
    DifferentiableAt ℝ (d.approximation.oscillationRemainder t) 0 := by
  have hJoint := d.approximation.oscillationRemainder_smooth d.onSlab.deformationOn.flow
    d.onSlab.smooth_velocity (fun r _ => d.parent.periodic_velocity r)
  have hSlice : ContDiff ℝ ∞ (d.approximation.oscillationRemainder t) :=
    contDiffOn_univ.mp (hJoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  exact hSlice.differentiable (by simp) 0

/-- The cutoff and its estimates for the selected first hierarchy produce
the initial certified pair of stages. -/
theorem exists_base (hLife : P.LifetimeBounds)
    (q : ScheduledPhysicalStage (activation := 0) d.parent d.approximation d.properties a) :
    ∃ base : InductiveEulerBase P, base.first.velocity = q.cutoff.velocity ∧
      base.first.pressure = q.cutoff.pressure ∧ base.stationary = d.parent ∧
      base.wave.oscillation = d.approximation.oscillation := by
  have hBase : 2 ≤ P.frequency 0 := (by norm_num : (2 : ℝ) ≤ 4).trans d.frequency_base_ge_four
  exact exists_inductiveEulerBase_of_actualHierarchy
    (radius := radius P a) (D := parentScale) (ell := radius P a) (h := width P) (a := a)
    d.parent d.approximation d.properties q.cutoff d.origin hLife hBase
    q.cutoffBounds q.bounds q.cutoff_nonneg q.tail_nonneg q.tail_le_parent q.mean_le_parent
    q.step_le_child q.cutoff_le_next q.parent_le_scale q.radius_pos q.jet_nonneg q.radius_inv rfl
    q.carrier_le q.flow_exponent q.flow_constant q.jets rfl d.tilt_small d.gain_ge_one
    d.parent_velocity d.radius_pos d.radius_cell d.shear_small d.oscillation_support
    d.approximation.oscillationRemainder d.velocity_split d.oscillationRemainder_differentiableAt
    q.center

end

end TorusEuler.InductiveFirstWaveSelection
