import TorusEuler.FirstPhysicalLeadingInput
import TorusEuler.InductivePhysicalApproximation
import TorusEuler.HierarchyTwistedSelectedRelay

/-! Selection of the stationary parent and its actual first physical wave. -/

open Set
open scoped InnerProductSpace Topology

namespace TorusEuler

open HierarchyTwistedProfile InductiveEulerParameters

noncomputable section

/-- The logarithmic gain sets the tilt of the stationary parent. -/
def InductiveEulerParameters.firstWaveTilt (P : InductiveEulerParameters) : ℝ :=
  couplingRatioOfGain (4 * Real.log (P.frequency 3))

/-- Data for the first wave on the actual restricted stationary parent slab. -/
structure InductiveFirstWaveSelection (P : InductiveEulerParameters) (a : ℕ) where
  exponent_ge : 6 ≤ a
  time_pos : 0 < P.slab 1 0
  time_le_one : P.slab 1 0 ≤ 1
  base_size : 1 + 4 * Real.pi ≤ P.frequency 0
  tilt_small : |P.firstWaveTilt| ≤ 1
  gain_ge_one : 1 ≤ 4 * Real.log (P.frequency 3)
  shear_small : P.slab 1 0 * ‖stationaryShearGradient P.firstWaveTilt‖ ≤ 1 / 8
  origin : FirstWaveOrigin P.firstWaveTilt (P.slab 1 0) (P.frequency 1)
  onSlab : (stationaryInductiveEulerStage P tilt_small base_size).OnSlab time_pos
    (firstWaveLaunchCovector (P.frequency 1))

namespace InductiveFirstWaveSelection

variable {P : InductiveEulerParameters} {a : ℕ} (d : InductiveFirstWaveSelection P a)

/-- The parent is the stationary stage with the scheduled tilt. -/
def parent : InductiveEulerStage P 0 0 :=
  stationaryInductiveEulerStage P d.tilt_small d.base_size

theorem parent_velocity : d.parent.velocity = fun _ => stationaryShear P.firstWaveTilt := by
  funext t x
  exact stationaryInductiveEulerStage_velocity P d.tilt_small d.base_size t x

theorem parent_flow : d.parent.flow = fun r t => stationaryShearFlow P.firstWaveTilt (t - r) :=
  rfl

theorem parent_pressure : d.parent.pressure = 0 :=
  rfl

include d in
theorem frequency_base_ge_four : 4 ≤ P.frequency 0 := by
  linarith only [d.base_size, Real.pi_gt_three]

include d in
theorem frequency_ge_one : 1 ≤ P.frequency 1 := by
  rw [P.frequency_step 0]
  exact one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 4).trans d.frequency_base_ge_four)

include d in
theorem frequency_pos : 0 < P.frequency 1 := zero_lt_one.trans_le d.frequency_ge_one

theorem launch_covector_initial : d.origin.covector 0 = firstWaveLaunchCovector (P.frequency 1) :=
  d.origin.covector_initial

include d in
theorem launch_covector_norm : ‖firstWaveLaunchCovector (P.frequency 1)‖ = P.frequency 1 := by
  simp [firstWaveLaunchCovector, norm_smul, EuclideanSpace.single, PiLp.norm_single,
    Real.norm_eq_abs, abs_of_pos d.frequency_pos]

/-- The first envelope radius at the parent power prescribed by the schedule. -/
def radius (P : InductiveEulerParameters) (a : ℕ) : ℝ :=
  ((P.frequency 0 ^ 9) ^ a)⁻¹

/-- The phase width at the child frequency. -/
def width (P : InductiveEulerParameters) : ℝ :=
  P.frequency 1 ^ (-1 / 2 : ℝ)

include d in
theorem radius_pos : 0 < radius P a :=
  inv_pos.mpr (pow_pos (pow_pos ((by norm_num : (0 : ℝ) < 4).trans_le d.frequency_base_ge_four) _) _)

include d in
theorem radius_eq_rpow : radius P a = (P.frequency 0 ^ 9) ^ (-(a : ℝ)) := by
  rw [Real.rpow_neg (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 4).trans d.frequency_base_ge_four) _),
    Real.rpow_natCast]
  rfl

include d in
theorem radius_le_inverse_power {j : ℕ} (hj : j ≤ a) :
    radius P a ≤ ((P.frequency 0 ^ 9) ^ j)⁻¹ := by
  have hD : 1 ≤ P.frequency 0 ^ 9 := one_le_pow₀
    ((by norm_num : (1 : ℝ) ≤ 4).trans d.frequency_base_ge_four)
  exact inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) _) (pow_le_pow_right₀ hD hj)

include d in
theorem radius_mul_parent_power {j : ℕ} (hj : j ≤ a) :
    radius P a * (P.frequency 0 ^ 9) ^ j ≤ 1 := by
  have hDpos : 0 < P.frequency 0 ^ 9 :=
    pow_pos ((by norm_num : (0 : ℝ) < 4).trans_le d.frequency_base_ge_four) _
  exact (mul_le_mul_of_nonneg_right (d.radius_le_inverse_power hj) (pow_nonneg hDpos.le _)).trans_eq
    (inv_mul_cancel₀ (pow_ne_zero _ hDpos.ne'))

include d in
theorem radius_cell : 2 * radius P a < 1 / 2 := by
  have hD : 4 ≤ P.frequency 0 ^ 9 :=
    d.frequency_base_ge_four.trans (le_self_pow₀
      ((by norm_num : (1 : ℝ) ≤ 4).trans d.frequency_base_ge_four) (by decide : (9 : ℕ) ≠ 0))
  have hR : radius P a ≤ ((4 : ℝ) ^ 2)⁻¹ :=
    (d.radius_le_inverse_power (by have ha := d.exponent_ge; omega)).trans
      (inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hD 2))
  linarith

include d in
theorem width_pos : 0 < width P := Real.rpow_pos_of_pos d.frequency_pos _

include d in
theorem width_le_one : width P ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos d.frequency_ge_one (by norm_num)

/-- The first typed input uses the same origin scale, radius, and width
in its velocity and pressure. Both switch sources are zero. -/
def leading : PhysicalLeadingInput d.onSlab.geometry :=
  d.onSlab.geometry.firstPhysicalLeadingInput d.parent_velocity d.parent_flow d.origin.scale
    d.frequency_pos.ne' d.radius_pos d.radius_cell d.width_pos d.width_le_one

theorem leading_inactive :
    d.leading.Inactive 0 (tsupport (periodizeCentered (radialEnvelope (radius P a)))) :=
  d.onSlab.geometry.firstPhysicalLeadingInput_inactive d.parent_velocity d.parent_flow d.origin.scale
    d.frequency_pos.ne' d.radius_pos d.radius_cell d.width_pos d.width_le_one subset_closure

/-- The hierarchy is solved to the depth required for the first cutoff. -/
def depth (P : InductiveEulerParameters) : ℕ :=
  6 * frequencyExponent P.exponentParameter (P.order 2)

theorem depth_ge_two (P : InductiveEulerParameters) : 2 ≤ depth P := by
  have hExponent : 0 < frequencyExponent P.exponentParameter (P.order 2) := by
    unfold frequencyExponent
    exact Nat.mul_pos (Nat.mul_pos (by decide) (zero_lt_one.trans_le P.exponentParameter_ge))
      (Nat.succ_pos _)
  unfold depth
  omega

/-- Select the physical hierarchy over this exact leading wave and parent. -/
def approximation : PhysicalApproximationData d.onSlab.geometry d.parent.pressure (depth P) :=
  d.onSlab.physicalApproximationData d.time_le_one d.leading (depth P)

theorem properties : PhysicalApproximationProperties d.approximation :=
  d.onSlab.physicalApproximationProperties d.time_le_one d.leading (depth_ge_two P)

theorem oscillation_support (t : ℝ) (ht : t ∈ Icc 0 (P.slab 1 0)) (x : Vec3)
    (hOsc : d.approximation.oscillation t x ≠ 0) :
    ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency 0)⁻¹ := by
  have hRadius := d.radius_le_inverse_power (j := 3) (by have ha := d.exponent_ge; omega)
  have hF : P.frequency 0 ≤ P.frequency 0 ^ 9 :=
    le_self_pow₀ ((by norm_num : (1 : ℝ) ≤ 4).trans d.frequency_base_ge_four)
      (by decide : (9 : ℕ) ≠ 0)
  exact d.onSlab.physicalApproximation_oscillation_support d.time_le_one d.leading
    ((by decide : 1 ≤ 2).trans (depth_ge_two P)) d.radius_pos
    ((by norm_num : (2 : ℝ) ≤ 4).trans d.frequency_base_ge_four)
    hF hRadius d.leading_inactive t ht x hOsc

theorem velocity_split (t : ℝ) (ht : t ∈ Icc 0 (P.slab 1 0)) :
    d.approximation.velocity t = stationaryShear P.firstWaveTilt +
      localizedTransportedProfile (fun u => stationaryShearFlow P.firstWaveTilt (-u))
        (firstWaveLaunchCovector (P.frequency 1))
        (firstWaveLeadingProfile P.firstWaveTilt d.origin.scale (radius P a) (width P)) t +
      d.approximation.oscillationRemainder t + d.approximation.meanCorrection t :=
  PhysicalApproximationData.velocity_eq_first_leading d.onSlab.geometry
    d.parent_velocity d.parent_flow d.origin.scale d.frequency_pos.ne'
    d.radius_pos d.radius_cell d.width_pos d.width_le_one d.approximation
    ((by decide : 1 ≤ 2).trans (depth_ge_two P)) rfl ht

/-- The phase pressure remains mean zero after the lattice phase shift. -/
theorem leading_pressure_phaseMean_zero (t : ℝ) (ht : t ∈ Icc 0 (P.slab 1 0))
    (x : Vec3) : phaseMean (fun z => d.leading.output.p.val.val.val (t, x, z)) = 0 := by
  let a₀ := centeredLabel x
  let k := firstWaveLaunchCovector (P.frequency 1)
  let b := -⟪k, x⟫_ℝ + ⟪k, a₀⟫_ℝ
  let f := firstWaveLeadingPressureProfile P.firstWaveTilt d.origin.scale (P.frequency 1)
    (radius P a) (width P) t a₀
  let c := -wavePressureCoefficient (radialEnvelope (radius P a) a₀)
    (firstWaveTransportedCovector P.firstWaveTilt (P.frequency 1) t a₀)
    (firstWaveSmoothSeed P.firstWaveTilt d.origin.scale t a₀)
    (firstWaveMaterialGradient P.firstWaveTilt a₀)
  have hf : f = fun z => c • wavePressurePrimitive (width P) z := by
    unfold f c
    rw [firstWaveLeadingPressureProfile_eq_phasePressure]
    change oscillatoryPhasePressure _ _ (fun _ => 0)
      (fun z => (radialEnvelope (radius P a) a₀ * waveProfile (width P) z) •
        firstWaveSmoothSeed P.firstWaveTilt d.origin.scale t a₀) = _
    exact oscillatoryPhasePressure_primary_eq _ _ _ _ _
  have hper : Function.Periodic f 1 := by
    rw [hf]
    exact fun z => congrArg (c • ·) (periodic_wavePressurePrimitive d.width_pos d.width_le_one z)
  have hvalue : (fun z => d.leading.output.p.val.val.val (t, x, z)) = fun z => f (z + b) := by
    funext z
    change (firstWaveHierarchyLeadingPressure P.firstWaveTilt d.origin.scale d.frequency_pos.ne'
      d.radius_pos d.radius_cell d.width_pos d.width_le_one).val.val.val (t, x, z) = _
    rw [firstWaveHierarchyLeadingPressure_eval _ _ d.frequency_pos.ne' d.radius_pos d.radius_cell
      d.width_pos d.width_le_one ⟨ht, mem_univ _⟩]
    unfold phaseTwistedPeriodizeCentered f
    congr 1
    simp only [b, k, a₀, sub_eq_add_neg, add_assoc]
  rw [hvalue, phaseMean_translate_periodic hper, hf, phaseMean_const_smul,
    phaseMean_wavePressurePrimitive d.width_pos d.width_le_one, smul_zero]

@[simp] theorem leadingSwitch_eq_zero : d.leading.leadingSwitch = 0 := rfl

@[simp] theorem completionSwitch_eq_zero : d.leading.completionSwitch = 0 := rfl

/-- The first wave uses the physical completion of its zero activation force. -/
theorem completionSwitch_eq_selected :
    d.leading.completionSwitch = d.approximation.solvers.complete d.leading.leadingSwitch := by
  let g := d.onSlab.geometry
  change 0 = complete d.time_pos g.inverse g.covector
    g.oscillation.covector_independent g.oscillation.covector_ne_zero 0
  exact (complete_zero_of_phaseIndependent d.time_pos g.inverse g.covector
    g.mean.inverse_independent g.oscillation.covector_independent g.oscillation.covector_ne_zero).symm

end InductiveFirstWaveSelection

/-- A single base-frequency threshold selects the first origin, geometry,
and physical leading input at any prescribed envelope exponent. -/
theorem exists_inductiveFirstWaveSelection_threshold :
    ∃ N : ℝ, 4 ≤ N ∧ ∀ (P : InductiveEulerParameters), N ≤ P.frequency 0 →
      P.LifetimeBounds → ∀ a : ℕ, 6 ≤ a → Nonempty (InductiveFirstWaveSelection P a) := by
  obtain ⟨Ngeom, hNgeom, hGeometry⟩ := InductiveEulerStage.exists_onSlab_threshold
  let N := max Ngeom (max (1 + 4 * Real.pi) (max (Real.exp 1) ((64 * Real.pi) ^ (16 : ℕ))))
  refine ⟨N, hNgeom.trans (le_max_left _ _), ?_⟩
  intro P hN hLife a ha
  have hNgeom' : Ngeom ≤ P.frequency 0 := (le_max_left _ _).trans hN
  have hBase : 1 + 4 * Real.pi ≤ P.frequency 0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hExp : Real.exp 1 ≤ P.frequency 0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hLarge : (64 * Real.pi) ^ (16 : ℕ) ≤ P.frequency 0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (by linarith only [hBase, Real.pi_gt_three]) P.frequency_step
  have hGain : 1 ≤ 4 * Real.log (P.frequency 3) := by
    have hg := Real.log_le_log (Real.exp_pos 1) (hExp.trans (hMono (Nat.zero_le 3)))
    rw [Real.log_exp] at hg
    linarith
  have hTilt : |P.firstWaveTilt| ≤ 1 := by
    rw [firstWaveTilt, couplingRatioOfGain, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    exact (inv_le_one₀ (sq_pos_of_pos (zero_lt_one.trans_le hGain))).2 (one_le_pow₀ hGain)
  have hTime : P.slab 1 0 = 2 * inductionHalfLength P.frequency 0 := by
    rw [P.slab_succ, zero_add]
  have hT : 0 < P.slab 1 0 := by
    rw [hTime]
    exact mul_pos zero_lt_two (hLife.step 0).1
  have hT₁ : P.slab 1 0 ≤ 1 := by
    rw [hTime]
    linarith only [hLife.first]
  have hSmall := firstWave_stationaryShear_window_small hTilt hT.le hTime.le (hLife.step 0).2.1 hLarge
  have hf : 0 < P.frequency 1 :=
    (show 0 < P.frequency 0 by linarith only [hBase, Real.pi_gt_three]).trans_le (hMono (Nat.zero_le 1))
  have hk : firstWaveLaunchCovector (P.frequency 1) ≠ 0 :=
    smul_ne_zero hf.ne' (by simp [EuclideanSpace.single])
  obtain ⟨d⟩ := hGeometry P hNgeom' (stationaryInductiveEulerStage P hTilt hBase)
    hT (by simpa only [P.slab_zero] using hT₁) hk
  obtain ⟨w⟩ := firstWaveOrigin_exists (s := P.firstWaveTilt) hT.le hf
  exact ⟨⟨ha, hT, hT₁, hBase, hTilt, hGain, hSmall, w, d⟩⟩

end

end TorusEuler
