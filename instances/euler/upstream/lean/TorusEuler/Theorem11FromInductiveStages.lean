import TorusEuler.InductionAmplificationSmallness
import TorusEuler.InductionBudget
import TorusEuler.InductionChildEstimates
import TorusEuler.InductiveActivationClock
import TorusEuler.InductiveVorticityBounds
import TorusEuler.OffOriginMomentumLimits
import TorusEuler.ParentVelocityEstimates
import TorusEuler.PeriodicEulerPressurePoisson
import TorusEuler.ScheduleGrowth

/-! From a compatible family of constructed stages in Theorem 7.1 to the
conclusion of Theorem 1.1. -/

open Filter MeasureTheory Metric Set UnitAddTorus
open scoped ContDiff ENNReal InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The schedule and constructed fields used by the final limit argument.
The estimates from (T1), (T2), (T4), and (7.4) are supplied for the same
velocity, residual, oscillation, and central-wave sequences. -/
structure InductiveEulerStages where
  exponentParameter : ℕ
  threshold : ℕ → ℝ
  order : ℕ → ℕ
  frequency : ℕ → ℝ
  exponentParameter_ge : 1 ≤ exponentParameter
  initial_order : order 1 = 1
  initial_threshold : threshold 1 ≤ frequency 0
  frequency_step : ∀ i, frequency (i + 1) = frequency i ^ frequencyExponent exponentParameter (order (i + 1))
  order_maximum : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ order (i + 1) + 1 ∧ threshold s ≤ frequency i} (order (i + 2))
  threshold_pos : ∀ s, 1 ≤ s → 0 < threshold s
  threshold_floor : ∀ s, 1 ≤ s →
    4 * (frequencyExponent exponentParameter (s + 1) : ℝ) ^ 3 ≤ Real.log (threshold s)
  activation : ℕ → ℝ
  slab : ℕ → ℝ
  activation_zero : activation 0 = 0
  first_activation : activation 1 = 0
  second_activation : activation 2 = 0
  slab_base : slab 0 = 1
  slab_step : ∀ j, slab (j + 1) = activation (j + 1) + 2 * inductionHalfLength frequency j
  activation_step : ∀ j, 0 ≤ activation (j + 2) - activation (j + 1) ∧
    activation (j + 2) - activation (j + 1) ≤ inductionHalfLength frequency j
  torusVelocity : ℕ → ℝ → C(Labels, Vec3)
  residual : ℕ → Velocity
  oscillation : ℕ → Velocity
  smooth : ∀ n, ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => torusVelocity n p.1 (toUnitTorus p.2))
    (Icc 0 (slab n) ×ˢ (univ : Set Vec3))
  odd : ∀ n t, t ∈ Icc 0 (slab n) → Function.Odd (fun x => torusVelocity n t (toUnitTorus x))
  divergence_free : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x,
    divergence (fun y => torusVelocity n t (toUnitTorus y)) x = 0
  velocity_bound : ∀ n t, t ∈ Icc 0 (slab n) → ‖torusVelocity n t‖ ≤ frequency n
  velocity_band : ∀ n t, t ∈ Icc 0 (slab n) → RealTorusFourierBand (2 * frequency n ^ 5) (torusVelocity n t)
  projected_residual : ∀ n t, t ∈ Icc 0 (slab n) →
    closedSlabLerayMomentum 0 (slab n) (fun s x => torusVelocity n s (toUnitTorus x)) t = residual n t
  residual_bound : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, ‖residual n t x‖ ≤ ((frequency (n + 1))⁻¹)^3
  oscillation_bound : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x, ‖oscillation (n + 1) t x‖ ≤ (frequency (n + 1))⁻¹
  correction_bound : ∀ n m, m ≤ order (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)),
    let v := (fun y => torusVelocity (n + 1) t (toUnitTorus y)) -
      (fun y => torusVelocity n t (toUnitTorus y)) - oscillation (n + 1) t
    SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (frequency (n + 1))⁻¹
  oscillation_vanishes : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), oscillation n t = 0
  oscillation_support : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x, oscillation (n + 1) t x ≠ 0 →
    ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (frequency n)⁻¹

namespace InductiveEulerStages

/-- Spatially periodic Euclidean lift of the stage velocities. -/
def velocity (s : InductiveEulerStages) (n : ℕ) : Velocity :=
  fun t x => s.torusVelocity n t (toUnitTorus x)

theorem periodic_velocity (s : InductiveEulerStages) (n : ℕ) (t : ℝ) :
    SpatiallyPeriodic (s.velocity n t) := by
  intro k x
  exact congrArg (s.torusVelocity n t) ((toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩)

private theorem correction_jet_bound (s : InductiveEulerStages)
    (n m : ℕ) (hm : m ≤ s.order (n + 1)) (t : ℝ) (ht : t ∈ Icc 0 (s.slab (n + 1))) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (s.velocity (n + 1) t - s.velocity n t - s.oscillation (n + 1) t) x‖ ≤
      (s.frequency (n + 1))⁻¹ := by
  have h := s.correction_bound n m hm t ht
  exact (norm_iteratedFDeriv_le_spatialHolderHalfNorm h.1 le_rfl x).trans h.2

private theorem frequency_mono (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) :
    Monotone s.frequency :=
  frequencySchedule_frequency_mono s.exponentParameter s.order s.frequency s.exponentParameter_ge
    (one_le_two.trans hinit) s.frequency_step

private theorem frequency_lower (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) (n : ℕ) :
    2 ≤ s.frequency n := hinit.trans (s.frequency_mono hinit (Nat.zero_le n))

private theorem frequency_gap (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) (n : ℕ) :
    s.frequency n ^ 288 ≤ s.frequency (n + 1) := by
  rw [s.frequency_step]
  exact pow_le_pow_right₀ (one_le_two.trans (s.frequency_lower hinit n))
    ((by decide : 288 ≤ 320).trans (by
      have hb := s.exponentParameter_ge
      unfold frequencyExponent
      exact (Nat.mul_le_mul_left 320 hb).trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos (s.order (n + 1))))))

theorem frequency_square_gap (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) (n : ℕ) :
    s.frequency n ^ 2 ≤ s.frequency (n + 1) :=
  (pow_le_pow_right₀ (one_le_two.trans (s.frequency_lower hinit n)) (by decide : 2 ≤ 288)).trans
    (s.frequency_gap hinit n)

private theorem frequency_tendsto (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) :
    Tendsto s.frequency atTop atTop :=
  frequencySchedule_frequency_tendsto_atTop s.exponentParameter s.order s.frequency s.exponentParameter_ge
    (one_lt_two.trans_le hinit) s.frequency_step

theorem order_tendsto (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) :
    Tendsto s.order atTop atTop :=
  frequencySchedule_order_tendsto_atTop s.threshold s.frequency s.order s.initial_order s.initial_threshold
    (s.frequency_mono hinit) (s.frequency_tendsto hinit) s.order_maximum

private theorem frequency_log_bound (s : InductiveEulerStages) (i : ℕ) :
    4 * Real.log (s.frequency (i + 3)) ≤ (Real.log (s.frequency i)) ^ 2 :=
  frequencySchedule_log_bound_of_maxima s.exponentParameter s.order s.threshold s.frequency
    (fun n => 4 * Real.log (s.frequency (n + 1))) s.exponentParameter_ge s.initial_order s.initial_threshold
    s.frequency_step (fun _ => rfl) s.order_maximum s.threshold_pos s.threshold_floor i

private theorem eventually_central_gradient_bound (s : InductiveEulerStages) (hinit : 2 ≤ s.frequency 0) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (s.slab n), ‖fderiv ℝ (s.velocity n t) 0‖ ≤ s.frequency n ^ 9 := by
  obtain ⟨K, _, hK⟩ := exists_bandBernsteinJetBounds
  filter_upwards [(s.frequency_tendsto hinit).eventually_ge_atTop (K 1)] with n hn t ht
  have hfreq : 1 ≤ s.frequency n := one_le_two.trans (s.frequency_lower hinit n)
  have hpos := zero_lt_one.trans_le hfreq
  have h := (hK (s.torusVelocity n t) (D := s.frequency n ^ 5) (A := s.frequency n)
    (pow_pos hpos _) hpos.le (s.velocity_bound n t ht) (fun k hk =>
      s.velocity_band n t ht k ((show 2 * s.frequency n ^ 5 ≤ 4 * s.frequency n ^ 5 by nlinarith [pow_nonneg hpos.le 5]).trans_lt hk))).2 1 0
  rw [norm_iteratedFDeriv_one, pow_one] at h
  calc
    ‖fderiv ℝ (s.velocity n t) 0‖ ≤ K 1 * s.frequency n * s.frequency n ^ 5 := h
    _ ≤ s.frequency n * s.frequency n * s.frequency n ^ 5 := by gcongr
    _ = s.frequency n ^ 7 := by ring
    _ ≤ s.frequency n ^ 9 := pow_le_pow_right₀ hfreq (by decide)

end InductiveEulerStages

open MovingWaveVector (PhysicalAmplification frame entry)

/-- The central data belonging to the same stages. At index `j` the
physical crossing selects wave `j + 2` over stage `j + 1`. -/
structure InductiveEulerCentralWaves (s : InductiveEulerStages) where
  waveVector : ℕ → ℝ → Vec3
  amplitude : ℕ → ℝ → Vec3
  cutoff : ℕ → ℝ → ℝ
  error : ℕ → ℝ → Vec3 →L[ℝ] Vec3
  strengthConstant : ℝ
  strengthConstant_ge : 2 ≤ strengthConstant
  gradient_split : ∀ j t, t ∈ Icc (s.activation (j + 1)) (s.slab (j + 1)) →
    fderiv ℝ (s.velocity (j + 1) t) 0 =
      fderiv ℝ (s.velocity j t) 0 +
        cutoff (j + 1) t • (innerSL ℝ (waveVector (j + 1) t)).smulRight (amplitude (j + 1) t) +
        error (j + 1) t
  error_bound : ∀ j t, t ∈ Icc (s.activation (j + 1)) (s.slab (j + 1)) →
    ‖error (j + 1) t‖ ≤ s.frequency (j + 1) ^ (-1 / 4 : ℝ)
  cutoff_complete : ∀ j t, t ∈ Icc (s.activation (j + 2)) (s.slab (j + 1)) → cutoff (j + 1) t = 1
  strength_at_crossing : ∀ j,
    strengthConstant⁻¹ * s.frequency (j + 1) ^ (1 / 4 : ℝ) ≤
      ‖waveVector (j + 1) (s.activation (j + 2))‖ * ‖amplitude (j + 1) (s.activation (j + 2))‖ ∧
    ‖waveVector (j + 1) (s.activation (j + 2))‖ * ‖amplitude (j + 1) (s.activation (j + 2))‖ ≤
      strengthConstant * s.frequency (j + 1) ^ (1 / 4 : ℝ) *
        (4 * Real.log (s.frequency (j + 3))) ^ 2
  coupling_at_crossing : ∀ j,
    let t := s.activation (j + 2)
    let ν := entry (frame (waveVector (j + 1)) (amplitude (j + 1)) t)
      (fderiv ℝ (s.velocity j t) 0) 0 1
    Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi
  comparisonConstant : ℕ
  comparisonConstant_ge : 240 ≤ comparisonConstant
  window : ℕ → ℝ
  physical : ∀ j, PhysicalAmplification (Icc (s.activation (j + 2)) (s.slab (j + 2))) (s.activation (j + 2))
  crossing : ∀ j, (physical j).GrowingCrossing (window j) (s.frequency (j + 2))
    (s.frequency (j + 2) ^ (-3 / 4 : ℝ)) (couplingRatioOfGain (4 * Real.log (s.frequency (j + 4))))
  physical_window : ∀ j, (physical j).clock (window j) = s.slab (j + 2)
  window_ge : ∀ j, 2 ≤ window j
  preceding_vector : ∀ j, (physical j).kp = waveVector (j + 1)
  preceding_amplitude : ∀ j, (physical j).ap = amplitude (j + 1)
  older_gradient : ∀ j t, t ∈ Icc (s.activation (j + 2)) (s.slab (j + 2)) →
    (physical j).B t = fderiv ℝ (s.velocity j t) 0
  preceding_error : ∀ j t, t ∈ Icc (s.activation (j + 2)) (s.slab (j + 2)) → (physical j).E t = error (j + 1) t
  current_vector : ∀ j, (crossing j).waveVector = waveVector (j + 2)
  current_amplitude : ∀ j, (crossing j).amplitude = amplitude (j + 2)
  crossing_time : ∀ j, (crossing j).crossing = s.activation (j + 3)
  prescribed_ratio : ∀ j, (physical j).ratio = couplingRatioOfGain (4 * Real.log (s.frequency (j + 3)))
  comparison_ratio : ∀ j, (comparisonConstant : ℝ) * (physical j).ratio ≤ 1
  comparison_error : ∀ j, (comparisonConstant : ℝ) * window j ^ comparisonConstant *
    (physical j).errorSize ≤ (physical j).ratio


/-- The base frequency bound makes the first endpoint interval shorter than the stationary slab. -/
theorem inductionHalfLength_zero_le_quarter {freq : ℕ → ℝ}
    (hbase : (4 : ℝ) ^ (16 : ℕ) ≤ freq 0)
    (hτ₀ : inductionHalfLength freq 0 ≤ freq 0 ^ (-1 / 16 : ℝ)) :
    inductionHalfLength freq 0 ≤ 1 / 4 := by
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : 0 < (4 : ℝ) ^ (16 : ℕ))
    hbase (by norm_num : (-1 / 16 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  norm_num at h
  rw [show (-1 / 16 : ℝ) = -(1 / 16) by ring] at hτ₀
  exact hτ₀.trans h

/-- With the paper's activation numbering, every endpoint problem fits inside its parent slab. -/
theorem frequencySchedule_endpointSlab_strict {freq activation slab : ℕ → ℝ}
    (hτ : ∀ j, 0 < inductionHalfLength freq j ∧ 4 * inductionHalfLength freq (j + 1) ≤ inductionHalfLength freq j)
    (hτ₀ : inductionHalfLength freq 0 ≤ 1 / 4) (h₁ : activation 1 = 0)
    (hstep : ∀ j, activation (j + 2) - activation (j + 1) ≤ inductionHalfLength freq j)
    (hslab₀ : slab 0 = 1)
    (hslab : ∀ j, slab (j + 1) = activation (j + 1) + 2 * inductionHalfLength freq j) :
    ∀ n, slab (n + 1) < slab n := by
  intro n
  cases n with
  | zero =>
    rw [hslab 0, h₁, hslab₀]
    linarith
  | succ j =>
    rw [hslab (j + 1), hslab j]
    change activation (j + 2) + 2 * inductionHalfLength freq (j + 1) < _
    linarith only [hstep j, (hτ j).1, (hτ j).2]

/-- The actual half-length bounds and successive crossings give a positive limit
strictly before every stage endpoint, with the frozen indexing `t₁ = t₂ = 0`. -/
theorem frequencySchedule_commonLifetime_of_halfLength_bounds {freq activation slab : ℕ → ℝ}
    (hbase : (4 : ℝ) ^ (16 : ℕ) ≤ freq 0)
    (hτ : ∀ j, 0 < inductionHalfLength freq j ∧
      inductionHalfLength freq j ≤ freq j ^ (-1 / 16 : ℝ) ∧
      4 * inductionHalfLength freq (j + 1) ≤ inductionHalfLength freq j)
    (h₀ : activation 0 = 0) (h₁ : activation 1 = 0) (h₂ : activation 2 = 0)
    (hstep : ∀ j, activation (j + 2) - activation (j + 1) ≤ inductionHalfLength freq j)
    (hstrict : ∀ j, activation (j + 2) < activation (j + 3))
    (hslab₀ : slab 0 = 1)
    (hslab : ∀ j, slab (j + 1) = activation (j + 1) + 2 * inductionHalfLength freq j) :
    ∃ T : ℝ, 0 < T ∧ Tendsto activation atTop (𝓝 T) ∧
      (∀ n, activation n < T) ∧ (∀ n, T < slab n) ∧
      (∀ j, T - activation (j + 1) ≤ (4 / 3 : ℝ) * inductionHalfLength freq j) := by
  let t := fun j => activation (j + 1)
  have hstep' (j : ℕ) : 0 ≤ t (j + 1) - t j ∧ t (j + 1) - t j ≤ inductionHalfLength freq j := by
    change 0 ≤ activation (j + 2) - activation (j + 1) ∧ _
    refine ⟨?_, hstep j⟩
    cases j with
    | zero => simpa only [Nat.zero_add, h₁, h₂, sub_self] using (le_rfl : (0 : ℝ) ≤ 0)
    | succ j => exact sub_nonneg.mpr (hstrict j).le
  have hLater (j : ℕ) : ∃ k, t j < t k := by
    refine ⟨j + 2, (sub_nonneg.mp (hstep' j).1).trans_lt ?_⟩
    exact hstrict j
  obtain ⟨T, hT, hlim, hTj⟩ := activationTimes_converge
    (show 0 ≤ t 0 from h₁.symm ▸ le_rfl) (fun j => (hτ j).1) (fun j => (hτ j).2.2) hstep' hLater
  have hlt₁ : T < slab 1 := by
    rw [show (1 : ℕ) = 0 + 1 by omega, hslab 0]
    exact (hTj 0).2.2
  have hBaseSlab : slab 1 < slab 0 := frequencySchedule_endpointSlab_strict
    (fun j => ⟨(hτ j).1, (hτ j).2.2⟩) (inductionHalfLength_zero_le_quarter hbase (hτ 0).2.1)
    h₁ hstep hslab₀ hslab 0
  refine ⟨T, hT, (tendsto_add_atTop_iff_nat 1).mp hlim, ?_, ?_, fun j => (hTj j).2.1⟩
  · intro n
    cases n with
    | zero => simpa only [h₀] using hT
    | succ j => exact sub_pos.mp (hTj j).1
  · intro n
    cases n with
    | zero => exact hlt₁.trans hBaseSlab
    | succ j =>
      rw [hslab j]
      exact (hTj j).2.2



/-- The chosen common-slab limit has the periodic terminal trace and the off-origin
spatial limits supplied by the shrinking supports of the inductive oscillations. -/
theorem inductiveEuler_terminal_trace_of_stage_limits
    {T : ℝ} {slab freq radius : ℕ → ℝ} {q : ℕ → ℕ} {U O : ℕ → Velocity} {u : Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hper : ∀ n t, t ∈ Icc 0 (slab n) → SpatiallyPeriodic (U n t))
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹)
    (hChosen : TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry u)
      atTop (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hradius : Tendsto radius atTop (𝓝 0))
    (hsupport : ∀ n t, t ∈ Icc 0 T → ∀ x, O (n + 1) t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ radius n) :
    HasOffOriginLimits T u ∧ Continuous (u T) ∧ SpatiallyPeriodic (u T) ∧
      ContDiffOn ℝ ∞ (u T) offOrigin ∧ TendstoUniformly u (u T) (𝓝[Ico 0 T] T) ∧
      ∀ K : Set Vec3, IsCompact K → K ⊆ offOrigin → ∀ m : ℕ,
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ m (u t)) (iteratedFDeriv ℝ m (u T))
          (𝓝[Ico 0 T] T) K := by
  obtain ⟨w, hw, hW, hLocal⟩ := exists_inductive_velocity_limit_and_spatial_jets
    hT hslab hinit hfreq hq hUstage hO hB
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) : u t = w t := by
    funext x
    exact tendsto_nhds_unique (hChosen.tendsto_at (x := (t, x)) ⟨ht, mem_univ _⟩)
      (hW.tendsto_at (x := (t, x)) ⟨ht, mem_univ _⟩)
  have hUcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hw.congr (fun p hp => congrFun (hEq p.1 hp.1) p.2)
  have huPer (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (u t) := by
    intro n x
    exact tendsto_nhds_unique_of_eventuallyEq
      (hChosen.tendsto_at (x := (t, x + latticeVector n)) ⟨ht, mem_univ _⟩)
      (hChosen.tendsto_at (x := (t, x)) ⟨ht, mem_univ _⟩)
      (Eventually.of_forall fun j => hper j t (Icc_subset_Icc_right (hslab j) ht) n x)
  have htT : T ∈ Icc (0 : ℝ) T := right_mem_Icc.mpr hT.le
  have hJets (s : Set Vec3) (hs : IsOpen s)
      (hcut : ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc 0 T, EqOn (O (n + 1) t) 0 s) :
      ContDiffOn ℝ ∞ (u T) s ∧
        ∀ m : ℕ, ContinuousOn (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (u z.1) z.2)
          (Icc 0 T ×ˢ s) := by
    obtain ⟨hS, hJ⟩ := hLocal (Icc 0 T) s Subset.rfl hs hcut
    refine ⟨?_, fun m => ((hJ m).2.1).congr ?_⟩
    · rw [hEq T htT]
      exact hS T htT
    · intro z hz
      exact congrArg (fun f : Vec3 → Vec3 => iteratedFDeriv ℝ m f z.2) (hEq z.1 hz.1)
  have hOff : HasOffOriginLimits T u :=
    hasOffOriginLimits_of_inductive_velocity_jets hT.le hradius hsupport hJets
  have huT : Continuous (u T) := continuousOn_univ.mp
    (hUcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨htT, mem_univ x⟩))
  have hSmoothT : ContDiffOn ℝ ∞ (u T) offOrigin := by
    intro x hx
    obtain ⟨s, hs, hxs, _, hcut⟩ := inductive_oscillations_eventually_zero_near_offOrigin_compact
      isCompact_singleton (singleton_subset_iff.mpr hx) hradius hsupport
    exact (((hJets s hs hcut).1).contDiffAt (hs.mem_nhds (hxs (mem_singleton x)))).contDiffWithinAt
  have hCell : TendstoUniformlyOn u (u T) (𝓝[Ico 0 T] T) centeredCell :=
    tendstoUniformlyOn_terminal_of_continuousOn hT.le isCompact_centeredCell
      (hUcont.mono (prod_mono_right (subset_univ centeredCell)))
  have hGlob : TendstoUniformly u (u T) (𝓝[Ico 0 T] T) := by
    rw [← tendstoUniformlyOn_univ, Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hCell ε hε, self_mem_nhdsWithin] with t ht htI x _
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
    have hT' : u T x = u T (x - latticeVector n) := by
      simpa only [sub_add_cancel] using huPer T htT n (x - latticeVector n)
    have ht' : u t x = u t (x - latticeVector n) := by
      simpa only [sub_add_cancel] using huPer t (Ico_subset_Icc_self htI) n (x - latticeVector n)
    rw [hT', ht']
    exact ht _ hn
  refine ⟨hOff, huT, huPer T htT, hSmoothT, hGlob, fun K hK hKo m => ?_⟩
  obtain ⟨s, hs, hKs, _, hcut⟩ := inductive_oscillations_eventually_zero_near_offOrigin_compact
    hK hKo hradius hsupport
  exact tendstoUniformlyOn_terminal_of_continuousOn hT.le hK
    (w := fun t x => iteratedFDeriv ℝ m (u t) x)
    (((hJets s hs hcut).2 m).mono (prod_mono_right hKs))


namespace MovingWaveVector.PhysicalAmplification

/-- The comparison bounds transfer to the physical basis and the actual wave in the crossing. -/
theorem GrowingCrossing.wave_geometry {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}
    {w : PhysicalAmplification I t₀} (d : w.GrowingCrossing T scale Ustar next)
    (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀) (hscale : scale ≠ 0)
    (hclock : MapsTo w.clock (Icc 0 T) I) (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio) {t : ℝ}
    (ht : t ∈ w.activeSlab T) :
    |X w.basis d.waveVector scale t| ≤ T ^ 2 ∧
      |Q w.basis d.waveVector scale w.shear t| ≤ T ∧
      |Z w.basis d.waveVector scale t - 1| ≤ 1 / 2 := by
  let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
  let K := d.waveVector ∘ w.clock
  have hmap : MapsTo w.clock (Icc 0 T) (w.activeSlab T) :=
    mapsTo_amplificationTime_Icc w.rate_pos
  have htime : w.elapsed t ∈ Icc 0 T := mapsTo_inverse_amplificationTime_Icc w.rate_pos ht
  have hB (s : ℝ) : W.basis s = w.basis (w.clock s) := rfl
  have hK₀ : K 0 = scale • W.basis 0 2 := by
    simpa only [K, hB, Function.comp_apply, clock_zero] using d.initial_waveVector
  have hK (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt K (-((W.gradient s).adjoint (K s))) (Icc 0 T) s := by
    have h := normalized_affineWave_derivatives
      (D := w.gradient (w.clock s)) hmap (d.waveVector_derivative _ (hmap hs))
      (by simpa only [affineWaveAmplitudeOperator_apply, clock] using d.amplitude_derivative _ (hmap hs))
    rw [show W.gradient s = (1 / w.rate) • w.gradient (w.clock s) from
      w.toNormalized_gradient_eq hT hC₀ hclock hsmallε hsmallδ hs]
    exact h.1
  obtain ⟨hZ₀, hZ₁, hX, hQ, _⟩ := W.wave_geometry hscale hK₀ hK htime
  have hZ : |Z W.basis K scale (w.elapsed t) - 1| ≤ 1 / 2 := by
    rw [abs_le]
    exact ⟨by linarith only [hZ₀], by linarith only [hZ₁]⟩
  simpa only [X, Q, Z, hB, K, Function.comp_apply, clock_elapsed] using And.intro hX (And.intro hQ hZ)


end MovingWaveVector.PhysicalAmplification

/-- The local and global velocity limits determine the terminal Euler
acceleration once the pressure slice satisfies the normalized Poisson equation. -/
theorem IsEulerSolution.hasOffOriginLimits_timeDerivative_of_velocity_jets
    {T : ℝ} {u : Velocity} {p : Pressure} (h : IsEulerSolution T u p)
    {w : Vec3 → Vec3} (hw : Continuous w) (hws : ContDiffOn ℝ ∞ w offOrigin)
    (hwp : SpatiallyPeriodic w)
    (hglobal : TendstoUniformlyOn u w (𝓝[Ico 0 T] T) (closure multiplierKernelCell))
    (hlocal : ∀ S : Set Vec3, IsCompact S → S ⊆ offOrigin → ∀ d,
      TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (u t)) (iteratedFDeriv ℝ d w)
        (𝓝[Ico 0 T] T) S) :
    HasOffOriginLimits T (timeDerivative T u) := by
  have hvelocity : HasOffOriginLimits T u := by
    intro K hK hKo m
    exact ⟨offOrigin, w, isOpen_offOrigin, hKo, subset_rfl, hws.of_le (by simp),
      fun d _ => hlocal K hK hKo d⟩
  have hpg := hasOffOriginLimits_normalizedPressureGradient_of_velocity_jets
    (p := fun t x => (p t x : ℂ))
    (fun t ht => ⟨h.contDiff_velocity_slice ht, h.periodic_velocity t ht⟩)
    (fun _ ht => h.complexPressureTensorPoisson ht) hw hws hwp hglobal hlocal
  apply h.hasOffOriginLimits_timeDerivative hvelocity
  simpa only [Complex.ofReal_re] using hpg



namespace InductiveEulerCentralWaves

variable {s : InductiveEulerStages} (w : InductiveEulerCentralWaves s)

include w in
theorem activation_strict (j : ℕ) : s.activation (j + 2) < s.activation (j + 3) := by
  have h := (w.crossing j).crossing_after_switch
  rw [w.crossing_time j] at h
  exact (lt_add_of_pos_right _ (one_div_pos.mpr (w.physical j).rate_pos)).trans h

private theorem activation_mono : Monotone s.activation := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => rw [s.activation_zero, s.first_activation]
  | succ n => exact sub_nonneg.mp (s.activation_step n).1

private theorem clock_maps (j : ℕ) :
    MapsTo (w.physical j).clock (Icc 0 (w.window j)) (Icc (s.activation (j + 2)) (s.slab (j + 2))) := by
  intro τ hτ
  have hr := (w.physical j).rate_pos
  refine ⟨le_add_of_nonneg_right (div_nonneg hτ.1 hr.le), ?_⟩
  have h : (w.physical j).clock τ ≤ (w.physical j).clock (w.window j) :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hr.le)
  exact h.trans_eq (w.physical_window j)

private theorem physical_activeSlab (j : ℕ) :
    (w.physical j).activeSlab (w.window j) = Icc (s.activation (j + 2)) (s.slab (j + 2)) := by
  rw [PhysicalAmplification.activeSlab, w.physical_window]

private theorem initial_strength_eq (j : ℕ) :
    (w.physical j).initialStrength =
      ‖w.waveVector (j + 1) (s.activation (j + 2))‖ * ‖w.amplitude (j + 1) (s.activation (j + 2))‖ := by
  rw [PhysicalAmplification.initialStrength, w.preceding_vector, w.preceding_amplitude]

private theorem first_coupling_eq (j : ℕ) :
    (w.physical j).firstCoupling =
      entry (frame (w.waveVector (j + 1)) (w.amplitude (j + 1)) (s.activation (j + 2)))
        (fderiv ℝ (s.velocity j (s.activation (j + 2))) 0) 0 1 := by
  unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis
  rw [w.preceding_vector, w.preceding_amplitude,
    w.older_gradient j _ (w.physical j).activation]

private def windowConstant : ℝ := 2 * Real.sqrt (8 * w.strengthConstant * Real.pi)

private theorem windowConstant_pos : 0 < w.windowConstant := by
  have h : 0 < w.strengthConstant := zero_lt_two.trans_le w.strengthConstant_ge
  unfold windowConstant
  positivity [Real.pi_pos]

private theorem physical_window_upper (hinit : 2 ≤ s.frequency 0) (j : ℕ) :
    w.window j ≤ w.windowConstant * (4 * Real.log (s.frequency (j + 4))) ^ 4 := by
  let μ := s.frequency (j + 1)
  let L := 4 * Real.log (s.frequency (j + 3))
  let LNext := 4 * Real.log (s.frequency (j + 4))
  let P := w.physical j
  have hμ : 0 < μ := zero_lt_two.trans_le (s.frequency_lower hinit (j + 1))
  have hL : 0 ≤ L := mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_two.trans (s.frequency_lower hinit (j + 3))))
  have hLNext : 0 ≤ LNext := mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_two.trans (s.frequency_lower hinit (j + 4))))
  have hLle : L ≤ LNext := mul_le_mul_of_nonneg_left
    (Real.log_le_log (zero_lt_two.trans_le (s.frequency_lower hinit (j + 3)))
      (s.frequency_mono hinit (by omega))) (by norm_num)
  have hC := zero_lt_two.trans_le w.strengthConstant_ge
  have hStrength := w.strength_at_crossing j
  rw [← w.initial_strength_eq] at hStrength
  have hCoupling := w.coupling_at_crossing j
  dsimp only at hCoupling
  rw [← w.first_coupling_eq] at hCoupling
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμ hL (inv_pos.mpr hC) hC
    hStrength.1 hStrength.2 hCoupling.1 hCoupling.2
  have hTime : w.window j = 2 * P.rate * inductionHalfLength s.frequency (j + 1) := by
    have h := (w.physical_window j).trans (s.slab_step (j + 1))
    have hd : w.window j / P.rate = 2 * inductionHalfLength s.frequency (j + 1) := by
      change s.activation (j + 2) + w.window j / P.rate =
        s.activation (j + 2) + 2 * inductionHalfLength s.frequency (j + 1) at h
      exact add_left_cancel h
    calc
      w.window j = (w.window j / P.rate) * P.rate := (div_mul_cancel₀ _ P.rate_pos.ne').symm
      _ = _ := by rw [hd]; ring
  rw [hTime]
  exact (induction_normalized_comparison_window hμ (Real.sqrt_nonneg _) hLNext hLle hrLo hrHi).2

private def curlCoefficient : ℝ :=
  Real.exp (-1) * w.strengthConstant⁻¹ / (6 * w.windowConstant ^ 2)

private theorem curlCoefficient_pos : 0 < w.curlCoefficient := by
  have h : 0 < w.strengthConstant := zero_lt_two.trans_le w.strengthConstant_ge
  unfold curlCoefficient
  exact div_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr h))
    (mul_pos (by norm_num) (pow_pos w.windowConstant_pos 2))

private abbrev curlErrorCoefficient : ℝ := 3 * ‖curlOfDerivativeCLM‖

private theorem no_zero_central_frequency (hinit : 2 ≤ s.frequency 0) (n : ℕ) : s.frequency n ≠ 0 :=
  (zero_lt_two.trans_le (s.frequency_lower hinit n)).ne'


private theorem order_at_least_one (n : ℕ) : 1 ≤ s.order (n + 1) := by
  cases n with
  | zero => rw [s.initial_order]
  | succ n => exact (s.order_maximum n).1.1

private theorem eventually_curl_lower_bound
    {T : ℝ} (hinit : 2 ≤ s.frequency 0) (hslab : ∀ n, T ≤ s.slab n)
    (hbefore : ∀ n, s.activation n < T)
    (hHalf : ∀ j, inductionHalfLength s.frequency j ≤ s.frequency j ^ (-1 / 16 : ℝ))
    {u : Velocity}
    (hprefix : ∀ S < T, TendstoUniformlyOn
      (fun n (z : ℝ × Vec3) => fderiv ℝ (s.velocity n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3))) :
    ∀ᶠ j : ℕ in atTop, 0 ≤ s.activation (j + 2) ∧
      ∀ t ∈ Ico (s.activation (j + 2)) (s.activation (j + 3)),
        w.curlCoefficient * s.frequency (j + 1) ^ (1 / 8 : ℝ) -
          curlErrorCoefficient * s.frequency (j + 1) ^ (1 / 32 : ℝ) - curlErrorCoefficient ≤
          ‖curl (u t) 0‖ := by
  have hmono := activation_mono (s := s)
  have ha (n : ℕ) : 0 ≤ s.activation n := by rw [← s.activation_zero]; exact hmono (Nat.zero_le n)
  have hWaves (n : ℕ) := stage_spatial_jets_of_joint_smoothness (u := s.velocity n)
    ((ha 0).trans_lt ((hbefore 0).trans_le (hslab n))) (s.smooth n)
  filter_upwards [s.eventually_central_gradient_bound hinit,
    eventually_inductive_projection_log_bound (s.frequency_tendsto hinit) s.frequency_log_bound]
    with j hOld hlog
  refine ⟨ha (j + 2), fun t ht => ?_⟩
  let I := Icc (s.activation (j + 2)) (s.activation (j + 3))
  let P := w.physical j
  let d := w.crossing j
  have htI : t ∈ I := Ico_subset_Icc_self ht
  have hWithin (n : ℕ) : s.activation (j + 3) ≤ s.slab n := (hbefore (j + 3)).le.trans (hslab n)
  have hI : I ⊆ Icc (s.activation (j + 2)) (s.slab (j + 2)) := Icc_subset_Icc_right (hWithin (j + 2))
  have hmOld (r : ℝ) (hr : r ∈ I) : r ∈ Icc 0 (s.slab j) :=
    ⟨(ha (j + 2)).trans hr.1, hr.2.trans (hWithin j)⟩
  have hμ : 1 ≤ s.frequency (j + 1) := one_le_two.trans (s.frequency_lower hinit (j + 1))
  have hshort : s.activation (j + 3) - s.activation (j + 2) ≤
      s.frequency (j + 1) ^ (-1 / 16 : ℝ) :=
    (s.activation_step (j + 1)).2.trans (hHalf (j + 1))
  have hB (r : ℝ) (hr : r ∈ I) : ‖P.B r‖ ≤ s.frequency (j + 1) ^ (1 / 32 : ℝ) := by
    rw [show P.B r = fderiv ℝ (s.velocity j r) 0 from w.older_gradient j r (hI hr)]
    exact (hOld r (hmOld r hr)).trans <|
      older_gradient_scale_le_of_frequency_gap (zero_le_two.trans (s.frequency_lower hinit j))
        (s.frequency_gap hinit j)
  have hStrength := preceding_strength_retained_on_short_interval
    (k := P.kp) (a := P.ap) (B := P.B) hμ hshort
    (fun r hr => P.preceding_data r (hI hr))
    (fun r hr => P.trace_zero r (hI hr))
    (fun r hr => (P.preceding_vector r (hI hr)).mono hI)
    (fun r hr => by simpa only [affineWaveAmplitudeOperator_apply] using
      (P.preceding_amplitude r (hI hr)).mono hI)
    hB htI
  have hPhysical : t ∈ P.activeSlab (w.window j) :=
    (w.physical_activeSlab j).symm ▸ hI htI
  have hVec := P.preceding_data t (hI htI)
  have hNew := d.transverse t hPhysical
  have hGeo := d.wave_geometry (w.window_ge j) w.comparisonConstant_ge
    (no_zero_central_frequency hinit (j + 2)) (w.clock_maps j)
    (w.comparison_ratio j) (w.comparison_error j) hPhysical
  have hShear : 1 ≤ P.shear := (P.toNormalized (w.window_ge j) w.comparisonConstant_ge (w.clock_maps j)
    (w.comparison_ratio j) (w.comparison_error j)).shearLower
  have hCarry : (Real.exp (-1) * w.strengthConstant⁻¹) * s.frequency (j + 1) ^ (1 / 4 : ℝ) ≤
      ‖w.waveVector (j + 1) t‖ * ‖w.amplitude (j + 1) t‖ := by
    change Real.exp (-1) * (‖(w.physical j).kp (s.activation (j + 2))‖ *
      ‖(w.physical j).ap (s.activation (j + 2))‖) ≤
        ‖(w.physical j).kp t‖ * ‖(w.physical j).ap t‖ at hStrength
    rw [w.preceding_vector, w.preceding_amplitude] at hStrength
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (w.strength_at_crossing j).1 (Real.exp_pos _).le).trans hStrength
  have hPrev : t ∈ Icc (s.activation (j + 1)) (s.slab (j + 1)) :=
    ⟨(hmono (by omega : j + 1 ≤ j + 2)).trans ht.1, htI.2.trans (hWithin (j + 1))⟩
  have hPrevDone : t ∈ Icc (s.activation (j + 2)) (s.slab (j + 1)) :=
    ⟨ht.1, htI.2.trans (hWithin (j + 1))⟩
  have hSplit := w.gradient_split j t hPrev
  rw [w.cutoff_complete j t hPrevDone, one_smul] at hSplit
  have hTail := norm_center_fderiv_sub_le_of_inductive_tail
    (j := j + 2) (by omega) htI hmono (ha (j + 2)) (hbefore (j + 3)) hslab hinit
    (s.frequency_square_gap hinit)
    (fun n r hr => ((hWaves n).1 r hr).differentiable (by simp) 0) s.oscillation_vanishes
    (fun n _ r hr => s.correction_jet_bound n 1 (order_at_least_one n) r hr 0) hprefix
  have hV := norm_limit_center_curl_ge_of_inductive_stage
    (j := j) (freq := s.frequency) (U := s.velocity) (w := u) (C := w.windowConstant)
    (a := d.amplitude) (Eprev := w.error (j + 1) t) (Enew := w.error (j + 2) t)
    (cutoff := w.cutoff (j + 2) t) (c := w.strengthConstant⁻¹) hμ (zero_le_two.trans (s.frequency_lower hinit j))
    (s.frequency_mono hinit (by omega)) (s.frequency_lower hinit (j + 3))
    (s.frequency_gap hinit j) hVec.1 hVec.2.1 hVec.2.2 hNew.1 hShear
    ((by norm_num : (1 : ℝ) ≤ 2).trans (w.window_ge j)) w.windowConstant_pos
    (w.physical_window_upper hinit j) hGeo.1 hGeo.2.1 hGeo.2.2 hlog.2
  have hkp : P.kp = w.waveVector (j + 1) := w.preceding_vector j
  have hap : P.ap = w.amplitude (j + 1) := w.preceding_amplitude j
  have hk : d.waveVector = w.waveVector (j + 2) := w.current_vector j
  have ha' : d.amplitude = w.amplitude (j + 2) := w.current_amplitude j
  exact hV
    (by simpa only [hkp, hap] using hCarry)
    (by simpa only [hkp, hap] using hSplit)
    (by simpa only [hk, ha'] using w.gradient_split (j + 1) t (hI htI))
    (hOld t (hmOld t htI)) (w.error_bound j t hPrev) (w.error_bound (j + 1) t (hI htI)) hTail

end InductiveEulerCentralWaves


/-- A compatible family of constructed stages satisfying the quantitative
hypotheses of the frozen induction yields the exact statement of Theorem 1.1.
The family supplies the stage estimates and matching central waves. The proof
constructs the common terminal time, the Euler solution and normalized
pressure, and derives the terminal curl and off-origin limits. -/
theorem exists_theorem11Witness_of_inductiveEulerStages :
    ∃ N₀ : ℝ, ∀ (s : InductiveEulerStages) (_w : InductiveEulerCentralWaves s),
      N₀ ≤ s.frequency 0 → 2 ≤ s.frequency 0 ∧
        ∃ (T : ℝ) (u : Velocity) (p : Pressure),
          0 < T ∧ (∀ n, T < s.slab n) ∧ Tendsto s.activation atTop (𝓝 T) ∧
          EulerSingularityWitness (u 0) T u p ∧
          TendstoUniformlyOn (fun n => Function.uncurry (s.velocity n)) (Function.uncurry u)
            atTop (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  obtain ⟨N, hN⟩ := frequencySchedule_halfLength_bounds
  refine ⟨max N ((4 : ℝ) ^ (16 : ℕ)), ?_⟩
  intro s w hLarge
  have hBase : (4 : ℝ) ^ (16 : ℕ) ≤ s.frequency 0 := (le_max_right _ _).trans hLarge
  have hinit : 2 ≤ s.frequency 0 := (by norm_num : (2 : ℝ) ≤ 4 ^ (16 : ℕ)).trans hBase
  have hHalf := hN s.exponentParameter s.order s.threshold s.frequency s.exponentParameter_ge s.initial_order
    s.initial_threshold ((le_max_left _ _).trans hLarge) s.frequency_step s.order_maximum
    s.threshold_pos s.threshold_floor
  obtain ⟨T, hT, hActivation, hBefore, hSlabStrict, _⟩ :=
    frequencySchedule_commonLifetime_of_halfLength_bounds hBase hHalf s.activation_zero
      s.first_activation s.second_activation (fun j => (s.activation_step j).2) w.activation_strict
      s.slab_base s.slab_step
  have hSlab (n : ℕ) : T ≤ s.slab n := (hSlabStrict n).le
  have hFreq := s.frequency_tendsto hinit
  have hSquare := s.frequency_square_gap hinit
  have hOrder := s.order_tendsto hinit
  obtain ⟨u, p, hEuler, hOdd, hContinuous, hLimit, hJets⟩ := exists_inductive_periodicEulerSolution (U := s.velocity)
    hT hSlab hinit hSquare hOrder hActivation s.smooth (fun n t _ => s.periodic_velocity n t)
    s.odd s.divergence_free s.oscillation_vanishes s.oscillation_bound s.correction_jet_bound
    s.projected_residual s.residual_bound
  have hRadius : Tendsto (fun n => (s.frequency n)⁻¹) atTop (𝓝 0) := by
    simpa only [zero_add] using (reciprocal_inductive_frequency_tail hinit hSquare 0).1.tendsto_atTop_zero
  obtain ⟨huOff, huTCont, huTPer, huTSmooth, huTGlobal, huTLocal⟩ :=
    inductiveEuler_terminal_trace_of_stage_limits (U := s.velocity) hT hSlab hinit hSquare hOrder s.smooth
      (fun n t _ => s.periodic_velocity n t) s.oscillation_bound s.correction_jet_bound hLimit hRadius
      (fun n t ht x hx => s.oscillation_support n t (Icc_subset_Icc_right (hSlab (n + 1)) ht) x hx)
  have hdtOff := hEuler.hasOffOriginLimits_timeDerivative_of_velocity_jets huTCont huTSmooth huTPer
    huTGlobal.tendstoUniformlyOn huTLocal
  have hPrefix (S : ℝ) (hST : S < T) : TendstoUniformlyOn
      (fun n (z : ℝ × Vec3) => fderiv ℝ (s.velocity n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
    obtain ⟨S', hSS', hS'T⟩ := exists_between (max_lt hST hT)
    have hS' : 0 < S' := (le_max_right _ _).trans_lt hSS'
    exact (tendstoUniformlyOn_spatial_fderiv_of_first_jet (hJets S' hS' hS'T 1).1).mono
      (prod_mono_left (Icc_subset_Icc_right ((le_max_left _ _).trans hSS'.le)))
  have hCurl := w.eventually_curl_lower_bound hinit hSlab hBefore (fun j => (hHalf j).2.1) hPrefix
  have hμ : Tendsto (fun j => s.frequency (j + 1)) atTop atTop :=
    hFreq.comp (tendsto_add_atTop_nat 1)
  have hActivation' : Tendsto (fun j => s.activation (j + 2)) atTop (𝓝 T) :=
    hActivation.comp (tendsto_add_atTop_nat 2)
  have hCentral : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop := by
    have hPrincipal : Tendsto (fun j => (w.curlCoefficient / 2) * s.frequency (j + 1) ^ (1 / 8 : ℝ))
        atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hμ).const_mul_atTop
        (half_pos w.curlCoefficient_pos)
    refine (tendsto_atTop_of_activationBounds hActivation' (fun j => hBefore (j + 2))
      hPrincipal ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
    filter_upwards [eventually_half_curl_power_lower_bound w.curlCoefficient_pos
      (B := InductiveEulerCentralWaves.curlErrorCoefficient) hμ, hCurl]
      with j hj hjet t ht
    exact hj.trans (hjet.2 t ht)
  have hCurlIntegral : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ := by
    have hC := zero_lt_two.trans_le w.strengthConstant_ge
    apply curlIntegral_eq_top_of_inductive_physical_crossings
      (σ := fun j => (w.physical j).initialStrength) (ν := fun j => (w.physical j).firstCoupling)
      w.curlCoefficient_pos (inv_pos.mpr hC) hC hFreq
      (InductiveEulerCentralWaves.activation_mono (s := s)) hBefore
      (fun t ht => (hEuler.contDiff_velocity_slice ht).of_le (by simp)) ?_ ?_ ?_ hCurl
    · exact Eventually.of_forall fun j => by
        rw [w.initial_strength_eq]
        exact w.strength_at_crossing j
    · exact Eventually.of_forall fun j => by
        rw [w.first_coupling_eq]
        exact w.coupling_at_crossing j
    · exact Eventually.of_forall fun j =>
        ⟨_, w.window j, w.physical j, w.crossing j, w.crossing_time j, rfl, rfl, w.prescribed_ratio j⟩
  refine ⟨hinit, T, u, p, hT, hSlabStrict, hActivation, ?_, hLimit⟩
  exact theorem11Witness_of_solution_and_terminal_bounds hEuler hOdd
    (terminalVelocityBound_of_extension
      (hContinuous.mono (prod_mono_right (subset_univ centeredCell))) (fun _ _ _ _ => rfl))
    hCentral huOff hdtOff hCurlIntegral

/-- The common physical stage family proves the frozen theorem. -/
theorem theorem11_of_inductiveEulerStages :
    ∃ N₀ : ℝ, ∀ (s : InductiveEulerStages) (_w : InductiveEulerCentralWaves s),
      N₀ ≤ s.frequency 0 → Theorem11 := by
  obtain ⟨N, hN⟩ := exists_theorem11Witness_of_inductiveEulerStages
  refine ⟨N, fun s w hLarge => ?_⟩
  obtain ⟨_, T, u, p, _, _, _, hWitness, _⟩ := hN s w hLarge
  exact ⟨u 0, T, u, p, hWitness⟩

end

end TorusEuler
