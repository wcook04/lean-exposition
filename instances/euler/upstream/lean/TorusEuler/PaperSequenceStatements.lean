import TorusEuler.Theorem11

/-! The common sequence and its quantitative predicates from frozen Theorem 7.1. -/

open Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

open MovingWaveVector (entry frame)

noncomputable section

variable {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)

local notation "U" => c.stages.velocity
local notation "time" => c.stages.activation
local notation "S" => c.stages.slab
local notation "freq" => c.stages.frequency
local notation "O" => c.stages.oscillation

/-- The fields of the common sequence, with the indexing of frozen Theorem 7.1.
At index `j`, the paper's positive wave index is `j+1`. -/
structure PaperTheorem71Conclusions (T : ℝ) : Prop where
  startup :
    U 0 = fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (freq 3)))
  initial_activations : time 1 = 0 ∧ time 2 = 0
  activation_strict : ∀ j : ℕ, time (j + 2) < time (j + 3)
  stage_slab : S 0 = 1 ∧ ∀ j : ℕ,
    S (j + 1) = time (j + 1) + 2 * (freq j ^ (-1 / 8 : ℝ) * (4 * Real.log (freq (j + 3))) ^ 3)
  stage_regular : ∀ n : ℕ,
    ContDiffOn ℝ ∞ (Function.uncurry (U n)) (Icc 0 (S n) ×ˢ (univ : Set Vec3)) ∧
      IsLabelFlowOn (U n) (c.stage n).flow (Icc 0 (S n)) ∧
      ∀ t ∈ Icc 0 (S n), SpatiallyPeriodic (U n t) ∧ Function.Odd (U n t) ∧
        (∀ x, divergence (U n t) x = 0) ∧
        RealTorusFourierBand (2 * freq n ^ 5) (c.stages.torusVelocity n t)
  stage_size : ∀ n : ℕ, ∀ t ∈ Icc 0 (S n),
    ‖c.stages.torusVelocity n t‖ ≤ freq n ∧
      (∀ x, ‖c.stages.residual n t x‖ ≤ freq (n + 1) ^ (-3 : ℝ)) ∧
      ∀ x : Vec3,
        let F := fderiv ℝ ((c.stage n).flow 0 t) x
        let G := fderiv ℝ ((c.stage n).flow t 0) ((c.stage n).flow 0 t x)
        ‖F‖ ≤ freq n ∧ ‖G‖ ≤ freq n ∧
          G.comp F = .id ℝ Vec3 ∧ F.comp G = .id ℝ Vec3
  pressure_upper : ∀ n : ℕ, ∀ t ∈ Icc 0 (S n), ∀ x v : Vec3,
    ⟪v, fderiv ℝ (gradient ((c.stage n).pressure t)) x v⟫_ℝ ≤
      (∑ i ∈ Finset.range n, (freq i)⁻¹) * ‖v‖ ^ 2
  central_gradient : ∀ j : ℕ, ∀ t ∈ Icc (time (j + 1)) (S (j + 1)),
    fderiv ℝ (U (j + 1) t) 0 =
      fderiv ℝ (U j t) 0 +
        c.centralWaves.cutoff (j + 1) t •
          (innerSL ℝ (c.centralWaves.waveVector (j + 1) t)).smulRight (c.centralWaves.amplitude (j + 1) t) +
        c.centralWaves.error (j + 1) t ∧
      ‖c.centralWaves.error (j + 1) t‖ ≤ freq (j + 1) ^ (-1 / 4 : ℝ)
  crossing_window : ∀ j : ℕ,
    0 ≤ time (j + 2) - time (j + 1) ∧
      time (j + 2) - time (j + 1) ≤ inductionHalfLength freq j ∧
      ∀ t ∈ Icc (time (j + 2)) (S (j + 1)), c.centralWaves.cutoff (j + 1) t = 1
  strength_constant : 2 ≤ c.centralWaves.strengthConstant
  crossing_values : ∀ j : ℕ,
    let t := time (j + 2)
    let E := frame (c.centralWaves.waveVector (j + 1)) (c.centralWaves.amplitude (j + 1)) t
    let B := fderiv ℝ (U j t) (0 : Vec3)
    let ν := entry E B 0 1
    let η := entry E B 2 1
    let σ := ‖c.centralWaves.amplitude (j + 1) t‖ * ‖c.centralWaves.waveVector (j + 1) t‖
    η / ν = couplingRatioOfGain (4 * Real.log (freq (j + 3))) ∧
      Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi ∧
      c.centralWaves.strengthConstant⁻¹ * freq (j + 1) ^ (1 / 4 : ℝ) ≤ σ ∧
      σ ≤ c.centralWaves.strengthConstant * freq (j + 1) ^ (1 / 4 : ℝ) *
        (4 * Real.log (freq (j + 3))) ^ 2
  lifetime : 0 < T ∧ Tendsto time atTop (𝓝 T) ∧ ∀ j, T < S j
  oscillation_support : ∀ j : ℕ, ∀ t ∈ Icc 0 (S (j + 1)), ∀ x,
    O (j + 1) t x ≠ 0 → ∃ n : Fin 3 → ℤ, dist (latticeVector n) x ≤ (freq j)⁻¹
  oscillation_small : ∀ j : ℕ, ∀ t ∈ Icc 0 (S (j + 1)), ∀ x,
    ‖O (j + 1) t x‖ ≤ (freq (j + 1))⁻¹
  increment : ∀ j m : ℕ, m ≤ c.stages.order (j + 1) → ∀ t ∈ Icc 0 (S (j + 1)),
    let V := U (j + 1) t - U j t - O (j + 1) t
    SpatialHolderHalf m V ∧ spatialHolderHalfNorm m V ≤ (freq (j + 1))⁻¹
  oscillation_before_activation : ∀ j ≥ 2, ∀ t ∈ Icc 0 (time j), O j t = 0

private theorem paperSequence_older_velocity (j : ℕ) :
    (c.tip j).older.velocity = U j := by
  cases j <;> rfl

private theorem paperSequence_activation_strict (j : ℕ) : time (j + 2) < time (j + 3) := by
  have h := (c.centralWaves.crossing j).crossing_after_switch
  rw [c.centralWaves.crossing_time j] at h
  exact (lt_add_of_pos_right _ (one_div_pos.mpr (c.centralWaves.physical j).rate_pos)).trans h

/-- A physical construction certifies every quantitative clause of Theorem 7.1,
including the inverse deformation and the prescribed exit ratio. -/
theorem paperTheorem71_of_construction
    (hFrequency : (4 : ℝ) ^ (16 : ℕ) ≤ P.frequency 0)
    (hStartup : c.base.stationary.velocity =
      fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3)))) :
    ∃ T : ℝ, PaperTheorem71Conclusions c T := by
  obtain ⟨T, hT, hActivation, _, hSlab, _⟩ :=
    frequencySchedule_commonLifetime_of_halfLength_bounds hFrequency c.lifetime.step
      c.stages.activation_zero c.stages.first_activation c.stages.second_activation (fun j => (c.stages.activation_step j).2)
      (paperSequence_activation_strict c) c.stages.slab_base c.stages.slab_step
  have hBase : 2 ≤ P.frequency 0 :=
    (by norm_num : (2 : ℝ) ≤ 4 ^ (16 : ℕ)).trans hFrequency
  have hMono : Monotone P.frequency := frequencySchedule_frequency_mono P.exponentParameter
    P.order P.frequency P.exponentParameter_ge (one_le_two.trans hBase) P.frequency_step
  refine ⟨T, { startup := hStartup
               initial_activations := ⟨c.stages.first_activation, c.stages.second_activation⟩
               activation_strict := paperSequence_activation_strict c
               stage_slab := ⟨c.stages.slab_base, c.stages.slab_step⟩
               stage_regular := ?_
               stage_size := ?_
               pressure_upper := fun n => (c.stage n).pressure_hessian
               central_gradient := fun j t ht => ⟨c.centralWaves.gradient_split j t ht, c.centralWaves.error_bound j t ht⟩
               crossing_window := ?_
               strength_constant := c.centralWaves.strengthConstant_ge
               crossing_values := ?_
               lifetime := ⟨hT, hActivation, hSlab⟩
               oscillation_support := c.stages.oscillation_support
               oscillation_small := c.stages.oscillation_bound
               increment := c.stages.correction_bound
               oscillation_before_activation := c.stages.oscillation_vanishes }⟩
  · exact fun n => ⟨c.stages.smooth n, (c.stage n).deformation.flow, fun t ht =>
      ⟨c.stages.periodic_velocity n t, c.stages.odd n t ht, c.stages.divergence_free n t ht, c.stages.velocity_band n t ht⟩⟩
  · intro n t ht
    refine ⟨c.stages.velocity_bound n t ht, ?_, ?_⟩
    · intro x
      have hn : 0 ≤ freq (n + 1) := zero_le_two.trans (hBase.trans (hMono (Nat.zero_le _)))
      have hr : freq (n + 1) ^ (-3 : ℝ) = ((freq (n + 1))⁻¹) ^ (3 : ℕ) := by
        rw [Real.rpow_neg hn, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
      rw [hr]
      exact c.stages.residual_bound n t ht x
    · intro x
      have hd := (c.stage n).deformation
      exact ⟨((hd.bounds t ht).2.1 x).2,
        ((hd.bounds t ht).2.2 ((c.stage n).flow 0 t x)).2, hd.fderiv_inverse ht x⟩
  · exact fun j => ⟨(c.stages.activation_step j).1, (c.stages.activation_step j).2, c.centralWaves.cutoff_complete j⟩
  · intro j
    dsimp only
    have hr := (c.tip j).wave.ratio_at_crossing
    rw [paperSequence_older_velocity c j] at hr
    refine ⟨hr, (c.centralWaves.coupling_at_crossing j).1, (c.centralWaves.coupling_at_crossing j).2, ?_⟩
    simpa only [mul_comm ‖c.centralWaves.waveVector (j + 1) (time (j + 2))‖] using c.centralWaves.strength_at_crossing j

end

/-- The fixed parameter and threshold yield the full common sequence for
each sufficiently large initial frequency in frozen Theorem 7.1. -/
theorem paperTheorem71 :
    ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ),
      1 ≤ b ∧ Monotone threshold ∧ threshold 1 ≤ N₁ ∧
      (∀ q ≥ 1, 0 < threshold q ∧
        4 * (frequencyExponent b (q + 1) : ℝ) ^ 3 ≤ Real.log (threshold q)) ∧
      ∀ N ≥ N₁, ∃ (P : InductiveEulerParameters) (c : ScheduledEulerConstruction P) (T : ℝ),
        P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧
          P.strengthConstant = 18 * Real.exp 3 ∧ PaperTheorem71Conclusions c.construction T := by
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ :=
    exists_scheduledEulerConstruction_of_uniformPhysicalEstimates
      (uniformPhysicalEstimates_of_laterPrimaryCosts (Classical.choice nonempty_laterPrimaryCosts))
      ((4 : ℝ) ^ (16 : ℕ))
  obtain ⟨P₁, _, hb₁, ht₁, hf₁, _, _⟩ := hSchedule N₁ le_rfl
  refine ⟨b, threshold, N₁, hb₁ ▸ P₁.exponentParameter_ge, hMono, ?_, ?_, ?_⟩
  · rw [← ht₁, ← hf₁]
    exact P₁.initial_threshold
  · intro q hq
    rw [← ht₁, ← hb₁]
    exact ⟨P₁.threshold_pos q hq, P₁.threshold_floor q hq⟩
  · intro N hN
    obtain ⟨P, c, hb, ht, hf, hFloor, hStrength⟩ := hSchedule N hN
    have hStartup : c.construction.base.stationary.velocity =
        fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3))) :=
      (congrArg (fun d : InductiveEulerStage P 0 0 => d.velocity) c.base.parent_eq).trans
        c.base.selected.parent_velocity
    obtain ⟨T, hT⟩ := paperTheorem71_of_construction c.construction hFloor hStartup
    exact ⟨P, c, T, hb, ht, hf, hStrength, hT⟩

end TorusEuler
