import TorusEuler.Paper.S678.Statements
import TorusEuler.PaperSequenceStatements
import TorusEuler.Paper.Proofs.S678b.Library.Comparison
import TorusEuler.Paper.Proofs.S678a.Library.Common

/-! # The conclusions of Theorem 7.1 for a construction (package S678a)

Own content of row 7.1: the quantitative clauses of `Theorem71Conclusions` are certified by the
fields of an `InductiveEulerConstruction` (the library's `paperTheorem71_of_construction`,
`frequencySchedule_commonLifetime_of_halfLength_bounds`, the last paragraph of the proof,
sections/08b_induction.tex:481-488), the cutoff clauses by the cutoff equations of the waves
(`waveSwitch`, Section 7), and the two exported clauses of item 2 (`comparison`,
`window_upper`) by the comparison library, which takes `h1_3`, `h2_2` and `hB_1` as hypotheses
(`Lib.S678b.eventually_finiteSmallness`, `Lib.S678b.CentralWaves.physical_window_upper`). -/

open Filter Set
open scoped Topology

namespace TorusEuler.Paper.Lib.S678a

open MovingWaveVector (frame entry)

/-- The later cutoff clause of `Theorem71Conclusions` from the cutoff equations
`χ̃_{i+2} = waveSwitch t_{i+2} r_i` of the waves (Section 7, sections/08b_induction.tex:94-140). -/
theorem later_cutoff_of_waveSwitch {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (hcut : ∀ i : ℕ, c.centralWaves.cutoff (i + 2) =
      waveSwitch (c.stages.activation (i + 2)) (c.centralWaves.physical i).rate) :
    ∀ j : ℕ, 2 ≤ j → ∀ t : ℝ,
    let t₀ := c.stages.activation j
    let σ := ‖c.centralWaves.amplitude (j - 1) t₀‖ * ‖c.centralWaves.waveVector (j - 1) t₀‖
    let ν := entry (frame (c.centralWaves.waveVector (j - 1)) (c.centralWaves.amplitude (j - 1)) t₀)
      (fderiv ℝ (c.stages.velocity (j - 2) t₀) 0) 0 1
    let r := Real.sqrt (2 * σ * ν)
    c.centralWaves.cutoff j t = if t < t₀ then 0 else 1 - envelopeCutoff (1 + r * (t - t₀)) := by
  intro j hj t
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  let w := c.centralWaves
  have hrate : (w.physical i).rate = Real.sqrt (2 *
      (‖w.amplitude (i + 1) (c.stages.activation (i + 2))‖ *
        ‖w.waveVector (i + 1) (c.stages.activation (i + 2))‖) *
      entry (frame (w.waveVector (i + 1)) (w.amplitude (i + 1)) (c.stages.activation (i + 2)))
        (fderiv ℝ (c.stages.velocity i (c.stages.activation (i + 2))) 0) 0 1) := by
    unfold MovingWaveVector.PhysicalAmplification.rate MovingWaveVector.amplificationGrowthRate
      MovingWaveVector.PhysicalAmplification.initialStrength
      MovingWaveVector.PhysicalAmplification.firstCoupling MovingWaveVector.PhysicalAmplification.basis
    rw [w.preceding_vector, w.preceding_amplitude, w.older_gradient i _ (w.physical i).activation,
      mul_comm ‖w.waveVector (i + 1) _‖]
  dsimp only
  simp only [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega]
  rw [hcut i, ← hrate]
  split_ifs with h
  · exact waveSwitch_eq_zero_of_le (w.physical i).rate_pos.le h.le
  · exact waveSwitch_eq_one_sub_envelopeCutoff _ _ _

/-- **The conclusions of Theorem 7.1 for a construction.** For a construction `c` whose first wave
has the cutoff `1` and whose later waves have the cutoffs `waveSwitch t_j r`, with initial
frequency at least `4^16` and the base velocity the shear (6.1) at `ρ = ε_1`, all clauses of
`Theorem71Conclusions c C T` hold for `C = P.strengthConstant` and some `T = T_∞`:
the quantitative clauses come from the fields of the construction
(`paperTheorem71_of_construction`; `T_∞` from `frequencySchedule_commonLifetime_of_halfLength_bounds`),
the cutoff clauses from `later_cutoff_of_waveSwitch`, and the clauses `comparison` (2.7) and
`window_upper` of item 2 (sections/08b_induction.tex:306-326) from `h1_3`, `h2_2` and `hB_1`
through the comparison library. -/
theorem conclusions_of_construction (h1_3 : Statement.lemma_1_3) (h2_2 : Statement.lemma_2_2)
    (hB_1 : Statement.lemma_B_1) {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (hFrequency : (4 : ℝ) ^ (16 : ℕ) ≤ P.frequency 0)
    (hStartup : c.base.stationary.velocity =
      fun _ => stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3))))
    (hfirst : ∀ t : ℝ, c.centralWaves.cutoff 1 t = 1)
    (hcut : ∀ i : ℕ, c.centralWaves.cutoff (i + 2) =
      waveSwitch (c.stages.activation (i + 2)) (c.centralWaves.physical i).rate) :
    ∃ T : ℝ, Theorem71Conclusions c c.centralWaves.strengthConstant T := by
  obtain ⟨T, h⟩ := paperTheorem71_of_construction c hFrequency hStartup
  have hBase : 2 ≤ P.frequency 0 :=
    (by norm_num : (2 : ℝ) ≤ 4 ^ (16 : ℕ)).trans hFrequency
  have hMono : Monotone P.frequency := frequencySchedule_frequency_mono P.exponentParameter
    P.order P.frequency P.exponentParameter_ge (one_le_two.trans hBase) P.frequency_step
  have shift : ∀ j : ℕ, 1 ≤ j → ∃ i, j = i + 1 := fun j hj => ⟨j - 1, by omega⟩
  refine ⟨T, { shear := fun t => congrFun h.startup t
               first_times := h.initial_activations
               times_increase := fun j hj => ?_
               final_times := ⟨h.stage_slab.1, fun j hj => ?_⟩
               T1 := fun j => ⟨(h.stage_regular j).1, fun t ht => (h.stage_regular j).2.2 t ht⟩
               T2 := fun j => ⟨fun t ht x => ((c.stages.torusVelocity j t).norm_coe_le_norm _).trans
                 (h.stage_size j t ht).1, (c.stage j).deformation, fun t ht x => ?_⟩
               T3 := h.pressure_upper
               T4_gradient := fun j hj => ?_
               T4_times := fun j hj => ?_
               strength_constant := h.strength_constant
               T4_late_values := fun j hj => ?_
               first_cutoff := hfirst
               later_cutoff := later_cutoff_of_waveSwitch c hcut
               lifetime := h.lifetime
               oscillation_support := fun j hj => ?_
               increment := fun j hj => ?_
               oscillation_vanishes := h.oscillation_before_activation
               comparison := fun C₀ => Lib.S678b.eventually_finiteSmallness h1_3 h2_2 hB_1 c C₀
               window_upper := ⟨Lib.S678b.CentralWaves.windowConstant c.centralWaves,
                 fun j => Lib.S678b.CentralWaves.physical_window_upper c.centralWaves
                   (Lib.S678a.two_le_frequency_zero P) j⟩ }⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    exact h.activation_strict i
  · obtain ⟨i, rfl⟩ := shift j hj
    exact h.stage_slab.2 i
  · have h3 := (h.stage_size j t ht).2.1 x
    have hn : 0 ≤ P.frequency (j + 1) :=
      zero_le_two.trans (hBase.trans (hMono (Nat.zero_le _)))
    have hr : P.frequency (j + 1) ^ (-3 : ℝ) = ((P.frequency (j + 1))⁻¹) ^ (3 : ℕ) := by
      rw [Real.rpow_neg hn, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    rw [← hr]; exact h3
  · obtain ⟨i, rfl⟩ := shift j hj
    exact h.central_gradient i
  · obtain ⟨i, rfl⟩ := shift j hj
    exact h.crossing_window i
  · obtain ⟨i, rfl⟩ := shift j hj
    exact h.crossing_values i
  · obtain ⟨i, rfl⟩ := shift j hj
    exact h.oscillation_support i
  · obtain ⟨i, rfl⟩ := shift j hj
    intro t ht
    exact ⟨h.oscillation_small i t ht, fun m hm => h.increment i m hm t ht⟩

end TorusEuler.Paper.Lib.S678a
