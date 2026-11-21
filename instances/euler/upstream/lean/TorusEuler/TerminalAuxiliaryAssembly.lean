import TorusEuler.Theorem11
import TorusEuler.TerminalScheduleCosts
import TorusEuler.TerminalScheduledStages
import TorusEuler.TerminalMixedStageLimits
import TorusEuler.TerminalSeeleyExtension

/-! The auxiliary theorem concerns the same Euler solution and stage sequence as the main theorem. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

open InductiveEulerParameters

/-- The two auxiliary estimates and the smooth extension for the exact
solution produced by an augmented fixed-order schedule. -/
def AuxiliaryTerminalSmoothness : Prop :=
  ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ),
    Monotone threshold ∧ ∀ N ≥ N₁,
    ∃ (P : InductiveEulerParameters) (c : ScheduledEulerConstruction P),
      P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧
      let s := c.construction.stages
      (∀ q, ∃ ψ : ℕ, ∀ᶠ n in atTop, s.StageTimeBounds q ψ n) ∧
      s.HasTerminalMixedIncrementBounds ∧
      ∃ (T : ℝ) (u : Velocity) (p : Pressure),
        0 < T ∧ Tendsto s.activation atTop (𝓝 T) ∧ (∀ j, T < s.slab j) ∧
        EulerSingularityWitness (u 0) T u p ∧ HasSmoothOffOriginExtension T u

/-- The auxiliary fixed-order coefficients fit the same threshold used to select the physical steps. -/
def TerminalCostBounds {κ : Type*} (P : InductiveEulerParameters)
    (cost : κ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ) : Prop :=
  ∀ i j q m d, let S := 7 * frequencyExponent P.exponentParameter (P.order (i + 2))
    q ≤ S → m ≤ S + reserve q d → d ≤ S → |cost j q m d| ≤ P.frequency i

/-- Local time-step estimates for the selected hierarchies imply both
auxiliary lemmas and smooth terminal extension on a single schedule. -/
theorem auxiliaryTerminalSmoothness_of_localTimeStep
    {κ : Type*} [Fintype κ] (cost : ℕ → κ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ)
    (Naux : ℝ) (radiusFloor : ℕ)
    (steps : ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P),
      Naux ≤ P.frequency 0 → radiusFloor ≤ c.radiusExponent → P.strengthConstant = 18 * Real.exp 3 →
      TerminalCostBounds P (cost c.radiusExponent) reserve → c.construction.stages.TerminalTimeStep) :
    AuxiliaryTerminalSmoothness := by
  obtain ⟨N₀, hLimit⟩ := exists_theorem11Witness_of_inductiveEulerStages
  have physical := uniformPhysicalEstimates_of_laterPrimaryCosts (Classical.choice nonempty_laterPrimaryCosts)
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ :=
    exists_scheduledEulerConstruction physical (fun a P => TerminalCostBounds P (cost a) reserve) (by
      intro base a p r power comparison strength cutoffConstant initialFloor hComparison hStrength hΓ
      let b := stepExponentFloor a p r power
      obtain ⟨N₁, hChoose⟩ := exists_of_inductiveStepCosts_withTerminal base (cost a) reserve
        a p r power b comparison strength cutoffConstant initialFloor le_rfl hComparison hStrength hΓ
      let table := (base.withTerminal (cost a) reserve).table
      refine ⟨b, fixedOrderThreshold b table, N₁, fixedOrderThreshold_mono b table, fun N hN => ?_⟩
      obtain ⟨P, hb, hCompare, hC, hThreshold, hFreq, hFloor, hLarge, hLife, hBudget, hCosts⟩ := hChoose N hN
      refine ⟨P, hb, hThreshold, hFreq, hCompare, hC, hFloor, hLarge, hLife, hBudget, ?_⟩
      intro i j q m d
      simpa only [hb] using hCosts i j q m d) (max N₀ Naux) radiusFloor
  refine ⟨b, threshold, N₁, hMono, fun N hN => ?_⟩
  obtain ⟨P, c, hb, hThreshold, hFreq, hBase, hStrength, hRadius, hCosts⟩ := hSchedule N hN
  let s := c.construction.stages
  obtain ⟨hInit, T, u, p, hT, hSlab, hActivation, hTheorem11, hConverge⟩ :=
    hLimit s c.construction.centralWaves ((le_max_left _ _).trans hBase)
  have hFreqOne (n : ℕ) : 1 ≤ s.frequency n :=
    (one_le_two.trans hInit).trans (P.terminal_frequency_mono (Nat.zero_le n))
  obtain ⟨hTime, hMixed⟩ :=
    s.terminalTimeBounds_of_step hFreqOne (s.order_tendsto hInit)
      (steps c ((le_max_right _ _).trans hBase) hRadius hStrength hCosts)
  have hSmooth :=
    s.terminal_contDiffOn_of_mixed_increment_bounds hT (fun j => (hSlab j).le)
      (fun j => (c.construction.slab_succ_lt j).le) hInit (s.frequency_square_gap hInit) hMixed hConverge
  have hEuler : IsEulerSolution T u p := hTheorem11.2.2.2.2.1.1
  exact ⟨P, c, hb, hThreshold, hFreq, hTime, hMixed, T, u, p, hT, hActivation,
    hSlab, hTheorem11, hEuler.hasSmoothOffOriginExtension hSmooth⟩

end TorusEuler
