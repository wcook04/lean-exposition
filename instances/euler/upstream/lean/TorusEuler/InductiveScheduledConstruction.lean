import TorusEuler.InductiveFirstStageAssembly
import TorusEuler.InductiveLaterStageAssembly

/-! One physical sequence retains the selected data behind every cutoff. -/

namespace TorusEuler

open InductiveEulerParameters

noncomputable section

/-- The first selected hierarchy, its cutoff, and the certified base built from it. -/
structure ScheduledEulerBase (P : InductiveEulerParameters) (a : ℕ) where
  selected : InductiveFirstWaveSelection P a
  stage : ScheduledPhysicalStage (activation := 0) selected.parent selected.approximation selected.properties a
  cutoff_symbol : stage.symbol = dyadicMultiplierCutoff
  base : InductiveEulerBase P
  velocity_eq : base.first.velocity = stage.cutoff.velocity
  pressure_eq : base.first.pressure = stage.cutoff.pressure
  parent_eq : base.stationary = selected.parent
  oscillation_eq : base.wave.oscillation = selected.approximation.oscillation

/-- The later selected hierarchy and the certified step at the exact preceding tip. -/
structure ScheduledEulerStep {P : InductiveEulerParameters} {n : ℕ}
    (tip : InductiveEulerTip P n) (Cenv : ℝ) (a : ℕ) where
  selected : tip.SelectedLaterInput Cenv a
  stage : ScheduledPhysicalStage tip.parent selected.approximation selected.properties a
  cutoff_symbol : stage.symbol = dyadicMultiplierCutoff
  step : InductiveEulerStep tip
  velocity_eq : step.child.velocity = stage.cutoff.velocity
  pressure_eq : step.child.pressure = stage.cutoff.pressure
  oscillation_eq : step.wave.oscillation = selected.approximation.oscillation

/-- The stage choices that determine one physical construction on the common schedule. -/
structure ScheduledEulerConstruction (P : InductiveEulerParameters) where
  lifetime : P.LifetimeBounds
  radiusExponent : ℕ
  envelopeConstant : ℝ
  base : ScheduledEulerBase P radiusExponent
  successor : ∀ (n : ℕ) (tip : InductiveEulerTip P n),
    InductiveEulerPrefix P lifetime n tip → ScheduledEulerStep tip envelopeConstant radiusExponent

namespace ScheduledEulerConstruction

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P)

/-- The physical stage sequence uses the exact selected successors. -/
def construction : InductiveEulerConstruction P :=
  ⟨c.lifetime, c.base.base, fun n tip prior => (c.successor n tip prior).step⟩

/-- The actual hierarchy used at the given prefix, with its physical fields retained. -/
def selectedStep (n : ℕ) : ScheduledEulerStep (c.construction.tip n) c.envelopeConstant c.radiusExponent :=
  c.successor n (c.construction.trace n).1 (c.construction.trace n).2

theorem stage_velocity_eq (n : ℕ) :
    (c.construction.stage (n + 2)).velocity = (c.selectedStep n).stage.cutoff.velocity :=
  (c.selectedStep n).velocity_eq

theorem stage_residual_eq (n : ℕ) :
    (c.construction.stage (n + 2)).residual = (c.selectedStep n).stage.cutoff.residual := by
  change momentumResidual _ (c.construction.stage (n + 2)).velocity
    (c.selectedStep n).step.child.pressure = _
  rw [c.stage_velocity_eq n, (c.selectedStep n).pressure_eq]
  rfl

theorem stage_oscillation_eq (n : ℕ) :
    c.construction.stages.oscillation (n + 2) = (c.selectedStep n).selected.approximation.oscillation :=
  (c.selectedStep n).oscillation_eq

end ScheduledEulerConstruction

/-- Uniform physical estimates supply the cutoffs before the choice of the
common frequency and order schedule. -/
def UniformPhysicalEstimates (ι : Type*) : Prop :=
  ∀ (C Cenv : ℝ) (aMin : ℕ), 2 ≤ C → 0 ≤ Cenv →
    ∃ (a p r power : ℕ) (cutoffConstant initialFloor : ℝ) (cost : StepCosts ι),
      aMin ≤ a ∧ (∀ depth, 1 ≤ cost.step depth) ∧
      (∀ (P : InductiveEulerParameters), initialFloor ≤ P.frequency 0 →
        P.strengthConstant = C → P.StepNumericalBudget 0 a p r power cutoffConstant cost →
        ∀ d : InductiveFirstWaveSelection P a,
        ∃ s : ScheduledPhysicalStage (activation := 0) d.parent d.approximation d.properties a,
          s.symbol = dyadicMultiplierCutoff) ∧
      (∀ {P : InductiveEulerParameters} {n : ℕ} {h : P.LifetimeBounds}
        {tip : InductiveEulerTip P n}, InductiveEulerPrefix P h n tip →
        initialFloor ≤ P.frequency 0 → P.strengthConstant = C →
        P.StepNumericalBudget (n + 1) a p r power cutoffConstant cost →
        ∀ d : tip.SelectedLaterInput Cenv a,
        ∃ s : ScheduledPhysicalStage tip.parent d.approximation d.properties a,
          s.symbol = dyadicMultiplierCutoff)

set_option maxHeartbeats 1500000 in
/-- A schedule can also bound further fixed-order constants. Its output
still determines the same physical stages and cutoffs for every prefix. -/
theorem exists_scheduledEulerConstruction {ι : Type*} (hEstimates : UniformPhysicalEstimates ι)
    (additional : ℕ → InductiveEulerParameters → Prop)
    (schedule : ∀ (cost : StepCosts ι) (a p r power comparison : ℕ)
      (strength cutoffConstant initialFloor : ℝ), 240 ≤ comparison → 2 ≤ strength →
      (∀ depth, 1 ≤ cost.step depth) →
      ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ), Monotone threshold ∧ ∀ N ≥ N₁,
        ∃ P : InductiveEulerParameters, P.exponentParameter = b ∧ P.threshold = threshold ∧
          P.frequency 0 = N ∧ P.comparisonConstant = comparison ∧
          P.strengthConstant = strength ∧ initialFloor ≤ P.frequency 0 ∧
          Real.exp 4 ≤ P.frequency 0 ∧ P.LifetimeBounds ∧
          (∀ i, P.StepNumericalBudget i a p r power cutoffConstant cost) ∧ additional a P)
    (N₀ : ℝ) (radiusFloor : ℕ) :
    ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ), Monotone threshold ∧ ∀ N ≥ N₁,
      ∃ (P : InductiveEulerParameters) (c : ScheduledEulerConstruction P),
        P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧
          N₀ ≤ P.frequency 0 ∧ P.strengthConstant = 18 * Real.exp 3 ∧
          radiusFloor ≤ c.radiusExponent ∧ additional c.radiusExponent P := by
  let C : ℝ := 18 * Real.exp 3
  have hC : 2 ≤ C := by
    dsimp [C]
    linarith [Real.add_one_le_exp (3 : ℝ)]
  obtain ⟨NF, _, hFirst⟩ := exists_inductiveFirstWaveSelection_threshold
  obtain ⟨C₀, NS, Cenv, A, hC₀, _, hCenv, hA, hLater⟩ :=
    InductiveEulerTip.exists_selectedLaterInput_threshold C hC
  obtain ⟨a,p,r,power,cutoffConstant,NA,cost,ha,hΓ,hFirstEstimates,hLaterEstimates⟩ :=
    hEstimates C Cenv (max A radiusFloor) hC hCenv
  have ha₀ : A ≤ a := (le_max_left _ _).trans ha
  have ha₁ : radiusFloor ≤ a := (le_max_right _ _).trans ha
  let init := max N₀ (max NF (max NS NA))
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ :=
    schedule cost a p r power C₀ C cutoffConstant init hC₀ hC hΓ
  refine ⟨b, threshold, N₁, hMono, fun N hN => ?_⟩
  obtain ⟨P, hb, hThreshold, hFrequency, hCompare, hStrength, hInit, hLarge, hLife, hBudget, hAdditional⟩ :=
    hSchedule N hN
  have hNF : NF ≤ P.frequency 0 := (le_max_left _ _).trans ((le_max_right _ _).trans hInit)
  have hNS : NS ≤ P.frequency 0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hInit))
  have hNA : NA ≤ P.frequency 0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hInit))
  have first : Nonempty (ScheduledEulerBase P a) := by
    obtain ⟨d⟩ := hFirst P hNF hLife a (hA.trans ha₀)
    obtain ⟨s, hSymbol⟩ := hFirstEstimates P hNA hStrength (hBudget 0) d
    obtain ⟨base, hVelocity, hPressure, hParent, hOscillation⟩ := d.exists_base hLife s
    exact ⟨⟨d, s, hSymbol, base, hVelocity, hPressure, hParent, hOscillation⟩⟩
  have later (n : ℕ) (tip : InductiveEulerTip P n) (pre : InductiveEulerPrefix P hLife n tip) :
      Nonempty (ScheduledEulerStep tip Cenv a) := by
    obtain ⟨d⟩ := hLater tip pre hNS hStrength hCompare a ha₀
    obtain ⟨s, hSymbol⟩ := hLaterEstimates pre hNA hStrength (hBudget (n + 1)) d
    obtain ⟨step, hVelocity, hPressure, hOscillation⟩ :=
      d.exists_inductiveEulerStep pre s hLarge (le_of_eq hStrength.symm)
    exact ⟨⟨d, s, hSymbol, step, hVelocity, hPressure, hOscillation⟩⟩
  exact ⟨P, ⟨hLife, a, Cenv, Classical.choice first, fun n tip pre => Classical.choice (later n tip pre)⟩,
    hb, hThreshold, hFrequency, (le_max_left _ _).trans hInit, hStrength, ha₁, hAdditional⟩

/-- The basic fixed-order costs are selected once for all sufficiently large initial frequencies. -/
theorem exists_scheduledEulerConstruction_of_uniformPhysicalEstimates {ι : Type*} [Fintype ι]
    (hEstimates : UniformPhysicalEstimates ι) (N₀ : ℝ) :
    ∃ (b : ℕ) (threshold : ℕ → ℝ) (N₁ : ℝ), Monotone threshold ∧ ∀ N ≥ N₁,
      ∃ (P : InductiveEulerParameters) (_c : ScheduledEulerConstruction P),
        P.exponentParameter = b ∧ P.threshold = threshold ∧ P.frequency 0 = N ∧ N₀ ≤ P.frequency 0 ∧
        P.strengthConstant = 18 * Real.exp 3 := by
  obtain ⟨b, threshold, N₁, hMono, hSchedule⟩ := exists_scheduledEulerConstruction hEstimates (fun _ _ => True) (by
    intro cost a p r power comparison strength cutoffConstant initialFloor hComparison hStrength hΓ
    let b := stepExponentFloor a p r power
    obtain ⟨N₁, hChoose⟩ := exists_of_inductiveStepCosts cost a p r power b comparison strength
      cutoffConstant initialFloor le_rfl hComparison hStrength hΓ
    refine ⟨b, fixedOrderThreshold b cost.table, N₁, fixedOrderThreshold_mono b cost.table, fun N hN => ?_⟩
    obtain ⟨Q, hb, hc, hs, hThreshold, hFreq, hFloor, hLarge, hLife, hBudget⟩ := hChoose N hN
    exact ⟨Q, hb, hThreshold, hFreq, hc, hs, hFloor, hLarge, hLife, hBudget, trivial⟩) N₀ 0
  refine ⟨b, threshold, N₁, hMono, fun N hN => ?_⟩
  obtain ⟨P, c, hb, hThreshold, hFreq, hFloor, hC, _, _⟩ := hSchedule N hN
  exact ⟨P, c, hb, hThreshold, hFreq, hFloor, hC⟩

/-- The physical stages with their basic numerical schedule prove the main theorem. -/
theorem theorem11_of_uniformPhysicalEstimates {ι : Type*} [Fintype ι]
    (hEstimates : UniformPhysicalEstimates ι) : Theorem11 := by
  obtain ⟨N₀, hLimit⟩ := theorem11_of_inductiveEulerStages
  obtain ⟨_, _, N₁, _, hSchedule⟩ := exists_scheduledEulerConstruction_of_uniformPhysicalEstimates hEstimates N₀
  obtain ⟨P, c, _, _, _, hN, _⟩ := hSchedule N₁ le_rfl
  exact hLimit c.construction.stages c.construction.centralWaves hN

end

end TorusEuler
