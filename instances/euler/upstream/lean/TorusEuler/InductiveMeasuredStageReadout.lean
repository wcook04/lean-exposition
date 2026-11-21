import TorusEuler.SelectedPhysicalStageSeed
import TorusEuler.InductiveStageVelocityBounds
import TorusEuler.InductiveStageProfileFlowBounds
import TorusEuler.InductiveScheduledReadout
import TorusEuler.InductiveCutoffBudget

/-! Velocity, cutoff, and flow estimates from the measured selected levels. -/

open Set
open scoped InnerProductSpace
open TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.SelectedPhysicalStageSeed

noncomputable section

variable {P : InductiveEulerParameters} {i : ℕ} {oldActivation activation : ℝ}
  {parent : InductiveEulerStage P i oldActivation} {k : Vec3} {hT : 0 < P.slab (i + 1) activation}
  {d : parent.OnSlab hT k} {b : PhysicalApproximationData d.geometry parent.pressure (P.stepDepth i)}
  {ι : Type*} [Fintype ι] {cost : InductiveEulerParameters.StepCosts ι}
  {a r power : ℕ} {seedCost coefficient K bernstein : ℕ → ℝ} {Ccutoff : ℝ}

local notation "T" => P.slab (i + 1) activation
local notation "μ" => P.frequency i
local notation "D" => μ ^ (9 : ℕ)
local notation "freq" => P.frequency (i + 1)
local notation "next" => P.frequency (i + 2)
local notation "depth" => P.stepDepth i
local notation "q" => P.order (i + 1)
local notation "ℓ" => ((D ^ a)⁻¹)
local notation "width" => freq ^ (-1 / 2 : ℝ)
local notation "Clevel" => InductiveEulerStage.scheduledVelocityLevelConstant K depth
local notation "Cstep" => cost.step depth * D ^ P.exponentParameter

set_option maxHeartbeats 2000000 in
/-- The cutoff and its deformation estimates are formed from the same
velocity graph whose full-depth bound is used to estimate the truncation. -/
theorem exists_scheduledPhysicalStage_of_levels
    (s : SelectedPhysicalStageSeed d b a seedCost) (properties : PhysicalApproximationProperties b)
    (num : P.StepNumericalBudget i a (profileFlowJetPower r) r power Ccutoff cost)
    (hCoefficient : ∀ m, 0 ≤ coefficient m) (hK : ∀ m, 1 ≤ K m)
    (caps : InductiveEulerStage.StageCoefficientCaps d a D ℓ width freq coefficient)
    (hBernstein : ∀ t ∈ Icc 0 (P.slab i oldActivation),
      PhaseJetBound (depth + 1) (bernstein depth * μ ^ (5 * (depth + 1) + 1)) (parent.velocity t))
    (parentIndex : ι)
    (hParentCost : InductiveEulerStage.scheduledVelocityParentCost bernstein depth ≤
      |cost.analytic parentIndex depth depth|)
    (hStepCost : InductiveEulerStage.scheduledVelocityStepCost coefficient K depth ≤ cost.step depth)
    (hMeanCost : InductiveEulerStage.scheduledVelocityMeanCost coefficient K q depth ≤ cost.mean q depth)
    (hVelocityPower : max a 1 + 1 + 6 * r ≤ power)
    (hJetCost : 1 + 40 * profileFlowJetConstant coefficient depth Clevel ≤ cost.step depth)
    (hLevels : ∀ m ≤ depth + 1, ∀ j ∈ Finset.Icc 1 depth,
      HierarchyLevelBound (s.measured (zero_le_two.trans num.child_ge_two)) freq (D ^ r) Clevel m j)
    (hKcutoff : 0 ≤ cost.cutoffTail depth) (hCcutoff : 0 ≤ Ccutoff)
    (hCutoff : ∃ cut : TruncatedChildStage T (freq ^ 5) dyadicMultiplierCutoff b.velocity b.residual,
      cut.CutoffBounds (b.potential properties) depth Ccutoff (cost.cutoffTail depth))
    (hResidual : ∀ t ∈ Icc 0 T, spatialHolderHalfNorm 1 (b.residual t) ≤ next ^ (-7 / 2 : ℝ))
    (hPressure : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (b.pressure t)) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (parent.pressure t)) x v⟫_ℝ +
        (Cstep * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2) :
    ∃ step : ScheduledPhysicalStage parent b properties a, step.symbol = dyadicMultiplierCutoff := by
  have hD : 1 ≤ D := one_le_pow₀ (one_le_two.trans num.parent_ge_two)
  have hf : 1 ≤ freq := one_le_two.trans num.child_ge_two
  have hDepth : 2 ≤ depth := (le_max_left _ _).trans num.order_le_depth
  have hClevel : 0 ≤ Clevel := zero_le_one.trans
    (hierarchyLevelConstant_one_le (zero_le_one.trans (hK _)) _)
  have hSupport := isClosed_tsupport (periodizeCentered (radialEnvelope ℓ))
  have hVelocity := InductiveEulerStage.OnSlab.scheduledPhysicalVelocityBounds parent d b properties num hCoefficient
    (fun m => zero_le_one.trans (hK m)) hBernstein parentIndex hParentCost hStepCost hMeanCost
    hVelocityPower caps s.activation_nonneg s.activation_lt.le s.gamma s.weight_continuous
    s.weight_pos s.weight_le_one hSupport s.leading_inactive hLevels
  obtain ⟨cut, hCut⟩ := hCutoff
  have hTail := properties.cutoff_error_of_stepBudget num cut hVelocity.velocity_size
  obtain ⟨hJetNonneg, hJets⟩ := b.pulledBackProfileJetBounds_of_actualLevels caps hD hCoefficient hf
    num.child_le_next properties hDepth cut hCut hTail hClevel s.activation_nonneg s.activation_lt.le
    hSupport s.leading_inactive s.gamma s.weight_continuous s.weight_pos s.weight_le_one
    (fun m hm => hLevels m (hm.trans (hDepth.trans (Nat.le_succ depth))))
  have hScheduled : ∃ sc : TruncatedChildStage T
      ((μ ^ frequencyExponent P.exponentParameter q) ^ 5) dyadicMultiplierCutoff b.velocity b.residual,
    sc.CutoffBounds (b.potential properties) depth Ccutoff (cost.cutoffTail depth) ∧
    sc.PulledBackProfileJetBounds parent.flow b.profileVelocity freq ℓ width
      (profileFlowJetConstant coefficient depth Clevel) D (profileFlowJetPower r) := by
    rw [← P.frequency_step i]
    exact ⟨cut, hCut, hJets⟩
  obtain ⟨hScheduledCut, hScheduledBounds, hScheduledJets⟩ := hScheduled
  exact ⟨ScheduledPhysicalStage.of_actual_readout parent b properties num hScheduledCut hScheduledBounds
    hCcutoff hKcutoff hVelocity.velocity_size hResidual hVelocity.oscillation_size hVelocity.mean_size
    hPressure s.carrier_le hJetNonneg hJetCost hScheduledJets hVelocity.center, rfl⟩

end

end TorusEuler.SelectedPhysicalStageSeed
