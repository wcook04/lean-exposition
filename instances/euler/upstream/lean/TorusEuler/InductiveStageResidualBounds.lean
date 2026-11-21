import TorusEuler.InductiveProfileBounds
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.InductiveStepNumericalBudgets

/-! The scheduled residual of the exact selected hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler

open HierarchyTwistedProfile LocalizedAmplitude

noncomputable section

namespace InductiveEulerStage

/-- The measured tail prefactor at the derivative reserve of the scheduled depth. -/
def scheduledResidualTailCost (K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  let Kdepth := K ((depth + 1) + 3 * depth)
  let C := hierarchyLevelConstant depth Kdepth depth
  2 * Kdepth * (C + 1) ^ 2 *
    (1 + ((hierarchyTailPairs depth 0).card : ℝ) + 2 * ((hierarchyTailPairs depth 1).card : ℝ))

/-- The joint graph prefactor for the depth tail and the primary switch profile. -/
def scheduledResidualStepCost (coefficient K : ℕ → ℝ) (primaryCost : ℝ) (depth : ℕ) : ℝ :=
  6 * ((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * stageCoframeOrderConstant coefficient 2)) ^ (2 : ℕ) *
    (4 ^ (2 : ℕ) * scheduledResidualTailCost K depth + primaryCost)

/-- The common parent power for the two order-two graph estimates. -/
def scheduledResidualParentExponent (a primaryPower : ℕ) : ℕ :=
  (max a 1 + 1) * 2 + primaryPower

theorem scheduledResidualTailCost_nonneg {K : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (depth : ℕ) : 0 ≤ scheduledResidualTailCost K depth := by
  have h := hK ((depth + 1) + 3 * depth)
  unfold scheduledResidualTailCost
  positivity

theorem scheduledResidualStepCost_nonneg {coefficient K : ℕ → ℝ} {primaryCost : ℝ}
    (hK : ∀ m, 0 ≤ K m) (hPrimary : 0 ≤ primaryCost) (depth : ℕ) :
    0 ≤ scheduledResidualStepCost coefficient K primaryCost depth := by
  have h := scheduledResidualTailCost_nonneg hK depth
  unfold scheduledResidualStepCost
  positivity

/-- The separate graph factors lie under the common scheduled residual cap. -/
theorem scheduledResidualGraphCaps (coefficient K : ℕ → ℝ) (primaryCost : ℝ) (depth : ℕ)
    {D Γ : ℝ} {a primaryPower b : ℕ} (hD : 1 ≤ D)
    (hK : ∀ m, 0 ≤ K m) (hPrimary : 0 ≤ primaryCost)
    (hCost : scheduledResidualStepCost coefficient K primaryCost depth ≤ Γ)
    (hPower : scheduledResidualParentExponent a primaryPower ≤ b) :
    (6 * (((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * stageCoframeOrderConstant coefficient 2)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * scheduledResidualTailCost K depth) * D ^ ((max a 1 + 1) * 2) ≤ Γ * D ^ b) ∧
    (6 * (((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * stageCoframeOrderConstant coefficient 2)) ^ (2 : ℕ)) *
      primaryCost * D ^ ((max a 1 + 1) * 2 + primaryPower) ≤ Γ * D ^ b) := by
  let G := 6 * ((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * stageCoframeOrderConstant coefficient 2)) ^ (2 : ℕ)
  let tail := (4 : ℝ) ^ (2 : ℕ) * scheduledResidualTailCost K depth
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hTail : 0 ≤ tail :=
    mul_nonneg (by norm_num) (scheduledResidualTailCost_nonneg hK depth)
  have hΓ : 0 ≤ Γ := (scheduledResidualStepCost_nonneg (coefficient := coefficient) hK hPrimary depth).trans hCost
  have hT : G * tail ≤ Γ :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hPrimary) hG).trans hCost
  have hP : G * primaryCost ≤ Γ :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hTail) hG).trans hCost
  have hPowTail : (max a 1 + 1) * 2 ≤ b :=
    (Nat.le_add_right _ _).trans hPower
  exact ⟨mul_le_mul hT (pow_le_pow_right₀ hD hPowTail)
      (pow_nonneg (zero_le_one.trans hD) _) hΓ,
    mul_le_mul hP (pow_le_pow_right₀ hD hPower)
      (pow_nonneg (zero_le_one.trans hD) _) hΓ⟩


/-- At every scheduled depth the order reserve for an order-two tail
is already included in the one used for the velocity readout. -/
theorem scheduledResidualTailCost_eq_of_profileBounds (K : ℕ → ℝ) {depth : ℕ}
    (hDepth : 2 ≤ depth) :
    let H := max (depth + 1) 3 + 3 * depth
    let C := hierarchyLevelConstant depth (K H) depth
    2 * K H * (C + 1) ^ 2 *
      (1 + ((hierarchyTailPairs depth 0).card : ℝ) + 2 * ((hierarchyTailPairs depth 1).card : ℝ)) =
      scheduledResidualTailCost K depth := by
  have hOrder : 3 ≤ depth + 1 := by omega
  simp [scheduledResidualTailCost, max_eq_left hOrder]

/-- The residual exponent for the actual primary-curl estimate. -/
theorem scheduledResidualParentExponent_of_primary {a : ℕ} (ha : 1 ≤ a) :
    scheduledResidualParentExponent a (a + 27) = 3 * a + 29 := by
  unfold scheduledResidualParentExponent
  rw [max_eq_left ha]
  omega

namespace OnSlab

variable {P : InductiveEulerParameters} {i : ℕ} {activationOld T : ℝ}
  {parent : InductiveEulerStage P i activationOld} {hT : 0 < T} {k : Vec3}
  {ι : Type*} {cost : InductiveEulerParameters.StepCosts ι}
  {a jetPower lossPower absolutePower primaryPower : ℕ}
  {cutoffConstant primaryCost : ℝ} {coefficient K : ℕ → ℝ}

local notation "depth" => P.stepDepth i
local notation "parentFreq" => P.frequency i
local notation "freq" => P.frequency (i + 1)
local notation "nextFreq" => P.frequency (i + 2)
local notation "D" => parentFreq ^ (9 : ℕ)
local notation "radius" => (D ^ a)⁻¹
local notation "width" => freq ^ (-1 / 2 : ℝ)
local notation "I" => Icc (0 : ℝ) T
local notation "graphConstant" => stageCoframeOrderConstant coefficient 2

set_option maxHeartbeats 1200000 in
/-- The exact order-two depth tail gives the scheduled residual estimate
for the selected first wave with both activation sources zero. -/
theorem residual_of_scheduledZeroSwitch
    (d : parent.OnSlab hT k) (cfg : PhysicalApproximationData d.geometry parent.pressure depth)
    (num : P.StepNumericalBudget i a jetPower lossPower absolutePower cutoffConstant cost)
    (caps : StageCoefficientCaps d a D radius width freq coefficient)
    (hCoefficient : ∀ m, 0 ≤ coefficient m) (hK : ∀ m, 0 ≤ K m)
    (hPrimaryCost : 0 ≤ primaryCost)
    (hCost : scheduledResidualStepCost coefficient K primaryCost depth ≤ cost.step depth)
    (hPower : scheduledResidualParentExponent a primaryPower ≤ absolutePower)
    (hTail : unweightedSeminorm False radius width 2 hT (cfg.operators.remainder cfg.profiles depth) ≤
      scheduledResidualTailCost K depth * freq ^ hierarchyOscExponent (depth + 1))
    (hLeading : cfg.leading.leadingSwitch = 0) (hCompletion : cfg.leading.completionSwitch = 0) :
    ∀ t ∈ I, SpatialHolderHalf 1 (cfg.residual t) ∧
      spatialHolderHalfNorm 1 (cfg.residual t) ≤ nextFreq ^ (-7 / 2 : ℝ) := by
  have hμ : 1 ≤ parentFreq := one_le_two.trans num.parent_ge_two
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hCaps := scheduledResidualGraphCaps coefficient K primaryCost depth hD hK hPrimaryCost
    hCost (hPower.trans num.absolute_exponent)
  have hRaw := cfg.residual_size_of_zeroSwitchGraph
    (a := a) (bExp := P.exponentParameter) (qNext := P.order (i + 2))
    (Ctail := scheduledResidualTailCost K depth) (L := graphConstant) (μ := parentFreq)
    hLeading hCompletion d.deformationOn.flow d.smooth_velocity (fun t _ => parent.periodic_velocity t)
    caps.label_pos caps.phase_pos hD num.child_ge_two (stageCoframeOrderConstant_ge_one coefficient hCoefficient 2)
    (scheduledResidualTailCost_nonneg hK depth) caps.label_inverse.le rfl caps.carrier
    (caps.scaledCoframe 2) hTail (by simpa only [mul_assoc] using hCaps.1)
    P.exponentParameter_ge hμ rfl num.step_rate_mul_parent
  simpa only [← P.frequency_step (i + 1)] using hRaw

set_option maxHeartbeats 1500000 in
/-- The same tail budget and the exact primary-curl activation estimate
give the scheduled residual bound for the chosen later wave. -/
theorem residual_of_scheduledLaterSwitch
    (d : parent.OnSlab hT k) (cfg : PhysicalApproximationData d.geometry parent.pressure depth)
    (num : P.StepNumericalBudget i a jetPower lossPower absolutePower cutoffConstant cost)
    (caps : StageCoefficientCaps d a D radius width freq coefficient)
    (hCoefficient : ∀ m, 0 ≤ coefficient m) (hK : ∀ m, 0 ≤ K m)
    (hPrimaryCost : 0 ≤ primaryCost)
    (hCost : scheduledResidualStepCost coefficient K primaryCost depth ≤ cost.step depth)
    (hPower : scheduledResidualParentExponent a primaryPower ≤ absolutePower)
    (hTail : unweightedSeminorm False radius width 2 hT (cfg.operators.remainder cfg.profiles depth) ≤
      scheduledResidualTailCost K depth * freq ^ hierarchyOscExponent (depth + 1))
    {t₀ r Cenv : ℝ} {center : ℝ → Vec3}
    (w : SeedOn (fun t x => fderiv ℝ (parent.velocity t) (parent.flow 0 t x))
      (fun t x => labelWaveVector parent.flow 0 x k t) center t₀ T radius D Cenv)
    (reg : w.HierarchyRegularity r width)
    (hEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : cfg.leading = PhysicalLeadingInput.ofLaterWave d.geometry w reg
      d.deformationOn.flow d.smooth_velocity (fun t _ => parent.periodic_velocity t)
      (fun t ht => parent.odd_velocity t (d.subset ht)) hEven)
    (hPrimary : ∀ t ∈ Icc t₀ T, PhaseJetBound 2
      ((freq ^ (3 / 4 : ℝ) * ‖center t‖) * (primaryCost * D ^ primaryPower * freq ^ (-5 / 4 : ℝ)))
      (scaledPhaseProfile radius width (PhysicalApproximationData.activationPrimary
        (h := width) w d.geometry.inverse t)))
    (hSwitch : ∀ t ∈ Icc t₀ T,
      |deriv (waveSwitch t₀ r) t| * (freq ^ (3 / 4 : ℝ) * ‖center t‖) ≤
        parentFreq * nextFreq ^ (-4 : ℝ)) :
    ∀ t ∈ I, SpatialHolderHalf 1 (cfg.residual t) ∧
      spatialHolderHalfNorm 1 (cfg.residual t) ≤ nextFreq ^ (-7 / 2 : ℝ) := by
  have hμ : 1 ≤ parentFreq := one_le_two.trans num.parent_ge_two
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hΓ (t : ℝ) (_ : t ∈ Icc t₀ T) : 0 ≤ freq ^ (3 / 4 : ℝ) * ‖center t‖ :=
    mul_nonneg (Real.rpow_nonneg (zero_le_two.trans num.child_ge_two) _) (norm_nonneg _)
  have hCaps := scheduledResidualGraphCaps coefficient K primaryCost depth hD hK hPrimaryCost
    hCost (hPower.trans num.absolute_exponent)
  have hRaw := cfg.residual_size_of_actualLaterGraph
    (a := a) (p := primaryPower) (bExp := P.exponentParameter) (qNext := P.order (i + 2))
    (Ctail := scheduledResidualTailCost K depth) (L := graphConstant) (μ := parentFreq)
    w reg d.deformationOn.flow d.smooth_velocity (fun t _ => parent.periodic_velocity t)
    (fun t ht => parent.odd_velocity t (d.subset ht)) hEven hLeading
    hD num.child_ge_two (stageCoframeOrderConstant_ge_one coefficient hCoefficient 2)
    (scheduledResidualTailCost_nonneg hK depth) hPrimaryCost caps.label_inverse.le rfl caps.carrier
    (caps.scaledCoframe 2) hTail hPrimary hΓ
    (fun t ht => by simpa only [← P.frequency_step (i + 1)] using hSwitch t ht)
    (by simpa only [mul_assoc] using hCaps.1) (by simpa only [mul_assoc] using hCaps.2)
    P.exponentParameter_ge hμ rfl num.step_rate_mul_parent
  simpa only [← P.frequency_step (i + 1)] using hRaw

end OnSlab
end InductiveEulerStage

end

end TorusEuler
