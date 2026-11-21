import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.HierarchyStageCoefficientCaps
import TorusEuler.InductiveStepNumericalBudgets
import TorusEuler.HierarchyCentralRemainder

/-! Quantitative readout of the actual velocity profiles on the inductive schedule. -/

open Set
open scoped ContDiff

namespace TorusEuler

open HierarchyTwistedProfile

noncomputable section

namespace InductiveEulerStage

/-- The retained-level constant at the order needed for the cutoff. -/
def scheduledVelocityLevelConstant (K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  hierarchyLevelConstant depth (K ((depth + 1) + 3 * depth)) depth

private def graphCoframeCost (coefficient : ℕ → ℝ) (depth : ℕ) : ℝ :=
  stageCoframeOrderConstant coefficient (depth + 1)

private def graphLevelCost (K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  ((Finset.Icc 1 depth).card : ℝ) * scheduledVelocityLevelConstant K depth

private def scheduledVelocityOscillationCost (coefficient K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  (3 * ((depth : ℝ) + 1)) *
    (((3 : ℝ) * 2 ^ (depth + 1) * (2 * graphCoframeCost coefficient depth)) ^ (depth + 1) *
      (4 ^ (depth + 1) * (2 * graphLevelCost K depth)))

/-- The order-`m` prefactor for the actual mean correction at the chosen depth. -/
def scheduledVelocityMeanCost (coefficient K : ℕ → ℝ) (m depth : ℕ) : ℝ :=
  (3 * ((m : ℝ) + 1)) *
    (((3 : ℝ) * 2 ^ (m + 1) * graphCoframeCost coefficient depth) ^ (m + 1) *
      (4 ^ (m + 1) * graphLevelCost K depth))

private def scheduledVelocityCenterCost (coefficient K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  96 * graphCoframeCost coefficient depth * graphLevelCost K depth +
    24 * graphCoframeCost coefficient depth * graphLevelCost K depth

/-- One fixed-depth prefactor covers the oscillation, the central remainder,
and both full-depth graph norms used in the cutoff estimate. -/
def scheduledVelocityStepCost (coefficient K : ℕ → ℝ) (depth : ℕ) : ℝ :=
  scheduledVelocityOscillationCost coefficient K depth +
    scheduledVelocityMeanCost coefficient K depth depth +
    2 * graphLevelCost K depth + scheduledVelocityCenterCost coefficient K depth

/-- The Fourier-band Bernstein cost for the actual parent in the full-depth estimate. -/
def scheduledVelocityParentCost (bernstein : ℕ → ℝ) (depth : ℕ) : ℝ :=
  (3 * ((depth : ℝ) + 1)) * bernstein depth

/-- Nonnegative coefficient and hierarchy costs give nonnegative velocity readout costs. -/
theorem scheduledVelocityCosts_nonneg {coefficient K : ℕ → ℝ}
    (hCoefficient : ∀ m, 0 ≤ coefficient m) (hK : ∀ m, 0 ≤ K m) (depth : ℕ) :
    0 ≤ scheduledVelocityStepCost coefficient K depth ∧
      ∀ m, 0 ≤ scheduledVelocityMeanCost coefficient K m depth := by
  have hL : 0 ≤ graphCoframeCost coefficient depth :=
    zero_le_one.trans (stageCoframeOrderConstant_ge_one coefficient hCoefficient _)
  have hC : 0 ≤ graphLevelCost K depth :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hierarchyLevelConstant_one_le (hK _) depth))
  constructor
  · unfold scheduledVelocityStepCost scheduledVelocityOscillationCost scheduledVelocityMeanCost
      scheduledVelocityCenterCost
    positivity
  · intro m
    unfold scheduledVelocityMeanCost
    positivity

end InductiveEulerStage

private theorem fullDepth_graphExponent_le {a c b P : ℕ}
    (ha : a ≤ b) (hc : c ≤ b) :
    a * (P + 1) + c ≤ b * (P + 2) := by
  calc
    _ ≤ b * (P + 1) + b := Nat.add_le_add (Nat.mul_le_mul_right _ ha) hc
    _ = _ := by rw [← Nat.mul_succ]

/-- The pure graph exponents use one parent power per differentiation index
and a single extra parent power for the recurrence loss. -/
private theorem fullDepth_velocityGraphBudget {D L C loss Γ : ℝ} {P a ρ b : ℕ}
    (hD : 1 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hLoss₀ : 0 ≤ loss) (hLoss : loss ≤ D ^ ρ)
    (ha : max a 1 + 1 ≤ b) (hρ : 6 * ρ ≤ b)
    (hOscCost : (3 * ((P : ℝ) + 1)) *
      (((3 : ℝ) * 2 ^ (P + 1) * (2 * L)) ^ (P + 1) *
        (4 ^ (P + 1) * (2 * ((Finset.Icc 1 P).card : ℝ) * C))) ≤ Γ)
    (hMeanCost : (3 * ((P : ℝ) + 1)) *
      (((3 : ℝ) * 2 ^ (P + 1) * L) ^ (P + 1) *
        (4 ^ (P + 1) * (((Finset.Icc 1 P).card : ℝ) * C))) ≤ Γ) :
    (3 * ((P : ℝ) + 1)) *
      ((((3 : ℝ) * 2 ^ (P + 1) * (2 * L)) ^ (P + 1) *
        (4 ^ (P + 1) * (2 * ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 2))) *
        D ^ ((max a 1 + 1) * (P + 1))) ≤ Γ * D ^ (b * (P + 2)) ∧
    (3 * ((P : ℝ) + 1)) *
      ((((3 : ℝ) * 2 ^ (P + 1) * L) ^ (P + 1) *
        (4 ^ (P + 1) * (((Finset.Icc 1 P).card : ℝ) * C * loss ^ 6))) *
        D ^ ((a + 1) * (P + 1))) ≤ Γ * D ^ (b * (P + 2)) := by
  let O := (3 * ((P : ℝ) + 1)) *
    (((3 : ℝ) * 2 ^ (P + 1) * (2 * L)) ^ (P + 1) *
      (4 ^ (P + 1) * (2 * ((Finset.Icc 1 P).card : ℝ) * C)))
  let M := (3 * ((P : ℝ) + 1)) *
    (((3 : ℝ) * 2 ^ (P + 1) * L) ^ (P + 1) *
      (4 ^ (P + 1) * (((Finset.Icc 1 P).card : ℝ) * C)))
  have hO₀ : 0 ≤ O := by dsimp only [O]; positivity
  have hM₀ : 0 ≤ M := by dsimp only [M]; positivity
  have hΓ : 0 ≤ Γ := hO₀.trans hOscCost
  have hLossPow (s : ℕ) : loss ^ s ≤ D ^ (s * ρ) := by
    rw [Nat.mul_comm s, pow_mul]
    exact pow_le_pow_left₀ hLoss₀ hLoss _
  constructor
  · calc
      _ = O * (loss ^ 2 * D ^ ((max a 1 + 1) * (P + 1))) := by dsimp only [O]; ring
      _ ≤ O * (D ^ (2 * ρ) * D ^ ((max a 1 + 1) * (P + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hLossPow 2) (by positivity)) hO₀
      _ ≤ Γ * D ^ (2 * ρ + (max a 1 + 1) * (P + 1)) := by
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right hOscCost (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hΓ
        rw [Nat.add_comm (2 * ρ)]
        exact pow_le_pow_right₀ hD (fullDepth_graphExponent_le ha (by omega))
  · calc
      _ = M * (loss ^ 6 * D ^ ((a + 1) * (P + 1))) := by dsimp only [M]; ring
      _ ≤ M * (D ^ (6 * ρ) * D ^ ((a + 1) * (P + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hLossPow 6) (by positivity)) hM₀
      _ ≤ Γ * D ^ (6 * ρ + (a + 1) * (P + 1)) := by
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right hMeanCost (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hΓ
        rw [Nat.add_comm (6 * ρ)]
        exact pow_le_pow_right₀ hD
          (fullDepth_graphExponent_le ((Nat.add_le_add_right (le_max_left a 1) 1).trans ha) hρ)

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ} {k : Vec3}
  {hT : 0 < P.slab (n + 1) activation}

local notation "T" => P.slab (n + 1) activation
local notation "depth" => P.stepDepth n
local notation "childOrder" => P.order (n + 1)
local notation "μ" => P.frequency n
local notation "freq" => P.frequency (n + 1)
local notation "D" => (μ ^ (9 : ℕ))
local notation "width" => (freq ^ (-1 / 2 : ℝ))
local notation "I" => Icc (0 : ℝ) T

/-- The velocity readout of the same finite hierarchy used by the cutoff. -/
structure ScheduledPhysicalVelocityBounds (parent : InductiveEulerStage P n activationOld)
    {g : ParentGeometry hT parent.velocity parent.flow k}
    (cfg : PhysicalApproximationData g parent.pressure depth) (Cstep Cmean : ℝ) : Prop where
  velocity_size : ∀ t ∈ I,
    1 + spatialHolderHalfNorm depth (cfg.velocity t) ≤ 3 * freq ^ (2 * (depth + 1))
  oscillation_size : ∀ t ∈ I, ∀ x, ‖cfg.oscillation t x‖ ≤ Cstep * freq ^ (-5 / 4 : ℝ)
  mean_size : ∀ m ≤ childOrder, ∀ t ∈ I, SpatialHolderHalf m (cfg.meanCorrection t) ∧
    spatialHolderHalfNorm m (cfg.meanCorrection t) ≤
      Cmean * D ^ (P.exponentParameter * (m + 2)) * freq ^ (-5 / 2 : ℝ)
  center : ∀ t ∈ Icc activation T,
    ‖fderiv ℝ (cfg.oscillationRemainder t) 0‖ + ‖fderiv ℝ (cfg.meanCorrection t) 0‖ ≤
      Cstep * freq ^ (-5 / 12 : ℝ)

namespace InductiveEulerStage.OnSlab

set_option maxHeartbeats 2500000 in
/-- Read the cutoff-order velocity, low-order mean, oscillation, and central
remainder from one measured hierarchy with the same fixed schedule costs. -/
theorem scheduledPhysicalVelocityBounds {ι : Type*} [Fintype ι]
    (parent : InductiveEulerStage P n activationOld)
    (d : parent.OnSlab hT k) (cfg : PhysicalApproximationData d.geometry parent.pressure depth)
    (properties : PhysicalApproximationProperties cfg)
    {a p r absolutePower : ℕ} {cutoffConstant : ℝ} {cost : InductiveEulerParameters.StepCosts ι}
    (budget : P.StepNumericalBudget n a p r absolutePower cutoffConstant cost)
    {coefficient K bernstein : ℕ → ℝ}
    (hCoefficient : ∀ m, 0 ≤ coefficient m) (hK : ∀ m, 0 ≤ K m)
    (hAnalytic : ∀ t ∈ Icc 0 (P.slab n activationOld),
      PhaseJetBound (depth + 1) (bernstein depth * μ ^ (5 * (depth + 1) + 1)) (parent.velocity t))
    (parentIndex : ι)
    (hParentCost : scheduledVelocityParentCost bernstein depth ≤ |cost.analytic parentIndex depth depth|)
    (hStepCost : scheduledVelocityStepCost coefficient K depth ≤ cost.step depth)
    (hMeanCost : scheduledVelocityMeanCost coefficient K childOrder depth ≤ cost.mean childOrder depth)
    (hAbsolute : max a 1 + 1 + 6 * r ≤ absolutePower)
    (caps : StageCoefficientCaps d a D ((D ^ a)⁻¹) width freq coefficient)
    (ht₀ : 0 ≤ activation) (htT : activation ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc activation T))
    (hγpos : ∀ t ∈ Icc activation T, 0 < γ t)
    (hγone : ∀ t ∈ Icc activation T, γ t ≤ 1)
    {support : Set Vec3} (hClosed : IsClosed support) (hInactive : cfg.leading.Inactive activation support)
    (hLevels : ∀ m ≤ depth + 1, ∀ i ∈ Finset.Icc 1 depth, HierarchyLevelBound
      (actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch cfg.parentResidual
        freq (zero_le_two.trans budget.child_ge_two) ((D ^ a)⁻¹) width hT ht₀ htT γ hγ hγpos)
      freq (D ^ r) (scheduledVelocityLevelConstant K depth) m i) :
    ScheduledPhysicalVelocityBounds parent cfg (cost.step depth * D ^ P.exponentParameter)
      (cost.mean childOrder depth) := by
  let L := graphCoframeCost coefficient depth
  let C := scheduledVelocityLevelConstant K depth
  let B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 := fun t x => fderiv ℝ (parent.flow t 0) (parent.flow 0 t x)
  let Γ := cost.step depth
  let ℓ : ℝ := (D ^ a)⁻¹
  have hμ : 1 ≤ μ := one_le_two.trans budget.parent_ge_two
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hf : 1 ≤ freq := one_le_two.trans budget.child_ge_two
  have hL : 1 ≤ L := stageCoframeOrderConstant_ge_one coefficient hCoefficient _
  have hC : 0 ≤ C := zero_le_one.trans (hierarchyLevelConstant_one_le (hK _) _)
  have hLoss : 1 ≤ D ^ r := one_le_pow₀ hD
  have hDepth : 2 ≤ depth := (le_max_left _ _).trans budget.order_le_depth
  have hOrder : childOrder ≤ depth := (le_max_right _ _).trans budget.order_le_depth
  have hDepth₁ : 1 ≤ depth := (by decide : 1 ≤ 2).trans hDepth
  have hPower : max a 1 + 1 + 6 * r ≤ P.exponentParameter := hAbsolute.trans budget.absolute_exponent
  have hLabel : ℓ⁻¹ ≤ D ^ a := caps.label_inverse.le
  have hGraph : ∀ t ∈ I, ∀ j ≤ depth + 1, ∀ x,
      ℓ ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L * D :=
    caps.scaledCoframe (depth + 1)
  have hinactive : ∀ t ∈ I, t < activation → cfg.oscillation t = 0 :=
    fun t ht hi => funext fun x => (cfg.inactive hDepth₁ hClosed hInactive ht x (Or.inl hi)).1
  have hLevelCost : 0 ≤ graphLevelCost K depth := mul_nonneg (Nat.cast_nonneg _) hC
  have hOscCost : 0 ≤ scheduledVelocityOscillationCost coefficient K depth := by
    unfold scheduledVelocityOscillationCost
    change 0 ≤ (3 * ((depth : ℝ) + 1)) * ((3 * 2 ^ (depth + 1) * (2 * L)) ^ (depth + 1) *
      (4 ^ (depth + 1) * (2 * graphLevelCost K depth)))
    positivity
  have hCostNonneg := scheduledVelocityCosts_nonneg hCoefficient hK depth
  have hMeanDepth₀ := hCostNonneg.2 depth
  have hCenterCost : 0 ≤ scheduledVelocityCenterCost coefficient K depth := by
    change 0 ≤ 96 * L * graphLevelCost K depth + 24 * L * graphLevelCost K depth
    positivity
  have hOscBudget : scheduledVelocityOscillationCost coefficient K depth ≤ Γ := by
    refine le_trans ?_ hStepCost
    unfold scheduledVelocityStepCost
    linarith
  have hMeanDepthBudget : scheduledVelocityMeanCost coefficient K depth depth ≤ Γ := by
    refine le_trans ?_ hStepCost
    unfold scheduledVelocityStepCost
    linarith
  have hSupBudget : 2 * graphLevelCost K depth ≤ Γ := by
    refine le_trans ?_ hStepCost
    unfold scheduledVelocityStepCost
    linarith
  have hCenterBudget : scheduledVelocityCenterCost coefficient K depth ≤ Γ := by
    refine le_trans ?_ hStepCost
    unfold scheduledVelocityStepCost
    linarith
  have hΓ : 0 ≤ Γ := hCostNonneg.1.trans hStepCost
  have hGraphs := fullDepth_velocityGraphBudget (P := depth) (a := a) (ρ := r)
    (b := P.exponentParameter) (L := L) (C := C) (Γ := Γ) hD (zero_le_one.trans hL) hC
    (zero_le_one.trans hLoss) le_rfl (by omega) budget.loss_exponent
    (by simpa only [scheduledVelocityOscillationCost, graphLevelCost, mul_assoc] using hOscBudget)
    (by simpa only [scheduledVelocityMeanCost, graphLevelCost] using hMeanDepthBudget)
  have hParent : scheduledVelocityParentCost bernstein depth ≤ μ :=
    hParentCost.trans (budget.analytic_le parentIndex depth (by omega))
  constructor
  · have hfEq := P.frequency_step n
    let f := μ ^ frequencyExponent P.exponentParameter childOrder
    have hLevels' : ∀ i ∈ Finset.Icc 1 depth, HierarchyLevelBound
        (actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch
          cfg.parentResidual f (pow_nonneg (zero_le_one.trans hμ) _) ℓ width hT ht₀ htT γ hγ hγpos)
        f (D ^ r) C (depth + 1) i := by
      dsimp only [f]
      simpa only [← hfEq] using hLevels (depth + 1) le_rfl
    rw [hfEq]
    exact cfg.velocity_size_of_actualLevels properties hDepth₁ budget.parent_ge_two
      P.exponentParameter_ge caps.label_pos caps.phase_pos hL hLoss hC hLabel
      (congrArg (fun q : ℝ => q ^ (-1 / 2 : ℝ)) hfEq) (hfEq ▸ caps.carrier)
      ht₀ htT γ hγ hγpos hγone hinactive d.smooth_velocity
      caps.inverseSmooth B caps.coframeGraph caps.coframeSmooth hGraph hLevels'
      hGraphs.1 hGraphs.2 budget.gamma_le budget.gamma_le
      (fun t ht => hAnalytic t (d.subset ht)) hParent
  · refine cfg.oscillation_sup_of_actualLevels hDepth₁ hf hLoss hC ht₀ htT γ hγ hγpos hγone
      hinactive (hLevels 0 (Nat.zero_le _)) ?_
    calc
      _ = (2 * graphLevelCost K depth) * D ^ (2 * r) := by
        unfold graphLevelCost
        change 2 * ((Finset.Icc 1 depth).card : ℝ) * C * (D ^ r) ^ 2 =
          2 * (((Finset.Icc 1 depth).card : ℝ) * C) * D ^ (2 * r)
        rw [Nat.mul_comm 2 r, pow_mul]
        ring
      _ ≤ Γ * D ^ P.exponentParameter :=
        mul_le_mul hSupBudget (pow_le_pow_right₀ hD (by omega))
          (pow_nonneg (zero_le_one.trans hD) _) hΓ
  · exact cfg.meanCorrection_holder_of_actualLevels hDepth₁ properties hf hLoss hC
      caps.label_pos hD hL hLabel (show D ^ r ≤ 1 * D ^ r by rw [one_mul])
      budget.radius_exponent budget.loss_exponent ht₀ htT γ hγ hγpos
      (fun m hm => hLevels (m + 1) (Nat.succ_le_succ (hm.trans hOrder))) B
      caps.inverseSmooth caps.coframeGraph caps.coframeSmooth
      (fun t ht j hj => hGraph t ht j (hj.trans (Nat.succ_le_succ hOrder)))
      (by simpa only [scheduledVelocityMeanCost, graphLevelCost, one_pow, mul_one, mul_assoc]
        using hMeanCost)
  · intro t ht
    have hI : t ∈ I := ⟨ht₀.trans ht.1, ht.2⟩
    have hSummed := cfg.velocityProfileSums_of_actualLevels hDepth₁ 1 hf hLoss hC ht₀ htT γ
      hγ hγpos (hLevels 1 (by omega))
    have hOsc := hSummed.2.1
    have hMean := hSummed.2.2
    have hOsc' : amplitudeSeminorm False ℓ width 1 hT ht₀ htT γ hγ hγpos
        (cfg.profiles.velocity depth - cfg.operators.average (cfg.profiles.velocity depth) - cfg.profiles.V 1) ≤
        (2 * graphLevelCost K depth) * D ^ (2 * r) * freq ^ (-23 / 12 : ℝ) := by
      refine hOsc.trans_eq ?_
      unfold graphLevelCost
      rw [Nat.mul_comm 2 r, pow_mul]
      ring
    have hMean' : unweightedSeminorm False ℓ width 1 hT
        (cfg.operators.average (cfg.profiles.velocity depth)) ≤
        graphLevelCost K depth * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ) := by
      simpa only [graphLevelCost, Nat.mul_comm 6 r, pow_mul] using hMean
    have hActual := cfg.norm_centralRemainder_le hDepth₁ ht₀ htT γ hγ hγpos hγone ht
      caps.label_pos caps.phase_pos hD hf hL (by positivity : 0 ≤ 2 * graphLevelCost K depth)
      hLevelCost hLabel rfl caps.carrier (caps.inverseSmooth t hI) (caps.coframeGraph t hI)
      (caps.coframeSmooth t hI) (fun j hj => hGraph t hI j (hj.trans (by omega))) hOsc' hMean'
    refine hActual.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hOscExponent : max a 1 + 1 + 2 * r ≤ P.exponentParameter := by omega
    have hMeanExponent : a + 1 + 6 * r ≤ P.exponentParameter := by
      have := le_max_left a 1
      omega
    calc
      _ ≤ (48 * L * (2 * graphLevelCost K depth)) * D ^ P.exponentParameter +
          (24 * L * graphLevelCost K depth) * D ^ P.exponentParameter :=
        add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hOscExponent) (by positivity))
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hMeanExponent) (by positivity))
      _ = scheduledVelocityCenterCost coefficient K depth * D ^ P.exponentParameter := by
        unfold scheduledVelocityCenterCost
        change _ = (96 * L * _ + 24 * L * _) * _
        ring
      _ ≤ Γ * D ^ P.exponentParameter := mul_le_mul_of_nonneg_right hCenterBudget (by positivity)

end InductiveEulerStage.OnSlab

end

end TorusEuler
