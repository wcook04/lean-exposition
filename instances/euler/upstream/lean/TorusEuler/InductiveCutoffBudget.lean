import TorusEuler.PhysicalWaveStageClosure
import TorusEuler.InductiveStepNumericalBudgets

/-! Uniform Fourier cutoff estimates for the physical hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler

open HierarchyTwistedProfile

/-- The fixed real dyadic cutoff gives one residual and pressure constant
and depth-dependent tail constants for all physical stages. -/
theorem exists_inductiveCutoffBudget :
    ∃ (C : ℝ) (K : ℕ → ℝ), 0 ≤ C ∧ (∀ depth, 0 ≤ K depth) ∧
      ∀ {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {q : Pressure}
        {hT : 0 < T} {d : ParentGeometry hT U X k} {depth : ℕ}
        (b : PhysicalApproximationData d q depth) (properties : PhysicalApproximationProperties b)
        {Λ : ℝ}, 2 ≤ depth → 1 ≤ Λ →
        ∃ s : TruncatedChildStage T Λ dyadicMultiplierCutoff b.velocity b.residual,
          s.CutoffBounds (b.potential properties) depth C (K depth) := by
  classical
  obtain ⟨C, hC, hCutoff⟩ := TruncatedChildStage.exists_cutoffBounds
    (fun ξ h => dyadicMultiplierCutoff_zero ξ h.le) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit
  let K (depth : ℕ) : ℝ := if h : 2 ≤ depth then (hCutoff depth h).choose else 0
  have hK (depth : ℕ) : 0 ≤ K depth := by
    by_cases h : 2 ≤ depth
    · simp only [K, dite_eq_left h]
      exact (hCutoff depth h).choose_spec.1
    · simp [K, h]
  refine ⟨C, K, hC, hK, ?_⟩
  intro T k U X q hT d depth b properties Λ hDepth hΛ
  obtain ⟨s⟩ := properties.nonempty_cutoffStage dyadicMultiplierCutoff.neg Λ
  refine ⟨s, ?_⟩
  simp only [K, dite_eq_left hDepth]
  exact (hCutoff depth hDepth).choose_spec.2 hT hΛ s (b.potential properties)
    properties.velocity_smooth properties.residual_smooth properties.divergence_free
    properties.momentum_of_potential

namespace HierarchyTwistedProfile.PhysicalApproximationProperties

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {q : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : InductiveEulerParameters} {i : ℕ}
  {b : PhysicalApproximationData d q (P.stepDepth i)}
  {ι : Type*} {cost : InductiveEulerParameters.StepCosts ι} {a p r absolutePower : ℕ} {C : ℝ}
  {ψ : Vec3 → ℝ}

/-- At the scheduled cutoff radius, the physical truncation error is
absorbed by the fifth inverse power of the following frequency. -/
theorem cutoff_error_of_stepBudget (properties : PhysicalApproximationProperties b)
    (num : P.StepNumericalBudget i a p r absolutePower C cost)
    (s : TruncatedChildStage T (P.frequency (i + 1) ^ 5) ψ b.velocity b.residual)
    (hSize : ∀ t ∈ Icc 0 T, 1 + spatialHolderHalfNorm (P.stepDepth i) (b.velocity t) ≤
      3 * P.frequency (i + 1) ^ (2 * (P.stepDepth i + 1))) :
    ∀ t ∈ Icc 0 T, cost.cutoffTail (P.stepDepth i) * s.truncationError (P.stepDepth i) t ≤
      P.frequency (i + 2) ^ (-5 : ℝ) := by
  intro t ht
  have hSlice : ContDiff ℝ ∞ (b.velocity t) :=
    contDiffOn_univ.mp (properties.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hV := spatialHolderHalf_of_contDiff_periodic hSlice (properties.periodic t ht).1 (P.stepDepth i)
  have hNorm : 0 ≤ spatialHolderHalfNorm (P.stepDepth i) (b.velocity t) :=
    (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hV (Nat.zero_le _) 0)
  have hf : 0 < P.frequency (i + 1) := zero_lt_two.trans_le num.child_ge_two
  have hErr : 0 ≤ s.truncationError (P.stepDepth i) t := by
    unfold TruncatedChildStage.truncationError
    positivity
  refine (mul_le_mul_of_nonneg_right num.cutoff_tail_le hErr).trans ?_
  have hVsize := hSize t ht
  unfold TruncatedChildStage.truncationError
  rw [P.frequency_step (i + 1), P.frequency_step i]
  rw [P.frequency_step i] at hVsize
  exact frequencySchedule_truncation_error_budget num.parent_ge_two P.exponentParameter_ge hNorm hVsize

/-- The selected cutoff has a smooth, periodic and divergence-free tail
of the size needed by the child deformation estimate. -/
theorem cutoffTail_of_stepBudget (properties : PhysicalApproximationProperties b)
    (num : P.StepNumericalBudget i a p r absolutePower C cost)
    (s : TruncatedChildStage T (P.frequency (i + 1) ^ 5) ψ b.velocity b.residual)
    (hCutoff : s.CutoffBounds (b.potential properties) (P.stepDepth i) C (cost.cutoffTail (P.stepDepth i)))
    (hSize : ∀ t ∈ Icc 0 T, 1 + spatialHolderHalfNorm (P.stepDepth i) (b.velocity t) ≤
      3 * P.frequency (i + 1) ^ (2 * (P.stepDepth i + 1))) :
    let tail : Velocity := fun t => s.velocity t - b.velocity t
    ContDiffOn ℝ ∞ (Function.uncurry tail) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (tail t) ∧ (∀ x, divergence (tail t) x = 0) ∧
        SpatialHolderHalf 2 (tail t) ∧ spatialHolderHalfNorm 2 (tail t) ≤ P.frequency (i + 1) ^ (-5 / 2 : ℝ) :=
  s.cutoffTail_for_childFlow (b.potential properties) hCutoff properties.velocity_smooth
    properties.divergence_free ((le_max_left _ _).trans num.order_le_depth)
    (one_le_two.trans num.child_ge_two) num.child_le_next (properties.cutoff_error_of_stepBudget num s hSize)

end HierarchyTwistedProfile.PhysicalApproximationProperties

end TorusEuler
