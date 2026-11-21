import TorusEuler.TerminalStageFromGraph

/-! Frequency separation absorbs the old-parent powers left by the mixed graph estimates. -/

open Filter Set
open scoped Topology

namespace TorusEuler.ScheduledEulerConstruction

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P)

local notation "slabEnd(" n ")" => c.construction.slab (n + 2)
local notation "parentFreq(" n ")" => P.frequency (n + 1)
local notation "childFreq(" n ")" => P.frequency (n + 2)
local notation "nextFreq(" n ")" => P.frequency (n + 3)
local notation "cutoffDepth(" n ")" => P.stepDepth (n + 1)

/-- The velocity and residual before the cutoff with a single old-parent loss.
The exponent is uniform in spatial order because the fixed-order constants
through the depth have already been bounded by the threshold. -/
def PolynomialApproximationTimeBounds (q B n : ℕ) : Prop :=
  ∀ i ≤ q, ∀ t ∈ Icc 0 (slabEnd(n)),
    (∀ m ≤ cutoffDepth(n), spatialHolderHalfNorm m (slabTimeJet 0 (slabEnd(n)) i (c.selectedStep n).selected.approximation.velocity t) ≤
      parentFreq(n) ^ B * (childFreq(n)) ^ (2 * ((m : ℝ) + 1) + 2 * q)) ∧
    spatialHolderHalfNorm 1 (slabTimeJet 0 (slabEnd(n)) i (c.selectedStep n).selected.approximation.residual t) ≤
      parentFreq(n) ^ B * (childFreq(n)) ^ (2 * ((q : ℝ) + 2)) * (nextFreq(n)) ^ (-4 : ℝ)

/-- Each fixed order of the mean graph carries no positive new-frequency loss. -/
def PolynomialMeanTimeBound (q m B n : ℕ) : Prop :=
  ∀ t ∈ Icc 0 (slabEnd(n)), let v := slabTimeJet 0 (slabEnd(n)) q (c.selectedStep n).selected.approximation.meanCorrection t
    SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ parentFreq(n) ^ B * (childFreq(n)) ^ (-(5 / 2) : ℝ)

/-- Absorb the old-parent powers simultaneously in the new frequency.
For the mean row both orders are fixed while the stage index tends to infinity. -/
theorem terminalGraphStep_of_parentPowers
    (approx : ∀ q A, ∃ B : ℕ, ∀ᶠ n in atTop, c.construction.stages.StageTimeBounds q A (n + 1) →
      c.PolynomialApproximationTimeBounds (q + 1) B n)
    (mean : ∀ q m A, ∃ B : ℕ, ∀ᶠ n in atTop, c.construction.stages.StageTimeBounds q A (n + 1) →
      c.PolynomialMeanTimeBound (q + 1) m B n) :
    c.TerminalGraphStep := by
  have hf (n : ℕ) : 1 ≤ childFreq(n) :=
    P.terminal_frequency_zero_gt_one.le.trans (P.terminal_frequency_mono (Nat.zero_le _))
  have hn (n : ℕ) : 0 ≤ (nextFreq(n)) ^ (-4 : ℝ) := by
    exact Real.rpow_nonneg (zero_le_one.trans (hf (n + 1))) _
  constructor
  · intro q A
    obtain ⟨B, hBounds⟩ := approx q A
    refine ⟨2 * (q + 1) + 5, ?_⟩
    have hRate := (tendsto_add_atTop_nat 1).eventually
      (P.eventually_parentPolynomial_le_child_rpow 1 (B : ℝ) 1 zero_lt_one)
    filter_upwards [hBounds, hRate] with n hN hRate
    intro hOld i hi t ht
    have hμ : parentFreq(n) ^ B ≤ childFreq(n) ^ (1 : ℝ) := by
      simpa only [one_mul, Real.rpow_natCast] using hRate
    have hf0 := zero_lt_one.trans_le (hf n)
    obtain ⟨hv, hr⟩ := hN hOld i hi t ht
    refine ⟨?_, ?_⟩
    · intro m hm
      refine (hv m hm).trans ((mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg hf0.le _)).trans ?_)
      rw [← Real.rpow_add hf0]
      refine Real.rpow_le_rpow_of_exponent_le (hf n) ?_
      push_cast
      linarith
    · refine hr.trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hμ
        (Real.rpow_nonneg hf0.le _)).trans_eq ?_) (hn n))
      rw [← Real.rpow_add hf0]
      congr 1
      push_cast
      ring
  · intro q m A
    obtain ⟨B, hBounds⟩ := mean q m A
    have hRate := (tendsto_add_atTop_nat 1).eventually
      (P.eventually_parentPolynomial_le_child_rpow 2 (B : ℝ) (3 / 2 : ℝ) (by norm_num))
    filter_upwards [hBounds, hRate] with n hN hRate
    intro hOld t ht
    have hf0 := zero_lt_one.trans_le (hf n)
    have hμ : parentFreq(n) ^ B ≤ (1 / 2 : ℝ) * childFreq(n) ^ (3 / 2 : ℝ) := by
      have hr : 2 * parentFreq(n) ^ B ≤ childFreq(n) ^ (3 / 2 : ℝ) := by
        simpa only [Real.rpow_natCast] using hRate
      linarith only [hr]
    obtain ⟨hs, hb⟩ := hN hOld t ht
    refine ⟨hs, hb.trans ((mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg hf0.le _)).trans_eq ?_)⟩
    rw [mul_assoc, ← Real.rpow_add hf0]
    have hsum : (3 / 2 : ℝ) + -(5 / 2) = -1 := by norm_num
    rw [hsum, Real.rpow_neg_one]

end TorusEuler.ScheduledEulerConstruction
