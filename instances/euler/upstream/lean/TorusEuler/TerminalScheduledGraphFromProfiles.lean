import TorusEuler.TerminalScheduledGraphReadout
import TorusEuler.TerminalScheduledProfileBounds

/-! The measured hierarchy supplies its actual scheduled physical graph. -/

open Set

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile

noncomputable section

set_option quotPrecheck false

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (n : ℕ)

local notation "Tip" => c.construction.tip n
local notation "Input" => (c.selectedStep n).selected
local notation "Schild" => c.construction.slab (n+2)
local notation "μ" => P.frequency (n+1)
local notation "freq" => P.frequency (n+2)
local notation "next" => P.frequency (n+3)
local notation "depth" => P.stepDepth (n+1)
local notation "a" => c.radiusExponent
local notation "D" => μ ^ (9 : ℕ)
local notation "ell" => (c.selectedStep n).selected.radius
local notation "t₀" => (c.construction.tip n).nextActivation

/-- The common fixed part of the mean and oscillation profile sums. -/
def terminalGraphProfileSumCost (d : ℕ) (K : ℝ) : ℝ :=
  ((Finset.Icc 1 d).card : ℝ) * hierarchyLevelConstant d K d

/-- The threshold row for the entire measured-to-physical graph estimate.
Here the reserve has already been included in the supplied recurrence
constant K. -/
def terminalProfileGraphReadoutCost (q d : ℕ) (K L : ℝ) (Kparent : ℕ → ℝ) : ℝ :=
  terminalGraphReadoutCost q (d+q+1) L (terminalGraphParentCost Kparent (d+q+1))
    (terminalGraphProfileSumCost d K) (2 * terminalGraphProfileSumCost d K)
    (terminalProfileTailFactor d K) (2 * K ^ 2)

private theorem terminalGraphProfileSumCost_nonneg (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ terminalGraphProfileSumCost d K :=
  mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hierarchyLevelConstant_one_le hK d))

private theorem terminalGraphProfileTailCost_nonneg (d : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ terminalProfileTailFactor d K := by
  unfold terminalProfileTailFactor
  positivity

set_option maxHeartbeats 1700000 in
/-- Extract the four concrete factorial norms from the measured hierarchy.
The sixth power in the mean row supplies the common exponent `54 * e`
when the recurrence loss is `(μ ^ 9) ^ e`. -/
theorem selectedProfileGraphTimeBounds_of_scheduledMixedProfileBounds {q H e : ℕ} {K : ℝ}
    (hReserve : (depth+q+1) + 3*depth ≤ H)
    (hActivationReserve : depth+q+2 ≤ H)
    (bounds : c.ScheduledMixedProfileBounds n q H K (D^e)) :
    c.SelectedProfileGraphTimeBounds n q (54*e)
      (terminalGraphProfileSumCost depth K) (2 * terminalGraphProfileSumCost depth K)
      (terminalProfileTailFactor depth K) (2 * K ^ 2) := by
  let N := depth+q+1
  have hμ : 1 ≤ μ := one_le_two.trans (Input).parent_frequency_ge_two
  have hK : 0 ≤ K := zero_le_one.trans bounds.one_le_cost
  have hM : 0 ≤ terminalGraphProfileSumCost depth K := terminalGraphProfileSumCost_nonneg depth hK
  have hR : 0 ≤ terminalProfileTailFactor depth K := terminalGraphProfileTailCost_nonneg depth hK
  have hFreq : ∀ x : ℝ, 0 ≤ freq ^ x :=
    Real.rpow_nonneg (zero_le_one.trans (Input).child_frequency_ge_one)
  have hLoss6 : (D^e) ^ (6 : ℕ) = μ ^ (54*e) := by
    simp only [← pow_mul]
    congr 1
    ring
  have hLoss2 : (D^e) ^ (2 : ℕ) ≤ μ ^ (54*e) := by
    exact (pow_le_pow_right₀ bounds.one_le_loss (by decide : 2 ≤ (6 : ℕ))).trans_eq hLoss6
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [terminalGraphProfileSumCost, hLoss6] using! bounds.mean N hReserve
  · calc
      _ ≤ (2 * terminalGraphProfileSumCost depth K) * ((D^e)^2) * freq ^ (-5/4 : ℝ) := by
        simpa only [terminalGraphProfileSumCost, mul_assoc] using! bounds.oscillation N hReserve
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLoss2 (mul_nonneg zero_le_two hM)) (hFreq _)
  · refine (bounds.remainder N hReserve).trans ?_
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hR (one_le_pow₀ hμ)) (hFreq _)
  · calc
      _ ≤ (2 * K ^ 2) * ((D^e)^2) * freq ^ (-5/4 : ℝ) := by
        simpa only [mul_pow, mul_assoc] using! bounds.activation N hActivationReserve
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLoss2 (by positivity)) (hFreq _)

set_option maxHeartbeats 1200000 in
/-- The actual scheduled mixed profile data give exactly the old-parent
polynomial graph bounds required by the cutoff step. -/
theorem polynomialTimeBounds_of_scheduledMixedProfileBounds
    {q B e H : ℕ} {K L : ℝ} {Kparent : ℕ → ℝ}
    (hBase : Real.exp 1 ≤ P.frequency 0)
    (hL : 1 ≤ L) (hKparent : ∀ m, 0 ≤ Kparent m)
    (hOldWave : D ^ (max a 1 + 1) ≤ freq ^ (1/2 : ℝ))
    (hCost : terminalProfileGraphReadoutCost q depth K L Kparent ≤ μ)
    (hCoframe : ∀ t ∈ Icc 0 Schild, ∀ m ≤ depth+q+1, ∀ x, ell ^ m *
      ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ ((Tip).parent.flow t 0)
        ((Tip).parent.flow 0 t y)) x‖ ≤ L * D)
    (hParent : TerminalMixedJetBound 0 Schild q 5 μ (μ^B) Kparent (Tip).parent.velocity)
    (hEnvelope : ∀ t ∈ Icc t₀ (t₀ + 1 / (Input).window.physical.rate),
      (Input).centerWeight t ≤ Real.exp 3 * next ^ (-4 : ℝ))
    (hReserve : (depth+q+1) + 3*depth ≤ H) (hActivationReserve : depth+q+2 ≤ H)
    (bounds : c.ScheduledMixedProfileBounds n q H K (D^e)) :
    c.PolynomialApproximationTimeBounds q (terminalGraphReadoutPower q B (54*e)) n ∧
      ∀ m ≤ depth, c.PolynomialMeanTimeBound q m
        (terminalGraphReadoutPower q B (54*e) + 9*(a+1)*(m+1+q)) n := by
  have hK := zero_le_one.trans bounds.one_le_cost
  have hM := terminalGraphProfileSumCost_nonneg depth hK
  have hR := terminalGraphProfileTailCost_nonneg depth hK
  exact c.polynomialTimeBounds_of_selectedProfileGraphTimeBounds n
    hBase hL hKparent hM (mul_nonneg zero_le_two hM) hR (by positivity)
    hOldWave hCost hCoframe hParent hEnvelope
    (c.selectedProfileGraphTimeBounds_of_scheduledMixedProfileBounds n hReserve hActivationReserve bounds)

end

end TorusEuler.ScheduledEulerConstruction
