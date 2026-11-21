import TorusEuler.TerminalStageFromGraph

/-! Fixed-order graph constants and differentiated cutoff constants on one schedule. -/

open Filter
open scoped BigOperators

namespace TorusEuler

/-- A cost may depend on the exponent in the parent velocity estimate.
For each time order the threshold includes all such exponents through that order. -/
noncomputable def terminalGraphCostEnvelope {κ : Type*}
    (cost : κ → ℕ → ℕ → ℕ → ℕ → ℝ) (row : κ) (s m d : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (s + 1), ∑ A ∈ Finset.range (s + 1), |cost row q A m d|

theorem abs_terminalGraphCost_le_envelope {κ : Type*}
    (cost : κ → ℕ → ℕ → ℕ → ℕ → ℝ) (row : κ) (q A m d : ℕ) :
    |cost row q A m d| ≤ terminalGraphCostEnvelope cost row (max q A) m d := by
  unfold terminalGraphCostEnvelope
  let s := Finset.range (max q A + 1)
  have hq : q ∈ s := Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left _ _))
  have hA : A ∈ s := Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))
  calc
    _ ≤ ∑ u ∈ s, |cost row q u m d| :=
      Finset.single_le_sum (f := fun u => |cost row q u m d|) (fun _ _ => abs_nonneg _) hA
    _ ≤ ∑ v ∈ s, ∑ u ∈ s, |cost row v u m d| :=
      Finset.single_le_sum (f := fun v => ∑ u ∈ s, |cost row v u m d|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hq

/-- The fixed-order graph costs are recovered from the common threshold,
including any fixed exponent in the prior velocity bound. -/
def TerminalGraphCostBounds {κ : Type*} (P : InductiveEulerParameters)
    (cost : κ → ℕ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ) : Prop :=
  ∀ i row q A m d, let S := 7 * frequencyExponent P.exponentParameter (P.order (i + 2))
    q ≤ S → A ≤ S → m ≤ S + reserve (max q A) d → d ≤ S → |cost row q A m d| ≤ P.frequency i

/-- The cutoff depth and the graph orders eventually fit the threshold
at any fixed time order and fixed exponent in the parent velocity bound. -/
theorem TerminalGraphCostBounds.eventually_le_at_depth {κ : Type*}
    {P : InductiveEulerParameters} {cost : κ → ℕ → ℕ → ℕ → ℕ → ℝ} {reserve : ℕ → ℕ → ℕ}
    (hCost : TerminalGraphCostBounds P cost reserve) (q A m₀ : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ j n, n ≤ max m₀ (P.stepDepth i + q + 2) →
      |cost j q A n (P.stepDepth i)| ≤ P.frequency i := by
  filter_upwards [P.eventually_terminalDerivativeReserve m₀ (max q A)] with i hi
  intro j n hn
  let S := 7 * frequencyExponent P.exponentParameter (P.order (i + 2))
  have hDeep : P.stepDepth i + max q A + 2 ≤ S := hi.2.2
  have hd : P.stepDepth i ≤ S := by omega
  have hMax : max m₀ (P.stepDepth i + q + 2) ≤ S := by
    apply max_le hi.1
    exact (Nat.add_le_add_right (Nat.add_le_add_left (le_max_left q A) _) _).trans hDeep
  exact hCost i j q A n (P.stepDepth i) ((le_max_left _ _).trans hi.2.1)
    ((le_max_right _ _).trans hi.2.1) (hn.trans (hMax.trans (Nat.le_add_right _ _))) hd

/-- The mixed graph estimates and the fixed cutoff costs can be imposed
by one nondecreasing schedule chosen before the initial frequency. -/
theorem auxiliaryTerminalSmoothness_of_graphStep
    {κ : Type*} [Fintype κ] (cost : ℕ → κ → ℕ → ℕ → ℕ → ℕ → ℝ) (reserve : ℕ → ℕ → ℕ)
    (Naux : ℝ) (radiusFloor : ℕ)
    (graph : ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P),
      Naux ≤ P.frequency 0 → radiusFloor ≤ c.radiusExponent → P.strengthConstant = 18 * Real.exp 3 →
      TerminalGraphCostBounds P (cost c.radiusExponent) reserve → c.TerminalGraphStep) :
    AuxiliaryTerminalSmoothness := by
  obtain ⟨cutoffCost, hCutoff⟩ := ScheduledEulerConstruction.exists_terminalCutoffCosts
  let fullCost (a : ℕ) : κ ⊕ Bool → ℕ → ℕ → ℕ → ℝ :=
    Sum.elim (terminalGraphCostEnvelope (cost a)) cutoffCost
  apply auxiliaryTerminalSmoothness_of_localTimeStep fullCost reserve Naux radiusFloor
  intro P c hN ha hC hCost
  apply hCutoff c reserve
  · intro i row q m d S hq hm hd
    exact hCost i (.inr row) q m d hq hm hd
  · apply graph c hN ha hC
    intro i row q A m d S hq hA hm hd
    exact (abs_terminalGraphCost_le_envelope (cost c.radiusExponent) row q A m d).trans
      ((le_abs_self _).trans (hCost i (.inl row) (max q A) m d (max_le hq hA) hm hd))

end TorusEuler
