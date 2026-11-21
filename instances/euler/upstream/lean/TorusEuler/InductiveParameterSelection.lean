import TorusEuler.InductiveStageConstruction
import TorusEuler.ThresholdSelection

/-! A single frequency and order schedule for the physical stage construction. -/

namespace TorusEuler

namespace InductiveEulerParameters

/-- The threshold for the construction can include all fixed-order costs and
any finite list of absolute initial-frequency constraints. -/
theorem exists_of_fixedOrderCosts {ι : Type*} [Fintype ι]
    (b C₀ : ℕ) (C N₀ : ℝ) (cost : ι → ℕ → ℕ → ℝ)
    (hb : 1 ≤ b) (hC₀ : 240 ≤ C₀) (hC : 2 ≤ C) :
    ∃ N₁ : ℝ, ∀ N ≥ N₁, ∃ P : InductiveEulerParameters,
      P.exponentParameter = b ∧ P.comparisonConstant = C₀ ∧ P.strengthConstant = C ∧
      P.threshold = fixedOrderThreshold b cost ∧ P.frequency 0 = N ∧ N₀ ≤ P.frequency 0 ∧
      P.LifetimeBounds ∧ ∀ i j m p, m ≤ 7 * frequencyExponent b (P.order (i + 2)) →
        p ≤ 7 * frequencyExponent b (P.order (i + 2)) → |cost j m p| ≤ P.frequency i := by
  obtain ⟨NT, hNT⟩ := exists_lifetime_threshold
  refine ⟨max (fixedOrderThreshold b cost 1) (max NT N₀), ?_⟩
  intro N hN
  have hB : fixedOrderThreshold b cost 1 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨q, f, hq, hf, hstep, horder, _, _, _, _, hcost⟩ :=
    exists_frequencySchedule_with_fixedOrderCosts b cost N hb hB
  let P : InductiveEulerParameters :=
    { exponentParameter := b
      threshold := fixedOrderThreshold b cost
      order := q
      frequency := f
      exponentParameter_ge := hb
      initial_order := hq
      initial_threshold := hf.symm ▸ hB
      frequency_step := hstep
      order_maximum := horder
      threshold_pos := fun s _ => fixedOrderThreshold_pos b cost s
      threshold_floor := fun s _ => fixedOrderThreshold_log_floor b cost s
      strengthConstant := C
      strengthConstant_ge := hC
      comparisonConstant := C₀
      comparisonConstant_ge := hC₀ }
  refine ⟨P, rfl, rfl, rfl, rfl, hf, ?_, hNT P ?_, hcost⟩
  · exact (le_max_right NT N₀).trans ((le_max_right _ _).trans (hN.trans hf.ge))
  · exact (le_max_left NT N₀).trans ((le_max_right _ _).trans (hN.trans hf.ge))

end InductiveEulerParameters

end TorusEuler
