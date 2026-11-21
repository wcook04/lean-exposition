import TorusEuler.TerminalGraphSchedule
import TorusEuler.TerminalScheduledGraphFromProfiles
import TorusEuler.TerminalScheduledParentJets

/-! All time-order estimates and the terminal extension on one physical schedule. -/

open Filter Set
open scoped Topology

namespace TorusEuler

open InductiveEulerParameters ScheduledEulerConstruction

set_option maxHeartbeats 2500000 in
/-- The frozen auxiliary theorem and its two quantitative lemmas. -/
theorem auxiliaryTerminalSmoothness : AuxiliaryTerminalSmoothness := by
  let strength : ℝ := 18 * Real.exp 3
  have hStrength : 2 ≤ strength := by
    dsimp [strength]
    linarith [Real.add_one_le_exp (3 : ℝ)]
  obtain ⟨a₀, Nprofile, ha₀, hNprofile, hProfiles⟩ := exists_scheduledProfileBounds strength hStrength
  obtain ⟨_, Nswitch, _, _, hSwitch⟩ :=
    InductiveEulerTip.SelectedLaterInput.exists_switchTimeJetBudget strength hStrength
  obtain ⟨L, hL, hCoframe⟩ := exists_scheduledGraphCoframeBounds
  choose B Kparent _hB hKparent hParent using exists_scheduledParentMixedJetBounds
  choose e K _hK _hMono hProfile using
    fun (a q A : ℕ) => hProfiles (max a₀ a) q A (le_max_left a₀ a)
  let readoutOrder (q d : ℕ) := d + (q + 1) + 1
  let hierarchyOrder (q d : ℕ) := readoutOrder q d + 3 * d
  let cost (a : ℕ) (_ : Unit) (q A _m d : ℕ) :=
    terminalProfileGraphReadoutCost (q + 1) d (K a q A (hierarchyOrder q d))
      (L (readoutOrder q d)) (Kparent q A)
  let N₀ := max Nprofile Nswitch
  apply auxiliaryTerminalSmoothness_of_graphStep cost (fun _ _ => 0) N₀ a₀
  intro P c hBase ha hC hBudget
  have hBaseProfile : Nprofile ≤ P.frequency 0 := (le_max_left _ _).trans hBase
  have hBaseSwitch : Nswitch ≤ P.frequency 0 := (le_max_right _ _).trans hBase
  have hExp : Real.exp 1 ≤ P.frequency 0 := hNprofile.trans hBaseProfile
  have ha7 : 7 ≤ c.radiusExponent := (by decide : 7 ≤ 16).trans (ha₀.trans ha)
  have haEq : c.radiusExponent = max a₀ c.radiusExponent := (max_eq_right ha).symm
  let a := c.radiusExponent
  let power (q A : ℕ) := terminalGraphReadoutPower (q + 1) (B q A) (54 * e a q A)
  have hReadout (q A : ℕ) : ∀ᶠ n : ℕ in atTop,
      c.construction.stages.StageTimeBounds q A (n + 1) →
      c.PolynomialApproximationTimeBounds (q + 1) (power q A) n ∧
        ∀ m ≤ P.stepDepth (n + 1), c.PolynomialMeanTimeBound (q + 1) m
          (power q A + 9 * (a + 1) * (m + 1 + (q + 1))) n := by
    let loss := e a q A
    have hCost := (tendsto_add_atTop_nat 1).eventually (hBudget.eventually_le_at_depth q A 0)
    have hSmall := (tendsto_add_atTop_nat 1).eventually
      (P.eventually_parentPolynomial_mul_child_rpow_le_one 1 (↑(54 * loss : ℕ)) (1/12) (by norm_num))
    have hWave := (tendsto_add_atTop_nat 1).eventually
      (P.eventually_parentPolynomial_le_child_rpow 1 (↑(9 * (max a 1 + 1) : ℕ)) (1/2) (by norm_num))
    filter_upwards [hCost, hSmall, hWave] with n hCost hSmall hWave
    intro hOld
    let d := (c.selectedStep n).selected
    let depth := P.stepDepth (n + 1)
    let H := hierarchyOrder q depth
    let mRead := readoutOrder q depth
    let μ := P.frequency (n + 1)
    let freq := P.frequency (n + 2)
    let D := μ ^ (9 : ℕ)
    have hDecay : -1 / 12 = -(1 / 12 : ℝ) := by ring
    have hExpLoss : (D ^ loss) ^ (6 : ℕ) = μ ^ (54 * loss) := by
      dsimp only [D]
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    have hRecurrence : (D ^ loss) ^ (6 : ℕ) * freq ^ (-1/12 : ℝ) ≤ 1 := by
      simpa only [hExpLoss, hDecay, one_mul, Real.rpow_natCast] using hSmall
    have hRate : D ^ (max a 1 + 1) ≤ freq ^ (1/2 : ℝ) := by
      rw [show D ^ (max a 1 + 1) = μ ^ (9 * (max a 1 + 1)) from (pow_mul _ _ _).symm]
      simpa only [one_mul, Real.rpow_natCast] using hWave
    have hCostHere : terminalProfileGraphReadoutCost (q + 1) depth (K a q A H)
        (L mRead) (Kparent q A) ≤ μ :=
      (le_abs_self _).trans (hCost () 0 (Nat.zero_le _))
    have hMeasured := hProfile a q A c n H haEq hBaseProfile hC hOld hRecurrence
    have hParentVelocity := (hParent q A c n d.parent_frequency_ge_two hOld).1
    have hEnvelope := (hSwitch d hBaseSwitch hC).2.1
    have hReserve : depth + (q+1) + 1 + 3 * depth ≤ H := le_rfl
    have hActiveReserve : depth + (q+1) + 2 ≤ H := by
      have hd : 2 ≤ depth := d.depth_ge_two
      dsimp only [H, hierarchyOrder, readoutOrder]
      omega
    exact c.polynomialTimeBounds_of_scheduledMixedProfileBounds n hExp (hL mRead) (hKparent q A)
      hRate hCostHere (hCoframe c ha7 n mRead) hParentVelocity hEnvelope hReserve hActiveReserve hMeasured
  apply c.terminalGraphStep_of_parentPowers
  · intro q A
    exact ⟨power q A, (hReadout q A).mono fun _ h hOld => (h hOld).1⟩
  · intro q m A
    refine ⟨power q A + 9 * (a + 1) * (m + 1 + (q + 1)), ?_⟩
    filter_upwards [hReadout q A,
      (P.terminal_frequencyExponent_tendsto_atTop.comp (tendsto_add_atTop_nat 2)).eventually_ge_atTop m]
      with n h hDepth
    intro hOld
    have hm : m ≤ P.stepDepth (n + 1) := by
      change m ≤ frequencyExponent P.exponentParameter (P.order (n + 3)) at hDepth
      exact hDepth.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 6))
    exact (h hOld).2 m hm

end TorusEuler
