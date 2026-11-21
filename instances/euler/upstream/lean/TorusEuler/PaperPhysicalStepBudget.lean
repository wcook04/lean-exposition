import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.InductiveStageProfileFlowBounds

/-! One choice of constants for the physical estimates in Lemmas 5.8–5.10. -/

namespace TorusEuler

open HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

/-- The common step exponent is independent of the expansion depth and
the derivative-order constants. -/
def paperPhysicalStepExponent (a r aMean : ℕ) : ℕ :=
  6 * r + 5 * a + 2 * aMean + 160

/-- The scalar inputs to the residual, pressure, center, and flow estimates.
The coframe cost for the pressure estimates is `K * D ^ 24`. -/
structure PaperPhysicalStepBudget (a r aMean depth : ℕ) (C : ℕ → ℝ)
    (L K Clevel Ctail Cprimary Clead Cparent D Γ : ℝ) : Prop where
  gamma_ge_one : 1 ≤ Γ
  hierarchyPower : 6 * r ≤ paperPhysicalStepExponent a r aMean
  graphPower : max a 1 + 1 ≤ paperPhysicalStepExponent a r aMean
  flowPower : max a 1 + (max a 1 + profileFlowJetPower r) + 1 ≤ paperPhysicalStepExponent a r aMean
  flowConstant : 1 + 40 * profileFlowJetConstant C depth Clevel ≤ Γ
  oscillationSup : 2 * ((Finset.Icc 1 depth).card : ℝ) * Clevel * (D ^ r) ^ 2 ≤
    Γ * D ^ paperPhysicalStepExponent a r aMean
  residualTail : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
    ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤
    Γ * D ^ paperPhysicalStepExponent a r aMean
  residualPrimary : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
    Cprimary * D ^ ((max a 1 + 1) * 2 + (a + 27))) ≤
    Γ * D ^ paperPhysicalStepExponent a r aMean
  center : let count := ((Finset.Icc 1 depth).card : ℝ)
    48 * L * (2 * count * Clevel) * D ^ (max a 1 + 1 + 2 * r) +
      24 * L * (count * Clevel) * D ^ (a + 1 + 6 * r) ≤ Γ * D ^ paperPhysicalStepExponent a r aMean
  pressure :
    Clead * D ^ (2 * a + 74) +
      higherOscillatoryHessianPrefactor depth Clevel (D ^ r) (K * D ^ (24 : ℕ)) (D ^ a) D +
      (48 * ‖pressureHessianMultiplier‖ * (13824 * (((Finset.Icc 2 depth).card : ℝ) * Clevel)) *
        (1 + Cparent)) * D ^ (6 * r + 2 * aMean + 2) ≤ Γ * D ^ paperPhysicalStepExponent a r aMean

/-- The fixed-order constants and depth determine one step coefficient,
which works for every parent scale and frequency. -/
theorem exists_paperPhysicalStepBudget
    (a r aMean depth : ℕ) (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    {L K Clevel Ctail Cprimary Clead Cparent : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hLevel : 0 ≤ Clevel)
    (hTail : 0 ≤ Ctail) (hPrimary : 0 ≤ Cprimary) (hLead : 0 ≤ Clead) (hParent : 0 ≤ Cparent) :
    ∃ Γ : ℝ, ∀ D : ℝ, 1 ≤ D → PaperPhysicalStepBudget a r aMean depth C
      L K Clevel Ctail Cprimary Clead Cparent D Γ := by
  let b := paperPhysicalStepExponent a r aMean
  let count := ((Finset.Icc 1 depth).card : ℝ)
  let count₂ := ((Finset.Icc 2 depth).card : ℝ)
  let F := 1 + 40 * profileFlowJetConstant C depth Clevel
  let A := 2 * count * Clevel
  let Ct := 6 * (((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) * ((4 : ℝ) ^ (2 : ℕ) * Ctail)
  let Cp := 6 * (((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) * Cprimary
  let Cc := 48 * L * A + 24 * L * (count * Clevel)
  let Ch := 12 * count₂ * Clevel * K ^ 2 * (8 + 32 * (K + 1))
  let Cm := 48 * ‖pressureHessianMultiplier‖ * (13824 * (count₂ * Clevel)) * (1 + Cparent)
  let P := Clead + Ch + Cm
  let Γ := F + A + Ct + Cp + Cc + P
  have hF : 1 ≤ F := le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (zero_le_one.trans (one_le_profileFlowJetConstant C hC depth hLevel)))
  have hCount : 0 ≤ count := Nat.cast_nonneg _
  have hCount₂ : 0 ≤ count₂ := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hCm : 0 ≤ Cm := by dsimp only [Cm]; positivity
  have hP : 0 ≤ P := add_nonneg (add_nonneg hLead hCh) hCm
  have hFΓ : F ≤ Γ := by dsimp only [Γ]; linarith
  have hAΓ : A ≤ Γ := by dsimp only [Γ]; linarith
  have hCtΓ : Ct ≤ Γ := by dsimp only [Γ]; linarith
  have hCpΓ : Cp ≤ Γ := by dsimp only [Γ]; linarith
  have hCcΓ : Cc ≤ Γ := by dsimp only [Γ]; linarith
  have hPΓ : P ≤ Γ := by dsimp only [Γ]; linarith
  refine ⟨Γ, fun D hD => ?_⟩
  have hD₀ := zero_le_one.trans hD
  have widen {c : ℝ} (hc : 0 ≤ c) {e : ℕ} (he : e ≤ b) :
      c * D ^ e ≤ c * D ^ b :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD he) hc
  have toStep {c : ℝ} (hc : 0 ≤ c) (hcΓ : c ≤ Γ) {e : ℕ} (he : e ≤ b) :
      c * D ^ e ≤ Γ * D ^ b :=
    (widen hc he).trans (mul_le_mul_of_nonneg_right hcΓ (pow_nonneg hD₀ b))
  have ha : max a 1 ≤ a + 1 := max_le (Nat.le_succ _) (Nat.succ_le_succ (Nat.zero_le _))
  have ha₂₄ : max 24 a ≤ a + 24 := max_le (by omega) (by omega)
  refine ⟨hF.trans hFΓ, by unfold paperPhysicalStepExponent; omega,
    by unfold paperPhysicalStepExponent; omega,
    by unfold profileFlowJetPower paperPhysicalStepExponent; omega, hFΓ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul]
    exact toStep hA hAΓ (by dsimp only [b, paperPhysicalStepExponent]; omega)
  · calc
      _ = Ct * D ^ ((max a 1 + 1) * 2) := by dsimp only [Ct]; ring
      _ ≤ _ := toStep hCt hCtΓ (by dsimp only [b, paperPhysicalStepExponent]; omega)
  · calc
      _ = Cp * D ^ ((max a 1 + 1) * 2 + (a + 27)) := by dsimp only [Cp]; ring
      _ ≤ _ := toStep hCp hCpΓ (by dsimp only [b, paperPhysicalStepExponent]; omega)
  · change 48 * L * A * D ^ (max a 1 + 1 + 2 * r) +
      24 * L * (count * Clevel) * D ^ (a + 1 + 6 * r) ≤ Γ * D ^ b
    refine (add_le_add (widen (by positivity) ?_) (widen (by positivity) ?_)).trans ?_
    · dsimp only [b, paperPhysicalStepExponent]; omega
    · dsimp only [b, paperPhysicalStepExponent]; omega
    · rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hCcΓ (pow_nonneg hD₀ b)
  · have hHigher := higherPressure_prefactor_le_parentPower (P := depth) (a := a) (b := r) (c := 1)
      (D := D) (L := 1) hD (mul_nonneg hK (pow_nonneg hD₀ _)) hD₀
      (pow_nonneg hD₀ a) (pow_nonneg hD₀ r) hLevel le_rfl (by rw [pow_one]) le_rfl
      (by rw [one_mul]) le_rfl
    have hHigher' :
        higherOscillatoryHessianPrefactor depth Clevel (D ^ r) (K * D ^ (24 : ℕ)) (D ^ a) D ≤
          Ch * D ^ (max a 1 + 48 + (max 24 a + r)) := by
      simpa only [higherOscillatoryHessianPrefactor, Ch, count₂, mul_one] using hHigher
    have hPress :
        Clead * D ^ (2 * a + 74) +
          higherOscillatoryHessianPrefactor depth Clevel (D ^ r) (K * D ^ (24 : ℕ)) (D ^ a) D +
          Cm * D ^ (6 * r + 2 * aMean + 2) ≤ P * D ^ b := by
      rw [show P = Clead + Ch + Cm from rfl, add_mul, add_mul]
      exact add_le_add (add_le_add
        (widen hLead (by dsimp only [b, paperPhysicalStepExponent]; omega))
        (hHigher'.trans (widen hCh (by dsimp only [b, paperPhysicalStepExponent]; omega))))
        (widen hCm (by dsimp only [b, paperPhysicalStepExponent]; omega))
    exact hPress.trans (mul_le_mul_of_nonneg_right hPΓ (pow_nonneg hD₀ b))

/-- The small-step assumption also supplies the smallness condition for
the hierarchy recurrence with parent loss `D ^ r`. -/
theorem PaperPhysicalStepBudget.hierarchySmall
    {a r aMean depth : ℕ} {C : ℕ → ℝ}
    {L K Clevel Ctail Cprimary Clead Cparent D Γ freq : ℝ}
    (h : PaperPhysicalStepBudget a r aMean depth C L K Clevel Ctail Cprimary Clead Cparent D Γ)
    (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hs : Γ * D ^ paperPhysicalStepExponent a r aMean * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    (D ^ r) ^ (6 : ℕ) * freq ^ (-1 / 12 : ℝ) ≤ 1 := by
  rw [← pow_mul, Nat.mul_comm r]
  have hpow := pow_le_pow_right₀ hD h.hierarchyPower
  have hΓ : D ^ paperPhysicalStepExponent a r aMean ≤ Γ * D ^ paperPhysicalStepExponent a r aMean :=
    le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hD) _) h.gamma_ge_one
  exact (mul_le_mul_of_nonneg_right (hpow.trans hΓ) (Real.rpow_nonneg (zero_le_one.trans hf) _)).trans hs

end

end TorusEuler
