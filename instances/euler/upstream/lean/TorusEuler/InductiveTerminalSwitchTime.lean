import TorusEuler.InductiveLaterStageAssembly
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.TerminalSwitchTime

/-! High-order switch estimates on the exact selected later stage. -/

open Set

namespace TorusEuler.InductiveEulerTip.SelectedLaterInput

/-- Both selected activation sources vanish outside the time switch, at
every label and phase on the physical slab. -/
theorem activationSwitch_eq_zero_outside
    {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
    {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a)
    {t : ℝ} (ht : t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation))
    (hOutside : t ∉ Icc tip.nextActivation (tip.nextActivation + 1 / d.window.physical.rate))
    (x : Vec3) (s : ℝ) :
    (d.approximation.leading.leadingSwitch + d.approximation.leading.completionSwitch).val.val.val
      (t, x, s) = 0 := by
  have hDeriv : deriv (waveSwitch tip.nextActivation d.window.physical.rate) t = 0 := by
    rw [← iteratedDeriv_one]
    exact iteratedDeriv_waveSwitch_zero_of_not_mem Nat.one_pos d.window.physical.rate_pos hOutside
  have h := d.approximation.activationSwitch_slice_eq d.seed d.regularity d.parent.deformationOn.flow
    d.parent.smooth_velocity (fun u _ => tip.parent.periodic_velocity u)
    (fun u hu => tip.parent.odd_velocity u (d.parent.subset hu)) d.seed_even rfl ht x s
  rw [hDeriv, zero_smul] at h
  exact h

/-- On the same prescribed later wave, the rate is bounded by the old
frequency and every positive-order switch derivative retains the early
growth gain `next^(-4)`. The threshold is independent of the derivative
order and the constants depend only on that order. -/
theorem exists_switchTimeJetBudget (Cstrength : ℝ) (hCstrength : 2 ≤ Cstrength) :
    ∃ (C : ℕ → ℝ) (N : ℝ), (∀ q, 0 ≤ C q) ∧ 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a),
        N ≤ P.frequency 0 → P.strengthConstant = Cstrength →
        let t₀ := tip.nextActivation
        let r := d.window.physical.rate
        let μ := P.frequency (n + 1)
        let next := P.frequency (n + 3)
        r ≤ μ ∧
          (∀ t ∈ Icc t₀ (t₀ + 1 / r), d.centerWeight t ≤ Real.exp 3 * next ^ (-4 : ℝ)) ∧
          (∀ q t, |iteratedDeriv q (waveSwitch t₀ r) t| ≤ C q * μ ^ q) ∧
          (∀ {q}, 0 < q → ∀ t,
            |iteratedDeriv q (waveSwitch t₀ r) t| * d.centerWeight t ≤
              (C q * Real.exp 3) * μ ^ q * next ^ (-4 : ℝ)) := by
  obtain ⟨C, hC, hSwitch⟩ := exists_waveSwitch_iteratedDeriv_bound
  obtain ⟨N, hN, hData⟩ := exists_inductiveEulerTip_switch_time_data Cstrength 1 hCstrength zero_le_one
  refine ⟨C, N, hC, hN, ?_⟩
  intro P n tip Cenv a d hBase hStrength t₀ r μ next
  obtain ⟨hNext, hRate, hEarly⟩ := hData tip hBase hStrength d.window d.selection
  have hr : 0 < r := d.window.physical.rate_pos
  have hExp : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hμ : r ≤ μ := (le_mul_of_one_le_right hr.le hExp).trans (by
    simpa only [one_mul] using hRate)
  have hInv : (next ^ (4 : ℕ))⁻¹ = next ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hNext.le, Real.rpow_ofNat]
  have hGamma (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + 1 / r)) :
      d.centerWeight t ≤ Real.exp 3 * next ^ (-4 : ℝ) := by
    have h : |d.centerWeight t| ≤ Real.exp (3 - 4 * Real.log next) := hEarly t ht
    rw [frequencySchedule_switchGain hNext, hInv] at h
    exact (le_abs_self _).trans h
  have hDerivative (q : ℕ) (t : ℝ) :
      |iteratedDeriv q (waveSwitch t₀ r) t| ≤ C q * μ ^ q :=
    (hSwitch q t₀ r t hr).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hμ q) (hC q))
  refine ⟨hμ, hGamma, hDerivative, fun {q} hq t => ?_⟩
  have hμ₀ : 0 ≤ μ := hr.le.trans hμ
  have hGammaBound : 0 ≤ Real.exp 3 * next ^ (-4 : ℝ) :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hNext.le _)
  have hGammaNonneg : 0 ≤ d.centerWeight t :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans d.child_frequency_ge_one) _) (norm_nonneg _)
  by_cases ht : t ∈ Icc t₀ (t₀ + 1 / r)
  · calc
      _ ≤ (C q * μ ^ q) * (Real.exp 3 * next ^ (-4 : ℝ)) :=
        mul_le_mul (hDerivative q t) (hGamma t ht) hGammaNonneg (mul_nonneg (hC q) (pow_nonneg hμ₀ _))
      _ = _ := by ring
  · rw [iteratedDeriv_waveSwitch_zero_of_not_mem hq hr ht, abs_zero, zero_mul]
    calc
      0 ≤ (C q * μ ^ q) * (Real.exp 3 * next ^ (-4 : ℝ)) :=
        mul_nonneg (mul_nonneg (hC q) (pow_nonneg hμ₀ _)) hGammaBound
      _ = _ := by ring

end TorusEuler.InductiveEulerTip.SelectedLaterInput
