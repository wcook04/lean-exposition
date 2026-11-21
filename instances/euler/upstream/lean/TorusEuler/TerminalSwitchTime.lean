import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TorusEuler.ActivationProfiles

/-! Time derivatives of the scalar switch in the terminal note. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

/-- The affine physical clock contributes exactly one factor of the rate
per time derivative. -/
theorem iteratedDeriv_waveSwitch (q : ℕ) (t₀ r t : ℝ) :
    iteratedDeriv q (waveSwitch t₀ r) t =
      r ^ q * iteratedDeriv q Real.smoothTransition (r * (t - t₀)) := by
  calc
    _ = iteratedDeriv q (fun u => Real.smoothTransition (r * u)) (t - t₀) :=
      congrFun (iteratedDeriv_comp_sub_const q (fun u => Real.smoothTransition (r * u)) t₀) t
    _ = _ := congrFun (iteratedDeriv_comp_const_mul
      (Real.smoothTransition.contDiff : ContDiff ℝ q Real.smoothTransition) r) (t - t₀)

private theorem iteratedDeriv_smoothTransition_zero_of_not_mem {q : ℕ} (hq : 0 < q) {s : ℝ}
    (hs : s ∉ Icc (0 : ℝ) 1) : iteratedDeriv q Real.smoothTransition s = 0 := by
  by_cases h₀ : s < 0
  · have hEq : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h₀] with _ hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hEq.iteratedDeriv_eq, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hq)]
  · have h₁ : 1 < s := lt_of_not_ge fun h => hs ⟨le_of_not_gt h₀, h⟩
    have hEq : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h₁] with _ hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [hEq.iteratedDeriv_eq, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hq)]

/-- Positive-order time derivatives have support in the physical switch interval. -/
theorem iteratedDeriv_waveSwitch_zero_of_not_mem {q : ℕ} (hq : 0 < q)
    {t₀ r t : ℝ} (hr : 0 < r) (ht : t ∉ Icc t₀ (t₀ + 1 / r)) :
    iteratedDeriv q (waveSwitch t₀ r) t = 0 := by
  have h : r * (t - t₀) ∉ Icc (0 : ℝ) 1 := by
    rintro ⟨hleft, hright⟩
    have h₀ := nonneg_of_mul_nonneg_right hleft hr
    have h₁ := (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hright)
    exact ht ⟨by linarith, by linarith⟩
  rw [iteratedDeriv_waveSwitch, iteratedDeriv_smoothTransition_zero_of_not_mem hq h, mul_zero]

/-- The switch derivatives are flat at both ends of the switching interval. -/
theorem iteratedDeriv_waveSwitch_zero_of_not_mem_open {q : ℕ} (hq : 0 < q)
    {t₀ r t : ℝ} (hr : 0 < r) (ht : t ∉ Ioo t₀ (t₀ + 1 / r)) :
    iteratedDeriv q (waveSwitch t₀ r) t = 0 := by
  let f := iteratedDeriv q (waveSwitch t₀ r)
  have hf : Continuous f := (contDiff_waveSwitch t₀ r).continuous_iteratedDeriv q (by simp)
  by_cases hLeft : t ≤ t₀
  · have hEq : EqOn f (fun _ => 0) (Iio t₀) := fun u hu =>
      iteratedDeriv_waveSwitch_zero_of_not_mem hq hr (fun hu' => (not_lt_of_ge hu'.1) hu)
    have hClosed := hEq.closure hf continuous_const
    rw [closure_Iio] at hClosed
    exact hClosed hLeft
  · have hRight : t₀ + 1 / r ≤ t := le_of_not_gt fun h => ht ⟨lt_of_not_ge hLeft, h⟩
    have hEq : EqOn f (fun _ => 0) (Ioi (t₀ + 1 / r)) := fun u hu =>
      iteratedDeriv_waveSwitch_zero_of_not_mem hq hr (fun hu' => (not_lt_of_ge hu'.2) hu)
    have hClosed := hEq.closure hf continuous_const
    rw [closure_Ioi] at hClosed
    exact hClosed hRight

/-- A single fixed coefficient at each order bounds all time derivatives
of the same switch. The bounds depend on the physical rate by (r^q). -/
theorem exists_waveSwitch_iteratedDeriv_bound :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ q t₀ r t, 0 < r → |iteratedDeriv q (waveSwitch t₀ r) t| ≤ C q * r ^ q := by
  have hBounds (q : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |iteratedDeriv q Real.smoothTransition s| ≤ C := by
    by_cases hq : q = 0
    · subst q
      exact ⟨1, zero_le_one, fun s => by
        rw [iteratedDeriv_zero, abs_of_nonneg (Real.smoothTransition.nonneg s)]
        exact Real.smoothTransition.le_one s⟩
    have hc : Continuous (iteratedDeriv q Real.smoothTransition) :=
      (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_iteratedDeriv q
        (by simp)
    obtain ⟨s, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
      ⟨(0 : ℝ), le_rfl, zero_le_one⟩ hc.abs.continuousOn
    refine ⟨|iteratedDeriv q Real.smoothTransition s|, abs_nonneg _, fun x => ?_⟩
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · exact hmax hx
    · rw [iteratedDeriv_smoothTransition_zero_of_not_mem (Nat.pos_of_ne_zero hq) hx, abs_zero]
      exact abs_nonneg _
  choose C hC hBound using hBounds
  refine ⟨C, hC, fun q t₀ r t hr => ?_⟩
  rw [iteratedDeriv_waveSwitch, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hBound q (r * (t - t₀))) (pow_nonneg hr.le q)

/-- The small time weight is needed only while a positive-order
derivative of the switch can be nonzero. -/
theorem exists_waveSwitch_weighted_iteratedDeriv_bound :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ {q : ℕ}, 0 < q → ∀ {t₀ r G : ℝ}, 0 < r → 0 ≤ G → ∀ γ : ℝ → ℝ,
      (∀ t ∈ Icc t₀ (t₀ + 1 / r), |γ t| ≤ G) →
      ∀ t, |iteratedDeriv q (waveSwitch t₀ r) t| * |γ t| ≤ C q * r ^ q * G := by
  obtain ⟨C, hC, hSwitch⟩ := exists_waveSwitch_iteratedDeriv_bound
  refine ⟨C, hC, ?_⟩
  intro q hq t₀ r G hr hG γ hγ t
  have hRate : 0 ≤ C q * r ^ q := mul_nonneg (hC q) (pow_nonneg hr.le _)
  by_cases ht : t ∈ Icc t₀ (t₀ + 1 / r)
  · exact mul_le_mul (hSwitch q t₀ r t hr) (hγ t ht) (abs_nonneg _) hRate
  · rw [iteratedDeriv_waveSwitch_zero_of_not_mem hq hr ht, abs_zero, zero_mul]
    exact mul_nonneg hRate hG

end TorusEuler
