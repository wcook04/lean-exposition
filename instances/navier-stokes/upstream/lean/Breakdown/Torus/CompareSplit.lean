import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace CompareSplit.Internal

theorem rpow_sub_intervalIntegrable (u : ℝ) :
    IntervalIntegrable (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) volume 0 u := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := u)
    (show (-1 : ℝ) < -(3 / 4 : ℝ) by norm_num)).comp_sub_left u
  simpa using h.symm

theorem tail_intervalIntegrable (u ε : ℝ) :
    IntervalIntegrable ((Ioi (u - ε)).indicator fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) volume 0 u := by
  have h := rpow_sub_intervalIntegrable u
  exact ⟨h.1.indicator measurableSet_Ioi, h.2.indicator measurableSet_Ioi⟩

theorem tail_integral_le (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∫ σ in (0 : ℝ)..u, (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ ≤
      4 * ε ^ (1 / 4 : ℝ) := by
  set p := max 0 (u - ε) with hp
  have hp0 : 0 ≤ p := le_max_left _ _
  have hpu : p ≤ u := max_le hu (by linarith)
  have hI := tail_intervalIntegrable u ε
  have h0p : IntervalIntegrable ((Ioi (u - ε)).indicator fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ)))
      volume 0 p := hI.mono_set (by rw [uIcc_of_le hp0, uIcc_of_le hu]; exact Icc_subset_Icc le_rfl hpu)
  have hpu' : IntervalIntegrable ((Ioi (u - ε)).indicator fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ)))
      volume p u := hI.mono_set (by rw [uIcc_of_le hpu, uIcc_of_le hu]; exact Icc_subset_Icc hp0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0p hpu']
  have e1 : ∫ σ in (0 : ℝ)..p, (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ = 0 := by
    have hz : ∫ σ in (0 : ℝ)..p, (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ =
        ∫ σ in (0 : ℝ)..p, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun σ hσ => ?_)
      rw [uIoc_of_le hp0] at hσ
      have hσp : σ ≤ u - ε := by
        rcases le_total 0 (u - ε) with h | h
        · have : p = u - ε := max_eq_right h
          linarith [hσ.2]
        · have : p = 0 := max_eq_left h
          linarith [hσ.1, hσ.2]
      rw [indicator_of_notMem (by simpa using hσp)]
    rw [hz, intervalIntegral.integral_zero]
  have e2 : ∫ σ in p..u, (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ =
      ∫ σ in p..u, (u - σ) ^ (-(3 / 4 : ℝ)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [uIoc_of_le hpu] at hσ
    have : u - ε < σ := lt_of_le_of_lt (le_max_right _ _) hσ.1
    rw [indicator_of_mem (show σ ∈ Ioi (u - ε) from this)]
  rw [e1, e2, zero_add, intervalIntegral.integral_comp_sub_left (fun r : ℝ => r ^ (-(3 / 4 : ℝ))) u,
    sub_self, integral_rpow (Or.inl (by norm_num))]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num), sub_zero, div_eq_mul_inv,
    show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num]
  have hup : 0 ≤ u - p := by linarith
  have hue : u - p ≤ ε := by
    have : u - ε ≤ p := le_max_right _ _
    linarith
  have := Real.rpow_le_rpow hup hue (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  linarith

end CompareSplit.Internal

theorem splitIntegralBound : SplitIntegralBound := by
  intro E _ _ _ f u ε a c hu hε ha hc hf
  set g : ℝ → ℝ := fun σ => a + c * (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ
    with hg
  have hgi : IntervalIntegrable g volume 0 u :=
    intervalIntegrable_const.add ((CompareSplit.Internal.tail_intervalIntegrable u ε).const_mul c)
  have hbound : ∀ᵐ t ∂volume, t ∈ Ioc 0 u → ‖f t‖ ≤ g t := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) u)] with t ht hmem
    have htu : t < u := lt_of_le_of_ne hmem.2 (by simpa using ht)
    have hind : 0 ≤ (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) t := by
      by_cases hm : t ∈ Ioi (u - ε)
      · rw [indicator_of_mem hm]
        exact Real.rpow_nonneg (by linarith) _
      · rw [indicator_of_notMem hm]
    rcases hf t ⟨hmem.1, htu⟩ with h | ⟨h1, h2⟩
    · have : 0 ≤ c * (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) t :=
        mul_nonneg hc hind
      simp only [hg]
      linarith
    · have hin : t ∈ Ioi (u - ε) := by simp; linarith
      simp only [hg, indicator_of_mem hin]
      linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hu hbound hgi
  have h2 : ∫ σ in (0 : ℝ)..u, g σ = a * u + c * ∫ σ in (0 : ℝ)..u,
      (Ioi (u - ε)).indicator (fun σ : ℝ => (u - σ) ^ (-(3 / 4 : ℝ))) σ := by
    simp only [hg]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((CompareSplit.Internal.tail_intervalIntegrable u ε).const_mul c),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero, mul_comm u a]
  have h3 := CompareSplit.Internal.tail_integral_le u ε hu hε
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  rw [h2] at h1
  linarith

end Breakdown.Periodic
