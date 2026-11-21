import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma bilin_sub_norm_le {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] X) (x y : X) :
    ‖B x x - B y y‖ ≤ ‖B‖ * ‖x - y‖ * ‖x‖ + ‖B‖ * ‖y‖ * ‖x - y‖ := by
  have e : B x x - B y y = B (x - y) x + B y (x - y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))

private lemma integral_sub_rpow_neg_three_quarters (t c : ℝ) :
    ∫ s in c..t, (t - s) ^ (-(3 / 4 : ℝ)) = 4 * (t - c) ^ ((1 : ℝ) / 4) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(3 / 4 : ℝ))) t]
  rw [integral_rpow (Or.inl (by norm_num))]
  simp only [sub_self]
  rw [Real.zero_rpow (by norm_num)]
  norm_num
  ring

private lemma intervalIntegrable_sub_rpow_neg_three_quarters (t c : ℝ) :
    IntervalIntegrable (fun s => (t - s) ^ (-(3 / 4 : ℝ))) volume c t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - c) (b := 0)
    (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left t
  simpa using h

private lemma mild_difference_estimate {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : MildFramework X) {C : ℝ}
    (hK : ∀ τ, 0 < τ → ‖F.K τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))) {u v : ℝ → X} {a b : ℝ}
    (hu : F.IsMildOnIcc u a b) (hv : F.IsMildOnIcc v a b) (h : u a = v a)
    {Mb E c t : ℝ} (hM : ∀ s ∈ Icc a b, ‖u s‖ ≤ Mb ∧ ‖v s‖ ≤ Mb) (hac : a ≤ c) (hct : c ≤ t)
    (htb : t ≤ b) (hzero : ∀ s ∈ Icc a c, u s = v s) (hE : ∀ s ∈ Icc c t, ‖u s - v s‖ ≤ E) :
    ‖u t - v t‖ ≤ 2 * C * Mb * E * (4 * (t - c) ^ ((1 : ℝ) / 4)) := by
  have ht : t ∈ Icc a b := ⟨hac.trans hct, htb⟩
  obtain ⟨hfi, hfe⟩ := hu.2 t ht
  obtain ⟨hgi, hge⟩ := hv.2 t ht
  have hdiff : u t - v t =
      ∫ s in a..t, (F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)) := by
    rw [intervalIntegral.integral_sub hfi hgi]
    rw [hfe, hge, h]
    abel
  have hfg := hfi.sub hgi
  have hat : a ≤ t := hac.trans hct
  have h1 : IntervalIntegrable
      (fun s => F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)) volume a c :=
    hfg.mono_set (by rw [uIcc_of_le hac, uIcc_of_le hat]; exact Icc_subset_Icc le_rfl hct)
  have h2 : IntervalIntegrable
      (fun s => F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)) volume c t :=
    hfg.mono_set (by rw [uIcc_of_le hct, uIcc_of_le hat]; exact Icc_subset_Icc hac le_rfl)
  have hz : ∫ s in a..c, (F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : X)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_le hac] at hs
      simp only [hzero s hs, sub_self]
  rw [hdiff, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, hz, zero_add]
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc c t →
      ‖F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)‖ ≤
        2 * C * Mb * E * (t - s) ^ (-(3 / 4 : ℝ)) := by
    filter_upwards [hne] with s hst hs
    have hτ : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hs.2 hst)
    have hsab : s ∈ Icc a b := ⟨hac.trans hs.1.le, hs.2.trans htb⟩
    have hds := hE s ⟨hs.1.le, hs.2⟩
    obtain ⟨hus, hvs⟩ := hM s hsab
    have hKb := hK (t - s) hτ
    have hKn : 0 ≤ ‖F.K (t - s)‖ := norm_nonneg _
    have hCp : 0 ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) := hKn.trans hKb
    have hEn : 0 ≤ E := (norm_nonneg _).trans hds
    have a1 : ‖F.K (t - s)‖ * ‖u s - v s‖ * ‖u s‖ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * E * Mb :=
      mul_le_mul (mul_le_mul hKb hds (norm_nonneg _) hCp) hus (norm_nonneg _)
        (mul_nonneg hCp hEn)
    have a2 : ‖F.K (t - s)‖ * ‖v s‖ * ‖u s - v s‖ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * Mb * E :=
      mul_le_mul (mul_le_mul hKb hvs (norm_nonneg _) hCp) hds (norm_nonneg _)
        (mul_nonneg hCp ((norm_nonneg _).trans hvs))
    calc ‖F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s)‖
        ≤ ‖F.K (t - s)‖ * ‖u s - v s‖ * ‖u s‖ + ‖F.K (t - s)‖ * ‖v s‖ * ‖u s - v s‖ :=
          bilin_sub_norm_le _ _ _
      _ ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) * E * Mb + C * (t - s) ^ (-(3 / 4 : ℝ)) * Mb * E :=
          add_le_add a1 a2
      _ = 2 * C * Mb * E * (t - s) ^ (-(3 / 4 : ℝ)) := by ring
  calc ‖∫ s in c..t, (F.K (t - s) (u s) (u s) - F.K (t - s) (v s) (v s))‖
      ≤ ∫ s in c..t, 2 * C * Mb * E * (t - s) ^ (-(3 / 4 : ℝ)) :=
        intervalIntegral.norm_integral_le_of_norm_le hct hbound
          ((intervalIntegrable_sub_rpow_neg_three_quarters t c).const_mul _)
    _ = 2 * C * Mb * E * ∫ s in c..t, (t - s) ^ (-(3 / 4 : ℝ)) :=
        intervalIntegral.integral_const_mul _ _
    _ = 2 * C * Mb * E * (4 * (t - c) ^ ((1 : ℝ) / 4)) := by
        rw [integral_sub_rpow_neg_three_quarters t c]

theorem MildFramework.eq_of_isMildOnIcc {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : MildFramework X) {C : ℝ}
    (hK : ∀ τ, 0 < τ → ‖F.K τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))) {u v : ℝ → X} {a b : ℝ}
    (hu : F.IsMildOnIcc u a b) (hv : F.IsMildOnIcc v a b) (h : u a = v a) :
    ∀ t ∈ Icc a b, u t = v t := by
  have hC : 0 ≤ C := by
    have h1 := hK 1 one_pos
    rw [Real.one_rpow, mul_one] at h1
    exact (norm_nonneg _).trans h1
  obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  obtain ⟨Mv, hMv⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.1
  set Mb := max (max Mu Mv) 0 with hMb
  have hMb0 : 0 ≤ Mb := le_max_right _ _
  have hM : ∀ s ∈ Icc a b, ‖u s‖ ≤ Mb ∧ ‖v s‖ ≤ Mb := fun s hs =>
    ⟨(hMu s hs).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hMv s hs).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  have hCM : 0 ≤ C * Mb := mul_nonneg hC hMb0
  set q : ℝ := 1 / (16 * (C * Mb) + 1) with hq
  have hden : 0 < 16 * (C * Mb) + 1 := by linarith
  have hqpos : 0 < q := by rw [hq]; positivity
  have hsmall : 8 * (C * Mb) * q ≤ 1 / 2 := by
    rw [hq, mul_one_div, div_le_iff₀ hden]
    linarith
  set hh : ℝ := q ^ 4 with hhh
  have hhpos : 0 < hh := by positivity
  have hroot : hh ^ ((1 : ℝ) / 4) = q := by
    rw [hhh, show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hqpos.le (by norm_num)
  have claim : ∀ n : ℕ, ∀ s ∈ Icc a b, s ≤ a + n * hh → u s = v s := by
    intro n
    induction n with
    | zero =>
      intro s hs hsn
      have : s = a := le_antisymm (by simpa using hsn) hs.1
      rw [this, h]
    | succ n ih =>
      intro s hs hsn
      by_cases hsc : s ≤ a + n * hh
      · exact ih s hs hsc
      replace hsc := not_le.1 hsc
      set c := a + n * hh with hc
      have hac : a ≤ c := by
        have : 0 ≤ (n : ℝ) * hh := mul_nonneg (Nat.cast_nonneg _) hhpos.le
        linarith
      set e := min (c + hh) b with he
      have hse : s ∈ Icc a e := ⟨hs.1, le_min (by push_cast at hsn; linarith) hs.2⟩
      have heb : e ≤ b := min_le_right _ _
      have hsub : Icc a e ⊆ Icc a b := Icc_subset_Icc le_rfl heb
      have hcont : ContinuousOn (fun s => ‖u s - v s‖) (Icc a e) :=
        ((hu.1.mono hsub).sub (hv.1.mono hsub)).norm
      obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s, hse⟩ hcont
      have hzero0 : ‖u t₀ - v t₀‖ = 0 := by
        by_cases ht₀c : t₀ ≤ c
        · rw [ih t₀ (hsub ht₀) ht₀c, sub_self, norm_zero]
        replace ht₀c := not_le.1 ht₀c
        have hzc : ∀ r ∈ Icc a c, u r = v r := fun r hr =>
          ih r ⟨hr.1, hr.2.trans (ht₀c.le.trans (ht₀.2.trans heb))⟩ hr.2
        have hEt : ∀ r ∈ Icc c t₀, ‖u r - v r‖ ≤ ‖u t₀ - v t₀‖ := fun r hr =>
          hmax ⟨hac.trans hr.1, hr.2.trans ht₀.2⟩
        have hest := mild_difference_estimate F hK hu hv h hM hac ht₀c.le (ht₀.2.trans heb)
          hzc hEt
        have hlen : t₀ - c ≤ hh := by
          have := ht₀.2.trans (min_le_left _ _)
          linarith
        have hpow : (t₀ - c) ^ ((1 : ℝ) / 4) ≤ q := by
          rw [← hroot]
          exact Real.rpow_le_rpow (by linarith) hlen (by norm_num)
        have hE0 : 0 ≤ ‖u t₀ - v t₀‖ := norm_nonneg _
        have hfin : ‖u t₀ - v t₀‖ ≤ ‖u t₀ - v t₀‖ / 2 := by
          calc ‖u t₀ - v t₀‖ ≤ 2 * C * Mb * ‖u t₀ - v t₀‖ * (4 * (t₀ - c) ^ ((1 : ℝ) / 4)) :=
                hest
            _ = (8 * (C * Mb) * (t₀ - c) ^ ((1 : ℝ) / 4)) * ‖u t₀ - v t₀‖ := by ring
            _ ≤ (8 * (C * Mb) * q) * ‖u t₀ - v t₀‖ := by
                apply mul_le_mul_of_nonneg_right _ hE0
                exact mul_le_mul_of_nonneg_left hpow (by linarith)
            _ ≤ (1 / 2) * ‖u t₀ - v t₀‖ := mul_le_mul_of_nonneg_right hsmall hE0
            _ = ‖u t₀ - v t₀‖ / 2 := by ring
        linarith
      have hs0 : ‖u s - v s‖ ≤ 0 := hzero0 ▸ hmax hse
      exact sub_eq_zero.1 (norm_le_zero_iff.1 hs0)
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / hh)
  apply claim n t ht
  have : b - a < n * hh := (div_lt_iff₀ hhpos).1 hn
  linarith [ht.2]

end Breakdown
