import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private theorem heatBilinear_ck_nonneg (H : HeatBilinear X) : 0 ≤ H.CK := by
  have h := H.K_bound 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

private theorem exists_contraction_length (H : HeatBilinear X) (M : ℝ) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 8 * H.CK * δ ^ (1 / 4 : ℝ) * M ≤ 1 / 2 := by
  have hC := heatBilinear_ck_nonneg H
  have hpos : 0 < 16 * H.CK * M + 1 := by positivity
  set c : ℝ := (16 * H.CK * M + 1)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hpos
  refine ⟨min 1 (c ^ 4), lt_min one_pos (pow_pos hc0 4), min_le_left _ _, ?_⟩
  have hroot : (c ^ 4) ^ (1 / 4 : ℝ) = c := by
    have h := Real.pow_rpow_inv_natCast hc0.le (n := 4) (by norm_num)
    rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact h
  have h1 : (min 1 (c ^ 4)) ^ (1 / 4 : ℝ) ≤ c :=
    calc (min 1 (c ^ 4)) ^ (1 / 4 : ℝ) ≤ (c ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (le_min zero_le_one (pow_pos hc0 4).le) (min_le_right _ _)
            (by norm_num)
      _ = c := hroot
  have h2 : 16 * H.CK * M * c ≤ 1 := by
    rw [hc, ← div_eq_mul_inv, div_le_one hpos]
    linarith
  have h3 : 0 ≤ 8 * H.CK * M := by positivity
  have h4 := mul_le_mul_of_nonneg_left h1 h3
  nlinarith

private theorem eq_on_next_interval (h1 : VarConstIntegralStatement) (h2 : RestrictStatement)
    (H : HeatBilinear X) (u v : ℝ → X) (a T M δ : ℝ) (hu : ContinuousOn u (Icc a T))
    (hv : ContinuousOn v (Icc a T)) (hdu : ∀ t ∈ Icc a T, H.VarConst u a t)
    (hdv : ∀ t ∈ Icc a T, H.VarConst v a t) (hMu : ∀ s ∈ Icc a T, ‖u s‖ ≤ M)
    (hMv : ∀ s ∈ Icc a T, ‖v s‖ ≤ M) (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : 8 * H.CK * δ ^ (1 / 4 : ℝ) * M ≤ 1 / 2) (m : ℝ) (hm : m ∈ Icc a T)
    (heq : ∀ r ∈ Icc a m, u r = v r) : ∀ r ∈ Icc a (min (m + δ) T), u r = v r := by
  have hC := heatBilinear_ck_nonneg H
  set m' := min (m + δ) T with hm'
  have hmm' : m ≤ m' := le_min (by linarith) hm.2
  have hm'T : m' ≤ T := min_le_right _ _
  have hm'δ : m' ≤ m + δ := min_le_left _ _
  have hsub : Icc m m' ⊆ Icc a T := Icc_subset_Icc hm.1 hm'T
  have hsub' : ∀ t ∈ Icc m m', Icc a t ⊆ Icc a T := fun t ht =>
    Icc_subset_Icc le_rfl (ht.2.trans hm'T)
  have hdum : ∀ t ∈ Icc m m', H.VarConst u m t := fun t ht =>
    h2 X H u a m t hm.1 ht.1 (hu.mono (hsub' t ht)) (hdu m hm) (hdu t (hsub ht))
  have hdvm : ∀ t ∈ Icc m m', H.VarConst v m t := fun t ht =>
    h2 X H v a m t hm.1 ht.1 (hv.mono (hsub' t ht)) (hdv m hm) (hdv t (hsub ht))
  have hcd : ContinuousOn (fun s => u s - v s) (Icc m m') := (hu.mono hsub).sub (hv.mono hsub)
  obtain ⟨s₀, hs₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hmm') hcd.norm
  have hN : ∀ s ∈ Icc m m', ‖u s - v s‖ ≤ ‖u s₀ - v s₀‖ := fun s hs =>
    isMaxOn_iff.mp hmax s hs
  obtain ⟨hi1, hb1, -⟩ := h1 X H (fun s => u s - v s) u m m' ‖u s₀ - v s₀‖ M hmm' hcd
    (hu.mono hsub) hN (fun s hs => hMu s (hsub hs))
  obtain ⟨hi2, hb2, -⟩ := h1 X H v (fun s => u s - v s) m m' M ‖u s₀ - v s₀‖ hmm'
    (hv.mono hsub) hcd (fun s hs => hMv s (hsub hs)) hN
  have hkey : ∀ t ∈ Icc m m', ‖u t - v t‖ ≤ ‖u s₀ - v s₀‖ / 2 := by
    intro t ht
    have hum := (hdum t ht).2
    have hvm := (hdvm t ht).2
    have huvm : u m = v m := heq m ⟨hm.1, le_rfl⟩
    have hrepr : u t - v t = (∫ s in m..t, H.K (t - s) (u s - v s) (u s)) +
        ∫ s in m..t, H.K (t - s) (v s) (u s - v s) := by
      rw [hum, hvm, huvm, ← intervalIntegral.integral_add (hi1 t ht) (hi2 t ht),
        add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hdum t ht).1 (hdvm t ht).1]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [map_sub, sub_apply]
      abel
    have ht1 : t - m ≤ 1 := by linarith [ht.2]
    have e1 := hb1 t ht ht1
    have e2 := hb2 t ht ht1
    have hr : (t - m) ^ (1 / 4 : ℝ) ≤ δ ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) (by norm_num)
    have hx := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 8 * (H.CK * ‖u s₀ - v s₀‖ * M) by positivity)
    have hy := mul_le_mul_of_nonneg_right hδ (norm_nonneg (u s₀ - v s₀))
    rw [hrepr]
    refine (norm_add_le _ _).trans ?_
    linarith
  have hzero : ‖u s₀ - v s₀‖ ≤ 0 := by
    have := hkey s₀ hs₀
    linarith
  intro r hr
  by_cases hrm : r ≤ m
  · exact heq r ⟨hr.1, hrm⟩
  · have hr' : r ∈ Icc m m' := ⟨le_of_lt (not_le.mp hrm), hr.2⟩
    have := (hN r hr').trans hzero
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

private theorem eq_on_Icc_of_varConst (h1 : VarConstIntegralStatement) (h2 : RestrictStatement)
    (H : HeatBilinear X) (u v : ℝ → X) (a T : ℝ) (haT : a ≤ T) (hu : ContinuousOn u (Icc a T))
    (hv : ContinuousOn v (Icc a T)) (hdu : ∀ t ∈ Icc a T, H.VarConst u a t)
    (hdv : ∀ t ∈ Icc a T, H.VarConst v a t) (h0 : u a = v a) :
    ∀ t ∈ Icc a T, u t = v t := by
  obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  obtain ⟨Mv, hMv⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  have hM0 : 0 ≤ max (max Mu Mv) 0 := le_max_right _ _
  have hMu' : ∀ s ∈ Icc a T, ‖u s‖ ≤ max (max Mu Mv) 0 := fun s hs =>
    (hMu s hs).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hMv' : ∀ s ∈ Icc a T, ‖v s‖ ≤ max (max Mu Mv) 0 := fun s hs =>
    (hMv s hs).trans ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_contraction_length H _ hM0
  have hind : ∀ n : ℕ, ∀ r ∈ Icc a (min (a + n * δ) T), u r = v r := by
    intro n
    induction n with
    | zero =>
      intro r hr
      have h' : r ≤ a + ((0 : ℕ) : ℝ) * δ := hr.2.trans (min_le_left _ _)
      simp only [Nat.cast_zero, zero_mul, add_zero] at h'
      rw [le_antisymm h' hr.1]
      exact h0
    | succ n ih =>
      intro r hr
      have hm : min (a + n * δ) T ∈ Icc a T :=
        ⟨le_min (le_add_of_nonneg_right (mul_nonneg n.cast_nonneg hδ0.le)) haT,
          min_le_right _ _⟩
      refine eq_on_next_interval h1 h2 H u v a T _ δ hu hv hdu hdv hMu' hMv' hM0 hδ0.le hδ1 hδ
        _ hm ih r ⟨hr.1, ?_⟩
      have h3 := le_min_iff.mp hr.2
      push_cast at h3
      refine le_min ?_ h3.2
      rcases min_cases (a + n * δ) T with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith [h3.1, h3.2]
  obtain ⟨n, hn⟩ := exists_nat_ge ((T - a) / δ)
  intro t ht
  refine hind n t ⟨ht.1, le_min ?_ ht.2⟩
  have := (div_le_iff₀ hδ0).mp hn
  linarith [ht.2]

theorem unique_of (h1 : VarConstIntegralStatement) (h2 : RestrictStatement) : UniqueStatement := by
  intro X _ _ _ H u v a b
  constructor
  · rintro ⟨hu, hdu⟩ ⟨hv, hdv⟩ h0 t ht
    have hsub : Icc a t ⊆ Ico a b := Icc_subset_Ico_right ht.2
    exact eq_on_Icc_of_varConst h1 h2 H u v a t ht.1 (hu.mono hsub) (hv.mono hsub)
      (fun s hs => hdu s (hsub hs)) (fun s hs => hdv s (hsub hs)) h0 t ⟨ht.1, le_rfl⟩
  · rintro ⟨hu, hdu⟩ ⟨hv, hdv⟩ h0 t ht
    exact eq_on_Icc_of_varConst h1 h2 H u v a b (ht.1.trans ht.2) hu hv hdu hdv h0 t ht

end Breakdown
