import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.BilinIntegrable

theorem bilinX_diag_sub (τ : ℝ) (u w : X) :
    bilinX τ u u - bilinX τ w w = bilinX τ (u - w) u + bilinX τ w (u - w) := by
  simp only [map_sub, sub_apply]
  abel

theorem continuous_bilinX_max {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : ℝ × X => bilinX (max p.1 δ) p.2 p.2) := by
  obtain ⟨C, hC0, hC⟩ := bilin_holds.2
  have hg : Continuous (fun p : ℝ × X => max p.1 δ) := continuous_fst.max continuous_const
  have hpos : ∀ p : ℝ × X, 0 < max p.1 δ := fun p => lt_of_lt_of_le hδ (le_max_right _ _)
  have hKle : ∀ p : ℝ × X, C * (max p.1 δ) ^ (-(3 / 4 : ℝ)) ≤ C * δ ^ (-(3 / 4 : ℝ)) := fun p =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ (le_max_right _ _) (by norm_num)) hC0
  rw [continuous_iff_continuousAt]
  intro p₀
  have hD : ContinuousAt (fun p : ℝ × X => bilinX (max p.1 δ) p₀.2 p₀.2) p₀ := by
    have h1 : ContinuousWithinAt (fun τ => bilinX τ p₀.2 p₀.2) (Ioi 0) (max p₀.1 δ) :=
      bilinCont_holds p₀.2 p₀.2 _ (hpos p₀)
    exact ContinuousAt.comp (g := fun τ => bilinX τ p₀.2 p₀.2) (f := fun p : ℝ × X => max p.1 δ)
      (h1.continuousAt (Ioi_mem_nhds (hpos p₀))) hg.continuousAt
  have hA : Continuous (fun p : ℝ × X => C * δ ^ (-(3 / 4 : ℝ)) *
      (‖p.2 - p₀.2‖ * ‖p.2‖ + ‖p₀.2‖ * ‖p.2 - p₀.2‖)) :=
    continuous_const.mul (((continuous_snd.sub continuous_const).norm.mul continuous_snd.norm).add
      (continuous_const.mul (continuous_snd.sub continuous_const).norm))
  have hlim : Tendsto (fun p : ℝ × X => C * δ ^ (-(3 / 4 : ℝ)) *
      (‖p.2 - p₀.2‖ * ‖p.2‖ + ‖p₀.2‖ * ‖p.2 - p₀.2‖) +
      ‖bilinX (max p.1 δ) p₀.2 p₀.2 - bilinX (max p₀.1 δ) p₀.2 p₀.2‖) (𝓝 p₀) (𝓝 0) := by
    have := (hA.tendsto p₀).add (tendsto_iff_norm_sub_tendsto_zero.1 hD.tendsto)
    simpa only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) hlim
  have e : bilinX (max p.1 δ) p.2 p.2 - bilinX (max p₀.1 δ) p₀.2 p₀.2 =
      (bilinX (max p.1 δ) (p.2 - p₀.2) p.2 + bilinX (max p.1 δ) p₀.2 (p.2 - p₀.2)) +
        (bilinX (max p.1 δ) p₀.2 p₀.2 - bilinX (max p₀.1 δ) p₀.2 p₀.2) := by
    have e0 := bilinX_diag_sub (max p.1 δ) p.2 p₀.2
    exact (sub_add_sub_cancel _ (bilinX (max p.1 δ) p₀.2 p₀.2) _).symm.trans
      (congrArg (· + (bilinX (max p.1 δ) p₀.2 p₀.2 - bilinX (max p₀.1 δ) p₀.2 p₀.2)) e0)
  refine (congrArg norm e).le.trans ?_
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
  have h1 := hC _ (hpos p) (p.2 - p₀.2) p.2
  have h2 := hC _ (hpos p) p₀.2 (p.2 - p₀.2)
  calc _ ≤ C * (max p.1 δ) ^ (-(3 / 4 : ℝ)) * ‖p.2 - p₀.2‖ * ‖p.2‖ +
        C * (max p.1 δ) ^ (-(3 / 4 : ℝ)) * ‖p₀.2‖ * ‖p.2 - p₀.2‖ := add_le_add h1 h2
    _ = C * (max p.1 δ) ^ (-(3 / 4 : ℝ)) * (‖p.2 - p₀.2‖ * ‖p.2‖ + ‖p₀.2‖ * ‖p.2 - p₀.2‖) := by
        ring
    _ ≤ C * δ ^ (-(3 / 4 : ℝ)) * (‖p.2 - p₀.2‖ * ‖p.2‖ + ‖p₀.2‖ * ‖p.2 - p₀.2‖) :=
        mul_le_mul_of_nonneg_right (hKle p) (by positivity)

theorem aestronglyMeasurable_piece (y : ℝ → X) (l r : ℝ)
    (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r))) {t₀ t ε : ℝ} (hl : l < t₀)
    (htr : t < r) (hε : 0 ≤ ε) (n : ℕ) :
    AEStronglyMeasurable (fun τ => bilinX (t - τ + ε) (y τ) (y τ))
      (volume.restrict (Ioo t₀ (t - 1 / ((n : ℝ) + 1)))) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsub : Ioo t₀ (t - 1 / ((n : ℝ) + 1)) ⊆ Ioo l r := fun τ hτ =>
    ⟨hl.trans hτ.1, by linarith [hτ.2]⟩
  have hy' := hy.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hc : Continuous (fun τ : ℝ => t - τ + ε) := (continuous_const.sub continuous_id).add continuous_const
  have hm : AEStronglyMeasurable (fun τ => bilinX (max (t - τ + ε) (1 / ((n : ℝ) + 1))) (y τ) (y τ))
      (volume.restrict (Ioo t₀ (t - 1 / ((n : ℝ) + 1)))) :=
    Continuous.comp_aestronglyMeasurable (g := fun p : ℝ × X => bilinX (max p.1 (1 / ((n : ℝ) + 1))) p.2 p.2)
      (f := fun τ => (t - τ + ε, y τ)) (continuous_bilinX_max hδ) (hc.aestronglyMeasurable.prodMk hy')
  refine hm.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun τ hτ => ?_)
  have h : 1 / ((n : ℝ) + 1) ≤ t - τ + ε := by linarith [hτ.2]
  simp only [max_eq_left h]

theorem aestronglyMeasurable_Ioo (y : ℝ → X) (l r : ℝ)
    (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r))) {t₀ t ε : ℝ} (hl : l < t₀)
    (htr : t < r) (hε : 0 ≤ ε) :
    AEStronglyMeasurable (fun τ => bilinX (t - τ + ε) (y τ) (y τ)) (volume.restrict (Ioo t₀ t)) := by
  have hU : Ioo t₀ t = ⋃ n : ℕ, Ioo t₀ (t - 1 / ((n : ℝ) + 1)) := by
    ext τ
    simp only [mem_Ioo, mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
      exact ⟨n, h1, by linarith⟩
    · rintro ⟨n, h1, h2⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨h1, by linarith⟩
  rw [hU]
  exact aestronglyMeasurable_iUnion_iff.2 fun n => aestronglyMeasurable_piece y l r hy hl htr hε n

end Internal.BilinIntegrable

open Internal.BilinIntegrable in
theorem bilinIntegrable_holds : BilinIntegrable := by
  intro y l r M hM hy t₀ t ε hl ht htr hε
  obtain ⟨C, hC0, hC⟩ := bilin_holds.2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hpow : IntegrableOn (fun τ => (t - τ + ε) ^ (-(3 / 4 : ℝ))) (Ioo t₀ t) := by
    have h0 := (intervalIntegral.intervalIntegrable_rpow' (r := -(3 / 4 : ℝ)) (by norm_num)
      (a := ε) (b := t - t₀ + ε)).comp_sub_left (t + ε)
    have e1 : t + ε - ε = t := by ring
    have e2 : t + ε - (t - t₀ + ε) = t₀ := by ring
    rw [e1, e2] at h0
    have h3 := h0.symm
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht] at h3
    refine h3.congr_fun (fun x _ => ?_) measurableSet_Ioo
    show (t + ε - x) ^ (-(3 / 4 : ℝ)) = (t - x + ε) ^ (-(3 / 4 : ℝ))
    rw [show t + ε - x = t - x + ε by ring]
  refine Integrable.mono' (hpow.const_mul (C * max M 0 ^ 2))
    (aestronglyMeasurable_Ioo y l r hy hl htr hε) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun τ hτ => ?_)
  have hτ' : 0 < t - τ + ε := by linarith [hτ.2]
  have hyτ : ‖y τ‖ ≤ max M 0 := (hM τ ⟨hl.trans hτ.1, hτ.2.trans htr⟩).trans (le_max_left _ _)
  have hp : 0 ≤ C * (t - τ + ε) ^ (-(3 / 4 : ℝ)) := mul_nonneg hC0 (Real.rpow_nonneg hτ'.le _)
  calc ‖bilinX (t - τ + ε) (y τ) (y τ)‖ ≤ C * (t - τ + ε) ^ (-(3 / 4 : ℝ)) * ‖y τ‖ * ‖y τ‖ :=
        hC _ hτ' _ _
    _ ≤ C * (t - τ + ε) ^ (-(3 / 4 : ℝ)) * max M 0 * max M 0 := by
        rw [mul_assoc _ ‖y τ‖, mul_assoc _ (max M 0)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hyτ hyτ (norm_nonneg _) (le_max_right _ _)) hp
    _ = C * max M 0 ^ 2 * (t - τ + ε) ^ (-(3 / 4 : ℝ)) := by ring

end Breakdown.WeakProfile
