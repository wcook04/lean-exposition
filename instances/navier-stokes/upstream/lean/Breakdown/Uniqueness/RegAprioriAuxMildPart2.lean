import Mathlib

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.SmoothFlow

private theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem lintegral_sq_lintegral_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SigmaFinite ν] {μ : Measure ℝ} [SFinite μ] {h : ℝ → β → ℝ≥0∞}
    (hh : AEMeasurable (Function.uncurry h) (μ.prod ν)) :
    ∫⁻ ξ, (∫⁻ s, h s ξ ∂μ) ^ 2 ∂ν ≤ (∫⁻ s, (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  set G : β → ℝ≥0∞ := fun ξ => ∫⁻ s, h s ξ ∂μ with hGdef
  set R := ∫⁻ s, (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ with hRdef
  have hG : AEMeasurable G ν := hh.lintegral_prod_left'
  have hsec : ∀ᵐ s ∂μ, AEMeasurable (h s) ν := by
    filter_upwards [hh.aestronglyMeasurable.prodMk_left] with s hs using hs.aemeasurable
  set Φ : ℕ → β → ℝ≥0∞ := fun n ξ =>
    (spanningSets ν n).indicator (fun ξ => min (G ξ) (n : ℝ≥0∞)) ξ with hΦdef
  have hΦm : ∀ n, AEMeasurable (Φ n) ν := fun n =>
    (hG.min aemeasurable_const).indicator (measurableSet_spanningSets ν n)
  have hΦG : ∀ n ξ, Φ n ξ ≤ G ξ := by
    intro n ξ
    by_cases hξ : ξ ∈ spanningSets ν n
    · simp only [hΦdef, Set.indicator_of_mem hξ]
      exact min_le_left _ _
    · simp [hΦdef, Set.indicator_of_notMem hξ]
  have hΦfin : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top (b := ∫⁻ ξ, (spanningSets ν n).indicator
      (fun _ => ((n : ℝ≥0∞)) ^ 2) ξ ∂ν) ?_ (lintegral_mono fun ξ => ?_)
    · rw [lintegral_indicator_const (measurableSet_spanningSets ν n)]
      exact ENNReal.mul_ne_top (by simp) (measure_spanningSets_lt_top ν n).ne
    · by_cases hξ : ξ ∈ spanningSets ν n
      · simp only [hΦdef, Set.indicator_of_mem hξ]
        gcongr
        exact min_le_right _ _
      · simp [hΦdef, Set.indicator_of_notMem hξ]
  have key : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * R := by
    intro n
    calc ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ ∫⁻ ξ, Φ n ξ * G ξ ∂ν := lintegral_mono fun ξ => by
          rw [sq]
          gcongr
          exact hΦG n ξ
      _ ≤ ∫⁻ ξ, ∫⁻ s, Φ n ξ * h s ξ ∂μ ∂ν := lintegral_mono fun ξ => lintegral_const_mul_le _ _
      _ = ∫⁻ s, ∫⁻ ξ, Φ n ξ * h s ξ ∂ν ∂μ :=
          (lintegral_lintegral_swap (f := fun s ξ => Φ n ξ * h s ξ)
            ((hΦm n).comp_snd.mul hh)).symm
      _ ≤ ∫⁻ s, (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ ξ, h s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsec] with s hs
          have := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two (hΦm n) hs
          simp only [Pi.mul_apply, ENNReal.rpow_two] at this
          exact this
      _ = (∫⁻ ξ, Φ n ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) * R :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hΦfin n))
  have hle : ∀ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν ≤ R ^ 2 := by
    intro n
    set X := ∫⁻ ξ, Φ n ξ ^ 2 ∂ν with hXdef
    set y := X ^ (1 / 2 : ℝ) with hy
    have hsq : X = y ^ 2 := (rpow_half_sq X).symm
    have hX : y * y ≤ y * R := by
      rw [← sq, ← hsq]
      exact key n
    by_cases h0 : y = 0
    · rw [hsq, h0]
      simp
    · have htop : y ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hΦfin n)
      have hyR : y ≤ R := (ENNReal.mul_le_mul_iff_right h0 htop).mp hX
      rw [hsq]
      gcongr
  have hsup : ∀ ξ, G ξ ^ 2 = ⨆ n, Φ n ξ ^ 2 := by
    intro ξ
    rw [← ENNReal.iSup_pow]
    congr 1
    refine le_antisymm ?_ (iSup_le fun n => hΦG n ξ)
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    set n := max N (spanningSetsIndex ν ξ)
    have hmem : ξ ∈ spanningSets ν n := mem_spanningSets_of_index_le ν ξ (le_max_right _ _)
    refine lt_iSup_iff.mpr ⟨n, ?_⟩
    simp only [hΦdef, Set.indicator_of_mem hmem]
    refine lt_min hc (hN.trans_le ?_)
    exact_mod_cast le_max_left _ _
  have hmono : ∀ ξ, Monotone fun n => Φ n ξ ^ 2 := by
    intro ξ a b hab
    by_cases ha : ξ ∈ spanningSets ν a
    · have hb := monotone_spanningSets ν hab ha
      simp only [hΦdef, Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      gcongr
    · simp [hΦdef, Set.indicator_of_notMem ha]
  calc ∫⁻ ξ, G ξ ^ 2 ∂ν = ∫⁻ ξ, ⨆ n, Φ n ξ ^ 2 ∂ν := lintegral_congr fun ξ => hsup ξ
    _ = ⨆ n, ∫⁻ ξ, Φ n ξ ^ 2 ∂ν :=
        lintegral_iSup' (fun n => (hΦm n).pow_const 2) (ae_of_all _ hmono)
    _ ≤ R ^ 2 := iSup_le hle

theorem lintegral_weighted_add_lintegral_sq_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SigmaFinite ν] {S : Set ℝ} {w a : β → ℝ≥0∞}
    {g : ℝ → β → ℝ≥0∞} (hw : Measurable w) (ha : AEMeasurable a ν)
    (hg : AEMeasurable (Function.uncurry g) ((volume.restrict S).prod ν)) :
    (∫⁻ ξ, w ξ * (a ξ + ∫⁻ s in S, g s ξ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ξ, w ξ * a ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) +
        ∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  set A : β → ℝ≥0∞ := fun ξ => w ξ ^ (1 / 2 : ℝ) * a ξ with hAdef
  set h : ℝ → β → ℝ≥0∞ := fun s ξ => w ξ ^ (1 / 2 : ℝ) * g s ξ with hhdef
  set H : β → ℝ≥0∞ := fun ξ => ∫⁻ s in S, h s ξ with hHdef
  have hwm : Measurable fun ξ => w ξ ^ (1 / 2 : ℝ) := hw.pow_const _
  have hA : AEMeasurable A ν := hwm.aemeasurable.mul ha
  have hh : AEMeasurable (Function.uncurry h) ((volume.restrict S).prod ν) :=
    (hwm.comp measurable_snd).aemeasurable.mul hg
  have hH : AEMeasurable H ν := hh.lintegral_prod_left'
  have hsq : ∀ x y : ℝ≥0∞, (x ^ (1 / 2 : ℝ) * y) ^ 2 = x * y ^ 2 := fun x y => by
    rw [mul_pow, rpow_half_sq]
  have h1 : ∫⁻ ξ, w ξ * (a ξ + ∫⁻ s in S, g s ξ) ^ 2 ∂ν ≤ ∫⁻ ξ, (A ξ + H ξ) ^ 2 ∂ν := by
    refine lintegral_mono fun ξ => ?_
    rw [← hsq, mul_add]
    gcongr
    exact lintegral_const_mul_le _ _
  have h2 := ENNReal.lintegral_Lp_add_le hA hH (p := 2) (by norm_num)
  simp only [Pi.add_apply, ENNReal.rpow_two] at h2
  have h3 : (∫⁻ ξ, H ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ ∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    have := lintegral_sq_lintegral_le hh
    have e : ∀ s, ∫⁻ ξ, h s ξ ^ 2 ∂ν = ∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν := fun s =>
      lintegral_congr fun ξ => hsq _ _
    simp only [e] at this
    calc (∫⁻ ξ, H ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
        ((∫⁻ s in S, (∫⁻ ξ, w ξ * g s ξ ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow this (by norm_num)
      _ = _ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  have e2 : ∫⁻ ξ, A ξ ^ 2 ∂ν = ∫⁻ ξ, w ξ * a ξ ^ 2 ∂ν := lintegral_congr fun ξ => hsq _ _
  rw [e2] at h2
  calc _ ≤ (∫⁻ ξ, (A ξ + H ξ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ ≤ _ := h2.trans (add_le_add le_rfl h3)

end Breakdown.SmoothFlow
