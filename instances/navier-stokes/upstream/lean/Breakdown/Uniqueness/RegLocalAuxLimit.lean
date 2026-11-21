import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def hsMeasure (m : ℕ) : Measure Space :=
  volume.withDensity (fun ξ => ENNReal.ofReal (hsWeight m ξ))

private theorem measurable_ofReal_hsWeight (m : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight m ξ)) := by
  unfold hsWeight
  fun_prop

private theorem hsMeasure_ac (m : ℕ) : hsMeasure m ≪ volume :=
  withDensity_absolutelyContinuous _ _

private theorem volume_ac_hsMeasure (m : ℕ) : (volume : Measure Space) ≪ hsMeasure m :=
  withDensity_absolutelyContinuous' (measurable_ofReal_hsWeight m).aemeasurable
    (Eventually.of_forall fun ξ => by
      unfold hsWeight
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity)

private theorem eLpNorm_hsMeasure (m : ℕ) (f : Space → CSpace) :
    eLpNorm f 2 (hsMeasure m) = hsNormSq m f ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  unfold hsMeasure hsNormSq
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_ofReal_hsWeight m)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two]

private theorem hsNormSq_eq_eLpNorm (m : ℕ) (f : Space → CSpace) :
    hsNormSq m f = eLpNorm f 2 (hsMeasure m) ^ 2 := by
  rw [eLpNorm_hsMeasure, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem eLpNorm_le_sqrt (m : ℕ) {f : Space → CSpace} {X : ℝ}
    (h : hsNormSq m f ≤ ENNReal.ofReal X) :
    eLpNorm f 2 (hsMeasure m) ≤ ENNReal.ofReal (Real.sqrt X) := by
  rw [eLpNorm_hsMeasure]
  rcases le_or_gt X 0 with hX | hX
  · rw [ENNReal.ofReal_of_nonpos hX] at h
    rw [nonpos_iff_eq_zero.mp h, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  · calc hsNormSq m f ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt X) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hX.le (by norm_num), Real.sqrt_eq_rpow]

private theorem memLp_hsMeasure (m : ℕ) {f : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (h : hsNormSq m f < ⊤) :
    MemLp f 2 (hsMeasure m) := by
  refine ⟨AEStronglyMeasurable.mono_ac (hsMeasure_ac m) hf, ?_⟩
  rw [eLpNorm_hsMeasure]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

private theorem eLpNorm_Lp_hsMeasure (m : ℕ) (u : Lp CSpace 2 (hsMeasure m)) :
    eLpNorm u 2 (hsMeasure m) = ENNReal.ofReal ‖u‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]

private theorem hsNormSq_comp_neg (m : ℕ) (f : Space → CSpace) :
    hsNormSq m (fun ξ => f (-ξ)) = hsNormSq m f := by
  unfold hsNormSq
  have hw : ∀ ξ : Space, hsWeight m (-ξ) = hsWeight m ξ := fun ξ => by simp [hsWeight]
  calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖f (-ξ)‖ₑ ^ 2
      = ∫⁻ ξ, ENNReal.ofReal (hsWeight m (-ξ)) * ‖f (-ξ)‖ₑ ^ 2 := by simp_rw [hw]
    _ = _ := lintegral_neg_eq_self (fun ξ => ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2)

private theorem enorm_conjVec_eq (z : CSpace) : ‖conjVec z‖ₑ = ‖z‖ₑ := by
  have h : ‖conjVec z‖ = ‖z‖ := by
    simp [EuclideanSpace.norm_eq, conjVec]
  rw [← ofReal_norm, h, ofReal_norm]

private theorem hsNormSq_comp_conj (m : ℕ) (f : Space → CSpace) :
    hsNormSq m (fun ξ => conjVec (f ξ)) = hsNormSq m f := by
  simp only [hsNormSq, enorm_conjVec_eq]

theorem hsCurve_limit (m : ℕ) (a b B K : ℝ) (G : ℕ → ℝ → Space → CSpace)
    (hG : ∀ n, IsHsCurve m (G n) a b)
    (hB : ∀ n, ∀ t ∈ Icc a b, hsNormSq m (G n t) ≤ ENNReal.ofReal B)
    (hconj : ∀ n, ∀ t ∈ Icc a b, ∀ᵐ ξ ∂volume, G n t (-ξ) = conjVec (G n t ξ))
    (hstep : ∀ n, ∀ t ∈ Icc a b, hsNormSq m (G (n + 1) t - G n t) ≤ ENNReal.ofReal (K * (1 / 4) ^ n)) :
    ∃ L : ℝ → Space → CSpace, IsHsCurve m L a b ∧
      (∀ t ∈ Icc a b, hsNormSq m (L t) ≤ ENNReal.ofReal B) ∧
      (∀ t ∈ Icc a b, ∀ᵐ ξ ∂volume, L t (-ξ) = conjVec (L t ξ)) ∧
      Tendsto (fun n => ⨆ t ∈ Icc a b, hsNormSq m (G n t - L t)) atTop (𝓝 0) := by
  have hmem : ∀ n, ∀ t ∈ Icc a b, MemLp (G n t) 2 (hsMeasure m) := fun n t ht =>
    memLp_hsMeasure m ((hG n).1 t ht).1 ((hG n).1 t ht).2
  let Φ : ℕ → ℝ → Lp CSpace 2 (hsMeasure m) := fun n t =>
    if h : t ∈ Icc a b then (hmem n t h).toLp (G n t) else 0
  have hΦ : ∀ n, ∀ t ∈ Icc a b, (Φ n t : Space → CSpace) =ᵐ[hsMeasure m] G n t := by
    intro n t ht
    simp only [Φ, dif_pos ht]
    exact MemLp.coeFn_toLp _
  have hdistΦ : ∀ n k t s, t ∈ Icc a b → s ∈ Icc a b →
      dist (Φ n t) (Φ k s) = (eLpNorm (G n t - G k s) 2 (hsMeasure m)).toReal := by
    intro n k t s ht hs
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (Φ n t) (Φ k s), hΦ n t ht, hΦ k s hs] with ξ h1 h2 h3
    simp only [h1, Pi.sub_apply, h2, h3]
  have hstep' : ∀ n t, dist (Φ n t) (Φ (n + 1) t) ≤ 2 * Real.sqrt K / 2 / 2 ^ n := by
    intro n t
    by_cases ht : t ∈ Icc a b
    · rw [hdistΦ n (n + 1) t t ht ht, eLpNorm_sub_comm]
      have h1 := eLpNorm_le_sqrt m (hstep n t ht)
      have h2 : Real.sqrt (K * (1 / 4) ^ n) = 2 * Real.sqrt K / 2 / 2 ^ n := by
        rw [Real.sqrt_mul' _ (by positivity)]
        have h4 : ((1 : ℝ) / 4) ^ n = ((1 / 2) ^ n) ^ 2 := by
          rw [sq, ← mul_pow]
          norm_num
        rw [h4, Real.sqrt_sq (by positivity), div_pow, one_pow]
        ring
      rw [h2] at h1
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
    · simp only [Φ, dif_neg ht, dist_self]
      positivity
  have hcseq : ∀ t, CauchySeq (fun n => Φ n t) := fun t =>
    cauchySeq_of_le_geometric_two (fun n => hstep' n t)
  let Λ : ℝ → Lp CSpace 2 (hsMeasure m) := fun t => limUnder atTop (fun n => Φ n t)
  have hΛ : ∀ t, Tendsto (fun n => Φ n t) atTop (𝓝 (Λ t)) := fun t =>
    (hcseq t).tendsto_limUnder
  have hrate : ∀ n t, dist (Φ n t) (Λ t) ≤ 2 * Real.sqrt K / 2 ^ n := fun n t =>
    dist_le_of_le_geometric_two_of_tendsto (fun k => hstep' k t) (hΛ t) n
  have h0 : Tendsto (fun n : ℕ => 2 * Real.sqrt K / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hGL : ∀ n, ∀ t ∈ Icc a b, eLpNorm (G n t - (Λ t : Space → CSpace)) 2 (hsMeasure m) ≤
      ENNReal.ofReal (2 * Real.sqrt K / 2 ^ n) := by
    intro n t ht
    have h1 : eLpNorm (G n t - (Λ t : Space → CSpace)) 2 (hsMeasure m) =
        ENNReal.ofReal (dist (Φ n t) (Λ t)) := by
      rw [dist_eq_norm, ← eLpNorm_Lp_hsMeasure]
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub (Φ n t) (Λ t), hΦ n t ht] with ξ h1 h2
      simp only [h1, Pi.sub_apply, h2]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hrate n t)
  have hHsL : ∀ t s, hsNormSq m ((Λ t : Space → CSpace) - Λ s) =
      ENNReal.ofReal (dist (Λ t) (Λ s)) ^ 2 := by
    intro t s
    rw [hsNormSq_eq_eLpNorm, dist_eq_norm, ← eLpNorm_Lp_hsMeasure]
    congr 1
    exact eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
  have hcontΦ : ∀ n, ContinuousOn (Φ n) (Icc a b) := by
    intro n t₀ ht₀
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun t => (hsNormSq m (G n t - G n t₀) ^ (1 / 2 : ℝ)).toReal)
        (𝓝[Icc a b] t₀) (𝓝 0) := by
      have h3 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp ((hG n).2 t₀ ht₀)
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
      rw [ENNReal.toReal_zero] at h2
      exact h2
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hdistΦ n n t t₀ ht ht₀, eLpNorm_hsMeasure]
  have hunif : TendstoUniformlyOn Φ Λ atTop (Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h0 (Iio_mem_nhds hε)] with n hn t _
    rw [dist_comm]
    exact (hrate n t).trans_lt hn
  have hcontΛ : ContinuousOn Λ (Icc a b) :=
    hunif.continuousOn (Frequently.of_forall hcontΦ)
  refine ⟨fun t => (Λ t : Space → CSpace), ⟨fun t _ => ⟨?_, ?_⟩, fun t₀ ht₀ => ?_⟩, ?_, ?_, ?_⟩
  · exact (Lp.stronglyMeasurable _).aestronglyMeasurable
  · rw [hsNormSq_eq_eLpNorm, eLpNorm_Lp_hsMeasure]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  · have h1 := hcontΛ t₀ ht₀
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero] at h1
    have h2 : Tendsto (fun t => ENNReal.ofReal (dist (Λ t) (Λ t₀))) (𝓝[Icc a b] t₀) (𝓝 0) := by
      have h3 := ENNReal.tendsto_ofReal h1
      rwa [ENNReal.ofReal_zero] at h3
    have h3 := ((ENNReal.continuous_pow 2).tendsto' 0 0 (by simp)).comp h2
    refine h3.congr' (Eventually.of_forall fun t => ?_)
    exact (hHsL t t₀).symm
  · intro t ht
    have hn : ∀ n, ‖Φ n t‖ ≤ Real.sqrt B := by
      intro n
      have h1 : ‖Φ n t‖ = (eLpNorm (G n t) 2 (hsMeasure m)).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae (hΦ n t ht)]
      rw [h1]
      exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (eLpNorm_le_sqrt m (hB n t ht))
    have hlim : ‖Λ t‖ ≤ Real.sqrt B :=
      le_of_tendsto' ((continuous_norm.tendsto _).comp (hΛ t)) hn
    show hsNormSq m (Λ t : Space → CSpace) ≤ ENNReal.ofReal B
    rw [hsNormSq_eq_eLpNorm, eLpNorm_Lp_hsMeasure, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rcases le_or_gt 0 B with hB0 | hB0
    · apply ENNReal.ofReal_le_ofReal
      calc ‖Λ t‖ ^ 2 ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlim 2
        _ = B := Real.sq_sqrt hB0
    · rw [Real.sqrt_eq_zero_of_nonpos hB0.le] at hlim
      have h1 : ‖Λ t‖ = 0 := le_antisymm hlim (norm_nonneg _)
      simp [h1]
  · intro t ht
    show ∀ᵐ ξ ∂volume, (Λ t : Space → CSpace) (-ξ) = conjVec ((Λ t : Space → CSpace) ξ)
    have hLm : StronglyMeasurable (Λ t : Space → CSpace) := Lp.stronglyMeasurable _
    have hmeas : AEStronglyMeasurable
        (fun ξ => (Λ t : Space → CSpace) (-ξ) - conjVec ((Λ t : Space → CSpace) ξ))
        (hsMeasure m) :=
      ((hLm.comp_measurable measurable_neg).sub
        (conjVec.continuous.comp_stronglyMeasurable hLm)).aestronglyMeasurable
    have hbound : ∀ n, eLpNorm
        (fun ξ => (Λ t : Space → CSpace) (-ξ) - conjVec ((Λ t : Space → CSpace) ξ)) 2
        (hsMeasure m) ≤ 2 * ENNReal.ofReal (2 * Real.sqrt K / 2 ^ n) := by
      intro n
      set D : Space → CSpace := G n t - (Λ t : Space → CSpace) with hD
      have hDv : AEStronglyMeasurable D volume :=
        ((hG n).1 t ht).1.sub (Lp.stronglyMeasurable _).aestronglyMeasurable
      have hDneg : AEStronglyMeasurable (fun ξ => D (-ξ)) (hsMeasure m) :=
        AEStronglyMeasurable.mono_ac (hsMeasure_ac m)
          (hDv.comp_measurePreserving (Measure.measurePreserving_neg volume))
      have hDconj : AEStronglyMeasurable (fun ξ => conjVec (D ξ)) (hsMeasure m) :=
        conjVec.continuous.comp_aestronglyMeasurable
          (AEStronglyMeasurable.mono_ac (hsMeasure_ac m) hDv)
      have hae : (fun ξ => (Λ t : Space → CSpace) (-ξ) - conjVec ((Λ t : Space → CSpace) ξ))
          =ᵐ[hsMeasure m] -((fun ξ => D (-ξ)) - (fun ξ => conjVec (D ξ))) := by
        filter_upwards [(hsMeasure_ac m).ae_le (hconj n t ht)] with ξ hξ
        simp only [hD, Pi.neg_apply, Pi.sub_apply, map_sub, hξ]
        abel
      rw [eLpNorm_congr_ae hae, eLpNorm_neg]
      calc eLpNorm ((fun ξ => D (-ξ)) - (fun ξ => conjVec (D ξ))) 2 (hsMeasure m)
          ≤ eLpNorm (fun ξ => D (-ξ)) 2 (hsMeasure m) +
              eLpNorm (fun ξ => conjVec (D ξ)) 2 (hsMeasure m) :=
            eLpNorm_sub_le hDneg hDconj (by norm_num)
        _ = 2 * eLpNorm D 2 (hsMeasure m) := by
            rw [eLpNorm_hsMeasure, eLpNorm_hsMeasure, eLpNorm_hsMeasure, hsNormSq_comp_neg,
              hsNormSq_comp_conj, two_mul]
        _ ≤ 2 * ENNReal.ofReal (2 * Real.sqrt K / 2 ^ n) := by
            gcongr
            exact hGL n t ht
    have hlim : Tendsto (fun n : ℕ => 2 * ENNReal.ofReal (2 * Real.sqrt K / 2 ^ n)) atTop (𝓝 0) := by
      have h2 := ENNReal.tendsto_ofReal h0
      rw [ENNReal.ofReal_zero] at h2
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      rwa [mul_zero] at h3
    have hzero := le_antisymm (ge_of_tendsto' hlim hbound) (zero_le)
    have hae0 := (volume_ac_hsMeasure m).ae_le ((eLpNorm_eq_zero_iff hmeas (by norm_num)).mp hzero)
    filter_upwards [hae0] with ξ hξ
    exact sub_eq_zero.mp hξ
  · have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * Real.sqrt K / 2 ^ n) ^ 2) atTop (𝓝 0) := by
      have h2 := ENNReal.tendsto_ofReal h0
      rw [ENNReal.ofReal_zero] at h2
      exact ((ENNReal.continuous_pow 2).tendsto' 0 0 (by simp)).comp h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => zero_le)
      (fun n => ?_)
    refine iSup₂_le fun t ht => ?_
    rw [hsNormSq_eq_eLpNorm]
    exact pow_le_pow_left₀ (zero_le) (hGL n t ht) 2

end Breakdown.SmoothFlow
