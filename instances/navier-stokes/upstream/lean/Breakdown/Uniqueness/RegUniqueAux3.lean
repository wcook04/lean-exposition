import Breakdown.Uniqueness.RegUniqueAux2
import Breakdown.Uniqueness.RegUniqueAux4

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem enorm_divFreeC_le (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ₑ ≤ 2 * ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  calc ENNReal.ofReal ‖divFreeC ξ z‖ ≤ ENNReal.ofReal (2 * ‖z‖) :=
        ENNReal.ofReal_le_ofReal (norm_divFreeC_le ξ z)
    _ = 2 * ENNReal.ofReal ‖z‖ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp

theorem convMass_lt_top {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hf3 : hsNormSq 3 f < ⊤) (hg3 : hsNormSq 3 g < ⊤)
    (ξ : Space) : convMass f g ξ < ⊤ := by
  refine lt_of_le_of_lt (convMass_le_hs hf hg ξ) ?_
  refine ENNReal.mul_lt_top ?_ ?_
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt (hsNormSq_zero_le_three f) hf3).ne
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt (homNormSq_one_le_three g) hg3).ne

theorem hsNormSq_sub_le (m : ℕ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    hsNormSq m (f - g) ≤ 2 * (hsNormSq m f + hsNormSq m g) := by
  have hneg : hsNormSq m (-g) = hsNormSq m g := by simp [hsNormSq]
  rw [sub_eq_add_neg, ← hneg]
  exact hsNormSq_add_le_two_mul m hf

theorem enorm_nonlinSymbol_sub_le {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hf3 : hsNormSq 3 f < ⊤) (hg3 : hsNormSq 3 g < ⊤)
    (ξ : Space) :
    ‖nonlinSymbol f ξ - nonlinSymbol g ξ‖ₑ ≤
      ENNReal.ofReal (36 * π) * (convMass (f - g) f ξ + convMass g (f - g) ξ) := by
  have e1 : advectionBilin (f - g) f ξ = advectionBilin f f ξ - advectionBilin g f ξ :=
    advectionBilin_sub_left hf hg hf ξ (convMass_lt_top hf hf hf3 hf3 ξ)
      (convMass_lt_top hg hf hg3 hf3 ξ)
  have e2 : advectionBilin g (f - g) ξ = advectionBilin g f ξ - advectionBilin g g ξ :=
    advectionBilin_sub_right hg hf hg ξ (convMass_lt_top hg hf hg3 hf3 ξ)
      (convMass_lt_top hg hg hg3 hg3 ξ)
  have key : nonlinSymbol f ξ - nonlinSymbol g ξ =
      -divFreeC ξ (advectionBilin (f - g) f ξ + advectionBilin g (f - g) ξ) := by
    rw [e1, e2, show advectionBilin f f ξ - advectionBilin g f ξ +
      (advectionBilin g f ξ - advectionBilin g g ξ) = advectionBilin f f ξ - advectionBilin g g ξ by
        abel, ← divFreeC_sub]
    simp only [nonlinSymbol, advectionSymbol]
    abel
  rw [key, enorm_neg]
  calc ‖divFreeC ξ (advectionBilin (f - g) f ξ + advectionBilin g (f - g) ξ)‖ₑ
      ≤ 2 * ‖advectionBilin (f - g) f ξ + advectionBilin g (f - g) ξ‖ₑ := enorm_divFreeC_le _ _
    _ ≤ 2 * (‖advectionBilin (f - g) f ξ‖ₑ + ‖advectionBilin g (f - g) ξ‖ₑ) := by
        gcongr; exact enorm_add_le _ _
    _ ≤ 2 * (ENNReal.ofReal (18 * π) * convMass (f - g) f ξ +
          ENNReal.ofReal (18 * π) * convMass g (f - g) ξ) := by
        gcongr <;> exact enorm_advectionBilin_le _ _ _
    _ = ENNReal.ofReal (36 * π) * (convMass (f - g) f ξ + convMass g (f - g) ξ) := by
        rw [← mul_add, ← mul_assoc]
        congr 1
        rw [show (36 * π) = 2 * (18 * π) by ring, ENNReal.ofReal_mul (by norm_num)]
        simp

theorem continuousOn_nonlinSymbol {F : ℝ → Space → CSpace} {a b : ℝ} (hF : IsHsCurve 3 F a b)
    (ξ : Space) : ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc a b) := by
  obtain ⟨C, hC, hCb⟩ := hsCurve_bound hF
  intro s₀ hs₀
  have hm : ∀ t ∈ Icc a b, AEStronglyMeasurable (F t) volume := fun t ht => (hF.1 t ht).1
  have hfin : ∀ t ∈ Icc a b, hsNormSq 3 (F t) < ⊤ := fun t ht => (hF.1 t ht).2
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  have hlim : Tendsto (fun t => ENNReal.ofReal (36 * π) *
      (hsNormSq 3 (F t - F s₀) ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) +
        C ^ (1 / 2 : ℝ) * hsNormSq 3 (F t - F s₀) ^ (1 / 2 : ℝ))) (𝓝[Icc a b] s₀) (𝓝 0) := by
    have h0 : Tendsto (fun t => hsNormSq 3 (F t - F s₀) ^ (1 / 2 : ℝ)) (𝓝[Icc a b] s₀) (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this.comp (hF.2 s₀ hs₀)
    have hCt : C ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC
    have h1 := ENNReal.Tendsto.mul_const h0 (Or.inr hCt)
    have h2 := ENNReal.Tendsto.const_mul h0 (Or.inr hCt)
    rw [zero_mul] at h1
    rw [mul_zero] at h2
    have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (36 * π)) (h1.add h2)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [edist_eq_enorm_sub]
  refine (enorm_nonlinSymbol_sub_le (hm t ht) (hm s₀ hs₀) (hfin t ht) (hfin s₀ hs₀) ξ).trans ?_
  gcongr
  · refine (convMass_le_hs ((hm t ht).sub (hm s₀ hs₀)) (hm t ht) ξ).trans ?_
    gcongr
    · exact hsNormSq_zero_le_three _
    · exact (homNormSq_one_le_three _).trans (hCb t ht)
  · refine (convMass_le_hs (hm s₀ hs₀) ((hm t ht).sub (hm s₀ hs₀)) ξ).trans ?_
    gcongr
    · exact (hsNormSq_zero_le_three _).trans (hCb s₀ hs₀)
    · exact homNormSq_one_le_three _

theorem varConst_sub_eq {F G : ℝ → Space → CSpace} {a b : ℝ} (hF : IsHsCurve 3 F a b)
    (hG : IsHsCurve 3 G a b) (hFd : IsVarConstSymbol F a b) (hGd : IsVarConstSymbol G a b)
    (h : F a = G a) {t : ℝ} (ht : t ∈ Icc a b) (ξ : Space) :
    F t ξ - G t ξ = ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) •
      (nonlinSymbol (F s) ξ - nonlinSymbol (G s) ξ) := by
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hc : ∀ H : ℝ → Space → CSpace, IsHsCurve 3 H a b →
      IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (H s) ξ)
        volume a t := by
    intro H hH
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.smul (f := fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ)) ?_
      ((continuousOn_nonlinSymbol hH ξ).mono hsub)
    exact (Complex.continuous_ofReal.comp (continuous_heatSymbol_sub t ξ)).continuousOn
  rw [hFd t ht ξ, hGd t ht ξ, h]
  simp only [smul_sub]
  rw [intervalIntegral.integral_sub (hc F hF) (hc G hG)]
  abel

theorem heat_varConst_bound {φ : ℝ → CSpace} {a b T t M : ℝ} (ξ : Space)
    (hφ : ContinuousOn φ (Icc a b)) (haT : a ≤ T) (hTt : T ≤ t) (htb : t ≤ b)
    (h0 : ∀ r ∈ Icc a T, φ r = 0) (hM : ∀ r ∈ Icc T t, ‖φ r‖ ≤ M) :
    (1 + ‖ξ‖) * ‖∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s‖ ≤
      M * ((t - T) + Real.sqrt (t - T)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM T ⟨le_rfl, hTt⟩)
  have hcont : ContinuousOn (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s) (Icc a b) :=
    ((Complex.continuous_ofReal.comp (continuous_heatSymbol_sub t ξ)).continuousOn).smul hφ
  have hi : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s) volume u v := by
    intro u v hu huv hv
    refine (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le huv]
    exact Icc_subset_Icc hu hv
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a T le_rfl haT (hTt.trans htb))
    (hi T t haT hTt htb)]
  have hz : ∫ s in a..T, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : CSpace))]
    · simp
    · intro r hr
      rw [uIcc_of_le haT] at hr
      simp [h0 r hr]
  rw [hz, zero_add]
  have hn : ‖∫ s in T..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s‖ ≤
      ∫ s in T..t, heatSymbol (t - s) ξ * M := by
    refine (intervalIntegral.norm_integral_le_integral_norm hTt).trans ?_
    refine intervalIntegral.integral_mono_on hTt ?_ ?_ ?_
    · exact (hi T t haT hTt htb).norm
    · exact ((continuous_heatSymbol_sub t ξ).mul continuous_const).intervalIntegrable _ _
    · intro r hr
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (hM r hr) (heatSymbol_nonneg _ _)
  rw [intervalIntegral.integral_mul_const] at hn
  calc (1 + ‖ξ‖) * ‖∫ s in T..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • φ s‖
      ≤ (1 + ‖ξ‖) * ((∫ s in T..t, heatSymbol (t - s) ξ) * M) := by gcongr
    _ = M * ((1 + ‖ξ‖) * ∫ s in T..t, heatSymbol (t - s) ξ) := by ring
    _ ≤ M * ((t - T) + Real.sqrt (t - T)) := by
        gcongr
        exact heatSymbol_integral_le hTt ξ

theorem norm_nonlinSymbol_sub_le_of_bound {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf3 : hsNormSq 3 f < ⊤) (hg3 : hsNormSq 3 g < ⊤) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hgw : gradFreqL1Norm f ≤ ENNReal.ofReal K) (hw : freqL1Norm g ≤ ENNReal.ofReal K)
    (hd : ∀ η, (1 + ‖η‖) * ‖f η - g η‖ ≤ B) (ξ : Space) :
    ‖nonlinSymbol f ξ - nonlinSymbol g ξ‖ ≤ 72 * π * K * B := by
  have hd1 : ∀ η, ‖(f - g) η‖ₑ ≤ ENNReal.ofReal B := by
    intro η
    rw [← ofReal_norm, Pi.sub_apply]
    refine ENNReal.ofReal_le_ofReal ((le_mul_of_one_le_left (norm_nonneg _) ?_).trans (hd η))
    linarith [norm_nonneg η]
  have hd2 : ∀ ζ, ‖ζ‖ₑ * ‖(f - g) ζ‖ₑ ≤ ENNReal.ofReal B := by
    intro ζ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      Pi.sub_apply]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans (hd ζ))
    linarith
  have h := enorm_nonlinSymbol_sub_le hf hg hf3 hg3 ξ
  have hA := convMass_le_left (g := f) ENNReal.ofReal_ne_top hd1 ξ
  have hB' := convMass_le_right (f := g) ENNReal.ofReal_ne_top hd2 ξ
  have htot : ‖nonlinSymbol f ξ - nonlinSymbol g ξ‖ₑ ≤ ENNReal.ofReal (72 * π * K * B) := by
    refine h.trans ?_
    calc ENNReal.ofReal (36 * π) * (convMass (f - g) f ξ + convMass g (f - g) ξ)
        ≤ ENNReal.ofReal (36 * π) * (ENNReal.ofReal B * ENNReal.ofReal K +
            ENNReal.ofReal B * ENNReal.ofReal K) := by
          gcongr
          · exact hA.trans (by gcongr)
          · exact hB'.trans (by gcongr)
      _ = ENNReal.ofReal (72 * π * K * B) := by
          rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  rw [← ofReal_norm] at htot
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htot

theorem enorm_nonlinSymbol_sub_le_const {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hfC : hsNormSq 3 f ≤ C) (hgC : hsNormSq 3 g ≤ C) (ξ : Space) :
    ‖nonlinSymbol f ξ - nonlinSymbol g ξ‖ₑ ≤ ENNReal.ofReal (36 * π) *
      ((2 * (C + C)) ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) + C ^ (1 / 2 : ℝ) * (2 * (C + C)) ^ (1 / 2 : ℝ)) := by
  have hf3 : hsNormSq 3 f < ⊤ := lt_of_le_of_lt hfC hC.lt_top
  have hg3 : hsNormSq 3 g < ⊤ := lt_of_le_of_lt hgC hC.lt_top
  have hd : hsNormSq 3 (f - g) ≤ 2 * (C + C) := (hsNormSq_sub_le 3 hf).trans (by gcongr)
  refine (enorm_nonlinSymbol_sub_le hf hg hf3 hg3 ξ).trans ?_
  gcongr
  · refine (convMass_le_hs (hf.sub hg) hf ξ).trans ?_
    gcongr
    · exact (hsNormSq_zero_le_three _).trans hd
    · exact (homNormSq_one_le_three _).trans hfC
  · refine (convMass_le_hs hg (hf.sub hg) ξ).trans ?_
    gcongr
    · exact (hsNormSq_zero_le_three _).trans hgC
    · exact (homNormSq_one_le_three _).trans hd

end Breakdown.SmoothFlow
