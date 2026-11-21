import Breakdown.Uniqueness.RegCurveAuxMeasure

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

theorem measurable_weight (k : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ k)) := by
  fun_prop

theorem weight_ne_zero (k : ℕ) (ξ : Space) : ENNReal.ofReal ((1 + ‖ξ‖) ^ k) ≠ 0 := by
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem lintegral_weighted (k : ℕ) (g : Space → ℝ≥0∞) :
    ∫⁻ ξ, g ξ ∂weightedVolume k = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * g ξ :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_weight k)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g

theorem ac_weighted (k k' : ℕ) : weightedVolume k ≪ weightedVolume k' :=
  (withDensity_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous' (measurable_weight k').aemeasurable
      (Eventually.of_forall (weight_ne_zero k')))

theorem memLp_mult (k k' : ℕ) (Φ : Space → CSpace → CSpace)
    (hΦm : Measurable (Function.uncurry Φ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ ξ z, (1 + ‖ξ‖) ^ k * ‖Φ ξ z‖ ≤ C * ((1 + ‖ξ‖) ^ k' * ‖z‖))
    {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume k')) :
    MemLp (fun ξ => Φ ξ (f ξ)) 1 (weightedVolume k) ∧
      eLpNorm (fun ξ => Φ ξ (f ξ)) 1 (weightedVolume k) ≤
        ENNReal.ofReal C * eLpNorm f 1 (weightedVolume k') := by
  have hfm : AEStronglyMeasurable f (weightedVolume k) := hf.1.mono_ac (ac_weighted k k')
  have hgm : AEStronglyMeasurable (fun ξ => Φ ξ (f ξ)) (weightedVolume k) := by
    refine (hΦm.comp (measurable_id.prodMk hfm.measurable_mk)).aestronglyMeasurable.congr ?_
    filter_upwards [hfm.ae_eq_mk] with ξ hξ
    simp [Function.uncurry, hξ]
  have hle : eLpNorm (fun ξ => Φ ξ (f ξ)) 1 (weightedVolume k) ≤
      ENNReal.ofReal C * eLpNorm f 1 (weightedVolume k') := by
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm, lintegral_weighted,
      lintegral_weighted, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ => ?_
    calc ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖Φ ξ (f ξ)‖ₑ
        = ENNReal.ofReal ((1 + ‖ξ‖) ^ k * ‖Φ ξ (f ξ)‖) := by
          rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
      _ ≤ ENNReal.ofReal (C * ((1 + ‖ξ‖) ^ k' * ‖f ξ‖)) := ENNReal.ofReal_le_ofReal (hb ξ (f ξ))
      _ = ENNReal.ofReal C * (ENNReal.ofReal ((1 + ‖ξ‖) ^ k') * ‖f ξ‖ₑ) := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (by positivity), ofReal_norm]
  exact ⟨⟨hgm, lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩, hle⟩

theorem exists_clm_mult (k k' : ℕ) (Φ : Space → CSpace → CSpace)
    (hΦm : Measurable (Function.uncurry Φ))
    (hadd : ∀ ξ z w, Φ ξ (z + w) = Φ ξ z + Φ ξ w)
    (hsmul : ∀ ξ (c : ℝ) z, Φ ξ (c • z) = c • Φ ξ z) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ ξ z, (1 + ‖ξ‖) ^ k * ‖Φ ξ z‖ ≤ C * ((1 + ‖ξ‖) ^ k' * ‖z‖)) :
    ∃ L : Lp CSpace 1 (weightedVolume k') →L[ℝ] Lp CSpace 1 (weightedVolume k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightedVolume k')),
        ∃ hg : MemLp (fun ξ => Φ ξ (f ξ)) 1 (weightedVolume k),
          L (hf.toLp f) = hg.toLp _ := by
  have H := fun (u : Lp CSpace 1 (weightedVolume k')) =>
    memLp_mult k k' Φ hΦm C hC hb (Lp.memLp u)
  let T : Lp CSpace 1 (weightedVolume k') →ₗ[ℝ] Lp CSpace 1 (weightedVolume k) :=
    { toFun := fun u => (H u).1.toLp _
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [(ac_weighted k k').ae_le (Lp.coeFn_add u v)] with ξ hξ
        simp only [Pi.add_apply]
        rw [hξ, Pi.add_apply, hadd]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [(ac_weighted k k').ae_le (Lp.coeFn_smul c u)] with ξ hξ
        simp [hξ, hsmul] }
  refine ⟨T.mkContinuous C fun u => ?_, fun f hf => ⟨(memLp_mult k k' Φ hΦm C hC hb hf).1, ?_⟩⟩
  · change ‖(H u).1.toLp _‖ ≤ C * ‖u‖
    rw [Lp.norm_toLp, Lp.norm_def]
    calc (eLpNorm (fun ξ => Φ ξ (u ξ)) 1 (weightedVolume k)).toReal
        ≤ (ENNReal.ofReal C * eLpNorm u 1 (weightedVolume k')).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u))
            (H u).2
      _ = C * (eLpNorm u 1 (weightedVolume k')).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  · change (H _).1.toLp _ = _
    apply MemLp.toLp_congr
    filter_upwards [(ac_weighted k k').ae_le (MemLp.coeFn_toLp hf)] with ξ hξ
    simp [hξ]

theorem norm_dot_le (ξ : Space) (z : CSpace) :
    ‖∑ i, ((ξ i : ℝ) : ℂ) * z i‖ ≤ 3 * ‖ξ‖ * ‖z‖ := by
  calc ‖∑ i, ((ξ i : ℝ) : ℂ) * z i‖ ≤ ∑ i, ‖((ξ i : ℝ) : ℂ) * z i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖ξ‖ * ‖z‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (PiLp.norm_apply_le ξ i) (PiLp.norm_apply_le z i) (norm_nonneg _)
          (norm_nonneg _)
    _ = 3 * ‖ξ‖ * ‖z‖ := by simp; ring

theorem norm_freqVec_le (ξ : Space) : ‖freqVec ξ‖ ≤ ‖complexifyVec‖ * ‖ξ‖ :=
  complexifyVec.le_opNorm ξ

theorem norm_divFreeC_le (ξ : Space) (z : CSpace) :
    ‖divFreeC ξ z‖ ≤ (1 + 3 * ‖complexifyVec‖) * ‖z‖ := by
  have hS := norm_dot_le ξ z
  have hv := norm_freqVec_le ξ
  have ha : 0 ≤ ‖complexifyVec‖ := norm_nonneg _
  have hinv : (‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2 ≤ 1 := by
    rcases eq_or_ne ‖ξ‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ (by positivity)]
  calc ‖divFreeC ξ z‖
      ≤ ‖z‖ + ‖(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i‖ * ‖freqVec ξ‖ := by
        unfold divFreeC
        exact (norm_sub_le _ _).trans (by rw [norm_smul])
    _ ≤ ‖z‖ + ((‖ξ‖ ^ 2)⁻¹ * (3 * ‖ξ‖ * ‖z‖)) * (‖complexifyVec‖ * ‖ξ‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        gcongr
    _ = ‖z‖ + 3 * ‖complexifyVec‖ * ((‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2) * ‖z‖ := by ring
    _ ≤ ‖z‖ + 3 * ‖complexifyVec‖ * 1 * ‖z‖ := by gcongr
    _ = (1 + 3 * ‖complexifyVec‖) * ‖z‖ := by ring

theorem norm_pressure_le (ξ : Space) (z : CSpace) :
    ‖(-(∑ i, ((ξ i : ℝ) : ℂ) * z i) /
        (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))) • freqVec ξ‖ ≤
      (3 * ‖complexifyVec‖ / (2 * π)) * ‖z‖ := by
  have hS := norm_dot_le ξ z
  have hv := norm_freqVec_le ξ
  have ha : 0 ≤ ‖complexifyVec‖ := norm_nonneg _
  rw [norm_smul]
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · have : ‖freqVec ξ‖ = 0 := le_antisymm (by simpa [h] using hv) (norm_nonneg _)
    rw [this, mul_zero]
    positivity
  · have hξ : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    have hD : ‖2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ)‖ = 2 * π * ‖ξ‖ ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg pi_pos.le, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 2)]
      norm_num
    rw [norm_div, norm_neg, hD]
    calc ‖∑ i, ((ξ i : ℝ) : ℂ) * z i‖ / (2 * π * ‖ξ‖ ^ 2) * ‖freqVec ξ‖
        ≤ (3 * ‖ξ‖ * ‖z‖) / (2 * π * ‖ξ‖ ^ 2) * (‖complexifyVec‖ * ‖ξ‖) := by gcongr
      _ = (3 * ‖complexifyVec‖ / (2 * π)) * ‖z‖ := by
        field_simp

end Internal

open Internal

theorem exists_clm_mulNormSq (k : ℕ) :
    ∃ L : Lp CSpace 1 (weightedVolume (k + 2)) →L[ℝ] Lp CSpace 1 (weightedVolume k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightedVolume (k + 2))),
        ∃ hg : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ) 1 (weightedVolume k),
          L (hf.toLp f) = hg.toLp _ := by
  refine exists_clm_mult k (k + 2) (fun ξ z => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • z) ?_
    (fun ξ z w => smul_add _ z w) (fun ξ c z => smul_comm _ c z) (4 * π ^ 2) (by positivity) ?_
  · change Measurable fun p : Space × CSpace => -(((4 * π ^ 2 * ‖p.1‖ ^ 2 : ℝ)) : ℂ) • p.2
    exact (by fun_prop : Continuous fun p : Space × CSpace =>
      -(((4 * π ^ 2 * ‖p.1‖ ^ 2 : ℝ)) : ℂ) • p.2).measurable
  · intro ξ z
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity), pow_add]
    have h0 : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by
      gcongr
      linarith [norm_nonneg ξ]
    calc (1 + ‖ξ‖) ^ k * (4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖z‖)
        = 4 * π ^ 2 * ((1 + ‖ξ‖) ^ k * ‖ξ‖ ^ 2 * ‖z‖) := by ring
      _ ≤ 4 * π ^ 2 * ((1 + ‖ξ‖) ^ k * (1 + ‖ξ‖) ^ 2 * ‖z‖) := by gcongr

theorem exists_clm_divFree (k : ℕ) :
    ∃ L : Lp CSpace 1 (weightedVolume k) →L[ℝ] Lp CSpace 1 (weightedVolume k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightedVolume k)),
        ∃ hg : MemLp (fun ξ => -divFreeC ξ (f ξ)) 1 (weightedVolume k),
          L (hf.toLp f) = hg.toLp _ := by
  refine exists_clm_mult k k (fun ξ z => -divFreeC ξ z) ?_ ?_ ?_ (1 + 3 * ‖complexifyVec‖)
    (by positivity) ?_
  · change Measurable fun p : Space × CSpace => -divFreeC p.1 p.2
    have hq : Measurable freqVec := complexifyVec.continuous.measurable
    unfold divFreeC
    fun_prop
  · intro ξ z w
    ext i
    simp [divFreeC, Fin.sum_univ_three]
    ring
  · intro ξ c z
    ext i
    simp [divFreeC, Fin.sum_univ_three, Complex.real_smul]
    ring
  · intro ξ z
    rw [norm_neg]
    calc (1 + ‖ξ‖) ^ k * ‖divFreeC ξ z‖ ≤ (1 + ‖ξ‖) ^ k * ((1 + 3 * ‖complexifyVec‖) * ‖z‖) := by
          gcongr
          exact norm_divFreeC_le ξ z
      _ = (1 + 3 * ‖complexifyVec‖) * ((1 + ‖ξ‖) ^ k * ‖z‖) := by ring

theorem exists_clm_pressureProj (k : ℕ) :
    ∃ L : Lp CSpace 1 (weightedVolume k) →L[ℝ] Lp CSpace 1 (weightedVolume k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightedVolume k)),
        ∃ hg : MemLp (fun ξ => (-(∑ i, ((ξ i : ℝ) : ℂ) * f ξ i) /
            (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))) • freqVec ξ) 1 (weightedVolume k),
          L (hf.toLp f) = hg.toLp _ := by
  refine exists_clm_mult k k (fun ξ z => (-(∑ i, ((ξ i : ℝ) : ℂ) * z i) /
      (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))) • freqVec ξ) ?_ ?_ ?_
    (3 * ‖complexifyVec‖ / (2 * π)) (by positivity) ?_
  · change Measurable fun p : Space × CSpace => (-(∑ i, ((p.1 i : ℝ) : ℂ) * p.2 i) /
      (2 * (π : ℂ) * Complex.I * (((‖p.1‖ ^ 2 : ℝ)) : ℂ))) • freqVec p.1
    have hq : Measurable freqVec := complexifyVec.continuous.measurable
    fun_prop
  · intro ξ z w
    ext i
    simp [Fin.sum_univ_three]
    ring
  · intro ξ c z
    ext i
    simp [Fin.sum_univ_three, Complex.real_smul]
    ring
  · intro ξ z
    calc (1 + ‖ξ‖) ^ k * ‖(-(∑ i, ((ξ i : ℝ) : ℂ) * z i) /
          (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))) • freqVec ξ‖
        ≤ (1 + ‖ξ‖) ^ k * ((3 * ‖complexifyVec‖ / (2 * π)) * ‖z‖) := by
          gcongr
          exact norm_pressure_le ξ z
      _ = (3 * ‖complexifyVec‖ / (2 * π)) * ((1 + ‖ξ‖) ^ k * ‖z‖) := by ring

end Breakdown.SmoothFlow
