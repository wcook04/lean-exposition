import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegAprioriAuxEnergyPart1
import Breakdown.Uniqueness.RegAprioriAuxEnergyPart2
import Breakdown.Uniqueness.RegPersistAuxMeas
import Breakdown.Uniqueness.RegAprioriAuxCont

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def dissipSq (α : ℝ) (f : Space → CSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * ‖f ξ‖ₑ ^ 2

private theorem quartic_le_sum {α : ℝ} (hα : 1 ≤ α) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 * 2) ≤ x ^ (2 * 1) + x ^ 2 * (2 * π * x) ^ (2 * α) := by
  have hw : 0 ≤ x ^ 2 * (2 * π * x) ^ (2 * α) := by positivity
  have h4 : x ^ (2 * 2) = x ^ 2 * x ^ 2 := by ring
  have h2 : x ^ (2 * 1) = x ^ 2 := by ring
  rw [h4, h2]
  rcases le_total x 1 with h | h
  · have hs : x ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
    linarith
  · have hpi := Real.pi_gt_three
    have h1 : 1 ≤ 2 * π * x := by nlinarith
    have hxy : x ^ 2 ≤ (2 * π * x) ^ (2 * α) := by
      calc x ^ 2 ≤ (2 * π * x) ^ 2 := pow_le_pow_left₀ hx (by nlinarith) 2
        _ = (2 * π * x) ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ ≤ (2 * π * x) ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have := mul_le_mul_of_nonneg_left hxy (sq_nonneg x)
    nlinarith [sq_nonneg x]

private theorem weight_le_hsWeight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) (ξ : Space) :
    ‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α) ≤ (1 + (2 * π) ^ 4) * hsWeight 3 ξ := by
  unfold hsWeight
  have hy0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have hy : (2 * π * ‖ξ‖) ^ (2 * α) ≤ 1 + (2 * π * ‖ξ‖) ^ 4 := by
    rcases le_total (2 * π * ‖ξ‖) 1 with h | h
    · have := Real.rpow_le_one hy0 h (by linarith : (0 : ℝ) ≤ 2 * α)
      have := pow_nonneg hy0 4
      linarith
    · have e : (2 * π * ‖ξ‖) ^ (4 : ℝ) = (2 * π * ‖ξ‖) ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have := Real.rpow_le_rpow_of_exponent_le h (by linarith : 2 * α ≤ 4)
      rw [e] at this
      linarith
  have hc : 0 ≤ (2 * π) ^ 4 := by positivity
  have hu := sq_nonneg ‖ξ‖
  have ha : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ 3 := by nlinarith [mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]
  have hb : (‖ξ‖ ^ 2) ^ 3 ≤ (1 + ‖ξ‖ ^ 2) ^ 3 := pow_le_pow_left₀ hu (by linarith) 3
  calc ‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α) ≤ ‖ξ‖ ^ 2 * (1 + (2 * π * ‖ξ‖) ^ 4) :=
        mul_le_mul_of_nonneg_left hy hu
    _ = ‖ξ‖ ^ 2 + (2 * π) ^ 4 * (‖ξ‖ ^ 2) ^ 3 := by ring
    _ ≤ (1 + (2 * π) ^ 4) * (1 + ‖ξ‖ ^ 2) ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hb hc]

private theorem ofReal_mul_rpow_three_quarters_le_self {a : ℝ} (ha : 0 ≤ a) (y : ℝ≥0∞) :
    ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤ y + ENNReal.ofReal (a ^ 4) := by
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ y = ENNReal.ofReal r :=
    ⟨y.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hy).symm⟩
  rw [ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_add hr (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq0 : 0 ≤ r ^ (1 / 4 : ℝ) := Real.rpow_nonneg hr _
  have hr3 : r ^ (3 / 4 : ℝ) = (r ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hr4 : r = (r ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  rw [hr3]
  conv_rhs => rw [hr4]
  rcases le_total (r ^ (1 / 4 : ℝ)) a with h | h
  · have h3 : (r ^ (1 / 4 : ℝ)) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hq0 h 3
    have := mul_le_mul_of_nonneg_left h3 ha
    have := pow_nonneg hq0 4
    nlinarith
  · have := mul_le_mul_of_nonneg_right h (pow_nonneg hq0 3)
    have := pow_nonneg ha 4
    nlinarith

theorem powerDissipation_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2)
    (h1 : PowerEnergyInequalityStatement α) (h2 : PowerAEMeasStatement α) :
    PowerDissipationStatement α := by
  intro m hm M T
  obtain ⟨C, hC⟩ := lintegral_weight_mul_nonlinSymbol_le
  obtain ⟨M', hM0, hMM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ M ≤ M' := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C', hC0, hCC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨a, ha, hadef⟩ : ∃ a : ℝ, 0 ≤ a ∧ a = 2 * C' * M' ^ (3 / 4 : ℝ) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨M' + (2 * M' + a ^ 4) * T, ?_⟩
  intro T' hT' F hF hd hs hM
  rcases eq_or_lt_of_le hT'.1 with h0 | hpos
  · have hz : volume.restrict (Icc (0 : ℝ) T') = 0 := by
      rw [← h0, Icc_self]; exact Measure.restrict_eq_zero.2 Real.volume_singleton
    rw [hz, lintegral_zero_measure]; exact bot_le
  have hT0 : (0 : ℝ) ∈ Icc 0 T' := ⟨le_rfl, hpos.le⟩
  have hF1 : IsHsCurve 1 F 0 T' := isHsCurve_of_le (by omega) hF
  have hF3 : IsHsCurve 3 F 0 T' := isHsCurve_of_le hm hF
  have hFm := h2 T' hpos F hF1 hd
  have hNm := aemeasurable_enorm_nonlinSymbol hF3 hs
  have hwm : Measurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α))) :=
    ((continuous_norm.measurable.pow_const 2).mul
      ((measurable_const.mul continuous_norm.measurable).pow_const (2 * α))).ennreal_ofReal
  have hw2 : Measurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ 2)) :=
    (continuous_norm.measurable.pow_const 2).ennreal_ofReal
  have hBA : ∀ s ∈ Icc 0 T', homNormSq 2 (F s) ≤ dissipSq α (F s) + ENNReal.ofReal M' := by
    intro s hs
    have hm1 : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖F s ξ‖ₑ ^ 2) volume :=
      (continuous_norm.measurable.pow_const _).ennreal_ofReal.aemeasurable.mul
        ((hF.1 s hs).1.enorm.pow_const 2)
    calc homNormSq 2 (F s) ≤ ∫⁻ ξ, (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖F s ξ‖ₑ ^ 2 +
          ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * ‖F s ξ‖ₑ ^ 2) := by
          refine lintegral_mono fun ξ => ?_
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (quartic_le_sum hα.le (norm_nonneg ξ))) le_rfl
      _ = homNormSq 1 (F s) + dissipSq α (F s) := lintegral_add_left' hm1 _
      _ ≤ ENNReal.ofReal M' + dissipSq α (F s) :=
          add_le_add ((hM s hs).trans (ENNReal.ofReal_le_ofReal hMM')) le_rfl
      _ = dissipSq α (F s) + ENNReal.ofReal M' := add_comm _ _
  obtain ⟨Bd, hBd⟩ := isCompact_Icc.bddAbove_image (continuousOn_hsNormSq_toReal hF)
  have hWle : ∀ s ∈ Icc 0 T', dissipSq α (F s) ≤
      ENNReal.ofReal (1 + (2 * π) ^ 4) * ENNReal.ofReal Bd := by
    intro s hs
    calc dissipSq α (F s) ≤ ∫⁻ ξ, ENNReal.ofReal (1 + (2 * π) ^ 4) *
          (ENNReal.ofReal (hsWeight m ξ) * ‖F s ξ‖ₑ ^ 2) := by
          refine lintegral_mono fun ξ => ?_
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          exact (weight_le_hsWeight (by linarith) (by linarith) ξ).trans
            (mul_le_mul_of_nonneg_left (hsWeight_le_of_le hm ξ) (by positivity))
      _ = ENNReal.ofReal (1 + (2 * π) ^ 4) * hsNormSq m (F s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          calc hsNormSq m (F s) = ENNReal.ofReal (hsNormSq m (F s)).toReal :=
                (ENNReal.ofReal_toReal (hF.1 s hs).2.ne).symm
            _ ≤ ENNReal.ofReal Bd := ENNReal.ofReal_le_ofReal (hBd ⟨s, hs, rfl⟩)
  have hWfin : ∫⁻ s in Icc 0 T', dissipSq α (F s) < ⊤ := by
    calc ∫⁻ s in Icc 0 T', dissipSq α (F s) ≤
          ∫⁻ s in Icc 0 T', ENNReal.ofReal (1 + (2 * π) ^ 4) * ENNReal.ofReal Bd :=
          setLIntegral_mono' measurableSet_Icc hWle
      _ = ENNReal.ofReal (1 + (2 * π) ^ 4) * ENNReal.ofReal Bd * volume (Icc (0 : ℝ) T') :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hI : (∫⁻ s in Icc 0 T', dissipSq α (F s)) =
      ∫⁻ ξ, ∫⁻ s in Icc 0 T', ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * ‖F s ξ‖ₑ ^ 2 := by
    unfold dissipSq
    exact lintegral_lintegral_swap
      (f := fun s ξ => ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * ‖F s ξ‖ₑ ^ 2)
      ((hwm.comp measurable_snd).aemeasurable.mul (hFm.pow_const 2))
  have hJ : ∫⁻ ξ, ∫⁻ s in Icc 0 T', ENNReal.ofReal (‖ξ‖ ^ 2) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) =
      ∫⁻ s in Icc 0 T', ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) :=
    (lintegral_lintegral_swap (f := fun s ξ => ENNReal.ofReal (‖ξ‖ ^ 2) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ))
      ((hw2.comp measurable_snd).aemeasurable.mul (hFm.mul hNm))).symm
  have hm0 : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F 0 ξ‖ₑ ^ 2) volume :=
    hw2.aemeasurable.mul ((hF.1 0 hT0).1.enorm.pow_const 2)
  have hA0 : homNormSq 1 (F 0) = ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F 0 ξ‖ₑ ^ 2 := rfl
  have h2ne : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hstep : 2 * ∫⁻ s in Icc 0 T', dissipSq α (F s) ≤
      homNormSq 1 (F 0) + ∫⁻ s in Icc 0 T', 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) := by
    calc 2 * ∫⁻ s in Icc 0 T', dissipSq α (F s)
        = ∫⁻ ξ, 2 * ∫⁻ s in Icc 0 T', ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) *
            ‖F s ξ‖ₑ ^ 2 := by
          rw [hI, lintegral_const_mul' _ _ h2ne]
      _ ≤ ∫⁻ ξ, (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F 0 ξ‖ₑ ^ 2 + 2 * ∫⁻ s in Icc 0 T',
            ENNReal.ofReal (‖ξ‖ ^ 2) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ)) :=
          lintegral_mono fun ξ => h1 T' hpos F hF1 hd ξ
      _ = _ := by
          rw [lintegral_add_left' hm0, lintegral_const_mul' _ _ h2ne, hJ,
            ← lintegral_const_mul' _ _ h2ne, hA0]
  have hpt : ∀ s ∈ Icc 0 T', 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) ≤ dissipSq α (F s) + ENNReal.ofReal (M' + a ^ 4) := by
    intro s hs'
    have hfs := hF.1 s hs'
    have h3s : hsNormSq 3 (F s) < ⊤ := lt_of_le_of_lt (hsNormSq_le_hsNormSq_of_le hm _) hfs.2
    calc 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ)
        ≤ 2 * (ENNReal.ofReal C * homNormSq 1 (F s) ^ (3 / 4 : ℝ) *
            homNormSq 2 (F s) ^ (3 / 4 : ℝ)) := mul_le_mul' le_rfl (hC _ hfs.1 (hs s hs') h3s)
      _ ≤ 2 * (ENNReal.ofReal C' * ENNReal.ofReal M' ^ (3 / 4 : ℝ) *
            (dissipSq α (F s) + ENNReal.ofReal M') ^ (3 / 4 : ℝ)) :=
          mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hCC')
            (ENNReal.rpow_le_rpow ((hM s hs').trans (ENNReal.ofReal_le_ofReal hMM')) (by norm_num)))
            (ENNReal.rpow_le_rpow (hBA s hs') (by norm_num)))
      _ = ENNReal.ofReal a * (dissipSq α (F s) + ENNReal.ofReal M') ^ (3 / 4 : ℝ) := by
          rw [hadef, ENNReal.ofReal_mul (mul_nonneg zero_le_two hC0), ENNReal.ofReal_mul zero_le_two,
            ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num), ENNReal.ofReal_ofNat]
          ring
      _ ≤ dissipSq α (F s) + ENNReal.ofReal M' + ENNReal.ofReal (a ^ 4) :=
          ofReal_mul_rpow_three_quarters_le_self ha _
      _ = _ := by rw [ENNReal.ofReal_add hM0 (by positivity), add_assoc]
  have hX := hWfin.ne
  have hmain : 2 * ∫⁻ s in Icc 0 T', dissipSq α (F s) ≤ ENNReal.ofReal M' +
      ((∫⁻ s in Icc 0 T', dissipSq α (F s)) + ENNReal.ofReal (M' + a ^ 4) * ENNReal.ofReal T') := by
    refine hstep.trans (add_le_add ((hM 0 hT0).trans (ENNReal.ofReal_le_ofReal hMM')) ?_)
    calc ∫⁻ s in Icc 0 T', 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ 2) *
          (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) ≤
          ∫⁻ s in Icc 0 T', (dissipSq α (F s) + ENNReal.ofReal (M' + a ^ 4)) :=
          setLIntegral_mono' measurableSet_Icc hpt
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Icc, sub_zero]
  have hWbd : ∫⁻ s in Icc 0 T', dissipSq α (F s) ≤
      ENNReal.ofReal M' + ENNReal.ofReal (M' + a ^ 4) * ENNReal.ofReal T' := by
    refine (ENNReal.add_le_add_iff_right hX).1 ?_
    calc _ = 2 * ∫⁻ s in Icc 0 T', dissipSq α (F s) := (two_mul _).symm
      _ ≤ _ := hmain
      _ = _ := by ring
  have hT'0 := hpos.le
  calc ∫⁻ s in Icc 0 T', homNormSq 2 (F s) ≤
        ∫⁻ s in Icc 0 T', (dissipSq α (F s) + ENNReal.ofReal M') :=
        setLIntegral_mono' measurableSet_Icc hBA
    _ = (∫⁻ s in Icc 0 T', dissipSq α (F s)) + ENNReal.ofReal M' * ENNReal.ofReal T' := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Icc, sub_zero]
    _ ≤ (ENNReal.ofReal M' + ENNReal.ofReal (M' + a ^ 4) * ENNReal.ofReal T') +
        ENNReal.ofReal M' * ENNReal.ofReal T' := add_le_add hWbd le_rfl
    _ = ENNReal.ofReal (M' + (M' + a ^ 4) * T' + M' * T') := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM0,
          ← ENNReal.ofReal_add hM0 (mul_nonneg (by positivity) hT'0),
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hM0 hT'0)]
    _ ≤ ENNReal.ofReal (M' + (2 * M' + a ^ 4) * T) := by
        apply ENNReal.ofReal_le_ofReal
        have hTT := hT'.2
        have ha4 : 0 ≤ a ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hTT (by positivity : (0 : ℝ) ≤ 2 * M' + a ^ 4)]

end Breakdown.SmoothFlow
