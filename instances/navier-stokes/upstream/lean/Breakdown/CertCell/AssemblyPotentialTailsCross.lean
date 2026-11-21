import Breakdown.FracCell.CellDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.PotentialTails

open CellCert.CellAnalysis

theorem polyFn_continuous {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := hP
  have e : P = fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
      c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) := funext hc
  rw [e]
  fun_prop

theorem proj_mem_polyFn (Kb : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Kb.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨fun _ _ => 0, fun p => by simp⟩

theorem proj_continuous (Kb : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (Kb.proj d d' F) :=
  polyFn_continuous (proj_mem_polyFn Kb d d' F)

theorem rect_measurableSet (Kb : CellBox) : MeasurableSet Kb.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem rect_isCompact (Kb : CellBox) : IsCompact Kb.rect :=
  isCompact_Icc.prod isCompact_Icc

theorem lineWeight_continuous (Kb : CellBox) : Continuous Kb.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem lineWeight_nonneg (Kb : CellBox) (hK : IsCellBox Kb) {p : ℝ × ℝ} (hp : p ∈ Kb.rect) :
    0 ≤ Kb.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hp.1.1
  · exact zero_le_one

theorem lineWeight_mul_rHat (Kb : CellBox) (p : ℝ × ℝ) :
    Kb.lineWeight p.1 * CellScalars.rHat Kb p = p.1 := by
  unfold CellScalars.rHat
  rcases eq_or_ne (Kb.lineWeight p.1) 0 with h | h
  · have : p.1 = 0 := by
      unfold CellBox.lineWeight at h
      split_ifs at h
      · exact h
      · exact absurd h one_ne_zero
    rw [h, this]; simp
  · field_simp

theorem rHat_measurable (Kb : CellBox) : Measurable (fun p : ℝ × ℝ => CellScalars.rHat Kb p) := by
  unfold CellScalars.rHat
  exact measurable_fst.div ((lineWeight_continuous Kb).measurable.comp measurable_fst)

theorem rHat_bound (Kb : CellBox) (hK : IsCellBox Kb) {p : ℝ × ℝ} (hp : p ∈ Kb.rect) :
    |CellScalars.rHat Kb p| ≤ max Kb.r₂ 1 := by
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have h2 : p.1 ≤ Kb.r₂ := hp.1.2
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · rcases eq_or_ne p.1 0 with h | h
    · rw [h]; simp
    · rw [div_self h]; simp
  · rw [div_one, abs_of_nonneg h0]; exact le_max_of_le_left h2

theorem volume_rect_ne_top (Kb : CellBox) : volume Kb.rect ≠ ⊤ :=
  (rect_isCompact Kb).measure_lt_top.ne

theorem rect_finite (Kb : CellBox) : IsFiniteMeasure (volume.restrict Kb.rect) :=
  isFiniteMeasure_restrict.2 (volume_rect_ne_top Kb)

attribute [local instance] rect_finite

theorem two_mul_le_weighted (a b β : ℝ) (hβ : 0 < β) : 2 * (a * b) ≤ β * a ^ 2 + b ^ 2 / β := by
  have h : 0 ≤ (β * a - b) ^ 2 / β := div_nonneg (sq_nonneg _) hβ.le
  have e : (β * a - b) ^ 2 / β = β * a ^ 2 - 2 * (a * b) + b ^ 2 / β := by
    field_simp
    ring
  linarith

theorem re_conj_mul_le (z w : ℂ) : |((starRingEnd ℂ) z * w).re| ≤ ‖z‖ * ‖w‖ := by
  calc |((starRingEnd ℂ) z * w).re| ≤ ‖(starRingEnd ℂ) z * w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]

theorem tail_cross_lower (Kb : CellBox) (hK : IsCellBox Kb) (Q : ℕ) (F h : ℝ × ℝ → ℂ) {β : ℝ} (hβ : 0 < β)
    (horth : ∀ P ∈ polyFn Q Q, Kb.pairOn Kb.lineWeightFn (fun p => F p - Kb.proj Q Q F p) P = 0)
    (hFm : AEStronglyMeasurable F (volume.restrict Kb.rect))
    (hFi : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖F p‖ ^ 2) Kb.rect)
    (hhm : AEStronglyMeasurable h (volume.restrict Kb.rect)) {C : ℝ} (hhC : ∀ p ∈ Kb.rect, ‖h p‖ ≤ C) :
    IntegrableOn (fun p => p.1 * ((starRingEnd ℂ) (F p - Kb.proj Q Q F p) * h p).re) Kb.rect ∧
    -(Kb.tailNormSq Q (fun p => (CellScalars.rHat Kb p : ℂ) * h p) / β + β * Kb.tailNormSq Q F)
      ≤ 2 * ∫ p in Kb.rect, p.1 * ((starRingEnd ℂ) (F p - Kb.proj Q Q F p) * h p).re := by
  have hs := rect_measurableSet Kb
  set μ := volume.restrict Kb.rect with hμ
  set w : ℝ × ℝ → ℝ := fun p => Kb.lineWeight p.1 with hw
  have hwc : Continuous w := (lineWeight_continuous Kb).comp continuous_fst
  have hwnn : ∀ p ∈ Kb.rect, 0 ≤ w p := fun p hp => lineWeight_nonneg Kb hK hp
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  set PF := Kb.proj Q Q F with hPF
  set T : ℝ × ℝ → ℂ := fun p => F p - PF p with hT
  set g : ℝ × ℝ → ℂ := fun p => (CellScalars.rHat Kb p : ℂ) * h p with hg
  set Pg := Kb.proj Q Q g with hPg
  set E : ℝ × ℝ → ℂ := fun p => g p - Pg p with hE
  have hPFc : Continuous PF := proj_continuous Kb Q Q F
  have hPgc : Continuous Pg := proj_continuous Kb Q Q g
  obtain ⟨CP, hCP⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hPFc.continuousOn
  obtain ⟨CQ, hCQ⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hPgc.continuousOn
  have hCQ' : ∀ p ∈ Kb.rect, ‖Pg p‖ ≤ max CQ 0 := fun p hp => le_max_of_le_left (hCQ p hp)
  have hTm : AEStronglyMeasurable T μ := hFm.sub hPFc.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ :=
    (Complex.measurable_ofReal.comp (rHat_measurable Kb)).aestronglyMeasurable.mul hhm
  have hEm : AEStronglyMeasurable E μ := hgm.sub hPgc.aestronglyMeasurable
  have hwm : AEStronglyMeasurable w μ := hwc.aestronglyMeasurable
  set M : ℝ := max Kb.r₂ 1 * max C 0 + max CQ 0 with hM
  have hEb : ∀ p ∈ Kb.rect, ‖E p‖ ≤ M := by
    intro p hp
    have h1 : ‖g p‖ ≤ max Kb.r₂ 1 * max C 0 := by
      show ‖(CellScalars.rHat Kb p : ℂ) * h p‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (rHat_bound Kb hK hp) (le_max_of_le_left (hhC p hp)) (norm_nonneg _)
        (le_trans (abs_nonneg _) (rHat_bound Kb hK hp))
    calc ‖E p‖ = ‖g p - Pg p‖ := rfl
      _ ≤ ‖g p‖ + ‖Pg p‖ := norm_sub_le _ _
      _ ≤ M := add_le_add h1 (hCQ' p hp)
  have hw1 : Integrable w μ := by
    refine Integrable.mono' (integrable_const Cw) hwm ?_
    exact ae_restrict_of_forall_mem hs fun p hp => hCw p hp
  have hT2 : Integrable (fun p => w p * ‖T p‖ ^ 2) μ := by
    refine Integrable.mono' ((hFi.const_mul 2).add (hw1.mul_const (2 * CP ^ 2))) (hwm.mul (hTm.norm.pow 2)) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := hwnn p hp
    have h1 : ‖T p‖ ≤ ‖F p‖ + ‖PF p‖ := norm_sub_le _ _
    have h2 : ‖PF p‖ ≤ CP := hCP p hp
    have h3 : ‖T p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * CP ^ 2 := by
      have h4 : ‖T p‖ ^ 2 ≤ (‖F p‖ + ‖PF p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h5 : ‖PF p‖ ^ 2 ≤ CP ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [sq_nonneg (‖F p‖ - ‖PF p‖)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    show w p * ‖T p‖ ^ 2 ≤ 2 * (w p * ‖F p‖ ^ 2) + w p * (2 * CP ^ 2)
    nlinarith
  have hE2 : Integrable (fun p => w p * ‖E p‖ ^ 2) μ := by
    refine Integrable.mono' (integrable_const (Cw * M ^ 2)) (hwm.mul (hEm.norm.pow 2)) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := hwnn p hp
    have h1 : ‖E p‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hEb p hp) 2
    have h2 : w p ≤ Cw := le_trans (le_abs_self _) (hCw p hp)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    exact mul_le_mul h2 h1 (sq_nonneg _) (le_trans h0 h2)
  set I1 : ℝ × ℝ → ℝ := fun p => w p * ((starRingEnd ℂ) (T p) * E p).re with hI1
  set f2 : ℝ × ℝ → ℂ := fun p => (w p : ℂ) * T p * (starRingEnd ℂ) (Pg p) with hf2
  have hI1i : Integrable I1 μ := by
    refine Integrable.mono' ((hT2.add hE2).div_const 2)
      (hwm.mul (Complex.continuous_re.comp_aestronglyMeasurable (hTm.star.mul hEm))) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := hwnn p hp
    have h1 := re_conj_mul_le (T p) (E p)
    have h2 : 2 * (‖T p‖ * ‖E p‖) ≤ ‖T p‖ ^ 2 + ‖E p‖ ^ 2 := by
      nlinarith [sq_nonneg (‖T p‖ - ‖E p‖)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    show w p * |((starRingEnd ℂ) (T p) * E p).re| ≤ (w p * ‖T p‖ ^ 2 + w p * ‖E p‖ ^ 2) / 2
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith
  have hf2i : Integrable f2 μ := by
    refine Integrable.mono' (((hw1.add hT2).div_const 2).mul_const (max CQ 0))
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable hwm).mul hTm).mul
        hPgc.aestronglyMeasurable.star) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := hwnn p hp
    have h2 := hCQ' p hp
    have h3 : ‖f2 p‖ = w p * ‖T p‖ * ‖Pg p‖ := by
      show ‖(w p : ℂ) * T p * (starRingEnd ℂ) (Pg p)‖ = _
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    rw [h3]
    show w p * ‖T p‖ * ‖Pg p‖ ≤ (w p + w p * ‖T p‖ ^ 2) / 2 * max CQ 0
    have h4 : w p * ‖T p‖ ≤ (w p + w p * ‖T p‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖T p‖ - 1), mul_nonneg h0 (sq_nonneg (‖T p‖ - 1))]
    exact mul_le_mul h4 h2 (norm_nonneg _) (by nlinarith [norm_nonneg (T p)])
  have hsplit : (fun p => p.1 * ((starRingEnd ℂ) (F p - Kb.proj Q Q F p) * h p).re)
      = fun p => I1 p + (f2 p).re := by
    funext p
    have e := lineWeight_mul_rHat Kb p
    show p.1 * ((starRingEnd ℂ) (F p - PF p) * h p).re
      = Kb.lineWeight p.1 * ((starRingEnd ℂ) (F p - PF p) * ((CellScalars.rHat Kb p : ℂ) * h p - Pg p)).re
        + ((Kb.lineWeight p.1 : ℂ) * (F p - PF p) * (starRingEnd ℂ) (Pg p)).re
    have key : Kb.lineWeight p.1 * ((starRingEnd ℂ) (F p - PF p) * ((CellScalars.rHat Kb p : ℂ) * h p - Pg p)).re
        + ((Kb.lineWeight p.1 : ℂ) * (F p - PF p) * (starRingEnd ℂ) (Pg p)).re
        = (Kb.lineWeight p.1 * CellScalars.rHat Kb p) * ((starRingEnd ℂ) (F p - PF p) * h p).re := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
      ring
    rw [key, e]
  have hzero : ∫ p, (f2 p).re ∂μ = 0 := by
    have h1 : ∫ p, f2 p ∂μ = 0 := horth Pg (proj_mem_polyFn Kb Q Q g)
    have h2 := integral_re hf2i
    rw [h1] at h2
    simpa using h2
  have hlow : ∫ p, ((-(β / 2)) * (w p * ‖T p‖ ^ 2) + (-(1 / (2 * β))) * (w p * ‖E p‖ ^ 2)) ∂μ
      ≤ ∫ p, I1 p ∂μ := by
    refine integral_mono_ae ((hT2.const_mul _).add (hE2.const_mul _)) hI1i ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := hwnn p hp
    have h1 := re_conj_mul_le (T p) (E p)
    have h2 := two_mul_le_weighted ‖T p‖ ‖E p‖ β hβ
    have h3 : -((β * ‖T p‖ ^ 2 + ‖E p‖ ^ 2 / β) / 2) ≤ ((starRingEnd ℂ) (T p) * E p).re := by
      have := neg_abs_le ((starRingEnd ℂ) (T p) * E p).re
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 h0
    show (-(β / 2)) * (w p * ‖T p‖ ^ 2) + (-(1 / (2 * β))) * (w p * ‖E p‖ ^ 2)
      ≤ w p * ((starRingEnd ℂ) (T p) * E p).re
    have e : (-(β / 2)) * (w p * ‖T p‖ ^ 2) + (-(1 / (2 * β))) * (w p * ‖E p‖ ^ 2)
        = w p * -((β * ‖T p‖ ^ 2 + ‖E p‖ ^ 2 / β) / 2) := by
      field_simp
      ring
    rw [e]
    exact h4
  rw [integral_add (hT2.const_mul _) (hE2.const_mul _), integral_const_mul, integral_const_mul] at hlow
  have hFeq : Kb.tailNormSq Q F = ∫ p, w p * ‖T p‖ ^ 2 ∂μ := rfl
  have hgeq : Kb.tailNormSq Q g = ∫ p, w p * ‖E p‖ ^ 2 ∂μ := rfl
  have hre : Integrable (fun p => (f2 p).re) μ := hf2i.re
  refine ⟨?_, ?_⟩
  · show Integrable _ μ
    rw [hsplit]
    exact hI1i.add hre
  · show -(Kb.tailNormSq Q g / β + β * Kb.tailNormSq Q F) ≤ 2 * ∫ p, _ ∂μ
    rw [hsplit, integral_add hI1i hre, hzero, add_zero, hFeq, hgeq]
    have e : -((∫ p, w p * ‖E p‖ ^ 2 ∂μ) / β + β * ∫ p, w p * ‖T p‖ ^ 2 ∂μ)
        = 2 * (-(β / 2) * (∫ p, w p * ‖T p‖ ^ 2 ∂μ) + -(1 / (2 * β)) * ∫ p, w p * ‖E p‖ ^ 2 ∂μ) := by
      field_simp
      ring
    rw [e]
    linarith

theorem tail_regular (Kb : CellBox) (hK : IsCellBox Kb) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hFm : AEStronglyMeasurable F (volume.restrict Kb.rect))
    (hFi : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖F p‖ ^ 2) Kb.rect) :
    AEStronglyMeasurable (fun p => F p - Kb.proj Q Q F p) (volume.restrict Kb.rect) ∧
    IntegrableOn (fun p => Kb.lineWeight p.1 * ‖F p - Kb.proj Q Q F p‖ ^ 2) Kb.rect := by
  have hs := rect_measurableSet Kb
  have hwc : Continuous fun p : ℝ × ℝ => Kb.lineWeight p.1 := (lineWeight_continuous Kb).comp continuous_fst
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  have hPFc := proj_continuous Kb Q Q F
  obtain ⟨CP, hCP⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hPFc.continuousOn
  have hTm : AEStronglyMeasurable (fun p => F p - Kb.proj Q Q F p) (volume.restrict Kb.rect) :=
    hFm.sub hPFc.aestronglyMeasurable
  have hw1 : IntegrableOn (fun p : ℝ × ℝ => Kb.lineWeight p.1) Kb.rect := by
    refine Integrable.mono' (integrable_const Cw) hwc.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hs fun p hp => hCw p hp
  refine ⟨hTm, ?_⟩
  refine Integrable.mono' ((hFi.const_mul 2).add (hw1.mul_const (2 * CP ^ 2)))
    (hwc.aestronglyMeasurable.mul (hTm.norm.pow 2)) ?_
  refine ae_restrict_of_forall_mem hs fun p hp => ?_
  have h0 := lineWeight_nonneg Kb hK hp
  have h1 : ‖F p - Kb.proj Q Q F p‖ ≤ ‖F p‖ + ‖Kb.proj Q Q F p‖ := norm_sub_le _ _
  have h2 : ‖Kb.proj Q Q F p‖ ≤ CP := hCP p hp
  have h4 : ‖F p - Kb.proj Q Q F p‖ ^ 2 ≤ (‖F p‖ + ‖Kb.proj Q Q F p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : ‖Kb.proj Q Q F p‖ ^ 2 ≤ CP ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3 : ‖F p - Kb.proj Q Q F p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * CP ^ 2 := by
    nlinarith [sq_nonneg (‖F p‖ - ‖Kb.proj Q Q F p‖)]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  show Kb.lineWeight p.1 * ‖F p - Kb.proj Q Q F p‖ ^ 2
    ≤ 2 * (Kb.lineWeight p.1 * ‖F p‖ ^ 2) + Kb.lineWeight p.1 * (2 * CP ^ 2)
  nlinarith

theorem fst_le_lineWeight (Kb : CellBox) (hK : IsCellBox Kb) {p : ℝ × ℝ} (hp : p ∈ Kb.rect) :
    0 ≤ p.1 ∧ p.1 ≤ max Kb.r₂ 1 * Kb.lineWeight p.1 := by
  have h0 := lineWeight_nonneg Kb hK hp
  refine ⟨le_trans hK.r_order.1 hp.1.1, ?_⟩
  calc p.1 = Kb.lineWeight p.1 * CellScalars.rHat Kb p := (lineWeight_mul_rHat Kb p).symm
    _ ≤ Kb.lineWeight p.1 * max Kb.r₂ 1 :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (rHat_bound Kb hK hp)) h0
    _ = max Kb.r₂ 1 * Kb.lineWeight p.1 := mul_comm _ _

theorem cross_integrable (Kb : CellBox) (hK : IsCellBox Kb) {T c : ℝ × ℝ → ℂ}
    (hTm : AEStronglyMeasurable T (volume.restrict Kb.rect))
    (hT2 : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T p‖ ^ 2) Kb.rect)
    (hcm : AEStronglyMeasurable c (volume.restrict Kb.rect)) {C : ℝ} (hcC : ∀ p ∈ Kb.rect, ‖c p‖ ≤ C) :
    IntegrableOn (fun p => p.1 * ((starRingEnd ℂ) (T p) * c p).re) Kb.rect := by
  have hs := rect_measurableSet Kb
  have hwc : Continuous fun p : ℝ × ℝ => Kb.lineWeight p.1 := (lineWeight_continuous Kb).comp continuous_fst
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  have hw1 : IntegrableOn (fun p : ℝ × ℝ => Kb.lineWeight p.1) Kb.rect := by
    refine Integrable.mono' (integrable_const Cw) hwc.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hs fun p hp => hCw p hp
  refine Integrable.mono' (((hw1.add hT2).div_const 2).mul_const (max Kb.r₂ 1 * max C 0))
    (continuous_fst.aestronglyMeasurable.mul
      (Complex.continuous_re.comp_aestronglyMeasurable (hTm.star.mul hcm))) ?_
  refine ae_restrict_of_forall_mem hs fun p hp => ?_
  obtain ⟨h0, h1⟩ := fst_le_lineWeight Kb hK hp
  have hw0 := lineWeight_nonneg Kb hK hp
  have h2 := re_conj_mul_le (T p) (c p)
  have h3 : ‖c p‖ ≤ max C 0 := le_max_of_le_left (hcC p hp)
  have h4 : ‖T p‖ ≤ (1 + ‖T p‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖T p‖ - 1)]
  have hM : 0 ≤ max Kb.r₂ 1 := le_trans zero_le_one (le_max_right _ _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  show p.1 * |((starRingEnd ℂ) (T p) * c p).re|
    ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 * (max Kb.r₂ 1 * max C 0)
  have h5 : |((starRingEnd ℂ) (T p) * c p).re| ≤ ‖T p‖ * max C 0 :=
    le_trans h2 (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have h6 : Kb.lineWeight p.1 * ‖T p‖ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hw0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc p.1 * |((starRingEnd ℂ) (T p) * c p).re| ≤ (max Kb.r₂ 1 * Kb.lineWeight p.1) * (‖T p‖ * max C 0) :=
        mul_le_mul h1 h5 (abs_nonneg _) (mul_nonneg hM hw0)
    _ = (Kb.lineWeight p.1 * ‖T p‖) * (max Kb.r₂ 1 * max C 0) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h6 (mul_nonneg hM hC0)

theorem cross_sum (Kb : CellBox) (hK : IsCellBox Kb) {T : ℝ × ℝ → ℂ} {ι : Type} (s : Finset ι)
    (c : ι → ℝ × ℝ → ℂ)
    (hTm : AEStronglyMeasurable T (volume.restrict Kb.rect))
    (hT2 : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T p‖ ^ 2) Kb.rect)
    (hcm : ∀ a, AEStronglyMeasurable (c a) (volume.restrict Kb.rect))
    (hcC : ∀ a, ∃ C, ∀ p ∈ Kb.rect, ‖c a p‖ ≤ C) :
    ∫ p in Kb.rect, p.1 * ((starRingEnd ℂ) (T p) * ∑ a ∈ s, c a p).re
      = ∑ a ∈ s, ∫ p in Kb.rect, p.1 * ((starRingEnd ℂ) (T p) * c a p).re := by
  rw [← integral_finsetSum]
  · congr 1
    funext p
    rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  · intro a _
    obtain ⟨C, hC⟩ := hcC a
    exact cross_integrable Kb hK hTm hT2 (hcm a) hC

theorem sum_fin12 (f : Fin 12 → ℝ) : ∑ i, f i = ∑ a : Fin 3, ∑ b : Fin 3, f ⟨3 * a.val + b.val, by omega⟩
    + ∑ a : Fin 3, f ⟨9 + a.val, by omega⟩ := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring_nf
  rfl

end Breakdown.CertCell.Assembly.Internal.PotentialTails
