import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal

theorem aesm_swap {X : Type*} [TopologicalSpace X] (F : ℝ → Space → X)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : Space × ℝ => F z.2 z.1)
      ((volume : Measure Space).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  rw [Measure.volume_eq_prod] at hF
  have h := (hF.prod_swap).restrict (s := univ ×ˢ Icc (0 : ℝ) 1)
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at h

theorem aesm_avg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (c : ℝ → ℝ) (hc : Measurable c) :
    AEStronglyMeasurable (fun y => ∫ τ in Icc (0 : ℝ) 1, c τ • F τ y) volume :=
  ((hc.comp measurable_snd).aestronglyMeasurable.smul (aesm_swap F hF)).integral_prod_right'

theorem aesm_slice {X : Type*} [TopologicalSpace X] (F : ℝ → Space → X)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) 1)), AEStronglyMeasurable (F τ) volume := by
  rw [Measure.volume_eq_prod] at hF
  exact ae_restrict_of_ae hF.prodMk_left

theorem lintegral_rpow_le_weighted (μ : Measure ℝ) {f b : ℝ → ℝ≥0∞} (hf : AEMeasurable f μ) (hb : AEMeasurable b μ)
    (hb0 : ∀ x, b x ≠ 0) (hbt : ∀ x, b x ≠ ⊤) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, f x ∂μ) ^ p ≤ (∫⁻ x, b x ∂μ) ^ (p - 1) * ∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hq : p.conjExponent.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hqe : p.conjExponent = p / (p - 1) := rfl
  set r := (p - 1) / p with hr
  have hsplit : ∀ x, f x = b x ^ r * (b x ^ (-r) * f x) := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (hb0 x) (hbt x), add_neg_cancel, ENNReal.rpow_zero, one_mul]
  have e1 : ∀ x, (b x ^ r) ^ p.conjExponent = b x := by
    intro x
    rw [← ENNReal.rpow_mul, hqe, hr]
    have : (p - 1) / p * (p / (p - 1)) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  have e2 : ∀ x, (b x ^ (-r) * f x) ^ p = b x ^ (1 - p) * f x ^ p := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hr]
    congr 2
    field_simp
    ring
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq (hb.pow_const r) ((hb.pow_const (-r)).mul hf)
  have h2 : ∫⁻ x, f x ∂μ ≤ (∫⁻ x, b x ∂μ) ^ (1 / p.conjExponent) *
      (∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ) ^ (1 / p) := by
    calc ∫⁻ x, f x ∂μ = ∫⁻ x, ((fun x => b x ^ r) * fun x => b x ^ (-r) * f x) x ∂μ :=
          lintegral_congr fun x => hsplit x
      _ ≤ _ := h1
      _ = _ := by simp only [Pi.mul_apply, e1, e2]
  calc (∫⁻ x, f x ∂μ) ^ p ≤ ((∫⁻ x, b x ∂μ) ^ (1 / p.conjExponent) *
        (∫⁻ x, b x ^ (1 - p) * f x ^ p ∂μ) ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h2 hp0.le
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hqe]
      have a1 : 1 / (p / (p - 1)) * p = p - 1 := by field_simp
      have a2 : 1 / p * p = 1 := by field_simp
      rw [a1, a2, ENNReal.rpow_one]

theorem lintegral_rpow_avg_lt_top (f : ℝ → Space → ℝ≥0∞)
    (hf : AEMeasurable (fun z : Space × ℝ => f z.2 z.1)
      ((volume : Measure Space).prod (volume.restrict (Icc (0 : ℝ) 1))))
    {p : ℝ} (hp : 1 < p) (hfin : ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, f τ y ^ p) ^ (1 / p) < ⊤) :
    ∫⁻ y, (∫⁻ τ in Icc (0 : ℝ) 1, f τ y) ^ p < ⊤ := by
  set μ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) with hμ
  have hp0 : 0 < p := by linarith
  have hsw : AEMeasurable (fun z : ℝ × Space => f z.1 z.2 ^ p) (μ.prod volume) :=
    (hf.pow_const p).prod_swap
  have ha : AEMeasurable (fun τ => ∫⁻ y, f τ y ^ p) μ := hsw.lintegral_prod_right'
  set a : ℝ → ℝ≥0∞ := fun τ => (∫⁻ y, f τ y ^ p) ^ (1 / p) with ha_def
  have haa : AEMeasurable a μ := ha.pow_const _
  set a₀ := haa.mk a
  have ha₀ : Measurable a₀ := haa.measurable_mk
  have hae : a =ᵐ[μ] a₀ := haa.ae_eq_mk
  set b : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal ((a₀ τ).toReal + 1) with hb_def
  have hbm : Measurable b := ENNReal.measurable_ofReal.comp (ha₀.ennreal_toReal.add_const 1)
  have hb0 : ∀ τ, b τ ≠ 0 := fun τ => by
    simp only [hb_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hbt : ∀ τ, b τ ≠ ⊤ := fun τ => ENNReal.ofReal_ne_top
  have hble : ∀ τ, b τ ≤ a₀ τ + 1 := fun τ => by
    simp only [hb_def]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_one]
    gcongr
    exact ENNReal.ofReal_toReal_le
  have hab : ∀ τ, a₀ τ ≠ ⊤ → a₀ τ ≤ b τ := fun τ h => by
    simp only [hb_def]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_one, ENNReal.ofReal_toReal h]
    exact le_self_add
  have hμ1 : μ univ = 1 := by simp [hμ]
  have hB : ∫⁻ τ, b τ ∂μ < ⊤ := by
    calc ∫⁻ τ, b τ ∂μ ≤ ∫⁻ τ, (a₀ τ + 1) ∂μ := lintegral_mono hble
      _ = ∫⁻ τ, a₀ τ ∂μ + ∫⁻ _τ, 1 ∂μ := lintegral_add_right _ measurable_const
      _ = ∫⁻ τ, a τ ∂μ + 1 := by rw [lintegral_congr_ae hae.symm, lintegral_const, hμ1, one_mul]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfin, ENNReal.one_lt_top⟩
  have hfy : ∀ᵐ y ∂(volume : Measure Space), AEMeasurable (fun τ => f τ y) μ :=
    (hf.aestronglyMeasurable.prodMk_left).mono fun y hy => hy.aemeasurable
  have step1 : ∫⁻ y, (∫⁻ τ, f τ y ∂μ) ^ p ≤
      ∫⁻ y, (∫⁻ τ, b τ ∂μ) ^ (p - 1) * ∫⁻ τ, b τ ^ (1 - p) * f τ y ^ p ∂μ :=
    lintegral_mono_ae (hfy.mono fun y hy => lintegral_rpow_le_weighted μ hy hbm.aemeasurable hb0 hbt hp)
  have hbr : ∀ τ, b τ ^ (1 - p) ≠ ⊤ := fun τ => by
    rw [ne_eq, ENNReal.rpow_eq_top_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hb0 τ h
    · exact hbt τ h
  have step2 : ∫⁻ y, ∫⁻ τ, b τ ^ (1 - p) * f τ y ^ p ∂μ = ∫⁻ τ, b τ ^ (1 - p) * (∫⁻ y, f τ y ^ p) ∂μ := by
    rw [lintegral_lintegral_swap]
    · exact lintegral_congr fun τ => lintegral_const_mul' _ _ (hbr τ)
    · exact ((hbm.pow_const _).comp measurable_snd).aemeasurable.mul (hf.pow_const p)
  have step3 : ∫⁻ τ, b τ ^ (1 - p) * (∫⁻ y, f τ y ^ p) ∂μ ≤ ∫⁻ τ, b τ ∂μ := by
    apply lintegral_mono_ae
    have hfin' : ∀ᵐ τ ∂μ, a τ < ⊤ := ae_lt_top' haa hfin.ne
    filter_upwards [hfin', hae] with τ h1 h2
    have hI : ∫⁻ y, f τ y ^ p = a τ ^ p := by
      simp only [ha_def]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    rw [hI]
    have hle : a τ ≤ b τ := by
      rw [h2]
      exact hab τ (h2 ▸ h1.ne)
    calc b τ ^ (1 - p) * a τ ^ p ≤ b τ ^ (1 - p) * b τ ^ p := by
          gcongr
      _ = b τ := by
          rw [← ENNReal.rpow_add _ _ (hb0 τ) (hbt τ)]
          simp
  have hBt : (∫⁻ τ, b τ ∂μ) ^ (p - 1) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) hB.ne).ne
  calc ∫⁻ y, (∫⁻ τ, f τ y ∂μ) ^ p ≤ _ := step1
    _ = (∫⁻ τ, b τ ∂μ) ^ (p - 1) * ∫⁻ y, ∫⁻ τ, b τ ^ (1 - p) * f τ y ^ p ∂μ :=
        lintegral_const_mul' _ _ hBt
    _ ≤ (∫⁻ τ, b τ ∂μ) ^ (p - 1) * ∫⁻ τ, b τ ∂μ := by
        rw [step2]
        gcongr
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBt) hB

theorem memLp_avg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (c : ℝ → ℝ) (hc : Measurable c)
    (hc1 : ∀ τ, |c τ| ≤ 1) {p : ℝ} (hp : 1 < p)
    (hfin : ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ‖F τ y‖ₑ ^ p) ^ (1 / p) < ⊤) :
    MemLp (fun y => ∫ τ in Icc (0 : ℝ) 1, c τ • F τ y) (ENNReal.ofReal p) volume := by
  refine ⟨aesm_avg F hF c hc, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  refine lt_of_le_of_lt (lintegral_mono fun y => ?_)
    (lintegral_rpow_avg_lt_top (fun τ y => ‖F τ y‖ₑ) (aesm_swap F hF).enorm hp hfin)
  refine ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_))
    (by linarith)
  rw [enorm_smul]
  calc ‖c τ‖ₑ * ‖F τ y‖ₑ ≤ 1 * ‖F τ y‖ₑ := by
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 (hc1 τ)
    _ = ‖F τ y‖ₑ := one_mul _


theorem apply_eq_sum_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (w : Space) : L w = ∑ i : Fin 3, w i • L (unitVector i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp [unitVector, EuclideanSpace.basisFun_apply]

theorem norm_le_sum_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun w => ?_
  rw [apply_eq_sum_cols L w]
  calc ‖∑ i : Fin 3, w i • L (unitVector i)‖ ≤ ∑ i : Fin 3, ‖w i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖w i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖w‖ * ‖L (unitVector i)‖ := by
        gcongr with i
        exact PiLp.norm_apply_le w i
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖w‖ := by rw [← Finset.mul_sum, mul_comm]

theorem norm_sq_le_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) :
    ‖L‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 := by
  have h1 := norm_le_sum_cols L
  have h0 := norm_nonneg L
  simp only [Fin.sum_univ_three] at h1 ⊢
  have a0 := norm_nonneg (L (unitVector 0))
  have a1 := norm_nonneg (L (unitVector 1))
  have a2 := norm_nonneg (L (unitVector 2))
  nlinarith [sq_nonneg (‖L (unitVector 0)‖ - ‖L (unitVector 1)‖),
    sq_nonneg (‖L (unitVector 1)‖ - ‖L (unitVector 2)‖), sq_nonneg (‖L (unitVector 0)‖ - ‖L (unitVector 2)‖)]

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem col_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) (i : Fin 3) :
    ‖L (unitVector i)‖ ≤ ‖L‖ := by
  simpa [norm_unitVector] using L.le_opNorm (unitVector i)

theorem sum_cols_sq_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) :
    ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ 3 * ‖L‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖L (unitVector i)‖ ^ 2 ≤ ‖L‖ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (col_norm_le L i) 2
  simp only [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 2 := pow_le_pow_right₀ h (by norm_num)
      _ ≤ 1 + x ^ 2 := le_add_self

theorem rpow_half_le (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · exact (ENNReal.rpow_le_one h (by norm_num)).trans le_self_add
  · calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_self

theorem sq_lt_top_of_bound {X : Type*} [NormedAddCommGroup X] (F : ℝ → Space → X) (S : ℝ → Space → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hle : ∀ τ y, ‖F τ y‖ ^ 2 ≤ K * S τ y)
    (hS : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (S τ y) < ⊤) :
    ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖F τ y‖ₑ ^ 2 < ⊤ := by
  have hpt : ∀ τ y, ‖F τ y‖ₑ ^ 2 ≤ ENNReal.ofReal K * ENNReal.ofReal (S τ y) := fun τ y => by
    rw [← ENNReal.ofReal_mul hK, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hle τ y)
  calc ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖F τ y‖ₑ ^ 2
      ≤ ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K * ENNReal.ofReal (S τ y) :=
        lintegral_mono fun τ => lintegral_mono fun y => hpt τ y
    _ = ENNReal.ofReal K * ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (S τ y) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun τ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS

theorem rpow_half_lintegral_lt_top_of_sq {X : Type*} [NormedAddCommGroup X] (F : ℝ → Space → X)
    (hsq : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖F τ y‖ₑ ^ 2 < ⊤) :
    ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ‖F τ y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < ⊤ := by
  have hμ1 : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by simp
  calc ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ‖F τ y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ ∫⁻ τ in Icc (0 : ℝ) 1, (1 + ∫⁻ y, ‖F τ y‖ₑ ^ 2) := by
        refine lintegral_mono fun τ => ?_
        simp only [ENNReal.rpow_two]
        exact rpow_half_le _
    _ = 1 + ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖F τ y‖ₑ ^ 2 := by
        rw [lintegral_add_left measurable_const, lintegral_const, hμ1, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hsq⟩

theorem hloc_of_sq {X : Type*} [NormedAddCommGroup X] (u : ℝ → Space → X)
    (hsq : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖u τ y‖ₑ ^ 2 < ⊤) (K : Set Space) (hK : IsCompact K) :
    ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in K, ‖u τ y‖ₑ < ⊤ := by
  have hμ1 : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by simp
  calc ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in K, ‖u τ y‖ₑ
      ≤ ∫⁻ τ in Icc (0 : ℝ) 1, (volume K + ∫⁻ y, ‖u τ y‖ₑ ^ 2) := by
        refine lintegral_mono fun τ => ?_
        calc ∫⁻ y in K, ‖u τ y‖ₑ ≤ ∫⁻ y in K, (1 + ‖u τ y‖ₑ ^ 2) :=
              lintegral_mono fun y => le_one_add_sq _
          _ = volume K + ∫⁻ y in K, ‖u τ y‖ₑ ^ 2 := by
              rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ ≤ volume K + ∫⁻ y, ‖u τ y‖ₑ ^ 2 := by
              exact add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ = volume K + ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖u τ y‖ₑ ^ 2 := by
        rw [lintegral_add_left measurable_const, lintegral_const, hμ1, mul_one]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hsq⟩

theorem enorm_pow_six {X : Type*} [NormedAddCommGroup X] (x : X) :
    ENNReal.ofReal (‖x‖ ^ 6) = ‖x‖ₑ ^ (6 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  norm_cast

theorem hloc_six {X : Type*} [NormedAddCommGroup X] (u : ℝ → Space → X)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (h6 : ∫⁻ σ in Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖u σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) < ⊤)
    (K : Set Space) (hK : IsCompact K) :
    ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in K, ‖u τ y‖ₑ < ⊤ := by
  have hpt : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∫⁻ y in K, ‖u τ y‖ₑ ≤
      (∫⁻ y, ENNReal.ofReal (‖u τ y‖ ^ 6)) ^ ((1 : ℝ) / 6) * volume K ^ ((1 : ℝ) - 1 / 6) := by
    filter_upwards [aesm_slice u hu] with τ hτ
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 6) (μ := volume.restrict K)
      (by norm_num) hτ.restrict
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
    refine h1.trans ?_
    have h2 : eLpNorm (u τ) 6 (volume.restrict K) ≤ eLpNorm (u τ) 6 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    have h3 : eLpNorm (u τ) 6 volume = (∫⁻ y, ‖u τ y‖ₑ ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := volume) (by norm_num) (by norm_num)]
      norm_num
    have e6 : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal = 1 - 1 / 6 := by norm_num
    rw [e6]
    simp only [enorm_pow_six]
    rw [← h3]
    exact mul_le_mul' h2 le_rfl
  calc ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in K, ‖u τ y‖ₑ
      ≤ ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖u τ y‖ ^ 6)) ^ ((1 : ℝ) / 6) *
          volume K ^ ((1 : ℝ) - 1 / 6) := lintegral_mono_ae hpt
    _ = (∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖u τ y‖ ^ 6)) ^ ((1 : ℝ) / 6)) *
          volume K ^ ((1 : ℝ) - 1 / 6) :=
        lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne)
    _ < ⊤ := ENNReal.mul_lt_top h6
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_lt_top.ne)

theorem smul_enorm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a : ℝ} (ha : |a| ≤ 1) (x : X) :
    ‖a • x‖ₑ ≤ ‖x‖ₑ := by
  rw [enorm_smul]
  calc ‖a‖ₑ * ‖x‖ₑ ≤ 1 * ‖x‖ₑ := by
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 ha
    _ = ‖x‖ₑ := one_mul _

theorem ae_integrable_avg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : ℝ → Space → X)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (c : ℝ → ℝ) (hc : Measurable c)
    (hc1 : ∀ τ, |c τ| ≤ 1) (hsq : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖F τ y‖ₑ ^ 2 < ⊤) :
    ∀ᵐ y ∂(volume : Measure Space), Integrable (fun τ => c τ • F τ y) (volume.restrict (Icc (0 : ℝ) 1)) := by
  set μ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) with hμ
  have hμ1 : μ univ = 1 := by simp [hμ]
  have hm : AEMeasurable (fun z : Space × ℝ => ‖F z.2 z.1‖ₑ ^ 2) ((volume : Measure Space).prod μ) :=
    (aesm_swap F hF).enorm.pow_const 2
  have h1 : ∫⁻ y, ∫⁻ τ, ‖F τ y‖ₑ ^ 2 ∂μ < ⊤ := by
    rw [lintegral_lintegral_swap (f := fun y τ => ‖F τ y‖ₑ ^ 2) hm]
    exact hsq
  have h2 : ∀ᵐ y ∂(volume : Measure Space), ∫⁻ τ, ‖F τ y‖ₑ ^ 2 ∂μ < ⊤ :=
    ae_lt_top' hm.lintegral_prod_right' h1.ne
  filter_upwards [h2, (aesm_swap F hF).prodMk_left] with y hy hy3
  refine ⟨hc.aestronglyMeasurable.smul hy3, ?_⟩
  show ∫⁻ τ, ‖c τ • F τ y‖ₑ ∂μ < ⊤
  calc ∫⁻ τ, ‖c τ • F τ y‖ₑ ∂μ ≤ ∫⁻ τ, (1 + ‖F τ y‖ₑ ^ 2) ∂μ :=
        lintegral_mono fun τ => (smul_enorm_le (hc1 τ) _).trans (le_one_add_sq _)
    _ = 1 + ∫⁻ τ, ‖F τ y‖ₑ ^ 2 ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, hμ1, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hy⟩

theorem integrable_test_prod {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (ψ : Space → ℝ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (u : ℝ → Space → X)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (hloc : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in tsupport ψ, ‖u τ y‖ₑ < ⊤)
    (c : ℝ → ℝ) (hc : Measurable c) (hc1 : ∀ τ, |c τ| ≤ 1) :
    Integrable (fun z : Space × ℝ => ψ z.1 • c z.2 • u z.2 z.1)
      ((volume : Measure Space).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  set μ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) with hμ
  obtain ⟨C, hC⟩ := hψc.bounded_above_of_compact_support hψs
  set K := tsupport ψ with hK
  have hKm : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  refine ⟨(hψc.measurable.comp measurable_fst).aestronglyMeasurable.smul
    ((hc.comp measurable_snd).aestronglyMeasurable.smul (aesm_swap u hu)), ?_⟩
  set g : Space × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal C * ‖u z.2 z.1‖ₑ with hg
  have hb : ∀ z : Space × ℝ, ‖ψ z.1 • c z.2 • u z.2 z.1‖ₑ ≤ (K ×ˢ univ).indicator g z := by
    intro z
    by_cases hz : z.1 ∈ K
    · rw [indicator_of_mem (mk_mem_prod hz (mem_univ z.2)), enorm_smul]
      refine mul_le_mul' ?_ (smul_enorm_le (hc1 z.2) _)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _)
    · rw [indicator_of_notMem (fun h => hz h.1), image_eq_zero_of_notMem_tsupport hz, zero_smul, enorm_zero]
  have hm : AEMeasurable ((K ×ˢ univ).indicator g) ((volume : Measure Space).prod μ) :=
    (aemeasurable_const.mul (aesm_swap u hu).enorm).indicator (hKm.prod MeasurableSet.univ)
  show ∫⁻ z, ‖ψ z.1 • c z.2 • u z.2 z.1‖ₑ ∂((volume : Measure Space).prod μ) < ⊤
  calc ∫⁻ z, ‖ψ z.1 • c z.2 • u z.2 z.1‖ₑ ∂((volume : Measure Space).prod μ)
      ≤ ∫⁻ z, (K ×ˢ univ).indicator g z ∂((volume : Measure Space).prod μ) := lintegral_mono hb
    _ = ∫⁻ τ, (∫⁻ y, (K ×ˢ univ).indicator g (y, τ)) ∂μ := lintegral_prod_symm _ hm
    _ = ∫⁻ τ, ENNReal.ofReal C * (∫⁻ y in K, ‖u τ y‖ₑ) ∂μ := by
        refine lintegral_congr fun τ => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hKm]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ K
        · simp [hy, hg]
        · simp [hy]
    _ = ENNReal.ofReal C * ∫⁻ τ, (∫⁻ y in K, ‖u τ y‖ₑ) ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hloc

theorem swap_test {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (ψ : Space → ℝ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (u : ℝ → Space → X)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (hloc : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y in tsupport ψ, ‖u τ y‖ₑ < ⊤)
    (c : ℝ → ℝ) (hc : Measurable c) (hc1 : ∀ τ, |c τ| ≤ 1) :
    ∫ y, ψ y • (∫ τ in Icc (0 : ℝ) 1, c τ • u τ y) =
      ∫ τ in Icc (0 : ℝ) 1, c τ • ∫ y, ψ y • u τ y := by
  have hI := integrable_test_prod ψ hψc hψs u hu hloc c hc hc1
  calc ∫ y, ψ y • (∫ τ in Icc (0 : ℝ) 1, c τ • u τ y)
      = ∫ y, ∫ τ in Icc (0 : ℝ) 1, ψ y • c τ • u τ y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (integral_smul _ _).symm
    _ = ∫ τ in Icc (0 : ℝ) 1, ∫ y, ψ y • c τ • u τ y := integral_integral_swap hI
    _ = ∫ τ in Icc (0 : ℝ) 1, c τ • ∫ y, ψ y • u τ y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact smul_comm _ _ _

theorem test_deriv (φ : Space → ℝ) (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) ∧
      HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := by
  refine ⟨(hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const, ?_⟩
  refine HasCompactSupport.mono' (hφ.2.fderiv (𝕜 := ℝ)) fun y hy => subset_tsupport _ ?_
  intro h
  apply hy
  simp [h]

theorem clm_avg {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (F : ℝ → Space → X) (c : ℝ → ℝ)
    (L : X →L[ℝ] Y)
    (h : ∀ᵐ y ∂(volume : Measure Space), Integrable (fun τ => c τ • F τ y) (volume.restrict (Icc (0 : ℝ) 1))) :
    ∀ᵐ y ∂(volume : Measure Space),
      L (∫ τ in Icc (0 : ℝ) 1, c τ • F τ y) = ∫ τ in Icc (0 : ℝ) 1, c τ • L (F τ y) :=
  h.mono fun y hy => by
    rw [← L.integral_comp_comm hy]
    simp only [map_smul]

theorem local_of_weight (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H)
    (c : ℝ → ℝ) (hc : Measurable c) (hc1 : ∀ τ, |c τ| ≤ 1) :
    IsLocalSecondOrderField (fun y => ∫ τ in Icc (0 : ℝ) 1, c τ • v τ y)
      (fun y => ∫ τ in Icc (0 : ℝ) 1, c τ • G τ y) (fun y => ∫ τ in Icc (0 : ℝ) 1, c τ • H τ y) := by
  set μ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) with hμ
  have hmv := hv.measurable_velocity
  have hmG := hv.measurable_gradient
  have hmH := hv.measurable_secondDeriv
  have hmGc : ∀ i : Fin 3, AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector i)) volume :=
    fun i => (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hmG
  have hmHe : ∀ i j : Fin 3,
      AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2 (unitVector i) (unitVector j)) volume :=
    fun i j => ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).comp_aestronglyMeasurable hmH
  have hGsq : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖G τ y‖ₑ ^ 2 < ⊤ :=
    sq_lt_top_of_bound G (fun σ y => matSq (G σ y)) 3 (by norm_num)
      (fun τ y => by unfold matSq; exact norm_sq_le_cols _) hv.gradient_finite
  have hHsq : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖H τ y‖ₑ ^ 2 < ⊤ := by
    refine sq_lt_top_of_bound H
      (fun σ y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H σ y (unitVector i) (unitVector j)‖ ^ 2) 9 (by norm_num)
      (fun τ y => ?_) hv.hessian_finite
    have h1 := norm_sq_le_cols (H τ y)
    have h2 := fun i => norm_sq_le_cols (H τ y (unitVector i))
    simp only [Fin.sum_univ_three] at h1 h2 ⊢
    linarith [h2 0, h2 1, h2 2]
  have hGcsq : ∀ i : Fin 3, ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖G τ y (unitVector i)‖ₑ ^ 2 < ⊤ := fun i =>
    sq_lt_top_of_bound (fun τ y => G τ y (unitVector i)) (fun σ y => matSq (G σ y)) 1 zero_le_one
      (fun τ y => by
        rw [one_mul]
        unfold matSq
        exact Finset.single_le_sum (f := fun i => ‖G τ y (unitVector i)‖ ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ i)) hv.gradient_finite
  have hHesq : ∀ i j : Fin 3,
      ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ‖H τ y (unitVector i) (unitVector j)‖ₑ ^ 2 < ⊤ := fun i j =>
    sq_lt_top_of_bound (fun τ y => H τ y (unitVector i) (unitVector j))
      (fun σ y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H σ y (unitVector i) (unitVector j)‖ ^ 2) 1 zero_le_one
      (fun τ y => by
        rw [one_mul]
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun i => ∑ j : Fin 3, ‖H τ y (unitVector i) (unitVector j)‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i))
        exact Finset.single_le_sum (f := fun j => ‖H τ y (unitVector i) (unitVector j)‖ ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ j)) hv.hessian_finite
  have hGi := ae_integrable_avg G hmG c hc hc1 hGsq
  have hHi := ae_integrable_avg H hmH c hc hc1 hHsq
  have hGcol : ∀ i : Fin 3, ∀ᵐ y ∂(volume : Measure Space),
      (∫ τ in Icc (0 : ℝ) 1, c τ • G τ y) (unitVector i) =
        ∫ τ in Icc (0 : ℝ) 1, c τ • G τ y (unitVector i) := fun i =>
    clm_avg G c (ContinuousLinearMap.apply ℝ Space (unitVector i)) hGi
  have hHent : ∀ i j : Fin 3, ∀ᵐ y ∂(volume : Measure Space),
      (∫ τ in Icc (0 : ℝ) 1, c τ • H τ y) (unitVector i) (unitVector j) =
        ∫ τ in Icc (0 : ℝ) 1, c τ • H τ y (unitVector i) (unitVector j) := fun i j =>
    clm_avg H c ((ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i))) hHi
  have h6 : ∫⁻ τ in Icc (0 : ℝ) 1, (∫⁻ y, ‖v τ y‖ₑ ^ (6 : ℝ)) ^ (1 / (6 : ℝ)) < ⊤ := by
    simpa only [enorm_pow_six] using hv.sixth_power_integrated
  refine ⟨aesm_avg v hmv c hc, aesm_avg G hmG c hc, aesm_avg H hmH c hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := memLp_avg v hmv c hc hc1 (p := 6) (by norm_num) h6
    have e : ENNReal.ofReal 6 = 6 := by norm_num
    rwa [e] at h
  · have h := memLp_avg G hmG c hc hc1 (p := 2) (by norm_num) (rpow_half_lintegral_lt_top_of_sq G hGsq)
    have e : ENNReal.ofReal 2 = ((2 : ℕ) : ℝ≥0∞) := by norm_num
    rw [e] at h
    have hI := (h.integrable_norm_pow two_ne_zero).const_mul 3
    have hcont : Continuous (fun L : Space →L[ℝ] Space => entrySq L) := by
      unfold entrySq
      exact continuous_finsetSum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm).pow 2
    refine hI.mono' (hcont.comp_aestronglyMeasurable (aesm_avg G hmG c hc))
      (Filter.Eventually.of_forall fun y => ?_)
    unfold entrySq
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact sum_cols_sq_le _
  · have h := memLp_avg H hmH c hc hc1 (p := 2) (by norm_num) (rpow_half_lintegral_lt_top_of_sq H hHsq)
    have e : ENNReal.ofReal 2 = ((2 : ℕ) : ℝ≥0∞) := by norm_num
    rw [e] at h
    have hI := (h.integrable_norm_pow two_ne_zero).const_mul 9
    have hcont : Continuous (fun L : Space →L[ℝ] Space →L[ℝ] Space =>
        ∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖ ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm).pow 2
    refine hI.mono' (hcont.comp_aestronglyMeasurable (aesm_avg H hmH c hc))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    set L := ∫ τ in Icc (0 : ℝ) 1, c τ • H τ y
    have h1 := fun i => sum_cols_sq_le (L (unitVector i))
    have h2 := sum_cols_sq_le L
    simp only [Fin.sum_univ_three] at h1 h2 ⊢
    linarith [h1 0, h1 1, h1 2]
  · intro φ hφ j
    obtain ⟨hψc, hψs⟩ := test_deriv φ hφ j
    have hL := swap_test _ hψc hψs v hmv (hloc_six v hmv hv.sixth_power_integrated _ hψs) c hc hc1
    have hR := swap_test φ hφ.1.continuous hφ.2 (fun τ y => G τ y (unitVector j)) (hmGc j)
      (hloc_of_sq _ (hGcsq j) _ hφ.2) c hc hc1
    have hw : ∀ᵐ τ ∂μ, ∫ y, fderiv ℝ φ y (unitVector j) • v τ y = -∫ y, φ y • G τ y (unitVector j) := by
      filter_upwards [ae_restrict_of_ae hv.weak_gradient] with τ hτ
      rw [hτ.2.2 φ hφ j, neg_neg]
    simp only
    rw [hL, integral_congr_ae ((hGcol j).mono fun y hy => by rw [hy]), hR, ← integral_neg]
    refine integral_congr_ae (hw.mono fun τ hτ => ?_)
    simp only
    rw [hτ, smul_neg]
  · intro φ hφ i j
    obtain ⟨hψc, hψs⟩ := test_deriv φ hφ j
    have hL := swap_test _ hψc hψs (fun τ y => G τ y (unitVector i)) (hmGc i)
      (hloc_of_sq _ (hGcsq i) _ hψs) c hc hc1
    have hR := swap_test φ hφ.1.continuous hφ.2 (fun τ y => H τ y (unitVector j) (unitVector i)) (hmHe j i)
      (hloc_of_sq _ (hHesq j i) _ hφ.2) c hc hc1
    have hw : ∀ᵐ τ ∂μ, ∫ y, fderiv ℝ φ y (unitVector j) • G τ y (unitVector i) =
        -∫ y, φ y • H τ y (unitVector j) (unitVector i) := by
      filter_upwards [ae_restrict_of_ae hv.weak_secondDeriv] with τ hτ
      have h := (hτ i).2.2 φ hφ j
      simp only [ContinuousLinearMap.flip_apply] at h
      rw [h, neg_neg]
    simp only
    rw [integral_congr_ae ((hGcol i).mono fun y hy => by rw [hy]), hL,
      integral_congr_ae ((hHent j i).mono fun y hy => by rw [hy]), hR, ← integral_neg]
    refine integral_congr_ae (hw.mono fun τ hτ => ?_)
    simp only
    rw [hτ, smul_neg]
  · set T : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
      ∑ i : Fin 3, (innerSL ℝ (unitVector i)).comp (ContinuousLinearMap.apply ℝ Space (unitVector i)) with hT
    have hT1 : ∀ L : Space →L[ℝ] Space, T L = ∑ i : Fin 3, inner ℝ (L (unitVector i)) (unitVector i) := by
      intro L
      simp [hT, real_inner_comm]
    have hT2 : ∀ L : Space →L[ℝ] Space, T L = ∑ i : Fin 3, (L (unitVector i)) i := by
      intro L
      simp [hT, unitVector, EuclideanSpace.inner_single_left]
    have hN : AEMeasurable (fun z : Space × ℝ => ‖T (G z.2 z.1)‖ₑ) ((volume : Measure Space).prod μ) :=
      (T.continuous.comp_aestronglyMeasurable (aesm_swap G hmG)).enorm
    have hz : ∫⁻ z, ‖T (G z.2 z.1)‖ₑ ∂((volume : Measure Space).prod μ) = 0 := by
      rw [lintegral_prod_symm _ hN]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [ae_restrict_of_ae hv.divergence_free] with τ hτ
      refine (lintegral_congr_ae (hτ.mono fun y hy => ?_)).trans lintegral_zero
      simp only [hT2, hy, enorm_zero]
    have hae := Measure.ae_ae_of_ae_prod ((lintegral_eq_zero_iff' hN).1 hz)
    filter_upwards [clm_avg G c T hGi, hae] with y h1 h2
    rw [← hT1, h1]
    refine integral_eq_zero_of_ae (h2.mono fun τ hτ => ?_)
    simp only [Pi.zero_apply, enorm_eq_zero] at hτ
    simp [hτ]

theorem harmonicSin_eq (ν : ℤ) {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (f : ℝ → Space → β) :
    harmonicSin ν f = fun y => ∫ τ in Icc (0 : ℝ) 1, (-Real.sin (2 * Real.pi * ν * τ)) • f τ y := by
  funext y
  simp only [harmonicSin, neg_smul, integral_neg]

end Internal

theorem harmonic_local (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (ν : ℤ) :
    IsLocalSecondOrderField (harmonicCos ν v) (harmonicCos ν G) (harmonicCos ν H) ∧
      IsLocalSecondOrderField (harmonicSin ν v) (harmonicSin ν G) (harmonicSin ν H) := by
  have hcm : Measurable fun τ : ℝ => Real.cos (2 * Real.pi * ν * τ) := by fun_prop
  have hsm : Measurable fun τ : ℝ => -Real.sin (2 * Real.pi * ν * τ) := by fun_prop
  refine ⟨Internal.local_of_weight v G H hv _ hcm fun τ => Real.abs_cos_le_one _, ?_⟩
  rw [Internal.harmonicSin_eq, Internal.harmonicSin_eq, Internal.harmonicSin_eq]
  exact Internal.local_of_weight v G H hv _ hsm fun τ => by rw [abs_neg]; exact Real.abs_sin_le_one _


end CellCalculus

end CertCell

end Breakdown
