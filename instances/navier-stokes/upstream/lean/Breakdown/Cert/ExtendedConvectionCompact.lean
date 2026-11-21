import Breakdown.Cert.ConvectionCompact
import Breakdown.Cert.ExtendedConvection

open scoped ContDiff ENNReal NNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedConvectionCompact

open Internal.Convection Internal.ConvectionTail
open Internal.ConvectionFirstOrder (IsFirstOrderCoefficient)

theorem fderiv_tail_le_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (y : Space) (hy : R < ‖y‖) :
    ‖fderiv ℝ (W σ) y‖ ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) * ‖(1 + ‖y‖) ^ (-(3 / 2) : ℝ)‖ := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hRpos : 0 < 1 + R := by linarith
  have hsplit : D / (1 + ‖y‖) ^ 2 =
      D * (1 + ‖y‖) ^ (-(1 / 2) : ℝ) * (1 + ‖y‖) ^ (-(3 / 2) : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hpos]
    norm_num
    rw [div_eq_mul_inv]
  have hmono : (1 + ‖y‖) ^ (-(1 / 2) : ℝ) ≤ (1 + R) ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_neg hRpos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hRpos _)
      (Real.rpow_le_rpow hRpos.le (by linarith) (by norm_num))
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  calc ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := hW.bound_one σ y
    _ = D * (1 + ‖y‖) ^ (-(1 / 2) : ℝ) * (1 + ‖y‖) ^ (-(3 / 2) : ℝ) := hsplit
    _ ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) * (1 + ‖y‖) ^ (-(3 / 2) : ℝ) := by
        gcongr

theorem eLpNorm_fderiv_tail_first {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsFirstOrderCoefficient W D) {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (h : X) :
    eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2
        (volume.restrict (Metric.closedBall (0 : Space) R)ᶜ) ≤
      ENNReal.ofReal (D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight *
        (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖)) := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  set μ := volume.restrict (Metric.closedBall (0 : Space) R)ᶜ with hμ
  have hcf : Continuous (fderiv ℝ (W σ)) :=
    (Internal.ConvectionFirstOrder.slice_contDiff hW σ).continuous_fderiv (by norm_num)
  have hf : AEStronglyMeasurable (fderiv ℝ (W σ)) μ := hcf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (velocity h : Space → Space) μ :=
    (Lp.aestronglyMeasurable _).restrict
  have hH : eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 μ ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderiv ℝ (W σ)) 3 μ *
        eLpNorm (velocity h : Space → Space) 6 μ := by
    have := exponentTriple_three_six
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun L x => L x) 1
      (ae_of_all _ fun y => by rw [one_mul]; exact ContinuousLinearMap.le_opNNNorm _ _)
  have hq : 0 ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) := mul_nonneg hD (Real.rpow_nonneg (by linarith) _)
  have hw : eLpNorm (fderiv ℝ (W σ)) 3 μ ≤
      ENNReal.ofReal (D * (1 + R) ^ (-(1 / 2) : ℝ)) *
        eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) 3 μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 3
    refine ae_restrict_of_forall_mem measurableSet_closedBall.compl fun y hy => ?_
    have hy' : R < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    exact fderiv_tail_le_first hW hR σ y hy'
  have hw2 : eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) 3 μ ≤
      ENNReal.ofReal tailWeight := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (le_of_eq ?_)
    exact (ENNReal.ofReal_toReal tailWeight_memLp.eLpNorm_lt_top.ne).symm
  have hv : eLpNorm (velocity h : Space → Space) 6 μ ≤
      ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
  refine hH.trans ?_
  rw [ENNReal.coe_one, one_mul, ENNReal.ofReal_mul (mul_nonneg hq tailWeight_nonneg),
    ENNReal.ofReal_mul hq]
  exact mul_le_mul' (hw.trans (by gcongr)) hv

theorem second_tail_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (h : X) :
    ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ,
        ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) ≤
      ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) *
        ‖h‖ ^ 2) := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hq : 0 ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) := mul_nonneg hD (Real.rpow_nonneg (by linarith) _)
  have hM : 0 ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight *
      (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    have := tailWeight_nonneg
    positivity
  have h1 : ∀ y, ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) =
      ENNReal.ofReal 2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ₑ ^ 2 := fun y => by
    rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm_sq_eq]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← JointRepresentativeInternal.sq_eLpNorm_two]
  calc ENNReal.ofReal 2 * eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2
        (volume.restrict (Metric.closedBall (0 : Space) R)ᶜ) ^ 2
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight *
          (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖)) ^ 2 := by
        gcongr
        exact eLpNorm_fderiv_tail_first hW hR σ h
    _ = ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) *
          ‖h‖ ^ 2) := by
        rw [← ENNReal.ofReal_pow hM, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        have hs := sq_half_rpow hR
        calc 2 * (D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight *
              (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖)) ^ 2
            = 2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 *
                ((1 + R) ^ (-(1 / 2) : ℝ)) ^ 2 * ‖h‖ ^ 2 := by ring
          _ = _ := by rw [hs]; ring

theorem tail_pointwise_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (h : X) (y : Space)
    (hy : y ∈ (Metric.closedBall (0 : Space) R)ᶜ) :
    ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2) +
        ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hRpos : 0 < 1 + R := by linarith
  have hy' : R < ‖y‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  have hWy : ‖W σ y‖ ≤ D / (1 + R) :=
    (hW.bound_zero σ y).trans (div_le_div_of_nonneg_left hD hRpos (by linarith))
  have hq : 0 ≤ ∑ j : Fin 3, ‖(partialX j h : Space → Space) y‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have key := tail_real hR
    (norm_add_le (∑ j : Fin 3, (W σ y) j • (partialX j h : Space → Space) y)
      (fderiv ℝ (W σ) y ((velocity h : Space → Space) y))) (norm_nonneg _) hq (norm_nonneg _) hWy
    (sum_smul_sq_le (W σ y) fun j => (partialX j h : Space → Space) y)
  have c1 : 0 ≤ 6 * D ^ 2 / (1 + R) := div_nonneg (by positivity) hRpos.le
  rw [sliceConvection_apply, ← ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _,
    ← ENNReal.ofReal_mul c1,
    ← ENNReal.ofReal_add (mul_nonneg c1 hq) (mul_nonneg (by norm_num) (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal key

theorem slice_tail_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (h : X) :
    ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (tailConst D / (1 + R) * ‖h‖ ^ 2) := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hRpos : 0 < 1 + R := by linarith
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
      ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2))
        (volume.restrict (Metric.closedBall (0 : Space) R)ᶜ) :=
    (Finset.aemeasurable_fun_sum _ fun j _ =>
      aemeasurable_partial_sq h j _ Measure.restrict_le_self).const_mul _
  have c1 : 0 ≤ 6 * D ^ 2 / (1 + R) := div_nonneg (by positivity) hRpos.le
  have c2 : 0 ≤ 2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) * ‖h‖ ^ 2 :=
    mul_nonneg (div_nonneg (by positivity) hRpos.le) (sq_nonneg _)
  calc ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2)
      ≤ ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, (ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2) +
        ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2)) :=
      lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_closedBall.compl
        (tail_pointwise_first hW hR σ h))
    _ = (∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) +
        ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ,
          ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) :=
      lintegral_add_left' hmeas
        (fun y => ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2))
    _ ≤ (∫⁻ y, ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) +
        ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) *
          ‖h‖ ^ 2) :=
      add_le_add (setLIntegral_le_lintegral _ _) (second_tail_first hW hR σ h)
    _ = ENNReal.ofReal (6 * D ^ 2 / (1 + R)) * ENNReal.ofReal (‖h‖ ^ 2) +
        ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) *
          ‖h‖ ^ 2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' _ fun j _ => aemeasurable_partial_sq h j _ le_rfl,
        sum_partial_integral]
    _ = ENNReal.ofReal (tailConst D / (1 + R) * ‖h‖ ^ 2) := by
      rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_add (mul_nonneg c1 (sq_nonneg _)) c2]
      congr 1
      unfold tailConst
      field_simp

theorem ball_pointwise_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    (σ : ℝ) (h : X) (y : Space) :
    ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) *
      (ENNReal.ofReal (‖(velocity h : Space → Space) y‖ ^ 2) +
        ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) := by
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hWy : ‖W σ y‖ ≤ D :=
    (hW.bound_zero σ y).trans (div_le_self hD (by linarith [norm_nonneg y]))
  have hgy : ‖fderiv ℝ (W σ) y‖ ≤ D := by
    refine (hW.bound_one σ y).trans (div_le_self hD ?_)
    nlinarith [norm_nonneg y]
  have hq : 0 ≤ ∑ j : Fin 3, ‖(partialX j h : Space → Space) y‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have key := ball_real hD
    (norm_add_le (∑ j : Fin 3, (W σ y) j • (partialX j h : Space → Space) y)
      (fderiv ℝ (W σ) y ((velocity h : Space → Space) y))) (norm_nonneg _) hq (norm_nonneg _) hWy
    (sum_smul_sq_le (W σ y) fun j => (partialX j h : Space → Space) y) (norm_nonneg _) hgy
    (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have c1 : 0 ≤ 6 * D ^ 2 := by positivity
  rw [sliceConvection_apply, ← ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _,
    ← ENNReal.ofReal_add (sq_nonneg _) hq, ← ENNReal.ofReal_mul c1]
  exact ENNReal.ofReal_le_ofReal key

theorem slice_ball_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    (R σ : ℝ) (h : X) (a : Space → Space) (b : Fin 3 → Space → Space)
    (ha : a =ᵐ[volume] (velocity h : Space → Space))
    (hb : ∀ j, b j =ᵐ[volume] (partialX j h : Space → Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2) *
        ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2))
          + ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖b j y‖ ^ 2)) := by
  have hb' : ∀ᵐ y ∂volume, ∀ j, b j y = (partialX j h : Space → Space) y := ae_all_iff.2 hb
  have hae : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R)),
      ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) *
        (ENNReal.ofReal (‖a y‖ ^ 2) + ∑ j : Fin 3, ENNReal.ofReal (‖b j y‖ ^ 2)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ha, hb'] with y hy1 hy2
    simp only [hy1, hy2]
    exact ball_pointwise_first hW σ h y
  have hma : AEMeasurable (fun y => ENNReal.ofReal (‖a y‖ ^ 2))
      (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    (((Lp.aestronglyMeasurable (velocity h)).congr ha.symm).restrict.norm.aemeasurable.pow_const
      2).ennreal_ofReal
  have hmb : ∀ j, AEMeasurable (fun y => ENNReal.ofReal (‖b j y‖ ^ 2))
      (volume.restrict (Metric.closedBall (0 : Space) R)) := fun j =>
    (((Lp.aestronglyMeasurable (partialX j h)).congr
      (hb j).symm).restrict.norm.aemeasurable.pow_const 2).ennreal_ofReal
  refine (lintegral_mono_ae hae).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hma,
    lintegral_finsetSum' _ fun j _ => hmb j]

theorem slice_split_first {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    {R : ℝ} (hR : 0 ≤ R) (σ : ℝ) (h : X) (a : Space → Space) (b : Fin 3 → Space → Space)
    (ha : a =ᵐ[volume] (velocity h : Space → Space))
    (hb : ∀ j, b j =ᵐ[volume] (partialX j h : Space → Space)) :
    ∫⁻ y, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2) *
        ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2))
          + ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖b j y‖ ^ 2)) +
      ENNReal.ofReal (tailConst D / (1 + R)) * ENNReal.ofReal (‖h‖ ^ 2) := by
  rw [← lintegral_add_compl _ (measurableSet_closedBall (x := (0 : Space)) (ε := R)),
    ← ENNReal.ofReal_mul (div_nonneg (tailConst_nonneg D) (by linarith))]
  exact add_le_add (slice_ball_first hW R σ h a b ha hb) (slice_tail_first hW hR σ h)

theorem conv_le_first (h2 : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) (u u' : XX) :
    ENNReal.ofReal (‖convection d.toCertificateData q u - convection d.toCertificateData q u'‖ ^ 2) ≤
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖sliceConvection (d.profile q σ)
        (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
          - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) y‖ ^ 2) := by
  have hW := Internal.ConvectionFirstOrder.isFirstOrderCoefficient_profile hd hq
  have hc : ConvectionSpec d.toCertificateData q (convection d.toCertificateData q) := by
    obtain ⟨T, hT⟩ := (h2 d hd q hq).1
    rw [convection_eq_of_spec hT]
    exact hT
  have hsub : convection d.toCertificateData q u - convection d.toCertificateData q u' =
      convection d.toCertificateData q (u - u') := (map_sub _ u u').symm
  refine (congrArg (fun z : HH => ENNReal.ofReal (‖z‖ ^ 2)) hsub).trans_le
    (lp_norm_le_of_ae _ _ ?_)
  have e1 := (ae_coe_iff _).1 (hc (u - u'))
  have e2 := (ae_coe_iff _).1 (Lp.coeFn_sub u u')
  filter_upwards [e1, e2] with σ h1 h3
  have hper : d.profile q (circleRep (σ : TimeCircle)) = d.profile q σ :=
    eq_of_coe_eq (periodic_of_isTimePeriodic hW.periodic) (coe_circleRep _)
  have h4 : gradPart (((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle)) =
      gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
        - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle)) :=
    (congrArg gradPart h3).trans (map_sub gradPart _ _)
  refine (congrArg (fun z : HBar => ‖z‖ₑ ^ 2) h1).trans_le ?_
  refine (congrArg (fun F => ‖solField F‖ₑ ^ 2) (congrArg₂ sliceConvection hper h4)).trans_le ?_
  exact enorm_solField_sq_le (Internal.ConvectionFirstOrder.slice_bound hW σ _).1

theorem core_bound_first (h2 : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) {R : ℝ} (hR : 0 ≤ R)
    {u u' : XX} {v v' : VelField} {G G' : GradField} {H H' : SecondField}
    (hr : IsReadingOf u v G H) (hr' : IsReadingOf u' v' G' H') :
    ‖convection d.toCertificateData q u - convection d.toCertificateData q u'‖ ≤
      3 * d.decay * (periodBallNorm R (fun σ y => v σ y - v' σ y)
        + ∑ j : Fin 3, periodBallNorm R (fun σ y => gradColumn G j σ y - gradColumn G' j σ y))
      + Real.sqrt (tailConst d.decay / (1 + R)) * ‖gradCLM u - gradCLM u'‖ := by
  have hW := Internal.ConvectionFirstOrder.isFirstOrderCoefficient_profile hd hq
  have hD := Internal.ConvectionFirstOrder.coefficient_nonneg hW
  have hK : 0 ≤ tailConst d.decay / (1 + R) := div_nonneg (tailConst_nonneg _) (by linarith)
  have hid := reading_diff hr hr'
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2 - v' z.1 z.2) volume :=
    hr.measurable_velocity.sub hr'.measurable_velocity
  have hgm : ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => gradColumn G j z.1 z.2 - gradColumn G' j z.1 z.2) volume := fun j =>
    (apply_aesm hr.measurable_gradient aestronglyMeasurable_const).sub
      (apply_aesm hr'.measurable_gradient aestronglyMeasurable_const)
  have hPm := aemeasurable_ball (f := fun σ y => v σ y - v' σ y) hvm R
  have hQm := fun j =>
    aemeasurable_ball (f := fun σ y => gradColumn G j σ y - gradColumn G' j σ y) (hgm j) R
  have hper : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖sliceConvection (d.profile q σ)
      (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
        - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) y‖ ^ 2) ≤
        ENNReal.ofReal (6 * d.decay ^ 2) *
          ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖v σ y - v' σ y‖ ^ 2)) +
            ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R,
              ENNReal.ofReal (‖gradColumn G j σ y - gradColumn G' j σ y‖ ^ 2)) +
        ENNReal.ofReal (tailConst d.decay / (1 + R)) *
          ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
            - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
    filter_upwards [hid] with σ hσ
    exact slice_split_first hW hR σ _ (fun y => v σ y - v' σ y)
      (fun j y => gradColumn G j σ y - gradColumn G' j σ y) hσ.1 hσ.2
  have hsum := integral_split (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (c := ENNReal.ofReal (6 * d.decay ^ 2)) ENNReal.ofReal_ne_top
    (fun σ => ENNReal.ofReal (tailConst d.decay / (1 + R)) *
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
        - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) hPm hQm
  have hT := time_integral_le u u' (c := ENNReal.ofReal (tailConst d.decay / (1 + R)))
    ENNReal.ofReal_ne_top (g := fun σ => ENNReal.ofReal (tailConst d.decay / (1 + R)) *
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
        - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2))
    (ae_of_all _ fun σ => le_rfl)
  have hfinP : periodBallLIntegral R (fun σ y => ‖v σ y - v' σ y‖ ^ 2) ≠ ⊤ := by
    obtain ⟨c, hc, hcb⟩ := ball_velocity_le R
    exact ((time_integral_le u u' hc (hid.mono fun σ hσ => hcb _ _ hσ.1)).trans_lt
      (ENNReal.mul_lt_top hc.lt_top ENNReal.ofReal_lt_top)).ne
  have hfinQ : ∀ j : Fin 3, periodBallLIntegral R
      (fun σ y => ‖gradColumn G j σ y - gradColumn G' j σ y‖ ^ 2) ≠ ⊤ := fun j =>
    ((time_integral_le u u' ENNReal.one_ne_top
      (hid.mono fun σ hσ => column_ball_le R _ j _ (hσ.2 j))).trans_lt
        (ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top)).ne
  have key := (conv_le_first h2 hd hq u u').trans ((lintegral_mono_ae (ae_restrict_of_ae hper)).trans
    (hsum.le.trans (add_le_add le_rfl hT)))
  exact final_bound (P := periodBallLIntegral R (fun σ y => ‖v σ y - v' σ y‖ ^ 2))
    (Q := fun j => periodBallLIntegral R
      (fun σ y => ‖gradColumn G j σ y - gradColumn G' j σ y‖ ^ 2))
    (norm_nonneg _) hD hK (norm_nonneg _) hfinP hfinQ key

theorem local_tail_bound_first (h2 : ExtendedConvectionHolds) {k : ℕ}
    (d : ExtendedCertificateData k) (hd : IsExtendedCertificate d) (q : Fin k → ℝ)
    (hq : q ∈ d.params) :
    ∀ ε > 0, ∃ R > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ u u' : XX,
      ‖convection d.toCertificateData q u - convection d.toCertificateData q u'‖ ≤
        A * (periodBallNorm R (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y)
          + ∑ j : Fin 3, periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ y
            - gradColumn (readingOf u').2.1 j σ y))
        + ε * (‖gradCLM u‖ + ‖gradCLM u'‖) := by
  intro ε hε
  have hT := tailConst_nonneg d.decay
  have hD : 0 ≤ d.decay := Internal.ConvectionFirstOrder.coefficient_nonneg
    (Internal.ConvectionFirstOrder.isFirstOrderCoefficient_profile hd hq)
  refine ⟨tailConst d.decay / ε ^ 2 + 1, by positivity, 3 * d.decay, by positivity, fun u u' => ?_⟩
  have hK := sqrt_tail_le hε hT
  have hb := core_bound_first h2 hd hq (R := tailConst d.decay / ε ^ 2 + 1) (by positivity)
    (reading_spec u) (reading_spec u')
  exact hb.trans (add_le_add le_rfl (mul_le_mul hK (norm_sub_le _ _) (norm_nonneg _) hε.le))

theorem fundamental_image_general (h1 : LocalCompactnessHolds) (h3 : FreeInvHolds)
    (T : XX →L[ℝ] HH) {P : ℝ} (hP : 0 < P)
    (hb : ∀ ε > 0, ∃ R > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ u u' : XX,
      ‖T u - T u'‖ ≤
        A * (periodBallNorm R (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y)
          + ∑ j : Fin 3, periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ y
            - gradColumn (readingOf u').2.1 j σ y))
        + ε * (‖gradCLM u‖ + ‖gradCLM u'‖))
    (f : ℕ → HH) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T (freeInv P (f (φ m))) - T (freeInv P (f (φ n)))‖ < ε := by
  have hmem : ∀ n, (fun _ : ℕ => P) n ∈ Set.Icc P P := fun _ => ⟨le_rfl, le_rfl⟩
  have hC : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := ⟨1, hf⟩
  have hx := h1 P P hP (fun _ => P) f hmem hC
  obtain ⟨φ, hφ, hloc⟩ := hx
  refine ⟨φ, hφ, ?_⟩
  exact Internal.ConvectionCompact.abstract_fundamental T
    (fun u => ‖gradCLM u‖)
    (fun R u u' => periodBallNorm R (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y))
    (fun R j u u' => periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ y
      - gradColumn (readingOf u').2.1 j σ y))
    (fun n => freeInv P (f (φ n)))
    (fun n => le_trans (Internal.ConvectionCompact.norm_gradCLM_freeInv_le h3 hP _)
      (by linarith [hf (φ n)]))
    hloc hb

end Internal.ExtendedConvectionCompact

theorem extendedConvectionCompactHolds_of (h1 : LocalCompactnessHolds)
    (h2 : ExtendedConvectionHolds) (h3 : FreeInvHolds) : ExtendedConvectionCompactHolds :=
  fun d hd q hq =>
    Internal.ConvectionCompact.isCompactOperator_of_fundamental_subseq
      ((convection d.toCertificateData q).comp (freeInv (d.period q)))
      (Internal.ExtendedConvectionCompact.fundamental_image_general h1 h3
        (convection d.toCertificateData q) (hd.period_pos q hq)
        (Internal.ExtendedConvectionCompact.local_tail_bound_first h2 d hd q hq))

end Breakdown.Cert
