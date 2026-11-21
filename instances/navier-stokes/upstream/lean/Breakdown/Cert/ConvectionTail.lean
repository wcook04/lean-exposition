import Breakdown.Cert.Nodes
import Breakdown.Cert.Convection
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.ReadingExists
import Breakdown.Cert.PeriodIntegral

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ConvectionTail

open Internal.Convection

def tailWeight : ℝ := (eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) 3 volume).toReal

def tailConst (D : ℝ) : ℝ := 6 * D ^ 2 + 2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2

theorem tailWeight_memLp : MemLp (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) 3 volume := by
  have hm : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
  have hi := integrable_one_add_norm (E := Space) (μ := volume) (r := 9 / 2) (by simp; norm_num)
  refine hi.congr (ae_of_all _ fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  simp only
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _), ← Real.rpow_mul hpos.le]
  norm_num

theorem tailWeight_nonneg : 0 ≤ tailWeight := ENNReal.toReal_nonneg

theorem tailConst_nonneg (D : ℝ) : 0 ≤ tailConst D := by
  unfold tailConst
  positivity

theorem sq_half_rpow {R : ℝ} (hR : 0 ≤ R) : ((1 + R) ^ (-(1 / 2) : ℝ)) ^ 2 = 1 / (1 + R) := by
  have hpos : 0 < 1 + R := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num
  rw [Real.rpow_neg_one]

theorem fderiv_tail_le {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ} (hR : 0 ≤ R)
    (σ : ℝ) (y : Space) (hy : R < ‖y‖) :
    ‖fderiv ℝ (W σ) y‖ ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) * ‖(1 + ‖y‖) ^ (-(3 / 2) : ℝ)‖ := by
  have hD := coefficient_nonneg hW
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

theorem eLpNorm_fderiv_tail {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ}
    (hR : 0 ≤ R) (σ : ℝ) (h : X) :
    eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2
        (volume.restrict (Metric.closedBall (0 : Space) R)ᶜ) ≤
      ENNReal.ofReal (D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight * (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖)) := by
  have hD := coefficient_nonneg hW
  set μ := volume.restrict (Metric.closedBall (0 : Space) R)ᶜ with hμ
  have hcf : Continuous (fderiv ℝ (W σ)) := (slice_contDiff hW σ).continuous_fderiv (by norm_num)
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
    exact fderiv_tail_le hW hR σ y hy'
  have hw2 : eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-(3 / 2) : ℝ)) 3 μ ≤ ENNReal.ofReal tailWeight := by
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

theorem second_tail {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ} (hR : 0 ≤ R)
    (σ : ℝ) (h : X) :
    ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ,
        ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) ≤
      ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) * ‖h‖ ^ 2) := by
  have hD := coefficient_nonneg hW
  have hq : 0 ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) := mul_nonneg hD (Real.rpow_nonneg (by linarith) _)
  have hM : 0 ≤ D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight * (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
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
        exact eLpNorm_fderiv_tail hW hR σ h
    _ = ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) * ‖h‖ ^ 2) := by
        rw [← ENNReal.ofReal_pow hM, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        have hs := sq_half_rpow hR
        calc 2 * (D * (1 + R) ^ (-(1 / 2) : ℝ) * tailWeight * (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖)) ^ 2
            = 2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 * ((1 + R) ^ (-(1 / 2) : ℝ)) ^ 2
              * ‖h‖ ^ 2 := by ring
          _ = _ := by rw [hs]; ring

theorem ofReal_integral_sq (f : L2R) :
    ∫⁻ y, ENNReal.ofReal (‖(f : Space → Space) y‖ ^ 2) = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [ofReal_norm_sq_Lp f]
  exact lintegral_congr fun y => ofReal_norm_sq_eq _

theorem sum_partial_integral (h : X) :
    ∑ j : Fin 3, ∫⁻ y, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2) =
      ENNReal.ofReal (‖h‖ ^ 2) := by
  simp_rw [ofReal_integral_sq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _),
    Internal.SliceFields.sum_norm_partialX_sq h]

theorem aemeasurable_partial_sq (h : X) (j : Fin 3) (μ : Measure Space) (hμ : μ ≤ volume) :
    AEMeasurable (fun y => ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) μ :=
  (((Lp.aestronglyMeasurable (partialX j h)).mono_measure hμ).norm.aemeasurable.pow_const
    2).ennreal_ofReal

theorem sum_smul_sq_le (w : Space) (x : Fin 3 → Space) :
    ‖∑ j : Fin 3, w j • x j‖ ^ 2 ≤ 3 * ‖w‖ ^ 2 * ∑ j : Fin 3, ‖x j‖ ^ 2 := by
  have hb : ‖∑ j : Fin 3, w j • x j‖ ≤ ∑ j : Fin 3, ‖w‖ * ‖x j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le _ _) (norm_nonneg _)
  have h0 : 0 ≤ ‖∑ j : Fin 3, w j • x j‖ := norm_nonneg _
  have hb2 : ‖∑ j : Fin 3, w j • x j‖ ≤ ‖w‖ * ‖x 0‖ + ‖w‖ * ‖x 1‖ + ‖w‖ * ‖x 2‖ :=
    hb.trans_eq (Fin.sum_univ_three _)
  rw [Fin.sum_univ_three (fun j => ‖x j‖ ^ 2)]
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  have ha : 0 ≤ ‖x 0‖ := norm_nonneg _
  have hb' : 0 ≤ ‖x 1‖ := norm_nonneg _
  have hc : 0 ≤ ‖x 2‖ := norm_nonneg _
  have hs : (‖w‖ * ‖x 0‖ + ‖w‖ * ‖x 1‖ + ‖w‖ * ‖x 2‖) ^ 2 ≤
      3 * ‖w‖ ^ 2 * (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖), sq_nonneg (‖x 1‖ - ‖x 2‖), sq_nonneg (‖x 0‖ - ‖x 2‖),
      sq_nonneg ‖w‖]
  exact (pow_le_pow_left₀ h0 hb2 2).trans hs

theorem tail_real {n s1 s2 q w D R : ℝ} (hR : 0 ≤ R) (hn : n ≤ s1 + s2) (hn0 : 0 ≤ n)
    (hq : 0 ≤ q) (hw0 : 0 ≤ w) (hw : w ≤ D / (1 + R)) (hf : s1 ^ 2 ≤ 3 * w ^ 2 * q) :
    n ^ 2 ≤ 6 * D ^ 2 / (1 + R) * q + 2 * s2 ^ 2 := by
  have hRpos : 0 < 1 + R := by linarith
  have h1 : w ^ 2 ≤ (D / (1 + R)) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have h2 : (D / (1 + R)) ^ 2 ≤ D ^ 2 / (1 + R) := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg D) hRpos (by nlinarith)
  have e2 : s1 ^ 2 ≤ 3 * (D ^ 2 / (1 + R)) * q :=
    hf.trans (mul_le_mul_of_nonneg_right (by linarith) hq)
  have e3 : 6 * D ^ 2 / (1 + R) * q = 2 * (3 * (D ^ 2 / (1 + R)) * q) := by ring
  have e1 : n ^ 2 ≤ (s1 + s2) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  nlinarith [sq_nonneg (s1 - s2)]

theorem sliceConvection_apply (W : Space → Space) (h : X) (y : Space) :
    sliceConvection W h y = ∑ j : Fin 3, (W y) j • (partialX j h : Space → Space) y +
      fderiv ℝ W y ((velocity h : Space → Space) y) := rfl

theorem tail_pointwise {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ} (hR : 0 ≤ R)
    (σ : ℝ) (h : X) (y : Space) (hy : y ∈ (Metric.closedBall (0 : Space) R)ᶜ) :
    ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2) +
        ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) := by
  have hD := coefficient_nonneg hW
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
    ← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_add (mul_nonneg c1 hq) (mul_nonneg (by norm_num) (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal key

theorem slice_tail {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ} (hR : 0 ≤ R)
    (σ : ℝ) (h : X) :
    ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (tailConst D / (1 + R) * ‖h‖ ^ 2) := by
  have hD := coefficient_nonneg hW
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
        (tail_pointwise hW hR σ h))
    _ = (∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ, ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) +
        ∫⁻ y in (Metric.closedBall (0 : Space) R)ᶜ,
          ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2) :=
      lintegral_add_left' hmeas
        (fun y => ENNReal.ofReal (2 * ‖fderiv ℝ (W σ) y ((velocity h : Space → Space) y)‖ ^ 2))
    _ ≤ (∫⁻ y, ENNReal.ofReal (6 * D ^ 2 / (1 + R)) *
          ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) +
        ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) * ‖h‖ ^ 2) :=
      add_le_add (setLIntegral_le_lintegral _ _) (second_tail hW hR σ h)
    _ = ENNReal.ofReal (6 * D ^ 2 / (1 + R)) * ENNReal.ofReal (‖h‖ ^ 2) +
        ENNReal.ofReal (2 * (D * tailWeight * ‖(velocity : X →L[ℝ] L6R)‖) ^ 2 / (1 + R) * ‖h‖ ^ 2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum' _ fun j _ => aemeasurable_partial_sq h j _ le_rfl, sum_partial_integral]
    _ = ENNReal.ofReal (tailConst D / (1 + R) * ‖h‖ ^ 2) := by
      rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_add (mul_nonneg c1 (sq_nonneg _)) c2]
      congr 1
      unfold tailConst
      field_simp

theorem ball_real {n s1 s2 q v w g D : ℝ} (hD : 0 ≤ D) (hn : n ≤ s1 + s2) (hn0 : 0 ≤ n)
    (hq : 0 ≤ q) (hw0 : 0 ≤ w) (hw : w ≤ D) (hf : s1 ^ 2 ≤ 3 * w ^ 2 * q) (_hg0 : 0 ≤ g) (hg : g ≤ D)
    (hv : 0 ≤ v) (h2 : s2 ≤ g * v) (hs2 : 0 ≤ s2) : n ^ 2 ≤ 6 * D ^ 2 * (v ^ 2 + q) := by
  have e1 : n ^ 2 ≤ (s1 + s2) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  have e2 : s1 ^ 2 ≤ 3 * D ^ 2 * q :=
    hf.trans (mul_le_mul_of_nonneg_right (by nlinarith) hq)
  have e3 : s2 ≤ D * v := h2.trans (mul_le_mul_of_nonneg_right hg hv)
  have e4 : (s1 + s2) ^ 2 ≤ 2 * s1 ^ 2 + 2 * s2 ^ 2 := by nlinarith [sq_nonneg (s1 - s2)]
  have e5 : s2 ^ 2 ≤ (D * v) ^ 2 := pow_le_pow_left₀ hs2 e3 2
  nlinarith [sq_nonneg (D * v), mul_nonneg (sq_nonneg D) (sq_nonneg v)]

theorem ball_pointwise {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (σ : ℝ) (h : X)
    (y : Space) :
    ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) *
      (ENNReal.ofReal (‖(velocity h : Space → Space) y‖ ^ 2) +
        ∑ j : Fin 3, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2)) := by
  have hD := coefficient_nonneg hW
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

theorem slice_ball {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) (R σ : ℝ) (h : X)
    (a : Space → Space) (b : Fin 3 → Space → Space) (ha : a =ᵐ[volume] (velocity h : Space → Space))
    (hb : ∀ j, b j =ᵐ[volume] (partialX j h : Space → Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2) * ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2))
        + ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖b j y‖ ^ 2)) := by
  have hb' : ∀ᵐ y ∂volume, ∀ j, b j y = (partialX j h : Space → Space) y := ae_all_iff.2 hb
  have hae : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R)),
      ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) *
        (ENNReal.ofReal (‖a y‖ ^ 2) + ∑ j : Fin 3, ENNReal.ofReal (‖b j y‖ ^ 2)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ha, hb'] with y hy1 hy2
    simp only [hy1, hy2]
    exact ball_pointwise hW σ h y
  have hma : AEMeasurable (fun y => ENNReal.ofReal (‖a y‖ ^ 2))
      (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    (((Lp.aestronglyMeasurable (velocity h)).congr ha.symm).restrict.norm.aemeasurable.pow_const
      2).ennreal_ofReal
  have hmb : ∀ j, AEMeasurable (fun y => ENNReal.ofReal (‖b j y‖ ^ 2))
      (volume.restrict (Metric.closedBall (0 : Space) R)) := fun j =>
    (((Lp.aestronglyMeasurable (partialX j h)).congr (hb j).symm).restrict.norm.aemeasurable.pow_const
      2).ennreal_ofReal
  refine (lintegral_mono_ae hae).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hma,
    lintegral_finsetSum' _ fun j _ => hmb j]

theorem slice_split {W : ℝ → Space → Space} {D : ℝ} (hW : IsCoefficient W D) {R : ℝ} (hR : 0 ≤ R)
    (σ : ℝ) (h : X) (a : Space → Space) (b : Fin 3 → Space → Space)
    (ha : a =ᵐ[volume] (velocity h : Space → Space))
    (hb : ∀ j, b j =ᵐ[volume] (partialX j h : Space → Space)) :
    ∫⁻ y, ENNReal.ofReal (‖sliceConvection (W σ) h y‖ ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2) * ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2))
        + ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖b j y‖ ^ 2)) +
      ENNReal.ofReal (tailConst D / (1 + R)) * ENNReal.ofReal (‖h‖ ^ 2) := by
  rw [← lintegral_add_compl _ (measurableSet_closedBall (x := (0 : Space)) (ε := R)),
    ← ENNReal.ofReal_mul (div_nonneg (tailConst_nonneg D) (by linarith))]
  exact add_le_add (slice_ball hW R σ h a b ha hb) (slice_tail hW hR σ h)

theorem enorm_solField_sq_le {F : Space → Space} (hF : MemLp F 2 volume) :
    ‖solField F‖ₑ ^ 2 ≤ ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) := by
  have h0 : solField F = solProj (hF.toLp F) := by
    unfold solField
    rw [toLpOrZero, dif_pos hF]
  have h1 : ‖solField F‖ ≤ ‖hF.toLp F‖ := by
    rw [h0]
    exact norm_solProj_le _
  calc ‖solField F‖ₑ ^ 2 = ENNReal.ofReal (‖solField F‖ ^ 2) := (ofReal_norm_sq_eq _).symm
    _ ≤ ENNReal.ofReal (‖hF.toLp F‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    _ = ∫⁻ y, ENNReal.ofReal (‖(hF.toLp F : Space → Space) y‖ ^ 2) := (ofReal_integral_sq _).symm
    _ = ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) :=
      lintegral_congr_ae (hF.coeFn_toLp.mono fun y hy => by simp only [hy])

theorem lintegral_sub_sq {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
    (f g : Lp F 2 μ) (a b : α → F) (ha : (f : α → F) =ᵐ[μ] a) (hb : (g : α → F) =ᵐ[μ] b) :
    ∫⁻ t, ENNReal.ofReal (‖a t - b t‖ ^ 2) ∂μ = ENNReal.ofReal (‖f - g‖ ^ 2) := by
  rw [ofReal_norm_sq_Lp (f - g)]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g, ha, hb] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  exact ofReal_norm_sq_eq _

theorem lp_norm_le_of_ae {E : Type*} [NormedAddCommGroup E] (f : Lp (α := TimeCircle) E 2)
    (B : ℝ → ℝ≥0∞) (h : ∀ᵐ σ : ℝ, ‖(f : TimeCircle → E) (σ : TimeCircle)‖ₑ ^ 2 ≤ B σ) :
    ENNReal.ofReal (‖f‖ ^ 2) ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, B σ := by
  have hmeas : AEMeasurable (fun t : TimeCircle => ‖(f : TimeCircle → E) t‖ₑ ^ 2) volume :=
    (Lp.aestronglyMeasurable _).enorm.pow_const 2
  rw [ofReal_norm_sq_Lp, ← lintegral_Icc_coe _ hmeas]
  exact lintegral_mono_ae (ae_restrict_of_ae h)

theorem conv_le (h2 : ConvectionHolds) {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) (u u' : XX) :
    ENNReal.ofReal (‖convection d p u - convection d p u'‖ ^ 2) ≤
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖sliceConvection (d.profile p σ)
        (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) y‖ ^ 2) := by
  have hW := isCoefficient_profile hd hp
  have hc : ConvectionSpec d p (convection d p) := by
    obtain ⟨T, hT⟩ := (h2 d hd p hp).1
    rw [convection_eq_of_spec hT]
    exact hT
  have hsub : convection d p u - convection d p u' = convection d p (u - u') := (map_sub _ u u').symm
  refine (congrArg (fun z : HH => ENNReal.ofReal (‖z‖ ^ 2)) hsub).trans_le (lp_norm_le_of_ae _ _ ?_)
  have e1 := (ae_coe_iff _).1 (hc (u - u'))
  have e2 := (ae_coe_iff _).1 (Lp.coeFn_sub u u')
  filter_upwards [e1, e2] with σ h1 h3
  have hper : d.profile p (circleRep (σ : TimeCircle)) = d.profile p σ :=
    eq_of_coe_eq (periodic_of_isTimePeriodic hW.periodic) (coe_circleRep _)
  have h4 : gradPart (((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle)) =
      gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle)) :=
    (congrArg gradPart h3).trans (map_sub gradPart _ _)
  refine (congrArg (fun z : HBar => ‖z‖ₑ ^ 2) h1).trans_le ?_
  refine (congrArg (fun F => ‖solField F‖ₑ ^ 2) (congrArg₂ sliceConvection hper h4)).trans_le ?_
  exact enorm_solField_sq_le (slice_bound hW σ _).1

set_option maxHeartbeats 800000 in
theorem time_integral_le (u u' : XX) {c : ℝ≥0∞} (hc : c ≠ ⊤) {g : ℝ → ℝ≥0∞}
    (hg : ∀ᵐ σ : ℝ, g σ ≤ c * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
      - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, g σ ≤ c * ENNReal.ofReal (‖gradCLM u - gradCLM u'‖ ^ 2) := by
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal
      (‖gradPart ((u : TimeCircle → XBar) t) - gradPart ((u' : TimeCircle → XBar) t)‖ ^ 2)) volume :=
    (((gradPart.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      (gradPart.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u'))).norm.aemeasurable.pow_const
        2).ennreal_ofReal
  have hu : ((gradCLM u : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u
  have hu' : ((gradCLM u' : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u' : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u'
  have heq := lintegral_sub_sq (gradCLM u) (gradCLM u') _ _ hu hu'
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, g σ
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, c * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
          - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := lintegral_mono_ae (ae_restrict_of_ae hg)
    _ = c * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
          - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := lintegral_const_mul' _ _ hc
    _ = c * ENNReal.ofReal (‖gradCLM u - gradCLM u'‖ ^ 2) := by
      rw [← heq]
      exact congrArg (fun z => c * z) (lintegral_Icc_coe _ hmeas)

theorem aemeasurable_ball {f : ℝ → Space → Space}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (R : ℝ) :
    AEMeasurable (fun σ => ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖f σ y‖ ^ 2))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖f z.1 z.2‖ ^ 2))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact (hf.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have h2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖f z.1 z.2‖ ^ 2))
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod
        ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) R))) := by
    rw [Measure.prod_restrict]
    exact h1.restrict
  exact h2.lintegral_prod_right'

theorem ball_velocity_le (R : ℝ) : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (h : X) (a : Space → Space),
    a =ᵐ[volume] (velocity h : Space → Space) →
      ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2) ≤
        c * ENNReal.ofReal (‖h‖ ^ 2) := by
  have hfin : (volume.restrict (Metric.closedBall (0 : Space) R)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top.ne
  have hmt : (volume.restrict (Metric.closedBall (0 : Space) R)) Set.univ ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin
  refine ⟨(ENNReal.ofReal ‖(velocity : X →L[ℝ] L6R)‖ *
      (volume.restrict (Metric.closedBall (0 : Space) R)) Set.univ ^
        (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2,
    ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt), fun h a ha => ?_⟩
  have ham : AEStronglyMeasurable a (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    ((Lp.aestronglyMeasurable (velocity h)).congr ha.symm).restrict
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6) (by norm_num) ham
  have h2 : eLpNorm a 6 (volume.restrict (Metric.closedBall (0 : Space) R)) ≤
      ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [eLpNorm_congr_ae ha, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
  have h3 : ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖a y‖ ^ 2) =
      eLpNorm a 2 (volume.restrict (Metric.closedBall (0 : Space) R)) ^ 2 := by
    rw [JointRepresentativeInternal.sq_eLpNorm_two]
    exact lintegral_congr fun y => ofReal_norm_sq_eq _
  rw [h3]
  calc eLpNorm a 2 (volume.restrict (Metric.closedBall (0 : Space) R)) ^ 2
      ≤ (ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) *
          (volume.restrict (Metric.closedBall (0 : Space) R)) Set.univ ^
            (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 := by
        gcongr
        exact h1.trans (by gcongr)
    _ = _ := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
        ring

theorem column_ball_le (R : ℝ) (h : X) (j : Fin 3) (b : Space → Space)
    (hb : b =ᵐ[volume] (partialX j h : Space → Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖b y‖ ^ 2) ≤
      1 * ENNReal.ofReal (‖h‖ ^ 2) := by
  rw [one_mul]
  have he : ∫⁻ y, ENNReal.ofReal (‖b y‖ ^ 2) =
      ∫⁻ y, ENNReal.ofReal (‖(partialX j h : Space → Space) y‖ ^ 2) :=
    lintegral_congr_ae (hb.mono fun y hy => by simp only [hy])
  refine (setLIntegral_le_lintegral _ _).trans ?_
  rw [he, ofReal_integral_sq]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_partialX_le j h) 2)

theorem reading_spec (u : XX) : IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  have hex : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 := by
    obtain ⟨v, G, H, hr, -⟩ := readingExistsHolds_proof u
    exact ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem coe_map_sub_ae {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : E →L[ℝ] Lp (α := Space) F p) (a b : E) :
    (L (a - b) : Space → F) =ᵐ[volume] (L a : Space → F) - (L b : Space → F) := by
  rw [map_sub]
  exact Lp.coeFn_sub _ _

theorem sub_ae_of_ae {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : E →L[ℝ] Lp (α := Space) F p) {a b : E} {f f' : Space → F}
    (hf : f =ᵐ[volume] (L a : Space → F)) (hf' : f' =ᵐ[volume] (L b : Space → F)) :
    (fun y => f y - f' y) =ᵐ[volume] (L (a - b) : Space → F) := by
  filter_upwards [hf, hf', coe_map_sub_ae L a b] with y h1 h2 h3
  rw [h3, Pi.sub_apply, h1, h2]

theorem reading_diff {u u' : XX} {v v' : VelField} {G G' : GradField} {H H' : SecondField}
    (hr : IsReadingOf u v G H) (hr' : IsReadingOf u' v' G' H') :
    ∀ᵐ σ : ℝ, (fun y => v σ y - v' σ y) =ᵐ[volume]
        (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) :
          Space → Space) ∧
      ∀ j : Fin 3, (fun y => gradColumn G j σ y - gradColumn G' j σ y) =ᵐ[volume]
        (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) :
          Space → Space) := by
  filter_upwards [hr.velocity_eq, hr'.velocity_eq, hr.weak_gradient, hr'.weak_gradient]
    with σ h1 h1' h2 h2'
  exact ⟨sub_ae_of_ae velocity h1 h1', fun j => sub_ae_of_ae (partialX j)
    (partialX_ae_of_weakGradient h2 _ h1 j) (partialX_ae_of_weakGradient h2' _ h1' j)⟩

theorem real_final {x D K g p q0 q1 q2 : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D) (hK : 0 ≤ K) (hg : 0 ≤ g)
    (hp : 0 ≤ p) (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (h : x ^ 2 ≤ 6 * D ^ 2 * (p + (q0 + q1 + q2)) + K * g ^ 2) :
    x ≤ 3 * D * (Real.sqrt p + (Real.sqrt q0 + Real.sqrt q1 + Real.sqrt q2)) + Real.sqrt K * g := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ p = a ^ 2 := ⟨Real.sqrt p, Real.sqrt_nonneg _, (Real.sq_sqrt hp).symm⟩
  obtain ⟨b0, hb0, rfl⟩ : ∃ a, 0 ≤ a ∧ q0 = a ^ 2 :=
    ⟨Real.sqrt q0, Real.sqrt_nonneg _, (Real.sq_sqrt hq0).symm⟩
  obtain ⟨b1, hb1, rfl⟩ : ∃ a, 0 ≤ a ∧ q1 = a ^ 2 :=
    ⟨Real.sqrt q1, Real.sqrt_nonneg _, (Real.sq_sqrt hq1).symm⟩
  obtain ⟨b2, hb2, rfl⟩ : ∃ a, 0 ≤ a ∧ q2 = a ^ 2 :=
    ⟨Real.sqrt q2, Real.sqrt_nonneg _, (Real.sq_sqrt hq2).symm⟩
  obtain ⟨c, hc, rfl⟩ : ∃ a, 0 ≤ a ∧ K = a ^ 2 := ⟨Real.sqrt K, Real.sqrt_nonneg _, (Real.sq_sqrt hK).symm⟩
  rw [Real.sqrt_sq ha, Real.sqrt_sq hb0, Real.sqrt_sq hb1, Real.sqrt_sq hb2, Real.sqrt_sq hc]
  have hs : 0 ≤ a + (b0 + b1 + b2) := by positivity
  refine (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 ?_
  have e1 : a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) ≤ (a + (b0 + b1 + b2)) ^ 2 := by
    nlinarith [mul_nonneg ha hb0, mul_nonneg ha hb1, mul_nonneg ha hb2, mul_nonneg hb0 hb1,
      mul_nonneg hb0 hb2, mul_nonneg hb1 hb2]
  have e2 : 0 ≤ 3 * D * (a + (b0 + b1 + b2)) * (c * g) := by positivity
  have e3 : 6 * D ^ 2 * (a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)) ≤ 9 * D ^ 2 * (a + (b0 + b1 + b2)) ^ 2 := by
    have e4 : 0 ≤ D ^ 2 * (a ^ 2 + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e1 (sq_nonneg D)]
  nlinarith

theorem final_bound {x D K g : ℝ} {P : ℝ≥0∞} {Q : Fin 3 → ℝ≥0∞} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hg : 0 ≤ g) (hP : P ≠ ⊤) (hQ : ∀ j, Q j ≠ ⊤)
    (h : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) * (P + ∑ j, Q j) +
      ENNReal.ofReal K * ENNReal.ofReal (g ^ 2)) :
    x ≤ 3 * D * (Real.sqrt P.toReal + ∑ j, Real.sqrt (Q j).toReal) + Real.sqrt K * g := by
  have hs : P + ∑ j, Q j = ENNReal.ofReal (P.toReal + ∑ j, (Q j).toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hP]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (hQ j)).symm
  have hs0 : 0 ≤ P.toReal + ∑ j, (Q j).toReal :=
    add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg)
  rw [hs, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK,
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hs0) (mul_nonneg hK (sq_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg (by positivity) hs0)
      (mul_nonneg hK (sq_nonneg _)))] at h
  rw [Fin.sum_univ_three] at h ⊢
  exact real_final hx hD hK hg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg h

theorem integral_split {μ : Measure ℝ} {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : ℝ → ℝ≥0∞}
    {g : Fin 3 → ℝ → ℝ≥0∞} (t : ℝ → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : ∀ j, AEMeasurable (g j) μ) :
    ∫⁻ σ, (c * (f σ + ∑ j, g j σ) + t σ) ∂μ = c * (∫⁻ σ, f σ ∂μ + ∑ j, ∫⁻ σ, g j σ ∂μ) + ∫⁻ σ, t σ ∂μ := by
  have hm : AEMeasurable (fun σ => c * (f σ + ∑ j, g j σ)) μ :=
    (hf.add (Finset.aemeasurable_fun_sum Finset.univ fun j _ => hg j)).const_mul c
  rw [lintegral_add_left' hm, lintegral_const_mul' _ _ hc, lintegral_add_left' hf,
    lintegral_finsetSum' _ fun j _ => hg j]

theorem core_bound (h2 : ConvectionHolds) {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) {R : ℝ} (hR : 0 ≤ R) {u u' : XX} {v v' : VelField}
    {G G' : GradField} {H H' : SecondField} (hr : IsReadingOf u v G H) (hr' : IsReadingOf u' v' G' H') :
    ‖convection d p u - convection d p u'‖ ≤
      3 * d.decay * (periodBallNorm R (fun σ y => v σ y - v' σ y)
        + ∑ j : Fin 3, periodBallNorm R (fun σ y => gradColumn G j σ y - gradColumn G' j σ y))
      + Real.sqrt (tailConst d.decay / (1 + R)) * ‖gradCLM u - gradCLM u'‖ := by
  have hW := isCoefficient_profile hd hp
  have hD := coefficient_nonneg hW
  have hK : 0 ≤ tailConst d.decay / (1 + R) := div_nonneg (tailConst_nonneg _) (by linarith)
  have hid := reading_diff hr hr'
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2 - v' z.1 z.2) volume :=
    hr.measurable_velocity.sub hr'.measurable_velocity
  have hgm : ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => gradColumn G j z.1 z.2 - gradColumn G' j z.1 z.2) volume := fun j =>
    (apply_aesm hr.measurable_gradient aestronglyMeasurable_const).sub
      (apply_aesm hr'.measurable_gradient aestronglyMeasurable_const)
  have hPm := aemeasurable_ball (f := fun σ y => v σ y - v' σ y) hvm R
  have hQm := fun j => aemeasurable_ball (f := fun σ y => gradColumn G j σ y - gradColumn G' j σ y) (hgm j) R
  have hper : ∀ᵐ σ : ℝ, ∫⁻ y, ENNReal.ofReal (‖sliceConvection (d.profile p σ)
      (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) y‖ ^ 2) ≤
        ENNReal.ofReal (6 * d.decay ^ 2) *
          ((∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖v σ y - v' σ y‖ ^ 2)) +
            ∑ j : Fin 3, ∫⁻ y in Metric.closedBall (0 : Space) R,
              ENNReal.ofReal (‖gradColumn G j σ y - gradColumn G' j σ y‖ ^ 2)) +
        ENNReal.ofReal (tailConst d.decay / (1 + R)) * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
          - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) := by
    filter_upwards [hid] with σ hσ
    exact slice_split hW hR σ _ (fun y => v σ y - v' σ y)
      (fun j y => gradColumn G j σ y - gradColumn G' j σ y) hσ.1 hσ.2
  have hsum := integral_split (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (c := ENNReal.ofReal (6 * d.decay ^ 2)) ENNReal.ofReal_ne_top
    (fun σ => ENNReal.ofReal (tailConst d.decay / (1 + R)) * ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))
          - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2)) hPm hQm
  have hT := time_integral_le u u' (c := ENNReal.ofReal (tailConst d.decay / (1 + R)))
    ENNReal.ofReal_ne_top (g := fun σ => ENNReal.ofReal (tailConst d.decay / (1 + R)) *
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) - gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2))
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
  have key := (conv_le h2 hd hp u u').trans ((lintegral_mono_ae (ae_restrict_of_ae hper)).trans
    (hsum.le.trans (add_le_add le_rfl hT)))
  exact final_bound (P := periodBallLIntegral R (fun σ y => ‖v σ y - v' σ y‖ ^ 2))
    (Q := fun j => periodBallLIntegral R (fun σ y => ‖gradColumn G j σ y - gradColumn G' j σ y‖ ^ 2))
    (norm_nonneg _) hD hK (norm_nonneg _) hfinP hfinQ key

theorem sqrt_tail_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    Real.sqrt (T / (1 + (T / ε ^ 2 + 1))) ≤ ε := by
  have hpos : 0 < 1 + (T / ε ^ 2 + 1) := by positivity
  have h1 : T / (1 + (T / ε ^ 2 + 1)) ≤ ε ^ 2 := by
    rw [div_le_iff₀ hpos]
    have h3 : ε ^ 2 * (T / ε ^ 2) = T := by field_simp
    nlinarith [sq_nonneg ε]
  exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq hε.le)

end Internal.ConvectionTail

namespace Internal.ConvectionCompact

open Internal.ConvectionTail

theorem local_tail_bound (h2 : ConvectionHolds) {k : ℕ} (d : CertificateData k)
    (hd : IsCertificate d) (p : Fin k → ℝ) (hp : p ∈ d.box) :
    ∀ ε > 0, ∃ R > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ u u' : XX,
      ‖convection d p u - convection d p u'‖ ≤
        A * (periodBallNorm R (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y)
          + ∑ j : Fin 3, periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ y
            - gradColumn (readingOf u').2.1 j σ y))
        + ε * (‖gradCLM u‖ + ‖gradCLM u'‖) := by
  intro ε hε
  have hT := tailConst_nonneg d.decay
  have hD : 0 ≤ d.decay := Internal.Convection.coefficient_nonneg
    (Internal.Convection.isCoefficient_profile hd hp)
  refine ⟨tailConst d.decay / ε ^ 2 + 1, by positivity, 3 * d.decay, by positivity, fun u u' => ?_⟩
  have hK := sqrt_tail_le hε hT
  have hb := core_bound h2 hd hp (R := tailConst d.decay / ε ^ 2 + 1) (by positivity)
    (reading_spec u) (reading_spec u')
  exact hb.trans (add_le_add le_rfl (mul_le_mul hK (norm_sub_le _ _) (norm_nonneg _) hε.le))

end Internal.ConvectionCompact


end Breakdown.Cert
