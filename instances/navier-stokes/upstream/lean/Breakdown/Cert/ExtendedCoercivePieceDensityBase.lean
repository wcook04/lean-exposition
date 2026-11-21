import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPieceDensityBase

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceDensityBase

open Coercive Coercive.Internal.SmoothPieceDensity Coercive.Internal.PieceAbsorb Coercive.Internal.FieldModes

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem secondDerivNorm_convD_bound {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) :
    ∃ K1, 0 ≤ K1 ∧ ∀ c y, ModeWeights.secondDerivNorm (m.convD c) y ≤ K1 := by
  obtain ⟨Bd, hBd⟩ := hm.convD_decay
  have hc : ∀ c, ∃ K, ∀ y, ModeWeights.secondDerivNorm (m.convD c) y ≤ K := by
    intro c
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
      ((hm.convD_smooth c).continuous_iteratedFDeriv (m := 2) le_rfl).norm.continuousOn
    refine ⟨max K Bd, fun y => ?_⟩
    by_cases hy : ‖y‖ ≤ 1
    · have h1 := hK y (by rw [Metric.mem_closedBall, dist_zero_right]; exact hy)
      rw [norm_norm] at h1
      exact le_max_of_le_left h1
    · rw [not_le] at hy
      have h2 := hBd c y 2 le_rfl
      have hn := norm_nonneg (iteratedFDeriv ℝ 2 (m.convD c) y)
      have : ModeWeights.secondDerivNorm (m.convD c) y ≤ Bd := by
        unfold ModeWeights.secondDerivNorm
        nlinarith [mul_nonneg hn (show (0 : ℝ) ≤ ‖y‖ ^ 2 - 1 by nlinarith)]
      exact le_max_of_le_right this
  choose Kc hKc using hc
  have := hm.finite_classes
  letI := Fintype.ofFinite C
  exact ⟨∑ c, |Kc c|, Finset.sum_nonneg fun c _ => abs_nonneg _, fun c y =>
    (hKc c y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun c => |Kc c|)
      (fun c _ => abs_nonneg (Kc c)) (Finset.mem_univ c)))⟩

theorem base_neg_finite (hP : ModeSquareSumHolds) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal
      (-modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))) < ⊤ := by
  obtain ⟨Bd, hBd⟩ := hm.convD_decay
  obtain ⟨Bz, hBz⟩ := hm.convZ_decay
  obtain ⟨Bw, hBw⟩ := hwb
  obtain ⟨K1, hK10, hK1⟩ := secondDerivNorm_convD_bound m P h w W HW hm
  have hBd0 : 0 ≤ Bd := le_trans (by positivity) (hBd (m.classOf 0) 0 0 (by norm_num))
  have hBz0 : 0 ≤ Bz := le_trans (by positivity) (hBz (m.classOf 0) 0 0 (by norm_num))
  have hBw0 : 0 ≤ Bw := le_trans (hm.weight_pos.le.trans (hm.weight_lower 0)) (hBw 0)
  have hcD : ∀ c y, |m.convD c y| ≤ Bd := fun c y => by
    have := hBd c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hcZ : ∀ c y, |m.convZ c y| ≤ Bz := fun c y => by
    have := hBz c y 0 (by norm_num)
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hhZ : ∀ c y, ModeWeights.secondDerivNorm (m.convZ c) y ≤ Bz * (1 / (1 + ‖y‖ ^ 2)) := fun c y => by
    have h2 := hBz c y 2 le_rfl
    have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have hle : 1 + ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    unfold ModeWeights.secondDerivNorm
    have e1 : ‖iteratedFDeriv ℝ 2 (m.convZ c) y‖ ≤ Bz / (1 + ‖y‖) ^ 2 := by
      rw [le_div_iff₀ hp]
      linarith
    calc ‖iteratedFDeriv ℝ 2 (m.convZ c) y‖ ≤ Bz / (1 + ‖y‖) ^ 2 := e1
      _ ≤ Bz / (1 + ‖y‖ ^ 2) := div_le_div_of_nonneg_left hBz0 hq hle
      _ = Bz * (1 / (1 + ‖y‖ ^ 2)) := by ring
  set K := Bd + m.c + 729 * (1 + Bd) + 243 * (1 / 4 + Bz) + Bz + K1 + m.c * Bw + Bz with hKdef
  have hK0 : 0 ≤ K := by
    have := hm.c_pos
    positivity
  have hpt : ∀ ι σ y, -modeVals v (gradField v) (secondDerivField v) ι σ y
      (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)
      ≤ K * (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y) + cnormSq (modeGrad ι (gradField v) σ y)
        + cnormSq (modeVel ι (dampVel v) σ y)) := by
    intro ι σ y
    have e2 := Real.sq_sqrt (cnormSq_nonneg' (modeSecondDeriv ι (secondDerivField v) σ y))
    have ec := Real.sq_sqrt (cnormSq_nonneg' (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y)))
    have e1 := Real.sq_sqrt (cnormSq_nonneg' (modeGrad ι (gradField v) σ y))
    have eo := Real.sq_sqrt (cnormSq_nonneg' (curlOfGrad (modeGrad ι (gradField v) σ y)))
    have e0 := Real.sq_sqrt (cnormSq_nonneg' (modeVel ι v σ y))
    have hd := cnormSq_modeVel_dampVel ι v σ y
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have key := base_coef_bound (x2 := secondDerivAmp (secondDerivField v) ι σ y) (xc := vortGradAmp (secondDerivField v) ι σ y)
      (x1 := gradAmp (gradField v) ι σ y) (xo := vortAmp (gradField v) ι σ y) (x0 := velAmp v ι σ y)
      (hcD (m.classOf ι) y) (hK1 (m.classOf ι) y) (hcZ (m.classOf ι) y) (hhZ (m.classOf ι) y) hm.c_pos
      (hm.weight_pos.le.trans (hm.weight_lower y)) (hBw y) (by positivity)
      (by
        unfold vortGradAmp secondDerivAmp
        rw [ec, e2]
        exact cnormSq_curlGradOfSecondDeriv_le _)
      (by
        unfold vortAmp gradAmp
        rw [eo, e1]
        exact cnormSq_curlOfGrad_le _) hBd0 hBz0 hK10 hBw0
    unfold modeVals baseDensity
    rw [hd]
    refine le_trans key (le_of_eq ?_)
    unfold secondDerivAmp gradAmp velAmp
    rw [e2, e1, e0, hKdef]
    ring
  have hGc : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    continuous_fderiv_slice (hv.smooth.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | decide))
  have hHm : Measurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) :=
    measurable_secondDeriv_slice (hv.smooth.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | decide))
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => dampVel v z.1 z.2) volume := by
    have hc : Continuous (fun z : ℝ × Space => (Real.sqrt (1 + ‖z.2‖ ^ 2))⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun z => ?_
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    exact hc.aestronglyMeasurable.smul hvc.aestronglyMeasurable
  have mH : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeSecondDeriv hHm.aestronglyMeasurable ι)
  have mG : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeGrad hGc.aestronglyMeasurable ι)
  have mV : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) z.1 z.2))) slabMeasure := fun ι =>
    aemeasurable_ofReal_cnormSq (aemeasurable_modeVel hXm ι)
  have hvp : ∀ σ, v (σ + 1) = v σ := fun σ => funext (hv.periodic σ)
  have pH : IsTimePeriodic (secondDerivField v) := fun σ y => by simp only [secondDerivField, hvp]
  have pG : IsTimePeriodic (gradField v) := fun σ y => by simp only [gradField, hvp]
  have pV : IsTimePeriodic (dampVel v) := fun σ y => by simp only [dampVel, hvp]
  have fH : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 9) (fun σ y => ?_) (hv.derivatives_finite 2 (by norm_num))
    have := secondDerivSq_le_base (secondDerivField v σ y)
    rwa [secondDerivField, ← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv] at this
  have fG : periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 3) (fun σ y => ?_) (hv.derivatives_finite 1 le_rfl)
    have := matSq_le_base (gradField v σ y)
    rwa [gradField, ← norm_iteratedFDeriv_one (𝕜 := ℝ)] at this
  have fV : periodLIntegral (fun σ y => ‖dampVel v σ y‖ ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top_of_le_base (by norm_num : (0 : ℝ) ≤ 2) (fun σ y => ?_) hv.weighted_finite
    rw [norm_dampVel_sq]
    have hq : 0 < 1 + ‖y‖ ^ 2 := by positivity
    have hp : 0 < (1 + ‖y‖) ^ 2 := by positivity
    rw [div_le_iff₀ hq, mul_comm, ← mul_assoc, mul_div_assoc']
    rw [le_div_iff₀ hp]
    nlinarith [sq_nonneg ‖v σ y‖, sq_nonneg (‖y‖ - 1), norm_nonneg y, mul_nonneg (sq_nonneg ‖v σ y‖) (sq_nonneg (‖y‖ - 1))]
  have eH := hP.2.2.1 (secondDerivField v) hHm.aestronglyMeasurable pH fH
  have eG := hP.2.1 (gradField v) hGc.aestronglyMeasurable pG fG
  have eV := hP.1 (dampVel v) hXm pV fV
  have sH := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) z.1 z.2))) mH
  have sG := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) z.1 z.2))) mG
  have sV := tsum_slab_base (f := fun ι z => ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) z.1 z.2))) mV
  have mSG := AEMeasurable.ennreal_tsum mG
  have mSV := AEMeasurable.ennreal_tsum mV
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal
        (-modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K *
          ((∑' ι, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)))
            + (∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)))
            + ∑' ι, ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) σ y))) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ?_
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun ι => ?_
        rw [← ENNReal.ofReal_add (cnormSq_nonneg' _) (cnormSq_nonneg' _),
          ← ENNReal.ofReal_add (add_nonneg (cnormSq_nonneg' _) (cnormSq_nonneg' _)) (cnormSq_nonneg' _),
          ← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hpt ι σ y)
    _ = ENNReal.ofReal K * ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            ∑' ι, ENNReal.ofReal (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)))
          + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)))
          + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (cnormSq (modeVel ι (dampVel v) σ y))) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_add_iter mSV, lintegral_add_iter mSG]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        simp only at sH sG sV
        rw [sH, sG, sV, ← eH, ← eG, ← eV]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨fH, fG⟩, fV⟩



end Internal.PieceDensityBase

end CoerciveWeak

end Breakdown
