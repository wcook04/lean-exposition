import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPieceDensityEnergy

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceDensity

open Coercive Coercive.Internal.PieceAbsorb Coercive.SmoothEnergyIdentityInternal
  Coercive.SmoothEnergyIdentityInternal.Rest Coercive.EnergyIdentityInternal

private theorem continuous_fderiv_slice_one {W : ℝ → Space → Space}
    (h : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have h2 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => W z.1 y) :=
    h.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

private theorem stretchFormWith_eq (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchFormWith W HW v G σ y = stretchOfData (G σ y, fderiv ℝ (W σ) y, HW σ y, v σ y) := rfl

private theorem aemeasurable_stretchFormWith_slab {P : ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : Coercive.IsSmoothPerturbation P v) :
    AEMeasurable (fun z : ℝ × Space => stretchFormWith W HW v (gradField v) z.1 z.2) slabMeasure := by
  have h2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := h2.continuous.aestronglyMeasurable
  have hGm : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume :=
    (continuous_fderiv_slice h2).aestronglyMeasurable
  have ht : AEStronglyMeasurable (fun z : ℝ × Space =>
      (gradField v z.1 z.2, fderiv ℝ (W z.1) z.2, HW z.1 z.2, v z.1 z.2)) volume :=
    hGm.prodMk ((continuous_fderiv_slice_one hW.smooth).aestronglyMeasurable.prodMk
      (hW.secondDeriv_measurable.prodMk hvm))
  rw [slabMeasure_eq]
  exact (continuous_stretchOfData.comp_aestronglyMeasurable ht).aemeasurable.restrict

private theorem stretchFormWith_integrable_slab {P : ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : Coercive.IsSmoothPerturbation P v) :
    Integrable (fun z : ℝ × Space => stretchFormWith W HW v (gradField v) z.1 z.2) slabMeasure := by
  have hD := hW.decay
  have hD0 : 0 ≤ D := by
    have := (hD 0 0).1
    simp at this
    exact (norm_nonneg _).trans this
  have h0 := hv.smooth
  have j1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have c0 : Continuous (fun z : ℝ × Space => v z.1 z.2) := h0.continuous
  have c1 := j1.continuous
  have i0 := joint_integrable (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
    (by
      refine Continuous.div ((continuous_norm.comp c0).pow 2)
        ((continuous_const.add (continuous_norm.comp continuous_snd)).pow 2) (fun z => by positivity))
    (fun σ y => by positivity) hv.weighted_finite
  have e1 : (fun σ y => ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) = fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2 := by
    funext σ y
    rw [norm_iteratedFDeriv_one]
  have p1 := hv.derivatives_finite 1 le_rfl
  rw [e1] at p1
  have i1 := joint_integrable (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) ((continuous_norm.comp c1).pow 2)
    (fun σ y => by positivity) p1
  have hM0 : 0 ≤ 81 * ‖curlCLM‖ + 729 / 2 := by positivity
  refine Integrable.mono' ((i1.const_mul (9 * ‖curlCLM‖ ^ 2 * D + (81 * ‖curlCLM‖ + 729 / 2) * D / 2)).add
    (i0.const_mul ((81 * ‖curlCLM‖ + 729 / 2) * D / 2)))
    (aemeasurable_stretchFormWith_slab hW hv).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  obtain ⟨σ, y⟩ := z
  simp only [Pi.add_apply]
  have hWσ1 := (hD σ y).2.1
  have hWσ2 := (hD σ y).2.2
  have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have dWle : ‖fderiv ℝ (W σ) y‖ ≤ D := by
    refine hWσ1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ hy1
    nlinarith
  have h3 : ‖HW σ y‖ ≤ D / (1 + ‖y‖) := by
    refine hWσ2.trans ?_
    apply div_le_div_of_nonneg_left hD0 (by positivity)
    calc 1 + ‖y‖ = (1 + ‖y‖) ^ 1 := (pow_one _).symm
      _ ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_right₀ hy1 (by norm_num)
  have hWle : ‖HW σ y‖ * ‖v σ y‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := by
    calc ‖HW σ y‖ * ‖v σ y‖
        ≤ D / (1 + ‖y‖) * ‖v σ y‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
  have hst : |stretchFormWith W HW v (gradField v) σ y| ≤
      3 * (3 * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖)))
        + (81 * ‖curlCLM‖ + 729 / 2) * (‖HW σ y‖ * ‖v σ y‖) * ‖fderiv ℝ (v σ) y‖ :=
    (stretch_le (fderiv ℝ (v σ) y) (fderiv ℝ (W σ) y) (HW σ y) (v σ y)).trans (le_of_eq (by ring))
  have hB0 : 0 ≤ ‖fderiv ℝ (v σ) y‖ := norm_nonneg _
  have hA0 : 0 ≤ ‖v σ y‖ / (1 + ‖y‖) := by positivity
  have q1 : 3 * (3 * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖)))
      ≤ 9 * ‖curlCLM‖ ^ 2 * D * ‖fderiv ℝ (v σ) y‖ ^ 2 := by
    have e : 3 * (3 * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ * (‖curlCLM‖ * ‖fderiv ℝ (v σ) y‖)))
        = 9 * ‖curlCLM‖ ^ 2 * ‖fderiv ℝ (v σ) y‖ ^ 2 * ‖fderiv ℝ (W σ) y‖ := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left dWle (by positivity : (0 : ℝ) ≤ 9 * ‖curlCLM‖ ^ 2 * ‖fderiv ℝ (v σ) y‖ ^ 2)]
  have q2 : (81 * ‖curlCLM‖ + 729 / 2) * (‖HW σ y‖ * ‖v σ y‖) * ‖fderiv ℝ (v σ) y‖
      ≤ (81 * ‖curlCLM‖ + 729 / 2) * D / 2 * (‖fderiv ℝ (v σ) y‖ ^ 2 + (‖v σ y‖ / (1 + ‖y‖)) ^ 2) := by
    have s1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWle hM0) hB0
    have s2 : (‖v σ y‖ / (1 + ‖y‖)) * ‖fderiv ℝ (v σ) y‖
        ≤ (‖fderiv ℝ (v σ) y‖ ^ 2 + (‖v σ y‖ / (1 + ‖y‖)) ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖v σ y‖ / (1 + ‖y‖) - ‖fderiv ℝ (v σ) y‖)]
    have s3 := mul_le_mul_of_nonneg_left s2 (mul_nonneg hM0 hD0)
    calc _ ≤ (81 * ‖curlCLM‖ + 729 / 2) * (D * (‖v σ y‖ / (1 + ‖y‖))) * ‖fderiv ℝ (v σ) y‖ := s1
      _ = (81 * ‖curlCLM‖ + 729 / 2) * D * ((‖v σ y‖ / (1 + ‖y‖)) * ‖fderiv ℝ (v σ) y‖) := by ring
      _ ≤ (81 * ‖curlCLM‖ + 729 / 2) * D * ((‖fderiv ℝ (v σ) y‖ ^ 2 + (‖v σ y‖ / (1 + ‖y‖)) ^ 2) / 2) := s3
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  refine hst.trans ((add_le_add q1 q2).trans (le_of_eq ?_))
  rw [div_pow]
  ring

theorem energy_split {P : ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} {v : ℝ → Space → Space}
    (hW : IsWeakSecondDerivState W HW D) (hv : Coercive.IsSmoothPerturbation P v) :
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (stretchFormWith W HW v (gradField v) z.1 z.2))
        slabMeasure ∧
      AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-stretchFormWith W HW v (gradField v) z.1 z.2))
        slabMeasure ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (stretchFormWith W HW v (gradField v) σ y)) < ⊤ ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-stretchFormWith W HW v (gradField v) σ y)) < ⊤ ∧
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y)
        = Coercive.vorticityEnergy v
          + ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              ENNReal.ofReal (stretchFormWith W HW v (gradField v) σ y)).toReal
            - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              ENNReal.ofReal (-stretchFormWith W HW v (gradField v) σ y)).toReal) := by
  have hf := stretchFormWith_integrable_slab hW hv
  have ha := Coercive.Internal.SmoothPieceDensity.vorticity_integrable_slab P v hv
  have hfm := aemeasurable_stretchFormWith_slab hW hv
  have mp : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (stretchFormWith W HW v (gradField v) z.1 z.2))
      slabMeasure := ENNReal.measurable_ofReal.comp_aemeasurable hfm
  have mn : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-stretchFormWith W HW v (gradField v) z.1 z.2))
      slabMeasure := ENNReal.measurable_ofReal.comp_aemeasurable hfm.neg
  have ep : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (stretchFormWith W HW v (gradField v) σ y))
      = ∫⁻ z, ENNReal.ofReal (stretchFormWith W HW v (gradField v) z.1 z.2) ∂slabMeasure :=
    (lintegral_prod _ mp).symm
  have en : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-stretchFormWith W HW v (gradField v) σ y))
      = ∫⁻ z, ENNReal.ofReal (-stretchFormWith W HW v (gradField v) z.1 z.2) ∂slabMeasure :=
    (lintegral_prod _ mn).symm
  refine ⟨mp, mn, ?_, ?_, ?_⟩
  · rw [ep]
    exact hf.lintegral_lt_top
  · rw [en]
    exact hf.neg.lintegral_lt_top
  · have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y))
        = ∫ z, ((matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)
          + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2) + stretchFormWith W HW v (gradField v) z.1 z.2)
          ∂slabMeasure := (integral_prod _ (ha.add hf)).symm
    have e2 : Coercive.vorticityEnergy v = ∫ z, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)
          + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2) ∂slabMeasure := (integral_prod _ ha).symm
    rw [e1, integral_add ha hf, e2, ep, en, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

end Internal.PieceDensity

end CoerciveWeak

end Breakdown
