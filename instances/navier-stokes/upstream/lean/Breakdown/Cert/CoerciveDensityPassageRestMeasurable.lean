import Breakdown.Cert.CoerciveSmoothDensityMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRestMeasurable

open PairingSplitInternal (periodMeasure)
open Internal.SmoothDensity (lift_snd measure_ac)

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem aem_base_of (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space =>
      modeVals v G H ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)) volume := by
  have d0 := lift_snd (hm.convD_smooth (m.classOf ι)).continuous.measurable
  have z0 := lift_snd (hm.convZ_smooth (m.classOf ι)).continuous.measurable
  have d2 := lift_snd (f := ModeWeights.secondDerivNorm (m.convD (m.classOf ι)))
    ((hm.convD_smooth (m.classOf ι)).continuous_iteratedFDeriv (le_refl _)).norm.measurable
  have z2 := lift_snd (f := ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)))
    ((hm.convZ_smooth (m.classOf ι)).continuous_iteratedFDeriv (le_refl _)).norm.measurable
  have w0 := lift_snd hm.weight_measurable
  have x2 := Internal.PieceAbsorb.aem_secondDerivAmp hH ι
  have xc := Internal.PieceAbsorb.aem_vortGradAmp hH ι
  have x1 := Internal.PieceAbsorb.aem_gradAmp hG ι
  have xo := Internal.PieceAbsorb.aem_vortAmp hG ι
  have x0 := Internal.PieceAbsorb.aem_velAmp hV ι
  unfold modeVals baseDensity
  exact (((((d0.sub_const m.c).mul (x2.pow_const 2)).add ((d0.const_sub 1).mul (xc.pow_const 2))).add
    ((z0.const_sub (1 / 4)).mul (xo.pow_const 2))).add (((z0.sub d2).sub (w0.const_mul m.c)).mul
      (x1.pow_const 2))).sub (z2.mul (x0.pow_const 2))

theorem aem_epsRest_of (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeEpsRest m W v G H ι z.1 z.2) volume := by
  obtain ⟨hWV, hWG, hWH⟩ := Internal.SmoothDensity.aem_fieldsW hW
  have a1 := lift_snd (Internal.SmoothDensity.measurable_eps hm ι)
  have a2 := lift_snd (Internal.SmoothDensity.measurable_rel hm hW (m.classOf ι))
  have a3 := lift_snd (f := m.epsGrad ι) (measurable_fderiv ℝ _).norm
  have a4 := lift_snd (f := fun y => ‖curlVec (fderiv ℝ (meanField W) y)‖)
    (Internal.SmoothDensity.continuous_curlVec.measurable.comp (measurable_fderiv ℝ _)).norm
  have a5 := lift_snd (continuous_abs.measurable.comp (hm.rate_measurable (m.classOf ι)))
  have a6 := lift_snd (f := fun y => ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖)
    (measurable_fderiv ℝ _).norm
  have b1 := fun κ => Internal.PieceAbsorb.aem_vortGradAmp hH κ
  have b2 := fun κ => Internal.PieceAbsorb.aem_vortAmp hG κ
  have b3 := fun κ => Internal.PieceAbsorb.aem_velAmp hV κ
  have b4 := fun κ => Internal.PieceAbsorb.aem_gradAmp hG κ
  have c1 := fun κ => Internal.PieceAbsorb.aem_velAmp hWV κ
  have c2 := fun κ => Internal.PieceAbsorb.aem_gradAmp hWG κ
  have c3 := fun κ => Internal.PieceAbsorb.aem_vortGradAmp hWH κ
  have c4 := fun κ => Internal.PieceAbsorb.aem_vortAmp hWG κ
  have hs : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      (velAmp W α z.1 z.2 * vortGradAmp H (ι - α) z.1 z.2
        + gradAmp (gradField W) α z.1 z.2 * vortAmp G (ι - α) z.1 z.2
        + vortGradAmp (secondDerivField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2
        + vortAmp (gradField W) α z.1 z.2 * gradAmp G (ι - α) z.1 z.2)) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ =>
      ((((c1 α).mul (b1 _)).add ((c2 α).mul (b2 _))).add ((c3 α).mul (b3 _))).add ((c4 α).mul (b4 _))
  unfold modeEpsRest
  exact ((((((a1.mul a2).add a3).mul (b1 ι)).mul (b2 ι)).neg.sub
    ((a1.mul ((a4.const_mul (1 / 2 : ℝ)).add a5)).mul ((b2 ι).pow_const 2))).sub
    (((a1.mul a6).mul (b3 ι)).mul (b2 ι))).sub (((a1.mul a4).mul (b4 ι)).mul (b2 ι)) |>.sub
    ((a1.mul (b2 ι)).mul hs)

theorem aem_muRest_of (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeMuRest m W v G ι z.1 z.2) volume := by
  obtain ⟨hWV, hWG, -⟩ := Internal.SmoothDensity.aem_fieldsW hW
  have a1 := lift_snd (Internal.SmoothDensity.measurable_mu hm ι)
  have a2 := lift_snd (Internal.SmoothDensity.measurable_rel hm hW (m.classOf ι))
  have a3 := lift_snd (f := m.muGrad ι) (measurable_fderiv ℝ _).norm
  have a5 := lift_snd (continuous_abs.measurable.comp (hm.rate_measurable (m.classOf ι)))
  have a7 := lift_snd (f := fun y => ‖fderiv ℝ (meanField W) y‖) (measurable_fderiv ℝ _).norm
  have b3 := fun κ => Internal.PieceAbsorb.aem_velAmp hV κ
  have b4 := fun κ => Internal.PieceAbsorb.aem_gradAmp hG κ
  have c1 := fun κ => Internal.PieceAbsorb.aem_velAmp hWV κ
  have c2 := fun κ => Internal.PieceAbsorb.aem_gradAmp hWG κ
  have s1 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      velAmp W α z.1 z.2 * gradAmp G (ι - α) z.1 z.2) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ => (c1 α).mul (b4 _)
  have s2 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ => (c2 α).mul (b3 _)
  unfold modeMuRest
  have t1 := (((a1.mul a2).add a3).mul (b4 ι)).mul (b3 ι)
  have t2 := (a1.mul a5).mul ((b3 ι).pow_const 2)
  have t3 := (a1.mul (b3 ι)).mul s1
  have t4 := (((a7.pow_const 2).mul ((b3 ι).pow_const 2)).add (s2.pow_const 2)).div_const (m.eta (m.classOf ι))
  have t5 := ((a1.pow_const 2).const_mul ((1 / 2 : ℝ) * m.eta (m.classOf ι))).mul ((b3 ι).pow_const 2)
  have t6 := (t4.add t5).const_mul (ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0))
  exact ((t1.neg.sub t2).sub t3).sub t6

theorem aem_modeRest_of (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeRest m w W v G H ι z.1 z.2) volume := by
  unfold modeRest
  exact ((aem_base_of hm hV hG hH ι).add (aem_epsRest_of hm hW hV hG hH ι)).add (aem_muRest_of hm hW hV hG ι)

theorem rest_difference_aemeasurable {Γ : Set Symmetry}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hSP : SmoothPerturbationIsPerturbationHolds) {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    {u : ℕ → ℝ → Space → Space} (hu : IsSmoothApproximation P v G H g u) (n : ℕ) :
    AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
          - modeRest m w W v G H ι z.1 z.2|)) PairingSplitInternal.periodMeasure := by
  have hp := hSP P (u n) (hu.1 n)
  refine AEMeasurable.ennreal_tsum fun ι => ?_
  have h1 := aem_modeRest_of (w := w) hA hWs hp.measurable_velocity hp.measurable_gradient hp.measurable_secondDeriv ι
  have h2 := aem_modeRest_of (w := w) hA hWs hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv ι
  exact ((continuous_abs.measurable.comp_aemeasurable (h1.sub h2)).ennreal_ofReal).mono_ac measure_ac

end Internal.DensityPassageRestMeasurable

end Coercive

end Breakdown
