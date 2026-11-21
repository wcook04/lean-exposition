import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothDensity

open PairingSplitInternal (periodMeasure)
open ModeL2Internal (IsSquareField)

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem measure_ac : periodMeasure ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    Measure.AbsolutelyContinuous.rfl

theorem lift_snd {f : Space → ℝ} (hf : Measurable f) : AEMeasurable (fun z : ℝ × Space => f z.2) volume :=
  (hf.comp measurable_snd).aemeasurable

theorem continuous_curlVec : Continuous curlVec := by
  unfold curlVec
  fun_prop

theorem aem_fields (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField v z.1 z.2) volume := by
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  exact ⟨hv.smooth.continuous.aestronglyMeasurable,
    (Internal.PieceAbsorb.continuous_fderiv_slice hv2).aestronglyMeasurable,
    (Internal.PieceAbsorb.measurable_secondDeriv_slice hv2).aestronglyMeasurable⟩

theorem aem_fieldsW (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField W z.1 z.2) volume :=
  ⟨hW.continuous.aestronglyMeasurable,
    (Internal.PieceAbsorb.continuous_fderiv_slice hW).aestronglyMeasurable,
    (Internal.PieceAbsorb.measurable_secondDeriv_slice hW).aestronglyMeasurable⟩

theorem measurable_eps (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) :
    Measurable (m.eps ι) := by
  obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
  exact (continuous_abs.comp hK.continuous).measurable

theorem measurable_mu (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) :
    Measurable (m.mu ι) := by
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  exact (continuous_abs.comp hK.continuous).measurable

theorem measurable_dop (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) :
    Measurable (fun y => |m.dop P ι y|) := by
  unfold ModeWeights.dop shiftedFrequency
  exact continuous_abs.measurable.comp (measurable_const.add (measurable_const.mul (hm.rate_measurable _)))

theorem measurable_rel (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (c : C) :
    Measurable (fun y => ‖relativeVelocity W (m.rate c) y‖) := by
  have h1 : Continuous (meanField W) := (StretchInternal.meanField_contDiff W hW).continuous
  have h2 : Measurable (m.rate c) := hm.rate_measurable c
  unfold relativeVelocity
  fun_prop

theorem aesm_epsPos (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeEpsPos m P (gradField v) ι z.1 z.2) periodMeasure := by
  obtain ⟨_, hG, _⟩ := aem_fields hv
  have a1 := lift_snd (measurable_eps hm ι)
  have a2 := lift_snd (measurable_dop hm ι)
  have a3 := Internal.PieceAbsorb.aem_vortAmp hG ι
  unfold modeEpsPos
  exact ((a1.mul a2).mul (a3.pow_const 2)).mono_ac measure_ac |>.aestronglyMeasurable

theorem aesm_epsRest (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2)
      periodMeasure := by
  obtain ⟨hV, hG, hH⟩ := aem_fields hv
  obtain ⟨hWV, hWG, hWH⟩ := aem_fieldsW hW
  have e1 : Measurable (m.eps ι) := measurable_eps hm ι
  have e2 : Measurable (fun y => ‖relativeVelocity W (m.rate (m.classOf ι)) y‖) := measurable_rel hm hW _
  have e3 : Measurable (m.epsGrad ι) := (measurable_fderiv ℝ _).norm
  have e4 : Measurable (fun y => ‖curlVec (fderiv ℝ (meanField W) y)‖) :=
    (continuous_curlVec.measurable.comp (measurable_fderiv ℝ _)).norm
  have e5 : Measurable (fun y => |m.rate (m.classOf ι) y|) :=
    continuous_abs.measurable.comp (hm.rate_measurable _)
  have e6 : Measurable (fun y => ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖) :=
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
      (velAmp W α z.1 z.2 * vortGradAmp (secondDerivField v) (ι - α) z.1 z.2
        + gradAmp (gradField W) α z.1 z.2 * vortAmp (gradField v) (ι - α) z.1 z.2
        + vortGradAmp (secondDerivField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2
        + vortAmp (gradField W) α z.1 z.2 * gradAmp (gradField v) (ι - α) z.1 z.2)) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ =>
      ((((c1 α).mul (b1 _)).add ((c2 α).mul (b2 _))).add ((c3 α).mul (b3 _))).add ((c4 α).mul (b4 _))
  have a1 := lift_snd e1
  have a2 := lift_snd e2
  have a3 := lift_snd e3
  have a4 := lift_snd e4
  have a5 := lift_snd e5
  have a6 := lift_snd e6
  unfold modeEpsRest
  refine (AEMeasurable.mono_ac ?_ measure_ac).aestronglyMeasurable
  exact ((((((a1.mul a2).add a3).mul (b1 ι)).mul (b2 ι)).neg.sub
    ((a1.mul ((a4.const_mul (1 / 2 : ℝ)).add a5)).mul ((b2 ι).pow_const 2))).sub
    (((a1.mul a6).mul (b3 ι)).mul (b2 ι))).sub (((a1.mul a4).mul (b4 ι)).mul (b2 ι)) |>.sub
    ((a1.mul (b2 ι)).mul hs)

theorem aesm_muPos (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeMuPos m P v ι z.1 z.2) periodMeasure := by
  obtain ⟨hV, _, _⟩ := aem_fields hv
  have a1 := lift_snd (measurable_mu hm ι)
  have a2 := lift_snd (measurable_dop hm ι)
  have a3 := Internal.PieceAbsorb.aem_velAmp hV ι
  unfold modeMuPos
  exact ((((a1.const_mul (1 - m.cμ)).mul a2).mul (a3.pow_const 2)).mono_ac measure_ac).aestronglyMeasurable

theorem aesm_muRest (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeMuRest m W v (gradField v) ι z.1 z.2) periodMeasure := by
  obtain ⟨hV, hG, _⟩ := aem_fields hv
  obtain ⟨hWV, hWG, _⟩ := aem_fieldsW hW
  have a1 := lift_snd (measurable_mu hm ι)
  have a2 := lift_snd (measurable_rel hm hW (m.classOf ι))
  have a3 := lift_snd (f := m.muGrad ι) (measurable_fderiv ℝ _).norm
  have a5 := lift_snd (continuous_abs.measurable.comp (hm.rate_measurable (m.classOf ι)))
  have a7 := lift_snd (f := fun y => ‖fderiv ℝ (meanField W) y‖) (measurable_fderiv ℝ _).norm
  have b3 := fun κ => Internal.PieceAbsorb.aem_velAmp hV κ
  have b4 := fun κ => Internal.PieceAbsorb.aem_gradAmp hG κ
  have c1 := fun κ => Internal.PieceAbsorb.aem_velAmp hWV κ
  have c2 := fun κ => Internal.PieceAbsorb.aem_gradAmp hWG κ
  have s1 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      velAmp W α z.1 z.2 * gradAmp (gradField v) (ι - α) z.1 z.2) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ => (c1 α).mul (b4 _)
  have s2 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ => (c2 α).mul (b3 _)
  unfold modeMuRest
  refine (AEMeasurable.mono_ac ?_ measure_ac).aestronglyMeasurable
  have t1 := (((a1.mul a2).add a3).mul (b4 ι)).mul (b3 ι)
  have t2 := (a1.mul a5).mul ((b3 ι).pow_const 2)
  have t3 := (a1.mul (b3 ι)).mul s1
  have t4 := (((a7.pow_const 2).mul ((b3 ι).pow_const 2)).add (s2.pow_const 2)).div_const (m.eta (m.classOf ι))
  have t5 := ((a1.pow_const 2).const_mul ((1 / 2 : ℝ) * m.eta (m.classOf ι))).mul ((b3 ι).pow_const 2)
  have t6 := (t4.add t5).const_mul (ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0))
  exact ((t1.neg.sub t2).sub t3).sub t6

theorem aesm_base (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v)
    (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space =>
      modeValues v ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)) periodMeasure := by
  obtain ⟨hV, hG, hH⟩ := aem_fields hv
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
  unfold modeValues baseDensity
  refine (AEMeasurable.mono_ac ?_ measure_ac).aestronglyMeasurable
  exact (((((d0.sub_const m.c).mul (x2.pow_const 2)).add ((d0.const_sub 1).mul (xc.pow_const 2))).add
    ((z0.const_sub (1 / 4)).mul (xo.pow_const 2))).add (((z0.sub d2).sub (w0.const_mul m.c)).mul
      (x1.pow_const 2))).sub (z2.mul (x0.pow_const 2))

end Internal.SmoothDensity

end Coercive

end Breakdown
