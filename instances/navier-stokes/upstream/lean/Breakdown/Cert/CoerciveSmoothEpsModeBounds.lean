import Breakdown.Cert.CoerciveSmoothEpsSquare
import Breakdown.Cert.CoerciveAbsorb

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

open Internal.Absorb

theorem lintegral_modeGrad_le (hPars : ModeSquareSumHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hGp : IsTimePeriodic G)
    (hGf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) (ι : ℤ × ℤ) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)))
      ≤ periodLIntegral (fun σ y => matSq (G σ y)) := by
  rw [hPars.2.1 G hGm hGp hGf]
  exact ENNReal.le_tsum ι

theorem aesm_cnormSq_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slabMeasure :=
  (aesm_cnormSq fun ij => Internal.FieldModes.aestronglyMeasurable_modeGrad hGm ι ij).mono_ac ac_slab

theorem integrable_cnormSq_modeGrad (hPars : ModeSquareSumHolds) {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hGp : IsTimePeriodic G)
    (hGf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slabMeasure :=
  ModeL2Internal.integrable_of_periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y))
    (aesm_cnormSq_modeGrad hGm ι) (fun _ _ => cnormSq_nonneg' _)
    (lt_of_le_of_lt (lintegral_modeGrad_le hPars hGm hGp hGf ι) hGf)

theorem integrable_cnormSq_modeSecondDeriv (hPars : ModeSquareSumHolds) {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hHm : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (hHp : IsTimePeriodic H)
    (hHf : periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeSecondDeriv ι H z.1 z.2)) slabMeasure := by
  have hle : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)))
      ≤ periodLIntegral (fun σ y => secondDerivSq (H σ y)) := by
    rw [hPars.2.2.1 H hHm hHp hHf]
    exact ENNReal.le_tsum ι
  exact ModeL2Internal.integrable_of_periodLIntegral (fun σ y => cnormSq (modeSecondDeriv ι H σ y))
    ((aesm_cnormSq fun ijl => aesm_modeSecondDeriv hHm ι ijl).mono_ac ac_slab) (fun _ _ => cnormSq_nonneg' _)
    (lt_of_le_of_lt hle hHf)

theorem abs_bound_aux {r wabs e a b A B : ℝ} (h1 : |r| ≤ wabs * ((1 * a + b / 1) / 2)) (h4 : wabs ≤ e)
    (h0 : 0 ≤ wabs) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ 2 * A) (hB : b ≤ 2 * B) : |r| ≤ e * (A + B) := by
  rw [one_mul, div_one] at h1
  have he : 0 ≤ e := h0.trans h4
  have h2 : wabs * ((a + b) / 2) ≤ e * ((a + b) / 2) := mul_le_mul_of_nonneg_right h4 (by linarith)
  have h3 : e * ((a + b) / 2) ≤ e * (A + B) := mul_le_mul_of_nonneg_left (by linarith) he
  linarith

theorem abs_epsIntegrand_le {C : Type} (m : ModeWeights C) {epsSup : ℝ} (hle : ∀ c y, |m.epsW c y| ≤ epsSup)
    (v f : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    |epsIntegrand m v f ι σ y| ≤
      epsSup * (cnormSq (modeGrad ι (gradField v) σ y) + cnormSq (modeGrad ι (gradField f) σ y)) :=
  abs_bound_aux (ModeL2Internal.abs_re_weighted_le (m.epsW (m.classOf ι) y)
    (curlOfGrad (modeGrad ι (gradField v) σ y)) (curlOfGrad (modeGrad ι (gradField f) σ y)) one_pos)
    (hle (m.classOf ι) y) (abs_nonneg _) (cnormSq_nonneg' _) (cnormSq_nonneg' _)
    (cnormSq_curlOfGrad_le _) (cnormSq_curlOfGrad_le _)

theorem aesm_epsIntegrand {C : Type} (m : ModeWeights C) (hw : ∀ c, Continuous (m.epsW c))
    {v f : ℝ → Space → Space}
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => gradField v z.1 z.2) volume)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => gradField f z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => epsIntegrand m v f ι z.1 z.2) slabMeasure := by
  have hc : ∀ (K : ℝ → Space → (Space →L[ℝ] Space)),
      AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume →
      ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => curlOfGrad (modeGrad ι K z.1 z.2) i) volume := by
    intro K hK i
    unfold curlOfGrad
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
      (Internal.FieldModes.aestronglyMeasurable_modeGrad hK ι (l, j)).const_mul _
  have hd := ModeL2Internal.aestronglyMeasurable_cdot (hc _ hv) (hc _ hf)
  have hwt : AEStronglyMeasurable (fun z : ℝ × Space => ((m.epsW (m.classOf ι) z.2 : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp ((hw _).comp continuous_snd)).aestronglyMeasurable
  unfold epsIntegrand
  exact (Complex.continuous_re.comp_aestronglyMeasurable ((aestronglyMeasurable_const.mul hwt).mul hd)).mono_ac
    ac_slab

theorem epsW_continuous {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (c : C) :
    Continuous (m.epsW c) := by
  obtain ⟨K, hK⟩ := hm.epsW_increment c
  exact hK.continuous

theorem integrable_epsIntegrand (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds) {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) {f : ℝ → Space → Space}
    (hfm : AEStronglyMeasurable (fun z : ℝ × Space => gradField f z.1 z.2) volume) (hfp : IsTimePeriodic (gradField f))
    (hff : periodLIntegral (fun σ y => matSq (gradField f σ y)) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => epsIntegrand m v f ι z.1 z.2) slabMeasure := by
  have hv := hSP P v hS.smooth
  have i1 := integrable_cnormSq_modeGrad hPars hv.measurable_gradient hv.periodic_gradient hv.gradient_finite ι
  have i2 := integrable_cnormSq_modeGrad hPars hfm hfp hff ι
  refine ((i1.add i2).const_mul epsSup).mono'
    (aesm_epsIntegrand m (epsW_continuous hS.admissible) hv.measurable_gradient hfm ι) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_epsIntegrand_le m hS.admissible.epsW_le v f ι z.1 z.2

end SmoothEpsInternal

end Coercive

end Breakdown
