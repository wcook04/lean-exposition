import Breakdown.Cert.CoerciveSmoothMuGlue
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoercivePairingSplit

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem continuous_average {X : Type*} [TopologicalSpace X] (ι : ℤ × ℤ) (F : (X × ℝ) × ℝ → ℝ)
    (hF : Continuous F) :
    Continuous (fun x => (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F ((x, τ), φ) : ℝ) : ℂ)) := by
  have hlin : Continuous (fun p : (X × ℝ) × ℝ => 2 * Real.pi * (ι.1 : ℝ) * p.1.2 + (ι.2 : ℝ) * p.2) := by
    fun_prop
  have hg : Continuous (fun p : (X × ℝ) × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)) * ((F p : ℝ) : ℂ)) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hlin).mul continuous_const).neg).mul
      (Complex.continuous_ofReal.comp hF)
  have h1 : Continuous (fun q : X × ℝ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * q.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F (q, φ) : ℝ) : ℂ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun q φ => Complex.exp (-(((2 * Real.pi * ι.1 * q.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((F (q, φ) : ℝ) : ℂ)) hg 0 (2 * Real.pi)
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun x τ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F ((x, τ), φ) : ℝ) : ℂ))
    h1 0 1
  exact continuous_const.mul h2

theorem continuous_modeVel {X : ℝ → Space → Space} (hX : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (ι : ℤ × ℤ) (i : Fin 3) : Continuous (fun z : ℝ × Space => modeVel ι X z.1 z.2 i) := by
  have hs : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => p.1.1.1 + p.1.2) := by fun_prop
  have hr : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot p.2 p.1.1.2) :=
    PairingSplitInternal.continuous_axialRot continuous_snd (by fun_prop)
  have hb : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => X (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) :=
    hX.comp (hs.prodMk hr)
  have hF : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      axialRot (-p.2) (X (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) i) :=
    (ModeL2Internal.continuous_coord i).comp (PairingSplitInternal.continuous_axialRot continuous_snd.neg hb)
  unfold modeVel modeAverage
  beta_reduce
  exact continuous_average ι (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      axialRot (-p.2) (X (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) i) hF

theorem continuous_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) (ι : ℤ × ℤ) (ij : Fin 3 × Fin 3) :
    Continuous (fun z : ℝ × Space => modeGrad ι G z.1 z.2 ij) := by
  have hs : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => p.1.1.1 + p.1.2) := by fun_prop
  have hr : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot p.2 p.1.1.2) :=
    PairingSplitInternal.continuous_axialRot continuous_snd (by fun_prop)
  have hb : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => G (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) :=
    hG.comp (hs.prodMk hr)
  have he : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot p.2 (unitVector ij.2)) :=
    PairingSplitInternal.continuous_axialRot continuous_snd continuous_const
  have hc : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      G (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2) (axialRot p.2 (unitVector ij.2))) := hb.clm_apply he
  have hF : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      axialRot (-p.2) (G (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2) (axialRot p.2 (unitVector ij.2))) ij.1) :=
    (ModeL2Internal.continuous_coord ij.1).comp (PairingSplitInternal.continuous_axialRot continuous_snd.neg hc)
  unfold modeGrad modeAverage
  beta_reduce
  exact continuous_average ι (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      axialRot (-p.2) (G (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2) (axialRot p.2 (unitVector ij.2))) ij.1) hF

theorem continuous_velAmp {X : ℝ → Space → Space} (hX : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (ι : ℤ × ℤ) : Continuous (fun z : ℝ × Space => velAmp X ι z.1 z.2) := by
  unfold velAmp cnormSq
  exact (continuous_finsetSum _ fun i _ => ((continuous_modeVel hX ι i).norm).pow 2).sqrt

theorem continuous_gradAmp {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) (ι : ℤ × ℤ) :
    Continuous (fun z : ℝ × Space => gradAmp G ι z.1 z.2) := by
  unfold gradAmp cnormSq
  exact (continuous_finsetSum _ fun i _ => ((continuous_modeGrad hG ι i).norm).pow 2).sqrt

theorem continuous_cnormSq_modeVel {X : ℝ → Space → Space} (hX : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (ι : ℤ × ℤ) : Continuous (fun z : ℝ × Space => cnormSq (modeVel ι X z.1 z.2)) := by
  unfold cnormSq
  exact continuous_finsetSum _ fun i _ => ((continuous_modeVel hX ι i).norm).pow 2


theorem meanField_continuous {W : ℝ → Space → Space} (hW : Continuous (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (meanField W) := by
  unfold meanField
  exact continuous_finsetSum _ fun i _ => (Complex.continuous_re.comp
    ((continuous_modeVel hW (0, 0) i).comp (continuous_const.prodMk continuous_id))).smul continuous_const

theorem relativeVelocity_measurable {W : ℝ → Space → Space} (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    {rate : Space → ℝ} (hr : Measurable rate) : Measurable (relativeVelocity W rate) := by
  have h0 : Continuous (fun y : Space => -(y 1) • unitVector 0 + y 0 • unitVector 1) :=
    (((ModeL2Internal.continuous_coord 1).neg).smul continuous_const).add
      ((ModeL2Internal.continuous_coord 0).smul continuous_const)
  have h1 : Measurable (meanField W) := (meanField_continuous hW).measurable
  have h2 : Measurable (fun y : Space => (1 / 2 : ℝ) • y) := (continuous_const_smul (1 / 2 : ℝ)).measurable
  have hsm : Continuous (fun q : ℝ × Space => q.1 • q.2) := continuous_fst.smul continuous_snd
  have h3 : Measurable (fun y : Space => rate y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)) :=
    hsm.measurable.comp (hr.prodMk h0.measurable)
  have h4 : Measurable (fun y : Space => meanField W y + (1 / 2 : ℝ) • y
      - rate y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)) := (h1.add h2).sub h3
  exact h4

theorem dop_measurable_of {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable (fun p : ℝ × Space => ENNReal.ofReal (dopDensity m P v ι p.1 p.2)) := by
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  have hmu : Measurable (fun p : ℝ × Space => m.mu ι p.2) :=
    (continuous_abs.comp (hK.continuous.comp continuous_snd)).measurable
  have hrt : Measurable (fun p : ℝ × Space => m.rate (m.classOf ι) p.2) :=
    (hm.rate_measurable (m.classOf ι)).comp measurable_snd
  have hdop : Measurable (fun p : ℝ × Space => |m.dop P ι p.2|) :=
    continuous_abs.measurable.comp (measurable_const.add (measurable_const.mul hrt))
  have hc : Measurable (fun p : ℝ × Space => cnormSq (modeVel ι v p.1 p.2)) :=
    (continuous_cnormSq_modeVel hv.smooth.continuous ι).measurable
  exact ((hmu.mul hdop).mul hc).ennreal_ofReal

theorem loss_measurable_of {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable (fun p : ℝ × Space => transportLoss m W v ι p.1 p.2) ∧
      Measurable (fun p : ℝ × Space => pressureLoss m W v ι p.1 p.2) := by
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  have hmu : Measurable (fun p : ℝ × Space => m.mu ι p.2) :=
    (continuous_abs.comp (hK.continuous.comp continuous_snd)).measurable
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGv : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  have hGW : Continuous (fun z : ℝ × Space => gradField W z.1 z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hW (by norm_num)).continuous
  have hrel : Measurable (fun p : ℝ × Space => ‖relativeVelocity W (m.rate (m.classOf ι)) p.2‖) :=
    ((relativeVelocity_measurable hWc (hm.rate_measurable (m.classOf ι))).norm).comp measurable_snd
  have hmg : Measurable (fun p : ℝ × Space => m.muGrad ι p.2) :=
    ((measurable_fderiv ℝ (m.muW (m.classOf ι))).norm).comp measurable_snd
  have hrt : Measurable (fun p : ℝ × Space => |m.rate (m.classOf ι) p.2|) :=
    continuous_abs.measurable.comp ((hm.rate_measurable (m.classOf ι)).comp measurable_snd)
  have hga : ∀ κ, Measurable (fun p : ℝ × Space => gradAmp (gradField v) κ p.1 p.2) := fun κ =>
    (continuous_gradAmp hGv κ).measurable
  have hva : ∀ κ, Measurable (fun p : ℝ × Space => velAmp v κ p.1 p.2) := fun κ =>
    (continuous_velAmp hvc κ).measurable
  have hWa : ∀ κ, Measurable (fun p : ℝ × Space => velAmp W κ p.1 p.2) := fun κ =>
    (continuous_velAmp hWc κ).measurable
  have hWg : ∀ κ, Measurable (fun p : ℝ × Space => gradAmp (gradField W) κ p.1 p.2) := fun κ =>
    (continuous_gradAmp hGW κ).measurable
  have hmf : Measurable (fun p : ℝ × Space => ‖fderiv ℝ (meanField W) p.2‖) :=
    ((measurable_fderiv ℝ (meanField W)).norm).comp measurable_snd
  have hs1 : Measurable (fun p : ℝ × Space =>
      ∑ α ∈ m.waves, velAmp W α p.1 p.2 * gradAmp (gradField v) (ι - α) p.1 p.2) :=
    Finset.measurable_sum _ fun α _ => (hWa α).mul (hga (ι - α))
  have hs2 : Measurable (fun p : ℝ × Space =>
      ∑ α ∈ m.waves, gradAmp (gradField W) α p.1 p.2 * velAmp v (ι - α) p.1 p.2) :=
    Finset.measurable_sum _ fun α _ => (hWg α).mul (hva (ι - α))
  refine ⟨?_, ?_⟩
  · unfold transportLoss
    exact ((((hmu.mul hrel).add hmg).mul (hga ι)).mul (hva ι)).add ((hmu.mul hrt).mul ((hva ι).pow_const 2))
      |>.add ((hmu.mul (hva ι)).mul hs1)
  · unfold pressureLoss
    exact measurable_const.mul (((((hmf.pow_const 2).mul ((hva ι).pow_const 2)).add (hs2.pow_const 2)).div_const _).add
      (((measurable_const.mul (hmu.pow_const 2))).mul ((hva ι).pow_const 2)))

end Internal.MuSmooth

end Coercive

end Breakdown
