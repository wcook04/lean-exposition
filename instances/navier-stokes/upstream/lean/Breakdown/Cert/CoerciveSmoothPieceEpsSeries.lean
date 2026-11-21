import Breakdown.Cert.CoerciveSmoothPieceEpsNeg
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEps

open Internal.PieceAbsorb in
theorem slab_tsum_eq {f : ℤ × ℤ → ℝ → Space → ℝ}
    (hfm : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f ι z.1 z.2)) volume) :
    ∫⁻ z, ∑' ι, ENNReal.ofReal (f ι z.1 z.2) ∂slabMeasure
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y) := by
  have hfm' : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f ι z.1 z.2)) slabMeasure := by
    intro ι
    rw [slabMeasure_eq]
    exact (hfm ι).restrict
  rw [lintegral_tsum hfm']
  exact tsum_congr fun ι => lintegral_prod _ (hfm' ι)

open Internal.PieceAbsorb in
theorem slab_aem {F : ℝ × Space → ℝ≥0∞} (hF : AEMeasurable F volume) : AEMeasurable F slabMeasure := by
  rw [slabMeasure_eq]
  exact hF.restrict

theorem modeAverage_const_mul {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) (c : ℝ) :
    modeAverage ι (fun τ φ b => c * f τ φ b) b = (c : ℂ) * modeAverage ι f b := by
  unfold modeAverage
  have e : ∀ τ φ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * (((c * f τ φ b : ℝ)) : ℂ) = (c : ℂ) * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ)
        * Complex.I)) * ((f τ φ b : ℝ) : ℂ)) := by
    intro τ φ; push_cast; ring
  simp_rw [e, intervalIntegral.integral_const_mul]
  ring

theorem cnormSq_modeVel_weighted (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) σ y) = (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have e : ∀ i, modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) σ y i
      = (((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * modeVel ι v σ y i := by
    intro i
    unfold modeVel
    rw [← modeAverage_const_mul]
    congr 1
    funext τ φ j
    show (axialRot (-φ) ((1 + ‖axialRot φ y‖)⁻¹ • v (σ + τ) (axialRot φ y))) j = _
    rw [RotationInternal.axialRot_norm]
    rw [show axialRot (-φ) ((1 + ‖y‖)⁻¹ • v (σ + τ) (axialRot φ y))
        = (1 + ‖y‖)⁻¹ • axialRot (-φ) (v (σ + τ) (axialRot φ y)) from
      (RotationInternal.axialRotLinear (-φ)).map_smul _ _]
    rfl
  unfold velAmp
  rw [div_pow, Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)]
  unfold cnormSq
  simp_rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  rw [← Finset.mul_sum]
  field_simp

theorem lintegral_add4 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f1 f2 f3 f4 : α → ℝ≥0∞}
    (h1 : AEMeasurable f1 μ) (h2 : AEMeasurable f2 μ) (h3 : AEMeasurable f3 μ) :
    ∫⁻ z, (f1 z + f2 z + f3 z + f4 z) ∂μ = ∫⁻ z, f1 z ∂μ + ∫⁻ z, f2 z ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z, f4 z ∂μ := by
  calc ∫⁻ z, (f1 z + f2 z + f3 z + f4 z) ∂μ = ∫⁻ z, (f1 z + f2 z + f3 z) ∂μ + ∫⁻ z, f4 z ∂μ :=
        lintegral_add_left' (f := fun z => f1 z + f2 z + f3 z) ((h1.add h2).add h3) f4
    _ = ∫⁻ z, (f1 z + f2 z) ∂μ + ∫⁻ z, f3 z ∂μ + ∫⁻ z, f4 z ∂μ := by
        rw [show ∫⁻ z, (f1 z + f2 z + f3 z) ∂μ = ∫⁻ z, (f1 z + f2 z) ∂μ + ∫⁻ z, f3 z ∂μ from
          lintegral_add_left' (f := fun z => f1 z + f2 z) (h1.add h2) f3]
    _ = _ := by
        rw [show ∫⁻ z, (f1 z + f2 z) ∂μ = ∫⁻ z, f1 z ∂μ + ∫⁻ z, f2 z ∂μ from lintegral_add_left' h1 f2]

theorem series_finite_of_le {f g : ℤ × ℤ → ℝ → Space → ℝ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hle : ∀ ι σ y, ENNReal.ofReal (f ι σ y) ≤ c * ENNReal.ofReal (g ι σ y))
    (hg : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g ι σ y) < ⊤) :
    ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y) < ⊤ := by
  calc ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f ι σ y)
      ≤ ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, c * ENNReal.ofReal (g ι σ y) :=
        ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => hle ι σ y
    _ = c * ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g ι σ y) := by
        simp_rw [lintegral_const_mul' c _ hc]
        rw [ENNReal.tsum_mul_left]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) hg

theorem amplitudeSeries_finite (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))) < ⊤ := by
  have hp := hSP P v hv
  have hG := hp.measurable_gradient
  have hH := hp.measurable_secondDeriv
  have hV := hp.measurable_velocity
  have m1 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2)
  have m2 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2))
      volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((Internal.PieceAbsorb.aem_vortGradAmp hH ι).pow_const 2)
  have m3 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((Internal.PieceAbsorb.aem_gradAmp hG ι).pow_const 2)
  have hden : AEMeasurable (fun z : ℝ × Space => 1 + ‖z.2‖) volume :=
    (continuous_const.add (continuous_norm.comp continuous_snd)).aemeasurable
  have m4 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))
      volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (((Internal.PieceAbsorb.aem_velAmp hV ι).div hden).pow_const 2)
  have hF : AEMeasurable (fun z : ℝ × Space =>
      (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))) Internal.PieceAbsorb.slabMeasure :=
    slab_aem ((((AEMeasurable.tsum m1).add (AEMeasurable.tsum m2)).add (AEMeasurable.tsum m3)).add
      (AEMeasurable.tsum m4))
  rw [← lintegral_prod _ hF]
  have E1 : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) ∂Internal.PieceAbsorb.slabMeasure
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2) :=
    slab_tsum_eq (f := fun ι σ y => vortAmp (gradField v) ι σ y ^ 2) m1
  have E2 : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι z.1 z.2 ^ 2))
        ∂Internal.PieceAbsorb.slabMeasure
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2) :=
    slab_tsum_eq (f := fun ι σ y => vortGradAmp (secondDerivField v) ι σ y ^ 2) m2
  have E3 : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)) ∂Internal.PieceAbsorb.slabMeasure
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2) :=
    slab_tsum_eq (f := fun ι σ y => gradAmp (gradField v) ι σ y ^ 2) m3
  have E4 : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))
        ∂Internal.PieceAbsorb.slabMeasure
      = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) :=
    slab_tsum_eq (f := fun ι σ y => (velAmp v ι σ y / (1 + ‖y‖)) ^ 2) m4
  refine lt_of_eq_of_lt (lintegral_add4 (slab_aem (AEMeasurable.tsum m1)) (slab_aem (AEMeasurable.tsum m2))
    (slab_aem (AEMeasurable.tsum m3))) ?_
  simp only [E1, E2, E3, E4]
  have hGpar := hPars.2.1 (gradField v) hG hp.periodic_gradient hp.gradient_finite
  have hHfin : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ :=
    lt_of_le_of_lt (perturbationSecondDerivBoundHolds_proof ∅ P v _ _ _ hp) hp.sumSecondPartials_finite
  have hHpar := hPars.2.2.1 (secondDerivField v) hH hp.periodic_secondDeriv hHfin
  have f3 : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2) < ⊤ := by
    have e : ∀ ι σ y, gradAmp (gradField v) ι σ y ^ 2 = cnormSq (modeGrad ι (gradField v) σ y) := fun ι σ y =>
      Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)
    simp_rw [e]
    rw [← hGpar]
    exact hp.gradient_finite
  have f1 : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2) < ⊤ := by
    refine series_finite_of_le (c := ENNReal.ofReal 243) ENNReal.ofReal_ne_top (g := fun ι σ y =>
      gradAmp (gradField v) ι σ y ^ 2) (fun ι σ y => ?_) f3
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [vortAmp, gradAmp, Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _),
      Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)]
    exact Internal.PieceAbsorb.cnormSq_curlOfGrad_le _
  have f2 : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2) < ⊤ := by
    refine series_finite_of_le (c := ENNReal.ofReal 729) ENNReal.ofReal_ne_top (g := fun ι σ y =>
      cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)) (fun ι σ y => ?_) ?_
    · rw [← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [vortGradAmp, Real.sq_sqrt (Internal.PieceAbsorb.cnormSq_nonneg' _)]
      exact Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le _
    · rw [← hHpar]; exact hHfin
  have f4 : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) < ⊤ := by
    set X : ℝ → Space → Space := fun s x => (1 + ‖x‖)⁻¹ • v s x with hX
    have hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume :=
      ((continuous_const.add (continuous_norm.comp continuous_snd)).inv₀
        (fun z => (by linarith [norm_nonneg z.2] : (0 : ℝ) < 1 + ‖z.2‖).ne')).aestronglyMeasurable.smul hV
    have hXp : IsTimePeriodic X := fun σ y => by simp only [hX, hv.periodic σ y]
    have hXn : ∀ σ y, ‖X σ y‖ ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := fun σ y => by
      have hr : 0 < 1 + ‖y‖ := by positivity
      simp only [hX, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
      field_simp
    have hXf : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
      simp_rw [hXn]; exact hv.weighted_finite
    have hXpar := hPars.1 X hXm hXp hXf
    simp_rw [← cnormSq_modeVel_weighted]
    rw [← hXpar]
    exact hXf
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨f1, f2⟩, f3⟩, f4⟩

open Internal.PieceAbsorb in
theorem iterated_add3_lt_top {f1 f2 f3 : ℝ × Space → ℝ≥0∞} (h1 : AEMeasurable f1 volume)
    (h2 : AEMeasurable f2 volume) (h3 : AEMeasurable f3 volume) {c1 c2 c3 : ℝ≥0∞} (hc1 : c1 ≠ ⊤) (hc2 : c2 ≠ ⊤)
    (hc3 : c3 ≠ ⊤) (t1 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f1 (σ, y) < ⊤)
    (t2 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f2 (σ, y) < ⊤) (t3 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f3 (σ, y) < ⊤) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (c1 * f1 (σ, y) + c2 * f2 (σ, y) + c3 * f3 (σ, y)) < ⊤ := by
  have s1 := slab_aem h1
  have s2 := slab_aem h2
  have s3 := slab_aem h3
  have hF : AEMeasurable (fun z => c1 * f1 z + c2 * f2 z + c3 * f3 z) slabMeasure :=
    ((s1.const_mul c1).add (s2.const_mul c2)).add (s3.const_mul c3)
  refine lt_of_eq_of_lt (lintegral_prod (fun z => c1 * f1 z + c2 * f2 z + c3 * f3 z) hF).symm ?_
  have e : ∫⁻ z, (c1 * f1 z + c2 * f2 z + c3 * f3 z) ∂slabMeasure
      = c1 * ∫⁻ z, f1 z ∂slabMeasure + c2 * ∫⁻ z, f2 z ∂slabMeasure + c3 * ∫⁻ z, f3 z ∂slabMeasure := by
    calc ∫⁻ z, (c1 * f1 z + c2 * f2 z + c3 * f3 z) ∂slabMeasure
        = ∫⁻ z, (c1 * f1 z + c2 * f2 z) ∂slabMeasure + ∫⁻ z, c3 * f3 z ∂slabMeasure :=
          lintegral_add_left' (f := fun z => c1 * f1 z + c2 * f2 z) ((s1.const_mul c1).add (s2.const_mul c2)) _
      _ = ∫⁻ z, c1 * f1 z ∂slabMeasure + ∫⁻ z, c2 * f2 z ∂slabMeasure + ∫⁻ z, c3 * f3 z ∂slabMeasure := by
          rw [show ∫⁻ z, (c1 * f1 z + c2 * f2 z) ∂slabMeasure
              = ∫⁻ z, c1 * f1 z ∂slabMeasure + ∫⁻ z, c2 * f2 z ∂slabMeasure from
            lintegral_add_left' (f := fun z => c1 * f1 z) (s1.const_mul c1) _]
      _ = _ := by rw [lintegral_const_mul' c1 f1 hc1, lintegral_const_mul' c2 f2 hc2, lintegral_const_mul' c3 f3 hc3]
  rw [e]
  have u1 : ∫⁻ z, f1 z ∂slabMeasure < ⊤ := by rw [lintegral_prod f1 s1]; exact t1
  have u2 : ∫⁻ z, f2 z ∂slabMeasure < ⊤ := by rw [lintegral_prod f2 s2]; exact t2
  have u3 : ∫⁻ z, f3 z ∂slabMeasure < ⊤ := by rw [lintegral_prod f3 s3]; exact t3
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc1) u1,
    ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc2) u2⟩, ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc3) u3⟩

end Internal.SmoothPieceEps

end Coercive

end Breakdown
