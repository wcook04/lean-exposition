import Breakdown.CertCell.AssemblyPotentialModelFrameFactsGiven

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation
  Coercive.StretchInternal Coercive.RotationInternal

private theorem fiber_section {E : Type*} [NormedAddCommGroup E] {u : ℝ × Space → E}
    (hu : AEStronglyMeasurable u volume) {Φ : ℝ × E → ℝ} (hΦ : Continuous Φ) {K : CellBox} (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      AEStronglyMeasurable (fun z : ℝ × ℝ => Φ (z.2, u (z.1, axialRot z.2 (planePoint p)))) boxMeasure := by
  filter_upwards [(rect_ac_halfPlane K hK).ae_le (ae_aestronglyMeasurable_orbit hu)] with p hp
  have h := hΦ.comp_aestronglyMeasurable (continuous_snd.aestronglyMeasurable.prodMk hp)
  exact h.mono_ac boxMeasure_ac

private theorem mean_section {E : Type*} [NormedAddCommGroup E] {u : ℝ × Space → E}
    (hu : AEStronglyMeasurable u volume) {Φ : ℝ × E → ℝ} (hΦ : Continuous Φ) {K : CellBox} (hK : IsCellBox K)
    (β : ℤ × ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor β τ φ * ((Φ (φ, u (τ, axialRot φ (planePoint p))) : ℝ) : ℂ)) (volume.restrict K.rect) := by
  have hac : (volume.restrict K.rect).prod boxMeasure
      ≪ (volume.restrict halfPlane).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.AbsolutelyContinuous.prod (rect_ac_halfPlane K hK) boxMeasure_ac
  have hq := quasiMeasurePreserving_orbitPair.mono_left hac
  have hU : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => u (w.2.1, axialRot w.2.2 (planePoint w.1)))
      ((volume.restrict K.rect).prod boxMeasure) := hu.comp_quasiMeasurePreserving hq
  have hΦ' : Continuous (fun x : (ℝ × ℝ) × E => Φ (x.1.2, x.2)) :=
    hΦ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hE : Continuous (fun x : (ℝ × ℝ) × E => expFactor β x.1.1 x.1.2) := by
    unfold expFactor
    fun_prop
  have hc : Continuous (fun x : (ℝ × ℝ) × E => expFactor β x.1.1 x.1.2 * ((Φ (x.1.2, x.2) : ℝ) : ℂ)) :=
    hE.mul (Complex.continuous_ofReal.comp hΦ')
  have hsnd : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.2) ((volume.restrict K.rect).prod boxMeasure) :=
    continuous_snd.aestronglyMeasurable
  have hpair := hsnd.prodMk hU
  have hf := hc.comp_aestronglyMeasurable hpair
  have hf' := hf.comp_measurePreserving (measurePreserving_prodAssoc (volume.restrict K.rect)
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
  have hh := hf'.integral_prod_right'.integral_prod_right'
  have e1 : (0 : ℝ) ≤ 1 := zero_le_one
  have e2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine hh.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [intervalIntegral.integral_of_le e1, intervalIntegral.integral_of_le e2, Function.comp_apply]
  rfl

theorem gradSection : GradSectionStatement := by
  intro F hF K hK
  refine ⟨?_, fun m ι ab => ?_⟩
  · have hall : ∀ a b : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect),
        AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad F (planePoint p) z.1 z.2 a b) boxMeasure := by
      intro a b
      have hc : Continuous (fun x : ℝ × (Space →L[ℝ] Space) => axialRot (-x.1) (x.2 (axialRot x.1 (unitVector b))) a) := by
        unfold axialRot
        fun_prop
      exact fiber_section hF hc hK
    simp only [ae_all_iff] at hall ⊢
    exact hall
  · have hc : Continuous (fun x : ℝ × (Space →L[ℝ] Space) =>
        axialRot (-x.1) (x.2 (axialRot x.1 (unitVector ab.2))) ab.1) := by
      unfold axialRot
      fun_prop
    have h := (mean_section hF hc hK (labelHarmonic m ι)).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [labelGrad]
    rw [show ab = (ab.1, ab.2) from rfl, modeGrad_zero_eq]
    rfl

theorem secondDerivSection : SecondDerivSectionStatement := by
  intro H hH K hK
  refine ⟨?_, fun m ι abc => ?_⟩
  · have hall : ∀ a b c : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect),
        AEStronglyMeasurable (fun z : ℝ × ℝ => frameSecondDeriv H (planePoint p) z.1 z.2 a b c) boxMeasure := by
      intro a b c
      have hc : Continuous (fun x : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
          axialRot (-x.1) (x.2 (axialRot x.1 (unitVector b)) (axialRot x.1 (unitVector c))) a) := by
        unfold axialRot
        fun_prop
      exact fiber_section hH hc hK
    simp only [ae_all_iff] at hall ⊢
    exact hall
  · have hc : Continuous (fun x : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-x.1) (x.2 (axialRot x.1 (unitVector abc.2.1)) (axialRot x.1 (unitVector abc.2.2))) abc.1) := by
      unfold axialRot
      fun_prop
    have h := (mean_section hH hc hK (labelHarmonic m ι)).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [labelHess]
    rw [show abc = (abc.1, abc.2.1, abc.2.2) from rfl, modeSecondDeriv_zero_eq]
    rfl

end Internal

end Assembly

end CertCell

end Breakdown
