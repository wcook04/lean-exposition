import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageLinear

open Internal.ModeRotation

theorem axialRot_sub (φ : ℝ) (a c : Space) : axialRot φ (a - c) = axialRot φ a - axialRot φ c := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem modeAverage_sub {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b : β)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2 b) boxMeasure)
    (hg : Integrable (fun p : ℝ × ℝ => g p.1 p.2 b) boxMeasure) :
    modeAverage ι (fun τ φ b => f τ φ b - g τ φ b) b = modeAverage ι f b - modeAverage ι g b := by
  have hint : ∀ {h : ℝ → ℝ → β → ℝ}, Integrable (fun p : ℝ × ℝ => h p.1 p.2 b) boxMeasure →
      Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((h p.1 p.2 b : ℝ) : ℂ)) boxMeasure := by
    intro h hh
    refine hh.norm.mono' ((continuous_expFactor ι).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.1)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]
  have hfg : Integrable (fun p : ℝ × ℝ => f p.1 p.2 b - g p.1 p.2 b) boxMeasure := hf.sub hg
  rw [modeAverage_eq, modeAverage_eq, modeAverage_eq,
    iter_eq_prod (fun τ φ => expFactor ι τ φ * ((f τ φ b - g τ φ b : ℝ) : ℂ)) (hint (h := fun τ φ b => f τ φ b - g τ φ b) hfg),
    iter_eq_prod (fun τ φ => expFactor ι τ φ * ((f τ φ b : ℝ) : ℂ)) (hint hf),
    iter_eq_prod (fun τ φ => expFactor ι τ φ * ((g τ φ b : ℝ) : ℂ)) (hint hg),
    ← mul_sub, ← integral_sub (hint hf) (hint hg)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  push_cast
  ring

theorem modeVel_sub {v₁ v₂ : ℝ → Space → Space} {z : ℝ × Space}
    (h₁ : Integrable (fun p : ℝ × ℝ => v₁ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (h₂ : Integrable (fun p : ℝ × ℝ => v₂ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ι : ℤ × ℤ) :
    modeVel ι (fun σ y => v₁ σ y - v₂ σ y) z.1 z.2 = modeVel ι v₁ z.1 z.2 - modeVel ι v₂ z.1 z.2 := by
  funext i
  unfold modeVel
  rw [Pi.sub_apply, ← modeAverage_sub ι _ _ i (integrable_velComponent axialRotationHolds_proof h₁ i)
    (integrable_velComponent axialRotationHolds_proof h₂ i)]
  congr 1
  funext τ φ j
  rw [axialRot_sub, PiLp.sub_apply]

theorem modeGrad_sub {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {z : ℝ × Space}
    (h₁ : Integrable (fun p : ℝ × ℝ => G₁ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (h₂ : Integrable (fun p : ℝ × ℝ => G₂ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ι : ℤ × ℤ) :
    modeGrad ι (fun σ y => G₁ σ y - G₂ σ y) z.1 z.2 = modeGrad ι G₁ z.1 z.2 - modeGrad ι G₂ z.1 z.2 := by
  funext ij
  unfold modeGrad
  rw [Pi.sub_apply, ← modeAverage_sub ι _ _ ij (integrable_gradComponent axialRotationHolds_proof h₁ ij)
    (integrable_gradComponent axialRotationHolds_proof h₂ ij)]
  congr 1
  funext τ φ kl
  rw [sub_apply, axialRot_sub, PiLp.sub_apply]

theorem curlOfGrad_sub (g₁ g₂ : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (g₁ - g₂) = curlOfGrad g₁ - curlOfGrad g₂ := by
  funext i
  simp only [curlOfGrad, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem cdot_sub_left (x₁ x₂ z : Fin 3 → ℂ) : cdot (x₁ - x₂) z = cdot x₁ z - cdot x₂ z := by
  simp only [cdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ae_mode_sub {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {v₁ v₂ : ℝ → Space → Space}
    {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g₁ g₂ : ℝ → Space → Space} (h₁ : IsPerturbation Γ₁ P v₁ G₁ H₁ g₁) (h₂ : IsPerturbation Γ₂ P v₂ G₂ H₂ g₂) :
    ∀ᵐ z : ℝ × Space, ∀ ι : ℤ × ℤ,
      modeVel ι (fun σ y => v₁ σ y - v₂ σ y) z.1 z.2 = modeVel ι v₁ z.1 z.2 - modeVel ι v₂ z.1 z.2 ∧
      modeGrad ι (fun σ y => G₁ σ y - G₂ σ y) z.1 z.2 = modeGrad ι G₁ z.1 z.2 - modeGrad ι G₂ z.1 z.2 := by
  obtain ⟨lv₁, lG₁, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ₁ P v₁ G₁ H₁ g₁ h₁
  obtain ⟨lv₂, lG₂, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ₂ P v₂ G₂ H₂ g₂ h₂
  filter_upwards [ae_integrable_orbit axialRotationHolds_proof lv₁, ae_integrable_orbit axialRotationHolds_proof lv₂,
    ae_integrable_orbit axialRotationHolds_proof lG₁, ae_integrable_orbit axialRotationHolds_proof lG₂]
    with z a₁ a₂ b₁ b₂
  exact fun ι => ⟨modeVel_sub a₁ a₂ ι, modeGrad_sub b₁ b₂ ι⟩

theorem ae_period {p : ℝ × Space → Prop} (h : ∀ᵐ z : ℝ × Space, p z) :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)), p z := by
  rw [Internal.Field.period_measure_eq]
  exact ae_restrict_of_ae h

theorem modeTerm_sub {C : Type} (m : ModeWeights C) {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {v₁ v₂ : ℝ → Space → Space}
    {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g₁ g₂ : ℝ → Space → Space} (h₁ : IsPerturbation Γ₁ P v₁ G₁ H₁ g₁) (h₂ : IsPerturbation Γ₂ P v₂ G₂ H₂ g₂)
    (ψ : ℝ → Space → Space) :
    ∀ᵐ z : ℝ × Space, ∀ ι : ℤ × ℤ,
      Internal.Field.termEps m (fun σ y => G₁ σ y - G₂ σ y) ψ ι z.1 z.2
          + Internal.Field.termMu m (fun σ y => v₁ σ y - v₂ σ y) ψ ι z.1 z.2 =
        (Internal.Field.termEps m G₁ ψ ι z.1 z.2 + Internal.Field.termMu m v₁ ψ ι z.1 z.2)
          - (Internal.Field.termEps m G₂ ψ ι z.1 z.2 + Internal.Field.termMu m v₂ ψ ι z.1 z.2) := by
  filter_upwards [ae_mode_sub h₁ h₂] with z hz
  intro ι
  obtain ⟨e1, e2⟩ := hz ι
  unfold Internal.Field.termEps Internal.Field.termMu
  rw [e1, e2, curlOfGrad_sub, cdot_sub_left, cdot_sub_left, mul_sub, mul_sub, Complex.sub_re, Complex.sub_re]
  ring

theorem fieldModeSum_sub (hPars : ModeSquareSumHolds) {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C}
    {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {Γ₁ Γ₂ : Set Symmetry} {v₁ v₂ : ℝ → Space → Space}
    {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g₁ g₂ : ℝ → Space → Space} (h₁ : IsPerturbation Γ₁ P v₁ G₁ H₁ g₁) (h₂ : IsPerturbation Γ₂ P v₂ G₂ H₂ g₂)
    {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Internal.Field.fieldModeSum m (fun σ y => v₁ σ y - v₂ σ y) (fun σ y => G₁ σ y - G₂ σ y) ψ =
      Internal.Field.fieldModeSum m v₁ G₁ ψ - Internal.Field.fieldModeSum m v₂ G₂ ψ := by
  have hL := perturbationLocalSquareIntegrabilityHolds_proof
  have hD := PassageCommon.isPerturbation_sub h₁ h₂
  have hae := ae_period (modeTerm_sub m h₁ h₂ ψ)
  rw [Internal.Field.fieldModeSum_eq, Internal.Field.fieldModeSum_eq, Internal.Field.fieldModeSum_eq]
  have key : ∀ ι, (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      (Internal.Field.termEps m (fun σ y => G₁ σ y - G₂ σ y) ψ ι σ y
        + Internal.Field.termMu m (fun σ y => v₁ σ y - v₂ σ y) ψ ι σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Internal.Field.termEps m G₁ ψ ι σ y + Internal.Field.termMu m v₁ ψ ι σ y))
        - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
          (Internal.Field.termEps m G₂ ψ ι σ y + Internal.Field.termMu m v₂ ψ ι σ y) := by
    intro ι
    have i1 := Internal.Field.fieldModeTerm_integrable hPars hL hm h₁ hψ ι
    have i2 := Internal.Field.fieldModeTerm_integrable hPars hL hm h₂ hψ ι
    have i3 := Internal.Field.fieldModeTerm_integrable hPars hL hm hD hψ ι
    rw [← integral_prod _ i1, ← integral_prod _ i2, ← integral_prod _ i3, ← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    exact hz ι
  simp_rw [key]
  exact (Internal.Field.fieldModeTerm_summable hPars hL hm h₁ hψ).tsum_sub
    (Internal.Field.fieldModeTerm_summable hPars hL hm h₂ hψ)

theorem secondDerivPart_sub {Γ₁ Γ₂ : Set Symmetry} {P : ℝ} {v₁ v₂ : ℝ → Space → Space}
    {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g₁ g₂ : ℝ → Space → Space} (h₁ : IsPerturbation Γ₁ P v₁ G₁ H₁ g₁) (h₂ : IsPerturbation Γ₂ P v₂ G₂ H₂ g₂)
    {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₁ σ y - H₂ σ y)) (ψ σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₁ σ y)) (ψ σ y))
        - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₂ σ y)) (ψ σ y) := by
  have hI : ∀ {Γ : Set Symmetry} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
      {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space},
      IsPerturbation Γ P v G H g →
      Integrable (fun z : ℝ × Space => inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ z.1 z.2))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    intro Γ v G H g hv
    have hF : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
      (Internal.Field.secondDerivTrace_continuous.comp_aestronglyMeasurable hv.measurable_secondDeriv).neg
    have hF2 : periodLIntegral (fun σ y => ‖-secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
      simpa only [norm_neg] using hv.sumSecondPartials_finite
    exact Internal.Field.pairing_integrable (F := fun σ y => -secondDerivTrace (H σ y)) (M := ψ) hF
      (Internal.Field.testField_aestronglyMeasurable hψ) hF2 (Internal.Field.testField_sq_lt_top hψ)
  have i1 := hI h₁
  have i2 := hI h₂
  have i3 := hI (PassageCommon.isPerturbation_sub h₁ h₂)
  rw [← integral_prod _ i1, ← integral_prod _ i2, ← integral_prod _ i3, ← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [PassageCommon.secondDerivTrace_sub, neg_sub, inner_sub_left, inner_neg_left]
  ring

theorem multiplier_difference_pairing (hPars : ModeSquareSumHolds) {C : Type} {m : ModeWeights C} {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    {Γ₁ Γ₂ : Set Symmetry} {v₁ v₂ : ℝ → Space → Space}
    {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g₁ g₂ : ℝ → Space → Space} (h₁ : IsPerturbation Γ₁ P v₁ G₁ H₁ g₁) (h₂ : IsPerturbation Γ₂ P v₂ G₂ H₂ g₂)
    {M₁ M₂ M₃ : ℝ → Space → Space} (hM₁ : m.IsMultiplierField v₁ G₁ H₁ M₁) (hM₂ : m.IsMultiplierField v₂ G₂ H₂ M₂)
    (hM₃ : m.IsMultiplierField (fun σ y => v₁ σ y - v₂ σ y) (fun σ y => G₁ σ y - G₂ σ y)
      (fun σ y => H₁ σ y - H₂ σ y) M₃)
    {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y - M₂ σ y - M₃ σ y) (ψ σ y) = 0 := by
  have hT := Internal.Field.testField_aestronglyMeasurable hψ
  have hT2 := Internal.Field.testField_sq_lt_top hψ
  have i1 := Internal.Field.pairing_integrable hM₁.1 hT hM₁.2.2.1 hT2
  have i2 := Internal.Field.pairing_integrable hM₂.1 hT hM₂.2.2.1 hT2
  have i3 := Internal.Field.pairing_integrable hM₃.1 hT hM₃.2.2.1 hT2
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y) (ψ σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₁ σ y)) (ψ σ y))
        + Internal.Field.fieldModeSum m v₁ G₁ ψ := hM₁.2.2.2.2 ψ hψ
  have e2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₂ σ y) (ψ σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₂ σ y)) (ψ σ y))
        + Internal.Field.fieldModeSum m v₂ G₂ ψ := hM₂.2.2.2.2 ψ hψ
  have e3 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₃ σ y) (ψ σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H₁ σ y - H₂ σ y)) (ψ σ y))
        + Internal.Field.fieldModeSum m (fun σ y => v₁ σ y - v₂ σ y) (fun σ y => G₁ σ y - G₂ σ y) ψ :=
    hM₃.2.2.2.2 ψ hψ
  have hsplit : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y - M₂ σ y - M₃ σ y) (ψ σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y) (ψ σ y))
        - (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₂ σ y) (ψ σ y))
        - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₃ σ y) (ψ σ y) := by
    have i123 : Integrable (fun z : ℝ × Space => inner ℝ (M₁ z.1 z.2 - M₂ z.1 z.2 - M₃ z.1 z.2) (ψ z.1 z.2))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
      refine ((i1.sub i2).sub i3).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply, inner_sub_left]
    rw [← integral_prod _ i1, ← integral_prod _ i2, ← integral_prod _ i3, ← integral_prod _ i123]
    calc (∫ z, inner ℝ (M₁ z.1 z.2 - M₂ z.1 z.2 - M₃ z.1 z.2) (ψ z.1 z.2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
        = ∫ z, ((inner ℝ (M₁ z.1 z.2) (ψ z.1 z.2) - inner ℝ (M₂ z.1 z.2) (ψ z.1 z.2))
            - inner ℝ (M₃ z.1 z.2) (ψ z.1 z.2))
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [inner_sub_left]
      _ = (∫ z, (inner ℝ (M₁ z.1 z.2) (ψ z.1 z.2) - inner ℝ (M₂ z.1 z.2) (ψ z.1 z.2))
            ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
          - ∫ z, inner ℝ (M₃ z.1 z.2) (ψ z.1 z.2)
            ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := integral_sub (i1.sub i2) i3
      _ = _ := by rw [integral_sub i1 i2]
  rw [hsplit, e1, e2, e3, secondDerivPart_sub h₁ h₂ hψ, fieldModeSum_sub hPars hm h₁ h₂ hψ]
  ring

end Internal.DensityPassageLinear

end Coercive

end Breakdown
