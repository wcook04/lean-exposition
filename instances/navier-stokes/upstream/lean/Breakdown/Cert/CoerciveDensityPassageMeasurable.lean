import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.CoerciveSmoothDensityMeasure
import Breakdown.Cert.CoerciveSmoothDensityIntegrable

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassage

open PairingSplitInternal (periodMeasure)

theorem splitLeft_aemeasurable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C}
    {w : Space → ℝ} {W v : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        AEMeasurable (fun y => splitLeft (fun σ y ι => modePos m P v (gradField v) ι σ y)
          (fun σ y ι => modeRest m w W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0)
          (stretchForm W v (gradField v)) σ y) volume) ∧
      AEMeasurable (fun σ => ∫⁻ y, splitLeft (fun σ y ι => modePos m P v (gradField v) ι σ y)
          (fun σ y ι => modeRest m w W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0)
          (stretchForm W v (gradField v)) σ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hJ : AEMeasurable (fun z : ℝ × Space => stretchForm W v (gradField v) z.1 z.2) periodMeasure :=
    (Internal.SmoothDensity.stretch_integrable hv hW hWdecay).aestronglyMeasurable.aemeasurable
  have hf : AEMeasurable (fun z : ℝ × Space => splitLeft (fun σ y ι => modePos m P v (gradField v) ι σ y)
      (fun σ y ι => modeRest m w W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0)
      (stretchForm W v (gradField v)) z.1 z.2) periodMeasure := by
    unfold splitLeft
    refine (((AEMeasurable.ennreal_tsum fun ι => ?_).add (AEMeasurable.ennreal_tsum fun ι => ?_)).add
      aemeasurable_const).add hJ.ennreal_ofReal
    · exact ((Internal.SmoothDensity.aesm_epsPos hm hv ι).aemeasurable.add
        (Internal.SmoothDensity.aesm_muPos hm hv ι).aemeasurable).ennreal_ofReal
    · exact (((Internal.SmoothDensity.aesm_base hm hv ι).aemeasurable.add
        (Internal.SmoothDensity.aesm_epsRest hm hW hv ι).aemeasurable).add
        (Internal.SmoothDensity.aesm_muRest hm hW hv ι).aemeasurable).ennreal_ofReal
  refine ⟨?_, hf.lintegral_prod_right'⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with σ hσ
  exact ⟨fun y => hf.mk _ (σ, y), hf.measurable_mk.comp measurable_prodMk_left, hσ⟩

end Internal.DensityPassage

end Coercive

end Breakdown
