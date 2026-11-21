import Breakdown.Cert.CoerciveFrequencySeminormWeightSlice
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

theorem weighted_velocity_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖ ^ 2)) < ⊤ := by
  unfold periodLIntegral
  calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, 4 * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free,
          ae_restrict_of_ae hv.sixth_power,
          Breakdown.Coercive.Internal.PerturbationFacts.ae_matSq_lt_top hv] with σ h1 h2 h3 h4
        exact slice_weighted_sq_le h1 h2 h3 h4
    _ = 4 * periodLIntegral (fun σ y => matSq (G σ y)) := lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hv.gradient_finite

end Internal

end FrequencySeminorm

end Coercive

end Breakdown
