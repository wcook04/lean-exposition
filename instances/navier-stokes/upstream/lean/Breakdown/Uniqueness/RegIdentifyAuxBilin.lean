import Breakdown.Uniqueness.RegEmbed
import Breakdown.Uniqueness.RegBounds
import Breakdown.Uniqueness.RegIdentifyAuxAdvect
import Breakdown.Uniqueness.RegIdentifyAuxSymbol
import Breakdown.Uniqueness.RegIdentifyAuxDivFree

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq
theorem coe_bilinX_physField (hR : FieldOpRealized) (hB : BilinH1Formula)
    {f : Space → CSpace} (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f)
    (hf : ∀ m, hsNormSq m f < ⊤) {τ : ℝ} (hτ : 0 < τ) :
    ((bilinX τ (embedX (physField f)) (embedX (physField f)) : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((phiFactor τ ξ : ℝ) : ℂ) • nonlinSymbol f ξ := by
  have hH1f := isH1Field_physField hm hs hf
  have hbd : ∃ C, ∀ x, ‖physField f x‖ ≤ C ∧ ‖fderiv ℝ (physField f) x‖ ≤ C :=
    ⟨max (freqL1Norm f).toReal (2 * π * (gradFreqL1Norm f).toReal), fun x =>
      ⟨(norm_physField_le hm (hf 3) x).trans (le_max_left _ _),
        (norm_fderiv_physField_le hm (hf 3) x).trans (le_max_right _ _)⟩⟩
  have hadv := advectionAt_physField_eq hm hs hf
  rw [hB _ hH1f hbd τ hτ, hadv]
  have hL := coe_heatDivFree_physField hR (memLp_one_advectionSymbol hm hs hf)
    (memLp_two_advectionSymbol hm hs hf) (advectionSymbol_neg hm hs hf) hτ
  have hn := Lp.coeFn_neg ((heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C)
  filter_upwards [hL, hn] with ξ h1 h2
  have h3 : (((-heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C) :
      Space → CSpace) ξ =
      -(((heatDivFree τ (toLpOrZero 2 (physField (advectionSymbol f))) : X) : L2C) :
        Space → CSpace) ξ := h2
  rw [h3, h1, nonlinSymbol, smul_neg]

end Breakdown.SmoothFlow
