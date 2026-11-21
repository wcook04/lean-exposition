import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.NNiceField
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.RHeat
import Breakdown.Weak.PairingVelocity
import Breakdown.FreqTr.PairingEmbed
import Breakdown.FreqTr.VelocityInjective

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace MildNiceHeatInternal

def heatSym (α τ : ℝ) (ξ : Space) : ℝ := Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α)))

def traceInv (ξ : Space) : ℝ := (sspFactor ξ)⁻¹

theorem isNiceSymbol_heat (α τ : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => heatSym α τ ξ • m ξ) :=
  Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm (heatSym α τ)
    (fun ξ hξ => by
      have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hne : 2 * π * ‖ξ‖ ≠ 0 := by positivity
      exact (contDiffAt_const.mul
        ((contDiffAt_const.mul (contDiffAt_norm ℝ hξ)).rpow_const_of_ne hne)).neg.exp)
    (fun ξ => by simp [heatSym])

theorem isNiceSymbol_traceInv {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => traceInv ξ • m ξ) :=
  Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm traceInv
    (fun ξ hξ => by
      have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hne : 4 * π ^ 2 * ‖ξ‖ ^ 2 ≠ 0 := by positivity
      exact (contDiffAt_const.mul ((contDiffAt_norm ℝ hξ).pow 2)).inv hne)
    (fun ξ => by simp [traceInv, sspFactor])

theorem negTrace_traceInv {m : Space → CSpace} (hm : IsNiceSymbol m) :
    negSsp (niceField (fun ξ => traceInv ξ • m ξ)) = niceField m := by
  rw [Freq.FracInternal.NiceEmbed.negTraceSecondDeriv_niceField (isNiceSymbol_traceInv hm)]
  congr 1
  funext ξ
  by_cases h : ξ = 0
  · obtain ⟨r, hr, hz⟩ := hm.2.2.1
    have h0 : m ξ = 0 := hz ξ (by rw [h, norm_zero]; exact hr)
    simp [h0]
  · have hp : 0 < ‖ξ‖ := norm_pos_iff.2 h
    have hne : sspFactor ξ ≠ 0 := by unfold sspFactor; positivity
    rw [smul_smul, traceInv, mul_inv_cancel₀ hne, one_smul]

theorem heatField_niceField (α τ : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    heatField α τ (niceField m) = niceField (fun ξ => heatSym α τ ξ • m ξ) := by
  funext y
  rw [← Breakdown.FracInternal.NiceField.fieldS_coe hm]
  unfold heatField
  rw [Breakdown.FracInternal.NiceField.transform_fieldS hm]
  rfl

open Freq.Internal.VelocityInjective in
theorem pairing_nice {ψ : Space → Space} (hψ : IsNiceField ψ) (x : X) :
    inner ℝ x (embedX ψ) = ∫ y, inner ℝ ((velocity x : Space → Space) y) (negSsp ψ y) := by
  have hN := Freq.niceFieldProps (5 / 4) (by norm_num) (by norm_num)
  obtain ⟨-, hψd, hψn, -, -⟩ := hN ψ hψ
  obtain ⟨⟨S, hS⟩, -, -, -, -⟩ := hN _ hψn
  have hG : MemLp (negSsp ψ) (6 / 5) volume := by rw [← hS]; exact S.memLp _ _
  have hE : PairingEmbed := pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2
  let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
  have heq : (fun y : X => inner ℝ y (embedX ψ)) = fun y => P (velocity y) (hG.toLp _) := by
    apply Continuous.ext_on testDense_holds.2 (by fun_prop)
      ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
    intro y hy
    obtain ⟨f, hf, rfl⟩ := testSpan_holds y hy
    show inner ℝ (embedX f) (embedX ψ) = P (velocity (embedX f)) (hG.toLp _)
    have hfd := Internal.VelocityInjective.isDecayField_of_test f hf
    rw [hE f ψ hfd hψd, nicePairingByParts f ψ hfd hψ,
      ← WeakProfile.Internal.PairingVelocity.pairing_eq_lp ψ hG]
    unfold fieldPairing
    apply integral_congr_ae
    filter_upwards [velocityDecay_holds f hfd] with z hz
    rw [hz]
  rw [congrFun heq x, WeakProfile.Internal.PairingVelocity.pairing_eq_lp ψ hG]

theorem heat_embed (α : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) {n : Space → CSpace} (hn : IsNiceSymbol n) :
    fracHeatX α τ (embedX (niceField n)) = embedX (niceField (fun ξ => heatSym α τ ξ • n ξ)) := by
  apply Subtype.ext
  show (fracHeatX α τ (embedX (niceField n)) : L2C) = (embedX (niceField _) : L2C)
  rw [Breakdown.FracInternal.RHeat.opX_coe]
  apply Lp.ext
  filter_upwards [Breakdown.FracInternal.RHeat.op_ae α τ (embedX (niceField n) : L2C),
    niceEmbedSymbol n hn, niceEmbedSymbol _ (isNiceSymbol_heat α τ hn)] with ξ h1 h2 h3
  rw [h1, h2, h3, fracHeatFactor, max_eq_left hτ, heatSym, smul_comm]

end MildNiceHeatInternal

open MildNiceHeatInternal in
theorem niceHeat : NiceHeatStatement := by
  intro α τ _ hτ φ hφ
  obtain ⟨m, hm, rfl⟩ := hφ
  have hem := isNiceSymbol_heat α τ hm
  refine ⟨⟨_, hem, heatField_niceField α τ hm⟩, fun x => ?_⟩
  rw [heatField_niceField α τ hm, ← negTrace_traceInv hm, ← negTrace_traceInv hem,
    ← pairing_nice ⟨_, isNiceSymbol_traceInv hm, rfl⟩,
    ← pairing_nice ⟨_, isNiceSymbol_traceInv hem, rfl⟩, (fracHeatSemigroup α).2.2.2.2.1,
    heat_embed α hτ (isNiceSymbol_traceInv hm)]
  congr 3
  funext ξ
  exact smul_comm _ _ _

end Breakdown.FracCert
