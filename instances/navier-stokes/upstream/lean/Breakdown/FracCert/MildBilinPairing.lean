import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.NNiceField
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.RExports
import Breakdown.Weak.PairingVelocity

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

private theorem nice_zero {m : Space → CSpace} (hm : IsNiceSymbol m) : m 0 = 0 := by
  obtain ⟨r, hr, hz⟩ := hm.2.2.1
  exact hz 0 (by simpa using hr)

private theorem sqFactor_pos {ξ : Space} (h : ξ ≠ 0) : 0 < sspFactor ξ := by
  have : 0 < ‖ξ‖ := norm_pos_iff.2 h
  unfold sspFactor
  positivity

private theorem nice_inv {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => (sspFactor ξ)⁻¹ • m ξ) :=
  Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm (fun ξ => (sspFactor ξ)⁻¹)
    (fun ξ hξ => by
      have h : ContDiffAt ℝ ∞ (fun ξ : Space => 4 * π ^ 2 * ‖ξ‖ ^ 2) ξ :=
        contDiffAt_const.mul ((contDiffAt_norm ℝ hξ).pow 2)
      exact h.inv (sqFactor_pos hξ).ne')
    (fun ξ => by simp [sspFactor])

private theorem secondOrder_inv {m : Space → CSpace} (hm : IsNiceSymbol m) :
    negSsp (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ)) = niceField m := by
  rw [Freq.FracInternal.NiceEmbed.negTraceSecondDeriv_niceField (nice_inv hm)]
  congr 1
  funext ξ
  rcases eq_or_ne ξ 0 with h | h
  · subst h
    simp [nice_zero hm]
  · rw [smul_smul, mul_inv_cancel₀ (sqFactor_pos h).ne', one_smul]

private theorem nice_heat (α τ : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) • m ξ) :=
  Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm (fun ξ => Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))))
    (fun ξ hξ => by
      have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have h1 : ContDiffAt ℝ ∞ (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) ξ :=
        (contDiffAt_const.mul (contDiffAt_norm ℝ hξ)).rpow_const_of_ne (by positivity)
      exact Real.contDiff_exp.contDiffAt.comp ξ (contDiffAt_const.mul h1).neg)
    (fun ξ => by simp)

private theorem heatField_nice (α τ : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    heatField α τ (niceField m) =
      niceField (fun ξ => Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) • m ξ) := by
  funext y
  rw [heatField, ← Breakdown.FracInternal.NiceField.fieldS_coe hm,
    Breakdown.FracInternal.NiceField.transform_fieldS hm]
  rfl

private theorem scalar_eq (α τ : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ : Space) :
    fracPhiFactor α τ ξ • ((2 * π * ‖ξ‖) • ((sspFactor ξ)⁻¹ • m ξ)) =
      Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) • m ξ := by
  rcases eq_or_ne ξ 0 with h | h
  · subst h
    simp [nice_zero hm]
  · have hp : 0 < ‖ξ‖ := norm_pos_iff.2 h
    rw [smul_smul, smul_smul]
    congr 1
    unfold fracPhiFactor sspFactor
    field_simp
    norm_num

private theorem phi_nice {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) {m : Space → CSpace}
    (hm : IsNiceSymbol m) :
    (fracPhiX α τ (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ))) : Space → Space)
      =ᵐ[volume] niceField (fun ξ => Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) • m ξ) := by
  have hn := nice_heat α τ hm
  set S := Breakdown.FracInternal.NiceField.symbolS hn with hSdef
  have hmul : Breakdown.FracInternal.fracPhiMul α τ
      (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ)) : L2C) = S.toLp 2 := by
    apply Lp.ext
    filter_upwards [Breakdown.FracInternal.fracPhiMul_ae hα hτ _,
      niceEmbedSymbol _ (nice_inv hm), S.coeFn_toLp 2 volume] with ξ h1 h2 h3
    rw [h1, h2, h3, Breakdown.FracInternal.NiceField.symbolS_coe]
    exact scalar_eq α τ hm ξ
  have e : fracPhiX α τ (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ))) = toPhys (S.toLp 2) := by
    rw [← hmul]
    rfl
  have e2 : (freqTrL2.symm (S.toLp 2) : L2C) = (𝓕⁻ S).toLp 2 := by
    rw [← SchwartzMap.toLp_fourierInv_eq]
    rfl
  rw [e]
  filter_upwards [Internal.VelocityInvert.l2Iso_toPhys_ae (S.toLp 2),
    (𝓕⁻ S).coeFn_toLp 2 volume] with x h1 h2
  rw [h1, e2, h2, SchwartzMap.fourierInv_coe, Breakdown.FracInternal.NiceField.symbolS_coe]
  rfl

open Freq.Internal.VelocityInjective in
private theorem nice_pairing {m : Space → CSpace} (hm : IsNiceSymbol m) (x : X) :
    inner ℝ x (embedX (niceField m)) =
      ∫ y, inner ℝ ((velocity x : Space → Space) y) (negSsp (niceField m) y) := by
  have hn : IsNiceField (niceField m) := ⟨m, hm, rfl⟩
  have hP := niceFieldProps (5 / 4) (by norm_num) (by norm_num) _ hn
  have hd : IsDecayField (niceField m) := hP.2.1
  obtain ⟨S, hS⟩ := Internal.NicePairing.rapid_of_nice hP.2.2.1
  have hG : MemLp (negSsp (niceField m)) (6 / 5) volume := by
    rw [← hS]
    exact S.memLp _ volume
  have hE : PairingEmbed := pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2
  let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
  have heq : (fun y : X => inner ℝ y (embedX (niceField m))) =
      fun y => P (velocity y) (hG.toLp _) := by
    apply Continuous.ext_on testDense_holds.2 (by fun_prop)
      ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds y hy
    have hψd : IsDecayField ψ := Internal.VelocityInvert.ofgrad_decay hψ
    show inner ℝ (embedX ψ) (embedX (niceField m)) = P (velocity (embedX ψ)) (hG.toLp _)
    rw [hE _ _ hψd hd, nicePairingByParts _ _ hψd hn,
      ← WeakProfile.Internal.PairingVelocity.pairing_eq_lp _ hG, fieldPairing]
    apply integral_congr_ae
    filter_upwards [velocityDecay_holds ψ hψd] with z hz
    rw [hz]
  rw [congrFun heq x, WeakProfile.Internal.PairingVelocity.pairing_eq_lp _ hG]

theorem bilinPairing : BilinPairingStatement := by
  intro α τ hα hτ u φ hφ
  obtain ⟨m, hm, rfl⟩ := hφ
  have h1 : inner ℝ (fracBilinX α τ u u) (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ))) =
      ∫ y, inner ℝ ((velocity (fracBilinX α τ u u) : Space → Space) y) (niceField m y) := by
    have h := nice_pairing (nice_inv hm) (fracBilinX α τ u u)
    simpa only [secondOrder_inv hm] using h
  have h3 := Breakdown.FracInternal.fracBilinX_spec (fracBilin_holds α hα).1 hτ u u
    (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ)))
  have h2 : trilinear u u (fracPhiX α τ (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ)))) =
      trilinear u u (heatField α τ (niceField m)) := by
    rw [heatField_nice α τ hm]
    unfold trilinear
    apply integral_congr_ae
    filter_upwards [phi_nice hα hτ hm] with x hx
    rw [hx]
  calc (∫ y, inner ℝ ((velocity (fracBilinX α τ u u) : Space → Space) y) (niceField m y))
      = fracBilinForm α τ u u (embedX (niceField (fun ξ => (sspFactor ξ)⁻¹ • m ξ))) := h1.symm.trans h3
    _ = -(1 / 2 : ℝ) * (trilinear u u (heatField α τ (niceField m)) +
          trilinear u u (heatField α τ (niceField m))) := by
        unfold fracBilinForm
        exact congrArg (fun T => -(1 / 2 : ℝ) * (T + T)) h2
    _ = -trilinear u u (heatField α τ (niceField m)) := by ring

end Breakdown.FracCert
