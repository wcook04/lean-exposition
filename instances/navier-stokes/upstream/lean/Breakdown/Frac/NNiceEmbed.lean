import Breakdown.Frac.StNiceEmbed
import Breakdown.FreqTr.NiceApprox

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.NiceEmbed

open Internal.NiceApprox

theorem realVec_complexifyVec_eq (v : Space) : realVec (complexifyVec v) = v := by
  ext i
  simp [realVec, complexifyVec]

theorem isNiceSymbol_smul {m : Space → CSpace} (hm : IsNiceSymbol m) (c : Space → ℝ)
    (hc : ∀ ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ c ξ) (hsym : ∀ ξ, c (-ξ) = c ξ) :
    IsNiceSymbol (fun ξ => c ξ • m ξ) := by
  obtain ⟨hs, hcs, ⟨r, hr, hz⟩, hconj, hdiv⟩ := hm
  refine ⟨?_, hcs.mono (fun ξ hξ h0 => hξ (by simp [h0])),
    ⟨r, hr, fun ξ hξ => by simp [hz ξ hξ]⟩, fun ξ => ?_, fun ξ => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro ξ
    rcases lt_or_ge ‖ξ‖ r with h | h
    · have hev : (fun ξ => c ξ • m ξ) =ᶠ[nhds ξ] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with y hy
        simp [hz y hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hne : ξ ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h
        linarith
      exact (hc ξ hne).smul hs.contDiffAt
  · show c (-ξ) • m (-ξ) = conjVec (c ξ • m ξ)
    rw [hsym, hconj, map_smul]
  · have h := hdiv ξ
    have e : ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (c ξ • m ξ) i =
        (c ξ : ℂ) * ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * m ξ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [PiLp.smul_apply, Complex.real_smul]
      ring
    rw [e, h, mul_zero]

theorem isNiceSymbol_traceSecondDeriv {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => sspFactor ξ • m ξ) :=
  isNiceSymbol_smul hm sspFactor
    (fun ξ hξ => contDiffAt_const.mul ((contDiffAt_norm ℝ hξ).pow 2))
    (fun ξ => by simp [sspFactor])

theorem isNiceSymbol_frac (α : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ) :=
  isNiceSymbol_smul hm (fun ξ => (2 * π * ‖ξ‖) ^ (2 * α))
    (fun ξ hξ => by
      have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      exact (contDiffAt_const.mul (contDiffAt_norm ℝ hξ)).rpow_const_of_ne (by positivity))
    (fun ξ => by simp)

theorem negTraceSecondDeriv_niceField {m : Space → CSpace} (hm : IsNiceSymbol m) :
    negSsp (niceField m) = niceField (fun ξ => sspFactor ξ • m ξ) := by
  set a : 𝓢(Space, CSpace) := hm.2.1.toSchwartzMap hm.1 with ha
  have haf : ⇑a = m := rfl
  set Ac : 𝓢(Space, CSpace) := 𝓕⁻ a with hAc
  set G : 𝓢(Space, Space) := SchwartzMap.postcompCLM realVec Ac with hG
  have hcG : ∀ x, complexifyVec (G x) = Ac x := by
    intro x
    rw [hG, SchwartzMap.postcompCLM_apply]
    exact complexify_realVec_of_conj
      (freqTrInv_conj a (fun ξ => by rw [haf]; exact hm.2.2.2.1 ξ) x)
  have hφ : niceField m = ⇑G := by
    funext x
    rw [hG, SchwartzMap.postcompCLM_apply, hAc, SchwartzMap.fourierInv_coe, haf]
    rfl
  set H : 𝓢(Space, CSpace) := SchwartzMap.postcompCLM complexifyVec (negSspS G) with hH
  have hHf : ⇑H = fun x => complexifyVec (negSsp G x) := by
    funext x
    rw [hH, SchwartzMap.postcompCLM_apply, negSspS_apply]
  have hcGf : (fun x => complexifyVec (G x)) = ⇑Ac := funext hcG
  set FH : 𝓢(Space, CSpace) := 𝓕 H with hFHdef
  have hFH : ⇑FH = fun ξ => sspFactor ξ • m ξ := by
    funext ξ
    rw [hFHdef, SchwartzMap.fourier_coe, hHf, freqTr_negSsp, hcGf, hAc, ← SchwartzMap.fourier_coe,
      FourierTransform.fourier_fourierInv_eq, haf]
  set IH : 𝓢(Space, CSpace) := 𝓕⁻ FH with hIH
  have hx : ∀ x, IH x = H x := fun x => by
    rw [hIH, hFHdef, FourierTransform.fourierInv_fourier_eq]
  rw [hφ]
  funext x
  have e : niceField (fun ξ => sspFactor ξ • m ξ) x = realVec (IH x) := by
    rw [hIH, SchwartzMap.fourierInv_coe, hFH]
    rfl
  rw [e, hx, hHf, realVec_complexifyVec_eq]

end FracInternal.NiceEmbed

open FracInternal.NiceEmbed in
theorem fracNiceEmbedPower (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (h2 : NiceEmbedSymbol)
    (h3 : ∀ m, IsNiceSymbol m → fractionalPowerAt α (niceField m) =
      niceField (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ)) : FracNiceEmbedPower α := by
  rintro φ ⟨m, hm, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [negTraceSecondDeriv_niceField hm]
    filter_upwards [h2 m hm, h2 _ (isNiceSymbol_traceSecondDeriv hm)] with ξ h0 h1
    rw [h1, h0]
    exact smul_comm _ _ _
  · rw [h3 m hm]
    filter_upwards [h2 m hm, h2 _ (isNiceSymbol_frac α hm)] with ξ h0 h1
    rw [h1, h0]
    exact smul_comm _ _ _

end Breakdown.Freq
