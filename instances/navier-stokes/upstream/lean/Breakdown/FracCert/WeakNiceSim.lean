import Breakdown.FracCert.StWeak
import Breakdown.FreqTr.BilinRotate
import Breakdown.FreqTr.BilinDilate
import Breakdown.FreqTr.Rotation
import Breakdown.Frac.NNiceEmbed

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace Internal.WeakNiceSim

theorem nice_const {m : Space → CSpace} (hm : IsNiceSymbol m) (s : ℝ) :
    IsNiceSymbol (fun ξ => s • m ξ) :=
  Breakdown.Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm (fun _ => s)
    (fun _ _ => contDiffAt_const) (fun _ => rfl)

theorem nice_dilate {l : ℝ} (hl : 0 < l) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => m (l • ξ)) := by
  obtain ⟨hs, hcs, ⟨r, hr, hz⟩, hconj, hdiv⟩ := hm
  refine ⟨hs.comp (contDiff_id.const_smul l), ?_, ⟨r / l, div_pos hr hl, fun ξ hξ => hz _ ?_⟩,
    fun ξ => ?_, fun ξ => ?_⟩
  · exact hcs.comp_homeomorph (Homeomorph.smulOfNeZero l hl.ne')
  · rw [norm_smul, Real.norm_of_nonneg hl.le]
    rw [lt_div_iff₀ hl] at hξ
    linarith
  · show m (l • -ξ) = conjVec (m (l • ξ))
    rw [smul_neg, hconj]
  · have h := hdiv (l • ξ)
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have e : ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * m (l • ξ) i =
        (l : ℂ)⁻¹ * ∑ i : Fin 3, (((l • ξ) i : ℝ) : ℂ) * m (l • ξ) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      field_simp
    rw [e, h, mul_zero]

theorem nice_rot (R : Space ≃ₗᵢ[ℝ] Space) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (fun ξ => rotC R (m (R.symm ξ))) := by
  obtain ⟨hs, hcs, ⟨r, hr, hz⟩, hconj, hdiv⟩ := hm
  refine ⟨(rotC R).contDiff.comp (hs.comp R.symm.contDiff), ?_,
    ⟨r, hr, fun ξ hξ => ?_⟩, fun ξ => ?_, fun ξ => ?_⟩
  · exact HasCompactSupport.comp_left (g := rotC R) (hcs.comp_homeomorph R.symm.toHomeomorph)
      (map_zero _)
  · show rotC R (m (R.symm ξ)) = 0
    have hn : ‖R.symm ξ‖ < r := by rw [LinearIsometryEquiv.norm_map R.symm ξ]; exact hξ
    rw [hz _ hn, map_zero]
  · show rotC R (m (R.symm (-ξ))) = conjVec (rotC R (m (R.symm ξ)))
    rw [map_neg, hconj, Internal.Rotation.conjVec_rotC]
  · have h := hdiv (R.symm ξ)
    have e : ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * rotC R (m (R.symm ξ)) i =
        ∑ j : Fin 3, (((R.symm ξ) j : ℝ) : ℂ) * m (R.symm ξ) j := by
      simp only [Internal.Rotation.rotC_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Internal.Rotation.apply_eq_sum R.symm ξ j]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Internal.Rotation.symm_unit]
      ring
    rw [e]
    exact h

theorem inverseTransform_const_smul (g : Space → CSpace) (s : ℝ) (x : Space) :
    𝓕⁻ (fun ξ => s • g ξ) x = s • 𝓕⁻ g x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_smul]
  congr 1
  ext v
  simp only [Circle.smul_def]
  rw [smul_comm]

def rotEquiv (R : Space ≃ₗᵢ[ℝ] Space) : CSpace ≃L[ℂ] CSpace :=
  ContinuousLinearEquiv.equivOfInverse (Internal.BilinRotate.rotCc R)
    (Internal.BilinRotate.rotCc R.symm)
    (fun z => by
      have h := Internal.Rotation.rotC_rotC_symm R.symm z
      rw [LinearIsometryEquiv.symm_symm] at h
      exact h)
    (fun z => Internal.Rotation.rotC_rotC_symm R z)

theorem rotEquiv_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotEquiv R z = rotC R z := rfl

theorem inverseTransform_rot (R : Space ≃ₗᵢ[ℝ] Space) (g : Space → CSpace) (y : Space) :
    𝓕⁻ (fun ξ => rotC R (g (R.symm ξ))) y = rotC R (𝓕⁻ g (R.symm y)) := by
  rw [Real.fourierInv_eq, ← Real.fourierInv_comp_linearIsometry R.symm g y, Real.fourierInv_eq]
  have key : (fun v : Space => 𝐞 (inner ℝ v y) • rotC R (g (R.symm v))) =
      fun v => rotEquiv R (𝐞 (inner ℝ v y) • (g ∘ R.symm) v) := by
    funext v
    simp only [Circle.smul_def, map_smul, Function.comp_apply, rotEquiv_apply]
  rw [key, ContinuousLinearEquiv.integral_comp_comm, rotEquiv_apply]

theorem transport (R : Space ≃ₗᵢ[ℝ] Space) (c : ℝ) {l : ℝ} (hl : 0 < l) (m : Space → CSpace)
    (y : Space) :
    R (c • realVec (𝓕⁻ m (l • R.symm y))) =
      realVec (𝓕⁻ (fun ξ => rotC R ((c * l⁻¹ ^ 3) • m (l⁻¹ • R.symm ξ))) y) := by
  have h1 := inverseTransform_rot R (fun ξ => (c * l⁻¹ ^ 3) • m (l⁻¹ • ξ)) y
  have h2 := inverseTransform_const_smul (fun ξ => m (l⁻¹ • ξ)) (c * l⁻¹ ^ 3) (R.symm y)
  have h3 := Internal.BilinDilate.freqTrInv_comp_smul_aux m l⁻¹ (inv_pos.2 hl) (R.symm y)
  rw [h1, h2, h3, inv_inv, smul_smul, Internal.BilinRotate.realVec_rotC, map_smul,
    mul_inv_cancel_right₀ (pow_ne_zero 3 (inv_ne_zero hl.ne')), map_smul, map_smul]

end Internal.WeakNiceSim

open Internal.WeakNiceSim in
theorem niceSimAdjClosed : NiceSimAdjClosedStatement := by
  intro α a μ _ hμ φ hφ
  obtain ⟨m, hm, rfl⟩ := hφ
  have hl : 0 < μ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hμ _
  refine ⟨_, nice_rot (axialRotation (-(a * Real.log μ)))
    (nice_const (nice_dilate (inv_pos.2 hl) hm) (μ ^ (4 * (1 / (2 * α)) - 1) * (μ ^ (1 / (2 * α)))⁻¹ ^ 3)), ?_⟩
  funext y
  exact transport _ _ hl m y

end Breakdown.FracCert
