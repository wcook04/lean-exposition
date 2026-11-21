import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.RDilation
import Breakdown.FreqTr.Rotation

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace FracInternal.SimMoments

open Breakdown.Freq.Internal.Rotation Breakdown.Freq.FracInternal.Dilation

theorem simOp_ae {α a μ : ℝ} (hμ : 0 < μ) (x : X) :
    (((simOp α a μ x : X) : L2C) : Space → CSpace) =ᵐ[volume] fun ξ =>
      ((μ⁻¹) ^ (1 - 3 / (2 * α))) • rotC (axialRotation (a * Real.log μ))
        ((x : L2C) ((axialRotation (a * Real.log μ)).symm (((μ⁻¹) ^ (-(1 / (2 * α)))) • ξ))) := by
  set R := axialRotation (a * Real.log μ) with hR
  have hsim : simOp α a μ x = fracDilX α μ⁻¹ (rotX R x) := rfl
  have hc : (μ⁻¹) ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos (inv_pos.2 hμ) _).ne'
  rw [hsim, fracDilX_coe (inv_pos.2 hμ)]
  filter_upwards [fracDilL2_ae (α := α) (inv_pos.2 hμ) ((rotX R x : X) : L2C),
    ae_comp (qmp_smul hc) (rotL2_realized fieldOpRealized R (x : L2C))] with ξ h1 h2
  rw [h1, rotX_coe fieldOpRealized R x]
  rw [h2]

theorem ofReal_mul_enorm_sq {r : ℝ} (hr : 0 ≤ r) (v : CSpace) :
    ENNReal.ofReal r * ‖v‖ₑ ^ 2 = ENNReal.ofReal (r * ‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_mul hr, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem real_identity (k : ℕ) (hk : 1 ≤ k) {s c t A : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    t ^ (2 * k) * (|(2 * π * t)⁻¹| * (c * A)) ^ 2 =
      c ^ 2 * s ^ 2 / s ^ (2 * k) * ((s * t) ^ (2 * k) * (|(2 * π * (s * t))⁻¹| * A) ^ 2) := by
  rcases ht.lt_or_eq with ht | ht
  · rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    field_simp
    ring
  · subst ht
    have h2k : 2 * k ≠ 0 := by omega
    simp [zero_pow h2k]

theorem lintegral_comp_rot_smul (R : Space ≃ₗᵢ[ℝ] Space) {s : ℝ} (hs : s ≠ 0) (G : Space → ℝ≥0∞) :
    ∫⁻ ξ, G (R (s • ξ)) = ENNReal.ofReal (|(s ^ Module.finrank ℝ Space)⁻¹|) * ∫⁻ η, G η := by
  have h1 : ∫⁻ ξ, G (R (s • ξ)) = ∫⁻ η, G (R η) ∂(Measure.map (s • ·) volume) := by
    rw [← MeasurableEquiv.coe_smul₀ hs, lintegral_map_equiv]
    rfl
  rw [h1, Measure.map_addHaar_smul volume hs, lintegral_smul_measure,
    (LinearIsometryEquiv.measurePreserving R).lintegral_comp_emb R.toHomeomorph.measurableEmbedding]
  rfl

end FracInternal.SimMoments

open FracInternal.SimMoments Breakdown.Freq.Internal.Rotation in
theorem simOpMoments : SimOpMomentsStatement := by
  intro α a μ _ hμ x hx k hk
  set R := axialRotation (a * Real.log μ) with hR
  set s : ℝ := (μ⁻¹) ^ (-(1 / (2 * α))) with hsdef
  set c : ℝ := (μ⁻¹) ^ (1 - 3 / (2 * α)) with hcdef
  have hs : 0 < s := Real.rpow_pos_of_pos (inv_pos.2 hμ) _
  have hc : 0 < c := Real.rpow_pos_of_pos (inv_pos.2 hμ) _
  set G : Space → ℝ≥0∞ := fun η => ENNReal.ofReal (‖η‖ ^ (2 * k)) * ‖symbolX x η‖ₑ ^ 2 with hG
  set K : ℝ := c ^ 2 * s ^ 2 / s ^ (2 * k) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : (fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symbolX (simOp α a μ x) ξ‖ₑ ^ 2) =ᵐ[volume]
      fun ξ => ENNReal.ofReal K * G (R.symm (s • ξ)) := by
    filter_upwards [simOp_ae (α := α) (a := a) hμ x] with ξ hξ
    simp only [hG, symbolX]
    rw [hξ, ofReal_mul_enorm_sq (by positivity), ofReal_mul_enorm_sq (by positivity),
      ← ENNReal.ofReal_mul hK0]
    congr 1
    rw [norm_smul, norm_smul, norm_smul, norm_rotC, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hc, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs]
    exact real_identity k hk hs (norm_nonneg ξ)
  have hfin : homNormSq k (symbolX x) < ⊤ := hx k hk
  unfold homNormSq at hfin ⊢
  rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_rot_smul R.symm hs.ne' G]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

end Breakdown.FracCert
