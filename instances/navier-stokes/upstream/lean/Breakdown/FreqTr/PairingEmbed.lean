import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.PairingEmbed

theorem decayField_add {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f + g) := by
  obtain ⟨hfc, hfd, C₁, hC₁⟩ := hf
  obtain ⟨hgc, hgd, C₂, hC₂⟩ := hg
  have hfD : Differentiable ℝ f := hfc.differentiable (by simp)
  have hgD : Differentiable ℝ g := hgc.differentiable (by simp)
  refine ⟨hfc.add hgc, fun y => ?_, C₁ + C₂, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hfd y
    have h2 := hgd y
    unfold divergenceAt at *
    rw [fderiv_add (hfD y) (hgD y)]
    simp only [add_apply, PiLp.add_apply, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  · calc ‖(f + g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_add_le _ _
      _ ≤ C₁ / (1 + ‖y‖) + C₂ / (1 + ‖y‖) := add_le_add (hC₁ y).1 (hC₂ y).1
      _ = (C₁ + C₂) / (1 + ‖y‖) := by rw [add_div]
  · rw [fderiv_add (hfD y) (hgD y)]
    calc ‖fderiv ℝ f y + fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_add_le _ _
      _ ≤ C₁ / (1 + ‖y‖) ^ 2 + C₂ / (1 + ‖y‖) ^ 2 := add_le_add (hC₁ y).2 (hC₂ y).2
      _ = (C₁ + C₂) / (1 + ‖y‖) ^ 2 := by rw [add_div]

theorem decayField_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  obtain ⟨hfc, hfd, C₁, hC₁⟩ := hf
  obtain ⟨hgc, hgd, C₂, hC₂⟩ := hg
  have hfD : Differentiable ℝ f := hfc.differentiable (by simp)
  have hgD : Differentiable ℝ g := hgc.differentiable (by simp)
  refine ⟨hfc.sub hgc, fun y => ?_, C₁ + C₂, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hfd y
    have h2 := hgd y
    unfold divergenceAt at *
    rw [fderiv_sub (hfD y) (hgD y)]
    simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
    rw [h1, h2, sub_zero]
  · calc ‖(f - g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ C₁ / (1 + ‖y‖) + C₂ / (1 + ‖y‖) := add_le_add (hC₁ y).1 (hC₂ y).1
      _ = (C₁ + C₂) / (1 + ‖y‖) := by rw [add_div]
  · rw [fderiv_sub (hfD y) (hgD y)]
    calc ‖fderiv ℝ f y - fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_sub_le _ _
      _ ≤ C₁ / (1 + ‖y‖) ^ 2 + C₂ / (1 + ‖y‖) ^ 2 := add_le_add (hC₁ y).2 (hC₂ y).2
      _ = (C₁ + C₂) / (1 + ‖y‖) ^ 2 := by rw [add_div]

theorem integrable_sq_fderiv {f : Space → Space} (hf : IsDecayField f) (i : Fin 3) :
    Integrable (fun y => ‖fderiv ℝ f y (unitVector i)‖ ^ 2) := by
  obtain ⟨hfc, -, C, hC⟩ := hf
  have hcont : Continuous (fun y => ‖fderiv ℝ f y (unitVector i)‖ ^ 2) :=
    ((hfc.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  refine (hint.const_mul (C ^ 2)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
  have h1 : ‖fderiv ℝ f y (unitVector i)‖ ≤ C / (1 + ‖y‖) ^ 2 := by
    calc ‖fderiv ℝ f y (unitVector i)‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f y‖ := by rw [hu, mul_one]
      _ ≤ C / (1 + ‖y‖) ^ 2 := (hC y).2
  have h0 : 0 ≤ ‖fderiv ℝ f y (unitVector i)‖ := norm_nonneg _
  have hrp : (1 + ‖y‖) ^ (-(4 : ℝ)) = (((1 + ‖y‖) ^ 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le, ← pow_mul]
    norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrp]
  calc ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = C ^ 2 * (((1 + ‖y‖) ^ 2) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]

theorem integrable_sum_sq_fderiv {f : Space → Space} (hf : IsDecayField f) :
    Integrable (fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2) :=
  integrable_finsetSum _ fun i _ => integrable_sq_fderiv hf i

end Internal.PairingEmbed

open Internal.PairingEmbed in
theorem pairingEmbed (h1 : EmbedNorm) (h2 : EmbedLinear) :
    PairingEmbed := by
  intro f g hf hg
  have hfD : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hgD : Differentiable ℝ g := hg.1.differentiable (by simp)
  have hadd := decayField_add hf hg
  have hsub := decayField_sub hf hg
  have hpol : inner ℝ (embedX f) (embedX g) =
      (‖embedX (f + g)‖ ^ 2 - ‖embedX (f - g)‖ ^ 2) / 4 := by
    rw [h2.1 f g hf hg, h2.2.1 f g hf hg, norm_add_sq_real, norm_sub_sq_real]
    ring
  rw [hpol, h1 _ hadd, h1 _ hsub, ← integral_sub (integrable_sum_sq_fderiv hadd)
    (integrable_sum_sq_fderiv hsub), ← integral_div]
  unfold gradientPairing
  congr 1
  funext y
  rw [fderiv_add (hfD y) (hgD y), fderiv_sub (hfD y) (hgD y), ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [add_apply, sub_apply]
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

end Breakdown.Freq
