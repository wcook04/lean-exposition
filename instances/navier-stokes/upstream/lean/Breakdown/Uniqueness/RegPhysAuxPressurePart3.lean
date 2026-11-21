import Breakdown.Uniqueness.RegPhysAuxPressurePart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PressureSingle.Internal

theorem norm_advTerm_le (z w : CSpace) (v : Space) (i j : Fin 3) :
    ‖z j * (2 * (π : ℂ) * Complex.I * ((v j : ℝ) : ℂ) * w i)‖ ≤ 2 * π * (‖z‖ * (‖v‖ * ‖w‖)) := by
  have h1 := PiLp.norm_apply_le z j
  have h2 := PiLp.norm_apply_le v j
  have h3 := PiLp.norm_apply_le w i
  have hA : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  simp only [norm_mul] at hA ⊢
  rw [hA, Complex.norm_real]
  calc ‖z j‖ * (2 * π * ‖v j‖ * ‖w i‖) ≤ ‖z‖ * (2 * π * ‖v‖ * ‖w‖) := by gcongr
    _ = 2 * π * (‖z‖ * (‖v‖ * ‖w‖)) := by ring

theorem integrable_advTerm' {f : Space → CSpace} (hm : AEStronglyMeasurable f volume) {ξ : Space}
    (hξ : ∫⁻ η, ‖f η‖ₑ * (‖ξ - η‖ₑ * ‖f (ξ - η)‖ₑ) < ⊤) (i j : Fin 3) :
    Integrable (fun η => f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)) := by
  have m1 : AEStronglyMeasurable (fun η => f η j) volume :=
    (by fun_prop : Continuous fun z : CSpace => z j).comp_aestronglyMeasurable hm
  have m3 : AEStronglyMeasurable (fun η => f (ξ - η) i) volume :=
    (by fun_prop : Continuous fun z : CSpace => z i).comp_aestronglyMeasurable (aesm_shift hm ξ)
  have m2 : AEStronglyMeasurable (fun η : Space => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ)) volume :=
    (by fun_prop : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ)).aestronglyMeasurable
  refine ⟨m1.mul (m2.mul m3), ?_⟩
  show ∫⁻ η, ‖f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)‖ₑ < ⊤
  have hb : ∀ η, ‖f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)‖ₑ ≤
      ENNReal.ofReal (2 * π) * (‖f η‖ₑ * (‖ξ - η‖ₑ * ‖f (ξ - η)‖ₑ)) := by
    intro η
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (norm_advTerm_le _ _ _ i j)
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hξ

theorem ae_advTerm_lt_top {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume 1)) :
    ∀ᵐ ξ ∂(volume : Measure Space), ∫⁻ η, ‖f η‖ₑ * (‖ξ - η‖ₑ * ‖f (ξ - η)‖ₑ) < ⊤ := by
  have hm := aesm_of_memLp hf
  have ha := hm.enorm
  have hb : AEMeasurable (fun η : Space => ‖η‖ₑ * ‖f η‖ₑ) volume :=
    measurable_id.enorm.aemeasurable.mul ha
  refine ae_lt_top' (aemeasurable_conv ha hb).aemeasurable ?_
  have e := lintegral_conv ha hb
  rw [e]
  refine ENNReal.mul_ne_top (lintegral_enorm_lt_top' hf).ne
    (lt_of_le_of_lt (lintegral_mono fun η => ?_) (lintegral_enorm_lt_top hf)).ne
  gcongr
  rw [← ofReal_norm, pow_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem pressureSymbol_ae_eq {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume 1))
    (hsol : IsSolenoidalSymbol f) :
    ∀ᵐ ξ ∂(volume : Measure Space), pressureSymbol f ξ = pressureBilinSymbol f f ξ := by
  have hm := aesm_of_memLp hf
  filter_upwards [ae_advTerm_lt_top hf] with ξ hξ
  have hT := integrable_advTerm' hm hξ
  have hA : ∀ i, advectionSymbol f ξ i = ∑ j, ∫ η,
      f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) := by
    intro i
    rfl
  have hsum : ∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i =
      ∫ η, 2 * (π : ℂ) * Complex.I * (freqDot ξ (f η) * freqDot ξ (f (ξ - η))) := by
    simp_rw [hA, Finset.mul_sum, ← integral_const_mul]
    rw [Finset.sum_congr rfl (fun i _ => (integral_finsetSum _ (fun j _ => (hT i j).const_mul _)).symm)]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hT i j).const_mul _))]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    have hs := (hsol η).1
    simp only [freqDot, Fin.sum_univ_three, PiLp.sub_apply, Complex.ofReal_sub] at hs ⊢
    linear_combination (-(2 * (π : ℂ) * Complex.I) * (((ξ 0 : ℝ) : ℂ) * f (ξ - η) 0 +
      ((ξ 1 : ℝ) : ℂ) * f (ξ - η) 1 + ((ξ 2 : ℝ) : ℂ) * f (ξ - η) 2)) * hs
  have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [pi_ne_zero]
  show -(∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i) / (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ)) =
    -∫ η, (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (freqDot ξ (f η) * freqDot ξ (f (ξ - η)))
  rw [hsum, integral_const_mul, integral_const_mul, neg_div, mul_div_mul_left _ _ h2, Complex.ofReal_inv,
    div_eq_inv_mul]

end PressureSingle.Internal

end Breakdown.SmoothFlow
