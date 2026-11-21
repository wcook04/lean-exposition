import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def convMass (f g : Space → CSpace) (ξ : Space) : ℝ≥0∞ :=
  ∫⁻ η, ‖f η‖ₑ * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ)

private theorem lintegral_sub_left_space (φ : Space → ℝ≥0∞) (ξ : Space) :
    ∫⁻ η, φ (ξ - η) = ∫⁻ ζ, φ ζ :=
  lintegral_sub_left_eq_self φ ξ

private theorem norm_le_sum_coord (x : CSpace) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have h1 : ‖x‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    two_ne_zero).1 h1

private theorem enorm_le_sum_coord (x : CSpace) : ‖x‖ₑ ≤ ∑ i, ‖x i‖ₑ := by
  rw [← ofReal_norm]
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_sum_coord x)

theorem enorm_advectionBilin_le (f g : Space → CSpace) (ξ : Space) :
    ‖advectionBilin f g ξ‖ₑ ≤ ENNReal.ofReal (18 * π) * convMass f g ξ := by
  have hc : ∀ i j : Fin 3, ‖convC (fun η => f η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) ξ‖ₑ ≤
      ENNReal.ofReal (2 * π) * convMass f g ξ := by
    intro i j
    unfold convC convMass
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun η => ?_
    have e1 : ‖f η j‖ₑ ≤ ‖f η‖ₑ := PiLp.enorm_apply_le _ _
    have e2 : ‖(ξ - η) j‖ₑ ≤ ‖ξ - η‖ₑ := PiLp.enorm_apply_le _ _
    have e3 : ‖g (ξ - η) i‖ₑ ≤ ‖g (ξ - η)‖ₑ := PiLp.enorm_apply_le _ _
    have e4 : ‖(2 * (π : ℂ) * Complex.I)‖ₑ = ENNReal.ofReal (2 * π) := by
      rw [← ofReal_norm]
      congr 1
      simp [abs_of_pos Real.pi_pos]
    have e5 : ‖(((ξ - η) j : ℝ) : ℂ)‖ₑ = ‖(ξ - η) j‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
    calc ‖f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * g (ξ - η) i)‖ₑ
        = ‖f η j‖ₑ * (‖(2 * (π : ℂ) * Complex.I)‖ₑ * ‖(((ξ - η) j : ℝ) : ℂ)‖ₑ *
            ‖g (ξ - η) i‖ₑ) := by simp only [enorm_mul]
      _ ≤ ‖f η‖ₑ * (ENNReal.ofReal (2 * π) * ‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ) := by
          rw [e4, e5]
          gcongr
      _ = ENNReal.ofReal (2 * π) * (‖f η‖ₑ * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ)) := by ring
  unfold advectionBilin
  refine (enorm_le_sum_coord _).trans ?_
  calc ∑ i, ‖(WithLp.toLp 2 (fun i => ∑ j, convC (fun η => f η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) ξ) : CSpace) i‖ₑ
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, ENNReal.ofReal (2 * π) * convMass f g ξ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hc i j)
    _ = ENNReal.ofReal (18 * π) * convMass f g ξ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (18 * π) = 9 * (2 * π) by ring, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),
          ENNReal.ofReal_ofNat]
        push_cast
        ring

theorem convMass_le_hs {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (ξ : Space) :
    convMass f g ξ ≤ hsNormSq 0 f ^ (1 / 2 : ℝ) * homNormSq 1 g ^ (1 / 2 : ℝ) := by
  have hg' : AEStronglyMeasurable (fun η => g (ξ - η)) volume :=
    hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have hm1 : AEMeasurable (fun η => ‖f η‖ₑ) volume := hf.enorm
  have hm2 : AEMeasurable (fun η => ‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ) volume :=
    ((continuous_const.sub continuous_id).enorm.measurable.aemeasurable).mul hg'.enorm
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hm1 hm2
  have s0 : hsNormSq 0 f = ∫⁻ η, ‖f η‖ₑ ^ (2 : ℝ) := by
    unfold hsNormSq hsWeight
    simp
  have s1 : homNormSq 1 g = ∫⁻ η, (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ) ^ (2 : ℝ) := by
    unfold homNormSq
    rw [lintegral_sub_left_space (fun ζ => (‖ζ‖ₑ * ‖g ζ‖ₑ) ^ (2 : ℝ)) ξ]
    refine lintegral_congr fun ζ => ?_
    rw [ENNReal.rpow_two, mul_pow, mul_one, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  rw [s0, s1]
  exact key

theorem convMass_le_left {f g : Space → CSpace} {β : ℝ≥0∞} (hβ : β ≠ ⊤) (h : ∀ η, ‖f η‖ₑ ≤ β)
    (ξ : Space) : convMass f g ξ ≤ β * gradFreqL1Norm g := by
  unfold convMass gradFreqL1Norm
  calc ∫⁻ η, ‖f η‖ₑ * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ)
      ≤ ∫⁻ η, β * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ) := lintegral_mono fun η => by gcongr; exact h η
    _ = β * ∫⁻ η, ‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ := lintegral_const_mul' _ _ hβ
    _ = β * ∫⁻ ζ, ENNReal.ofReal ‖ζ‖ * ‖g ζ‖ₑ := by
        rw [lintegral_sub_left_space (fun ζ => ‖ζ‖ₑ * ‖g ζ‖ₑ) ξ]
        simp only [ofReal_norm]

theorem convMass_le_right {f g : Space → CSpace} {β : ℝ≥0∞} (hβ : β ≠ ⊤)
    (h : ∀ ζ, ‖ζ‖ₑ * ‖g ζ‖ₑ ≤ β) (ξ : Space) : convMass f g ξ ≤ β * freqL1Norm f := by
  unfold convMass freqL1Norm
  calc ∫⁻ η, ‖f η‖ₑ * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ)
      ≤ ∫⁻ η, ‖f η‖ₑ * β := lintegral_mono fun η => by gcongr; exact h (ξ - η)
    _ = (∫⁻ η, ‖f η‖ₑ) * β := lintegral_mul_const' _ _ hβ
    _ = β * ∫⁻ η, ‖f η‖ₑ := mul_comm _ _

end Breakdown.SmoothFlow
