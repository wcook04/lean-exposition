import Breakdown.Uniqueness.RegUniqueAux1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem norm_advTerm_le (f g : Space → CSpace) (ξ η : Space) (i j : Fin 3) :
    ‖f η j * (2 * (π : ℂ) * Complex.I * ((ξ j - η j : ℝ) : ℂ) * g (ξ - η) i)‖ ≤
      2 * π * (‖f η‖ * (‖ξ - η‖ * ‖g (ξ - η)‖)) := by
  have a1 := PiLp.norm_apply_le (f η) j
  have a2 : |ξ j - η j| ≤ ‖ξ - η‖ := by
    have := PiLp.norm_apply_le (ξ - η) j
    simpa [Real.norm_eq_abs] using this
  have a3 := PiLp.norm_apply_le (g (ξ - η)) i
  have e : ‖f η j * (2 * (π : ℂ) * Complex.I * ((ξ j - η j : ℝ) : ℂ) * g (ξ - η) i)‖ =
      2 * π * (‖f η j‖ * (|ξ j - η j| * ‖g (ξ - η) i‖)) := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      abs_of_pos Real.pi_pos]
    ring
  rw [e]
  have hp : 0 ≤ 2 * π := by positivity
  gcongr

private theorem integrable_advTerm {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (ξ : Space) (h : convMass f g ξ < ⊤) (i j : Fin 3) :
    Integrable (fun η => f η j * (2 * (π : ℂ) * Complex.I * ((ξ j - η j : ℝ) : ℂ) * g (ξ - η) i))
      volume := by
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable (fun η => f η j) volume := by fun_prop
    have h2 : AEStronglyMeasurable (fun η => g (ξ - η)) volume :=
      hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
    have key : ∀ u : Space → CSpace, AEStronglyMeasurable u volume →
        AEStronglyMeasurable (fun η => u η i) volume := fun u hu => by fun_prop
    have h3 : AEStronglyMeasurable (fun η => g (ξ - η) i) volume := key _ h2
    have h4 : Continuous (fun η : Space => ((ξ j - η j : ℝ) : ℂ)) := by fun_prop
    exact h1.mul ((aestronglyMeasurable_const.mul h4.aestronglyMeasurable).mul h3)
  · unfold HasFiniteIntegral
    calc ∫⁻ η, ‖f η j * (2 * (π : ℂ) * Complex.I * ((ξ j - η j : ℝ) : ℂ) * g (ξ - η) i)‖ₑ
        ≤ ∫⁻ η, ENNReal.ofReal (2 * π) * (‖f η‖ₑ * (‖ξ - η‖ₑ * ‖g (ξ - η)‖ₑ)) := by
          refine lintegral_mono (fun η => ?_)
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
            ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
            ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (norm_advTerm_le f g ξ η i j)
      _ = ENNReal.ofReal (2 * π) * convMass f g ξ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem advectionBilin_sub_left {f f' g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hf' : AEStronglyMeasurable f' volume) (hg : AEStronglyMeasurable g volume) (ξ : Space)
    (h1 : convMass f g ξ < ⊤) (h2 : convMass f' g ξ < ⊤) :
    advectionBilin (f - f') g ξ = advectionBilin f g ξ - advectionBilin f' g ξ := by
  ext i
  simp only [advectionBilin, convC, Pi.sub_apply, PiLp.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [sub_mul]
  exact integral_sub (integrable_advTerm hf hg ξ h1 i j) (integrable_advTerm hf' hg ξ h2 i j)

theorem advectionBilin_sub_right {f g g' : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) (hg' : AEStronglyMeasurable g' volume) (ξ : Space)
    (h1 : convMass f g ξ < ⊤) (h2 : convMass f g' ξ < ⊤) :
    advectionBilin f (g - g') ξ = advectionBilin f g ξ - advectionBilin f g' ξ := by
  ext i
  simp only [advectionBilin, convC, Pi.sub_apply, PiLp.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [mul_sub]
  exact integral_sub (integrable_advTerm hf hg ξ h1 i j) (integrable_advTerm hf hg' ξ h2 i j)

end Breakdown.SmoothFlow
