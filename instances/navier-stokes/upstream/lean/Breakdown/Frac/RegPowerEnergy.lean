import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegAprioriAuxEnergyPart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem powerEnergyInequality_of (α : ℝ) (hα : 1 < α) (h1 : PowerPointwiseDerivStatement α) :
    PowerEnergyInequalityStatement α := by
  intro T hT F hF hd ξ
  set L : ℝ := (2 * π * ‖ξ‖) ^ (2 * α) with hLdef
  have hL : 0 ≤ L := Real.rpow_nonneg (by positivity) _
  have hN := continuousOn_nonlinSymbol_of_hsCurve hF ξ
  have hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => F τ ξ)
      (-((L : ℝ) : ℂ) • F t ξ + nonlinSymbol (F t) ξ) (Icc 0 T) t := fun t ht => by
    have := h1 T hT F hd ξ hN t ht
    simpa [powerTimeDerivSymbol, powerSymbol, hLdef, neg_smul] using this
  have hu : ContinuousOn (fun τ => F τ ξ) (Icc 0 T) := fun t ht => (hder t ht).continuousWithinAt
  have hsm : ∀ t, (-((L : ℝ) : ℂ) • F t ξ) = (-L : ℝ) • F t ξ := fun t => by
    rw [← Complex.coe_smul]; push_cast; rfl
  have hin : ∀ t, inner ℝ (F t ξ) (-((L : ℝ) : ℂ) • F t ξ + nonlinSymbol (F t) ξ) =
      -L * ‖F t ξ‖ ^ 2 + inner ℝ (F t ξ) (nonlinSymbol (F t) ξ) := fun t => by
    rw [inner_add_right, hsm, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hφ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => ‖F τ ξ‖ ^ 2)
      (2 * (-L * ‖F t ξ‖ ^ 2 + inner ℝ (F t ξ) (nonlinSymbol (F t) ξ))) (Icc 0 T) t :=
    fun t ht => by
    rw [← hin]; exact (hder t ht).norm_sq
  have hi : ContinuousOn (fun t => inner ℝ (F t ξ) (nonlinSymbol (F t) ξ)) (Icc 0 T) := hu.inner hN
  have hn2 : ContinuousOn (fun t => ‖F t ξ‖ ^ 2) (Icc 0 T) := hu.norm.pow 2
  have hnn : ContinuousOn (fun t => ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖) (Icc 0 T) :=
    hu.norm.mul hN.norm
  have hgc : ContinuousOn (fun t => 2 * (-L * ‖F t ξ‖ ^ 2 +
      inner ℝ (F t ξ) (nonlinSymbol (F t) ξ))) (Icc 0 T) :=
    continuousOn_const.mul ((continuousOn_const.mul hn2).add hi)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le hn2
    (fun t ht => ((hφ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt) (hgc.intervalIntegrable_of_Icc hT.le)
  have i1 := hn2.intervalIntegrable_of_Icc (μ := volume) hT.le
  have i2 := hi.intervalIntegrable_of_Icc (μ := volume) hT.le
  have i3 := hnn.intervalIntegrable_of_Icc (μ := volume) hT.le
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i1.const_mul _) i2,
    intervalIntegral.integral_const_mul] at hFTC
  have hQR : ∫ t in (0 : ℝ)..T, inner ℝ (F t ξ) (nonlinSymbol (F t) ξ) ≤
      ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖ :=
    intervalIntegral.integral_mono_on hT.le i2 i3 fun t _ => real_inner_le_norm _ _
  have hT2 : 0 ≤ ‖F T ξ‖ ^ 2 := by positivity
  have hx : 0 ≤ ‖ξ‖ ^ 2 := by positivity
  have key : 2 * L * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ ^ 2 ≤
      ‖F 0 ξ‖ ^ 2 + 2 * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖ := by
    nlinarith
  have hreal : 2 * ((‖ξ‖ ^ 2 * L) * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ ^ 2) ≤
      ‖ξ‖ ^ 2 * ‖F 0 ξ‖ ^ 2 +
        2 * (‖ξ‖ ^ 2 * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖) := by
    have := mul_le_mul_of_nonneg_left key hx
    nlinarith
  have e1 : ∀ s, ENNReal.ofReal (‖ξ‖ ^ 2 * L) * ‖F s ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖ξ‖ ^ 2 * L * ‖F s ξ‖ ^ 2) := fun s => by
    rw [ENNReal.ofReal_mul (mul_nonneg hx hL), ENNReal.ofReal_pow (norm_nonneg (F s ξ)) 2, ofReal_norm]
  have e2 : ∀ s, ENNReal.ofReal (‖ξ‖ ^ 2) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) =
      ENNReal.ofReal (‖ξ‖ ^ 2 * (‖F s ξ‖ * ‖nonlinSymbol (F s) ξ‖)) := fun s => by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
      ofReal_norm]
  have e0 : ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F 0 ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖ξ‖ ^ 2 * ‖F 0 ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg (F 0 ξ)) 2, ofReal_norm]
  simp only [e1, e2, e0]
  rw [setLIntegral_ofReal_eq_intervalIntegral (g := fun s => ‖ξ‖ ^ 2 * L * ‖F s ξ‖ ^ 2) hT.le
      (continuousOn_const.mul hn2) (fun s => by positivity),
    setLIntegral_ofReal_eq_intervalIntegral
      (g := fun s => ‖ξ‖ ^ 2 * (‖F s ξ‖ * ‖nonlinSymbol (F s) ξ‖)) hT.le
      (continuousOn_const.mul hnn) (fun s => by positivity),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h2 : ∀ x : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := fun x => by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h2, h2, ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) (mul_nonneg hx
    (intervalIntegral.integral_nonneg hT.le fun t _ => by positivity)))]
  exact ENNReal.ofReal_le_ofReal hreal

end Breakdown.SmoothFlow
