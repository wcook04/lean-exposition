import Breakdown.FracCert.FreeSymbolExistsParts

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolExistsInternal

theorem rot_coord (θ : ℝ) (y : Space) :
    axialRotationFormula θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 ∧
      axialRotationFormula θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 ∧ axialRotationFormula θ y 2 = y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [axialRotationFormula]

theorem rot_norm (θ : ℝ) (y : Space) : ‖axialRotationFormula θ y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := rot_coord θ y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, h0, h1, h2]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem rot_neg (θ : ℝ) (y : Space) : axialRotationFormula θ (-y) = -axialRotationFormula θ y := by
  ext i
  fin_cases i <;> simp [axialRotationFormula] <;> ring

theorem rotC_coord (θ : ℝ) (z : Freq.CSpace) :
    axialRotationC θ z 0 = (Real.cos θ : ℂ) * z 0 - (Real.sin θ : ℂ) * z 1 ∧
      axialRotationC θ z 1 = (Real.sin θ : ℂ) * z 0 + (Real.cos θ : ℂ) * z 1 ∧ axialRotationC θ z 2 = z 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [axialRotationC]

theorem conj_coord (z : Freq.CSpace) (i : Fin 3) : Freq.conjVec z i = star (z i) := by
  simp [Freq.conjVec]

theorem rotC_conj (θ : ℝ) (z : Freq.CSpace) :
    axialRotationC θ (Freq.conjVec z) = Freq.conjVec (axialRotationC θ z) := by
  ext i
  fin_cases i <;> simp [axialRotationC, conj_coord, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal]

theorem rotC_zero (θ : ℝ) : axialRotationC θ 0 = 0 := by
  ext i
  fin_cases i <;> simp [axialRotationC]

def conjIsometry : Freq.CSpace →ₗᵢ[ℝ] Freq.CSpace where
  toLinearMap := Freq.conjVec.toLinearMap
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [conj_coord]

theorem support_zero {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ∃ R : ℝ, ∀ ξ : Space, R < ‖ξ‖ → freeSolution α a s ξ = 0 := by
  obtain ⟨R, hR⟩ := hs.2.1.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun ξ hξ => ?_⟩
  unfold freeSolution
  refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
  have hτ0 : (0 : ℝ) ≤ τ / (2 * α) := div_nonneg (le_of_lt hτ) (by linarith)
  have hn : R < ‖Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ‖ := by
    rw [norm_smul, rot_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc R < ‖ξ‖ := hξ
      _ = 1 * ‖ξ‖ := (one_mul _).symm
      _ ≤ Real.exp (τ / (2 * α)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (Real.one_le_exp hτ0) (norm_nonneg _)
  have hz : s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hR hm
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  rw [hz, rotC_zero, smul_zero]

theorem conjSymmetric {α a : ℝ} {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) (ξ : Space) :
    freeSolution α a s (-ξ) = Freq.conjVec (freeSolution α a s ξ) := by
  unfold freeSolution
  change _ = conjIsometry _
  rw [← conjIsometry.integral_comp_comm]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  have hw : freeWeight α τ (-ξ) = freeWeight α τ ξ := by simp [freeWeight, freqPow]
  rw [hw, rot_neg, smul_neg, hs.2.2.2.1, rotC_conj]
  change _ = Freq.conjVec _
  rw [Freq.conjVec.map_smul]

theorem pair_rotC (θ : ℝ) (ξ : Space) (z : Freq.CSpace) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * axialRotationC θ z i =
      ∑ i : Fin 3, ((axialRotationFormula (-θ) ξ i : ℝ) : ℂ) * z i := by
  obtain ⟨h0, h1, h2⟩ := rotC_coord θ z
  obtain ⟨k0, k1, k2⟩ := rot_coord (-θ) ξ
  simp only [Fin.sum_univ_three, h0, h1, h2, k0, k1, k2, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem divergence {α a : ℝ} {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) (ξ : Space) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * freeSolution α a s ξ i = 0 := by
  let L : Freq.CSpace →L[ℂ] ℂ := ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) • EuclideanSpace.proj i
  have hL : ∀ z : Freq.CSpace, L z = ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * z i := by
    intro z
    simp [L]
  rw [← hL]
  unfold freeSolution
  by_cases hI : IntegrableOn (fun τ => freeWeight α τ ξ •
    axialRotationC (a * τ) (s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ))) (Set.Ioi 0)
  · rw [← L.integral_comp_comm hI]
    refine setIntegral_eq_zero_of_forall_eq_zero fun τ _ => ?_
    rw [L.map_smul_of_tower, hL, pair_rotC]
    have hd := hs.2.2.2.2 (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ)
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc] at hd
    rw [← Finset.mul_sum] at hd
    have he : ((Real.exp (τ / (2 * α)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    rw [(mul_eq_zero.mp hd).resolve_left he, smul_zero]
  · rw [integral_undef hI, map_zero]

end FreeSymbolExistsInternal

end SteadyCert

end Breakdown
