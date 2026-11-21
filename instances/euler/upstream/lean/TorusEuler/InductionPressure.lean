import TorusEuler.ResidualGradient
import Mathlib.Analysis.SpecificLimits.Basic

open Set
open scoped BigOperators InnerProductSpace

namespace TorusEuler

/-- The sum of all pressure-Hessian budgets through a given step in Theorem 7.1. -/
theorem inductionPressure_sum_le {freq : ℕ → ℝ} (h0 : 0 < freq 0)
    (hgrow : ∀ n, 2 * freq n ≤ freq (n + 1)) (j : ℕ) :
    (∑ i ∈ Finset.range j, (freq i)⁻¹) ≤ 2 / freq 0 := by
  have hFreq (i : ℕ) : freq 0 * 2 ^ i ≤ freq i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← mul_assoc, mul_comm (freq 0 * 2 ^ i)]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans (hgrow i)
  have hInv (i : ℕ) : (freq i)⁻¹ ≤ (freq 0)⁻¹ * (1 / 2 : ℝ) ^ i := by
    rw [one_div, inv_pow, ← mul_inv]
    exact inv_anti₀ (by positivity) (hFreq i)
  calc
    (∑ i ∈ Finset.range j, (freq i)⁻¹) ≤
        ∑ i ∈ Finset.range j, (freq 0)⁻¹ * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum fun i _ => hInv i
    _ = (freq 0)⁻¹ * ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ (freq 0)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le j) (inv_nonneg.mpr h0.le)
    _ = 2 / freq 0 := by rw [div_eq_mul_inv, mul_comm]

/-- The pressure budget and a small residual gradient imply the quadratic upper bound
needed for endpoint coercivity at the next step. -/
theorem inductionPressure_endpointHessian_upper {T t : ℝ} {u : Velocity} {p : Pressure}
    {X : ℝ → Vec3} {freq : ℕ → ℝ} {j : ℕ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hX : HasDerivWithinAt X (u t (X t)) (Icc 0 T) t)
    (hp : DifferentiableAt ℝ (gradient (p t)) (X t))
    (hN : 4 ≤ freq 0) (hgrow : ∀ n, 2 * freq n ≤ freq (n + 1))
    (hpress : ∀ w : Vec3, ⟪fderiv ℝ (gradient (p t)) (X t) w, w⟫_ℝ ≤
      (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖w‖ ^ 2)
    (hres : ‖fderiv ℝ (momentumResidual (Icc 0 T) u p t) (X t)‖ ≤ 1 / 2) (w : Vec3) :
    ⟪endpointHessian (fderiv ℝ (u t) (X t))
      (derivWithin (fun r => fderiv ℝ (u r) (X r)) (Icc 0 T) t) w, w⟫_ℝ ≤ ‖w‖ ^ 2 := by
  let DR := fderiv ℝ (momentumResidual (Icc 0 T) u p t) (X t)
  have hNpos : 0 < freq 0 := (by norm_num : (0 : ℝ) < 4).trans_le hN
  have hsum := (inductionPressure_sum_le hNpos hgrow j).trans
    ((div_le_iff₀ hNpos).2 (by linarith : (2 : ℝ) ≤ (1 / 2) * freq 0))
  have hpressure := (hpress w).trans (mul_le_mul_of_nonneg_right hsum (sq_nonneg _))
  have hresidual : -⟪DR w, w⟫_ℝ ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
    rw [← inner_neg_left]
    calc
      _ ≤ ‖-DR w‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ (‖DR‖ * ‖w‖) * ‖w‖ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right (DR.le_opNorm w) (norm_nonneg _)
      _ = ‖DR‖ * ‖w‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hres (sq_nonneg _)
  rw [endpointHessian_eq_pressureHessian_sub_residualGradient hT ht hu hX hp,
    sub_apply, inner_sub_left]
  change ⟪fderiv ℝ (gradient (p t)) (X t) w, w⟫_ℝ - ⟪DR w, w⟫_ℝ ≤ ‖w‖ ^ 2
  linarith

end TorusEuler
