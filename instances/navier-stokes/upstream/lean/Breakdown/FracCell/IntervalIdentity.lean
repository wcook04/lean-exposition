import Breakdown.FracCell.StSpectral

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

private lemma evenSeries_second_derivative (μ : ℝ) (hμ : μ ≠ 0) (p : ℝ[X]) :
    derivative (derivative (evenSeries μ p)) = μ • (evenSeries μ p - p) := by
  unfold evenSeries
  have hz : derivative^[2 * (p.natDegree + 1)] p = 0 := iterate_derivative_eq_zero (by omega)
  have hdd : ∀ i : ℕ, derivative (derivative (derivative^[2 * i] p)) = derivative^[2 * (i + 1)] p := by
    intro i
    rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  simp only [map_sum, map_smul, hdd]
  rw [Finset.sum_range_succ, hz, smul_zero, add_zero]
  rw [Finset.sum_range_succ' (fun i => (μ ^ i)⁻¹ • derivative^[2 * i] p)]
  simp only [pow_zero, inv_one, one_smul, mul_zero, Function.iterate_zero, id]
  rw [add_sub_cancel_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  rw [pow_succ]
  field_simp

private lemma hasDerivAt_combination (P : ℝ[X]) (A B s x : ℝ) :
    HasDerivAt (fun y => P.eval y - A * Real.cosh (s * y) - B * Real.sinh (s * y))
      ((derivative P).eval x - A * (s * Real.sinh (s * x)) - B * (s * Real.cosh (s * x))) x := by
  have h2 : HasDerivAt (fun y => s * y) s x := by simpa using (hasDerivAt_id x).const_mul s
  exact (((P.hasDerivAt x).sub (h2.cosh.const_mul A)).sub (h2.sinh.const_mul B)).congr_deriv (by ring)

private lemma hasDerivAt_combination_deriv (P : ℝ[X]) (A B s x : ℝ) :
    HasDerivAt (fun y => (derivative P).eval y - A * (s * Real.sinh (s * y)) - B * (s * Real.cosh (s * y)))
      ((derivative (derivative P)).eval x - A * (s * (s * Real.cosh (s * x)))
        - B * (s * (s * Real.sinh (s * x)))) x := by
  have h2 : HasDerivAt (fun y => s * y) s x := by simpa using (hasDerivAt_id x).const_mul s
  exact ((((derivative P).hasDerivAt x).sub ((h2.sinh.const_mul s).const_mul A)).sub
    ((h2.cosh.const_mul s).const_mul B)).congr_deriv (by ring)

private lemma identity_of_form (μ : ℝ) (hμ : 0 < μ) (p P : ℝ[X])
    (hP : derivative (derivative P) = μ • (P - p)) (A B : ℝ) (U : ℝ → ℝ)
    (hU : U = fun y => P.eval y - A * Real.cosh (Real.sqrt μ * y) - B * Real.sinh (Real.sqrt μ * y))
    (h1 : U 1 = 0) (hm1 : U (-1) = 0) :
    ContDiff ℝ 2 U ∧
      (∫ x in (-1 : ℝ)..1, (p.eval x - U x) ^ 2) + μ⁻¹ * (∫ x in (-1 : ℝ)..1, deriv U x ^ 2)
        = ∫ x in (-1 : ℝ)..1, (p.eval x - U x) * p.eval x := by
  set s := Real.sqrt μ with hs
  have hs2 : s * s = μ := Real.mul_self_sqrt hμ.le
  set V : ℝ → ℝ := fun y => (derivative P).eval y - A * (s * Real.sinh (s * y))
    - B * (s * Real.cosh (s * y)) with hV
  set W : ℝ → ℝ := fun y => (derivative (derivative P)).eval y - A * (s * (s * Real.cosh (s * y)))
    - B * (s * (s * Real.sinh (s * y))) with hW
  have dU : ∀ x, HasDerivAt U (V x) x := by
    intro x; rw [hU]; exact hasDerivAt_combination P A B s x
  have dV : ∀ x, HasDerivAt V (W x) x := fun x => hasDerivAt_combination_deriv P A B s x
  have hWU : ∀ x, W x = μ * (U x - p.eval x) := by
    intro x
    simp only [hW, hU, hP, eval_smul, eval_sub, smul_eq_mul]
    linear_combination (-(A * Real.cosh (s * x)) - B * Real.sinh (s * x)) * hs2
  have cU : Continuous U := continuous_iff_continuousAt.2 fun x => (dU x).continuousAt
  have cV : Continuous V := continuous_iff_continuousAt.2 fun x => (dV x).continuousAt
  have cp : Continuous fun x => p.eval x := p.continuous
  have cW : Continuous W := by
    have : W = fun x => μ * (U x - p.eval x) := funext hWU
    rw [this]; exact continuous_const.mul (cU.sub cp)
  have hPc : ContDiff ℝ 2 fun y => P.eval y := by
    simpa using P.contDiff_aeval (𝕜 := ℝ) 2
  refine ⟨?_, ?_⟩
  · rw [hU]; fun_prop
  have hderiv : deriv U = V := funext fun x => (dU x).deriv
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (-1 : ℝ)) (b := 1)
    (fun x _ => dU x) (fun x _ => dV x) (cV.intervalIntegrable _ _) (cW.intervalIntegrable _ _)
  rw [h1, hm1, zero_mul, zero_mul, sub_zero, zero_sub] at ibp
  have e1 : (∫ x in (-1 : ℝ)..1, U x * W x) = -μ * ∫ x in (-1 : ℝ)..1, U x * (p.eval x - U x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; rw [hWU]; ring
  have e2 : (∫ x in (-1 : ℝ)..1, V x ^ 2) = μ * ∫ x in (-1 : ℝ)..1, U x * (p.eval x - U x) := by
    have : (∫ x in (-1 : ℝ)..1, V x ^ 2) = ∫ x in (-1 : ℝ)..1, V x * V x := by
      congr 1; funext x; ring
    rw [this]; linarith
  have i1 : IntervalIntegrable (fun x => (p.eval x - U x) ^ 2) volume (-1 : ℝ) 1 :=
    ((cp.sub cU).pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => U x * (p.eval x - U x)) volume (-1 : ℝ) 1 :=
    (cU.mul (cp.sub cU)).intervalIntegrable _ _
  rw [hderiv, e2, ← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul, ← intervalIntegral.integral_add i1 i2]
  congr 1; funext x; ring

theorem intervalIdentity : IntervalIdentityStatement := by
  intro μ p hμ
  have hs0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hc : Real.cosh (Real.sqrt μ) ≠ 0 := (Real.cosh_pos _).ne'
  have hsn : Real.sinh (Real.sqrt μ) ≠ 0 := (Real.sinh_pos_iff.2 hs0).ne'
  have hU : intervalResolvent μ p = fun y => (evenSeries μ p).eval y
      - ((evenSeries μ p).eval 1 + (evenSeries μ p).eval (-1)) / (2 * Real.cosh (Real.sqrt μ))
        * Real.cosh (Real.sqrt μ * y)
      - ((evenSeries μ p).eval 1 - (evenSeries μ p).eval (-1)) / (2 * Real.sinh (Real.sqrt μ))
        * Real.sinh (Real.sqrt μ * y) := by
    funext y; simp only [intervalResolvent, intervalSmoothed]; ring
  have h1 : intervalResolvent μ p 1 = 0 := by
    rw [hU]; simp only [mul_one]; field_simp; ring
  have hm1 : intervalResolvent μ p (-1) = 0 := by
    rw [hU]; simp only [mul_neg, mul_one, Real.cosh_neg, Real.sinh_neg]; field_simp; ring
  obtain ⟨hcd, hid⟩ := identity_of_form μ hμ p (evenSeries μ p)
    (evenSeries_second_derivative μ hμ.ne' p) _ _ _ hU h1 hm1
  have hsm : ∀ x, intervalSmoothed μ p x = p.eval x - intervalResolvent μ p x := by
    intro x; simp only [intervalResolvent]; ring
  simp_rw [hsm]
  exact ⟨hcd, hm1, h1, hid⟩

end Spectral

end CellCert

end Breakdown
