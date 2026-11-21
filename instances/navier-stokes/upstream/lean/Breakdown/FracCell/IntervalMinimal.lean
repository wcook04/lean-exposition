import Breakdown.FracCell.StSpectral

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

namespace IntervalMinimalInternal

theorem evenSeries_second (μ : ℝ) (hμ : μ ≠ 0) (p : ℝ[X]) :
    derivative (derivative (evenSeries μ p)) = μ • (evenSeries μ p - p) := by
  have hz : derivative^[2 * (p.natDegree + 1)] p = 0 := iterate_derivative_eq_zero (by omega)
  have hE : evenSeries μ p = (∑ i ∈ Finset.range (p.natDegree + 1),
      (μ ^ (i + 1))⁻¹ • derivative^[2 * (i + 1)] p) + p := by
    have h := Finset.sum_range_succ' (fun i => (μ ^ i)⁻¹ • derivative^[2 * i] p) (p.natDegree + 1)
    rw [Finset.sum_range_succ, hz, smul_zero, add_zero] at h
    simp only [evenSeries]
    rw [h]
    simp
  have hDD : derivative (derivative (evenSeries μ p)) = ∑ i ∈ Finset.range (p.natDegree + 1),
      (μ ^ i)⁻¹ • derivative^[2 * (i + 1)] p := by
    simp only [evenSeries, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [show 2 * (i + 1) = (2 * i).succ.succ by omega, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  rw [hDD, hE, add_sub_cancel_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  field_simp
  ring

theorem second_form (E : ℝ[X]) (A B s : ℝ) :
    deriv (deriv (fun x => E.eval x - A * Real.cosh (s * x) - B * Real.sinh (s * x))) =
      fun x => (derivative (derivative E)).eval x
        - s ^ 2 * (A * Real.cosh (s * x) + B * Real.sinh (s * x)) := by
  have h1 : ∀ x, HasDerivAt (fun x => E.eval x - A * Real.cosh (s * x) - B * Real.sinh (s * x))
      ((derivative E).eval x - A * s * Real.sinh (s * x) - B * s * Real.cosh (s * x)) x := by
    intro x
    have hc := ((hasDerivAt_id x).const_mul s).cosh
    have hs := ((hasDerivAt_id x).const_mul s).sinh
    convert ((E.hasDerivAt x).sub (hc.const_mul A)).sub (hs.const_mul B) using 1
    all_goals first | rfl | (simp only [id, mul_one]; ring)
  have hd1 : deriv (fun x => E.eval x - A * Real.cosh (s * x) - B * Real.sinh (s * x)) =
      fun x => (derivative E).eval x - A * s * Real.sinh (s * x) - B * s * Real.cosh (s * x) :=
    funext fun x => (h1 x).deriv
  rw [hd1]
  funext x
  have hc := ((hasDerivAt_id x).const_mul s).cosh
  have hs := ((hasDerivAt_id x).const_mul s).sinh
  have h2 : HasDerivAt
      (fun x => (derivative E).eval x - A * s * Real.sinh (s * x) - B * s * Real.cosh (s * x))
      ((derivative (derivative E)).eval x
        - s ^ 2 * (A * Real.cosh (s * x) + B * Real.sinh (s * x))) x := by
    convert (((derivative E).hasDerivAt x).sub (hs.const_mul (A * s))).sub (hc.const_mul (B * s))
      using 1
    all_goals first | rfl | (simp only [id, mul_one]; ring)
  exact h2.deriv

theorem resolvent_second (μ : ℝ) (hμ : 0 < μ) (p : ℝ[X]) (x : ℝ) :
    deriv (deriv (intervalResolvent μ p)) x = μ * (intervalResolvent μ p x - p.eval x) := by
  have hu : intervalResolvent μ p = fun x => (evenSeries μ p).eval x
      - ((evenSeries μ p).eval 1 + (evenSeries μ p).eval (-1)) / (2 * Real.cosh (Real.sqrt μ))
        * Real.cosh (Real.sqrt μ * x)
      - ((evenSeries μ p).eval 1 - (evenSeries μ p).eval (-1)) / (2 * Real.sinh (Real.sqrt μ))
        * Real.sinh (Real.sqrt μ * x) := by
    funext y
    simp only [intervalResolvent, intervalSmoothed]
    ring
  rw [hu, second_form, evenSeries_second μ hμ.ne' p, Real.sq_sqrt hμ.le]
  simp only [eval_smul, eval_sub, smul_eq_mul]
  ring

end IntervalMinimalInternal

open IntervalMinimalInternal in
theorem intervalMinimal_of (h1 : IntervalIdentityStatement) : IntervalMinimalStatement := by
  intro μ p hμ w hwL hw0 hw1
  obtain ⟨K, hK⟩ := hwL
  obtain ⟨hC, hu0, hu1, hval⟩ := h1 μ p hμ
  rw [← hval]
  have hODE : ∀ x, deriv (deriv (intervalResolvent μ p)) x
      = μ * (intervalResolvent μ p x - p.eval x) := resolvent_second μ hμ p
  set u := intervalResolvent μ p with hu_def
  have hPc : Continuous fun x => p.eval x := p.continuous
  have huc : Continuous u := hC.continuous
  have hC1 : ContDiff ℝ 1 (deriv u) := hC.deriv'
  have hu'c : Continuous (deriv u) := hC1.continuous
  have hwc : Continuous w := hK.continuous
  have hwAC : AbsolutelyContinuousOnInterval w (-1) 1 :=
    hK.lipschitzOnWith.absolutelyContinuousOnInterval
  have huAC : AbsolutelyContinuousOnInterval u (-1) 1 :=
    (hC.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval
  have hu'AC : AbsolutelyContinuousOnInterval (deriv u) (-1) 1 :=
    hC1.contDiffOn.absolutelyContinuousOnInterval
  have hw'i : IntervalIntegrable (deriv w) volume (-1) 1 := hwAC.intervalIntegrable_deriv
  have hw'b : ∀ x, |deriv w x| ≤ K := fun x => by
    have := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hK
    simpa using this
  have hw'2 : IntervalIntegrable (fun x => deriv w x ^ 2) volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => (K : ℝ) ^ 2) intervalIntegrable_const
      ((measurable_deriv w).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw'b x) 2
  have huw : IntervalIntegrable (fun x => deriv u x * deriv w x) volume (-1) 1 :=
    hw'i.continuousOn_mul hu'c.continuousOn
  have hci : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume (-1) 1 :=
    fun f hf => hf.intervalIntegrable _ _
  have hdd : IntervalIntegrable (fun x => (deriv w x - deriv u x) ^ 2) volume (-1) 1 := by
    have := (hw'2.sub (huw.const_mul 2)).add (hci (fun x => deriv u x ^ 2) (by fun_prop))
    convert this using 1
    funext x
    ring
  have hIBPw : ∫ x in (-1 : ℝ)..1, deriv u x * deriv w x
      = -∫ x in (-1 : ℝ)..1, deriv (deriv u) x * w x := by
    rw [hu'AC.integral_mul_deriv_eq_deriv_mul hwAC, hw0, hw1]
    ring
  have hIBPu : ∫ x in (-1 : ℝ)..1, deriv u x ^ 2
      = -∫ x in (-1 : ℝ)..1, deriv (deriv u) x * u x := by
    have h := hu'AC.integral_mul_deriv_eq_deriv_mul huAC
    rw [hu0, hu1] at h
    simp only [sq]
    rw [h]
    ring
  have hc1 : ∫ x in (-1 : ℝ)..1, deriv (deriv u) x * w x
      = μ * ∫ x in (-1 : ℝ)..1, (u x - p.eval x) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [hODE]
    ring
  have hc2 : ∫ x in (-1 : ℝ)..1, deriv (deriv u) x * u x
      = μ * ∫ x in (-1 : ℝ)..1, (u x - p.eval x) * u x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [hODE]
    ring
  have ha1 : ∫ x in (-1 : ℝ)..1, (p.eval x - w x) ^ 2
      = (∫ x in (-1 : ℝ)..1, (p.eval x - u x) ^ 2) + (∫ x in (-1 : ℝ)..1, (u x - w x) ^ 2)
        - 2 * (∫ x in (-1 : ℝ)..1, (u x - p.eval x) * u x)
        + 2 * (∫ x in (-1 : ℝ)..1, (u x - p.eval x) * w x) := by
    have hf : (fun x => (p.eval x - w x) ^ 2) = fun x => ((p.eval x - u x) ^ 2 + (u x - w x) ^ 2)
        - 2 * ((u x - p.eval x) * u x) + 2 * ((u x - p.eval x) * w x) := by
      funext x
      ring
    rw [hf, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact hci _ (by fun_prop)
  have hb1 : ∫ x in (-1 : ℝ)..1, deriv w x ^ 2
      = (∫ x in (-1 : ℝ)..1, (deriv w x - deriv u x) ^ 2)
        + 2 * (∫ x in (-1 : ℝ)..1, deriv u x * deriv w x)
        - ∫ x in (-1 : ℝ)..1, deriv u x ^ 2 := by
    have hf : (fun x => deriv w x ^ 2) = fun x => ((deriv w x - deriv u x) ^ 2
        + 2 * (deriv u x * deriv w x)) - deriv u x ^ 2 := by
      funext x
      ring
    rw [hf, intervalIntegral.integral_sub (hdd.add (huw.const_mul 2)) (hci _ (by fun_prop)),
      intervalIntegral.integral_add hdd (huw.const_mul 2), intervalIntegral.integral_const_mul]
  have h3 : 0 ≤ ∫ x in (-1 : ℝ)..1, (u x - w x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have h4 : 0 ≤ ∫ x in (-1 : ℝ)..1, (deriv w x - deriv u x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have hk2 : μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv u x ^ 2
      = -∫ x in (-1 : ℝ)..1, (u x - p.eval x) * u x := by
    rw [hIBPu, hc2]
    field_simp
  have hk4 : μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv u x * deriv w x
      = -∫ x in (-1 : ℝ)..1, (u x - p.eval x) * w x := by
    rw [hIBPw, hc1]
    field_simp
  have h5 : 0 ≤ μ⁻¹ * ∫ x in (-1 : ℝ)..1, (deriv w x - deriv u x) ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hμ.le) h4
  rw [ha1, hb1]
  have hexp : μ⁻¹ * ((∫ x in (-1 : ℝ)..1, (deriv w x - deriv u x) ^ 2)
        + 2 * (∫ x in (-1 : ℝ)..1, deriv u x * deriv w x)
        - ∫ x in (-1 : ℝ)..1, deriv u x ^ 2)
      = μ⁻¹ * (∫ x in (-1 : ℝ)..1, (deriv w x - deriv u x) ^ 2)
        + 2 * (μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv u x * deriv w x)
        - μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv u x ^ 2 := by
    ring
  rw [hexp]
  linarith

end Spectral

end CellCert

end Breakdown
