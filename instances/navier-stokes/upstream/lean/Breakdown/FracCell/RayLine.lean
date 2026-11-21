import Breakdown.FracCell.StExterior

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

private lemma rayLine_interval (a b : ℝ) (g : ℝ → ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hg : ContDiff ℝ 1 g) (hb : g b = 0) :
    (∫ r in a..b, g r ^ 2) ≤ 4 * ∫ r in a..b, r ^ 2 * deriv g r ^ 2 := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    ((hg.differentiable one_ne_zero) x).hasDerivAt
  have hcd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hc : Continuous g := hg.continuous
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun r => g r ^ 2) (2 * g x * deriv g x) x := by
    intro x _
    exact ((hd x).pow 2).congr_deriv (by norm_num)
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (fun r : ℝ => r) 1 x := fun x _ => hasDerivAt_id x
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (((continuous_const.mul hc).mul hcd).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)
  simp only [mul_one, hb] at hibp
  have hpt : ∀ x ∈ Icc a b, -(2 * g x * deriv g x * x) ≤
      g x ^ 2 / 2 + 2 * (x ^ 2 * deriv g x ^ 2) := by
    intro x _
    nlinarith [sq_nonneg (g x + 2 * x * deriv g x)]
  have hc1 : Continuous (fun x => g x ^ 2 / 2) := (hc.pow 2).div_const 2
  have hc2 : Continuous (fun x : ℝ => 2 * (x ^ 2 * deriv g x ^ 2)) :=
    continuous_const.mul ((continuous_id.pow 2).mul (hcd.pow 2))
  have hc3 : Continuous (fun x => -(2 * g x * deriv g x * x)) :=
    (((continuous_const.mul hc).mul hcd).mul continuous_id).neg
  have hmono : (∫ x in a..b, -(2 * g x * deriv g x * x)) ≤
      ∫ x in a..b, (g x ^ 2 / 2 + 2 * (x ^ 2 * deriv g x ^ 2)) := intervalIntegral.integral_mono_on hab (hc3.intervalIntegrable (μ := volume) a b)
    ((hc1.add hc2).intervalIntegrable (μ := volume) a b) hpt
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_add (hc1.intervalIntegrable a b)
    (hc2.intervalIntegrable a b), intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul] at hmono
  have hpos : 0 ≤ g a ^ 2 * a := by positivity
  linarith

theorem rayLine : RayLineStatement := by
  intro a g ha hg hsupp
  obtain ⟨b, hb⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
  have hz : ∀ x, b < x → g x = 0 ∧ deriv g x = 0 := by
    intro x hx
    have hn : x ∉ tsupport g := by
      intro hm
      have h1 := hb hm
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
      linarith [le_abs_self x]
    constructor
    · by_contra h
      exact hn (subset_tsupport g h)
    · by_contra h
      exact hn (support_deriv_subset h)
  set B := max a b + 1 with hB
  have haB : a ≤ B := by rw [hB]; linarith [le_max_left a b]
  have hbB : ∀ x, B < x → b < x := fun x hx => by
    rw [hB] at hx; linarith [le_max_right a b]
  have hconv : ∀ f : ℝ → ℝ, (∀ x, B < x → f x = 0) →
      ∫ r in Ioi a, f r = ∫ r in a..B, f r := by
    intro f hf
    rw [intervalIntegral.integral_of_le haB,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
    intro x hx
    apply hf
    simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hx
    exact hx.2 hx.1
  rw [hconv (fun r => g r ^ 2) (fun x hx => by simp [(hz x (hbB x hx)).1]),
    hconv (fun r => r ^ 2 * deriv g r ^ 2) (fun x hx => by simp [(hz x (hbB x hx)).2])]
  have hgB : g B = 0 := (hz B (by rw [hB]; linarith [le_max_right a b])).1
  exact rayLine_interval a B g ha haB hg hgB

end Exterior

end CellCert

end Breakdown
