import Breakdown.FracCert.StKernel

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.KernelMultiplier

lemma far_le (e N ρ : ℝ) (l : ℤ) (hN : 0 ≤ N) (hρ : 0 < ρ) (h : 1 < (2:ℝ) ^ (l:ℝ) * ρ) :
    (2:ℝ) ^ (e * l) ≤
      2 ^ N * ρ ^ N * ((2:ℝ) ^ ((e + N) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-N)) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have hsplit : (2:ℝ) ^ ((e + N) * l) = 2 ^ (e * l) * ((2:ℝ) ^ (l:ℝ)) ^ N := by
    rw [add_mul, Real.rpow_add (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm N]
  rw [hsplit, Real.rpow_neg h1.le]
  have hle : (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N ≤ (2 * ((2:ℝ) ^ (l:ℝ) * ρ)) ^ N :=
    Real.rpow_le_rpow h1.le (by linarith) hN
  have hpos : 0 < (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N := Real.rpow_pos_of_pos h1 N
  rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow ht.le hρ.le] at hle
  have h2e : 0 < (2:ℝ) ^ (e * l) := by positivity
  have heq : 2 ^ N * ρ ^ N * (2 ^ (e * (l:ℝ)) * ((2:ℝ) ^ (l:ℝ)) ^ N * ((1 + 2 ^ (l:ℝ) * ρ) ^ N)⁻¹)
      = 2 ^ (e * (l:ℝ)) * ((2 ^ N * (((2:ℝ) ^ (l:ℝ)) ^ N * ρ ^ N)) / (1 + 2 ^ (l:ℝ) * ρ) ^ N) := by
    ring
  rw [heq]
  have hq : 1 ≤ (2 ^ N * (((2:ℝ) ^ (l:ℝ)) ^ N * ρ ^ N)) / (1 + 2 ^ (l:ℝ) * ρ) ^ N := by
    rw [le_div_iff₀ hpos]; linarith
  nlinarith

lemma near_le (a N ρ : ℝ) (l : ℤ) (hN : 0 ≤ N) (hρ : 0 < ρ) (h : (2:ℝ) ^ (l:ℝ) * ρ ≤ 1) :
    (2:ℝ) ^ (a * l) ≤ 2 ^ N * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-N)) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have hpos : 0 < (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N := Real.rpow_pos_of_pos h1 N
  have hle : (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ N ≤ 2 ^ N :=
    Real.rpow_le_rpow h1.le (by linarith) hN
  rw [Real.rpow_neg h1.le]
  have h2e : 0 < (2:ℝ) ^ (a * l) := by positivity
  have heq : 2 ^ N * (2 ^ (a * (l:ℝ)) * ((1 + 2 ^ (l:ℝ) * ρ) ^ N)⁻¹)
      = 2 ^ (a * (l:ℝ)) * (2 ^ N / (1 + 2 ^ (l:ℝ) * ρ) ^ N) := by ring
  rw [heq]
  have hq : 1 ≤ (2:ℝ) ^ N / (1 + 2 ^ (l:ℝ) * ρ) ^ N := by
    rw [le_div_iff₀ hpos]; linarith
  nlinarith

lemma combine (f T1 T2 T3 : ℤ → ℝ) (c1 c2 c3 : ℝ) (hf : ∀ l, 0 ≤ f l)
    (hfg : ∀ l, f l ≤ c1 * T1 l + c2 * T2 l + c3 * T3 l)
    (s1 : Summable T1) (s2 : Summable T2) (s3 : Summable T3) :
    Summable f ∧ ∑' l, f l ≤ c1 * ∑' l, T1 l + c2 * ∑' l, T2 l + c3 * ∑' l, T3 l := by
  have hg : Summable (fun l => c1 * T1 l + c2 * T2 l + c3 * T3 l) :=
    ((s1.mul_left c1).add (s2.mul_left c2)).add (s3.mul_left c3)
  have hs : Summable f := Summable.of_nonneg_of_le hf hfg hg
  refine ⟨hs, (Summable.tsum_le_tsum hfg hs hg).trans (le_of_eq ?_)⟩
  rw [Summable.tsum_add ((s1.mul_left c1).add (s2.mul_left c2)) (s3.mul_left c3),
    Summable.tsum_add (s1.mul_left c1) (s2.mul_left c2), tsum_mul_left, tsum_mul_left,
    tsum_mul_left]

lemma pointwise (a e1 e2 p1 p2 ρ : ℝ) (l : ℤ) (ha : 0 < a) (he1 : e1 < 0) (he2 : e2 < 0)
    (hρ : 0 < ρ) :
    (if (2:ℝ) ^ (l:ℝ) * ρ ≤ 1 then (2:ℝ) ^ (a * l)
        else (2:ℝ) ^ (e1 * l) * ρ ^ p1 + (2:ℝ) ^ (e2 * l) * ρ ^ p2)
      ≤ 2 ^ (a + 1) * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(a + 1)))
        + (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1)))
        + (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by
  have ht : 0 < (2:ℝ) ^ (l:ℝ) := by positivity
  have h1 : 0 < 1 + (2:ℝ) ^ (l:ℝ) * ρ := by positivity
  have n1 : 0 ≤ 2 ^ (a + 1) * ((2:ℝ) ^ (a * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(a + 1))) := by
    positivity
  have n2 : 0 ≤ (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) := by positivity
  have n3 : 0 ≤ (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by positivity
  split_ifs with hl
  · have := near_le a (a + 1) ρ l (by linarith) hρ hl
    linarith
  · push Not at hl
    have k2 := far_le e1 (1 - e1) ρ l (by linarith) hρ hl
    have k3 := far_le e2 (1 - e2) ρ l (by linarith) hρ hl
    rw [show e1 + (1 - e1) = 1 by ring] at k2
    rw [show e2 + (1 - e2) = 1 by ring] at k3
    have q2 := mul_le_mul_of_nonneg_right k2 (by positivity : (0:ℝ) ≤ ρ ^ p1)
    have q3 := mul_le_mul_of_nonneg_right k3 (by positivity : (0:ℝ) ≤ ρ ^ p2)
    have r2 : 2 ^ (1 - e1) * ρ ^ (1 - e1) *
        ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) * ρ ^ p1
        = (2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e1))) := by ring
    have r3 : 2 ^ (1 - e2) * ρ ^ (1 - e2) *
        ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) * ρ ^ p2
        = (2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2)
          * ((2:ℝ) ^ ((1:ℝ) * l) * (1 + (2:ℝ) ^ (l:ℝ) * ρ) ^ (-(1 - e2))) := by ring
    rw [r2] at q2
    rw [r3] at q3
    linarith

lemma far_sum (h4 : Breakdown.FracCert.DyadicSumStatement) (a e1 e2 p1 p2 : ℝ) (ha : 0 < a) (he1 : e1 < 0)
    (he2 : e2 < 0) (hp1 : p1 - e1 = -a) (hp2 : p2 - e2 = -a) :
    ∃ K : ℝ, ∀ ρ : ℝ, 0 < ρ →
      Summable (fun l : ℤ => if (2:ℝ) ^ (l:ℝ) * ρ ≤ 1 then (2:ℝ) ^ (a * l)
        else (2:ℝ) ^ (e1 * l) * ρ ^ p1 + (2:ℝ) ^ (e2 * l) * ρ ^ p2) ∧
      ∑' l : ℤ, (if (2:ℝ) ^ (l:ℝ) * ρ ≤ 1 then (2:ℝ) ^ (a * l)
        else (2:ℝ) ^ (e1 * l) * ρ ^ p1 + (2:ℝ) ^ (e2 * l) * ρ ^ p2) ≤ K * ρ ^ (-a) := by
  obtain ⟨C1, hC1⟩ := h4 a (a + 1) ha (by linarith)
  obtain ⟨C2, hC2⟩ := h4 1 (1 - e1) one_pos (by linarith)
  obtain ⟨C3, hC3⟩ := h4 1 (1 - e2) one_pos (by linarith)
  refine ⟨2 ^ (a + 1) * C1 + 2 ^ (1 - e1) * C2 + 2 ^ (1 - e2) * C3, fun ρ hρ => ?_⟩
  obtain ⟨s1, t1⟩ := hC1 ρ hρ
  obtain ⟨s2, t2⟩ := hC2 ρ hρ
  obtain ⟨s3, t3⟩ := hC3 ρ hρ
  have hfn : ∀ l : ℤ, 0 ≤ (if (2:ℝ) ^ (l:ℝ) * ρ ≤ 1 then (2:ℝ) ^ (a * l)
        else (2:ℝ) ^ (e1 * l) * ρ ^ p1 + (2:ℝ) ^ (e2 * l) * ρ ^ p2) := by
    intro l; split_ifs <;> positivity
  have hA2n : (0:ℝ) ≤ 2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1 := by positivity
  have hA3n : (0:ℝ) ≤ 2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2 := by positivity
  obtain ⟨hs, hle⟩ := combine _ _ _ _ _ _ _ hfn
    (fun l => pointwise a e1 e2 p1 p2 ρ l ha he1 he2 hρ) s1 s2 s3
  refine ⟨hs, hle.trans ?_⟩
  have e2' : 2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1 * ρ ^ (-(1:ℝ)) = 2 ^ (1 - e1) * ρ ^ (-a) := by
    rw [mul_assoc, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 2; linarith
  have e3' : 2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2 * ρ ^ (-(1:ℝ)) = 2 ^ (1 - e2) * ρ ^ (-a) := by
    rw [mul_assoc, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 2; linarith
  have u1 := mul_le_mul_of_nonneg_left t1 (by positivity : (0:ℝ) ≤ 2 ^ (a + 1))
  have u2 := mul_le_mul_of_nonneg_left t2 hA2n
  have u3 := mul_le_mul_of_nonneg_left t3 hA3n
  have w2 : 2 ^ (1 - e1) * ρ ^ (1 - e1) * ρ ^ p1 * (C2 * ρ ^ (-(1:ℝ)))
      = 2 ^ (1 - e1) * C2 * ρ ^ (-a) := by
    rw [mul_left_comm, e2']; ring
  have w3 : 2 ^ (1 - e2) * ρ ^ (1 - e2) * ρ ^ p2 * (C3 * ρ ^ (-(1:ℝ)))
      = 2 ^ (1 - e2) * C3 * ρ ^ (-a) := by
    rw [mul_left_comm, e3']; ring
  rw [w2] at u2
  rw [w3] at u3
  have := add_le_add (add_le_add u1 u2) u3
  linarith

end Breakdown.FracInternal.KernelMultiplier

namespace Breakdown.FracCert

open Breakdown.FracInternal.KernelMultiplier in
theorem homogeneousMultiplier_of (h1 : RingCutoffStatement) (h2 : DyadicSplitStatement)
    (h3 : DyadicPieceBoundStatement) (h4 : DyadicSumStatement) :
    HomogeneousMultiplierStatement := by
  intro σ d β hd hβ hβ3 hσ f F hf hF hM
  obtain ⟨θ, hθ⟩ := h1
  obtain ⟨hsmooth, hsum⟩ := h2 σ d β θ hd hβ hβ3 hσ hθ f F hf hF hM
  refine ⟨hsmooth, fun i => ?_⟩
  have hcont : Continuous (iteratedFDeriv ℝ i
      (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ))) :=
    hsmooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) 2).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨C, hC⟩ := h3 σ d β θ hd hβ hβ3 hσ hθ f hf i
  have hc : d ≤ (⌈d⌉₊ : ℝ) := Nat.le_ceil d
  obtain ⟨K, hK⟩ := far_sum h4 (d + i + β) (d - 2 * (⌈d⌉₊ + 1)) (d - 1 - ⌈d⌉₊)
    (-(β + i + 2 * (⌈d⌉₊ + 1))) (-(1 + β + ⌈d⌉₊ + i)) (by positivity) (by linarith)
    (by linarith) (by ring) (by ring)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hexp : 0 ≤ β + d + i := by positivity
  refine ⟨max (3 ^ (β + d + i) * B) (2 ^ (β + d + i) * (max C 0 * K)), fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ 2
  · have hyb : y ∈ Metric.closedBall (0 : Space) 2 := by simpa using hy
    have hp : (1 + ‖y‖) ^ (β + d + i) ≤ 3 ^ (β + d + i) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hexp
    refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul hp (hB y hyb) (norm_nonneg _) (by positivity)
  · push Not at hy
    have hρ : 0 < ‖y‖ := by linarith
    obtain ⟨hs, ht⟩ := hK ‖y‖ hρ
    have hnorm := HasSum.norm_le_of_bounded (hsum i y) (hs.hasSum.mul_left (max C 0))
      (fun l => (hC l y hy.le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by split_ifs <;> positivity)))
    have hD : ‖iteratedFDeriv ℝ i (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ)) y‖
        ≤ max C 0 * K * ‖y‖ ^ (-(β + d + i)) := by
      rw [show -(β + d + i) = -(d + i + β) by ring, mul_assoc]
      exact hnorm.trans (mul_le_mul_of_nonneg_left ht (le_max_right _ _))
    have hp : (1 + ‖y‖) ^ (β + d + i) ≤ (2 * ‖y‖) ^ (β + d + i) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hexp
    have hcancel : (2 * ‖y‖) ^ (β + d + i) * ‖y‖ ^ (-(β + d + i)) = 2 ^ (β + d + i) := by
      rw [Real.mul_rpow (by norm_num) hρ.le, mul_assoc, ← Real.rpow_add hρ, add_neg_cancel,
        Real.rpow_zero, mul_one]
    refine le_trans ?_ (le_max_right _ _)
    have hK0 : 0 ≤ max C 0 * K * ‖y‖ ^ (-(β + d + i)) :=
      (norm_nonneg _).trans hD
    calc (1 + ‖y‖) ^ (β + d + i) * ‖iteratedFDeriv ℝ i
          (FourierTransform.fourierInv (fun ξ => σ ξ * F ξ)) y‖
        ≤ (2 * ‖y‖) ^ (β + d + i) * (max C 0 * K * ‖y‖ ^ (-(β + d + i))) :=
          mul_le_mul hp hD (norm_nonneg _) (by positivity)
      _ = 2 ^ (β + d + i) * (max C 0 * K) := by
          rw [← hcancel]; ring

end Breakdown.FracCert
