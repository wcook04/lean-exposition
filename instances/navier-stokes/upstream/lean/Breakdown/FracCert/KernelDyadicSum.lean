import Breakdown.FracCert.StKernel

open Real

noncomputable section

namespace Breakdown.FracCert

namespace KernelDyadicSumInternal

def baseTerm (a N : ℝ) (m : ℤ) : ℝ := (2 : ℝ) ^ (a * (m : ℝ)) * (1 + (2 : ℝ) ^ (m : ℝ)) ^ (-N)

lemma baseTerm_nonneg (a N : ℝ) (m : ℤ) : 0 ≤ baseTerm a N m := by
  unfold baseTerm
  positivity

lemma baseTerm_summable (a N : ℝ) (ha : 0 < a) (hN : a < N) : Summable (baseTerm a N) := by
  apply Summable.of_nat_of_neg
  · have hq : (2 : ℝ) ^ (a - N) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    refine Summable.of_nonneg_of_le (fun n => baseTerm_nonneg a N _) (fun n => ?_)
      (summable_geometric_of_lt_one (by positivity) hq)
    unfold baseTerm
    have hc : (((n : ℤ) : ℝ)) = (n : ℝ) := by push_cast; ring
    rw [hc]
    have h1 : (1 + (2 : ℝ) ^ (n : ℝ)) ^ (-N) ≤ ((2 : ℝ) ^ (n : ℝ)) ^ (-N) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h2 : (2 : ℝ) ^ (a * (n : ℝ)) * ((2 : ℝ) ^ (n : ℝ)) ^ (-N) = ((2 : ℝ) ^ (a - N)) ^ n := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (a - N)), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · have hq : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    refine Summable.of_nonneg_of_le (fun n => baseTerm_nonneg a N _) (fun n => ?_)
      (summable_geometric_of_lt_one (by positivity) hq)
    unfold baseTerm
    have h1 : (1 + (2 : ℝ) ^ (((-(n : ℤ)) : ℤ) : ℝ)) ^ (-N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (((-(n : ℤ)) : ℤ) : ℝ); linarith) (by linarith)
    have h2 : (2 : ℝ) ^ (a * (((-(n : ℤ)) : ℤ) : ℝ)) = ((2 : ℝ) ^ (-a)) ^ n := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-a)), ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [← h2]
    calc (2 : ℝ) ^ (a * (((-(n : ℤ)) : ℤ) : ℝ)) * (1 + (2 : ℝ) ^ (((-(n : ℤ)) : ℤ) : ℝ)) ^ (-N)
        ≤ (2 : ℝ) ^ (a * (((-(n : ℤ)) : ℤ) : ℝ)) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _

lemma term_le (a N r : ℝ) (ha : 0 < a) (hN : a < N) (hr : 0 < r) (k : ℤ)
    (hk1 : 1 ≤ (2 : ℝ) ^ (k : ℝ) * r) (hk2 : (2 : ℝ) ^ (k : ℝ) * r ≤ 2) (l : ℤ) :
    (2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N) ≤
      (2 : ℝ) ^ a * r ^ (-a) * baseTerm a N (l - k) := by
  unfold baseTerm
  have hlk : (((l - k : ℤ)) : ℝ) = (l : ℝ) - (k : ℝ) := by push_cast; ring
  rw [hlk]
  set t := (2 : ℝ) ^ (k : ℝ) * r with ht
  have hsplit : (2 : ℝ) ^ (l : ℝ) * r = (2 : ℝ) ^ ((l : ℝ) - (k : ℝ)) * t := by
    rw [ht, ← mul_assoc, ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  have hden : (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N) ≤ (1 + (2 : ℝ) ^ ((l : ℝ) - (k : ℝ))) ^ (-N) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    rw [hsplit]
    have h0 : 0 ≤ (2 : ℝ) ^ ((l : ℝ) - (k : ℝ)) := by positivity
    nlinarith
  have hexp : (2 : ℝ) ^ (a * (l : ℝ)) = (2 : ℝ) ^ (a * ((l : ℝ) - (k : ℝ))) * ((2 : ℝ) ^ (k : ℝ)) ^ a := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hka : ((2 : ℝ) ^ (k : ℝ)) ^ a ≤ (2 : ℝ) ^ a * r ^ (-a) := by
    have hra : 0 < r ^ a := Real.rpow_pos_of_pos hr a
    have htt : ((2 : ℝ) ^ (k : ℝ)) ^ a * r ^ a = t ^ a := by
      rw [ht, Real.mul_rpow (by positivity) hr.le]
    have htle : t ^ a ≤ (2 : ℝ) ^ a := Real.rpow_le_rpow (by linarith) hk2 ha.le
    rw [Real.rpow_neg hr.le, ← div_eq_mul_inv, le_div_iff₀ hra, htt]
    exact htle
  rw [hexp]
  have hA : 0 ≤ (2 : ℝ) ^ (a * ((l : ℝ) - (k : ℝ))) := by positivity
  have hB : 0 ≤ (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N) := by positivity
  have hC : 0 ≤ (2 : ℝ) ^ a * r ^ (-a) := by positivity
  calc (2 : ℝ) ^ (a * ((l : ℝ) - (k : ℝ))) * ((2 : ℝ) ^ (k : ℝ)) ^ a * (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N)
      ≤ (2 : ℝ) ^ (a * ((l : ℝ) - (k : ℝ))) * ((2 : ℝ) ^ a * r ^ (-a)) * (1 + (2 : ℝ) ^ ((l : ℝ) - (k : ℝ))) ^ (-N) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hka hA) hden hB (mul_nonneg hA hC)
    _ = (2 : ℝ) ^ a * r ^ (-a) * ((2 : ℝ) ^ (a * ((l : ℝ) - (k : ℝ))) * (1 + (2 : ℝ) ^ ((l : ℝ) - (k : ℝ))) ^ (-N)) := by ring

lemma exists_shift (r : ℝ) (hr : 0 < r) :
    ∃ k : ℤ, 1 ≤ (2 : ℝ) ^ (k : ℝ) * r ∧ (2 : ℝ) ^ (k : ℝ) * r ≤ 2 := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hr one_lt_two
  refine ⟨-n, ?_, ?_⟩
  · rw [Real.rpow_intCast, zpow_neg, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
    exact hn1
  · rw [Real.rpow_intCast, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [zpow_add_one₀ (by norm_num)] at hn2
    linarith

end KernelDyadicSumInternal

open KernelDyadicSumInternal in
theorem dyadicSum : DyadicSumStatement := by
  intro a N ha hN
  refine ⟨(2 : ℝ) ^ a * ∑' m : ℤ, baseTerm a N m, fun r hr => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := exists_shift r hr
  have hG := baseTerm_summable a N ha hN
  have hGs : Summable (fun l : ℤ => baseTerm a N (l - k)) :=
    (Equiv.subRight k).summable_iff.mpr hG
  have hH : Summable (fun l : ℤ => (2 : ℝ) ^ a * r ^ (-a) * baseTerm a N (l - k)) := hGs.mul_left _
  have hF : Summable (fun l : ℤ => (2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * r) ^ (-N)) :=
    Summable.of_nonneg_of_le (fun l => by positivity) (term_le a N r ha hN hr k hk1 hk2) hH
  refine ⟨hF, ?_⟩
  have hle := Summable.tsum_le_tsum (term_le a N r ha hN hr k hk1 hk2) hF hH
  have hshift : ∑' l : ℤ, baseTerm a N (l - k) = ∑' m : ℤ, baseTerm a N m :=
    (Equiv.subRight k).tsum_eq (baseTerm a N)
  rw [tsum_mul_left, hshift] at hle
  linarith

end Breakdown.FracCert
