import Breakdown.CertCell.ShapeTypeTwoDecayKey

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem bound_near_or_far {C0 M R r u : ℝ} (hM : 0 ≤ M) (hR : 2 ≤ R) (hr : 0 ≤ r) (hu : 0 ≤ u) {k : ℕ}
    (hk : k ≤ 3) (hnear : r ≤ R → u ≤ C0) (hfar : R ≤ r → u ≤ M / r ^ k) :
    u ≤ max (|C0| * (1 + R) ^ 3) (8 * M) / (1 + r) ^ k := by
  rw [le_div_iff₀ (by positivity)]
  by_cases hrR : r ≤ R
  · have h1 : (1 + r) ^ k ≤ (1 + R) ^ 3 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)
    have h2 : u ≤ |C0| := (hnear hrR).trans (le_abs_self C0)
    exact (mul_le_mul h2 h1 (by positivity) (abs_nonneg _)).trans (le_max_left _ _)
  · have hRr : R ≤ r := le_of_lt (not_le.1 hrR)
    have hr0 : 0 < r := by linarith
    have h1 : (1 + r) ^ k ≤ 8 * r ^ k := by
      calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = 2 ^ k * r ^ k := by rw [mul_pow]
        _ ≤ 8 * r ^ k := by
          have : (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
          nlinarith [pow_pos hr0 k]
    have h2 := hfar hRr
    calc u * (1 + r) ^ k ≤ M / r ^ k * (8 * r ^ k) := mul_le_mul h2 h1 (by positivity) ((hu).trans h2)
      _ = 8 * M := by field_simp
      _ ≤ max (|C0| * (1 + R) ^ 3) (8 * M) := le_max_right _ _

end Internal

theorem typeTwoKeyDecay_of_smooth (hs : TypeTwoKeySmooth) : TypeTwoKeyDecay := by
  intro P D κ σ hP hD hκ h0
  obtain ⟨M, R, hM, hR, hfar⟩ := (Internal.farBound_typeTwoKey P hP D hD κ hκ h0 σ).bounds_one
  obtain ⟨C0, hC0⟩ := (hs P D κ σ hP hD hκ h0).bounded_on_ball R
  refine ⟨⟨max (|C0| * (1 + R) ^ 3) (8 * M), fun y => ⟨?_, ?_, ?_⟩⟩⟩
  · have h := Internal.bound_near_or_far (k := 1) hM hR (norm_nonneg y) (norm_nonneg _) (by norm_num)
      (fun h => (hC0 y h).1) (fun h => by rw [pow_one]; exact (hfar y h).1)
    rwa [pow_one] at h
  · exact Internal.bound_near_or_far (k := 2) hM hR (norm_nonneg y) (norm_nonneg _) (by norm_num)
      (fun h => (hC0 y h).2.1) (fun h => (hfar y h).2.1)
  · exact Internal.bound_near_or_far (k := 3) hM hR (norm_nonneg y) (norm_nonneg _) (by norm_num)
      (fun h => (hC0 y h).2.2) (fun h => (hfar y h).2.2)

end GivenShape

end CertCell

end Breakdown
