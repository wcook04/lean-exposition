import Breakdown.CertCell.TailStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

theorem tailAbsorption : TailAbsorption := by
  intro b K Q k hT cT gT oT vT lowTop hB hF hC hg ho hv hog hH hCc hvl
  unfold TailBudget.Holds TailBudget.gradCharge at hB
  unfold TailBudget.remainder
  have hW0 : 0 ≤ b.velCharge := le_max_right _ _
  have hWv : b.velAbsorb + b.velPotential + b.velLeak ≤ b.velCharge := le_max_left _ _
  have hM0 : 0 ≤ max (b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k) 0 := le_max_right _ _
  have hMc : b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k ≤
      max (b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k) 0 := le_max_left _ _
  have h1 : b.hessFloor * (hessTailGain K Q k * gT) ≤ b.hessFloor * hT :=
    mul_le_mul_of_nonneg_left hH hF
  have h2 : b.curlGradFloor * (curlTailGain K Q k * oT) ≤ b.curlGradFloor * cT :=
    mul_le_mul_of_nonneg_left hCc hC
  have h3 : (b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k) * oT ≤
      max (b.curlAbsorb - b.curlGradFloor * curlTailGain K Q k) 0 * (2 * gT) :=
    (mul_le_mul_of_nonneg_right hMc ho).trans (mul_le_mul_of_nonneg_left hog hM0)
  have h4 : (b.velAbsorb + b.velPotential + b.velLeak) * vT ≤
      b.velCharge * (lowTop + gT / velTailGain K Q) :=
    (mul_le_mul_of_nonneg_right hWv hv).trans (mul_le_mul_of_nonneg_left hvl hW0)
  have h5 := mul_le_mul_of_nonneg_right hB hg
  have h6 : b.velCharge * (lowTop + gT / velTailGain K Q) =
      b.velCharge * lowTop + b.velCharge / velTailGain K Q * gT := by ring
  rw [h6] at h4
  nlinarith [h1, h2, h3, h4, h5]

private theorem quadForm_nonneg {A B c x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : c ^ 2 ≤ 4 * A * B) :
    0 ≤ A * x ^ 2 + B * y ^ 2 - c * x * y := by
  rcases hA.eq_or_lt with h0 | hpos
  · subst h0
    have hc : c = 0 := by nlinarith [sq_nonneg c]
    subst hc
    nlinarith [sq_nonneg y]
  · have key : 4 * A * (A * x ^ 2 + B * y ^ 2 - c * x * y) =
        (2 * A * x - c * y) ^ 2 + (4 * A * B - c ^ 2) * y ^ 2 := by ring
    have hr : 0 ≤ (2 * A * x - c * y) ^ 2 + (4 * A * B - c ^ 2) * y ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    rcases lt_or_ge (A * x ^ 2 + B * y ^ 2 - c * x * y) 0 with hn | hn
    · have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 4 * A) hn
      linarith
    · exact hn

private theorem sq_ratio_le {m u r v : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hu : 0 ≤ u) (h : m * u ≤ r * v) :
    m ^ 2 / r ^ 2 * u ^ 2 ≤ v ^ 2 := by
  have hsq : (m * u) ^ 2 ≤ (r * v) ^ 2 := pow_le_pow_left₀ (mul_nonneg hm hu) h 2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [hsq]

theorem pointwiseQuadraticTest : PointwiseQuadraticTest := by
  intro lo a kLow k r s x2 xc x1 xo x0 hr hk hcg hD hP hR
  obtain ⟨dh, dcg, dc, dg, dv, dx⟩ := hD
  obtain ⟨ph, ps, pG, pV, pX⟩ := hP
  obtain ⟨h2, hc, h1, ho, h0, hoo, r01, r12, rco⟩ := hR
  simp only [PointCoef.gradFloor, PointCoef.curlWithGain, PointCoef.velWithShift, mul_div_assoc]
    at pG pV pX
  unfold PointCoef.quad
  have m1n : 0 ≤ max (kLow - 1) 0 := le_max_right _ _
  have m2n : 0 ≤ max (kLow - 2) 0 := le_max_right _ _
  have m1k : max (kLow - 1) 0 ≤ max (k - 1) 0 := max_le_max (by linarith) le_rfl
  have m2k : max (kLow - 2) 0 ≤ max (k - 2) 0 := max_le_max (by linarith) le_rfl
  have q01 := sq_ratio_le hr m1n h0 ((mul_le_mul_of_nonneg_right m1k h0).trans r01)
  have q12 := sq_ratio_le hr m2n h1 ((mul_le_mul_of_nonneg_right m2k h1).trans r12)
  have qco := sq_ratio_le hr m1n ho ((mul_le_mul_of_nonneg_right m1k ho).trans rco)
  have t1n : 0 ≤ max (kLow - 1) 0 ^ 2 / r ^ 2 := by positivity
  generalize max (kLow - 1) 0 ^ 2 / r ^ 2 = t1 at q01 qco t1n pG pV pX
  generalize max (kLow - 2) 0 ^ 2 / r ^ 2 = t2 at q12 pG pV pX
  have T1 : lo.hess * t2 * x1 ^ 2 ≤ a.hess * x2 ^ 2 := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left q12 ph).trans
      (mul_le_mul_of_nonneg_right dh (sq_nonneg _))
  have T2 : lo.curlGrad * t1 * xo ^ 2 ≤ a.curlGrad * xc ^ 2 := by
    rcases le_or_gt 0 lo.curlGrad with hl | hl
    · rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left qco hl).trans
        (mul_le_mul_of_nonneg_right dcg (sq_nonneg _))
    · have : lo.curlGrad * t1 * xo ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hl.le t1n) (sq_nonneg _)
      exact this.trans (mul_nonneg hcg (sq_nonneg _))
  have T3 : lo.curl * xo ^ 2 ≤ a.curl * xo ^ 2 := mul_le_mul_of_nonneg_right dc (sq_nonneg _)
  have T4 : min (lo.curl + lo.curlGrad * t1) 0 * (2 * x1 ^ 2) ≤
      (lo.curl + lo.curlGrad * t1) * xo ^ 2 :=
    (mul_le_mul_of_nonpos_left hoo (min_le_right _ _)).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have T5 : lo.grad * x1 ^ 2 ≤ a.grad * x1 ^ 2 := mul_le_mul_of_nonneg_right dg (sq_nonneg _)
  have T6 : lo.vel * x0 ^ 2 ≤ a.vel * x0 ^ 2 := mul_le_mul_of_nonneg_right dv (sq_nonneg _)
  have T7 : a.cross * (x1 * x0) ≤ lo.cross * (x1 * x0) :=
    mul_le_mul_of_nonneg_right dx (mul_nonneg h1 h0)
  have T8 : s * (t1 * x0 ^ 2) ≤ s * x1 ^ 2 := mul_le_mul_of_nonneg_left q01 ps
  have QF := quadForm_nonneg (x := x1) (y := x0) pG pV pX
  nlinarith [T1, T2, T3, T4, T5, T6, T7, T8, QF]

end TailBand

end CertCell

end Breakdown
