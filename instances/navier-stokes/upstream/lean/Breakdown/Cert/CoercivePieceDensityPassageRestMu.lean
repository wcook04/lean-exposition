import Breakdown.Cert.CoerciveSmoothPieceMuNeg

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageRestMu

open Internal.SmoothPieceEps

theorem muEdge_pointwise (h : HarmonicBounds) (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    {D : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {Bw : ℝ} (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hwB : wt y ≤ Bw) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) *
        (∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
          + 2 * ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr' : (1 + ‖y‖) ≠ 0 := hr.ne'
  have hBw : 0 ≤ Bw := le_trans hw0 hwB
  have p3 : ∀ κ, 0 ≤ gradAmp G κ σ y := fun _ => Real.sqrt_nonneg _
  have p4 : ∀ κ, 0 ≤ velAmp v κ σ y / (1 + ‖y‖) := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  have hM : 0 ≤ 3 * (D / (1 + ‖y‖)) := by positivity
  have hpt : ∀ ι, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖))
        * ∑ α ∈ h.harmonics, (gradAmp G (ι - α) σ y + gradAmp G (ι + α) σ y)) := by
    intro ι
    have E := edgeSum_le_crude h T (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y)
      (fun κ => gradAmp G κ σ y) ι hM p3 fun α _ κ =>
        mul_le_mul_of_nonneg_right (velAmp_le W hD α σ y) (p3 κ)
    have hS : 0 ≤ ∑ α ∈ h.harmonics, (gradAmp G (ι - α) σ y + gradAmp G (ι + α) σ y) :=
      Finset.sum_nonneg fun α _ => add_nonneg (p3 _) (p3 _)
    have hv0 : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_mul (mul_nonneg hBw (by positivity))]
    refine ENNReal.ofReal_le_ofReal ?_
    set S := ∑ α ∈ h.harmonics, (gradAmp G (ι - α) σ y + gradAmp G (ι + α) σ y)
    calc wt y * velAmp v ι σ y * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι
        ≤ wt y * velAmp v ι σ y * (3 * (D / (1 + ‖y‖)) * S) :=
          mul_le_mul_of_nonneg_left E (mul_nonneg hw0 hv0)
      _ = wt y * (3 * D) * ((velAmp v ι σ y / (1 + ‖y‖)) * S) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ Bw * (3 * D) * ((velAmp v ι σ y / (1 + ‖y‖)) * S) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwB (by positivity)) (mul_nonneg (p4 ι) hS)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_edge_le _ (fun κ => velAmp v κ σ y / (1 + ‖y‖))
    (fun κ => gradAmp G κ σ y) p4 p3) zero_le

theorem muBlock_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space))
    (β : Fin nM) {D B4 Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (σ : ℝ) (y : Space) (hw0 : 0 ≤ (m.muP β).wt y) (hw4 : (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ B4)
    (hg1 : PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg) :
    ENNReal.ofReal (-pieceMuBlock m W v G β σ y) ≤
      ENNReal.ofReal (2 * (B4 * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * B4)) *
        (∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hB40 : 0 ≤ B4 := le_trans (mul_nonneg hw0 (sq_nonneg _)) hw4
  have hg0 : 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := norm_nonneg _
  have hBg : 0 ≤ Bg := le_trans (mul_nonneg hg0 hr.le) hg1
  set T := (m.muP β).modes with hT
  set a := (m.muP β).frame with ha
  set wt := (m.muP β).wt y with hwtdef
  set S3 := pieceNorm T (fun κ => gradAmp G κ σ y) with hS3
  set S4 := pieceNorm T (fun κ => velAmp v κ σ y / (1 + ‖y‖)) with hS4
  have hSv : pieceNorm T (fun κ => velAmp v κ σ y) = (1 + ‖y‖) * S4 := by
    rw [hS4, ← pieceNorm_mul T _ hr.le]
    congr 1
    funext κ
    field_simp
  have fss := frameSpeedSup_le W hD a y
  have fss0 := frameSpeedSup_nonneg W a y
  have s3 : 0 ≤ S3 := pieceNorm_nonneg' _ _
  have s4 : 0 ≤ S4 := pieceNorm_nonneg' _ _
  set c := (1 / 2 + 2 * |a|) with hcdef
  have hc : 0 ≤ c := by positivity
  set K0 := B4 * (D + c) + Bg + |a| * B4 with hK0
  have e : -pieceMuBlock m W v G β σ y =
      ((wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)) * S3 * S4
        + (wt * |a| * (1 + ‖y‖) ^ 2) * S4 ^ 2 := by
    unfold pieceMuBlock
    rw [hSv]
    ring
  have k1 : (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖) ≤ B4 * (D + c) + Bg := by
    have h1 : frameSpeedSup W a y * (1 + ‖y‖) ≤ (D + c) * (1 + ‖y‖) ^ 2 := by
      have : D + c * ‖y‖ ≤ (D + c) * (1 + ‖y‖) := by nlinarith [mul_nonneg hD0 (norm_nonneg y)]
      calc frameSpeedSup W a y * (1 + ‖y‖) ≤ (D + c * ‖y‖) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right fss hr.le
        _ ≤ (D + c) * (1 + ‖y‖) * (1 + ‖y‖) := mul_le_mul_of_nonneg_right this hr.le
        _ = (D + c) * (1 + ‖y‖) ^ 2 := by ring
    have h2 : wt * (frameSpeedSup W a y * (1 + ‖y‖)) ≤ B4 * (D + c) := by
      calc wt * (frameSpeedSup W a y * (1 + ‖y‖)) ≤ wt * ((D + c) * (1 + ‖y‖) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hw0
        _ = (wt * (1 + ‖y‖) ^ 2) * (D + c) := by ring
        _ ≤ B4 * (D + c) := mul_le_mul_of_nonneg_right hw4 (by positivity)
    have e2 : (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)
        = wt * (frameSpeedSup W a y * (1 + ‖y‖)) + PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) := by ring
    linarith
  have k2 : wt * |a| * (1 + ‖y‖) ^ 2 ≤ |a| * B4 := by
    calc wt * |a| * (1 + ‖y‖) ^ 2 = |a| * (wt * (1 + ‖y‖) ^ 2) := by ring
      _ ≤ |a| * B4 := mul_le_mul_of_nonneg_left hw4 (abs_nonneg _)
  have c1 : 0 ≤ (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖) :=
    mul_nonneg (add_nonneg (mul_nonneg hw0 fss0) hg0) hr.le
  have c2 : 0 ≤ wt * |a| * (1 + ‖y‖) ^ 2 := by positivity
  have hK0' : K0 = B4 * (D + c) + Bg + |a| * B4 := hK0
  have hm1 : 0 ≤ |a| * B4 := mul_nonneg (abs_nonneg _) hB40
  have hm2 : 0 ≤ B4 * (D + c) := mul_nonneg hB40 (by positivity)
  have hK00 : 0 ≤ K0 := by linarith
  have hb : -pieceMuBlock m W v G β σ y ≤ (2 * K0) * (S3 ^ 2 + S4 ^ 2) := by
    rw [e]
    have hxz : S3 * S4 ≤ S3 ^ 2 + S4 ^ 2 := by nlinarith [sq_nonneg (S3 - S4)]
    have t1 : ((wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)) * S3 * S4
        ≤ K0 * (S3 ^ 2 + S4 ^ 2) := by
      calc ((wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)) * S3 * S4
          = ((wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)) * (S3 * S4) := by ring
        _ ≤ K0 * (S3 ^ 2 + S4 ^ 2) := mul_le_mul (by linarith) hxz (mul_nonneg s3 s4) hK00
    have t2 : (wt * |a| * (1 + ‖y‖) ^ 2) * S4 ^ 2 ≤ K0 * (S3 ^ 2 + S4 ^ 2) :=
      mul_le_mul (by linarith) (by linarith [sq_nonneg S3]) (sq_nonneg _) hK00
    linarith
  refine le_trans (ENNReal.ofReal_le_ofReal hb) ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (sq_nonneg S3) (sq_nonneg S4)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact add_le_add (ofReal_pieceNorm_sq_le T _) (ofReal_pieceNorm_sq_le T _)

end Internal.PieceDensityPassageRestMu

end Coercive

end Breakdown
