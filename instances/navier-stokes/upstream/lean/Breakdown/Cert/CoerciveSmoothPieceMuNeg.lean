import Breakdown.Cert.CoerciveSmoothPieceEpsSeries

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuNeg

open Internal.SmoothPieceEps

theorem ind_le_one (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ind_nonneg_of (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

open Classical in
theorem edgeSum_nonneg_of (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ)
    (hX : ∀ β, 0 ≤ X β) (hg : ∀ κ, 0 ≤ g κ) (ι : ℤ × ℤ) : 0 ≤ edgeSum h T X g ι := by
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg (hX β) (hg _)]
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg (hX β) (hg _)]
  · exact le_rfl

theorem tsum_shift_sum (s : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) :
    ∑' ι, ∑ α ∈ s, ENNReal.ofReal (g (ι - α) ^ 2) = (s.card : ℝ≥0∞) * ∑' ι, ENNReal.ofReal (g ι ^ 2) := by
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e : ∀ α ∈ s, ∑' ι, ENNReal.ofReal (g (ι - α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) := fun α _ =>
    (Equiv.subRight α).tsum_eq (fun ι => ENNReal.ofReal (g ι ^ 2))
  rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]

section Pointwise

variable (h : HarmonicBounds) (W v : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem edge_pointwise (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {Bw : ℝ} (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hwB : wt y ≤ Bw) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) *
        (∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
          + 2 * ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr' : (1 + ‖y‖) ≠ 0 := hr.ne'
  have hBw : 0 ≤ Bw := le_trans hw0 hwB
  have p3 : ∀ κ, 0 ≤ gradAmp (gradField v) κ σ y := fun _ => Real.sqrt_nonneg _
  have p4 : ∀ κ, 0 ≤ velAmp v κ σ y / (1 + ‖y‖) := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  have hM : 0 ≤ 3 * (D / (1 + ‖y‖)) := by positivity
  have hpt : ∀ ι, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖))
        * ∑ α ∈ h.harmonics, (gradAmp (gradField v) (ι - α) σ y + gradAmp (gradField v) (ι + α) σ y)) := by
    intro ι
    have E := edgeSum_le_crude h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y)
      (fun κ => gradAmp (gradField v) κ σ y) ι hM p3 fun α _ κ =>
        mul_le_mul_of_nonneg_right (velAmp_le W hD α σ y) (p3 κ)
    have hS : 0 ≤ ∑ α ∈ h.harmonics, (gradAmp (gradField v) (ι - α) σ y + gradAmp (gradField v) (ι + α) σ y) :=
      Finset.sum_nonneg fun α _ => add_nonneg (p3 _) (p3 _)
    have hv0 : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_mul (mul_nonneg hBw (by positivity))]
    refine ENNReal.ofReal_le_ofReal ?_
    set S := ∑ α ∈ h.harmonics, (gradAmp (gradField v) (ι - α) σ y + gradAmp (gradField v) (ι + α) σ y)
    calc wt y * velAmp v ι σ y * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι
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
    (fun κ => gradAmp (gradField v) κ σ y) p4 p3) zero_le

theorem press_pointwise (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {η B4 : ℝ} (hη : 0 < η) (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hw4 : wt y * (1 + ‖y‖) ^ 2 ≤ B4) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * η)
          + (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤
      ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * η))
          * ((h.harmonics.card : ℝ≥0∞) * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
        + ENNReal.ofReal ((1 / 2) * η * B4 ^ 2) * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr' : (1 + ‖y‖) ≠ 0 := hr.ne'
  have hr1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hu : ∀ κ, velAmp v κ σ y = (1 + ‖y‖) * (velAmp v κ σ y / (1 + ‖y‖)) := fun κ =>
    (mul_div_cancel₀ _ hr').symm
  set a4 : ℤ × ℤ → ℝ := fun κ => velAmp v κ σ y / (1 + ‖y‖) with ha4
  have p4 : ∀ κ, 0 ≤ a4 κ := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  set c1 : ℝ := (h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * η) with hc1
  set c2 : ℝ := (1 / 2) * η * B4 ^ 2 with hc2
  have hc10 : 0 ≤ c1 := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))
    (by linarith)
  have hB40 : 0 ≤ B4 := le_trans (mul_nonneg hw0 (sq_nonneg _)) hw4
  have hc20 : 0 ≤ c2 := mul_nonneg (mul_nonneg (by norm_num) hη.le) (sq_nonneg _)
  have hgu : ∀ α κ, gradAmp (gradField W) α σ y * velAmp v κ σ y ≤ 9 * D * a4 κ := by
    intro α κ
    have h1 := gradAmp_le W hD α σ y
    have hq : D / (1 + ‖y‖) ^ 2 * (1 + ‖y‖) ≤ D := by
      rw [div_mul_eq_mul_div, pow_two, mul_div_mul_right _ _ hr']
      exact div_le_self hD0 hr1
    calc gradAmp (gradField W) α σ y * velAmp v κ σ y
        ≤ 9 * (D / (1 + ‖y‖) ^ 2) * velAmp v κ σ y := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = 9 * (D / (1 + ‖y‖) ^ 2 * (1 + ‖y‖)) * a4 κ := by rw [hu κ]; ring
      _ ≤ 9 * D * a4 κ := mul_le_mul_of_nonneg_right (by linarith) (p4 κ)
  have hpt : ∀ ι, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * η)
          + (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤
      ENNReal.ofReal c1 * ∑ α ∈ h.harmonics, ENNReal.ofReal (a4 (ι - α) ^ 2) + ENNReal.ofReal c2 * ENNReal.ofReal (a4 ι ^ 2) := by
    intro ι
    set S := ∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y
    have hS2 : S ^ 2 ≤ (h.harmonics.card : ℝ) * ∑ α ∈ h.harmonics, (81 * D ^ 2) * a4 (ι - α) ^ 2 := by
      refine le_trans (sq_sum_le_card_mul_sum_sq) (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun α _ => ?_) (Nat.cast_nonneg _))
      have hx0 : 0 ≤ gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hx := hgu α (ι - α)
      have := mul_le_mul hx hx hx0 (le_trans hx0 hx)
      nlinarith
    have hP1 : S ^ 2 / (2 * η) ≤ c1 * ∑ α ∈ h.harmonics, a4 (ι - α) ^ 2 := by
      have e : c1 * ∑ α ∈ h.harmonics, a4 (ι - α) ^ 2
          = ((h.harmonics.card : ℝ) * ∑ α ∈ h.harmonics, (81 * D ^ 2) * a4 (ι - α) ^ 2) / (2 * η) := by
        rw [hc1, ← Finset.mul_sum]
        ring
      rw [e]
      gcongr
    have hwr : wt y * (1 + ‖y‖) ≤ B4 := by
      have : wt y * (1 + ‖y‖) ≤ wt y * (1 + ‖y‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hw0
        nlinarith
      linarith
    have hwr0 : 0 ≤ wt y * (1 + ‖y‖) := mul_nonneg hw0 hr.le
    have hP2 : (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2 ≤ c2 * a4 ι ^ 2 := by
      rw [hu ι, hc2]
      have hsq : (wt y * (1 + ‖y‖)) ^ 2 ≤ B4 ^ 2 := by nlinarith
      have e : (1 / 2) * η * wt y ^ 2 * ((1 + ‖y‖) * a4 ι) ^ 2 = (1 / 2) * η * (wt y * (1 + ‖y‖)) ^ 2 * a4 ι ^ 2 := by
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    have hb0 : 0 ≤ S ^ 2 / (2 * η) + (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2 := by positivity
    have hle : ModeWeights.ind (PieceWeights.inPiece T ι)
        * (S ^ 2 / (2 * η) + (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2)
        ≤ c1 * ∑ α ∈ h.harmonics, a4 (ι - α) ^ 2 + c2 * a4 ι ^ 2 := by
      have := mul_le_of_le_one_left hb0 (ind_le_one (PieceWeights.inPiece T ι))
      linarith
    refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
    rw [ENNReal.ofReal_add (mul_nonneg hc10 (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg hc20 (sq_nonneg _)), ENNReal.ofReal_mul hc10, ENNReal.ofReal_mul hc20,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, tsum_shift_sum]

end Pointwise

theorem block_pointwise_mu {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (β : Fin nM) {D B4 Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (σ : ℝ) (y : Space) (hw0 : 0 ≤ (m.muP β).wt y) (hw4 : (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ B4)
    (hg1 : PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg) :
    ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y) ≤
      ENNReal.ofReal (2 * (B4 * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * B4)) *
        (∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
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
  set S3 := pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) with hS3
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
  have e : -pieceMuBlock m W v (gradField v) β σ y =
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
  have hb : -pieceMuBlock m W v (gradField v) β σ y ≤ (2 * K0) * (S3 ^ 2 + S4 ^ 2) := by
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

theorem weight_facts {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nM) :
    ∃ B Bg : ℝ, ∀ y, 0 ≤ (m.muP β).wt y ∧ (m.muP β).wt y ≤ B ∧ (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ 4 * B
      ∧ PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  obtain ⟨K, hK⟩ := hm.mu_increment β
  refine ⟨B, (K : ℝ) + B, fun y => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hB β y
  have h0 := hm.mu_wt_nonneg β y
  have hg : PieceWeights.wtGrad (m.muP β).wt y ≤ K := by
    unfold PieceWeights.wtGrad
    exact norm_fderiv_le_of_lipschitz ℝ hK
  refine ⟨h0, h1, ?_, ?_⟩
  · nlinarith [mul_nonneg (sq_nonneg (‖y‖ - 1)) h0]
  · have e : PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖)
        = PieceWeights.wtGrad (m.muP β).wt y + ‖y‖ * PieceWeights.wtGrad (m.muP β).wt y := by ring
    linarith

theorem pressure_nonneg {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) (W v : ℝ → Space → Space)
    (β : Fin nM) (hη : 0 < (m.muP β).eta) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2) :=
  mul_nonneg (ind_nonneg_of _) (add_nonneg (div_nonneg (sq_nonneg _) (by linarith))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη.le) (sq_nonneg _)) (sq_nonneg _)))

theorem negPart_finite {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (_hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (_hWp : IsTimePeriodic W)
    (_hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (_hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds) (_hDer : ModeDerivativeHolds) (_hRotM : ModeRotationHolds)
    (_hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (_hSsp : WeightedSumSecondPartialsPairingHolds) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι σ y))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y))) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨B, Bg, hw⟩ := weight_facts m P h w W hm β
  have hη := hm.mu_eta_pos β
  set K : ℝ≥0∞ := ENNReal.ofReal (B * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) * 3)
    + ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * (h.harmonics.card : ℝ≥0∞)
    + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * B) ^ 2)
    + 2 * ENNReal.ofReal (2 * (4 * B * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * (4 * B)))
    with hK
  have hKt : K ≠ ⊤ := by
    rw [hK]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ENNReal.ofReal_ne_top⟩, ?_⟩
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
    · exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hpt : ∀ σ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι σ y))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)) ≤
      K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
    intro σ y
    obtain ⟨h0, h1, h4, hg⟩ := hw y
    have hE := edge_pointwise h W v hD (m.muP β).modes (m.muP β).wt σ y h0 h1
    have hP := press_pointwise h W v hD (m.muP β).modes (m.muP β).wt hη σ y h0 h4
    have hB := block_pointwise_mu m W v β hD σ y h0 h4 hg
    have hsplit : ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι σ y)
        = (∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
          * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι))
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
            + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)) := by
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun ι => ?_
      have hE0 : 0 ≤ (m.muP β).wt y * velAmp v ι σ y
          * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι :=
        mul_nonneg (mul_nonneg (hm.mu_wt_nonneg β y) (Real.sqrt_nonneg _))
          (edgeSum_nonneg_of _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) ι)
      rw [← ENNReal.ofReal_add hE0 (pressure_nonneg m h W v β hη ι σ y)]
      congr 1
      unfold pieceMuRestMode
      ring
    rw [hsplit]
    set A1 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
    set A2 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
    set A3 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
    set A4 := ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
    have l3 : A3 ≤ A1 + A2 + A3 + A4 := le_trans le_add_self le_self_add
    have l4 : A4 ≤ A1 + A2 + A3 + A4 := le_add_self
    set A := A1 + A2 + A3 + A4 with hA
    calc _ ≤ ENNReal.ofReal (B * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A4 + 2 * A3))
          + (ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta))
              * ((h.harmonics.card : ℝ≥0∞) * A4) + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * B) ^ 2) * A4)
          + ENNReal.ofReal (2 * (4 * B * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * (4 * B)))
            * (A3 + A4) := add_le_add (add_le_add hE hP) hB
      _ ≤ ENNReal.ofReal (B * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A + 2 * A))
          + (ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta))
              * ((h.harmonics.card : ℝ≥0∞) * A) + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * B) ^ 2) * A)
          + ENNReal.ofReal (2 * (4 * B * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * (4 * B)))
            * (A + A) := by gcongr
      _ = K * A := by rw [hK]; ring
  calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = K * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))) := by
        simp_rw [lintegral_const_mul' K _ hKt]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) (amplitudeSeries_finite hPars hSP P v hv)

theorem pressureLoss_finite {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (_hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (_hWp : IsTimePeriodic W)
    (_hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (_hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds) (_hDer : ModeDerivativeHolds) (_hRotM : ModeRotationHolds)
    (_hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (_hSsp : WeightedSumSecondPartialsPairingHolds) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨B, Bg, hw⟩ := weight_facts m P h w W hm β
  have hη := hm.mu_eta_pos β
  set K : ℝ≥0∞ := ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * (h.harmonics.card : ℝ≥0∞)
    + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * B) ^ 2) with hK
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
      ENNReal.ofReal_ne_top⟩
  have hpt : ∀ σ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤
      K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
    intro σ y
    obtain ⟨h0, h1, h4, hg⟩ := hw y
    have hP := press_pointwise h W v hD (m.muP β).modes (m.muP β).wt hη σ y h0 h4
    set A1 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
    set A2 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
    set A3 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
    set A4 := ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
    have l4 : A4 ≤ A1 + A2 + A3 + A4 := le_add_self
    set A := A1 + A2 + A3 + A4 with hA
    calc _ ≤ _ := hP
      _ ≤ ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta))
              * ((h.harmonics.card : ℝ≥0∞) * A) + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * B) ^ 2) * A := by
          gcongr
      _ = K * A := by rw [hK]; ring
  calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = K * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))) := by
        simp_rw [lintegral_const_mul' K _ hKt]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) (amplitudeSeries_finite hPars hSP P v hv)

end Internal.SmoothPieceMuNeg

end Coercive

end Breakdown
