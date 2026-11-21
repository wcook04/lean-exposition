import Breakdown.Cert.CoerciveSmoothPieceEpsNeg

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageRestEps

open Internal.SmoothPieceEps

theorem epsRest_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    {Bw : ℝ} (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y) ≤
      ENNReal.ofReal (Bw * (729 * D)) *
        ((h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg W hD
  set M : ℝ := 729 * D with hMdef
  have hM : 0 ≤ M := by positivity
  have hBw : 0 ≤ Bw := le_trans (hwt0 0) (hwtB 0)
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  set a1 : ℤ × ℤ → ℝ := fun κ => vortAmp G κ σ y with ha1
  set a2 : ℤ × ℤ → ℝ := fun κ => vortGradAmp H κ σ y with ha2
  set a3 : ℤ × ℤ → ℝ := fun κ => gradAmp G κ σ y with ha3
  set a4 : ℤ × ℤ → ℝ := fun κ => velAmp v κ σ y / (1 + ‖y‖) with ha4
  have p1 : ∀ κ, 0 ≤ a1 κ := fun _ => Real.sqrt_nonneg _
  have p2 : ∀ κ, 0 ≤ a2 κ := fun _ => Real.sqrt_nonneg _
  have p3 : ∀ κ, 0 ≤ a3 κ := fun _ => Real.sqrt_nonneg _
  have p4 : ∀ κ, 0 ≤ a4 κ := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  have S : ∀ (g : ℤ × ℤ → ℝ), (∀ κ, 0 ≤ g κ) → ∀ ι, 0 ≤ ∑ α ∈ h.harmonics, (g (ι - α) + g (ι + α)) :=
    fun g hg ι => Finset.sum_nonneg fun α _ => add_nonneg (hg _) (hg _)
  have E1 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
      ≤ M * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p2 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (velAmp_le W hD α σ y) (by have := div_le_self hD0 (by linarith [norm_nonneg y] : (1 : ℝ) ≤ 1 + ‖y‖); rw [hMdef]; linarith)) (p2 κ)
  have E2 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
      ≤ M * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p1 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (gradAmp_le W hD α σ y) (by have := decay_le_self W hD y 2; rw [hMdef]; linarith)) (p1 κ)
  have E3 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y)
      (fun κ => velAmp v κ σ y) ι ≤ M * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)) := fun ι => by
    refine edgeSum_le_crude h _ _ _ _ ι hM p4 fun α _ κ => ?_
    have hu : 0 ≤ velAmp v κ σ y := Real.sqrt_nonneg _
    have h3 : D / (1 + ‖y‖) ^ 3 ≤ D / (1 + ‖y‖) :=
      div_le_div_of_nonneg_left hD0 hr (le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num))
    calc vortGradAmp (secondDerivField W) α σ y * velAmp v κ σ y
        ≤ (27 * (27 * (D / (1 + ‖y‖) ^ 3))) * velAmp v κ σ y :=
          mul_le_mul_of_nonneg_right (vortGradAmp_le W hD α σ y) hu
      _ ≤ (729 * (D / (1 + ‖y‖))) * velAmp v κ σ y := by nlinarith
      _ = M * a4 κ := by rw [hMdef, ha4]; field_simp
  have E4 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι
      ≤ M * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p3 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (vortAmp_le W hD α σ y) (by have := decay_le_self W hD y 2; rw [hMdef]; linarith)) (p3 κ)
  have hpt : ∀ ι, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)))) := by
    intro ι
    have e : -pieceEpsRestMode m h W v G H β ι σ y =
        (m.epsP β).wt y * a1 ι * (edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
          + edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
          + edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι
          + edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι) := by
      unfold pieceEpsRestMode; ring
    rw [e]
    exact rest_term_le (hwt0 y) (hwtB y) (p1 ι) hM (E1 ι) (E2 ι) (E3 ι) (E4 ι)
      (S a2 p2 ι) (S a1 p1 ι) (S a4 p4 ι) (S a3 p3 ι)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left, show Bw * (729 * D) = Bw * M from rfl]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  exact add_le_add (add_le_add (add_le_add (tsum_edge_le _ a1 a2 p1 p2) (tsum_edge_le _ a1 a1 p1 p1))
    (tsum_edge_le _ a1 a4 p1 p4)) (tsum_edge_le _ a1 a3 p1 p3)

theorem epsBlock_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) {D Bw Bd Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (hdec : ∀ y, ‖y‖ * (m.epsP β).wt y ≤ Bd) (hgrad : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ Bg)
    (σ : ℝ) (y : Space) :
    ENNReal.ofReal (-pieceEpsBlock m W v G H β σ y) ≤
      ENNReal.ofReal (4 * (Bw * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + Bg + Bw * (27 * D + |(m.epsP β).frame|)
          + 27 * Bw * D)) *
        (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hw := hwt0 y
  have hwB := hwtB y
  have hBw : 0 ≤ Bw := le_trans hw hwB
  have hBd : 0 ≤ Bd := le_trans (mul_nonneg (norm_nonneg y) hw) (hdec y)
  have hg0 : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  have hBg : 0 ≤ Bg := le_trans hg0 (hgrad y)
  set T := (m.epsP β).modes with hT
  set a := (m.epsP β).frame with ha
  set wt := (m.epsP β).wt y with hwtdef
  set S1 := pieceNorm T (fun κ => vortAmp G κ σ y) with hS1
  set S2 := pieceNorm T (fun κ => vortGradAmp H κ σ y) with hS2
  set S3 := pieceNorm T (fun κ => gradAmp G κ σ y) with hS3
  set S4 := pieceNorm T (fun κ => velAmp v κ σ y / (1 + ‖y‖)) with hS4
  have hSv : pieceNorm T (fun κ => velAmp v κ σ y) = (1 + ‖y‖) * S4 := by
    rw [hS4, ← pieceNorm_mul T _ hr.le]
    congr 1
    funext κ
    field_simp
  have fss := frameSpeedSup_le W hD a y
  have vs := vortSup_le W hD y
  have vgs := vortGradSup_le W hD hW y
  have fss0 := frameSpeedSup_nonneg W a y
  have vs0 := vortSup_nonneg W y
  have vgs0 := vortGradSup_nonneg W y
  set K0 := Bw * D + (1 / 2 + 2 * |a|) * Bd + Bg + Bw * (27 * D + |a|) + 27 * Bw * D with hK0
  have d2 : D / (1 + ‖y‖) ^ 2 ≤ D := decay_le_self W hD y 2
  have d3 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0), mul_le_mul_of_nonneg_left
      (le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0)) hD0]
  have e : -pieceEpsBlock m W v G H β σ y =
      (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y) * S2 * S1
        + wt * ((1 / 2) * vortSup W y + |a|) * S1 ^ 2
        + (wt * vortGradSup W y * (1 + ‖y‖)) * S4 * S1 + wt * vortSup W y * S3 * S1 := by
    unfold pieceEpsBlock
    rw [hSv]
    ring
  have k1 : wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y ≤ K0 := by
    have := hdec y
    have hA : 0 ≤ 1 / 2 + 2 * |a| := by positivity
    have : wt * frameSpeedSup W a y ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := by
      calc wt * frameSpeedSup W a y ≤ wt * (D + (1 / 2 + 2 * |a|) * ‖y‖) := mul_le_mul_of_nonneg_left fss hw
        _ = wt * D + (1 / 2 + 2 * |a|) * (‖y‖ * wt) := by ring
        _ ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := add_le_add (mul_le_mul_of_nonneg_right hwB hD0)
            (mul_le_mul_of_nonneg_left (hdec y) hA)
    have := hgrad y
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    have : 0 ≤ 27 * Bw * D := by positivity
    rw [hK0]; linarith
  have k2 : wt * ((1 / 2) * vortSup W y + |a|) ≤ K0 := by
    have h27 : (1 / 2) * vortSup W y + |a| ≤ 27 * D + |a| := by nlinarith
    have : wt * ((1 / 2) * vortSup W y + |a|) ≤ Bw * (27 * D + |a|) :=
      mul_le_mul hwB h27 (by positivity) hBw
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ 27 * Bw * D := by positivity
    rw [hK0]; linarith
  have k3 : wt * vortGradSup W y * (1 + ‖y‖) ≤ K0 := by
    have h1 : vortGradSup W y * (1 + ‖y‖) ≤ 27 * D := by
      calc vortGradSup W y * (1 + ‖y‖) ≤ 27 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right vgs hr.le
        _ = 27 * (D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖)) := by ring
        _ ≤ 27 * D := by linarith
    have : wt * vortGradSup W y * (1 + ‖y‖) ≤ 27 * Bw * D := by
      calc wt * vortGradSup W y * (1 + ‖y‖) = wt * (vortGradSup W y * (1 + ‖y‖)) := by ring
        _ ≤ Bw * (27 * D) := mul_le_mul hwB h1 (by positivity) hBw
        _ = 27 * Bw * D := by ring
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    rw [hK0]; linarith
  have k4 : wt * vortSup W y ≤ K0 := by
    have h1 : vortSup W y ≤ 27 * D := by nlinarith
    have : wt * vortSup W y ≤ 27 * Bw * D := by
      calc wt * vortSup W y ≤ Bw * (27 * D) := mul_le_mul hwB h1 vs0 hBw
        _ = 27 * Bw * D := by ring
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    rw [hK0]; linarith
  have c1 : 0 ≤ wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y :=
    add_nonneg (mul_nonneg hw fss0) hg0
  have c2 : 0 ≤ wt * ((1 / 2) * vortSup W y + |a|) := mul_nonneg hw (by positivity)
  have c3 : 0 ≤ wt * vortGradSup W y * (1 + ‖y‖) := by positivity
  have c4 : 0 ≤ wt * vortSup W y := mul_nonneg hw vs0
  have hb := block_real c1 c2 c3 c4 k1 k2 k3 k4 (show 0 ≤ S1 from pieceNorm_nonneg' _ _)
    (show 0 ≤ S2 from pieceNorm_nonneg' _ _) (show 0 ≤ S3 from pieceNorm_nonneg' _ _)
    (show 0 ≤ S4 from pieceNorm_nonneg' _ _)
  rw [e]
  refine le_trans (ENNReal.ofReal_le_ofReal hb) ?_
  have hK00 : 0 ≤ K0 := le_trans c4 k4
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK00),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3)) (sq_nonneg S4),
    ENNReal.ofReal_add (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3),
    ENNReal.ofReal_add (sq_nonneg S1) (sq_nonneg S2)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact add_le_add (add_le_add (add_le_add (ofReal_pieceNorm_sq_le T _) (ofReal_pieceNorm_sq_le T _))
    (ofReal_pieceNorm_sq_le T _)) (ofReal_pieceNorm_sq_le T _)

end Internal.PieceDensityPassageRestEps

end Coercive

end Breakdown
