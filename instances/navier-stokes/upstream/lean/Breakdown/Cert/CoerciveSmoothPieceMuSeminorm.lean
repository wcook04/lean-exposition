import Breakdown.Cert.CoerciveFrequencySeminorm

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuSeminorm

theorem sgn_abs_le_one (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : |PieceWeights.sgn T ι| ≤ 1 := by
  unfold PieceWeights.sgn
  split_ifs <;> norm_num

theorem frameFreq_abs_le {P : ℝ} (hP : 0 < P) (a : ℝ) (ι : ℤ × ℤ) :
    |PieceWeights.frameFreq P a ι| ≤ (2 * Real.pi / P + |a|) * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) := by
  unfold PieceWeights.frameFreq
  have h1 : |2 * Real.pi * (ι.1 : ℝ) / P| = 2 * Real.pi / P * |(ι.1 : ℝ)| := by
    rw [show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Real.pi / P)]
  have h2 : |a * (ι.2 : ℝ)| = |a| * |(ι.2 : ℝ)| := abs_mul _ _
  have hp : 0 ≤ 2 * Real.pi / P := by positivity
  have e1 := abs_nonneg (ι.1 : ℝ)
  have e2 := abs_nonneg (ι.2 : ℝ)
  have e3 := abs_nonneg a
  refine (abs_add_le _ _).trans ?_
  rw [h1, h2]
  nlinarith [mul_nonneg hp e2, mul_nonneg e3 e1]

theorem seminorm_finite {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds)
    (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    pieceSeminormPart m P β v < ⊤ := by
  have hp := hSP P v hv
  have hP0 : 0 < P := hm.period_pos
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hwt0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  obtain ⟨K, hK⟩ := hm.mu_increment β
  have key := FrequencySeminorm.Internal.weightedFrequency_lt_top hPars hDer hRotM hp hP0 (m.muP β).wt hwt0
    hK.continuous ⟨B, fun y => ⟨(hB β y).1, (hB β y).2.1⟩⟩
  set c : ℝ := 2 * Real.pi / P + |(m.muP β).frame| with hc
  have hc0 : 0 ≤ c := add_nonneg (by positivity) (abs_nonneg _)
  have hpt : ∀ ι σ y, ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι|
      * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y * cnormSq (modeVel ι v σ y))
      ≤ ENNReal.ofReal c * ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y
        * cnormSq (modeVel ι v σ y)) := by
    intro ι σ y
    rw [← ENNReal.ofReal_mul hc0]
    apply ENNReal.ofReal_le_ofReal
    have hs := sgn_abs_le_one (m.muP β).modes ι
    have hf := frameFreq_abs_le hP0 (m.muP β).frame ι
    have hx : 0 ≤ (m.muP β).wt y * cnormSq (modeVel ι v σ y) :=
      mul_nonneg (hwt0 y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hsf : |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
        ≤ c * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) :=
      (mul_le_of_le_one_left (abs_nonneg _) hs).trans hf
    calc |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
          * (m.muP β).wt y * cnormSq (modeVel ι v σ y)
        = (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|)
          * ((m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by ring
      _ ≤ (c * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|)) * ((m.muP β).wt y * cnormSq (modeVel ι v σ y)) :=
          mul_le_mul_of_nonneg_right hsf hx
      _ = c * ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by ring
  unfold pieceSeminormPart
  calc _ ≤ ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal c
        * ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) :=
        ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => hpt ι σ y
    _ = ENNReal.ofReal c * ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ι => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun σ => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top key

end Internal.SmoothPieceMuSeminorm

end Coercive

end Breakdown
