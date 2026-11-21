import Breakdown.Cert.CoerciveSmoothPieceEpsRestDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore

theorem ind_nonneg (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : 0 ≤ ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold ModeWeights.ind; split_ifs <;> norm_num

theorem ind_le_one (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : ModeWeights.ind (PieceWeights.inPiece T ι) ≤ 1 := by
  unfold ModeWeights.ind; split_ifs <;> norm_num

theorem term_abs_le (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (u : Fin 3 → ℂ) (hwt : 0 ≤ wt y) :
    |(Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) u).re|
      ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * wt y * vortAmp (gradField v) ι σ y
        * Real.sqrt (cnormSq u) := by
  refine (Internal.FieldModes.abs_re_I_mul_le _ _).trans ?_
  rw [abs_mul, abs_sgn_eq, abs_of_nonneg hwt, mul_assoc _ (vortAmp _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (Internal.Field.norm_cdot_le_sqrt _ _)
    (mul_nonneg (ind_nonneg T ι) hwt)

theorem assemble (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (v Z : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (c : ℤ × ℤ → Fin 3 → ℂ) (E : ℤ × ℤ → ℝ) (K : ℝ) (hwt : 0 ≤ wt y) (hE0 : ∀ ι, 0 ≤ E ι)
    (hE : ∀ ι, PieceWeights.inPiece T ι → Real.sqrt (cnormSq (modeVel ι Z σ y - c ι)) ≤ E ι)
    (hEs : Summable (fun ι => wt y * vortAmp (gradField v) ι σ y * E ι))
    (hcs : Summable (fun ι =>
      (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) (c ι)).re))
    (hcK : |∑' ι, (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) (c ι)).re|
      ≤ K) :
    Summable (fun ι => restPart T wt v Z ι σ y) ∧
      -(∑' ι, restPart T wt v Z ι σ y) ≤ (∑' ι, wt y * vortAmp (gradField v) ι σ y * E ι) + K ∧
      (∑' ι, restPart T wt v Z ι σ y) ≤ (∑' ι, wt y * vortAmp (gradField v) ι σ y * E ι) + K := by
  set p : ℤ × ℤ → ℝ := fun ι =>
    (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) (c ι)).re
  set d : ℤ × ℤ → ℝ := fun ι =>
    (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) (modeVel ι Z σ y - c ι)).re
  have hsplit : ∀ ι, restPart T wt v Z ι σ y = p ι + d ι := by
    intro ι
    simp only [restPart, p, d, cdot_sub, mul_sub, Complex.sub_re]
    ring
  have hd : ∀ ι, |d ι| ≤ wt y * vortAmp (gradField v) ι σ y * E ι := by
    intro ι
    refine (term_abs_le T wt v ι σ y _ hwt).trans ?_
    have ha : 0 ≤ vortAmp (gradField v) ι σ y := Real.sqrt_nonneg _
    by_cases hi : PieceWeights.inPiece T ι
    · have h1 : ModeWeights.ind (PieceWeights.inPiece T ι) = 1 := by
        unfold ModeWeights.ind; rw [if_pos hi]
      rw [h1, one_mul]
      exact mul_le_mul_of_nonneg_left (hE ι hi) (mul_nonneg hwt ha)
    · have h0 : ModeWeights.ind (PieceWeights.inPiece T ι) = 0 := by
        unfold ModeWeights.ind; rw [if_neg hi]
      rw [h0, zero_mul, zero_mul, zero_mul]
      exact mul_nonneg (mul_nonneg hwt ha) (hE0 ι)
  have hds : Summable d := (hEs.of_nonneg_of_le (fun ι => abs_nonneg _) hd).of_abs
  have hrs : Summable (fun ι => restPart T wt v Z ι σ y) := by
    have e : (fun ι => restPart T wt v Z ι σ y) = fun ι => p ι + d ι := funext hsplit
    rw [e]
    exact hcs.add hds
  have hsum : ∑' ι, restPart T wt v Z ι σ y = (∑' ι, p ι) + ∑' ι, d ι := by
    rw [tsum_congr hsplit, hcs.tsum_add hds]
  have hdab : |∑' ι, d ι| ≤ ∑' ι, wt y * vortAmp (gradField v) ι σ y * E ι := by
    have h1 : ‖∑' ι, d ι‖ ≤ ∑' ι, ‖d ι‖ := norm_tsum_le_tsum_norm hds.norm
    simp only [Real.norm_eq_abs] at h1
    exact h1.trans (hds.abs.tsum_le_tsum hd hEs)
  have hpK : |∑' ι, p ι| ≤ K := hcK
  refine ⟨hrs, ?_, ?_⟩
  · rw [hsum]
    linarith [neg_abs_le (∑' ι, p ι), neg_abs_le (∑' ι, d ι)]
  · rw [hsum]
    linarith [le_abs_self (∑' ι, p ι), le_abs_self (∑' ι, d ι)]

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown
