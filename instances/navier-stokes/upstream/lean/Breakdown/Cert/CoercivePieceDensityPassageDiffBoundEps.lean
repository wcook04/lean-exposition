import Breakdown.Cert.CoercivePieceDensityPassageDiffBoundMu

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PiecePassageDiffBoundEps

open DensityPassageRestBound PiecePassageDiffBoundMu

theorem coeff_le_of {p e M : ℝ} (hp : 0 ≤ p) (hpM : p ≤ M) (he0 : 0 ≤ e) (he1 : e ≤ 1) : |p * e| ≤ M := by
  rw [abs_of_nonneg (mul_nonneg hp he0)]
  nlinarith

open Classical in
theorem edgeSum_scale (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ) {c : ℝ}
    (hc : c ≠ 0) : edgeSum h T X g ι = edgeSum h T (fun α => X α * c) (fun κ => g κ / c) ι := by
  unfold edgeSum
  split_ifs
  · refine Finset.sum_congr rfl fun β _ => ?_
    split_ifs
    · rfl
    · field_simp
  · refine Finset.sum_congr rfl fun β _ => ?_
    split_ifs
    · rfl
    · field_simp
  · rfl

theorem edge_bound {A Bm : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    (hA : IsAmp A) (hB : IsAmp Bm) (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X : ℤ × ℤ → ℝ → Space → ℝ)
    (k : ℝ → Space → ℝ) {M : ℝ} (hM : 0 ≤ M) (hk : ∀ σ y, 0 ≤ k σ y) (hX : ∀ α σ y, 0 ≤ X α σ y)
    (hkX : ∀ α σ y, k σ y * X α σ y ≤ M) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => k σ y * A v G H ι σ y
      * edgeSum h T (fun α => X α σ y) (fun κ => Bm v G H κ σ y) ι) v G H := by
  classical
  have h1 : IsRestBound (fun v G H ι σ y => ∑ α ∈ h.harmonics,
      ((k σ y * X α σ y * (if ι ∉ T then 0 else if ι - α ∈ T then 0 else 1))
          * (A v G H (ι - 0) σ y * Bm v G H (ι - α) σ y)
        + (k σ y * X α σ y * (if ι ∈ T then 0 else if -ι ∈ T then (if -ι - α ∈ T then 0 else 1) else 0))
          * (A v G H (ι - 0) σ y * Bm v G H (ι - -α) σ y))) v G H := by
    refine isRestBound_finsetSum _ fun α _ => IsRestBound.add ?_ ?_
    · refine isRestBound_prod hA hB _ hM (fun ι σ y => ?_) 0 α v G H
      exact coeff_le_of (mul_nonneg (hk σ y) (hX α σ y)) (hkX α σ y) (by split_ifs <;> norm_num)
        (by split_ifs <;> norm_num)
    · refine isRestBound_prod hA hB _ hM (fun ι σ y => ?_) 0 (-α) v G H
      exact coeff_le_of (mul_nonneg (hk σ y) (hX α σ y)) (hkX α σ y) (by split_ifs <;> norm_num)
        (by split_ifs <;> norm_num)
  refine isRestBound_congr h1 fun v' G' H' ι σ y => ?_
  simp only [sub_zero]
  rw [mul_edgeSum_eq]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}

theorem epsRest_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => pieceEpsRestMode m h W v G H β ι σ y) v G H := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 : 0 ≤ D := by
    have h0 := hD 0 0 0 (by norm_num)
    rw [norm_zero, add_zero, zero_add, pow_one, div_one] at h0
    exact (norm_nonneg _).trans h0
  have hy1 : ∀ y : Space, 1 ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  have hw0 : ∀ y, 0 ≤ (m.epsP β).wt y := fun y => hm.eps_wt_nonneg β y
  have hwE : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    (Finset.single_le_sum (f := fun b => (m.epsP β).wt y |> fun _ => (m.epsP b).wt y)
      (fun b _ => hm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  have hE0 : 0 ≤ epsSup := (hw0 0).trans (hwE 0)
  have hle : ∀ (y : Space) (j : ℕ), D / (1 + ‖y‖) ^ j ≤ D := fun y j =>
    div_le_self hD0 (one_le_pow₀ (hy1 y))
  have hA := isAmp_vort
  have b1 := edge_bound hA isAmp_vortGrad h (m.epsP β).modes (fun α σ y => velAmp W α σ y)
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (3 * D)) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => Real.sqrt_nonneg _)
    (fun α σ y => mul_le_mul (hwE y) ((SmoothPieceEps.velAmp_le W hD α σ y).trans (by
      have := hle y 1; rw [pow_one] at this; linarith)) (Real.sqrt_nonneg _) hE0) v G H
  have b2 := edge_bound hA hA h (m.epsP β).modes (fun α σ y => gradAmp (gradField W) α σ y)
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (9 * D)) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => Real.sqrt_nonneg _)
    (fun α σ y => mul_le_mul (hwE y) ((SmoothPieceEps.gradAmp_le W hD α σ y).trans (by
      have := hle y 2; linarith)) (Real.sqrt_nonneg _) hE0) v G H
  have b3 := edge_bound hA isAmp_vel h (m.epsP β).modes
    (fun α σ y => vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖))
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (27 * (27 * D))) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    (fun α σ y => by
      have h1 := SmoothPieceEps.vortGradAmp_le W hD α σ y
      have hp : 0 < 1 + ‖y‖ := by positivity
      have h2 : vortGradAmp (secondDerivField W) α σ y * (1 + ‖y‖) ≤ 27 * (27 * D) := by
        have e : 27 * (27 * (D / (1 + ‖y‖) ^ 3)) * (1 + ‖y‖) = 27 * (27 * (D / (1 + ‖y‖) ^ 2)) := by
          field_simp
        have := hle y 2
        nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
      exact mul_le_mul (hwE y) h2 (mul_nonneg (Real.sqrt_nonneg _) hp.le) hE0) v G H
  have b4 := edge_bound hA isAmp_grad h (m.epsP β).modes (fun α σ y => vortAmp (gradField W) α σ y)
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (16 * (9 * D))) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => Real.sqrt_nonneg _)
    (fun α σ y => mul_le_mul (hwE y) ((SmoothPieceEps.vortAmp_le W hD α σ y).trans (by
      have := hle y 2; nlinarith)) (Real.sqrt_nonneg _) hE0) v G H
  refine isRestBound_congr (((b1.neg.add b2.neg).add b3.neg).add b4.neg) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  unfold pieceEpsRestMode
  rw [edgeSum_scale h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v' κ σ y) ι
    hp.ne']
  ring

end Internal.PiecePassageDiffBoundEps

end Coercive

end Breakdown
