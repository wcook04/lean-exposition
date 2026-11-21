import Breakdown.Cert.CoerciveDensityPassageRestBound
import Breakdown.Cert.CoerciveSmoothPieceEpsBounds
import Breakdown.Cert.CoerciveSmoothPieceMuNeg

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PiecePassageDiffBoundMu

open DensityPassageRestBound

theorem ind_nonneg (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ind_le_one (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ite_nonneg_le_one (p q : Prop) [Decidable p] [Decidable q] :
    0 ≤ (if p then (0 : ℝ) else if q then 1 else 0) ∧ (if p then (0 : ℝ) else if q then 1 else 0) ≤ 1 := by
  split_ifs <;> norm_num

open Classical in
theorem mul_edgeSum_eq (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (a : ℝ) (ι : ℤ × ℤ) :
    a * edgeSum h T X g ι = ∑ β ∈ h.harmonics,
      ((a * X β * (if ι ∉ T then 0 else if ι - β ∈ T then 0 else 1)) * g (ι - β)
        + (a * X β * (if ι ∈ T then 0 else if -ι ∈ T then (if -ι - β ∈ T then 0 else 1) else 0)) * g (ι - -β)) := by
  unfold edgeSum
  by_cases h1 : ι ∈ T
  · rw [if_pos h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h2 : ι - β ∈ T <;> simp [h1, h2] <;> ring
  · by_cases h2 : -ι ∈ T
    · rw [if_neg h1, if_pos h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases h3 : -ι - β ∈ T <;> simp [h1, h2, h3, sub_neg_eq_add] <;> ring
    · rw [if_neg h1, if_neg h2, mul_zero]
      symm
      refine Finset.sum_eq_zero fun β _ => ?_
      simp [h1, h2]

theorem isRestBound_congr {R R' : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hR : IsRestBound R v G H) (e : ∀ v G H ι σ y, R v G H ι σ y = R' v G H ι σ y) :
    IsRestBound R' v G H := by
  have : R = R' := by
    funext a b c ι σ y
    exact e a b c ι σ y
  subst this
  exact hR

theorem coeff_le {a A x X e : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hx : 0 ≤ x) (hX : x ≤ X) (he : 0 ≤ e)
    (he1 : e ≤ 1) : |a * x * e| ≤ A * X := by
  rw [abs_of_nonneg (by positivity)]
  have h1 : a * x ≤ A * X := mul_le_mul hA hX hx (ha.trans hA)
  have h2 : a * x * e ≤ a * x := by nlinarith [mul_nonneg ha hx]
  linarith

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}

theorem muRest_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => pieceMuRestMode m h W v G β ι σ y) v G H := by
  classical
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨B, Bg, hB⟩ := SmoothPieceMuNeg.weight_facts m P h w W hm β
  have hB0 : 0 ≤ B := (hB 0).1.trans (hB 0).2.1
  have hD0 : 0 ≤ D := by
    have h0 := hD 0 0 0 (by norm_num)
    rw [norm_zero, add_zero, zero_add, pow_one, div_one] at h0
    exact (norm_nonneg _).trans h0
  have heta := hm.mu_eta_pos β
  have hy1 : ∀ y : Space, 1 ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  have hwt1 : ∀ y : Space, (m.muP β).wt y * (1 + ‖y‖) ≤ 4 * B := fun y => by
    have h3 := (hB y).2.2.1
    have h0 := (hB y).1
    have : (m.muP β).wt y * (1 + ‖y‖) ≤ (m.muP β).wt y * (1 + ‖y‖) ^ 2 := by
      have := hy1 y
      have : (1 + ‖y‖) ≤ (1 + ‖y‖) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this h0
    linarith
  have hwt0 : ∀ y : Space, 0 ≤ (m.muP β).wt y * (1 + ‖y‖) := fun y => mul_nonneg (hB y).1 (by positivity)
  have hXv : ∀ α σ y, velAmp W α σ y ≤ 3 * D := fun α σ y => by
    have := SmoothPieceEps.velAmp_le W hD α σ y
    have : D / (1 + ‖y‖) ≤ D := div_le_self hD0 (hy1 y)
    linarith
  have hXg : ∀ α σ y, gradAmp (gradField W) α σ y * (1 + ‖y‖) ≤ 9 * D := fun α σ y => by
    have h1 := SmoothPieceEps.gradAmp_le W hD α σ y
    have hp : 0 < 1 + ‖y‖ := by positivity
    have h2 : 9 * (D / (1 + ‖y‖) ^ 2) * (1 + ‖y‖) ≤ 9 * D := by
      rw [show 9 * (D / (1 + ‖y‖) ^ 2) * (1 + ‖y‖) = 9 * (D / (1 + ‖y‖)) by field_simp]
      have : D / (1 + ‖y‖) ≤ D := div_le_self hD0 (hy1 y)
      linarith
    exact (mul_le_mul_of_nonneg_right h1 hp.le).trans h2
  have hXg0 : ∀ α σ y, 0 ≤ gradAmp (gradField W) α σ y * (1 + ‖y‖) := fun α σ y =>
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hAamp : IsAmp (fun v _ _ ι σ y => velAmp v ι σ y / (1 + ‖y‖)) := isAmp_vel
  have hBamp : IsAmp (fun _ G _ ι σ y => gradAmp G ι σ y) := isAmp_grad
  have h1 : IsRestBound (fun v G H ι σ y => ∑ α ∈ h.harmonics,
      (((m.muP β).wt y * (1 + ‖y‖) * velAmp W α σ y * (if ι ∉ (m.muP β).modes then 0 else if ι - α ∈ (m.muP β).modes then 0 else 1))
          * (velAmp v (ι - 0) σ y / (1 + ‖y‖) * gradAmp G (ι - α) σ y)
        + ((m.muP β).wt y * (1 + ‖y‖) * velAmp W α σ y
            * (if ι ∈ (m.muP β).modes then 0 else if -ι ∈ (m.muP β).modes then (if -ι - α ∈ (m.muP β).modes then 0 else 1) else 0))
          * (velAmp v (ι - 0) σ y / (1 + ‖y‖) * gradAmp G (ι - -α) σ y))) v G H := by
    refine isRestBound_finsetSum _ fun α _ => IsRestBound.add ?_ ?_
    · refine isRestBound_prod hAamp hBamp _ (M := 4 * B * (3 * D)) (by positivity) (fun ι σ y => ?_) 0 α v G H
      refine coeff_le (hwt0 y) (hwt1 y) (Real.sqrt_nonneg _) (hXv α σ y) ?_ ?_
      · split_ifs <;> norm_num
      · split_ifs <;> norm_num
    · refine isRestBound_prod hAamp hBamp _ (M := 4 * B * (3 * D)) (by positivity) (fun ι σ y => ?_) 0 (-α) v G H
      refine coeff_le (hwt0 y) (hwt1 y) (Real.sqrt_nonneg _) (hXv α σ y) ?_ ?_
      · split_ifs <;> norm_num
      · split_ifs <;> norm_num
  have h2 : IsRestBound (fun v G H ι σ y => ∑ α ∈ h.harmonics, ∑ α' ∈ h.harmonics,
      (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ((gradAmp (gradField W) α σ y * (1 + ‖y‖))
        * (gradAmp (gradField W) α' σ y * (1 + ‖y‖))) / (2 * (m.muP β).eta))
        * (velAmp v (ι - α) σ y / (1 + ‖y‖) * (velAmp v (ι - α') σ y / (1 + ‖y‖)))) v G H := by
    refine isRestBound_finsetSum _ fun α _ => isRestBound_finsetSum _ fun α' _ => ?_
    refine isRestBound_prod hAamp hAamp _ (M := (9 * D) * (9 * D) / (2 * (m.muP β).eta)) (by positivity)
      (fun ι σ y => ?_) α α' v G H
    rw [abs_of_nonneg (by
      have := ind_nonneg (PieceWeights.inPiece (m.muP β).modes ι)
      have := hXg0 α σ y
      have := hXg0 α' σ y
      positivity)]
    have e0 := ind_nonneg (PieceWeights.inPiece (m.muP β).modes ι)
    have e1 := ind_le_one (PieceWeights.inPiece (m.muP β).modes ι)
    have p := mul_le_mul (hXg α σ y) (hXg α' σ y) (hXg0 α' σ y) (by positivity)
    have q : 0 ≤ (gradAmp (gradField W) α σ y * (1 + ‖y‖)) * (gradAmp (gradField W) α' σ y * (1 + ‖y‖)) :=
      mul_nonneg (hXg0 α σ y) (hXg0 α' σ y)
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have h3 : IsRestBound (fun v G H ι σ y =>
      (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ((1 / 2) * (m.muP β).eta * ((m.muP β).wt y * (1 + ‖y‖)) ^ 2))
        * (velAmp v (ι - 0) σ y / (1 + ‖y‖) * (velAmp v (ι - 0) σ y / (1 + ‖y‖)))) v G H := by
    refine isRestBound_prod hAamp hAamp _ (M := (1 / 2) * (m.muP β).eta * (4 * B) ^ 2) (by positivity)
      (fun ι σ y => ?_) 0 0 v G H
    have e0 := ind_nonneg (PieceWeights.inPiece (m.muP β).modes ι)
    have e1 := ind_le_one (PieceWeights.inPiece (m.muP β).modes ι)
    have p : ((m.muP β).wt y * (1 + ‖y‖)) ^ 2 ≤ (4 * B) ^ 2 := pow_le_pow_left₀ (hwt0 y) (hwt1 y) 2
    have q : 0 ≤ (1 / 2) * (m.muP β).eta * ((m.muP β).wt y * (1 + ‖y‖)) ^ 2 := by positivity
    rw [abs_of_nonneg (mul_nonneg e0 q)]
    have : (1 / 2) * (m.muP β).eta * ((m.muP β).wt y * (1 + ‖y‖)) ^ 2 ≤ (1 / 2) * (m.muP β).eta * (4 * B) ^ 2 :=
      mul_le_mul_of_nonneg_left p (by positivity)
    nlinarith
  refine isRestBound_congr ((h1.neg.add h2.neg).add h3.neg) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have E1 : (m.muP β).wt y * velAmp v' ι σ y * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y)
      (fun κ => gradAmp G' κ σ y) ι = ∑ α ∈ h.harmonics,
      (((m.muP β).wt y * (1 + ‖y‖) * velAmp W α σ y
          * (if ι ∉ (m.muP β).modes then 0 else if ι - α ∈ (m.muP β).modes then 0 else 1))
          * (velAmp v' ι σ y / (1 + ‖y‖) * gradAmp G' (ι - α) σ y)
        + ((m.muP β).wt y * (1 + ‖y‖) * velAmp W α σ y
            * (if ι ∈ (m.muP β).modes then 0 else if -ι ∈ (m.muP β).modes then
              (if -ι - α ∈ (m.muP β).modes then 0 else 1) else 0))
          * (velAmp v' ι σ y / (1 + ‖y‖) * gradAmp G' (ι - -α) σ y)) := by
    rw [mul_edgeSum_eq]
    refine Finset.sum_congr rfl fun α _ => ?_
    field_simp
  have E2 : ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v' (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta))
      = ∑ α ∈ h.harmonics, ∑ α' ∈ h.harmonics,
        (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ((gradAmp (gradField W) α σ y * (1 + ‖y‖))
          * (gradAmp (gradField W) α' σ y * (1 + ‖y‖))) / (2 * (m.muP β).eta))
          * (velAmp v' (ι - α) σ y / (1 + ‖y‖) * (velAmp v' (ι - α') σ y / (1 + ‖y‖))) := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α' _ => ?_
    field_simp
  have E3 : ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v' ι σ y ^ 2)
      = (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * ((1 / 2) * (m.muP β).eta * ((m.muP β).wt y * (1 + ‖y‖)) ^ 2))
        * (velAmp v' ι σ y / (1 + ‖y‖) * (velAmp v' ι σ y / (1 + ‖y‖))) := by
    field_simp
  simp only [sub_zero]
  unfold pieceMuRestMode
  linear_combination E1 + E2 + E3

end Internal.PiecePassageDiffBoundMu

end Coercive

end Breakdown
