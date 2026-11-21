import Breakdown.Cert.CoercivePieceDensityPassageDiffBound
import Breakdown.Cert.ExtendedCoercivePassageRest
import Breakdown.Cert.ExtendedCoercivePassageBlockDefs
import Breakdown.Cert.ExtendedCoercivePieceDensityMeasure

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PassageDiff

open Coercive Coercive.Internal Coercive.Internal.DensityPassageRestBound

section Mu

open Coercive.Internal.PiecePassageDiffBoundMu

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem muRest_bound_one (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => pieceMuRestMode m h W v G β ι σ y) v G H := by
  classical
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨B, Bg, hB⟩ := SmoothPieceMuNeg.weight_facts (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) β
  replace hB : ∀ y, 0 ≤ (m.muP β).wt y ∧ (m.muP β).wt y ≤ B ∧ (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ 4 * B ∧
      PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg := hB
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
    have := Internal.PassageRest.velAmp_le_one W hD α σ y
    have : D / (1 + ‖y‖) ≤ D := div_le_self hD0 (hy1 y)
    linarith
  have hXg : ∀ α σ y, gradAmp (gradField W) α σ y * (1 + ‖y‖) ≤ 9 * D := fun α σ y => by
    have h1 := Internal.PassageRest.gradAmp_le_one W hD α σ y
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

end Mu

section Eps

open Coercive.Internal.PiecePassageDiffBoundMu Coercive.Internal.PiecePassageDiffBoundEps

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem epsRest_bound_with (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ σ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3)
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => pieceEpsRestModeWith m h W HW v G H β ι σ y) v G H := by
  obtain ⟨D, hD, hH⟩ := hWdecay
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
    (fun α σ y => mul_le_mul (hwE y) ((Internal.PassageRest.velAmp_le_one W hD α σ y).trans (by
      have := hle y 1; rw [pow_one] at this; linarith)) (Real.sqrt_nonneg _) hE0) v G H
  have b2 := edge_bound hA hA h (m.epsP β).modes (fun α σ y => gradAmp (gradField W) α σ y)
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (9 * D)) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => Real.sqrt_nonneg _)
    (fun α σ y => mul_le_mul (hwE y) ((Internal.PassageRest.gradAmp_le_one W hD α σ y).trans (by
      have := hle y 2; linarith)) (Real.sqrt_nonneg _) hE0) v G H
  have b3 := edge_bound hA isAmp_vel h (m.epsP β).modes
    (fun α σ y => vortGradAmp HW α σ y * (1 + ‖y‖))
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (27 * (27 * D))) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    (fun α σ y => by
      have h1 := Internal.PassageRest.vortGradAmp_le_with hH α σ y
      have hp : 0 < 1 + ‖y‖ := by positivity
      have h2 : vortGradAmp HW α σ y * (1 + ‖y‖) ≤ 27 * (27 * D) := by
        have e : 27 * (27 * (D / (1 + ‖y‖) ^ 3)) * (1 + ‖y‖) = 27 * (27 * (D / (1 + ‖y‖) ^ 2)) := by
          field_simp
        have := hle y 2
        nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
      exact mul_le_mul (hwE y) h2 (mul_nonneg (Real.sqrt_nonneg _) hp.le) hE0) v G H
  have b4 := edge_bound hA isAmp_grad h (m.epsP β).modes (fun α σ y => vortAmp (gradField W) α σ y)
    (fun σ y => (m.epsP β).wt y) (M := epsSup * (16 * (9 * D))) (by positivity) (fun σ y => hw0 y)
    (fun α σ y => Real.sqrt_nonneg _)
    (fun α σ y => mul_le_mul (hwE y) ((Internal.PassageRest.vortAmp_le_one W hD α σ y).trans (by
      have := hle y 2; nlinarith)) (Real.sqrt_nonneg _) hE0) v G H
  refine isRestBound_congr (((b1.neg.add b2.neg).add b3.neg).add b4.neg) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  unfold pieceEpsRestModeWith
  rw [edgeSum_scale h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v' κ σ y) ι
    hp.ne']
  ring

theorem rest_diff_bound_with (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ σ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3)
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => pieceRestWith m h w W HW v G H ι σ y) v G H :=
  ((PiecePassageDiffBound.base_bound (zeroFlowAdmissibleHolds_proof m P h w W HW hm) hwb v G H).add
    (PiecePassageDiffBound.isRestBound_sum Finset.univ fun β _ => epsRest_bound_with hm hWdecay β v G H)).add
    (PiecePassageDiffBound.isRestBound_sum Finset.univ fun β _ =>
      muRest_bound_one hm (let ⟨D, hD, _⟩ := hWdecay; ⟨D, hD⟩) β v G H)

end Eps

section Block

open Coercive.Internal.PiecePassageDiffBoundMu Coercive.Internal.PiecePassageDiffBoundBlock

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem muBlock_bound_one (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => if ι = 0 then pieceMuBlock m W v G β σ y else 0) v G H := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 := Internal.PassageRest.decay_const_nonneg_one W hD
  obtain ⟨B, Bg, hB⟩ := SmoothPieceMuNeg.weight_facts (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) β
  replace hB : ∀ y, 0 ≤ (m.muP β).wt y ∧ (m.muP β).wt y ≤ B ∧ (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ 4 * B ∧
      PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg := hB
  have hB0 : 0 ≤ B := (hB 0).1.trans (hB 0).2.1
  have hBg0 : 0 ≤ Bg := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hB 0).2.2.2
  set a := (m.muP β).frame
  have hfs : ∀ y : Space, frameSpeedSup W a y ≤ (D + 1 / 2 + 2 * |a|) * (1 + ‖y‖) := fun y => by
    have := Internal.PassageRest.frameSpeedSup_le_one W hD a y
    nlinarith [norm_nonneg y, abs_nonneg a]
  have hc1 : ∀ (σ : ℝ) (y : Space), |-(((m.muP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y)
      * (1 + ‖y‖))| ≤ 4 * B * (D + 1 / 2 + 2 * |a|) + Bg := fun σ y => by
    obtain ⟨w0, -, w2, w3⟩ := hB y
    have f0 := SmoothPieceEps.frameSpeedSup_nonneg W a y
    have g0 : 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := norm_nonneg _
    have hp : 0 ≤ 1 + ‖y‖ := by positivity
    refine abs_neg_le (by positivity) ?_
    have e1 : (m.muP β).wt y * frameSpeedSup W a y * (1 + ‖y‖)
        ≤ (m.muP β).wt y * ((D + 1 / 2 + 2 * |a|) * (1 + ‖y‖)) * (1 + ‖y‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfs y) w0) hp
    have e2 : (m.muP β).wt y * ((D + 1 / 2 + 2 * |a|) * (1 + ‖y‖)) * (1 + ‖y‖)
        = (m.muP β).wt y * (1 + ‖y‖) ^ 2 * (D + 1 / 2 + 2 * |a|) := by ring
    have e3 : (m.muP β).wt y * (1 + ‖y‖) ^ 2 * (D + 1 / 2 + 2 * |a|) ≤ 4 * B * (D + 1 / 2 + 2 * |a|) :=
      mul_le_mul_of_nonneg_right w2 (by positivity)
    nlinarith
  have hc2 : ∀ (σ : ℝ) (y : Space), |-((m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2)| ≤ 4 * B * |a| := fun σ y => by
    obtain ⟨w0, -, w2, -⟩ := hB y
    refine abs_neg_le (by positivity) ?_
    have : (m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2 = (m.muP β).wt y * (1 + ‖y‖) ^ 2 * |a| := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right w2 (abs_nonneg a)
  have b1 := block_prod_bound isAmp_grad isAmp_vel (m.muP β).modes
    (fun σ y => -(((m.muP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)))
    (by positivity) hc1 v G H
  have b2 := block_prod_bound isAmp_vel isAmp_vel (m.muP β).modes
    (fun σ y => -((m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2)) (by positivity) hc2 v G H
  refine isRestBound_congr (b1.add b2) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
    unfold pieceMuBlock
    rw [pieceNorm_scale (m.muP β).modes (fun κ => velAmp v' κ σ y) hp]
    ring
  · simp only [if_neg h0, add_zero]

theorem epsBlockLower_bound (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) {s : Space → ℝ} (hs0 : ∀ y, 0 ≤ s y)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ y, s y * (1 + ‖y‖) ≤ 27 * D)
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => if ι = 0 then epsBlockLower m W s v G H β σ y else 0) v G H := by
  obtain ⟨D, hD, hvg⟩ := hWdecay
  have hD0 := Internal.PassageRest.decay_const_nonneg_one W hD
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  have hw0 : ∀ y, 0 ≤ (m.epsP β).wt y := fun y => hm.eps_wt_nonneg β y
  have hwE : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  have hgE : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup := fun y =>
    (Finset.single_le_sum (f := fun b => PieceWeights.wtGrad (m.epsP b).wt y) (fun b _ => norm_nonneg _)
      (Finset.mem_univ β)).trans (hm.eps_grad_sum_le y)
  have hE0 : 0 ≤ epsSup := (hw0 0).trans (hwE 0)
  have hG0 : 0 ≤ epsGradSup := (norm_nonneg _).trans (hgE 0)
  have hBd0 : 0 ≤ Bd := (mul_nonneg (norm_nonneg _) (hw0 0)).trans (hBd β 0)
  have hy1 : ∀ y : Space, 1 ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  set a := (m.epsP β).frame
  have hvs : ∀ y : Space, vortSup W y ≤ 27 * D := fun y => by
    have := Internal.PassageRest.vortSup_le_one W hD y
    have : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ (hy1 y))
    linarith
  have hvs0 : ∀ y, 0 ≤ vortSup W y := fun y => SmoothPieceEps.vortSup_nonneg W y
  have hvg0 : ∀ y, 0 ≤ s y := hs0
  have hwfs : ∀ y : Space, (m.epsP β).wt y * frameSpeedSup W a y ≤ epsSup * D + (1 / 2 + 2 * |a|) * Bd :=
    fun y => by
      have h1 := Internal.PassageRest.frameSpeedSup_le_one W hD a y
      have h2 := mul_le_mul_of_nonneg_left h1 (hw0 y)
      have h3 := hBd β y
      have h4 : (m.epsP β).wt y * D ≤ epsSup * D := mul_le_mul_of_nonneg_right (hwE y) hD0
      have h5 : (m.epsP β).wt y * ((1 / 2 + 2 * |a|) * ‖y‖) ≤ (1 / 2 + 2 * |a|) * Bd := by
        have : (m.epsP β).wt y * ((1 / 2 + 2 * |a|) * ‖y‖) = (1 / 2 + 2 * |a|) * (‖y‖ * (m.epsP β).wt y) := by
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      nlinarith
  have b1 := block_prod_bound isAmp_vortGrad isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y))
    (M := epsSup * D + (1 / 2 + 2 * |a|) * Bd + epsGradSup) (by positivity)
    (fun σ y => abs_neg_le (add_nonneg (mul_nonneg (hw0 y) (SmoothPieceEps.frameSpeedSup_nonneg W a y))
      (norm_nonneg _)) (add_le_add (hwfs y) (hgE y))) v G H
  have b2 := block_prod_bound isAmp_vort isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * ((1 / 2) * vortSup W y + |a|)))
    (M := epsSup * ((1 / 2) * (27 * D) + |a|)) (by positivity)
    (fun σ y => abs_neg_le (mul_nonneg (hw0 y) (by have := hvs0 y; positivity))
      (mul_le_mul (hwE y) (by have := hvs y; linarith) (by have := hvs0 y; positivity) hE0)) v G H
  have b3 := block_prod_bound isAmp_vel isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * s y * (1 + ‖y‖)))
    (M := epsSup * (27 * D)) (by positivity)
    (fun σ y => abs_neg_le (by have := hw0 y; have := hvg0 y; positivity) (by
      rw [mul_assoc]; exact mul_le_mul (hwE y) (hvg y) (by have := hvg0 y; positivity) hE0)) v G H
  have b4 := block_prod_bound isAmp_grad isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * vortSup W y))
    (M := epsSup * (27 * D)) (by positivity)
    (fun σ y => abs_neg_le (mul_nonneg (hw0 y) (hvs0 y)) (mul_le_mul (hwE y) (hvs y) (hvs0 y) hE0)) v G H
  refine isRestBound_congr (((b1.add b2).add b3).add b4) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
    unfold epsBlockLower
    rw [pieceNorm_scale (m.epsP β).modes (fun κ => velAmp v' κ σ y) hp]
    ring
  · simp only [if_neg h0, add_zero]

theorem pieceBlockLower_eq (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    Internal.PieceDensityPassageWeak.pieceBlockLower m W HW v G H σ y
      = ∑ β, epsBlockLower m W (Internal.Minorant.vortGradSupLower HW) v G H β σ y
        + ∑ β, pieceMuBlock m W v G β σ y := by
  have e : ∀ β, epsBlockLower m W (Internal.Minorant.vortGradSupLower HW) v G H β σ y
      = pieceEpsBlockWith m W 0 v G H β σ y - Internal.Minorant.vortGradSupLower HW y * ((m.epsP β).wt y
        * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
        * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)) := by
    intro β
    unfold epsBlockLower pieceEpsBlockWith
    rw [Internal.PieceDensityPassageWeak.vortGradSupWith_zero]
    ring
  unfold Internal.PieceDensityPassageWeak.pieceBlockLower pieceBlockWith Internal.PieceDensityPassageWeak.blockGain
  rw [Finset.sum_congr rfl fun β _ => e β, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem block_lower_diff_bound (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ y, Internal.Minorant.vortGradSupLower HW y * (1 + ‖y‖) ≤ 27 * D)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (PiecePassageDiffBound.atOrigin fun v G H σ y =>
      Internal.PieceDensityPassageWeak.pieceBlockLower m W HW v G H σ y) v G H := by
  refine PiecePassageDiffBound.isRestBound_congr ((PiecePassageDiffBound.isRestBound_sum Finset.univ fun β _ =>
    epsBlockLower_bound hm (Internal.Minorant.vortGradSupLower_nonneg HW) hWdecay β v G H).add
    (PiecePassageDiffBound.isRestBound_sum Finset.univ fun β _ =>
      muBlock_bound_one hm (let ⟨D, hD, _⟩ := hWdecay; ⟨D, hD⟩) β v G H)) fun a b c ι σ y => ?_
  unfold PiecePassageDiffBound.atOrigin
  beta_reduce
  rw [pieceBlockLower_eq]
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
  · simp only [if_neg h0, Finset.sum_const_zero, add_zero]

end Block

end Internal.PassageDiff

end CoerciveWeak

end Breakdown
