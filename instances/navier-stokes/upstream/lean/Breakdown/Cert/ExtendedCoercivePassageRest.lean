import Breakdown.Cert.CoercivePieceDensityPassageRestSum
import Breakdown.Cert.ExtendedCoerciveZeroFlow

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PassageRest

open Coercive Coercive.Internal Coercive.Internal.SmoothPieceEps Coercive.Internal.SmoothPieceMuNeg
open Coercive.Internal.PieceDensityPassageRestSum

section Amplitudes

variable (W : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem velAmp_le_one (α : ℤ × ℤ) (σ : ℝ) (y : Space) : velAmp W α σ y ≤ 3 * (D / (1 + ‖y‖)) := by
  have hb : ∀ s x, ‖W s x‖ ≤ D / (1 + ‖x‖) := fun s x => by
    have := hD s x 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
  have hK : 0 ≤ D / (1 + ‖y‖) := le_trans (norm_nonneg _) (hb 0 y)
  have := sqrt_cnormSq_le (modeVel α W σ y) hK fun i => by
    refine norm_modeAverage_le α _ i fun τ φ => ?_
    refine le_trans (abs_coord_le _ i) ?_
    rw [RotationInternal.axialRot_norm]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [velAmp] using this

theorem gradAmp_le_one (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    gradAmp (gradField W) α σ y ≤ 9 * (D / (1 + ‖y‖) ^ 2) := by
  have hb : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ D / (1 + ‖x‖) ^ 2 := fun s x => by
    have := hD s x 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 2 := le_trans (norm_nonneg _) (hb 0 y)
  have := sqrt_cnormSq_le (modeGrad α (gradField W) σ y) hK fun ij => by
    refine norm_modeAverage_le α _ ij fun τ φ => ?_
    refine le_trans (abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [norm_rot_unit, mul_one]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [gradAmp] using this

theorem vortAmp_le_one (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortAmp (gradField W) α σ y ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by
  have h1 := gradAmp_le_one W hD α σ y
  have h0 : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
  unfold vortAmp
  calc Real.sqrt (cnormSq (curlOfGrad (modeGrad α (gradField W) σ y)))
      ≤ Real.sqrt (16 ^ 2 * cnormSq (modeGrad α (gradField W) σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Internal.PieceAbsorb.cnormSq_curlOfGrad_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 16 * gradAmp (gradField W) α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by linarith

end Amplitudes

section Sups

variable (W : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem decay_const_nonneg_one : 0 ≤ D := by
  have := hD 0 0 0 (by norm_num)
  have h := le_trans (norm_nonneg _) this
  simpa using h

theorem frameSpeedSup_le_one (a : ℝ) (y : Space) :
    frameSpeedSup W a y ≤ D + (1 / 2 + 2 * |a|) * ‖y‖ := by
  have hD0 := decay_const_nonneg_one W hD
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have hb : ‖W p.1 (axialRot p.2 y)‖ ≤ D := by
    have := hD p.1 (axialRot p.2 y) 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
    refine le_trans this (div_le_self hD0 ?_)
    linarith [norm_nonneg (axialRot p.2 y)]
  have hr := RotationInternal.axialRot_norm p.2 y
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hr]
  have hp := norm_perp_le (axialRot p.2 y)
  rw [hr] at hp
  have : |a| * ‖-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1‖ ≤ |a| * (2 * ‖y‖) :=
    mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [abs_nonneg a, norm_nonneg y]

theorem vortSup_le_one (y : Space) : vortSup W y ≤ 27 * (D / (1 + ‖y‖) ^ 2) := by
  have hD0 := decay_const_nonneg_one W hD
  refine Real.iSup_le (fun p => ?_) (by positivity)
  refine le_trans (norm_curlVec_le _) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have := hD p.1 (axialRot p.2 y) 1 (by norm_num)
  rwa [norm_iteratedFDeriv_one, RotationInternal.axialRot_norm] at this

end Sups

section SecondDerivDecay

variable {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
  (hH : ∀ σ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3)
include hH

theorem secondDerivAmp_le_with (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    secondDerivAmp HW α σ y ≤ 27 * (D / (1 + ‖y‖) ^ 3) := by
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 3 := le_trans (norm_nonneg _) (hH 0 y)
  have := sqrt_cnormSq_le (modeSecondDeriv α HW σ y) hK fun ijl => by
    refine norm_modeAverage_le α _ ijl fun τ φ => ?_
    refine le_trans (abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm₂ _ _ _) ?_
    rw [norm_rot_unit, norm_rot_unit, mul_one, mul_one]
    have := hH (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [secondDerivAmp] using this

theorem vortGradAmp_le_with (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortGradAmp HW α σ y ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by
  have h1 := secondDerivAmp_le_with hH α σ y
  unfold vortGradAmp
  calc Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α HW σ y)))
      ≤ Real.sqrt (27 ^ 2 * cnormSq (modeSecondDeriv α HW σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 27 * secondDerivAmp HW α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by linarith

end SecondDerivDecay

section Pointwise

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) (W v : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem decay_le_self_one (y : Space) (k : ℕ) : D / (1 + ‖y‖) ^ k ≤ D :=
  div_le_self (decay_const_nonneg_one W hD) (one_le_pow₀ (by linarith [norm_nonneg y]))

end Pointwise

section MuPointwise

variable (h : HarmonicBounds) (W v : ℝ → Space → Space) {D : ℝ}
  (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem edge_pointwise_one (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {Bw : ℝ} (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hwB : wt y ≤ Bw) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) *
        (∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
          + 2 * ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg_one W hD
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
        mul_le_mul_of_nonneg_right (velAmp_le_one W hD α σ y) (p3 κ)
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

theorem press_pointwise_one (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {η B4 : ℝ} (hη : 0 < η) (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hw4 : wt y * (1 + ‖y‖) ^ 2 ≤ B4) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * η)
          + (1 / 2) * η * wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤
      ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * η))
          * ((h.harmonics.card : ℝ≥0∞) * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
        + ENNReal.ofReal ((1 / 2) * η * B4 ^ 2) * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) := by
  have hD0 := decay_const_nonneg_one W hD
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
    have h1 := gradAmp_le_one W hD α σ y
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

end MuPointwise

theorem muEdge_pointwise_one (h : HarmonicBounds) (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    {D : ℝ} (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (T : Set (ℤ × ℤ)) (wt : Space → ℝ) {Bw : ℝ} (σ : ℝ) (y : Space)
    (hw0 : 0 ≤ wt y) (hwB : wt y ≤ Bw) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (wt y * velAmp v ι σ y
        * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι) ≤
      ENNReal.ofReal (Bw * (3 * D)) * ((h.harmonics.card : ℝ≥0∞) *
        (∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
          + 2 * ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg_one W hD
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
        mul_le_mul_of_nonneg_right (velAmp_le_one W hD α σ y) (p3 κ)
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

theorem epsRest_pointwise_one {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : ∀ σ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3)
    {Bw : ℝ} (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y) ≤
      ENNReal.ofReal (Bw * (729 * D)) *
        ((h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg_one W hD
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
      (le_trans (velAmp_le_one W hD α σ y) (by have := div_le_self hD0 (by linarith [norm_nonneg y] : (1 : ℝ) ≤ 1 + ‖y‖); rw [hMdef]; linarith)) (p2 κ)
  have E2 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
      ≤ M * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p1 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (gradAmp_le_one W hD α σ y) (by have := decay_le_self_one W hD y 2; rw [hMdef]; linarith)) (p1 κ)
  have E3 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y)
      (fun κ => velAmp v κ σ y) ι ≤ M * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)) := fun ι => by
    refine edgeSum_le_crude h _ _ _ _ ι hM p4 fun α _ κ => ?_
    have hu : 0 ≤ velAmp v κ σ y := Real.sqrt_nonneg _
    have h3 : D / (1 + ‖y‖) ^ 3 ≤ D / (1 + ‖y‖) :=
      div_le_div_of_nonneg_left hD0 hr (le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num))
    calc vortGradAmp HW α σ y * velAmp v κ σ y
        ≤ (27 * (27 * (D / (1 + ‖y‖) ^ 3))) * velAmp v κ σ y :=
          mul_le_mul_of_nonneg_right (vortGradAmp_le_with hH α σ y) hu
      _ ≤ (729 * (D / (1 + ‖y‖))) * velAmp v κ σ y := by nlinarith
      _ = M * a4 κ := by rw [hMdef, ha4]; field_simp
  have E4 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι
      ≤ M * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p3 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (vortAmp_le_one W hD α σ y) (by have := decay_le_self_one W hD y 2; rw [hMdef]; linarith)) (p3 κ)
  have hpt : ∀ ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)))) := by
    intro ι
    have e : -pieceEpsRestModeWith m h W HW v G H β ι σ y =
        (m.epsP β).wt y * a1 ι * (edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
          + edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
          + edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι
          + edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι) := by
      unfold pieceEpsRestModeWith; ring
    rw [e]
    exact rest_term_le (hwt0 y) (hwtB y) (p1 ι) hM (E1 ι) (E2 ι) (E3 ι) (E4 ι)
      (S a2 p2 ι) (S a1 p1 ι) (S a4 p4 ι) (S a3 p3 ι)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left, show Bw * (729 * D) = Bw * M from rfl]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  exact add_le_add (add_le_add (add_le_add (tsum_edge_le _ a1 a2 p1 p2) (tsum_edge_le _ a1 a1 p1 p1))
    (tsum_edge_le _ a1 a4 p1 p4)) (tsum_edge_le _ a1 a3 p1 p3)

private theorem sq_sqrt_cnormSq {β : Type*} [Fintype β] (x : β → ℂ) : Real.sqrt (cnormSq x) ^ 2 = cnormSq x :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem ampSq_eq (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    secondDerivAmp H ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortAmp G ι σ y ^ 2
      + (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 = DensityPassageRest.ampSq v G H ι σ y := by
  simp only [secondDerivAmp, vortGradAmp, gradAmp, vortAmp, velAmp, DensityPassageRest.ampSq, div_pow, sq_sqrt_cnormSq]

private theorem families_le (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) ≤ DensityPassageRest.ampTot v G H σ y := by
  have e := ampSq_eq v G H
  have p : ∀ ι, 0 ≤ secondDerivAmp H ι σ y ^ 2 ∧ 0 ≤ vortGradAmp H ι σ y ^ 2 ∧ 0 ≤ gradAmp G ι σ y ^ 2
      ∧ 0 ≤ vortAmp G ι σ y ^ 2 ∧ 0 ≤ (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := fun ι =>
    ⟨sq_nonneg _, sq_nonneg _, sq_nonneg _, sq_nonneg _, sq_nonneg _⟩
  unfold DensityPassageRest.ampTot
  refine ⟨ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_⟩ <;>
  · rw [← e ι σ y]
    obtain ⟨a, b, c, d, f⟩ := p ι
    linarith

private theorem ofReal_abs_split {n k : ℕ} (a : ℝ) (e : Fin n → ℝ) (mm c d : Fin k → ℝ) (he : ∀ β, e β ≤ 0)
    (hmm : ∀ β, mm β = -(c β) - d β) (hc : ∀ β, 0 ≤ c β) (hd : ∀ β, 0 ≤ d β) :
    ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β| ≤
      ENNReal.ofReal |a| + ∑ β, ENNReal.ofReal (-e β) + ∑ β, (ENNReal.ofReal (c β) + ENNReal.ofReal (d β)) := by
  have h1 : |∑ β, e β| ≤ ∑ β, -e β := by
    rw [abs_of_nonpos (Finset.sum_nonpos fun β _ => he β), Finset.sum_neg_distrib]
  have h2 : |∑ β, mm β| ≤ ∑ β, (c β + d β) := by
    have hs : ∑ β, mm β = -∑ β, (c β + d β) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by rw [hmm β]; ring
    rw [hs, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun β _ => add_nonneg (hc β) (hd β))]
  have h3 : |a + ∑ β, e β + ∑ β, mm β| ≤ |a| + ∑ β, -e β + ∑ β, (c β + d β) := by
    have := abs_add_le (a + ∑ β, e β) (∑ β, mm β)
    have := abs_add_le a (∑ β, e β)
    linarith
  have n1 : 0 ≤ ∑ β, -e β := Finset.sum_nonneg fun β _ => neg_nonneg.2 (he β)
  have n2 : 0 ≤ ∑ β, (c β + d β) := Finset.sum_nonneg fun β _ => add_nonneg (hc β) (hd β)
  calc ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β|
      ≤ ENNReal.ofReal (|a| + ∑ β, -e β + ∑ β, (c β + d β)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) n1) n2, ENNReal.ofReal_add (abs_nonneg _) n1,
        ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (he β)),
        ENNReal.ofReal_sum_of_nonneg (fun β _ => add_nonneg (hc β) (hd β))]
      congr 1
      exact Finset.sum_congr rfl fun β _ => ENNReal.ofReal_add (hc β) (hd β)

theorem rest_tsum_le_one {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ σ y, ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3)
    (hwb : ∃ B, ∀ y, w y ≤ B) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ∑' ι : ℤ × ℤ, ENNReal.ofReal |pieceRestWith m h w W HW v G H ι σ y| ≤ K * DensityPassageRest.ampTot v G H σ y := by
  obtain ⟨D, hD, hH⟩ := hWdecay
  obtain ⟨Kb, hKb0, hKb⟩ := PieceDensityPassageRestBase.base_pointwise (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) hwb
  choose Bm Bgm hBm using fun β => SmoothPieceMuNeg.weight_facts (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) β
  have hwtB : ∀ β y, (m.epsP β).wt y ≤ epsSup := fun β y =>
    (Finset.single_le_sum (fun b _ => hm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  set card : ℝ≥0∞ := (h.harmonics.card : ℝ≥0∞) with hcard
  set ce : ℝ≥0∞ := ENNReal.ofReal (epsSup * (729 * D)) * (12 * card) with hce
  set cz : Fin nM → ℝ≥0∞ := fun β => ENNReal.ofReal (Bm β * (3 * D)) * (3 * card) with hcz
  set cp : Fin nM → ℝ≥0∞ := fun β =>
    ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * card
      + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * Bm β) ^ 2) with hcp
  refine ⟨ENNReal.ofReal Kb + ∑ _β : Fin nE, ce + ∑ β, (cz β + cp β), ?_, ?_⟩
  · simp only [hce, hcz, hcp, hcard]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))⟩,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)),
        ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
          ENNReal.ofReal_ne_top⟩⟩⟩
  intro v G H σ y
  obtain ⟨fv, fvg, fg, fl⟩ := families_le v G H σ y
  set A := DensityPassageRest.ampTot v G H σ y with hA
  have hpt : ∀ ι, ENNReal.ofReal |pieceRestWith m h w W HW v G H ι σ y| ≤
      ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y)
        + ∑ β, (ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) := by
    intro ι
    unfold pieceRestWith
    refine ofReal_abs_split _ _ _ _ _ (fun β => ?_) (fun β => ?_) (fun β => ?_) (fun β => ?_)
    · unfold pieceEpsRestModeWith
      refine neg_nonpos.2 (mul_nonneg (mul_nonneg (hm.eps_wt_nonneg β y) (Real.sqrt_nonneg _)) ?_)
      have hX : ∀ (X : ℤ × ℤ → ℝ), (∀ α, 0 ≤ X α) → ∀ (g : ℤ × ℤ → ℝ), (∀ κ, 0 ≤ g κ) →
          0 ≤ edgeSum h (m.epsP β).modes X g ι := fun X hX g hg =>
        SmoothPieceMuNeg.edgeSum_nonneg_of h _ X g hX hg ι
      exact add_nonneg (add_nonneg (add_nonneg (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _)))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _)))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _))
    · unfold pieceMuRestMode
      ring
    · exact mul_nonneg (mul_nonneg (hm.mu_wt_nonneg β y) (Real.sqrt_nonneg _))
        (SmoothPieceMuNeg.edgeSum_nonneg_of h _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) ι)
    · exact mul_nonneg (SmoothPieceMuNeg.ind_nonneg_of _) (add_nonneg
        (div_nonneg (sq_nonneg _) (by linarith [hm.mu_eta_pos β]))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hm.mu_eta_pos β).le) (sq_nonneg _)) (sq_nonneg _)))
  have hbase : ∑' ι, ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
      ≤ ENNReal.ofReal Kb * A := by
    rw [hA, DensityPassageRest.ampTot, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← ENNReal.ofReal_mul hKb0, ← ampSq_eq]
    exact ENNReal.ofReal_le_ofReal (hKb v G H ι σ y)
  have heps : ∀ β, ∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y) ≤ ce * A := by
    intro β
    calc _ ≤ _ := epsRest_pointwise_one m h W v G H β hD hH (fun y => hm.eps_wt_nonneg β y)
          (fun y => hwtB β y) σ y
      _ ≤ ENNReal.ofReal (epsSup * (729 * D)) * (card * (A + 2 * A) + card * (A + 2 * A)
          + card * (A + 2 * A) + card * (A + 2 * A)) := by gcongr
      _ = ce * A := by rw [hce]; ring
  have hedge : ∀ β, ∑' ι, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
      * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι) ≤ cz β * A := by
    intro β
    obtain ⟨h0, h1, -, -⟩ := hBm β y
    calc _ ≤ _ := muEdge_pointwise_one h W v G hD (m.muP β).modes (m.muP β).wt σ y h0 h1
      _ ≤ ENNReal.ofReal (Bm β * (3 * D)) * (card * (A + 2 * A)) := by gcongr
      _ = cz β * A := by rw [hcz]; ring
  have hpress : ∀ β, ∑' ι, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
        + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤ cp β * A := by
    intro β
    obtain ⟨h0, -, h4, -⟩ := hBm β y
    calc _ ≤ _ := press_pointwise_one h W v hD (m.muP β).modes (m.muP β).wt (hm.mu_eta_pos β) σ y h0 h4
      _ ≤ ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * (card * A)
          + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * Bm β) ^ 2) * A := by gcongr
      _ = cp β * A := by rw [hcp]; ring
  calc ∑' ι, ENNReal.ofReal |pieceRestWith m h w W HW v G H ι σ y|
      ≤ ∑' ι, (ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y)
        + ∑ β, (ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)))) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' ι, ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v G H β ι σ y)
        + ∑ β, (∑' ι, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ∑' ι, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1
      exact Finset.sum_congr rfl fun β _ => ENNReal.tsum_add
    _ ≤ ENNReal.ofReal Kb * A + ∑ _β : Fin nE, ce * A + ∑ β, (cz β * A + cp β * A) := by
      gcongr with β _ β _
      · exact heps β
      · exact hedge β
      · exact hpress β
    _ = (ENNReal.ofReal Kb + ∑ _β : Fin nE, ce + ∑ β, (cz β + cp β)) * A := by
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun β _ => (add_mul _ _ _).symm

theorem muBlock_pointwise_one {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space))
    (β : Fin nM) {D B4 Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (σ : ℝ) (y : Space) (hw0 : 0 ≤ (m.muP β).wt y) (hw4 : (m.muP β).wt y * (1 + ‖y‖) ^ 2 ≤ B4)
    (hg1 : PieceWeights.wtGrad (m.muP β).wt y * (1 + ‖y‖) ≤ Bg) :
    ENNReal.ofReal (-pieceMuBlock m W v G β σ y) ≤
      ENNReal.ofReal (2 * (B4 * (D + (1 / 2 + 2 * |(m.muP β).frame|)) + Bg + |(m.muP β).frame| * B4)) *
        (∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := decay_const_nonneg_one W hD
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
  have fss := frameSpeedSup_le_one W hD a y
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

theorem epsBlock_pointwise_one {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) {D Bw Bd Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hS : ∀ y, vortGradSupWith HW y ≤ 27 * (D / (1 + ‖y‖) ^ 3))
    (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (hdec : ∀ y, ‖y‖ * (m.epsP β).wt y ≤ Bd) (hgrad : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ Bg)
    (σ : ℝ) (y : Space) :
    ENNReal.ofReal (-pieceEpsBlockWith m W HW v G H β σ y) ≤
      ENNReal.ofReal (4 * (Bw * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + Bg + Bw * (27 * D + |(m.epsP β).frame|)
          + 27 * Bw * D)) *
        (∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := decay_const_nonneg_one W hD
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
  have fss := frameSpeedSup_le_one W hD a y
  have vs := vortSup_le_one W hD y
  have vgs := hS y
  have fss0 := frameSpeedSup_nonneg W a y
  have vs0 := vortSup_nonneg W y
  have vgs0 := (Real.iSup_nonneg fun _ => norm_nonneg _ : 0 ≤ vortGradSupWith HW y)
  set K0 := Bw * D + (1 / 2 + 2 * |a|) * Bd + Bg + Bw * (27 * D + |a|) + 27 * Bw * D with hK0
  have d2 : D / (1 + ‖y‖) ^ 2 ≤ D := decay_le_self_one W hD y 2
  have d3 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0), mul_le_mul_of_nonneg_left
      (le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0)) hD0]
  have e : -pieceEpsBlockWith m W HW v G H β σ y =
      (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y) * S2 * S1
        + wt * ((1 / 2) * vortSup W y + |a|) * S1 ^ 2
        + (wt * vortGradSupWith HW y * (1 + ‖y‖)) * S4 * S1 + wt * vortSup W y * S3 * S1 := by
    unfold pieceEpsBlockWith
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
  have k3 : wt * vortGradSupWith HW y * (1 + ‖y‖) ≤ K0 := by
    have h1 : vortGradSupWith HW y * (1 + ‖y‖) ≤ 27 * D := by
      calc vortGradSupWith HW y * (1 + ‖y‖) ≤ 27 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right vgs hr.le
        _ = 27 * (D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖)) := by ring
        _ ≤ 27 * D := by linarith
    have : wt * vortGradSupWith HW y * (1 + ‖y‖) ≤ 27 * Bw * D := by
      calc wt * vortGradSupWith HW y * (1 + ‖y‖) = wt * (vortGradSupWith HW y * (1 + ‖y‖)) := by ring
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
  have c3 : 0 ≤ wt * vortGradSupWith HW y * (1 + ‖y‖) := by positivity
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

theorem epsBlockWith_nonpos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (β : Fin nE) (σ : ℝ) (y : Space) :
    pieceEpsBlockWith m W HW v G H β σ y ≤ 0 := by
  have hFS : 0 ≤ frameSpeedSup W (m.epsP β).frame y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS : 0 ≤ vortGradSupWith HW y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hwg : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  have ha := hE β y
  have h1 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y) := Real.sqrt_nonneg _
  have h2 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) := Real.sqrt_nonneg _
  have h3 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y) := Real.sqrt_nonneg _
  have h4 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y) := Real.sqrt_nonneg _
  have t1 := mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha hFS) hwg) h1) h2
  have t2 := mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
    (abs_nonneg (m.epsP β).frame))) (pow_nonneg h2 2)
  have t3 := mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2
  have t4 := mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2
  unfold pieceEpsBlockWith
  linarith

theorem block_le_one {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, (∀ σ y, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) ∧
      ∀ y, vortGradSupWith HW y ≤ 27 * (D / (1 + ‖y‖) ^ 3)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ENNReal.ofReal |pieceBlockWith m W HW v G H σ y| ≤ K * DensityPassageRest.ampTot v G H σ y := by
  obtain ⟨D, hD, hS⟩ := hWdecay
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  choose Ke hKe using hm.eps_increment
  choose Bm Bgm hBm using fun β => SmoothPieceMuNeg.weight_facts (zeroFlowWeights m) P h w (fun _ _ => 0)
    (zeroFlowAdmissibleHolds_proof m P h w W HW hm) β
  have hwtB : ∀ β y, (m.epsP β).wt y ≤ epsSup := fun β y =>
    (Finset.single_le_sum (fun b _ => hm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  have hg : ∀ β y, PieceWeights.wtGrad (m.epsP β).wt y ≤ (Ke β : ℝ) := fun β y => by
    unfold PieceWeights.wtGrad
    exact norm_fderiv_le_of_lipschitz ℝ (hKe β)
  set ce : Fin nE → ℝ≥0∞ := fun β => ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd
      + (Ke β : ℝ) + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) * 4 with hce
  set cm : Fin nM → ℝ≥0∞ := fun β => ENNReal.ofReal (2 * (4 * Bm β * (D + (1 / 2 + 2 * |(m.muP β).frame|))
      + Bgm β + |(m.muP β).frame| * (4 * Bm β))) * 2 with hcm
  refine ⟨∑ β, ce β + ∑ β, cm β, ?_, ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by norm_num), ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)⟩
  intro v G H σ y
  obtain ⟨fv, fvg, fg, fl⟩ := families_le v G H σ y
  set A := DensityPassageRest.ampTot v G H σ y with hA
  have hne := fun β => epsBlockWith_nonpos m W HW v G H (fun β y => hm.eps_wt_nonneg β y) β σ y
  have hnm := fun β => SmoothPieceDensity.muBlock_nonpos m W v G (fun β y => hm.mu_wt_nonneg β y) β σ y
  have hsplit : ENNReal.ofReal |pieceBlockWith m W HW v G H σ y| =
      ∑ β, ENNReal.ofReal (-pieceEpsBlockWith m W HW v G H β σ y) + ∑ β, ENNReal.ofReal (-pieceMuBlock m W v G β σ y) := by
    unfold pieceBlockWith
    rw [abs_of_nonpos (add_nonpos (Finset.sum_nonpos fun β _ => hne β) (Finset.sum_nonpos fun β _ => hnm β)),
      neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hne β))
        (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hnm β)),
      ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (hne β)),
      ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (hnm β))]
  have he : ∀ β, ENNReal.ofReal (-pieceEpsBlockWith m W HW v G H β σ y) ≤ ce β * A := by
    intro β
    calc _ ≤ _ := epsBlock_pointwise_one m W v G H β hD hS (fun y => hm.eps_wt_nonneg β y)
          (fun y => hwtB β y) (fun y => hBd β y) (fun y => hg β y) σ y
      _ ≤ ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd
          + (Ke β : ℝ) + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) * (A + A + A + A) := by gcongr
      _ = ce β * A := by rw [hce]; ring
  have hmu : ∀ β, ENNReal.ofReal (-pieceMuBlock m W v G β σ y) ≤ cm β * A := by
    intro β
    obtain ⟨h0, -, h4, hg1⟩ := hBm β y
    calc _ ≤ _ := muBlock_pointwise_one m W v G β hD σ y h0 h4 hg1
      _ ≤ ENNReal.ofReal (2 * (4 * Bm β * (D + (1 / 2 + 2 * |(m.muP β).frame|))
          + Bgm β + |(m.muP β).frame| * (4 * Bm β))) * (A + A) := by gcongr
      _ = cm β * A := by rw [hcm]; ring
  rw [hsplit, add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with β _ β _
  · exact he β
  · exact hmu β

end Internal.PassageRest

end CoerciveWeak

end Breakdown
