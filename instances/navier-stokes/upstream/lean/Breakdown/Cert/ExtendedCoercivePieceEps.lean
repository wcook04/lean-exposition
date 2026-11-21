import Breakdown.Cert.CoerciveSmoothPieceEpsFrequency
import Breakdown.Cert.ExtendedCoerciveNodes
import Breakdown.Cert.ExtendedCoerciveMinorant
import Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope
import Breakdown.Cert.ExtendedCoercivePieceEpsSumSecondPartials
import Breakdown.Cert.ExtendedCoercivePieceEpsRightGradient
import Breakdown.Cert.ExtendedCoercivePieceEpsRotation
import Breakdown.Cert.CoerciveDensityPassageLinear
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.ExtendedCoerciveVortGradMap
import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionAssembly
import Breakdown.Cert.ExtendedCoercivePieceEpsTransport
import Breakdown.Cert.ExtendedCoercivePieceEpsModeIdentity
import Breakdown.Cert.ExtendedCoercivePieceEpsOrbitSecondDeriv
import Breakdown.Cert.ExtendedCoercivePieceEpsSymbolBound
import Breakdown.Cert.ExtendedCoercivePieceEpsStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.ExtendedPieceEps

open Coercive

theorem ind_nonneg_of (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem edgeSum_nonneg_of (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ)
    (hX : ∀ α, 0 ≤ X α) (hg : ∀ κ, 0 ≤ g κ) : 0 ≤ edgeSum h T X g ι := by
  classical
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun α _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX α) (hg _)]
  · exact Finset.sum_nonneg fun α _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX α) (hg _)]
  · exact le_rfl

theorem ennreal_le_step {A N : ℝ≥0∞} {X : ℝ} (hA : A < ⊤) (hN : N < ⊤) (hI : A.toReal ≤ X + N.toReal) :
    A + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + N := by
  rcases le_or_gt 0 X with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero]
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA.ne).symm
      _ ≤ ENNReal.ofReal (X + N.toReal) := ENNReal.ofReal_le_ofReal hI
      _ = ENNReal.ofReal X + ENNReal.ofReal N.toReal := ENNReal.ofReal_add hX ENNReal.toReal_nonneg
      _ = ENNReal.ofReal X + N := by rw [ENNReal.ofReal_toReal hN.ne]
  · rw [ENNReal.ofReal_of_nonpos hX.le, zero_add]
    calc A + ENNReal.ofReal (-X) = ENNReal.ofReal A.toReal + ENNReal.ofReal (-X) := by
          rw [ENNReal.ofReal_toReal hA.ne]
      _ = ENNReal.ofReal (A.toReal + -X) := (ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)).symm
      _ ≤ ENNReal.ofReal N.toReal := ENNReal.ofReal_le_ofReal (by linarith)
      _ = N := ENNReal.ofReal_toReal hN.ne

theorem splitBound_of_signs {X : ℝ} {Pos Rest : ℝ → Space → ℤ × ℤ → ℝ} {Blk : ℝ → Space → ℝ}
    (hR : ∀ σ y ι, Rest σ y ι ≤ 0) (hB : ∀ σ y, Blk σ y ≤ 0)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))) < ⊤)
    (hI : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)).toReal ≤
      X + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))).toReal) :
    IsSplitLowerBound X Pos Rest Blk (fun _ _ => 0) := by
  unfold IsSplitLowerBound
  refine ⟨hN, ?_⟩
  have eR : ∀ σ y ι, ENNReal.ofReal (Rest σ y ι) = 0 := fun σ y ι => ENNReal.ofReal_of_nonpos (hR σ y ι)
  have eB : ∀ σ y, ENNReal.ofReal (Blk σ y) = 0 := fun σ y => ENNReal.ofReal_of_nonpos (hB σ y)
  simp only [eR, eB, tsum_zero, add_zero, neg_zero, ENNReal.ofReal_zero]
  exact ennreal_le_step hA hN hI

section Bounds

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
  (hW : IsWeakSecondDerivState W HW D)
include hW

theorem flow_decay_nonneg : 0 ≤ D := by
  have h := le_trans (norm_nonneg _) (hW.decay 0 0).1
  simpa using h

theorem flow_decay_le_self (y : Space) (k : ℕ) : D / (1 + ‖y‖) ^ k ≤ D :=
  div_le_self (flow_decay_nonneg hW) (one_le_pow₀ (by linarith [norm_nonneg y]))

theorem velFlowAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) : velAmp W α σ y ≤ 3 * (D / (1 + ‖y‖)) := by
  have hb : ∀ s x, ‖W s x‖ ≤ D / (1 + ‖x‖) := fun s x => (hW.decay s x).1
  have hK : 0 ≤ D / (1 + ‖y‖) := le_trans (norm_nonneg _) (hb 0 y)
  have := Coercive.Internal.SmoothPieceEps.sqrt_cnormSq_le (modeVel α W σ y) hK fun i => by
    refine Coercive.Internal.SmoothPieceEps.norm_modeAverage_le α _ i fun τ φ => ?_
    refine le_trans (Coercive.Internal.SmoothPieceEps.abs_coord_le _ i) ?_
    rw [RotationInternal.axialRot_norm]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [velAmp] using this

theorem gradFlowAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    gradAmp (gradField W) α σ y ≤ 9 * (D / (1 + ‖y‖) ^ 2) := by
  have hb : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ D / (1 + ‖x‖) ^ 2 := fun s x => (hW.decay s x).2.1
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 2 := le_trans (norm_nonneg _) (hb 0 y)
  have := Coercive.Internal.SmoothPieceEps.sqrt_cnormSq_le (modeGrad α (gradField W) σ y) hK fun ij => by
    refine Coercive.Internal.SmoothPieceEps.norm_modeAverage_le α _ ij fun τ φ => ?_
    refine le_trans (Coercive.Internal.SmoothPieceEps.abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [Coercive.Internal.SmoothPieceEps.norm_rot_unit, mul_one]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [gradAmp] using this

theorem secondDerivWithAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    secondDerivAmp HW α σ y ≤ 27 * (D / (1 + ‖y‖) ^ 3) := by
  have hb : ∀ s x, ‖HW s x‖ ≤ D / (1 + ‖x‖) ^ 3 := fun s x => (hW.decay s x).2.2
  have hK : 0 ≤ D / (1 + ‖y‖) ^ 3 := le_trans (norm_nonneg _) (hb 0 y)
  have := Coercive.Internal.SmoothPieceEps.sqrt_cnormSq_le (modeSecondDeriv α HW σ y) hK fun ijl => by
    refine Coercive.Internal.SmoothPieceEps.norm_modeAverage_le α _ ijl fun τ φ => ?_
    refine le_trans (Coercive.Internal.SmoothPieceEps.abs_coord_le _ _) ?_
    rw [RotationInternal.axialRot_norm]
    refine le_trans (ContinuousLinearMap.le_opNorm₂ _ _ _) ?_
    rw [Coercive.Internal.SmoothPieceEps.norm_rot_unit, Coercive.Internal.SmoothPieceEps.norm_rot_unit,
      mul_one, mul_one]
    have := hb (σ + τ) (axialRot φ y)
    rwa [RotationInternal.axialRot_norm] at this
  simpa [secondDerivAmp] using this

theorem vortFlowAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortAmp (gradField W) α σ y ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by
  have h1 := gradFlowAmp_le hW α σ y
  unfold vortAmp
  calc Real.sqrt (cnormSq (curlOfGrad (modeGrad α (gradField W) σ y)))
      ≤ Real.sqrt (16 ^ 2 * cnormSq (modeGrad α (gradField W) σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Coercive.Internal.PieceAbsorb.cnormSq_curlOfGrad_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Coercive.Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 16 * gradAmp (gradField W) α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 16 * (9 * (D / (1 + ‖y‖) ^ 2)) := by linarith

theorem vortGradWithAmp_le (α : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortGradAmp HW α σ y ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by
  have h1 := secondDerivWithAmp_le hW α σ y
  unfold vortGradAmp
  calc Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α HW σ y)))
      ≤ Real.sqrt (27 ^ 2 * cnormSq (modeSecondDeriv α HW σ y)) :=
        Real.sqrt_le_sqrt (le_trans (Coercive.Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le _)
          (mul_le_mul_of_nonneg_right (by norm_num) (Coercive.Internal.PieceAbsorb.cnormSq_nonneg' _)))
    _ = 27 * secondDerivAmp HW α σ y := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl
    _ ≤ 27 * (27 * (D / (1 + ‖y‖) ^ 3)) := by linarith

theorem frameSpeedFlow_le (a : ℝ) (y : Space) :
    frameSpeedSup W a y ≤ D + (1 / 2 + 2 * |a|) * ‖y‖ := by
  have hD0 := flow_decay_nonneg hW
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have hb : ‖W p.1 (axialRot p.2 y)‖ ≤ D := by
    refine le_trans (hW.decay p.1 (axialRot p.2 y)).1 (div_le_self hD0 ?_)
    linarith [norm_nonneg (axialRot p.2 y)]
  have hr := RotationInternal.axialRot_norm p.2 y
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hr]
  have hp := Coercive.Internal.SmoothPieceEps.norm_perp_le (axialRot p.2 y)
  rw [hr] at hp
  have : |a| * ‖-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1‖ ≤ |a| * (2 * ‖y‖) :=
    mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [abs_nonneg a, norm_nonneg y]

theorem vortSupFlow_le (y : Space) : vortSup W y ≤ 27 * (D / (1 + ‖y‖) ^ 2) := by
  have hD0 := flow_decay_nonneg hW
  refine Real.iSup_le (fun p => ?_) (by positivity)
  refine le_trans (Coercive.Internal.SmoothPieceEps.norm_curlVec_le _) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have := (hW.decay p.1 (axialRot p.2 y)).2.1
  rwa [RotationInternal.axialRot_norm] at this

theorem vortGradSupWith_decay (y : Space) : vortGradSupWith HW y ≤ 81 * (D / (1 + ‖y‖) ^ 3) := by
  have hD0 := flow_decay_nonneg hW
  refine Real.iSup_le (fun p => ?_) (by positivity)
  refine (CoerciveWeak.Internal.PieceDensity.norm_vortGradMap_le _).trans
    (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have := (hW.decay p.1 (axialRot p.2 y)).2.2
  rwa [RotationInternal.axialRot_norm] at this

end Bounds


section Signs

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
  (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
  (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE)

theorem restWith_nonpos (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceEpsRestModeWith m h W HW v G H β ι σ y ≤ 0 := by
  unfold pieceEpsRestModeWith
  have e1 := edgeSum_nonneg_of h (m.epsP β).modes
    (fun α => velAmp W α σ y) (fun κ => vortGradAmp H κ σ y) ι
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e2 := edgeSum_nonneg_of h (m.epsP β).modes
    (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp G κ σ y) ι
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e3 := edgeSum_nonneg_of h (m.epsP β).modes
    (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e4 := edgeSum_nonneg_of h (m.epsP β).modes
    (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp G κ σ y) ι
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have hv : 0 ≤ vortAmp G ι σ y := Real.sqrt_nonneg _
  have := mul_nonneg (mul_nonneg (hwt y) hv) (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4)
  linarith

theorem blockWith_nonpos (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (σ : ℝ) (y : Space) :
    pieceEpsBlockWith m W HW v G H β σ y ≤ 0 := by
  unfold pieceEpsBlockWith
  have n1 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
  have n2 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => vortAmp G κ σ y)
  have n3 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => velAmp v κ σ y)
  have n4 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => gradAmp G κ σ y)
  have s1 := Coercive.Internal.SmoothPieceEps.frameSpeedSup_nonneg W (m.epsP β).frame y
  have s2 := Coercive.Internal.SmoothPieceEps.vortSup_nonneg W y
  have s3 := CoerciveWeak.Internal.PieceDensity.vortGradSupWith_nonneg HW y
  have g0 : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  have w0 := hwt y
  have t1 : 0 ≤ ((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y + PieceWeights.wtGrad (m.epsP β).wt y)
      * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg w0 s1) g0) n1) n2
  have t2 : 0 ≤ (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2 :=
    mul_nonneg (mul_nonneg w0 (add_nonneg (mul_nonneg (by norm_num) s2) (abs_nonneg _))) (sq_nonneg _)
  have t3 : 0 ≤ (m.epsP β).wt y * vortGradSupWith HW y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (mul_nonneg w0 s3) n3) n2
  have t4 : 0 ≤ (m.epsP β).wt y * vortSup W y * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (mul_nonneg w0 s2) n4) n2
  linarith

end Signs

section Pointwise

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) {W : ℝ → Space → Space}
  {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (v : ℝ → Space → Space) (β : Fin nE) {D : ℝ}
  (hW : IsWeakSecondDerivState W HW D)
include hW

theorem restWith_pointwise {Bw : ℝ} (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y) ≤
      ENNReal.ofReal (Bw * (729 * D)) *
        ((h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2))) := by
  have hD0 := flow_decay_nonneg hW
  set M : ℝ := 729 * D with hMdef
  have hM : 0 ≤ M := by positivity
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  set a1 : ℤ × ℤ → ℝ := fun κ => vortAmp (gradField v) κ σ y with ha1
  set a2 : ℤ × ℤ → ℝ := fun κ => vortGradAmp (secondDerivField v) κ σ y with ha2
  set a3 : ℤ × ℤ → ℝ := fun κ => gradAmp (gradField v) κ σ y with ha3
  set a4 : ℤ × ℤ → ℝ := fun κ => velAmp v κ σ y / (1 + ‖y‖) with ha4
  have p1 : ∀ κ, 0 ≤ a1 κ := fun _ => Real.sqrt_nonneg _
  have p2 : ∀ κ, 0 ≤ a2 κ := fun _ => Real.sqrt_nonneg _
  have p3 : ∀ κ, 0 ≤ a3 κ := fun _ => Real.sqrt_nonneg _
  have p4 : ∀ κ, 0 ≤ a4 κ := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  have S : ∀ (g : ℤ × ℤ → ℝ), (∀ κ, 0 ≤ g κ) → ∀ ι, 0 ≤ ∑ α ∈ h.harmonics, (g (ι - α) + g (ι + α)) :=
    fun g hg ι => Finset.sum_nonneg fun α _ => add_nonneg (hg _) (hg _)
  have E1 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
      ≤ M * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)) := fun ι =>
    Coercive.Internal.SmoothPieceEps.edgeSum_le_crude h _ _ _ _ ι hM p2 fun α _ κ =>
      mul_le_mul_of_nonneg_right (le_trans (velFlowAmp_le hW α σ y)
        (by have := div_le_self hD0 (by linarith [norm_nonneg y] : (1 : ℝ) ≤ 1 + ‖y‖); rw [hMdef]; linarith))
        (p2 κ)
  have E2 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
      ≤ M * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)) := fun ι =>
    Coercive.Internal.SmoothPieceEps.edgeSum_le_crude h _ _ _ _ ι hM p1 fun α _ κ =>
      mul_le_mul_of_nonneg_right (le_trans (gradFlowAmp_le hW α σ y)
        (by have := flow_decay_le_self hW y 2; rw [hMdef]; linarith)) (p1 κ)
  have E3 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y)
      (fun κ => velAmp v κ σ y) ι ≤ M * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)) := fun ι => by
    refine Coercive.Internal.SmoothPieceEps.edgeSum_le_crude h _ _ _ _ ι hM p4 fun α _ κ => ?_
    have hu : 0 ≤ velAmp v κ σ y := Real.sqrt_nonneg _
    have h3 : D / (1 + ‖y‖) ^ 3 ≤ D / (1 + ‖y‖) :=
      div_le_div_of_nonneg_left hD0 hr (le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num))
    calc vortGradAmp HW α σ y * velAmp v κ σ y
        ≤ (27 * (27 * (D / (1 + ‖y‖) ^ 3))) * velAmp v κ σ y :=
          mul_le_mul_of_nonneg_right (vortGradWithAmp_le hW α σ y) hu
      _ ≤ (729 * (D / (1 + ‖y‖))) * velAmp v κ σ y := by nlinarith
      _ = M * a4 κ := by rw [hMdef, ha4]; field_simp
  have E4 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι
      ≤ M * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)) := fun ι =>
    Coercive.Internal.SmoothPieceEps.edgeSum_le_crude h _ _ _ _ ι hM p3 fun α _ κ =>
      mul_le_mul_of_nonneg_right (le_trans (vortFlowAmp_le hW α σ y)
        (by have := flow_decay_le_self hW y 2; rw [hMdef]; linarith)) (p3 κ)
  have hpt : ∀ ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)))) := by
    intro ι
    have e : -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y =
        (m.epsP β).wt y * a1 ι * (edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
          + edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
          + edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι
          + edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι) := by
      unfold pieceEpsRestModeWith; ring
    rw [e]
    exact Coercive.Internal.SmoothPieceEps.rest_term_le (hwt0 y) (hwtB y) (p1 ι) hM (E1 ι) (E2 ι) (E3 ι) (E4 ι)
      (S a2 p2 ι) (S a1 p1 ι) (S a4 p4 ι) (S a3 p3 ι)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left, show Bw * (729 * D) = Bw * M from rfl]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  exact add_le_add (add_le_add (add_le_add
    (Coercive.Internal.SmoothPieceEps.tsum_edge_le _ a1 a2 p1 p2)
    (Coercive.Internal.SmoothPieceEps.tsum_edge_le _ a1 a1 p1 p1))
    (Coercive.Internal.SmoothPieceEps.tsum_edge_le _ a1 a4 p1 p4))
    (Coercive.Internal.SmoothPieceEps.tsum_edge_le _ a1 a3 p1 p3)

end Pointwise

theorem blockWith_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (v : ℝ → Space → Space)
    (β : Fin nE) {D Bw Bd Bg : ℝ} (hW : IsWeakSecondDerivState W HW D)
    (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (hdec : ∀ y, ‖y‖ * (m.epsP β).wt y ≤ Bd) (hgrad : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ Bg)
    (σ : ℝ) (y : Space) :
    ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y) ≤
      ENNReal.ofReal (4 * (Bw * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + Bg + Bw * (27 * D + |(m.epsP β).frame|)
          + 81 * Bw * D)) *
        (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := flow_decay_nonneg hW
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
  set S1 := pieceNorm T (fun κ => vortAmp (gradField v) κ σ y) with hS1
  set S2 := pieceNorm T (fun κ => vortGradAmp (secondDerivField v) κ σ y) with hS2
  set S3 := pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) with hS3
  set S4 := pieceNorm T (fun κ => velAmp v κ σ y / (1 + ‖y‖)) with hS4
  have hSv : pieceNorm T (fun κ => velAmp v κ σ y) = (1 + ‖y‖) * S4 := by
    rw [hS4, ← Coercive.Internal.SmoothPieceEps.pieceNorm_mul T _ hr.le]
    congr 1
    funext κ
    field_simp
  have fss := frameSpeedFlow_le hW a y
  have vs := vortSupFlow_le hW y
  have vgs := vortGradSupWith_decay hW y
  have fss0 := Coercive.Internal.SmoothPieceEps.frameSpeedSup_nonneg W a y
  have vs0 := Coercive.Internal.SmoothPieceEps.vortSup_nonneg W y
  have vgs0 := CoerciveWeak.Internal.PieceDensity.vortGradSupWith_nonneg HW y
  set K0 := Bw * D + (1 / 2 + 2 * |a|) * Bd + Bg + Bw * (27 * D + |a|) + 81 * Bw * D with hK0
  have d2 : D / (1 + ‖y‖) ^ 2 ≤ D := flow_decay_le_self hW y 2
  have d3 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0), mul_le_mul_of_nonneg_left
      (le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0)) hD0]
  have e : -pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y =
      (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y) * S2 * S1
        + wt * ((1 / 2) * vortSup W y + |a|) * S1 ^ 2
        + (wt * vortGradSupWith HW y * (1 + ‖y‖)) * S4 * S1 + wt * vortSup W y * S3 * S1 := by
    unfold pieceEpsBlockWith
    rw [hSv]
    ring
  have k1 : wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y ≤ K0 := by
    have hA : 0 ≤ 1 / 2 + 2 * |a| := by positivity
    have : wt * frameSpeedSup W a y ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := by
      calc wt * frameSpeedSup W a y ≤ wt * (D + (1 / 2 + 2 * |a|) * ‖y‖) := mul_le_mul_of_nonneg_left fss hw
        _ = wt * D + (1 / 2 + 2 * |a|) * (‖y‖ * wt) := by ring
        _ ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := add_le_add (mul_le_mul_of_nonneg_right hwB hD0)
            (mul_le_mul_of_nonneg_left (hdec y) hA)
    have := hgrad y
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    have : 0 ≤ 81 * Bw * D := by positivity
    rw [hK0]; linarith
  have k2 : wt * ((1 / 2) * vortSup W y + |a|) ≤ K0 := by
    have h27 : (1 / 2) * vortSup W y + |a| ≤ 27 * D + |a| := by nlinarith
    have : wt * ((1 / 2) * vortSup W y + |a|) ≤ Bw * (27 * D + |a|) :=
      mul_le_mul hwB h27 (by positivity) hBw
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ 81 * Bw * D := by positivity
    rw [hK0]; linarith
  have k3 : wt * vortGradSupWith HW y * (1 + ‖y‖) ≤ K0 := by
    have h1 : vortGradSupWith HW y * (1 + ‖y‖) ≤ 81 * D := by
      calc vortGradSupWith HW y * (1 + ‖y‖) ≤ 81 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right vgs hr.le
        _ = 81 * (D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖)) := by ring
        _ ≤ 81 * D := by linarith
    have : wt * vortGradSupWith HW y * (1 + ‖y‖) ≤ 81 * Bw * D := by
      calc wt * vortGradSupWith HW y * (1 + ‖y‖) = wt * (vortGradSupWith HW y * (1 + ‖y‖)) := by ring
        _ ≤ Bw * (81 * D) := mul_le_mul hwB h1 (by positivity) hBw
        _ = 81 * Bw * D := by ring
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
  have hb := Coercive.Internal.SmoothPieceEps.block_real c1 c2 c3 c4 k1 k2 k3 k4
    (show 0 ≤ S1 from Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' _ _)
    (show 0 ≤ S2 from Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' _ _)
    (show 0 ≤ S3 from Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' _ _)
    (show 0 ≤ S4 from Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' _ _)
  rw [e]
  refine le_trans (ENNReal.ofReal_le_ofReal hb) ?_
  have hK00 : 0 ≤ K0 := le_trans c4 k4
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK00),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3)) (sq_nonneg S4),
    ENNReal.ofReal_add (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3),
    ENNReal.ofReal_add (sq_nonneg S1) (sq_nonneg S2)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact add_le_add (add_le_add (add_le_add
    (Coercive.Internal.SmoothPieceEps.ofReal_pieceNorm_sq_le T _)
    (Coercive.Internal.SmoothPieceEps.ofReal_pieceNorm_sq_le T _))
    (Coercive.Internal.SmoothPieceEps.ofReal_pieceNorm_sq_le T _))
    (Coercive.Internal.SmoothPieceEps.ofReal_pieceNorm_sq_le T _)

theorem posWith_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)) < ⊤ := by
  have hP : 0 < P := hm.period_pos
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwtc : Continuous (m.epsP β).wt := hK.continuous
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  set a := (m.epsP β).frame
  set c : ℝ := epsSup * (2 * Real.pi / P) with hc
  have hc0 : 0 ≤ c := mul_nonneg (le_trans (hwt0 0) (hwtB 0)) (by positivity)
  have hpt : ∀ σ y ι, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y) ≤
      ENNReal.ofReal c * ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2)
        + ENNReal.ofReal c * ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ENNReal.ofReal |a| * ENNReal.ofReal ((m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2) := by
    intro σ y ι
    have hx := sq_nonneg (vortAmp (gradField v) ι σ y)
    have hw := hwt0 y
    have hwB := hwtB y
    have hi0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) := ind_nonneg_of _
    have hi1 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) ≤ 1 := by
      unfold ModeWeights.ind; split_ifs <;> norm_num
    have hf : |PieceWeights.frameFreq P a ι| ≤ 2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)| := by
      unfold PieceWeights.frameFreq
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul,
        abs_of_pos (by positivity : 0 < 2 * Real.pi / P)]
    have hn : |(ι.1 : ℝ)| ≤ (ι.1 : ℝ) ^ 2 + 1 := by
      nlinarith [abs_nonneg (ι.1 : ℝ), sq_abs (ι.1 : ℝ), sq_nonneg (|(ι.1 : ℝ)| - 1)]
    have hle : pieceEpsPos m P (gradField v) β ι σ y ≤
        c * ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2) + c * vortAmp (gradField v) ι σ y ^ 2
          + |a| * ((m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2) := by
      unfold pieceEpsPos
      set x := vortAmp (gradField v) ι σ y ^ 2
      set wt := (m.epsP β).wt y
      have h1 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt
          * |PieceWeights.frameFreq P a ι| * x ≤ wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) * x := by
        have := mul_le_mul (mul_le_of_le_one_left hw hi1 |>.trans le_rfl) hf (abs_nonneg _) hw
        have h2 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt ≤ wt :=
          mul_le_of_le_one_left hw hi1
        have h3 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt * |PieceWeights.frameFreq P a ι|
            ≤ wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) :=
          mul_le_mul h2 hf (abs_nonneg _) hw
        exact mul_le_mul_of_nonneg_right h3 hx
      have hpi : 0 ≤ 2 * Real.pi / P := by positivity
      have h4 : wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x ≤ c * ((ι.1 : ℝ) ^ 2 * x) + c * x := by
        have h5 : wt * (2 * Real.pi / P) ≤ c := mul_le_mul_of_nonneg_right hwB hpi
        calc wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x = (wt * (2 * Real.pi / P)) * (|(ι.1 : ℝ)| * x) := by ring
          _ ≤ c * (((ι.1 : ℝ) ^ 2 + 1) * x) := mul_le_mul h5 (mul_le_mul_of_nonneg_right hn hx)
              (mul_nonneg (abs_nonneg _) hx) hc0
          _ = c * ((ι.1 : ℝ) ^ 2 * x) + c * x := by ring
      have e : wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) * x
          = wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x + |a| * (wt * |(ι.2 : ℝ)| * x) := by ring
      linarith
    refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
    have q1 : 0 ≤ (ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2 := mul_nonneg (sq_nonneg _) hx
    have q3 : 0 ≤ (m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2 :=
      mul_nonneg (mul_nonneg hw (abs_nonneg _)) hx
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hc0 q1) (mul_nonneg hc0 hx)) (mul_nonneg (abs_nonneg _) q3),
      ENNReal.ofReal_add (mul_nonneg hc0 q1) (mul_nonneg hc0 hx), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_mul (abs_nonneg _)]
  have hp := hSP P v hv
  have hG := hp.measurable_gradient
  have m1 : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (((Coercive.Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2).const_mul _)
  have m2 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((Coercive.Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2)
  have hwm : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
    (hwtc.comp continuous_snd).aemeasurable
  have m3 : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal ((m.epsP β).wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hwm.mul_const _).mul ((Coercive.Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2))
  have T1 := Coercive.Internal.SmoothPieceEpsFrequency.time_series_finite hPars hDer hSP P v hv
  have T3 := Coercive.Internal.SmoothPieceEpsFrequency.angular_series_finite hPars hDer hRotM hSP P v hv (m.epsP β).wt hwt0 hwtc ⟨Bd, hBd β⟩
    ⟨epsSup, hwtB⟩
  have T2 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) (Coercive.Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv)
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have key := Coercive.Internal.SmoothPieceEps.iterated_add3_lt_top (f1 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (f2 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (f3 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((m.epsP β).wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (AEMeasurable.tsum m1) (AEMeasurable.tsum m2) (AEMeasurable.tsum m3)
    (c1 := ENNReal.ofReal c) (c2 := ENNReal.ofReal c) (c3 := ENNReal.ofReal |a|)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top T1 T2 T3
  refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) key
  refine le_trans (ENNReal.tsum_le_tsum (hpt σ y)) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]


theorem negWith_finite (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y))) < ⊤ := by
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  have hgB : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => PieceWeights.wtGrad (m.epsP b).wt y)
      (fun b _ => norm_nonneg _) (Finset.mem_univ β)) (hm.eps_grad_sum_le y)
  set K : ℝ≥0∞ := ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12)
    + ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + epsGradSup
      + epsSup * (27 * D + |(m.epsP β).frame|) + 81 * epsSup * D)) with hK
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num)), ENNReal.ofReal_ne_top⟩
  have hpt : ∀ σ y, ((∑' ι : ℤ × ℤ,
        ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y)) ≤
      K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
    intro σ y
    have hR := restWith_pointwise m h v β hW hwt0 hwtB σ y
    have hB := blockWith_pointwise m v β hW hwt0 hwtB (fun y => hBd β y) hgB σ y
    set A1 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
    set A2 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
    set A3 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
    set A4 := ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
    have l1 : A1 ≤ A1 + A2 + A3 + A4 := by
      calc A1 ≤ A1 + A2 := le_self_add
        _ ≤ A1 + A2 + A3 := le_self_add
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l2 : A2 ≤ A1 + A2 + A3 + A4 := by
      calc A2 ≤ A1 + A2 := le_add_self
        _ ≤ A1 + A2 + A3 := le_self_add
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l3 : A3 ≤ A1 + A2 + A3 + A4 := by
      calc A3 ≤ A1 + A2 + A3 := le_add_self
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l4 : A4 ≤ A1 + A2 + A3 + A4 := le_add_self
    set A := A1 + A2 + A3 + A4 with hA
    have hR' : ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y)
        ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A := by
      refine le_trans hR ?_
      calc ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A2)
            + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A1) + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A4)
            + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A3))
          ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A + 2 * A)
            + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A) + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A)
            + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A)) := by gcongr
        _ = ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A := by ring
    calc _ ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A
          + ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + epsGradSup
            + epsSup * (27 * D + |(m.epsP β).frame|) + 81 * epsSup * D)) * A := add_le_add hR' hB
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
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt)
        (Coercive.Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv)


def blockWithSup {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (s : Space → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) : ℝ :=
  -(((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y + PieceWeights.wtGrad (m.epsP β).wt y)
      * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * s y
      * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    - (m.epsP β).wt y * vortSup W y
      * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)

theorem pieceEpsBlockWith_eq_blockWithSup {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) :
    pieceEpsBlockWith m W HW v G H β σ y = blockWithSup m W (vortGradSupWith HW) v G H β σ y := rfl

theorem neg_blockWithSup_mono {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (W : ℝ → Space → Space) {s t : Space → ℝ} (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (hst : ∀ y, s y ≤ t y) (σ : ℝ) (y : Space) :
    ENNReal.ofReal (-blockWithSup m W s v G H β σ y) ≤ ENNReal.ofReal (-blockWithSup m W t v G H β σ y) := by
  refine ENNReal.ofReal_le_ofReal ?_
  unfold blockWithSup
  have n2 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => vortAmp G κ σ y)
  have n3 := Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg' (m.epsP β).modes (fun κ => velAmp v κ σ y)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hst y) (hwt y)) n3) n2
  linarith

section WeakCore

open Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.PieceAbsorb
  Internal.ExtendedPieceEpsSumSecondPartials

def negSeriesWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (β : Fin nE) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
    + ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v)
      (secondDerivField v) β σ y)

def frameRestWith (a : ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (fun x' => curlVec (fderiv ℝ (v s) x')) x
      (W s x + (1 / 2 : ℝ) • x - a • (-(x 1) • unitVector 0 + x 0 • unitVector 1))
    - fderiv ℝ (W s) x (curlVec (fderiv ℝ (v s) x)) + vortGradMap (HW s x) (v s x)
    - fderiv ℝ (v s) x (curlVec (fderiv ℝ (W s) x))
    + a • (-(curlVec (fderiv ℝ (v s) x) 1) • unitVector 0 + curlVec (fderiv ℝ (v s) x) 0 • unitVector 1)

def restTermWith (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (a : ℝ) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
    (modeVel ι (frameRestWith a W HW v) σ y)).re

def transportPartWith (a : ℝ) (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (fun x' => curlVec (fderiv ℝ (v s) x')) x
    (W s x + (1 / 2 : ℝ) • x - a • (-(x 1) • unitVector 0 + x 0 • unitVector 1))

def stretchPartWith (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (W s) x (curlVec (fderiv ℝ (v s) x))

def vortTransportPartWith (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space) :
    ℝ → Space → Space := fun s x =>
  vortGradMap (HW s x) (v s x)

def vortStretchPartWith (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (v s) x (curlVec (fderiv ℝ (W s) x))

theorem frameRestWith_eq (a : ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) :
    frameRestWith a W HW v = transportPartWith a W v - stretchPartWith W v + vortTransportPartWith HW v
      - vortStretchPartWith W v + rotationPartWith a v := rfl

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
  {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem posSeries_aemeasurable (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hv : IsSmoothPerturbation P v)
    (β : Fin nE) :
    AEMeasurable (fun z : ℝ × Space => posSeries m P v β z.1 z.2) slabMeasure := by
  have hp := hSP P v hv
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwc : Continuous (m.epsP β).wt := hK.continuous
  have hwm : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
    (hwc.comp continuous_snd).aemeasurable
  refine Coercive.Internal.SmoothPieceEps.slab_aem (AEMeasurable.ennreal_tsum fun ι => ?_)
  unfold pieceEpsPos
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (((aemeasurable_const.mul hwm).mul_const _).mul ((aem_vortAmp hp.measurable_gradient ι).pow_const 2))

theorem negSeriesWith_aemeasurable (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    AEMeasurable (fun z : ℝ × Space => negSeriesWith m h W HW v β z.1 z.2) slabMeasure := by
  have hp := hSP P v hv
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwc : Continuous (m.epsP β).wt := hK.continuous
  have hwm : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
    (hwc.comp continuous_snd).aemeasurable
  have hG := hp.measurable_gradient
  have hH := hp.measurable_secondDeriv
  have hV := hp.measurable_velocity
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have cDW : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => W p.1 x) (g := fun p => p.2)
      (hW.smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  have hWv : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume := cW.aestronglyMeasurable
  have hWg : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    cDW.aestronglyMeasurable
  have hWh : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume := hW.secondDeriv_measurable
  have hs1 : Measurable (frameSpeedSup W (m.epsP β).frame) := by
    set a := (m.epsP β).frame
    refine measurable_iSup_of_continuous (fun p => ?_) (fun y => ⟨D + (1 / 2 + 2 * |a|) * ‖y‖, fun p => ?_⟩)
    · have hWs : Continuous (W p.1) := cW.comp (continuous_const.prodMk continuous_id)
      have hr := continuous_rot p.2
      have c0 : Continuous (fun x : Space => x 0) := by fun_prop
      have c1 : Continuous (fun x : Space => x 1) := by fun_prop
      have hq : Continuous (fun y : Space => W p.1 (axialRot p.2 y)) := hWs.comp hr
      have h0 : Continuous (fun y : Space => axialRot p.2 y 0) := c0.comp hr
      have h1 : Continuous (fun y : Space => axialRot p.2 y 1) := c1.comp hr
      exact Continuous.norm (by fun_prop)
    · have hD0 : 0 ≤ D := by
        have h0 := (hW.decay 0 0).1
        rw [norm_zero, add_zero, div_one] at h0
        exact le_trans (norm_nonneg _) h0
      have hb : ‖W p.1 (axialRot p.2 y)‖ ≤ D := by
        refine le_trans (hW.decay p.1 (axialRot p.2 y)).1 (div_le_self hD0 ?_)
        linarith [norm_nonneg (axialRot p.2 y)]
      have hr := RotationInternal.axialRot_norm p.2 y
      refine le_trans (norm_sub_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hr]
      have hp := Coercive.Internal.SmoothPieceEps.norm_perp_le (axialRot p.2 y)
      rw [hr] at hp
      have : |a| * ‖-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1‖ ≤ |a| * (2 * ‖y‖) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith [abs_nonneg a, norm_nonneg y]
  have hs2 : Measurable (vortSup W) := by
    refine measurable_iSup_of_continuous (fun p => ?_) (fun y => ⟨27 * (D / (1 + ‖y‖) ^ 2), fun p => ?_⟩)
    · have hc : Continuous (fun x => fderiv ℝ (W p.1) x) := cDW.comp (continuous_const.prodMk continuous_id)
      exact (Coercive.Internal.SmoothPieceEps.curlLinear.continuous.comp (hc.comp (continuous_rot p.2))).norm
    · refine le_trans (Coercive.Internal.SmoothPieceEps.norm_curlVec_le _) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have := (hW.decay p.1 (axialRot p.2 y)).2.1
      rwa [RotationInternal.axialRot_norm] at this
  have hs3 : Measurable (Internal.Minorant.vortGradSupLower HW) := Internal.Minorant.measurable_vortGradSupLower HW
  have hg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.epsP β).wt z.2) volume :=
    ((measurable_fderiv ℝ (m.epsP β).wt).norm.comp measurable_snd).aemeasurable
  refine Coercive.Internal.SmoothPieceEps.slab_aem ((AEMeasurable.ennreal_tsum fun ι => ?_).add ?_)
  · unfold pieceEpsRestModeWith
    have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
      (g := fun z κ => vortGradAmp (secondDerivField v) κ z.1 z.2) (fun α => aem_velAmp hWv α)
      (fun κ => aem_vortGradAmp hH κ) ι
    have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
      (g := fun z κ => vortAmp (gradField v) κ z.1 z.2) (fun α => aem_gradAmp hWg α)
      (fun κ => aem_vortAmp hG κ) ι
    have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp HW α z.1 z.2)
      (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hWh α)
      (fun κ => aem_velAmp hV κ) ι
    have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
      (g := fun z κ => gradAmp (gradField v) κ z.1 z.2) (fun α => aem_vortAmp hWg α)
      (fun κ => aem_gradAmp hG κ) ι
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((((hwm.mul (aem_vortAmp hG ι)).mul (((e1.add e2).add e3).add e4)).neg).neg)
  · unfold blockWithSup
    have n1 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
      (fun κ => aem_vortGradAmp hH κ)
    have n2 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => vortAmp (gradField v) κ z.1 z.2)
      (fun κ => aem_vortAmp hG κ)
    have n3 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => velAmp v κ z.1 z.2)
      (fun κ => aem_velAmp hV κ)
    have n4 := aem_pieceNorm (m.epsP β).modes (g := fun z κ => gradAmp (gradField v) κ z.1 z.2)
      (fun κ => aem_gradAmp hG κ)
    have a1 : AEMeasurable (fun z : ℝ × Space => frameSpeedSup W (m.epsP β).frame z.2) volume :=
      (hs1.comp measurable_snd).aemeasurable
    have a2 : AEMeasurable (fun z : ℝ × Space => vortSup W z.2) volume := (hs2.comp measurable_snd).aemeasurable
    have a3 : AEMeasurable (fun z : ℝ × Space => Internal.Minorant.vortGradSupLower HW z.2) volume :=
      (hs3.comp measurable_snd).aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((((((((hwm.mul a1).add hg).mul n1).mul n2).neg.sub
        ((hwm.mul ((aemeasurable_const.mul a2).add aemeasurable_const)).mul (n2.pow_const 2))).sub
        (((hwm.mul a3).mul n3).mul n2)).sub (((hwm.mul a2).mul n4).mul n2))).neg)

theorem rightGradient_finite_weak (hSP : SmoothPerturbationIsPerturbationHolds)
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (smoothRight P W v) z.1 z.2) volume ∧
      IsTimePeriodic (gradField (smoothRight P W v)) ∧
      periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ :=
  Internal.WeakRightGradient.rightGradient_finite_of_weak hv hW

theorem cdot_sub_right' (x z₁ z₂ : Fin 3 → ℂ) : cdot x (z₁ - z₂) = cdot x z₁ - cdot x z₂ :=
  (Coercive.ModeL2Internal.cdot_sub_right x z₁ z₂).symm

theorem modeVel_add_of {X Y : ℝ → Space → Space} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure)
    (hY : Integrable (fun p : ℝ × ℝ => Y (z.1 + p.1) (axialRot p.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure)
    (ι : ℤ × ℤ) : modeVel ι (X + Y) z.1 z.2 = modeVel ι X z.1 z.2 + modeVel ι Y z.1 z.2 := by
  have e := Coercive.Internal.DensityPassageLinear.modeVel_sub (v₁ := fun σ y => X σ y + Y σ y) (v₂ := Y)
    (z := z) (hX.add hY) hY ι
  have e2 : (fun σ y => X σ y + Y σ y - Y σ y) = X := by
    funext σ y
    simp
  rw [e2] at e
  change modeVel ι (fun σ y => X σ y + Y σ y) z.1 z.2 = _
  rw [e]
  abel

theorem modeVel_sub_of {X Y : ℝ → Space → Space} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure)
    (hY : Integrable (fun p : ℝ × ℝ => Y (z.1 + p.1) (axialRot p.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure)
    (ι : ℤ × ℤ) : modeVel ι (X - Y) z.1 z.2 = modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2 :=
  Coercive.Internal.DensityPassageLinear.modeVel_sub hX hY ι

theorem orbit_integrable_of_continuous {X : ℝ → Space → Space}
    (hX : Continuous (fun z : ℝ × Space => X z.1 z.2)) (z : ℝ × Space) :
    Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure :=
  Coercive.StretchInternal.integrable_box_of_continuous (hX.comp ((continuous_const.add continuous_fst).prodMk
    (Coercive.Internal.Field.axialRot_comp_continuous continuous_snd continuous_const)))

theorem slabMeasure_ac_volume :
    (slabMeasure : Measure (ℝ × Space)) ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl

theorem ae_orbit_integrable_vortTransport (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) :
    ∀ᵐ z ∂slabMeasure, Integrable (fun p : ℝ × ℝ => vortTransportPartWith HW v (z.1 + p.1) (axialRot p.2 z.2))
      Coercive.Internal.ModeRotation.boxMeasure := by
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := (contDiff_infty.mp hv.smooth 0).continuous
  have hg : Continuous (fun q : (Space →L[ℝ] Space →L[ℝ] Space) × Space => curlVec (q.1 q.2)) :=
    Coercive.Internal.SmoothPieceEps.curlLinear.continuous.comp
      (isBoundedBilinearMap_apply.continuous.comp (continuous_fst.prodMk continuous_snd))
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => vortTransportPartWith HW v z.1 z.2) volume := by
    have e : (fun z : ℝ × Space => vortTransportPartWith HW v z.1 z.2)
        = fun z => curlVec (HW z.1 z.2 (v z.1 z.2)) := by
      funext z
      exact Internal.VortGradMap.vortGradMap_apply _ _
    rw [e]
    have h1 : AEStronglyMeasurable (fun z : ℝ × Space => (HW z.1 z.2, v z.1 z.2)) volume :=
      hW.secondDeriv_measurable.prodMk cv.aestronglyMeasurable
    have h2 := hg.comp_aestronglyMeasurable h1
    exact h2
  have hq := hF.comp_quasiMeasurePreserving
    (Coercive.ModeL2Internal.quasiMeasurePreserving_shiftRot Coercive.Internal.ModeRotation.boxMeasure)
  have hs := hq.prodMk_left
  refine slabMeasure_ac_volume.ae_le (hs.mono fun z hz => ?_)
  have cb : Continuous (fun p : ℝ × ℝ => ‖v (z.1 + p.1) (axialRot p.2 z.2)‖) :=
    (cv.comp ((continuous_const.add continuous_fst).prodMk
      (Coercive.Internal.Field.axialRot_comp_continuous continuous_snd continuous_const))).norm
  have hb : Integrable (fun p : ℝ × ℝ => ‖Coercive.Internal.SmoothPieceEps.curlLinear‖ * D
      * ‖v (z.1 + p.1) (axialRot p.2 z.2)‖) Coercive.Internal.ModeRotation.boxMeasure :=
    Coercive.StretchInternal.integrable_box_of_continuous (continuous_const.mul cb)
  refine hb.mono' hz (Filter.Eventually.of_forall fun p => ?_)
  have hD0 : 0 ≤ D := by
    have h0 := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hH : ‖HW (z.1 + p.1) (axialRot p.2 z.2)‖ ≤ D :=
    (hW.decay _ _).2.2.trans (div_le_self hD0 (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))))
  show ‖vortGradMap (HW (z.1 + p.1) (axialRot p.2 z.2)) (v (z.1 + p.1) (axialRot p.2 z.2))‖ ≤ _
  rw [Internal.VortGradMap.vortGradMap_apply, ← Coercive.Internal.SmoothPieceEps.curlLinear_apply]
  calc ‖Coercive.Internal.SmoothPieceEps.curlLinear (HW (z.1 + p.1) (axialRot p.2 z.2) (v (z.1 + p.1) (axialRot p.2 z.2)))‖
      ≤ ‖Coercive.Internal.SmoothPieceEps.curlLinear‖
        * ‖HW (z.1 + p.1) (axialRot p.2 z.2) (v (z.1 + p.1) (axialRot p.2 z.2))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Coercive.Internal.SmoothPieceEps.curlLinear‖
        * (‖HW (z.1 + p.1) (axialRot p.2 z.2)‖ * ‖v (z.1 + p.1) (axialRot p.2 z.2)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖Coercive.Internal.SmoothPieceEps.curlLinear‖ * (D * ‖v (z.1 + p.1) (axialRot p.2 z.2)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem parts_continuous (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (a : ℝ) :
    Continuous (fun z : ℝ × Space => transportPartWith a W v z.1 z.2)
      ∧ Continuous (fun z : ℝ × Space => stretchPartWith W v z.1 z.2)
      ∧ Continuous (fun z : ℝ × Space => vortStretchPartWith W v z.1 z.2)
      ∧ Continuous (fun z : ℝ × Space => rotationPartWith a v z.1 z.2) := by
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    Coercive.Internal.SmoothRightGradient.contDiff_fderiv_param (F := v) hV (by norm_num)
  have hCv : ContDiff ℝ 2 (fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2)) :=
    Coercive.Internal.SmoothPieceEps.curlLinear.contDiff.comp hDv
  have hDCv : Continuous (fun z : ℝ × Space => fderiv ℝ (fun x' => curlVec (fderiv ℝ (v z.1) x')) z.2) :=
    (Coercive.Internal.SmoothRightGradient.contDiff_fderiv_param
      (F := fun s x => curlVec (fderiv ℝ (v s) x)) (m := 0) hCv (by norm_num)).continuous
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have cDW : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    (Coercive.Internal.SmoothRightGradient.contDiff_fderiv_param (F := W) (m := 0) hW.smooth
      (by norm_num)).continuous
  have c0 : Continuous (fun x : Space => x 0) := Coercive.ModeL2Internal.continuous_coord 0
  have c1 : Continuous (fun x : Space => x 1) := Coercive.ModeL2Internal.continuous_coord 1
  have hperp : Continuous perpVec := by
    unfold perpVec
    exact ((c1.neg).smul continuous_const).add (c0.smul continuous_const)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold transportPartWith
    have hx : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • z.2) := continuous_snd.const_smul (1 / 2 : ℝ)
    have hp : Continuous (fun z : ℝ × Space => a • (-(z.2 1) • unitVector 0 + z.2 0 • unitVector 1)) :=
      (((c1.comp continuous_snd).neg.smul continuous_const).add
        ((c0.comp continuous_snd).smul continuous_const)).const_smul a
    exact hDCv.clm_apply ((cW.add hx).sub hp)
  · unfold stretchPartWith
    exact cDW.clm_apply hCv.continuous
  · unfold vortStretchPartWith
    exact hDv.continuous.clm_apply (Coercive.Internal.SmoothPieceEps.curlLinear.continuous.comp cDW)
  · unfold rotationPartWith curlField
    exact (hperp.comp hCv.continuous).const_smul a

theorem restTermWith_split (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, ∀ ι : ℤ × ℤ,
      restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2
        = modePart (m.epsP β).modes (m.epsP β).wt v (transportPartWith (m.epsP β).frame W v) ι z.1 z.2
          - modePart (m.epsP β).modes (m.epsP β).wt v (stretchPartWith W v) ι z.1 z.2
          + modePart (m.epsP β).modes (m.epsP β).wt v (vortTransportPartWith HW v) ι z.1 z.2
          - modePart (m.epsP β).modes (m.epsP β).wt v (vortStretchPartWith W v) ι z.1 z.2
          + modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2 := by
  obtain ⟨cT, cS, cVS, cR⟩ := parts_continuous hW hv (m.epsP β).frame
  filter_upwards [ae_orbit_integrable_vortTransport hW hv] with z hz
  intro ι
  have iT := orbit_integrable_of_continuous cT z
  have iS := orbit_integrable_of_continuous cS z
  have iVS := orbit_integrable_of_continuous cVS z
  have iR := orbit_integrable_of_continuous cR z
  have e1 := modeVel_sub_of iT iS ι
  have e2 := modeVel_add_of (X := transportPartWith (m.epsP β).frame W v - stretchPartWith W v)
    (Y := vortTransportPartWith HW v) (iT.sub iS) hz ι
  have e3 := modeVel_sub_of (X := transportPartWith (m.epsP β).frame W v - stretchPartWith W v
    + vortTransportPartWith HW v) (Y := vortStretchPartWith W v) ((iT.sub iS).add hz) iVS ι
  have e4 := modeVel_add_of (X := transportPartWith (m.epsP β).frame W v - stretchPartWith W v
    + vortTransportPartWith HW v - vortStretchPartWith W v) (Y := rotationPartWith (m.epsP β).frame v)
    (((iT.sub iS).add hz).sub iVS) iR ι
  unfold restTermWith modePart
  rw [frameRestWith_eq, e4, e3, e2, e1]
  simp only [Coercive.Internal.Field.cdot_add_right, cdot_sub_right', mul_add, mul_sub, Complex.add_re,
    Complex.sub_re]

theorem pieceTerm_sub_weak (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, ∀ ι : ℤ × ℤ,
      pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2
        - pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2
        = pieceEpsPos m P (gradField v) β ι z.1 z.2
          + restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2 := by
  obtain ⟨cT, cS, cVS, cR⟩ := parts_continuous hW hv (m.epsP β).frame
  have hRi : ∀ᵐ z ∂slabMeasure, Integrable (fun q : ℝ × ℝ =>
      frameRestWith (m.epsP β).frame W HW v (z.1 + q.1) (axialRot q.2 z.2)) Coercive.Internal.ModeRotation.boxMeasure := by
    filter_upwards [ae_orbit_integrable_vortTransport hW hv] with z hz
    rw [frameRestWith_eq]
    exact ((((orbit_integrable_of_continuous cT z).sub (orbit_integrable_of_continuous cS z)).add hz).sub
      (orbit_integrable_of_continuous cVS z)).add (orbit_integrable_of_continuous cR z)
  have hid := Internal.WeakModeIdentity.ae_mode_identity_weak hv hW (m.epsP β).frame
    (R := frameRestWith (m.epsP β).frame W HW v)
    (fun s x => by
      show frameRestWith _ _ _ _ s x = _
      unfold frameRestWith
      rw [Internal.VortGradMap.vortGradMap_apply]
      rfl) slabMeasure_ac_volume hRi
  filter_upwards [hid] with z hz
  intro ι
  have e := Coercive.Internal.SmoothPieceEpsCore.term_split
    (PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2)
    (PieceWeights.frameFreq P (m.epsP β).frame ι) (Coercive.Internal.SmoothPieceEpsCore.vortMode v ι z.1 z.2)
    (Coercive.Internal.SmoothPieceEpsCore.vortMode (smoothRight P W v) ι z.1 z.2)
    (Coercive.Internal.SmoothPieceEpsCore.vortMode (negSumSecondPartials v) ι z.1 z.2)
    (modeVel ι (frameRestWith (m.epsP β).frame W HW v) z.1 z.2) (hz ι)
  unfold pieceTerm restTermWith
  unfold Coercive.Internal.SmoothPieceEpsCore.vortMode at e
  rw [e]
  congr 1
  unfold pieceEpsPos vortAmp
  rw [Real.sq_sqrt (Coercive.Internal.FieldModes.cnormSq_nonneg _)]
  have hs := Coercive.Internal.SmoothPieceEpsCore.sgn_mul_frameFreq (hm.eps_oneSided β) ι
  calc PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 * PieceWeights.frameFreq P (m.epsP β).frame ι
        * cnormSq (curlOfGrad (modeGrad ι (gradField v) z.1 z.2))
      = (PieceWeights.sgn (m.epsP β).modes ι * PieceWeights.frameFreq P (m.epsP β).frame ι) * (m.epsP β).wt z.2
        * cnormSq (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) := by ring
    _ = _ := by rw [hs]; ring

theorem edge_summable_weak (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (β : Fin nE) (σ : ℝ)
    (y : Space) (hN : negSeriesWith m h W HW v β σ y < ⊤) :
    Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι) ∧
      Summable (fun ι => (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) := by
  have hwt0 : 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β y
  have hn : ∀ (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ), (∀ α, 0 ≤ X α) → (∀ κ, 0 ≤ g κ) →
      0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes X g ι := fun X g ι hX hg =>
    mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _)) (edgeSum_nonneg_of _ _ _ _ _ hX hg)
  have n1 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n2 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n3 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have n4 : ∀ ι, 0 ≤ (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := fun ι => hn _ _ ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have hE : ∀ ι, -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y
      = (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp (secondDerivField v) κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp (gradField v) κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι
        + (m.epsP β).wt y * vortAmp (gradField v) ι σ y * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := by
    intro ι
    unfold pieceEpsRestModeWith
    ring
  have hR0 : ∀ ι, 0 ≤ -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y := fun ι => by
    rw [hE]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]
  have hAne : (∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.ne le_self_add
  have sR : Summable (fun ι => -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y) := by
    have := ENNReal.summable_toReal hAne
    simpa only [ENNReal.toReal_ofReal (hR0 _)] using this
  refine ⟨sR.of_nonneg_of_le n1 (fun ι => ?_), sR.of_nonneg_of_le n2 (fun ι => ?_),
    sR.of_nonneg_of_le n3 (fun ι => ?_), sR.of_nonneg_of_le n4 (fun ι => ?_)⟩ <;>
  · rw [hE ι]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]

theorem transport_compression_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (transportPartWith (m.epsP β).frame W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re| ≤ (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [Internal.ExtendedPieceEpsTransport.transport_compression_of hPars hSP hm hW hv β]
    with z hz _
  exact hz

theorem stretch_compression_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (stretchPartWith W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re| ≤ (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  filter_upwards [Internal.PieceEpsStretch.stretch_compression_of hPars hSP hm hW hv β] with z hz _
  exact hz

theorem summable_vel_ae_weak (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsSmoothPerturbation P v) :
    ∀ᵐ z ∂slabMeasure, Summable (fun ι => velAmp v ι z.1 z.2 ^ 2) := by
  have hp := hSP P v hv
  have hV := hp.measurable_velocity
  have hden : AEMeasurable (fun z : ℝ × Space => 1 + ‖z.2‖) volume :=
    (continuous_const.add (continuous_norm.comp continuous_snd)).aemeasurable
  have m4 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))
      volume :=
    fun ι => (((aem_velAmp hV ι).div hden).pow_const 2).ennreal_ofReal
  have hAm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) slabMeasure :=
    Coercive.Internal.SmoothPieceEps.slab_aem (AEMeasurable.ennreal_tsum m4)
  have hfin : ∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) ∂slabMeasure < ⊤ := by
    refine lt_of_le_of_lt (lintegral_prod_le _) (lt_of_le_of_lt
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
      (Coercive.Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv))
    exact le_add_self
  filter_upwards [ae_lt_top' hAm hfin.ne] with z hz
  have s := ENNReal.summable_toReal hz.ne
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at s
  have hpos : 0 < 1 + ‖z.2‖ := by positivity
  have e : ∀ ι, velAmp v ι z.1 z.2 ^ 2 = (1 + ‖z.2‖) ^ 2 * (velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2 := by
    intro ι
    field_simp
  simp_rw [e]
  exact s.mul_left _

theorem vortTransport_orbit_expansion_weak (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) :
    ∀ᵐ z ∂slabMeasure, ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure, ∀ i j : Fin 3,
      ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
          + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I)
            * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j) :=
  slabMeasure_ac_volume.ae_le (Internal.OrbitSecondDeriv.orbit_expansion_ae hW h.harmonics hm.harmonics_span
    hm.harmonics_zero hm.harmonics_neg)

theorem vortTransport_symbol_bound_weak (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) :
    ∀ᵐ z ∂slabMeasure, ∀ τ φ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j, (curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
        + ∑ α ∈ h.harmonics.erase 0, Coercive.Internal.SmoothPieceEpsCompression.torusPhase α τ φ
          * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)) * u j)
          ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq u :=
  Internal.PieceEpsSymbolBound.symbol_bound_of_expansion hW (vortTransport_orbit_expansion_weak hm hW)

theorem vortTransport_orbit_symbol_weak (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) (hv : IsSmoothPerturbation P v) :
    ∀ᵐ z ∂slabMeasure, ∃ D0 : Fin 3 → Fin 3 → ℂ,
      (∀ ι, modeVel ι (vortTransportPartWith HW v) z.1 z.2 = fun i => ∑ j : Fin 3,
        (D0 i j * modeVel ι v z.1 z.2 j
          + ∑ α ∈ h.harmonics.erase 0, curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j) * modeVel (ι - α) v z.1 z.2 j)) ∧
      ∀ τ φ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j, (D0 i j + ∑ α ∈ h.harmonics.erase 0,
        Coercive.Internal.SmoothPieceEpsCompression.torusPhase α τ φ * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)) * u j)
          ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq u := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := (contDiff_infty.mp hv.smooth 0).continuous
  filter_upwards [vortTransport_orbit_expansion_weak hm hW, vortTransport_symbol_bound_weak hm hW] with z hE hB
  refine ⟨fun i j => curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j), fun ι => ?_, hB⟩
  funext i
  exact Internal.WeakModeIdentity.mode_product_orbit (h.harmonics.erase 0) (fun s x => vortGradMap (HW s x)) v hvc z
    _ (fun α => curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2)) hE ι i

theorem vortTransport_compression_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (vortTransportPartWith HW v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re| ≤ (m.epsP β).wt z.2 * Internal.Minorant.vortGradSupLower HW z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  have hA := hm
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hA.harmonics_zero
  filter_upwards [Internal.ExtendedPieceEpsTransport.summable_ae_weak hPars hSP hm hv, summable_vel_ae_weak hPars hSP hv,
    vortTransport_orbit_symbol_weak hm hW hv] with z hsum hvel hsym _hN
  obtain ⟨s1, _⟩ := hsum
  obtain ⟨D0, hf, hU⟩ := hsym
  have hS0 : 0 ≤ Internal.Minorant.vortGradSupLower HW z.2 := Internal.Minorant.vortGradSupLower_nonneg HW z.2
  have hcneg : ∀ α, cnormSq (curlGradOfSecondDeriv (modeSecondDeriv (-α) HW z.1 z.2))
      = cnormSq (curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2)) := by
    intro α
    unfold cnormSq
    refine Finset.sum_congr rfl fun il _ => ?_
    have e : curlGradOfSecondDeriv (modeSecondDeriv (-α) HW z.1 z.2) il
        = (starRingEnd ℂ) (curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) il) := by
      unfold curlGradOfSecondDeriv
      simp only [Coercive.Internal.SmoothEpsPointwise.modeSecondDeriv_neg, map_sum, map_mul, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
  obtain ⟨c', h1, h2, h3⟩ := Coercive.Internal.SmoothPieceEpsCompression.compression_mat h (m.epsP β).modes
    (Internal.ExtendedPieceEpsTransport.piece_disjoint_weak hm hv β) hA.harmonics_neg h0
    D0 (fun α => curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2)) (Internal.Minorant.vortGradSupLower HW z.2) hS0 hU hcneg
    (fun ι => curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (fun ι => modeVel ι (vortTransportPartWith HW v) z.1 z.2)
    (fun ι => modeVel ι v z.1 z.2) hf
    (Internal.ExtendedPieceEpsTransport.ind_summable_weak _ _ s1)
    (Internal.ExtendedPieceEpsTransport.ind_summable_weak _ _ hvel) ((m.epsP β).wt z.2) (hA.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

theorem vortStretch_compression_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (vortStretchPartWith W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
            * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2)) (c ι)).re| ≤ (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [Internal.ExtendedPieceEpsTransport.vortStretch_compression_of hPars hSP hm hW hv β]
    with z hz _
  exact hz

theorem transport_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (transportPartWith (m.epsP β).frame W v) ι z.1 z.2) ∧
      -(∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (transportPartWith (m.epsP β).frame W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [transport_compression_weak hPars hDer hRotM hSP hm hW hwb hv β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable_weak hm β z.1 z.2 hN
  have r := Coercive.Internal.SmoothPieceEpsCompression.assemble (m.epsP β).modes (m.epsP β).wt v
    (transportPartWith (m.epsP β).frame W v) z.1 z.2 c _ _ (hm.eps_wt_nonneg β z.2)
    (fun ι => edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.1 hcs hcK
  exact ⟨r.1, r.2.1⟩

theorem stretch_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (stretchPartWith W v) ι z.1 z.2) ∧
      (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (stretchPartWith W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  filter_upwards [stretch_compression_weak hPars hDer hRotM hSP hm hW hwb hv β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable_weak hm β z.1 z.2 hN
  have r := Coercive.Internal.SmoothPieceEpsCompression.assemble (m.epsP β).modes (m.epsP β).wt v
    (stretchPartWith W v) z.1 z.2 c _ _ (hm.eps_wt_nonneg β z.2)
    (fun ι => edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.1 hcs hcK
  exact ⟨r.1, r.2.2⟩

theorem vortTransport_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (vortTransportPartWith HW v) ι z.1 z.2) ∧
      -(∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (vortTransportPartWith HW v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * Internal.Minorant.vortGradSupLower HW z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [vortTransport_compression_weak hPars hDer hRotM hSP hm hW hwb hv β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable_weak hm β z.1 z.2 hN
  have r := Coercive.Internal.SmoothPieceEpsCompression.assemble (m.epsP β).modes (m.epsP β).wt v
    (vortTransportPartWith HW v) z.1 z.2 c _ _ (hm.eps_wt_nonneg β z.2)
    (fun ι => edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.2.1 hcs hcK
  exact ⟨r.1, r.2.1⟩

theorem vortStretch_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (vortStretchPartWith W v) ι z.1 z.2) ∧
      (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (vortStretchPartWith W v) ι z.1 z.2)
        ≤ (∑' ι, (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
            * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)
          + (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
  filter_upwards [vortStretch_compression_weak hPars hDer hRotM hSP hm hW hwb hv β] with z hc hN
  obtain ⟨c, hE, hcs, hcK⟩ := hc hN
  have e := edge_summable_weak hm β z.1 z.2 hN
  have r := Coercive.Internal.SmoothPieceEpsCompression.assemble (m.epsP β).modes (m.epsP β).wt v
    (vortStretchPartWith W v) z.1 z.2 c _ _ (hm.eps_wt_nonneg β z.2)
    (fun ι => edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)) hE e.2.2.2 hcs hcK
  exact ⟨r.1, r.2.2⟩

theorem rotation_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι => modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2) ∧
      -(∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2)
        ≤ (m.epsP β).wt z.2 * |(m.epsP β).frame|
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  filter_upwards [RotationPart.rotation_bound_of hPars hSP hm hv β] with z hz _ using hz

theorem compression_bound_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι : ℤ × ℤ =>
        restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2) →
      -(∑' ι : ℤ × ℤ, restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2)
        ≤ (negSeriesWith m h W HW v β z.1 z.2).toReal - gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2 := by
  filter_upwards [transport_bound_weak hPars hDer hRotM hSP hm hW hwb hv β,
    stretch_bound_weak hPars hDer hRotM hSP hm hW hwb hv β,
    vortTransport_bound_weak hPars hDer hRotM hSP hm hW hwb hv β,
    vortStretch_bound_weak hPars hDer hRotM hSP hm hW hwb hv β,
    rotation_bound_weak hPars hDer hRotM hSP hm hW hwb hv β, restTermWith_split hm hW hv β]
    with z b1 b2 b3 b4 b5 hsplit hN _hR
  obtain ⟨s1, i1⟩ := b1 hN
  obtain ⟨s2, i2⟩ := b2 hN
  obtain ⟨s3, i3⟩ := b3 hN
  obtain ⟨s4, i4⟩ := b4 hN
  obtain ⟨s5, i5⟩ := b5 hN
  have eR : ∑' ι, restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2
      = (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (transportPartWith (m.epsP β).frame W v) ι z.1 z.2)
        - (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (stretchPartWith W v) ι z.1 z.2)
        + (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (vortTransportPartWith HW v) ι z.1 z.2)
        - (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (vortStretchPartWith W v) ι z.1 z.2)
        + (∑' ι, modePart (m.epsP β).modes (m.epsP β).wt v (rotationPartWith (m.epsP β).frame v) ι z.1 z.2) := by
    rw [tsum_congr fun ι => hsplit ι, (((s1.sub s2).add s3).sub s4).tsum_add s5,
      ((s1.sub s2).add s3).tsum_sub s4, (s1.sub s2).tsum_add s3, s1.tsum_sub s2]
  have hwt0 : 0 ≤ (m.epsP β).wt z.2 := hm.eps_wt_nonneg β z.2
  set E1 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2) ι
  set E2 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2) (fun κ => vortAmp (gradField v) κ z.1 z.2) ι
  set E3 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α z.1 z.2) (fun κ => velAmp v κ z.1 z.2) ι
  set E4 : ℤ × ℤ → ℝ := fun ι => (m.epsP β).wt z.2 * vortAmp (gradField v) ι z.1 z.2
    * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι
  have hE : ∀ ι, -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2 = E1 ι + E2 ι + E3 ι + E4 ι := by
    intro ι
    unfold pieceEpsRestModeWith
    simp only [E1, E2, E3, E4]
    ring
  have n1 : ∀ ι, 0 ≤ E1 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n2 : ∀ ι, 0 ≤ E2 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n3 : ∀ ι, 0 ≤ E3 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have n4 : ∀ ι, 0 ≤ E4 ι := fun ι => mul_nonneg (mul_nonneg hwt0 (Real.sqrt_nonneg _))
    (edgeSum_nonneg_of _ _ _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _))
  have hR0 : ∀ ι, 0 ≤ -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2 := fun ι => by
    rw [hE]; linarith [n1 ι, n2 ι, n3 ι, n4 ι]
  have hAne : (∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.ne le_self_add
  have hBne : ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v) (secondDerivField v) β z.1 z.2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have sR : Summable (fun ι => -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2) := by
    have := ENNReal.summable_toReal hAne
    simpa only [ENNReal.toReal_ofReal (hR0 _)] using this
  have eA : (∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2)).toReal
      = ∑' ι, -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2 := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun ι => ENNReal.toReal_ofReal (hR0 ι)
  have t1 : Summable E1 := Summable.of_nonneg_of_le n1 (fun ι => by rw [hE ι]; linarith [n2 ι, n3 ι, n4 ι]) sR
  have t2 : Summable E2 := Summable.of_nonneg_of_le n2 (fun ι => by rw [hE ι]; linarith [n1 ι, n3 ι, n4 ι]) sR
  have t3 : Summable E3 := Summable.of_nonneg_of_le n3 (fun ι => by rw [hE ι]; linarith [n1 ι, n2 ι, n4 ι]) sR
  have t4 : Summable E4 := Summable.of_nonneg_of_le n4 (fun ι => by rw [hE ι]; linarith [n1 ι, n2 ι, n3 ι]) sR
  have eS : ∑' ι, -pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2
      = tsum E1 + tsum E2 + tsum E3 + tsum E4 := by
    rw [tsum_congr hE, ((t1.add t2).add t3).tsum_add t4, (t1.add t2).tsum_add t3, t1.tsum_add t2]
  have eN : (negSeriesWith m h W HW v β z.1 z.2).toReal
      = (∑' ι, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι z.1 z.2)).toReal
        + (ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v) (secondDerivField v) β z.1 z.2)).toReal := by
    unfold negSeriesWith
    exact ENNReal.toReal_add hAne hBne
  have hB : -blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v) (secondDerivField v) β z.1 z.2
      ≤ (ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v) (secondDerivField v) β z.1 z.2)).toReal := by
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  have eBlk : -blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v) (secondDerivField v) β z.1 z.2
      - gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
      = (m.epsP β).wt z.2 * frameSpeedSup W (m.epsP β).frame z.2
            * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp (secondDerivField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2)
        + (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
        + (m.epsP β).wt z.2 * |(m.epsP β).frame|
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2
        + (m.epsP β).wt z.2 * Internal.Minorant.vortGradSupLower HW z.2
            * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2)
        + (m.epsP β).wt z.2 * vortSup W z.2
            * pieceNorm (m.epsP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) := by
    unfold blockWithSup gradPart
    ring
  rw [eR]
  linarith [i1, i2, i3, i4, i5, eS, eN, hB, eBlk, eA]

theorem pointwise_lower_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure, posSeries m P v β z.1 z.2 < ⊤ → negSeriesWith m h W HW v β z.1 z.2 < ⊤ →
      Summable (fun ι : ℤ × ℤ => pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2) →
      Summable (fun ι : ℤ × ℤ => pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) →
      (posSeries m P v β z.1 z.2).toReal ≤
        (∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2)
          + (negSeriesWith m h W HW v β z.1 z.2).toReal
          - (gradPart (m.epsP β).modes (m.epsP β).wt v z.1 z.2
            + ∑' ι : ℤ × ℤ, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2) := by
  filter_upwards [compression_bound_weak hPars hDer hRotM hSP hm hW hwb hv β,
    pieceTerm_sub_weak hm hW hv β] with z hc hsub hA hN hs hl
  have hpos : ∀ ι, 0 ≤ pieceEpsPos m P (gradField v) β ι z.1 z.2 := fun ι => by
    unfold pieceEpsPos
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (hm.eps_wt_nonneg β z.2)) (abs_nonneg _)) (sq_nonneg _)
    exact ind_nonneg_of _
  have hAs : Summable (fun ι => pieceEpsPos m P (gradField v) β ι z.1 z.2) := by
    have := ENNReal.summable_toReal hA.ne
    simpa only [posSeries, ENNReal.toReal_ofReal (hpos _)] using this
  have eA : (posSeries m P v β z.1 z.2).toReal = ∑' ι, pieceEpsPos m P (gradField v) β ι z.1 z.2 := by
    unfold posSeries
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun ι => ENNReal.toReal_ofReal (hpos ι)
  have eT : ∀ ι, restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2
      = (pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2
        - pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2)
        - pieceEpsPos m P (gradField v) β ι z.1 z.2 := fun ι => by
    rw [hsub ι]; ring
  have hRs : Summable (fun ι =>
      restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2) := by
    simp_rw [eT]
    exact (hs.sub hl).sub hAs
  have hb := hc hN hRs
  have eS : (∑' ι, pieceTerm (m.epsP β).modes (m.epsP β).wt v (smoothRight P W v) ι z.1 z.2)
      - ∑' ι, pieceTerm (m.epsP β).modes (m.epsP β).wt v (negSumSecondPartials v) ι z.1 z.2
      = (∑' ι, pieceEpsPos m P (gradField v) β ι z.1 z.2)
        + ∑' ι, restTermWith (m.epsP β).modes (m.epsP β).wt (m.epsP β).frame W HW v ι z.1 z.2 := by
    rw [← hs.tsum_sub hl, ← hAs.tsum_add hRs]
    exact tsum_congr fun ι => hsub ι
  rw [eA]
  linarith

theorem core_of_weak_parts (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (hv : IsSmoothPerturbation P v) (β : Fin nE)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeriesWith m h W HW v β σ y) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y).toReal ≤
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeriesWith m h W HW v β σ y).toReal := by
  have hAm := posSeries_aemeasurable hSP hm hv β
  have hNm := negSeriesWith_aemeasurable hSP hm hW hv β
  obtain ⟨hFm, hFp, hF2⟩ := rightGradient_finite_weak hSP hW hv
  obtain ⟨hSs, hSi, hX⟩ := weakPairingExchange hPars hSP hm hv β hFm hFp hF2
  obtain ⟨hLs, hQi, hQ⟩ := weakSumSecondPartialsLower hPars hDer hSP hSsp hm hv β
  have eA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, posSeries m P v β σ y)
      = ∫⁻ z, posSeries m P v β z.1 z.2 ∂slabMeasure := (lintegral_prod _ hAm).symm
  have eN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, negSeriesWith m h W HW v β σ y)
      = ∫⁻ z, negSeriesWith m h W HW v β z.1 z.2 ∂slabMeasure := (lintegral_prod _ hNm).symm
  rw [eA] at hA
  rw [eN] at hN
  rw [eA, eN]
  refine core_of_parts hAm hNm hA hN hSi hX hQi hQ ?_
  filter_upwards [pointwise_lower_weak hPars hDer hRotM hSP hm hW hwb hv β, hSs, hLs,
    ae_lt_top' hAm hA.ne, ae_lt_top' hNm hN.ne] with z h3 hs hl ha hn
  exact h3 ha hn hs hl

end WeakCore

theorem core_inequality_measurable (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v)
          (secondDerivField v) β σ y))) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)).toReal ≤
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
            + ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v)
              (secondDerivField v) β σ y))).toReal := by
  exact core_of_weak_parts hPars hDer hRotM hSP hSsp hm hW hwb hv β hA hN

theorem core_inequality_weak (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y))) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)).toReal ≤
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
            + ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y))).toReal := by
  have hwt : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hle : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-blockWithSup m W (Internal.Minorant.vortGradSupLower HW) v (gradField v)
          (secondDerivField v) β σ y))) ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y))) :=
    lintegral_mono fun σ => lintegral_mono fun y => add_le_add le_rfl (by
      rw [pieceEpsBlockWith_eq_blockWithSup]
      exact neg_blockWithSup_mono m W v (gradField v) (secondDerivField v) β hwt
        (Internal.Minorant.vortGradSupLower_le HW) σ y)
  have hN' := lt_of_le_of_lt hle hN
  have key := core_inequality_measurable hPars hDer hRotM hSP hSsp m P h w W HW D hm hW hwb v hv β hA hN'
  have := ENNReal.toReal_mono hN.ne hle
  linarith

end Internal.ExtendedPieceEps

open Coercive Internal.ExtendedPieceEps in
theorem pieceEpsEstimateSmoothWeakHolds_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds) : PieceEpsEstimateSmoothWeakHolds := by
  intro C nE nM m P h w W HW D w₀ epsSup epsGradSup ratio hm hW hwb v hv β
  have hwt : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hA := posWith_finite hPars hDer hRotM hSP m P h w W HW hm v hv β
  have hN := negWith_finite hPars hSP m P h w W HW D hm hW v hv β
  exact splitBound_of_signs
    (fun σ y ι => restWith_nonpos m h W HW v (gradField v) (secondDerivField v) β hwt ι σ y)
    (fun σ y => blockWith_nonpos m W HW v (gradField v) (secondDerivField v) β hwt σ y) hA hN
    (core_inequality_weak hPars hDer hRotM hSP hSsp m P h w W HW D hm hW hwb v hv β hA hN)

end CoerciveWeak

end Breakdown
