import Breakdown.Cert.CoercivePieceDensityPassageMeasurable
import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.CoerciveDensityPassageNegative
import Breakdown.Cert.CoercivePieceDensityPassageRestSum

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageRest

open PairingSplitInternal (periodMeasure)

theorem rest_abs_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal |pieceRest m h w W v G H ι σ y|) < ⊤ := by
  obtain ⟨K, hK, hb⟩ := PieceDensityPassageRestSum.rest_tsum_le m P h w W hm hWdecay hwb
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal |pieceRest m h w W v G H ι σ y|)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * DensityPassageRest.ampTot v G H σ y :=
        lintegral_mono fun σ => lintegral_mono fun y => hb v G H σ y
    _ = K * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, DensityPassageRest.ampTot v G H σ y := by
        rw [← lintegral_const_mul' _ _ hK]
        refine lintegral_congr fun σ => ?_
        rw [← lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) (DensityPassageRest.ampTot_finite hPars hv hu)

theorem block_abs_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    periodLIntegral (fun σ y => |pieceBlock m W v G H σ y|) < ⊤ := by
  obtain ⟨K, hK, hb⟩ := PieceDensityPassageRestSum.block_le m P h w W hm hW hWdecay
  unfold periodLIntegral
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal |pieceBlock m W v G H σ y|)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * DensityPassageRest.ampTot v G H σ y :=
        lintegral_mono fun σ => lintegral_mono fun y => hb v G H σ y
    _ = K * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, DensityPassageRest.ampTot v G H σ y := by
        rw [← lintegral_const_mul' _ _ hK]
        refine lintegral_congr fun σ => ?_
        rw [← lintegral_const_mul' _ _ hK]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) (DensityPassageRest.ampTot_finite hPars hv hu)

theorem rest_negative_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRest m h w W v G H ι σ y)) < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.tsum_le_tsum fun ι =>
    ENNReal.ofReal_le_ofReal (neg_le_abs _))
    (rest_abs_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb v G H g u hv hu)

theorem block_negative_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceBlock m W v G H σ y)) < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (neg_le_abs _))
    (block_abs_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb v G H g u hv hu)

theorem right_finite_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y)
      (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y) < ⊤ := by
  have hR := rest_negative_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
    v G H g u hv hu
  have hB := block_negative_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
    v G H g u hv hu
  have hJ := PassageCommon.stretchForm_finite hv hWdecay (PassageLimit.weightedVelocity_lt_top hv hu)
  have hJ' : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-stretchForm W v G σ y)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (neg_le_abs _)) hJ
  have hRm : AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRest m h w W v G H ι z.1 z.2)) periodMeasure := by
    rw [PairingSplitInternal.periodMeasure_eq]
    exact (AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (PieceDensityPassageMeasure.piece_parts_aemeasurable_of hm hW hv.measurable_velocity
        hv.measurable_gradient hv.measurable_secondDeriv ι).2.neg).restrict
  have hBm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-pieceBlock m W v G H z.1 z.2)) periodMeasure := by
    rw [PairingSplitInternal.periodMeasure_eq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (PieceDensityPassageMeasure.pieceBlock_aemeasurable_of hm hW hv.measurable_velocity
        hv.measurable_gradient hv.measurable_secondDeriv).neg).restrict
  have e : ∀ σ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y)
      (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y =
        ENNReal.ofReal (-stretchForm W v G σ y) + ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRest m h w W v G H ι σ y))
          + ENNReal.ofReal (-pieceBlock m W v G H σ y)) := fun σ y => by
    unfold splitRight
    rw [add_comm]
  simp only [e]
  rw [DensityPassage.iterated_lintegral_add_right _ (hRm.add hBm),
    DensityPassage.iterated_lintegral_add_right _ hBm]
  exact ENNReal.add_lt_top.2 ⟨hJ', ENNReal.add_lt_top.2 ⟨hR, hB⟩⟩

end Internal.PieceDensityPassageRest

end Coercive

end Breakdown
