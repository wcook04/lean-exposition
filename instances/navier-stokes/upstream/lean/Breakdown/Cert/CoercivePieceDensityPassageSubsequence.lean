import Breakdown.Cert.CoercivePieceDensityPassageRest
import Breakdown.Cert.CoerciveDensityPassageLiminf
import Breakdown.Cert.CoerciveSmoothDensityIntegrable
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoercivePieceDensityPassageSubsequenceModes
import Breakdown.Cert.CoercivePieceDensityPassageDiffBound

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageSubsequence

open PairingSplitInternal (periodMeasure)

theorem rest_abs_sub_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal |pieceRest m h w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y
          - pieceRest m h w W v G H ι σ y|) atTop (𝓝 0) := by
  obtain ⟨K, -, -, hb⟩ := PiecePassageDiffBound.rest_diff_bound hm hW hWdecay hwb v G H
  have hpn := fun n => hSP P (u n) (hu.1 n)
  exact PiecePassageModes.tendsto_of_absorb_bound (K := K)
    (fun n => DensityPassageRest.diffTot_aemeasurable (hpn n).measurable_velocity (hpn n).measurable_gradient
      (hpn n).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv)
    (DensityPassageRest.ampTot_aemeasurable hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv)
    (DensityPassageRest.ampTot_finite hPars hv hu) (DensityPassageRest.diffTot_tendsto hPars hSP hv hu)
    (fun t ht n σ y => hb t ht (u n) (gradField (u n)) (secondDerivField (u n)) σ y)

theorem block_abs_sub_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    Tendsto (fun n => periodLIntegral (fun σ y =>
        |pieceBlock m W (u n) (gradField (u n)) (secondDerivField (u n)) σ y - pieceBlock m W v G H σ y|)) atTop (𝓝 0) := by
  obtain ⟨K, -, -, hb'⟩ := PiecePassageDiffBound.block_diff_bound hm hW hWdecay v G H
  have hb : ∀ t : ℝ, 0 < t → ∀ (u' : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
      (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ENNReal.ofReal |pieceBlock m W u' Gu Hu σ y - pieceBlock m W v G H σ y|
        ≤ ENNReal.ofReal (K * (1 + 1 / t)) * DensityPassageRestBound.diffTotal u' Gu Hu v G H σ y
          + ENNReal.ofReal (K * t) * DensityPassageRestBound.ampTotal v G H σ y := by
    intro t ht u' Gu Hu σ y
    have e := hb' t ht u' Gu Hu σ y
    simp only [PiecePassageDiffBound.atOrigin] at e
    rwa [PiecePassageDiffBound.tsum_atOrigin_sub] at e
  unfold periodLIntegral
  have hpn := fun n => hSP P (u n) (hu.1 n)
  exact PiecePassageModes.tendsto_of_absorb_bound (K := K)
    (fun n => DensityPassageRest.diffTot_aemeasurable (hpn n).measurable_velocity (hpn n).measurable_gradient
      (hpn n).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv)
    (DensityPassageRest.ampTot_aemeasurable hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv)
    (DensityPassageRest.ampTot_finite hPars hv hu) (DensityPassageRest.diffTot_tendsto hPars hSP hv hu)
    (fun t ht n σ y => hb t ht (u n) (gradField (u n)) (secondDerivField (u n)) σ y)

theorem rest_negative_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (-pieceRest m h w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRest m h w W v G H ι σ y))) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hm' : ∀ n, AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal |pieceRest m h w W (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
        - pieceRest m h w W v G H ι z.1 z.2|) periodMeasure := fun n => by
    rw [PairingSplitInternal.periodMeasure_eq]
    refine (AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable (AEMeasurable.sub ?_ ?_))).restrict
    · exact (PieceDensityPassageMeasure.piece_parts_aemeasurable_of hm hW (hpn n).measurable_velocity
        (hpn n).measurable_gradient (hpn n).measurable_secondDeriv ι).2
    · exact (PieceDensityPassageMeasure.piece_parts_aemeasurable_of hm hW hv.measurable_velocity
        hv.measurable_gradient hv.measurable_secondDeriv ι).2
  exact (DensityPassage.tsum_negPart_tendsto
    (R := fun n σ y ι => pieceRest m h w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
    (R₀ := fun σ y ι => pieceRest m h w W v G H ι σ y) hm'
    (PieceDensityPassageRest.rest_abs_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv
      hWdecay hwb v G H g u hv hu)
    (rest_abs_sub_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
      v G H g u hv hu)).2

theorem block_negative_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (-pieceBlock m W (u n) (gradField (u n)) (secondDerivField (u n)) σ y)) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceBlock m W v G H σ y))) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hmn : ∀ n, AEMeasurable (fun z : ℝ × Space =>
      pieceBlock m W (u n) (gradField (u n)) (secondDerivField (u n)) z.1 z.2) periodMeasure := fun n => by
    rw [PairingSplitInternal.periodMeasure_eq]
    exact (PieceDensityPassageMeasure.pieceBlock_aemeasurable_of hm hW (hpn n).measurable_velocity
      (hpn n).measurable_gradient (hpn n).measurable_secondDeriv).restrict
  have hm0 : AEMeasurable (fun z : ℝ × Space => pieceBlock m W v G H z.1 z.2) periodMeasure := by
    rw [PairingSplitInternal.periodMeasure_eq]
    exact (PieceDensityPassageMeasure.pieceBlock_aemeasurable_of hm hW hv.measurable_velocity
      hv.measurable_gradient hv.measurable_secondDeriv).restrict
  exact (DensityPassage.negPart_tendsto hmn hm0
    (PieceDensityPassageRest.block_abs_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv
      hWdecay hwb v G H g u hv hu)
    (block_abs_sub_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
      v G H g u hv hu)).2

theorem stretchForm_aemeasurable (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    AEMeasurable (fun z : ℝ × Space => stretchForm W v G z.1 z.2) periodMeasure := by
  rw [PairingSplitInternal.periodMeasure_eq]
  exact (Internal.PieceAbsorb.aem_stretchForm hW hv.measurable_velocity hv.measurable_gradient).restrict

theorem pieces_converge_ae (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ ι, Tendsto (fun n => piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) atTop
        (𝓝 (piecePos m P v G ι σ y))) ∧
      (∀ ι, Tendsto (fun n => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
        atTop (𝓝 (pieceRest m h w W v G H ι σ y))) ∧
      Tendsto (fun n => stretchForm W (u (φ n)) (gradField (u (φ n))) σ y) atTop (𝓝 (stretchForm W v G σ y)) := by
  obtain ⟨φ, hφ, hae⟩ := PiecePassageModes.ae_subseq_modes hPars hSP hv hu
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  obtain ⟨hV, hG, hH, hu0, hg0⟩ := hy
  exact PiecePassageModes.piece_limits_of_modes m P h w W (U := fun n => u (φ n)) hV hG hH hu0 hg0

theorem splitLeft_block_eq (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) {Blk : ℝ → Space → ℝ} (J : ℝ → Space → ℝ)
    (hB : ∀ σ y, Blk σ y ≤ 0) (σ : ℝ) (y : Space) :
    splitLeft Pos Rest Blk J σ y = splitLeft Pos Rest (fun _ _ => 0) J σ y := by
  simp only [splitLeft, ENNReal.ofReal_of_nonpos (hB σ y), ENNReal.ofReal_zero]

theorem splitRight_split (Rest : ℝ → Space → ℤ × ℤ → ℝ) (Blk J : ℝ → Space → ℝ)
    (hR : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest z.1 z.2 ι)) periodMeasure)
    (hB : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-Blk z.1 z.2)) periodMeasure) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest Blk J σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y)) +
        ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) +
          ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-Blk σ y)) := by
  have e : ∀ σ y, splitRight Rest Blk J σ y =
      ENNReal.ofReal (-J σ y) + ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y)) :=
    fun σ y => by
      unfold splitRight
      rw [add_comm]
  simp only [e]
  rw [DensityPassage.iterated_lintegral_add_right _ (hR.add hB), DensityPassage.iterated_lintegral_add_right _ hB]

theorem subsequence_limits_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
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
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          splitRight (fun σ y ι => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlock m W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchForm W (u (φ n)) (gradField (u (φ n)))) σ y) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y) (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y)) ∧
      ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y, splitLeft (fun σ y ι => piecePos m P v G ι σ y) (fun σ y ι => pieceRest m h w W v G H ι σ y) (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y
        ≤ liminf (fun n => splitLeft (fun σ y ι => piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) (fun σ y ι => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlock m W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchForm W (u (φ n)) (gradField (u (φ n)))) σ y) atTop := by
  obtain ⟨φ, hφ, hae⟩ := pieces_converge_ae hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay
    hwb v G H g u hv hu
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hRm : ∀ (a : ℝ → Space → Space) (A : ℝ → Space → (Space →L[ℝ] Space))
      (B : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      AEStronglyMeasurable (fun z : ℝ × Space => a z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume →
      AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceRest m h w W a A B ι z.1 z.2))
        periodMeasure ∧
      AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-pieceBlock m W a A B z.1 z.2)) periodMeasure :=
    fun a A B ha hA hB => by
      rw [PairingSplitInternal.periodMeasure_eq]
      exact ⟨(AEMeasurable.ennreal_tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
          (PieceDensityPassageMeasure.piece_parts_aemeasurable_of hm hW ha hA hB ι).2.neg).restrict,
        (ENNReal.measurable_ofReal.comp_aemeasurable
          (PieceDensityPassageMeasure.pieceBlock_aemeasurable_of hm hW ha hA hB).neg).restrict⟩
  have hv0 := hRm v G H hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv
  have hn := fun n => hRm (u n) (gradField (u n)) (secondDerivField (u n)) (hpn n).measurable_velocity
    (hpn n).measurable_gradient (hpn n).measurable_secondDeriv
  have hJm : ∀ n, AEMeasurable (fun z : ℝ × Space => stretchForm W (u n) (gradField (u n)) z.1 z.2) periodMeasure :=
    fun n => (Internal.SmoothDensity.stretch_integrable (hu.1 n) hW hWdecay).aestronglyMeasurable.aemeasurable
  have hJ := (DensityPassage.negPart_tendsto hJm
    (stretchForm_aemeasurable hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
      v G H g u hv hu)
    (PassageCommon.stretchForm_finite hv hWdecay (PassageLimit.weightedVelocity_lt_top hv hu))
    (PassageCommon.stretchForm_tendsto hSP hv hu hWdecay)).2
  have hR := rest_negative_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
    v G H g u hv hu
  have hB := block_negative_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
    v G H g u hv hu
  have hall : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      splitRight (fun σ y ι => pieceRest m h w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y)
        (fun σ y => pieceBlock m W (u n) (gradField (u n)) (secondDerivField (u n)) σ y)
        (stretchForm W (u n) (gradField (u n))) σ y) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y)
        (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y)) := by
    rw [splitRight_split _ _ _ hv0.1 hv0.2]
    refine (hJ.add (hR.add hB)).congr fun n => ?_
    exact (splitRight_split _ _ _ (hn n).1 (hn n).2).symm
  refine ⟨φ, hφ, hall.comp hφ.tendsto_atTop, ?_⟩
  filter_upwards [hae] with σ hσ
  filter_upwards [hσ] with y hy
  obtain ⟨hp, hr, hj⟩ := hy
  rw [splitLeft_block_eq _ _ _ (fun σ y => PieceDensityPassageMeasure.pieceBlock_nonpos hm.eps_wt_nonneg
    hm.mu_wt_nonneg _ _ σ y)]
  simp only [splitLeft_block_eq _ _ _ (fun σ y => PieceDensityPassageMeasure.pieceBlock_nonpos hm.eps_wt_nonneg
    hm.mu_wt_nonneg _ _ σ y)]
  exact DensityPassage.splitLeft_le_liminf (Pos := fun n σ y ι => piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y)
    (Rest := fun n σ y ι => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
    (J := fun n => stretchForm W (u (φ n)) (gradField (u (φ n)))) hp hr hj

end Internal.PieceDensityPassageSubsequence

end Coercive

end Breakdown
