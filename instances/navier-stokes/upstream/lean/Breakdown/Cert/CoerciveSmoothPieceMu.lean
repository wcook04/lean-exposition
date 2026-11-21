import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveSmoothPressure
import Breakdown.Cert.CoerciveSmoothPiecePairingSplit
import Breakdown.Cert.CoerciveSmoothPieceMuSeminorm
import Breakdown.Cert.CoerciveSmoothPieceMuNeg
import Breakdown.Cert.CoerciveSmoothPieceMuReflect
import Breakdown.Cert.CoerciveSmoothPieceMuTransport

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMu

private theorem ind_nonneg' (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

open Classical in
private theorem edgeSum_nonneg (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ)
    (hX : ∀ β, 0 ≤ X β) (hg : ∀ κ, 0 ≤ g κ) (ι : ℤ × ℤ) : 0 ≤ edgeSum h T X g ι := by
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg (hX β) (hg _)]
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg (hX β) (hg _)]
  · exact le_rfl

private theorem frameSpeedSup_nonneg (W : ℝ → Space → Space) (a : ℝ) (y : Space) :
    0 ≤ frameSpeedSup W a y :=
  Real.iSup_nonneg fun _ => norm_nonneg _

private theorem pieceNorm_nonneg (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) : 0 ≤ pieceNorm T g :=
  Real.sqrt_nonneg _

private theorem splitLowerBound_of_nonpos (X : ℝ) (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ)
    (Blk : ℝ → Space → ℝ) (hR : ∀ σ y ι, Rest σ y ι ≤ 0) (hB : ∀ σ y, Blk σ y ≤ 0)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))) < ⊤)
    (hX : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)).toReal
      ≤ X + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))).toReal) :
    IsSplitLowerBound X Pos Rest Blk (fun _ _ => 0) := by
  have hR' : ∀ σ y ι, ENNReal.ofReal (Rest σ y ι) = 0 := fun σ y ι => ENNReal.ofReal_of_nonpos (hR σ y ι)
  have hB' : ∀ σ y, ENNReal.ofReal (Blk σ y) = 0 := fun σ y => ENNReal.ofReal_of_nonpos (hB σ y)
  refine ⟨by simpa using hN, ?_⟩
  simp only [hR', hB', tsum_zero, add_zero, neg_zero, ENNReal.ofReal_zero]
  rw [← ENNReal.ofReal_toReal hA.ne, ← ENNReal.ofReal_toReal hN.ne]
  rcases le_total 0 X with hX0 | hX0
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero,
      ← ENNReal.ofReal_add hX0 ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hX
  · rw [ENNReal.ofReal_of_nonpos hX0, zero_add,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith : 0 ≤ -X)]
    exact ENNReal.ofReal_le_ofReal (by linarith)


private theorem seminorm_eq {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) :
    pieceSeminormPart m P β v = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  have hpt : ∀ ι σ y, |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
      * (m.muP β).wt y * cnormSq (modeVel ι v σ y) = ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2 := by
    intro ι σ y
    have hs : |PieceWeights.sgn (m.muP β).modes ι| = ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
      unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
      by_cases h1 : ι ∈ (m.muP β).modes <;> by_cases h2 : -ι ∈ (m.muP β).modes <;> simp [h1, h2]
    have hc : velAmp v ι σ y ^ 2 = cnormSq (modeVel ι v σ y) :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hs, hc]
    ring
  unfold pieceSeminormPart
  simp only [hpt]
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ≪ (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      Measure.AbsolutelyContinuous.rfl
  have hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume :=
    hv.smooth.continuous.aestronglyMeasurable
  have hcn : Continuous (fun x : Fin 3 → ℂ => cnormSq x) :=
    continuous_finsetSum _ fun b _ => (continuous_norm.comp (continuous_apply b)).pow 2
  have hF : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt z.2
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι z.1 z.2 ^ 2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    intro ι
    have h1 : AEMeasurable (fun z : ℝ × Space => velAmp v ι z.1 z.2) volume :=
      Real.continuous_sqrt.measurable.comp_aemeasurable (hcn.measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun i => (Internal.FieldModes.aestronglyMeasurable_modeVel hvm ι i).aemeasurable))
    have h2 : Measurable (fun z : ℝ × Space => (m.muP β).wt z.2) := hK.continuous.measurable.comp measurable_snd
    have h3 : AEMeasurable (fun z : ℝ × Space => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt z.2
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι z.1 z.2 ^ 2) volume :=
      ((aemeasurable_const.mul h2.aemeasurable).mul aemeasurable_const).mul (h1.pow_const 2)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h3).mono_ac hac
  symm
  rw [show (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2)) = ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt z.2
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι z.1 z.2 ^ 2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) from
      (lintegral_prod _ (AEMeasurable.tsum hF)).symm, lintegral_tsum hF]
  exact tsum_congr fun ι => lintegral_prod _ (hF ι)

private theorem pairing_additive {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds)
    (Q : ℝ → Space → Space) (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) (Y : ℝ → Space → Space)
    (hYm : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) (hYp : IsTimePeriodic Y)
    (hY2 : periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤)
    (hSm : AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume)
    (hSp : IsTimePeriodic (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)))
    (hS2 : periodLIntegral (fun σ y => ‖smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤)
    (hae : ∀ᵐ z : ℝ × Space, Q z.1 z.2 =
      (smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) + Y z.1 z.2) :
    muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q = muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) + muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Y := by
  obtain ⟨B, hB⟩ := Internal.SmoothPieceSplit.muWt_bound hm
  have hB' : ∀ ι y, |Internal.SmoothPieceSplit.muWt m β ι y| ≤ B := hB β
  have hwm := Internal.SmoothPieceSplit.muWt_measurable hm β
  have hU := Internal.SmoothWeightSplit.scaledField_square hv
  have hSs : ModeL2Internal.IsSquareField (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) := ⟨hSm, hSp, hS2⟩
  have hYs : ModeL2Internal.IsSquareField Y := ⟨hYm, hYp, hY2⟩
  have e : ∀ X : ℝ → Space → Space, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v X
      = ∑' ι, ModeL2Internal.weightedModeTerm (Internal.SmoothPieceSplit.muWt m β)
        (Internal.SmoothWeightSplit.scaledField v) X ι :=
    fun X => Internal.SmoothPieceSplit.muPairing_eq_scaled _ v X
  obtain ⟨K, hK⟩ := ModeL2Internal.weightedMode_bound hPars (Internal.SmoothPieceSplit.muWt m β) hwm hB' hU
  have hsS := (hK _ _ hSs hSs).1
  have hsY := (hK _ _ hYs hYs).1
  rw [e Q, e, e Y, ← hsS.tsum_add hsY]
  refine tsum_congr fun ι => ?_
  exact modeTerm_add_of_ae (Internal.SmoothPieceSplit.muWt m β ι) (Internal.SmoothWeightSplit.scaledField v) Q
    (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) Y ι
    (modeVel_add_ae (X := fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) (Y := Y) (Z := Q) hPars
      hSm hSp hS2 hYm hYp hY2 hQ.1 hQ.2.1 hQ.2.2.1 hae ι)
    (ModeL2Internal.integrable_weightedMode hPars _ hwm hB' hU hSs ι)
    (ModeL2Internal.integrable_weightedMode hPars _ hwm hB' hU hYs ι)

private theorem pressure_bound {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    (Q : ℝ → Space → Space) (hQ : IsSolenoidalPartOf (smoothRight P W v) Q)
    (hPr : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) < ⊤) :
    muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))).toReal ≤ muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q := by
  obtain ⟨hFm, hFp, hF2, hSm, hSp, hS2, Q', hQ', hae⟩ :=
    solenoidal_split_smooth hSolenoidal P W hW hWp hWdiv hWdecay v hv Q hQ
  obtain ⟨hYm, hYp, hY2, hYmodes⟩ :=
    solenoidal_reflection_modes hPars hSolenoidal (fun σ y => fderiv ℝ (W σ) y (v σ y)) Q' hFm hFp hF2 hQ'
  have hadd := pairing_additive m P h w W hm v hv β hPars
    Q hQ _ hYm hYp hY2 hSm hSp hS2 hae
  have hb := Internal.SmoothPieceMuReflect.reflected_pairing_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP
    hSsp _ hYm hYp hY2 hYmodes hPr
  linarith

end Internal.SmoothPieceMu

open Internal.SmoothPieceMu in
theorem pieceMuEstimateSmoothHolds_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds) : PieceMuEstimateSmoothHolds := by
  intro C nE nM m P h w W w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb v hv Q hQ β
  have hcμ : 0 ≤ 1 - m.cμ := by linarith [hm.cμ_lt_one]
  have hη : 0 < (m.muP β).eta := hm.mu_eta_pos β
  have hφ : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hvel : ∀ (X : ℝ → Space → Space) ι σ y, 0 ≤ velAmp X ι σ y := fun _ _ _ _ => Real.sqrt_nonneg _
  have hgr : ∀ (G : ℝ → Space → (Space →L[ℝ] Space)) ι σ y, 0 ≤ gradAmp G ι σ y :=
    fun _ _ _ _ => Real.sqrt_nonneg _
  have hE0 : ∀ σ y ι, 0 ≤ (m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := fun σ y ι =>
    mul_nonneg (mul_nonneg (hφ y) (hvel _ _ _ _))
      (edgeSum_nonneg _ _ _ _ (fun _ => hvel _ _ _ _) (fun _ => hgr _ _ _ _) ι)
  have hP0 : ∀ σ y ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2) := fun σ y ι =>
    mul_nonneg (ind_nonneg' _) (add_nonneg (div_nonneg (sq_nonneg _) (by linarith))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη.le) (sq_nonneg _)) (sq_nonneg _)))
  have hRestEq : ∀ σ y ι, -pieceMuRestMode m h W v (gradField v) β ι σ y = (m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι + ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2) := by
    intro σ y ι
    unfold pieceMuRestMode
    ring
  have hR : ∀ σ y ι, pieceMuRestMode m h W v (gradField v) β ι σ y ≤ 0 := by
    intro σ y ι
    have := hRestEq σ y ι
    linarith [hE0 σ y ι, hP0 σ y ι]
  have hB : ∀ σ y, pieceMuBlock m W v (gradField v) β σ y ≤ 0 := by
    intro σ y
    unfold pieceMuBlock
    have h1 := hφ y
    have h2 := frameSpeedSup_nonneg W (m.muP β).frame y
    have h3 : 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := norm_nonneg _
    have h4 := pieceNorm_nonneg (m.muP β).modes (fun κ => gradAmp (gradField v) κ σ y)
    have h5 := pieceNorm_nonneg (m.muP β).modes (fun κ => velAmp v κ σ y)
    have e1 := mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg h1 h2) h3) h4) h5
    have e2 := mul_nonneg (mul_nonneg h1 (abs_nonneg (m.muP β).frame))
      (sq_nonneg (pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)))
    linarith
  have hPosEq : ∀ σ y ι, ENNReal.ofReal (pieceMuPos m P v β ι σ y)
      = ENNReal.ofReal (1 - m.cμ) * ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2) := by
    intro σ y ι
    rw [← ENNReal.ofReal_mul hcμ]
    congr 1
    unfold pieceMuPos
    ring
  have hA : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (pieceMuPos m P v β ι σ y)
      = ENNReal.ofReal (1 - m.cμ) * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2)) := by
    simp only [hPosEq, ENNReal.tsum_mul_left]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext σ
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hNeq : ∀ σ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι σ y))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y))
      = (∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)) + (∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y) := by
    intro σ y
    rw [← ENNReal.tsum_add]
    congr 1
    refine tsum_congr fun ι => ?_
    rw [hRestEq, ENNReal.ofReal_add (hE0 σ y ι) (hP0 σ y ι)]
  have hsup : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)) ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceMuRestMode m h W v (gradField v) β ι σ y))
        + ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y))) := by
    refine ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)).trans ?_
    refine lintegral_mono fun σ => ?_
    refine ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)).trans ?_
    exact le_of_eq (lintegral_congr fun y => (hNeq σ y).symm)
  have hN := Internal.SmoothPieceMuNeg.negPart_finite m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hSem := seminorm_eq m P h w W hm v hv β
  have hSemF := Internal.SmoothPieceMuSeminorm.seminorm_finite m P h w W hm v hv β hPars hDer hRotM hSP
  rw [hSem] at hSemF
  have hEf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)) < ⊤ := ((le_self_add.trans le_self_add).trans hsup).trans_lt hN
  have hPf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) < ⊤ := ((le_add_self.trans le_self_add).trans hsup).trans_lt hN
  have hPr := pressure_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp Q hQ hPf
  have hBf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)) < ⊤ := (le_add_self.trans hsup).trans_lt hN
  have hTr := Internal.SmoothPieceMuTransport.transport_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp hSemF hEf hBf
  have hsum := ENNReal.toReal_mono hN.ne hsup
  rw [ENNReal.toReal_add (ENNReal.add_lt_top.2 ⟨hEf, hPf⟩).ne hBf.ne,
    ENNReal.toReal_add hEf.ne hPf.ne] at hsum
  refine splitLowerBound_of_nonpos _ _ _ _ hR hB ?_ hN ?_
  · rw [hA]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSemF
  · rw [hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcμ, hSem]
    nlinarith [hm.cμ_pos]

end Coercive

end Breakdown
