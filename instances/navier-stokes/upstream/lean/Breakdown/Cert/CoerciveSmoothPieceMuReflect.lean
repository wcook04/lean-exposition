import Breakdown.Cert.CoerciveSmoothPiecePairingSplit
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveSmoothMuMeasure
import Breakdown.Cert.CoerciveSmoothPieceMuHarmonics

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuReflect

open ModeL2Internal (IsSquareField weightedModeTerm slab)

theorem cnormSq_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (Internal.SmoothWeightSplit.scaledField v) σ y) = (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
  have hr : 0 < 1 + ‖y‖ := by positivity
  have hc : velAmp v ι σ y ^ 2 = cnormSq (modeVel ι v σ y) :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [div_pow, hc]
  unfold cnormSq
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Internal.SmoothWeightSplit.modeVel_scaled, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr), inv_pow]
  ring

theorem pointwise_absorb {s d φ r η vel : ℝ} (x z : Fin 3 → ℂ) (hsd : |s| = d) (hd : d = 0 ∨ d = 1)
    (hφ : 0 ≤ φ) (hr : 0 < r) (hη : 0 < η) (hx : cnormSq x = (vel / r) ^ 2) :
    -(Complex.I * ((s * φ * r : ℝ) : ℂ) * cdot x z).re
      ≤ d * (cnormSq z / (2 * η) + (1 / 2) * η * φ ^ 2 * vel ^ 2) := by
  have hz0 : 0 ≤ cnormSq z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : |(Complex.I * ((s * φ * r : ℝ) : ℂ) * cdot x z).re| ≤ |s * φ * r| * ‖cdot x z‖ :=
    Internal.FieldModes.abs_re_I_mul_le _ _
  have hab : |s * φ * r| = d * (φ * r) := by
    rw [abs_mul, abs_mul, hsd, abs_of_nonneg hφ, abs_of_pos hr]
    ring
  rw [hab] at hb
  rcases hd with hd | hd
  · subst hd
    have : |(Complex.I * ((s * φ * r : ℝ) : ℂ) * cdot x z).re| ≤ 0 := by simpa using hb
    have h2 := neg_abs_le (Complex.I * ((s * φ * r : ℝ) : ℂ) * cdot x z).re
    simp only [zero_mul]
    linarith
  · subst hd
    rcases hφ.eq_or_lt with h0 | hpos
    · subst h0
      simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.zero_re, neg_zero]
      exact mul_nonneg zero_le_one (add_nonneg (div_nonneg hz0 (by linarith)) (by positivity))
    · have ht : 0 < η * (φ * r) := by positivity
      have hc := ModeL2Internal.norm_cdot_le x z ht
      have h2 := neg_abs_le (Complex.I * ((s * φ * r : ℝ) : ℂ) * cdot x z).re
      have h3 : 1 * (φ * r) * ‖cdot x z‖ ≤ (φ * r) * ((η * (φ * r) * cnormSq x + cnormSq z / (η * (φ * r))) / 2) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      have h4 : (φ * r) * ((η * (φ * r) * cnormSq x + cnormSq z / (η * (φ * r))) / 2)
          = 1 * (cnormSq z / (2 * η) + (1 / 2) * η * φ ^ 2 * vel ^ 2) := by
        rw [hx]
        field_simp
        ring
      linarith

private def pressDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (β : Fin nM) (ι : ℤ × ℤ) (z : ℝ × Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
    * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2 / (2 * (m.muP β).eta)
      + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)

private def reflDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (v Y : ℝ → Space → Space) (β : Fin nM) (ι : ℤ × ℤ) (z : ℝ × Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
    * (cnormSq (modeVel ι Y z.1 z.2) / (2 * (m.muP β).eta)
      + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)

theorem ind_cases (p : Prop) : ModeWeights.ind p = 0 ∨ ModeWeights.ind p = 1 := by
  unfold ModeWeights.ind
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem abs_sgn (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T <;> by_cases h2 : -ι ∈ T <;> simp [h1, h2]

theorem ofReal_split (d a b c : ℝ) (hd : 0 ≤ d) (ha : 0 ≤ a) (hc : 0 < c) (hb : 0 ≤ b) :
    ENNReal.ofReal (d * (a / c + b)) = ENNReal.ofReal (d / c) * ENNReal.ofReal a + ENNReal.ofReal (d * b) := by
  rw [← ENNReal.ofReal_mul (div_nonneg hd hc.le), ← ENNReal.ofReal_add (mul_nonneg (div_nonneg hd hc.le) ha)
    (mul_nonneg hd hb)]
  congr 1
  ring

theorem reflected_pairing_bound {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (_hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (_hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (_hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM) (hPars : ModeSquareSumHolds) (_hDer : ModeDerivativeHolds) (_hRotM : ModeRotationHolds)
    (_hSolenoidal : SolenoidalModeHolds) (_hSP : SmoothPerturbationIsPerturbationHolds)
    (_hSsp : WeightedSumSecondPartialsPairingHolds) (Y : ℝ → Space → Space)
    (hYm : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) (hYp : IsTimePeriodic Y)
    (hY2 : periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤)
    (hYmodes : ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Y σ y)))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)))
    (hPr : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) < ⊤) :
    -(∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))).toReal ≤ muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Y := by
  have hη : 0 < (m.muP β).eta := hm.mu_eta_pos β
  have hη2 : 0 < 2 * (m.muP β).eta := by linarith
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  obtain ⟨Kl, hKl⟩ := hm.mu_increment β
  have hφc : Continuous (m.muP β).wt := hKl.continuous
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGc : Continuous (fun z : ℝ × Space => gradField W z.1 z.2) :=
    Internal.PieceAbsorb.continuous_fderiv_slice hW
  have hFc : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    (Internal.PieceAbsorb.continuous_fderiv_slice hW).clm_apply hvc
  obtain ⟨B, hB⟩ := Internal.SmoothPieceSplit.muWt_bound hm
  have hB' : ∀ ι y, |Internal.SmoothPieceSplit.muWt m β ι y| ≤ B := hB β
  have hwm := Internal.SmoothPieceSplit.muWt_measurable hm β
  have hU := Internal.SmoothWeightSplit.scaledField_square hv
  have hYs : IsSquareField Y := ⟨hYm, hYp, hY2⟩
  obtain ⟨K, hK⟩ := ModeL2Internal.weightedMode_bound hPars (Internal.SmoothPieceSplit.muWt m β) hwm hB' hU
  have hsY := (hK _ _ hYs hYs).1
  have e : muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Y
      = ∑' ι, weightedModeTerm (Internal.SmoothPieceSplit.muWt m β)
        (Internal.SmoothWeightSplit.scaledField v) Y ι :=
    Internal.SmoothPieceSplit.muPairing_eq_scaled _ v Y
  have hqc : ∀ ι, Continuous (pressDensity m h W v β ι) := by
    intro ι
    unfold pressDensity
    refine continuous_const.mul (((continuous_finsetSum _ fun α _ =>
      (Internal.MuSmooth.continuous_gradAmp hGc α).mul (Internal.MuSmooth.continuous_velAmp hvc (ι - α))).pow 2).div_const _
        |>.add (((continuous_const.mul ((hφc.comp continuous_snd).pow 2)).mul
          ((Internal.MuSmooth.continuous_velAmp hvc ι).pow 2))))
  have hqm : ∀ ι, AEMeasurable (fun z => ENNReal.ofReal (pressDensity m h W v β ι z)) slab :=
    fun ι => (ENNReal.measurable_ofReal.comp (hqc ι).measurable).aemeasurable
  have hPrEq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
          + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) = ∑' ι, ∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab := by
    rw [← lintegral_tsum hqm]
    exact (lintegral_prod _ (AEMeasurable.tsum hqm)).symm
  rw [hPrEq] at hPr ⊢
  have hQt : ∀ ι, ∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hPr.ne (ENNReal.le_tsum ι)
  have hterm : ∀ ι, -weightedModeTerm (Internal.SmoothPieceSplit.muWt m β)
      (Internal.SmoothWeightSplit.scaledField v) Y ι
        ≤ (∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab).toReal := by
    intro ι
    have hint := ModeL2Internal.integrable_weightedMode hPars _ hwm hB' hU hYs ι
    rw [ModeL2Internal.weightedModeTerm_eq hPars _ hwm hB' hU hYs ι, ← integral_neg]
    have h1 : ∫ z, -(Complex.I * (Internal.SmoothPieceSplit.muWt m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂slab
        ≤ (∫⁻ z, ENNReal.ofReal (-(Complex.I * (Internal.SmoothPieceSplit.muWt m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) ∂slab).toReal := by
      have hn : Integrable (fun z : ℝ × Space => -(Complex.I * (Internal.SmoothPieceSplit.muWt m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) slab :=
        hint.neg
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hn]
      linarith [@ENNReal.toReal_nonneg (∫⁻ z, ENNReal.ofReal (- -(Complex.I * (Internal.SmoothPieceSplit.muWt m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re) ∂slab)]
    refine h1.trans (ENNReal.toReal_mono (hQt ι) ?_)
    have hd0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
      rcases ind_cases (PieceWeights.inPiece (m.muP β).modes ι) with h | h <;> simp [h]
    have hb0 : ∀ z : ℝ × Space, 0 ≤ (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2 :=
      fun z => by positivity
    have hpt : ∀ z : ℝ × Space, ENNReal.ofReal (-(Complex.I * (Internal.SmoothPieceSplit.muWt m β ι z.2 : ℂ)
          * cdot (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)).re)
        ≤ ENNReal.ofReal (reflDensity m v Y β ι z) := by
      intro z
      apply ENNReal.ofReal_le_ofReal
      exact pointwise_absorb (modeVel ι (Internal.SmoothWeightSplit.scaledField v) z.1 z.2) (modeVel ι Y z.1 z.2)
        (abs_sgn _ ι) (ind_cases _) (hφ0 z.2) (by positivity) hη
        (cnormSq_scaled v ι z.1 z.2)
    have hYa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2))) slab :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (ModeL2Internal.aestronglyMeasurable_cnormSq
        (fun i => Internal.FieldModes.aestronglyMeasurable_modeVel hYm ι i)).aemeasurable).mono_ac ModeL2Internal.slab_ac
    have hFa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι
        (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2))) slab :=
      (ENNReal.measurable_ofReal.comp (Internal.MuSmooth.continuous_cnormSq_modeVel hFc ι).measurable).aemeasurable
    have hSc : Continuous (fun z : ℝ × Space => (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
        * velAmp v (ι - α) z.1 z.2) ^ 2) :=
      (continuous_finsetSum _ fun α _ =>
        (Internal.MuSmooth.continuous_gradAmp hGc α).mul (Internal.MuSmooth.continuous_velAmp hvc (ι - α))).pow 2
    have hSa : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
        * velAmp v (ι - α) z.1 z.2) ^ 2)) slab :=
      (ENNReal.measurable_ofReal.comp hSc.measurable).aemeasurable
    have hYF : ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab
        = ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)) ∂slab := by
      calc ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab
          = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι Y σ y)) := lintegral_prod _ hYa
        _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι
            (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)) := hYmodes ι
        _ = _ := (lintegral_prod _ hFa).symm
    have hFS : ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)) ∂slab
        ≤ ∫⁻ z, ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
          * velAmp v (ι - α) z.1 z.2) ^ 2) ∂slab := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have hs := Internal.SmoothPieceMuHarmonics.stretch_mode_le m P h w W hm hW hWp v hvc ι z.1 z.2
      have e2 : cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) z.1 z.2)
          = velAmp (fun σ y => fderiv ℝ (W σ) y (v σ y)) ι z.1 z.2 ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      rw [e2]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    have e1 : ∀ z : ℝ × Space, ENNReal.ofReal (reflDensity m v Y β ι z)
        = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2))
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) := fun z =>
      ofReal_split _ _ _ _ hd0 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hη2 (hb0 z)
    have e2 : ∀ z : ℝ × Space, ENNReal.ofReal (pressDensity m h W v β ι z)
        = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) := fun z =>
      ofReal_split _ _ _ _ hd0 (sq_nonneg _) hη2 (hb0 z)
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (reflDensity m v Y β ι z) ∂slab := lintegral_mono hpt
      _ = _ := lintegral_congr fun z => e1 z
      _ = ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * (∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι Y z.1 z.2)) ∂slab)
          + ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) ∂slab := by
          rw [lintegral_add_left' (hYa.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) / (2 * (m.muP β).eta))
            * (∫⁻ z, ENNReal.ofReal ((∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2
              * velAmp v (ι - α) z.1 z.2) ^ 2) ∂slab)
          + ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2)) ∂slab := by
          rw [hYF]
          gcongr
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' (hSa.const_mul _)]
          exact lintegral_congr fun z => (e2 z).symm
  have hsQ : Summable (fun ι => (∫⁻ z, ENNReal.ofReal (pressDensity m h W v β ι z) ∂slab).toReal) :=
    ENNReal.summable_toReal hPr.ne
  rw [ENNReal.tsum_toReal_eq hQt, e]
  have hle := hsY.neg.tsum_le_tsum hterm hsQ
  rw [tsum_neg] at hle
  linarith

end Internal.SmoothPieceMuReflect

end Coercive

end Breakdown
