import Breakdown.CertCell.ActuatorPairingGradientDensity

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.ActuatorPairingGradient

open Coercive.ModeL2Internal

theorem iter_congr_ae {f g : ℝ → Space → ℝ} (h : ∀ᵐ z : ℝ × Space, f z.1 z.2 = g z.1 z.2) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, g σ y := by
  rw [Measure.volume_eq_prod] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  exact integral_congr_ae (ae_restrict_of_ae (h2.mono fun σ hσ => integral_congr_ae hσ))

variable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}

theorem scaled_square (hv : IsPerturbation Γ P v G H g) :
    IsSquareField (Coercive.Internal.SmoothWeightSplit.scaledField v) := by
  refine ⟨?_, fun σ y => ?_, ?_⟩
  · have hi : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖)⁻¹) :=
      Continuous.inv₀ (by fun_prop) (fun z => by positivity)
    exact hi.aestronglyMeasurable.smul hv.measurable_velocity
  · simp only [Coercive.Internal.SmoothWeightSplit.scaledField, hv.periodic_velocity σ y]
  · refine lt_of_le_of_lt (le_of_eq ?_) (Coercive.Internal.SmoothApprox.weightedField_sq_lt_top hv)
    unfold periodLIntegral Coercive.Internal.SmoothWeightSplit.scaledField
      Coercive.Internal.SmoothApprox.weightedField
    simp only [one_div]

theorem curlG_square (hv : IsPerturbation Γ P v G H g) : IsSquareField (fun σ y => curlVec (G σ y)) :=
  ⟨Coercive.Internal.CurlEnergy.continuous_curlVec.comp_aestronglyMeasurable hv.measurable_gradient,
    fun σ y => by simp only [hv.periodic_gradient σ y],
    by rw [Coercive.periodLIntegral_curlVec_sq_eq hv]; exact hv.gradient_finite⟩

variable {C : Type} {nE nM : ℕ} {w : PieceWeights C nE nM}

theorem pieceModeSum_split {P' : ℝ} {h : HarmonicBounds} {wt : Space → ℝ} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ epsSup epsGradSup ratio : ℝ}
    (hw : CoerciveWeak.IsAdmissibleWeak w P' h wt W HW w₀ epsSup epsGradSup ratio)
    (hv : IsPerturbation Γ P v G H g) {X : ℝ → Space → Space} (hX : IsSquareField X)
    (hXc : IsSquareField (fun σ y => curlVec (fderiv ℝ (X σ) y)))
    (hXm : ∀ ι, ∀ᵐ z : ℝ × Space, curlOfGrad (modeGrad ι (gradField X) z.1 z.2) =
      modeVel ι (fun σ y => curlVec (fderiv ℝ (X σ) y)) z.1 z.2) :
    Coercive.PieceField.Internal.pieceModeSum w v G X =
      ∑ β : Fin nE, ∑' ι, weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.epsWeight w β)
          (fun σ y => curlVec (G σ y)) (fun σ y => curlVec (fderiv ℝ (X σ) y)) ι
        + ∑ β : Fin nM, ∑' ι, weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.muWeight w β)
          (Coercive.Internal.SmoothWeightSplit.scaledField v) X ι := by
  obtain ⟨Bm, hBm⟩ := CoerciveWeak.Internal.WeakPairingSplit.muWeight_bound hw
  rw [← Coercive.Internal.SmoothPieceSplit.tsum_pieces CoerciveWeak.modeSquareSumHolds_closed
    (CoerciveWeak.Internal.WeakPairingSplit.epsWeight w) (CoerciveWeak.Internal.WeakPairingSplit.muWeight w)
    (CoerciveWeak.Internal.WeakPairingSplit.epsWeight_measurable hw)
    (CoerciveWeak.Internal.WeakPairingSplit.muWeight_measurable hw) (fun _ => epsSup) (fun _ => Bm)
    (CoerciveWeak.Internal.WeakPairingSplit.epsWeight_bound hw) hBm (curlG_square hv) hXc (scaled_square hv) hX]
  unfold Coercive.PieceField.Internal.pieceModeSum
  refine tsum_congr fun ι => iter_congr_ae ?_
  filter_upwards [Coercive.ae_curlOfGrad_modeGrad hv ι, hXm ι] with z h1 h2
  simp only [Coercive.PieceField.Internal.pieceIntegrand, h1, h2,
    Coercive.Internal.SmoothPieceSplit.cdot_modeVel_scaled v, Coercive.Internal.SmoothPieceSplit.mul_weight,
    CoerciveWeak.Internal.WeakPairingSplit.muWeight, CoerciveWeak.Internal.WeakPairingSplit.epsWeight]

theorem mu_terms_zero {X : ℝ → Space → Space}
    (hX : ∀ β ι, PieceWeights.inPiece (w.muP β).modes ι → ∀ᵐ z : ℝ × Space, modeVel ι X z.1 z.2 = 0)
    (U : ℝ → Space → Space) :
    ∑ β : Fin nM, ∑' ι, weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.muWeight w β) U X ι = 0 := by
  refine Finset.sum_eq_zero fun β _ => ?_
  have e : ∀ ι, weightedModeTerm (CoerciveWeak.Internal.WeakPairingSplit.muWeight w β) U X ι = 0 := by
    intro ι
    unfold weightedModeTerm
    by_cases hι : PieceWeights.inPiece (w.muP β).modes ι
    · rw [iter_congr_ae (g := fun _ _ => (0 : ℝ)) ?_]
      · simp
      · filter_upwards [hX β ι hι] with z hz
        simp [hz, cdot]
    · have hs : PieceWeights.sgn (w.muP β).modes ι = 0 := by
        unfold PieceWeights.inPiece at hι
        simp only [not_or] at hι
        simp [PieceWeights.sgn, hι.1, hι.2]
      simp [CoerciveWeak.Internal.WeakPairingSplit.muWeight, hs]
  simp [e]

end Internal.ActuatorPairingGradient

open Internal.ActuatorPairingGradient in
theorem multiplierField_pairing_gradient_part {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (wt : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ}
    (hw : CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio) (b : ℝ → Space → Space)
    (hb : Instance.ActuatorFacts w b) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g)
    (M : ℝ → Space → Space) (hM : w.IsMultiplierField v G H M) :
    ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → Space → Space, ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2) ∧
      IsTimePeriodic ψ ∧ (∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) ∧ (∀ σ y, divergenceAt (ψ σ) y = 0) ∧
      |periodPairing b M - periodPairing ψ M| + |multiplierRight w v G H b - multiplierRight w v G H ψ| < ε := by
  intro ε hε
  have hPars := CoerciveWeak.modeSquareSumHolds_closed
  have hSol := CoerciveWeak.solenoidalModeHolds_closed
  have hbs := actuator_square hb
  obtain ⟨Q, hQ, -, -, -, hmove⟩ := hSol b hb.measurable hb.periodic hb.square_finite
  have hQs := Coercive.PairingSplitInternal.square_of_solenoidal hQ
  obtain ⟨ψ, hψt, hL2, hcurl⟩ := actuator_density hb hQ
  have hψs : ∀ n, Coercive.ModeL2Internal.IsSquareField (ψ n) := fun n =>
    Coercive.PairingSplitInternal.testField_square (hψt n)
  have hψ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => ψ n z.1 z.2) := fun n => (hψt n).1.of_le (by simp)
  have hMs : Coercive.ModeL2Internal.IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hMself : Coercive.IsSolenoidalPartOf M M := ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, fun _ _ => rfl⟩
  have T1 : Tendsto (fun n => periodPairing (ψ n) M) atTop (𝓝 (periodPairing b M)) := by
    have t := Coercive.PairingSplitInternal.pairing_tendsto hMs hQs hψs hL2
    rw [Coercive.PairingSplitInternal.pairing_comm hMs hQs,
      ← Coercive.PairingSplitInternal.pairing_eq_solenoidal hSol hbs hQ hMself] at t
    exact t.congr fun n => Coercive.PairingSplitInternal.pairing_comm hMs (hψs n)
  have hLs := negTrace_square hv
  have hLself := negTrace_solenoidal_self hv
  have T2 : Tendsto (fun n => periodPairing (fun σ y => -secondDerivTrace (H σ y)) (ψ n)) atTop
      (𝓝 (periodPairing (fun σ y => -secondDerivTrace (H σ y)) b)) := by
    have t := Coercive.PairingSplitInternal.pairing_tendsto hLs hQs hψs hL2
    rwa [Coercive.PairingSplitInternal.pairing_comm hLs hQs,
      ← Coercive.PairingSplitInternal.pairing_eq_solenoidal hSol hbs hQ hLself,
      Coercive.PairingSplitInternal.pairing_comm hbs hLs] at t
  have hbc := curl_actuator_square hb
  have hbm : ∀ ι, ∀ᵐ z : ℝ × Space, curlOfGrad (modeGrad ι (gradField b) z.1 z.2) =
      modeVel ι (fun σ y => curlVec (fderiv ℝ (b σ) y)) z.1 z.2 := by
    intro ι
    filter_upwards [Coercive.Internal.ModeRotation.ae_integrable_orbit Coercive.axialRotationHolds_proof
      (gradField_locallyIntegrable hb)] with z hz
    exact Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq ι hz
  have hψm : ∀ n ι, ∀ᵐ z : ℝ × Space, curlOfGrad (modeGrad ι (gradField (ψ n)) z.1 z.2) =
      modeVel ι (fun σ y => curlVec (fderiv ℝ (ψ n σ) y)) z.1 z.2 := fun n ι =>
    Eventually.of_forall fun z => CoerciveWeak.Internal.WeakPairingSplit.hasCurlModes_of_contDiff (hψ1 n) ι z.1 z.2
  have hψc : ∀ n, Coercive.ModeL2Internal.IsSquareField (fun σ y => curlVec (fderiv ℝ (ψ n σ) y)) := fun n =>
    Coercive.PairingSplitInternal.curl_square (hψ1 n) (hψt n).2.1 (hψt n).2.2.1
  have hbmodes : ∀ β ι, PieceWeights.inPiece (w.muP β).modes ι →
      ∀ᵐ z : ℝ × Space, modeVel ι b z.1 z.2 = 0 := by
    intro β ι hι
    filter_upwards [ae_off_axis_joint] with z hz
    by_contra hne
    exact hb.mu_free β ι ⟨z.1, z.2, hz, hne⟩ hι
  have hQmodes : ∀ β ι, PieceWeights.inPiece (w.muP β).modes ι →
      ∀ᵐ z : ℝ × Space, modeVel ι Q z.1 z.2 = 0 :=
    fun β ι hι => solenoidalPart_modeVel_ae_zero hbs hQ hmove ι (hbmodes β ι hι)
  have μb := mu_terms_zero hbmodes (Coercive.Internal.SmoothWeightSplit.scaledField v)
  have μQ := mu_terms_zero hQmodes (Coercive.Internal.SmoothWeightSplit.scaledField v)
  obtain ⟨Bm, hBm⟩ := CoerciveWeak.Internal.WeakPairingSplit.muWeight_bound hw
  have T3 : Tendsto (fun n => Coercive.PieceField.Internal.pieceModeSum w v G (ψ n)) atTop
      (𝓝 (Coercive.PieceField.Internal.pieceModeSum w v G b)) := by
    rw [pieceModeSum_split hw hv hbs hbc hbm, μb, ← μQ]
    simp only [fun n => pieceModeSum_split hw hv (hψs n) (hψc n) (hψm n)]
    refine (tendsto_finsetSum _ fun β _ => ?_).add (tendsto_finsetSum _ fun β _ => ?_)
    · exact Coercive.ModeL2Internal.weightedMode_tendsto hPars _
        (CoerciveWeak.Internal.WeakPairingSplit.epsWeight_measurable hw β)
        (CoerciveWeak.Internal.WeakPairingSplit.epsWeight_bound hw β) (curlG_square hv) hbc hψc hcurl
    · exact Coercive.ModeL2Internal.weightedMode_tendsto hPars _
        (CoerciveWeak.Internal.WeakPairingSplit.muWeight_measurable hw β) (hBm β) (scaled_square hv) hQs hψs hL2
  have T4 : Tendsto (fun n => multiplierRight w v G H (ψ n)) atTop (𝓝 (multiplierRight w v G H b)) :=
    T2.add T3
  have h1 := (Metric.tendsto_nhds.1 T1) (ε / 2) (by positivity)
  have h2 := (Metric.tendsto_nhds.1 T4) (ε / 2) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  rw [Real.dist_eq, abs_sub_comm] at hn1 hn2
  exact ⟨ψ n, hψ1 n, (hψt n).2.1, (hψt n).2.2.1, (hψt n).2.2.2, by linarith⟩

end CertCell

end Breakdown
