import Breakdown.Cert.CoerciveSmoothPiecePairingSplitDensity
import Breakdown.Cert.CoerciveSmoothPairingSplitClass

open scoped ContDiff ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceSplit

open ModeL2Internal (IsSquareField weightedModeTerm)
open Internal.SmoothWeightSplit
open Internal.SmoothPairingClass

theorem cdot_modeVel_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (Z : Fin 3 → ℂ) :
    cdot (modeVel ι v σ y) Z = ((1 + ‖y‖ : ℝ) : ℂ) * cdot (modeVel ι (scaledField v) σ y) Z := by
  unfold cdot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [modeVel_eq_scaled v ι σ y i]; ring

theorem mul_weight (a c : ℝ) (z : ℂ) :
    Complex.I * (a : ℂ) * ((c : ℂ) * z) = Complex.I * ((a * c : ℝ) : ℂ) * z := by
  push_cast
  ring

theorem muPairing_eq_scaled (wt : ℤ × ℤ → Space → ℝ) (v Q : ℝ → Space → Space) :
    muPairing wt v Q = ∑' ι, weightedModeTerm (fun ι y => wt ι y * (1 + ‖y‖)) (scaledField v) Q ι := by
  unfold muPairing weightedModeTerm
  simp only [cdot_modeVel_scaled v, mul_weight]

def pieceForm {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v A B : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    ((∑ β : Fin nE, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
          (curlOfGrad (modeGrad ι (gradField A) σ y))).re)
      + ∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
        * cdot (modeVel ι v σ y) (modeVel ι B σ y)).re)

def curlField (X : ℝ → Space → Space) : ℝ → Space → Space := fun s x => curlVec (fderiv ℝ (X s) x)

theorem abs_sgn_le (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : |PieceWeights.sgn T ι| ≤ 1 := by
  unfold PieceWeights.sgn
  split_ifs <;> simp

theorem sgnWeight_bound (T : Set (ℤ × ℤ)) {f : Space → ℝ} {B : ℝ} (hf : ∀ y, |f y| ≤ B)
    (ι : ℤ × ℤ) (y : Space) : |PieceWeights.sgn T ι * f y| ≤ B := by
  rw [abs_mul]
  calc |PieceWeights.sgn T ι| * |f y| ≤ 1 * |f y| := mul_le_mul_of_nonneg_right (abs_sgn_le T ι) (abs_nonneg _)
    _ ≤ B := by rw [one_mul]; exact hf y

theorem sgnWeight_measurable (T : Set (ℤ × ℤ)) {f : Space → ℝ} (hf : Continuous f)
    (ι : ℤ × ℤ) : Measurable (fun y => PieceWeights.sgn T ι * f y) :=
  measurable_const.mul hf.measurable

theorem tsum_pieces (hPars : ModeSquareSumHolds) {nE nM : ℕ}
    (wE : Fin nE → ℤ × ℤ → Space → ℝ) (wM : Fin nM → ℤ × ℤ → Space → ℝ)
    (hEm : ∀ β ι, Measurable (wE β ι)) (hMm : ∀ β ι, Measurable (wM β ι))
    (BE : Fin nE → ℝ) (BM : Fin nM → ℝ) (hEb : ∀ β ι y, |wE β ι y| ≤ BE β)
    (hMb : ∀ β ι y, |wM β ι y| ≤ BM β) {U1 X1 U2 X2 : ℝ → Space → Space}
    (hU1 : IsSquareField U1) (hX1 : IsSquareField X1)
    (hU2 : IsSquareField U2) (hX2 : IsSquareField X2) :
    ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      ((∑ β : Fin nE, (Complex.I * (wE β ι y : ℂ) * cdot (modeVel ι U1 σ y) (modeVel ι X1 σ y)).re)
        + ∑ β : Fin nM, (Complex.I * (wM β ι y : ℂ) * cdot (modeVel ι U2 σ y) (modeVel ι X2 σ y)).re)
      = ∑ β : Fin nE, ∑' ι, weightedModeTerm (wE β) U1 X1 ι
        + ∑ β : Fin nM, ∑' ι, weightedModeTerm (wM β) U2 X2 ι := by
  have iE : ∀ ι, ∀ β ∈ (Finset.univ : Finset (Fin nE)), Integrable (fun z : ℝ × Space =>
      (Complex.I * (wE β ι z.2 : ℂ) * cdot (modeVel ι U1 z.1 z.2) (modeVel ι X1 z.1 z.2)).re)
      ModeL2Internal.slab :=
    fun ι β _ => ModeL2Internal.integrable_weightedMode hPars (wE β) (hEm β) (hEb β) hU1 hX1 ι
  have iM : ∀ ι, ∀ β ∈ (Finset.univ : Finset (Fin nM)), Integrable (fun z : ℝ × Space =>
      (Complex.I * (wM β ι z.2 : ℂ) * cdot (modeVel ι U2 z.1 z.2) (modeVel ι X2 z.1 z.2)).re)
      ModeL2Internal.slab :=
    fun ι β _ => ModeL2Internal.integrable_weightedMode hPars (wM β) (hMm β) (hMb β) hU2 hX2 ι
  have sE : ∀ β ∈ (Finset.univ : Finset (Fin nE)),
      Summable (fun ι => weightedModeTerm (wE β) U1 X1 ι) := fun β _ => by
    obtain ⟨K, hK⟩ := ModeL2Internal.weightedMode_bound hPars (wE β) (hEm β) (hEb β) hU1
    exact (hK X1 X1 hX1 hX1).1
  have sM : ∀ β ∈ (Finset.univ : Finset (Fin nM)),
      Summable (fun ι => weightedModeTerm (wM β) U2 X2 ι) := fun β _ => by
    obtain ⟨K, hK⟩ := ModeL2Internal.weightedMode_bound hPars (wM β) (hMm β) (hMb β) hU2
    exact (hK X2 X2 hX2 hX2).1
  have hterm : ∀ ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      ((∑ β : Fin nE, (Complex.I * (wE β ι y : ℂ) * cdot (modeVel ι U1 σ y) (modeVel ι X1 σ y)).re)
        + ∑ β : Fin nM, (Complex.I * (wM β ι y : ℂ) * cdot (modeVel ι U2 σ y) (modeVel ι X2 σ y)).re)
      = ∑ β : Fin nE, weightedModeTerm (wE β) U1 X1 ι
        + ∑ β : Fin nM, weightedModeTerm (wM β) U2 X2 ι := by
    intro ι
    have hiE := integrable_finsetSum _ (iE ι)
    have hiM := integrable_finsetSum _ (iM ι)
    have e1 : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        ((∑ β : Fin nE, (Complex.I * (wE β ι y : ℂ) * cdot (modeVel ι U1 σ y) (modeVel ι X1 σ y)).re)
          + ∑ β : Fin nM, (Complex.I * (wM β ι y : ℂ) * cdot (modeVel ι U2 σ y) (modeVel ι X2 σ y)).re)
        = ∫ z, ((∑ β : Fin nE, (Complex.I * (wE β ι z.2 : ℂ)
            * cdot (modeVel ι U1 z.1 z.2) (modeVel ι X1 z.1 z.2)).re)
          + ∑ β : Fin nM, (Complex.I * (wM β ι z.2 : ℂ)
            * cdot (modeVel ι U2 z.1 z.2) (modeVel ι X2 z.1 z.2)).re) ∂ModeL2Internal.slab :=
      (integral_prod _ (hiE.add hiM)).symm
    rw [e1, integral_add hiE hiM, integral_finsetSum _ (iE ι), integral_finsetSum _ (iM ι)]
    congr 1
    · exact Finset.sum_congr rfl fun β _ =>
        (ModeL2Internal.weightedModeTerm_eq hPars (wE β) (hEm β) (hEb β) hU1 hX1 ι).symm
    · exact Finset.sum_congr rfl fun β _ =>
        (ModeL2Internal.weightedModeTerm_eq hPars (wM β) (hMm β) (hMb β) hU2 hX2 ι).symm
  rw [tsum_congr hterm, (summable_sum sE).tsum_add (summable_sum sM), Summable.tsum_finsetSum sE,
    Summable.tsum_finsetSum sM]

section Weights

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}

def epsWt (m : PieceWeights C nE nM) (β : Fin nE) : ℤ × ℤ → Space → ℝ :=
  fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y

def muWt (m : PieceWeights C nE nM) (β : Fin nM) : ℤ × ℤ → Space → ℝ :=
  fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y * (1 + ‖y‖)

theorem epsWt_bound (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nE) (ι : ℤ × ℤ)
    (y : Space) : |epsWt m β ι y| ≤ epsSup := by
  refine sgnWeight_bound _ (fun y => ?_) ι y
  rw [abs_of_nonneg (hadm.eps_wt_nonneg β y)]
  exact (Finset.single_le_sum (fun b _ => hadm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans
    (hadm.eps_sum_le y)

theorem epsWt_measurable (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nE)
    (ι : ℤ × ℤ) : Measurable (epsWt m β ι) :=
  sgnWeight_measurable _ (hadm.eps_increment β).choose_spec.continuous ι

theorem muWt_bound (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) :
    ∃ B, ∀ β ι y, |muWt m β ι y| ≤ B := by
  obtain ⟨Bm, hBm⟩ := hadm.mu_decay
  refine ⟨2 * Bm, fun β ι y => ?_⟩
  have e : muWt m β ι y = PieceWeights.sgn (m.muP β).modes ι * ((1 + ‖y‖) * (m.muP β).wt y) := by
    unfold muWt
    ring
  rw [e]
  refine sgnWeight_bound (f := fun x => (1 + ‖x‖) * (m.muP β).wt x) _ (fun y => ?_) ι y
  have h0 : 0 ≤ (1 + ‖y‖) * (m.muP β).wt y := mul_nonneg (by positivity) (hadm.mu_wt_nonneg β y)
  rw [abs_of_nonneg h0]
  exact one_add_norm_mul_le (hadm.mu_wt_nonneg β) (fun x => ⟨(hBm β x).1, (hBm β x).2.1⟩) y

theorem muWt_measurable (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nM)
    (ι : ℤ × ℤ) : Measurable (muWt m β ι) :=
  (sgnWeight_measurable _ (hadm.mu_increment β).choose_spec.continuous ι).mul
    (measurable_const.add continuous_norm.measurable)

theorem pieceForm_eq (hPars : ModeSquareSumHolds)
    (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {A B : ℝ → Space → Space}
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) (hAc : IsSquareField (curlField A))
    (hB : IsSquareField B) :
    pieceForm m v A B
      = ∑ β : Fin nE, ∑' ι, weightedModeTerm (epsWt m β) (curlField v) (curlField A) ι
        + ∑ β : Fin nM, ∑' ι, weightedModeTerm (muWt m β) (scaledField v) B ι := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU : IsSquareField (curlField v) :=
    curl_square_of_fderiv hv1 hv.periodic (perturbation_fderiv_sq hv)
  obtain ⟨Bm, hBm⟩ := muWt_bound hadm
  have e : pieceForm m v A B = ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      ((∑ β : Fin nE, (Complex.I * (epsWt m β ι y : ℂ)
          * cdot (modeVel ι (curlField v) σ y) (modeVel ι (curlField A) σ y)).re)
        + ∑ β : Fin nM, (Complex.I * (muWt m β ι y : ℂ)
          * cdot (modeVel ι (scaledField v) σ y) (modeVel ι B σ y)).re) := by
    unfold pieceForm curlField epsWt muWt
    simp only [PairingSplitInternal.curlOfGrad_modeGrad hv1, PairingSplitInternal.curlOfGrad_modeGrad hA,
      cdot_modeVel_scaled v, mul_weight]
  rw [e]
  exact tsum_pieces hPars (epsWt m) (muWt m) (epsWt_measurable hadm) (muWt_measurable hadm)
    (fun _ => epsSup) (fun _ => Bm) (epsWt_bound hadm) hBm hU hAc (scaledField_square hv) hB

theorem pieceForm_tendsto (hPars : ModeSquareSumHolds)
    (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {F Q : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hFc : IsSquareField (curlField F))
    (hQs : IsSquareField Q)
    {ψ : ℕ → ℝ → Space → Space} (hψ : ∀ n, IsPeriodicTestField (ψ n))
    (h1 : Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) Filter.atTop
      (nhds 0))
    (h2 : Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => pieceForm m v (ψ n) (ψ n)) Filter.atTop (nhds (pieceForm m v F Q)) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU : IsSquareField (curlField v) :=
    curl_square_of_fderiv hv1 hv.periodic (perturbation_fderiv_sq hv)
  have hV := scaledField_square hv
  have hψ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => ψ n z.1 z.2) := fun n => (hψ n).1.of_le (by simp)
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => PairingSplitInternal.testField_square (hψ n)
  have hψc : ∀ n, IsSquareField (curlField (ψ n)) := fun n =>
    PairingSplitInternal.curl_square (hψ1 n) (hψ n).2.1 (hψ n).2.2.1
  obtain ⟨Bm, hBm⟩ := muWt_bound hadm
  have eL : (fun n => pieceForm m v (ψ n) (ψ n)) = fun n =>
      ∑ β : Fin nE, ∑' ι, weightedModeTerm (epsWt m β) (curlField v) (curlField (ψ n)) ι
        + ∑ β : Fin nM, ∑' ι, weightedModeTerm (muWt m β) (scaledField v) (ψ n) ι :=
    funext fun n => pieceForm_eq hPars hadm hv (hψ1 n) (hψc n) (hψs n)
  rw [eL, pieceForm_eq hPars hadm hv hF hFc hQs]
  refine (tendsto_finsetSum _ fun β _ => ?_).add (tendsto_finsetSum _ fun β _ => ?_)
  · exact ModeL2Internal.weightedMode_tendsto hPars _ (epsWt_measurable hadm β)
      (epsWt_bound hadm β) hU hFc hψc h2
  · exact ModeL2Internal.weightedMode_tendsto hPars _ (muWt_measurable hadm β)
      (hBm β) hV hQs hψs h1

theorem mode_tsum_split (hPars : ModeSquareSumHolds)
    (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {F Q : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hFc : IsSquareField (curlField F))
    (hQs : IsSquareField Q) :
    pieceForm m v F Q
      = ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v F
          + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  rw [pieceForm_eq hPars hadm hv hF hFc hQs]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun β _ => ?_) (Finset.sum_congr rfl fun β _ => ?_)
  · unfold epsPairing weightedModeTerm curlField epsWt
    simp only [PairingSplitInternal.curlOfGrad_modeGrad hv1, PairingSplitInternal.curlOfGrad_modeGrad hF]
  · rw [muPairing_eq_scaled]
    rfl

theorem multiplier_pairing (hPars : ModeSquareSumHolds) (hSolMode : SolenoidalModeHolds)
    (hadm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW2 : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWd : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) {M Q : ℝ → Space → Space}
    (hM : m.IsMultiplierField v (gradField v) (secondDerivField v) M)
    (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    periodPairing Q M =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
        + ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
            (smoothRight P W v)
        + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q := by
  have hFc1 := smoothRight_contDiff' (P := P) hW2 hv
  have hFp := smoothRight_periodic' (P := P) hWp hv
  have hFs := smoothRight_square' hW2 hWp hWd hv
  have hFd := smoothRight_fderiv_sq hW2 hWp hWd hv
  have hFcurl : IsSquareField (curlField (smoothRight P W v)) := curl_square_of_fderiv hFc1 hFp hFd
  obtain ⟨ψ, hψt, hL2, hcurl⟩ := curlGraphDensityL2 hSolMode (smoothRight P W v) Q hFc1 hFp hFs.2.2 hFd hQ
  have hQs := PairingSplitInternal.square_of_solenoidal hQ
  have hMs : IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => PairingSplitInternal.testField_square (hψt n)
  have hLself := negSsp_solenoidal_self hv
  have hLs := PairingSplitInternal.square_of_solenoidal hLself
  have hseq : ∀ n, periodPairing M (ψ n) =
      periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) (ψ n) + pieceForm m v (ψ n) (ψ n) :=
    fun n => hM.2.2.2.2 (ψ n) (hψt n)
  have t1 := PairingSplitInternal.pairing_tendsto hMs hQs hψs hL2
  have t2 := PairingSplitInternal.pairing_tendsto hLs hQs hψs hL2
  have t3 := pieceForm_tendsto hPars hadm hv hFc1 hFcurl hQs hψt hL2 hcurl
  have t5 : Filter.Tendsto (fun n => periodPairing M (ψ n)) Filter.atTop
      (nhds (periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q + pieceForm m v (smoothRight P W v) Q)) :=
    (t2.add t3).congr fun n => (hseq n).symm
  have hlim := tendsto_nhds_unique t1 t5
  have u3 := PairingSplitInternal.pairing_eq_solenoidal hSolMode hFs hQ hLself
  have hL : periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) := by
    rw [PairingSplitInternal.pairing_comm hLs hQs, ← u3]
    rfl
  rw [PairingSplitInternal.pairing_comm hQs hMs, hlim, hL,
    mode_tsum_split hPars hadm hv hFc1 hFcurl hQs, add_assoc]

end Weights

end Internal.SmoothPieceSplit

theorem piecePairingSplitSmoothHolds_of (hPars : ModeSquareSumHolds) (hSolMode : SolenoidalModeHolds) :
    PiecePairingSplitSmoothHolds := by
  intro C nE nM m P h w W w₀ epsSup epsGradSup ratio hadm hW2 hWp _ hWd _ v hv M Q hM hQ
  rw [PairingSplitInternal.pairing_eq_solenoidal hSolMode (Internal.SmoothPairingClass.smoothRight_square' hW2 hWp hWd hv) hQ
    ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, fun _ _ => rfl⟩]
  exact Internal.SmoothPieceSplit.multiplier_pairing hPars hSolMode hadm hW2 hWp hWd hv hM hQ

end Coercive

end Breakdown
