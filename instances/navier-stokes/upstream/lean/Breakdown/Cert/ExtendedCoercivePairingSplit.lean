import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoerciveSmoothPiecePairingSplit
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.ExtendedCoercivePairingSplitIncrement
import Breakdown.Cert.ExtendedCoercivePairingSplitAeDiff
import Breakdown.Cert.ExtendedCoercivePairingSplitMollify

open scoped ContDiff ENNReal InnerProductSpace
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakPairingSplit

open Coercive
open Coercive.Internal.SmoothWeightSplit
open Coercive.Internal.SmoothPairingClass

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ}

def epsWeight (m : PieceWeights C nE nM) (β : Fin nE) : ℤ × ℤ → Space → ℝ :=
  fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y

def muWeight (m : PieceWeights C nE nM) (β : Fin nM) : ℤ × ℤ → Space → ℝ :=
  fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y * (1 + ‖y‖)

theorem epsWeight_bound (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (β : Fin nE)
    (ι : ℤ × ℤ) (y : Space) : |epsWeight m β ι y| ≤ epsSup := by
  refine Internal.SmoothPieceSplit.sgnWeight_bound _ (fun y => ?_) ι y
  rw [abs_of_nonneg (hadm.eps_wt_nonneg β y)]
  exact (Finset.single_le_sum (fun b _ => hadm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans
    (hadm.eps_sum_le y)

theorem epsWeight_measurable (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (β : Fin nE) (ι : ℤ × ℤ) : Measurable (epsWeight m β ι) :=
  Internal.SmoothPieceSplit.sgnWeight_measurable _ (hadm.eps_increment β).choose_spec.continuous ι

theorem muWeight_bound (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) :
    ∃ B, ∀ β ι y, |muWeight m β ι y| ≤ B := by
  obtain ⟨Bm, hBm⟩ := hadm.mu_decay
  refine ⟨2 * Bm, fun β ι y => ?_⟩
  have e : muWeight m β ι y = PieceWeights.sgn (m.muP β).modes ι * ((1 + ‖y‖) * (m.muP β).wt y) := by
    unfold muWeight
    ring
  rw [e]
  refine Internal.SmoothPieceSplit.sgnWeight_bound (f := fun x => (1 + ‖x‖) * (m.muP β).wt x) _
    (fun y => ?_) ι y
  have h0 : 0 ≤ (1 + ‖y‖) * (m.muP β).wt y := mul_nonneg (by positivity) (hadm.mu_wt_nonneg β y)
  rw [abs_of_nonneg h0]
  exact one_add_norm_mul_le (hadm.mu_wt_nonneg β) (fun x => ⟨(hBm β x).1, (hBm β x).2.1⟩) y

theorem muWeight_measurable (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (β : Fin nM) (ι : ℤ × ℤ) : Measurable (muWeight m β ι) :=
  (Internal.SmoothPieceSplit.sgnWeight_measurable _ (hadm.mu_increment β).choose_spec.continuous ι).mul
    (measurable_const.add continuous_norm.measurable)

def HasCurlModes (A : ℝ → Space → Space) : Prop :=
  ∀ ι σ y, curlOfGrad (modeGrad ι (gradField A) σ y)
    = modeVel ι (fun s x => curlVec (fderiv ℝ (A s) x)) σ y

theorem hasCurlModes_of_contDiff {A : ℝ → Space → Space}
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) : HasCurlModes A :=
  fun ι σ y => PairingSplitInternal.curlOfGrad_modeGrad hA ι σ y

theorem pieceForm_eq (hPars : ModeSquareSumHolds)
    (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {A B : ℝ → Space → Space}
    (hA : HasCurlModes A) (hAc : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField A))
    (hB : ModeL2Internal.IsSquareField B) :
    Internal.SmoothPieceSplit.pieceForm m v A B
      = ∑ β : Fin nE, ∑' ι, ModeL2Internal.weightedModeTerm (epsWeight m β)
          (Internal.SmoothPieceSplit.curlField v) (Internal.SmoothPieceSplit.curlField A) ι
        + ∑ β : Fin nM, ∑' ι, ModeL2Internal.weightedModeTerm (muWeight m β) (scaledField v) B ι := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField v) :=
    curl_square_of_fderiv hv1 hv.periodic (perturbation_fderiv_sq hv)
  obtain ⟨Bm, hBm⟩ := muWeight_bound hadm
  have e : Internal.SmoothPieceSplit.pieceForm m v A B = ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      ((∑ β : Fin nE, (Complex.I * (epsWeight m β ι y : ℂ)
          * cdot (modeVel ι (Internal.SmoothPieceSplit.curlField v) σ y)
            (modeVel ι (Internal.SmoothPieceSplit.curlField A) σ y)).re)
        + ∑ β : Fin nM, (Complex.I * (muWeight m β ι y : ℂ)
          * cdot (modeVel ι (scaledField v) σ y) (modeVel ι B σ y)).re) := by
    have hA' : ∀ ι σ y, curlOfGrad (modeGrad ι (gradField A) σ y)
        = modeVel ι (fun s x => curlVec (fderiv ℝ (A s) x)) σ y := hA
    unfold Internal.SmoothPieceSplit.pieceForm Internal.SmoothPieceSplit.curlField epsWeight muWeight
    simp only [PairingSplitInternal.curlOfGrad_modeGrad hv1, hA',
      Internal.SmoothPieceSplit.cdot_modeVel_scaled v, Internal.SmoothPieceSplit.mul_weight]
  rw [e]
  exact Internal.SmoothPieceSplit.tsum_pieces hPars (epsWeight m) (muWeight m)
    (epsWeight_measurable hadm) (muWeight_measurable hadm)
    (fun _ => epsSup) (fun _ => Bm) (epsWeight_bound hadm) hBm hU hAc (scaledField_square hv) hB

theorem pieceForm_tendsto (hPars : ModeSquareSumHolds)
    (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {F Q : ℝ → Space → Space}
    (hF : HasCurlModes F) (hFc : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField F))
    (hQs : ModeL2Internal.IsSquareField Q)
    {ψ : ℕ → ℝ → Space → Space} (hψ : ∀ n, IsPeriodicTestField (ψ n))
    (h1 : Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) Filter.atTop
      (nhds 0))
    (h2 : Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => Internal.SmoothPieceSplit.pieceForm m v (ψ n) (ψ n)) Filter.atTop
      (nhds (Internal.SmoothPieceSplit.pieceForm m v F Q)) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  have hU : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField v) :=
    curl_square_of_fderiv hv1 hv.periodic (perturbation_fderiv_sq hv)
  have hV := scaledField_square hv
  have hψ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => ψ n z.1 z.2) := fun n => (hψ n).1.of_le (by simp)
  have hψs : ∀ n, ModeL2Internal.IsSquareField (ψ n) := fun n =>
    PairingSplitInternal.testField_square (hψ n)
  have hψc : ∀ n, ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField (ψ n)) := fun n =>
    PairingSplitInternal.curl_square (hψ1 n) (hψ n).2.1 (hψ n).2.2.1
  obtain ⟨Bm, hBm⟩ := muWeight_bound hadm
  have eL : (fun n => Internal.SmoothPieceSplit.pieceForm m v (ψ n) (ψ n)) = fun n =>
      ∑ β : Fin nE, ∑' ι, ModeL2Internal.weightedModeTerm (epsWeight m β)
          (Internal.SmoothPieceSplit.curlField v) (Internal.SmoothPieceSplit.curlField (ψ n)) ι
        + ∑ β : Fin nM, ∑' ι, ModeL2Internal.weightedModeTerm (muWeight m β) (scaledField v) (ψ n) ι :=
    funext fun n => pieceForm_eq hPars hadm hv (hasCurlModes_of_contDiff (hψ1 n)) (hψc n) (hψs n)
  rw [eL, pieceForm_eq hPars hadm hv hF hFc hQs]
  refine (tendsto_finsetSum _ fun β _ => ?_).add (tendsto_finsetSum _ fun β _ => ?_)
  · exact ModeL2Internal.weightedMode_tendsto hPars _ (epsWeight_measurable hadm β)
      (epsWeight_bound hadm β) hU hFc hψc h2
  · exact ModeL2Internal.weightedMode_tendsto hPars _ (muWeight_measurable hadm β)
      (hBm β) hV hQs hψs h1

theorem mode_tsum_split (hPars : ModeSquareSumHolds)
    (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) {P' : ℝ}
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P' v) {F Q : ℝ → Space → Space}
    (hF : HasCurlModes F) (hFc : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField F))
    (hQs : ModeL2Internal.IsSquareField Q) :
    Internal.SmoothPieceSplit.pieceForm m v F Q
      = ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v F
          + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y)
            v Q := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by simp)
  rw [pieceForm_eq hPars hadm hv hF hFc hQs]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun β _ => ?_) (Finset.sum_congr rfl fun β _ => ?_)
  · have hF' : ∀ ι σ y, curlOfGrad (modeGrad ι (gradField F) σ y)
        = modeVel ι (fun s x => curlVec (fderiv ℝ (F s) x)) σ y := hF
    unfold epsPairing ModeL2Internal.weightedModeTerm Internal.SmoothPieceSplit.curlField epsWeight
    simp only [PairingSplitInternal.curlOfGrad_modeGrad hv1, hF']
  · rw [Internal.SmoothPieceSplit.muPairing_eq_scaled]
    rfl

theorem multiplier_pairing (hPars : ModeSquareSumHolds)
    (hadm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) {F M Q : ℝ → Space → Space}
    (hFm : HasCurlModes F) (hFcurl : ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField F))
    (hLF : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Q σ y) (-secondDerivTrace (secondDerivField v σ y))
      = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (F σ y) (-secondDerivTrace (secondDerivField v σ y)))
    (hM : m.IsMultiplierField v (gradField v) (secondDerivField v) M)
    (hQs : ModeL2Internal.IsSquareField Q)
    (hdens : ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0)) :
    periodPairing Q M =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (F σ y) (-secondDerivTrace (secondDerivField v σ y)))
        + ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v F
        + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y)
            v Q := by
  obtain ⟨ψ, hψt, hL2, hcurl⟩ := hdens
  have hMs : ModeL2Internal.IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hψs : ∀ n, ModeL2Internal.IsSquareField (ψ n) := fun n =>
    PairingSplitInternal.testField_square (hψt n)
  have hLself := negSsp_solenoidal_self hv
  have hLs := PairingSplitInternal.square_of_solenoidal hLself
  have hseq : ∀ n, periodPairing M (ψ n) =
      periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) (ψ n)
        + Internal.SmoothPieceSplit.pieceForm m v (ψ n) (ψ n) :=
    fun n => hM.2.2.2.2 (ψ n) (hψt n)
  have t1 := PairingSplitInternal.pairing_tendsto hMs hQs hψs hL2
  have t2 := PairingSplitInternal.pairing_tendsto hLs hQs hψs hL2
  have t3 := pieceForm_tendsto hPars hadm hv hFm hFcurl hQs hψt hL2 hcurl
  have t5 : Filter.Tendsto (fun n => periodPairing M (ψ n)) Filter.atTop
      (nhds (periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q
        + Internal.SmoothPieceSplit.pieceForm m v F Q)) :=
    (t2.add t3).congr fun n => (hseq n).symm
  have hlim := tendsto_nhds_unique t1 t5
  have hL : periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (F σ y) (-secondDerivTrace (secondDerivField v σ y)) := by
    rw [PairingSplitInternal.pairing_comm hLs hQs, ← hLF]
    rfl
  rw [PairingSplitInternal.pairing_comm hQs hMs, hlim, hL,
    mode_tsum_split hPars hadm hv hFm hFcurl hQs, add_assoc]

theorem smoothRight_continuous {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
  have hV := hv.smooth
  have d1 := slice_contDiff hV
  have dW : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    PairingSplitInternal.contDiff_slice (V := W) hW.smooth (by norm_num)
  have c1 : Continuous (fun z : ℝ × Space => transportPart P v z.1 z.2) :=
    (transport_contDiff P hV).continuous
  have c4 : Continuous (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) :=
    (secondDerivTrace_contDiff hV).continuous
  have c5 : Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2)) :=
    d1.continuous.clm_apply hW.smooth.continuous
  have c6 : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    dW.continuous.clm_apply hV.continuous
  exact ((c1.sub c4).add c5).add c6

theorem decay_const_nonneg {D : ℝ} (hW : IsWeakSecondDerivState W HW D) : 0 ≤ D := by
  have h := (hW.decay 0 0).1
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem fderiv_sub_le_of_segment {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (x x' : Space)
    (K : ℝ) (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, D / (1 + ‖x + t • (x' - x)‖) ^ 3 ≤ K) :
    ‖fderiv ℝ (W σ) x' - fderiv ℝ (W σ) x‖ ≤ K * ‖x' - x‖ := by
  have hD := decay_const_nonneg hW
  have hK0 : 0 ≤ K := (div_nonneg hD (by positivity)).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  have hfc : Continuous (fderiv ℝ (W σ)) := (slice_of_joint hW.smooth σ).continuous_fderiv one_ne_zero
  refine Internal.WeakIncrement.increment_of_weakSecondDeriv (f := fderiv ℝ (W σ)) (H := HW σ) hfc
    (hW.secondDeriv_weak σ) x x' K ?_
  intro ε hε
  have hc : ContinuousAt (fun δ : ℝ => K / (1 - δ) ^ 3) 0 :=
    continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 3) (by norm_num)
  have hev : ∀ᶠ δ in nhds (0 : ℝ), K / (1 - δ) ^ 3 < K + ε :=
    hc.eventually (gt_mem_nhds (by norm_num; linarith))
  obtain ⟨δ, hδ1, hδ2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  refine ⟨δ, hδ2.1, fun z hz w hw => ?_⟩
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hzK := hK t ht
  set z := x + t • (x' - x)
  have h1m : 0 < 1 - δ := by linarith [hδ2.2]
  have hwz : ‖z‖ - δ ≤ ‖w‖ := by
    have := norm_sub_norm_le z w
    rw [norm_sub_rev] at this
    linarith
  have hlow : (1 + ‖z‖) * (1 - δ) ≤ 1 + ‖w‖ := by nlinarith [norm_nonneg z, hδ2.1]
  have hp : 0 < (1 + ‖z‖) * (1 - δ) := by positivity
  calc ‖HW σ w‖ ≤ D / (1 + ‖w‖) ^ 3 := (hW.decay σ w).2.2
    _ ≤ D / ((1 + ‖z‖) * (1 - δ)) ^ 3 :=
        div_le_div_of_nonneg_left hD (pow_pos hp 3) (pow_le_pow_left₀ hp.le hlow 3)
    _ = D / (1 + ‖z‖) ^ 3 / (1 - δ) ^ 3 := by rw [mul_pow, div_div]
    _ ≤ K / (1 - δ) ^ 3 := div_le_div_of_nonneg_right hzK (pow_pos h1m 3).le
    _ ≤ K + ε := hδ1.le

theorem secondDerivField_norm_le {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) :
    ‖secondDerivField W σ y‖ ≤ D / (1 + ‖y‖) ^ 3 := by
  have hD := decay_const_nonneg hW
  have key : ∀ r : ℝ, 0 < r → r < 1 → ‖secondDerivField W σ y‖ ≤ D / (1 + ‖y‖ - r) ^ 3 := by
    intro r hr0 hr1
    have hpos : 0 < 1 + ‖y‖ - r := by linarith [norm_nonneg y]
    refine norm_fderiv_le_of_lip' ℝ (div_nonneg hD (pow_nonneg hpos.le 3)) ?_
    filter_upwards [Metric.ball_mem_nhds y hr0] with x hx
    refine fderiv_sub_le_of_segment hW σ y x _ (fun t ht => ?_)
    have hd : ‖x - y‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
    have hz : ‖y‖ - r ≤ ‖y + t • (x - y)‖ := by
      have h1 : ‖t • (x - y)‖ ≤ r := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        nlinarith [ht.2, norm_nonneg (x - y)]
      have h2 := norm_sub_norm_le y (-(t • (x - y)))
      rw [sub_neg_eq_add, norm_neg] at h2
      linarith [norm_add_le y (t • (x - y)), abs_norm_sub_norm_le y (-(t • (x - y))),
        norm_sub_norm_le y (y + t • (x - y)), norm_sub_rev y (y + t • (x - y)),
        show y - (y + t • (x - y)) = -(t • (x - y)) by abel, norm_neg (t • (x - y))]
    have hz' : 0 < 1 + ‖y + t • (x - y)‖ := by positivity
    exact div_le_div_of_nonneg_left hD (pow_pos hpos 3) (pow_le_pow_left₀ hpos.le (by linarith) 3)
  have hcont : Filter.Tendsto (fun r : ℝ => D / (1 + ‖y‖ - r) ^ 3) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (D / (1 + ‖y‖) ^ 3)) := by
    have hc : ContinuousAt (fun r : ℝ => D / (1 + ‖y‖ - r) ^ 3) 0 := by
      refine continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 3) ?_
      simp only [sub_zero]
      positivity
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact key r hr.1 hr.2

theorem decay_iterated {D : ℝ} (hW : IsWeakSecondDerivState W HW D) :
    ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1) := by
  intro σ y j hj
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    simpa using (hW.decay σ y).1
  · rw [norm_iteratedFDeriv_one]
    exact (hW.decay σ y).2.1
  · rw [norm_iter_two]
    exact secondDerivField_norm_le hW σ y

theorem smoothRight_square {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) : ModeL2Internal.IsSquareField (smoothRight P W v) := by
  have hD := decay_iterated hW
  have hc := smoothRight_continuous hW hv
  refine ⟨hc.aestronglyMeasurable, smoothRight_periodic' hW.periodic hv, ?_⟩
  have hg := (((memLp_transport hv).add ((memLp_deriv_two hv).const_mul 3)).add
    ((memLp_deriv_one hv).const_mul D)).add ((memLp_weighted hv).const_mul D)
  have hm := memLp_of_bound (h := fun σ y => ‖smoothRight P W v σ y‖)
    (g := fun σ y => ‖transportPart P v σ y‖ + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖
      + D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖))) hc.norm hg
    (fun σ y => by rw [abs_norm]; exact smoothRight_norm_le P hD σ y)
  exact lt_top_of_memLp_real hm

theorem fderiv_sub_le_near {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ x ∈ Metric.ball y r, ‖fderiv ℝ (W σ) x - fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖ - r) ^ 3 * ‖x - y‖ := by
  have hD := decay_const_nonneg hW
  have hpos : 0 < 1 + ‖y‖ - r := by linarith [norm_nonneg y]
  intro x hx
  refine fderiv_sub_le_of_segment hW σ y x _ (fun t ht => ?_)
  have hd : ‖x - y‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have h1 : ‖t • (x - y)‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [ht.2, norm_nonneg (x - y)]
  have hz : ‖y‖ - r ≤ ‖y + t • (x - y)‖ := by
    have h2 := norm_sub_norm_le y (y + t • (x - y))
    have e : y - (y + t • (x - y)) = -(t • (x - y)) := by abel
    rw [e, norm_neg] at h2
    linarith
  exact div_le_div_of_nonneg_left hD (pow_pos hpos 3) (pow_le_pow_left₀ hpos.le (by linarith) 3)

theorem fderiv_smooth_part_le {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (y : Space) :
    DifferentiableAt ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)
      + fderiv ℝ (v σ) x (W σ x)) y ∧
    ‖fderiv ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)
      + fderiv ℝ (v σ) x (W σ x)) y‖ ≤ ‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖) := by
  have hD0 := decay_const_nonneg hW
  have hr := norm_nonneg y
  have hvs : ContDiff ℝ ∞ (v σ) := slice_of_joint hv.smooth σ
  have hWs : ContDiff ℝ 1 (W σ) := slice_of_joint hW.smooth σ
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (v σ))) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have hT : ContDiff ℝ ∞ (transportPart P v σ) := slice_of_joint (transport_contDiff P hv.smooth) σ
  have dT : DifferentiableAt ℝ (transportPart P v σ) y := (hT.differentiable (by simp)) y
  have dH : DifferentiableAt ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y := by
    have e : (fun x => secondDerivTrace (secondDerivField v σ x)) = fun x => traceCLM (fderiv ℝ (fderiv ℝ (v σ)) x) :=
      funext fun x => (traceCLM_apply _).symm
    rw [e]
    exact traceCLM.differentiableAt.comp y ((hD2.differentiable (by simp)) y)
  have dA : DifferentiableAt ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y :=
    ((hD1.differentiable (by simp)) y).clm_apply ((hWs.differentiable (by norm_num)) y)
  have w0 : ‖W σ y‖ ≤ D := (hW.decay σ y).1.trans (div_le_self hD0 (by linarith))
  have w1 : ‖fderiv ℝ (W σ) y‖ ≤ D := (hW.decay σ y).2.1.trans (div_pow_le hD0 hr _)
  have eH : ‖fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y‖
      ≤ 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ :=
    norm_fderiv_trace_le (g := fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x)
      ((hD2.differentiable (by simp)) y)
  have eA : ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y‖
      ≤ D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ := by
    have h := norm_fderiv_apply_le (N := 1) (hD1.of_le (by norm_cast)) hWs le_rfl y
    have a1 : ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ ≤ D * ‖fderiv ℝ (v σ) y‖ := by
      rw [mul_comm D]; exact mul_le_mul_of_nonneg_left w1 (norm_nonneg _)
    have a2 : ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖ ≤ D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ := by
      rw [mul_comm D]; exact mul_le_mul_of_nonneg_left w0 (norm_nonneg _)
    exact h.trans (add_le_add a1 a2)
  have dTH : DifferentiableAt ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)) y :=
    dT.sub dH
  refine ⟨dTH.add dA, ?_⟩
  rw [fderiv_fun_add dTH dA, fderiv_fun_sub dT dH]
  calc ‖fderiv ℝ (transportPart P v σ) y - fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y
        + fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y‖
      ≤ ‖fderiv ℝ (transportPart P v σ) y‖ + ‖fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y‖
        + ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem eventually_sub_le {f : Space → Space} {y : Space} (hf : DifferentiableAt ℝ f y) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x in nhds y, ‖f x - f y‖ ≤ (‖fderiv ℝ f y‖ + ε) * ‖x - y‖ := by
  have hlo : ∀ᶠ x in nhds y, ‖f x - f y - fderiv ℝ f y (x - y)‖ ≤ ε * ‖x - y‖ :=
    (hasFDerivAt_iff_isLittleO.1 hf.hasFDerivAt).def hε
  filter_upwards [hlo] with x hx
  have h1 := (fderiv ℝ f y).le_opNorm (x - y)
  have h2 := norm_le_insert' (f x - f y) (fderiv ℝ f y (x - y))
  nlinarith [norm_nonneg (x - y)]

theorem fderiv_smoothRight_le {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ ‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
      + (D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖))) := by
  have hD0 := decay_const_nonneg hW
  have hr := norm_nonneg y
  set S : Space → Space := fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)
      + fderiv ℝ (v σ) x (W σ x) with hS
  obtain ⟨dS, bS⟩ := fderiv_smooth_part_le hW hv σ y
  have hvs : ContDiff ℝ ∞ (v σ) := slice_of_joint hv.smooth σ
  have dv : DifferentiableAt ℝ (v σ) y := (hvs.differentiable (by simp)) y
  have e : smoothRight P W v σ = fun x => S x + fderiv ℝ (W σ) x (v σ x) := rfl
  set a := ‖fderiv ℝ S y‖
  set b := ‖v σ y‖
  set c0 := ‖fderiv ℝ (W σ) y‖
  set d := ‖fderiv ℝ (v σ) y‖
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ (a + ε) + (D / (1 + ‖y‖ - ε) ^ 3 * (b + ε) + c0 * (d + ε)) := by
    intro ε hε0 hε1
    have hp : 0 < 1 + ‖y‖ - ε := by linarith
    have hK : 0 ≤ D / (1 + ‖y‖ - ε) ^ 3 := div_nonneg hD0 (pow_nonneg hp.le 3)
    refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
    have hvc : ∀ᶠ x in nhds y, ‖v σ x‖ ≤ b + ε := by
      filter_upwards [(hvs.continuous.tendsto y).eventually (Metric.ball_mem_nhds (v σ y) hε0)] with x hx
      have hx' : dist (v σ x) (v σ y) < ε := hx
      rw [dist_eq_norm] at hx'
      have := norm_le_insert' (v σ x) (v σ y)
      linarith
    filter_upwards [eventually_sub_le dS hε0, eventually_sub_le dv hε0, hvc,
      Metric.ball_mem_nhds y hε0] with x h1 h2 h3 h4
    have h5 := fderiv_sub_le_near hW σ y hε0 hε1 x h4
    show ‖(S x + fderiv ℝ (W σ) x (v σ x)) - (S y + fderiv ℝ (W σ) y (v σ y))‖ ≤ _
    have split : S x + fderiv ℝ (W σ) x (v σ x) - (S y + fderiv ℝ (W σ) y (v σ y))
        = (S x - S y) + ((fderiv ℝ (W σ) x - fderiv ℝ (W σ) y) (v σ x)
          + fderiv ℝ (W σ) y (v σ x - v σ y)) := by
      simp only [sub_apply, map_sub]
      abel
    rw [split]
    have t1 := (fderiv ℝ (W σ) x - fderiv ℝ (W σ) y).le_opNorm (v σ x)
    have t2 := (fderiv ℝ (W σ) y).le_opNorm (v σ x - v σ y)
    have n1 : ‖fderiv ℝ (W σ) x - fderiv ℝ (W σ) y‖ * ‖v σ x‖
        ≤ D / (1 + ‖y‖ - ε) ^ 3 * ‖x - y‖ * (b + ε) :=
      mul_le_mul h5 h3 (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))
    have n2 : c0 * ‖v σ x - v σ y‖ ≤ c0 * ((d + ε) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    calc ‖(S x - S y) + ((fderiv ℝ (W σ) x - fderiv ℝ (W σ) y) (v σ x)
          + fderiv ℝ (W σ) y (v σ x - v σ y))‖
        ≤ ‖S x - S y‖ + (‖(fderiv ℝ (W σ) x - fderiv ℝ (W σ) y) (v σ x)‖
          + ‖fderiv ℝ (W σ) y (v σ x - v σ y)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ ((a + ε) + (D / (1 + ‖y‖ - ε) ^ 3 * (b + ε) + c0 * (d + ε))) * ‖x - y‖ := by
          nlinarith
  have hlim : Filter.Tendsto (fun ε : ℝ => (a + ε) + (D / (1 + ‖y‖ - ε) ^ 3 * (b + ε) + c0 * (d + ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((a + 0) + (D / (1 + ‖y‖ - 0) ^ 3 * (b + 0) + c0 * (d + 0)))) := by
    have hc : ContinuousAt (fun ε : ℝ => (a + ε) + (D / (1 + ‖y‖ - ε) ^ 3 * (b + ε) + c0 * (d + ε))) 0 := by
      refine (continuousAt_const.add continuousAt_id).add
        (((continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 3) ?_).mul
          (continuousAt_const.add continuousAt_id)).add
          (continuousAt_const.mul (continuousAt_const.add continuousAt_id)))
      first | positivity | (norm_num; positivity)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hle := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact key r hr.1 hr.2)
  simp only [add_zero, sub_zero] at hle
  have u1 : D / (1 + ‖y‖) ^ 3 * b ≤ D * (b / (1 + ‖y‖)) := by
    have := div_pow_le_div hD0 (norm_nonneg (v σ y)) hr (show 1 ≤ 3 by norm_num)
    calc D / (1 + ‖y‖) ^ 3 * b = D / (1 + ‖y‖) ^ 3 * ‖v σ y‖ := rfl
      _ ≤ D * (b / (1 + ‖y‖)) := by
        rw [mul_div_assoc']
        have h1 : (1 + ‖y‖) ^ 1 ≤ (1 + ‖y‖) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
        rw [div_mul_eq_mul_div, mul_comm D b]
        rw [pow_one] at h1
        exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) hD0) hpos h1
  have u2 : c0 * d ≤ D * d :=
    mul_le_mul_of_nonneg_right ((hW.decay σ y).2.1.trans (div_pow_le hD0 hr _)) (norm_nonneg _)
  linarith

theorem continuous_curlVec : Continuous (fun A : Space →L[ℝ] Space => curlVec A) := by
  unfold curlVec
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous (fun A : Space →L[ℝ] Space =>
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => continuous_const.mul
      ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp (continuous_id.clm_apply continuous_const))
  exact hc.smul continuous_const

theorem smoothRight_curl_square {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    ModeL2Internal.IsSquareField (Internal.SmoothPieceSplit.curlField (smoothRight P W v)) := by
  have hc := smoothRight_continuous hW hv
  have hmeas : Measurable (fun z : ℝ × Space => fderiv ℝ (smoothRight P W v z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := fun s x => smoothRight P W v s x) hc
  refine ⟨(continuous_curlVec.measurable.comp hmeas).aestronglyMeasurable,
    fun σ y => ?_, ?_⟩
  · have e : smoothRight P W v (σ + 1) = smoothRight P W v σ :=
      funext fun x => smoothRight_periodic' hW.periodic hv σ x
    simp only [Internal.SmoothPieceSplit.curlField, e]
  · have hg := (((memLp_transport_deriv hv).add ((memLp_deriv_three hv).const_mul 3)).add
      (((memLp_deriv_one hv).const_mul D).add ((memLp_deriv_two hv).const_mul D))).add
      (((memLp_deriv_one hv).const_mul D).add ((memLp_weighted hv).const_mul D))
    have hg2 := lt_top_of_memLp_real (h := fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
      + (D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖)))) hg
    refine periodLIntegral_lt_top_of_le (show (0 : ℝ) ≤ 27 ^ 2 by norm_num) (fun σ y => ?_) hg2
    have a1 := norm_curlVec_le (fderiv ℝ (smoothRight P W v σ) y)
    have a2 := fderiv_smoothRight_le hW hv σ y
    have a3 : ‖curlVec (fderiv ℝ (smoothRight P W v σ) y)‖ ≤ 27 * (‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
      + (D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖)))) := by linarith
    have a0 := norm_nonneg (curlVec (fderiv ℝ (smoothRight P W v σ) y))
    show ‖curlVec (fderiv ℝ (smoothRight P W v σ) y)‖ ^ 2 ≤ _
    nlinarith

def derivBound (P D : ℝ) (v : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  ‖fderiv ℝ (transportPart P v z.1) z.2‖
    + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v z.1) x') x) z.2‖
    + (D * ‖fderiv ℝ (v z.1) z.2‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖)
    + (D * ‖fderiv ℝ (v z.1) z.2‖ + D * (‖v z.1 z.2‖ / (1 + ‖z.2‖)))

theorem derivBound_continuous {D : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (derivBound P D v) := by
  have c1 := (slice_contDiff (transport_contDiff P hv.smooth)).continuous.norm
  have c3 := (slice_contDiff (V := fun s x => fderiv ℝ (fun x' => fderiv ℝ (v s) x') x)
    (slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hv.smooth))).continuous.norm
  have c1v := (slice_contDiff hv.smooth).continuous.norm
  have c2v := (slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hv.smooth)).continuous.norm
  have cw := weighted_continuous hv.smooth.continuous
  exact ((c1.add (continuous_const.mul c3)).add ((continuous_const.mul c1v).add (continuous_const.mul c2v))).add
      ((continuous_const.mul c1v).add (continuous_const.mul cw))

theorem continuous_orbit (σ : ℝ) (y : Space) :
    Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
  (continuous_const.add continuous_fst).prodMk
    (PairingSplitInternal.continuous_axialRot continuous_snd continuous_const)

theorem derivBound_on_box {D : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (σ : ℝ)
    (y : Space) : ∃ Cb, ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
      derivBound P D v (σ + p.1, axialRot p.2 y) ≤ Cb := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hc : Continuous (fun p : ℝ × ℝ => derivBound P D v (σ + p.1, axialRot p.2 y)) :=
    (derivBound_continuous hv).comp (continuous_orbit σ y)
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨Cb, fun p hp => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hCb p hp)⟩

theorem smoothRight_hasCurlModes {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) : HasCurlModes (smoothRight P W v) := by
  intro ι σ y
  have hc := smoothRight_continuous hW hv
  have hmeas : Measurable (fun z : ℝ × Space => fderiv ℝ (smoothRight P W v z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := fun s x => smoothRight P W v s x) hc
  obtain ⟨Cb, hCb⟩ := derivBound_on_box (D := D) hv σ y
  have hint : Integrable (fun p : ℝ × ℝ => fderiv ℝ (smoothRight P W v (σ + p.1))
      (axialRot p.2 y)) Coercive.Internal.ModeRotation.boxMeasure := by
    have hm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => fderiv ℝ (smoothRight P W v (σ + p.1))
        (axialRot p.2 y)) Coercive.Internal.ModeRotation.boxMeasure :=
      (hmeas.comp (continuous_orbit σ y).measurable).aestronglyMeasurable
    refine Integrable.of_bound hm2 Cb ?_
    have eμ : Coercive.Internal.ModeRotation.boxMeasure
        = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := Measure.prod_restrict _ _
    rw [eμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have h1 := fderiv_smoothRight_le hW hv (σ + p.1) (axialRot p.2 y)
    exact h1.trans (hCb p ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩)
  have key := Coercive.Internal.CurlEnergy.curlOfGrad_modeGrad_eq (G := gradField (smoothRight P W v)) ι
    (z := (σ, y)) hint
  exact key

theorem density_of_approx (hSolMode : SolenoidalModeHolds) {F Q : ℝ → Space → Space}
    (hFc : Continuous (fun z : ℝ × Space => F z.1 z.2)) (hp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hQ : IsSolenoidalPartOf F Q)
    {G : ℕ → ℝ → Space → Space} (hG1 : ∀ k, ContDiff ℝ 1 (fun z : ℝ × Space => G k z.1 z.2))
    (hGp : ∀ k, IsTimePeriodic (G k)) (hG2 : ∀ k, periodLIntegral (fun σ y => ‖G k σ y‖ ^ 2) < ⊤)
    (hGd : ∀ k, periodLIntegral (fun σ y => matSq (fderiv ℝ (G k σ) y)) < ⊤)
    (hL2 : Filter.Tendsto (fun k => periodLIntegral (fun σ y => ‖G k σ y - F σ y‖ ^ 2)) Filter.atTop
      (nhds 0))
    (hcurl : Filter.Tendsto (fun k => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (G k σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0) := by
  have hFm : Measurable (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := fun s x => F s x) hFc
  have hFcm : AEStronglyMeasurable (fun z : ℝ × Space => curlVec (fderiv ℝ (F z.1) z.2)) volume :=
    (continuous_curlVec.measurable.comp hFm).aestronglyMeasurable
  have key : ∀ k : ℕ, ∃ ψ : ℝ → Space → Space, IsPeriodicTestField ψ ∧
      periodLIntegral (fun σ y => ‖ψ σ y - Q σ y‖ ^ 2) ≤ 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
      periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)
        ≤ 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    set δ := ENNReal.ofReal (1 / ((k : ℝ) + 1)) with hδ
    have hδpos : 0 < δ := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨n, hn1, hn2⟩ := (((tendsto_order.1 hL2).2 δ hδpos).and
      ((tendsto_order.1 hcurl).2 δ hδpos)).exists
    have hGm : AEStronglyMeasurable (fun z : ℝ × Space => G n z.1 z.2) volume :=
      (hG1 n).continuous.aestronglyMeasurable
    obtain ⟨Qn, hQn, -⟩ := hSolMode _ hGm (hGp n) (hG2 n)
    obtain ⟨ψ, hψt, h1, h2⟩ := curlGraphDensityL2 hSolMode (G n) Qn (hG1 n) (hGp n) (hG2 n) (hGd n) hQn
    obtain ⟨j, hj1, hj2⟩ := (((tendsto_order.1 h1).2 δ hδpos).and ((tendsto_order.1 h2).2 δ hδpos)).exists
    have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ j z.1 z.2) := (hψt j).1.of_le (by simp)
    refine ⟨ψ j, hψt j, ?_, ?_⟩
    · have hle := solenoidal_diff_le hSolMode hGm (hGp n) (hG2 n) hFc.aestronglyMeasurable hp hF2 hQn hQ
      calc periodLIntegral (fun σ y => ‖ψ j σ y - Q σ y‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y => ‖ψ j σ y - Qn σ y‖ ^ 2)
            + 2 * periodLIntegral (fun σ y => ‖Qn σ y - Q σ y‖ ^ 2) :=
            periodLIntegral_triangle hψ1.continuous.aestronglyMeasurable hQn.1 hQ.1
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
            exact hle.trans hn1.le
        _ = 4 * δ := by ring
    · calc periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ j σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y =>
              ‖curlVec (fderiv ℝ (ψ j σ) y) - curlVec (fderiv ℝ (G n σ) y)‖ ^ 2)
            + 2 * periodLIntegral (fun σ y =>
              ‖curlVec (fderiv ℝ (G n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2) :=
            periodLIntegral_triangle (X := fun σ y => curlVec (fderiv ℝ (ψ j σ) y))
              (Y := fun σ y => curlVec (fderiv ℝ (G n σ) y)) (Z := fun σ y => curlVec (fderiv ℝ (F σ) y))
              (PairingSplitInternal.continuous_curl hψ1).aestronglyMeasurable
              (PairingSplitInternal.continuous_curl (hG1 n)).aestronglyMeasurable hFcm
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
        _ = 4 * δ := by ring
  choose ψ hψt h1 h2 using key
  have hlim : Filter.Tendsto (fun k : ℕ => 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1))) Filter.atTop (nhds 0) := by
    have a : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) Filter.atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have b := ENNReal.Tendsto.const_mul a (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    rwa [mul_zero] at b
  exact ⟨ψ, hψt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) h1,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) h2⟩

theorem periodLIntegral_tendsto_zero {f : ℕ → ℝ → Space → ℝ} {g : ℝ → Space → ℝ}
    (hfm : ∀ k, AEStronglyMeasurable (fun z : ℝ × Space => f k z.1 z.2) volume)
    (hgm : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hle : ∀ k σ y, f k σ y ≤ g σ y) (hg : periodLIntegral g < ⊤)
    (hlim : ∀ᵐ z : ℝ × Space, Filter.Tendsto (fun k => f k z.1 z.2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => periodLIntegral (f k)) Filter.atTop (nhds 0) := by
  have e : ∀ k, periodLIntegral (f k) = ∫⁻ z, ENNReal.ofReal (f k z.1 z.2) ∂ModeL2Internal.slab :=
    fun k => ModeL2Internal.periodLIntegral_eq_slab (f k) ((hfm k).mono_ac ModeL2Internal.slab_ac)
  have eg : periodLIntegral g = ∫⁻ z, ENNReal.ofReal (g z.1 z.2) ∂ModeL2Internal.slab :=
    ModeL2Internal.periodLIntegral_eq_slab g (hgm.mono_ac ModeL2Internal.slab_ac)
  simp only [e]
  have h0 : (∫⁻ _z : ℝ × Space, (0 : ℝ≥0∞) ∂ModeL2Internal.slab) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_of_dominated_convergence' (fun z => ENNReal.ofReal (g z.1 z.2))
    (fun k => ((hfm k).mono_ac ModeL2Internal.slab_ac).aemeasurable.ennreal_ofReal)
    (fun k => Filter.Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (hle k z.1 z.2))
    (by rw [← eg]; exact hg.ne) ?_
  filter_upwards [ModeL2Internal.slab_ac.ae_le hlim] with z hz
  have := (ENNReal.continuous_ofReal.tendsto 0).comp hz
  rw [ENNReal.ofReal_zero] at this
  exact this

theorem ae_hasFDerivAt_joint {D : ℝ} (hW : IsWeakSecondDerivState W HW D) :
    ∀ᵐ z : ℝ × Space, HasFDerivAt (fderiv ℝ (W z.1)) (HW z.1 z.2) z.2 := by
  have hc : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    (PairingSplitInternal.contDiff_slice (V := W) hW.smooth (n := 0) (by norm_num)).continuous
  obtain ⟨H', hH'm, hH'e⟩ := hW.secondDeriv_measurable
  have hdm : MeasurableSet {z : ℝ × Space | DifferentiableAt ℝ (fderiv ℝ (W z.1)) z.2} :=
    measurableSet_of_differentiableAt_with_param ℝ (f := fun s x => fderiv ℝ (W s) x) hc
  have hhm : Measurable (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (W z.1)) z.2) :=
    measurable_fderiv_with_param ℝ (f := fun s x => fderiv ℝ (W s) x) hc
  set T : Set (ℝ × Space) := {z | DifferentiableAt ℝ (fderiv ℝ (W z.1)) z.2 ∧
      fderiv ℝ (fderiv ℝ (W z.1)) z.2 = H' z} with hTdef
  have hTm : MeasurableSet T := hdm.inter (measurableSet_eq_fun hhm hH'm.measurable)
  have hslice : ∀ᵐ σ : ℝ, ∀ᵐ y : Space, HW σ y = H' (σ, y) := by
    have h := hH'e
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  have hnull : (volume : Measure (ℝ × Space)) Tᶜ = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hTm.compl]
    filter_upwards [hslice] with σ hσ
    have hy : ∀ᵐ y : Space, (σ, y) ∈ T := by
      filter_upwards [hσ, Internal.WeakAeDiff.ae_hasFDerivAt hW σ] with y h1 h2
      exact ⟨h2.differentiableAt, h2.fderiv.trans h1⟩
    exact ae_iff.1 hy
  have hT : ∀ᵐ z : ℝ × Space, z ∈ T := ae_iff.2 hnull
  filter_upwards [hT, hH'e] with z h1 h2
  have e : HW z.1 z.2 = fderiv ℝ (fderiv ℝ (W z.1)) z.2 := h2.trans h1.2.symm
  rw [e]
  exact h1.1.hasFDerivAt

theorem smoothApprox_exists {D : ℝ} (hW : IsWeakSecondDerivState W HW D) :
    ∃ D' : ℝ, ∃ V : ℕ → ℝ → Space → Space,
      (∀ k, ContDiff ℝ 2 (fun z : ℝ × Space => V k z.1 z.2)) ∧ (∀ k, IsTimePeriodic (V k)) ∧
      (∀ k σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (V k σ) y‖ ≤ D' / (1 + ‖y‖) ^ (j + 1)) ∧
      (∀ σ y, Filter.Tendsto (fun k => V k σ y) Filter.atTop (nhds (W σ y))) ∧
      (∀ σ y, Filter.Tendsto (fun k => fderiv ℝ (V k σ) y) Filter.atTop (nhds (fderiv ℝ (W σ) y))) ∧
      (∀ᵐ z : ℝ × Space, Filter.Tendsto (fun k => fderiv ℝ (fun x => fderiv ℝ (V k z.1) x) z.2)
        Filter.atTop (nhds (HW z.1 z.2))) := by
  exact Internal.WeakMollify.smoothApprox_of hW
    (PairingSplitInternal.contDiff_slice (V := W) hW.smooth (n := 0) (by norm_num)).continuous
    (ae_hasFDerivAt_joint hW)

theorem fderiv_smoothRight_tendsto {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    {V : ℕ → ℝ → Space → Space} (hV : ∀ k, ContDiff ℝ 2 (fun z : ℝ × Space => V k z.1 z.2))
    {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) {A : Space →L[ℝ] Space →L[ℝ] Space}
    (h0 : Filter.Tendsto (fun k => V k σ y) Filter.atTop (nhds (W σ y)))
    (h1 : Filter.Tendsto (fun k => fderiv ℝ (V k σ) y) Filter.atTop (nhds (fderiv ℝ (W σ) y)))
    (h2 : Filter.Tendsto (fun k => fderiv ℝ (fun x => fderiv ℝ (V k σ) x) y) Filter.atTop (nhds A))
    (hA : HasFDerivAt (fderiv ℝ (W σ)) A y) :
    Filter.Tendsto (fun k => fderiv ℝ (smoothRight P (V k) v σ) y) Filter.atTop
      (nhds (fderiv ℝ (smoothRight P W v σ) y)) := by
  have hvs : ContDiff ℝ ∞ (v σ) := slice_of_joint hv.smooth σ
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (v σ))) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have hT : ContDiff ℝ ∞ (transportPart P v σ) := slice_of_joint (transport_contDiff P hv.smooth) σ
  have dT : DifferentiableAt ℝ (transportPart P v σ) y := (hT.differentiable (by simp)) y
  have dH : DifferentiableAt ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y := by
    have e : (fun x => secondDerivTrace (secondDerivField v σ x)) = fun x => traceCLM (fderiv ℝ (fderiv ℝ (v σ)) x) :=
      funext fun x => (traceCLM_apply _).symm
    rw [e]
    exact traceCLM.differentiableAt.comp y ((hD2.differentiable (by simp)) y)
  have dS : DifferentiableAt ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)) y :=
    dT.sub dH
  have dv : HasFDerivAt (v σ) (fderiv ℝ (v σ) y) y := ((hvs.differentiable (by simp)) y).hasFDerivAt
  have dDv : HasFDerivAt (fderiv ℝ (v σ)) (fderiv ℝ (fderiv ℝ (v σ)) y) y :=
    ((hD1.differentiable (by simp)) y).hasFDerivAt
  have key : ∀ (X : ℝ → Space → Space) (B : Space →L[ℝ] Space →L[ℝ] Space),
      HasFDerivAt (X σ) (fderiv ℝ (X σ) y) y → HasFDerivAt (fderiv ℝ (X σ)) B y →
      fderiv ℝ (smoothRight P X v σ) y = fderiv ℝ (fun x => transportPart P v σ x
          - secondDerivTrace (secondDerivField v σ x)) y
        + ((fderiv ℝ (v σ) y).comp (fderiv ℝ (X σ) y) + (fderiv ℝ (fderiv ℝ (v σ)) y).flip (X σ y))
        + ((fderiv ℝ (X σ) y).comp (fderiv ℝ (v σ) y) + B.flip (v σ y)) := by
    intro X B hX hB
    have e : smoothRight P X v σ = fun x => (transportPart P v σ x - secondDerivTrace (secondDerivField v σ x))
        + fderiv ℝ (v σ) x (X σ x) + fderiv ℝ (X σ) x (v σ x) := rfl
    rw [e]
    exact ((dS.hasFDerivAt.add (dDv.clm_apply hX)).add (hB.clm_apply dv)).fderiv
  have hWs : ContDiff ℝ 1 (W σ) := slice_of_joint hW.smooth σ
  have hVs : ∀ k, ContDiff ℝ 2 (V k σ) := fun k => slice_of_joint (hV k) σ
  have eW := key W A ((hWs.differentiable one_ne_zero) y).hasFDerivAt hA
  have eV : ∀ k, fderiv ℝ (smoothRight P (V k) v σ) y = _ := fun k =>
    key (V k) (fderiv ℝ (fun x => fderiv ℝ (V k σ) x) y) (((hVs k).differentiable (by norm_num)) y).hasFDerivAt
      ((((hVs k).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y).hasFDerivAt
  simp only [eV, eW]
  have c1 : Continuous (fun B : Space →L[ℝ] Space => (fderiv ℝ (v σ) y).comp B) :=
    continuous_const.clm_comp continuous_id
  have c2 : Continuous (fun u : Space => (fderiv ℝ (fderiv ℝ (v σ)) y).flip u) :=
    ((fderiv ℝ (fderiv ℝ (v σ)) y).flip).continuous
  have c3 : Continuous (fun B : Space →L[ℝ] Space => B.comp (fderiv ℝ (v σ) y)) :=
    continuous_id.clm_comp continuous_const
  have c4 : Continuous (fun B : Space →L[ℝ] Space →L[ℝ] Space => B.flip (v σ y)) :=
    (ContinuousLinearMap.apply ℝ _ (v σ y)).continuous.comp
      (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).continuous
  exact tendsto_const_nhds.add (((c1.tendsto _).comp h1).add ((c2.tendsto _).comp h0)) |>.add
    (((c3.tendsto _).comp h1).add ((c4.tendsto _).comp h2))

theorem smoothRight_approx {D : ℝ} (hW : IsWeakSecondDerivState W HW D) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) :
    ∃ G : ℕ → ℝ → Space → Space, (∀ k, ContDiff ℝ 1 (fun z : ℝ × Space => G k z.1 z.2)) ∧
      (∀ k, IsTimePeriodic (G k)) ∧ (∀ k, periodLIntegral (fun σ y => ‖G k σ y‖ ^ 2) < ⊤) ∧
      (∀ k, periodLIntegral (fun σ y => matSq (fderiv ℝ (G k σ) y)) < ⊤) ∧
      Filter.Tendsto (fun k => periodLIntegral (fun σ y => ‖G k σ y - smoothRight P W v σ y‖ ^ 2))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (G k σ) y) - curlVec (fderiv ℝ (smoothRight P W v σ) y)‖ ^ 2))
        Filter.atTop (nhds 0) := by
  obtain ⟨D', V, hV2, hVp, hVd, hVpos, hV1, hVH⟩ := smoothApprox_exists hW
  have hD := decay_iterated hW
  have hFc := smoothRight_continuous hW hv
  have hGc : ∀ k, ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P (V k) v z.1 z.2) :=
    fun k => smoothRight_contDiff' (hV2 k) hv
  refine ⟨fun k => smoothRight P (V k) v, hGc, fun k => smoothRight_periodic' (hVp k) hv,
    fun k => (smoothRight_square' (hV2 k) (hVp k) ⟨D', hVd k⟩ hv).2.2,
    fun k => smoothRight_fderiv_sq (hV2 k) (hVp k) ⟨D', hVd k⟩ hv, ?_, ?_⟩
  · have c1 := (transport_contDiff P hv.smooth).continuous.norm
    have c2v := (slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hv.smooth)).continuous.norm
    have c1v := (slice_contDiff hv.smooth).continuous.norm
    have cw := weighted_continuous hv.smooth.continuous
    have hb : ∀ E : ℝ, Continuous (fun z : ℝ × Space => ‖transportPart P v z.1 z.2‖
        + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖ + E * ‖fderiv ℝ (v z.1) z.2‖
        + E * (‖v z.1 z.2‖ / (1 + ‖z.2‖))) := fun E =>
      ((c1.add (continuous_const.mul c2v)).add (continuous_const.mul c1v)).add (continuous_const.mul cw)
    have hbm : ∀ E : ℝ, MemLp (fun z : ℝ × Space => ‖transportPart P v z.1 z.2‖
        + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖ + E * ‖fderiv ℝ (v z.1) z.2‖
        + E * (‖v z.1 z.2‖ / (1 + ‖z.2‖))) 2 periodProductMeasure := fun E =>
      (((memLp_transport hv).add ((memLp_deriv_two hv).const_mul 3)).add
        ((memLp_deriv_one hv).const_mul E)).add ((memLp_weighted hv).const_mul E)
    have hg := lt_top_of_memLp_real (h := fun σ y => (‖transportPart P v σ y‖
        + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ + D' * ‖fderiv ℝ (v σ) y‖
        + D' * (‖v σ y‖ / (1 + ‖y‖))) + (‖transportPart P v σ y‖
        + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ + D * ‖fderiv ℝ (v σ) y‖
        + D * (‖v σ y‖ / (1 + ‖y‖)))) ((hbm D').add (hbm D))
    refine periodLIntegral_tendsto_zero
      (fun k => (((hGc k).continuous.sub hFc).norm.pow 2).aestronglyMeasurable)
      ((((hb D').add (hb D)).pow 2).aestronglyMeasurable) (fun k σ y => ?_) hg
      (Filter.Eventually.of_forall fun z => ?_)
    · have a1 := smoothRight_norm_le P (hVd k) (v := v) σ y
      have a2 := smoothRight_norm_le P hD (v := v) σ y
      have a3 := norm_sub_le (smoothRight P (V k) v σ y) (smoothRight P W v σ y)
      have a0 := norm_nonneg (smoothRight P (V k) v σ y - smoothRight P W v σ y)
      show ‖smoothRight P (V k) v σ y - smoothRight P W v σ y‖ ^ 2 ≤ _
      nlinarith
    · have t : Filter.Tendsto (fun k => smoothRight P (V k) v z.1 z.2) Filter.atTop
          (nhds (smoothRight P W v z.1 z.2)) := by
        unfold smoothRight
        exact (tendsto_const_nhds.add (((fderiv ℝ (v z.1) z.2).continuous.tendsto _).comp (hVpos z.1 z.2))).add
          (((ContinuousLinearMap.apply ℝ Space (v z.1 z.2)).continuous.tendsto _).comp (hV1 z.1 z.2))
      have t2 := ((t.sub (tendsto_const_nhds (x := smoothRight P W v z.1 z.2))).norm.pow 2)
      simpa using t2
  · have hFm : Measurable (fun z : ℝ × Space => fderiv ℝ (smoothRight P W v z.1) z.2) :=
      measurable_fderiv_with_param ℝ (f := fun s x => smoothRight P W v s x) hFc
    have hFcm : AEStronglyMeasurable (fun z : ℝ × Space => curlVec (fderiv ℝ (smoothRight P W v z.1) z.2))
        volume := (continuous_curlVec.measurable.comp hFm).aestronglyMeasurable
    have hbm : ∀ E : ℝ, MemLp (fun z : ℝ × Space => derivBound P E v z) 2 periodProductMeasure := fun E =>
      (((memLp_transport_deriv hv).add ((memLp_deriv_three hv).const_mul 3)).add
        (((memLp_deriv_one hv).const_mul E).add ((memLp_deriv_two hv).const_mul E))).add
        (((memLp_deriv_one hv).const_mul E).add ((memLp_weighted hv).const_mul E))
    have hg := lt_top_of_memLp_real (h := fun σ y => 27 * (derivBound P D' v (σ, y) + derivBound P D v (σ, y)))
      (((hbm D').add (hbm D)).const_mul 27)
    refine periodLIntegral_tendsto_zero
      (fun k => (((PairingSplitInternal.continuous_curl (hGc k)).aestronglyMeasurable.sub hFcm).norm.pow 2))
      (((continuous_const.mul ((derivBound_continuous (D := D') hv).add
        (derivBound_continuous (D := D) hv))).pow 2).aestronglyMeasurable) (fun k σ y => ?_) hg ?_
    · have a1 := smoothRight_fderiv_norm_le P (hV2 k) (hVd k) hv σ y
      have a2 := fderiv_smoothRight_le hW hv σ y
      have a3 : ‖curlVec (fderiv ℝ (smoothRight P (V k) v σ) y) - curlVec (fderiv ℝ (smoothRight P W v σ) y)‖
          ≤ 27 * (derivBound P D' v (σ, y) + derivBound P D v (σ, y)) := by
        rw [curlVec_sub]
        refine (norm_curlVec_le _).trans ?_
        have := norm_sub_le (fderiv ℝ (smoothRight P (V k) v σ) y) (fderiv ℝ (smoothRight P W v σ) y)
        unfold derivBound
        linarith
      have a0 := norm_nonneg (curlVec (fderiv ℝ (smoothRight P (V k) v σ) y)
        - curlVec (fderiv ℝ (smoothRight P W v σ) y))
      show _ ≤ (27 * (derivBound P D' v (σ, y) + derivBound P D v (σ, y))) ^ 2
      nlinarith
    · filter_upwards [hVH, ae_hasFDerivAt_joint hW] with z h1 h2
      have t := fderiv_smoothRight_tendsto hv hV2 hW z.1 z.2 (hVpos z.1 z.2) (hV1 z.1 z.2) h1 h2
      have t2 := ((((continuous_curlVec.tendsto _).comp t).sub
        (tendsto_const_nhds (x := curlVec (fderiv ℝ (smoothRight P W v z.1) z.2)))).norm.pow 2)
      simpa using t2

theorem smoothRight_curlDensity (hSolMode : SolenoidalModeHolds) {D : ℝ} (hW : IsWeakSecondDerivState W HW D)
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) {Q : ℝ → Space → Space}
    (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (smoothRight P W v σ) y)‖ ^ 2))
        Filter.atTop (nhds 0) := by
  obtain ⟨G, hG1, hGp, hG2, hGd, hL2, hcurl⟩ := smoothRight_approx hW hv
  have hFs := smoothRight_square hW hv
  exact density_of_approx hSolMode (smoothRight_continuous hW hv) hFs.2.1 hFs.2.2 hQ hG1 hGp hG2 hGd hL2 hcurl

end Internal.WeakPairingSplit

open Internal.WeakPairingSplit in
theorem piecePairingSplitSmoothWeakHolds_of (hPars : Coercive.ModeSquareSumHolds)
    (hSolMode : Coercive.SolenoidalModeHolds) : PiecePairingSplitSmoothWeakHolds := by
  intro C nE nM m P h w W HW D w₀ epsSup epsGradSup ratio hadm hW _ v hv M Q hM hQ
  have hFs := smoothRight_square hW hv
  have hQs := Coercive.PairingSplitInternal.square_of_solenoidal hQ
  have hLself := Coercive.Internal.SmoothPairingClass.negSsp_solenoidal_self hv
  rw [Coercive.PairingSplitInternal.pairing_eq_solenoidal hSolMode hFs hQ
    ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, fun _ _ => rfl⟩]
  have u3 := Coercive.PairingSplitInternal.pairing_eq_solenoidal hSolMode hFs hQ hLself
  exact multiplier_pairing hPars hadm hv (smoothRight_hasCurlModes hW hv) (smoothRight_curl_square hW hv)
    u3.symm hM hQs (smoothRight_curlDensity hSolMode hW hv hQ)

end CoerciveWeak

end Breakdown
