import Breakdown.Cert.CoerciveSmoothPairingSplitClass
import Breakdown.Cert.CoerciveSmoothPiecePairingSplitDensity

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothModeSplit

open ModeL2Internal (IsSquareField weightedModeTerm weightedMode_bound integrable_weightedMode)
open PairingSplitInternal (epsTerm muTerm modeSum)

theorem cdot_scaled (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) (Z : Fin 3 → ℂ) :
    cdot (modeVel ι v σ y) Z
      = ((1 + ‖y‖ : ℝ) : ℂ) * cdot (modeVel ι (SmoothWeightSplit.scaledField v) σ y) Z := by
  unfold cdot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothWeightSplit.modeVel_eq_scaled v ι σ y i]
  ring

theorem mu_integrand_eq {C : Type} (m : ModeWeights C) (v X : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) :
    (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι X σ y)).re
      = (Complex.I * ((m.muW (m.classOf ι) y * (1 + ‖y‖) : ℝ) : ℂ)
        * cdot (modeVel ι (SmoothWeightSplit.scaledField v) σ y) (modeVel ι X σ y)).re := by
  congr 1
  rw [cdot_scaled v ι σ y]
  push_cast
  ring

theorem muTerm_eq {C : Type} (m : ModeWeights C) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) :
    muTerm m v X ι = weightedModeTerm (fun ι y => m.muW (m.classOf ι) y * (1 + ‖y‖))
      (SmoothWeightSplit.scaledField v) X ι := by
  unfold muTerm weightedModeTerm
  simp only [mu_integrand_eq]

theorem epsTerm_eq {C : Type} (m : ModeWeights C) {v X : ℝ → Space → Space}
    (hv : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2)) (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2))
    (ι : ℤ × ℤ) :
    epsTerm m v X ι = weightedModeTerm (fun ι y => m.epsW (m.classOf ι) y)
      (fun s x => curlVec (fderiv ℝ (v s) x)) (fun s x => curlVec (fderiv ℝ (X s) x)) ι := by
  unfold epsTerm weightedModeTerm
  simp only [PairingSplitInternal.curlOfGrad_modeGrad hv, PairingSplitInternal.curlOfGrad_modeGrad hX]

theorem modeSum_tendsto_smooth (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) {P : ℝ}
    {b : FlowBounds C} {w : Space → ℝ} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsSmoothPerturbation P v) {F Q : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hFp : IsTimePeriodic F)
    (hFd : periodLIntegral (fun σ y => matSq (fderiv ℝ (F σ) y)) < ⊤) (hQ : IsSolenoidalPartOf F Q)
    (ψ : ℕ → ℝ → Space → Space) (hψ : ∀ n, IsPeriodicTestField (ψ n))
    (h1 : Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) atTop (nhds 0))
    (h2 : Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (nhds 0)) :
    Tendsto (fun n => modeSum m v (ψ n)) atTop
      (nhds (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v F
        + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q)) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  have hψ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => ψ n z.1 z.2) := fun n => (hψ n).1.of_le (by norm_cast)
  have hcv : IsSquareField (fun σ y => curlVec (fderiv ℝ (v σ) y)) :=
    SmoothWeightSplit.curl_square_of_fderiv hv1 hv.periodic (SmoothWeightSplit.perturbation_fderiv_sq hv)
  have hcF : IsSquareField (fun σ y => curlVec (fderiv ℝ (F σ) y)) :=
    SmoothWeightSplit.curl_square_of_fderiv hF hFp hFd
  have hcψ : ∀ n, IsSquareField (fun σ y => curlVec (fderiv ℝ (ψ n σ) y)) := fun n =>
    PairingSplitInternal.curl_square (hψ1 n) (hψ n).2.1 (hψ n).2.2.1
  have hsv := SmoothWeightSplit.scaledField_square hv
  have hQs := PairingSplitInternal.square_of_solenoidal hQ
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => PairingSplitInternal.testField_square (hψ n)
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hwE : ∀ ι y, |(fun ι y => m.epsW (m.classOf ι) y) ι y| ≤ epsSup := fun ι y => hm.epsW_le _ y
  have hwEm : ∀ ι, Measurable ((fun ι y => m.epsW (m.classOf ι) y) ι) := fun ι => by
    obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
    exact hK.continuous.measurable
  have hwM : ∀ ι y, |(fun ι y => m.muW (m.classOf ι) y * (1 + ‖y‖)) ι y| ≤ 2 * B := fun ι y => by
    show |m.muW (m.classOf ι) y * (1 + ‖y‖)| ≤ 2 * B
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖y‖), mul_comm]
    exact SmoothWeightSplit.one_add_norm_mul_le (f := fun y => |m.muW (m.classOf ι) y|)
      (fun y => abs_nonneg _) (fun y => ⟨(hB _ y).1, (hB _ y).2.1⟩) y
  have hwMm : ∀ ι, Measurable ((fun ι y => m.muW (m.classOf ι) y * (1 + ‖y‖)) ι) := fun ι => by
    obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
    exact (hK.continuous.mul (continuous_const.add continuous_norm)).measurable
  obtain ⟨KE, hKE⟩ := weightedMode_bound hPars _ hwEm hwE hcv
  obtain ⟨KM, hKM⟩ := weightedMode_bound hPars _ hwMm hwM hsv
  have tE := PairingSplitInternal.tsum_tendsto_of_bound (fun n => (hKE _ _ (hcψ n) hcF).1) (hKE _ _ hcF hcF).1
    (fun n => (hKE _ _ (hcψ n) hcF).2.1) (fun n => (hKE _ _ (hcψ n) hcF).2.2)
    (by simpa only [mul_zero] using (PairingSplitInternal.sqrt_toReal_tendsto h2).const_mul KE)
  have tM := PairingSplitInternal.tsum_tendsto_of_bound (fun n => (hKM _ _ (hψs n) hQs).1) (hKM _ _ hQs hQs).1
    (fun n => (hKM _ _ (hψs n) hQs).2.1) (fun n => (hKM _ _ (hψs n) hQs).2.2)
    (by simpa only [mul_zero] using (PairingSplitInternal.sqrt_toReal_tendsto h1).const_mul KM)
  have lE : epsPairing (fun ι y => m.epsW (m.classOf ι) y) v F
      = ∑' ι, weightedModeTerm (fun ι y => m.epsW (m.classOf ι) y)
          (fun s x => curlVec (fderiv ℝ (v s) x)) (fun s x => curlVec (fderiv ℝ (F s) x)) ι :=
    tsum_congr fun ι => epsTerm_eq m hv1 hF ι
  have lM : muPairing (fun ι y => m.muW (m.classOf ι) y) v Q
      = ∑' ι, weightedModeTerm (fun ι y => m.muW (m.classOf ι) y * (1 + ‖y‖))
          (SmoothWeightSplit.scaledField v) Q ι :=
    tsum_congr fun ι => muTerm_eq m v Q ι
  have hsplit : ∀ n, modeSum m v (ψ n)
      = (∑' ι, weightedModeTerm (fun ι y => m.epsW (m.classOf ι) y)
          (fun s x => curlVec (fderiv ℝ (v s) x)) (fun s x => curlVec (fderiv ℝ (ψ n s) x)) ι)
        + ∑' ι, weightedModeTerm (fun ι y => m.muW (m.classOf ι) y * (1 + ‖y‖))
          (SmoothWeightSplit.scaledField v) (ψ n) ι := by
    intro n
    rw [← (hKE _ _ (hcψ n) hcF).1.tsum_add (hKM _ _ (hψs n) hQs).1]
    refine tsum_congr fun ι => ?_
    have iE : Integrable (fun z : ℝ × Space => (Complex.I * (m.epsW (m.classOf ι) z.2 : ℂ)
        * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2))
          (curlOfGrad (modeGrad ι (gradField (ψ n)) z.1 z.2))).re)
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
      simp only [PairingSplitInternal.curlOfGrad_modeGrad hv1, PairingSplitInternal.curlOfGrad_modeGrad (hψ1 n)]
      exact integrable_weightedMode hPars _ hwEm hwE hcv (hcψ n) ι
    have iM : Integrable (fun z : ℝ × Space => (Complex.I * (m.muW (m.classOf ι) z.2 : ℂ)
        * cdot (modeVel ι v z.1 z.2) (modeVel ι (ψ n) z.1 z.2)).re)
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
      simp only [mu_integrand_eq]
      exact integrable_weightedMode hPars _ hwMm hwM hsv (hψs n) ι
    rw [← epsTerm_eq m hv1 (hψ1 n) ι, ← muTerm_eq m v (ψ n) ι]
    unfold epsTerm muTerm
    rw [← integral_prod _ iE, ← integral_prod _ iM, ← integral_add iE iM]
    exact (integral_prod _ (iE.add iM)).symm
  rw [lE, lM]
  exact (tE.add tM).congr fun n => (hsplit n).symm

theorem solenoidal_multiplier_pairing_smooth (hPars : ModeSquareSumHolds) (hSolMode : SolenoidalModeHolds) {C : Type}
    (m : ModeWeights C) {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W : ℝ → Space → Space}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWd : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) {M Q : ℝ → Space → Space}
    (hM : m.IsMultiplierField v (gradField v) (secondDerivField v) M) (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    periodPairing Q M =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
        + epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
        + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q := by
  have hFc := SmoothPairingClass.smoothRight_contDiff' hW hv
  have hFp := SmoothPairingClass.smoothRight_periodic' hWp hv
  have hFs := SmoothPairingClass.smoothRight_square' hW hWp hWd hv
  have hFd := SmoothPairingClass.smoothRight_fderiv_sq hW hWp hWd hv
  obtain ⟨ψ, hψt, hL2, hcurl⟩ := SmoothWeightSplit.curlGraphDensityL2 hSolMode (smoothRight P W v) Q hFc hFp hFs.2.2 hFd hQ
  have hQs := PairingSplitInternal.square_of_solenoidal hQ
  have hMs : IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => PairingSplitInternal.testField_square (hψt n)
  have hLself := SmoothPairingClass.negSsp_solenoidal_self hv
  have hLs := PairingSplitInternal.square_of_solenoidal hLself
  have hseq : ∀ n, periodPairing M (ψ n) =
      periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) (ψ n) + modeSum m v (ψ n) :=
    fun n => hM.2.2.2.2 (ψ n) (hψt n)
  have t1 := PairingSplitInternal.pairing_tendsto hMs hQs hψs hL2
  have t2 := PairingSplitInternal.pairing_tendsto hLs hQs hψs hL2
  have t3 := modeSum_tendsto_smooth hPars m hm hv hFc hFp hFd hQ ψ hψt hL2 hcurl
  have t5 : Tendsto (fun n => periodPairing M (ψ n)) atTop
      (nhds (periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q
        + (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
          + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q))) :=
    (t2.add t3).congr fun n => (hseq n).symm
  have hlim := tendsto_nhds_unique t1 t5
  have hL : periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) := by
    rw [PairingSplitInternal.pairing_comm hLs hQs]
    exact (PairingSplitInternal.pairing_eq_solenoidal hSolMode hFs hQ hLself).symm
  rw [PairingSplitInternal.pairing_comm hQs hMs, hlim, hL]
  ring

end Internal.SmoothModeSplit

theorem modePairingSplitSmoothHolds_of (hPars : ModeSquareSumHolds) (hSolMode : SolenoidalModeHolds) :
    ModePairingSplitSmoothHolds := by
  intro C m P b w W w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb v hv M Q hM hQ
  rw [PairingSplitInternal.pairing_eq_solenoidal hSolMode
    (Internal.SmoothPairingClass.smoothRight_square' hW hWp hWdecay hv) hQ
    (PairingSplitInternal.solenoidal_self_of_multiplier m hM)]
  exact Internal.SmoothModeSplit.solenoidal_multiplier_pairing_smooth hPars hSolMode m hm hW hWp hWdecay hv hM hQ

end Coercive

end Breakdown
