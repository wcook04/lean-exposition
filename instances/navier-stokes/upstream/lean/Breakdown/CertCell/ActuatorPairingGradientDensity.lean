import Breakdown.CertCell.ActuatorPairingGradientModes
import Breakdown.Cert.ExtendedCoercivePairingSplit
import Breakdown.Cert.CoerciveSmoothApproxLimits
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound
import Breakdown.Cert.CoerciveSmoothCurlWeight

open scoped ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.ActuatorPairingGradient

open Coercive.ModeL2Internal

theorem opNorm_sq_le_columnSq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have h := Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply A
  have h0 : 0 ≤ ‖A‖ := norm_nonneg _
  unfold matSq
  simp only [Fin.sum_univ_three] at h ⊢
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖), sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖),
    norm_nonneg (A (unitVector 0)), norm_nonneg (A (unitVector 1)), norm_nonneg (A (unitVector 2))]

variable {C : Type} {nE nM : ℕ} {w : PieceWeights C nE nM} {b : ℝ → Space → Space}

theorem actuator_square (hb : Instance.ActuatorFacts w b) : IsSquareField b :=
  ⟨hb.measurable, hb.periodic, hb.square_finite⟩

theorem gradField_norm_sq_finite (hb : Instance.ActuatorFacts w b) :
    periodLIntegral (fun σ y => ‖gradField b σ y‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt (b := ENNReal.ofReal 3 * periodLIntegral (fun σ y => matSq (gradField b σ y))) ?_
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.gradient_finite)
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (opNorm_sq_le_columnSq _)

theorem gradField_locallyIntegrable (hb : Instance.ActuatorFacts w b) :
    LocallyIntegrable (fun z : ℝ × Space => gradField b z.1 z.2) volume := by
  have hcol : ∀ i, LocallyIntegrable (fun z : ℝ × Space => ‖gradField b z.1 z.2 (unitVector i)‖) volume :=
    fun i => Cert.Internal.CoerciveBordered.column_locallyIntegrable hb.gradient_measurable
      hb.gradient_periodic hb.gradient_finite i
  have hs := locallyIntegrable_finsetSum Finset.univ fun i _ => hcol i
  refine hs.mono hb.gradient_measurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply _

theorem curl_actuator_square (hb : Instance.ActuatorFacts w b) :
    IsSquareField (fun σ y => curlVec (fderiv ℝ (b σ) y)) := by
  refine ⟨Coercive.Internal.CurlEnergy.continuous_curlVec.comp_aestronglyMeasurable hb.gradient_measurable,
    fun σ y => ?_, ?_⟩
  · have e := hb.gradient_periodic σ y
    simp only [gradField] at e
    show curlVec (fderiv ℝ (b (σ + 1)) y) = curlVec (fderiv ℝ (b σ) y)
    rw [e]
  · refine lt_of_le_of_lt (b := ENNReal.ofReal 3 * periodLIntegral (fun σ y => matSq (gradField b σ y))) ?_
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.gradient_finite)
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal ((Coercive.SmoothCurlWeight.Internal.curl_sq_le _).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _)))

theorem mollify_eq_conv (n : ℕ) (f : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    Coercive.Internal.SmoothApprox.mollify n f σ y =
      ∫ t, Coercive.Internal.SmoothApprox.kernel n t • Coercive.Internal.SmoothApprox.joint f ((σ, y) - t) := by
  rw [Coercive.Internal.SmoothApprox.mollify, convolution_def]
  rfl

theorem periodLIntegral_le_const_mul {f g : ℝ → Space → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ σ y, f σ y ≤ c * g σ y) :
    periodLIntegral f ≤ ENNReal.ofReal c * periodLIntegral g := by
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (h σ y)

theorem mollified_actuator (hb : Instance.ActuatorFacts w b) (k : ℕ) :
    ContDiff ℝ 1 (fun z : ℝ × Space => Coercive.Internal.SmoothApprox.mollify k b z.1 z.2) ∧
    IsTimePeriodic (Coercive.Internal.SmoothApprox.mollify k b) ∧
    periodLIntegral (fun σ y => ‖Coercive.Internal.SmoothApprox.mollify k b σ y‖ ^ 2) < ⊤ ∧
    periodLIntegral (fun σ y => matSq (fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y)) < ⊤ ∧
    (∀ σ y, fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y =
      (Coercive.Internal.SmoothApprox.kernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Coercive.Internal.SmoothApprox.joint (gradField b)) (σ, y)) := by
  have hbl : LocallyIntegrable (Coercive.Internal.SmoothApprox.joint b) volume :=
    locallyIntegrable_of_square (actuator_square hb)
  have hgl : LocallyIntegrable (Coercive.Internal.SmoothApprox.joint (gradField b)) volume :=
    gradField_locallyIntegrable hb
  have hfd : ∀ σ y, fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y =
      (Coercive.Internal.SmoothApprox.kernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Coercive.Internal.SmoothApprox.joint (gradField b)) (σ, y) := fun σ y => by
    rw [Coercive.Internal.SmoothApprox.mollify_fderiv_clm k hbl hgl (Eventually.of_forall hb.weak_gradient) σ]
  have hk1 := Coercive.Internal.SmoothApprox.lintegral_kernel_eq_one k
  refine ⟨(Coercive.Internal.SmoothApprox.mollify_smooth k hbl).of_le (by simp),
    Coercive.Internal.SmoothApprox.mollify_periodic k hb.periodic, ?_, ?_, hfd⟩
  · have h := Coercive.Internal.SmoothApprox.period_convolution_sq_le
      (Coercive.Internal.SmoothApprox.kernel_contDiff k).continuous
      (Coercive.Internal.SmoothApprox.kernel_hasCompactSupport k) (w := b) hb.measurable hb.periodic
    rw [hk1, one_pow, one_mul] at h
    simp only [← mollify_eq_conv] at h
    exact lt_of_le_of_lt h hb.square_finite
  · have h := Coercive.Internal.SmoothApprox.period_convolution_sq_le
      (Coercive.Internal.SmoothApprox.kernel_contDiff k).continuous
      (Coercive.Internal.SmoothApprox.kernel_hasCompactSupport k) (w := gradField b) hb.gradient_measurable
      hb.gradient_periodic
    rw [hk1, one_pow, one_mul] at h
    refine lt_of_le_of_lt (periodLIntegral_le_const_mul (c := 3) (by norm_num) fun σ y => ?_)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt h (gradField_norm_sq_finite hb)))
    rw [hfd σ y, convolution_def]
    exact Coercive.Internal.SmoothApprox.matSq_le_three_sq _

theorem mollified_tendsto (hb : Instance.ActuatorFacts w b) :
    Tendsto (fun k => periodLIntegral (fun σ y => ‖Coercive.Internal.SmoothApprox.mollify k b σ y - b σ y‖ ^ 2))
      atTop (𝓝 0) :=
  Coercive.Internal.SmoothApprox.convolution_sq_tendsto (w := b) hb.measurable hb.periodic hb.square_finite

theorem mollified_curl_tendsto (hb : Instance.ActuatorFacts w b) :
    Tendsto (fun k => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y) - curlVec (fderiv ℝ (b σ) y)‖ ^ 2))
      atTop (𝓝 0) := by
  have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 6)
    (Coercive.Internal.SmoothApprox.convolution_sq_tendsto (w := gradField b) hb.gradient_measurable
      hb.gradient_periodic (gradField_norm_sq_finite hb)) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) (fun k => ?_)
  refine periodLIntegral_le_const_mul (by norm_num) fun σ y => ?_
  rw [(mollified_actuator hb k).2.2.2.2 σ y, Coercive.Internal.SmoothWeightSplit.curlVec_sub]
  refine (Coercive.SmoothCurlWeight.Internal.curl_sq_le _).trans ?_
  have h := Coercive.Internal.SmoothApprox.matSq_le_three_sq
    ((Coercive.Internal.SmoothApprox.kernel k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Coercive.Internal.SmoothApprox.joint (gradField b)) (σ, y) - fderiv ℝ (b σ) y)
  simp only [gradField]
  linarith

theorem actuator_density (hb : Instance.ActuatorFacts w b) {Q : ℝ → Space → Space}
    (hQ : Coercive.IsSolenoidalPartOf b Q) :
    ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (b σ) y)‖ ^ 2)) atTop (𝓝 0) := by
  have hSol := CoerciveWeak.solenoidalModeHolds_closed
  have hbm : AEStronglyMeasurable (fun z : ℝ × Space => curlVec (fderiv ℝ (b z.1) z.2)) volume :=
    (curl_actuator_square hb).1
  have key : ∀ j : ℕ, ∃ ψ : ℝ → Space → Space, IsPeriodicTestField ψ ∧
      periodLIntegral (fun σ y => ‖ψ σ y - Q σ y‖ ^ 2) ≤ 4 * ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧
      periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ σ) y) - curlVec (fderiv ℝ (b σ) y)‖ ^ 2)
        ≤ 4 * ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    set δ := ENNReal.ofReal (1 / ((j : ℝ) + 1)) with hδ
    have hδpos : 0 < δ := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨k, hk1, hk2⟩ := (((tendsto_order.1 (mollified_tendsto hb)).2 δ hδpos).and
      ((tendsto_order.1 (mollified_curl_tendsto hb)).2 δ hδpos)).exists
    obtain ⟨hG1, hGp, hG2, hGd, -⟩ := mollified_actuator hb k
    have hGm : AEStronglyMeasurable (fun z : ℝ × Space => Coercive.Internal.SmoothApprox.mollify k b z.1 z.2)
        volume := hG1.continuous.aestronglyMeasurable
    obtain ⟨Qk, hQk, -⟩ := hSol _ hGm hGp hG2
    obtain ⟨ψ, hψt, h1, h2⟩ := Coercive.Internal.SmoothWeightSplit.curlGraphDensityL2 hSol _ Qk hG1 hGp hG2 hGd hQk
    obtain ⟨m, hm1, hm2⟩ := (((tendsto_order.1 h1).2 δ hδpos).and ((tendsto_order.1 h2).2 δ hδpos)).exists
    have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ m z.1 z.2) := (hψt m).1.of_le (by simp)
    refine ⟨ψ m, hψt m, ?_, ?_⟩
    · have hle := Coercive.Internal.SmoothWeightSplit.solenoidal_diff_le hSol hGm hGp hG2 hb.measurable
        hb.periodic hb.square_finite hQk hQ
      calc periodLIntegral (fun σ y => ‖ψ m σ y - Q σ y‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y => ‖ψ m σ y - Qk σ y‖ ^ 2)
            + 2 * periodLIntegral (fun σ y => ‖Qk σ y - Q σ y‖ ^ 2) :=
            Coercive.Internal.SmoothWeightSplit.periodLIntegral_triangle hψ1.continuous.aestronglyMeasurable
              hQk.1 hQ.1
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
            exact hle.trans hk1.le
        _ = 4 * δ := by ring
    · calc periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ m σ) y) - curlVec (fderiv ℝ (b σ) y)‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ m σ) y)
              - curlVec (fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y)‖ ^ 2)
            + 2 * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y)
              - curlVec (fderiv ℝ (b σ) y)‖ ^ 2) :=
            Coercive.Internal.SmoothWeightSplit.periodLIntegral_triangle
              (X := fun σ y => curlVec (fderiv ℝ (ψ m σ) y))
              (Y := fun σ y => curlVec (fderiv ℝ (Coercive.Internal.SmoothApprox.mollify k b σ) y))
              (Z := fun σ y => curlVec (fderiv ℝ (b σ) y))
              (Coercive.PairingSplitInternal.continuous_curl hψ1).aestronglyMeasurable
              (Coercive.PairingSplitInternal.continuous_curl hG1).aestronglyMeasurable hbm
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
        _ = 4 * δ := by ring
  choose ψ hψt h1 h2 using key
  have hlim : Tendsto (fun j : ℕ => 4 * ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    have a : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have b := ENNReal.Tendsto.const_mul a (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    rwa [mul_zero] at b
  exact ⟨ψ, hψt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) h1,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) h2⟩

theorem secondTrace_sub (A B : Space →L[ℝ] Space →L[ℝ] Space) :
    secondDerivTrace (A - B) = secondDerivTrace A - secondDerivTrace B := by
  simp [secondDerivTrace, Finset.sum_sub_distrib]

theorem secondTrace_sq_le (A : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondDerivTrace A‖ ^ 2 ≤ 3 * Coercive.secondDerivSq A := by
  unfold secondDerivTrace Coercive.secondDerivSq
  simp only [Fin.sum_univ_three]
  have h1 : ‖A (unitVector 0) (unitVector 0) + A (unitVector 1) (unitVector 1) + A (unitVector 2) (unitVector 2)‖
      ≤ ‖A (unitVector 0) (unitVector 0)‖ + ‖A (unitVector 1) (unitVector 1)‖ + ‖A (unitVector 2) (unitVector 2)‖ :=
    norm_add₃_le
  have h0 := norm_nonneg (A (unitVector 0) (unitVector 0) + A (unitVector 1) (unitVector 1)
    + A (unitVector 2) (unitVector 2))
  nlinarith [sq_nonneg (‖A (unitVector 0) (unitVector 0)‖ - ‖A (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1) (unitVector 1)‖ - ‖A (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0) (unitVector 0)‖ - ‖A (unitVector 2) (unitVector 2)‖),
    norm_nonneg (A (unitVector 0) (unitVector 0)), norm_nonneg (A (unitVector 1) (unitVector 1)),
    norm_nonneg (A (unitVector 2) (unitVector 2)),
    sq_nonneg ‖A (unitVector 0) (unitVector 1)‖, sq_nonneg ‖A (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖A (unitVector 1) (unitVector 0)‖, sq_nonneg ‖A (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖A (unitVector 2) (unitVector 0)‖, sq_nonneg ‖A (unitVector 2) (unitVector 1)‖]

theorem continuous_negTrace : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => -secondDerivTrace A) := by
  unfold secondDerivTrace
  exact (continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const).neg

theorem negTrace_square {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    IsSquareField (fun σ y => -secondDerivTrace (H σ y)) :=
  ⟨continuous_negTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv,
    fun σ y => by simp only [hv.periodic_secondDeriv σ y],
    by simpa only [norm_neg] using hv.sumSecondPartials_finite⟩

theorem negTrace_solenoidal_self {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    Coercive.IsSolenoidalPartOf (fun σ y => -secondDerivTrace (H σ y)) (fun σ y => -secondDerivTrace (H σ y)) := by
  have hs := negTrace_square hv
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_, fun _ _ => rfl⟩
  intro q hq
  obtain ⟨u, hu1, -, hu3, -, -⟩ := Coercive.smoothApproximationHolds_proof Γ P v G H g hv
  have hself : ∀ n, Coercive.IsSolenoidalPartOf (fun σ y => -secondDerivTrace (secondDerivField (u n) σ y))
      (fun σ y => -secondDerivTrace (secondDerivField (u n) σ y)) := fun n =>
    Coercive.Internal.SmoothPairingClass.negSsp_solenoidal_self (hu1 n)
  have hconv : Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖-secondDerivTrace (secondDerivField (u n) σ y) - -secondDerivTrace (H σ y)‖ ^ 2)) atTop (𝓝 0) := by
    have hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 3) hu3 (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le) (fun n => ?_)
    refine periodLIntegral_le_const_mul (by norm_num) fun σ y => ?_
    rw [neg_sub_neg, norm_sub_rev, ← secondTrace_sub]
    exact secondTrace_sq_le _
  have hgs := Coercive.PairingSplitInternal.gradient_square hq
  have T := Coercive.PairingSplitInternal.pairing_tendsto hgs hs
    (fun n => Coercive.PairingSplitInternal.square_of_solenoidal (hself n)) hconv
  have hz : ∀ n, periodPairing (fun σ y => gradientAt (q σ) y)
      (fun σ y => -secondDerivTrace (secondDerivField (u n) σ y)) = 0 := fun n => by
    rw [Coercive.PairingSplitInternal.pairing_comm hgs (Coercive.PairingSplitInternal.square_of_solenoidal (hself n))]
    exact (hself n).2.2.2.1 q hq
  have hlim0 : periodPairing (fun σ y => gradientAt (q σ) y) (fun σ y => -secondDerivTrace (H σ y)) = 0 :=
    tendsto_nhds_unique T (tendsto_const_nhds.congr fun n => (hz n).symm)
  rw [Coercive.PairingSplitInternal.pairing_comm hgs hs] at hlim0
  exact hlim0

end Internal.ActuatorPairingGradient

end CertCell

end Breakdown
