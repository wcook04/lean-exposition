import Breakdown.Cert.FreeTransportReading
import Breakdown.Cert.GradInvSpec
import Breakdown.Cert.FreeTransportHeatLimit
import Breakdown.Cert.FreeTransportRescaled
import Breakdown.Cert.FreeTransportCirclePairing

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FreePerturbation

theorem lintegral_ball_sq_le (x : Freq.X) (r : ℝ) {w : Space → Space}
    (hw : w =ᵐ[volume] (velocity x : Space → Space)) :
    ∫⁻ y, ENNReal.ofReal (‖(Metric.closedBall (0 : Space) r).indicator w y‖ ^ 2) ≤
      (‖velocity‖ₑ * volume (Metric.closedBall (0 : Space) r) ^
        (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 * ‖x‖ₑ ^ 2 := by
  have hB : MeasurableSet (Metric.closedBall (0 : Space) r) := Metric.isClosed_closedBall.measurableSet
  have hwm : AEStronglyMeasurable w volume := (Lp.aestronglyMeasurable (velocity x)).congr hw.symm
  have e1 : ∫⁻ y, ENNReal.ofReal (‖(Metric.closedBall (0 : Space) r).indicator w y‖ ^ 2) =
      eLpNorm ((Metric.closedBall (0 : Space) r).indicator w) 2 volume ^ 2 := by
    rw [JointRepresentativeInternal.sq_eLpNorm_two]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have e2 : eLpNorm w 6 volume = ‖velocity x‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae hw
  have h3 : eLpNorm ((Metric.closedBall (0 : Space) r).indicator w) 2 volume ≤
      ‖velocity‖ₑ * volume (Metric.closedBall (0 : Space) r) ^
        (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) * ‖x‖ₑ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hB]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6) (by norm_num) hwm.restrict).trans ?_
    rw [Measure.restrict_apply_univ]
    have h4 : eLpNorm w 6 (volume.restrict (Metric.closedBall (0 : Space) r)) ≤ ‖velocity‖ₑ * ‖x‖ₑ :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (e2.le.trans (velocity.le_opENorm x))
    calc eLpNorm w 6 (volume.restrict (Metric.closedBall (0 : Space) r)) *
          volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)
        ≤ ‖velocity‖ₑ * ‖x‖ₑ *
          volume (Metric.closedBall (0 : Space) r) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
          by gcongr
      _ = _ := by ring
  rw [e1, ← mul_pow]
  exact pow_le_pow_left₀ zero_le h3 2

theorem integrable_inner_velocity {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (ψ z.1 z.2)) := by
  obtain ⟨r, hrb⟩ := hψs.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  have hB : MeasurableSet (Metric.closedBall (0 : Space) r) := Metric.isClosed_closedBall.measurableSet
  have hFm : AEStronglyMeasurable
      (fun z : ℝ × Space => (Metric.closedBall (0 : Space) r).indicator (v z.1) z.2) volume := by
    have e : (fun z : ℝ × Space => (Metric.closedBall (0 : Space) r).indicator (v z.1) z.2) =
        (Set.univ ×ˢ Metric.closedBall (0 : Space) r).indicator (fun z : ℝ × Space => v z.1 z.2) := by
      funext z
      by_cases hz : z.2 ∈ Metric.closedBall (0 : Space) r
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (Set.mk_mem_prod (Set.mem_univ _) hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem fun h => hz (Set.mem_prod.1 h).2]
    rw [e]
    exact hr.measurable_velocity.indicator (MeasurableSet.univ.prod hB)
  have hFp : IsTimePeriodic (fun σ y => (Metric.closedBall (0 : Space) r).indicator (v σ) y) :=
    fun σ y => by
    show (Metric.closedBall (0 : Space) r).indicator (v (σ + 1)) y = (Metric.closedBall (0 : Space) r).indicator (v σ) y
    rw [show v (σ + 1) = v σ from funext (hr.periodic_velocity σ)]
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = (‖velocity‖ₑ * volume (Metric.closedBall (0 : Space) r) ^
    (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 := ⟨_, rfl⟩
  have hKt : K < ⊤ := by
    rw [hK]
    refine ENNReal.pow_lt_top (ENNReal.mul_lt_top enorm_lt_top ?_)
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  have hc0 : ∀ᵐ t : TimeCircle, ((gradCLM u : HH) : TimeCircle → HBar) t =
      gradPart ((u : TimeCircle → XBar) t) := ContinuousLinearMap.coeFn_compLpL _ _
  have hc : ∀ᵐ σ : ℝ, ((gradCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle) =
      gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) :=
    (ae_coe_iff (fun t => ((gradCLM u : HH) : TimeCircle → HBar) t =
      gradPart ((u : TimeCircle → XBar) t))).1 hc0
  have hle : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (‖(Metric.closedBall (0 : Space) r).indicator (v σ) y‖ ^ 2) ≤
        K * ‖((gradCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle)‖ₑ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hr.velocity_eq, ae_restrict_of_ae hc] with σ h1 h2
    rw [hK]
    refine (lintegral_ball_sq_le _ r h1).trans_eq ?_
    exact congrArg (fun a : Freq.X => (‖velocity‖ₑ * volume (Metric.closedBall (0 : Space) r) ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 * ‖a‖ₑ ^ 2) h2.symm
  have hFf : periodLIntegral
      (fun σ y => ‖(Metric.closedBall (0 : Space) r).indicator (v σ) y‖ ^ 2) < ⊤ := by
    unfold periodLIntegral
    refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
    rw [lintegral_const_mul' _ _ hKt.ne]
    have hs := lintegral_sum_curve (fun _ : Unit => (gradCLM u : HH))
    simp only [Finset.univ_unique, Finset.sum_singleton] at hs
    exact ENNReal.mul_lt_top hKt hs
  have hi := integrable_inner_of_periodic hFm hFp hFf hψc hψs
  refine hi.congr (ae_of_all _ fun z => ?_)
  by_cases hz : z.2 ∈ Metric.closedBall (0 : Space) r
  · simp only [Set.indicator_of_mem hz]
  · have h0 : ψ z.1 z.2 = 0 := by
      refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => ψ z.1 z.2) fun ht => hz ?_
      have h1 := hrb ht
      rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
      exact (norm_snd_le z).trans h1
    simp only [h0, inner_zero_right]

def transportTest (P : ℝ) (φ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  -(1 / P) • deriv (fun s => φ s y) σ - φ σ y - (1 / 2 : ℝ) • fderiv ℝ (φ σ) y y

def sspTest (φ : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  ∑ j : Fin 3, fderiv ℝ (fun w => fderiv ℝ (φ σ) w (unitVector j)) y (unitVector j)

def sliceVelocityPairing (g : HH) (ψ : ℝ → Space → Space) : ℝ :=
  ∫ σ : ℝ, ∫ y, inner ℝ ((velocity ((g : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) y) (ψ σ y)

theorem deriv_time_eq {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (s : ℝ) (y : Space) : deriv (fun t => φ t y) s =
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) (ContinuousLinearMap.inl ℝ ℝ Space 1) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) := (hφ.differentiable (by simp)) _
  exact (hd.hasFDerivAt.comp s (hasFDerivAt_prodMk_left s y)).hasDerivAt.deriv

theorem contDiff_partialField {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) =
      fun z => fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inr ℝ ℝ Space (unitVector j)) := by
    funext z
    rw [fderiv_slice hφ z.1 z.2]
    rfl
  rw [h]
  exact (contDiff_infty_iff_fderiv.1 hφ).2.clm_apply contDiff_const

theorem transportTest_eq {P : ℝ} {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (s : ℝ) (y : Space) : transportTest P φ s y =
      -(1 / P) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)
        - φ s y - (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y)
          (ContinuousLinearMap.inr ℝ ℝ Space y) := by
  rw [transportTest, deriv_time_eq hφ s y, fderiv_slice hφ s y]
  rfl

theorem continuous_sspTest {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    Continuous (fun z : ℝ × Space => sspTest φ z.1 z.2) :=
  continuous_finsetSum _ fun j _ =>
    partial_continuous (φ := fun s w => fderiv ℝ (φ s) w (unitVector j)) (contDiff_partialField hφ.1 j) j

theorem hasCompactSupport_sspTest {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    HasCompactSupport (fun z : ℝ × Space => sspTest φ z.1 z.2) := by
  have hj : ∀ j : Fin 3, HasCompactSupport (fun z : ℝ × Space =>
      fderiv ℝ (fun w => fderiv ℝ (φ z.1) w (unitVector j)) z.2 (unitVector j)) := fun j =>
    partial_hasCompactSupport (φ := fun s w => fderiv ℝ (φ s) w (unitVector j)) (contDiff_partialField hφ.1 j)
      (partial_hasCompactSupport hφ.1 hφ.2 j) j
  have e : (fun z : ℝ × Space => sspTest φ z.1 z.2) =
      (fun z : ℝ × Space => fderiv ℝ (fun w => fderiv ℝ (φ z.1) w (unitVector 0)) z.2 (unitVector 0)) +
      (fun z : ℝ × Space => fderiv ℝ (fun w => fderiv ℝ (φ z.1) w (unitVector 1)) z.2 (unitVector 1)) +
      (fun z : ℝ × Space => fderiv ℝ (fun w => fderiv ℝ (φ z.1) w (unitVector 2)) z.2 (unitVector 2)) := by
    funext z
    simp only [sspTest, Fin.sum_univ_three, Pi.add_apply]
  rw [e]
  exact ((hj 0).add (hj 1)).add (hj 2)

theorem continuous_transportTest {P : ℝ} {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    Continuous (fun z : ℝ × Space => transportTest P φ z.1 z.2 - sspTest φ z.1 z.2) := by
  have hφc := hφ.1
  have e : (fun z : ℝ × Space => transportTest P φ z.1 z.2) = fun z =>
      -(1 / P) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1)
        - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z
          (ContinuousLinearMap.inr ℝ ℝ Space z.2) := by
    funext z
    exact transportTest_eq hφc z.1 z.2
  have hd := hφc.continuous_fderiv (by simp)
  have hT : Continuous (fun z : ℝ × Space => transportTest P φ z.1 z.2) := by
    rw [e]
    exact (((hd.clm_apply continuous_const).const_smul (-(1 / P))).sub hφc.continuous).sub
      ((hd.clm_apply ((ContinuousLinearMap.inr ℝ ℝ Space).continuous.comp continuous_snd)).const_smul (1 / 2 : ℝ))
  exact hT.sub (continuous_sspTest hφ)

theorem hasCompactSupport_transportTest {P : ℝ} {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    HasCompactSupport (fun z : ℝ × Space => transportTest P φ z.1 z.2 - sspTest φ z.1 z.2) := by
  have hφc := hφ.1
  have hT : HasCompactSupport (fun z : ℝ × Space => transportTest P φ z.1 z.2) := by
    refine hφ.2.mono' fun z hz => ?_
    by_contra hn
    obtain ⟨s, y⟩ := z
    have h0 : φ s y = 0 := image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) hn
    have h1 : fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) = 0 := by
      by_contra h2
      exact hn (support_fderiv_subset ℝ h2)
    apply hz
    show transportTest P φ s y = 0
    rw [transportTest_eq hφc s y, h1, h0]
    simp
  have e : (fun z : ℝ × Space => transportTest P φ z.1 z.2 - sspTest φ z.1 z.2) =
      (fun z : ℝ × Space => transportTest P φ z.1 z.2) + (fun a : Space => -a) ∘ (fun z : ℝ × Space => sspTest φ z.1 z.2) := by
    funext z
    simp only [Pi.add_apply, Function.comp_apply, sub_eq_add_neg]
  rw [e]
  exact hT.add ((hasCompactSupport_sspTest hφ).comp_left neg_zero)

theorem slice_column_velocity {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f g) {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (j k : Fin 3) :
    Integrable (fun y => ψ y k * g y (unitVector j) k) ∧
      Integrable (fun y => fderiv ℝ ψ y (unitVector j) k * f y k) ∧
      ∫ y, ψ y k * g y (unitVector j) k = -∫ y, fderiv ℝ ψ y (unitVector j) k * f y k := by
  have ht := isTestFunction_coord hψ hψs k
  have h := hw.2.2 _ ht j
  have hi1 : Integrable (fun y => ψ y k • g y (unitVector j)) :=
    (locallyIntegrable_column hw.2.1 j).integrable_smul_left_of_hasCompactSupport ht.1.continuous ht.2
  have hi2 : Integrable (fun y => fderiv ℝ (fun y => ψ y k) y (unitVector j) • f y) :=
    hw.1.integrable_smul_left_of_hasCompactSupport
      ((ht.1.continuous_fderiv (by simp)).clm_apply continuous_const) (ht.2.fderiv_apply (𝕜 := ℝ) _)
  have c1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp hi1
  have c2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp hi2
  refine ⟨c1.congr (ae_of_all _ fun y => ?_), c2.congr (ae_of_all _ fun y => ?_), ?_⟩
  · show (ψ y k • g y (unitVector j)) k = _
    simp only [PiLp.smul_apply, smul_eq_mul]
  · show (fderiv ℝ (fun y => ψ y k) y (unitVector j) • f y) k = _
    simp only [PiLp.smul_apply, smul_eq_mul, fderiv_coord hψ]
  have e1 := congrArg (fun w : Space => w k) h
  simp only [PiLp.neg_apply] at e1
  have e2 : ∫ y, (ψ y k • g y (unitVector j)) k = (∫ y, ψ y k • g y (unitVector j)) k :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hi1
  have e3 : ∫ y, (fderiv ℝ (fun y => ψ y k) y (unitVector j) • f y) k =
      (∫ y, fderiv ℝ (fun y => ψ y k) y (unitVector j) • f y) k :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hi2
  rw [← e2, ← e3] at e1
  simp only [PiLp.smul_apply, smul_eq_mul, fderiv_coord hψ] at e1
  exact e1

theorem slice_byParts_velocity {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f g) {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, matInner (g y) (fderiv ℝ ψ y) =
      -∫ y, inner ℝ (f y) (∑ j : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (unitVector j)) y (unitVector j)) := by
  have hψj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun w => fderiv ℝ ψ w (unitVector j)) := fun j =>
    (contDiff_infty_iff_fderiv.1 hψ).2.clm_apply contDiff_const
  have hψjs : ∀ j : Fin 3, HasCompactSupport (fun w => fderiv ℝ ψ w (unitVector j)) := fun j =>
    hψs.fderiv_apply (𝕜 := ℝ) _
  have hI := fun j k => slice_column_velocity hw (hψj j) (hψjs j) j k
  have hl : (fun y => matInner (g y) (fderiv ℝ ψ y)) =
      fun y => ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ ψ y (unitVector j) k * g y (unitVector j) k := by
    funext y
    simp only [matInner, inner_eq_sum_coord, mul_comm]
  have hr : (fun y => inner ℝ (f y)
      (∑ j : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (unitVector j)) y (unitVector j))) =
      fun y => ∑ j : Fin 3, ∑ k : Fin 3,
        fderiv ℝ (fun w => fderiv ℝ ψ w (unitVector j)) y (unitVector j) k * f y k := by
    funext y
    rw [inner_eq_sum_coord]
    simp only [coord_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hl, hr, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hI j k).1,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hI j k).2.1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (hI j k).1, integral_finsetSum _ fun k _ => (hI j k).2.1,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => (hI j k).2.2

theorem integral_matInner_eq_ssp {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) =
      -∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2) := by
  have hfi := (integral_matInner_eq hr φ hφ).1
  have hli := integrable_inner_velocity hr (ψ := sspTest φ) (continuous_sspTest hφ) (hasCompactSupport_sspTest hφ)
  rw [Measure.volume_eq_prod] at hfi hli ⊢
  rw [integral_prod _ hfi, integral_prod _ hli, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hr.weak_gradient] with σ hσ
  exact slice_byParts_velocity hσ (contDiff_slice hφ.1 σ) (hasCompactSupport_slice hφ.2 σ)

theorem integral_inner_velocity_eq_slices {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (ψ z.1 z.2) = sliceVelocityPairing (gradCLM u) ψ := by
  have hi := integrable_inner_velocity hr hψc hψs
  have hc0 : ∀ᵐ t : TimeCircle, ((gradCLM u : HH) : TimeCircle → HBar) t =
      gradPart ((u : TimeCircle → XBar) t) := ContinuousLinearMap.coeFn_compLpL _ _
  have hc : ∀ᵐ σ : ℝ, ((gradCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle) =
      gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) :=
    (ae_coe_iff (fun t => ((gradCLM u : HH) : TimeCircle → HBar) t =
      gradPart ((u : TimeCircle → XBar) t))).1 hc0
  have e1 : ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (ψ z.1 z.2) = ∫ σ : ℝ, ∫ y, inner ℝ (v σ y) (ψ σ y) := by
    rw [Measure.volume_eq_prod] at hi ⊢
    exact integral_prod _ hi
  have e2 : (∫ σ : ℝ, ∫ y, inner ℝ (v σ y) (ψ σ y)) = ∫ σ : ℝ, ∫ y, inner ℝ
      ((velocity (((gradCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) y) (ψ σ y) := by
    refine integral_congr_ae ?_
    filter_upwards [hr.velocity_eq, hc] with σ h1 h2
    refine integral_congr_ae ?_
    have h3 : (velocity (((gradCLM u : HH) : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) =
        (velocity (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) :=
      congrArg (fun a : Freq.X => (velocity a : Space → Space)) h2
    filter_upwards [h1] with y hy
    exact congrArg (fun a => inner ℝ a (ψ σ y)) (hy.trans (congrFun h3 y).symm)
  exact e1.trans e2

set_option maxHeartbeats 1000000 in
theorem exists_velocity_pairing_bound {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Freq.X,
      (∃ g : Space → ℝ, Integrable g ∧
        ∀ r y, ‖inner ℝ ((velocity h : Space → Space) y) (ψ r y)‖ ≤ g y) ∧
      ∀ r : ℝ, Integrable (fun y => inner ℝ ((velocity h : Space → Space) y) (ψ r y)) ∧
        |∫ y, inner ℝ ((velocity h : Space → Space) y) (ψ r y)| ≤ C * ‖h‖ := by
  obtain ⟨R, hR⟩ := hψs.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψs
  have hB : MeasurableSet (Metric.closedBall (0 : Space) R) := Metric.isClosed_closedBall.measurableSet
  have hBt : volume (Metric.closedBall (0 : Space) R) < ⊤ := measure_closedBall_lt_top
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = volume (Metric.closedBall (0 : Space) R) ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  have hVt : V < ⊤ := by
    rw [hV]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBt.ne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0))
  refine ⟨M * (‖velocity‖ₑ * V).toReal, mul_nonneg hM0 ENNReal.toReal_nonneg, fun h => ?_⟩
  have hwm : AEStronglyMeasurable (velocity h : Space → Space) volume := Lp.aestronglyMeasurable _
  have hzero : ∀ r y, y ∉ Metric.closedBall (0 : Space) R → ψ r y = 0 := fun r y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => ψ z.1 z.2) (x := (r, y)) fun ht => hy (by
      have h1 := hR ht
      rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
      exact (norm_snd_le _).trans h1)
  have hpt : ∀ r y, ‖inner ℝ ((velocity h : Space → Space) y) (ψ r y)‖ ≤
      M * ‖(Metric.closedBall (0 : Space) R).indicator (velocity h : Space → Space) y‖ := fun r y => by
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      calc ‖inner ℝ ((velocity h : Space → Space) y) (ψ r y)‖
          ≤ ‖(velocity h : Space → Space) y‖ * ‖ψ r y‖ := norm_inner_le_norm _ _
        _ ≤ ‖(velocity h : Space → Space) y‖ * M := by
          gcongr
          exact hM (r, y)
        _ = M * ‖(velocity h : Space → Space) y‖ := mul_comm _ _
    · rw [hzero r y hy, inner_zero_right, Set.indicator_of_notMem hy, norm_zero, norm_zero, mul_zero]
  have hL1 : eLpNorm ((Metric.closedBall (0 : Space) R).indicator (velocity h : Space → Space)) 1 volume ≤
      ‖velocity‖ₑ * V * ‖h‖ₑ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hB]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 6) (by norm_num) hwm.restrict).trans ?_
    rw [Measure.restrict_apply_univ]
    have e2 : eLpNorm (velocity h : Space → Space) 6 volume = ‖velocity h‖ₑ := (Lp.enorm_def (velocity h)).symm
    have h4 : eLpNorm (velocity h : Space → Space) 6 (volume.restrict (Metric.closedBall (0 : Space) R)) ≤
        ‖velocity‖ₑ * ‖h‖ₑ :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (e2.le.trans (velocity.le_opENorm h))
    calc eLpNorm (velocity h : Space → Space) 6 (volume.restrict (Metric.closedBall (0 : Space) R)) *
          volume (Metric.closedBall (0 : Space) R) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)
        ≤ ‖velocity‖ₑ * ‖h‖ₑ *
          volume (Metric.closedBall (0 : Space) R) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
          gcongr
      _ = ‖velocity‖ₑ * V * ‖h‖ₑ := by
          rw [hV]
          ring
  have hfin : ‖velocity‖ₑ * V * ‖h‖ₑ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top hVt) enorm_lt_top
  have hI1 : Integrable ((Metric.closedBall (0 : Space) R).indicator (velocity h : Space → Space)) :=
    memLp_one_iff_integrable.1 ⟨hwm.indicator hB, hL1.trans_lt hfin⟩
  have hg := hI1.norm.const_mul M
  refine ⟨⟨_, hg, hpt⟩, fun r => ?_⟩
  have hmeas : AEStronglyMeasurable (fun y => inner ℝ ((velocity h : Space → Space) y) (ψ r y)) volume :=
    hwm.inner (hψc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hg.mono' hmeas (ae_of_all _ (hpt r)), ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ (hpt r))).trans ?_
  rw [integral_const_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  rw [integral_norm_eq_lintegral_enorm hI1.1, ← eLpNorm_one_eq_lintegral_enorm]
  calc (eLpNorm ((Metric.closedBall (0 : Space) R).indicator (velocity h : Space → Space)) 1 volume).toReal
      ≤ (‖velocity‖ₑ * V * ‖h‖ₑ).toReal := ENNReal.toReal_mono hfin.ne hL1
    _ = (‖velocity‖ₑ * V).toReal * ‖h‖ := by rw [ENNReal.toReal_mul, toReal_enorm]

set_option maxHeartbeats 1000000 in
theorem continuous_velocity_pairing {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    Continuous (fun p : ℝ × Freq.X => ∫ y, inner ℝ ((velocity p.2 : Space → Space) y) (ψ p.1 y)) := by
  obtain ⟨C, -, hC⟩ := exists_velocity_pairing_bound (ψ := ψ) hψc hψs
  have hlin : ∀ (r : ℝ) (h h' : Freq.X), (∫ y, inner ℝ ((velocity h : Space → Space) y) (ψ r y)) -
      ∫ y, inner ℝ ((velocity h' : Space → Space) y) (ψ r y) =
        ∫ y, inner ℝ ((velocity (h - h') : Space → Space) y) (ψ r y) := by
    intro r h h'
    rw [← integral_sub ((hC h).2 r).1 ((hC h').2 r).1]
    refine integral_congr_ae ?_
    have e : ((velocity (h - h') : L6R) : Space → Space) =ᵐ[volume]
        (velocity h : Space → Space) - (velocity h' : Space → Space) := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [e] with y hy
    rw [hy, Pi.sub_apply, inner_sub_left]
  rw [continuous_iff_continuousAt]
  rintro ⟨r0, h0⟩
  have hcr : Continuous (fun r => ∫ y, inner ℝ ((velocity h0 : Space → Space) y) (ψ r y)) := by
    obtain ⟨g, hgi, hgb⟩ := (hC h0).1
    refine continuous_of_dominated (bound := g) (fun r => ((hC h0).2 r).1.1)
      (fun r => ae_of_all _ (hgb r)) hgi (ae_of_all _ fun y => ?_)
    exact continuous_const.inner (hψc.comp (continuous_id.prodMk continuous_const))
  have h1 : Tendsto (fun p : ℝ × Freq.X => ∫ y, inner ℝ ((velocity (p.2 - h0) : Space → Space) y) (ψ p.1 y))
      (𝓝 (r0, h0)) (𝓝 0) := by
    refine squeeze_zero_norm (fun p => (Real.norm_eq_abs _).le.trans ((hC _).2 p.1).2) ?_
    have h5 : Tendsto (fun p : ℝ × Freq.X => C * ‖p.2 - h0‖) (𝓝 (r0, h0)) (𝓝 (C * ‖h0 - h0‖)) :=
      ((continuous_const.mul ((continuous_snd.sub continuous_const).norm))).tendsto _
    rw [sub_self, norm_zero, mul_zero] at h5
    exact h5
  have h2 : Tendsto (fun p : ℝ × Freq.X => ∫ y, inner ℝ ((velocity h0 : Space → Space) y) (ψ p.1 y))
      (𝓝 (r0, h0)) (𝓝 (∫ y, inner ℝ ((velocity h0 : Space → Space) y) (ψ r0 y))) :=
    (hcr.comp continuous_fst).tendsto (r0, h0)
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr' (Eventually.of_forall fun p => ?_)
  show (∫ y, inner ℝ ((velocity (p.2 - h0) : Space → Space) y) (ψ p.1 y)) +
      ∫ y, inner ℝ ((velocity h0 : Space → Space) y) (ψ p.1 y) =
    ∫ y, inner ℝ ((velocity p.2 : Space → Space) y) (ψ p.1 y)
  rw [← hlin, sub_add_cancel]

private theorem isSlicePairingBound_velocity {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    ∃ C R : ℝ, Internal.SlicePairingSwap.IsSlicePairingBound
      (fun r h => ∫ y, inner ℝ ((velocity h : Space → Space) y) (ψ r y)) C R := by
  have hE := exists_velocity_pairing_bound (ψ := ψ) hψc hψs
  have hRb := hψs.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  have hC := hE.choose_spec.2
  have hR := hRb.choose_spec
  refine ⟨hE.choose, hRb.choose, continuous_velocity_pairing hψc hψs, hE.choose_spec.1, ?_, ?_,
    fun r h => ((hC h).2 r).2, ?_⟩
  · intro r h h'
    rw [← integral_add ((hC h).2 r).1 ((hC h').2 r).1]
    refine integral_congr_ae ?_
    have e : ((velocity (h + h') : L6R) : Space → Space) =ᵐ[volume]
        (velocity h : Space → Space) + (velocity h' : Space → Space) := by
      rw [map_add]
      exact Lp.coeFn_add _ _
    filter_upwards [e] with y hy
    rw [hy, Pi.add_apply, inner_add_left]
  · intro r c h
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : ((velocity (c • h) : L6R) : Space → Space) =ᵐ[volume] c • (velocity h : Space → Space) := by
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [e] with y hy
    rw [hy, Pi.smul_apply, real_inner_smul_left]
  · intro r h hr
    have hz : ∀ y, ψ r y = 0 := fun y =>
      image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => ψ z.1 z.2) (x := (r, y)) fun ht => hr (by
        have h1 := hR ht
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        have h2 : |r| ≤ hRb.choose := (le_of_eq (Real.norm_eq_abs _).symm).trans ((norm_fst_le _).trans h1)
        exact ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩)
    simp only [hz, inner_zero_right, integral_zero]

theorem slicePairing_gradInv_eq_Ioi (hB : PropagatorBoundHolds) (hG : GradInvHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) {ψ : ℝ → Space → Space} (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    sliceVelocityPairing (gradInv P f) ψ =
      ∫ τ in Set.Ioi (0 : ℝ), ∫ σ : ℝ, ∫ y, inner ℝ
        ((velocity (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) : Space → Space) y)
        (ψ (σ + τ / P) y) :=
  Internal.SlicePairingSwap.circlePairing_gradInv (isSlicePairingBound_velocity hψc hψs).choose_spec.choose_spec P f

theorem integral_swap_propagator (hB : PropagatorBoundHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) {ψ : ℝ → Space → Space} (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    ∫ τ in Set.Ioi (0 : ℝ), ∫ σ : ℝ, ∫ y, inner ℝ
        ((velocity (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) : Space → Space) y)
        (ψ (σ + τ / P) y) =
      ∫ σ : ℝ, ∫ τ in Set.Ioi (0 : ℝ), ∫ y, inner ℝ
        ((velocity (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) : Space → Space) y)
        (ψ (σ + τ / P) y) :=
  Internal.SlicePairingSwap.integral_swap_kernelPairing (isSlicePairingBound_velocity hψc hψs).choose_spec.choose_spec P f

theorem propagator_weak_derivative (hB : PropagatorBoundHolds) (x : HBar) {χ : ℝ → Space → Space}
    (hχ : IsSpaceTimeTestVector χ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y))
      (∫ y, inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)
        (deriv (fun r => χ r y) τ + sspTest χ τ y + χ τ y + (1 / 2 : ℝ) • fderiv ℝ (χ τ) y y)) τ :=
  Internal.PropagatorDerivative.hasDerivAt_pairing_slicePropagator x hχ hτ

theorem propagator_initial_trace (hB : PropagatorBoundHolds) (x : HBar) {χ : ℝ → Space → Space}
    (hχc : Continuous (fun z : ℝ × Space => χ z.1 z.2))
    (hχs : HasCompactSupport (fun z : ℝ × Space => χ z.1 z.2)) :
    Tendsto (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y))
      (𝓝[>] 0) (𝓝 (∫ y, inner ℝ ((toPhysH x : Space → Space) y) (χ 0 y))) :=
  tendsto_propagator_pairing x hχc hχs

theorem integrableOn_propagator_pairing (hB : PropagatorBoundHolds) (x : HBar) {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    IntegrableOn (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (ψ r y))
      (Set.Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_velocity_pairing_bound hψc hψs
  have hcont : ContinuousOn
      (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (ψ r y)) (Set.Ioi 0) :=
    (continuous_velocity_pairing (ψ := ψ) hψc hψs).comp_continuousOn (f := fun r : ℝ => ((r, slicePropagator r x) : ℝ × Freq.X)) ((continuousOn_id' _).prodMk (hB.2 x))
  refine Integrable.mono' ((GradInv.Internal.integrableOn_kernel.mul_const ‖x‖).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_)
  rw [Real.norm_eq_abs]
  refine ((hC _).2 r).2.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (GradInv.Internal.norm_slicePropagator_op_le hr) (norm_nonneg _))

theorem continuous_timeShift {ψ : ℝ → Space → Space} (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (s P : ℝ) : Continuous (fun z : ℝ × Space => ψ (s + z.1 / P) z.2) :=
  hψc.comp ((continuous_const.add (continuous_fst.div_const P)).prodMk continuous_snd)

theorem hasCompactSupport_timeShift {ψ : ℝ → Space → Space}
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) (s : ℝ) {P : ℝ} (hP : P ≠ 0) :
    HasCompactSupport (fun z : ℝ × Space => ψ (s + z.1 / P) z.2) := by
  have hc : Continuous (fun w : ℝ × Space => (P * (w.1 - s), w.2)) :=
    (continuous_const.mul (continuous_fst.sub continuous_const)).prodMk continuous_snd
  refine HasCompactSupport.intro (hψs.isCompact.image hc) fun z hz => ?_
  refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => ψ z.1 z.2)
    (x := (s + z.1 / P, z.2)) fun ht => hz ⟨(s + z.1 / P, z.2), ht, ?_⟩
  refine Prod.ext ?_ rfl
  show P * (s + z.1 / P - s) = z.1
  rw [add_sub_cancel_left]
  field_simp

theorem slicePairing_gradInv_eq (hB : PropagatorBoundHolds) (hG : GradInvHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) {ψ : ℝ → Space → Space} (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    sliceVelocityPairing (gradInv P f) ψ =
      ∫ σ : ℝ, ∫ τ in Set.Ioi (0 : ℝ), ∫ y, inner ℝ
        ((velocity (slicePropagator τ ((f : TimeCircle → HBar) (σ : TimeCircle))) : Space → Space) y)
        (ψ (σ + τ / P) y) := by
  rw [slicePairing_gradInv_eq_Ioi hB hG hP f hψc hψs, integral_swap_propagator hB hP f hψc hψs]

theorem propagator_transport_pairing (hB : PropagatorBoundHolds) {P : ℝ} (hP : 0 < P) (x : HBar)
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) (s : ℝ) :
    ∫ τ in Set.Ioi (0 : ℝ), ∫ y, inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)
        (transportTest P φ (s + τ / P) y - sspTest φ (s + τ / P) y) =
      ∫ y, inner ℝ ((toPhysH x : Space → Space) y) (φ s y) := by
  have hP0 : P ≠ 0 := hP.ne'
  have hχt : IsSpaceTimeTestVector (fun r y => φ (s + r / P) y) :=
    ⟨hφ.1.comp ((contDiff_const.add (contDiff_fst.div_const P)).prodMk contDiff_snd),
      hasCompactSupport_timeShift hφ.2 s hP0⟩
  have hdt : ∀ r y, deriv (fun r => φ (s + r / P) y) r = (1 / P) • deriv (fun σ => φ σ y) (s + r / P) := by
    intro r y
    have hd : HasDerivAt (fun σ => φ σ y) (deriv (fun σ => φ σ y) (s + r / P)) (s + r / P) := by
      have h0 : DifferentiableAt ℝ (fun z : ℝ × Space => φ z.1 z.2) (s + r / P, y) :=
        (hφ.1.differentiable (by simp)) _
      exact (h0.hasFDerivAt.comp (s + r / P)
        (hasFDerivAt_prodMk_left (s + r / P) y)).hasDerivAt.differentiableAt.hasDerivAt
    have hg : HasDerivAt (fun r => s + r / P) (1 / P) r := ((hasDerivAt_id r).div_const P).const_add s
    exact (hd.scomp r hg).deriv
  have key : ∀ τ y, deriv (fun r => φ (s + r / P) y) τ + sspTest (fun r y => φ (s + r / P) y) τ y +
      φ (s + τ / P) y + (1 / 2 : ℝ) • fderiv ℝ (fun y => φ (s + τ / P) y) y y =
      -(transportTest P φ (s + τ / P) y - sspTest φ (s + τ / P) y) := by
    intro τ y
    rw [hdt]
    simp only [transportTest, sspTest, neg_smul]
    abel
  have hQ' : ∀ τ, 0 < τ → HasDerivAt
      (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (φ (s + r / P) y))
      (-∫ y, inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)
        (transportTest P φ (s + τ / P) y - sspTest φ (s + τ / P) y)) τ := by
    intro τ hτ
    have h1 := propagator_weak_derivative hB x hχt hτ
    refine h1.congr_deriv ?_
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hk : deriv (fun r => φ (s + r / P) y) τ + sspTest (fun r y => φ (s + r / P) y) τ y +
        φ (s + τ / P) y + (1 / 2 : ℝ) • fderiv ℝ (fun y => φ (s + τ / P) y) y y =
        -(transportTest P φ (s + τ / P) y - sspTest φ (s + τ / P) y) := key τ y
    exact (congrArg (inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)) hk).trans
      (inner_neg_right _ _)
  have hψc := continuous_timeShift (ψ := fun σ y => transportTest P φ σ y - sspTest φ σ y)
    (continuous_transportTest (P := P) hφ) s P
  have hψs := hasCompactSupport_timeShift (ψ := fun σ y => transportTest P φ σ y - sspTest φ σ y)
    (hasCompactSupport_transportTest (P := P) hφ) s hP0
  have hint := (integrableOn_propagator_pairing
    (ψ := fun r y => transportTest P φ (s + r / P) y - sspTest φ (s + r / P) y) hB x hψc hψs).neg
  have h2 := propagator_initial_trace (χ := fun r y => φ (s + r / P) y) hB x hχt.1.continuous hχt.2
  simp only [zero_div, add_zero] at h2
  obtain ⟨R, hR⟩ := hφ.2.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  let L0 : ℝ := ∫ y, inner ℝ ((toPhysH x : Space → Space) y) (φ s y)
  let g : ℝ → ℝ := fun r => if 0 < r then
    ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (φ (s + r / P) y) else L0
  have hg0 : g 0 = L0 := if_neg (lt_irrefl 0)
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    refine continuousWithinAt_Ioi_iff_Ici.mp ?_
    show Tendsto g (𝓝[>] 0) (𝓝 (g 0))
    rw [hg0]
    exact h2.congr' (eventually_nhdsWithin_of_forall fun r hr => (if_pos hr).symm)
  have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt g
      (-∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y)
        (transportTest P φ (s + r / P) y - sspTest φ (s + r / P) y)) r := by
    intro r hr
    refine (hQ' r hr).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hr] with t ht
    exact if_pos ht
  have htend : Tendsto g atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max 0 (P * (R - s)))] with r hr
    have hr0 : 0 < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hr1 : P * (R - s) < r := lt_of_le_of_lt (le_max_right _ _) hr
    have hlt : R < s + r / P := by
      have : R - s < r / P := by
        rw [lt_div_iff₀ hP]
        linarith [mul_comm P (R - s)]
      linarith
    show 0 = if 0 < r then _ else L0
    rw [if_pos hr0]
    have hz : ∀ y, φ (s + r / P) y = 0 := fun y =>
      image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) (x := (s + r / P, y)) fun ht => by
        have h3 := hR ht
        rw [Metric.mem_closedBall, dist_zero_right] at h3
        have h4 : |s + r / P| ≤ R := (le_of_eq (Real.norm_eq_abs _).symm).trans ((norm_fst_le _).trans h3)
        linarith [le_abs_self (s + r / P)]
    simp only [hz, inner_zero_right, integral_zero]
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [integral_neg, hg0, zero_sub, neg_inj] at hF
  exact hF

theorem integral_inner_of_slices (f : HH) {F : ℝ → Space → Space}
    (hF : IsPeriodicField F)
    (hFs : ∀ᵐ σ : ℝ, F σ =ᵐ[volume] (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space))
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      ∫ σ : ℝ, ∫ y, inner ℝ ((toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) y) (φ σ y) := by
  have hi := integrable_inner_of_periodic hF.1 hF.2.1 hF.2.2 hφ.1.continuous hφ.2
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  refine integral_congr_ae ?_
  filter_upwards [hFs] with σ hσ
  refine integral_congr_ae ?_
  filter_upwards [hσ] with y hy
  exact congrArg (fun a => inner ℝ a (φ σ y)) hy

theorem mild_slice_pairing (hB : PropagatorBoundHolds) (hG : GradInvHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) {F : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hFs : ∀ᵐ σ : ℝ, F σ =ᵐ[volume] (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space))
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    sliceVelocityPairing (gradInv P f) (fun σ y => transportTest P φ σ y - sspTest φ σ y) =
      ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) := by
  rw [slicePairing_gradInv_eq hB hG hP f (ψ := fun σ y => transportTest P φ σ y - sspTest φ σ y)
    (continuous_transportTest (P := P) hφ) (hasCompactSupport_transportTest (P := P) hφ),
    integral_inner_of_slices f hF hFs φ hφ]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  exact propagator_transport_pairing hB hP _ φ hφ σ

theorem freeInvSpec_of (hInv : FreeInvHolds) {P : ℝ} (hP : 0 < P) : FreeInvSpec P (freeInv P) := by
  have h := (hInv P hP).1
  unfold freeInv
  rw [dif_pos h]
  exact h.choose_spec

theorem mild_transport (hInv : FreeInvHolds) (hB : PropagatorBoundHolds) (hG : GradInvHolds)
    {P : ℝ} (hP : 0 < P)
    (f : HH) {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf (freeInv P f) v G H)
    {F : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hFs : ∀ᵐ σ : ℝ, F σ =ᵐ[volume] (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space))
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2) =
      (∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2))
        - ∫ z : ℝ × Space, matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) := by
  have hbase := mild_slice_pairing hB hG hP f hF hFs φ hφ
  have hsl := integral_inner_velocity_eq_slices hr
    (ψ := fun σ y => transportTest P φ σ y - sspTest φ σ y) (continuous_transportTest (P := P) hφ)
    (hasCompactSupport_transportTest (P := P) hφ)
  have hspec : gradCLM (freeInv P f) = gradInv P f := freeInvSpec_of hInv hP f
  have hsl' : ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2 - sspTest φ z.1 z.2) =
      ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) :=
    hsl.trans ((congrArg (fun g => sliceVelocityPairing g
      (fun σ y => transportTest P φ σ y - sspTest φ σ y)) hspec).trans hbase)
  have hssp := integral_matInner_eq_ssp hr φ hφ
  have iL := integrable_inner_velocity hr (ψ := sspTest φ) (continuous_sspTest hφ) (hasCompactSupport_sspTest hφ)
  have iD := integrable_inner_velocity hr
    (ψ := fun σ y => transportTest P φ σ y - sspTest φ σ y) (continuous_transportTest (P := P) hφ)
    (hasCompactSupport_transportTest (P := P) hφ)
  have iT : Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2)) :=
    (iD.add iL).congr (ae_of_all _ fun z =>
      (congrArg (fun a => a + inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2))
        (inner_sub_right (v z.1 z.2) (transportTest P φ z.1 z.2) (sspTest φ z.1 z.2))).trans
        (sub_add_cancel _ _))
  have e1 : (∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2 - sspTest φ z.1 z.2)) = (∫ z : ℝ × Space, (inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2) - inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2))) :=
    congrArg (fun g : ℝ × Space → ℝ => ∫ z, g z) (funext fun z => inner_sub_right (v z.1 z.2) (transportTest P φ z.1 z.2) (sspTest φ z.1 z.2))
  have e2 : (∫ z : ℝ × Space, (inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2) - inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2))) = ((∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2)) - ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2)) := integral_sub iT iL
  have e3 : ((∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (transportTest P φ z.1 z.2)) - ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (sspTest φ z.1 z.2)) = ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) := (e1.trans e2).symm.trans hsl'
  exact (eq_add_of_sub_eq e3).trans ((sub_neg_eq_add _ _).symm.trans
    (congrArg (fun a => (∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2)) - a) hssp.symm))

end Internal.FreePerturbation

end Breakdown.Cert
