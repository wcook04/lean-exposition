import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.HeldContracts

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.AtProfile

theorem weighted_sub_le {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ a, 0 ≤ τ a) (x y : Fin m → ℝ) :
    Real.sqrt (∑ a, τ a * (x a - y a) ^ 2) ≤
      Real.sqrt (∑ a, τ a * x a ^ 2) + Real.sqrt (∑ a, τ a * y a ^ 2) := by
  have hX : 0 ≤ ∑ a, τ a * x a ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hY : 0 ≤ ∑ a, τ a * y a ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => Real.sqrt (τ a) * x a)
    (fun a => -(Real.sqrt (τ a) * y a))
  have e1 : ∀ a, (Real.sqrt (τ a) * x a) ^ 2 = τ a * x a ^ 2 := fun a => by
    rw [mul_pow, Real.sq_sqrt (hτ a)]
  have e2 : ∀ a, (-(Real.sqrt (τ a) * y a)) ^ 2 = τ a * y a ^ 2 := fun a => by
    rw [neg_sq, mul_pow, Real.sq_sqrt (hτ a)]
  have e3 : ∀ a, Real.sqrt (τ a) * x a * -(Real.sqrt (τ a) * y a) = -(τ a * x a * y a) := fun a => by
    have h := Real.mul_self_sqrt (hτ a)
    linear_combination (-(x a * y a)) * h
  simp only [e1, e2, e3, Finset.sum_neg_distrib] at hcs
  have hexp : ∑ a, τ a * (x a - y a) ^ 2 =
      ∑ a, τ a * x a ^ 2 - 2 * ∑ a, τ a * x a * y a + ∑ a, τ a * y a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine Real.sqrt_le_sqrt ?_
  rw [hexp, add_sq, Real.sq_sqrt hX, Real.sq_sqrt hY]
  linarith

theorem rowNorm_div {m : ℕ} (e : Fin m → ℝ → Space → Space) (τ : Fin m → ℝ)
    (F : ℝ → Space → Space) {c : ℝ} (hc : 0 < c) :
    rowNorm e (fun a => τ a / c ^ 2) F = rowNorm e τ F / c := by
  unfold rowNorm
  have h : ∑ a, τ a / c ^ 2 * periodPairing F (e a) ^ 2 =
      (∑ a, τ a * periodPairing F (e a) ^ 2) / c ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h, Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le]

theorem pairing_eq_inner {F M : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hM : IsPeriodicField M) :
    periodPairing F M =
      inner ℝ ((Coercive.Internal.Field.memLp_of_period hF.1 hF.2.2).toLp
          (fun z : ℝ × Space => F z.1 z.2))
        ((Coercive.Internal.Field.memLp_of_period hM.1 hM.2.2).toLp
          (fun z : ℝ × Space => M z.1 z.2)) := by
  rw [Coercive.Internal.Field.inner_toLp,
    Coercive.Internal.PassageLimit.periodPairing_eq_integral
      (Coercive.Internal.PassageLimit.period_integrable_inner hF.1 hM.1 hF.2.2 hM.2.2)]

theorem rows_sub_le {m : ℕ} (e : Fin m → ℝ → Space → Space) (τ : Fin m → ℝ) (B : ℝ)
    (he : ∀ a, IsPeriodicField (e a))
    (hon : ∀ a b, periodPairing (e a) (e b) = if a = b then 1 else 0)
    (hτ0 : ∀ a, 0 ≤ τ a) (hτB : ∀ a, τ a ≤ B ^ 2) (hB : 0 ≤ B)
    {F T : ℝ → Space → Space} (hF : IsPeriodicField F) (hT : IsPeriodicField T)
    (hD2 : periodLIntegral (fun σ y => ‖F σ y - T σ y‖ ^ 2) < ⊤) :
    rowNorm e τ (fun σ y => F σ y - T σ y) ≤ rowNorm e τ F + B * periodNorm T := by
  have hlin : ∀ a, periodPairing (fun σ y => F σ y - T σ y) (e a) =
      periodPairing F (e a) - periodPairing T (e a) := by
    intro a
    rw [Coercive.Internal.PassageLimit.periodPairing_comm _ (e a),
      Coercive.Internal.PassageLimit.periodPairing_comm F (e a),
      Coercive.Internal.PassageLimit.periodPairing_comm T (e a)]
    exact (Coercive.Internal.PassageLimit.periodPairing_sub_right (he a).1 hF.1 hT.1 (he a).2.2
      hF.2.2 hT.2.2 hD2).symm
  have hcoeffSq : Real.sqrt (∑ a, τ a * periodPairing T (e a) ^ 2) ≤ B * periodNorm T := by
    have hTL := Coercive.Internal.Field.memLp_of_period hT.1 hT.2.2
    have hon' : Orthonormal ℝ (fun a => (Coercive.Internal.Field.memLp_of_period (he a).1
        (he a).2.2).toLp (fun z : ℝ × Space => e a z.1 z.2)) := by
      rw [orthonormal_iff_ite]
      intro a b
      rw [← pairing_eq_inner (he a) (he b)]
      exact hon a b
    have hsumInner := hon'.sum_inner_products_le (x := hTL.toLp (fun z : ℝ × Space => T z.1 z.2))
      (s := Finset.univ)
    have hnorm := Coercive.Internal.Field.norm_toLp_eq_periodNorm hTL
    have hsum : ∑ a, periodPairing T (e a) ^ 2 ≤ periodNorm T ^ 2 := by
      rw [← hnorm]
      refine le_trans (le_of_eq ?_) hsumInner
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [pairing_eq_inner hT (he a), real_inner_comm, Real.norm_eq_abs, sq_abs]
    have hPN : 0 ≤ periodNorm T := Real.sqrt_nonneg _
    calc Real.sqrt (∑ a, τ a * periodPairing T (e a) ^ 2)
        ≤ Real.sqrt (B ^ 2 * ∑ a, periodPairing T (e a) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_right (hτB a) (sq_nonneg _)
      _ ≤ Real.sqrt (B ^ 2 * periodNorm T ^ 2) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum (sq_nonneg B))
      _ = B * periodNorm T := by
          rw [← mul_pow, Real.sqrt_sq (mul_nonneg hB hPN)]
  unfold rowNorm
  simp only [hlin]
  exact (weighted_sub_le τ hτ0 (fun a => periodPairing F (e a)) (fun a => periodPairing T (e a))).trans
    (add_le_add le_rfl hcoeffSq)

theorem continuous_fderiv_slice {W : ℝ → Space → Space}
    (h : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have h2 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => W z.1 y) :=
    h.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem profile_slice_smooth {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (q : Fin k → ℝ) : ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2) :=
  hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)

def gapField {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : Space :=
  G σ y (d.profile q σ y - d.model q σ y)
    + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y) (v σ y)

theorem isPeriodicField_gap {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hpert : IsPerturbation d.symmetries (d.period q) v G H g) :
    IsPeriodicField (gapField d q v G) := by
  have hp := profile_slice_smooth hd q
  have hm := hd.model_smooth q hq
  have hδ : Continuous (fun z : ℝ × Space => d.profile q z.1 z.2 - d.model q z.1 z.2) :=
    hp.continuous.sub hm.continuous
  have hDδ : Continuous (fun z : ℝ × Space =>
      fderiv ℝ (d.profile q z.1) z.2 - fderiv ℝ (d.model q z.1) z.2) :=
    (continuous_fderiv_slice hp).sub (continuous_fderiv_slice hm)
  refine ⟨?_, ?_, ?_⟩
  · exact ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hpert.measurable_gradient hδ.aestronglyMeasurable).add
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      hDδ.aestronglyMeasurable hpert.measurable_velocity)
  · intro σ y
    have e1 : d.profile q (σ + 1) = d.profile q σ := funext fun y => hd.profile_periodic q σ y
    have e2 : d.model q (σ + 1) = d.model q σ := funext fun y => hd.model_periodic q hq σ y
    simp only [gapField, e1, e2, hpert.periodic_gradient σ y, hpert.periodic_velocity σ y]
  · exact lt_of_le_of_lt (hd.gap_transfer q hq v G H g hpert) ENNReal.ofReal_lt_top

theorem periodNorm_gap_le {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hpert : IsPerturbation d.symmetries (d.period q) v G H g) :
    periodNorm (gapField d q v G) ≤ d.gapSize * Real.sqrt (weightedEnergy d.weightFn G H) := by
  have hE : 0 ≤ weightedEnergy d.weightFn G H := ENNReal.toReal_nonneg
  have h := hd.gap_transfer q hq v G H g hpert
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hE)] at h2
  calc periodNorm (gapField d q v G)
      ≤ Real.sqrt (d.gapSize ^ 2 * weightedEnergy d.weightFn G H) := Real.sqrt_le_sqrt h2
    _ = d.gapSize * Real.sqrt (weightedEnergy d.weightFn G H) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd.gapSize_nonneg]

theorem integrable_transport {W : ℝ → Space → Space}
    (hW : Continuous fun z : ℝ × Space => W z.1 z.2)
    (hDW : Continuous fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hpert : IsPerturbation Γ P v G H g) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (G z.1 z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := by
  have hφc := Cert.Internal.CoerciveBordered.continuous_test hφ
  have hGm := hpert.measurable_gradient
  have hvm := hpert.measurable_velocity
  simp_rw [inner_add_left]
  refine Integrable.add ?_ ?_
  · have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (W z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hGm hW.aestronglyMeasurable
    refine Cert.Internal.CoerciveBordered.integrable_of_le
      (c := fun z => ‖W z.1 z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (locallyIntegrable_finsetSum Finset.univ fun j _ =>
        Cert.Internal.CoerciveBordered.column_locallyIntegrable hGm hpert.periodic_gradient
          hpert.gradient_finite j)
      (hW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left) fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := Cert.Internal.CoerciveBordered.norm_apply_le_sum (G z.1 z.2) (W z.1 z.2)
    calc ‖G z.1 z.2 (W z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖W z.1 z.2‖ * ∑ j : Fin 3, ‖G z.1 z.2 (unitVector j)‖) * ‖φ z.1 z.2‖ := by
          gcongr
      _ = _ := by ring
  · have hmeas : AEStronglyMeasurable
        (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
        hDW.aestronglyMeasurable hvm
    refine Cert.Internal.CoerciveBordered.integrable_of_le
      (c := fun z => ‖fderiv ℝ (W z.1) z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (LocallyIntegrable.mono (Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable hpert)
        hvm.norm (Eventually.of_forall fun z => by simp))
      (hDW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left) fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖fderiv ℝ (W z.1) z.2 (v z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖fderiv ℝ (W z.1) z.2‖ * ‖v z.1 z.2‖) * ‖φ z.1 z.2‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring

theorem integrable_actuator_pairing {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (κ : Fin k → ℝ) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2))
      volume := by
  simp_rw [sum_inner, inner_smul_left]
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.const_mul ?_ _
  have hfin : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤ := by
    have hle : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
        ∑ j, periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2) :=
      Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
        (fun j _ => bot_le) (Finset.mem_univ i)
    exact lt_of_le_of_lt (hle.trans hd.actuator_norm) ENNReal.ofReal_lt_top
  exact Cert.Internal.CoerciveBordered.integrable_inner_of_periodic (hd.actuator_measurable i)
    (hd.actuator_periodic i) hfin (Cert.Internal.CoerciveBordered.continuous_test hφ) hφ.2.1

theorem isRightSide_model {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hpert : IsPerturbation d.symmetries (d.period q) v G H g)
    (κ : Fin k → ℝ) {F : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hR : IsRightSide (d.profile q) d.actuator κ v G g F) :
    IsRightSide (d.model q) d.actuator κ v G g (fun σ y => F σ y - gapField d q v G σ y) := by
  intro φ hφ
  have hT := isPeriodicField_gap hd hq hpert
  have hφc := Cert.Internal.CoerciveBordered.continuous_test hφ
  have iF := Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hF.1 hF.2.1 hF.2.2 hφc hφ.2.1
  have iT := Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hT.1 hT.2.1 hT.2.2 hφc hφ.2.1
  have hA : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    (Cert.Internal.CoerciveBordered.integrable_inner_of_periodic hpert.measurable_derivative
      hpert.periodic_derivative hpert.derivative_finite hφc hφ.2.1).add
      (Cert.Internal.CoerciveBordered.integrable_matNorm hpert.measurable_gradient
        hpert.periodic_gradient hpert.gradient_finite hφ)
  have hp := profile_slice_smooth hd q
  have hB := integrable_transport hp.continuous (continuous_fderiv_slice hp) hpert hφ
  have hC := integrable_actuator_pairing hd κ hφ
  have iP : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile q z.1 z.2)
      + fderiv ℝ (d.profile q z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume := by
    refine ((hA.add hB).add hC).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, inner_add_left]
    ring
  have epw : ∀ z : ℝ × Space, inner ℝ (g z.1 z.2 + G z.1 z.2 (d.model q z.1 z.2)
      + fderiv ℝ (d.model q z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) =
      (inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile q z.1 z.2)
      + fderiv ℝ (d.profile q z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2))
      - inner ℝ (gapField d q v G z.1 z.2) (φ z.1 z.2) := by
    intro z
    simp only [gapField, map_sub, sub_apply, inner_add_left, inner_sub_left]
    ring
  have e1 := hR φ hφ
  calc ∫ z : ℝ × Space, inner ℝ (F z.1 z.2 - gapField d q v G z.1 z.2) (φ z.1 z.2)
      = (∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2))
        - ∫ z : ℝ × Space, inner ℝ (gapField d q v G z.1 z.2) (φ z.1 z.2) := by
        rw [← integral_sub iF iT]
        exact integral_congr_ae (ae_of_all _ fun z => inner_sub_left _ _ _)
    _ = (∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile q z.1 z.2)
          + fderiv ℝ (d.profile q z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
          + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)))
        - ∫ z : ℝ × Space, inner ℝ (gapField d q v G z.1 z.2) (φ z.1 z.2) := by
        rw [e1]
    _ = ∫ z : ℝ × Space, ((inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile q z.1 z.2)
          + fderiv ℝ (d.profile q z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
          + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2))
          - inner ℝ (gapField d q v G z.1 z.2) (φ z.1 z.2)) := (integral_sub iP iT).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun z => (epw z).symm)

theorem coercive_at_profile {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d) :
    ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
      ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile q) d.actuator κ v G g F →
        Real.sqrt (weightedEnergy d.weightFn G H + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) ≤
          d.coerciveL2 / (1 - d.transferLoss) * periodNorm F
            + rowNorm d.rowField (fun a => d.rowWeight a / (1 - d.transferLoss) ^ 2) F
            + d.coercivePin / (1 - d.transferLoss) * vecNorm (fun i => pinValue (d.pin i) G) := by
  intro q hq v G H g hpert κ F hFm hFp hF2 hR
  have hη1 : 0 < 1 - d.transferLoss := by linarith [hd.transfer_lt]
  have hF : IsPeriodicField F := ⟨hFm, hFp, hF2⟩
  have hT := isPeriodicField_gap hd hq hpert
  have hmF := Coercive.Internal.Field.memLp_of_period hFm hF2
  have hmT := Coercive.Internal.Field.memLp_of_period hT.1 hT.2.2
  have hD2 : periodLIntegral (fun σ y => ‖F σ y - gapField d q v G σ y‖ ^ 2) < ⊤ :=
    Coercive.Internal.Field.period_lt_top_of_memLp (F := fun σ y => F σ y - gapField d q v G σ y)
      (hmF.sub hmT)
  have hD : IsPeriodicField (fun σ y => F σ y - gapField d q v G σ y) :=
    ⟨hFm.sub hT.1, fun σ y => by simp only [hFp σ y, hT.2.1 σ y], hD2⟩
  have hRm := isRightSide_model hd hq hpert κ hF hR
  have hc := hd.coercive q hq v G H g hpert κ _ hD.1 hD.2.1 hD.2.2 hRm
  have hN1 : periodNorm (fun σ y => F σ y - gapField d q v G σ y) ≤
      periodNorm F + periodNorm (gapField d q v G) := by
    have h := Cert.Internal.HeldContracts.periodNorm_neg_add_le hF
      (F₂ := fun σ y => -gapField d q v G σ y)
      ⟨hT.1.neg, fun σ y => by simp only [hT.2.1 σ y], by simpa only [norm_neg] using hT.2.2⟩
    have e1 : (fun σ y => -(F σ y + -gapField d q v G σ y)) =
        fun σ y => -(F σ y - gapField d q v G σ y) := by
      funext σ y; rw [sub_eq_add_neg]
    have e2 : periodNorm (fun σ y => -(F σ y - gapField d q v G σ y)) =
        periodNorm (fun σ y => F σ y - gapField d q v G σ y) := by
      unfold periodNorm; simp only [norm_neg]
    have e3 : periodNorm (fun σ y => -gapField d q v G σ y) = periodNorm (gapField d q v G) := by
      unfold periodNorm; simp only [norm_neg]
    rw [e1, e2, e3] at h
    exact h
  have hN2 : d.rows (fun σ y => F σ y - gapField d q v G σ y) ≤
      d.rows F + d.rowBound * periodNorm (gapField d q v G) :=
    rows_sub_le d.rowField d.rowWeight d.rowBound
      (fun a => ⟨hd.rowField_measurable a, hd.rowField_periodic a, hd.rowField_finite a⟩)
      hd.rowField_orthonormal hd.rowWeight_nonneg hd.rowWeight_le hd.rowBound_nonneg hF hT hD2
  have hN3 := periodNorm_gap_le hd hq hpert
  set E := weightedEnergy d.weightFn G H with hEdef
  set Z := Real.sqrt (E + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) with hZdef
  have hZ : Real.sqrt E ≤ Z := Real.sqrt_le_sqrt (le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)))
  have hK0 := hd.coerciveL2_nonneg
  have hrB := hd.rowBound_nonneg
  have h1 := mul_le_mul_of_nonneg_left hN1 hK0
  have h2 : (d.coerciveL2 + d.rowBound) * periodNorm (gapField d q v G) ≤
      (d.coerciveL2 + d.rowBound) * (d.gapSize * Z) :=
    mul_le_mul_of_nonneg_left (hN3.trans (mul_le_mul_of_nonneg_left hZ hd.gapSize_nonneg))
      (add_nonneg hK0 hrB)
  have hη : d.transferLoss = (d.coerciveL2 + d.rowBound) * d.gapSize := rfl
  have key : (1 - d.transferLoss) * Z ≤ d.coerciveL2 * periodNorm F + d.rows F
      + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G) := by
    rw [hη]
    nlinarith [hc, h1, h2]
  rw [rowNorm_div d.rowField d.rowWeight F hη1]
  have e : d.coerciveL2 / (1 - d.transferLoss) * periodNorm F
      + rowNorm d.rowField d.rowWeight F / (1 - d.transferLoss)
      + d.coercivePin / (1 - d.transferLoss) * vecNorm (fun i => pinValue (d.pin i) G) =
      (d.coerciveL2 * periodNorm F + d.rows F
        + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)) / (1 - d.transferLoss) := by
    unfold ExtendedCertificateData.rows
    ring
  rw [e, le_div_iff₀ hη1]
  linarith

theorem stationaryEnergy_nonneg {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : 0 ≤ stationaryEnergy d.weightFn G H := by
  unfold stationaryEnergy
  refine add_nonneg (integral_nonneg fun y => sq_nonneg _) (integral_nonneg fun y => ?_)
  exact mul_nonneg (hd.weight_pos.le.trans (hd.weightFn_lower y))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem transferLoss_atProfile {k : ℕ} (d : ExtendedCertificateData k) :
    d.atProfile.transferLoss = 0 := by
  simp [ExtendedCertificateData.transferLoss, ExtendedCertificateData.atProfile]

theorem isExtendedCertificate_atProfile {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) : IsExtendedCertificate d.atProfile := by
  have hη1 : 0 < 1 - d.transferLoss := by linarith [hd.transfer_lt]
  have hloss := transferLoss_atProfile d
  exact
  { hd with
    coerciveL2_nonneg := by
      show 0 ≤ d.coerciveL2 / (1 - d.transferLoss)
      exact div_nonneg hd.coerciveL2_nonneg hη1.le
    coercivePin_nonneg := by
      show 0 ≤ d.coercivePin / (1 - d.transferLoss)
      exact div_nonneg hd.coercivePin_nonneg hη1.le
    rowBound_nonneg := by
      show 0 ≤ d.rowBound / (1 - d.transferLoss)
      exact div_nonneg hd.rowBound_nonneg hη1.le
    gapSize_nonneg := le_refl (0 : ℝ)
    formShift_nonneg := le_refl (0 : ℝ)
    transfer_lt := by
      rw [hloss]
      exact one_pos
    coerciveTotal_ge := by
      rw [hloss]
      show d.coerciveL2 / (1 - d.transferLoss) + d.rowBound / (1 - d.transferLoss) ≤
        (1 - 0) * d.coerciveTotal
      rw [← add_div, div_le_iff₀ hη1]
      linarith [hd.coerciveTotal_ge]
    modelFormBound_nonneg := by
      show 0 ≤ d.formBound
      linarith [hd.modelFormBound_nonneg, hd.formShift_nonneg, hd.formBound_ge]
    formBound_ge := by
      show d.formBound + 0 ≤ d.formBound
      rw [add_zero]
    model_smooth := fun q _ => profile_slice_smooth hd q
    model_periodic := fun q _ => hd.profile_periodic q
    gap_transfer := by
      intro q _ v G H g _
      show periodLIntegral (fun σ y => ‖G σ y (d.profile q σ y - d.profile q σ y)
        + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile q σ) y) (v σ y)‖ ^ 2) ≤
        ENNReal.ofReal ((0 : ℝ) ^ 2 * weightedEnergy d.weightFn G H)
      simp [periodLIntegral]
    form_shift := by
      intro q _ σ w G H _
      show -(0 : ℝ) * stationaryEnergy d.weightFn G H ≤
        frozenForm (d.profile q σ) w G H - frozenForm (d.profile q σ) w G H
      simp
    rowWeight_nonneg := fun a => by
      show 0 ≤ d.rowWeight a / (1 - d.transferLoss) ^ 2
      exact div_nonneg (hd.rowWeight_nonneg a) (sq_nonneg _)
    rowWeight_le := fun a => by
      show d.rowWeight a / (1 - d.transferLoss) ^ 2 ≤ (d.rowBound / (1 - d.transferLoss)) ^ 2
      rw [div_pow]
      exact div_le_div_of_nonneg_right (hd.rowWeight_le a) (sq_nonneg _)
    coercive := coercive_at_profile hd
    frozen_form := by
      intro q hq σ w G H hw
      show -d.formBound * stationaryEnergy d.weightFn G H ≤ frozenForm (d.profile q σ) w G H
      have h1 := hd.form_shift q hq σ w G H hw
      have h2 := hd.frozen_form q hq σ w G H hw
      have hS := stationaryEnergy_nonneg hd G H
      have h3 := mul_le_mul_of_nonneg_right hd.formBound_ge hS
      linarith
    defect_nonneg := fun q hq => ⟨(hd.defect_nonneg q hq).1,
      div_nonneg (hd.defect_nonneg q hq).2 hη1.le⟩
    defect_rows := fun q hq => by
      show rowNorm d.rowField (fun a => d.rowWeight a / (1 - d.transferLoss) ^ 2) (d.defect q) ≤
        d.defectRowBound q / (1 - d.transferLoss)
      rw [rowNorm_div d.rowField d.rowWeight (d.defect q) hη1]
      exact div_le_div_of_nonneg_right (hd.defect_rows q hq) hη1.le
    size := fun q hq => by
      rw [hloss]
      show d.coerciveL2 / (1 - d.transferLoss) * d.defectBound q
        + d.defectRowBound q / (1 - d.transferLoss)
        + d.coercivePin / (1 - d.transferLoss) * vecNorm (d.targetGap q) ≤ (1 - 0) * d.sizeBound
      have e : d.coerciveL2 / (1 - d.transferLoss) * d.defectBound q
          + d.defectRowBound q / (1 - d.transferLoss)
          + d.coercivePin / (1 - d.transferLoss) * vecNorm (d.targetGap q) =
          (d.coerciveL2 * d.defectBound q + d.defectRowBound q
            + d.coercivePin * vecNorm (d.targetGap q)) / (1 - d.transferLoss) := by ring
      rw [e, div_le_iff₀ hη1]
      linarith [hd.size q hq] }

end Internal.AtProfile

theorem extendedAtProfileHolds : ExtendedAtProfileHolds :=
  fun hd => Internal.AtProfile.isExtendedCertificate_atProfile hd

end Breakdown.Cert
