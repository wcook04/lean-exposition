import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.ExtendedNodes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedCoerciveBordered

open Internal.CoerciveBordered

theorem continuous_profile {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (p : Fin k → ℝ) : Continuous (fun z : ℝ × Space => d.profile p z.1 z.2) :=
  hd.profile_smooth.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_fderiv_profile {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (p : Fin k → ℝ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (d.profile p z.1) z.2) := by
  have h1 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => d.profile p z.1 y) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_fst.fst.prodMk contDiff_snd))
  exact (h1.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem integrable_convection (W : ℝ → Space → Space)
    (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hDW : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2))
    {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hread : IsReadingOf u v G H) (hGf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (G z.1 z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := by
  have hφc := continuous_test hφ
  have hGm := hread.measurable_gradient
  have hvm := hread.measurable_velocity
  simp_rw [inner_add_left]
  refine Integrable.add ?_ ?_
  · have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (W z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hGm hW.aestronglyMeasurable
    refine integrable_of_le (c := fun z => ‖W z.1 z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (locallyIntegrable_finsetSum Finset.univ fun j _ =>
        column_locallyIntegrable hGm hread.periodic_gradient hGf j)
      (hW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left) fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := norm_apply_le_sum (G z.1 z.2) (W z.1 z.2)
    calc ‖G z.1 z.2 (W z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖W z.1 z.2‖ * ∑ j : Fin 3, ‖G z.1 z.2 (unitVector j)‖) * ‖φ z.1 z.2‖ := by
          gcongr
      _ = _ := by ring
  · have hmeas : AEStronglyMeasurable
        (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hDW.aestronglyMeasurable hvm
    refine integrable_of_le (c := fun z => ‖fderiv ℝ (W z.1) z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (locallyIntegrable_norm_velocity hread) (hDW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left)
      fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖fderiv ℝ (W z.1) z.2 (v z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖fderiv ℝ (W z.1) z.2‖ * ‖v z.1 z.2‖) * ‖φ z.1 z.2‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring

theorem integrable_actuator {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (κ : Fin k → ℝ) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) volume := by
  simp_rw [sum_inner, inner_smul_left]
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.const_mul ?_ _
  have hfin : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤ := by
    have h := hd.actuator_norm
    have hle : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
        ∑ j, periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2) :=
      Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
        (fun j _ => bot_le) (Finset.mem_univ i)
    exact lt_of_le_of_lt (hle.trans h) ENNReal.ofReal_lt_top
  exact integrable_inner_of_periodic (hd.actuator_measurable i) (hd.actuator_periodic i) hfin
    (continuous_test hφ) hφ.2.1

theorem isRightSide_of {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (p : Fin k → ℝ) (f : HH) (κ : Fin k → ℝ) (F : ℝ → Space → Space) {u : XX} {v : VelField}
    {G : GradField} {H : SecondField} {g : ℝ → Space → Space} (hread : IsReadingOf u v G H)
    (hpert : IsPerturbation d.symmetries (d.period p) v G H g)
    (hpair : ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (f + convection d.toCertificateData p u + actuatorH d.toCertificateData κ)
        (testInHH φ))
    (hg : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ))
    (hconv : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) =
        inner ℝ (convection d.toCertificateData p u) (testInHH φ))
    (hact : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (actuatorH d.toCertificateData κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) :
    IsRightSide (d.profile p) d.actuator κ v G g F := by
  intro φ hφ
  have hA : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    (integrable_inner_of_periodic hpert.measurable_derivative hpert.periodic_derivative
      hpert.derivative_finite (continuous_test hφ) hφ.2.1).add
      (integrable_matNorm hpert.measurable_gradient hpert.periodic_gradient hpert.gradient_finite hφ)
  have hB := integrable_convection (d.profile p) (continuous_profile hd p)
    (continuous_fderiv_profile hd p) hread hpert.gradient_finite hφ
  have hC := integrable_actuator hd κ hφ
  have hAB : Integrable (fun z : ℝ × Space => (inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) + inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
      + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := hA.add hB
  have e3 : ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) =
      ∫ z : ℝ × Space, ((inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) + inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)
        + inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    integral_congr_ae (Eventually.of_forall fun z => (integrand_eq _ _ _ _ _ _).symm)
  have e4 := integral_add hAB hC
  have e5 := integral_add hA hB
  have e1 := hpair φ hφ
  simp only [inner_add_left] at e1
  have e6 := hg φ hφ
  have e7 := hconv φ hφ
  have e8 := hact φ hφ
  show _ = _
  linarith

theorem unit_weight_bound (E S a r c x μ : ℝ) (hμ : μ = 1)
    (h : Real.sqrt (E + μ ^ 2 * S) ≤ a + r + c * x) : Real.sqrt (E + S) ≤ (a + r) + c * x := by
  subst hμ
  simpa using h

end Internal.ExtendedCoerciveBordered

open Internal.CoerciveBordered Internal.ExtendedCoerciveBordered

theorem extendedCoerciveBorderedHolds_of (h1 : ReadingExistsHolds) (h2 : ReadingEnergyHolds)
    (h3 : FreePerturbationHolds) (h4 : ExtendedConvectionHolds) (h5 : ExtendedDataHolds)
    (_h6 : TestPairingHolds) : ExtendedCoerciveBorderedHolds := by
  intro k d hN p hp f hf κ F hF hpair
  have hd := hN.certificate
  have h1' := h1 (freeInv (d.period p) f)
  obtain ⟨v, hv⟩ := h1'
  obtain ⟨G, hG⟩ := hv
  obtain ⟨H, hH⟩ := hG
  have hread := hH.1
  have h3' := h3 d.symmetries (d.period p) (hd.period_pos p hp) f hf v G H hread
  obtain ⟨g, hg0⟩ := h3'
  have hpert := hg0.1
  have hg := hg0.2
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hE := (h2 d.weightFn d.weight hadm _ v G H hread).1
  have hconv := (h4 d hd p hp).2.2
  have hact := (h5 d hd p hp).2.2.2.1
  have hpin := (h5 d hd p hp).2.2.2.2.2.2
  have hpair' : ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (f + convection d.toCertificateData p (freeInv (d.period p) f)
        + actuatorH d.toCertificateData κ) (testInHH φ) := by
    intro φ hφ
    exact (hpair φ hφ).trans
      (congrArg (fun x : HH => inner ℝ x (testInHH φ)) (bordered_fst d.toCertificateData p f κ))
  have hRS := isRightSide_of hd p f κ F hread hpert hpair' hg
    (fun φ hφ => hconv _ v G H hread φ hφ) (fun φ hφ => hact κ φ hφ)
  have hRS' : IsRightSide (d.model p) d.actuator κ v G g F := hN.model_eq ▸ hRS
  have hc := hd.coercive p hp v G H g hpert κ F hF.1 hF.2.1 hF.2.2 hRS'
  have hc' := unit_weight_bound _ _ _ _ _ _ _ hN.unit_weight hc
  have hpv : (fun i => pinValue (d.pin i) G) = pinMap d.toCertificateData (freeInv (d.period p) f) :=
    funext fun i => (hpin _ v G H hread i).symm
  exact size_bound_of _ _ κ _ _ _ _ _ hE hpv hc'

end Breakdown.Cert
