import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.Data
import Breakdown.Cert.ProductPairing
import Breakdown.Cert.JointRepresentative
import Breakdown.Held.Statements

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedAdjointEnclosure

open Internal.CoerciveBordered

theorem continuous_profile_slice {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (q : Fin k → ℝ) :
    Continuous (fun z : ℝ × Space => d.profile q z.1 z.2) :=
  hd.profile_smooth.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_fderiv_profile_slice {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (q : Fin k → ℝ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (d.profile q z.1) z.2) := by
  have h1 : ContDiff ℝ 1 (Function.uncurry fun (z : ℝ × Space) (y : Space) => d.profile q z.1 y) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_fst.fst.prodMk contDiff_snd))
  exact (h1.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem integrable_transport {W : ℝ → Space → Space}
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

theorem isRightSide_zero {k : ℕ} {Γ : Set Symmetry} {P : ℝ} {W : ℝ → Space → Space}
    (b : Fin k → ℝ → Space → Space)
    (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hDW : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2))
    (f c : HH) (F : ℝ → Space → Space) {u : XX} {v : VelField} {G : GradField}
    {H : SecondField} {g : ℝ → Space → Space} (hread : IsReadingOf u v G H)
    (hpert : IsPerturbation Γ P v G H g)
    (hpair : ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (f + c) (testInHH φ))
    (hg : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ))
    (hconv : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (G z.1 z.2 (W z.1 z.2)
        + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) = inner ℝ c (testInHH φ)) :
    IsRightSide W b 0 v G g F := by
  intro φ hφ
  have hA : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    (integrable_inner_of_periodic hpert.measurable_derivative hpert.periodic_derivative
      hpert.derivative_finite (continuous_test hφ) hφ.2.1).add
      (integrable_matNorm hpert.measurable_gradient hpert.periodic_gradient hpert.gradient_finite hφ)
  have hB := integrable_transport hW hDW hread hpert.gradient_finite hφ
  have e1 : ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2)
        + fderiv ℝ (W z.1) z.2 (v z.1 z.2) + ∑ i, (0 : Fin k → ℝ) i • b i z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) =
      ∫ z : ℝ × Space, ((inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) + inner ℝ (G z.1 z.2 (W z.1 z.2)
        + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, inner_add_left]
    ring
  have e2 := integral_add hA hB
  have e3 := hpair φ hφ
  rw [inner_add_left] at e3
  have e4 := hg φ hφ
  have e5 := hconv φ hφ
  show _ = _
  linarith

theorem compLpL_left_inverse {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (A : E →L[ℝ] E') (B : E' →L[ℝ] E)
    (hAB : ∀ x, B (A x) = x) (h : Lp (α := TimeCircle) E 2) :
    ContinuousLinearMap.compLpL 2 volume B (ContinuousLinearMap.compLpL 2 volume A h) = h := by
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL B (ContinuousLinearMap.compLpL 2 volume A h),
    ContinuousLinearMap.coeFn_compLpL A h] with t h1 h2
  rw [h1]
  show B _ = _
  rw [h2]
  exact hAB _

theorem exists_representative (hP : ProjectionHolds) (h : HH) :
    ∃ F : ℝ → Space → Space, IsPeriodicField F ∧ physToHH F = h := by
  obtain ⟨F, hm, hper, hc⟩ := exists_joint_representative (p := 2)
    (ContinuousLinearMap.compLpL 2 volume toPhysH h)
  refine ⟨F, ⟨hm, hper, ?_⟩, ?_⟩
  · rw [Internal.Data.periodLIntegral_eq_of_curve _ hc]
    exact ENNReal.ofReal_lt_top
  · exact (Internal.Data.physToHH_eq hper _ hc).trans
      (compLpL_left_inverse toPhysH solProj hP.2.2.2 h)

theorem actuator_periodicField {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (i : Fin k) : IsPeriodicField (d.actuator i) := by
  refine ⟨hd.actuator_measurable i, hd.actuator_periodic i, ?_⟩
  have hle : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
      ∑ j, periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2) :=
    Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
      (fun j _ => bot_le) (Finset.mem_univ i)
  exact lt_of_le_of_lt (hle.trans hd.actuator_norm) ENNReal.ofReal_lt_top

theorem energyW_nonneg_of {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) : 0 ≤ energyW w u := by
  unfold energyW
  refine add_nonneg (sq_nonneg _) (integral_nonneg fun t => ?_)
  unfold sliceWeightedGrad
  exact integral_nonneg fun y => mul_nonneg (hw y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem delta_core (h4 : ReadingEnergyHolds) (h5 : ExtendedConvectionHolds)
    (h6 : ExtendedDataHolds) (h8 : TestPairingHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) {j : Fin k}
    (hj : j ∈ d.adjointSet)
    (hAdj : ∀ F, IsPeriodicField F →
      periodPairing F (d.adjoint j q) = inner ℝ (physToHH F) (physToHH (d.adjoint j q)))
    (f : HH) {v : VelField} {G : GradField} {H : SecondField} {g : ℝ → Space → Space}
    (hread : IsReadingOf (freeInv (d.period q) f) v G H)
    (hpert : IsPerturbation d.symmetries (d.period q) v G H g)
    (hg : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ))
    (F : ℝ → Space → Space) (hF : IsPeriodicField F)
    (hFeq : physToHH F = f + convection d.toCertificateData q (freeInv (d.period q) f)) :
    |inner ℝ (f + convection d.toCertificateData q (freeInv (d.period q) f))
        (physToHH (d.adjoint j q))
      - ∑ l, d.coupling q j l * pinMap d.toCertificateData (freeInv (d.period q) f) l| ≤
      d.adjointDefect j * Real.sqrt (energyW d.weightFn (freeInv (d.period q) f)) := by
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hpair : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
        inner ℝ (f + convection d.toCertificateData q (freeInv (d.period q) f)) (testInHH φ) := by
    intro φ hφ
    exact (h8 F hF φ hφ).symm.trans (congrArg (fun x => inner ℝ x (testInHH φ)) hFeq)
  have hconv := (h5 d hd q hq).2.2
  have hRS : IsRightSide (d.profile q) d.actuator 0 v G g F :=
    isRightSide_zero d.actuator (continuous_profile_slice hd q)
      (continuous_fderiv_profile_slice hd q) f _ F hread hpert hpair hg
      (fun φ hφ => hconv _ v G H hread φ hφ)
  have hb := hd.adjoint_defect j hj q hq v G H g hpert F hF.1 hF.2.1 hF.2.2 hRS
  have hE := (h4 d.weightFn d.weight hadm _ v G H hread).1
  have hpin := (h6 d hd q hq).2.2.2.2.2.2
  have hpv : ∀ l, pinValue (d.pin l) G = pinMap d.toCertificateData (freeInv (d.period q) f) l :=
    fun l => (hpin _ v G H hread l).symm
  simp only [hAdj F hF, hFeq, hE, hpv] at hb
  exact hb

theorem delta_bound (h2 : FreePerturbationHolds) (h3 : ReadingExistsHolds)
    (h4 : ReadingEnergyHolds) (h5 : ExtendedConvectionHolds) (h6 : ExtendedDataHolds)
    (h8 : TestPairingHolds) (h9 : ProjectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) {j : Fin k}
    (hj : j ∈ d.adjointSet)
    (hAdj : ∀ F, IsPeriodicField F →
      periodPairing F (d.adjoint j q) = inner ℝ (physToHH F) (physToHH (d.adjoint j q)))
    (f : HH) (hf : f ∈ invariantHH d.symmetries) :
    |inner ℝ (f + convection d.toCertificateData q (freeInv (d.period q) f))
        (physToHH (d.adjoint j q))
      - ∑ l, d.coupling q j l * pinMap d.toCertificateData (freeInv (d.period q) f) l| ≤
      d.adjointDefect j * Real.sqrt (energyW d.weightFn (freeInv (d.period q) f)) := by
  have hP : 0 < d.period q := hd.period_pos q hq
  have h3' := h3 (freeInv (d.period q) f)
  obtain ⟨v, hv⟩ := h3'
  obtain ⟨G, hG⟩ := hv
  obtain ⟨H, hH⟩ := hG
  have hread := hH.1
  have h2' := h2 d.symmetries (d.period q) hP f hf v G H hread
  obtain ⟨g, hg0⟩ := h2'
  have hrep := exists_representative h9
    (f + convection d.toCertificateData q (freeInv (d.period q) f))
  exact delta_core h4 h5 h6 h8 hd hq hj hAdj f hread hg0.1 hg0.2 hrep.choose
    hrep.choose_spec.1 hrep.choose_spec.2

theorem quad_bound (h2 : FreePerturbationHolds) (h3 : ReadingExistsHolds)
    (h4 : ReadingEnergyHolds) (h7 : ProductBoundHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) {j : Fin k}
    (hj : j ∈ d.adjointSet)
    (hAdj : ∀ F, IsPeriodicField F →
      periodPairing F (d.adjoint j q) = inner ℝ (physToHH F) (physToHH (d.adjoint j q)))
    (f : HH) (hf : f ∈ invariantHH d.symmetries)
    (hsup : supGrad (freeInv (d.period q) f) < ⊤) :
    |inner ℝ (productH (freeInv (d.period q) f) (freeInv (d.period q) f))
      (physToHH (d.adjoint j q))| ≤
        d.adjointQuad j * energyW d.weightFn (freeInv (d.period q) f) := by
  have hP : 0 < d.period q := hd.period_pos q hq
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hPF := (h7 d.weightFn d.weight hadm (freeInv (d.period q) f) (freeInv (d.period q) f) hsup).1
  have hrd := Internal.ProductPairing.isReadingOf_readingOf h3 (freeInv (d.period q) f)
  have h2' := h2 d.symmetries (d.period q) hP f hf _ _ _ hrd
  obtain ⟨g, hg0⟩ := h2'
  have hqd : |periodPairing (productField (freeInv (d.period q) f) (freeInv (d.period q) f))
      (d.adjoint j q)| ≤ d.adjointQuad j * weightedEnergy d.weightFn
        (readingOf (freeInv (d.period q) f)).2.1 (readingOf (freeInv (d.period q) f)).2.2 :=
    hd.adjoint_quadratic j hj q hq _ _ _ g hg0.1
  have e3 := (h4 d.weightFn d.weight hadm _ _ _ _ hrd).1
  simp only [e3] at hqd
  have e1 := Internal.ProductPairing.productH_eq_physToHH h3 hPF.2.1
  have e2 := hAdj _ hPF
  have e4 : inner ℝ (productH (freeInv (d.period q) f) (freeInv (d.period q) f))
      (physToHH (d.adjoint j q)) =
      periodPairing (productField (freeInv (d.period q) f) (freeInv (d.period q) f))
        (d.adjoint j q) :=
    (congrArg (fun x => inner ℝ x (physToHH (d.adjoint j q))) e1).trans e2.symm
  exact (congrArg abs e4).le.trans hqd

theorem final_compare {A δ aq ρ S : ℝ} {k : ℕ} (e : Fin k → ℝ)
    (hS : S = ∑ l, e l ^ 2)
    (h : A ≤ aq * ρ ^ 2 + ρ * Real.sqrt (δ ^ 2 + S / 1 ^ 2)) :
    A ≤ aq * ρ ^ 2 + ρ * Real.sqrt (δ ^ 2 + (vecNorm e / 1) ^ 2) := by
  have hv : (vecNorm e / 1) ^ 2 = S / 1 ^ 2 := by
    rw [hS, div_one, one_pow, div_one]
    exact Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg (e l))
  rw [hv]
  exact h

def transportPart {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) :
    ↥(invariantHH d.symmetries) →ₗ[ℝ] HH :=
  ((ContinuousLinearMap.id ℝ HH + (convection d.toCertificateData q).comp (freeInv (d.period q))
    : HH →L[ℝ] HH) : HH →ₗ[ℝ] HH).comp (invariantHH d.symmetries).subtype

def pinPart {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) :
    ↥(invariantHH d.symmetries) →ₗ[ℝ] (Fin k → ℝ) :=
  (((pinMap d.toCertificateData).comp (freeInv (d.period q)) : HH →L[ℝ] (Fin k → ℝ))
    : HH →ₗ[ℝ] (Fin k → ℝ)).comp (invariantHH d.symmetries).subtype

theorem transportPart_apply {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ)
    (v : ↥(invariantHH d.symmetries)) :
    transportPart d q v = (v : HH) + convection d.toCertificateData q (freeInv (d.period q) v) :=
  rfl

theorem pinPart_apply {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ)
    (v : ↥(invariantHH d.symmetries)) :
    pinPart d q v = pinMap d.toCertificateData (freeInv (d.period q) v) :=
  rfl

end Internal.ExtendedAdjointEnclosure

open Internal.ExtendedAdjointEnclosure

theorem extendedAdjointEnclosureHolds_of (h1 : ExtendedAdjointPairingHolds)
    (h2 : FreePerturbationHolds) (h3 : ReadingExistsHolds) (h4 : ReadingEnergyHolds)
    (h5 : ExtendedConvectionHolds) (h6 : ExtendedDataHolds) (h7 : ProductBoundHolds)
    (h8 : TestPairingHolds) (h9 : ProjectionHolds) (h10 : Held.AdjointEnclosureStatement) :
    ExtendedAdjointEnclosureHolds := by
  intro k d hN q hq f κ hheld j hj
  have hd := hN.certificate
  have hw0 : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hAdj := (h1 d hd j hj q hq).2
  have hData := (h6 d hd q hq).1
  have hδ : ∀ v : ↥(invariantHH d.symmetries),
      |inner ℝ (transportPart d q v) (physToHH (d.adjoint j q))
        - ∑ l, d.coupling q j l * pinPart d q v l| ≤
        d.adjointDefect j * Real.sqrt (energyW d.weightFn (freeInv (d.period q) v)) := fun v =>
    delta_bound h2 h3 h4 h5 h6 h8 h9 hd hq hj hAdj v v.2
  have hQ := quad_bound h2 h3 h4 h7 hd hq hj hAdj f hheld.invariant
    (lt_of_le_of_lt hheld.sup ENNReal.ofReal_lt_top)
  have heq : transportPart d q ⟨f, hheld.invariant⟩ + ∑ l, κ l • physToHH (d.actuator l)
      + productH (freeInv (d.period q) f) (freeInv (d.period q) f) = -(d.defectH q) := by
    have e := hheld.equation
    simp only [Internal.Data.actuatorH_apply] at e
    exact eq_neg_of_add_eq_zero_left e
  have hr : Real.sqrt (energyW d.weightFn (freeInv (d.period q) f) + 1 ^ 2 * ∑ l, κ l ^ 2) ≤
      2 * d.sizeBound := by
    have e := hheld.size
    have h11 : energyW d.weightFn (freeInv (d.period q) f) + (1 : ℝ) ^ 2 * ∑ l, κ l ^ 2 =
        energyW d.weightFn (freeInv (d.period q) f) + ∑ l, κ l ^ 2 := by ring
    exact (congrArg Real.sqrt h11).le.trans e
  have key := h10 (fun v : ↥(invariantHH d.symmetries) =>
      energyW d.weightFn (freeInv (d.period q) v)) (transportPart d q)
    (fun v : ↥(invariantHH d.symmetries) =>
      productH (freeInv (d.period q) v) (freeInv (d.period q) v))
    (fun l => physToHH (d.actuator l)) (pinPart d q) (physToHH (d.adjoint j q))
    (fun l => d.coupling q j l) (fun l => d.frame l j) (d.adjointDefect j) (d.adjointQuad j) 1
    (2 * d.sizeBound) (fun v => energyW_nonneg_of hw0 _) one_pos (hd.adjointDefect_nonneg j hj)
    (hd.adjointQuad_nonneg j hj) hδ ⟨f, hheld.invariant⟩ κ (d.defectH q) hQ heq hr
  have hDef : periodPairing (d.defect q) (d.adjoint j q) =
      inner ℝ (d.defectH q) (physToHH (d.adjoint j q)) := hAdj _ hData
  have hpinu : pinPart d q ⟨f, hheld.invariant⟩ = d.targetGap q := hheld.pins
  have hbl : ∀ l, inner ℝ (physToHH (d.actuator l)) (physToHH (d.adjoint j q)) - d.frame l j =
      d.actuatorAdjointError q j l := by
    intro l
    have e := hAdj _ (actuator_periodicField hd l)
    exact (congrArg (fun x => x - d.frame l j) e).symm
  have hL : ∑ l, d.frame l j * κ l + periodPairing (d.defect q) (d.adjoint j q)
      + ∑ l, d.coupling q j l * d.targetGap q l =
      ∑ l, d.frame l j * κ l + inner ℝ (d.defectH q) (physToHH (d.adjoint j q))
      + ∑ l, d.coupling q j l * pinPart d q ⟨f, hheld.invariant⟩ l := by
    simp only [hDef, hpinu]
  have fin := final_compare (d.actuatorAdjointError q j)
    (Finset.sum_congr rfl fun l _ => congrArg (fun x => x ^ 2) (hbl l)) key
  simp only [hL, hN.unit_weight]
  exact fin

end Breakdown.Cert
