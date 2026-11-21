import Breakdown.Cert.Convection
import Breakdown.Cert.ExtendedNodes

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ConvectionFirstOrder

open Internal.Convection

structure IsFirstOrderCoefficient (W : ℝ → Space → Space) (D : ℝ) : Prop where
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)
  periodic : IsTimePeriodic W
  bound_zero : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖)
  bound_one : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2

theorem isFirstOrderCoefficient_profile {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    IsFirstOrderCoefficient (d.profile q) d.decay :=
  ⟨hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id), hd.profile_periodic q,
    fun σ y => (hd.profile_decay q hq σ y).1, fun σ y => (hd.profile_decay q hq σ y).2.1⟩

theorem aesm_readingConvection {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsFirstOrderCoefficient W D) {v : VelField} {G : GradField}
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => readingConvection W v G z.1 z.2) volume := by
  have hc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hd : Measurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := W) hc
  exact (apply_aesm hG hc.aestronglyMeasurable).add (apply_aesm hd.aestronglyMeasurable hv)

theorem coefficient_nonneg {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D) :
    0 ≤ D := by
  have h := hW.bound_zero 0 0
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem slice_contDiff {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    (σ : ℝ) : ContDiff ℝ 1 (W σ) :=
  hW.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem first_term {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D) (σ : ℝ)
    (h : X) (j : Fin 3) :
    MemLp (fun y => (W σ y) j • (partialX j h : Space → Space) y) 2 volume ∧
      eLpNorm (fun y => (W σ y) j • (partialX j h : Space → Space) y) 2 volume ≤
        ENNReal.ofReal (D * ‖h‖) := by
  have hD := coefficient_nonneg hW
  have hc : Continuous (W σ) := (slice_contDiff hW σ).continuous
  have hm : AEStronglyMeasurable (fun y => (W σ y) j • (partialX j h : Space → Space) y) volume :=
    ((EuclideanSpace.proj j).continuous.comp hc).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  have hb : ∀ᵐ y ∂volume, ‖(W σ y) j • (partialX j h : Space → Space) y‖ ≤
      D * ‖(partialX j h : Space → Space) y‖ := by
    refine ae_of_all _ fun y => ?_
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖(W σ y) j‖ ≤ ‖W σ y‖ := PiLp.norm_apply_le _ _
      _ ≤ D / (1 + ‖y‖) := hW.bound_zero σ y
      _ ≤ D := div_le_self hD (by linarith [norm_nonneg y])
  refine ⟨(Lp.memLp _).of_le_mul hm hb, ?_⟩
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb 2).trans ?_
  rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_partialX_le j h) hD)

theorem second_term {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D) (σ : ℝ)
    (h : X) :
    MemLp (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ∧
      eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
        ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
  have hD := coefficient_nonneg hW
  have hcf : Continuous (fderiv ℝ (W σ)) := (slice_contDiff hW σ).continuous_fderiv (by norm_num)
  have hf : AEStronglyMeasurable (fderiv ℝ (W σ)) volume := hcf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (velocity h : Space → Space) volume := Lp.aestronglyMeasurable _
  have hm : AEStronglyMeasurable (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y))
      volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hf.prodMk hg)
  have hH : eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderiv ℝ (W σ)) 3 volume *
        eLpNorm (velocity h : Space → Space) 6 volume := by
    have := exponentTriple_three_six
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun L x => L x) 1
      (ae_of_all _ fun y => by rw [one_mul]; exact ContinuousLinearMap.le_opNNNorm _ _)
  have hw : eLpNorm (fderiv ℝ (W σ)) 3 volume ≤
      ENNReal.ofReal D * eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun y => ?_) 3
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _), Real.rpow_neg hpos.le,
      Real.rpow_two, ← div_eq_mul_inv]
    exact hW.bound_one σ y
  have hwc : eLpNorm (fun y : Space => (1 + ‖y‖) ^ (-2 : ℝ)) 3 volume =
      ENNReal.ofReal weightCube :=
    (ENNReal.ofReal_toReal weight_memLp.eLpNorm_lt_top.ne).symm
  have hv : eLpNorm (velocity h : Space → Space) 6 volume ≤
      ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
  have hwc0 : 0 ≤ weightCube := ENNReal.toReal_nonneg
  have hbound : eLpNorm (fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y)) 2 volume ≤
      ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    refine hH.trans ?_
    rw [ENNReal.coe_one, one_mul]
    calc eLpNorm (fderiv ℝ (W σ)) 3 volume * eLpNorm (velocity h : Space → Space) 6 volume
        ≤ (ENNReal.ofReal D * ENNReal.ofReal weightCube) *
            ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← hwc]
          exact mul_le_mul' hw hv
      _ = ENNReal.ofReal (D * weightCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul (mul_nonneg hD hwc0),
            mul_assoc _ ‖_‖]
  exact ⟨⟨hm, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

theorem slice_bound {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D) (σ : ℝ)
    (h : X) :
    MemLp (sliceConvection (W σ) h) 2 volume ∧
      eLpNorm (sliceConvection (W σ) h) 2 volume ≤ ENNReal.ofReal (sliceConst D * ‖h‖) := by
  have hD := coefficient_nonneg hW
  set t : Fin 3 → Space → Space := fun j y => (W σ y) j • (partialX j h : Space → Space) y with ht
  have hsum : (fun y => ∑ j : Fin 3, t j y) = ∑ j : Fin 3, t j := by
    funext y
    simp [Finset.sum_apply]
  have heq : sliceConvection (W σ) h = (∑ j : Fin 3, t j) +
      fun y => fderiv ℝ (W σ) y ((velocity h : Space → Space) y) := by
    rw [← hsum]
    rfl
  have h1 : MemLp (∑ j : Fin 3, t j) 2 volume :=
    memLp_finsetSum' _ fun j _ => (first_term hW σ h j).1
  have h1b : eLpNorm (∑ j : Fin 3, t j) 2 volume ≤ ENNReal.ofReal (3 * (D * ‖h‖)) := by
    refine (eLpNorm_sum_le (fun j _ => (first_term hW σ h j).1.1) (by norm_num)).trans ?_
    calc ∑ j : Fin 3, eLpNorm (t j) 2 volume ≤ ∑ _j : Fin 3, ENNReal.ofReal (D * ‖h‖) :=
          Finset.sum_le_sum fun j _ => (first_term hW σ h j).2
      _ = ENNReal.ofReal (3 * (D * ‖h‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
  have h2 := second_term hW σ h
  rw [heq]
  refine ⟨h1.add h2.1, ?_⟩
  refine (eLpNorm_add_le h1.1 h2.1.1 (by norm_num)).trans ?_
  refine (add_le_add h1b h2.2).trans ?_
  have hwc0 : 0 ≤ weightCube := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold sliceConst
  ring

theorem sliceConst_nonneg {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D) :
    0 ≤ sliceConst D := by
  have hD := coefficient_nonneg hW
  have hw : 0 ≤ weightCube := ENNReal.toReal_nonneg
  unfold sliceConst
  positivity

theorem lintegral_slice_le {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    (σ : ℝ) (h : X) (f : Space → Space) (hf : f =ᵐ[volume] sliceConvection (W σ) h) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ≤
      ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖h‖ ^ 2) := by
  have hb := (slice_bound hW σ h).2
  have hM := sliceConst_nonneg hW
  calc ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) = ∫⁻ y, ‖sliceConvection (W σ) h y‖ₑ ^ 2 :=
        lintegral_congr_ae (hf.mono fun y hy =>
          (congrArg (fun x : Space => ENNReal.ofReal (‖x‖ ^ 2)) hy).trans (ofReal_norm_sq_eq _))
    _ = eLpNorm (sliceConvection (W σ) h) 2 volume ^ 2 :=
        (JointRepresentativeInternal.sq_eLpNorm_two _ _).symm
    _ ≤ ENNReal.ofReal (sliceConst D * ‖h‖) ^ 2 := by gcongr
    _ = ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖h‖ ^ 2) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg hM (norm_nonneg h)), mul_pow,
          ENNReal.ofReal_mul (sq_nonneg (sliceConst D))]

theorem periodLIntegral_le {W : ℝ → Space → Space} {D : ℝ} (hW : IsFirstOrderCoefficient W D)
    (u : XX) (F : ℝ → Space → Space)
    (hF : ∀ᵐ σ : ℝ, F σ =ᵐ[volume]
      sliceConvection (W σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) ≤
      ENNReal.ofReal ((sliceConst D * ‖gradCLM u‖) ^ 2) := by
  have hmeas : AEMeasurable (fun t : TimeCircle =>
      ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)) volume :=
    ((gradPart.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).norm.pow
      2).aemeasurable.ennreal_ofReal
  calc periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) := rfl
    _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))‖ ^ 2) :=
      lintegral_mono_ae (ae_restrict_of_ae (hF.mono fun σ hσ => lintegral_slice_le hW σ _ _ hσ))
    _ = ∫⁻ t, ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) :=
      lintegral_Icc_coe (fun t => ENNReal.ofReal (sliceConst D ^ 2) *
        ENNReal.ofReal (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2)) (hmeas.const_mul _)
    _ = ENNReal.ofReal (sliceConst D ^ 2) * ENNReal.ofReal (‖gradCLM u‖ ^ 2) :=
      (lintegral_const_mul'' (ENNReal.ofReal (sliceConst D ^ 2)) hmeas).trans
        (congrArg (fun x => ENNReal.ofReal (sliceConst D ^ 2) * x) (ofReal_norm_sq_gradCLM u).symm)
    _ = ENNReal.ofReal ((sliceConst D * ‖gradCLM u‖) ^ 2) :=
      (ENNReal.ofReal_mul (sq_nonneg (sliceConst D))).symm.trans
        (congrArg ENNReal.ofReal (mul_pow (sliceConst D) ‖gradCLM u‖ 2).symm)

theorem periodic_readingConvection {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsFirstOrderCoefficient W D) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : IsTimePeriodic (readingConvection W v G) := by
  intro σ y
  have hw : W (σ + 1) = W σ := funext (hW.periodic σ)
  simp only [readingConvection, hw, hr.periodic_gradient σ y, hr.periodic_velocity σ y]

theorem exists_sliceCurve (h1 : ReadingExistsHolds) {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsFirstOrderCoefficient W D) (u : XX) :
    ∃ c, IsSliceCurve W u c ∧ ‖c‖ ≤ sliceConst D * ‖gradCLM u‖ := by
  have e := h1 u
  have hr : IsReadingOf u e.choose e.choose_spec.choose e.choose_spec.choose_spec.choose :=
    e.choose_spec.choose_spec.choose_spec.1
  have hs := readingConvection_slice hr W
  have hfin := periodLIntegral_le hW u _ hs
  have ec := exists_curve_of_joint (readingConvection W e.choose e.choose_spec.choose)
    (aesm_readingConvection hW hr.measurable_velocity hr.measurable_gradient)
    (periodic_readingConvection hW hr) (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  refine ⟨ec.choose, ?_, ?_⟩
  · have h' : ∀ᵐ σ : ℝ, ((ec.choose (σ : TimeCircle) : L2R) : Space → Space) =ᵐ[volume]
        sliceConvection (W σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := by
      filter_upwards [ec.choose_spec.1, hs] with σ ha hb using ha.trans hb
    exact ae_circle_of_ae (f := W) (periodic_of_isTimePeriodic hW.periodic)
      (R := fun t w => ((ec.choose t : L2R) : Space → Space) =ᵐ[volume]
        sliceConvection w (gradPart ((u : TimeCircle → XBar) t))) h'
  · have hM : 0 ≤ sliceConst D * ‖gradCLM u‖ :=
      mul_nonneg (sliceConst_nonneg hW) (norm_nonneg (gradCLM u))
    have hsq : ‖ec.choose‖ ^ 2 ≤ (sliceConst D * ‖gradCLM u‖) ^ 2 :=
      (le_of_eq ec.choose_spec.2).trans (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hfin)
    exact (pow_le_pow_iff_left₀ (norm_nonneg ec.choose) hM (by norm_num)).1 hsq

theorem exists_sliceCurveCLM (h1 : ReadingExistsHolds) {W : ℝ → Space → Space} {D : ℝ}
    (hW : IsFirstOrderCoefficient W D) :
    ∃ T : XX →L[ℝ] CurveSpace, ∀ u,
      IsSliceCurve W u (T u) ∧ ‖T u‖ ≤ sliceConst D * ‖gradCLM u‖ := by
  choose c hc hb using exists_sliceCurve h1 hW
  let L : XX →ₗ[ℝ] CurveSpace :=
    { toFun := c
      map_add' := fun u u' => sliceCurve_unique (hc (u + u')) (isSliceCurve_add (hc u) (hc u'))
      map_smul' := fun a u => sliceCurve_unique (hc (a • u)) (isSliceCurve_smul a (hc u)) }
  refine ⟨L.mkContinuous (sliceConst D * ‖gradCLM‖) fun u => ?_, fun u => ⟨hc u, hb u⟩⟩
  calc ‖L u‖ ≤ sliceConst D * ‖gradCLM u‖ := hb u
    _ ≤ sliceConst D * (‖gradCLM‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (gradCLM.le_opNorm u) (sliceConst_nonneg hW)
    _ = sliceConst D * ‖gradCLM‖ * ‖u‖ := by ring

theorem physToHH_eq_convection {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ} {D : ℝ}
    (hW : IsFirstOrderCoefficient (d.profile p) D) (hc : ConvectionSpec d p (convection d p))
    {u : XX} {F : ℝ → Space → Space} (hper : IsTimePeriodic F)
    (hF : ∀ᵐ σ : ℝ, F σ =ᵐ[volume]
      sliceConvection (d.profile p σ) (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)))) :
    physToHH F = convection d p u := by
  have hpair : Function.Periodic (fun σ => (F σ, d.profile p σ)) 1 := fun σ =>
    Prod.ext (periodic_of_isTimePeriodic hper σ) (periodic_of_isTimePeriodic hW.periodic σ)
  have h1 : ∀ᵐ t : TimeCircle, F (circleRep t) =ᵐ[volume]
      sliceConvection (d.profile p (circleRep t)) (gradPart ((u : TimeCircle → XBar) t)) :=
    ae_circle_of_ae (f := fun σ => (F σ, d.profile p σ)) hpair
      (R := fun t q => q.1 =ᵐ[volume] sliceConvection q.2 (gradPart ((u : TimeCircle → XBar) t)))
      hF
  have h2 : (onCircle fun σ => solField (F σ)) =ᵐ[volume]
      ((convection d p u : HH) : TimeCircle → HBar) := by
    filter_upwards [h1, hc u] with t ht hct
    exact (congrArg solProj (toLpOrZero_congr ht)).trans hct.symm
  have hm : MemLp (onCircle fun σ => solField (F σ)) 2 volume := (Lp.memLp _).ae_eq h2.symm
  exact ((dif_pos hm).trans (Lp.ext (hm.coeFn_toLp.trans h2)) :
    circleLpOrZero (onCircle fun σ => solField (F σ)) = convection d p u)

end Internal.ConvectionFirstOrder

open Internal.Convection Internal.ConvectionFirstOrder in
theorem extendedConvectionHolds_of (h1 : ReadingExistsHolds) (_h2 : ProjectionHolds)
    (h3 : TestPairingHolds) : ExtendedConvectionHolds := by
  intro k d hd q hq
  have hW : IsFirstOrderCoefficient (d.toCertificateData.profile q) d.toCertificateData.decay :=
    isFirstOrderCoefficient_profile hd hq
  have eT := exists_sliceCurveCLM h1 hW
  have hspec := convectionSpec_of_curve (d := d.toCertificateData) (p := q) eT.choose
    (fun u => (eT.choose_spec u).1)
  have hconv := convection_eq_of_spec hspec
  have hc : ConvectionSpec d.toCertificateData q (convection d.toCertificateData q) := fun u =>
    (EventuallyEq.of_eq (congrArg (fun L : XX →L[ℝ] HH => ((L u : HH) : TimeCircle → HBar))
      hconv)).trans (hspec u)
  refine ⟨⟨_, hspec⟩, ⟨‖solProj‖ * sliceConst d.toCertificateData.decay, fun u => ?_⟩, ?_⟩
  · calc ‖convection d.toCertificateData q u‖ =
          ‖(ContinuousLinearMap.compLpL 2 volume solProj) (eT.choose u)‖ :=
          congrArg (‖·‖) (DFunLike.congr_fun hconv u)
      _ ≤ ‖ContinuousLinearMap.compLpL 2 volume solProj‖ * ‖eT.choose u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖solProj‖ * (sliceConst d.toCertificateData.decay * ‖gradCLM u‖) :=
        mul_le_mul (ContinuousLinearMap.norm_compLpL_le _) (eT.choose_spec u).2 (norm_nonneg _)
          (norm_nonneg _)
      _ = ‖solProj‖ * sliceConst d.toCertificateData.decay * ‖gradCLM u‖ := by ring
  · intro u v G H hr φ hφ
    have hs := readingConvection_slice hr (d.toCertificateData.profile q)
    have hF : IsPeriodicField (readingConvection (d.toCertificateData.profile q) v G) :=
      ⟨aesm_readingConvection hW hr.measurable_velocity hr.measurable_gradient,
        periodic_readingConvection hW hr,
        lt_of_le_of_lt (periodLIntegral_le hW u _ hs) ENNReal.ofReal_lt_top⟩
    have hphys := physToHH_eq_convection hW hc (periodic_readingConvection hW hr) hs
    exact ((congrArg (fun x => inner ℝ x (testInHH φ)) hphys).symm.trans (h3 _ hF φ hφ)).symm

end Breakdown.Cert
