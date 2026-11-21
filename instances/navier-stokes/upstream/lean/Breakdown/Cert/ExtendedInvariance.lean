import Breakdown.Cert.ExtendedInvarianceTest
import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldLimitReadings

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedInvariance

open Internal.Invariance Internal.ExtendedInvarianceTrace Internal.ExtendedInvarianceTest

variable {k : ℕ} {d : ExtendedCertificateData k}

theorem profile_shift (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) :
    d.profile q (σ + γ.2) = pushForward γ.1 (d.profile q σ) := by
  funext y
  have := hd.profile_invariant q hq γ hγ σ (γ.1.symm y)
  simpa [pushForward] using this

theorem profile_slice_contDiff (hd : IsExtendedCertificate d) (q : Fin k → ℝ) (σ : ℝ) :
    ContDiff ℝ 1 (d.profile q σ) :=
  hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

theorem profile_slice_differentiable (hd : IsExtendedCertificate d) (q : Fin k → ℝ) (σ : ℝ) :
    Differentiable ℝ (d.profile q σ) :=
  (profile_slice_contDiff hd q σ).differentiable (by norm_num)

theorem convection_mem (h1 : ExtendedConvectionHolds)
    (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {u : XX} (hu : IsInvariantXX d.symmetries u) :
    convection d.toCertificateData q u ∈ invariantHH d.symmetries := by
  refine mem_invariantHH_of fun γ hγ => shift_eq_rot_of_ae ?_
  have hs := convectionSpec_of (h1 d hd q hq).1 u
  filter_upwards [hs, ae_shift γ.2 hs, grad_shift hu hγ] with t b1 b2 b3
  have eW : d.profile q (circleRep (t + (γ.2 : TimeCircle))) =
      pushForward γ.1 (d.profile q (circleRep t)) :=
    (periodic_shift (hd.profile_periodic q) t γ.2).trans (profile_shift hd hq hγ _)
  exact b2.trans ((congrArg₂ (fun W h => solField (sliceConvection W h)) eW b3).trans
    ((solField_congr (sliceConvection_pushForward γ.1
      (profile_slice_differentiable hd q _) _)).trans
      ((solField_pushForward hP _ _).trans (congrArg (rotX γ.1) b1.symm))))

theorem actuatorH_mem (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (hd : IsExtendedCertificate d) (κ : Fin k → ℝ) :
    actuatorH d.toCertificateData κ ∈ invariantHH d.symmetries := by
  refine (congrArg (fun w => w ∈ invariantHH d.symmetries)
    (actuatorH_apply d.toCertificateData κ)).mpr ?_
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact mem_invariantHH_of fun γ hγ => physToHH_shift (hd.actuator_periodic i)
    (solField_shift_of_ae hP (hd.actuator_invariant i γ hγ))

def smoothPart (P : ℝ) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => W s y) σ + (1 / 2 : ℝ) • W σ y + (1 / 2 : ℝ) • fderiv ℝ (W σ) y y
    + advectionAt (W σ) y

def forcePart (b : Fin k → ℝ → Space → Space) (lam : Fin k → ℝ) (σ : ℝ) (y : Space) : Space :=
  ∑ i, lam i • b i σ y

def restPart (d : ExtendedCertificateData k) (q : Fin k → ℝ) (σ : ℝ) (y : Space) : Space :=
  d.defect q σ y - d.pressureGrad q σ y

theorem restPart_eq (q : Fin k → ℝ) (σ : ℝ) (y : Space) :
    restPart d q σ y = smoothPart (d.period q) (d.profile q) σ y
      - secondDerivTrace (d.profileSecondDeriv q σ y) + forcePart d.actuator (d.multiplier q) σ y := by
  simp only [restPart, smoothPart, forcePart, ExtendedCertificateData.defect, weakDefectField]
  abel

theorem defect_eq (q : Fin k → ℝ) (σ : ℝ) (y : Space) :
    d.defect q σ y = restPart d q σ y + d.pressureGrad q σ y := by
  simp only [restPart, sub_add_cancel]

theorem deriv_shift (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) (y : Space) :
    deriv (fun s => d.profile q s y) (σ + γ.2) =
      γ.1 (deriv (fun s => d.profile q s (γ.1.symm y)) σ) := by
  have hc : ContDiff ℝ 1 (fun s => d.profile q s (γ.1.symm y)) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hg := (hc.differentiable (by norm_num) σ).hasDerivAt
  have h3 := ((γ.1.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).hasFDerivAt.comp_hasDerivAt σ hg
  have e : (fun s => d.profile q (s + γ.2) y) = fun s => γ.1 (d.profile q s (γ.1.symm y)) := by
    funext s
    rw [profile_shift hd hq hγ s]
    rfl
  have h4 : HasDerivAt (fun s => γ.1 (d.profile q s (γ.1.symm y)))
      (γ.1 (deriv (fun s => d.profile q s (γ.1.symm y)) σ)) σ := h3
  rw [← deriv_comp_add_const, e, h4.deriv]

theorem smoothPart_shift (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) (y : Space) :
    smoothPart (d.period q) (d.profile q) (σ + γ.2) y =
      γ.1 (smoothPart (d.period q) (d.profile q) σ (γ.1.symm y)) := by
  have hdiff := profile_slice_differentiable hd q σ
  simp only [smoothPart, advectionAt]
  rw [profile_shift hd hq hγ σ, deriv_shift hd hq hγ σ y]
  simp only [fderiv_pushForward γ.1 hdiff]
  simp only [pushForward, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]

theorem continuous_secondDerivTrace' : Continuous secondDerivTrace :=
  continuous_finsetSum _ fun _ _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem measurePreserving_shift (a : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (z.1 + a, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume a).prod (MeasurePreserving.id volume)

theorem measurePreserving_rot (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (fun z : ℝ × Space => (z.1, R z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id volume).prod R.measurePreserving

theorem integral_shift (f : ℝ × Space → ℝ) (a : ℝ) :
    ∫ z : ℝ × Space, f (z.1 + a, z.2) = ∫ z, f z :=
  (measurePreserving_shift a).integral_comp
    ((MeasurableEquiv.addRight a).prodCongr (MeasurableEquiv.refl Space)).measurableEmbedding f

theorem integral_rot (f : ℝ × Space → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∫ z : ℝ × Space, f (z.1, R z.2) = ∫ z, f z :=
  (measurePreserving_rot R).integral_comp
    ((MeasurableEquiv.refl ℝ).prodCongr R.toHomeomorph.toMeasurableEquiv).measurableEmbedding f

theorem secondDeriv_ae (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) :
    ∀ᵐ z : ℝ × Space, secondDerivTrace (d.profileSecondDeriv q (z.1 + γ.2) z.2) =
      γ.1 (secondDerivTrace (d.profileSecondDeriv q z.1 (γ.1.symm z.2))) := by
  have hm := hd.profileSecondDeriv_measurable q hq
  have hF : AEStronglyMeasurable
      (fun z : ℝ × Space => secondDerivTrace (d.profileSecondDeriv q (z.1 + γ.2) z.2)) volume :=
    continuous_secondDerivTrace'.comp_aestronglyMeasurable
      (hm.comp_measurePreserving (measurePreserving_shift γ.2))
  have hG : AEStronglyMeasurable
      (fun z : ℝ × Space => γ.1 (secondDerivTrace (d.profileSecondDeriv q z.1 (γ.1.symm z.2)))) volume :=
    γ.1.continuous.comp_aestronglyMeasurable (continuous_secondDerivTrace'.comp_aestronglyMeasurable
      (hm.comp_measurePreserving (measurePreserving_rot γ.1.symm)))
  have hs : ∀ σ : ℝ, ∀ᵐ y : Space, secondDerivTrace (d.profileSecondDeriv q (σ + γ.2) y) =
      γ.1 (secondDerivTrace (d.profileSecondDeriv q σ (γ.1.symm y))) := fun σ =>
    secondDerivTrace_pushForward γ.1 (profile_slice_differentiable hd q σ)
      (hd.profileSecondDeriv_weak q hq σ) (fun j => by
        have h := hd.profileSecondDeriv_weak q hq (σ + γ.2) j
        rwa [profile_shift hd hq hγ σ] at h)
  rw [Measure.volume_eq_prod] at hF hG ⊢
  exact Internal.HeldLimitReadings.ae_prod_of_ae_ae hF hG (Eventually.of_forall hs)

theorem force_ae (hd : IsExtendedCertificate d) (q : Fin k → ℝ)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) :
    ∀ᵐ z : ℝ × Space, forcePart d.actuator (d.multiplier q) (z.1 + γ.2) z.2 =
      γ.1 (forcePart d.actuator (d.multiplier q) z.1 (γ.1.symm z.2)) := by
  have hb : ∀ i, ∀ᵐ z : ℝ × Space, d.actuator i (z.1 + γ.2) z.2 =
      γ.1 (d.actuator i z.1 (γ.1.symm z.2)) := by
    intro i
    filter_upwards [(measurePreserving_rot γ.1.symm).quasiMeasurePreserving.ae
      (hd.actuator_invariant i γ hγ)] with z hz
    simpa using hz
  filter_upwards [ae_all_iff.2 hb] with z hz
  simp only [forcePart, hz, map_sum, map_smul]

theorem rest_ae (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) :
    ∀ᵐ z : ℝ × Space, restPart d q (z.1 + γ.2) z.2 = γ.1 (restPart d q z.1 (γ.1.symm z.2)) := by
  filter_upwards [secondDeriv_ae hd hq hγ, force_ae hd q hγ] with z h1 h2
  rw [restPart_eq, restPart_eq, smoothPart_shift hd hq hγ, h1, h2, map_add, map_sub]

theorem continuous_smoothPart (P : ℝ) {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => smoothPart P W z.1 z.2) := by
  have hD : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    contDiff_fderiv_slice hW (by norm_num)
  have hT : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun s => W s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => W s z.2) (g := Prod.fst)
      (hW.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by norm_num)
  have hTc : Continuous (fun z : ℝ × Space => deriv (fun s => W s z.2) z.1) :=
    hT.continuous.clm_apply continuous_const
  exact (((hTc.const_smul (1 / P)).add (hW.continuous.const_smul (1 / 2 : ℝ))).add
    ((hD.continuous.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))).add
    (hD.continuous.clm_apply hW.continuous)

theorem norm_trace_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  unfold secondDerivTrace
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ‖H‖ := fun j => by
    have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
    calc ‖H (unitVector j) (unitVector j)‖ ≤ ‖H (unitVector j)‖ * ‖unitVector j‖ :=
          (H (unitVector j)).le_opNorm _
      _ ≤ ‖H‖ * ‖unitVector j‖ * ‖unitVector j‖ :=
          mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
      _ = ‖H‖ := by rw [hu, mul_one, mul_one]
  calc ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖H‖ :=
        Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖H‖ := by simp

theorem profile_joint_contDiff (hd : IsExtendedCertificate d) (q : Fin k → ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2) :=
  hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem defect_isPeriodicField (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    IsPeriodicField (d.defect q) := by
  have hW := profile_joint_contDiff hd q
  have hS : AEStronglyMeasurable
      (fun z : ℝ × Space => forcePart d.actuator (d.multiplier q) z.1 z.2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((hd.actuator_measurable i).const_smul (d.multiplier q i) :
        AEStronglyMeasurable (fun z : ℝ × Space => d.multiplier q i • d.actuator i z.1 z.2) volume)
  have hH : AEStronglyMeasurable
      (fun z : ℝ × Space => secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) volume :=
    continuous_secondDerivTrace'.comp_aestronglyMeasurable (hd.profileSecondDeriv_measurable q hq)
  have e : (fun z : ℝ × Space => d.defect q z.1 z.2) = fun z =>
      smoothPart (d.period q) (d.profile q) z.1 z.2 - secondDerivTrace (d.profileSecondDeriv q z.1 z.2)
        + forcePart d.actuator (d.multiplier q) z.1 z.2 + d.pressureGrad q z.1 z.2 := by
    funext z
    rw [defect_eq, restPart_eq]
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => d.defect q z.1 z.2) volume := by
    rw [e]
    exact (((continuous_smoothPart _ hW).aestronglyMeasurable.sub hH).add hS).add
      (hd.pressureGrad_measurable q hq)
  refine ⟨hm, ?_, lt_of_le_of_lt (hd.defect_l2 q hq) ENNReal.ofReal_lt_top⟩
  intro σ y
  have hW1 : d.profile q (σ + 1) = d.profile q σ := funext (hd.profile_periodic q σ)
  have hH1 : d.profileSecondDeriv q (σ + 1) = d.profileSecondDeriv q σ :=
    funext (hd.profileSecondDeriv_periodic q hq σ)
  have hg : d.pressureGrad q (σ + 1) = d.pressureGrad q σ := funext (hd.pressureGrad_periodic q hq σ)
  have hb : ∀ i, d.actuator i (σ + 1) = d.actuator i σ := fun i => funext (hd.actuator_periodic i σ)
  have hdv : deriv (fun s => d.profile q s y) (σ + 1) = deriv (fun s => d.profile q s y) σ := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f σ) (funext fun s => hd.profile_periodic q s y)
  simp only [ExtendedCertificateData.defect, weakDefectField, hW1, hH1, hg, hb, hdv]

theorem inner_hasCompactSupport {ψ : ℝ → Space → Space}
    (hc : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) (A : ℝ × Space → Space) :
    HasCompactSupport (fun z : ℝ × Space => inner ℝ (A z) (ψ z.1 z.2)) := by
  refine hc.mono' fun z hz => subset_tsupport _ ?_
  rw [Function.mem_support] at hz ⊢
  intro h0
  apply hz
  show inner ℝ (A z) (ψ z.1 z.2) = 0
  rw [show ψ z.1 z.2 = 0 from h0, inner_zero_right]

theorem rest_integrable (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {ψ : ℝ → Space → Space} (hψ : IsSpaceTimeTestField ψ) :
    Integrable (fun z : ℝ × Space => inner ℝ (restPart d q z.1 z.2) (ψ z.1 z.2)) := by
  obtain ⟨hs, hc, -⟩ := hψ
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hc
  have hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2) := hs.continuous
  have hW := profile_joint_contDiff hd q
  have I1 : Integrable (fun z : ℝ × Space =>
      inner ℝ (smoothPart (d.period q) (d.profile q) z.1 z.2) (ψ z.1 z.2)) :=
    ((continuous_smoothPart _ hW).inner hψc).integrable_of_hasCompactSupport
      (inner_hasCompactSupport hc _)
  have hdec : 0 ≤ d.decay := by
    have h := (hd.profile_decay q hq 0 0).1
    have h2 := (norm_nonneg _).trans h
    simpa using h2
  have hHb : ∀ σ y, ‖d.profileSecondDeriv q σ y‖ ≤ d.decay := fun σ y =>
    (hd.profile_decay q hq σ y).2.2.trans
      (div_le_self hdec (one_le_pow₀ (by linarith [norm_nonneg y])))
  have I2 : Integrable (fun z : ℝ × Space =>
      inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (ψ z.1 z.2)) := by
    refine Integrable.mono' (((hψc.norm).integrable_of_hasCompactSupport hc.norm).const_mul
      (3 * d.decay)) ((continuous_secondDerivTrace'.comp_aestronglyMeasurable
        (hd.profileSecondDeriv_measurable q hq)).inner hψc.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right ((norm_trace_le _).trans
      (mul_le_mul_of_nonneg_left (hHb _ _) (by norm_num))) (norm_nonneg _)
  have hb : ∀ i, IsPeriodicField (d.actuator i) := fun i =>
    ⟨hd.actuator_measurable i, hd.actuator_periodic i, lt_of_le_of_lt
      ((Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
        (fun j _ => bot_le) (Finset.mem_univ i)).trans hd.actuator_norm) ENNReal.ofReal_lt_top⟩
  have I3 : Integrable (fun z : ℝ × Space =>
      inner ℝ (forcePart d.actuator (d.multiplier q) z.1 z.2) (ψ z.1 z.2)) := by
    have e : (fun z : ℝ × Space => inner ℝ (forcePart d.actuator (d.multiplier q) z.1 z.2) (ψ z.1 z.2)) =
        fun z => ∑ i, d.multiplier q i * inner ℝ (d.actuator i z.1 z.2) (ψ z.1 z.2) := by
      funext z
      simp only [forcePart, sum_inner, real_inner_smul_left]
    rw [e]
    exact integrable_finsetSum _ fun i _ =>
      (Internal.TestPairing.integrable_pairing (hb i) hs hc hR).const_mul (d.multiplier q i)
  have e : (fun z : ℝ × Space => inner ℝ (restPart d q z.1 z.2) (ψ z.1 z.2)) = fun z =>
      inner ℝ (smoothPart (d.period q) (d.profile q) z.1 z.2) (ψ z.1 z.2)
        - inner ℝ (secondDerivTrace (d.profileSecondDeriv q z.1 z.2)) (ψ z.1 z.2)
        + inner ℝ (forcePart d.actuator (d.multiplier q) z.1 z.2) (ψ z.1 z.2) := by
    funext z
    rw [restPart_eq, inner_add_left, inner_sub_left]
  rw [e]
  exact (I1.sub I2).add I3

theorem defect_pairing (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params)
    {ψ : ℝ → Space → Space} (hψ : IsSpaceTimeTestField ψ) :
    ∫ z : ℝ × Space, inner ℝ (d.defect q z.1 z.2) (ψ z.1 z.2) =
      ∫ z : ℝ × Space, inner ℝ (restPart d q z.1 z.2) (ψ z.1 z.2) := by
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hψ.2.1
  have hD := Internal.TestPairing.integrable_pairing (defect_isPeriodicField hd hq) hψ.1 hψ.2.1 hR
  have hE := rest_integrable hd hq hψ
  have e : (fun z : ℝ × Space => inner ℝ (d.defect q z.1 z.2) (ψ z.1 z.2)) =
      fun z => inner ℝ (restPart d q z.1 z.2) (ψ z.1 z.2) +
        inner ℝ (d.pressureGrad q z.1 z.2) (ψ z.1 z.2) := by
    funext z
    rw [defect_eq, inner_add_left]
  have hG : Integrable (fun z : ℝ × Space => inner ℝ (d.pressureGrad q z.1 z.2) (ψ z.1 z.2)) := by
    refine (hD.sub hE).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, defect_eq, inner_add_left, add_sub_cancel_left]
  rw [e, integral_add hE hG, hd.pressureGrad_orthogonal q hq ψ hψ, add_zero]

theorem defect_mem (h3 : TestPairingHolds) (h4 : TestDenseHolds)
    (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    d.defectH q ∈ invariantHH d.symmetries := by
  refine mem_invariantHH_of fun γ hγ => sub_eq_zero.1 (h4 _ fun φ hφ => ?_)
  have hPF := defect_isPeriodicField hd hq
  have hφa := isSpaceTimeTestField_shift hφ (-γ.2)
  have hφR := isSpaceTimeTestField_rot hφ γ.1
  have hae := rest_ae hd hq hγ
  have ea : inner ℝ ((shiftLp γ.2 : HH →L[ℝ] HH) (d.defectH q)) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (restPart d q (z.1 + γ.2) z.2) (φ z.1 z.2) := by
    refine (inner_shiftLp γ.2 _ _).trans ((congrArg (inner ℝ (d.defectH q))
      (shiftLp_testInHH φ (-γ.2))).trans ((h3 _ hPF _ hφa).trans
        ((defect_pairing hd hq hφa).trans ?_)))
    refine (integral_shift (fun z : ℝ × Space =>
      inner ℝ (restPart d q z.1 z.2) (φ (z.1 + -γ.2) z.2)) γ.2).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [add_neg_cancel_right]
  have eR : inner ℝ (rotHH γ.1 (d.defectH q)) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (γ.1 (restPart d q z.1 (γ.1.symm z.2))) (φ z.1 z.2) := by
    refine (inner_rotHH γ.1 _ _).trans ((congrArg (inner ℝ (d.defectH q))
      (rotHH_testInHH hP γ.1 φ)).trans ((h3 _ hPF _ hφR).trans
        ((defect_pairing hd hq hφR).trans ?_)))
    refine (integral_rot (fun z : ℝ × Space =>
      inner ℝ (restPart d q z.1 z.2) (γ.1.symm (φ z.1 (γ.1 z.2)))) γ.1.symm).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rw [← γ.1.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  refine (inner_sub_left _ _ _).trans ((congrArg₂ (fun x y : ℝ => x - y) ea eR).trans
    (sub_eq_zero.2 (integral_congr_ae ?_)))
  filter_upwards [hae] with z hz
  exact congrArg (fun v => inner ℝ v (φ z.1 z.2)) hz

end Internal.ExtendedInvariance

open Internal.ExtendedInvariance

theorem extendedInvarianceHolds_of (h1 : ExtendedConvectionHolds) (h2 : ProjectionHolds)
    (h3 : TestPairingHolds) (h4 : TestDenseHolds) : ExtendedInvarianceHolds := by
  intro k d hd q hq
  have hP := h2.2.2.1
  exact ⟨fun u hu => ⟨convection_mem h1 hP hd hq hu, Internal.Invariance.productH_mem hP hu⟩,
    fun κ => actuatorH_mem hP hd κ, defect_mem h3 h4 hP hd hq⟩

end Breakdown.Cert
