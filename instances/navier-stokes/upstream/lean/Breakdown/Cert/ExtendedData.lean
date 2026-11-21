import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.Data

open scoped ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedData

open Internal.Data

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_weak_part {P : ℝ} {V : ℝ → Space → Space}
    (hV : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2)) :
    Continuous (fun z : ℝ × Space => (1 / P) • deriv (fun s => V s z.2) z.1 + (1 / 2 : ℝ) • V z.1 z.2
      + (1 / 2 : ℝ) • fderiv ℝ (V z.1) z.2 z.2) ∧
    Continuous (fun z : ℝ × Space => advectionAt (V z.1) z.2) := by
  have hVc : Continuous (fun z : ℝ × Space => V z.1 z.2) := hV.continuous
  have h1 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (V z.1) z.2) :=
    contDiff_fderiv_param hV (by rw [zero_add])
  have h1c := h1.continuous
  have ht : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun s => V s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => V s z.2) (g := fun z => z.1)
      (hV.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by rw [zero_add])
  have htc : Continuous (fun z : ℝ × Space => deriv (fun s => V s z.2) z.1) :=
    ht.continuous.clm_apply continuous_const
  exact ⟨((htc.const_smul (1 / P)).add (hVc.const_smul (1 / 2 : ℝ))).add
    ((h1c.clm_apply continuous_snd).const_smul (1 / 2 : ℝ)), h1c.clm_apply hVc⟩

theorem aestronglyMeasurable_weakDefect {k : ℕ} {P : ℝ} {V : ℝ → Space → Space}
    {Hs : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ)
    (hV : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => Hs z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hb : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => b i z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => weakDefectField P V Hs g b lam z.1 z.2) volume := by
  obtain ⟨hC, hA⟩ := continuous_weak_part (P := P) hV
  have hT : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (Hs z.1 z.2)) volume :=
    continuous_secondDerivTrace.comp_aestronglyMeasurable hH
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, lam i • b i z.1 z.2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hb i).const_smul (lam i)
  exact (((hC.aestronglyMeasurable.sub hT).add hA.aestronglyMeasurable).add hS).add hg

theorem weakDefect_periodic {k : ℕ} {P : ℝ} {V : ℝ → Space → Space}
    {Hs : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ) (hV : IsTimePeriodic V)
    (hH : IsTimePeriodic Hs) (hg : IsTimePeriodic g) (hb : ∀ i, IsTimePeriodic (b i)) :
    IsTimePeriodic (weakDefectField P V Hs g b lam) := by
  intro σ y
  have h1 : V (σ + 1) = V σ := funext (hV σ)
  have h2 : Hs (σ + 1) y = Hs σ y := hH σ y
  have h3 : deriv (fun s => V s y) (σ + 1) = deriv (fun s => V s y) σ := by
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hV s y
  have h4 : ∀ i, b i (σ + 1) y = b i σ y := fun i => hb i σ y
  have h5 : g (σ + 1) y = g σ y := hg σ y
  simp only [weakDefectField, h1, h2, h3, h4, h5]

theorem defect_field {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) : IsPeriodicField (d.defect q) := by
  have hV : ContDiff ℝ 1 (fun z : ℝ × Space => d.profile q z.1 z.2) :=
    hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)
  exact ⟨aestronglyMeasurable_weakDefect _ hV (hd.profileSecondDeriv_measurable q hq)
      (hd.pressureGrad_measurable q hq) hd.actuator_measurable,
    weakDefect_periodic _ (hd.profile_periodic q) (hd.profileSecondDeriv_periodic q hq)
      (hd.pressureGrad_periodic q hq) hd.actuator_periodic,
    lt_of_le_of_lt (hd.defect_l2 q hq) ENNReal.ofReal_lt_top⟩

theorem defect_norm (h1 : ProjectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    ‖d.defectH q‖ ≤ d.defectBound q := by
  have hb := hd.defect_nonneg q hq
  have hsq : ‖d.defectH q‖ ^ 2 ≤ d.defectBound q ^ 2 :=
    (norm_physToHH_sq_le h1 (defect_field hd hq)).trans
      (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (hd.defect_l2 q hq))
  nlinarith [norm_nonneg (d.defectH q), hb.1]

theorem actuator_fin {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans hd.actuator_norm)

theorem actuator_field {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) : IsPeriodicField (d.actuator i) :=
  ⟨hd.actuator_measurable i, hd.actuator_periodic i, lt_top_iff_ne_top.2 (actuator_fin hd i)⟩

theorem pin_fold_meas {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) : AEStronglyMeasurable
      (fun z : ℝ × Space => d.pin i (circleRep (z.1 : TimeCircle)) z.2) volume :=
  aestronglyMeasurable_fold (hd.pin_measurable i)

theorem pin_fold_period {k : ℕ} (d : ExtendedCertificateData k) (i : Fin k) :
    periodLIntegral (fun σ y => matSq (d.pin i (circleRep (σ : TimeCircle)) y)) =
      periodLIntegral (fun σ y => matSq (d.pin i σ y)) := by
  unfold periodLIntegral
  rw [setLIntegral_congr Ico_ae_eq_Icc.symm, setLIntegral_congr Ico_ae_eq_Icc.symm]
  exact setLIntegral_congr_fun measurableSet_Ico fun σ hσ => by
    simp only [circleRep_coe_of_mem hσ]

theorem pin_fold_fin {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) (j : Fin 3) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal
      (‖d.pin i (circleRep (σ : TimeCircle)) y (unitVector j)‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt ?_ ((pin_fold_period d i).symm ▸ hd.pin_finite i)
  refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  exact Finset.single_le_sum (f := fun l : Fin 3 =>
    ‖d.pin i (circleRep (σ : TimeCircle)) y (unitVector l)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem exists_pin_curve {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (i : Fin k) (j : Fin 3) : ∃ c : Lp (α := TimeCircle) L2R 2,
      ∀ᵐ t : TimeCircle, (c t : Space → Space) =ᵐ[volume]
        fun y => d.pin i (circleRep t) y (unitVector j) := by
  obtain ⟨c, hc, -⟩ := exists_curve_of_joint
    (fun σ y => d.pin i (circleRep (σ : TimeCircle)) y (unitVector j))
    (((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      (pin_fold_meas hd i)).congr (ae_of_all _ fun z => rfl))
    (fun σ y => by simp only [circleRep_coe_add_one]) (pin_fold_fin hd i j)
  exact ⟨c, (ae_coe_iff _).2 hc⟩

theorem exists_pinSpec {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d) :
    ∃ T, PinSpec d.toCertificateData T := by
  choose cp hcp using exists_pin_curve hd
  exact ⟨pinCLM cp, pinSpec_pinCLM d.toCertificateData cp hcp⟩

theorem pinMap_eq (h3 : ReadingEnergyHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {u : XX} {v G H} (hr : IsReadingOf u v G H) (i : Fin k) :
    pinMap d.toCertificateData u i = pinValue (d.pin i) G := by
  have hex := exists_pinSpec hd
  have hpm : PinSpec d.toCertificateData (pinMap d.toCertificateData) := by
    unfold pinMap
    rw [dif_pos hex]
    exact hex.choose_spec
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, ⟨d.weightMax, hd.weightFn_upper⟩⟩
  have hχ := (h3 d.weightFn d.weight hw u v G H hr).2.2
    (fun σ y => d.pin i (circleRep (σ : TimeCircle)) y) (pin_fold_meas hd i)
    (fun σ y => by simp only [circleRep_coe_add_one])
    (by rw [pin_fold_period d i]; exact hd.pin_finite i)
  have hval : pinValue (fun σ y => d.pin i (circleRep (σ : TimeCircle)) y) G =
      pinValue (d.pin i) G := by
    unfold pinValue
    rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
    exact setIntegral_congr_fun measurableSet_Ico fun σ hσ => by
      simp only [circleRep_coe_of_mem hσ]
  rw [hpm u i, ← hval, hχ]
  simp only [coe_circleRep, sliceOf]
  rfl

theorem actuator_pairing (h2 : TestPairingHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (κ : Fin k → ℝ) (φ : ℝ → Space → Space)
    (hφ : IsSpaceTimeTestField φ) :
    inner ℝ (actuatorH d.toCertificateData κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
  choose c hc _ using fun i => exists_curve_of_joint (d.actuator i) (actuator_field hd i).1
    (actuator_field hd i).2.1 (actuator_field hd i).2.2
  have hcF : ∀ᵐ σ : ℝ, ((∑ i, κ i • c i) (σ : TimeCircle) : Space → Space) =ᵐ[volume]
      fun y => ∑ i, κ i • d.actuator i σ y := actuator_sum_curve (d := d.toCertificateData) κ c hc
  have hper : IsTimePeriodic (fun σ y => ∑ i, κ i • d.actuator i σ y) := fun σ y =>
    Finset.sum_congr rfl fun i _ => by rw [hd.actuator_periodic i σ y]
  have hFa : IsPeriodicField (fun σ y => ∑ i, κ i • d.actuator i σ y) :=
    ⟨Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hd.actuator_measurable i).const_smul (κ i),
      hper, by rw [periodLIntegral_eq_of_curve _ hcF]; exact ENNReal.ofReal_lt_top⟩
  have e1 : physToHH (fun σ y => ∑ i, κ i • d.actuator i σ y) =
      ContinuousLinearMap.compLpL 2 volume solProj (∑ i, κ i • c i) := physToHH_eq hper _ hcF
  have e2 : ∀ i, physToHH (d.actuator i) = ContinuousLinearMap.compLpL 2 volume solProj (c i) :=
    fun i => physToHH_eq (hd.actuator_periodic i) (c i) (hc i)
  have hA : actuatorH d.toCertificateData κ =
      ∑ i, κ i • ContinuousLinearMap.compLpL 2 volume solProj (c i) :=
    (actuatorH_apply d.toCertificateData κ).trans
      (Finset.sum_congr rfl fun i _ => congrArg (fun x => κ i • x) (e2 i))
  have hA' : actuatorH d.toCertificateData κ = physToHH (fun σ y => ∑ i, κ i • d.actuator i σ y) :=
    hA.trans ((compLpL_sum solProj κ c).symm.trans e1.symm)
  exact (congrArg (fun x => inner ℝ x (testInHH φ)) hA').trans (h2 _ hFa φ hφ)

theorem actuator_norm_le (h1 : ProjectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (κ : Fin k → ℝ) :
    ‖actuatorH d.toCertificateData κ‖ ≤ d.actuatorBound * vecNorm κ := by
  rw [actuatorH_apply]
  have hx : ∀ i, ‖physToHH (d.actuator i)‖ ^ 2 ≤
      (periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2)).toReal := fun i =>
    norm_physToHH_sq_le h1 (actuator_field hd i)
  have hsum : ∑ i, ‖physToHH (d.actuator i)‖ ^ 2 ≤ d.actuatorBound ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hx i).trans ?_
    rw [← ENNReal.toReal_sum fun i _ => actuator_fin hd i]
    exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hd.actuator_norm
  have hs : Real.sqrt (∑ i, ‖physToHH (d.actuator i)‖ ^ 2) ≤ d.actuatorBound := by
    rw [← Real.sqrt_sq hd.actuatorBound_nonneg]
    exact Real.sqrt_le_sqrt hsum
  calc ‖∑ i, κ i • physToHH (d.actuator i)‖ ≤ ∑ i, ‖κ i • physToHH (d.actuator i)‖ :=
        norm_sum_le _ _
    _ = ∑ i, |κ i| * ‖physToHH (d.actuator i)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ i, |κ i| ^ 2) * Real.sqrt (∑ i, ‖physToHH (d.actuator i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = vecNorm κ * Real.sqrt (∑ i, ‖physToHH (d.actuator i)‖ ^ 2) := by
        simp only [sq_abs, vecNorm]
    _ ≤ vecNorm κ * d.actuatorBound :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = d.actuatorBound * vecNorm κ := mul_comm _ _

end Internal.ExtendedData

open Internal.ExtendedData

theorem extendedDataHolds_of (h1 : ProjectionHolds) (h2 : TestPairingHolds)
    (h3 : ReadingEnergyHolds) : ExtendedDataHolds := fun _ hd _ hq =>
  ⟨defect_field hd hq, fun φ hφ => h2 _ (defect_field hd hq) φ hφ, defect_norm h1 hd hq,
    fun κ φ hφ => actuator_pairing h2 hd κ φ hφ, fun κ => actuator_norm_le h1 hd κ,
    exists_pinSpec hd, fun _ _ _ _ hr i => pinMap_eq h3 hd hr i⟩

end Breakdown.Cert
