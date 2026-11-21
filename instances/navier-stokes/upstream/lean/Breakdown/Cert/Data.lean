import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.JointRepresentative

open scoped ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.Data

theorem coeFn_finset_sum {α E ι : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (s : Finset ι) (f : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Lp.coeFn_add _ _).trans (EventuallyEq.rfl.add ih)

theorem ofReal_norm_sq_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E 2 μ) : ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    JointRepresentativeInternal.sq_eLpNorm_two]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem coe_circleRep (t : TimeCircle) : ((circleRep t : ℝ) : TimeCircle) = t :=
  AddCircle.coe_equivIco

theorem circleRep_coe (x : ℝ) : circleRep (x : TimeCircle) = Int.fract x := by
  have h := AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x
  rw [div_one, mul_one] at h
  exact h

theorem circleRep_coe_of_mem {σ : ℝ} (h : σ ∈ Ico (0 : ℝ) 1) : circleRep (σ : TimeCircle) = σ := by
  rw [circleRep_coe, Int.fract_eq_self]
  exact h

theorem circleRep_coe_sub {n : ℤ} {σ : ℝ} (h : σ ∈ Ico (n : ℝ) (n + 1)) :
    circleRep (σ : TimeCircle) = σ - n := by
  rw [circleRep_coe, ← Int.self_sub_floor, Int.floor_eq_iff.2 h]

theorem circleRep_coe_add_one (σ : ℝ) : circleRep (((σ + 1 : ℝ)) : TimeCircle) = circleRep σ := by
  rw [AddCircle.coe_add_period]

theorem aestronglyMeasurable_fold {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] {f : ℝ → Space → E}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => f (circleRep (z.1 : TimeCircle)) z.2) volume := by
  rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ × Space))), ← univ_prod_univ,
    ← iUnion_Ico_intCast, iUnion_prod_const, aestronglyMeasurable_iUnion_iff]
  intro n
  have hmp : MeasurePreserving (fun z : ℝ × Space => (z.1 - n, z.2)) volume volume :=
    (measurePreserving_sub_right volume (n : ℝ)).prod (MeasurePreserving.id volume)
  refine (hf.comp_measurePreserving hmp).restrict.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ)] with z hz
  simp only [Function.comp_apply]
  rw [circleRep_coe_sub hz.1]

theorem contDiff_fderiv_param {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {V : E → Space → G} {m n : WithTop ℕ∞}
    (hV : ContDiff ℝ m (fun z : E × Space => V z.1 z.2)) (hnm : n + 1 ≤ m) :
    ContDiff ℝ n (fun z : E × Space => fderiv ℝ (V z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : E × Space) (y : Space) => V z.1 y) (g := fun z => z.2)
    (hV.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd hnm

theorem continuous_defect_smooth {P : ℝ} {V : ℝ → Space → Space} {Q : ℝ → Space → ℝ}
    (hV : ContDiff ℝ 2 (fun z : ℝ × Space => V z.1 z.2))
    (hQ : ContDiff ℝ 1 (fun z : ℝ × Space => Q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => (1 / P) • deriv (fun s => V s z.2) z.1 + (1 / 2 : ℝ) • V z.1 z.2
      + (1 / 2 : ℝ) • fderiv ℝ (V z.1) z.2 z.2 - sumSecondPartialsAt (V z.1) z.2 + advectionAt (V z.1) z.2)
    ∧ Continuous (fun z : ℝ × Space => gradientAt (Q z.1) z.2) := by
  have hVc : Continuous (fun z : ℝ × Space => V z.1 z.2) := hV.continuous
  have h1 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (V z.1) z.2) :=
    contDiff_fderiv_param hV one_add_one_eq_two.le
  have h1c := h1.continuous
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun y => fderiv ℝ (V z.1) y) z.2) :=
    contDiff_fderiv_param (V := fun (s : ℝ) y => fderiv ℝ (V s) y) h1 (by rw [zero_add])
  have h2c := h2.continuous
  have ht : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun s => V s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => V s z.2) (g := fun z => z.1)
      (hV.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst one_add_one_eq_two.le
  have htc : Continuous (fun z : ℝ × Space => deriv (fun s => V s z.2) z.1) :=
    ht.continuous.clm_apply continuous_const
  have hssp : (fun z : ℝ × Space => sumSecondPartialsAt (V z.1) z.2) = fun z =>
      ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (V z.1) y) z.2 (unitVector i) (unitVector i) := by
    funext z
    simp [sumSecondPartialsAt, iteratedFDeriv_two_apply]
  have hsspc : Continuous (fun z : ℝ × Space => sumSecondPartialsAt (V z.1) z.2) := by
    rw [hssp]
    exact continuous_finsetSum _ fun i _ =>
      (h2c.clm_apply continuous_const).clm_apply continuous_const
  have hq : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (Q z.1) z.2) :=
    contDiff_fderiv_param hQ (by rw [zero_add])
  refine ⟨((((htc.const_smul (1 / P)).add (hVc.const_smul (1 / 2 : ℝ))).add
    ((h1c.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))).sub hsspc).add (h1c.clm_apply hVc), ?_⟩
  exact continuous_finsetSum _ fun i _ =>
    (hq.continuous.clm_apply continuous_const).smul continuous_const

theorem aestronglyMeasurable_defect {k : ℕ} {P : ℝ} {V : ℝ → Space → Space} {Q : ℝ → Space → ℝ}
    {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ)
    (hV : ContDiff ℝ 2 (fun z : ℝ × Space => V z.1 z.2))
    (hQ : ContDiff ℝ 1 (fun z : ℝ × Space => Q z.1 z.2))
    (hb : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => b i z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => defectField P V Q b lam z.1 z.2) volume := by
  obtain ⟨hC, hG⟩ := continuous_defect_smooth (P := P) hV hQ
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, lam i • b i z.1 z.2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hb i).const_smul (lam i)
  exact (hC.aestronglyMeasurable.add hS).add hG.aestronglyMeasurable

theorem defect_periodic {k : ℕ} {P : ℝ} {V : ℝ → Space → Space} {Q : ℝ → Space → ℝ}
    {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ) (hV : IsTimePeriodic V)
    (hQ : IsTimePeriodic Q) (hb : ∀ i, IsTimePeriodic (b i)) :
    IsTimePeriodic (defectField P V Q b lam) := by
  intro σ y
  have h1 : V (σ + 1) = V σ := funext (hV σ)
  have h2 : Q (σ + 1) = Q σ := funext (hQ σ)
  have h3 : deriv (fun s => V s y) (σ + 1) = deriv (fun s => V s y) σ := by
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hV s y
  have h4 : ∀ i, b i (σ + 1) y = b i σ y := fun i => hb i σ y
  simp only [defectField, h1, h2, h3, h4]

theorem norm_solProj_op (h1 : ProjectionHolds) : ‖solProj‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => by rw [one_mul]; exact h1.2.1 F

theorem circleLpOrZero_eq {E : Type*} [NormedAddCommGroup E] (g : TimeCircle → E)
    (f : Lp (α := TimeCircle) E 2) (h : g =ᵐ[volume] ⇑f) : circleLpOrZero g = f := by
  have hm : MemLp g 2 volume := (Lp.memLp f).ae_eq h.symm
  rw [circleLpOrZero, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem physToHH_eq {F : ℝ → Space → Space} (hper : IsTimePeriodic F)
    (c : Lp (α := TimeCircle) L2R 2)
    (hc : ∀ᵐ σ : ℝ, (c (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ) :
    physToHH F = ContinuousLinearMap.compLpL 2 volume solProj c := by
  have hs : ∀ᵐ t : TimeCircle, toLpOrZero 2 (F (circleRep t)) = c t := by
    rw [ae_coe_iff]
    filter_upwards [hc] with σ hσ
    have hr : F (circleRep (σ : TimeCircle)) = F σ :=
      JointRepresentativeInternal.periodic_of_coe_eq hper (coe_circleRep _)
    rw [hr]
    have hm : MemLp (F σ) 2 volume := (Lp.memLp (c σ)).ae_eq hσ
    rw [toLpOrZero, dif_pos hm]
    exact Lp.ext (hm.coeFn_toLp.trans hσ.symm)
  have hg : (onCircle fun σ => solField (F σ)) =ᵐ[volume]
      ⇑(ContinuousLinearMap.compLpL 2 volume solProj c) := by
    filter_upwards [hs, ContinuousLinearMap.coeFn_compLpL solProj c] with t ht ht'
    rw [ht']
    show solProj (toLpOrZero 2 (F (circleRep t))) = solProj (c t)
    rw [ht]
  exact circleLpOrZero_eq _ _ hg

theorem periodLIntegral_eq_of_curve {F : ℝ → Space → Space} (c : Lp (α := TimeCircle) L2R 2)
    (hc : ∀ᵐ σ : ℝ, (c (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) = ENNReal.ofReal (‖c‖ ^ 2) := by
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖c t‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable c).norm.aemeasurable.pow_const 2).ennreal_ofReal
  unfold periodLIntegral
  rw [ofReal_norm_sq_Lp c, ← lintegral_Icc_coe _ hmeas]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hc] with σ hσ
  rw [ofReal_norm_sq_Lp (c σ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hσ] with y hy
  rw [hy]

theorem norm_physToHH_sq_le (h1 : ProjectionHolds) {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    ‖physToHH F‖ ^ 2 ≤ (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal := by
  obtain ⟨c, hc, hn⟩ := exists_curve_of_joint F hF.1 hF.2.1 hF.2.2
  rw [physToHH_eq hF.2.1 c hc]
  have hle : ‖ContinuousLinearMap.compLpL 2 volume solProj c‖ ≤ ‖c‖ := by
    have h := ContinuousLinearMap.norm_compLp_le solProj c
    have h' : ‖solProj‖ * ‖c‖ ≤ ‖c‖ :=
      (mul_le_mul_of_nonneg_right (norm_solProj_op h1) (norm_nonneg _)).trans (by rw [one_mul])
    exact h.trans h'
  calc ‖ContinuousLinearMap.compLpL 2 volume solProj c‖ ^ 2 ≤ ‖c‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := hn

end Internal.Data

namespace Internal.Data

theorem actuatorH_apply {k : ℕ} (d : CertificateData k) (κ : Fin k → ℝ) :
    actuatorH d κ = ∑ i, κ i • physToHH (d.actuator i) := by
  simp [actuatorH, actuatorSlice]

theorem pinSlice_eq_inner {χ : Space → (Space →L[ℝ] Space)} (h : Freq.X) (c : Fin 3 → L2R)
    (hc : ∀ j, (c j : Space → Space) =ᵐ[volume] fun y => χ y (unitVector j)) :
    ∑ j : Fin 3, inner ℝ (c j) (partialX j h) = pinSlice χ h := by
  have hint : ∀ j : Fin 3, Integrable (fun y => inner ℝ ((partialX j h : Space → Space) y)
      (χ y (unitVector j))) volume := fun j =>
    (L2.integrable_inner (𝕜 := ℝ) (partialX j h) (c j)).congr (by
      filter_upwards [hc j] with y hy
      rw [hy])
  unfold pinSlice
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hc j] with y hy
  rw [hy, real_inner_comm]

theorem inner_compLpL_eq (c : Lp (α := TimeCircle) L2R 2) (u : XX) (j : Fin 3) :
    inner ℝ c (ContinuousLinearMap.compLpL 2 volume (partialX j ∘L gradPart) u) =
      ∫ t, inner ℝ (c t) (partialX j (gradPart ((u : TimeCircle → XBar) t))) := by
  refine (L2.inner_def _ _).trans (integral_congr_ae ?_)
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (partialX j ∘L gradPart) u] with t ht
  exact congrArg (fun w => inner ℝ (c t) w) ht

theorem integrable_inner_slice (c : Lp (α := TimeCircle) L2R 2) (u : XX) (j : Fin 3) :
    Integrable (fun t => inner ℝ (c t) (partialX j (gradPart ((u : TimeCircle → XBar) t)))) volume :=
  (L2.integrable_inner (𝕜 := ℝ) c
    (ContinuousLinearMap.compLpL 2 volume (partialX j ∘L gradPart) u)).congr (by
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (partialX j ∘L gradPart) u] with t ht
      exact congrArg (fun w => inner ℝ (c t) w) ht)

def pinCLM {k : ℕ} (cp : Fin k → Fin 3 → Lp (α := TimeCircle) L2R 2) : XX →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 3,
    (innerSL ℝ (cp i j)).comp (ContinuousLinearMap.compLpL 2 volume (partialX j ∘L gradPart))

theorem pinCLM_apply {k : ℕ} (cp : Fin k → Fin 3 → Lp (α := TimeCircle) L2R 2) (u : XX) (i : Fin k) :
    pinCLM cp u i = ∑ j : Fin 3,
      inner ℝ (cp i j) (ContinuousLinearMap.compLpL 2 volume (partialX j ∘L gradPart) u) := by
  simp [pinCLM]

theorem pinSpec_pinCLM {k : ℕ} (d : CertificateData k)
    (cp : Fin k → Fin 3 → Lp (α := TimeCircle) L2R 2)
    (hcp : ∀ i j, ∀ᵐ t : TimeCircle, (cp i j t : Space → Space) =ᵐ[volume]
      fun y => d.pin i (circleRep t) y (unitVector j)) : PinSpec d (pinCLM cp) := by
  intro u i
  rw [pinCLM_apply]
  simp only [inner_compLpL_eq]
  rw [← integral_finsetSum _ fun j _ => integrable_inner_slice (cp i j) u j]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 (hcp i)] with t ht
  exact pinSlice_eq_inner _ _ ht

theorem defect_field {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) : IsPeriodicField (defectField (d.period p) (d.profile p) (d.pressure p)
      d.actuator (d.multiplier p)) := by
  have hV : ContDiff ℝ 2 (fun z : ℝ × Space => d.profile p z.1 z.2) :=
    hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)
  exact ⟨aestronglyMeasurable_defect _ hV (hd.pressure_smooth p hp) hd.actuator_measurable,
    defect_periodic _ (hd.profile_periodic p) (hd.pressure_periodic p hp) hd.actuator_periodic,
    lt_of_le_of_lt (hd.defect_l2 p hp) ENNReal.ofReal_lt_top⟩

theorem actuator_fin {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k) :
    periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans hd.actuator_norm)

theorem actuator_field {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k) :
    IsPeriodicField (d.actuator i) :=
  ⟨hd.actuator_measurable i, hd.actuator_periodic i, lt_top_iff_ne_top.2 (actuator_fin hd i)⟩

theorem pin_fold_meas {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k) :
    AEStronglyMeasurable (fun z : ℝ × Space => d.pin i (circleRep (z.1 : TimeCircle)) z.2) volume :=
  aestronglyMeasurable_fold (hd.pin_measurable i)

theorem pin_fold_period {k : ℕ} (d : CertificateData k) (i : Fin k) :
    periodLIntegral (fun σ y => matSq (d.pin i (circleRep (σ : TimeCircle)) y)) =
      periodLIntegral (fun σ y => matSq (d.pin i σ y)) := by
  unfold periodLIntegral
  rw [setLIntegral_congr Ico_ae_eq_Icc.symm, setLIntegral_congr Ico_ae_eq_Icc.symm]
  exact setLIntegral_congr_fun measurableSet_Ico fun σ hσ => by
    simp only [circleRep_coe_of_mem hσ]

theorem pin_fold_fin {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k) (j : Fin 3) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal
      (‖d.pin i (circleRep (σ : TimeCircle)) y (unitVector j)‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt ?_ ((pin_fold_period d i).symm ▸ hd.pin_finite i)
  refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  exact Finset.single_le_sum (f := fun l : Fin 3 =>
    ‖d.pin i (circleRep (σ : TimeCircle)) y (unitVector l)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem exists_pin_curve {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (i : Fin k)
    (j : Fin 3) : ∃ c : Lp (α := TimeCircle) L2R 2,
      ∀ᵐ t : TimeCircle, (c t : Space → Space) =ᵐ[volume]
        fun y => d.pin i (circleRep t) y (unitVector j) := by
  obtain ⟨c, hc, -⟩ := exists_curve_of_joint
    (fun σ y => d.pin i (circleRep (σ : TimeCircle)) y (unitVector j))
    (((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      (pin_fold_meas hd i)).congr (ae_of_all _ fun z => rfl))
    (fun σ y => by simp only [circleRep_coe_add_one]) (pin_fold_fin hd i j)
  exact ⟨c, (ae_coe_iff _).2 hc⟩

theorem exists_pinSpec {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) :
    ∃ T, PinSpec d T := by
  choose cp hcp using exists_pin_curve hd
  exact ⟨pinCLM cp, pinSpec_pinCLM d cp hcp⟩

theorem pinMap_eq (h3 : ReadingEnergyHolds) {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {u : XX} {v G H} (hr : IsReadingOf u v G H) (i : Fin k) :
    pinMap d u i = pinValue (d.pin i) G := by
  have hex := exists_pinSpec hd
  have hpm : PinSpec d (pinMap d) := by
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

theorem defect_norm (h1 : ProjectionHolds) {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) : ‖defectH d p‖ ≤ d.defectBound p := by
  have hb := hd.defect_nonneg p hp
  have hsq : ‖defectH d p‖ ^ 2 ≤ d.defectBound p ^ 2 :=
    (norm_physToHH_sq_le h1 (defect_field hd hp)).trans
      (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (hd.defect_l2 p hp))
  nlinarith [norm_nonneg (defectH d p), hb.1]

theorem actuator_sum_curve {k : ℕ} {d : CertificateData k} (κ : Fin k → ℝ)
    (c : Fin k → Lp (α := TimeCircle) L2R 2)
    (hc : ∀ i, ∀ᵐ σ : ℝ, (c i (σ : TimeCircle) : Space → Space) =ᵐ[volume] d.actuator i σ) :
    ∀ᵐ σ : ℝ, ((∑ i, κ i • c i) (σ : TimeCircle) : Space → Space) =ᵐ[volume]
      fun y => ∑ i, κ i • d.actuator i σ y := by
  have e1 : ∀ᵐ t : TimeCircle, (∑ i, κ i • c i) t = ∑ i, κ i • c i t := by
    filter_upwards [coeFn_finset_sum Finset.univ (fun i => κ i • c i),
      ae_all_iff.2 fun i => Lp.coeFn_smul (κ i) (c i)] with t ht ht'
    rw [ht, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [ht' i]; rfl
  rw [ae_coe_iff] at e1
  filter_upwards [e1, ae_all_iff.2 hc] with σ h h'
  rw [h]
  filter_upwards [coeFn_finset_sum Finset.univ (fun i => κ i • c i (σ : TimeCircle)),
    ae_all_iff.2 fun i => Lp.coeFn_smul (κ i) (c i (σ : TimeCircle)), ae_all_iff.2 h']
    with y hy hy' hy''
  rw [hy, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [hy' i, Pi.smul_apply, hy'' i]

theorem clm_sum {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] {k : ℕ} (T : E →L[ℝ] F) (κ : Fin k → ℝ) (c : Fin k → E) :
    T (∑ i, κ i • c i) = ∑ i, κ i • T (c i) := by
  simp only [map_sum, map_smul]

theorem compLpL_sum {k : ℕ} (L : L2R →L[ℝ] HBar) (κ : Fin k → ℝ)
    (c : Fin k → Lp L2R 2 (volume : Measure TimeCircle)) :
    ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) L (∑ i, κ i • c i) =
      ∑ i, κ i • ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) L (c i) :=
  clm_sum _ κ c

theorem actuator_pairing (h2 : TestPairingHolds) {k : ℕ} {d : CertificateData k}
    (hd : IsCertificate d) (κ : Fin k → ℝ) (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    inner ℝ (actuatorH d κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2) := by
  choose c hc _ using fun i => exists_curve_of_joint (d.actuator i) (actuator_field hd i).1
    (actuator_field hd i).2.1 (actuator_field hd i).2.2
  have hcF := actuator_sum_curve κ c hc
  have hper : IsTimePeriodic (fun σ y => ∑ i, κ i • d.actuator i σ y) := fun σ y =>
    Finset.sum_congr rfl fun i _ => by rw [hd.actuator_periodic i σ y]
  have hFa : IsPeriodicField (fun σ y => ∑ i, κ i • d.actuator i σ y) :=
    ⟨Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hd.actuator_measurable i).const_smul (κ i),
      hper, by rw [periodLIntegral_eq_of_curve _ hcF]; exact ENNReal.ofReal_lt_top⟩
  have e1 : physToHH (fun σ y => ∑ i, κ i • d.actuator i σ y) =
      ContinuousLinearMap.compLpL 2 volume solProj (∑ i, κ i • c i) := physToHH_eq hper _ hcF
  have e2 : ∀ i, physToHH (d.actuator i) = ContinuousLinearMap.compLpL 2 volume solProj (c i) :=
    fun i => physToHH_eq (hd.actuator_periodic i) (c i) (hc i)
  have hA : actuatorH d κ = ∑ i, κ i • ContinuousLinearMap.compLpL 2 volume solProj (c i) :=
    (actuatorH_apply d κ).trans (Finset.sum_congr rfl fun i _ => congrArg (fun x => κ i • x) (e2 i))
  have hA' : actuatorH d κ = physToHH (fun σ y => ∑ i, κ i • d.actuator i σ y) :=
    hA.trans ((compLpL_sum solProj κ c).symm.trans e1.symm)
  exact (congrArg (fun x => inner ℝ x (testInHH φ)) hA').trans (h2 _ hFa φ hφ)

theorem actuator_norm_le (h1 : ProjectionHolds) {k : ℕ} {d : CertificateData k}
    (hd : IsCertificate d) (κ : Fin k → ℝ) : ‖actuatorH d κ‖ ≤ d.actuatorBound * vecNorm κ := by
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

end Internal.Data

open Internal.Data

theorem dataHolds_of (h1 : ProjectionHolds) (h2 : TestPairingHolds) (h3 : ReadingEnergyHolds) :
    DataHolds := fun _ hd _ hp =>
  ⟨fun φ hφ => h2 _ (defect_field hd hp) φ hφ, defect_norm h1 hd hp,
    fun κ φ hφ => actuator_pairing h2 hd κ φ hφ, fun κ => actuator_norm_le h1 hd κ,
    exists_pinSpec hd, fun _ _ _ _ hr i => pinMap_eq h3 hd hr i⟩

end Breakdown.Cert
