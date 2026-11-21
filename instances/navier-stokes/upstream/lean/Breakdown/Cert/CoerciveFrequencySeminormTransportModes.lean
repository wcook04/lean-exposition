import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

open ModeDerivative.Internal

theorem weak_radial {f : Space → Space} {F : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f F)
    {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    ∫ y, θ y • F y y = -∫ y, (3 * θ y + fderiv ℝ θ y y) • f y := by
  have hco : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space => y j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  have htest : ∀ j : Fin 3, IsTestFunction (fun y => θ y * y j) := fun j =>
    ⟨hθ.1.mul (hco j), hθ.2.mul_right⟩
  have hder : ∀ j : Fin 3, ∀ y, fderiv ℝ (fun y => θ y * y j) y (unitVector j) =
      fderiv ℝ θ y (unitVector j) * y j + θ y := by
    intro j y
    have hd1 : DifferentiableAt ℝ θ y := (hθ.1.differentiable (by simp)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y : Space => y j) y := ((hco j).differentiable (by simp)).differentiableAt
    rw [fderiv_fun_mul hd1 hd2]
    have : fderiv ℝ (fun y : Space => y j) y = (EuclideanSpace.proj (𝕜 := ℝ) j : Space →L[ℝ] ℝ) :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).fderiv
    simp [this, unitVector]
    ring
  have hw := fun j => h.2.2 _ (htest j) j
  have hF : ∀ y, θ y • F y y = ∑ j : Fin 3, (θ y * y j) • F y (unitVector j) := by
    intro y
    have hy := congrArg (F y) (vec_eq_sum y)
    simp only [map_sum, map_smul] at hy
    rw [hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  have hD : ∀ y, (3 * θ y + fderiv ℝ θ y y) • f y =
      ∑ j : Fin 3, fderiv ℝ (fun y => θ y * y j) y (unitVector j) • f y := by
    intro y
    simp only [hder]
    rw [← Finset.sum_smul]
    congr 1
    have hy := congrArg (fderiv ℝ θ y) (vec_eq_sum y)
    simp only [map_sum, map_smul, smul_eq_mul] at hy
    rw [hy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  have hI1 : ∀ j : Fin 3, Integrable (fun y => (θ y * y j) • F y (unitVector j)) volume := by
    intro j
    have hi : Integrable (fun y => (θ y * y j) • F y) volume :=
      h.2.1.integrable_smul_left_of_hasCompactSupport (htest j).1.continuous (htest j).2
    exact hi.apply_continuousLinearMap (unitVector j)
  have hI2 : ∀ j : Fin 3, Integrable (fun y => fderiv ℝ (fun y => θ y * y j) y (unitVector j) • f y) volume := by
    intro j
    have hc : Continuous (fun y => fderiv ℝ (fun y => θ y * y j) y (unitVector j)) :=
      ((htest j).1.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h.1.integrable_smul_left_of_hasCompactSupport hc ((htest j).2.fderiv_apply (𝕜 := ℝ) _)
  simp_rw [hF, hD]
  rw [integral_finsetSum _ fun j _ => hI1 j, integral_finsetSum _ fun j _ => hI2 j, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hw j

theorem derivative_locallyIntegrable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    LocallyIntegrable (fun z : ℝ × Space => g z.1 z.2) volume := by
  intro x
  set I : Set ℝ := Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) with hI
  set S : Set (ℝ × Space) := Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1 with hS
  refine ⟨S, prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
  refine ⟨hv.measurable_derivative.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hper : Function.Periodic (fun σ => ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2)) 1 := fun σ => by
    simp only [hv.periodic_derivative σ]
  have hΦ : ∫⁻ σ in I, ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2) < ⊤ := by
    rw [hI, Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic _ hper]
    exact hv.derivative_finite
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) volume :=
    (hv.measurable_derivative.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hSf : volume S < ⊤ :=
    ((Metric.isBounded_Ioo _ _).prod Metric.isBounded_ball).measure_lt_top
  calc ∫⁻ z in S, ‖g z.1 z.2‖ₑ ≤ ∫⁻ z in S, (1 + ENNReal.ofReal (‖g z.1 z.2‖ ^ 2)) := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (g z.1 z.2)])
    _ = volume S + ∫⁻ z in S, ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ ≤ volume S + ∫⁻ z in I ×ˢ (Set.univ : Set Space), ENNReal.ofReal (‖g z.1 z.2‖ ^ 2) := by
        exact add_le_add le_rfl (lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioc_self (Set.subset_univ _)))
    _ = volume S + ∫⁻ σ in I, ∫⁻ y, ENNReal.ofReal (‖g σ y‖ ^ 2) := by
        rw [Measure.volume_eq_prod, setLIntegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖g z.1 z.2‖ ^ 2))
          hm.restrict, Measure.restrict_univ]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hSf, hΦ⟩

theorem mode_weakGradient (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hvl : LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) (σ : ℝ) :
    IsWeakGradient (fun y => reVec (modeVel ι v σ y)) (fun y => reMat (modeGrad ι G σ y)) ∧
      IsWeakGradient (fun y => imVec (modeVel ι v σ y)) (fun y => imMat (modeGrad ι G σ y)) := by
  have hav := fun (K : Set Space) (hK : IsCompact K) => integrable_velFamily hRot hv hvl σ hK
  have hag := fun (K : Set Space) (hK : IsCompact K) => integrable_gradFamily hRot hv hGl σ hK
  have hw := ae_weakGradient_vel hRot hv σ
  have sv := ae_slice_integrable hav
  have sg := ae_slice_integrable hag
  constructor
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightRe ι) (measurable_weightRe ι) (abs_weightRe_le ι) hav hag hw) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (reVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (reMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightIm ι) (measurable_weightIm ι) (abs_weightIm_le ι) hav hag hw) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (imVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (imMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm

theorem integrable_family (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ : ℝ) {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => velFamily F σ q.2 q.1) ((volume.restrict K).prod angleMeasure) :=
  integrable_of_rot (integrable_rotated hRot hFm hFl σ hK) (fun φ w => axialRot (-φ) w)
    (continuous_axialRot_comp (X := ℝ × Space) continuous_fst.neg continuous_snd)
    (fun _ _ => (norm_axialRot hRot _ _).le)

theorem ae_modeVel_average (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (ι : ℤ × ℤ) (σ : ℝ) :
    (∀ᵐ y, reVec (modeVel ι F σ y) = ∫ p, weightRe ι p • velFamily F σ p y ∂angleMeasure) ∧
      ∀ᵐ y, imVec (modeVel ι F σ y) = ∫ p, weightIm ι p • velFamily F σ p y ∂angleMeasure := by
  have sv := ae_slice_integrable (F := velFamily F σ) fun K hK => integrable_family hRot hFm hFl σ hK
  refine ⟨?_, ?_⟩
  · filter_upwards [sv] with y hy
    exact reVec_modeAverage ι (f := fun τ φ => velFamily F σ (τ, φ) y) hy
  · filter_upwards [sv] with y hy
    exact imVec_modeAverage ι (f := fun τ φ => velFamily F σ (τ, φ) y) hy

theorem average_pairing (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ : ℝ) {c : ℝ × ℝ → ℝ}
    (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {θ : Space → ℝ} (hθ : IsTestFunction θ) (w : Space → ℝ)
    (hw : Continuous w) (hw0 : ∀ y, y ∉ tsupport θ → w y = 0) {X : Space → Space}
    (hX : ∀ᵐ y, X y = ∫ p, c p • velFamily F σ p y ∂angleMeasure) :
    ∫ y, w y • X y = ∫ p, c p • (∫ y, w y • velFamily F σ p y) ∂angleMeasure := by
  rw [← average_swap hθ w hw hw0 c hcm hc (integrable_family hRot hFm hFl σ hθ.2)]
  refine integral_congr_ae ?_
  filter_upwards [hX] with y hy
  rw [hy]

theorem test_weight_zero {θ : Space → ℝ} (y : Space) (hy : y ∉ tsupport θ) :
    -θ y - (1 / 2) * fderiv ℝ θ y y = 0 := by
  have h1 : θ y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h2 : y ∉ tsupport (fderiv ℝ θ) := fun h => hy (tsupport_fderiv_subset ℝ h)
  rw [h1, image_eq_zero_of_notMem_tsupport h2]
  simp

theorem continuous_test_weight {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    Continuous (fun y => -θ y - (1 / 2) * fderiv ℝ θ y y) :=
  (hθ.1.continuous.neg).sub (continuous_const.mul
    ((hθ.1.continuous_fderiv (by simp)).clm_apply continuous_id))

theorem integrable_pairing_family (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ : ℝ) {θ : Space → ℝ}
    (hθ : IsTestFunction θ) (w : Space → ℝ) (hw : Continuous w) (hw0 : ∀ y, y ∉ tsupport θ → w y = 0) :
    Integrable (fun p => ∫ y, w y • velFamily F σ p y) angleMeasure := by
  have ha := integrable_family hRot hFm hFl σ hθ.2
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, ‖w y‖ ≤ B := by
    have hcs : HasCompactSupport w := by
      refine hθ.2.mono' ?_
      intro y hy
      by_contra h
      exact hy (hw0 y h)
    exact hw.bounded_above_of_compact_support hcs
  have hF : Integrable (fun q : Space × (ℝ × ℝ) => w q.1 • velFamily F σ q.2 q.1)
      ((volume : Measure Space).prod angleMeasure) := by
    refine integrable_of_restrict_tsupport hθ ?_ fun q hq => by simp [hw0 q.1 hq]
    refine Integrable.mono' (ha.norm.const_mul B) ?_ ?_
    · exact ((hw.comp continuous_fst).aestronglyMeasurable).smul ha.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hB q.1) (norm_nonneg _)
  exact hF.integral_prod_right

theorem locallyIntegrable_angleFamily (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ φ : ℝ) :
    LocallyIntegrable (fun q : ℝ × Space => velFamily F σ (q.1, φ) q.2) volume := by
  obtain ⟨R, hR⟩ := hRot.1 φ
  set e : ℝ × Space ≃ₜ ℝ × Space := (Homeomorph.addLeft σ).prodCongr R.toHomeomorph with he
  have he_apply : ∀ q : ℝ × Space, e q = (σ + q.1, axialRot φ q.2) := fun q => by
    simp [he, Prod.map, hR]
  have hmp : MeasurePreserving e volume volume := by
    have hm := (measurePreserving_add_left (volume : Measure ℝ) σ).prod R.measurePreserving
    rw [← Measure.volume_eq_prod] at hm
    have hf : (Prod.map (fun x : ℝ => σ + x) (R : Space → Space)) = (e : ℝ × Space → ℝ × Space) := by
      funext q; rw [he_apply]; simp [Prod.map, hR]
    rw [← hf]; exact hm
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  have h1 : IntegrableOn (fun z : ℝ × Space => F z.1 z.2) (e '' K) volume :=
    hFl.integrableOn_isCompact (hK.image e.continuous)
  have h2 := (hmp.integrableOn_image hemb).1 h1
  have ef : (fun q : ℝ × Space => velFamily F σ (q.1, φ) q.2) =
      fun q => axialRot (-φ) (((fun z : ℝ × Space => F z.1 z.2) ∘ e) q) := by
    funext q; simp only [velFamily, Function.comp, he_apply]
  rw [ef]
  refine Integrable.mono h2 ((continuous_axialRot_comp continuous_const continuous_id).comp_aestronglyMeasurable
    h2.aestronglyMeasurable) (Filter.Eventually.of_forall fun q => ?_)
  rw [norm_axialRot hRot]

theorem locallyIntegrable_pairing_time (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ φ : ℝ) {w : Space → ℝ}
    (hw : Continuous w) (hws : HasCompactSupport w) (k : Fin 3) :
    LocallyIntegrable (fun τ => (∫ y, w y • velFamily F σ (τ, φ) y) k) volume := by
  have hLI := locallyIntegrable_angleFamily hRot hFl σ φ
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  have hKt : IsCompact (tsupport w) := hws
  have h1 : IntegrableOn (fun q : ℝ × Space => w q.2 • velFamily F σ (q.1, φ) q.2) (K ×ˢ tsupport w) volume :=
    (hLI.integrableOn_isCompact (hK.prod hKt)).continuousOn_smul (hw.comp continuous_snd).continuousOn
      (hK.prod hKt)
  have h2 : IntegrableOn (fun q : ℝ × Space => w q.2 • velFamily F σ (q.1, φ) q.2) (K ×ˢ Set.univ) volume := by
    refine h1.of_forall_sdiff_eq_zero (hK.measurableSet.prod MeasurableSet.univ) fun q hq => ?_
    have : q.2 ∉ tsupport w := fun h => hq.2 ⟨hq.1.1, h⟩
    rw [image_eq_zero_of_notMem_tsupport this, zero_smul]
  have h3 : Integrable (fun q : ℝ × Space => w q.2 • velFamily F σ (q.1, φ) q.2)
      ((volume.restrict K).prod volume) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at h2
    exact h2
  have h4 := h3.integral_prod_left
  have h5 := (EuclideanSpace.proj (𝕜 := ℝ) k).integrable_comp h4
  show Integrable _ (volume.restrict K)
  simpa using h5

def timeCutoff (s : ℝ) : ℝ := Real.smoothTransition (s + 1) - Real.smoothTransition s

def timeCutoffDeriv (s : ℝ) : ℝ := deriv Real.smoothTransition (s + 1) - deriv Real.smoothTransition s

theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) : deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with x hx using Real.smoothTransition.zero_of_nonpos (le_of_lt hx)
    rw [h.deriv_eq, deriv_const]
  · have h : Real.smoothTransition =ᶠ[nhds t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx using Real.smoothTransition.one_of_one_le (le_of_lt hx)
    rw [h.deriv_eq, deriv_const]

theorem contDiff_timeCutoff : ContDiff ℝ ∞ timeCutoff := by
  unfold timeCutoff
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff

theorem hasCompactSupport_timeCutoff : HasCompactSupport timeCutoff := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun s hs => ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hs
  unfold timeCutoff
  rcases hs with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
    simp

theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem hasDerivAt_timeCutoff (s : ℝ) : HasDerivAt timeCutoff (timeCutoffDeriv s) s := by
  have hd : Differentiable ℝ Real.smoothTransition := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun t => Real.smoothTransition (t + 1)) (deriv Real.smoothTransition (s + 1)) s :=
    (hd (s + 1)).hasDerivAt.comp_add_const s 1
  have h2 := (hd s).hasDerivAt
  unfold timeCutoff timeCutoffDeriv
  exact h1.sub h2

theorem hasCompactSupport_deriv_shift (a : ℝ) : HasCompactSupport (fun s => deriv Real.smoothTransition (s + a)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1 - a) (b := 2 - a)) fun s hs => ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hs
  refine deriv_smoothTransition_eq_zero ?_
  rcases hs with hs | hs
  · left; linarith
  · right; linarith

theorem integral_timeCutoffDeriv_mul {F : ℝ → ℝ} (hF : Function.Periodic F 1) (hFi : LocallyIntegrable F volume) :
    ∫ s, timeCutoffDeriv s * F s = 0 := by
  have i1 : Integrable (fun s => deriv Real.smoothTransition (s + 1) * F s) volume := by
    simpa [smul_eq_mul] using hFi.integrable_smul_left_of_hasCompactSupport
      (continuous_deriv_smoothTransition.comp (continuous_id.add continuous_const)) (hasCompactSupport_deriv_shift 1)
  have i2 : Integrable (fun s => deriv Real.smoothTransition s * F s) volume := by
    simpa [smul_eq_mul] using hFi.integrable_smul_left_of_hasCompactSupport
      continuous_deriv_smoothTransition (by simpa using hasCompactSupport_deriv_shift 0)
  have e : (fun s => timeCutoffDeriv s * F s) =
      fun s => deriv Real.smoothTransition (s + 1) * F s - deriv Real.smoothTransition s * F s := by
    funext s; unfold timeCutoffDeriv; ring
  rw [e, integral_sub i1 i2]
  have e2 : (fun s => deriv Real.smoothTransition (s + 1) * F s) =
      fun s => (fun t => deriv Real.smoothTransition t * F t) (s + 1) := by
    funext s; simp only [hF s]
  rw [e2, integral_add_right_eq_self (fun t => deriv Real.smoothTransition t * F t) (1 : ℝ), sub_self]

theorem integral_timeCutoff_mul {F : ℝ → ℝ} (hF : Function.Periodic F 1) (hFi : LocallyIntegrable F volume) :
    ∫ s, timeCutoff s * F s = ∫ s in Set.Ioc (0 : ℝ) 1, F s := by
  have hc : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  have hcut : Continuous timeCutoff := contDiff_timeCutoff.continuous
  have hii : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    (hFi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hmul : ∀ {u : ℝ → ℝ}, Continuous u → ∀ a b : ℝ, IntervalIntegrable (fun s => u s * F s) volume a b :=
    fun hu a b => (hii a b).continuousOn_mul hu.continuousOn
  have h0 : ∫ s, timeCutoff s * F s = ∫ s in (-1 : ℝ)..1, timeCutoff s * F s := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
    unfold timeCutoff
    rcases hs with hs | hs
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith), Real.smoothTransition.zero_of_nonpos (by linarith)]
      simp
    · rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
      simp
  rw [h0, ← intervalIntegral.integral_add_adjacent_intervals (hmul hcut (-1) 0) (hmul hcut 0 1)]
  have e1 : ∫ s in (-1 : ℝ)..0, timeCutoff s * F s = ∫ s in (0 : ℝ)..1, Real.smoothTransition s * F s := by
    have : ∫ s in (-1 : ℝ)..0, timeCutoff s * F s =
        ∫ s in (-1 : ℝ)..0, (fun t => Real.smoothTransition t * F t) (s + 1) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hs
      simp only [timeCutoff, hF s]
      rw [Real.smoothTransition.zero_of_nonpos hs.2, sub_zero]
    rw [this]
    have h := intervalIntegral.integral_comp_add_right (a := (-1 : ℝ)) (b := 0)
      (fun t => Real.smoothTransition t * F t) (1 : ℝ)
    norm_num at h
    exact h
  have e2 : ∫ s in (0 : ℝ)..1, timeCutoff s * F s = ∫ s in (0 : ℝ)..1, (1 - Real.smoothTransition s) * F s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    simp only [timeCutoff]
    rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1])]
  have ha : IntervalIntegrable (fun s => Real.smoothTransition s * F s) volume 0 1 := hmul hc 0 1
  have hb : IntervalIntegrable (fun s => (1 - Real.smoothTransition s) * F s) volume 0 1 :=
    hmul (continuous_const.sub hc) 0 1
  rw [e1, e2, ← intervalIntegral.integral_add ha hb, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  ring

theorem exchange_weight (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ φ : ℝ) (k : Fin 3) {θ : Space → ℝ}
    (hθ : IsTestFunction θ) {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) {K : Set ℝ} (hK : IsCompact K)
    (ha0 : ∀ τ, τ ∉ K → a τ = 0) (hb0 : ∀ τ, τ ∉ K → b τ = 0) (w : Space → ℝ) (hw : Continuous w)
    (hw0 : ∀ y, y ∉ tsupport θ → w y = 0) :
    ∫ q : ℝ × Space, (a q.1 * θ q.2 + b q.1 * w q.2) * (velFamily F σ (q.1, φ) q.2) k =
      ∫ τ, (a τ * (∫ y, θ y • velFamily F σ (τ, φ) y) k + b τ * (∫ y, w y • velFamily F σ (τ, φ) y) k) := by
  have hθ0 : ∀ y, y ∉ tsupport θ → θ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hVl := locallyIntegrable_angleFamily hRot hFl σ φ
  have hVk : LocallyIntegrable (fun q : ℝ × Space => (velFamily F σ (q.1, φ) q.2) k) volume :=
    hVl.mono ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_aestronglyMeasurable hVl.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => PiLp.norm_apply_le _ k)
  have hWc : Continuous (fun q : ℝ × Space => a q.1 * θ q.2 + b q.1 * w q.2) :=
    ((ha.comp continuous_fst).mul (hθ.1.continuous.comp continuous_snd)).add
      ((hb.comp continuous_fst).mul (hw.comp continuous_snd))
  have hWs : HasCompactSupport (fun q : ℝ × Space => a q.1 * θ q.2 + b q.1 * w q.2) := by
    refine HasCompactSupport.intro (hK.prod hθ.2) fun q hq => ?_
    by_cases h1 : q.1 ∈ K
    · have h2 : q.2 ∉ tsupport θ := fun h2 => hq ⟨h1, h2⟩
      simp only [hθ0 _ h2, hw0 _ h2]; ring
    · simp only [ha0 _ h1, hb0 _ h1]; ring
  have hint : Integrable (fun q : ℝ × Space => (a q.1 * θ q.2 + b q.1 * w q.2) * (velFamily F σ (q.1, φ) q.2) k)
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    have := hVk.integrable_smul_left_of_hasCompactSupport hWc hWs
    rw [Measure.volume_eq_prod] at this
    simpa [smul_eq_mul] using this
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  have hae : ∀ᵐ τ, τ ∈ K → Integrable (fun y => velFamily F σ (τ, φ) y) (volume.restrict (tsupport θ)) := by
    have h1 : Integrable (fun q : ℝ × Space => velFamily F σ (q.1, φ) q.2)
        ((volume.restrict K).prod (volume.restrict (tsupport θ))) := by
      have := hVl.integrableOn_isCompact (hK.prod hθ.2)
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at this
      exact this
    exact (ae_restrict_iff' hK.measurableSet).1 h1.prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [hae] with τ hτ
  by_cases h1 : τ ∈ K
  · have hi := hτ h1
    have j1 : Integrable (fun y => θ y • velFamily F σ (τ, φ) y) volume :=
      (IntegrableOn.continuousOn_smul (g := fun y => velFamily F σ (τ, φ) y) hi hθ.1.continuous.continuousOn
        hθ.2).integrable_of_forall_notMem_eq_zero
        fun y hy => by rw [hθ0 y hy, zero_smul]
    have j2 : Integrable (fun y => w y • velFamily F σ (τ, φ) y) volume :=
      (IntegrableOn.continuousOn_smul (g := fun y => velFamily F σ (τ, φ) y) hi hw.continuousOn
        hθ.2).integrable_of_forall_notMem_eq_zero
        fun y hy => by rw [hw0 y hy, zero_smul]
    have c1 : (∫ y, θ y • velFamily F σ (τ, φ) y) k = ∫ y, θ y * (velFamily F σ (τ, φ) y) k := by
      simpa using ((EuclideanSpace.proj (𝕜 := ℝ) k).integral_comp_comm j1).symm
    have c2 : (∫ y, w y • velFamily F σ (τ, φ) y) k = ∫ y, w y * (velFamily F σ (τ, φ) y) k := by
      simpa using ((EuclideanSpace.proj (𝕜 := ℝ) k).integral_comp_comm j2).symm
    have k1 : Integrable (fun y => θ y * (velFamily F σ (τ, φ) y) k) volume := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) k).integrable_comp j1
    have k2 : Integrable (fun y => w y * (velFamily F σ (τ, φ) y) k) volume := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) k).integrable_comp j2
    rw [c1, c2, ← integral_const_mul, ← integral_const_mul, ← integral_add (k1.const_mul _) (k2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  · simp only [ha0 τ h1, hb0 τ h1]
    simp

theorem deriv_zero_off_tsupport {χ χ' : ℝ → ℝ} (hχ' : ∀ s, HasDerivAt χ (χ' s) s) {s : ℝ}
    (hs : s ∉ tsupport χ) : χ' s = 0 := by
  have h : χ =ᶠ[nhds s] fun _ => (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq).1 hs
  exact (hχ' s).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq h)

theorem time_weak_transport {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (σ φ : ℝ)
    {θ : Space → ℝ} (hθ : IsTestFunction θ) (k : Fin 3) {χ χ' : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) (hχ' : ∀ s, HasDerivAt χ (χ' s) s) :
    ∫ τ, (-(1 / P) * χ' τ * (∫ y, θ y • velFamily v σ (τ, φ) y) k
        + χ τ * (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • velFamily v σ (τ, φ) y) k) =
      ∫ τ, χ τ * (∫ y, θ y • velFamily g σ (τ, φ) y) k := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hvl, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  set R : Space ≃ₗᵢ[ℝ] Space := rotIso hRot φ with hRdef
  have hRa : ∀ y, R y = axialRot φ y := fun y => rotIso_apply hRot φ y
  have hRs : ∀ y, R.symm y = axialRot (-φ) y := fun y => rotIso_symm_apply hRot φ y
  set L : Space →L[ℝ] Space := (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space) with hL
  have hLa : ∀ y, L y = R.symm y := fun y => rfl
  set u : Space := R (unitVector k) with hu
  set Φ : ℝ → Space → Space := fun s x => (χ (s - σ) * θ (L x)) • u with hΦ
  have hθd : Differentiable ℝ θ := hθ.1.differentiable (by simp)
  have hΦc : ContDiff ℝ ∞ (fun z : ℝ × Space => Φ z.1 z.2) :=
    ((hχ.comp (contDiff_fst.sub contDiff_const)).mul (hθ.1.comp (L.contDiff.comp contDiff_snd))).smul
      contDiff_const
  have hχ0 : ∀ s, s ∉ tsupport χ → χ s = 0 := fun s hs => image_eq_zero_of_notMem_tsupport hs
  have hθ0 : ∀ y, y ∉ tsupport θ → θ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hΦs : HasCompactSupport (fun z : ℝ × Space => Φ z.1 z.2) := by
    refine HasCompactSupport.intro ((hχs.image (continuous_add_const σ)).prod (hθ.2.image R.continuous))
      fun z hz => ?_
    by_cases h1 : z.1 - σ ∈ tsupport χ
    · have h2 : L z.2 ∉ tsupport θ := by
        intro h2; apply hz
        exact ⟨⟨z.1 - σ, h1, by ring⟩, ⟨L z.2, h2, by rw [hLa]; exact R.apply_symm_apply z.2⟩⟩
      show (χ (z.1 - σ) * θ (L z.2)) • u = 0
      rw [hθ0 _ h2]; simp
    · show (χ (z.1 - σ) * θ (L z.2)) • u = 0
      rw [hχ0 _ h1]; simp
  have htr := hv.transport Φ ⟨hΦc, hΦs⟩
  have hder : ∀ s x, deriv (fun t => Φ t x) s = (χ' (s - σ) * θ (L x)) • u := by
    intro s x
    have : HasDerivAt (fun t => Φ t x) ((χ' (s - σ) * θ (L x)) • u) s :=
      (((hχ' (s - σ)).comp_sub_const s σ).mul_const (θ (L x))).smul_const u
    exact this.deriv
  have hfd : ∀ s x, fderiv ℝ (Φ s) x x = (χ (s - σ) * fderiv ℝ θ (L x) (L x)) • u := by
    intro s x
    have h1 : HasFDerivAt (fun x => θ (L x)) ((fderiv ℝ θ (L x)).comp L) x :=
      (hθd (L x)).hasFDerivAt.comp x L.hasFDerivAt
    have h2 := (h1.const_mul (χ (s - σ))).smul_const u
    have e : Φ s = fun x => (χ (s - σ) * θ (L x)) • u := rfl
    rw [e, h2.fderiv]
    simp
  have hL_R : ∀ y, L (R y) = y := fun y => R.symm_apply_apply y
  have hinner : ∀ x : Space, inner ℝ x u = (L x) k := by
    intro x
    rw [← R.symm.inner_map_map x u, hu, R.symm_apply_apply]
    simp [unitVector, EuclideanSpace.inner_single_right, hLa]
  set W : ℝ → Space → ℝ := fun τ y => -(1 / P) * χ' τ * θ y + χ τ * (-θ y - (1 / 2) * fderiv ℝ θ y y) with hW
  have hlhs : (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => Φ s z.2) z.1 - Φ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (Φ z.1) z.2 z.2)) = fun z => W (z.1 - σ) (L z.2) * (L (v z.1 z.2)) k := by
    funext z
    rw [hder, hfd]
    show inner ℝ (v z.1 z.2) (-(1 / P) • ((χ' (z.1 - σ) * θ (L z.2)) • u) - (χ (z.1 - σ) * θ (L z.2)) • u
      - (1 / 2 : ℝ) • ((χ (z.1 - σ) * fderiv ℝ θ (L z.2) (L z.2)) • u)) = _
    rw [smul_smul, smul_smul, ← sub_smul, ← sub_smul, real_inner_smul_right, hinner]
    simp only [hW]
    ring
  have hrhs : (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (Φ z.1 z.2)) =
      fun z => (χ (z.1 - σ) * θ (L z.2)) * (L (g z.1 z.2)) k := by
    funext z
    show inner ℝ (g z.1 z.2) ((χ (z.1 - σ) * θ (L z.2)) • u) = _
    rw [real_inner_smul_right, hinner]
  rw [hlhs, hrhs] at htr
  set e : ℝ × Space ≃ₜ ℝ × Space := (Homeomorph.addLeft σ).prodCongr R.toHomeomorph with he
  have he_apply : ∀ q : ℝ × Space, e q = (σ + q.1, R q.2) := fun q => by
    simp [he, Prod.map]
  have hmp : MeasurePreserving e volume volume := by
    have hm := (measurePreserving_add_left (volume : Measure ℝ) σ).prod R.measurePreserving
    rw [← Measure.volume_eq_prod] at hm
    have hf : (Prod.map (fun x : ℝ => σ + x) (R : Space → Space)) = (e : ℝ × Space → ℝ × Space) := by
      funext q; rw [he_apply]; simp [Prod.map]
    rw [← hf]; exact hm
  have cv : ∀ F : ℝ × Space → ℝ, ∫ z, F z = ∫ q, F (e q) := fun F =>
    (hmp.integral_comp e.measurableEmbedding F).symm
  rw [cv, cv (fun z => (χ (z.1 - σ) * θ (L z.2)) * (L (g z.1 z.2)) k)] at htr
  simp only [he_apply, add_sub_cancel_left, hL_R] at htr
  have hV : ∀ (F : ℝ → Space → Space) (τ : ℝ) (y : Space), velFamily F σ (τ, φ) y = L (F (σ + τ) (R y)) := by
    intro F τ y
    simp only [velFamily, hLa, hRs, hRa]
  simp only [← hV] at htr
  have hχd : χ' = deriv χ := funext fun s => (hχ' s).deriv.symm
  have hχ'c : Continuous χ' := by rw [hχd]; exact hχ.continuous_deriv (by simp)
  have lhsEq := exchange_weight hRot hvl σ φ k hθ (a := fun τ => -(1 / P) * χ' τ) (b := χ)
    (continuous_const.mul hχ'c) hχ.continuous hχs (fun τ hτ => by rw [deriv_zero_off_tsupport hχ' hτ, mul_zero])
    hχ0 _ (continuous_test_weight hθ) (fun y hy => test_weight_zero y hy)
  have rhsEq := exchange_weight hRot hgl σ φ k hθ (a := χ) (b := fun _ => 0)
    hχ.continuous continuous_const hχs hχ0 (fun _ _ => rfl) θ hθ.1.continuous hθ0
  rw [← lhsEq]
  simp only [zero_mul, add_zero] at rhsEq
  rw [← rhsEq]
  exact htr

theorem locallyIntegrable_continuous_mul {u : ℝ → ℝ} (hu : Continuous u) {F : ℝ → ℝ}
    (hF : LocallyIntegrable F volume) : LocallyIntegrable (fun s => u s * F s) volume :=
  (locallyIntegrable_iff).2 fun K hK => by
    simpa [smul_eq_mul] using (hF.integrableOn_isCompact hK).continuousOn_smul hu.continuousOn hK

theorem integrable_compact_mul {u : ℝ → ℝ} (hu : Continuous u) (hus : HasCompactSupport u) {F : ℝ → ℝ}
    (hF : LocallyIntegrable F volume) : Integrable (fun s => u s * F s) volume := by
  simpa [smul_eq_mul] using hF.integrable_smul_left_of_hasCompactSupport hu hus

theorem hasCompactSupport_test_weight {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    HasCompactSupport (fun y => -θ y - (1 / 2) * fderiv ℝ θ y y) :=
  HasCompactSupport.intro hθ.2 fun y hy => test_weight_zero y hy

theorem angle_transport {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (σ φ : ℝ)
    {θ : Space → ℝ} (hθ : IsTestFunction θ) (k : Fin 3) (c c' : ℝ → ℝ) (hcs : ContDiff ℝ ∞ c)
    (hc : ∀ τ, HasDerivAt c (c' τ) τ)
    (hc' : Continuous c') (hcp : Function.Periodic c 1) (hcp' : Function.Periodic c' 1) :
    ∫ τ in Set.Ioc (0 : ℝ) 1, c τ * (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • velFamily v σ (τ, φ) y) k =
      (1 / P) * (∫ τ in Set.Ioc (0 : ℝ) 1, c' τ * (∫ y, θ y • velFamily v σ (τ, φ) y) k)
        + ∫ τ in Set.Ioc (0 : ℝ) 1, c τ * (∫ y, θ y • velFamily g σ (τ, φ) y) k := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hvl, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  have hfam : ∀ {F : ℝ → Space → Space}, IsTimePeriodic F →
      ∀ τ y, velFamily F σ (τ + 1, φ) y = velFamily F σ (τ, φ) y := by
    intro F hF τ y
    simp only [velFamily]
    rw [← add_assoc, hF]
  set A : ℝ → ℝ := fun τ => (∫ y, θ y • velFamily v σ (τ, φ) y) k with hA
  set B : ℝ → ℝ := fun τ => (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • velFamily v σ (τ, φ) y) k with hB
  set C : ℝ → ℝ := fun τ => (∫ y, θ y • velFamily g σ (τ, φ) y) k with hC
  have pA : Function.Periodic A 1 := fun τ => by simp only [hA, hfam hv.periodic_velocity]
  have pB : Function.Periodic B 1 := fun τ => by simp only [hB, hfam hv.periodic_velocity]
  have pC : Function.Periodic C 1 := fun τ => by simp only [hC, hfam hv.periodic_derivative]
  have lA : LocallyIntegrable A volume := locallyIntegrable_pairing_time hRot hvl σ φ hθ.1.continuous hθ.2 k
  have lB : LocallyIntegrable B volume := locallyIntegrable_pairing_time hRot hvl σ φ
    (continuous_test_weight hθ) (hasCompactSupport_test_weight hθ) k
  have lC : LocallyIntegrable C volume := locallyIntegrable_pairing_time hRot hgl σ φ hθ.1.continuous hθ.2 k
  have hcc : Continuous c := hcs.continuous
  have hχ : ContDiff ℝ ∞ (fun s => timeCutoff s * c s) := contDiff_timeCutoff.mul hcs
  have hχs : HasCompactSupport (fun s => timeCutoff s * c s) := hasCompactSupport_timeCutoff.mul_right
  have hχ' : ∀ s, HasDerivAt (fun s => timeCutoff s * c s) (timeCutoffDeriv s * c s + timeCutoff s * c' s) s :=
    fun s => (hasDerivAt_timeCutoff s).mul (hc s)
  have h := time_weak_transport hv hP0 σ φ hθ k hχ hχs hχ'
  have hdc : Continuous timeCutoffDeriv :=
    (continuous_deriv_smoothTransition.comp (continuous_id.add continuous_const)).sub continuous_deriv_smoothTransition
  have hds : HasCompactSupport timeCutoffDeriv := by
    have h1 := hasCompactSupport_deriv_shift 1
    have h0 : HasCompactSupport (fun s => deriv Real.smoothTransition s) := by
      simpa using hasCompactSupport_deriv_shift 0
    exact h1.sub h0
  have hcut : Continuous timeCutoff := contDiff_timeCutoff.continuous
  have i1 : Integrable (fun τ => timeCutoffDeriv τ * (c τ * A τ)) volume :=
    integrable_compact_mul hdc hds (locallyIntegrable_continuous_mul hcc lA)
  have i2 : Integrable (fun τ => timeCutoff τ * (c' τ * A τ)) volume :=
    integrable_compact_mul hcut hasCompactSupport_timeCutoff (locallyIntegrable_continuous_mul hc' lA)
  have i3 : Integrable (fun τ => timeCutoff τ * (c τ * B τ)) volume :=
    integrable_compact_mul hcut hasCompactSupport_timeCutoff (locallyIntegrable_continuous_mul hcc lB)
  have e : (fun τ => -(1 / P) * (timeCutoffDeriv τ * c τ + timeCutoff τ * c' τ) * A τ
      + timeCutoff τ * c τ * B τ) = fun τ => (-(1 / P) * (timeCutoffDeriv τ * (c τ * A τ))
        + -(1 / P) * (timeCutoff τ * (c' τ * A τ))) + timeCutoff τ * (c τ * B τ) := by
    funext τ; ring
  have e2 : (fun τ => timeCutoff τ * c τ * C τ) = fun τ => timeCutoff τ * (c τ * C τ) := by
    funext τ; ring
  have h' : ∫ τ, (-(1 / P) * (timeCutoffDeriv τ * c τ + timeCutoff τ * c' τ) * A τ
      + timeCutoff τ * c τ * B τ) = ∫ τ, timeCutoff τ * c τ * C τ := h
  have j1 : Integrable (fun τ => -(1 / P) * (timeCutoffDeriv τ * (c τ * A τ))) volume := i1.const_mul _
  have j2 : Integrable (fun τ => -(1 / P) * (timeCutoff τ * (c' τ * A τ))) volume := i2.const_mul _
  have j12 : Integrable (fun τ => -(1 / P) * (timeCutoffDeriv τ * (c τ * A τ))
      + -(1 / P) * (timeCutoff τ * (c' τ * A τ))) volume := j1.add j2
  rw [e, e2, integral_add j12 i3, integral_add j1 j2,
    integral_const_mul, integral_const_mul] at h'
  have q1 : ∫ s, timeCutoffDeriv s * (c s * A s) = 0 :=
    integral_timeCutoffDeriv_mul (F := fun τ => c τ * A τ) (hcp.mul pA) (locallyIntegrable_continuous_mul hcc lA)
  have q2 : ∫ s, timeCutoff s * (c' s * A s) = ∫ s in Set.Ioc (0 : ℝ) 1, c' s * A s :=
    integral_timeCutoff_mul (F := fun τ => c' τ * A τ) (hcp'.mul pA) (locallyIntegrable_continuous_mul hc' lA)
  have q3 : ∫ s, timeCutoff s * (c s * B s) = ∫ s in Set.Ioc (0 : ℝ) 1, c s * B s :=
    integral_timeCutoff_mul (F := fun τ => c τ * B τ) (hcp.mul pB) (locallyIntegrable_continuous_mul hcc lB)
  have q4 : ∫ s, timeCutoff s * (c s * C s) = ∫ s in Set.Ioc (0 : ℝ) 1, c s * C s :=
    integral_timeCutoff_mul (F := fun τ => c τ * C τ) (hcp.mul pC) (locallyIntegrable_continuous_mul hcc lC)
  rw [q1, q2, q3, q4] at h'
  show ∫ τ in Set.Ioc (0 : ℝ) 1, c τ * B τ = (1 / P) * (∫ τ in Set.Ioc (0 : ℝ) 1, c' τ * A τ)
    + ∫ τ in Set.Ioc (0 : ℝ) 1, c τ * C τ
  linarith

theorem hasDerivAt_weightRe (ι : ℤ × ℤ) (φ τ : ℝ) :
    HasDerivAt (fun t => weightRe ι (t, φ)) (2 * Real.pi * ι.1 * weightIm ι (τ, φ)) τ := by
  have h := ((((hasDerivAt_id τ).const_mul (2 * Real.pi * ι.1)).add_const (ι.2 * φ)).cos).div_const
    (2 * Real.pi)
  have e : (fun t => weightRe ι (t, φ)) =
      fun x => Real.cos (2 * Real.pi * ι.1 * id x + ι.2 * φ) / (2 * Real.pi) := by
    funext t; simp [weightRe, modePhase]
  rw [e]
  refine h.congr_deriv ?_
  simp [weightIm, modePhase]
  ring

theorem hasDerivAt_weightIm (ι : ℤ × ℤ) (φ τ : ℝ) :
    HasDerivAt (fun t => weightIm ι (t, φ)) (-(2 * Real.pi * ι.1) * weightRe ι (τ, φ)) τ := by
  have h := (((((hasDerivAt_id τ).const_mul (2 * Real.pi * ι.1)).add_const (ι.2 * φ)).sin).neg).div_const
    (2 * Real.pi)
  simp only [Pi.neg_apply] at h
  have e : (fun t => weightIm ι (t, φ)) =
      fun x => -Real.sin (2 * Real.pi * ι.1 * id x + ι.2 * φ) / (2 * Real.pi) := by
    funext t; simp [weightIm, modePhase]
  rw [e]
  refine h.congr_deriv ?_
  simp [weightRe, modePhase]
  ring

theorem weightRe_periodic (ι : ℤ × ℤ) (φ : ℝ) : Function.Periodic (fun t => weightRe ι (t, φ)) 1 := by
  intro t
  have : 2 * Real.pi * ι.1 * (t + 1) + ι.2 * φ = (2 * Real.pi * ι.1 * t + ι.2 * φ) + (ι.1 : ℤ) * (2 * Real.pi) := by
    ring
  simp only [weightRe, modePhase]
  rw [this, Real.cos_add_int_mul_two_pi]

theorem weightIm_periodic (ι : ℤ × ℤ) (φ : ℝ) : Function.Periodic (fun t => weightIm ι (t, φ)) 1 := by
  intro t
  have : 2 * Real.pi * ι.1 * (t + 1) + ι.2 * φ = (2 * Real.pi * ι.1 * t + ι.2 * φ) + (ι.1 : ℤ) * (2 * Real.pi) := by
    ring
  simp only [weightIm, modePhase]
  rw [this, Real.sin_add_int_mul_two_pi]

theorem continuous_weightRe (ι : ℤ × ℤ) : Continuous (weightRe ι) := by
  unfold weightRe modePhase; fun_prop

theorem continuous_weightIm (ι : ℤ × ℤ) : Continuous (weightIm ι) := by
  unfold weightIm modePhase; fun_prop

theorem family_transport_of_angle {P : ℝ} {c d : ℝ × ℝ → ℝ} (κ : ℝ)
    (hcm : Measurable c) (hc1 : ∀ p, |c p| ≤ 1) (hdm : Measurable d) (hd1 : ∀ p, |d p| ≤ 1)
    {F1 F2 F3 : ℝ × ℝ → Space} (h1 : Integrable F1 angleMeasure) (h2 : Integrable F2 angleMeasure)
    (h3 : Integrable F3 angleMeasure)
    (hang : ∀ φ k, ∫ τ in Set.Ioc (0 : ℝ) 1, c (τ, φ) * F1 (τ, φ) k =
      (1 / P) * (∫ τ in Set.Ioc (0 : ℝ) 1, (κ * d (τ, φ)) * F2 (τ, φ) k)
        + ∫ τ in Set.Ioc (0 : ℝ) 1, c (τ, φ) * F3 (τ, φ) k) :
    ∫ p, c p • F1 p ∂angleMeasure = (κ / P) • (∫ p, d p • F2 p ∂angleMeasure) + ∫ p, c p • F3 p ∂angleMeasure := by
  have i1 := integrable_weight_smul hcm hc1 h1
  have i2 := integrable_weight_smul hdm hd1 h2
  have i3 := integrable_weight_smul hcm hc1 h3
  ext k
  rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, integral_coord i1, integral_coord i2, integral_coord i3]
  have j1 : Integrable (fun p => c p * F1 p k) angleMeasure := by
    simpa using integrable_coord i1 k
  have j2 : Integrable (fun p => d p * F2 p k) angleMeasure := by
    simpa using integrable_coord i2 k
  have j3 : Integrable (fun p => c p * F3 p k) angleMeasure := by
    simpa using integrable_coord i3 k
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [integral_prod_symm _ j1, integral_prod_symm _ j2, integral_prod_symm _ j3]
  have e : ∀ φ, ∫ τ in Set.Ioc (0 : ℝ) 1, c (τ, φ) * F1 (τ, φ) k =
      (κ / P) * (∫ τ in Set.Ioc (0 : ℝ) 1, d (τ, φ) * F2 (τ, φ) k)
        + ∫ τ in Set.Ioc (0 : ℝ) 1, c (τ, φ) * F3 (τ, φ) k := fun φ => by
    rw [hang φ k]
    simp_rw [mul_assoc κ]
    rw [integral_const_mul]
    ring
  simp_rw [e]
  have k2 : Integrable (fun φ => ∫ τ in Set.Ioc (0 : ℝ) 1, d (τ, φ) * F2 (τ, φ) k)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := j2.integral_prod_right
  have k3 : Integrable (fun φ => ∫ τ in Set.Ioc (0 : ℝ) 1, c (τ, φ) * F3 (τ, φ) k)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := j3.integral_prod_right
  rw [integral_add (k2.const_mul _) k3, integral_const_mul]

theorem family_transport {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (ι : ℤ × ℤ) (σ : ℝ)
    {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    (∫ p, weightRe ι p • (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • velFamily v σ p y) ∂angleMeasure =
      (2 * Real.pi * ι.1 / P) • (∫ p, weightIm ι p • (∫ y, θ y • velFamily v σ p y) ∂angleMeasure)
        + ∫ p, weightRe ι p • (∫ y, θ y • velFamily g σ p y) ∂angleMeasure) ∧
    (∫ p, weightIm ι p • (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • velFamily v σ p y) ∂angleMeasure =
      -(2 * Real.pi * ι.1 / P) • (∫ p, weightRe ι p • (∫ y, θ y • velFamily v σ p y) ∂angleMeasure)
        + ∫ p, weightIm ι p • (∫ y, θ y • velFamily g σ p y) ∂angleMeasure) := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hvl, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  have hθ0 : ∀ y, y ∉ tsupport θ → θ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have i1 := integrable_pairing_family hRot hv.measurable_velocity hvl σ hθ _ (continuous_test_weight hθ)
    (fun y hy => test_weight_zero y hy)
  have i2 := integrable_pairing_family hRot hv.measurable_velocity hvl σ hθ θ hθ.1.continuous hθ0
  have i3 := integrable_pairing_family hRot hv.measurable_derivative hgl σ hθ θ hθ.1.continuous hθ0
  constructor
  · have h := family_transport_of_angle (P := P) (2 * Real.pi * ι.1) (measurable_weightRe ι) (abs_weightRe_le ι)
      (measurable_weightIm ι) (abs_weightIm_le ι) i1 i2 i3 fun φ k => by
        have := angle_transport hv hP0 σ φ hθ k (fun t => weightRe ι (t, φ))
          (fun t => 2 * Real.pi * ι.1 * weightIm ι (t, φ)) (by unfold weightRe modePhase; fun_prop)
          (hasDerivAt_weightRe ι φ)
          (continuous_const.mul ((continuous_weightIm ι).comp (continuous_id.prodMk continuous_const)))
          (weightRe_periodic ι φ) (fun t => by simp only [weightIm_periodic ι φ t])
        exact this
    rw [h, mul_div_assoc]
  · have h := family_transport_of_angle (P := P) (-(2 * Real.pi * ι.1)) (measurable_weightIm ι) (abs_weightIm_le ι)
      (measurable_weightRe ι) (abs_weightRe_le ι) i1 i2 i3 fun φ k => by
        have := angle_transport hv hP0 σ φ hθ k (fun t => weightIm ι (t, φ))
          (fun t => -(2 * Real.pi * ι.1) * weightRe ι (t, φ)) (by unfold weightIm modePhase; fun_prop)
          (hasDerivAt_weightIm ι φ)
          (continuous_const.mul ((continuous_weightRe ι).comp (continuous_id.prodMk continuous_const)))
          (weightIm_periodic ι φ) (fun t => by simp only [weightRe_periodic ι φ t])
        exact this
    rw [h, neg_div]

theorem core_pairings {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (ι : ℤ × ℤ) (σ : ℝ)
    {θ : Space → ℝ} (hθ : IsTestFunction θ) :
    (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • reVec (modeVel ι v σ y) =
      (2 * Real.pi * ι.1 / P) • (∫ y, θ y • imVec (modeVel ι v σ y)) + ∫ y, θ y • reVec (modeVel ι g σ y)) ∧
    (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • imVec (modeVel ι v σ y) =
      -(2 * Real.pi * ι.1 / P) • (∫ y, θ y • reVec (modeVel ι v σ y)) + ∫ y, θ y • imVec (modeVel ι g σ y)) := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hvl, -, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  have hv0 := ae_modeVel_average hRot hv.measurable_velocity hvl ι σ
  have hg0 := ae_modeVel_average hRot hv.measurable_derivative hgl ι σ
  have hθ0 : ∀ y, y ∉ tsupport θ → θ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hft := family_transport hv hP0 ι σ hθ
  have pr := fun {c : ℝ × ℝ → ℝ} (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {X : Space → Space}
      (hX : ∀ᵐ y, X y = ∫ p, c p • velFamily v σ p y ∂angleMeasure) =>
    average_pairing hRot hv.measurable_velocity hvl σ hcm hc hθ _ (continuous_test_weight hθ)
      (fun y hy => test_weight_zero y hy) hX
  have pv := fun {c : ℝ × ℝ → ℝ} (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {X : Space → Space}
      (hX : ∀ᵐ y, X y = ∫ p, c p • velFamily v σ p y ∂angleMeasure) =>
    average_pairing hRot hv.measurable_velocity hvl σ hcm hc hθ θ hθ.1.continuous hθ0 hX
  have pg := fun {c : ℝ × ℝ → ℝ} (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {X : Space → Space}
      (hX : ∀ᵐ y, X y = ∫ p, c p • velFamily g σ p y ∂angleMeasure) =>
    average_pairing hRot hv.measurable_derivative hgl σ hcm hc hθ θ hθ.1.continuous hθ0 hX
  constructor
  · rw [pr (measurable_weightRe ι) (abs_weightRe_le ι) hv0.1, pv (measurable_weightIm ι) (abs_weightIm_le ι) hv0.2,
      pg (measurable_weightRe ι) (abs_weightRe_le ι) hg0.1]
    exact hft.1
  · rw [pr (measurable_weightIm ι) (abs_weightIm_le ι) hv0.2, pv (measurable_weightRe ι) (abs_weightRe_le ι) hv0.1,
      pg (measurable_weightIm ι) (abs_weightIm_le ι) hg0.2]
    exact hft.2

theorem reVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  simp [reVec, unitVector, Pi.single_apply]

theorem imVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  simp [imVec, unitVector, Pi.single_apply]

theorem reMat_apply (m : Fin 3 × Fin 3 → ℂ) (u : Space) (i : Fin 3) :
    reMat m u i = ∑ j : Fin 3, (m (i, j)).re * u j := by
  simp [reMat, unitVector, EuclideanSpace.inner_single_left, Pi.single_apply, mul_comm]

theorem imMat_apply (m : Fin 3 × Fin 3 → ℂ) (u : Space) (i : Fin 3) :
    imMat m u i = ∑ j : Fin 3, (m (i, j)).im * u j := by
  simp [imMat, unitVector, EuclideanSpace.inner_single_left, Pi.single_apply, mul_comm]

def transportDefect (P : ℝ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (σ : ℝ) (y : Space) : Fin 3 → ℂ := fun i =>
  (((2 * Real.pi * ι.1 / P : ℝ) : ℂ) * Complex.I + 1 / 2) * modeVel ι v σ y i
    + (1 / 2 : ℂ) * ∑ j : Fin 3, modeGrad ι G σ y (i, j) * ((y j : ℝ) : ℂ) - modeVel ι g σ y i

theorem locallyIntegrable_apply_self {A : Space → (Space →L[ℝ] Space)} (hA : LocallyIntegrable A volume) :
    LocallyIntegrable (fun y => A y y) volume := by
  have e : (fun y => A y y) = fun y => ∑ j : Fin 3, y j • A y (unitVector j) := by
    funext y
    have hy := congrArg (A y) (vec_eq_sum y)
    simp only [map_sum, map_smul] at hy
    exact hy
  rw [e]
  refine locallyIntegrable_finsetSum _ fun j _ => ?_
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  exact ((Breakdown.Coercive.Internal.PerturbationFacts.apply_locallyIntegrable hA j).integrableOn_isCompact
    hK).continuousOn_smul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousOn) hK

theorem reVec_transportDefect (P : ℝ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (g : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    reVec (transportDefect P ι v G g σ y) = (1 / 2 : ℝ) • reVec (modeVel ι v σ y)
      - (2 * Real.pi * ι.1 / P) • imVec (modeVel ι v σ y) + (1 / 2 : ℝ) • reMat (modeGrad ι G σ y) y
      - reVec (modeVel ι g σ y) := by
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, reVec_apply, imVec_apply,
    reMat_apply, transportDefect]
  simp [Complex.mul_re, Complex.re_sum, Finset.mul_sum]

theorem imVec_transportDefect (P : ℝ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (g : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    imVec (transportDefect P ι v G g σ y) = (1 / 2 : ℝ) • imVec (modeVel ι v σ y)
      + (2 * Real.pi * ι.1 / P) • reVec (modeVel ι v σ y) + (1 / 2 : ℝ) • imMat (modeGrad ι G σ y) y
      - imVec (modeVel ι g σ y) := by
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, reVec_apply, imVec_apply,
    imMat_apply, transportDefect]
  simp [Complex.mul_im, Complex.im_sum, Finset.mul_sum]

theorem split_pairing {θ : Space → ℝ} (hθ : IsTestFunction θ) {X : Space → Space}
    (hX : LocallyIntegrable X volume) :
    (∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • X y) =
        -(∫ y, θ y • X y) - (1 / 2 : ℝ) • ∫ y, fderiv ℝ θ y y • X y ∧
      (∫ y, (3 * θ y + fderiv ℝ θ y y) • X y) = (3 : ℝ) • (∫ y, θ y • X y) + ∫ y, fderiv ℝ θ y y • X y := by
  have hdc : Continuous (fun y => fderiv ℝ θ y y) :=
    (hθ.1.continuous_fderiv (by simp)).clm_apply continuous_id
  have hds : HasCompactSupport (fun y => fderiv ℝ θ y y) := by
    refine (hθ.2.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
    simp only [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    rw [h0]
    rfl
  have i1 : Integrable (fun y => θ y • X y) volume :=
    hX.integrable_smul_left_of_hasCompactSupport hθ.1.continuous hθ.2
  have i2 : Integrable (fun y => fderiv ℝ θ y y • X y) volume :=
    hX.integrable_smul_left_of_hasCompactSupport hdc hds
  constructor
  · have e : (fun y => (-θ y - (1 / 2) * fderiv ℝ θ y y) • X y) =
        fun y => -(θ y • X y) - (1 / 2 : ℝ) • (fderiv ℝ θ y y • X y) := by
      funext y; rw [sub_smul, neg_smul, mul_smul]
    have i1n : Integrable (fun y => -(θ y • X y)) volume := i1.neg
    have i2s : Integrable (fun y => (1 / 2 : ℝ) • (fderiv ℝ θ y y • X y)) volume := i2.smul (1 / 2 : ℝ)
    rw [e, integral_sub i1n i2s, integral_neg, integral_smul]
  · have e : (fun y => (3 * θ y + fderiv ℝ θ y y) • X y) =
        fun y => (3 : ℝ) • (θ y • X y) + fderiv ℝ θ y y • X y := by
      funext y; rw [add_smul, mul_smul]
    have i1s : Integrable (fun y => (3 : ℝ) • (θ y • X y)) volume := i1.smul (3 : ℝ)
    rw [e, integral_add i1s i2, integral_smul]

theorem locallyIntegrable_modeVel (hRot : AxialRotationHolds) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (ι : ℤ × ℤ) (σ : ℝ) :
    LocallyIntegrable (fun y => reVec (modeVel ι F σ y)) volume ∧
      LocallyIntegrable (fun y => imVec (modeVel ι F σ y)) volume := by
  obtain ⟨h1, h2⟩ := ae_modeVel_average hRot hFm hFl ι σ
  refine ⟨?_, ?_⟩
  · refine LocallyIntegrable.congr ?_ (h1.mono fun y hy => hy.symm)
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    exact (integrable_weight (weightRe ι) (measurable_weightRe ι) (abs_weightRe_le ι)
      (integrable_family hRot hFm hFl σ hK)).integral_prod_left
  · refine LocallyIntegrable.congr ?_ (h2.mono fun y hy => hy.symm)
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    exact (integrable_weight (weightIm ι) (measurable_weightIm ι) (abs_weightIm_le ι)
      (integrable_family hRot hFm hFl σ hK)).integral_prod_left

theorem integrable_test_smul {θ : Space → ℝ} (hθ : IsTestFunction θ) {X : Space → Space}
    (hX : LocallyIntegrable X volume) : Integrable (fun y => θ y • X y) volume :=
  hX.integrable_smul_left_of_hasCompactSupport hθ.1.continuous hθ.2

theorem defect_pairing_zero {θ : Space → ℝ} (hθ : IsTestFunction θ) (k : ℝ) {a b m r : Space → Space}
    (ha : LocallyIntegrable a volume) (hb : LocallyIntegrable b volume) (hm : LocallyIntegrable m volume)
    (hr : LocallyIntegrable r volume)
    (hM : ∫ y, θ y • m y = -∫ y, (3 * θ y + fderiv ℝ θ y y) • a y)
    (hC : ∫ y, (-θ y - (1 / 2) * fderiv ℝ θ y y) • a y = k • (∫ y, θ y • b y) + ∫ y, θ y • r y) :
    ∫ y, θ y • ((1 / 2 : ℝ) • a y - k • b y + (1 / 2 : ℝ) • m y - r y) = 0 := by
  have I1 : Integrable (fun y => (1 / 2 : ℝ) • (θ y • a y)) volume := (integrable_test_smul hθ ha).smul (1 / 2 : ℝ)
  have I2 : Integrable (fun y => k • (θ y • b y)) volume := (integrable_test_smul hθ hb).smul k
  have I3 : Integrable (fun y => (1 / 2 : ℝ) • (θ y • m y)) volume := (integrable_test_smul hθ hm).smul (1 / 2 : ℝ)
  have I4 : Integrable (fun y => θ y • r y) volume := integrable_test_smul hθ hr
  have e : (fun y => θ y • ((1 / 2 : ℝ) • a y - k • b y + (1 / 2 : ℝ) • m y - r y)) =
      fun y => ((1 / 2 : ℝ) • (θ y • a y) - k • (θ y • b y) + (1 / 2 : ℝ) • (θ y • m y)) - θ y • r y := by
    funext y
    simp only [smul_sub, smul_add, smul_comm (θ y)]
  have I12 : Integrable (fun y => (1 / 2 : ℝ) • (θ y • a y) - k • (θ y • b y)) volume := I1.sub I2
  have I123 : Integrable (fun y => (1 / 2 : ℝ) • (θ y • a y) - k • (θ y • b y) + (1 / 2 : ℝ) • (θ y • m y))
      volume := I12.add I3
  rw [e, integral_sub I123 I4, integral_add I12 I3, integral_sub I1 I2,
    integral_smul, integral_smul, integral_smul, hM, (split_pairing hθ ha).2]
  rw [(split_pairing hθ ha).1] at hC
  have hr' := eq_sub_of_add_eq' hC.symm
  rw [hr']
  module

theorem ae_transportDefect {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (ι : ℤ × ℤ) (σ : ℝ) :
    ∀ᵐ y, transportDefect P ι v G g σ y = 0 := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hvl, hGl, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hgl := derivative_locallyIntegrable hv
  obtain ⟨hwr, hwi⟩ := mode_weakGradient hRot hv hvl hGl ι σ
  have hgL := locallyIntegrable_modeVel hRot hv.measurable_derivative hgl ι σ
  have hre : ∀ᵐ y, reVec (transportDefect P ι v G g σ y) = 0 := by
    have e0 : (fun y => reVec (transportDefect P ι v G g σ y)) = fun y =>
        (1 / 2 : ℝ) • reVec (modeVel ι v σ y) - (2 * Real.pi * ι.1 / P) • imVec (modeVel ι v σ y)
          + (1 / 2 : ℝ) • reMat (modeGrad ι G σ y) y - reVec (modeVel ι g σ y) :=
      funext fun y => reVec_transportDefect P ι v G g σ y
    have hm := locallyIntegrable_apply_self hwr.2.1
    have hf : LocallyIntegrable (fun y => reVec (transportDefect P ι v G g σ y)) volume := by
      rw [e0]
      exact (((hwr.1.smul (1 / 2 : ℝ)).sub (hwi.1.smul (2 * Real.pi * ι.1 / P))).add
        (hm.smul (1 / 2 : ℝ))).sub hgL.1
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf fun θ h1 h2 => ?_
    have hθ : IsTestFunction θ := ⟨h1, h2⟩
    simp only [reVec_transportDefect]
    exact defect_pairing_zero hθ _ hwr.1 hwi.1 hm hgL.1 (weak_radial hwr hθ)
      (core_pairings hv hP0 ι σ hθ).1
  have him : ∀ᵐ y, imVec (transportDefect P ι v G g σ y) = 0 := by
    have e1 : ∀ y, imVec (transportDefect P ι v G g σ y) =
        (1 / 2 : ℝ) • imVec (modeVel ι v σ y) - (-(2 * Real.pi * ι.1 / P)) • reVec (modeVel ι v σ y)
          + (1 / 2 : ℝ) • imMat (modeGrad ι G σ y) y - imVec (modeVel ι g σ y) := by
      intro y
      rw [imVec_transportDefect, neg_smul, sub_neg_eq_add]
    have e0 := funext e1
    have hm := locallyIntegrable_apply_self hwi.2.1
    have hf : LocallyIntegrable (fun y => imVec (transportDefect P ι v G g σ y)) volume := by
      rw [e0]
      exact (((hwi.1.smul (1 / 2 : ℝ)).sub (hwr.1.smul (-(2 * Real.pi * ι.1 / P)))).add
        (hm.smul (1 / 2 : ℝ))).sub hgL.2
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf fun θ h1 h2 => ?_
    have hθ : IsTestFunction θ := ⟨h1, h2⟩
    simp only [e1]
    exact defect_pairing_zero hθ _ hwi.1 hwr.1 hm hgL.2 (weak_radial hwi hθ)
      (core_pairings hv hP0 ι σ hθ).2
  filter_upwards [hre, him] with y h1 h2
  funext i
  have a := congrArg (fun u : Space => u i) h1
  have b := congrArg (fun u : Space => u i) h2
  simp only [reVec_apply, imVec_apply, PiLp.zero_apply] at a b
  exact Complex.ext a b

theorem modeAverage_shift {β : Type*} (ι : ℤ × ℤ) (F : ℝ → ℝ → β → ℝ) (hF : ∀ t φ b, F (t + 1) φ b = F t φ b)
    (σ : ℝ) (b : β) :
    modeAverage ι (fun τ φ b => F (σ + τ) φ b) b =
      Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * modeAverage ι (fun τ φ b => F τ φ b) b := by
  set K : ℝ → ℂ := fun t => ∫ φ in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(((ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F t φ b : ℝ) : ℂ) with hK
  set E : ℝ → ℂ := fun t => Complex.exp (-(((2 * Real.pi * ι.1 * t : ℝ) : ℂ) * Complex.I)) with hE
  have hsplit : ∀ t s, (∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * t + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F s φ b : ℝ) : ℂ)) =
        E t * K s := by
    intro t s
    rw [hK, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [hE]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hKp : ∀ t, K (t + 1) = K t := fun t => by simp only [hK, hF]
  have hEp : ∀ t, E (t + 1) = E t := by
    intro t
    simp only [hE]
    have : (-(((2 * Real.pi * ι.1 * (t + 1) : ℝ) : ℂ) * Complex.I)) =
        (-(((2 * Real.pi * ι.1 * t : ℝ) : ℂ) * Complex.I)) + ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hEs : ∀ t, E (t - σ) = Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * E t := by
    intro t
    simp only [hE]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold modeAverage
  simp_rw [hsplit]
  have hper : Function.Periodic (fun t => E t * K t) 1 := fun t => by simp only [hEp, hKp]
  have h1 : (∫ τ in (0 : ℝ)..1, E τ * K (σ + τ)) = ∫ t in σ..σ + 1, E (t - σ) * K t := by
    have := intervalIntegral.integral_comp_add_left (fun t => E (t - σ) * K t) σ (a := 0) (b := 1)
    simp only [add_sub_cancel_left, add_zero] at this
    exact this
  rw [h1]
  simp_rw [hEs, mul_assoc]
  rw [intervalIntegral.integral_const_mul, hper.intervalIntegral_add_eq σ 0, zero_add]
  ring

theorem modeVel_shift (ι : ℤ × ℤ) {v : ℝ → Space → Space} (hv : IsTimePeriodic v) (σ : ℝ) (y : Space) :
    modeVel ι v σ y = fun i =>
      Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * modeVel ι v 0 y i := by
  funext i
  have h := modeAverage_shift ι (fun t φ i => axialRot (-φ) (v t (axialRot φ y)) i)
    (fun t φ b => by simp only [hv t]) σ i
  unfold modeVel
  simpa only [zero_add] using h

theorem modeGrad_shift (ι : ℤ × ℤ) {G : ℝ → Space → (Space →L[ℝ] Space)} (hG : IsTimePeriodic G) (σ : ℝ)
    (y : Space) :
    modeGrad ι G σ y = fun ij =>
      Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * modeGrad ι G 0 y ij := by
  funext ij
  have h := modeAverage_shift ι
    (fun t φ ij => axialRot (-φ) (G t (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)
    (fun t φ b => by simp only [hG t]) σ ij
  unfold modeGrad
  simpa only [zero_add] using h

theorem cnormSq_smul (c : ℂ) (x : Fin 3 → ℂ) : cnormSq (fun i => c * x i) = ‖c‖ ^ 2 * cnormSq x := by
  unfold cnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow]

theorem norm_sq_transport_factor (a : ℝ) : ‖((a : ℝ) : ℂ) * Complex.I + 1 / 2‖ ^ 2 = a ^ 2 + 1 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

end Internal

end FrequencySeminorm

end Coercive

end Breakdown
