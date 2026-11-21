import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal.TestModes

open Internal.ModeRotation ModeDerivative.Internal

def modeTestIntegrand (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space)
    (p : ℝ × ℝ) : ℂ :=
  expFactor ι p.1 p.2 * ((axialRot (-p.2) (ψ (σ + p.1) (axialRot p.2 x)) l : ℝ) : ℂ)

def modeTestIntegrandDeriv (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space)
    (p : ℝ × ℝ) : Space →L[ℝ] ℂ :=
  expFactor ι p.1 p.2 • (Complex.ofRealCLM.comp ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).comp
    (rotConj axialRotationHolds_proof p.2 (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)))))

theorem boxMeasure_eq_restrict :
    boxMeasure = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  rw [boxMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]

theorem integrable_box_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) : Integrable f boxMeasure := by
  rw [boxMeasure_eq_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem ae_box_mem : ∀ᵐ p ∂boxMeasure, p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
  rw [boxMeasure_eq_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

theorem contDiff_testSlice {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (s : ℝ) :
    ContDiff ℝ ∞ (ψ s) :=
  hψ.1.comp (contDiff_const.prodMk contDiff_id)

theorem continuous_testSlice_fderiv {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (ψ z.1) z.2) :=
  (ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => ψ z.1 y) (g := fun z => z.2)
    (hψ.1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (n := 0) (by simp)).continuous

theorem testSlice_fderiv_bound {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (σ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc σ (σ + 1), ∀ y, ‖fderiv ℝ (ψ s) y‖ ≤ B := by
  obtain ⟨R, hR⟩ := hψ.2.2.1
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    (continuous_testSlice_fderiv hψ).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs y => ?_⟩
  by_cases hy : ‖y‖ ≤ R
  · exact (hC (s, y) ⟨hs, by rw [Metric.mem_closedBall, dist_zero_right]; exact hy⟩).trans (le_max_left _ _)
  · have hy' : R < ‖y‖ := lt_of_not_ge hy
    have h : ψ s =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hy')
        fun x hx => hR s x hx
    rw [h.fderiv_eq, fderiv_const_apply, norm_zero]
    exact le_max_right _ _

theorem hasFDerivAt_modeTestIntegrand {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ)
    (σ : ℝ) (l : Fin 3) (x : Space) (p : ℝ × ℝ) :
    HasFDerivAt (fun x => modeTestIntegrand ψ ι σ l x p) (modeTestIntegrandDeriv ψ ι σ l x p) x := by
  have hRot := axialRotationHolds_proof
  have e1 : (fun x => axialRot p.2 x) = ⇑((rotIso hRot p.2 : Space ≃ₗᵢ[ℝ] Space).toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext x
    exact (rotIso_apply hRot p.2 x).symm
  have h1 : HasFDerivAt (fun x => axialRot p.2 x)
      ((rotIso hRot p.2).toContinuousLinearEquiv : Space →L[ℝ] Space) x := by
    rw [e1]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 : HasFDerivAt (ψ (σ + p.1)) (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) (axialRot p.2 x) :=
    ((contDiff_testSlice hψ (σ + p.1)).differentiable (by simp) _).hasFDerivAt
  have e3 : (fun w : Space => axialRot (-p.2) w) = ⇑((rotIso hRot p.2).symm.toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext w
    exact (rotIso_symm_apply hRot p.2 w).symm
  have h3 : ∀ w, HasFDerivAt (fun w : Space => axialRot (-p.2) w)
      ((rotIso hRot p.2).symm.toContinuousLinearEquiv : Space →L[ℝ] Space) w := by
    intro w
    rw [e3]
    exact ContinuousLinearMap.hasFDerivAt _
  have h4 := (h3 _).comp x (h2.comp x h1)
  have h5 := ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).hasFDerivAt).comp x h4
  have h6 := (Complex.ofRealCLM.hasFDerivAt).comp x h5
  have h7 := h6.const_mul (expFactor ι p.1 p.2)
  refine HasFDerivAt.congr_of_eventuallyEq (h7.congr_fderiv ?_) (Filter.Eventually.of_forall fun y => ?_)
  · refine ContinuousLinearMap.ext fun u => ?_
    simp [modeTestIntegrandDeriv, rotConj_apply, rotIso_apply, rotIso_symm_apply]
  · simp [modeTestIntegrand]

theorem continuous_modeTestIntegrandDeriv {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrandDeriv ψ ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) :=
    (continuous_testSlice_fderiv hψ).comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ =>
      rotConj axialRotationHolds_proof p.2 (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x))) :=
    Continuous.comp (g := fun q : ℝ × (Space →L[ℝ] Space) => rotConj axialRotationHolds_proof q.1 q.2)
      (f := fun p : ℝ × ℝ => (p.2, fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)))
      (continuous_rotConj axialRotationHolds_proof) (continuous_snd.prodMk hA)
  refine continuous_clm_apply.2 fun u => ?_
  have e : (fun p => modeTestIntegrandDeriv ψ ι σ l x p u) = fun p => expFactor ι p.1 p.2 *
      ((rotConj axialRotationHolds_proof p.2 (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) u l : ℝ) : ℂ) := by
    funext p
    simp [modeTestIntegrandDeriv]
  rw [e]
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp (hB.clm_apply continuous_const)))

theorem continuous_modeTestIntegrand {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrand ψ ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => ψ (σ + p.1) (axialRot p.2 x)) :=
    hψ.1.continuous.comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (ψ (σ + p.1) (axialRot p.2 x))) :=
    continuous_axialRot_comp continuous_snd.neg hA
  unfold modeTestIntegrand
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp hB))

theorem norm_modeTestIntegrandDeriv_le {ψ : ℝ → Space → Space} (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3)
    (x : Space) (p : ℝ × ℝ) :
    ‖modeTestIntegrandDeriv ψ ι σ l x p‖ ≤ ‖fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  unfold modeTestIntegrandDeriv
  rw [smul_apply, norm_smul, norm_expFactor, one_mul]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
  calc ‖(EuclideanSpace.proj l : Space →L[ℝ] ℝ) (rotConj axialRotationHolds_proof p.2
          (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) u)‖
        ≤ ‖rotConj axialRotationHolds_proof p.2 (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) u‖ := by
          simpa using PiLp.norm_apply_le (rotConj axialRotationHolds_proof p.2
            (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)) u) l
    _ ≤ ‖rotConj axialRotationHolds_proof p.2 (fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x))‖ * ‖u‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (ψ (σ + p.1)) (axialRot p.2 x)‖ * ‖u‖ :=
          mul_le_mul_of_nonneg_right (norm_rotConj_le _ _ _) (norm_nonneg _)

theorem modeVel_eq_box {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) (σ : ℝ)
    (l : Fin 3) (x : Space) :
    modeVel ι ψ σ x l = (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand ψ ι σ l x p ∂boxMeasure := by
  unfold modeVel
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (ψ (σ + τ) (axialRot φ x)) l : ℝ) : ℂ))
    (integrable_box_of_continuous (continuous_modeTestIntegrand hψ ι σ l x))

end CurlWeight.Internal.TestModes

namespace CurlWeight.Internal

open Internal.ModeRotation ModeDerivative.Internal TestModes

theorem hasFDerivAt_modeVel_testField {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) :
    ∃ C : ℝ, ∃ D : Space → (Space →L[ℝ] ℂ),
      (∀ y, HasFDerivAt (fun x => modeVel ι ψ σ x l) (D y) y) ∧
      (∀ y j, D y (unitVector j) = modeGrad ι (gradField ψ) σ y (l, j)) ∧
      ∀ y, ‖D y‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := testSlice_fderiv_bound hψ σ
  have hbound : ∀ᵐ p ∂boxMeasure, ∀ x ∈ (Set.univ : Set Space),
      ‖modeTestIntegrandDeriv ψ ι σ l x p‖ ≤ B := by
    filter_upwards [ae_box_mem] with p hp x _
    refine (norm_modeTestIntegrandDeriv_le ι σ l x p).trans (hB _ ?_ _)
    exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  refine ⟨‖(1 / (2 * Real.pi) : ℂ)‖ * ∫ _p, B ∂boxMeasure,
    fun y => (1 / (2 * Real.pi) : ℂ) • ∫ p, modeTestIntegrandDeriv ψ ι σ l y p ∂boxMeasure, ?_, ?_, ?_⟩
  · intro y
    have hfun : (fun x => modeVel ι ψ σ x l) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand ψ ι σ l x p ∂boxMeasure := by
      funext x
      exact modeVel_eq_box hψ ι σ l x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => modeTestIntegrand ψ ι σ l x p) (F' := fun x p => modeTestIntegrandDeriv ψ ι σ l x p)
      (bound := fun _ => B) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (continuous_modeTestIntegrand hψ ι σ l x).aestronglyMeasurable)
      (integrable_box_of_continuous (continuous_modeTestIntegrand hψ ι σ l y))
      (continuous_modeTestIntegrandDeriv hψ ι σ l y).aestronglyMeasurable hbound
      (integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => hasFDerivAt_modeTestIntegrand hψ ι σ l x p)
    exact hI.const_mul _
  · intro y j
    have hint := integrable_box_of_continuous (continuous_modeTestIntegrandDeriv hψ ι σ l y)
    rw [smul_apply, ContinuousLinearMap.integral_apply hint, smul_eq_mul]
    unfold modeGrad
    rw [modeAverage_eq]
    congr 1
    rw [iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (gradField ψ (σ + τ) (axialRot φ y)
      (axialRot φ (unitVector (l, j).2))) (l, j).1 : ℝ) : ℂ))]
    · congr 1
      funext p
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]
    · refine (hint.apply_continuousLinearMap (unitVector j)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]
  · intro y
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact norm_integral_le_of_norm_le (integrable_box_of_continuous continuous_const)
      (hbound.mono fun p hp => hp y (Set.mem_univ _))

end CurlWeight.Internal

end Coercive

end Breakdown
