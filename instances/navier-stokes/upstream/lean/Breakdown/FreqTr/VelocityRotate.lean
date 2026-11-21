import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.VelocityRotate

variable {A : Space → Space} {c : ℝ≥0∞}

theorem memLp_comp (hA : MeasurePreserving A volume (c • volume)) (hc : c ≠ ⊤)
    (M : Space →L[ℝ] Space) {g : Space → Space} (hg : MemLp g 6 volume) :
    MemLp (fun y => M (g (A y))) 6 volume :=
  M.comp_memLp' ((hg.smul_measure hc).comp_measurePreserving hA)

theorem ae_comp (hA : MeasurePreserving A volume (c • volume)) {g g' : Space → Space}
    (h : g =ᵐ[volume] g') : (fun y => g (A y)) =ᵐ[volume] fun y => g' (A y) :=
  hA.quasiMeasurePreserving.ae_eq_comp (Measure.smul_absolutelyContinuous.ae_eq h)

theorem eLpNorm_comp_le (hA : MeasurePreserving A volume (c • volume))
    (M : Space →L[ℝ] Space) {g : Space → Space} (hg : MemLp g 6 volume) :
    eLpNorm (fun y => M (g (A y))) 6 volume ≤
      ‖M‖₊ • (c ^ (1 / (6 : ℝ≥0∞)).toReal • eLpNorm g 6 volume) := by
  have h1 : eLpNorm (fun y => M (g (A y))) 6 volume ≤ ‖M‖₊ • eLpNorm (g ∘ A) 6 volume :=
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (Filter.Eventually.of_forall fun y => M.le_opNNNorm (g (A y))) 6
  have h2 : eLpNorm (g ∘ A) 6 volume = eLpNorm g 6 (c • volume) :=
    eLpNorm_comp_measurePreserving
      (hg.aestronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous) hA
  rw [h2, eLpNorm_smul_measure_of_ne_top (by simp)] at h1
  exact h1

def compOp (hA : MeasurePreserving A volume (c • volume)) (hc : c ≠ ⊤) (M : Space →L[ℝ] Space) :
    L6R →L[ℝ] L6R :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_comp hA hc M (Lp.memLp g)).toLp _
      map_add' := fun g₁ g₂ => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp (g₁ + g₂))),
          MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp g₁)),
          MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp g₂)),
          Lp.coeFn_add ((memLp_comp hA hc M (Lp.memLp g₁)).toLp _)
            ((memLp_comp hA hc M (Lp.memLp g₂)).toLp _),
          ae_comp hA (Lp.coeFn_add g₁ g₂)] with y h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5 ⊢
        rw [h4, h1, h2, h3, h5, map_add]
      map_smul' := fun r g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp (r • g))),
          MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp g)),
          Lp.coeFn_smul r ((memLp_comp hA hc M (Lp.memLp g)).toLp _),
          ae_comp hA (Lp.coeFn_smul r g)] with y h1 h2 h3 h4
        simp only [Pi.smul_apply, RingHom.id_apply] at h3 h4 ⊢
        rw [h3, h1, h2, h4, map_smul] }
    (‖M‖ * (c ^ (1 / (6 : ℝ≥0∞)).toReal).toReal) (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      have hne : c ^ (1 / (6 : ℝ≥0∞)).toReal ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hc
      have h := eLpNorm_comp_le hA M (Lp.memLp g)
      have hR : ‖M‖₊ • (c ^ (1 / (6 : ℝ≥0∞)).toReal • eLpNorm (g : Space → Space) 6 volume) ≠ ⊤ := by
        rw [ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hne (Lp.memLp g).2.ne)
      calc (eLpNorm (fun y => M ((g : Space → Space) (A y))) 6 volume).toReal
          ≤ (‖M‖₊ • (c ^ (1 / (6 : ℝ≥0∞)).toReal • eLpNorm (g : Space → Space) 6 volume)).toReal :=
            ENNReal.toReal_mono hR h
        _ = ‖M‖ * (c ^ (1 / (6 : ℝ≥0∞)).toReal).toReal * ‖g‖ := by
            rw [ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
              Lp.norm_def]
            simp [mul_assoc])

theorem compOp_ae (hA : MeasurePreserving A volume (c • volume)) (hc : c ≠ ⊤) (M : Space →L[ℝ] Space)
    (g : L6R) : (compOp hA hc M g : Space → Space) =ᵐ[volume] fun y => M ((g : Space → Space) (A y)) :=
  MemLp.coeFn_toLp (memLp_comp hA hc M (Lp.memLp g))

theorem compOp_toLp (hA : MeasurePreserving A volume (c • volume)) (hc : c ≠ ⊤) (M : Space →L[ℝ] Space)
    {φ : Space → Space} (hφ : MemLp φ 6 volume) :
    compOp hA hc M (toLpOrZero 6 φ) = toLpOrZero 6 (fun y => M (φ (A y))) := by
  have hφ' := memLp_comp hA hc M hφ
  simp only [toLpOrZero, dif_pos hφ, dif_pos hφ']
  apply Lp.ext
  filter_upwards [compOp_ae hA hc M (hφ.toLp φ), MemLp.coeFn_toLp hφ',
    ae_comp hA (MemLp.coeFn_toLp hφ)] with y h1 h2 h3
  rw [h1, h2, h3]

theorem decay_of_test {φ : Space → Space} (hφ : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨hs, hd, ?_⟩
  have hf : Continuous (fderiv ℝ φ) := hs.continuous_fderiv (by simp)
  have hφc : Continuous φ := hs.continuous
  have hcont : Continuous (fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖)) := by fun_prop
  have hsupp : HasCompactSupport (fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖)) :=
    (hc.norm.add (hc.fderiv ℝ).norm).mul_left
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨C, fun y => ?_⟩
  have h := hC y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 : 1 + ‖y‖ ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
  have ha := norm_nonneg (φ y)
  have hb := norm_nonneg (fderiv ℝ φ y)
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_nonneg (sq_nonneg (1 + ‖y‖)) hb]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (1 + ‖y‖)) ha]

theorem memLp_test {φ : Space → Space} (hφ : IsTestField φ) : MemLp φ 6 volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1

theorem coord_eq_inner (v : Space) (i : Fin 3) : v i = inner ℝ (unitVector i) v := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem sum_rot (R : Space ≃ₗᵢ[ℝ] Space) (T : Space →L[ℝ] Space) :
    ∑ i : Fin 3, (R (T (R.symm (unitVector i)))) i = ∑ i : Fin 3, (T (unitVector i)) i := by
  have hb := LinearMap.trace_eq_sum_inner (T : Space →ₗ[ℝ] Space)
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm)
  have he := LinearMap.trace_eq_sum_inner (T : Space →ₗ[ℝ] Space) (EuclideanSpace.basisFun (Fin 3) ℝ)
  simp only [coord_eq_inner]
  have hu : ∀ i, (EuclideanSpace.basisFun (Fin 3) ℝ) i = unitVector i := fun i => by
    simp [unitVector]
  have hl : ∀ i, inner ℝ (unitVector i) (R (T (R.symm (unitVector i)))) =
      inner ℝ (R.symm (unitVector i)) (T (R.symm (unitVector i))) := fun i => by
    rw [← R.inner_map_map (R.symm (unitVector i)) (T (R.symm (unitVector i))), R.apply_symm_apply]
  simp only [hl]
  simp only [OrthonormalBasis.map_apply, hu, ContinuousLinearMap.coe_coe] at hb he
  rw [← hb, he]

theorem test_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (pushForward R φ) := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨?_, ?_, fun y => ?_⟩
  · exact R.contDiff.comp (hs.comp R.symm.contDiff)
  · exact (hc.comp_homeomorph R.symm.toHomeomorph).comp_left (g := R) (map_zero R)
  · have hfd : HasFDerivAt (pushForward R φ)
        ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
          ((fderiv ℝ φ (R.symm y)).comp (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
      (R.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp y
        ((hs.differentiable (by simp) _).hasFDerivAt.comp y
          (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt)
    unfold divergenceAt
    rw [hfd.fderiv]
    have := sum_rot R (fderiv ℝ φ (R.symm y))
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [this]
    exact hd _

theorem test_dilate {μ : ℝ} (hμ : 0 < μ) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (dilateField μ φ) := by
  obtain ⟨hs, hc, hd⟩ := hφ
  have hne : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  refine ⟨?_, ?_, fun y => ?_⟩
  · exact (hs.comp (contDiff_const_smul _)).const_smul _
  · exact (hc.comp_smul hne).comp_left (g := fun v : Space => Real.sqrt μ • v) (smul_zero _)
  · have hA : HasFDerivAt (fun y : Space => Real.sqrt μ • y)
        (Real.sqrt μ • ContinuousLinearMap.id ℝ Space) y := (hasFDerivAt_id (𝕜 := ℝ) y).const_smul (Real.sqrt μ)
    have hfd : HasFDerivAt (fun y => Real.sqrt μ • φ (Real.sqrt μ • y))
        (Real.sqrt μ • (fderiv ℝ φ (Real.sqrt μ • y)).comp (Real.sqrt μ • ContinuousLinearMap.id ℝ Space)) y :=
      (((hs.differentiable (by simp) _).hasFDerivAt.comp y hA).const_smul (Real.sqrt μ))
    unfold divergenceAt
    rw [show dilateField μ φ = fun y => Real.sqrt μ • φ (Real.sqrt μ • y) from rfl, hfd.fderiv]
    have h0 := hd (Real.sqrt μ • y)
    unfold divergenceAt at h0
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, h0]
    ring

theorem velocity_spec (h1 : VelocityExists) : VelocitySpec velocity := by
  have hv : velocity = h1.choose := by unfold velocity; exact dif_pos h1
  rw [hv]
  exact h1.choose_spec

theorem eq_of_test (h2 : TestDense) (h3 : TestSpanSpec) {T : X → X} (hT : Continuous T)
    (P : L6R →L[ℝ] L6R)
    (h : ∀ φ, IsTestField φ → velocity (T (embedX φ)) = P (velocity (embedX φ))) (x : X) :
    velocity (T x) = P (velocity x) := by
  have hext := Continuous.ext_on h2 (f := fun x => velocity (T x)) (g := fun x => P (velocity x))
    (velocity.continuous.comp hT) (P.continuous.comp velocity.continuous)
    (fun x hx => by obtain ⟨φ, hφ, rfl⟩ := h3 x hx; exact h φ hφ)
  exact congrFun hext x

end Internal.VelocityRotate

open Internal.VelocityRotate in
theorem velocityRotateDilate (h1 : VelocityExists) (h2 : TestDense) (h3 : TestSpanSpec) (h4 : EmbedRot)
    (h5 : EmbedDilate) (_h6 : RotationAlgebra) (_h7 : DilationAlgebra) (_h8 : EmbedLinear) :
    VelocityRotate ∧ VelocityDilate := by
  refine ⟨fun R x => ?_, fun μ hμ x => ?_⟩
  · have hR : MeasurePreserving R.symm volume ((1 : ℝ≥0∞) • volume) := by
      rw [one_smul]
      exact R.symm.measurePreserving
    have key := eq_of_test h2 h3 (rotX R).continuous
      (compOp hR ENNReal.one_ne_top (R.toContinuousLinearEquiv : Space →L[ℝ] Space))
      (fun φ hφ => by
        rw [h4 R φ (decay_of_test hφ), velocity_spec h1 _ (test_pushForward R hφ),
          velocity_spec h1 _ hφ, compOp_toLp hR _ _ (memLp_test hφ)]
        rfl) x
    rw [key]
    exact compOp_ae hR _ _ (velocity x)
  · have hne : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
    have hD : MeasurePreserving (fun y : Space => Real.sqrt μ • y) volume
        (ENNReal.ofReal |(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| • volume) :=
      ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume hne⟩
    have key := eq_of_test h2 h3 (dilX μ).continuous
      (compOp hD ENNReal.ofReal_ne_top (Real.sqrt μ • ContinuousLinearMap.id ℝ Space))
      (fun φ hφ => by
        rw [h5 μ φ hμ (decay_of_test hφ), velocity_spec h1 _ (test_dilate hμ hφ),
          velocity_spec h1 _ hφ, compOp_toLp hD _ _ (memLp_test hφ)]
        rfl) x
    rw [key]
    exact compOp_ae hD _ _ (velocity x)

end Breakdown.Freq
