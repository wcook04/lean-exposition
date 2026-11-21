import TorusEuler.PeriodicLerayL2
import TorusEuler.EndpointSmoothSlices

/-! Identification of the real spatial Leray projection in Appendix A. -/

open MeasureTheory UnitAddTorus
open scoped InnerProductSpace ContDiff

namespace TorusEuler

noncomputable section

local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "Hℂ" => PeriodicComplexL2

/-- Coordinatewise real part on the complex Euclidean spatial vector. -/
def periodicRealPartVector : ComplexEuclideanVec3 →L[ℝ] Vec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap fun _ : Fin 3 => Complex.reCLM).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).toContinuousLinearMap)

@[simp] theorem periodicRealPartVector_apply (v : ComplexEuclideanVec3) (i : Fin 3) :
    periodicRealPartVector v i = (v i).re := rfl

/-- Coordinatewise real part on spatial L². -/
def periodicRealPartL2 : Hℂ →L[ℝ] H :=
  periodicRealPartVector.compLpL 2 unitTorusMeasure

theorem periodicRealPartL2_apply_ae (v : Hℂ) :
    periodicRealPartL2 v =ᵐ[unitTorusMeasure] fun a => periodicRealPartVector (v a) :=
  periodicRealPartVector.coeFn_compLpL v

@[simp] theorem periodicRealPartL2_complexify (v : H) :
    periodicRealPartL2 (periodicComplexifyL2 v) = v := by
  apply Lp.ext
  filter_upwards [periodicRealPartL2_apply_ae (periodicComplexifyL2 v),
    periodicComplexifyL2_apply_ae v] with a h₁ h₂
  rw [h₁, h₂]
  apply PiLp.ext
  intro i
  simp

theorem periodicComplexifyL2_injective : Function.Injective periodicComplexifyL2 :=
  Function.LeftInverse.injective periodicRealPartL2_complexify

private theorem inner_realPartVector_left (u : ComplexEuclideanVec3) (v : Vec3) :
    ⟪periodicRealPartVector u, v⟫_ℝ = (⟪u, periodicComplexifyVector v⟫_ℂ).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change _ = Complex.reCLM (∑ i : Fin 3, ⟪u i, periodicComplexifyVector v i⟫_ℂ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, Complex.mul_re, mul_comm]

private theorem inner_realPartL2_left (u : Hℂ) (v : H) :
    ⟪periodicRealPartL2 u, v⟫_ℝ = (⟪u, periodicComplexifyL2 v⟫_ℂ).re := by
  rw [L2.inner_def, L2.inner_def]
  have hI := L2.integrable_inner (𝕜 := ℂ) u (periodicComplexifyL2 v)
  change _ = Complex.reCLM (∫ z, ⟪u z, periodicComplexifyL2 v z⟫_ℂ ∂unitTorusMeasure)
  rw [← Complex.reCLM.integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [periodicRealPartL2_apply_ae u, periodicComplexifyL2_apply_ae v] with a h₁ h₂
  rw [h₁, h₂]
  change _ = (⟪u a, periodicComplexifyVector (v a)⟫_ℂ).re
  exact inner_realPartVector_left (u a) (v a)

private abbrev ScalarTorusL2 := Lp ℂ 2 unitTorusMeasure

private def coordinateL2 (i : Fin 3) : Hℂ →L[ℂ] ScalarTorusL2 :=
  (EuclideanSpace.proj i).compLpL 2 unitTorusMeasure

private def insertCoordinateL2 (i : Fin 3) : ScalarTorusL2 →L[ℂ] Hℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i (1 : ℂ))).compLpL 2 unitTorusMeasure

private theorem sum_insertCoordinateL2 (u : Hℂ) :
    (∑ i, insertCoordinateL2 i (coordinateL2 i u)) = u := by
  apply Lp.ext
  have hs (i : Fin 3) : ∀ᵐ a ∂unitTorusMeasure, insertCoordinateL2 i (coordinateL2 i u) a =
      u a i • EuclideanSpace.single i (1 : ℂ) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i (1 : ℂ))) (coordinateL2 i u),
      ContinuousLinearMap.coeFn_compLpL
        (EuclideanSpace.proj i : ComplexEuclideanVec3 →L[ℂ] ℂ) u] with a h₁ h₂
    change insertCoordinateL2 i (coordinateL2 i u) a =
      (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i (1 : ℂ))) (coordinateL2 i u a) at h₁
    change coordinateL2 i u a = u a i at h₂
    rw [h₁, h₂, ContinuousLinearMap.toSpanSingleton_apply]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => insertCoordinateL2 i (coordinateL2 i u)),
    ae_all_iff.mpr hs] with a ha hsa
  rw [ha]
  simp only [Finset.sum_apply, hsa]
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin 3) ℂ).sum_repr (u a)

private def periodicL2ModeSpan : Submodule ℂ Hℂ :=
  Submodule.span ℂ
    (Set.range fun w : (Fin 3 → ℤ) × ComplexEuclideanVec3 => periodicL2Mode w.1 w.2)

private theorem periodicL2ModeSpan_closure_eq_top : periodicL2ModeSpan.topologicalClosure = ⊤ := by
  let S : Submodule ℂ ScalarTorusL2 := Submodule.span ℂ (Set.range (mFourierLp (d := Fin 3) 2))
  have hS : S.topologicalClosure = ⊤ :=
    span_mFourierLp_closure_eq_top (d := Fin 3) (p := 2) (by simp)
  apply top_unique
  intro u _
  have hcoord (i : Fin 3) :
      insertCoordinateL2 i (coordinateL2 i u) ∈ periodicL2ModeSpan.topologicalClosure := by
    have hmap : S.map (insertCoordinateL2 i).toLinearMap ≤ periodicL2ModeSpan := by
      rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(k, EuclideanSpace.single i 1), rfl⟩
    have hmem : coordinateL2 i u ∈ S.topologicalClosure := hS ▸ Submodule.mem_top
    exact Submodule.topologicalClosure_mono hmap
      (S.topologicalClosure_map (insertCoordinateL2 i) (Submodule.mem_map_of_mem hmem))
  rw [← sum_insertCoordinateL2 u]
  exact periodicL2ModeSpan.topologicalClosure.sum_mem fun i _ => hcoord i

private theorem periodicL2_eq_zero_of_vanishes_on_modes (L : Hℂ →L[ℝ] ℝ)
    (hL : ∀ k a, L (periodicL2Mode k a) = 0) (u : Hℂ) :
    L u = 0 := by
  have hSpan (v : Hℂ) (hv : v ∈ periodicL2ModeSpan) : ∀ c : ℂ, L (c • v) = 0 := by
    refine Submodule.span_induction (p := fun w _ => ∀ c : ℂ, L (c • w) = 0)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨k, a⟩, rfl⟩ c
      rw [← map_smul]
      exact hL k (c • a)
    · simp
    · intro v w _ _ hv hw c
      rw [smul_add, map_add, hv c, hw c, add_zero]
    · intro c v _ hv d
      rw [smul_smul]
      exact hv (d * c)
  have hsubset : (periodicL2ModeSpan : Set Hℂ) ⊆ {v : Hℂ | L v = 0} := by
    intro v hv
    simpa using hSpan v hv 1
  have hclosed : IsClosed {v : Hℂ | L v = 0} := isClosed_eq L.continuous continuous_const
  have hu : u ∈ periodicL2ModeSpan.topologicalClosure :=
    periodicL2ModeSpan_closure_eq_top ▸ Submodule.mem_top
  exact closure_minimal hsubset hclosed hu

/-- Apply a real linear functional to each component of a complex Fourier wave. -/
private def scalarizedFourierMode (L : ℂ →L[ℝ] ℝ) (k : Fin 3 → ℤ) (a : ComplexVec3) :
    C(UnitAddTorus (Fin 3), Vec3) where
  toFun z := WithLp.toLp 2 (fun i => L (mFourier k z * a i))
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun _i => L.continuous.comp ((mFourier k).continuous.mul continuous_const))

@[simp] private theorem scalarizedFourierMode_apply (L : ℂ →L[ℝ] ℝ) (k : Fin 3 → ℤ)
    (a : ComplexVec3) (z : UnitAddTorus (Fin 3)) (i : Fin 3) :
    scalarizedFourierMode L k a z i = L (mFourier k z * a i) := rfl

private theorem contDiff_scalarizedFourierMode_lift (L : ℂ →L[ℝ] ℝ)
    (k : Fin 3 → ℤ) (a : ComplexVec3) :
    ContDiff ℝ ∞ (fun x => scalarizedFourierMode L k a (toUnitTorus x)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ ∞ (fun x => L (fourierMode k x * a i))
  exact L.contDiff.comp ((contDiff_fourierMode k).mul contDiff_const)

private theorem divergence_scalarizedFourierMode_lift (L : ℂ →L[ℝ] ℝ)
    (k : Fin 3 → ℤ) (a : ComplexVec3) (x : Vec3) :
    divergence (fun y => scalarizedFourierMode L k a (toUnitTorus y)) x =
      L (fourierMode k x * divergenceMode k a) := by
  let f (y : Vec3) := scalarizedFourierMode L k a (toUnitTorus y)
  have hf : DifferentiableAt ℝ f x :=
    (contDiff_scalarizedFourierMode_lift L k a).differentiable (by simp) x
  have h (i : Fin 3) : (fderiv ℝ f x (EuclideanSpace.single i 1)) i =
      L (fourierDerivativeSymbol k i * fourierMode k x * a i) := by
    let P : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj i
    have hP := (P.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
    have hL := (L.hasFDerivAt.comp x
      (((contDiff_fourierMode k).differentiable (by simp) x).hasFDerivAt.mul_const' (a i))).fderiv
    have hagree : P ∘ f = (fun y => L (fourierMode k y * a i)) := rfl
    change fderiv ℝ (fun y => L (fourierMode k y * a i)) x = _ at hL
    rw [hagree, hL] at hP
    have hp := congrArg (fun D : Vec3 →L[ℝ] ℝ => D (EuclideanSpace.single i 1)) hP
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, op_smul_eq_mul,
      fderiv_fourierMode_single, P] at hp
    exact hp.symm
  change (∑ i : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) i) = _
  simp_rw [h]
  rw [← map_sum, divergenceMode, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- Smooth real Fourier waves with transverse complex coefficients pass the weak spatial tests. -/
private theorem scalarizedFourierMode_toLp_mem_endpointSpatialSolenoidal
    (L : ℂ →L[ℝ] ℝ) (k : Fin 3 → ℤ) (a : ComplexVec3)
    (h : frequencyContraction k a = 0) :
    (scalarizedFourierMode L k a).toLp 2 unitTorusMeasure ℝ ∈ endpointSpatialSolenoidal := by
  rw [mem_endpointSpatialSolenoidal]
  intro p
  have hA := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure
    (scalarizedFourierMode L k a)
  rw [integral_congr_ae (hA.mono fun z hz =>
    congrArg (fun v => ⟪endpointPotentialGradient p z, v⟫_ℝ) hz)]
  refine endpointTorusGradientPairing_eq_zero_of_divergence_free
    ((contDiff_scalarizedFourierMode_lift L k a).of_le (by simp)) (fun _ => rfl) (fun x => ?_) p
  rw [divergence_scalarizedFourierMode_lift, divergenceMode_eq, h, mul_zero, mul_zero, map_zero]


private theorem periodicRealPartL2_mode_transverse_mem (k : Fin 3 → ℤ)
    (a : ComplexEuclideanVec3) (ha : a ∈ transverseModeSpace k) :
    periodicRealPartL2 (periodicL2Mode k a) ∈ endpointSpatialSolenoidal := by
  have hcontraction : frequencyContraction k a.ofLp = 0 :=
    (mem_transverseModeSpace_iff k a.ofLp).mp ha
  let g := scalarizedFourierMode Complex.reCLM k a.ofLp
  have hEq : periodicRealPartL2 (periodicL2Mode k a) = g.toLp 2 unitTorusMeasure ℝ := by
    apply Lp.ext
    filter_upwards [periodicRealPartL2_apply_ae (periodicL2Mode k a),
      periodicL2Mode_apply_ae k a, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure g]
      with z hreal hmode hg
    rw [hreal, hmode, hg]
    apply PiLp.ext
    intro i
    rfl
  rw [hEq]
  exact scalarizedFourierMode_toLp_mem_endpointSpatialSolenoidal Complex.reCLM k a.ofLp hcontraction

/-- The real part of every projected complex L² field passes the smooth weak divergence tests. -/
theorem periodicRealPartL2_leray_mem_endpointSpatialSolenoidal (u : Hℂ) :
    periodicRealPartL2 (periodicComplexLeray u) ∈ endpointSpatialSolenoidal := by
  rw [mem_endpointSpatialSolenoidal]
  intro p
  rw [← endpointSpatialDivergenceTest_apply]
  let L : Hℂ →L[ℝ] ℝ :=
    (endpointSpatialDivergenceTest p).comp (periodicRealPartL2.comp (periodicComplexLeray.restrictScalars ℝ))
  change L u = 0
  refine periodicL2_eq_zero_of_vanishes_on_modes L ?_ u
  intro k a
  change endpointSpatialDivergenceTest p
    (periodicRealPartL2 (periodicComplexLeray (periodicL2Mode k a))) = 0
  rw [periodicComplexLeray_mode, endpointSpatialDivergenceTest_apply]
  have ha : lerayModeProjection k a ∈ transverseModeSpace k :=
    (transverseModeSpace k).starProjection_apply_mem a
  exact (mem_endpointSpatialSolenoidal _).mp (periodicRealPartL2_mode_transverse_mem k _ ha) p

private instance : endpointSpatialSolenoidal.HasOrthogonalProjection :=
  let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
  inferInstance

/-- The real spatial L² Leray projection onto the weak gradient kernel, with ambient codomain. -/
def periodicRealLeray : H →L[ℝ] H :=
  endpointSpatialSolenoidal.starProjection

theorem norm_periodicRealLeray_le : ‖periodicRealLeray‖ ≤ 1 :=
  endpointSpatialSolenoidal.starProjection_norm_le

theorem range_periodicRealLeray : periodicRealLeray.range = endpointSpatialSolenoidal :=
  endpointSpatialSolenoidal.range_starProjection

/-- Taking real parts intertwines the complex Fourier multiplier and the real weak projection. -/
theorem periodicRealLeray_realPart_eq (u : Hℂ) :
    periodicRealLeray (periodicRealPartL2 u) = periodicRealPartL2 (periodicComplexLeray u) := by
  change endpointSpatialSolenoidal.starProjection _ = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact periodicRealPartL2_leray_mem_endpointSpatialSolenoidal u
  · intro w hw
    have hJ := periodicComplexifyL2_mem_solenoidal_of_endpointSpatialSolenoidal w hw
    have horth : ⟪u - periodicComplexLeray u, periodicComplexifyL2 w⟫_ℂ = 0 :=
      periodicComplexSolenoidal.starProjection_inner_eq_zero u _ hJ
    rw [← map_sub, inner_realPartL2_left, horth]
    rfl

/-- A real L² field satisfies the weak gradient constraints exactly when its
complexification has transverse Fourier coefficients. -/
theorem periodicComplexifyL2_mem_solenoidal_iff (v : H) :
    periodicComplexifyL2 v ∈ periodicComplexSolenoidal ↔ v ∈ endpointSpatialSolenoidal := by
  refine ⟨fun hv => ?_, fun hv => periodicComplexifyL2_mem_solenoidal_of_endpointSpatialSolenoidal v hv⟩
  have h := periodicRealPartL2_leray_mem_endpointSpatialSolenoidal (periodicComplexifyL2 v)
  have hfixed : periodicComplexLeray (periodicComplexifyL2 v) = periodicComplexifyL2 v :=
    periodicComplexSolenoidal.starProjection_eq_self_iff.mpr hv
  simpa only [hfixed, periodicRealPartL2_complexify] using h


private theorem periodicRealPartL2_negI_apply_ae (u : Hℂ) :
    periodicRealPartL2 ((-Complex.I) • u) =ᵐ[unitTorusMeasure]
      fun z => (WithLp.toLp 2 (fun i => (u z i).im) : Vec3) := by
  filter_upwards [periodicRealPartL2_apply_ae ((-Complex.I) • u), Lp.coeFn_smul (-Complex.I) u]
    with z hreal hz
  rw [hreal, hz]
  apply PiLp.ext
  intro i
  change ((-Complex.I) * u z i).re = (u z i).im
  simp [Complex.mul_re]

private theorem periodicRealPartL2_negI_complexify (v : H) :
    periodicRealPartL2 ((-Complex.I) • periodicComplexifyL2 v) = 0 := by
  apply Lp.ext
  filter_upwards [periodicRealPartL2_negI_apply_ae (periodicComplexifyL2 v),
    periodicComplexifyL2_apply_ae v, (Lp.coeFn_zero (E := Vec3) (p := 2) (μ := unitTorusMeasure))]
    with z hreal hcomplex hzero
  rw [hreal, hcomplex, hzero]
  apply PiLp.ext
  intro i
  change (periodicComplexifyVector (v z) i).im = 0
  simp

private theorem periodicComplexifyL2_realPart_of_negI_eq_zero (u : Hℂ)
    (hi : periodicRealPartL2 ((-Complex.I) • u) = 0) :
    periodicComplexifyL2 (periodicRealPartL2 u) = u := by
  have him := periodicRealPartL2_negI_apply_ae u
  rw [hi] at him
  apply Lp.ext
  filter_upwards [him, (Lp.coeFn_zero (E := Vec3) (p := 2) (μ := unitTorusMeasure)),
    periodicComplexifyL2_apply_ae (periodicRealPartL2 u), periodicRealPartL2_apply_ae u]
    with z hi hz hc hr
  rw [hc, hr]
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simp
  · have hcoord := congrArg (fun w : Vec3 => w i) (hz.symm.trans hi)
    change 0 = (u z i).im at hcoord
    simpa using hcoord

/-- Complexification intertwines the real weak projection and the complex Fourier projection. -/
theorem periodicComplexifyL2_realLeray (v : H) :
    periodicComplexifyL2 (periodicRealLeray v) = periodicComplexLeray (periodicComplexifyL2 v) := by
  have hr := periodicRealLeray_realPart_eq (periodicComplexifyL2 v)
  rw [periodicRealPartL2_complexify] at hr
  rw [hr]
  apply periodicComplexifyL2_realPart_of_negI_eq_zero
  rw [← map_smul, ← periodicRealLeray_realPart_eq, periodicRealPartL2_negI_complexify, map_zero]

/-- The real weak projection has the Leray symbol on every Fourier coefficient. -/
theorem periodicL2Coefficient_realLeray (k : Fin 3 → ℤ) (v : H) :
    periodicL2Coefficient k (periodicComplexifyL2 (periodicRealLeray v)) =
      lerayModeProjection k (periodicL2Coefficient k (periodicComplexifyL2 v)) := by
  rw [periodicComplexifyL2_realLeray, periodicL2Coefficient_leray]

/-- The Fourier coefficients of the discarded part are the gradients of the
mean-zero pressure correction coefficients. -/
theorem periodicL2Coefficient_sub_realLeray (k : Fin 3 → ℤ) (v : H) :
    (periodicL2Coefficient k (periodicComplexifyL2 (v - periodicRealLeray v))).ofLp =
      gradientMode k (pressureCorrectionMode k (periodicL2Coefficient k (periodicComplexifyL2 v)).ofLp) := by
  simp only [map_sub, periodicL2Coefficient_realLeray]
  let a := periodicL2Coefficient k (periodicComplexifyL2 v)
  change a.ofLp - (lerayModeProjection k a).ofLp = gradientMode k (pressureCorrectionMode k a.ofLp)
  have h := lerayModeProjection_toLp k a.ofLp
  change lerayModeProjection k a = WithLp.toLp 2 (lerayMode k a.ofLp) at h
  rw [h]
  change a.ofLp - lerayMode k a.ofLp = gradientMode k (pressureCorrectionMode k a.ofLp)
  rw [lerayMode_eq_sub_gradient, sub_sub_cancel]

end

end TorusEuler
