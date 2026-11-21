import TorusEuler.TruncatedParentResidual
import TorusEuler.PressureHessianMultiplier

/-! Spatial differentiation of the real Fourier cutoff in Proposition 5.11. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

private theorem spatiallyPeriodic_pullback {E : Type*} (g : Labels → E) :
    SpatiallyPeriodic (fun x => g (toUnitTorus x)) :=
  fun n _ => congrArg g ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

private theorem mFourierCoeff_comp_complexCLM
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (g : C(Labels, E)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => L (g z)) k = L (mFourierCoeff g k) := by
  have hcont : Continuous (fun z => mFourier (-k) z • g z) :=
    (mFourier (-k)).continuous.smul g.continuous
  have hint : Integrable (fun z => mFourier (-k) z • g z) unitTorusMeasure := by
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ
  change (∫ z, mFourier (-k) z • L (g z) ∂unitTorusMeasure) =
    L (∫ z, mFourier (-k) z • g z ∂unitTorusMeasure)
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

private theorem smoothFourierCutoff_comp_complexCLM
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (g : C(Labels, E)) (ψ : Vec3 → ℝ) (Λ : ℝ) (z : Labels) :
    L (smoothFourierCutoff ψ Λ g z) = smoothFourierCutoff ψ Λ (fun a => L (g a)) z := by
  unfold smoothFourierCutoff finiteFourierSum
  simp only [map_sum, map_smul, ContinuousLinearMap.map_smul_of_tower, mFourierCoeff_comp_complexCLM]

private theorem fderiv_left_comp_CLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Vec3 → E}
    {x : Vec3} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => L (f y)) x = L.comp (fderiv ℝ f x) :=
  (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- A coordinate derivative of a continuous torus vector field has the exact Fourier multiplier. -/
theorem mFourierCoeff_coordinateDerivative_complexVector
    (g d : C(Labels, ComplexEuclideanVec3)) (i : Fin 3)
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) (k : Fin 3 → ℤ) :
    mFourierCoeff d k = fourierDerivativeSymbol k i • mFourierCoeff g k := by
  apply PiLp.ext
  intro j
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj j
  change L (mFourierCoeff d k) = L (fourierDerivativeSymbol k i • mFourierCoeff g k)
  rw [map_smul, ← mFourierCoeff_comp_complexCLM L d, ← mFourierCoeff_comp_complexCLM L g, smul_eq_mul]
  rw [fourierCoeff_eq_centeredCell, fourierCoeff_eq_centeredCell]
  have hc : ContDiff ℝ 1 (fun x => L (g (toUnitTorus x))) := (L.restrictScalars ℝ).contDiff.comp hg
  have hper := spatiallyPeriodic_pullback (fun a => L (g a))
  simp only [smul_eq_mul]
  have hder (x : Vec3) : L (d (toUnitTorus x)) =
      fderiv ℝ (fun y => L (g (toUnitTorus y))) x (EuclideanSpace.single i 1) := by
    rw [hd]
    exact (congrArg (fun A : Vec3 →L[ℝ] ℂ => A (EuclideanSpace.single i 1))
      (fderiv_left_comp_CLM (L.restrictScalars ℝ) (hg.differentiable (by simp) x))).symm
  simp_rw [hder]
  exact centeredCell_fourier_coordinate_deriv hc hper k i

private theorem fderiv_lift_smoothFourierCutoff_single
    (ψ : Vec3 → ℝ) (Λ : ℝ) (g d : C(Labels, ComplexEuclideanVec3)) (i : Fin 3)
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) (x : Vec3) :
    fderiv ℝ (fun y => smoothFourierCutoff ψ Λ g (toUnitTorus y)) x (EuclideanSpace.single i 1) =
      smoothFourierCutoff ψ Λ d (toUnitTorus x) := by
  unfold smoothFourierCutoff
  rw [fderiv_lift_finiteFourierSum_single]
  congr 1
  funext k
  rw [mFourierCoeff_coordinateDerivative_complexVector g d i hg hd]
  exact smul_comm _ _ _

/-- The real cutoff commutes with every coordinate of the spatial derivative on torus lifts. -/
theorem fderiv_lift_realVectorFourierCutoff_single
    (ψ : Vec3 → ℝ) (Λ : ℝ) (g d : C(Labels, Vec3)) (i : Fin 3)
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) (x : Vec3) :
    fderiv ℝ (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x (EuclideanSpace.single i 1) =
      realVectorFourierCutoff ψ Λ d (toUnitTorus x) := by
  let gc := endpointComplexifyContinuous g
  let dc := endpointComplexifyContinuous d
  let fc := fun y => smoothFourierCutoff ψ Λ gc (toUnitTorus y)
  have hgc : ContDiff ℝ 1 (fun y => gc (toUnitTorus y)) := periodicComplexifyVector.contDiff.comp hg
  have hdc (y : Vec3) : dc (toUnitTorus y) =
      fderiv ℝ (fun z => gc (toUnitTorus z)) y (EuclideanSpace.single i 1) := by
    change periodicComplexifyVector (d (toUnitTorus y)) =
      fderiv ℝ (fun z => periodicComplexifyVector (g (toUnitTorus z))) y (EuclideanSpace.single i 1)
    rw [hd, fderiv_left_comp_CLM periodicComplexifyVector (hg.differentiable (by simp) y)]
    rfl
  have hfc : ContDiff ℝ ∞ fc := contDiff_lift_smoothFourierCutoff ψ Λ gc
  change fderiv ℝ (fun y => periodicRealPartVector (fc y)) x (EuclideanSpace.single i 1) =
    periodicRealPartVector (smoothFourierCutoff ψ Λ dc (toUnitTorus x))
  rw [fderiv_left_comp_CLM periodicRealPartVector (hfc.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply]
  exact congrArg periodicRealPartVector (fderiv_lift_smoothFourierCutoff_single ψ Λ gc dc i hgc hdc x)

/-- The real tensor cutoff operates on the columns of a physical momentum tensor. -/
def momentumTensorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(Labels, MomentumTensor))
    (z : Labels) : MomentumTensor :=
  realTensorFourierCutoff
    (ContinuousLinearMap.piMap fun _ : Fin 3 => periodicComplexifyVector)
    (ContinuousLinearMap.piMap fun _ : Fin 3 => periodicRealPartVector) ψ Λ g z

def momentumTensorColumn (g : C(Labels, MomentumTensor)) (i : Fin 3) : C(Labels, Vec3) :=
  ⟨fun z => g z i, (continuous_apply i).comp g.continuous⟩

@[simp]
theorem momentumTensorFourierCutoff_apply (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(Labels, MomentumTensor)) (z : Labels) (i : Fin 3) :
    momentumTensorFourierCutoff ψ Λ g z i = realVectorFourierCutoff ψ Λ (momentumTensorColumn g i) z := by
  let gc : C(Labels, Fin 3 → ComplexEuclideanVec3) :=
    ⟨fun a => (ContinuousLinearMap.piMap fun _ : Fin 3 => periodicComplexifyVector) (g a),
      (ContinuousLinearMap.piMap fun _ : Fin 3 => periodicComplexifyVector).continuous.comp g.continuous⟩
  let L : (Fin 3 → ComplexEuclideanVec3) →L[ℂ] ComplexEuclideanVec3 := ContinuousLinearMap.proj i
  change periodicRealPartVector (L (smoothFourierCutoff ψ Λ gc z)) = _
  rw [smoothFourierCutoff_comp_complexCLM L gc]
  rfl


private theorem mFourierCoeff_add_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (g h : C(Labels, E)) (k : Fin 3 → ℤ) :
    mFourierCoeff (g + h) k = mFourierCoeff g k + mFourierCoeff h k := by
  have hI (a : C(Labels, E)) : Integrable (fun z => mFourier (-k) z • a z) unitTorusMeasure := by
    have hc : Continuous (fun z => mFourier (-k) z • a z) := (mFourier (-k)).continuous.smul a.continuous
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ
  unfold mFourierCoeff
  simp only [ContinuousMap.add_apply, smul_add]
  exact integral_add (hI g) (hI h)

/-- Real vector cutoff preserves addition of continuous torus fields. -/
theorem realVectorFourierCutoff_add (ψ : Vec3 → ℝ) (Λ : ℝ) (g h : C(Labels, Vec3)) (z : Labels) :
    realVectorFourierCutoff ψ Λ (g + h) z =
      realVectorFourierCutoff ψ Λ g z + realVectorFourierCutoff ψ Λ h z := by
  change periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous (g + h)) z) =
    periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z) +
      periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous h) z)
  have hc : endpointComplexifyContinuous (g + h) = endpointComplexifyContinuous g + endpointComplexifyContinuous h := by
    ext a : 1
    exact periodicComplexifyVector.map_add (g a) (h a)
  rw [hc]
  simp only [smoothFourierCutoff, finiteFourierSum, mFourierCoeff_add_continuous, smul_add,
    Finset.sum_add_distrib, map_add]

private theorem realVectorFourierCutoff_zero (ψ : Vec3 → ℝ) (Λ : ℝ) (z : Labels) :
    realVectorFourierCutoff ψ Λ (0 : C(Labels, Vec3)) z = 0 := by
  change periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous 0) z) = 0
  have hc : endpointComplexifyContinuous 0 = 0 := by
    ext a : 1
    exact periodicComplexifyVector.map_zero
  rw [hc]
  simp [smoothFourierCutoff, finiteFourierSum, mFourierCoeff]

/-- The commutation with finite vector field sums, used in tensor divergence. -/
theorem realVectorFourierCutoff_sum {ι : Type*} (s : Finset ι) (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : ι → C(Labels, Vec3)) (z : Labels) :
    realVectorFourierCutoff ψ Λ (∑ j ∈ s, g j) z = ∑ j ∈ s, realVectorFourierCutoff ψ Λ (g j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realVectorFourierCutoff_zero]
  | @insert j s hj ih => simp [Finset.sum_insert hj, realVectorFourierCutoff_add, ih]

private theorem fderiv_tensorColumn {f : Vec3 → MomentumTensor} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    fderiv ℝ (fun y => f y i) x (EuclideanSpace.single i 1) = fderiv ℝ f x (EuclideanSpace.single i 1) i :=
  congrArg (fun D : Vec3 →L[ℝ] Vec3 => D (EuclideanSpace.single i 1))
    (fderiv_left_comp_CLM (ContinuousLinearMap.proj i) hf)

/-- The smooth lift of the actual tensor Fourier cutoff. -/
theorem contDiff_lift_momentumTensorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(Labels, MomentumTensor)) :
    ContDiff ℝ ∞ (fun x => momentumTensorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  let J : MomentumTensor →L[ℝ] (Fin 3 → ComplexEuclideanVec3) :=
    ContinuousLinearMap.piMap fun _ => periodicComplexifyVector
  let R : (Fin 3 → ComplexEuclideanVec3) →L[ℝ] MomentumTensor :=
    ContinuousLinearMap.piMap fun _ => periodicRealPartVector
  exact R.contDiff.comp (contDiff_lift_smoothFourierCutoff ψ Λ (fun z => J (g z)))

private theorem exists_torusVectorCoordinateDerivative (g : C(Labels, Vec3))
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x))) (i : Fin 3) :
    ∃ d : C(Labels, Vec3), ∀ x,
      d (toUnitTorus x) = fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1) := by
  have hper := (spatiallyPeriodic_pullback g).fderiv (hg.differentiable (by simp))
  have hD : SpatiallyPeriodic (fun x => fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) :=
    fun n x => congrArg (fun A : Vec3 →L[ℝ] Vec3 => A (EuclideanSpace.single i 1)) (hper n x)
  exact hD.exists_continuousTorusFunction ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- The cutoff commutes with the physical tensor divergence in (5.58). -/
theorem realVectorFourierCutoff_tensorDivergence
    (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(Labels, MomentumTensor)) (d : C(Labels, Vec3))
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) = momentumTensorDivergence (fderiv ℝ (fun y => g (toUnitTorus y)) x)) :
    (fun x => realVectorFourierCutoff ψ Λ d (toUnitTorus x)) =
      momentumTensorDivergence ∘ fderiv ℝ (fun x => momentumTensorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  let f := fun x => g (toUnitTorus x)
  let T := fun x => momentumTensorFourierCutoff ψ Λ g (toUnitTorus x)
  have hT : ContDiff ℝ ∞ T := contDiff_lift_momentumTensorFourierCutoff ψ Λ g
  have hf (i : Fin 3) : ContDiff ℝ 1 (fun x => momentumTensorColumn g i (toUnitTorus x)) := by
    let L : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj i
    exact L.contDiff.comp hg
  choose dc hdc using fun i => exists_torusVectorCoordinateDerivative (momentumTensorColumn g i) (hf i) i
  have hsum : d = ∑ j : Fin 3, dc j := by
    ext a : 1
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hd, momentumTensorDivergence_apply]
    simp only [ContinuousMap.sum_apply, hdc]
    exact Finset.sum_congr rfl fun j _ => (fderiv_tensorColumn (hg.differentiable (by simp) x) j).symm
  funext x
  change realVectorFourierCutoff ψ Λ d (toUnitTorus x) = momentumTensorDivergence (fderiv ℝ T x)
  rw [hsum, realVectorFourierCutoff_sum, momentumTensorDivergence_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hpoint : (fun y => T y j) = fun y => realVectorFourierCutoff ψ Λ (momentumTensorColumn g j) (toUnitTorus y) :=
    funext fun y => momentumTensorFourierCutoff_apply ψ Λ g (toUnitTorus y) j
  rw [← fderiv_tensorColumn (hT.differentiable (by simp) x) j, hpoint]
  exact (fderiv_lift_realVectorFourierCutoff_single ψ Λ (momentumTensorColumn g j) (dc j) j (hf j) (hdc j) x).symm



/-- The real scalar cutoff obtained by taking the real part of complex Fourier synthesis. -/
def realScalarFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(Labels, ℝ)) (z : Labels) : ℝ :=
  (smoothFourierCutoff ψ Λ (fun a => (g a : ℂ)) z).re

private def vectorCoordinate (g : C(Labels, Vec3)) (i : Fin 3) : C(Labels, ℝ) :=
  ⟨fun z => g z i, (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).continuous.comp g.continuous⟩

private theorem realScalarFourierCutoff_coordinate (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(Labels, Vec3)) (i : Fin 3) (z : Labels) :
    realScalarFourierCutoff ψ Λ (vectorCoordinate g i) z = realVectorFourierCutoff ψ Λ g z i := by
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj i
  exact congrArg Complex.re (smoothFourierCutoff_comp_complexCLM L (endpointComplexifyContinuous g) ψ Λ z).symm

private theorem realScalarFourierCutoff_add (ψ : Vec3 → ℝ) (Λ : ℝ) (g h : C(Labels, ℝ)) (z : Labels) :
    realScalarFourierCutoff ψ Λ (g + h) z = realScalarFourierCutoff ψ Λ g z + realScalarFourierCutoff ψ Λ h z := by
  let complexify (w : C(Labels, ℝ)) : C(Labels, ℂ) :=
    ⟨fun a => (w a : ℂ), Complex.ofRealCLM.continuous.comp w.continuous⟩
  change (smoothFourierCutoff ψ Λ (complexify (g + h)) z).re =
    (smoothFourierCutoff ψ Λ (complexify g) z).re + (smoothFourierCutoff ψ Λ (complexify h) z).re
  have hc : complexify (g + h) = complexify g + complexify h := by
    ext a : 1
    exact Complex.ofReal_add (g a) (h a)
  rw [hc]
  simp only [smoothFourierCutoff, finiteFourierSum, mFourierCoeff_add_continuous, smul_add,
    Finset.sum_add_distrib, Complex.add_re]

private theorem realScalarFourierCutoff_sum {ι : Type*} (s : Finset ι) (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : ι → C(Labels, ℝ)) (z : Labels) :
    realScalarFourierCutoff ψ Λ (∑ j ∈ s, g j) z = ∑ j ∈ s, realScalarFourierCutoff ψ Λ (g j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realScalarFourierCutoff, smoothFourierCutoff, finiteFourierSum, mFourierCoeff]
  | @insert j s hj ih => simp [Finset.sum_insert hj, realScalarFourierCutoff_add, ih]

/-- The real cutoff of the divergence equals the divergence of the real cutoff. -/
theorem realScalarFourierCutoff_divergence
    (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(Labels, Vec3)) (d : C(Labels, ℝ))
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) = divergence (fun y => g (toUnitTorus y)) x) :
    (fun x => realScalarFourierCutoff ψ Λ d (toUnitTorus x)) =
      divergence (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  choose dc hdc using fun i => exists_torusVectorCoordinateDerivative g hg i
  have hsum : d = ∑ j : Fin 3, vectorCoordinate (dc j) j := by
    ext a : 1
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hd, divergence, ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    change (fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single j 1)) j = dc j (toUnitTorus x) j
    rw [hdc]
  funext x
  rw [hsum, realScalarFourierCutoff_sum, divergence]
  apply Finset.sum_congr rfl
  intro j _
  rw [realScalarFourierCutoff_coordinate, fderiv_lift_realVectorFourierCutoff_single ψ Λ g (dc j) j hg (hdc j)]

/-- The unprojected momentum identity behind (5.58). -/
theorem momentum_realFourierCutoff_eq_residual_input
    (ψ : Vec3 → ℝ) (Λ : ℝ)
    (gV gVt gD gPG gRV : C(Labels, Vec3)) (u_t : Vec3 → Vec3)
    (hV : ContDiff ℝ 1 (fun x => gV (toUnitTorus x)))
    (ht : u_t = fun x => realVectorFourierCutoff ψ Λ gVt (toUnitTorus x))
    (hVeq : gVt + gD + gPG = gRV)
    (hD : ∀ x, gD (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV (toUnitTorus y)) (gV (toUnitTorus y))) x))
    (hu : ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ gV (toUnitTorus y)) x = 0) :
    let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
    u_t + (fun x => fderiv ℝ u x (u x)) + (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)) =
      truncatedEulerProjectedResidual id ψ Λ gV gRV := by
  let V := fun x => gV (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
  let v := u - V
  let gVV : C(Labels, MomentumTensor) := ⟨fun z => momentumTensor (gV z) (gV z),
    (momentumTensor.continuous.comp gV.continuous).clm_apply gV.continuous⟩
  let VV := fun x => gVV (toUnitTorus x)
  let cutVV := fun x => momentumTensorFourierCutoff ψ Λ gVV (toUnitTorus x)
  let uu := fun x => momentumTensor (u x) (u x)
  let E := (fun x => momentumTensor (v x) (u x)) + (fun x => momentumTensor (V x) (v x)) + (VV - cutVV)
  let cutD := fun x => realVectorFourierCutoff ψ Λ gD (toUnitTorus x)
  let cutPG := fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)
  let cutRV := fun x => realVectorFourierCutoff ψ Λ gRV (toUnitTorus x)
  let divT := fun g : Vec3 → MomentumTensor => momentumTensorDivergence ∘ fderiv ℝ g
  let adv := fun x => fderiv ℝ u x (u x)
  have hVV : ContDiff ℝ 1 VV := (momentumTensor.contDiff.comp hV).clm_apply hV
  have hcD : cutD = divT cutVV := realVectorFourierCutoff_tensorDivergence ψ Λ gVV gD hVV hD
  have hcRV : cutRV = u_t + cutD + cutPG := by
    funext x
    change realVectorFourierCutoff ψ Λ gRV (toUnitTorus x) = (u_t + cutD + cutPG) x
    rw [← hVeq, realVectorFourierCutoff_add, realVectorFourierCutoff_add, ht]
    rfl
  have hu' : ContDiff ℝ ∞ u := contDiff_lift_realVectorFourierCutoff ψ Λ gV
  have hcutVV : ContDiff ℝ ∞ cutVV := contDiff_lift_momentumTensorFourierCutoff ψ Λ gVV
  have huu : ContDiff ℝ ∞ uu := (momentumTensor.contDiff.comp hu').clm_apply hu'
  have hE : E = uu - cutVV := by
    funext x
    change momentumTensor (u x - V x) (u x) + momentumTensor (V x) (u x - V x) +
      (momentumTensor (V x) (V x) - cutVV x) = momentumTensor (u x) (u x) - cutVV x
    simp only [map_sub, sub_apply]
    abel
  have hdivE : divT E = divT uu - divT cutVV := by
    funext x
    change momentumTensorDivergence (fderiv ℝ E x) =
       momentumTensorDivergence (fderiv ℝ uu x) - momentumTensorDivergence (fderiv ℝ cutVV x)
    rw [hE, fderiv_sub (huu.differentiable (by simp) x) (hcutVV.differentiable (by simp) x), map_sub]
  have hA : divT uu = adv := momentumTensorDivergence_self_eq_advection (hu'.differentiable (by simp)) hu
  change u_t + adv + cutPG = cutRV + divT E
  rw [← hA, hdivE, hcRV, hcD]
  abel

/-- The physical projected momentum of the truncated field is the residual (5.58).
It suffices for the projection to remove the cutoff pressure gradient on this momentum field. -/
theorem projectedMomentum_realFourierCutoff_eq_residual
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) (ψ : Vec3 → ℝ) (Λ : ℝ)
    (gV gVt gD gPG gRV : C(Labels, Vec3)) (u_t : Vec3 → Vec3)
    (hV : ContDiff ℝ 1 (fun x => gV (toUnitTorus x)))
    (ht : u_t = fun x => realVectorFourierCutoff ψ Λ gVt (toUnitTorus x))
    (hVeq : gVt + gD + gPG = gRV)
    (hD : ∀ x, gD (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV (toUnitTorus y)) (gV (toUnitTorus y))) x))
    (hu : ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ gV (toUnitTorus y)) x = 0) :
    let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
    let mom := u_t + fun x => fderiv ℝ u x (u x)
    proj (mom + (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x))) = proj mom →
    proj mom = truncatedEulerProjectedResidual proj ψ Λ gV gRV := by
  intro u mom hP
  rw [← hP, show mom + (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)) =
    truncatedEulerProjectedResidual id ψ Λ gV gRV from
    momentum_realFourierCutoff_eq_residual_input ψ Λ gV gVt gD gPG gRV u_t hV ht hVeq hD hu]
  rfl

end

end TorusEuler
