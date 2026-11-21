import TorusEuler.PeriodicLerayReal
import TorusEuler.FreezingSymbol
import Mathlib.Analysis.Normed.Ring.Units

/-! Complexification of the real coefficient operators used in Appendix A. -/

open MeasureTheory Set UnitAddTorus
open scoped InnerProductSpace ComplexConjugate

namespace TorusEuler

/-- A realization of a complexified real normed space whose norm splits
orthogonally into its real and imaginary parts. -/
structure EndpointComplexification (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] where
  ofReal : E →L[ℝ] F
  re : F →L[ℝ] E
  im : F →L[ℝ] E
  re_ofReal : ∀ x, re (ofReal x) = x
  im_ofReal : ∀ x, im (ofReal x) = 0
  re_I : ∀ z, re (Complex.I • z) = -im z
  im_I : ∀ z, im (Complex.I • z) = re z
  reconstruct : ∀ z, ofReal (re z) + Complex.I • ofReal (im z) = z
  norm_sq : ∀ z, ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2

namespace EndpointComplexification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

variable (X : EndpointComplexification E F)

theorem norm_ofReal (x : E) : ‖X.ofReal x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [X.norm_sq, X.re_ofReal, X.im_ofReal, norm_zero, zero_pow (by decide), add_zero]

private noncomputable def extendReal (A : E →L[ℝ] E) : F →L[ℝ] F :=
  X.ofReal.comp (A.comp X.re) + Complex.I • X.ofReal.comp (A.comp X.im)

private theorem extendReal_apply (A : E →L[ℝ] E) (z : F) :
    X.extendReal A z = X.ofReal (A (X.re z)) + Complex.I • X.ofReal (A (X.im z)) :=
  rfl

private theorem re_extendReal (A : E →L[ℝ] E) (z : F) :
    X.re (X.extendReal A z) = A (X.re z) := by
  rw [extendReal_apply, map_add, X.re_ofReal, X.re_I, X.im_ofReal, neg_zero, add_zero]

private theorem im_extendReal (A : E →L[ℝ] E) (z : F) :
    X.im (X.extendReal A z) = A (X.im z) := by
  rw [extendReal_apply, map_add, X.im_ofReal, X.im_I, X.re_ofReal, zero_add]

private theorem extendReal_I (A : E →L[ℝ] E) (z : F) :
    X.extendReal A (Complex.I • z) = Complex.I • X.extendReal A z := by
  simp only [extendReal_apply, X.re_I, X.im_I, map_neg, smul_add, smul_smul,
    Complex.I_mul_I, neg_one_smul, add_comm]

private theorem complex_smul_parts (c : ℂ) (z : F) :
    c • z = c.re • z + c.im • (Complex.I • z) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]
  exact congrArg₂ (· + ·)
    (RCLike.real_smul_eq_coe_smul (K := ℂ) c.re z).symm
    (RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (Complex.I • z)).symm

private theorem norm_extendReal_apply_le (A : E →L[ℝ] E) (z : F) :
    ‖X.extendReal A z‖ ≤ ‖A‖ * ‖z‖ := by
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [X.norm_sq (X.extendReal A z), re_extendReal, im_extendReal, mul_pow, X.norm_sq z]
  calc
    ‖A (X.re z)‖ ^ 2 + ‖A (X.im z)‖ ^ 2 ≤
      (‖A‖ * ‖X.re z‖) ^ 2 + (‖A‖ * ‖X.im z‖) ^ 2 :=
        add_le_add
          (pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2)
          (pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2)
    _ = _ := by ring

/-- Extend a real operator complex-linearly on the given complexification. -/
noncomputable def extendOperator (A : E →L[ℝ] E) : F →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := X.extendReal A
      map_add' := (X.extendReal A).map_add
      map_smul' := fun c z => by
        change X.extendReal A (c • z) = c • X.extendReal A z
        rw [complex_smul_parts c z, map_add, map_smul, map_smul, extendReal_I]
        exact (complex_smul_parts c (X.extendReal A z)).symm }
    ‖A‖ (X.norm_extendReal_apply_le A)

theorem extendOperator_apply (A : E →L[ℝ] E) (z : F) :
    X.extendOperator A z = X.ofReal (A (X.re z)) + Complex.I • X.ofReal (A (X.im z)) :=
  rfl

@[simp] theorem re_extendOperator (A : E →L[ℝ] E) (z : F) :
    X.re (X.extendOperator A z) = A (X.re z) :=
  X.re_extendReal A z

@[simp] theorem im_extendOperator (A : E →L[ℝ] E) (z : F) :
    X.im (X.extendOperator A z) = A (X.im z) :=
  X.im_extendReal A z

@[simp] theorem extendOperator_ofReal (A : E →L[ℝ] E) (x : E) :
    X.extendOperator A (X.ofReal x) = X.ofReal (A x) := by
  rw [extendOperator_apply, X.re_ofReal, X.im_ofReal, map_zero, map_zero, smul_zero, add_zero]

theorem norm_extendOperator (A : E →L[ℝ] E) :
    ‖X.extendOperator A‖ = ‖A‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (X.norm_extendReal_apply_le A)) ?_
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (X.extendOperator A).le_opNorm (X.ofReal x)
  simpa only [X.extendOperator_ofReal, X.norm_ofReal] using h

@[simp] theorem extendOperator_one : X.extendOperator 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  exact X.reconstruct z

@[simp] theorem extendOperator_add (A B : E →L[ℝ] E) :
    X.extendOperator (A + B) = X.extendOperator A + X.extendOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [extendOperator_apply, _root_.add_apply, map_add, smul_add]
  abel

@[simp] theorem extendOperator_smul (c : ℝ) (A : E →L[ℝ] E) :
    X.extendOperator (c • A) = c • X.extendOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [extendOperator_apply, _root_.smul_apply, map_smul,
    smul_add, smul_comm Complex.I c]

@[simp] theorem extendOperator_mul (A B : E →L[ℝ] E) :
    X.extendOperator (A * B) = X.extendOperator A * X.extendOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  change X.extendOperator (A * B) z = X.extendOperator A (X.extendOperator B z)
  nth_rewrite 1 [X.extendOperator_apply]
  rw [X.extendOperator_apply A, X.re_extendOperator, X.im_extendOperator]
  rfl

/-- Complex extension is a norm-preserving real-linear map on operators. -/
noncomputable def extendOperatorCLM : (E →L[ℝ] E) →L[ℝ] (F →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := X.extendOperator
      map_add' := X.extendOperator_add
      map_smul' := X.extendOperator_smul }
    1 (fun A => by
      change ‖X.extendOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul, X.norm_extendOperator])

@[simp] theorem extendOperatorCLM_apply (A : E →L[ℝ] E) :
    X.extendOperatorCLM A = X.extendOperator A := rfl

/-- The same extension preserves the ring operations on endomorphisms. -/
noncomputable def extendOperatorRingHom : (E →L[ℝ] E) →+* (F →L[ℂ] F) where
  toFun := X.extendOperator
  map_one' := X.extendOperator_one
  map_mul' := X.extendOperator_mul
  map_zero' := X.extendOperatorCLM.map_zero
  map_add' := X.extendOperator_add

theorem extendOperator_ringInverse {A : E →L[ℝ] E} (hA : IsUnit A) :
    X.extendOperator (Ring.inverse A) = Ring.inverse (X.extendOperator A) := by
  obtain ⟨u, rfl⟩ := hA
  let v := Units.map X.extendOperatorRingHom.toMonoidHom u
  change X.extendOperator (Ring.inverse (u : E →L[ℝ] E)) = Ring.inverse (v : F →L[ℂ] F)
  rw [Ring.inverse_unit, Ring.inverse_unit]
  rfl

end EndpointComplexification

theorem EndpointComplexification.extendOperator_frozenSymbol
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    (X : EndpointComplexification E F) (r B : E →L[ℝ] E) :
    X.extendOperator (frozenSymbol r B) =
      X.extendOperator r * X.extendOperator B * X.extendOperator r + (1 - X.extendOperator r) := by
  change X.extendOperatorRingHom (r * B * r + (1 - r)) = _
  simp only [map_add, map_mul, map_sub, map_one]
  rfl

noncomputable section

/-- Coordinatewise imaginary part from complex Euclidean velocities. -/
def periodicImagPartVector : ComplexEuclideanVec3 →L[ℝ] Vec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap fun _ : Fin 3 => Complex.imCLM).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).toContinuousLinearMap)

@[simp] theorem periodicImagPartVector_apply (v : ComplexEuclideanVec3) (i : Fin 3) :
    periodicImagPartVector v i = (v i).im := rfl

private theorem norm_sq_real_imag_vector (v : ComplexEuclideanVec3) :
    ‖v‖ ^ 2 = ‖periodicRealPartVector v‖ ^ 2 + ‖periodicImagPartVector v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ‖v i‖ ^ 2 = (periodicRealPartVector v i) ^ 2 + (periodicImagPartVector v i) ^ 2
  rw [periodicRealPartVector_apply, periodicImagPartVector_apply, Complex.sq_norm, Complex.normSq_apply]
  ring


/-- The spatial coefficient space uses the usual complexification of Euclidean three-space. -/
def endpointSpatialComplexification : EndpointComplexification Vec3 ComplexEuclideanVec3 where
  ofReal := periodicComplexifyVector
  re := periodicRealPartVector
  im := periodicImagPartVector
  re_ofReal x := by
    apply PiLp.ext
    intro i
    simp
  im_ofReal x := by
    apply PiLp.ext
    intro i
    simp
  re_I z := by
    apply PiLp.ext
    intro i
    change (Complex.I * z i).re = -(z i).im
    simp [Complex.mul_re]
  im_I z := by
    apply PiLp.ext
    intro i
    change (Complex.I * z i).im = (z i).re
    simp [Complex.mul_im]
  reconstruct z := by
    apply PiLp.ext
    intro i
    change ((z i).re : ℂ) + Complex.I * ((z i).im : ℂ) = z i
    simpa only [mul_comm Complex.I] using Complex.re_add_im (z i)
  norm_sq := norm_sq_real_imag_vector

section L2Paths

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The coordinatewise embedding of real vector-valued L² paths. -/
def complexifyL2Vec3 : Lp Vec3 2 μ →L[ℝ] Lp ComplexEuclideanVec3 2 μ :=
  periodicComplexifyVector.compLpL 2 μ

/-- The real part of a complex vector-valued L² path. -/
def realPartL2Vec3 : Lp ComplexEuclideanVec3 2 μ →L[ℝ] Lp Vec3 2 μ :=
  periodicRealPartVector.compLpL 2 μ

/-- The imaginary part of a complex vector-valued L² path. -/
def imagPartL2Vec3 : Lp ComplexEuclideanVec3 2 μ →L[ℝ] Lp Vec3 2 μ :=
  periodicImagPartVector.compLpL 2 μ

theorem complexifyL2Vec3_apply_ae (v : Lp Vec3 2 μ) :
    complexifyL2Vec3 μ v =ᵐ[μ] fun a => periodicComplexifyVector (v a) :=
  periodicComplexifyVector.coeFn_compLpL v

theorem realPartL2Vec3_apply_ae (v : Lp ComplexEuclideanVec3 2 μ) :
    realPartL2Vec3 μ v =ᵐ[μ] fun a => periodicRealPartVector (v a) :=
  periodicRealPartVector.coeFn_compLpL v

theorem imagPartL2Vec3_apply_ae (v : Lp ComplexEuclideanVec3 2 μ) :
    imagPartL2Vec3 μ v =ᵐ[μ] fun a => periodicImagPartVector (v a) :=
  periodicImagPartVector.coeFn_compLpL v

@[simp] theorem realPartL2Vec3_complexify (v : Lp Vec3 2 μ) :
    realPartL2Vec3 μ (complexifyL2Vec3 μ v) = v := by
  apply Lp.ext
  filter_upwards [realPartL2Vec3_apply_ae μ (complexifyL2Vec3 μ v),
    complexifyL2Vec3_apply_ae μ v] with a h₁ h₂
  rw [h₁, h₂]
  apply PiLp.ext
  intro i
  simp

@[simp] theorem imagPartL2Vec3_complexify (v : Lp Vec3 2 μ) :
    imagPartL2Vec3 μ (complexifyL2Vec3 μ v) = 0 := by
  apply Lp.ext
  filter_upwards [imagPartL2Vec3_apply_ae μ (complexifyL2Vec3 μ v),
    complexifyL2Vec3_apply_ae μ v, Lp.coeFn_zero Vec3 2 μ] with a h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  apply PiLp.ext
  intro i
  simp

theorem complexifyL2Vec3_reconstruct (v : Lp ComplexEuclideanVec3 2 μ) :
    complexifyL2Vec3 μ (realPartL2Vec3 μ v) +
      Complex.I • complexifyL2Vec3 μ (imagPartL2Vec3 μ v) = v := by
  apply Lp.ext
  let xr := complexifyL2Vec3 μ (realPartL2Vec3 μ v)
  let xi := complexifyL2Vec3 μ (imagPartL2Vec3 μ v)
  filter_upwards [Lp.coeFn_add xr (Complex.I • xi), Lp.coeFn_smul Complex.I xi,
    complexifyL2Vec3_apply_ae μ (realPartL2Vec3 μ v),
    complexifyL2Vec3_apply_ae μ (imagPartL2Vec3 μ v),
    realPartL2Vec3_apply_ae μ v, imagPartL2Vec3_apply_ae μ v] with a h₁ h₂ h₃ h₄ h₅ h₆
  change (xr + Complex.I • xi) a = v a
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply]
  change xr a = _ at h₃
  change xi a = _ at h₄
  rw [h₃, h₄, h₅, h₆]
  apply PiLp.ext
  intro i
  change (periodicComplexifyVector (periodicRealPartVector (v a))) i +
    Complex.I * (periodicComplexifyVector (periodicImagPartVector (v a))) i = v a i
  simpa only [periodicComplexifyVector_apply, periodicRealPartVector_apply,
    periodicImagPartVector_apply, mul_comm Complex.I] using Complex.re_add_im (v a i)

@[simp] theorem realPartL2Vec3_I_smul (v : Lp ComplexEuclideanVec3 2 μ) :
    realPartL2Vec3 μ (Complex.I • v) = -imagPartL2Vec3 μ v := by
  apply Lp.ext
  filter_upwards [realPartL2Vec3_apply_ae μ (Complex.I • v), Lp.coeFn_smul Complex.I v,
    Lp.coeFn_neg (imagPartL2Vec3 μ v), imagPartL2Vec3_apply_ae μ v] with a h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply, Pi.neg_apply, h₄]
  apply PiLp.ext
  intro i
  change (periodicRealPartVector (Complex.I • v a)) i = -periodicImagPartVector (v a) i
  rw [periodicRealPartVector_apply, periodicImagPartVector_apply]
  change (Complex.I * v a i).re = -(v a i).im
  simp [Complex.mul_re]

@[simp] theorem imagPartL2Vec3_I_smul (v : Lp ComplexEuclideanVec3 2 μ) :
    imagPartL2Vec3 μ (Complex.I • v) = realPartL2Vec3 μ v := by
  apply Lp.ext
  filter_upwards [imagPartL2Vec3_apply_ae μ (Complex.I • v), Lp.coeFn_smul Complex.I v,
    realPartL2Vec3_apply_ae μ v] with a h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  apply PiLp.ext
  intro i
  change (periodicImagPartVector (Complex.I • v a)) i = periodicRealPartVector (v a) i
  rw [periodicImagPartVector_apply, periodicRealPartVector_apply]
  change (Complex.I * v a i).im = (v a i).re
  simp [Complex.mul_im]

private theorem norm_sq_L2Path_eq_integral {E : Type*} [NormedAddCommGroup E]
    (u : Lp E 2 μ) : ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- Squared norm is the sum of the squared real and imaginary path norms. -/
theorem norm_sq_real_imag_L2Vec3 (v : Lp ComplexEuclideanVec3 2 μ) :
    ‖v‖ ^ 2 = ‖realPartL2Vec3 μ v‖ ^ 2 + ‖imagPartL2Vec3 μ v‖ ^ 2 := by
  have hr := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (realPartL2Vec3 μ v))).mp
    (Lp.memLp (realPartL2Vec3 μ v))
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (imagPartL2Vec3 μ v))).mp
    (Lp.memLp (imagPartL2Vec3 μ v))
  rw [norm_sq_L2Path_eq_integral, norm_sq_L2Path_eq_integral,
    norm_sq_L2Path_eq_integral, ← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [realPartL2Vec3_apply_ae μ v, imagPartL2Vec3_apply_ae μ v] with a hra hia
  rw [hra, hia, norm_sq_real_imag_vector]

theorem norm_realPartL2Vec3_le (v : Lp ComplexEuclideanVec3 2 μ) :
    ‖realPartL2Vec3 μ v‖ ≤ ‖v‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_sq_real_imag_L2Vec3 μ v]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_imagPartL2Vec3_le (v : Lp ComplexEuclideanVec3 2 μ) :
    ‖imagPartL2Vec3 μ v‖ ≤ ‖v‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_sq_real_imag_L2Vec3 μ v]
  exact le_add_of_nonneg_left (sq_nonneg _)


/-- Complexification of the vector-valued L² paths with respect to any measure. -/
def endpointL2Complexification :
    EndpointComplexification (Lp Vec3 2 μ) (Lp ComplexEuclideanVec3 2 μ) where
  ofReal := complexifyL2Vec3 μ
  re := realPartL2Vec3 μ
  im := imagPartL2Vec3 μ
  re_ofReal := realPartL2Vec3_complexify μ
  im_ofReal := imagPartL2Vec3_complexify μ
  re_I := realPartL2Vec3_I_smul μ
  im_I := imagPartL2Vec3_I_smul μ
  reconstruct := complexifyL2Vec3_reconstruct μ
  norm_sq := norm_sq_real_imag_L2Vec3 μ

theorem norm_complexifyL2Vec3_eq (v : Lp Vec3 2 μ) :
    ‖complexifyL2Vec3 μ v‖ = ‖v‖ :=
  (endpointL2Complexification μ).norm_ofReal v

end L2Paths

abbrev EndpointRealTimeL2 (T : ℝ) := Lp Vec3 2 (volume.restrict (Ioc 0 T))
abbrev EndpointComplexTimeL2 (T : ℝ) := Lp ComplexEuclideanVec3 2 (volume.restrict (Ioc 0 T))

/-- Real-linear complex extension on the spatial coefficient operators. -/
def endpointComplexifySpatialOperator :
    (Vec3 →L[ℝ] Vec3) →L[ℝ] (ComplexEuclideanVec3 →L[ℂ] ComplexEuclideanVec3) :=
  endpointSpatialComplexification.extendOperatorCLM

/-- Real-linear complex extension on the coefficient operators of the mixed time-path space. -/
def endpointComplexifyTimeOperator (T : ℝ) :
    (EndpointRealTimeL2 T →L[ℝ] EndpointRealTimeL2 T) →L[ℝ]
      (EndpointComplexTimeL2 T →L[ℂ] EndpointComplexTimeL2 T) :=
  (endpointL2Complexification (volume.restrict (Ioc 0 T))).extendOperatorCLM

@[simp] theorem norm_endpointComplexifySpatialOperator (A : Vec3 →L[ℝ] Vec3) :
    ‖endpointComplexifySpatialOperator A‖ = ‖A‖ :=
  endpointSpatialComplexification.norm_extendOperator A

@[simp] theorem norm_endpointComplexifyTimeOperator (T : ℝ)
    (A : EndpointRealTimeL2 T →L[ℝ] EndpointRealTimeL2 T) :
    ‖endpointComplexifyTimeOperator T A‖ = ‖A‖ :=
  (endpointL2Complexification (volume.restrict (Ioc 0 T))).norm_extendOperator A

theorem norm_endpointComplexifySpatialOperator_le : ‖endpointComplexifySpatialOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul, norm_endpointComplexifySpatialOperator]

theorem norm_endpointComplexifyTimeOperator_le (T : ℝ) :
    ‖endpointComplexifyTimeOperator T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul, norm_endpointComplexifyTimeOperator]

@[simp] theorem endpointComplexifySpatialOperator_ofReal
    (A : Vec3 →L[ℝ] Vec3) (v : Vec3) :
    endpointComplexifySpatialOperator A (periodicComplexifyVector v) =
      periodicComplexifyVector (A v) :=
  endpointSpatialComplexification.extendOperator_ofReal A v

@[simp] theorem endpointComplexifySpatialOperator_re
    (A : Vec3 →L[ℝ] Vec3) (v : ComplexEuclideanVec3) :
    periodicRealPartVector (endpointComplexifySpatialOperator A v) = A (periodicRealPartVector v) :=
  endpointSpatialComplexification.re_extendOperator A v

@[simp] theorem endpointComplexifySpatialOperator_im
    (A : Vec3 →L[ℝ] Vec3) (v : ComplexEuclideanVec3) :
    periodicImagPartVector (endpointComplexifySpatialOperator A v) = A (periodicImagPartVector v) :=
  endpointSpatialComplexification.im_extendOperator A v

@[simp] theorem endpointComplexifyTimeOperator_ofReal (T : ℝ)
    (A : EndpointRealTimeL2 T →L[ℝ] EndpointRealTimeL2 T) (v : EndpointRealTimeL2 T) :
    endpointComplexifyTimeOperator T A (complexifyL2Vec3 (volume.restrict (Ioc 0 T)) v) =
      complexifyL2Vec3 (volume.restrict (Ioc 0 T)) (A v) :=
  (endpointL2Complexification (volume.restrict (Ioc 0 T))).extendOperator_ofReal A v

@[simp] theorem endpointComplexifyTimeOperator_re (T : ℝ)
    (A : EndpointRealTimeL2 T →L[ℝ] EndpointRealTimeL2 T) (v : EndpointComplexTimeL2 T) :
    realPartL2Vec3 (volume.restrict (Ioc 0 T)) (endpointComplexifyTimeOperator T A v) =
      A (realPartL2Vec3 (volume.restrict (Ioc 0 T)) v) :=
  (endpointL2Complexification (volume.restrict (Ioc 0 T))).re_extendOperator A v

@[simp] theorem endpointComplexifyTimeOperator_im (T : ℝ)
    (A : EndpointRealTimeL2 T →L[ℝ] EndpointRealTimeL2 T) (v : EndpointComplexTimeL2 T) :
    imagPartL2Vec3 (volume.restrict (Ioc 0 T)) (endpointComplexifyTimeOperator T A v) =
      A (imagPartL2Vec3 (volume.restrict (Ioc 0 T)) v) :=
  (endpointL2Complexification (volume.restrict (Ioc 0 T))).im_extendOperator A v

section RealFourierMoments

local notation "A" => UnitAddTorus (Fin 3)
local notation "ν" => unitTorusMeasure

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The real-character moment of the real part uses the two opposite complex
Fourier coefficients. This needs no reality assumption on the input field. -/
theorem realPart_fourierCoeff_pair (Re : E →L[ℝ] F) (f : C(A, E))
    (k : Fin 3 → ℤ) (c : ℂ) :
    (∫ a, (c * mFourier k a).re • Re (f a) ∂ν) =
      (2 : ℝ)⁻¹ • Re (c • mFourierCoeff f (-k) + conj c • mFourierCoeff f k) := by
  let g (a : A) := c • (mFourier k a • f a)
  let h (a : A) := conj c • (mFourier (-k) a • f a)
  have hg : Integrable g ν :=
    (continuous_const.smul ((mFourier k).continuous.smul f.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh : Integrable h ν :=
    (continuous_const.smul ((mFourier (-k)).continuous.smul f.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [mFourierCoeff, neg_neg]
  change _ = (2 : ℝ)⁻¹ • Re
    (c • (∫ a, mFourier k a • f a ∂ν) + conj c • (∫ a, mFourier (-k) a • f a ∂ν))
  rw [← integral_smul c, ← integral_smul (conj c)]
  change _ = (2 : ℝ)⁻¹ • Re ((∫ a, g a ∂ν) + ∫ a, h a ∂ν)
  rw [← integral_add hg hh]
  change _ = (2 : ℝ)⁻¹ • Re (∫ a, (g + h) a ∂ν)
  rw [← Re.integral_comp_comm (hg.add hh), ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    change _ = (2 : ℝ)⁻¹ • Re (g a + h a)
    have hsum : g a + h a = (2 * (c * mFourier k a).re : ℝ) • f a := by
      change (c • (mFourier k a • f a) + conj c • (mFourier (-k) a • f a)) = _
      rw [smul_smul, smul_smul, ← add_smul, mFourier_neg, ← map_mul, Complex.add_conj]
      exact IsScalarTower.algebraMap_smul (R := ℝ) (M := E) ℂ (2 * (c * mFourier k a).re) (f a)
    rw [hsum, map_smul, smul_smul]
    rw [show (2 : ℝ)⁻¹ * (2 * (c * mFourier k a).re) = (c * mFourier k a).re by ring]

/-- Paired complex-mode compatibility gives the real multiplier formula for
that character when the same real operator supplies both opposite modes. -/
theorem realPart_fourierCoeff_pair_transfer (Re : E →L[ℝ] F)
    (B : F →L[ℝ] F) (BC : E →L[ℂ] E) (hRe : ∀ z : E, Re (BC z) = B (Re z))
    (f g : C(A, E)) (k : Fin 3 → ℤ) (c : ℂ)
    (hneg : mFourierCoeff g (-k) = BC (mFourierCoeff f (-k)))
    (hpos : mFourierCoeff g k = BC (mFourierCoeff f k)) :
    (∫ a, (c * mFourier k a).re • Re (g a) ∂ν) =
      B (∫ a, (c * mFourier k a).re • Re (f a) ∂ν) := by
  rw [realPart_fourierCoeff_pair Re g, realPart_fourierCoeff_pair Re f, hneg, hpos,
    ← BC.map_smul c, ← BC.map_smul (conj c), ← map_add, hRe, map_smul]

end RealFourierMoments

end

end TorusEuler
