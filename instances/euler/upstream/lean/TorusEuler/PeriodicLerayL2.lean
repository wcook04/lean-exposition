import TorusEuler.PeriodicMultiplierBounds
import TorusEuler.EndpointSpaceCompatibility

/-! The Leray projection on the complex spatial L² space in Appendix A. -/

open MeasureTheory UnitAddTorus
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace TorusEuler

noncomputable section

private abbrev Frequency := Fin 3 → ℤ

abbrev ComplexEuclideanVec3 := EuclideanSpace ℂ (Fin 3)

abbrev PeriodicComplexL2 := Lp ComplexEuclideanVec3 2 unitTorusMeasure

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- Insert a coefficient at a single Fourier mode in spatial L². -/
def periodicL2Mode (k : Frequency) : ComplexEuclideanVec3 →L[ℂ] PeriodicComplexL2 :=
  let lift := ContinuousLinearMap.compLpL₂ 2 unitTorusMeasure
    (ContinuousLinearMap.toSpanSingletonLIE ℂ ComplexEuclideanVec3).toContinuousLinearMap
  lift.flip (mFourierLp 2 k)

theorem periodicL2Mode_apply_ae (k : Frequency) (a : ComplexEuclideanVec3) :
    periodicL2Mode k a =ᵐ[unitTorusMeasure] fun z => mFourier k z • a := by
  let f : Lp ℂ 2 unitTorusMeasure := mFourierLp 2 k
  have hχ : f =ᵐ[unitTorusMeasure] mFourier k := coeFn_mFourierLp 2 k
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ a).coeFn_compLp f, hχ] with z h hz
  change ((ContinuousLinearMap.toSpanSingleton ℂ a).compLp f) z = _
  exact h.trans (congrArg (fun c : ℂ => c • a) hz)

private theorem inner_periodicL2Mode_mode (k j : Frequency) (a b : ComplexEuclideanVec3) :
    ⟪periodicL2Mode k a, periodicL2Mode j b⟫_ℂ = if k = j then ⟪a, b⟫_ℂ else 0 := by
  classical
  rw [L2.inner_def]
  calc
    _ = ∫ z, (mFourier (-k) z * mFourier j z) * ⟪a, b⟫_ℂ ∂unitTorusMeasure := by
      apply integral_congr_ae
      filter_upwards [periodicL2Mode_apply_ae k a, periodicL2Mode_apply_ae j b] with z hk hj
      rw [hk, hj, inner_smul_left, inner_smul_right, ← mFourier_neg, mul_assoc]
    _ = _ := by
      rw [integral_mul_const, integral_fourier_pair]
      split <;> simp_all

private def longitudinalMode (k : Frequency) : ComplexEuclideanVec3 :=
  WithLp.toLp 2 (complexFrequency k)

private def periodicLongitudinalSpan : Submodule ℂ PeriodicComplexL2 :=
  Submodule.span ℂ (Set.range fun k => periodicL2Mode k (longitudinalMode k))

/-- The closed subspace orthogonal to every longitudinal Fourier mode. -/
def periodicComplexSolenoidal : Submodule ℂ PeriodicComplexL2 :=
  periodicLongitudinalSpanᗮ

theorem mem_periodicComplexSolenoidal (u : PeriodicComplexL2) :
    u ∈ periodicComplexSolenoidal ↔
      ∀ k : Frequency, ⟪periodicL2Mode k (WithLp.toLp 2 (complexFrequency k)), u⟫_ℂ = 0 := by
  change u ∈ periodicLongitudinalSpanᗮ ↔
    ∀ k : Frequency, ⟪periodicL2Mode k (longitudinalMode k), u⟫_ℂ = 0
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h k
    exact h _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro h x hx
    have hle : periodicLongitudinalSpan ≤ (ℂ ∙ u)ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h k)
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hx)

private instance : periodicComplexSolenoidal.HasOrthogonalProjection := by
  unfold periodicComplexSolenoidal
  infer_instance

/-- Orthogonal Leray projection on all complex periodic L² velocity fields. -/
def periodicComplexLeray : PeriodicComplexL2 →L[ℂ] PeriodicComplexL2 :=
  periodicComplexSolenoidal.starProjection

theorem norm_periodicComplexLeray_le : ‖periodicComplexLeray‖ ≤ 1 :=
  periodicComplexSolenoidal.starProjection_norm_le

theorem range_periodicComplexLeray : periodicComplexLeray.range = periodicComplexSolenoidal :=
  periodicComplexSolenoidal.range_starProjection

theorem inner_periodicComplexLeray_left_eq_right (u v : PeriodicComplexL2) :
    ⟪periodicComplexLeray u, v⟫_ℂ = ⟪u, periodicComplexLeray v⟫_ℂ :=
  periodicComplexSolenoidal.inner_starProjection_left_eq_right u v

/-- The all-field projection acts by the verified Leray symbol at each Fourier mode. -/
theorem periodicComplexLeray_mode (k : Frequency) (a : ComplexEuclideanVec3) :
    periodicComplexLeray (periodicL2Mode k a) =
      periodicL2Mode k (lerayModeProjection k a) := by
  classical
  change periodicComplexSolenoidal.starProjection _ = _
  apply Submodule.eq_starProjection_of_mem_orthogonal (K := periodicComplexSolenoidal)
  · rw [mem_periodicComplexSolenoidal]
    intro j
    rw [inner_periodicL2Mode_mode]
    by_cases h : j = k
    · subst j
      simp only [ite_true]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.mem_span_singleton_self (longitudinalMode k))
        ((transverseModeSpace k).starProjection_apply_mem a)
    · simp [h]
  · rw [← map_sub]
    apply periodicLongitudinalSpan.le_orthogonal_orthogonal
    have hcomp : a - lerayModeProjection k a ∈ ℂ ∙ longitudinalMode k := by
      have h := (transverseModeSpace k).sub_starProjection_mem_orthogonal a
      change a - lerayModeProjection k a ∈ (ℂ ∙ longitudinalMode k)ᗮᗮ at h
      rwa [Submodule.orthogonal_orthogonal] at h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hcomp
    rw [← hc, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The Fourier coefficient map on spatial L², expressed as the adjoint of insertion. -/
def periodicL2Coefficient (k : Frequency) : PeriodicComplexL2 →L[ℂ] ComplexEuclideanVec3 :=
  (periodicL2Mode k).adjoint

private theorem integrable_fourier_smul (k : Frequency) (u : PeriodicComplexL2) :
    Integrable (fun z => mFourier k z • u z) unitTorusMeasure := by
  have hu := (Lp.memLp u).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact hu.bdd_smul 1 (mFourier k).continuous.aestronglyMeasurable
    (ae_of_all _ fun z =>
      ((mFourier k).norm_coe_le_norm z).trans (show ‖mFourier k‖ ≤ 1 from mFourier_norm.le))

theorem periodicL2Coefficient_eq_mFourierCoeff (k : Frequency) (u : PeriodicComplexL2) :
    periodicL2Coefficient k u = mFourierCoeff u k := by
  apply ext_inner_left ℂ
  intro a
  rw [periodicL2Coefficient, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  have hI := integrable_fourier_smul (-k) u
  change _ = innerSL ℂ a (∫ z, mFourier (-k) z • u z ∂unitTorusMeasure)
  rw [← (innerSL ℂ a).integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [periodicL2Mode_apply_ae k a] with z hz
  rw [hz, inner_smul_left, innerSL_apply_apply, inner_smul_right, mFourier_neg]

/-- The Leray projection acts by the Leray symbol on every L² Fourier coefficient. -/
theorem periodicL2Coefficient_leray (k : Frequency) (u : PeriodicComplexL2) :
    periodicL2Coefficient k (periodicComplexLeray u) =
      lerayModeProjection k (periodicL2Coefficient k u) := by
  apply ext_inner_left ℂ
  intro a
  rw [← inner_lerayModeProjection_left_eq_right, periodicL2Coefficient,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← inner_periodicComplexLeray_left_eq_right, periodicComplexLeray_mode]

theorem mem_periodicComplexSolenoidal_iff_coeff (u : PeriodicComplexL2) :
    u ∈ periodicComplexSolenoidal ↔
      ∀ k : Frequency, periodicL2Coefficient k u ∈ transverseModeSpace k := by
  rw [mem_periodicComplexSolenoidal]
  apply forall_congr'
  intro k
  change _ ↔ periodicL2Coefficient k u ∈ (ℂ ∙ longitudinalMode k)ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, periodicL2Coefficient,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

section RealWeakSolenoidal

/-- A real scalar component of a complex Fourier character. -/
noncomputable def endpointFourierPotential (L : ℂ →L[ℝ] ℝ) (k : Fin 3 → ℤ) :
    EndpointSmoothPotential where
  lift := L ∘ fourierMode k
  smooth := L.contDiff.comp (contDiff_fourierMode k)
  periodic := fun n x => congrArg L (spatiallyPeriodic_fourierMode k n x)

theorem endpointPotentialGradient_fourierPotential (L : ℂ →L[ℝ] ℝ)
    (k : Fin 3 → ℤ) (a : UnitAddTorus (Fin 3)) :
    endpointPotentialGradient (endpointFourierPotential L k) a =
      L ((2 * (Real.pi : ℂ) * Complex.I) * mFourier k a) • latticeVector k := by
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
  rw [endpointPotentialGradient_toUnitTorus]
  apply PiLp.ext
  intro i
  have hg (p : Vec3 → ℝ) :
      (gradient p x) i = fderiv ℝ p x (EuclideanSpace.single i 1) := by
    calc
      (gradient p x) i = ⟪gradient p x, EuclideanSpace.single i 1⟫_ℝ := by
        rw [EuclideanSpace.inner_single_right]
        simp
      _ = _ := inner_gradient_left
  rw [hg]
  change fderiv ℝ (L ∘ fourierMode k) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x L.differentiableAt ((contDiff_fourierMode k).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    fderiv_fourierMode_single]
  have hs : fourierDerivativeSymbol k i * fourierMode k x =
      (k i : ℝ) • ((2 * (Real.pi : ℂ) * Complex.I) * fourierMode k x) := by
    rw [Complex.real_smul, Complex.ofReal_intCast]
    unfold fourierDerivativeSymbol
    ring
  rw [hs, map_smul]
  change (k i : ℝ) * L ((2 * (Real.pi : ℂ) * Complex.I) * fourierMode k x) = _
  change _ = L ((2 * (Real.pi : ℂ) * Complex.I) * fourierMode k x) * (k i : ℝ)
  exact mul_comm _ _

/-- The longitudinal scalar Fourier coefficient of a weakly solenoidal
real L² field vanishes at each integer frequency. -/
theorem mFourierCoeff_inner_latticeVector_eq_zero_of_solenoidal
    (v : Lp Vec3 2 unitTorusMeasure) (hv : v ∈ endpointSpatialSolenoidal)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun a => (⟪latticeVector k, v a⟫_ℝ : ℂ)) k = 0 := by
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let g (a : UnitAddTorus (Fin 3)) : ℂ := (⟪latticeVector k, v a⟫_ℝ : ℝ)
  let w (a : UnitAddTorus (Fin 3)) : ℂ := C * (mFourier (-k) a * g a)
  have hg : Integrable g unitTorusMeasure :=
    (Complex.ofRealCLM.comp (innerSL ℝ (latticeVector k))).integrable_comp
      ((Lp.memLp v).integrable (by norm_num))
  have hχ : ∀ a : UnitAddTorus (Fin 3), ‖mFourier (-k) a‖ = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact norm_fourierMode (-k) x
  have hw : Integrable w unitTorusMeasure :=
    (hg.bdd_mul (mFourier (-k)).continuous.aestronglyMeasurable
      (ae_of_all _ fun a => (hχ a).le)).const_mul C
  have hvneg : latticeVector (-k) = -latticeVector k := by
    apply PiLp.ext
    intro i
    exact Int.cast_neg (k i)
  have hL (L : ℂ →L[ℝ] ℝ) : L (∫ a, w a ∂unitTorusMeasure) = 0 := by
    have htest := (mem_endpointSpatialSolenoidal v).mp hv (endpointFourierPotential L (-k))
    rw [← L.integral_comp_comm hw]
    have hpoint (a : UnitAddTorus (Fin 3)) :
        L (w a) = -⟪endpointPotentialGradient (endpointFourierPotential L (-k)) a, v a⟫_ℝ := by
      rw [endpointPotentialGradient_fourierPotential, hvneg, smul_neg, inner_neg_left, neg_neg,
        real_inner_smul_left]
      change L (C * (mFourier (-k) a * g a)) = L (C * mFourier (-k) a) * ⟪latticeVector k, v a⟫_ℝ
      have hfactor : C * (mFourier (-k) a * g a) =
          ⟪latticeVector k, v a⟫_ℝ • (C * mFourier (-k) a) := by
        simp only [g, Complex.real_smul]
        ring
      rw [hfactor, map_smul]
      exact mul_comm _ _
    rw [integral_congr_ae (ae_of_all _ hpoint), integral_neg, htest, neg_zero]
  have hzero : (∫ a, w a ∂unitTorusMeasure) = 0 := by
    apply Complex.ext
    · exact hL Complex.reCLM
    · exact hL Complex.imCLM
  change (∫ a, mFourier (-k) a * g a ∂unitTorusMeasure) = 0
  have hCn : C ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  apply (mul_eq_zero.mp ?_).resolve_left hCn
  simpa only [w, integral_const_mul] using hzero


/-- Coordinatewise complexification of the real Euclidean spatial vector. -/
def periodicComplexifyVector : Vec3 →L[ℝ] ComplexEuclideanVec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap fun _ : Fin 3 => Complex.ofRealCLM).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)

@[simp] theorem periodicComplexifyVector_apply (v : Vec3) (i : Fin 3) :
    periodicComplexifyVector v i = (v i : ℂ) := rfl

/-- The canonical real-linear embedding into the complex spatial L² space. -/
def periodicComplexifyL2 : Lp Vec3 2 unitTorusMeasure →L[ℝ] PeriodicComplexL2 :=
  periodicComplexifyVector.compLpL 2 unitTorusMeasure

theorem periodicComplexifyL2_apply_ae (v : Lp Vec3 2 unitTorusMeasure) :
    periodicComplexifyL2 v =ᵐ[unitTorusMeasure] fun a => periodicComplexifyVector (v a) :=
  periodicComplexifyVector.coeFn_compLpL v

private theorem inner_longitudinalMode_complexify (k : Frequency) (v : Vec3) :
    ⟪longitudinalMode k, periodicComplexifyVector v⟫_ℂ =
      (⟪latticeVector k, v⟫_ℝ : ℂ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [longitudinalMode, complexFrequency, latticeVector, RCLike.inner_apply, mul_comm]

/-- Real weak solenoidality implies that the complexified field lies in the
range of the all-field Fourier Leray projection. -/
theorem periodicComplexifyL2_mem_solenoidal_of_endpointSpatialSolenoidal
    (v : Lp Vec3 2 unitTorusMeasure) (hv : v ∈ endpointSpatialSolenoidal) :
    periodicComplexifyL2 v ∈ periodicComplexSolenoidal := by
  rw [mem_periodicComplexSolenoidal]
  intro k
  change ⟪periodicL2Mode k (longitudinalMode k), periodicComplexifyL2 v⟫_ℂ = 0
  rw [L2.inner_def]
  calc
    _ = mFourierCoeff (fun a => (⟪latticeVector k, v a⟫_ℝ : ℂ)) k := by
      change _ = ∫ a, mFourier (-k) a * (⟪latticeVector k, v a⟫_ℝ : ℂ) ∂unitTorusMeasure
      apply integral_congr_ae
      filter_upwards [periodicL2Mode_apply_ae k (longitudinalMode k),
        periodicComplexifyL2_apply_ae v] with a hmode hv'
      rw [hmode, hv', inner_smul_left, ← mFourier_neg, inner_longitudinalMode_complexify]
    _ = 0 := mFourierCoeff_inner_latticeVector_eq_zero_of_solenoidal v hv k

end RealWeakSolenoidal

end

end TorusEuler
