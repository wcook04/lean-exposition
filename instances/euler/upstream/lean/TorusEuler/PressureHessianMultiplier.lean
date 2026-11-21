import TorusEuler.HalfHolderFourierMultiplier
import TorusEuler.EndpointComplexification
import TorusEuler.AngularLeraySymbol
import TorusEuler.CutoffResidual
import TorusEuler.EndpointSmoothSlices
import TorusEuler.EulerAdvectionBounds

/-! The pressure Hessian multiplier in the proof of Proposition 5.11. -/

open ContinuousLinearMap MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "RealOp" => (Vec3 →L[ℝ] Vec3)
local notation "ComplexOp" => (ComplexEuclideanVec3 →L[ℂ] ComplexEuclideanVec3)

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- The rank-one angular projection onto the spatial frequency direction.
The zero mode vanishes. -/
def pressureHessianAngular (ξ : Vec3) : RealOp := 1 - angularLeray ξ

@[simp] theorem pressureHessianAngular_zero : pressureHessianAngular 0 = 0 := by
  simp [pressureHessianAngular]

@[simp] theorem pressureHessianAngular_neg (ξ : Vec3) :
    pressureHessianAngular (-ξ) = pressureHessianAngular ξ := by
  simp [pressureHessianAngular]

theorem pressureHessianAngular_pos_smul {c : ℝ} (hc : 0 < c) (ξ : Vec3) :
    pressureHessianAngular (c • ξ) = pressureHessianAngular ξ := by
  simp [pressureHessianAngular, angularLeray_pos_smul hc]

theorem pressureHessianAngular_apply (ξ v : Vec3) :
    pressureHessianAngular ξ v = (⟪ξ, v⟫_ℝ / ‖ξ‖ ^ 2) • ξ := by
  change v - angularLeray ξ v = _
  rw [angularLeray_apply, sub_sub_cancel]

private theorem contDiffOn_pressureHessianAngular :
    ContDiffOn ℝ ∞ pressureHessianAngular ({0}ᶜ : Set Vec3) := by
  have h : ContDiffOn ℝ ∞ (fun _ : Vec3 => (1 : RealOp)) ({0}ᶜ : Set Vec3) :=
    contDiffOn_const
  exact h.sub contDiffOn_angularLeray

/-- The complex symbol of D² Δ⁻¹, taking a scalar coefficient to a Hessian. -/
def pressureHessianSymbol (ξ : Vec3) : ℂ →L[ℂ] ComplexOp :=
  toSpanSingleton ℂ (endpointComplexifySpatialOperator (pressureHessianAngular ξ))

theorem pressureHessianSymbol_apply (ξ : Vec3) (s : ℂ) :
    pressureHessianSymbol ξ s = s • endpointComplexifySpatialOperator (pressureHessianAngular ξ) :=
  rfl

@[simp] theorem pressureHessianSymbol_zero : pressureHessianSymbol 0 = 0 := by
  simp [pressureHessianSymbol]

@[simp] theorem pressureHessianSymbol_neg (ξ : Vec3) :
    pressureHessianSymbol (-ξ) = pressureHessianSymbol ξ := by
  simp [pressureHessianSymbol]

theorem pressureHessianSymbol_pos_smul (c : ℝ) (hc : 0 < c) (ξ : Vec3) :
    pressureHessianSymbol (c • ξ) = pressureHessianSymbol ξ := by
  rw [pressureHessianSymbol, pressureHessianAngular_pos_smul hc]
  rfl

theorem contDiffOn_pressureHessianSymbol :
    ContDiffOn ℝ ∞ pressureHessianSymbol ({0}ᶜ : Set Vec3) := by
  let L : ComplexOp →L[ℝ] (ℂ →L[ℂ] ComplexOp) :=
    ((toSpanSingletonLIE ℂ ComplexOp).toContinuousLinearMap).restrictScalars ℝ
  have hL : ContDiff ℝ ∞ (⇑L) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ComplexOp) (F := ℂ →L[ℂ] ComplexOp) L
  have hC : ContDiff ℝ ∞ (⇑endpointComplexifySpatialOperator) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := RealOp) (F := ComplexOp) endpointComplexifySpatialOperator
  exact hL.comp_contDiffOn (hC.comp_contDiffOn contDiffOn_pressureHessianAngular)

private theorem pressureHessianAngular_lattice_apply (k : Fin 3 → ℤ) (i j : Fin 3) :
    pressureHessianAngular (latticeVector k) (EuclideanSpace.single j 1) i =
      ((k j : ℝ) / frequencyNormSq k) * (k i : ℝ) := by
  rw [pressureHessianAngular_apply, EuclideanSpace.inner_single_right]
  have hnorm : ‖latticeVector k‖ ^ 2 = frequencyNormSq k := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hnorm]
  simp [latticeVector]

private theorem periodicComplexifyVector_single_one (j : Fin 3) :
    periodicComplexifyVector (EuclideanSpace.single j (1 : ℝ)) =
      EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro l
  by_cases hl : l = j <;> simp [hl]

/-- At every integer frequency the symbol is exactly the second derivative of the
mean-zero inverse Laplacian, including the zero mode. -/
theorem pressureHessianSymbol_lattice_apply (k : Fin 3 → ℤ) (s : ℂ) (i j : Fin 3) :
    (pressureHessianSymbol (latticeVector k) s (EuclideanSpace.single j 1)) i =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * inverseLaplacianMode k * s := by
  rw [pressureHessianSymbol_apply, _root_.smul_apply, ← periodicComplexifyVector_single_one,
    endpointComplexifySpatialOperator_ofReal]
  change s * ((pressureHessianAngular (latticeVector k) (EuclideanSpace.single j 1) i : ℝ) : ℂ) = _
  rw [pressureHessianAngular_lattice_apply]
  by_cases hk : k = 0
  · subst k
    simp [fourierDerivativeSymbol]
  · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hn : (frequencyNormSq k : ℂ) ≠ 0 := by
      exact_mod_cast (frequencyNormSq_pos hk).ne'
    have hprod : fourierDerivativeSymbol k i * fourierDerivativeSymbol k j =
        -(2 * (Real.pi : ℂ)) ^ 2 * (k i : ℂ) * (k j : ℂ) := by
      unfold fourierDerivativeSymbol
      calc
        _ = (2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2 * (k i : ℂ) * (k j : ℂ) := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    rw [hprod, inverseLaplacianMode, laplacianMode]
    push_cast
    field_simp

/-- Restrict a complex operator to real input and take the real part of its output. -/
def realSpatialOperatorPart : ComplexOp →L[ℝ] RealOp :=
  (((compL ℝ Vec3 ComplexEuclideanVec3 Vec3).flip periodicComplexifyVector).comp
    ((compL ℝ ComplexEuclideanVec3 ComplexEuclideanVec3 Vec3) periodicRealPartVector)).comp
    (restrictScalarsL ℂ ComplexEuclideanVec3 ComplexEuclideanVec3 ℝ ℝ)

theorem realSpatialOperatorPart_apply (A : ComplexOp) (v : Vec3) :
    realSpatialOperatorPart A v = periodicRealPartVector (A (periodicComplexifyVector v)) := rfl

theorem norm_realSpatialOperatorPart_le : ‖realSpatialOperatorPart‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [realSpatialOperatorPart_apply]
  have h (z : ComplexEuclideanVec3) : ‖periodicRealPartVector z‖ ≤ ‖z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    have hn := endpointSpatialComplexification.norm_sq z
    change ‖z‖ ^ 2 = ‖periodicRealPartVector z‖ ^ 2 + ‖periodicImagPartVector z‖ ^ 2 at hn
    rw [hn]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (h _).trans ((A.le_opNorm _).trans_eq
    (congrArg (‖A‖ * ·) (endpointSpatialComplexification.norm_ofReal v)))

theorem realSpatialOperatorPart_pressureHessianSymbol (ξ : Vec3) (s : ℂ) :
    realSpatialOperatorPart (pressureHessianSymbol ξ s) = s.re • pressureHessianAngular ξ := by
  apply ContinuousLinearMap.ext
  intro v
  rw [realSpatialOperatorPart_apply, pressureHessianSymbol_apply, _root_.smul_apply,
    endpointComplexifySpatialOperator_ofReal]
  apply PiLp.ext
  intro i
  change (s * (pressureHessianAngular ξ v i : ℂ)).re = s.re * pressureHessianAngular ξ v i
  simp [Complex.mul_re]

/-- The bounded complex periodic Hessian multiplier. -/
def complexPressureHessianMultiplier : HalfHolder Labels ℂ →L[ℝ] HalfHolder Labels ComplexOp :=
  homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero contDiffOn_pressureHessianSymbol

/-- The real scalar-source to real Hessian multiplier on the periodic half-Hölder spaces. -/
def pressureHessianMultiplier : HalfHolder Labels ℝ →L[ℝ] HalfHolder Labels RealOp :=
  (HalfHolder.map realSpatialOperatorPart).comp
    (complexPressureHessianMultiplier.comp (HalfHolder.map Complex.ofRealCLM))

theorem mFourierCoeff_complexPressureHessianMultiplier (f : HalfHolder Labels ℂ) (k : Fin 3 → ℤ) :
    mFourierCoeff (continuousHalfHolder (complexPressureHessianMultiplier f)) k =
      pressureHessianSymbol (latticeVector k) (mFourierCoeff (continuousHalfHolder f) k) :=
  mFourierCoeff_homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero contDiffOn_pressureHessianSymbol
    (fun c hc ξ _ => pressureHessianSymbol_pos_smul c hc ξ) f k

/-- The real multiplier acts on each real cosine/sine moment by the real pressure Hessian symbol. -/
theorem pressureHessianMultiplier_realFourier (f : HalfHolder Labels ℝ)
    (k : Fin 3 → ℤ) (c : ℂ) :
    (∫ a, (c * mFourier k a).re • HalfHolder.eval a (pressureHessianMultiplier f) ∂unitTorusMeasure) =
      (∫ a, (c * mFourier k a).re * HalfHolder.eval a f ∂unitTorusMeasure) •
        pressureHessianAngular (latticeVector k) := by
  let fC := HalfHolder.map Complex.ofRealCLM f
  let gC := complexPressureHessianMultiplier fC
  let f' := continuousHalfHolder fC
  let g' := continuousHalfHolder gC
  have hlattice : latticeVector (-k) = -latticeVector k := by
    apply PiLp.ext
    intro i
    exact Int.cast_neg (k i)
  change (∫ a, (c * mFourier k a).re •
      HalfHolder.eval a (HalfHolder.map realSpatialOperatorPart gC) ∂unitTorusMeasure) = _
  simp only [HalfHolder.eval_map]
  change (∫ a, (c * mFourier k a).re • realSpatialOperatorPart (g' a) ∂unitTorusMeasure) = _
  have hf : ∀ a : Labels, Complex.reCLM (f' a) = HalfHolder.eval a f := by
    intro a
    change Complex.reCLM (HalfHolder.eval a (HalfHolder.map Complex.ofRealCLM f)) = _
    rw [HalfHolder.eval_map]
    rfl
  have hB := realPart_fourierCoeff_pair Complex.reCLM f' k c
  simp only [hf] at hB
  have hpos := mFourierCoeff_complexPressureHessianMultiplier fC k
  have hneg := mFourierCoeff_complexPressureHessianMultiplier fC (-k)
  change mFourierCoeff g' k = pressureHessianSymbol (latticeVector k) (mFourierCoeff f' k) at hpos
  change mFourierCoeff g' (-k) = pressureHessianSymbol (latticeVector (-k)) (mFourierCoeff f' (-k)) at hneg
  rw [hlattice, pressureHessianSymbol_neg] at hneg
  rw [realPart_fourierCoeff_pair realSpatialOperatorPart g', hneg, hpos,
    ← (pressureHessianSymbol (latticeVector k)).map_smul c,
    ← (pressureHessianSymbol (latticeVector k)).map_smul (conj c), ← map_add,
    realSpatialOperatorPart_pressureHessianSymbol, smul_smul]
  have hB' : (∫ a, (c * mFourier k a).re * HalfHolder.eval a f ∂unitTorusMeasure) =
      (2 : ℝ)⁻¹ * (c • mFourierCoeff f' (-k) + conj c • mFourierCoeff f' k).re := hB
  rw [← hB']

/-- The periodic pressure Hessian difference is bounded by its scalar source in the same norm. -/
theorem norm_pressureHessianMultiplier_apply_le (f : HalfHolder Labels ℝ) :
    ‖pressureHessianMultiplier f‖ ≤ ‖pressureHessianMultiplier‖ * ‖f‖ :=
  pressureHessianMultiplier.le_opNorm f

section CutoffSource

private abbrev VelocityGradient := Vec3 →L[ℝ] Vec3

private def pressureTraceCLM : VelocityGradient →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp
    (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))

private theorem pressureTraceCLM_apply (D : VelocityGradient) :
    pressureTraceCLM D = LinearMap.trace ℝ Vec3 D.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [pressureTraceCLM, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

private theorem norm_pressureTraceCLM_le : ‖pressureTraceCLM‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro D
  have h (i : Fin 3) : ‖(D (EuclideanSpace.single i 1)) i‖ ≤ ‖D‖ := by
    calc
      ‖(D (EuclideanSpace.single i 1)) i‖ ≤ ‖D (EuclideanSpace.single i 1)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ ‖D‖ * ‖(EuclideanSpace.single i 1 : Vec3)‖ := D.le_opNorm _
      _ = ‖D‖ := by simp [EuclideanSpace.single]
  simp only [pressureTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  calc
    ‖∑ i : Fin 3, (D (EuclideanSpace.single i 1)) i‖ ≤
        ∑ i : Fin 3, ‖(D (EuclideanSpace.single i 1)) i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖D‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖D‖ := by simp [nsmul_eq_mul]

variable {X : Type*} [MetricSpace X]

private theorem gradientProduct_bounds (U V : HalfHolder X VelocityGradient) :
    (∀ x, ‖HalfHolder.eval x U * HalfHolder.eval x V‖ ≤ 2 * ‖U‖ * ‖V‖) ∧
    ∀ x y, ‖HalfHolder.eval x U * HalfHolder.eval x V -
        HalfHolder.eval y U * HalfHolder.eval y V‖ ≤
      (2 * ‖U‖ * ‖V‖) * Real.sqrt (dist x y) := by
  obtain ⟨hU, hUh⟩ := (HalfHolder.norm_le_iff (norm_nonneg U)).mp (le_refl _)
  obtain ⟨hV, hVh⟩ := (HalfHolder.norm_le_iff (norm_nonneg V)).mp (le_refl _)
  change (∀ x, ‖HalfHolder.eval x U‖ ≤ ‖U‖) at hU
  change (∀ x, ‖HalfHolder.eval x V‖ ≤ ‖V‖) at hV
  change (∀ x y, ‖HalfHolder.eval x U - HalfHolder.eval y U‖ ≤
    ‖U‖ * Real.sqrt (dist x y)) at hUh
  change (∀ x y, ‖HalfHolder.eval x V - HalfHolder.eval y V‖ ≤
    ‖V‖ * Real.sqrt (dist x y)) at hVh
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · calc
      ‖HalfHolder.eval x U * HalfHolder.eval x V‖ ≤ ‖U‖ * ‖V‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul (hU x) (hV x) (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := by
        nlinarith [mul_nonneg (norm_nonneg U) (norm_nonneg V)]
  · let u := HalfHolder.eval x U
    let u' := HalfHolder.eval y U
    let v := HalfHolder.eval x V
    let v' := HalfHolder.eval y V
    let δ := Real.sqrt (dist x y)
    change ‖u * v - u' * v'‖ ≤ (2 * ‖U‖ * ‖V‖) * δ
    have hsplit : u * v - u' * v' = (u - u') * v + u' * (v - v') := by
      rw [sub_mul, mul_sub]
      abel
    rw [hsplit]
    calc
      ‖(u - u') * v + u' * (v - v')‖ ≤ ‖(u - u') * v‖ + ‖u' * (v - v')‖ := norm_add_le _ _
      _ ≤ (‖U‖ * δ) * ‖V‖ + ‖U‖ * (‖V‖ * δ) := add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul (hUh x y) (hV x)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))
        ((norm_mul_le _ _).trans (mul_le_mul (hU y) (hVh x y)
          (norm_nonneg _) (norm_nonneg _)))
      _ = _ := by ring

private def halfHolderGradientProduct (U V : HalfHolder X VelocityGradient) :
    HalfHolder X VelocityGradient :=
  HalfHolder.ofBound
    ⟨fun x => HalfHolder.eval x U * HalfHolder.eval x V,
      U.val.1.continuous.mul V.val.1.continuous⟩
    (gradientProduct_bounds U V).1 (gradientProduct_bounds U V).2

@[simp] private theorem eval_halfHolderGradientProduct (U V : HalfHolder X VelocityGradient)
    (x : X) : HalfHolder.eval x (halfHolderGradientProduct U V) =
      HalfHolder.eval x U * HalfHolder.eval x V := rfl

private theorem norm_halfHolderGradientProduct_le (U V : HalfHolder X VelocityGradient) :
    ‖halfHolderGradientProduct U V‖ ≤ 2 * ‖U‖ * ‖V‖ := by
  apply (HalfHolder.norm_le_iff (by positivity)).mpr
  exact gradientProduct_bounds U V

/-- The pressure-source trace difference formed from the two cutoff gradients. -/
def pressureTraceSquareDifference (U V : HalfHolder X VelocityGradient) : HalfHolder X ℝ :=
  HalfHolder.map pressureTraceCLM (halfHolderGradientProduct U U - halfHolderGradientProduct V V)

theorem pressureTraceSquareDifference_eval (U V : HalfHolder X VelocityGradient) (x : X) :
    HalfHolder.eval x (pressureTraceSquareDifference U V) =
      LinearMap.trace ℝ Vec3 (HalfHolder.eval x U * HalfHolder.eval x U).toLinearMap -
        LinearMap.trace ℝ Vec3 (HalfHolder.eval x V * HalfHolder.eval x V).toLinearMap := by
  simp only [pressureTraceSquareDifference, HalfHolder.eval_map, map_sub,
    eval_halfHolderGradientProduct, pressureTraceCLM_apply]

/-- The exact trace-square comparison for the cutoff error D = U - V. -/
theorem pressureTraceSquareDifference_eq (U V : HalfHolder X VelocityGradient)
    (D : HalfHolder X VelocityGradient) (hD : D = U - V) :
    pressureTraceSquareDifference U V =
      HalfHolder.map pressureTraceCLM
        (halfHolderGradientProduct D V + halfHolderGradientProduct U D) := by
  subst D
  apply HalfHolder.ext
  intro x
  simp only [pressureTraceSquareDifference, HalfHolder.eval_map, map_sub, map_add,
    eval_halfHolderGradientProduct, sub_mul, mul_sub]
  abel

theorem pressureTraceSquareDifference_eval_cutoff (U V D : HalfHolder X VelocityGradient)
    (hD : D = U - V) (x : X) :
    HalfHolder.eval x (pressureTraceSquareDifference U V) =
      LinearMap.trace ℝ Vec3 (HalfHolder.eval x D * HalfHolder.eval x V).toLinearMap +
        LinearMap.trace ℝ Vec3 (HalfHolder.eval x U * HalfHolder.eval x D).toLinearMap := by
  rw [pressureTraceSquareDifference_eq U V D hD]
  simp only [HalfHolder.eval_map, map_add, eval_halfHolderGradientProduct, pressureTraceCLM_apply]

/-- The pressure-source error is controlled in the same half-Hölder norm
by the cutoff gradient error and the two parent gradient bounds. -/
theorem norm_pressureTraceSquareDifference_le (U V D : HalfHolder X VelocityGradient)
    (hD : D = U - V) :
    ‖pressureTraceSquareDifference U V‖ ≤ 6 * ‖D‖ * (‖U‖ + ‖V‖) := by
  rw [pressureTraceSquareDifference_eq U V D hD]
  let W := halfHolderGradientProduct D V + halfHolderGradientProduct U D
  have hW : ‖W‖ ≤ 2 * ‖D‖ * ‖V‖ + 2 * ‖U‖ * ‖D‖ :=
    (norm_add_le _ _).trans (add_le_add
      (norm_halfHolderGradientProduct_le D V) (norm_halfHolderGradientProduct_le U D))
  change ‖(HalfHolder.map pressureTraceCLM) W‖ ≤ _
  calc
    _ ≤ 3 * ‖W‖ := (HalfHolder.map pressureTraceCLM).le_of_opNorm_le
      ((HalfHolder.norm_map_le pressureTraceCLM).trans norm_pressureTraceCLM_le) W
    _ ≤ 3 * (2 * ‖D‖ * ‖V‖ + 2 * ‖U‖ * ‖D‖) := mul_le_mul_of_nonneg_left hW (by norm_num)
    _ = _ := by ring

end CutoffSource

/-- The source of the pressure difference in Proposition 5.11. The real
operator fields are the two velocity gradients and the residual gradient. -/
def cutoffPressureDifferenceSource (U V DR : HalfHolder Labels RealOp) : HalfHolder Labels ℝ :=
  -pressureTraceSquareDifference U V - HalfHolder.map pressureTraceCLM DR

theorem cutoffPressureDifferenceSource_eval (U V DR : HalfHolder Labels RealOp) (a : Labels) :
    HalfHolder.eval a (cutoffPressureDifferenceSource U V DR) =
      -(LinearMap.trace ℝ Vec3 (HalfHolder.eval a U * HalfHolder.eval a U).toLinearMap -
        LinearMap.trace ℝ Vec3 (HalfHolder.eval a V * HalfHolder.eval a V).toLinearMap) -
        LinearMap.trace ℝ Vec3 (HalfHolder.eval a DR).toLinearMap := by
  simp only [cutoffPressureDifferenceSource, map_sub, map_neg, HalfHolder.eval_map,
    pressureTraceCLM_apply, pressureTraceSquareDifference_eval]

/-- The pressure Hessian contribution to (5.57), with the actual order-zero multiplier
and the half-Hölder source comparison. -/
theorem norm_cutoffPressureHessian_le (U V D DR : HalfHolder Labels RealOp) (hD : D = U - V) :
    ‖pressureHessianMultiplier (cutoffPressureDifferenceSource U V DR)‖ ≤
      ‖pressureHessianMultiplier‖ * (6 * ‖D‖ * (‖U‖ + ‖V‖) + 3 * ‖DR‖) := by
  apply (pressureHessianMultiplier.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hR : ‖HalfHolder.map pressureTraceCLM DR‖ ≤ 3 * ‖DR‖ :=
    (HalfHolder.map pressureTraceCLM).le_of_opNorm_le
      ((HalfHolder.norm_map_le pressureTraceCLM).trans norm_pressureTraceCLM_le) DR
  exact (norm_sub_le _ _).trans
    (add_le_add ((norm_neg _).trans_le (norm_pressureTraceSquareDifference_le U V D hD)) hR)

section PressurePoisson

private theorem integral_real_coordinate_deriv_centeredCell_eq_zero
    {f : Vec3 → ℝ} (hf : ContDiff ℝ 1 f) (hper : SpatiallyPeriodic f) (i : Fin 3) :
    (∫ x in centeredCell, fderiv ℝ f x (EuclideanSpace.single i 1)) = 0 := by
  let e : Vec3 := EuclideanSpace.single i 1
  have hdiv (x : Vec3) : divergence (fun y => f y • e) x = fderiv ℝ f x e := by
    unfold divergence
    rw [((hf.differentiable (by simp) x).hasFDerivAt.smul_const e).fderiv]
    simp only [ContinuousLinearMap.smulRight_apply]
    rw [Finset.sum_eq_single i]
    · simp [e, PiLp.smul_apply]
    · intro j _ hji
      simp [e, PiLp.smul_apply, hji]
    · simp
  have hp : SpatiallyPeriodic (fun y => f y • e) := by
    intro n x
    change f (x + latticeVector n) • e = f x • e
    rw [hper n x]
  have h := integral_divergence_centeredCell_eq_zero (hf.smul contDiff_const) hp
  change (∫ x in centeredCell, divergence (fun y => f y • e) x) = 0 at h
  simpa only [hdiv, e] using h

private theorem integral_complex_coordinate_deriv_centeredCell_eq_zero
    {f : Vec3 → ℂ} (hf : ContDiff ℝ 1 f) (hper : SpatiallyPeriodic f) (i : Fin 3) :
    (∫ x in centeredCell, fderiv ℝ f x (EuclideanSpace.single i 1)) = 0 := by
  let e : Vec3 := EuclideanSpace.single i 1
  have hd : Continuous (fun x => fderiv ℝ f x e) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : IntegrableOn (fun x => fderiv ℝ f x e) centeredCell :=
    hd.continuousOn.integrableOn_compact isCompact_centeredCell
  have hproj (L : ℂ →L[ℝ] ℝ) :
      L (∫ x in centeredCell, fderiv ℝ f x e) = 0 := by
    have hdL (x : Vec3) :
        fderiv ℝ (L ∘ f) x e = L (fderiv ℝ f x e) := by
      rw [fderiv_comp x L.differentiableAt (hf.differentiable (by simp) x),
        ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    have hpL : SpatiallyPeriodic (L ∘ f) := by
      intro n x
      exact congrArg L (hper n x)
    rw [← L.integral_comp_comm hI]
    simp_rw [← hdL]
    exact integral_real_coordinate_deriv_centeredCell_eq_zero (L.contDiff.comp hf) hpL i
  apply Complex.ext
  · exact hproj Complex.reCLM
  · exact hproj Complex.imCLM

private theorem fourierDerivativeSymbol_neg (k : Fin 3 → ℤ) (i : Fin 3) :
    fourierDerivativeSymbol (-k) i = -fourierDerivativeSymbol k i := by
  simp [fourierDerivativeSymbol]

private theorem periodicCoordinateDeriv
    {f : Vec3 → ℂ} (hf : Differentiable ℝ f) (hper : SpatiallyPeriodic f) (i : Fin 3) :
    SpatiallyPeriodic (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
  fun n x => congrArg (fun D : Vec3 →L[ℝ] ℂ => D (EuclideanSpace.single i 1)) (hper.fderiv hf n x)

/-- Periodic integration by parts transfers a spatial derivative to its Fourier symbol. -/
theorem centeredCell_fourier_coordinate_deriv {f : Vec3 → ℂ}
    (hf : ContDiff ℝ 1 f) (hper : SpatiallyPeriodic f) (k : Fin 3 → ℤ) (i : Fin 3) :
    (∫ x in centeredCell, fourierMode (-k) x * fderiv ℝ f x (EuclideanSpace.single i 1)) =
      fourierDerivativeSymbol k i * (∫ x in centeredCell, fourierMode (-k) x * f x) := by
  let e : Vec3 := EuclideanSpace.single i 1
  let a : ℂ := fourierDerivativeSymbol k i
  let w := fourierMode (-k)
  have hw : ContDiff ℝ 1 w := (contDiff_fourierMode (-k)).of_le (by simp)
  have hperw : SpatiallyPeriodic w := spatiallyPeriodic_fourierMode _
  have hperprod : SpatiallyPeriodic (fun x => w x * f x) := by
    intro n x
    change w (x + latticeVector n) * f (x + latticeVector n) = w x * f x
    rw [hperw n x, hper n x]
  have hderiv (x : Vec3) :
      fderiv ℝ (fun y => w y * f y) x e =
        w x * fderiv ℝ f x e - a * (w x * f x) := by
    have hp := ((hw.differentiable (by simp) x).hasFDerivAt.mul
      (hf.differentiable (by simp) x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => w y * f y) x = _ at hp
    rw [hp]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have hmode : fderiv ℝ w x e = -a * w x := by
      exact (fderiv_fourierMode_single (-k) x i).trans
        (congrArg (fun b : ℂ => b * fourierMode (-k) x) (fourierDerivativeSymbol_neg k i))
    rw [hmode]
    ring
  have hI1 : IntegrableOn (fun x => w x * fderiv ℝ f x e) centeredCell :=
    (hw.continuous.mul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn.integrableOn_compact
      isCompact_centeredCell
  have hI2 : IntegrableOn (fun x => a * (w x * f x)) centeredCell :=
    (continuous_const.mul (hw.continuous.mul hf.continuous)).continuousOn.integrableOn_compact
      isCompact_centeredCell
  have h := integral_complex_coordinate_deriv_centeredCell_eq_zero (hw.mul hf) hperprod i
  change (∫ x in centeredCell, fderiv ℝ (fun y => w y * f y) x e) = 0 at h
  simp_rw [hderiv] at h
  rw [integral_sub hI1 hI2, integral_const_mul] at h
  exact sub_eq_zero.mp h

/-- The second spatial derivative of a smooth periodic scalar has two Fourier factors. -/
theorem centeredCell_fourier_coordinate_hessian {f : Vec3 → ℂ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f) (k : Fin 3 → ℤ) (i j : Fin 3) :
    (∫ x in centeredCell, fourierMode (-k) x *
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j *
        (∫ x in centeredCell, fourierMode (-k) x * f x) := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf₂ : ContDiff ℝ 1 (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  rw [centeredCell_fourier_coordinate_deriv hf₂ (periodicCoordinateDeriv
      (hf₁.differentiable (by simp)) hper j),
    centeredCell_fourier_coordinate_deriv hf₁ hper, mul_assoc]

/-- The torus Fourier coefficient of a represented coordinate Hessian of a smooth periodic lift. -/
theorem mFourierCoeff_coordinate_hessian {f : Vec3 → ℂ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f)
    (g h : C(UnitAddTorus (Fin 3), ℂ)) (i j : Fin 3)
    (hg : ∀ x, g (toUnitTorus x) = f x)
    (hh : ∀ x, h (toUnitTorus x) =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1))
    (k : Fin 3 → ℤ) :
    mFourierCoeff h k = fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * mFourierCoeff g k := by
  simp_rw [fourierCoeff_eq_centeredCell, hg, hh, smul_eq_mul]
  exact centeredCell_fourier_coordinate_hessian hf hper k i j

/-- The trace of the coordinate Hessian has the Laplacian Fourier symbol. -/
theorem centeredCell_fourier_laplacian {f : Vec3 → ℂ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f) (k : Fin 3 → ℤ) :
    (∫ x in centeredCell, fourierMode (-k) x *
      (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1))) =
      laplacianMode k * (∫ x in centeredCell, fourierMode (-k) x * f x) := by
  have hInt (i : Fin 3) : IntegrableOn
      (fun x => fourierMode (-k) x * fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)) centeredCell := by
    have hc : ContDiff ℝ 1 (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (((contDiff_fourierMode (-k)).continuous.mul
      ((hc.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn).integrableOn_compact
      isCompact_centeredCell
  have hs : (∑ i : Fin 3, fourierDerivativeSymbol k i * fourierDerivativeSymbol k i) =
      laplacianMode k := by
    simpa only [divergenceMode, gradientMode, mul_one] using divergenceMode_gradientMode k 1
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  simp_rw [centeredCell_fourier_coordinate_hessian hf hper, ← Finset.sum_mul, hs]

private theorem fderiv_ofReal_comp_apply {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (e : Vec3) :
    fderiv ℝ (fun y => (f y : ℂ)) x e = (fderiv ℝ f x e : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y : ℂ)) x = _ at h
  rw [h]
  rfl

private theorem coordinate_hessian_ofReal {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vec3) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z : ℂ)) y (EuclideanSpace.single j 1))
        x (EuclideanSpace.single i 1) =
      (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1))
        x (EuclideanSpace.single i 1) : ℂ) := by
  have hj : (fun y => fderiv ℝ (fun z => (f z : ℂ)) y (EuclideanSpace.single j 1)) =
      fun y => (fderiv ℝ f y (EuclideanSpace.single j 1) : ℂ) := by
    funext y
    exact fderiv_ofReal_comp_apply (hf.differentiable (by norm_num) y) _
  have hc : ContDiff ℝ 1 (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  rw [hj, fderiv_ofReal_comp_apply (hc.differentiable (by simp) x)]

/-- Fourier coefficients of a real coordinate Hessian after complexification. -/
theorem mFourierCoeff_real_coordinate_hessian {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f)
    (g h : C(UnitAddTorus (Fin 3), ℝ)) (i j : Fin 3)
    (hg : ∀ x, g (toUnitTorus x) = f x)
    (hh : ∀ x, h (toUnitTorus x) =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1))
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun a => (h a : ℂ)) k =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j *
        mFourierCoeff (fun a => (g a : ℂ)) k := by
  have hper' : SpatiallyPeriodic (fun z => (f z : ℂ)) := by
    intro n x
    exact congrArg Complex.ofReal (hper n x)
  have hc : ContDiff ℝ 2 (fun z => (f z : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hfourier := centeredCell_fourier_coordinate_hessian hc hper' k i j
  simp_rw [fourierCoeff_eq_centeredCell, hg, hh, smul_eq_mul]
  simpa only [coordinate_hessian_ofReal hf] using hfourier

/-- Fourier coefficients of a real Laplacian after complexification. -/
theorem mFourierCoeff_real_laplacian {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f)
    (g q : C(UnitAddTorus (Fin 3), ℝ))
    (hg : ∀ x, g (toUnitTorus x) = f x)
    (hq : ∀ x, q (toUnitTorus x) =
      ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1))
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun a => (q a : ℂ)) k =
      laplacianMode k * mFourierCoeff (fun a => (g a : ℂ)) k := by
  have hper' : SpatiallyPeriodic (fun z => (f z : ℂ)) := by
    intro n x
    exact congrArg Complex.ofReal (hper n x)
  have hc : ContDiff ℝ 2 (fun z => (f z : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hfourier := centeredCell_fourier_laplacian hc hper' k
  simp_rw [fourierCoeff_eq_centeredCell, hg, hq, smul_eq_mul, Complex.ofReal_sum]
  simpa only [coordinate_hessian_ofReal hf] using hfourier

/-- The coordinate of the derivative of the gradient is the corresponding mixed derivative. -/
theorem fderiv_gradient_single_coord {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vec3) (i j : Fin 3) :
    (fderiv ℝ (gradient f) x (EuclideanSpace.single i 1)) j =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
  let P : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj j
  have hd : DifferentiableAt ℝ (gradient f) x :=
    (((InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
      (hf.fderiv_right (m := 1) (by norm_num))).differentiable (by simp)) x
  have hfun : P ∘ gradient f = fun y => fderiv ℝ f y (EuclideanSpace.single j 1) := by
    funext y
    change (gradient f y) j = _
    calc
      (gradient f y) j = ⟪gradient f y, EuclideanSpace.single j 1⟫_ℝ := by
        rw [EuclideanSpace.inner_single_right]
        simp
      _ = _ := inner_gradient_left
  rw [← hfun, fderiv_comp x P.differentiableAt hd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- Fourier characterization of a real pressure Hessian from its Laplacian
source, including the zero mode. -/
theorem mFourierCoeff_real_hessian_eq_inverseLaplacian {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hper : SpatiallyPeriodic f)
    (p h q : C(UnitAddTorus (Fin 3), ℝ)) (i j : Fin 3)
    (hp : ∀ x, p (toUnitTorus x) = f x)
    (hh : ∀ x, h (toUnitTorus x) =
      (fderiv ℝ (gradient f) x (EuclideanSpace.single i 1)) j)
    (hq : ∀ x, q (toUnitTorus x) = divergence (gradient f) x)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun a => (h a : ℂ)) k =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * inverseLaplacianMode k *
        mFourierCoeff (fun a => (q a : ℂ)) k := by
  have hh' (x : Vec3) : h (toUnitTorus x) =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) :=
    (hh x).trans (fderiv_gradient_single_coord hf x i j)
  have hq' (x : Vec3) : q (toUnitTorus x) =
      ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single l 1))
        x (EuclideanSpace.single l 1) := by
    rw [hq, divergence]
    exact Finset.sum_congr rfl fun l _ => fderiv_gradient_single_coord hf x l l
  rw [mFourierCoeff_real_coordinate_hessian hf hper p h i j hp hh',
    mFourierCoeff_real_laplacian hf hper p q hp hq']
  by_cases hk : k = 0
  · subst k
    simp [fourierDerivativeSymbol]
  · rw [inverseLaplacianMode]
    rw [← mul_assoc, mul_assoc
      (fourierDerivativeSymbol k i * fourierDerivativeSymbol k j),
      inv_mul_cancel₀ (laplacianMode_ne_zero hk), mul_one]


private def realHessianEntry (i j : Fin 3) : RealOp →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))

private def complexHessianEntry (i j : Fin 3) : ComplexOp →L[ℂ] ℂ :=
  (EuclideanSpace.proj j).comp
    (ContinuousLinearMap.apply ℂ ComplexEuclideanVec3 (EuclideanSpace.single i 1))

private theorem mFourierCoeff_complexHessianEntry (F : C(Labels, ComplexOp))
    (k : Fin 3 → ℤ) (i j : Fin 3) :
    mFourierCoeff (fun a => complexHessianEntry i j (F a)) k =
      complexHessianEntry i j (mFourierCoeff F k) := by
  have h : Integrable (fun a => mFourier (-k) a • F a) unitTorusMeasure :=
    ((mFourier (-k)).continuous.smul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ a, mFourier (-k) a • complexHessianEntry i j (F a) ∂unitTorusMeasure) =
    complexHessianEntry i j (∫ a, mFourier (-k) a • F a ∂unitTorusMeasure)
  rw [← (complexHessianEntry i j).integral_comp_comm h]
  simp only [map_smul]

private theorem mFourierCoeff_realInput (f : HalfHolder Labels ℝ) (k : Fin 3 → ℤ) :
    mFourierCoeff (continuousHalfHolder (HalfHolder.map Complex.ofRealCLM f)) k =
      mFourierCoeff (fun b => Complex.ofReal (HalfHolder.eval b f)) k := by
  apply congrArg (fun F : Labels → ℂ => mFourierCoeff F k)
  funext b
  change HalfHolder.eval b (HalfHolder.map Complex.ofRealCLM f) = _
  rw [HalfHolder.eval_map]
  rfl

private theorem mFourierCoeff_complexPressureHessianEntry (f : HalfHolder Labels ℝ)
    (k : Fin 3 → ℤ) (i j : Fin 3) :
    mFourierCoeff (fun b => complexHessianEntry i j
      (continuousHalfHolder (complexPressureHessianMultiplier (HalfHolder.map Complex.ofRealCLM f)) b)) k =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * inverseLaplacianMode k *
        mFourierCoeff (fun b => Complex.ofReal (HalfHolder.eval b f)) k := by
  rw [mFourierCoeff_complexHessianEntry, mFourierCoeff_complexPressureHessianMultiplier]
  change (pressureHessianSymbol (latticeVector k)
    (mFourierCoeff (continuousHalfHolder (HalfHolder.map Complex.ofRealCLM f)) k)
      (EuclideanSpace.single i 1)) j = _
  rw [pressureHessianSymbol_lattice_apply, mul_comm (fourierDerivativeSymbol k j),
    mFourierCoeff_realInput]

private def complexPressureHessianLift (f : HalfHolder Labels ℝ) : C(Labels, ComplexOp) :=
  continuousHalfHolder (complexPressureHessianMultiplier (HalfHolder.map Complex.ofRealCLM f))

private def realHessianEntryLift (H : HalfHolder Labels RealOp) (i j : Fin 3) : C(Labels, ℝ) := by
  have hH : Continuous (fun b : Labels => HalfHolder.eval b H) := H.val.1.continuous
  exact ⟨fun a => realHessianEntry i j (HalfHolder.eval a H),
    (realHessianEntry i j).continuous.comp hH⟩

set_option maxHeartbeats 750000 in
private theorem complexPressureHessianEntry_eq_of_periodicPoisson (f : HalfHolder Labels ℝ)
    {pLift : Vec3 → ℝ} (hp : ContDiff ℝ 2 pLift) (hper : SpatiallyPeriodic pLift)
    (p h : C(Labels, ℝ)) (i j : Fin 3)
    (hpRep : ∀ x, p (toUnitTorus x) = pLift x)
    (hh : ∀ x, h (toUnitTorus x) =
      (fderiv ℝ (gradient pLift) x (EuclideanSpace.single i 1)) j)
    (hpoisson : ∀ x, HalfHolder.eval (toUnitTorus x) f = divergence (gradient pLift) x)
    (a : Labels) :
    complexHessianEntry i j (complexPressureHessianLift f a) = Complex.ofReal (h a) := by
  let z := complexPressureHessianLift f
  let L := complexHessianEntry i j
  let g : C(Labels, ℂ) := ⟨fun b => L (z b), L.continuous.comp z.continuous⟩
  let h' : C(Labels, ℂ) := ⟨fun b => Complex.ofReal (h b),
    Complex.continuous_ofReal.comp h.continuous⟩
  let q : C(Labels, ℝ) := f.val.1.toContinuousMap
  have hq (x : Vec3) : q (toUnitTorus x) = divergence (gradient pLift) x := hpoisson x
  have heq : g = h' := by
    apply eq_of_mFourierCoeff_eq
    intro k
    change mFourierCoeff (fun b => L (z b)) k = mFourierCoeff (fun b => Complex.ofReal (h b)) k
    calc
      _ = fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * inverseLaplacianMode k *
          mFourierCoeff (fun b => Complex.ofReal (HalfHolder.eval b f)) k :=
        mFourierCoeff_complexPressureHessianEntry f k i j
      _ = _ := (mFourierCoeff_real_hessian_eq_inverseLaplacian hp hper p h
        q i j hpRep hh hq k).symm
  exact DFunLike.congr_fun heq a

private theorem eval_pressureHessianMultiplier_entry (f : HalfHolder Labels ℝ)
    (a : Labels) (i j : Fin 3) :
    (HalfHolder.eval a (pressureHessianMultiplier f) (EuclideanSpace.single i 1)) j =
      (complexHessianEntry i j (complexPressureHessianLift f a)).re := by
  change (HalfHolder.eval a (HalfHolder.map realSpatialOperatorPart
      (complexPressureHessianMultiplier (HalfHolder.map Complex.ofRealCLM f)))
        (EuclideanSpace.single i 1)) j = _
  rw [HalfHolder.eval_map, realSpatialOperatorPart_apply, periodicComplexifyVector_single_one,
    periodicRealPartVector_apply]
  rfl

/-- If a periodic pressure solves the Poisson equation, the actual Hessian equals
the real half-Hölder pressure multiplier of its scalar Laplacian source. -/
theorem pressureHessianMultiplier_eq_of_periodicPoisson
    (f : HalfHolder Labels ℝ) (H : HalfHolder Labels RealOp) {pLift : Vec3 → ℝ}
    (hp : ContDiff ℝ 2 pLift) (hper : SpatiallyPeriodic pLift) (p : C(Labels, ℝ))
    (hpRep : ∀ x, p (toUnitTorus x) = pLift x)
    (hH : ∀ x, HalfHolder.eval (toUnitTorus x) H = fderiv ℝ (gradient pLift) x)
    (hpoisson : ∀ x, HalfHolder.eval (toUnitTorus x) f = divergence (gradient pLift) x) :
    pressureHessianMultiplier f = H := by
  apply HalfHolder.ext
  intro a
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro i
  apply PiLp.ext
  intro j
  let h := realHessianEntryLift H i j
  have hh (x : Vec3) : h (toUnitTorus x) =
      (fderiv ℝ (gradient pLift) x (EuclideanSpace.single i 1)) j := by
    change realHessianEntry i j (HalfHolder.eval (toUnitTorus x) H) = _
    rw [hH]
    rfl
  have heq := complexPressureHessianEntry_eq_of_periodicPoisson
    f hp hper p h i j hpRep hh hpoisson a
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (HalfHolder.eval a (pressureHessianMultiplier f) (EuclideanSpace.single i 1)) j =
    (HalfHolder.eval a H (EuclideanSpace.single i 1)) j
  rw [eval_pressureHessianMultiplier_entry, heq, Complex.ofReal_re]
  rfl

/-- The pressure estimate of Proposition 5.11 on a periodic slice, for the actual
Hessian of the pressure difference with the cutoff source. -/
theorem norm_cutoffPressureHessian_of_periodicPoisson_le
    (U V D DR H : HalfHolder Labels RealOp) (hD : D = U - V)
    {pLift : Vec3 → ℝ} (hp : ContDiff ℝ 2 pLift) (hper : SpatiallyPeriodic pLift)
    (p : C(Labels, ℝ)) (hpRep : ∀ x, p (toUnitTorus x) = pLift x)
    (hH : ∀ x, HalfHolder.eval (toUnitTorus x) H = fderiv ℝ (gradient pLift) x)
    (hpoisson : ∀ x, HalfHolder.eval (toUnitTorus x) (cutoffPressureDifferenceSource U V DR) =
      divergence (gradient pLift) x) :
    ‖H‖ ≤ ‖pressureHessianMultiplier‖ * (6 * ‖D‖ * (‖U‖ + ‖V‖) + 3 * ‖DR‖) := by
  rw [← pressureHessianMultiplier_eq_of_periodicPoisson _ H hp hper p hpRep hH hpoisson]
  exact norm_cutoffPressureHessian_le U V D DR hD

private theorem divergence_fun_add_pressureSlice {F G : Vec3 → Vec3} {x : Vec3}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y + G y) x = divergence F x + divergence G x := by
  simp only [divergence, fderiv_fun_add hF hG, _root_.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

private theorem divergence_fun_sub_pressureSlice {F G : Vec3 → Vec3} {x : Vec3}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y - G y) x = divergence F x - divergence G x := by
  simp only [divergence, fderiv_fun_sub hF hG, _root_.sub_apply, PiLp.sub_apply,
    Finset.sum_sub_distrib]

/-- Subtracting the pressure Poisson equations on one spatial slice gives
the scalar source for the cutoff pressure difference. -/
theorem divergence_gradient_cutoffPressureDifference
    {u V W R : Vec3 → Vec3} {p pi : Vec3 → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : ContDiff ℝ 2 p) (hpi : ContDiff ℝ 2 pi)
    (hdivV : ∀ x, divergence V x = 0)
    (hP : ∀ x, divergence (gradient p) x =
      -LinearMap.trace ℝ Vec3 ((fderiv ℝ u x).comp (fderiv ℝ u x)).toLinearMap)
    (hR : ∀ x, W x + fderiv ℝ V x (V x) + gradient pi x = R x)
    (x : Vec3) (hW : DifferentiableAt ℝ W x) (hdivW : divergence W x = 0) :
    divergence (gradient (fun y => p y - pi y)) x =
      -(LinearMap.trace ℝ Vec3 ((fderiv ℝ u x).comp (fderiv ℝ u x)).toLinearMap -
        LinearMap.trace ℝ Vec3 ((fderiv ℝ V x).comp (fderiv ℝ V x)).toLinearMap) -
      divergence R x := by
  let adv (y : Vec3) := fderiv ℝ V y (V y)
  have hA : DifferentiableAt ℝ adv x :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).clm_apply
      (hV.differentiable (by norm_num) x)
  have hdiffGrad (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f) :
      DifferentiableAt ℝ (gradient f) x :=
    (((InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
      (hf.fderiv_right (m := 1) (by norm_num))).differentiable (by norm_num) x)
  have hGradSub : gradient (fun y => p y - pi y) =
      (fun y => gradient p y - gradient pi y) := by
    funext y
    unfold gradient
    rw [fderiv_fun_sub (hp.differentiable (by norm_num) y)
      (hpi.differentiable (by norm_num) y), map_sub]
  have hMomentum : (fun y => W y + adv y + gradient pi y) = R := funext hR
  have hDiv : divergence R x =
      LinearMap.trace ℝ Vec3 ((fderiv ℝ V x).comp (fderiv ℝ V x)).toLinearMap +
        divergence (gradient pi) x := by
    have hWA : DifferentiableAt ℝ (fun y => W y + adv y) x := hW.add hA
    rw [← hMomentum, divergence_fun_add_pressureSlice hWA (hdiffGrad pi hpi),
      divergence_fun_add_pressureSlice hW hA, hdivW, zero_add]
    exact congrArg (fun y => y + divergence (gradient pi) x)
      (divergence_advection_eq_trace_square hV hdivV x)
  rw [hGradSub, divergence_fun_sub_pressureSlice (hdiffGrad p hp) (hdiffGrad pi hpi), hP]
  linarith

/-- The cutoff pressure estimate with the scalar source obtained from the
divergence-free momentum slice and pressure equation. -/
theorem norm_cutoffPressureHessian_of_residual_le
    (U V DR H : HalfHolder Labels RealOp)
    {u v w R : Vec3 → Vec3} {p pi : Vec3 → ℝ}
    (hv : ContDiff ℝ 2 v) (hp : ContDiff ℝ 2 p) (hpi : ContDiff ℝ 2 pi)
    (hper : SpatiallyPeriodic (fun x => p x - pi x))
    (pDiff : C(Labels, ℝ)) (hpDiff : ∀ x, pDiff (toUnitTorus x) = p x - pi x)
    (huRep : ∀ x, HalfHolder.eval (toUnitTorus x) U = fderiv ℝ u x)
    (hvRep : ∀ x, HalfHolder.eval (toUnitTorus x) V = fderiv ℝ v x)
    (hDR : ∀ x, HalfHolder.eval (toUnitTorus x) DR = fderiv ℝ R x)
    (hH : ∀ x, HalfHolder.eval (toUnitTorus x) H =
      fderiv ℝ (gradient (fun y => p y - pi y)) x)
    (hdivV : ∀ x, divergence v x = 0) (hw : Differentiable ℝ w)
    (hdivW : ∀ x, divergence w x = 0)
    (hP : ∀ x, divergence (gradient p) x =
      -LinearMap.trace ℝ Vec3 ((fderiv ℝ u x).comp (fderiv ℝ u x)).toLinearMap)
    (hR : ∀ x, w x + fderiv ℝ v x (v x) + gradient pi x = R x) :
    ‖H‖ ≤ ‖pressureHessianMultiplier‖ * (6 * ‖U - V‖ * (‖U‖ + ‖V‖) + 3 * ‖DR‖) := by
  apply norm_cutoffPressureHessian_of_periodicPoisson_le U V (U - V) DR H rfl
    (hp.sub hpi) hper pDiff hpDiff hH
  intro x
  rw [cutoffPressureDifferenceSource_eval, huRep, hvRep, hDR, ← divergence_eq_trace_fderiv]
  exact (divergence_gradient_cutoffPressureDifference hv hp hpi hdivV hP hR x
    (hw x) (hdivW x)).symm

end PressurePoisson

end

end TorusEuler
