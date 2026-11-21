import TorusEuler.PressureHessianMultiplier
import TorusEuler.EndpointCoefficientCompatibility
import TorusEuler.TruncatedParentPoissonPressure
import TorusEuler.SmoothPeriodicHolder

/-! The pressure Poisson equation for the Eulerian mean in Proposition 5.10. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Gradient" => (Vec3 →L[ℝ] Vec3)

private theorem divergence_add_meanPressure {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  simp only [divergence_eq_trace_fderiv, fderiv_add hf hg, ContinuousLinearMap.toLinearMap_add, map_add]

private theorem contDiff_one_crossAdvection {F G : Vec3 → Vec3}
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 1 (fun x => fderiv ℝ F x (G x)) :=
  (hF.fderiv_right (m := 1) (by norm_num)).clm_apply (hG.of_le (by norm_num))

/-- The divergence of the two linearized advection terms is twice the mixed gradient trace. -/
theorem divergence_linearizedAdvection_eq_two_trace {U V : Vec3 → Vec3}
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hUdiv : ∀ x, divergence U x = 0) (hVdiv : ∀ x, divergence V x = 0) (x : Vec3) :
    divergence ((fun y => fderiv ℝ V y (U y)) + (fun y => fderiv ℝ U y (V y))) x =
      2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ U x).comp (fderiv ℝ V x)).toLinearMap := by
  let A := fun y => fderiv ℝ U y (U y)
  let B := fun y => fderiv ℝ V y (V y)
  let C := (fun y => fderiv ℝ V y (U y)) + (fun y => fderiv ℝ U y (V y))
  let DU := fderiv ℝ U x
  let DV := fderiv ℝ V x
  have hUg := hU.differentiable (by norm_num)
  have hVg := hV.differentiable (by norm_num)
  have hA : ContDiff ℝ 1 A := contDiff_one_crossAdvection hU hU
  have hB : ContDiff ℝ 1 B := contDiff_one_crossAdvection hV hV
  have hC : ContDiff ℝ 1 C := (contDiff_one_crossAdvection hV hU).add (contDiff_one_crossAdvection hU hV)
  have hdiv (y : Vec3) : divergence (U + V) y = 0 := by
    rw [divergence_add_meanPressure (hUg y) (hVg y), hUdiv, hVdiv, add_zero]
  have hpolarize : (fun y => fderiv ℝ (U + V) y ((U + V) y)) = (A + B) + C := by
    funext y
    rw [fderiv_add (hUg y) (hVg y)]
    simp only [A, B, C, Pi.add_apply, _root_.add_apply, map_add]
    abel
  have htotal := divergence_advection_eq_trace_square (show ContDiff ℝ 2 (U + V) from hU.add hV) hdiv x
  rw [hpolarize, divergence_add_meanPressure
    (show DifferentiableAt ℝ (A + B) x from (hA.differentiable (by simp) x).add (hB.differentiable (by simp) x))
    (hC.differentiable (by simp) x), divergence_add_meanPressure (hA.differentiable (by simp) x)
      (hB.differentiable (by simp) x), fderiv_add (hUg x) (hVg x)] at htotal
  have htrace : LinearMap.trace ℝ Vec3 ((DU + DV).comp (DU + DV)).toLinearMap =
      LinearMap.trace ℝ Vec3 (DU.comp DU).toLinearMap +
        LinearMap.trace ℝ Vec3 (DV.comp DV).toLinearMap +
        2 * LinearMap.trace ℝ Vec3 (DU.comp DV).toLinearMap := by
    change LinearMap.trace ℝ Vec3 ((DU.toLinearMap + DV.toLinearMap).comp
      (DU.toLinearMap + DV.toLinearMap)) =
        LinearMap.trace ℝ Vec3 (DU.toLinearMap.comp DU.toLinearMap) +
        LinearMap.trace ℝ Vec3 (DV.toLinearMap.comp DV.toLinearMap) +
        2 * LinearMap.trace ℝ Vec3 (DU.toLinearMap.comp DV.toLinearMap)
    simp only [LinearMap.add_comp, LinearMap.comp_add, map_add]
    rw [LinearMap.trace_comp_comm' DU.toLinearMap DV.toLinearMap]
    ring
  change divergence A x + divergence B x + divergence C x =
    LinearMap.trace ℝ Vec3 ((DU + DV).comp (DU + DV)).toLinearMap at htotal
  change divergence C x = 2 * LinearMap.trace ℝ Vec3 (DU.comp DV).toLinearMap
  rw [htrace, divergence_advection_eq_trace_square hU hUdiv x,
      divergence_advection_eq_trace_square hV hVdiv x] at htotal
  linarith only [htotal]

/-- The exact Poisson equation for the mean pressure, obtained by taking the
spatial divergence of the Eulerian linearized momentum equation. -/
theorem divergence_gradient_meanPressure_of_linearizedMomentum
    {U V W f : Vec3 → Vec3} {q : Vec3 → ℝ}
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V) (hW : Differentiable ℝ W) (hq : ContDiff ℝ 2 q)
    (hUdiv : ∀ x, divergence U x = 0) (hVdiv : ∀ x, divergence V x = 0)
    (hWdiv : ∀ x, divergence W x = 0)
    (hMom : ∀ x, W x + fderiv ℝ V x (U x) + fderiv ℝ U x (V x) + gradient q x = f x)
    (x : Vec3) :
    divergence (gradient q) x = divergence f x -
      2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ U x).comp (fderiv ℝ V x)).toLinearMap := by
  let A := (fun y => fderiv ℝ V y (U y)) + (fun y => fderiv ℝ U y (V y))
  have hA : ContDiff ℝ 1 A := (contDiff_one_crossAdvection hV hU).add (contDiff_one_crossAdvection hU hV)
  have hG : ContDiff ℝ 1 (gradient q) := (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
    (hq.fderiv_right (m := 1) (by norm_num))
  have hEq : W + A + gradient q = f := by
    funext y
    change W y + (fderiv ℝ V y (U y) + fderiv ℝ U y (V y)) + gradient q y = f y
    exact (by rw [← add_assoc]; exact hMom y)
  have hd := congrArg (fun F : Vec3 → Vec3 => divergence F x) hEq
  rw [divergence_add_meanPressure ((hW x).add (hA.differentiable (by simp) x))
      (hG.differentiable (by simp) x), divergence_add_meanPressure (hW x) (hA.differentiable (by simp) x),
    hWdiv x, zero_add, show divergence A x = 2 * LinearMap.trace ℝ Vec3
      ((fderiv ℝ U x).comp (fderiv ℝ V x)).toLinearMap from
      divergence_linearizedAdvection_eq_two_trace hU hV hUdiv hVdiv x] at hd
  linarith only [hd]

private theorem contDiff_meanPressure_slice {T t : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω} {F : ℝ → Vec3 → E}
    (hF : ContDiffOn ℝ n (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ n (F t) :=
  contDiffOn_univ.mp (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun x _ => ⟨ht, mem_univ x⟩)

/-- The Eulerian mean pressure Poisson equation holds on the whole closed slab,
with the time derivative taken within the slab. -/
theorem meanPressure_poisson_closedSlab {T : ℝ} (hT : 0 < T)
    {U V f : Velocity} {q : Pressure}
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hq : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (q t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun r => V r x) (Icc 0 T) t + fderiv ℝ (V t) x (U t x) +
        fderiv ℝ (U t) x (V t x) + gradient (q t) x = f t x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      divergence (gradient (q t)) x = divergence (f t) x -
        2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ (U t) x).comp (fderiv ℝ (V t) x)).toLinearMap := by
  intro t ht x
  exact divergence_gradient_meanPressure_of_linearizedMomentum
    (contDiff_meanPressure_slice hU ht) (contDiff_meanPressure_slice hV ht)
    (fun y => (hasFDerivAt_slabVelocityTimeDerivative hT ht hV y).differentiableAt)
    (hq t ht) (hUdiv t ht) (hVdiv t ht) (divergence_slabVelocityTimeDerivative hT ht hV hVdiv)
    (hMom t ht) x



section Source

private abbrev MeanPressureGradient := Vec3 →L[ℝ] Vec3

private def meanPressureTraceCLM : MeanPressureGradient →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp
    (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))

private theorem meanPressureTraceCLM_apply (D : MeanPressureGradient) :
    meanPressureTraceCLM D = LinearMap.trace ℝ Vec3 D.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [meanPressureTraceCLM, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

private theorem norm_meanPressureTraceCLM_le : ‖meanPressureTraceCLM‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro D
  have h (i : Fin 3) : ‖(D (EuclideanSpace.single i 1)) i‖ ≤ ‖D‖ := by
    calc
      ‖(D (EuclideanSpace.single i 1)) i‖ ≤ ‖D (EuclideanSpace.single i 1)‖ :=
        PiLp.norm_apply_le _ _
      _ ≤ ‖D‖ * ‖(EuclideanSpace.single i 1 : Vec3)‖ := D.le_opNorm _
      _ = ‖D‖ := by simp [EuclideanSpace.single]
  simp only [meanPressureTraceCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  calc
    ‖∑ i : Fin 3, (D (EuclideanSpace.single i 1)) i‖ ≤
        ∑ i : Fin 3, ‖(D (EuclideanSpace.single i 1)) i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖D‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖D‖ := by simp [nsmul_eq_mul]

variable {X : Type*} [MetricSpace X]

private theorem meanPressureGradientProduct_bounds (U V : HalfHolder X MeanPressureGradient) :
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

private def meanPressureGradientComp (U V : HalfHolder X MeanPressureGradient) :
    HalfHolder X MeanPressureGradient :=
  HalfHolder.ofBound
    ⟨fun x => HalfHolder.eval x U * HalfHolder.eval x V,
      U.val.1.continuous.mul V.val.1.continuous⟩
    (meanPressureGradientProduct_bounds U V).1 (meanPressureGradientProduct_bounds U V).2

@[simp] private theorem eval_meanPressureGradientComp (U V : HalfHolder X MeanPressureGradient)
    (x : X) : HalfHolder.eval x (meanPressureGradientComp U V) =
      (HalfHolder.eval x U).comp (HalfHolder.eval x V) := rfl

private theorem norm_meanPressureGradientComp_le (U V : HalfHolder X MeanPressureGradient) :
    ‖meanPressureGradientComp U V‖ ≤ 2 * ‖U‖ * ‖V‖ := by
  apply (HalfHolder.norm_le_iff (by positivity)).mpr
  exact meanPressureGradientProduct_bounds U V

/-- The scalar mean-pressure source from the two velocity gradients and the forcing gradient. -/
def meanPressurePoissonSource (DU DV Df : HalfHolder X (Vec3 →L[ℝ] Vec3)) : HalfHolder X ℝ :=
  HalfHolder.map meanPressureTraceCLM Df -
    (2 : ℝ) • HalfHolder.map meanPressureTraceCLM (meanPressureGradientComp DU DV)

/-- The source is the forcing divergence minus twice the contracted velocity gradients. -/
theorem meanPressurePoissonSource_eval (DU DV Df : HalfHolder X (Vec3 →L[ℝ] Vec3)) (x : X) :
    HalfHolder.eval x (meanPressurePoissonSource DU DV Df) =
      LinearMap.trace ℝ Vec3 (HalfHolder.eval x Df).toLinearMap -
        2 * LinearMap.trace ℝ Vec3 ((HalfHolder.eval x DU).comp (HalfHolder.eval x DV)).toLinearMap := by
  simp only [meanPressurePoissonSource, map_sub, map_smul, HalfHolder.eval_map,
    eval_meanPressureGradientComp, meanPressureTraceCLM_apply, smul_eq_mul]

/-- The trace and composition estimates preserve the half-Hölder source with explicit factors. -/
theorem norm_meanPressurePoissonSource_le (DU DV Df : HalfHolder X (Vec3 →L[ℝ] Vec3)) :
    ‖meanPressurePoissonSource DU DV Df‖ ≤ 3 * ‖Df‖ + 12 * ‖DU‖ * ‖DV‖ := by
  have hTrace (D : HalfHolder X MeanPressureGradient) : ‖HalfHolder.map meanPressureTraceCLM D‖ ≤ 3 * ‖D‖ :=
    (HalfHolder.map meanPressureTraceCLM).le_of_opNorm_le
      ((HalfHolder.norm_map_le meanPressureTraceCLM).trans norm_meanPressureTraceCLM_le) D
  unfold meanPressurePoissonSource
  refine (norm_sub_le _ _).trans (add_le_add (hTrace Df) ?_)
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * ‖HalfHolder.map meanPressureTraceCLM (meanPressureGradientComp DU DV)‖ ≤
        2 * (3 * (2 * ‖DU‖ * ‖DV‖)) := by
      exact mul_le_mul_of_nonneg_left ((hTrace _).trans
        (mul_le_mul_of_nonneg_left (norm_meanPressureGradientComp_le DU DV) (by norm_num))) (by norm_num)
    _ = 12 * ‖DU‖ * ‖DV‖ := by ring

/-- With the actual derivative representatives the scalar source is the Euclidean-lift source. -/
theorem meanPressurePoissonSource_lift {U V f : Vec3 → Vec3}
    (DU DV Df : HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3))
    (hU : ∀ x, HalfHolder.eval (toUnitTorus x) DU = fderiv ℝ U x)
    (hV : ∀ x, HalfHolder.eval (toUnitTorus x) DV = fderiv ℝ V x)
    (hf : ∀ x, HalfHolder.eval (toUnitTorus x) Df = fderiv ℝ f x) (x : Vec3) :
    HalfHolder.eval (toUnitTorus x) (meanPressurePoissonSource DU DV Df) =
      divergence f x - 2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ U x).comp (fderiv ℝ V x)).toLinearMap := by
  rw [meanPressurePoissonSource_eval, hU, hV, hf, divergence_eq_trace_fderiv]


end Source

private theorem spatialHolderHalfSeminorm_zero_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec3 → E} (hf : SpatialHolderHalf 0 f) :
    0 ≤ spatialHolderHalfSeminorm f := by
  have h := le_ciSup ((spatialHolderHalf_zero_iff f).mp hf).2.2 ((0 : Vec3), (0 : Vec3))
  have hz : spatialHolderHalfQuotient f (0, 0) = 0 := by simp [spatialHolderHalfQuotient]
  rw [hz] at h
  exact h

private theorem spatialHolderHalfNorm_zero_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec3 → E} (hf : SpatialHolderHalf 0 f) :
    0 ≤ spatialHolderHalfNorm 0 f := by
  rw [spatialHolderHalfNorm_zero_eq]
  exact add_nonneg ((norm_nonneg (f 0)).trans
    (norm_le_spatialSupNorm ((spatialHolderHalf_zero_iff f).mp hf).2.1 0))
    (spatialHolderHalfSeminorm_zero_nonneg hf)

/-- Order-one half-Hölder regularity controls the order-zero norm of the spatial derivative. -/
private theorem spatialHolderHalf_fderiv_zero {f : Vec3 → Vec3} (hf : SpatialHolderHalf 1 f) :
    SpatialHolderHalf 0 (fderiv ℝ f) ∧ spatialHolderHalfNorm 0 (fderiv ℝ f) ≤ spatialHolderHalfNorm 1 f := by
  obtain ⟨_, hf₀, hfD⟩ := (spatialHolderHalf_one_iff f).mp hf
  refine ⟨hfD, ?_⟩
  rw [spatialHolderHalfNorm_one_eq]
  exact le_add_of_nonneg_left (spatialHolderHalfNorm_zero_nonneg hf₀)

set_option maxHeartbeats 1000000 in
/-- The Hessian of the actual periodic mean pressure has a half-Hölder bound
in the lift norms of the parent gradient, mean gradient, and force gradient. -/
theorem meanPressureHessian_halfHolder_of_periodicPoisson
    {DU DV Df : Vec3 → Gradient} {q : Vec3 → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqper : SpatiallyPeriodic q)
    (hUper : SpatiallyPeriodic DU) (hVper : SpatiallyPeriodic DV) (hfper : SpatiallyPeriodic Df)
    (hU : SpatialHolderHalf 0 DU) (hV : SpatialHolderHalf 0 DV) (hf : SpatialHolderHalf 0 Df)
    (hPoisson : ∀ x, divergence (gradient q) x = LinearMap.trace ℝ Vec3 (Df x).toLinearMap -
      2 * LinearMap.trace ℝ Vec3 ((DU x).comp (DV x)).toLinearMap) :
    SpatialHolderHalf 0 (fderiv ℝ (gradient q)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (gradient q)) ≤
        (48 * ‖pressureHessianMultiplier‖) * (spatialHolderHalfNorm 0 Df +
          spatialHolderHalfNorm 0 DU * spatialHolderHalfNorm 0 DV) := by
  obtain ⟨U, hUrep, hUnorm⟩ := exists_halfHolder_of_spatialHolderHalf_zero hUper hU
  obtain ⟨V, hVrep, hVnorm⟩ := exists_halfHolder_of_spatialHolderHalf_zero hVper hV
  obtain ⟨f, hfrep, hfnorm⟩ := exists_halfHolder_of_spatialHolderHalf_zero hfper hf
  obtain ⟨qT, hqrep⟩ := hqper.exists_continuousTorusFunction hq.continuous
  have hG : ContDiff ℝ ∞ (gradient q) := (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
    (hq.fderiv_right (m := ∞) (by simp))
  have hDq : ContDiff ℝ ∞ (fderiv ℝ (gradient q)) := hG.fderiv_right (m := ∞) (by simp)
  have hHper : SpatiallyPeriodic (fderiv ℝ (gradient q)) :=
    (hqper.gradient (hq.differentiable (by simp))).fderiv (hG.differentiable (by simp))
  obtain ⟨H, hHrep, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hHper
    (spatialHolderHalf_of_contDiff_periodic hDq hHper 0)
  let F := meanPressurePoissonSource U V f
  have hFrep (x : Vec3) : HalfHolder.eval (toUnitTorus x) F = divergence (gradient q) x := by
    rw [meanPressurePoissonSource_eval, hUrep, hVrep, hfrep, hPoisson]
  have hH : pressureHessianMultiplier F = H := pressureHessianMultiplier_eq_of_periodicPoisson F H
    (hq.of_le (by simp)) hqper qT hqrep hHrep hFrep
  have h0 := spatialHolderHalf_zero_of_halfHolder H
  rw [funext hHrep] at h0
  refine ⟨h0.1, ?_⟩
  let A := spatialHolderHalfNorm 0 DU
  let B := spatialHolderHalfNorm 0 DV
  let C := spatialHolderHalfNorm 0 Df
  let M := ‖pressureHessianMultiplier‖
  have hA : 0 ≤ A := spatialHolderHalfNorm_zero_nonneg hU
  have hB : 0 ≤ B := spatialHolderHalfNorm_zero_nonneg hV
  have hC : 0 ≤ C := spatialHolderHalfNorm_zero_nonneg hf
  have hM : 0 ≤ M := norm_nonneg pressureHessianMultiplier
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt₂ : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hUpper : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  change ‖U‖ ≤ Real.sqrt 2 * A at hUnorm
  change ‖V‖ ≤ Real.sqrt 2 * B at hVnorm
  change ‖f‖ ≤ Real.sqrt 2 * C at hfnorm
  have hUV : ‖U‖ * ‖V‖ ≤ 2 * (A * B) := by
    calc
      _ ≤ (Real.sqrt 2 * A) * (Real.sqrt 2 * B) :=
        mul_le_mul hUnorm hVnorm (norm_nonneg V) (mul_nonneg hsqrt hA)
      _ = (Real.sqrt 2)^2 * (A * B) := by ring
      _ = _ := by rw [hsqrt₂]
  have hfn : ‖f‖ ≤ 2 * C := hfnorm.trans
    (mul_le_mul_of_nonneg_right hUpper hC)
  have hForce : ‖F‖ ≤ 24 * (C + A * B) := by
    refine (norm_meanPressurePoissonSource_le U V f).trans ?_
    nlinarith only [hfn, hUV, hC]
  calc
    _ ≤ 2 * ‖H‖ := h0.2
    _ ≤ 2 * (M * ‖F‖) := by
      rw [← hH]
      exact mul_le_mul_of_nonneg_left (norm_pressureHessianMultiplier_apply_le F) (by norm_num)
    _ ≤ 2 * (M * (24 * (C + A * B))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hForce hM) (by norm_num)
    _ = _ := by dsimp only [M, C, A, B]; ring


/-- The spatial half-Hölder parent-gradient bound follows from the parent bandwidth
and the actual first-gradient bound. -/
theorem exists_parentGradient_halfHolder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : C(Labels, Vec3)) {D : ℝ}, 1 ≤ D →
      RealTorusFourierBand (4 * D) g →
      (∀ x, ‖fderiv ℝ (fun y => g (toUnitTorus y)) x‖ ≤ D) →
      let DU := fderiv ℝ (fun y => g (toUnitTorus y))
      SpatialHolderHalf 0 DU ∧ spatialHolderHalfNorm 0 DU ≤ C * D^2 := by
  obtain ⟨K, hK, hJet⟩ := exists_parentVelocityJetBounds
  refine ⟨1 + Real.sqrt (2 * K 2), by positivity, ?_⟩
  intro g D hD hBand hGrad DU
  let u : Vec3 → Vec3 := fun x => g (toUnitTorus x)
  obtain ⟨_, _, hBernstein⟩ := exists_bandBernsteinJetBounds
  have hu : ContDiff ℝ ∞ u := (hBernstein g (zero_lt_one.trans_le hD) (norm_nonneg g) le_rfl hBand).1
  have hDU : ContDiff ℝ ∞ DU := hu.fderiv_right (m := ∞) (by simp)
  let B (n : ℕ) := if n = 0 then D else K 2 * D^2
  have hBounds (j : ℕ) (hj : j ≤ 0 + 1) (x : Vec3) : ‖iteratedFDeriv ℝ j DU x‖ ≤ B j := by
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simpa only [norm_iteratedFDeriv_zero, B, ite_true] using hGrad x
    · change ‖iteratedFDeriv ℝ 1 (fderiv ℝ u) x‖ ≤ B 1
      rw [norm_iteratedFDeriv_fderiv]
      simpa [B] using hJet g hD hBand hGrad 2 2 (by norm_num) le_rfl x
  obtain ⟨hHolder, hHolderNorm⟩ := spatialHolderHalf_of_bounded_jets hDU B hBounds
  refine ⟨hHolder, hHolderNorm.trans ?_⟩
  simp only [Finset.range_one, Finset.sum_singleton, B, ite_true, zero_add, one_ne_zero, ite_false]
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hpow : D^3 ≤ D^4 := pow_le_pow_right₀ hD (by norm_num)
  have hK₀ : 0 ≤ 2 * K 2 := mul_nonneg (by norm_num) (hK 2)
  have hsqrt : Real.sqrt (2 * D * (K 2 * D^2)) ≤ Real.sqrt (2 * K 2) * D^2 := by
    calc
      _ = Real.sqrt ((2 * K 2) * D^3) := by congr 1; ring
      _ ≤ Real.sqrt ((2 * K 2) * D^4) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hpow hK₀)
      _ = _ := by rw [Real.sqrt_mul hK₀, show D^4 = (D^2)^2 by ring, Real.sqrt_sq (sq_nonneg D)]
  calc
    _ ≤ D^2 + Real.sqrt (2 * K 2) * D^2 := add_le_add (le_self_pow₀ hD (by norm_num)) hsqrt
    _ = _ := by ring

/-- The actual mean pressure Hessian on the closed slab has its uniform
spatial Hölder bound and its supremum bound from the linearized momentum. -/
theorem meanPressureHessian_closedSlab_bound {T MU MV Mf : ℝ} (hT : 0 < T)
    {U V f : Velocity} {q : Pressure}
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hq : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (q t)) (hqper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (q t))
    (hUper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hfper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun r => V r x) (Icc 0 T) t + fderiv ℝ (V t) x (U t x) +
        fderiv ℝ (U t) x (V t x) + gradient (q t) x = f t x)
    (hUsize : ∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (fderiv ℝ (U t)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (U t)) ≤ MU)
    (hVsize : ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (V t) ∧ spatialHolderHalfNorm 1 (V t) ≤ MV)
    (hfsize : ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (f t) ∧ spatialHolderHalfNorm 1 (f t) ≤ Mf) :
    let H := fun t => fderiv ℝ (gradient (q t))
    let I := {t : ℝ // t ∈ Icc 0 T}
    let K := (48 * ‖pressureHessianMultiplier‖) * (Mf + MU * MV)
    (∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (H t) ∧ spatialHolderHalfNorm 0 (H t) ≤ K) ∧
      (⨆ t : I, spatialHolderHalfNorm 0 (H t)) ≤ K ∧
      (⨆ t : I, spatialSupNorm (H t)) ≤ K := by
  intro H I K
  have hBound (t : ℝ) (ht : t ∈ Icc 0 T) :
      SpatialHolderHalf 0 (H t) ∧ spatialHolderHalfNorm 0 (H t) ≤ K := by
    have hU' := hUsize t ht
    have hV' := spatialHolderHalf_fderiv_zero (hVsize t ht).1
    have hf' := spatialHolderHalf_fderiv_zero (hfsize t ht).1
    have hUdiff := (contDiff_meanPressure_slice hU ht).differentiable (by norm_num)
    have hVdiff := (contDiff_meanPressure_slice hV ht).differentiable (by norm_num)
    have hfdiff := (hfsize t ht).1.1.differentiable (by simp)
    have hΔ (x : Vec3) : divergence (gradient (q t)) x =
        LinearMap.trace ℝ Vec3 (fderiv ℝ (f t) x).toLinearMap -
          2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ (U t) x).comp (fderiv ℝ (V t) x)).toLinearMap := by
      rw [← divergence_eq_trace_fderiv]
      exact meanPressure_poisson_closedSlab hT hU hV (fun r hr => (hq r hr).of_le (by simp))
        hUdiv hVdiv hMom t ht x
    obtain ⟨hh, hnorm⟩ := meanPressureHessian_halfHolder_of_periodicPoisson (hq t ht) (hqper t ht)
      ((hUper t ht).fderiv hUdiff) ((hVper t ht).fderiv hVdiff) ((hfper t ht).fderiv hfdiff)
      hU'.1 hV'.1 hf'.1 hΔ
    have hMU : 0 ≤ MU := (spatialHolderHalfNorm_zero_nonneg hU'.1).trans hU'.2
    have hp : spatialHolderHalfNorm 0 (fderiv ℝ (U t)) * spatialHolderHalfNorm 0 (fderiv ℝ (V t))
        ≤ MU * MV := mul_le_mul hU'.2 (hV'.2.trans (hVsize t ht).2)
          (spatialHolderHalfNorm_zero_nonneg hV'.1) hMU
    exact ⟨hh, hnorm.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hf'.2.trans (hfsize t ht).2) hp) (by positivity))⟩
  have : Nonempty I := ⟨⟨0, le_rfl, hT.le⟩⟩
  refine ⟨hBound, ciSup_le fun t => (hBound t t.property).2, ciSup_le fun t => ?_⟩
  have he := (hBound t t.property).1
  refine le_trans ?_ (hBound t t.property).2
  rw [spatialHolderHalfNorm_zero_eq]
  exact le_add_of_nonneg_right (spatialHolderHalfSeminorm_zero_nonneg he)


/-- The source and mean velocity rate of Proposition 5.10 gives the same
frequency decay for the pressure Hessian after absorbing the parent factor. -/
theorem meanPressureHessian_rate_absorption {D frequency MU MV Mf Cparent Cmean : ℝ} {b : ℕ}
    (hD : 1 ≤ D) (hfrequency : 0 < frequency) (hCparent : 0 ≤ Cparent) (hCmean : 0 ≤ Cmean)
    (hMV₀ : 0 ≤ MV) (hMU : MU ≤ Cparent * D^2)
    (hMV : MV ≤ Cmean * D^b * frequency ^ (-5 / 2 : ℝ))
    (hMf : Mf ≤ Cmean * D^b * frequency ^ (-5 / 2 : ℝ)) :
    (48 * ‖pressureHessianMultiplier‖) * (Mf + MU * MV) ≤
      (48 * ‖pressureHessianMultiplier‖ * Cmean * (1 + Cparent)) * D^(b + 2) * frequency ^ (-5 / 2 : ℝ) := by
  let m := Cmean * D^b * frequency ^ (-5 / 2 : ℝ)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  have hparent : 0 ≤ Cparent * D^2 := by positivity
  have hpow : 1 ≤ D^2 := one_le_pow₀ hD
  calc
    _ ≤ (48 * ‖pressureHessianMultiplier‖) * (m + (Cparent * D^2) * m) :=
      mul_le_mul_of_nonneg_left (add_le_add hMf (mul_le_mul hMU hMV hMV₀ hparent)) (by positivity)
    _ ≤ (48 * ‖pressureHessianMultiplier‖) * (D^2 * m + (Cparent * D^2) * m) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_mul_of_one_le_left hm hpow) le_rfl) (by positivity)
    _ = _ := by dsimp only [m]; rw [pow_add]; ring

end

end TorusEuler
