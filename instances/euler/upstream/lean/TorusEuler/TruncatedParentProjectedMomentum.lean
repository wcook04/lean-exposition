import TorusEuler.TruncationFourierCommutation
import TorusEuler.PeriodicLerayHolderLift
import TorusEuler.SmoothPeriodicHolder

/-! The closed-slab projected momentum equation and estimate (5.58) in Proposition 5.11. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Pointwise

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The within-slab time derivative is jointly smooth, including at both time endpoints. -/
theorem contDiffOn_sliceTimeDerivWithin_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b)
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => derivWithin (fun t => f t p.2) (Icc a b) p.1)
      (Icc a b ×ˢ (univ : Set Vec3)) := by
  let S : Set (ℝ × Vec3) := Icc a b ×ˢ univ
  let L : ((ℝ × Vec3) →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (1, 0)
  have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ (Function.uncurry f) S) S :=
    hf.fderivWithin ((uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ) (by simp)
  refine (L.contDiff.comp_contDiffOn hD).congr ?_
  rintro ⟨t, x⟩ ⟨ht, _⟩
  have hd := (hf.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hslice := hd.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasFDerivWithinAt
    (fun r hr => (show (r, x) ∈ S from ⟨hr, mem_univ x⟩))
  have htime : HasDerivWithinAt (fun r => f r x)
      (fderivWithin ℝ (Function.uncurry f) S (t, x) (1, 0)) (Icc a b) t := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using hslice.hasDerivWithinAt
  exact htime.derivWithin (uniqueDiffOn_Icc hab t ht)

private theorem contDiff_slice_of_contDiffOn_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) {t : ℝ}
    (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (f t) := by
  have hp : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.1 (hf.comp hp.contDiffOn fun x _ => ⟨ht, mem_univ x⟩)

private theorem periodic_sliceTimeDerivWithin_Icc {a b : ℝ} {f : Velocity}
    (hf : ∀ t ∈ Icc a b, SpatiallyPeriodic (f t)) {t : ℝ} (ht : t ∈ Icc a b) :
    SpatiallyPeriodic (fun x => derivWithin (fun r => f r x) (Icc a b) t) := by
  intro n x
  exact derivWithin_congr (fun r hr => hf r hr n x) (hf t ht n x)

/-- Coefficient differentiation commutes with restriction to the closed time slab. -/
theorem hasDerivWithinAt_mFourierCoeff_closedSlab
    {a b : ℝ} {V Vt : Velocity} (g gt : ℝ → C(Labels, Vec3))
    (hV : ContinuousOn (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (hVt : ContinuousOn (Function.uncurry Vt) (Icc a b ×ˢ (univ : Set Vec3)))
    (hrep : ∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x)
    (hrept : ∀ t ∈ Icc a b, ∀ x, gt t (toUnitTorus x) = Vt t x)
    (hder : ∀ t ∈ Icc a b, ∀ x, HasDerivWithinAt (fun r => V r x) (Vt t x) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Icc a b) (k : Fin 3 → ℤ) :
    HasDerivWithinAt (fun r => mFourierCoeff (endpointComplexifyContinuous (g r)) k)
      (mFourierCoeff (endpointComplexifyContinuous (gt t)) k) (Icc a b) t := by
  let F (r : ℝ) (x : Vec3) := fourierMode (-k) x • periodicComplexifyVector (V r x)
  let D (r : ℝ) (x : Vec3) := fourierMode (-k) x • periodicComplexifyVector (Vt r x)
  have hmode : Continuous (fun p : ℝ × Vec3 => fourierMode (-k) p.2) :=
    (contDiff_fourierMode (-k)).continuous.comp continuous_snd
  have hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ centeredCell) :=
    (hmode.continuousOn.smul (periodicComplexifyVector.continuous.comp_continuousOn hV)).mono
      (prod_mono_right (subset_univ centeredCell))
  have hD : ContinuousOn (Function.uncurry D) (Icc a b ×ˢ centeredCell) :=
    (hmode.continuousOn.smul (periodicComplexifyVector.continuous.comp_continuousOn hVt)).mono
      (prod_mono_right (subset_univ centeredCell))
  have hdiff (r : ℝ) (hr : r ∈ Icc a b) (x : Vec3) (_ : x ∈ centeredCell) :
      HasDerivWithinAt (fun s => F s x) (D r x) (Icc a b) r :=
    (periodicComplexifyVector.hasFDerivAt.comp_hasDerivWithinAt r (hder r hr x)).const_smul (fourierMode (-k) x)
  have hd := hasDerivWithinAt_integral_prod_Icc isCompact_centeredCell ht hF hD hdiff
  have hcoeff (r : ℝ) (hr : r ∈ Icc a b) :
      mFourierCoeff (endpointComplexifyContinuous (g r)) k = ∫ x in centeredCell, F r x := by
    rw [fourierCoeff_eq_centeredCell]
    change (∫ x in centeredCell, fourierMode (-k) x • periodicComplexifyVector (g r (toUnitTorus x))) = _
    simp_rw [hrep r hr, F]
  have hcoefft : mFourierCoeff (endpointComplexifyContinuous (gt t)) k = ∫ x in centeredCell, D t x := by
    rw [fourierCoeff_eq_centeredCell]
    change (∫ x in centeredCell, fourierMode (-k) x • periodicComplexifyVector (gt t (toUnitTorus x))) = _
    simp_rw [hrept t ht, D]
  rw [hcoefft]
  exact hd.congr_of_mem hcoeff ht

/-- Differentiating the actual real cutoff in time gives the cutoff of the within-slab derivative. -/
theorem hasDerivWithinAt_realVectorFourierCutoff_time
    {a b : ℝ} (hab : a < b) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (g gt : ℝ → C(Labels, Vec3))
    (hrep : ∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x)
    (hrept : ∀ t ∈ Icc a b, ∀ x, gt t (toUnitTorus x) = derivWithin (fun r => V r x) (Icc a b) t)
    (ψ : Vec3 → ℝ) (Λ : ℝ) {t : ℝ} (ht : t ∈ Icc a b) (x : Vec3) :
    HasDerivWithinAt (fun r => realVectorFourierCutoff ψ Λ (g r) (toUnitTorus x))
      (realVectorFourierCutoff ψ Λ (gt t) (toUnitTorus x)) (Icc a b) t := by
  let Vt (r : ℝ) (y : Vec3) := derivWithin (fun s => V s y) (Icc a b) r
  have hVt : ContDiffOn ℝ ∞ (Function.uncurry Vt) (Icc a b ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hab hV
  have hder (r : ℝ) (hr : r ∈ Icc a b) (y : Vec3) :
      HasDerivWithinAt (fun s => V s y) (Vt r y) (Icc a b) r := by
    have hj : ContDiff ℝ ∞ (fun q : ℝ => (q, y)) := contDiff_id.prodMk contDiff_const
    have hslice : ContDiffOn ℝ ∞ (fun s => V s y) (Icc a b) :=
      hV.comp hj.contDiffOn fun q hq => ⟨hq, mem_univ y⟩
    exact (hslice.differentiableOn (by simp) r hr).hasDerivWithinAt
  let term (k : Fin 3 → ℤ) (r : ℝ) := fourierMode k x •
    (ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (endpointComplexifyContinuous (g r)) k)
  let termD (k : Fin 3 → ℤ) := fourierMode k x •
    (ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (endpointComplexifyContinuous (gt t)) k)
  have hterm (k : Fin 3 → ℤ) : HasDerivWithinAt (term k) (termD k) (Icc a b) t :=
    ((hasDerivWithinAt_mFourierCoeff_closedSlab g gt hV.continuousOn hVt.continuousOn
      hrep hrept hder ht k).const_smul (ψ (Λ⁻¹ • latticeVector k))).const_smul (fourierMode k x)
  let s := frequencyBand (2 * Λ)
  have hsynth : HasDerivWithinAt (fun r => ∑ k ∈ s, term k r) (∑ k ∈ s, termD k) (Icc a b) t :=
    HasDerivWithinAt.fun_sum (fun k _ => hterm k)
  exact periodicRealPartVector.hasFDerivAt.comp_hasDerivWithinAt t hsynth



private theorem cutoff_pressure_gradient_coord (f : Vec3 → ℝ) (x : Vec3) (i : Fin 3) :
    (gradient f x) i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  calc
    _ = ⟪gradient f x, EuclideanSpace.single i 1⟫_ℝ := by
      rw [EuclideanSpace.inner_single_right]
      simp
    _ = _ := inner_gradient_left

/-- The vector cutoff of a spatial gradient is the gradient of the scalar cutoff. -/
theorem realVectorFourierCutoff_gradient (ψ : Vec3 → ℝ) (Λ : ℝ)
    (p : C(Labels, ℝ)) (g : C(Labels, Vec3))
    (hp : ContDiff ℝ 1 (fun x => p (toUnitTorus x)))
    (hg : ∀ x, g (toUnitTorus x) = gradient (fun y => p (toUnitTorus y)) x) :
    (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) =
      gradient (fun x => realScalarFourierCutoff ψ Λ p (toUnitTorus x)) := by
  let pc := fun a : Labels => (p a : ℂ)
  let gc := endpointComplexifyContinuous g
  let s := frequencyBand (2 * Λ)
  let a := fun k => ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff pc k
  let b := fun k => ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff gc k
  let Q := fun x => finiteFourierSum s a (toUnitTorus x)
  have hpc : ContDiff ℝ 1 (fun x => pc (toUnitTorus x)) := Complex.ofRealCLM.contDiff.comp hp
  have hperiod : SpatiallyPeriodic (fun x => pc (toUnitTorus x)) := by
    intro n _
    exact congrArg pc ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hb (k : Fin 3 → ℤ) (i : Fin 3) : (b k) i = fourierDerivativeSymbol k i • a k := by
    let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj i
    have hInt : IntegrableOn (fun x => fourierMode (-k) x • gc (toUnitTorus x)) centeredCell := by
      apply ContinuousOn.integrableOn_compact isCompact_centeredCell
      exact (((contDiff_fourierMode (-k)).continuous).smul (gc.continuous.comp
        isOpenQuotientMap_toUnitTorus.continuous)).continuousOn
    have hD (x : Vec3) : L (gc (toUnitTorus x)) =
        fderiv ℝ (fun y => pc (toUnitTorus y)) x (EuclideanSpace.single i 1) := by
      have hd := (Complex.ofRealCLM.hasFDerivAt.comp x (hp.differentiable one_ne_zero x).hasFDerivAt).fderiv
      change fderiv ℝ (fun y => pc (toUnitTorus y)) x = _ at hd
      rw [hd]
      change ((g (toUnitTorus x) i : ℝ) : ℂ) = _
      rw [hg, cutoff_pressure_gradient_coord]
      rfl
    have hcoeff : L (mFourierCoeff gc k) = fourierDerivativeSymbol k i • mFourierCoeff pc k := by
      rw [fourierCoeff_eq_centeredCell, fourierCoeff_eq_centeredCell, ← L.integral_comp_comm hInt]
      simp_rw [map_smul, hD, smul_eq_mul]
      exact centeredCell_fourier_coordinate_deriv hpc hperiod k i
    change L (ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff gc k) = _
    rw [L.map_smul_of_tower, hcoeff]
    exact smul_comm _ _ _
  funext x
  apply PiLp.ext
  intro i
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj i
  rw [cutoff_pressure_gradient_coord]
  have hQ := ((contDiff_lift_finiteFourierSum s a).differentiable (by simp) x).hasFDerivAt
  have hD := (Complex.reCLM.hasFDerivAt.comp x hQ).fderiv
  change (L (finiteFourierSum s b (toUnitTorus x))).re =
    fderiv ℝ (fun y => (Q y).re) x (EuclideanSpace.single i 1)
  change fderiv ℝ (fun y => (Q y).re) x = _ at hD
  rw [hD, ContinuousLinearMap.comp_apply]
  change (L (finiteFourierSum s b (toUnitTorus x))).re =
    (fderiv ℝ Q x (EuclideanSpace.single i 1)).re
  rw [show fderiv ℝ Q x (EuclideanSpace.single i 1) =
    finiteFourierSum s (fun k => fourierDerivativeSymbol k i • a k) (toUnitTorus x) from
    fderiv_lift_finiteFourierSum_single s a x i]
  apply congrArg Complex.re
  simp only [finiteFourierSum, map_sum, map_smul]
  exact Finset.sum_congr rfl fun k _ => congrArg (fun z : ℂ => mFourier k (toUnitTorus x) • z) (hb k i)

/-- A continuously differentiable periodic lift belongs to the spatial half-Hölder domain. -/
theorem spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec3 → E} (hf : ContDiff ℝ 1 f) (hper : SpatiallyPeriodic f) :
    SpatialHolderHalf 0 f := by
  obtain ⟨g, hg⟩ := hper.exists_continuousTorusFunction hf.continuous
  have hd := hf.differentiable one_ne_zero
  obtain ⟨D, hD⟩ := (hper.fderiv hd).exists_continuousTorusFunction (hf.continuous_fderiv one_ne_zero)
  have hval (x : Vec3) : ‖f x‖ ≤ ‖g‖ := (hg x) ▸ g.norm_coe_le_norm (toUnitTorus x)
  have hder (x : Vec3) : ‖fderiv ℝ f x‖ ≤ ‖D‖ := (hD x) ▸ D.norm_coe_le_norm (toUnitTorus x)
  refine (spatialHolderHalf_zero_iff f).2 ⟨hf.continuous, ⟨‖g‖, forall_mem_range.mpr hval⟩,
    ⟨Real.sqrt (2 * ‖g‖ * ‖D‖), forall_mem_range.mpr ?_⟩⟩
  rintro ⟨x, v⟩
  have hv : ‖f (x + v) - f x‖ ≤ ‖D‖ * ‖v‖ := by
    have h := (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd y) (fun y _ => hder y) (mem_univ x) (mem_univ (x + v))
    simpa only [add_sub_cancel_left] using h
  have hsum : ‖f (x + v) - f x‖ ≤ 2 * ‖g‖ := by
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hval _) (hval _))
  have hsq : ‖f (x + v) - f x‖ ^ 2 ≤ (2 * ‖g‖ * ‖D‖) * ‖v‖ := by
    rw [sq, mul_assoc]
    exact mul_le_mul hsum hv (norm_nonneg _) (by positivity)
  have hinc : ‖f (x + v) - f x‖ ≤ Real.sqrt (2 * ‖g‖ * ‖D‖) * Real.sqrt ‖v‖ := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le hsq
  change ‖f (x + v) - f x‖ / Real.sqrt ‖v‖ ≤ _
  by_cases hv0 : v = 0
  · simp [hv0]
    positivity
  · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv0))).2 hinc

/-- The concrete torus Leray projection kills a smooth periodic pressure gradient. -/
theorem periodicLerayHolderLift_gradient_eq_zero (p : EndpointSmoothPotential) :
    periodicLerayHolderLift (gradient p.lift) = 0 := by
  have hp := p.smooth.differentiable (by simp)
  have hper := p.periodic.gradient hp
  have hs : ContDiff ℝ 1 (gradient p.lift) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (p.smooth.fderiv_right (by simp))
  obtain ⟨g, hg, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper
    (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic hs hper)
  have hrep (a : Labels) : HalfHolder.eval a g = endpointPotentialGradient p a := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hg, endpointPotentialGradient_toUnitTorus]
  have hLp : endpointHalfHolderToL2 g = (endpointPotentialGradient p).toLp 2 unitTorusMeasure ℝ := by
    apply Lp.ext
    filter_upwards [endpointHalfHolderToL2_apply_ae g,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure (endpointPotentialGradient p)] with a ha hb
    rw [ha, hb, hrep]
  have hk : endpointStrongSpatialLeray g = 0 := by
    apply endpointHalfHolderToL2_injective
    rw [endpointStrongSpatialLeray_agrees_L2, map_zero, hLp]
    let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
    change endpointSpatialSolenoidal.starProjection _ = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (zero_mem _) fun w hw => ?_
    rw [sub_zero]
    change endpointSpatialDivergenceTest p w = 0
    rw [endpointSpatialDivergenceTest_apply]
    exact (mem_endpointSpatialSolenoidal w).mp hw p
  rw [← funext hg, periodicLerayHolderLift_pullback, hk]
  simp only [map_zero]
  rfl

/-- The periodic Leray projection removes the Fourier-truncated pressure gradient. -/
theorem periodicLerayHolderLift_add_cutoff_pressure_gradient (ψ : Vec3 → ℝ) (Λ : ℝ)
    (p : EndpointSmoothPotential) (mom : Vec3 → Vec3) (hmomPer : SpatiallyPeriodic mom)
    (hmom : SpatialHolderHalf 0 mom) :
    periodicLerayHolderLift (mom + fun x => realVectorFourierCutoff ψ Λ (endpointPotentialGradient p)
      (toUnitTorus x)) = periodicLerayHolderLift mom := by
  obtain ⟨pTorus, hpTorus⟩ := p.periodic.exists_continuousTorusFunction p.smooth.continuous
  have hpEq : (fun x => pTorus (toUnitTorus x)) = p.lift := funext hpTorus
  have hp : ContDiff ℝ 1 (fun x => pTorus (toUnitTorus x)) := by
    rw [hpEq]
    exact p.smooth.of_le (by simp)
  have hg (x : Vec3) : endpointPotentialGradient p (toUnitTorus x) =
      gradient (fun y => pTorus (toUnitTorus y)) x := by
    rw [hpEq, endpointPotentialGradient_toUnitTorus]
  let q : EndpointSmoothPotential :=
    ⟨fun x => realScalarFourierCutoff ψ Λ pTorus (toUnitTorus x),
      Complex.reCLM.contDiff.comp (contDiff_lift_smoothFourierCutoff ψ Λ (fun a => (pTorus a : ℂ))),
      fun n _ => congrArg (realScalarFourierCutoff ψ Λ pTorus) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)⟩
  have hcut : (fun x => realVectorFourierCutoff ψ Λ (endpointPotentialGradient p) (toUnitTorus x)) =
      gradient q.lift := realVectorFourierCutoff_gradient ψ Λ pTorus _ hp hg
  have hper := q.periodic.gradient (q.smooth.differentiable (by simp))
  have hs : ContDiff ℝ 1 (gradient q.lift) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (q.smooth.fderiv_right (by simp))
  rw [hcut, periodicLerayHolderLift_add hmomPer hper hmom
    (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic hs hper),
    periodicLerayHolderLift_gradient_eq_zero, add_zero]


private theorem exists_closedSlab_torusSlices {a b : ℝ} {V : Velocity}
    (hc : ∀ t ∈ Icc a b, Continuous (V t)) (hp : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t)) :
    ∃ g : ℝ → C(Labels, Vec3), ∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x := by
  classical
  have h (t : ℝ) (ht : t ∈ Icc a b) := (hp t ht).exists_continuousTorusFunction (hc t ht)
  refine ⟨fun t => if ht : t ∈ Icc a b then (h t ht).choose else 0, ?_⟩
  intro t ht x
  simp only [dite_eq_left ht]
  exact (h t ht).choose_spec x

/-- The actual periodic Leray projection of the closed-slab time derivative and Euler advection. -/
def closedSlabLerayMomentum (a b : ℝ) (u : Velocity) (t : ℝ) : Vec3 → Vec3 :=
  periodicLerayHolderLift (fun x => derivWithin (fun r => u r x) (Icc a b) t + fderiv ℝ (u t) x (u t x))

/-- Applying the actual real cutoff and periodic Leray projection to the approximate
momentum equation gives (5.58), including at the two time endpoints. -/
theorem closedSlabLerayMomentum_realFourierCutoff
    {a b : ℝ} (hab : a < b) {V RV : Velocity} (pressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc a b, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc a b, ∀ x, derivWithin (fun r => V r x) (Icc a b) t +
      fderiv ℝ (V t) x (V t x) + gradient (pressure t).lift x = RV t x)
    (gV gRV : ℝ → C(Labels, Vec3))
    (hgV : ∀ t ∈ Icc a b, ∀ x, gV t (toUnitTorus x) = V t x)
    (hgRV : ∀ t ∈ Icc a b, ∀ x, gRV t (toUnitTorus x) = RV t x)
    {ψ : Vec3 → ℝ} (hEven : Function.Even ψ) (Λ : ℝ) :
    let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)
    ∀ t ∈ Icc a b, closedSlabLerayMomentum a b u t =
      truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t) := by
  intro u
  let Vt : Velocity := fun t x => derivWithin (fun r => V r x) (Icc a b) t
  let A : Velocity := fun t x => fderiv ℝ (V t) x (V t x)
  have hVs (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (V t) := contDiff_slice_of_contDiffOn_Icc hV ht
  have hVts (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (Vt t) :=
    contDiff_slice_of_contDiffOn_Icc (f := Vt) (contDiffOn_sliceTimeDerivWithin_Icc hab hV) ht
  obtain ⟨gVt, hgVt⟩ := exists_closedSlab_torusSlices (fun t ht => (hVts t ht).continuous)
    (fun _ ht => periodic_sliceTimeDerivWithin_Icc hVper ht)
  have hAc (t : ℝ) (ht : t ∈ Icc a b) : Continuous (A t) :=
    ((hVs t ht).continuous_fderiv (by simp)).clm_apply (hVs t ht).continuous
  have hAper (t : ℝ) (ht : t ∈ Icc a b) : SpatiallyPeriodic (A t) := by
    intro n x
    change fderiv ℝ (V t) (x + latticeVector n) (V t (x + latticeVector n)) = fderiv ℝ (V t) x (V t x)
    rw [(hVper t ht).fderiv ((hVs t ht).differentiable (by simp)) n x, hVper t ht n x]
  obtain ⟨gA, hgA⟩ := exists_closedSlab_torusSlices hAc hAper
  intro t ht
  let ut := fun x => derivWithin (fun r => u r x) (Icc a b) t
  let mom := ut + fun x => fderiv ℝ (u t) x (u t x)
  have hut : ut = fun x => realVectorFourierCutoff ψ Λ (gVt t) (toUnitTorus x) := by
    funext x
    exact (hasDerivWithinAt_realVectorFourierCutoff_time hab hV gV gVt hgV hgVt ψ Λ ht x).derivWithin
      (uniqueDiffOn_Icc hab t ht)
  have hEq : gVt t + gA t + endpointPotentialGradient (pressure t) = gRV t := by
    ext z : 1
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    simp only [ContinuousMap.add_apply, hgVt t ht, hgA t ht, endpointPotentialGradient_toUnitTorus, hgRV t ht]
    exact hMom t ht x
  have hVG : (fun x => gV t (toUnitTorus x)) = V t := funext (hgV t ht)
  have hV₁ : ContDiff ℝ 1 (fun x => gV t (toUnitTorus x)) := by
    rw [hVG]
    exact (hVs t ht).of_le (by simp)
  have hD (x : Vec3) : gA t (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV t (toUnitTorus y)) (gV t (toUnitTorus y))) x) := by
    rw [hgA t ht]
    have hA := congrFun (momentumTensorDivergence_self_eq_advection
      ((hVs t ht).differentiable (by simp)) (hVdiv t ht)) x
    change A t x = _
    simpa only [hgV t ht, Function.comp_apply, A] using hA.symm
  have huDiv : ∀ x, divergence (u t) x = 0 := by
    apply divergence_free_lift_realVectorFourierCutoff hEven Λ (gV t)
    · rw [hVG]; exact hVs t ht
    · rw [hVG]; exact hVdiv t ht
  have hu : ContDiff ℝ ∞ (u t) := contDiff_lift_realVectorFourierCutoff ψ Λ (gV t)
  have huper : SpatiallyPeriodic (u t) := spatiallyPeriodic_lift_realVectorFourierCutoff ψ Λ (gV t)
  have hm : ContDiff ℝ 1 mom := by
    have htime : ContDiff ℝ ∞ ut := by
      rw [hut]
      exact contDiff_lift_realVectorFourierCutoff ψ Λ (gVt t)
    exact (htime.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).add
      ((hu.fderiv_right (m := 1) (by simp)).clm_apply (hu.of_le (by simp)))
  have hmper : SpatiallyPeriodic mom := by
    have htper : SpatiallyPeriodic ut := by
      rw [hut]
      exact spatiallyPeriodic_lift_realVectorFourierCutoff ψ Λ (gVt t)
    intro n x
    change ut (x + latticeVector n) + fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
      ut x + fderiv ℝ (u t) x (u t x)
    rw [htper n x, huper.fderiv (hu.differentiable (by simp)) n x, huper n x]
  change periodicLerayHolderLift mom = _
  exact projectedMomentum_realFourierCutoff_eq_residual periodicLerayHolderLift ψ Λ
    (gV t) (gVt t) (gA t) (endpointPotentialGradient (pressure t)) (gRV t) ut hV₁ hut hEq hD huDiv
    (periodicLerayHolderLift_add_cutoff_pressure_gradient ψ Λ (pressure t) mom hmper
      (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic hm hmper))


/-- The exact projected momentum equation and time-uniform velocity-tail and residual
bounds of Proposition 5.11 for a smooth periodic approximate solution. -/
theorem exists_realTruncatedParentProjectedMomentum_bound
    {a b : ℝ} (hab : a < b) {V RV : Velocity} (pressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc a b, ∀ x, divergence (V t) x = 0)
    (hRV : ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc a b ×ˢ (univ : Set Vec3)))
    (hRVper : ∀ t ∈ Icc a b, SpatiallyPeriodic (RV t))
    (hMom : ∀ t ∈ Icc a b, ∀ x, derivWithin (fun r => V r x) (Icc a b) t +
      fderiv ℝ (V t) x (V t x) + gradient (pressure t).lift x = RV t x)
    {ψ : Vec3 → ℝ} (hEven : Function.Even ψ)
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ) (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) :
    ∃ gV gRV : ℝ → C(Labels, Vec3),
      (∀ t ∈ Icc a b, ∀ x, gV t (toUnitTorus x) = V t x) ∧
      (∀ t ∈ Icc a b, ∀ x, gRV t (toUnitTorus x) = RV t x) ∧
      ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (P : ℕ), 2 ≤ P →
        ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (Λ : ℝ), 1 ≤ Λ →
          let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)
          let I := {t : ℝ // t ∈ Icc a b}
          let ε := Λ ^ ((2 : ℤ) - P) * (1 + (⨆ t : I, spatialHolderHalfNorm P (V t)))^2
          (∀ t ∈ Icc a b, closedSlabLerayMomentum a b u t =
            truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t)) ∧
          (⨆ t : I, spatialHolderHalfNorm 2 (u t - V t)) ≤ Ct * ε ∧
          (⨆ t : I, spatialHolderHalfNorm 1 (closedSlabLerayMomentum a b u t)) ≤
            Cr * (⨆ t : I, spatialHolderHalfNorm 1 (RV t)) + Ct * ε := by
  obtain ⟨gV, hgV⟩ := exists_closedSlab_torusSlices
    (fun _ ht => (contDiff_slice_of_contDiffOn_Icc hV ht).continuous) hVper
  obtain ⟨gRV, hgRV⟩ := exists_closedSlab_torusSlices
    (fun _ ht => (contDiff_slice_of_contDiffOn_Icc hRV ht).continuous) hRVper
  let I := {t : ℝ // t ∈ Icc a b}
  have : Nonempty I := ⟨⟨a, le_rfl, hab.le⟩⟩
  obtain ⟨Cr, hCr, hbound⟩ := truncatedEulerLerayProjectedResidual_time_bound (ι := I) hψ hs hunit
  refine ⟨gV, gRV, hgV, hgRV, Cr, hCr, ?_⟩
  intro P hP
  obtain ⟨Ct, hCt, hCtbound⟩ := hbound P hP
  refine ⟨Ct, hCt, ?_⟩
  intro Λ hΛ u _ ε
  have hEq := closedSlabLerayMomentum_realFourierCutoff hab pressure hV hVper hVdiv hMom gV gRV hgV hgRV hEven Λ
  refine ⟨hEq, ?_⟩
  obtain ⟨M, hM⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hab hV hVper P
  obtain ⟨N, hN⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hab hRV hRVper 1
  have hvrep (t : I) : (fun x => gV t (toUnitTorus x)) = V t := funext (hgV t t.property)
  have hrrep (t : I) : (fun x => gRV t (toUnitTorus x)) = RV t := funext (hgRV t t.property)
  have hBhV (t : I) : SpatialHolderHalf P (fun x => gV t (toUnitTorus x)) := by rw [hvrep t]; exact (hM t t.property).1
  have hBhRV (t : I) : SpatialHolderHalf 1 (fun x => gRV t (toUnitTorus x)) := by rw [hrrep t]; exact (hN t t.property).1
  have hMV : BddAbove (range fun t : I => spatialHolderHalfNorm P (fun x => gV t (toUnitTorus x))) :=
    ⟨M, forall_mem_range.mpr fun t => by rw [hvrep t]; exact (hM t t.property).2⟩
  have hNR : BddAbove (range fun t : I => spatialHolderHalfNorm 1 (fun x => gRV t (toUnitTorus x))) :=
    ⟨N, forall_mem_range.mpr fun t => by rw [hrrep t]; exact (hN t t.property).2⟩
  have h := hCtbound Λ hΛ (fun t => gV t) (fun t => gRV t) hBhV hBhRV hMV hNR
  have hS (t : I) : truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t) =
      closedSlabLerayMomentum a b u t := (hEq t t.property).symm
  dsimp only at h
  simpa only [hvrep, hrrep, hS] using h

end

end TorusEuler
