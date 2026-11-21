import TorusEuler.EndpointPressureRecovery
import TorusEuler.EulerLimitClosure
import TorusEuler.ParentVelocityEstimates
import TorusEuler.StationaryShear
import TorusEuler.TruncatedParentProjectedMomentum

/-! The mean-zero periodic pressure of the truncated parent in Proposition 5.11. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The pressure obtained by applying the negative inverse Laplacian to the
divergence of the advective momentum on a slice of the given band. -/
def truncatedParentSlicePressure (r : ℝ) (A : C(Labels, Vec3)) : Vec3 → ℝ :=
  -endpointFiniteFourierPressure (frequencyBand r)
    (fun k => (mFourierCoeff (endpointComplexifyContinuous A) k).ofLp)

theorem contDiff_truncatedParentSlicePressure (r : ℝ) (A : C(Labels, Vec3)) :
    ContDiff ℝ ∞ (truncatedParentSlicePressure r A) :=
  (contDiff_endpointFiniteFourierPressure _ _).neg

theorem spatiallyPeriodic_truncatedParentSlicePressure (r : ℝ) (A : C(Labels, Vec3)) :
    SpatiallyPeriodic (truncatedParentSlicePressure r A) := by
  intro n x
  simp only [truncatedParentSlicePressure, Pi.neg_apply,
    spatiallyPeriodic_endpointFiniteFourierPressure _ _ n x]

theorem integral_truncatedParentSlicePressure (r : ℝ) (A : C(Labels, Vec3)) :
    (∫ x in centeredCell, truncatedParentSlicePressure r A x) = 0 := by
  simp only [truncatedParentSlicePressure, Pi.neg_apply, integral_neg,
    integral_endpointFiniteFourierPressure, neg_zero]

private theorem pullback_torusField_spatiallyPeriodic {E : Type*} (f : Labels → E) :
    SpatiallyPeriodic (fun x => f (toUnitTorus x)) := by
  intro n x
  exact congrArg f ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

theorem periodicLerayHolderLift_eq_self_of_divergence_free {v : Vec3 → Vec3}
    (hv : ContDiff ℝ ∞ v) (hper : SpatiallyPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    periodicLerayHolderLift v = v := by
  obtain ⟨g, hg, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper
    (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hv.of_le (by simp)) hper)
  have hmem : g ∈ endpointHalfHolderSolenoidal :=
    (mem_endpointHalfHolderSolenoidal g).mpr
      ((endpointTorusGradientPairing_iff_divergence_free hv hg).mpr hdiv)
  rw [← funext hg, periodicLerayHolderLift_pullback, (endpointStrongSpatialLeray_fixed_iff g).mpr hmem]

private theorem divergence_truncatedParent_add {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  change divergence (fun y => f y + g y) x = _
  simp only [divergence, fderiv_fun_add hf hg, _root_.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

private theorem gradient_truncatedParent_neg (f : Vec3 → ℝ) :
    gradient (-f) = -gradient f := by
  funext x
  simp only [gradient, fderiv_neg, map_neg, Pi.neg_apply]

private theorem divergence_truncatedParent_neg (f : Vec3 → Vec3) (x : Vec3) :
    divergence (-f) x = -divergence f x := by
  change divergence (fun y => -f y) x = _
  simp only [divergence, fderiv_fun_neg, _root_.neg_apply, PiLp.neg_apply,
    Finset.sum_neg_distrib]

private theorem contDiff_gradient_truncatedParent {p : Vec3 → ℝ} (h : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (gradient p) :=
  (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (h.fderiv_right (m := ∞) (by simp))

private def finitePressureRealPart : ComplexVec3 →L[ℝ] Vec3 :=
  periodicRealPartVector.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap

private theorem finitePressureRealPart_apply (w : ComplexVec3) (i : Fin 3) :
    finitePressureRealPart w i = (w i).re := rfl

private theorem divergence_finitePressureRealPart {v : Vec3 → ComplexVec3} {x : Vec3}
    (hv : DifferentiableAt ℝ v x) :
    divergence (finitePressureRealPart ∘ v) x = (complexDivergence v x).re := by
  rw [divergence, (finitePressureRealPart.hasFDerivAt.comp x hv.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, finitePressureRealPart_apply, complexDivergence]
  exact (map_sum Complex.reCLM
    (fun i : Fin 3 => (fderiv ℝ v x (EuclideanSpace.single i 1)) i) Finset.univ).symm

private theorem gradient_re_eq_finitePressureRealPart {f : Vec3 → ℂ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) :
    gradient (Complex.reCLM ∘ f) x = finitePressureRealPart (complexGradient f x) := by
  apply PiLp.ext
  intro i
  rw [finitePressureRealPart_apply]
  calc
    _ = ⟪gradient (Complex.reCLM ∘ f) x, EuclideanSpace.single i 1⟫_ℝ := by
      rw [EuclideanSpace.inner_single_right]
      simp
    _ = fderiv ℝ (Complex.reCLM ∘ f) x (EuclideanSpace.single i 1) := inner_gradient_left
    _ = _ := by rw [(Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]; rfl

private theorem ofLp_finiteFourierSum (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → ComplexEuclideanVec3) (z : UnitAddTorus (Fin 3)) :
    (finiteFourierSum s a z).ofLp = finiteFourierSum s (fun k => (a k).ofLp) z := by
  exact map_sum (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ))
    (fun k => mFourier k z • a k) s

/-- The real mean-zero Fourier potential solves the Poisson equation with the
divergence of the real trigonometric polynomial as its source. -/
theorem divergence_gradient_endpointFiniteFourierPressure
    (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → ComplexEuclideanVec3) (x : Vec3) :
    divergence (gradient (endpointFiniteFourierPressure s (fun k => (a k).ofLp))) x =
      divergence (fun y => periodicRealPartVector (finiteFourierSum s a (toUnitTorus y))) x := by
  let b : (Fin 3 → ℤ) → ComplexVec3 := fun k => (a k).ofLp
  let P (y : Vec3) := finiteFourierSum s (fun k => pressureCorrectionMode k (b k)) (toUnitTorus y)
  let V (y : Vec3) := finiteFourierSum s b (toUnitTorus y)
  let G (y : Vec3) := complexGradient P y
  have hP : ContDiff ℝ ∞ P := contDiff_lift_finiteFourierSum s _
  have hG : ContDiff ℝ ∞ G := by
    rw [show G = fun y => finiteFourierSum s
      (fun k => gradientMode k (pressureCorrectionMode k (b k))) (toUnitTorus y)
      from funext (complexGradient_lift_finiteFourierSum s _)]
    exact contDiff_lift_finiteFourierSum s _
  have hV : ContDiff ℝ ∞ V := contDiff_lift_finiteFourierSum s _
  have hg : gradient (endpointFiniteFourierPressure s b) = finitePressureRealPart ∘ G :=
    funext fun y => gradient_re_eq_finitePressureRealPart (hP.differentiable (by simp) y)
  have hv : (fun y => periodicRealPartVector (finiteFourierSum s a (toUnitTorus y))) =
      finitePressureRealPart ∘ V := by
    funext y
    change periodicRealPartVector (finiteFourierSum s a (toUnitTorus y)) =
      finitePressureRealPart (finiteFourierSum s b (toUnitTorus y))
    rw [← ofLp_finiteFourierSum s a]
    rfl
  rw [hg, hv, divergence_finitePressureRealPart (hG.differentiable (by simp) x),
    divergence_finitePressureRealPart (hV.differentiable (by simp) x)]
  exact congrArg Complex.re (complexLaplacian_lift_pressureCorrectionMode s b x)

/-- The finite pressure potential solves the negative divergence equation on the entire slice. -/
theorem divergence_gradient_truncatedParentSlicePressure (r : ℝ) (A : C(Labels, Vec3))
    (hA : RealTorusFourierBand r A) (x : Vec3) :
    divergence (gradient (truncatedParentSlicePressure r A)) x =
      -divergence (fun y => A (toUnitTorus y)) x := by
  let s := frequencyBand r
  let a := mFourierCoeff (endpointComplexifyContinuous A)
  have hSyn : finiteFourierSum s a = ⇑(endpointComplexifyContinuous A) :=
    finiteFourierSum_mFourierCoeff_eq_of_band _ r hA
  have hReal : (fun y => periodicRealPartVector (finiteFourierSum s a (toUnitTorus y))) =
      fun y => A (toUnitTorus y) := by
    funext y
    rw [hSyn]
    exact periodicRealPartVector_complexifyVector _
  unfold truncatedParentSlicePressure
  rw [gradient_truncatedParent_neg, divergence_truncatedParent_neg,
    divergence_gradient_endpointFiniteFourierPressure, hReal]

/-- Adding the slice pressure gradient gives the actual periodic Leray projection. -/
theorem add_gradient_truncatedParentSlicePressure_eq_projected (r : ℝ)
    (A : C(Labels, Vec3)) (hA : RealTorusFourierBand r A)
    (hSmooth : ContDiff ℝ ∞ (fun x => A (toUnitTorus x))) :
    (fun x => A (toUnitTorus x)) + gradient (truncatedParentSlicePressure r A) =
      periodicLerayHolderLift (fun x => A (toUnitTorus x)) := by
  let f (x : Vec3) := A (toUnitTorus x)
  let p : EndpointSmoothPotential :=
    ⟨truncatedParentSlicePressure r A, contDiff_truncatedParentSlicePressure r A,
      spatiallyPeriodic_truncatedParentSlicePressure r A⟩
  let g := gradient p.lift
  have hfper : SpatiallyPeriodic f := pullback_torusField_spatiallyPeriodic A
  have hgper : SpatiallyPeriodic g := p.periodic.gradient (p.smooth.differentiable (by simp))
  have hgSmooth : ContDiff ℝ ∞ g := contDiff_gradient_truncatedParent p.smooth
  have hsumPer : SpatiallyPeriodic (f + g) := fun n x => by
    change f (x + latticeVector n) + g (x + latticeVector n) = f x + g x
    rw [hfper, hgper]
  have hsumDiv (x : Vec3) : divergence (f + g) x = 0 := by
    rw [divergence_truncatedParent_add (hSmooth.differentiable (by simp) x)
      (hgSmooth.differentiable (by simp) x)]
    change divergence f x + divergence (gradient (truncatedParentSlicePressure r A)) x = 0
    rw [divergence_gradient_truncatedParentSlicePressure r A hA, add_neg_cancel]
  have hfixed : periodicLerayHolderLift (f + g) = f + g :=
    periodicLerayHolderLift_eq_self_of_divergence_free (hSmooth.add hgSmooth) hsumPer hsumDiv
  have hAdd := periodicLerayHolderLift_add hfper hgper
    (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hSmooth.of_le (by simp)) hfper)
    (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hgSmooth.of_le (by simp)) hgper)
  change f + g = periodicLerayHolderLift f
  rw [← hfixed, hAdd, show periodicLerayHolderLift g = 0 from
    periodicLerayHolderLift_gradient_eq_zero p, add_zero]

/-- The time derivative of an incompressible velocity on a closed slab is
incompressible, including at the endpoints. -/
theorem divergence_slabVelocityTimeDerivative {u : Velocity} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hdiv : ∀ r ∈ Icc 0 T, ∀ x, divergence (u r) x = 0) (x : Vec3) :
    divergence (fun y => derivWithin (fun r => u r y) (Icc 0 T) t) x = 0 := by
  let I := Icc (0 : ℝ) T
  let C : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
    ∑ i : Fin 3, (EuclideanSpace.proj i).comp
      (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))
  have hC (D : Vec3 →L[ℝ] Vec3) :
      C D = ∑ i : Fin 3, (D (EuclideanSpace.single i 1)) i := by
    simp [C]
  have hD : ContDiffOn ℝ 1 (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) (I ×ˢ univ) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT) hu
  have hx : ContDiffOn ℝ 1 (fun r => fderiv ℝ (u r) x) I :=
    hD.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, mem_univ x⟩)
  have hd := (hx.differentiableOn (by simp) t ht).hasDerivWithinAt
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
      (C (derivWithin (fun r => fderiv ℝ (u r) x) I t)) I t :=
    (C.hasFDerivAt.comp_hasDerivWithinAt t hd).congr_of_mem (fun r hr => by
      change 0 = C (fderiv ℝ (u r) x)
      rw [hC]
      exact (hdiv r hr x).symm) ht
  have hzero : C (derivWithin (fun r => fderiv ℝ (u r) x) I t) = 0 := by
    rw [← hc.derivWithin (uniqueDiffOn_Icc hT t ht), derivWithin_fun_const]
    rfl
  rw [divergence, (hasFDerivAt_slabVelocityTimeDerivative hT ht hu x).fderiv, ← hC]
  exact hzero

/-- Smooth Fourier coefficient paths give joint smoothness of the finite pressure
on the closed slab. -/
theorem contDiffOn_truncatedParentSlicePressure {a b : ℝ} (hab : a < b)
    (r : ℝ) (A : ℝ → C(Labels, Vec3))
    (hA : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => A z.1 (toUnitTorus z.2))
      (Icc a b ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t => truncatedParentSlicePressure r (A t)))
      (Icc a b ×ˢ (univ : Set Vec3)) := by
  let c (t : ℝ) (k : Fin 3 → ℤ) := mFourierCoeff (endpointComplexifyContinuous (A t)) k
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 =>
    -(finiteFourierSum (frequencyBand r) (fun k => pressureCorrectionMode k (c z.1 k).ofLp)
      (toUnitTorus z.2)).re) _
  apply ContDiffOn.neg
  apply Complex.reCLM.contDiff.comp_contDiffOn
  change ContDiffOn ℝ ∞
    (fun z : ℝ × Vec3 => ∑ k ∈ frequencyBand r, fourierMode k z.2 •
      pressureCorrectionMode k (c z.1 k).ofLp) _
  apply ContDiffOn.sum
  intro k _
  have hc : ContDiffOn ℝ ∞ (fun t => c t k) (Icc a b) :=
    contDiffOn_mFourierCoeff_of_truncatedParentLift
      (V := fun t x => A t (toUnitTorus x)) hab hA
      (fun t z => A t z) (fun _ _ _ => rfl) k
  have hp : ContDiffOn ℝ ∞ (fun t => pressureCorrectionMode k (c t k).ofLp) (Icc a b) := by
    unfold pressureCorrectionMode divergenceMode
    refine contDiffOn_const.mul (ContDiffOn.sum ?_)
    intro i _
    let L : ComplexEuclideanVec3 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
    exact contDiffOn_const.mul (L.contDiff.comp_contDiffOn hc)
  exact ((contDiff_fourierMode k).comp contDiff_snd).contDiffOn.smul
    (hp.comp contDiff_fst.contDiffOn (fun z hz => hz.1))

private theorem truncatedParent_smooth_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {F : ℝ → Vec3 → E}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (F t) := by
  exact contDiffOn_univ.mp (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- A jointly smooth solenoidal velocity in the cutoff band admits the real
mean-zero Poisson pressure on the full slab. The true Euler residual is its
actual periodic projected momentum. -/
theorem exists_truncatedParentPoissonPressure {T Λ : ℝ} (hT : 0 < T)
    (U : ℝ → C(Labels, Vec3))
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => U z.1 (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hband : ∀ t ∈ Icc 0 T, RealTorusFourierBand (2 * Λ) (U t))
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (fun y => U t (toUnitTorus y)) x = 0) :
    let u : Velocity := fun t x => U t (toUnitTorus x)
    ∃ p : Pressure, ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t) ∧ (∫ x in centeredCell, p t x) = 0 ∧
        (∀ x, divergence (gradient (p t)) x =
          -LinearMap.trace ℝ Vec3 ((fderiv ℝ (u t) x).comp (fderiv ℝ (u t) x)).toLinearMap) ∧
        momentumResidual (Icc 0 T) u p t = closedSlabLerayMomentum 0 T u t := by
  classical
  intro u
  let adv : Velocity := fun t x => fderiv ℝ (u t) x (u t x)
  have hUj : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) := hU
  have hUs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (u t) :=
    truncatedParent_smooth_slice hUj ht
  have hUp (t : ℝ) : SpatiallyPeriodic (u t) := pullback_torusField_spatiallyPeriodic (U t)
  have hAdv : ContDiffOn ℝ ∞ (Function.uncurry adv) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    exact (contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT)
      (by simpa using hUj)).clm_apply hUj
  have hAdvPer (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (adv t) := by
    intro n x
    change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
      fderiv ℝ (u t) x (u t x)
    rw [(hUp t).fderiv ((hUs t ht).differentiable (by simp)), hUp]
  have hEither (t : ℝ) : ∃ A : C(Labels, Vec3), t ∈ Icc 0 T →
      ∀ x, A (toUnitTorus x) = adv t x := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨A, hA⟩ := (hAdvPer t ht).exists_continuousTorusFunction
        (truncatedParent_smooth_slice hAdv ht).continuous
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun ht' => (ht ht').elim⟩
  choose A hA using hEither
  have hArep {t : ℝ} (ht : t ∈ Icc 0 T) : (fun x => A t (toUnitTorus x)) = adv t :=
    funext (hA t ht)
  have hAb (t : ℝ) (ht : t ∈ Icc 0 T) : RealTorusFourierBand (4 * Λ) (A t) :=
    fun k hk => mFourierCoeff_advection_eq_zero_outside_band (U t) (A t)
      (hband t ht) (hA t ht) k hk
  let p : Pressure := fun t => truncatedParentSlicePressure (4 * Λ) (A t)
  have hPj : ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_truncatedParentSlicePressure hT (4 * Λ) A
      (hAdv.congr (fun z hz => hA z.1 hz.1 z.2))
  refine ⟨p, hPj, fun t ht => ⟨spatiallyPeriodic_truncatedParentSlicePressure _ _,
    integral_truncatedParentSlicePressure _ _, ?_, ?_⟩⟩
  · intro x
    have h := divergence_gradient_truncatedParentSlicePressure (4 * Λ) (A t) (hAb t ht) x
    rw [hArep ht, divergence_advection_eq_trace_square ((hUs t ht).of_le (by simp))
      (hdiv t ht)] at h
    exact h
  · let W (x : Vec3) := derivWithin (fun r => u r x) (Icc 0 T) t
    have hWj : ContDiffOn ℝ ∞
        (Function.uncurry (fun t x => derivWithin (fun r => u r x) (Icc 0 T) t))
        (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_sliceTimeDerivWithin_Icc hT hUj
    have hWs : ContDiff ℝ ∞ W := truncatedParent_smooth_slice hWj ht
    have hWp : SpatiallyPeriodic W := fun n x =>
      derivWithin_congr (fun r _ => hUp r n x) (hUp t n x)
    have hWdiv : ∀ x, divergence W x = 0 :=
      divergence_slabVelocityTimeDerivative hT ht (hUj.of_le (by simp)) hdiv
    have hW := periodicLerayHolderLift_eq_self_of_divergence_free hWs hWp hWdiv
    have hAs := truncatedParent_smooth_slice hAdv ht
    have hAp := hAdvPer t ht
    have hG := add_gradient_truncatedParentSlicePressure_eq_projected
      (4 * Λ) (A t) (hAb t ht) (by rw [hArep ht]; exact hAs)
    rw [hArep ht] at hG
    change W + adv t + gradient (p t) = periodicLerayHolderLift (W + adv t)
    rw [periodicLerayHolderLift_add hWp hAp
      (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hWs.of_le (by simp)) hWp)
      (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hAs.of_le (by simp)) hAp),
      hW, add_assoc]
    exact congrArg (W + ·) hG

/-- For the actual cutoff of the approximate velocity, the constructed
pressure turns the projected cutoff equation into the true residual equation. -/
theorem exists_realFourierCutoffPoissonPressure {T Λ : ℝ} (hT : 0 < T)
    {V RV : Velocity} (pressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
      fderiv ℝ (V t) x (V t x) + gradient (pressure t).lift x = RV t x)
    (gV gRV : ℝ → C(Labels, Vec3))
    (hgV : ∀ t ∈ Icc 0 T, ∀ x, gV t (toUnitTorus x) = V t x)
    (hgRV : ∀ t ∈ Icc 0 T, ∀ x, gRV t (toUnitTorus x) = RV t x)
    {ψ : Vec3 → ℝ} (hEven : Function.Even ψ) :
    let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)
    ∃ p : Pressure, ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t) ∧ (∫ x in centeredCell, p t x) = 0 ∧
        (∀ x, divergence (gradient (p t)) x =
          -LinearMap.trace ℝ Vec3 ((fderiv ℝ (u t) x).comp (fderiv ℝ (u t) x)).toLinearMap) ∧
        momentumResidual (Icc 0 T) u p t =
          truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t) := by
  intro u
  let U (t : ℝ) : C(Labels, Vec3) := by
    refine ⟨realVectorFourierCutoff ψ Λ (gV t), periodicRealPartVector.continuous.comp ?_⟩
    unfold smoothFourierCutoff finiteFourierSum
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  have hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => U z.1 (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_lift_realVectorFourierCutoff_of_coefficients ψ Λ gV fun k _ =>
      contDiffOn_mFourierCoeff_of_truncatedParentLift hT hV (fun t z => gV t z) hgV k
  have hB (t : ℝ) (_ : t ∈ Icc 0 T) : RealTorusFourierBand (2 * Λ) (U t) := by
    intro k hk
    change mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ (gV t) z)) k = 0
    rw [mFourierCoeff_realVectorFourierCutoff_of_even hEven,
      ite_eq_right (fun hm => (not_lt_of_ge ((mem_frequencyBand _ _).mp hm)) hk)]
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) :
      ∀ x, divergence (fun y => U t (toUnitTorus y)) x = 0 := by
    change ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus y)) x = 0
    have hrep : (fun y => gV t (toUnitTorus y)) = V t := funext (hgV t ht)
    apply divergence_free_lift_realVectorFourierCutoff hEven Λ (gV t)
    · rw [hrep]; exact truncatedParent_smooth_slice hV ht
    · rw [hrep]; exact hVdiv t ht
  obtain ⟨p, hp, hSlice⟩ := exists_truncatedParentPoissonPressure hT U hU hB hD
  refine ⟨p, hp, fun t ht => ?_⟩
  obtain ⟨hper, hmean, hPois, hRes⟩ := hSlice t ht
  have hProj := closedSlabLerayMomentum_realFourierCutoff hT pressure hV hVper hVdiv hMom
    gV gRV hgV hgRV hEven Λ t ht
  exact ⟨hper, hmean, hPois, hRes.trans hProj⟩

theorem truncatedParentSlicePressure_stationaryShear (r σ : ℝ) (A : C(Labels, Vec3))
    (hA : ∀ x, A (toUnitTorus x) = fderiv ℝ (stationaryShear σ) x (stationaryShear σ x)) :
    truncatedParentSlicePressure r A = 0 := by
  have hz (z : Labels) : A z = 0 := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [hA, stationaryShear_advection]
  funext x
  have hc (k : Fin 3 → ℤ) : mFourierCoeff (endpointComplexifyContinuous A) k = 0 := by
    simp [mFourierCoeff, endpointComplexifyContinuous, hz]
  simp [truncatedParentSlicePressure, endpointFiniteFourierPressure, hc,
    finiteFourierSum, pressureCorrectionMode, divergenceMode]

end

end TorusEuler
