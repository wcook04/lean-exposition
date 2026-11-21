import TorusEuler.PeriodicEulerLimit
import TorusEuler.OffOriginPressureAssembly
import TorusEuler.EulerLimitClosure

/-! The complex tensor Poisson identity for the real periodic Euler pressure. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

private theorem pressurePoisson_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Ico 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (f t) := by
  have h := hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨ht, mem_univ x⟩)
  exact contDiffOn_univ.mp h

private theorem pressurePoisson_leray_fixed_divergence {f : Vec3 → Vec3}
    (hs : ContDiff ℝ ∞ f) (hp : SpatiallyPeriodic f) (hFix : periodicLerayHolderLift f = f) :
    ∀ x, divergence f x = 0 := by
  obtain ⟨q, hq, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hp
    (spatialHolderHalf_of_contDiff_periodic hs hp 0)
  have hfixed : endpointStrongSpatialLeray q = q := by
    apply HalfHolder.ext
    intro z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    have h := congrFun hFix x
    rw [← funext hq, periodicLerayHolderLift_pullback] at h
    exact h
  exact (endpointTorusGradientPairing_iff_divergence_free hs hq).1
    ((mem_endpointHalfHolderSolenoidal q).1 ((endpointStrongSpatialLeray_fixed_iff q).1 hfixed))

private theorem pressurePoisson_timeDerivative_divergence
    {T : ℝ} {u : Velocity} {p : Pressure} (h : IsEulerSolution T u p)
    {t : ℝ} (ht : t ∈ Ico 0 T) : ∀ x, divergence (timeDerivative T u t) x = 0 := by
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hS : 0 < S := ht.1.trans_lt htS
  have hsub : Icc (0 : ℝ) S ⊆ Ico 0 T := fun _ hr => ⟨hr.1, hr.2.trans_lt hST⟩
  have ht' : t ∈ Icc 0 S := ⟨ht.1, htS.le⟩
  have hFix := periodicLerayHolderLift_sliceTimeDerivWithin_eq_self hS
    (h.smooth_velocity.mono (prod_mono_left hsub))
    (fun r hr => h.periodic_velocity r (hsub hr))
    (fun r hr => h.incompressible r (hsub hr)) ht'
  have hEq : (fun x => derivWithin (fun r => u r x) (Icc 0 S) t) = timeDerivative T u t := by
    funext x
    exact ((h.hasDerivWithinAt_velocity ht x).mono hsub).derivWithin (uniqueDiffOn_Icc hS t ht')
  rw [hEq] at hFix
  have hW : ContDiffOn ℝ ∞ (Function.uncurry (timeDerivative T u)) (Ico 0 T ×ˢ univ) :=
    contDiffOn_timeDerivative_of_joint_contDiff (by simpa using h.smooth_velocity)
  have hPer : SpatiallyPeriodic (timeDerivative T u t) := fun n x =>
    derivWithin_congr (fun r hr => h.periodic_velocity r hr n x) (h.periodic_velocity t ht n x)
  exact pressurePoisson_leray_fixed_divergence (pressurePoisson_slice hW ht) hPer hFix

private theorem pressurePoisson_fderiv_ofReal {f : Vec3 → ℝ} {x : Vec3}
    (h : DifferentiableAt ℝ f x) (v : Vec3) :
    fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℂ) := by
  have heq := (Complex.ofRealCLM.hasFDerivAt.comp x h.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y : ℂ)) x = _ at heq
  rw [heq]
  rfl

private theorem pressurePoisson_coordHessian_ofReal {f : Vec3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vec3) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z : ℂ)) y (EuclideanSpace.single j 1))
        x (EuclideanSpace.single i 1) =
      (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1))
        x (EuclideanSpace.single i 1) : ℂ) := by
  have hj : (fun y => fderiv ℝ (fun z => (f z : ℂ)) y (EuclideanSpace.single j 1)) =
      fun y => (fderiv ℝ f y (EuclideanSpace.single j 1) : ℂ) := by
    funext y
    exact pressurePoisson_fderiv_ofReal (hf.differentiable (by norm_num) y) _
  have hc : ContDiff ℝ 1 (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  rw [hj, pressurePoisson_fderiv_ofReal (hc.differentiable (by simp) x)]

private theorem pressurePoisson_complexLaplacian {p : Vec3 → ℝ} (hp : ContDiff ℝ 2 p) (x : Vec3) :
    complexLaplacian (fun y => (p y : ℂ)) x = (divergence (gradient p) x : ℂ) := by
  let q := fun y => (p y : ℂ)
  have hq : ContDiff ℝ 2 q := Complex.ofRealCLM.contDiff.comp hp
  have hgrad : ContDiff ℝ 1 (complexGradient q) :=
    contDiff_pi.mpr fun i => (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  unfold complexLaplacian complexDivergence divergence
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  let L : ComplexVec3 →L[ℝ] ℂ := ContinuousLinearMap.proj i
  have hL : L ∘ complexGradient q = fun y => fderiv ℝ q y (EuclideanSpace.single i 1) := rfl
  have hchain := (L.hasFDerivAt.comp x ((hgrad.differentiable (by simp) x).hasFDerivAt)).fderiv
  rw [hL] at hchain
  change L (fderiv ℝ (complexGradient q) x (EuclideanSpace.single i 1)) = _
  rw [← ContinuousLinearMap.comp_apply, ← hchain, fderiv_gradient_single_coord hp]
  exact pressurePoisson_coordHessian_ofReal hp x i i

private theorem pressurePoisson_coord_divTensor {F : Vec3 → MomentumTensor}
    (hs : ContDiff ℝ 2 F) (i : Fin 3) :
    (fun y => ((momentumTensorDivergence ∘ fderiv ℝ F) y) i) =
      fun y => ∑ j : Fin 3, fderiv ℝ (fun z => (F z j) i) y (EuclideanSpace.single j 1) := by
  funext y
  simp only [Function.comp_apply, momentumTensorDivergence_apply]
  change (EuclideanSpace.proj i) (∑ j : Fin 3, fderiv ℝ F y (EuclideanSpace.single j 1) j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let L : MomentumTensor →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (ContinuousLinearMap.proj j)
  have hchain := (L.hasFDerivAt.comp y (hs.differentiable (by norm_num) y).hasFDerivAt).fderiv
  change ((ContinuousLinearMap.proj j : MomentumTensor →L[ℝ] Vec3)
    (fderiv ℝ F y (EuclideanSpace.single j 1))) i = _
  exact (congrArg (fun J : Vec3 →L[ℝ] ℝ => J (EuclideanSpace.single j 1)) hchain).symm

private theorem pressurePoisson_complexTensorDoubleDivergence {v : Vec3 → Vec3}
    (hv : ContDiff ℝ 2 v) (x : Vec3) :
    pressureTensorDoubleDivergence (pressureVelocityTensor v) x =
      (divergence (momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (v y) (v y))) x : ℂ) := by
  let F := fun y => momentumTensor (v y) (v y)
  let w := momentumTensorDivergence ∘ fderiv ℝ F
  have hF : ContDiff ℝ 2 F := (momentumTensor.contDiff.comp hv).clm_apply hv
  have hw : ContDiff ℝ 1 w := momentumTensorDivergence.contDiff.comp
    (hF.fderiv_right (m := 1) (by norm_num))
  have hcoord (i j : Fin 3) : ContDiff ℝ 2 (fun y => (F y j) i) := by
    let L : MomentumTensor →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (ContinuousLinearMap.proj j)
    change ContDiff ℝ 2 (L ∘ F)
    exact L.contDiff.comp hF
  change _ = (divergence w x : ℂ)
  unfold pressureTensorDoubleDivergence divergence
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  let P : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj i
  have hchain := (P.hasFDerivAt.comp x ((hw.differentiable (by simp) x).hasFDerivAt)).fderiv
  change _ = ((P (fderiv ℝ w x (EuclideanSpace.single i 1))) : ℂ)
  rw [← ContinuousLinearMap.comp_apply, ← hchain]
  change _ = (fderiv ℝ (fun y => (w y) i) x (EuclideanSpace.single i 1) : ℂ)
  rw [pressurePoisson_coord_divTensor hF]
  have hd (j : Fin 3) (_ : j ∈ (Finset.univ : Finset (Fin 3))) :
      DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => (F z j) i) y (EuclideanSpace.single j 1)) x :=
    (((hcoord i j).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by simp) x
  have hsum := fderiv_sum hd
  change fderiv ℝ (fun y => ∑ j : Fin 3, fderiv ℝ (fun z => (F z j) i) y (EuclideanSpace.single j 1)) x = _ at hsum
  rw [hsum, sum_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  change fderiv ℝ (fun y => fderiv ℝ (fun z => pressureVelocityTensor v z i j)
    y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) = _
  simp only [pressureVelocityTensor, velocityPressureTensor_apply]
  have heq : (fun z => (F z j) i) = fun z => v z i * v z j := by
    funext z
    simp only [F, momentumTensor_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]
  have heqC : (fun z => ((F z j) i : ℂ)) = fun z => Complex.ofReal (v z i * v z j) := by
    funext z
    exact congrArg Complex.ofReal (congrFun heq z)
  rw [← heqC]
  exact pressurePoisson_coordHessian_ofReal (hcoord i j) x i j

/-- The normalized real pressure of a smooth periodic Euler solution, complexified, satisfies the
actual tensor Poisson equation used to identify the off-origin pressure multiplier. -/
theorem IsEulerSolution.complexPressureTensorPoisson {T : ℝ} {u : Velocity} {p : Pressure}
    (h : IsEulerSolution T u p) {t : ℝ} (ht : t ∈ Ico 0 T) :
    ContDiff ℝ 2 (fun x => (p t x : ℂ)) ∧ SpatiallyPeriodic (fun x => (p t x : ℂ)) ∧
      (∫ x in centeredCell, (p t x : ℂ)) = 0 ∧
      ∀ x, complexLaplacian (fun y => (p t y : ℂ)) x =
        -pressureTensorDoubleDivergence (pressureVelocityTensor (u t)) x := by
  have hp : ContDiff ℝ 2 (p t) := (pressurePoisson_slice h.smooth_pressure ht).of_le (by simp)
  have hu : ContDiff ℝ 2 (u t) := (h.contDiff_velocity_slice ht).of_le (by simp)
  refine ⟨Complex.ofRealCLM.contDiff.comp hp, fun n x => congrArg Complex.ofReal (h.periodic_pressure t ht n x),
    ?_, fun x => ?_⟩
  · rw [integral_complex_ofReal, h.mean_zero_pressure t ht, Complex.ofReal_zero]
  let W := timeDerivative T u t
  let A := fun x => fderiv ℝ (u t) x (u t x)
  let G := gradient (p t)
  have hWj : ContDiffOn ℝ ∞ (Function.uncurry (timeDerivative T u)) (Ico 0 T ×ˢ univ) :=
    contDiffOn_timeDerivative_of_joint_contDiff (by simpa using h.smooth_velocity)
  have hW : DifferentiableAt ℝ W x := (pressurePoisson_slice hWj ht).differentiable (by simp) x
  have hA : DifferentiableAt ℝ A x :=
    (((hu.fderiv_right (m := 1) (by norm_num)).clm_apply (hu.of_le (by norm_num))).differentiable (by simp)) x
  have hG : DifferentiableAt ℝ G x :=
    (((InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp
      (hp.fderiv_right (m := 1) (by norm_num))).differentiable (by simp)) x
  have hMom : (fun y => W y + A y + G y) = (fun _ => 0) := funext (h.momentum t ht)
  have hD : HasFDerivAt (fun y => W y + A y + G y)
      (fderiv ℝ W x + fderiv ℝ A x + fderiv ℝ G x) x :=
    (hW.hasFDerivAt.add hA.hasFDerivAt).add hG.hasFDerivAt
  have hDiv : divergence (fun y => W y + A y + G y) x = divergence W x + divergence A x + divergence G x := by
    unfold divergence
    rw [hD.fderiv]
    simp only [_root_.add_apply, PiLp.add_apply, Finset.sum_add_distrib]
  rw [hMom, pressurePoisson_timeDerivative_divergence h ht x, zero_add] at hDiv
  have hZero : divergence (fun _ => (0 : Vec3)) x = 0 := by simp [divergence]
  rw [hZero] at hDiv
  have hTensor : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) = A :=
    momentumTensorDivergence_self_eq_advection (hu.differentiable (by norm_num)) (h.incompressible t ht)
  rw [pressurePoisson_complexLaplacian hp, pressurePoisson_complexTensorDoubleDivergence hu, hTensor,
    show divergence (gradient (p t)) x = -divergence A x by change divergence G x = _; linarith,
    Complex.ofReal_neg]

end

end TorusEuler
