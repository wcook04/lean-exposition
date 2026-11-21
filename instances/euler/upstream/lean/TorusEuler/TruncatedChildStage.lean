import TorusEuler.InductionChildEstimates
import TorusEuler.PressureHessianMultiplier
import TorusEuler.TruncatedParentPoissonPressure

/-! Assembly of the frequency cutoff and next-parent estimates. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The spatial order-zero half-Hölder norm controls pointwise values. -/
theorem norm_apply_le_spatialHolderHalfNorm_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec3 → E} (hf : SpatialHolderHalf 0 f) (x : Vec3) :
    ‖f x‖ ≤ spatialHolderHalfNorm 0 f := by
  obtain ⟨_, hs, hq⟩ := (spatialHolderHalf_zero_iff f).mp hf
  have hq₀ : 0 ≤ spatialHolderHalfSeminorm f := by
    have h := le_ciSup hq ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient f (0, 0) = 0 by simp [spatialHolderHalfQuotient]] at h
    exact h
  rw [spatialHolderHalfNorm_zero_eq]
  exact (norm_le_spatialSupNorm hs x).trans (le_add_of_nonneg_right hq₀)

private theorem cutoffPressure_spatialHolderHalf_fderiv {f : Vec3 → Vec3}
    (hf : SpatialHolderHalf 1 f) : SpatialHolderHalf 0 (fderiv ℝ f) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ f) ≤ spatialHolderHalfNorm 1 f := by
  let I := ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)
  have h := spatialHolderHalf_contraction_fderiv I (m := 0) hf
  change SpatialHolderHalf 0 (fderiv ℝ f) ∧
    spatialHolderHalfNorm 0 (fderiv ℝ f) ≤ ‖I‖ * spatialHolderHalfNorm 1 f at h
  simpa only [I, ContinuousLinearMap.norm_id, one_mul] using h

private theorem cutoffPressure_descend_fderiv {f : Vec3 → Vec3}
    (hf : ContDiff ℝ ∞ f) (hper : SpatiallyPeriodic f) :
    ∃ F : HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3),
      (∀ x, HalfHolder.eval (toUnitTorus x) F = fderiv ℝ f x) ∧
      ‖F‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm 1 f := by
  have hD := cutoffPressure_spatialHolderHalf_fderiv (spatialHolderHalf_of_contDiff_periodic hf hper 1)
  obtain ⟨F, hF, hN⟩ := exists_halfHolder_of_spatialHolderHalf_zero
    (hper.fderiv (hf.differentiable (by simp))) hD.1
  exact ⟨F, hF, hN.trans (mul_le_mul_of_nonneg_left hD.2 (Real.sqrt_nonneg _))⟩

/-- The periodic Poisson pressure difference obeys the cutoff estimate in the physical half-Hölder norm. -/
theorem spatialHolderHalfNorm_cutoffPressureHessian_of_residual_le
    {u v w R : Vec3 → Vec3} {p pi : Vec3 → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hRs : ContDiff ℝ ∞ R)
    (hp : ContDiff ℝ ∞ p) (hpi : ContDiff ℝ ∞ pi)
    (huper : SpatiallyPeriodic u) (hvper : SpatiallyPeriodic v) (hRper : SpatiallyPeriodic R)
    (hpper : SpatiallyPeriodic p) (hpiper : SpatiallyPeriodic pi)
    (hdivV : ∀ x, divergence v x = 0) (hw : Differentiable ℝ w)
    (hdivW : ∀ x, divergence w x = 0)
    (hP : ∀ x, divergence (gradient p) x =
      -LinearMap.trace ℝ Vec3 ((fderiv ℝ u x).comp (fderiv ℝ u x)).toLinearMap)
    (hR : ∀ x, w x + fderiv ℝ v x (v x) + gradient pi x = R x) :
    spatialHolderHalfNorm 0 (fderiv ℝ (gradient (fun y => p y - pi y))) ≤
      (24 * ‖pressureHessianMultiplier‖) * (spatialHolderHalfNorm 1 (u - v) *
        (spatialHolderHalfNorm 1 u + spatialHolderHalfNorm 1 v) + spatialHolderHalfNorm 1 R) := by
  let d := fun x => p x - pi x
  have hd : ContDiff ℝ ∞ d := hp.sub hpi
  have hdper : SpatiallyPeriodic d := fun n x => by simp only [d, hpper n x, hpiper n x]
  have hG : ContDiff ℝ ∞ (gradient d) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (hd.fderiv_right (m := ∞) (by simp))
  have hGper : SpatiallyPeriodic (gradient d) := hdper.gradient (hd.differentiable (by simp))
  have hH : ContDiff ℝ ∞ (fderiv ℝ (gradient d)) := hG.fderiv_right (m := ∞) (by simp)
  have hHper : SpatiallyPeriodic (fderiv ℝ (gradient d)) := hGper.fderiv (hG.differentiable (by simp))
  have hsubper : SpatiallyPeriodic (u - v) := fun n x => by
    simp only [Pi.sub_apply, huper n x, hvper n x]
  obtain ⟨U, hU, hUb⟩ := cutoffPressure_descend_fderiv hu huper
  obtain ⟨V, hV, hVb⟩ := cutoffPressure_descend_fderiv hv hvper
  obtain ⟨D, hD, hDb⟩ := cutoffPressure_descend_fderiv (hu.sub hv) hsubper
  obtain ⟨DR, hDR, hDRb⟩ := cutoffPressure_descend_fderiv hRs hRper
  obtain ⟨H, hHrep, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hHper
    (spatialHolderHalf_of_contDiff_periodic hH hHper 0)
  obtain ⟨pDiff, hpDiff⟩ := hdper.exists_continuousTorusFunction hd.continuous
  have hDeq : U - V = D := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    simp only [map_sub, hU, hV, hD]
    rw [fderiv_fun_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  have hNorm := norm_cutoffPressureHessian_of_residual_le U V DR H
    (hv.of_le (by simp)) (hp.of_le (by simp)) (hpi.of_le (by simp)) hdper pDiff hpDiff
    hU hV hDR hHrep hdivV hw hdivW hP hR
  rw [hDeq] at hNorm
  have hPull : spatialHolderHalfNorm 0 (fderiv ℝ (gradient d)) ≤ 2 * ‖H‖ := by
    have h := (spatialHolderHalf_zero_of_halfHolder H).2
    rwa [funext hHrep] at h
  let a := spatialHolderHalfNorm 1 (u - v)
  let b := spatialHolderHalfNorm 1 u + spatialHolderHalfNorm 1 v
  let c := spatialHolderHalfNorm 1 R
  have hS : ‖U‖ + ‖V‖ ≤ Real.sqrt 2 * b := by
    simpa only [b, mul_add] using add_le_add hUb hVb
  have hD0 : 0 ≤ Real.sqrt 2 * a := (norm_nonneg D).trans hDb
  have hc : 0 ≤ c := (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.2 (by norm_num))).1
    ((norm_nonneg DR).trans hDRb)
  have h1 : ‖D‖ * (‖U‖ + ‖V‖) ≤ 2 * (a * b) := by
    calc
      _ ≤ (Real.sqrt 2 * a) * (Real.sqrt 2 * b) :=
        mul_le_mul hDb hS (add_nonneg (norm_nonneg _) (norm_nonneg _)) hD0
      _ = 2 * (a * b) := by
        calc
          _ = Real.sqrt 2 ^ 2 * (a * b) := by ring
          _ = _ := by rw [Real.sq_sqrt (by norm_num)]
  have h2 : ‖DR‖ ≤ 2 * c := hDRb.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_left (by norm_num) |>.2 (by norm_num)) hc)
  have h3 : 6 * ‖D‖ * (‖U‖ + ‖V‖) + 3 * ‖DR‖ ≤ 12 * (a * b + c) := by
    rw [mul_assoc 6]
    linarith
  change spatialHolderHalfNorm 0 (fderiv ℝ (gradient d)) ≤ _ * (a * b + c)
  calc
    _ ≤ 2 * ‖H‖ := hPull
    _ ≤ 2 * (‖pressureHessianMultiplier‖ * (6 * ‖D‖ * (‖U‖ + ‖V‖) + 3 * ‖DR‖)) :=
      mul_le_mul_of_nonneg_left hNorm (by norm_num)
    _ ≤ 2 * (‖pressureHessianMultiplier‖ * (12 * (a * b + c))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg pressureHessianMultiplier)) (by norm_num)
    _ = _ := by ring

private theorem cutoff_spatial_level_nonneg {f : Vec3 → Vec3} {P m : ℕ}
    (hf : SpatialHolderHalf P f) (hm : m ≤ P) :
    0 ≤ spatialSupNorm (iteratedFDeriv ℝ m f) +
      spatialHolderHalfSeminorm (iteratedFDeriv ℝ m f) := by
  apply add_nonneg ((norm_nonneg _).trans (norm_le_spatialSupNorm (hf.2 m hm).1 0))
  have h := le_ciSup (hf.2 m hm).2 ((0 : Vec3), (0 : Vec3))
  rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ m f) (0, 0) = 0 by
    simp [spatialHolderHalfQuotient]] at h
  exact h

private theorem cutoff_spatial_norm_mono {f : Vec3 → Vec3} {P m : ℕ}
    (hf : SpatialHolderHalf P f) (hm : m ≤ P) :
    SpatialHolderHalf m f ∧ spatialHolderHalfNorm m f ≤ spatialHolderHalfNorm P f := by
  refine ⟨⟨hf.1.of_le (by exact_mod_cast hm), fun j hj => hf.2 j (hj.trans hm)⟩, ?_⟩
  unfold spatialHolderHalfNorm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hm 1))
  exact fun j hj _ => cutoff_spatial_level_nonneg hf (by simpa using hj)

private theorem cutoff_spatial_norm_neg {f : Vec3 → Vec3} {m : ℕ}
    (hf : SpatialHolderHalf m f) : SpatialHolderHalf m (-f) ∧
      spatialHolderHalfNorm m (-f) = spatialHolderHalfNorm m f := by
  have hsup (j : ℕ) : (fun x => ‖iteratedFDeriv ℝ j (-f) x‖) =
      fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    simp only [iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
  have hq (j : ℕ) : spatialHolderHalfQuotient (iteratedFDeriv ℝ j (-f)) =
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) := by
    rw [iteratedFDeriv_neg]
    funext p
    simp only [spatialHolderHalfQuotient, Pi.neg_apply, neg_sub_neg]
    rw [norm_sub_rev]
  refine ⟨⟨hf.1.neg, fun j hj => ?_⟩, ?_⟩
  · rw [hsup j, hq j]
    exact hf.2 j hj
  · unfold spatialHolderHalfNorm
    apply Finset.sum_congr rfl
    intro j _
    simp only [spatialSupNorm, spatialHolderHalfSeminorm, hsup j, hq j]

/-- The velocity difference, in the sign used for the child increment. -/
theorem spatialHolderHalfNorm_cutoffVelocityDifference
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {P m : ℕ} (hm : m ≤ P)
    (hg : SpatialHolderHalf P (fun x => g (toUnitTorus x))) :
    let V : Vec3 → Vec3 := fun x => g (toUnitTorus x)
    let u : Vec3 → Vec3 := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf m (u - V) ∧ spatialHolderHalfNorm m (u - V) ≤
      cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) P *
        Λ ^ ((m : ℤ) - P) * spatialHolderHalfNorm P V := by
  intro V u
  have h := spatialHolderHalfNorm_realVectorCutoffTail hψ hs hunit hΛ g hm hg
  change SpatialHolderHalf m (V - u) ∧ _ at h
  have hNeg := cutoff_spatial_norm_neg h.1
  rw [neg_sub] at hNeg
  exact ⟨hNeg.1, hNeg.2.trans_le h.2⟩

/-- The quadratic velocity factor in the cutoff pressure error has the
same depth-dependent scale as the projected residual. -/
theorem spatialHolderHalfNorm_cutoffPressureTailProduct
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {P : ℕ} (hP : 2 ≤ P)
    (hg : SpatialHolderHalf P (fun x => g (toUnitTorus x))) :
    let V : Vec3 → Vec3 := fun x => g (toUnitTorus x)
    let u : Vec3 → Vec3 := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    let C := cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) P
    spatialHolderHalfNorm 1 (u - V) * (spatialHolderHalfNorm 1 u + spatialHolderHalfNorm 1 V) ≤
      C * (2 + C) * (Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2) := by
  intro V u C
  let M := spatialHolderHalfNorm P V
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (norm_iteratedFDeriv_le_spatialHolderHalfNorm hg (Nat.zero_le P) 0)
  have hC : 0 ≤ C := by
    change 0 ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) P
    unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
    positivity
  have hΛ₀ : 0 < Λ := zero_lt_one.trans_le hΛ
  have hv := cutoff_spatial_norm_mono hg (one_le_two.trans hP)
  have ht := spatialHolderHalfNorm_cutoffVelocityDifference hψ hs hunit hΛ₀ g
    (show 1 ≤ P from one_le_two.trans hP) hg
  change SpatialHolderHalf 1 (u - V) ∧
    spatialHolderHalfNorm 1 (u - V) ≤ C * Λ ^ ((1 : ℤ) - P) * M at ht
  have htNonneg : 0 ≤ spatialHolderHalfNorm 1 (u - V) := (norm_nonneg _).trans
    (norm_iteratedFDeriv_le_spatialHolderHalfNorm ht.1 (Nat.zero_le 1) 0)
  have hpow (n : ℤ) (hn : (1 : ℤ) - P ≤ n) : Λ ^ ((1 : ℤ) - P) ≤ Λ ^ n :=
    zpow_le_zpow_right₀ hΛ hn
  have htSmall : spatialHolderHalfNorm 1 (u - V) ≤ C * M := by
    calc
      _ ≤ C * Λ ^ ((1 : ℤ) - P) * M := ht.2
      _ ≤ C * Λ ^ (0 : ℤ) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow 0 (by omega)) hC) hM
      _ = C * M := by rw [zpow_zero, mul_one]
  have htDepth : spatialHolderHalfNorm 1 (u - V) ≤ C * Λ ^ ((2 : ℤ) - P) * M :=
    ht.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpow ((2 : ℤ) - P) (by omega)) hC) hM)
  have hu : spatialHolderHalfNorm 1 u ≤ (1 + C) * M := by
    calc
      _ = spatialHolderHalfNorm 1 ((u - V) + V) := by rw [sub_add_cancel]
      _ ≤ spatialHolderHalfNorm 1 (u - V) + spatialHolderHalfNorm 1 V :=
        (spatialHolderHalf_add_exact ht.1 hv.1).2
      _ ≤ C * M + M := add_le_add htSmall hv.2
      _ = (1 + C) * M := by ring
  calc
    _ ≤ spatialHolderHalfNorm 1 (u - V) * ((1 + C) * M + M) :=
      mul_le_mul_of_nonneg_left (add_le_add hu hv.2) htNonneg
    _ ≤ (C * Λ ^ ((2 : ℤ) - P) * M) * ((1 + C) * M + M) :=
      mul_le_mul_of_nonneg_right htDepth (by positivity)
    _ = C * (2 + C) * (Λ ^ ((2 : ℤ) - P) * M ^ 2) := by ring
    _ ≤ _ := by gcongr; linarith

/-- One application of the final Fourier cutoff to the approximate velocity.
Its pressure and residual are the physical fields on the closed slab. -/
structure TruncatedChildStage (T Λ : ℝ) (ψ : Vec3 → ℝ)
    (V RV : Velocity) where
  approximateTorus : ℝ → C(Labels, Vec3)
  approximateResidualTorus : ℝ → C(Labels, Vec3)
  torusVelocity : ℝ → C(Labels, Vec3)
  pressure : Pressure
  approximate_rep : ∀ t ∈ Icc 0 T, ∀ x, approximateTorus t (toUnitTorus x) = V t x
  approximateResidual_rep : ∀ t ∈ Icc 0 T, ∀ x,
    approximateResidualTorus t (toUnitTorus x) = RV t x
  cutoff : ∀ t z, torusVelocity t z = realVectorFourierCutoff ψ Λ (approximateTorus t) z
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => torusVelocity z.1 (toUnitTorus z.2))
    (Icc 0 T ×ˢ (univ : Set Vec3))
  odd_velocity : ∀ t ∈ Icc 0 T, Function.Odd (fun x => torusVelocity t (toUnitTorus x))
  divergence_free : ∀ t ∈ Icc 0 T, ∀ x, divergence (fun y => torusVelocity t (toUnitTorus y)) x = 0
  velocity_band : ∀ t ∈ Icc 0 T, RealTorusFourierBand (2 * Λ) (torusVelocity t)
  smooth_pressure : ContDiffOn ℝ ∞ (Function.uncurry pressure) (Icc 0 T ×ˢ (univ : Set Vec3))
  periodic_pressure : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (pressure t)
  mean_zero_pressure : ∀ t ∈ Icc 0 T, (∫ x in centeredCell, pressure t x) = 0
  poisson : ∀ t ∈ Icc 0 T, ∀ x, divergence (gradient (pressure t)) x =
    -LinearMap.trace ℝ Vec3 ((fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x).comp
      (fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x)).toLinearMap
  projected_eq : ∀ t ∈ Icc 0 T,
    momentumResidual (Icc 0 T) (fun r x => torusVelocity r (toUnitTorus x)) pressure t =
      closedSlabLerayMomentum 0 T (fun r x => torusVelocity r (toUnitTorus x)) t
  residual_cutoff : ∀ t ∈ Icc 0 T,
    momentumResidual (Icc 0 T) (fun r x => torusVelocity r (toUnitTorus x)) pressure t =
      truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ
        (approximateTorus t) (approximateResidualTorus t)

namespace TruncatedChildStage

variable {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}

/-- Real velocity on the Euclidean lift. -/
def velocity (s : TruncatedChildStage T Λ ψ V RV) : Velocity :=
  fun t x => s.torusVelocity t (toUnitTorus x)

/-- The true momentum residual computed using the selected pressure. -/
def residual (s : TruncatedChildStage T Λ ψ V RV) : Velocity :=
  momentumResidual (Icc 0 T) s.velocity s.pressure

theorem periodic_velocity (s : TruncatedChildStage T Λ ψ V RV) (t : ℝ) :
    SpatiallyPeriodic (s.velocity t) := by
  intro n x
  exact congrArg (s.torusVelocity t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

private theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

end TruncatedChildStage

theorem contDiffOn_closedSlab_momentumResidual {T : ℝ} (hT : 0 < T)
    {u : Velocity} {p : Pressure}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (momentumResidual (Icc 0 T) u p))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  let I := Icc (0 : ℝ) T
  let S := I ×ˢ (univ : Set Vec3)
  let D := fderivWithin ℝ (Function.uncurry p) S
  let C := (ContinuousLinearMap.compL ℝ Vec3 (ℝ × Vec3) ℝ).flip
    (ContinuousLinearMap.inr ℝ ℝ Vec3)
  have hD : ContDiffOn ℝ ∞ D S :=
    hp.fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) (by simp)
  have hSpace : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (p z.1) z.2) S := by
    apply (C.contDiff.comp_contDiffOn hD).congr
    rintro ⟨t, x⟩ ht
    exact ((hp.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt.comp_hasFDerivAt x
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
      (Filter.Eventually.of_forall fun y => ⟨ht.1, mem_univ y⟩)).fderiv
  have hGrad : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => gradient (p z.1) z.2) S :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp_contDiffOn hSpace
  have hUSpace : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) S :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT) (by simpa using hu)
  exact ((contDiffOn_sliceTimeDerivWithin_Icc hT hu).add (hUSpace.clm_apply hu)).add hGrad

theorem spatiallyPeriodic_closedSlab_momentumResidual {T t : ℝ}
    {u : Velocity} {p : Pressure} (ht : t ∈ Icc 0 T)
    (hu : ContDiff ℝ ∞ (u t)) (hp : ContDiff ℝ ∞ (p t))
    (huPer : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (u r))
    (hpPer : SpatiallyPeriodic (p t)) :
    SpatiallyPeriodic (momentumResidual (Icc 0 T) u p t) := by
  intro k x
  have hTime := derivWithin_congr (fun r hr => huPer r hr k x) (huPer t ht k x)
  simp only [momentumResidual, materialAcceleration, hTime,
    (huPer t ht).fderiv (hu.differentiable (by simp)) k x, huPer t ht k x,
    hpPer.gradient (hp.differentiable (by simp)) k x]

private theorem childStage_div_add {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  change divergence (fun y => f y + g y) x = _
  simp only [divergence, fderiv_fun_add hf hg, _root_.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

theorem divergence_closedSlab_momentumResidual {T t : ℝ} (hT : 0 < T)
    {u : Velocity} {p : Pressure} (ht : t ∈ Icc 0 T)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hp : ContDiff ℝ ∞ (p t))
    (hDiv : ∀ r ∈ Icc 0 T, ∀ x, divergence (u r) x = 0)
    (hPoisson : ∀ x, divergence (gradient (p t)) x =
      -LinearMap.trace ℝ Vec3 ((fderiv ℝ (u t) x).comp (fderiv ℝ (u t) x)).toLinearMap)
    (x : Vec3) :
    divergence (momentumResidual (Icc 0 T) u p t) x = 0 := by
  let W : Velocity := fun r y => derivWithin (fun s => u s y) (Icc 0 T) r
  let A : Vec3 → Vec3 := fun y => fderiv ℝ (u t) y (u t y)
  have hWj : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hT hu
  have hWs := TruncatedChildStage.contDiff_slice hWj ht
  have hus := TruncatedChildStage.contDiff_slice hu ht
  have hAs : ContDiff ℝ ∞ A := (hus.fderiv_right (m := ∞) (by simp)).clm_apply hus
  have hG : ContDiff ℝ ∞ (gradient (p t)) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (hp.fderiv_right (m := ∞) (by simp))
  change divergence (W t + A + gradient (p t)) x = 0
  rw [childStage_div_add (f := W t + A) (g := gradient (p t))
      ((hWs.add hAs).differentiable (by simp) x) (hG.differentiable (by simp) x),
    childStage_div_add (f := W t) (g := A)
      (hWs.differentiable (by simp) x) (hAs.differentiable (by simp) x),
    divergence_slabVelocityTimeDerivative hT ht (hu.of_le (by simp)) hDiv]
  change 0 + divergence (fun y => fderiv ℝ (u t) y (u t y)) x + divergence (gradient (p t)) x = 0
  rw [divergence_advection_eq_trace_square (hus.of_le (by simp)) (hDiv t ht), hPoisson,
    zero_add, add_neg_cancel]

/-- Bundled torus slices of the true residual and advection, with the
projected evolution required for the derivative and Fourier-band estimates. -/
theorem exists_closedSlab_momentumResidual_projectedData
    {T Λ t : ℝ} (hT : 0 < T) (hΛ : 0 ≤ Λ) (ht : t ∈ Icc 0 T)
    (U : ℝ → C(Labels, Vec3)) (p : Pressure)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => U z.1 (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hpPer : SpatiallyPeriodic (p t))
    (hBand : ∀ r ∈ Icc 0 T, RealTorusFourierBand (2 * Λ) (U r))
    (hDiv : ∀ r ∈ Icc 0 T, ∀ x, divergence (fun y => U r (toUnitTorus y)) x = 0)
    (hProj : let u : Velocity := fun r x => U r (toUnitTorus x)
      momentumResidual (Icc 0 T) u p t = closedSlabLerayMomentum 0 T u t) :
    let u : Velocity := fun r x => U r (toUnitTorus x)
    ∃ R : C(Labels, Vec3), ∃ A : HalfHolder Labels Vec3,
      (∀ x, R (toUnitTorus x) = momentumResidual (Icc 0 T) u p t x) ∧
      RealTorusFourierBand (4 * Λ) R ∧
      (∀ x, HalfHolder.eval (toUnitTorus x) A = fderiv ℝ (u t) x (u t x)) ∧
      ∀ x, HasDerivWithinAt (fun r => u r x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + R (toUnitTorus x))
        (Icc 0 T) t := by
  intro u
  have huJ : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) := hu
  have huS := TruncatedChildStage.contDiff_slice huJ ht
  have hpS := TruncatedChildStage.contDiff_slice hp ht
  have huPer (r : ℝ) (_ : r ∈ Icc 0 T) : SpatiallyPeriodic (u r) := fun n x =>
    congrArg (U r) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  let W : Velocity := fun r x => derivWithin (fun s => u s x) (Icc 0 T) r
  let a : Vec3 → Vec3 := fun x => fderiv ℝ (u t) x (u t x)
  have hWj : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hT huJ
  have hWs := TruncatedChildStage.contDiff_slice hWj ht
  have hWp : SpatiallyPeriodic (W t) := fun n x =>
    derivWithin_congr (fun r hr => huPer r hr n x) (huPer t ht n x)
  have hAs : ContDiff ℝ ∞ a := (huS.fderiv_right (m := ∞) (by simp)).clm_apply huS
  have hAp : SpatiallyPeriodic a := fun n x => by
    change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
      fderiv ℝ (u t) x (u t x)
    rw [(huPer t ht).fderiv (huS.differentiable (by simp)), huPer t ht]
  have hWp0 := spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hWs.of_le (by simp)) hWp
  have hAp0 := spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hAs.of_le (by simp)) hAp
  obtain ⟨A, hA, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hAp hAp0
  have hRs := TruncatedChildStage.contDiff_slice (contDiffOn_closedSlab_momentumResidual hT huJ hp) ht
  have hRp := spatiallyPeriodic_closedSlab_momentumResidual ht huS hpS huPer hpPer
  obtain ⟨R, hR⟩ := hRp.exists_continuousTorusFunction hRs.continuous
  have hWfix : periodicLerayHolderLift (W t) = W t :=
    periodicLerayHolderLift_eq_self_of_divergence_free hWs hWp
      (divergence_slabVelocityTimeDerivative hT ht (huJ.of_le (by simp)) hDiv)
  have hPA : periodicLerayHolderLift a =
      fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) := by
    rw [← funext hA, periodicLerayHolderLift_pullback]
  change momentumResidual (Icc 0 T) u p t = periodicLerayHolderLift (W t + a) at hProj
  rw [periodicLerayHolderLift_add hWp hAp hWp0 hAp0, hWfix, hPA] at hProj
  have hDeriv (x : Vec3) :
      HasDerivWithinAt (fun r => u r x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + R (toUnitTorus x))
        (Icc 0 T) t := by
    have hs : ContDiffOn ℝ ∞ (fun r => u r x) (Icc 0 T) :=
      huJ.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun r hr => ⟨hr, mem_univ x⟩)
    have h := (hs.differentiableOn (by simp) t ht).hasDerivWithinAt
    change HasDerivWithinAt (fun r => u r x) (W t x) (Icc 0 T) t at h
    have hd := (hR x).trans (congrFun hProj x)
    have hD : -HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) +
        R (toUnitTorus x) = W t x := by
      rw [hd, Pi.add_apply]
      abel
    rw [hD]
    exact h
  exact ⟨R, A, hR, parentResidualFourierBand_of_projectedMomentum hT hΛ ht U R A hu hBand hA hDeriv,
    hA, hDeriv⟩

/-- Construct the actual smooth, odd and solenoidal child and
the jointly smooth mean-zero pressure specified in Proposition 5.11. -/
theorem nonempty_truncatedChildStage {T Λ : ℝ} (hT : 0 < T)
    {V RV : Velocity} (approximatePressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hRV : ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hRVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (RV t))
    (hVodd : ∀ t ∈ Icc 0 T, Function.Odd (V t))
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
      fderiv ℝ (V t) x (V t x) + gradient (approximatePressure t).lift x = RV t x)
    {ψ : Vec3 → ℝ} (hEven : Function.Even ψ) :
    Nonempty (TruncatedChildStage T Λ ψ V RV) := by
  classical
  obtain ⟨gV, hgV, hs, hSlices⟩ := exists_truncatedParent_T1 hT hV hVper hVodd hVdiv hEven Λ
  have hChoose (t : ℝ) : ∃ g : C(Labels, Vec3), t ∈ Icc 0 T →
      ∀ x, g (toUnitTorus x) = RV t x := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨g, hg⟩ := (hRVper t ht).exists_continuousTorusFunction
        (TruncatedChildStage.contDiff_slice hRV ht).continuous
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun ht' => (ht ht').elim⟩
  choose gRV hgRV using hChoose
  obtain ⟨p, hp, hP⟩ := exists_realFourierCutoffPoissonPressure (Λ := Λ) hT approximatePressure
    hV hVper hVdiv hMom gV gRV hgV hgRV hEven
  let U (t : ℝ) : C(Labels, Vec3) := by
    refine ⟨realVectorFourierCutoff ψ Λ (gV t), periodicRealPartVector.continuous.comp ?_⟩
    unfold smoothFourierCutoff finiteFourierSum
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  refine ⟨{
    approximateTorus := gV
    approximateResidualTorus := gRV
    torusVelocity := U
    pressure := p
    approximate_rep := hgV
    approximateResidual_rep := hgRV
    cutoff := fun _ _ => rfl
    smooth_velocity := hs
    odd_velocity := fun t ht => (hSlices t ht).2.1
    divergence_free := fun t ht => (hSlices t ht).2.2.1
    velocity_band := ?_
    smooth_pressure := hp
    periodic_pressure := fun t ht => (hP t ht).1
    mean_zero_pressure := fun t ht => (hP t ht).2.1
    poisson := fun t ht => (hP t ht).2.2.1
    projected_eq := ?_
    residual_cutoff := fun t ht => (hP t ht).2.2.2
  }⟩
  · intro t ht k hk
    apply (hSlices t ht).2.2.2 k
    exact fun h => (not_lt_of_ge ((mem_frequencyBand _ _).mp h)) hk
  · intro t ht
    exact (hP t ht).2.2.2.trans
      (closedSlabLerayMomentum_realFourierCutoff hT approximatePressure hV hVper hVdiv hMom
        gV gRV hgV hgRV hEven Λ t ht).symm

namespace TruncatedChildStage

variable {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}

/-- The slice form of the truncation error in (5.56). -/
def truncationError (_s : TruncatedChildStage T Λ ψ V RV) (P : ℕ) (t : ℝ) : ℝ :=
  Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P (V t))^2

/-- The cutoff and the untruncated approximate velocity use the same
physical lift on each time slice. -/
theorem velocity_eq_cutoff (s : TruncatedChildStage T Λ ψ V RV) (t : ℝ) :
    s.velocity t = fun x => realVectorFourierCutoff ψ Λ (s.approximateTorus t) (toUnitTorus x) :=
  funext fun x => s.cutoff t (toUnitTorus x)

/-- The physical zero-order Hessian error and the first-order residual use a
common constant independent of the depth of the Fourier expansion. -/
structure CutoffBounds (s : TruncatedChildStage T Λ ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential) (P : ℕ) (C K : ℝ) : Prop where
  all_tails : ∀ m ≤ P, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - V t) ∧
    spatialHolderHalfNorm m (s.velocity t - V t) ≤
      K * Λ ^ ((m : ℤ) - P) * spatialHolderHalfNorm P (V t)
  tail_two : ∀ t ∈ Icc 0 T,
    spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ K * s.truncationError P t
  residual : ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (s.residual t) ∧
    spatialHolderHalfNorm 1 (s.residual t) ≤
      C * spatialHolderHalfNorm 1 (RV t) + K * s.truncationError P t
  pressure : ∀ t ∈ Icc 0 T,
    spatialHolderHalfNorm 0 (fderiv ℝ (gradient (fun x => s.pressure t x - (approximatePressure t).lift x))) ≤
      C * spatialHolderHalfNorm 1 (RV t) + K * s.truncationError P t

theorem pressureHessian_le_of_cutoff {p q : Vec3 → ℝ}
    (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hper : SpatiallyPeriodic p) (hqper : SpatiallyPeriodic q)
    {B : ℝ} (hB : spatialHolderHalfNorm 0
      (fderiv ℝ (gradient (fun y => p y - q y))) ≤ B) (x v : Vec3) :
    ⟪v, fderiv ℝ (gradient p) x v⟫_ℝ ≤ ⟪v, fderiv ℝ (gradient q) x v⟫_ℝ + B * ‖v‖ ^ 2 := by
  let d : Vec3 → ℝ := fun y => p y - q y
  have hd : ContDiff ℝ ∞ d := hp.sub hq
  have hdper : SpatiallyPeriodic d := fun n y => by simp only [d, hper n y, hqper n y]
  have hGrad (f : Vec3 → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gradient f) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (hf.fderiv_right (m := ∞) (by simp))
  have hH : SpatialHolderHalf 0 (fderiv ℝ (gradient d)) :=
    spatialHolderHalf_of_contDiff_periodic ((hGrad d hd).fderiv_right (m := ∞) (by simp))
      ((hdper.gradient (hd.differentiable (by simp))).fderiv ((hGrad d hd).differentiable (by simp))) 0
  have hG : gradient d = fun y => gradient p y - gradient q y := by
    funext y
    simp only [gradient, d, fderiv_fun_sub (hp.differentiable (by simp) y)
      (hq.differentiable (by simp) y), map_sub]
  have heq : fderiv ℝ (gradient p) x =
      fderiv ℝ (gradient q) x + fderiv ℝ (gradient d) x := by
    rw [hG, fderiv_fun_sub ((hGrad p hp).differentiable (by simp) x)
      ((hGrad q hq).differentiable (by simp) x)]
    abel
  have hOp : ‖fderiv ℝ (gradient d) x‖ ≤ B :=
    (norm_apply_le_spatialHolderHalfNorm_zero hH x).trans hB
  rw [heq, _root_.add_apply, inner_add_right]
  apply add_le_add_right
  calc
    _ ≤ ‖v‖ * ‖fderiv ℝ (gradient d) x v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) :=
      mul_le_mul_of_nonneg_left (((fderiv ℝ (gradient d) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hOp (norm_nonneg _))) (norm_nonneg _)
    _ = B * ‖v‖ ^ 2 := by ring
/-- The cutoff estimates in (5.57), with constants uniform over all smooth
approximate stages on a closed slab. -/
theorem exists_cutoffBounds
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T Λ : ℝ}, 0 < T → 1 ≤ Λ → ∀ {V RV : Velocity}
      (s : TruncatedChildStage T Λ ψ V RV) (approximatePressure : ℝ → EndpointSmoothPotential),
      ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
        fderiv ℝ (V t) x (V t x) + gradient (approximatePressure t).lift x = RV t x) →
      s.CutoffBounds approximatePressure P C K := by
  let Cproj := 2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖
  have hCproj : 0 ≤ Cproj := by dsimp only [Cproj]; positivity
  let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
    (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1))
  let Cp := 24 * ‖pressureHessianMultiplier‖
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  let C := max Cr Cp
  refine ⟨C, hCp.trans (le_max_right _ _), fun P hP => ?_⟩
  obtain ⟨Kres, hKres, hres⟩ := truncatedEulerProjectedResidual_holder_bound
    periodicLerayHolderLift hCproj periodicLerayHolderLift_holder_one hψ hs hunit P hP
  let Kp := cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) P
  have hKp : 0 ≤ Kp := by
    dsimp only [Kp]
    unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
    positivity
  let K := max Kp (max Kres (Cp * Kp * (2 + Kp)))
  have hTailK : Kp ≤ K := le_max_left _ _
  have hResK : Kres ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hPressureK : Cp * Kp * (2 + Kp) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hKp.trans hTailK, ?_⟩
  intro T Λ hT hΛ V RV s approximatePressure hV hRV hdivV hMom
  have hΛ₀ : 0 < Λ := zero_lt_one.trans_le hΛ
  have hVrep (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => s.approximateTorus t (toUnitTorus x)) = V t := funext (s.approximate_rep t ht)
  have hRVrep (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => s.approximateResidualTorus t (toUnitTorus x)) = RV t :=
    funext (s.approximateResidual_rep t ht)
  have hVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (V t) := by
    rw [← hVrep t ht]
    exact fun n x => congrArg (s.approximateTorus t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hRVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (RV t) := by
    rw [← hRVrep t ht]
    exact fun n x => congrArg (s.approximateResidualTorus t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hVholder (t : ℝ) (ht : t ∈ Icc 0 T) : SpatialHolderHalf P (V t) :=
    spatialHolderHalf_of_contDiff_periodic (contDiff_slice hV ht) (hVper t ht) P
  have hRVholder (t : ℝ) (ht : t ∈ Icc 0 T) : SpatialHolderHalf 1 (RV t) :=
    spatialHolderHalf_of_contDiff_periodic (contDiff_slice hRV ht) (hRVper t ht) 1
  have hRV₀ (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ spatialHolderHalfNorm 1 (RV t) :=
    (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hRVholder t ht) (Nat.zero_le 1) 0)
  have hε (t : ℝ) : 0 ≤ s.truncationError P t := by
    unfold truncationError
    positivity
  have hQuant (t : ℝ) (ht : t ∈ Icc 0 T) :
      spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ Kres * s.truncationError P t ∧
      SpatialHolderHalf 1 (s.residual t) ∧ spatialHolderHalfNorm 1 (s.residual t) ≤
        Cr * spatialHolderHalfNorm 1 (RV t) + Kres * s.truncationError P t := by
    have hgV : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have hgRV : SpatialHolderHalf 1 (fun x => s.approximateResidualTorus t (toUnitTorus x)) :=
      (hRVrep t ht).symm ▸ hRVholder t ht
    have h := hres Λ hΛ (s.approximateTorus t) (s.approximateResidualTorus t) hgV hgRV
    have hR : s.residual t = truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ
        (s.approximateTorus t) (s.approximateResidualTorus t) := s.residual_cutoff t ht
    dsimp only at h
    simpa only [← s.velocity_eq_cutoff t, ← hR, hVrep t ht, hRVrep t ht, truncationError] using h.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm t ht
    have hg : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have h := spatialHolderHalfNorm_cutoffVelocityDifference hψ hs hunit hΛ₀
      (s.approximateTorus t) hm hg
    dsimp only at h
    rw [← s.velocity_eq_cutoff t, hVrep t ht] at h
    have hV₀ : 0 ≤ spatialHolderHalfNorm P (V t) := (norm_nonneg _).trans
      (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hVholder t ht) (Nat.zero_le P) 0)
    refine ⟨h.1, h.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTailK (by positivity)) hV₀
  · intro t ht
    exact (hQuant t ht).1.trans (mul_le_mul_of_nonneg_right hResK (hε t))
  · intro t ht
    have h := (hQuant t ht).2
    exact ⟨h.1, h.2.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (hRV₀ t ht))
      (mul_le_mul_of_nonneg_right hResK (hε t)))⟩
  · intro t ht
    let w : Velocity := fun r x => derivWithin (fun q => V q x) (Icc 0 T) r
    have hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_sliceTimeDerivWithin_Icc hT hV
    have hDivW : ∀ x, divergence (w t) x = 0 :=
      divergence_slabVelocityTimeDerivative hT ht (hV.of_le (by simp)) hdivV
    have hH := spatialHolderHalfNorm_cutoffPressureHessian_of_residual_le
      (contDiff_slice (f := s.velocity) s.smooth_velocity ht) (contDiff_slice hV ht)
      (contDiff_slice hRV ht) (contDiff_slice s.smooth_pressure ht) (approximatePressure t).smooth
      (s.periodic_velocity t) (hVper t ht) (hRVper t ht) (s.periodic_pressure t ht)
      (approximatePressure t).periodic (hdivV t ht)
      ((contDiff_slice hw ht).differentiable (by simp)) hDivW (s.poisson t ht) (hMom t ht)
    have hg : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have hProduct := spatialHolderHalfNorm_cutoffPressureTailProduct hψ hs hunit hΛ
      (s.approximateTorus t) hP hg
    dsimp only at hProduct
    rw [← s.velocity_eq_cutoff t, hVrep t ht] at hProduct
    calc
      _ ≤ Cp * (spatialHolderHalfNorm 1 (s.velocity t - V t) *
          (spatialHolderHalfNorm 1 (s.velocity t) + spatialHolderHalfNorm 1 (V t)) +
          spatialHolderHalfNorm 1 (RV t)) := hH
      _ ≤ Cp * ((Kp * (2 + Kp)) * s.truncationError P t + spatialHolderHalfNorm 1 (RV t)) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hProduct _) hCp
      _ = Cp * spatialHolderHalfNorm 1 (RV t) + (Cp * Kp * (2 + Kp)) * s.truncationError P t := by ring
      _ ≤ C * spatialHolderHalfNorm 1 (RV t) + K * s.truncationError P t :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) (hRV₀ t ht))
          (mul_le_mul_of_nonneg_right hPressureK (hε t))

/-- The full-depth size bound absorbs the physical cutoff constants into the
fifth inverse power of the following frequency. -/
theorem truncationError_le_next {μ K : ℝ} {b q qNext : ℕ}
    (s : TruncatedChildStage T ((μ ^ frequencyExponent b q) ^ 5) ψ V RV)
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hK : K ≤ μ) (t : ℝ)
    (hV : SpatialHolderHalf (6 * frequencyExponent b qNext) (V t))
    (hSize : 1 + spatialHolderHalfNorm (6 * frequencyExponent b qNext) (V t) ≤
      3 * (μ ^ frequencyExponent b q) ^ (2 * (6 * frequencyExponent b qNext + 1))) :
    K * s.truncationError (6 * frequencyExponent b qNext) t ≤
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-5 : ℝ) := by
  have hN : 0 ≤ spatialHolderHalfNorm (6 * frequencyExponent b qNext) (V t) :=
    (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hV (Nat.zero_le _) 0)
  have hε : 0 ≤ s.truncationError (6 * frequencyExponent b qNext) t := by
    unfold truncationError
    positivity
  exact (mul_le_mul_of_nonneg_right hK hε).trans
    (frequencySchedule_truncation_error_budget hμ hb hN hSize)

/-- The actual cutoff tail is a smooth solenoidal perturbation with the
smallness required by the child flow estimate. -/
theorem cutoffTail_for_childFlow {freq next C K : ℝ} {P : ℕ}
    (s : TruncatedChildStage T Λ ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hB : CutoffBounds s approximatePressure P C K)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hDiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hP : 2 ≤ P) (hFreq : 1 ≤ freq) (hNext : freq ≤ next)
    (hErr : ∀ t ∈ Icc 0 T, K * s.truncationError P t ≤ next ^ (-5 : ℝ)) :
    let tail : Velocity := fun t => s.velocity t - V t
    ContDiffOn ℝ ∞ (Function.uncurry tail) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (tail t) ∧ (∀ x, divergence (tail t) x = 0) ∧
        SpatialHolderHalf 2 (tail t) ∧ spatialHolderHalfNorm 2 (tail t) ≤ freq ^ (-5 / 2 : ℝ) := by
  intro tail
  have hChild : ContDiffOn ℝ ∞ (Function.uncurry s.velocity) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    s.smooth_velocity
  refine ⟨hChild.sub hV, fun t ht => ⟨?_, ?_, (hB.all_tails 2 hP t ht).1, ?_⟩⟩
  · intro n x
    have hVp : V t (x + latticeVector n) = V t x :=
      (s.approximate_rep t ht _).symm.trans
        ((congrArg (s.approximateTorus t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)).trans
          (s.approximate_rep t ht x))
    change s.velocity t (x + latticeVector n) - V t (x + latticeVector n) =
      s.velocity t x - V t x
    rw [s.periodic_velocity t, hVp]
  · intro x
    have hu := (contDiff_slice hChild ht).differentiable (by simp) x
    have hv := (contDiff_slice hV ht).differentiable (by simp) x
    have heq : divergence (tail t) x = divergence (s.velocity t) x - divergence (V t) x := by
      change divergence (fun y => s.velocity t y - V t y) x = _
      simp only [divergence, fderiv_fun_sub hu hv, _root_.sub_apply, PiLp.sub_apply,
        Finset.sum_sub_distrib]
    have hChildDiv : divergence (s.velocity t) x = 0 := s.divergence_free t ht x
    rw [heq, hChildDiv, hDiv t ht x, sub_self]
  · exact (hB.tail_two t ht).trans ((hErr t ht).trans (induction_child_flow_tail_budget hFreq hNext))

theorem scheduled_increment {μ Cmean C K : ℝ} {b q qNext P : ℕ}
    (s : TruncatedChildStage T ((μ ^ frequencyExponent b q) ^ 5) ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hB : CutoffBounds s approximatePressure P C K)
    {parent osc mean : Velocity} (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hOrder : q ≤ qNext)
    (hDepth : q ≤ P) (hCmean : Cmean ≤ μ) (hK : 0 ≤ K)
    (hV : ∀ t ∈ Icc 0 T, SpatialHolderHalf P (V t))
    (hSplit : ∀ t ∈ Icc 0 T, V t = parent t + osc t + mean t)
    (hMean : ∀ m ≤ q, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (mean t) ∧
      spatialHolderHalfNorm m (mean t) ≤ Cmean * (μ ^ 9) ^ (b * (m + 2)) *
        (μ ^ frequencyExponent b q) ^ (-5 / 2 : ℝ))
    (hErr : ∀ t ∈ Icc 0 T, K * s.truncationError P t ≤
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-5 : ℝ)) :
    ∀ m ≤ q, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - parent t - osc t) ∧
      spatialHolderHalfNorm m (s.velocity t - parent t - osc t) ≤ (μ ^ frequencyExponent b q)⁻¹ := by
  intro m hm t ht
  let tail := s.velocity t - V t
  have hTail := hB.all_tails m (hm.trans hDepth) t ht
  have hSize : 0 ≤ spatialHolderHalfNorm P (V t) := (norm_nonneg _).trans
    (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hV t ht) (Nat.zero_le _) 0)
  have hFreq : 1 ≤ μ ^ frequencyExponent b q := one_le_pow₀ (by linarith)
  have hTailRate := induction_child_cutoffTail_budget (μ := K) hFreq hK hSize le_rfl
    hTail.2 (hErr t ht)
  exact frequencySchedule_child_velocity_increment hμ hb hm hOrder hCmean
    (show s.velocity t = V t + tail by dsimp [tail]; abel) (hSplit t ht)
    (hMean m hm t ht).1 hTail.1 (hMean m hm t ht).2 hTailRate

/-- T2 and T3 for the actual truncated child and its Poisson pressure. -/
theorem scheduled_T2_T3
    {freq : ℕ → ℝ} {Cstep C K Sparent : ℝ} {b q qNext j P : ℕ}
    (s : TruncatedChildStage T (((freq j) ^ frequencyExponent b q) ^ 5) ψ V RV)
    (approximatePressure : ℝ → EndpointSmoothPotential)
    (hB : CutoffBounds s approximatePressure P C K)
    {parent osc : Velocity} {parentPressure : Pressure} {Y : ℝ → Velocity}
    (hμ : 2 ≤ freq j) (hb : 1 ≤ b) (hC : 0 ≤ C) (hS : T ≤ Sparent)
    (hCstep : Cstep ≤ ((freq j) ^ frequencyExponent b q) ^ (1 / 32 : ℝ))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T
      (Cstep * ((freq j) ^ frequencyExponent b q) ^ (1 / 4 : ℝ)))
    (hParent : ∀ t ∈ Icc 0 T, ∀ x, ‖parent t x‖ ≤ freq j)
    (hOsc : ∀ t ∈ Icc 0 T, ∀ x,
      ‖osc t x‖ ≤ Cstep * ((freq j) ^ frequencyExponent b q) ^ (-5 / 4 : ℝ))
    (hInc : ∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (s.velocity t - parent t - osc t) ∧
      spatialHolderHalfNorm 0 (s.velocity t - parent t - osc t) ≤ ((freq j) ^ frequencyExponent b q)⁻¹)
    (hRV : let next := ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 T, spatialHolderHalfNorm 1 (RV t) ≤ next ^ (-7 / 2 : ℝ))
    (hErr : let next := ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 T, K * s.truncationError P t ≤ next ^ (-5 : ℝ))
    (hParentPressure : ∀ t ∈ Icc 0 Sparent, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (parentPressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖v‖ ^ 2)
    (hApproxPressure : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (approximatePressure t).lift) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (parentPressure t)) x v⟫_ℝ +
          (Cstep * ((freq j) ^ frequencyExponent b q) ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2) :
    let childFrequency := (freq j) ^ frequencyExponent b q
    let next := childFrequency ^ frequencyExponent b qNext
    (∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ childFrequency) ∧
      ChildFlow.DeformationOn s.velocity Y T childFrequency ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ next ^ (-3 : ℝ)) ∧
      ∀ t ∈ Icc 0 T, ∀ x v : Vec3, ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range (j + 1), (freq i)⁻¹) * ‖v‖ ^ 2 := by
  let childFrequency := (freq j) ^ frequencyExponent b q
  let next := childFrequency ^ frequencyExponent b qNext
  have hchildFrequency : 1 ≤ childFrequency := one_le_pow₀ (by linarith)
  have hRate (t : ℝ) (ht : t ∈ Icc 0 T) : C * spatialHolderHalfNorm 1 (RV t) +
      K * s.truncationError P t ≤ C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left (hRV t ht) hC) (hErr t ht)
  have hRpoint (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖s.residual t x‖ ≤ C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) := by
    have h := norm_iteratedFDeriv_le_spatialHolderHalfNorm (hB.residual t ht).1 (Nat.zero_le 1) x
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans ((hB.residual t ht).2.trans (hRate t ht))
  obtain ⟨hU, hY, hR⟩ := frequencySchedule_child_T2 (qNext := qNext) hμ hb hC hCstep
    hlarge hFlow hParent hOsc hInc hRpoint
  refine ⟨fun t ht => (ContinuousMap.norm_le _ (zero_le_one.trans hchildFrequency)).mpr fun z => ?_,
    hY, hR, ?_⟩
  · obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    exact hU t ht x
  · refine frequencySchedule_child_T3 (qNext := qNext) hμ hb hC hS hCstep hlarge hParentPressure ?_
    dsimp only
    intro t ht x v
    have hH := pressureHessian_le_of_cutoff (contDiff_slice s.smooth_pressure ht)
      (approximatePressure t).smooth (s.periodic_pressure t ht) (approximatePressure t).periodic
      ((hB.pressure t ht).trans (hRate t ht)) x v
    linarith only [hH, hApproxPressure t ht x v, add_mul
      (Cstep * childFrequency ^ (-1 / 4 : ℝ)) (C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ)) (‖v‖ ^ 2)]

end TruncatedChildStage

private theorem childStage_toUnitTorus_neg (x : Vec3) :
    toUnitTorus (-x) = -toUnitTorus x := by
  funext i
  change ((-(x i) : ℝ) : UnitAddCircle) = -(x i : UnitAddCircle)
  exact AddCircle.coe_neg (p := (1 : ℝ)) (x := x i)

private def childStage_continuousHalfHolder (f : HalfHolder Labels Vec3) : C(Labels, Vec3) :=
  f.val.1.toContinuousMap

private theorem childStage_complexHalfHolder_coeff (f : HalfHolder Labels Vec3) (k : Fin 3 → ℤ) :
    mFourierCoeff (endpointComplexifyContinuous (childStage_continuousHalfHolder f)) k =
      complexifiedHalfHolderFourierCoeff endpointSpatialComplexification f k := by
  apply congrArg (fun g : Labels → ComplexEuclideanVec3 => mFourierCoeff g k)
  funext z
  change periodicComplexifyVector (HalfHolder.eval z f) =
    HalfHolder.eval z (HalfHolder.map endpointSpatialComplexification.ofReal f)
  rw [HalfHolder.eval_map]
  rfl

set_option maxHeartbeats 1000000 in
private theorem childStage_odd_leray_of_band (r : ℝ) (A : HalfHolder Labels Vec3)
    (hBand : RealTorusFourierBand r (childStage_continuousHalfHolder A))
    (hOdd : Function.Odd (fun x => HalfHolder.eval (toUnitTorus x) A)) :
    Function.Odd (fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A)) := by
  let f := endpointComplexifyContinuous (childStage_continuousHalfHolder A)
  let g := endpointComplexifyContinuous (childStage_continuousHalfHolder (endpointStrongSpatialLeray A))
  let lc (k : Fin 3 → ℤ) := endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k))
  have hCoeff (k : Fin 3 → ℤ) : mFourierCoeff g k = lc k (mFourierCoeff f k) := by
    dsimp only [g, f, lc]
    rw [childStage_complexHalfHolder_coeff, childStage_complexHalfHolder_coeff]
    exact endpointStrongSpatialLeray_complexCoefficient A k
  have hF (z : Labels) : f (-z) = (-1 : ℝ) • f z := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [← childStage_toUnitTorus_neg]
    change periodicComplexifyVector (HalfHolder.eval (toUnitTorus (-x)) A) =
      (-1 : ℝ) • periodicComplexifyVector (HalfHolder.eval (toUnitTorus x) A)
    have hx : HalfHolder.eval (toUnitTorus (-x)) A = -HalfHolder.eval (toUnitTorus x) A := hOdd x
    rw [hx, map_neg, neg_one_smul]
  have hG (k : Fin 3 → ℤ) : mFourierCoeff g (-k) = (-1 : ℝ) • mFourierCoeff g k := by
    have hl : latticeVector (-k) = -latticeVector k := PiLp.ext fun i => Int.cast_neg (k i)
    rw [hCoeff, hCoeff, mFourierCoeff_neg_of_parity (-1) hF, show lc (-k) = lc k by
      simp only [lc, hl, angularLeray_neg]]
    simp only [neg_one_smul, map_neg]
  have hS := finiteFourierSum_mFourierCoeff_eq_of_band g r (fun k hk => by
    rw [hCoeff, show mFourierCoeff f k = 0 from hBand k hk, map_zero])
  intro x
  have hgs := finiteFourierSum_neg_arg r (mFourierCoeff g) (-1) hG (toUnitTorus x)
  rw [hS, ← childStage_toUnitTorus_neg, neg_one_smul] at hgs
  have hr := congrArg (fun z => periodicRealPartVector z) hgs
  change periodicRealPartVector (periodicComplexifyVector
      (HalfHolder.eval (toUnitTorus (-x)) (endpointStrongSpatialLeray A))) =
    periodicRealPartVector (-periodicComplexifyVector
      (HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A))) at hr
  simpa only [map_neg, periodicRealPartVector_complexifyVector] using hr

private theorem childStage_even_fderiv_of_odd {f : Vec3 → Vec3} (hf : Function.Odd f) :
    Function.Even (fderiv ℝ f) := by
  intro x
  let N : Vec3 ≃L[ℝ] Vec3 := (LinearIsometryEquiv.neg ℝ : Vec3 ≃ₗᵢ[ℝ] Vec3).toContinuousLinearEquiv
  have hfun : f ∘ N = -f := funext hf
  have h := N.comp_right_fderiv (f := f) (x := x)
  rw [hfun, fderiv_neg] at h
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h v
  change -(fderiv ℝ f x v) = fderiv ℝ f (-x) (-v) at hv
  rw [map_neg] at hv
  exact (neg_injective hv).symm

set_option maxHeartbeats 1000000 in
/-- Odd truncated velocity has odd true residual, since the Leray projection
preserves the odd finite-band advection. -/
theorem odd_closedSlab_momentumResidual_of_projectedData {T Λ t : ℝ}
    (ht : t ∈ Icc 0 T) (U : ℝ → C(Labels, Vec3)) (p : Pressure)
    (hBand : RealTorusFourierBand (2 * Λ) (U t))
    (hOdd : ∀ r ∈ Icc 0 T, Function.Odd (fun x => U r (toUnitTorus x)))
    (A : HalfHolder Labels Vec3)
    (hA : ∀ x, HalfHolder.eval (toUnitTorus x) A =
      fderiv ℝ (fun y => U t (toUnitTorus y)) x (U t (toUnitTorus x)))
    (hDeriv : let u : Velocity := fun r x => U r (toUnitTorus x)
      ∀ x, HasDerivWithinAt (fun r => u r x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) +
          momentumResidual (Icc 0 T) u p t x) (Icc 0 T) t)
    (hT : 0 < T) :
    Function.Odd (momentumResidual (Icc 0 T) (fun r x => U r (toUnitTorus x)) p t) := by
  let u : Velocity := fun r x => U r (toUnitTorus x)
  let W : Vec3 → Vec3 := fun x => derivWithin (fun r => u r x) (Icc 0 T) t
  have hW : Function.Odd W := fun x => by
    change derivWithin (fun r => u r (-x)) (Icc 0 T) t = _
    rw [derivWithin_congr (fun r hr => hOdd r hr x) (hOdd t ht x)]
    exact derivWithin.neg
  have hAO : Function.Odd (fun x => HalfHolder.eval (toUnitTorus x) A) := fun x => by
    change HalfHolder.eval (toUnitTorus (-x)) A = -HalfHolder.eval (toUnitTorus x) A
    rw [hA, hA]
    have hD := childStage_even_fderiv_of_odd (hOdd t ht) x
    have hV := hOdd t ht x
    change fderiv ℝ (u t) (-x) (U t (toUnitTorus (-x))) =
      -fderiv ℝ (u t) x (U t (toUnitTorus x))
    change fderiv ℝ (u t) (-x) = fderiv ℝ (u t) x at hD
    change U t (toUnitTorus (-x)) = -U t (toUnitTorus x) at hV
    rw [hD, hV, map_neg]
  have hAB : RealTorusFourierBand (4 * Λ) (childStage_continuousHalfHolder A) :=
    mFourierCoeff_advection_eq_zero_outside_band (U t) (childStage_continuousHalfHolder A) hBand hA
  let P : Vec3 → Vec3 := fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A)
  have hP : Function.Odd P := childStage_odd_leray_of_band (4 * Λ) A hAB hAO
  have hR (x : Vec3) : momentumResidual (Icc 0 T) u p t x = W x + P x := by
    have h := (hDeriv x).derivWithin (uniqueDiffOn_Icc hT t ht)
    change W x = -P x + momentumResidual (Icc 0 T) u p t x at h
    rw [h]
    abel
  intro x
  change momentumResidual (Icc 0 T) u p t (-x) = -momentumResidual (Icc 0 T) u p t x
  rw [hR, hR, hW x, hP x, neg_add]


namespace TruncatedChildStage

variable {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}

theorem smooth_residual (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (Function.uncurry s.residual) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  contDiffOn_closedSlab_momentumResidual (u := s.velocity) hT s.smooth_velocity s.smooth_pressure

theorem periodic_residual (s : TruncatedChildStage T Λ ψ V RV) {t : ℝ} (ht : t ∈ Icc 0 T) :
    SpatiallyPeriodic (s.residual t) :=
  spatiallyPeriodic_closedSlab_momentumResidual ht
    (contDiff_slice (f := s.velocity) s.smooth_velocity ht) (contDiff_slice s.smooth_pressure ht)
    (fun r _ => s.periodic_velocity r) (s.periodic_pressure t ht)

theorem divergence_free_residual (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    divergence (s.residual t) x = 0 :=
  divergence_closedSlab_momentumResidual (u := s.velocity) hT ht s.smooth_velocity
    (contDiff_slice s.smooth_pressure ht) s.divergence_free (s.poisson t ht) x

/-- Continuous torus representatives for the true residual and advection,
with the exact projected time derivative of this child. -/
theorem residual_projectedData (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T)
    (hΛ : 0 ≤ Λ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ R : C(Labels, Vec3), ∃ A : HalfHolder Labels Vec3,
      (∀ x, R (toUnitTorus x) = s.residual t x) ∧
      RealTorusFourierBand (4 * Λ) R ∧
      (∀ x, HalfHolder.eval (toUnitTorus x) A = fderiv ℝ (s.velocity t) x (s.velocity t x)) ∧
      ∀ x, HasDerivWithinAt (fun r => s.velocity r x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + R (toUnitTorus x))
        (Icc 0 T) t :=
  exists_closedSlab_momentumResidual_projectedData hT hΛ ht s.torusVelocity s.pressure
    s.smooth_velocity s.smooth_pressure (s.periodic_pressure t ht) s.velocity_band
    s.divergence_free (s.projected_eq t ht)

/-- The actual first spatial jet and its closed-slab time derivative obey the
parent bounds of (7.5) at cutoff radius `freq ^ 5`. -/
theorem exists_derivedLowBounds :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T freq next : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}
        (s : TruncatedChildStage T (freq ^ 5) ψ V RV),
        0 < T → N ≤ freq → 1 ≤ next →
        (∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ freq) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ next ^ (-3 : ℝ)) →
        ∀ t ∈ Icc 0 T, ∀ x : Vec3,
          ‖fderiv ℝ (s.velocity t) x‖ ≤ freq ^ 9 ∧
          ‖derivWithin (fun r => fderiv ℝ (s.velocity r) x) (Icc 0 T) t‖ ≤ freq ^ 18 := by
  classical
  obtain ⟨N, hN, hLow⟩ := exists_parentDerivedLowBounds
  refine ⟨N, hN, ?_⟩
  intro T freq next ψ V RV s hT hfreq hnext hU hR
  have hΛ : 0 ≤ freq ^ (5 : ℕ) := pow_nonneg ((zero_le_one.trans hN).trans hfreq) _
  have hData (t : ℝ) :
      ∃ R : C(Labels, Vec3), ∃ A : HalfHolder Labels Vec3, t ∈ Icc 0 T →
        (∀ x, R (toUnitTorus x) = s.residual t x) ∧
        (∀ x, HalfHolder.eval (toUnitTorus x) A = fderiv ℝ (s.velocity t) x (s.velocity t x)) ∧
        ∀ x, HasDerivWithinAt (fun r => s.velocity r x)
          (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + R (toUnitTorus x))
          (Icc 0 T) t := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨R, A, hrep, _, hA, hD⟩ := s.residual_projectedData hT hΛ ht
      exact ⟨R, A, fun _ => ⟨hrep, hA, hD⟩⟩
    · exact ⟨0, 0, fun h => (ht h).elim⟩
  choose R A hData using hData
  have hRN (t : ℝ) (ht : t ∈ Icc 0 T) : ‖R t‖ ≤ next ^ (-3 : ℝ) := by
    refine (ContinuousMap.norm_le (R t) (Real.rpow_nonneg (zero_le_one.trans hnext) _)).mpr ?_
    intro z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [(hData t ht).1 x]
    exact hR t ht x
  exact hLow hT hfreq hnext s.torusVelocity R A s.smooth_velocity
    (fun t ht => ⟨hU t ht, s.velocity_band t ht⟩) hRN
    (fun t ht => (hData t ht).2.1) (fun t ht => (hData t ht).2.2)

/-- The true cutoff residual inherits oddness from the child velocity. -/
theorem odd_residual (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T)
    (hΛ : 0 ≤ Λ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.Odd (s.residual t) := by
  obtain ⟨R, A, hR, _, hA, hD⟩ := s.residual_projectedData hT hΛ ht
  have hDeriv (x : Vec3) : HasDerivWithinAt (fun r => s.velocity r x)
      (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray A) + s.residual t x)
      (Icc 0 T) t := by
    rw [← hR x]
    exact hD x
  exact odd_closedSlab_momentumResidual_of_projectedData ht s.torusVelocity s.pressure
    (s.velocity_band t ht) s.odd_velocity A hA hDeriv hT

end TruncatedChildStage

end

end TorusEuler
