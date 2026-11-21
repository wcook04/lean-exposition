import TorusEuler.EndpointMixedProjection
import TorusEuler.EndpointMixedOperators
import TorusEuler.EndpointRealFourierTransfer
import TorusEuler.EndpointWeakInstantaneous
import TorusEuler.FreezingConcreteMultipliers
import TorusEuler.FreezingSolvability

/-! The spatial and mixed half-Hölder Leray projections and their weak counterparts. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Punctured" => ({0}ᶜ : Set Vec3)
local notation "TimePaths(" T ")" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))

local instance concreteProjectionCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance concreteProjectionCircleHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

private theorem projection_lattice_neg (k : Fin 3 → ℤ) :
    latticeVector (-k) = -latticeVector k := by
  apply PiLp.ext
  intro i
  exact Int.cast_neg (k i)

section Angular

variable {H HC : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup HC] [NormedSpace ℂ HC] [CompleteSpace HC]

omit [CompleteSpace H] [CompleteSpace HC] in
private theorem contDiffOn_complexAngular (X : EndpointComplexification H HC)
    {P : Vec3 → H →L[ℝ] H} (hP : ContDiffOn ℝ ∞ P Punctured) :
    ContDiffOn ℝ ∞ (fun ξ => X.extendOperator (P ξ)) Punctured :=
  X.extendOperatorCLM.contDiff.comp_contDiffOn hP

/-- An even real angular symbol has the expected action on every real character. -/
theorem realHomogeneousHalfHolderMultiplier_realCoefficient
    (X : EndpointComplexification H HC) {P : Vec3 → H →L[ℝ] H}
    (hP : ContDiffOn ℝ ∞ P Punctured) (hEven : Function.Even P)
    (hHom : ∀ r : ℝ, 0 < r → ∀ ξ : Vec3, ξ ≠ 0 → P (r • ξ) = P ξ)
    (f : HalfHolder Labels H) (k : Fin 3 → ℤ) (c : ℂ) :
    (∫ a, (c * mFourier k a).re • HalfHolder.eval a
      (realHomogeneousHalfHolderMultiplier X (contDiffOn_complexAngular X hP) f)
      ∂unitTorusMeasure) =
      P (latticeVector k)
        (∫ a, (c * mFourier k a).re • HalfHolder.eval a f ∂unitTorusMeasure) := by
  let A := fun ξ => X.extendOperator (P ξ)
  let fC := HalfHolder.map X.ofReal f
  let gC := homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero (contDiffOn_complexAngular X hP) fC
  have hCoeff (j : Fin 3 → ℤ) :
      mFourierCoeff (continuousHalfHolder gC) j =
        A (latticeVector j) (mFourierCoeff (continuousHalfHolder fC) j) :=
    mFourierCoeff_homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
      dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero (contDiffOn_complexAngular X hP)
      (fun r hr ξ hξ => congrArg X.extendOperator (hHom r hr ξ hξ)) fC j
  have hNeg : mFourierCoeff (continuousHalfHolder gC) (-k) =
      A (latticeVector k) (mFourierCoeff (continuousHalfHolder fC) (-k)) := by
    rw [hCoeff, projection_lattice_neg,
      show A (-latticeVector k) = A (latticeVector k) from
        congrArg X.extendOperator (hEven (latticeVector k))]
  have hReal (a : Labels) : X.re (continuousHalfHolder fC a) = HalfHolder.eval a f := by
    change X.re (HalfHolder.eval a (HalfHolder.map X.ofReal f)) = HalfHolder.eval a f
    rw [HalfHolder.eval_map, X.re_ofReal]
  have h := realPart_fourierCoeff_pair_transfer X.re (P (latticeVector k))
    (A (latticeVector k)) (X.re_extendOperator (P (latticeVector k)))
    (continuousHalfHolder fC) (continuousHalfHolder gC) k c hNeg (hCoeff k)
  change (∫ a, (c * mFourier k a).re • HalfHolder.eval a
    (HalfHolder.map X.re gC) ∂unitTorusMeasure) = _
  have hEval (a : Labels) : continuousHalfHolder gC a = HalfHolder.eval a gC := rfl
  simpa only [HalfHolder.eval_map, hReal, hEval] using h

end Angular

/-- The actual fixed-time Leray projection on real half-Hölder fields. -/
def endpointStrongSpatialLeray :
    HalfHolder Labels Vec3 →L[ℝ] HalfHolder Labels Vec3 :=
  realHomogeneousHalfHolderMultiplier endpointSpatialComplexification
    (contDiffOn_complexAngular endpointSpatialComplexification contDiffOn_angularLeray)

private theorem endpointSpatial_realPart_embedding
    (u : HalfHolder Labels ComplexEuclideanVec3) :
    endpointHalfHolderToL2 (HalfHolder.map endpointSpatialComplexification.re u) =
      periodicRealPartL2 (halfHolderTorusL2 u) := by
  apply Lp.ext
  filter_upwards [endpointHalfHolderToL2_apply_ae
    (HalfHolder.map endpointSpatialComplexification.re u),
    periodicRealPartL2_apply_ae (halfHolderTorusL2 u),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure (continuousHalfHolder u)]
    with a hLeft hRight hL2
  rw [hLeft, hRight, HalfHolder.eval_map]
  change endpointSpatialComplexification.re (HalfHolder.eval a u) =
    periodicRealPartVector (halfHolderTorusL2 u a)
  change halfHolderTorusL2 u a = HalfHolder.eval a u at hL2
  rw [hL2]
  rfl

/-- The strong real spatial projector is the same as the weak orthogonal
Leray projector under the canonical embedding. -/
theorem endpointStrongSpatialLeray_agrees_L2 (u : HalfHolder Labels Vec3) :
    endpointHalfHolderToL2 (endpointStrongSpatialLeray u) =
      periodicRealLeray (endpointHalfHolderToL2 u) := by
  let X := endpointSpatialComplexification
  let P := fun ξ => X.extendOperator (angularLeray ξ)
  let f := HalfHolder.map X.ofReal u
  let g := homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
    (contDiffOn_complexAngular X contDiffOn_angularLeray) f
  have hG : halfHolderTorusL2 g = periodicComplexLeray (halfHolderTorusL2 f) := by
    apply homogeneousHalfHolderMultiplier_agrees_L2 dyadicMultiplierCutoff_smooth
      dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
      (contDiffOn_complexAngular X contDiffOn_angularLeray)
      (fun r hr ξ _ => congrArg X.extendOperator (angularLeray_pos_smul hr ξ))
      (periodicComplexLeray.restrictScalars ℝ)
    intro v k
    change mFourierCoeff (periodicComplexLeray v) k = P (latticeVector k) (mFourierCoeff v k)
    rw [← periodicL2Coefficient_eq_mFourierCoeff, ← periodicL2Coefficient_eq_mFourierCoeff,
      periodicL2Coefficient_leray, show P (latticeVector k) = lerayModeProjection k from
        endpointComplexify_angularLeray_latticeVector k]
  have hReal : HalfHolder.map X.re f = u := by
    apply HalfHolder.ext
    intro a
    simp only [f, HalfHolder.eval_map, X.re_ofReal]
  change endpointHalfHolderToL2 (HalfHolder.map X.re g) = _
  rw [endpointSpatial_realPart_embedding, hG, ← periodicRealLeray_realPart_eq,
    ← endpointSpatial_realPart_embedding, hReal]

theorem endpointStrongSpatialLeray_fixed_iff (u : HalfHolder Labels Vec3) :
    endpointStrongSpatialLeray u = u ↔ u ∈ endpointHalfHolderSolenoidal := by
  change endpointStrongSpatialLeray u = u ↔ endpointHalfHolderToL2 u ∈ endpointSpatialSolenoidal
  constructor
  · intro h
    have hP := endpointStrongSpatialLeray_agrees_L2 u
    rw [h] at hP
    rw [hP, ← range_periodicRealLeray]
    exact ⟨_, rfl⟩
  · intro h
    apply endpointHalfHolderToL2_injective
    rw [endpointStrongSpatialLeray_agrees_L2]
    exact Submodule.starProjection_eq_self_iff.mpr h

theorem endpointStrongSpatialLeray_idempotent (u : HalfHolder Labels Vec3) :
    endpointStrongSpatialLeray (endpointStrongSpatialLeray u) = endpointStrongSpatialLeray u := by
  apply (endpointStrongSpatialLeray_fixed_iff _).2
  change endpointHalfHolderToL2 (endpointStrongSpatialLeray u) ∈ endpointSpatialSolenoidal
  rw [endpointStrongSpatialLeray_agrees_L2, ← range_periodicRealLeray]
  exact ⟨_, rfl⟩

def endpointStrongSpatialProjection :
    HalfHolder Labels Vec3 →L[ℝ] endpointHalfHolderSolenoidal :=
  endpointStrongSpatialLeray.codRestrict _ (fun f =>
    (endpointStrongSpatialLeray_fixed_iff _).mp (endpointStrongSpatialLeray_idempotent f))

theorem endpointStrongSpatialProjection_agrees_weak (f : HalfHolder Labels Vec3) :
    endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (endpointStrongSpatialProjection f) := by
  apply Subtype.ext
  exact (endpointStrongSpatialLeray_agrees_L2 f).symm

theorem endpointStrongSpatialLeray_realCoefficient (u : HalfHolder Labels Vec3)
    (k : Fin 3 → ℤ) (c : ℂ) :
    (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (endpointStrongSpatialLeray u)
      ∂unitTorusMeasure) =
      angularLeray (latticeVector k)
        (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a u ∂unitTorusMeasure) :=
  realHomogeneousHalfHolderMultiplier_realCoefficient endpointSpatialComplexification
    contDiffOn_angularLeray angularLeray_neg
    (fun _ hr ξ _ => angularLeray_pos_smul hr ξ) u k c

theorem endpointStrongSpatialLeray_complexCoefficient (u : HalfHolder Labels Vec3)
    (k : Fin 3 → ℤ) :
    complexifiedHalfHolderFourierCoeff endpointSpatialComplexification
      (endpointStrongSpatialLeray u) k =
    endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k))
      (complexifiedHalfHolderFourierCoeff endpointSpatialComplexification u k) :=
  complexifiedHalfHolderFourierCoeff_multiplier_of_realCharacterMoments
    endpointSpatialComplexification endpointStrongSpatialLeray angularLeray
    endpointStrongSpatialLeray_realCoefficient u k

theorem endpointStrongSpatialLeray_pairing (w : HalfHolder Labels Vec3)
    (v : freezingFixedSpace endpointStrongSpatialLeray) :
    ⟪freezingHaarEmbedding (endpointStrongSpatialLeray w), freezingHaarEmbedding v.val⟫_ℝ =
      ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ := by
  have hv : v.val ∈ endpointHalfHolderSolenoidal :=
    (endpointStrongSpatialLeray_fixed_iff _).mp ((mem_freezingFixedSpace _ _).mp v.property)
  let z := endpointSolenoidalEmbedding ⟨v.val, hv⟩
  let : CompleteSpace endpointSpatialSolenoidal :=
    isClosed_endpointSpatialSolenoidal.completeSpace_coe
  change ⟪endpointHalfHolderToL2 (endpointStrongSpatialLeray w), (z : Lp Vec3 2 unitTorusMeasure)⟫_ℝ =
    ⟪endpointHalfHolderToL2 w, (z : Lp Vec3 2 unitTorusMeasure)⟫_ℝ
  rw [endpointStrongSpatialLeray_agrees_L2]
  exact endpointSpatialSolenoidal.inner_orthogonalProjectionOnto_eq_of_mem_right z _

/-- The actual path-valued projection imposes both the spatial Leray and the
zero-time-mean constraints. -/
def endpointStrongMixedLeray (T : ℝ) :
    HalfHolder Labels TimePaths(T) →L[ℝ] HalfHolder Labels TimePaths(T) :=
  let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
  realHomogeneousHalfHolderMultiplier X
    (contDiffOn_complexAngular X (contDiffOn_angularTimeLeray T))

set_option maxHeartbeats 600000 in
theorem endpointStrongMixedLeray_realCoefficient (T : ℝ) (u : HalfHolder Labels TimePaths(T))
    (k : Fin 3 → ℤ) (c : ℂ) :
    (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (endpointStrongMixedLeray T u)
      ∂unitTorusMeasure) =
      angularTimeLeray T (realFourierFrequency k)
        (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a u ∂unitTorusMeasure) := by
  let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
  have hEven : Function.Even (angularTimeLeray T) := by
    intro ξ
    simp only [angularTimeLeray, angularLeray_neg]
  exact realHomogeneousHalfHolderMultiplier_realCoefficient X (contDiffOn_angularTimeLeray T)
    hEven (fun r hr ξ _ => angularTimeLeray_pos_smul T hr ξ) u k c

set_option maxHeartbeats 800000 in
theorem endpointStrongMixedLeray_complexCoefficient (T : ℝ) (u : HalfHolder Labels TimePaths(T))
    (k : Fin 3 → ℤ) :
    let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
    complexifiedHalfHolderFourierCoeff X (endpointStrongMixedLeray T u) k =
      X.extendOperator (angularTimeLeray T (latticeVector k))
        (complexifiedHalfHolderFourierCoeff X u k) := by
  let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
  exact complexifiedHalfHolderFourierCoeff_multiplier_of_realCharacterMoments X
    (endpointStrongMixedLeray T) (angularTimeLeray T)
    (endpointStrongMixedLeray_realCoefficient T) u k

theorem endpointStrongMixedLeray_agrees_L2 {T : ℝ} (hT : 0 < T)
    (u : HalfHolder Labels TimePaths(T)) :
    endpointMixedToJoint T (endpointStrongMixedLeray T u) =
      endpointJointConstraintProjection T (endpointMixedToJoint T u) :=
  endpointMixedToJoint_eq_projection_of_fourierCoeff hT u (endpointStrongMixedLeray T u)
    (endpointStrongMixedLeray_realCoefficient T u)

theorem endpointStrongMixedLeray_idempotent {T : ℝ} (hT : 0 < T)
    (u : HalfHolder Labels TimePaths(T)) :
    endpointStrongMixedLeray T (endpointStrongMixedLeray T u) = endpointStrongMixedLeray T u := by
  apply endpointMixedToJoint_injective T
  rw [endpointStrongMixedLeray_agrees_L2 hT, endpointStrongMixedLeray_agrees_L2 hT,
    endpointJointConstraintProjection]
  exact Submodule.starProjection_eq_self_iff.mpr ((endpointTorusSpace T).starProjection_apply_mem _)

theorem endpointStrongMixedLeray_mem_weak {T : ℝ} (hT : 0 < T)
    (u : HalfHolder Labels TimePaths(T)) :
    endpointMixedToJoint T (endpointStrongMixedLeray T u) ∈ endpointTorusSpace T := by
  rw [endpointStrongMixedLeray_agrees_L2 hT, ← range_endpointJointConstraintProjection]
  exact ⟨_, rfl⟩

/-- The time mean of a strongly projected path vanishes at every spatial label. -/
theorem endpointStrongMixedLeray_timeIntegral_eq_zero {T : ℝ} (hT : 0 < T)
    (u : HalfHolder Labels TimePaths(T)) (a : Labels) :
    endpointIntegral T (HalfHolder.eval a (endpointStrongMixedLeray T u)) = 0 := by
  let v := endpointStrongMixedLeray T u
  let w := endpointMixedToJoint T v
  have hw : w ∈ endpointTorusSpace T := endpointStrongMixedLeray_mem_weak hT u
  have hWeak : endpointTorusTimeIntegral hT.le w = 0 :=
    (endpointTimeIntegral_eq_zero_iff hT.le w).mpr ((mem_endpointTorusSpace_iff_slices T w).mp hw).1
  have hStrong : HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) v = 0 := by
    apply endpointHalfHolderToL2_injective
    rw [endpointMixedToJoint_terminal hT.le, map_zero]
    exact hWeak
  have ha := congrArg (HalfHolder.eval a) hStrong
  rw [HalfHolder.eval_map, endpointPrimitiveEvaluation_apply, map_zero, endpointPrimitive,
    intervalIntegral.integral_of_le hT.le, ← endpointIntegral_apply] at ha
  exact ha

set_option maxHeartbeats 800000 in
private theorem endpointMixedToJoint_inner_eq_freezingHaarEmbedding {T : ℝ}
    (u v : HalfHolder Labels TimePaths(T)) :
    ⟪endpointMixedToJoint T u, endpointMixedToJoint T v⟫_ℝ =
      ⟪freezingHaarEmbedding u, freezingHaarEmbedding v⟫_ℝ := by
  have h (w : HalfHolder Labels TimePaths(T)) :
      ‖endpointMixedToJoint T w‖ ^ 2 = ‖freezingHaarEmbedding w‖ ^ 2 := by
    rw [endpointMixedToJoint_norm_sq, norm_freezingHaarEmbedding_eq, Real.sq_sqrt]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have huv := h (u + v)
  rw [map_add, map_add, norm_add_sq_real, norm_add_sq_real, h u, h v] at huv
  linarith

set_option maxHeartbeats 800000 in
theorem endpointStrongMixedLeray_pairing {T : ℝ} (hT : 0 < T) (w : HalfHolder Labels TimePaths(T))
    (v : freezingFixedSpace (endpointStrongMixedLeray T)) :
    ⟪freezingHaarEmbedding (endpointStrongMixedLeray T w), freezingHaarEmbedding v.val⟫_ℝ =
      ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ := by
  have hv := (mem_freezingFixedSpace _ _).mp v.property
  have hmem : endpointMixedToJoint T v.val ∈ endpointTorusSpace T := by
    rw [← hv]
    exact endpointStrongMixedLeray_mem_weak hT v.val
  let z : endpointTorusSpace T := ⟨endpointMixedToJoint T v.val, hmem⟩
  let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
  rw [← endpointMixedToJoint_inner_eq_freezingHaarEmbedding,
    ← endpointMixedToJoint_inner_eq_freezingHaarEmbedding, endpointStrongMixedLeray_agrees_L2 hT]
  exact (endpointTorusSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right z _

end

end TorusEuler
