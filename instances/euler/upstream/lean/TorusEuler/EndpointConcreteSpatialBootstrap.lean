import TorusEuler.EndpointConcreteProjection
import TorusEuler.EndpointSpatialDerivativeHierarchy

/-! Spatial differentiation for the concrete spatial and path-valued Leray projections. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder A Vec3
local notation "M" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "TimePaths(" T ")" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))
local notation "WT(" T ")" => HalfHolder A TimePaths(T)
local notation "MT(" T ")" => HalfHolder A (TimePaths(T) →L[ℝ] TimePaths(T))

/-- The concrete, fixed-time spatial Leray projector commutes with torus translation. -/
theorem endpointStrongSpatialLeray_torusTranslate (b : A) (z : W) :
    endpointStrongSpatialLeray (HalfHolder.torusTranslate b z) =
      HalfHolder.torusTranslate b (endpointStrongSpatialLeray z) :=
  halfHolder_torusTranslate_commutes_of_complexFourierCoefficient endpointSpatialComplexification
    endpointStrongSpatialLeray
    (fun k => endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k)))
    endpointStrongSpatialLeray_complexCoefficient b z

/-- Imposing a zero time mean preserves commutation with spatial translations. -/
theorem endpointStrongMixedLeray_torusTranslate (T : ℝ) (b : A) (z : WT(T)) :
    endpointStrongMixedLeray T (HalfHolder.torusTranslate b z) =
      HalfHolder.torusTranslate b (endpointStrongMixedLeray T z) :=
  let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
  halfHolder_torusTranslate_commutes_of_complexFourierCoefficient X
    (endpointStrongMixedLeray T) (fun k => X.extendOperator (angularTimeLeray T (latticeVector k)))
    (endpointStrongMixedLeray_complexCoefficient T) b z

/-- The fixed-time strong projector contracts the Haar L² norm. -/
theorem endpointStrongSpatialLeray_haar_norm_le (z : W) :
    ‖freezingHaarEmbedding (endpointStrongSpatialLeray z)‖ ≤ ‖freezingHaarEmbedding z‖ := by
  change ‖endpointHalfHolderToL2 (endpointStrongSpatialLeray z)‖ ≤ ‖endpointHalfHolderToL2 z‖
  rw [endpointStrongSpatialLeray_agrees_L2]
  simpa only [one_mul] using
    periodicRealLeray.le_of_opNorm_le norm_periodicRealLeray_le (endpointHalfHolderToL2 z)

private theorem endpointMixedToJoint_norm_eq_freezingHaarEmbedding {T : ℝ} (z : WT(T)) :
    ‖endpointMixedToJoint T z‖ = ‖freezingHaarEmbedding z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [endpointMixedToJoint_norm_sq, norm_freezingHaarEmbedding_eq, Real.sq_sqrt]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- The combined spatial Leray and time-mean projector contracts the Haar L² norm. -/
theorem endpointStrongMixedLeray_haar_norm_le {T : ℝ} (hT : 0 < T) (z : WT(T)) :
    ‖freezingHaarEmbedding (endpointStrongMixedLeray T z)‖ ≤ ‖freezingHaarEmbedding z‖ := by
  rw [← endpointMixedToJoint_norm_eq_freezingHaarEmbedding,
    ← endpointMixedToJoint_norm_eq_freezingHaarEmbedding, endpointStrongMixedLeray_agrees_L2 hT]
  let : CompleteSpace (endpointTorusSpace T) :=
    (isClosed_endpointTorusSpace T).completeSpace_coe
  exact (endpointTorusSpace T).norm_starProjection_apply_le (endpointMixedToJoint T z)

section Spatial

local notation "P" => endpointStrongSpatialLeray

/-- First spatial derivative for the fixed-time spatial projector, with the
differentiated equation and its half-Hölder estimate. -/
theorem endpointStrongSpatialLeray_spatialDerivative
    (B dB : M) (v f df : W) (u : Vec3) (hv : P v = v)
    (heq : P (B.coefficientMul v) = f)
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul endpointStrongSpatialLeray_idempotent)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hf : endpointTorusHasSpatialDerivative u f df) (hB : endpointTorusHasSpatialDerivative u B dB) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) ∧ endpointTorusHasSpatialDerivative u v w := by
  obtain ⟨w, hw, hEq, hbound, hd⟩ := endpointSpatialDerivative_of_haar_bound P
    endpointStrongSpatialLeray_idempotent 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongSpatialLeray_haar_norm_le z)
    endpointStrongSpatialLeray_pairing B dB v f df u
    (fun h z => endpointStrongSpatialLeray_torusTranslate (toUnitTorus (h • u)) z)
    hv heq S hS hμ hcoercive hf hB
  exact ⟨w, hw, hEq, hbound, (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt v w u).mp hd⟩

/-- Second mixed spatial derivative for the fixed-time spatial projector. The inputs
`w₁` and `w₂` are the first derivatives in the two directions. -/
theorem endpointStrongSpatialLeray_secondSpatialDerivative
    (B dB₁ dB₂ ddB : M) (v w₁ w₂ df₁ ddf : W) (u : Vec3) (hw₁ : P w₁ = w₁)
    (hEq : P (B.coefficientMul w₁) = df₁ - P (dB₁.coefficientMul v))
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul endpointStrongSpatialLeray_idempotent)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hdf₁ : endpointTorusHasSpatialDerivative u df₁ ddf)
    (hB : endpointTorusHasSpatialDerivative u B dB₂)
    (hdB₁ : endpointTorusHasSpatialDerivative u dB₁ ddB)
    (hv : endpointTorusHasSpatialDerivative u v w₂) :
    let dg := ddf - P (ddB.coefficientMul v + dB₁.coefficientMul w₂)
    ∃ w₁₂ : W, P w₁₂ = w₁₂ ∧
      P (B.coefficientMul w₁₂) = dg - P (dB₂.coefficientMul w₁) ∧
      ‖w₁₂‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖dg‖ + 2 * ‖P‖ * ‖dB₂‖ * ‖w₁‖) ∧ endpointTorusHasSpatialDerivative u w₁ w₁₂ :=
  endpointSpatialSecondMixedDerivative_of_haar_bound P endpointStrongSpatialLeray_idempotent 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongSpatialLeray_haar_norm_le z)
    endpointStrongSpatialLeray_pairing B dB₁ dB₂ ddB v w₁ w₂ df₁ ddf u
    (fun h z => endpointStrongSpatialLeray_torusTranslate (toUnitTorus (h • u)) z)
    hw₁ hEq S hS hμ hcoercive hdf₁ hB hdB₁ hv

set_option maxHeartbeats 800000 in
/-- Mixed spatial derivatives of every order through the data cutoff, with
the exact projected equations and the lower-order commutator bound. -/
theorem endpointStrongSpatialLeray_allSpatialDerivatives {I : Type*}
    (B : List I → M) (f : List I → W) (v : W) (u : I → Vec3)
    (hv : P v = v) (heq : P ((B []).coefficientMul v) = f [])
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P (B []).coefficientMul endpointStrongSpatialLeray_idempotent)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a (B []) (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (N : ℕ)
    (hB : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (B t) (B (i :: t)))
    (hf : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (f t) (f (i :: t))) :
    ∃ w : List I → W, w [] = v ∧ (∀ t : List I, t.length ≤ N → P (w t) = w t) ∧
      (∀ t : List I, t.length ≤ N →
        P ((B []).coefficientMul (w t)) = f t - P (endpointMixedCorrection B w t)) ∧
      (∀ (i : I) (t : List I), t.length < N →
        endpointTorusHasSpatialDerivative (u i) (w t) (w (i :: t))) ∧
      (∀ t : List I, t.length ≤ N →
        ‖w t‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
          (‖f t‖ + ‖P‖ * ((endpointMixedCorrectionPairs t).map fun p =>
            2 * ‖B p.1‖ * ‖w p.2‖).sum)) := by
  obtain ⟨w, hw, hfix, hEq, hd⟩ := endpointSpatialAllFiniteMixedDerivatives (H := Vec3)
    P endpointStrongSpatialLeray_idempotent 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongSpatialLeray_haar_norm_le z)
    endpointStrongSpatialLeray_pairing B f v u
    (fun i h z => endpointStrongSpatialLeray_torusTranslate (toUnitTorus (h • u i)) z)
    hv heq S hS hμ hcoercive N hB hf
  exact ⟨w, hw, hfix, hEq, hd, fun t ht => norm_endpointSpatialMixedDerivative_le_of_equation
    P endpointStrongSpatialLeray_idempotent B f w t (hfix t ht) (hEq t ht) S hS⟩

end Spatial

section Mixed

local notation "P[" T "]" => endpointStrongMixedLeray T

set_option maxHeartbeats 800000 in
/-- First spatial derivative for the path-valued projector, with the
differentiated equation and its half-Hölder estimate. -/
theorem endpointStrongMixedLeray_spatialDerivative {T : ℝ} (hT : 0 < T)
    (B dB : MT(T)) (v f df : WT(T)) (u : Vec3) (hv : P[T] v = v)
    (heq : P[T] (B.coefficientMul v) = f)
    (S : freezingFixedSpace P[T] ≃L[ℝ] freezingFixedSpace P[T])
    (hS : (S : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T]) =
      freezingCompression P[T] B.coefficientMul (endpointStrongMixedLeray_idempotent hT))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P[T]) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hf : endpointTorusHasSpatialDerivative u f df) (hB : endpointTorusHasSpatialDerivative u B dB) :
    ∃ w : WT(T), P[T] w = w ∧
      P[T] (B.coefficientMul w) = df - P[T] (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T])‖ *
        (‖df‖ + 2 * ‖P[T]‖ * ‖dB‖ * ‖v‖) ∧ endpointTorusHasSpatialDerivative u v w := by
  obtain ⟨w, hw, hEq, hbound, hd⟩ := endpointSpatialDerivative_of_haar_bound (H := TimePaths(T)) P[T]
    (endpointStrongMixedLeray_idempotent hT) 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le hT z)
    (endpointStrongMixedLeray_pairing hT) B dB v f df u
    (fun h z => endpointStrongMixedLeray_torusTranslate T (toUnitTorus (h • u)) z)
    hv heq S hS hμ hcoercive hf hB
  exact ⟨w, hw, hEq, hbound, (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt v w u).mp hd⟩

set_option maxHeartbeats 800000 in
/-- Second mixed spatial derivative for the path-valued projector. The inputs
`w₁` and `w₂` are the first derivatives in the two directions. -/
theorem endpointStrongMixedLeray_secondSpatialDerivative {T : ℝ} (hT : 0 < T)
    (B dB₁ dB₂ ddB : MT(T)) (v w₁ w₂ df₁ ddf : WT(T)) (u : Vec3) (hw₁ : P[T] w₁ = w₁)
    (hEq : P[T] (B.coefficientMul w₁) = df₁ - P[T] (dB₁.coefficientMul v))
    (S : freezingFixedSpace P[T] ≃L[ℝ] freezingFixedSpace P[T])
    (hS : (S : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T]) =
      freezingCompression P[T] B.coefficientMul (endpointStrongMixedLeray_idempotent hT))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P[T]) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hdf₁ : endpointTorusHasSpatialDerivative u df₁ ddf)
    (hB : endpointTorusHasSpatialDerivative u B dB₂)
    (hdB₁ : endpointTorusHasSpatialDerivative u dB₁ ddB)
    (hv : endpointTorusHasSpatialDerivative u v w₂) :
    let dg := ddf - P[T] (ddB.coefficientMul v + dB₁.coefficientMul w₂)
    ∃ w₁₂ : WT(T), P[T] w₁₂ = w₁₂ ∧
      P[T] (B.coefficientMul w₁₂) = dg - P[T] (dB₂.coefficientMul w₁) ∧
      ‖w₁₂‖ ≤ ‖(S.symm : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T])‖ *
        (‖dg‖ + 2 * ‖P[T]‖ * ‖dB₂‖ * ‖w₁‖) ∧ endpointTorusHasSpatialDerivative u w₁ w₁₂ :=
  endpointSpatialSecondMixedDerivative_of_haar_bound (H := TimePaths(T)) P[T]
    (endpointStrongMixedLeray_idempotent hT) 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le hT z)
    (endpointStrongMixedLeray_pairing hT) B dB₁ dB₂ ddB v w₁ w₂ df₁ ddf u
    (fun h z => endpointStrongMixedLeray_torusTranslate T (toUnitTorus (h • u)) z)
    hw₁ hEq S hS hμ hcoercive hdf₁ hB hdB₁ hv

set_option maxHeartbeats 800000 in
/-- Mixed spatial derivatives of every order through the data cutoff, with
the exact projected equations and the lower-order commutator bound. -/
theorem endpointStrongMixedLeray_allSpatialDerivatives {I : Type*} {T : ℝ} (hT : 0 < T)
    (B : List I → MT(T)) (f : List I → WT(T)) (v : WT(T)) (u : I → Vec3)
    (hv : P[T] v = v) (heq : P[T] ((B []).coefficientMul v) = f [])
    (S : freezingFixedSpace P[T] ≃L[ℝ] freezingFixedSpace P[T])
    (hS : (S : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T]) =
      freezingCompression P[T] (B []).coefficientMul (endpointStrongMixedLeray_idempotent hT))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P[T]) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a (B []) (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (N : ℕ)
    (hB : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (B t) (B (i :: t)))
    (hf : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (f t) (f (i :: t))) :
    ∃ w : List I → WT(T), w [] = v ∧ (∀ t : List I, t.length ≤ N → P[T] (w t) = w t) ∧
      (∀ t : List I, t.length ≤ N →
        P[T] ((B []).coefficientMul (w t)) = f t - P[T] (endpointMixedCorrection B w t)) ∧
      (∀ (i : I) (t : List I), t.length < N →
        endpointTorusHasSpatialDerivative (u i) (w t) (w (i :: t))) ∧
      (∀ t : List I, t.length ≤ N →
        ‖w t‖ ≤ ‖(S.symm : freezingFixedSpace P[T] →L[ℝ] freezingFixedSpace P[T])‖ *
          (‖f t‖ + ‖P[T]‖ * ((endpointMixedCorrectionPairs t).map fun p =>
            2 * ‖B p.1‖ * ‖w p.2‖).sum)) := by
  obtain ⟨w, hw, hfix, hEq, hd⟩ := endpointSpatialAllFiniteMixedDerivatives (H := TimePaths(T))
    P[T] (endpointStrongMixedLeray_idempotent hT) 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le hT z)
    (endpointStrongMixedLeray_pairing hT) B f v u
    (fun i h z => endpointStrongMixedLeray_torusTranslate T (toUnitTorus (h • u i)) z)
    hv heq S hS hμ hcoercive N hB hf
  exact ⟨w, hw, hfix, hEq, hd, fun t ht => norm_endpointSpatialMixedDerivative_le_of_equation
    P[T] (endpointStrongMixedLeray_idempotent hT) B f w t (hfix t ht) (hEq t ht) S hS⟩

end Mixed

end

end TorusEuler
