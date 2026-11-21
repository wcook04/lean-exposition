import TorusEuler.EndpointConcreteSpatialBootstrap
import TorusEuler.EndpointInstantaneousInverse
import TorusEuler.EndpointPhysicalJetEstimates
import TorusEuler.MeanDerivativeLifting

/-! The weighted fixed-time inverse estimate for the differentiated physical mean. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "P" => endpointStrongSpatialLeray
local notation "S" => endpointHalfHolderSolenoidal
local notation "Fixed" => freezingFixedSpace P

local instance meanSpatialSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance meanSpatialSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- The actual periodic Leray projection commutes with each spatial direction. -/
theorem endpointStrongSpatialLeray_preservesSpatialDerivative {u : Vec3} {f df : W}
    (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (P f) (P df) :=
  freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound P 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongSpatialLeray_haar_norm_le z)
    u (fun r z => endpointStrongSpatialLeray_torusTranslate (toUnitTorus (r • u)) z) f df h

private theorem spatialDerivative_unique {u : Vec3} {v w₁ w₂ : W}
    (h₁ : endpointTorusHasSpatialDerivative u v w₁)
    (h₂ : endpointTorusHasSpatialDerivative u v w₂) : w₁ = w₂ := by
  apply HalfHolder.ext
  intro a
  simpa only [zero_smul, toUnitTorus_zero, add_zero] using (h₁ a 0).unique (h₂ a 0)

private def fixedIso : Fixed ≃ₗᵢ[ℝ] S where
  toLinearEquiv := LinearEquiv.ofEq _ _ endpointStrongSpatialLeray_fixedSpace
  norm_map' := fun _ => rfl

private theorem fixedIso_val (v : Fixed) : (fixedIso v).val = v.val :=
  LinearEquiv.coe_ofEq_apply endpointStrongSpatialLeray_fixedSpace v

private theorem fixedIso_symm_val (v : S) : (fixedIso.symm v).val = v.val := by
  simpa only [fixedIso_val] using congrArg Subtype.val (fixedIso.apply_symm_apply v)

set_option maxHeartbeats 1000000 in
/-- Each word of the actual label velocity satisfies the fixed-time projected
equation, with lower-order corrections given by the ordered spatial Leibniz rule. -/
theorem terminalMeanSpatialInverse_wordRecurrence {I : Type*} (N : ℕ) (u : I → Vec3)
    (K : List I → K½) (F : List I → W) (v : List I → S)
    (e : S ≃L[ℝ] S)
    (he : ∀ z : S, e z = endpointStrongSpatialProjection ((K []).coefficientMul z.val))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ a (z : Vec3), μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K []) z, z⟫_ℝ)
    (hEq : P ((K []).coefficientMul (v []).val) = P (F []))
    (hK : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (K q) (K (i :: q)))
    (hF : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (F q) (F (i :: q)))
    (hv : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (v q).val (v (i :: q)).val)
    {Ainv : ℝ} (hAinv : ‖(e.symm : S →L[ℝ] S)‖ ≤ Ainv) :
    ∀ q : List I, q.length ≤ N → ‖v q‖ ≤ Ainv *
      (‖P‖ * ‖F q‖ + ((endpointMixedCorrectionPairs q).map fun p =>
        (2 * ‖P‖ * ‖K p.1‖) * ‖v p.2‖).sum) := by
  let iso := fixedIso.toContinuousLinearEquiv
  let E := iso.trans (e.trans iso.symm)
  have hE_forward : (E : Fixed →L[ℝ] Fixed) =
      freezingCompression P (K []).coefficientMul endpointStrongSpatialLeray_idempotent := by
    ext v₀ : 1
    apply Subtype.ext
    change (fixedIso.symm (e (fixedIso v₀))).val =
      P ((K []).coefficientMul v₀.val)
    rw [fixedIso_symm_val, he, fixedIso_val]
    rfl
  have hA : 0 ≤ Ainv := (norm_nonneg (e.symm : S →L[ℝ] S)).trans hAinv
  have hE_inv : ‖(E.symm : Fixed →L[ℝ] Fixed)‖ ≤ Ainv := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro z
    change ‖fixedIso.symm (e.symm (fixedIso z))‖ ≤ Ainv * ‖z‖
    rw [LinearIsometryEquiv.norm_map]
    exact ((e.symm : S →L[ℝ] S).le_of_opNorm_le hAinv (fixedIso z)).trans_eq
      (by rw [LinearIsometryEquiv.norm_map])
  have hv₀ : P (v []).val = (v []).val :=
    (endpointStrongSpatialLeray_fixed_iff _).mpr (v []).property
  obtain ⟨w, hBase, _, _, hD, hbound⟩ := endpointStrongSpatialLeray_allSpatialDerivatives
    K (fun q => P (F q)) (v []).val u hv₀ hEq E hE_forward hμ
    (fun z a => hcoercive a (HalfHolder.eval a z.val)) N hK
    (fun i q hq => endpointStrongSpatialLeray_preservesSpatialDerivative (hF i q hq))
  have hSame (q : List I) (hq : q.length ≤ N) : w q = (v q).val := by
    induction q with
    | nil => exact hBase
    | cons i q ih =>
      have hq' : q.length < N := by simp only [List.length_cons] at hq; omega
      have hd := hD i q hq'
      rw [ih hq'.le] at hd
      exact spatialDerivative_unique hd (hv i q hq')
  intro q hq
  have hSum :
      ‖P‖ * ((endpointMixedCorrectionPairs q).map fun p => 2 * ‖K p.1‖ * ‖w p.2‖).sum =
        ((endpointMixedCorrectionPairs q).map fun p =>
          (2 * ‖P‖ * ‖K p.1‖) * ‖v p.2‖).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hlen := (endpointMixedCorrectionPairs_mem hp).2.2
    rw [hSame p.2 (hlen.le.trans hq), ← Submodule.coe_norm]
    ring
  have h := hbound q hq
  rw [hSame q hq, ← Submodule.coe_norm, hSum] at h
  refine h.trans (mul_le_mul hE_inv (add_le_add (endpointStrongSpatialLeray.le_opNorm _) le_rfl) ?_ hA)
  apply add_nonneg (norm_nonneg _)
  apply List.sum_nonneg
  intro k hk
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hk
  positivity

set_option maxHeartbeats 700000 in
/-- A weighted estimate for spatial derivatives of a fixed-time kinetic
solve. Once the positive coefficient words pay the radius threshold, only
one copy of the inverse cap multiplies the source bound. -/
theorem terminalMeanSpatialInverse_wordBounds {I : Type*} (N : ℕ) (u : I → Vec3)
    (K : List I → K½) (F : List I → W) (v : List I → S)
    (e : S ≃L[ℝ] S)
    (he : ∀ z : S, e z = endpointStrongSpatialProjection ((K []).coefficientMul z.val))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ a (z : Vec3), μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K []) z, z⟫_ℝ)
    (hEq : P ((K []).coefficientMul (v []).val) = P (F []))
    (hK : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (K q) (K (i :: q)))
    (hF : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (F q) (F (i :: q)))
    (hv : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (v q).val (v (i :: q)).val)
    {ℓ Ainv B C : ℝ} (hℓ : 0 ≤ ℓ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAinv : ‖(e.symm : S →L[ℝ] S)‖ ≤ Ainv)
    (hRHS : ∀ q, q.length ≤ N → ℓ ^ q.length * ‖F q‖ ≤ B)
    (hCoeff : ∀ q, 1 ≤ q.length → q.length ≤ N →
      Ainv * (ℓ ^ q.length * (2 * ‖P‖ * ‖K q‖)) ≤ C) :
    ∀ q : List I, q.length ≤ N →
      ℓ ^ q.length * ‖v q‖ ≤ Ainv * (‖P‖ * B) * (1 + (2 : ℝ) ^ N * C) ^ q.length := by
  have hA : 0 ≤ Ainv := (norm_nonneg (e.symm : S →L[ℝ] S)).trans hAinv
  have hR (q : List I) (hq : q.length ≤ N) : ℓ ^ q.length * (‖P‖ * ‖F q‖) ≤ ‖P‖ * B := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hRHS q hq) endpointStrongSpatialLeray.opNorm_nonneg
  exact meanDerivativeLifting N (fun q => ‖v q‖) (fun q => ‖P‖ * ‖F q‖)
    (fun q => 2 * ‖P‖ * ‖K q‖) hℓ hA (mul_nonneg endpointStrongSpatialLeray.opNorm_nonneg hB) hC
    (fun _ => norm_nonneg _) hR hCoeff
    (terminalMeanSpatialInverse_wordRecurrence N u K F v e he hμ hcoercive hEq hK hF hv hAinv)

/-- A positive spatial coefficient word pays for the inverse once the
radius controls the coefficient scale. -/
theorem terminalMeanSpatialInverse_radiusThreshold {D ℓ Ainv H : ℝ} {b r : ℕ}
    (K : K½) (hA : 0 ≤ Ainv) (hH : 0 ≤ H)
    (hsmall : Ainv * D ^ b * Real.sqrt ℓ ≤ 1)
    (hK : ℓ ^ r * ‖K‖ ≤ H * D ^ b * Real.sqrt ℓ) :
    Ainv * (ℓ ^ r * (2 * ‖P‖ * ‖K‖)) ≤ (2 * ‖P‖) * H := by
  have hP : 0 ≤ 2 * ‖P‖ := by positivity
  calc
    _ = (2 * ‖P‖) * (Ainv * (ℓ ^ r * ‖K‖)) := by ring
    _ ≤ (2 * ‖P‖) * (Ainv * (H * D ^ b * Real.sqrt ℓ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hA) hP
    _ = (2 * ‖P‖) * (H * (Ainv * D ^ b * Real.sqrt ℓ)) := by ring
    _ ≤ (2 * ‖P‖) * H := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hH) hP

set_option maxHeartbeats 700000 in
/-- The same fixed-time estimate holds in the supremum on the closed slab. -/
theorem terminalMeanSpatialInverse_closedTimeNorm {I : Type*} {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (u : I → Vec3) (K : List I → ℝ → K½) (F : List I → ℝ → W) (v : List I → ℝ → S)
    (e : ℝ → S ≃L[ℝ] S)
    (he : ∀ t ∈ Icc 0 T, ∀ z : S, e t z = endpointStrongSpatialProjection ((K [] t).coefficientMul z.val))
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ t ∈ Icc 0 T, ∀ a (z : Vec3), μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) z, z⟫_ℝ)
    (hEq : ∀ t ∈ Icc 0 T, P ((K [] t).coefficientMul (v [] t).val) = P (F [] t))
    (hK : ∀ i q, q.length < N → ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative (u i) (K q t) (K (i :: q) t))
    (hF : ∀ i q, q.length < N → ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative (u i) (F q t) (F (i :: q) t))
    (hv : ∀ i q, q.length < N → ∀ t ∈ Icc 0 T,
      endpointTorusHasSpatialDerivative (u i) (v q t).val (v (i :: q) t).val)
    (hKc : ∀ q, q.length ≤ N → ContinuousOn (K q) (Icc 0 T))
    (hFc : ∀ q, q.length ≤ N → ContinuousOn (F q) (Icc 0 T))
    {ℓ Ainv B C : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAinv : ∀ t ∈ Icc 0 T, ‖((e t).symm : S →L[ℝ] S)‖ ≤ Ainv)
    (hRHS : ∀ q, q.length ≤ N → ℓ ^ q.length * endpointClosedTimeNorm T (F q) ≤ B)
    (hCoeff : ∀ q, 1 ≤ q.length → q.length ≤ N →
      Ainv * (ℓ ^ q.length * (2 * ‖P‖ * endpointClosedTimeNorm T (K q))) ≤ C) :
    ∀ q : List I, q.length ≤ N →
      ℓ ^ q.length * endpointClosedTimeNorm T (v q) ≤ Ainv * (‖P‖ * B) * (1 + (2 : ℝ) ^ N * C) ^ q.length := by
  have hA : 0 ≤ Ainv := (norm_nonneg ((e 0).symm : S →L[ℝ] S)).trans (hAinv 0 ⟨le_rfl, hT⟩)
  intro q hq
  have hℓq : 0 < ℓ ^ q.length := pow_pos hℓ _
  rw [mul_comm (ℓ ^ q.length), ← le_div_iff₀ hℓq]
  apply endpointClosedTimeNorm_le hT
  intro t ht
  rw [le_div_iff₀ hℓq, mul_comm ‖v q t‖]
  exact terminalMeanSpatialInverse_wordBounds N u (fun w => K w t) (fun w => F w t) (fun w => v w t)
    (e t) (he t ht) hμ (hcoercive t ht) (hEq t ht) (fun i w hw => hK i w hw t ht)
    (fun i w hw => hF i w hw t ht) (fun i w hw => hv i w hw t ht) hℓ.le hB hC (hAinv t ht)
    (fun w hw => (mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm (hFc w hw) ht)
      (pow_nonneg hℓ.le _)).trans (hRHS w hw))
    (fun w hpos hw => (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm (hKc w hw) ht) (by positivity))
      (pow_nonneg hℓ.le _)) hA).trans (hCoeff w hpos hw)) q hq

end

end TorusEuler
