import TorusEuler.EndpointConcreteInverses
import TorusEuler.EndpointTimeRegularity

/-! The instantaneous real Leray inverse as a smooth operator on a closed time slab. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "Fixed" => freezingFixedSpace endpointStrongSpatialLeray

local instance instantaneousSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance instantaneousSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private def endpointSpatialFixedIso : Fixed ≃ₗᵢ[ℝ] S where
  toLinearEquiv := LinearEquiv.ofEq _ _ endpointStrongSpatialLeray_fixedSpace
  norm_map' := fun _ => rfl

private theorem endpointSpatialFixedIso_apply (u : Fixed) :
    (endpointSpatialFixedIso u).val = u.val :=
  LinearEquiv.coe_ofEq_apply endpointStrongSpatialLeray_fixedSpace u

private theorem endpointSpatialFixedIso_symm_apply (u : S) :
    (endpointSpatialFixedIso.symm u).val = u.val := by
  simpa only [endpointSpatialFixedIso_apply] using
    congrArg (fun q : S => q.val) (endpointSpatialFixedIso.apply_symm_apply u)

/-- The inverse on the fixed space is the inverse on the canonical spatial
solenoidal subspace used by the endpoint recovery theorem. -/
theorem exists_endpointSpatialSolenoidalInverse :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : HalfHolder A (Vec3 →L[ℝ] Vec3)) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a K - HalfHolder.eval b K‖ ≤ L * dist a b) →
      (∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a K v, v⟫_ℝ) →
      ∃ e : S ≃L[ℝ] S,
        (∀ v : S, e v = endpointStrongSpatialProjection (K.coefficientMul v.val)) ∧
        ‖(e.symm : S →L[ℝ] S)‖ ≤ C * (4 + μ⁻¹ + ‖K.val.1‖ + L) ^ 145 := by
  obtain ⟨C, hC, hS⟩ := exists_endpointSpatialLerayInverse
  refine ⟨C, hC, ?_⟩
  intro K μ L hμ hL hK hpos
  obtain ⟨e, he, hBound⟩ := hS K hμ hL hK hpos
  let iso := endpointSpatialFixedIso.toContinuousLinearEquiv
  let g := iso.symm.trans (e.trans iso)
  refine ⟨g, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    change (endpointSpatialFixedIso (e (endpointSpatialFixedIso.symm v))).val =
      endpointStrongSpatialLeray (K.coefficientMul v.val)
    rw [endpointSpatialFixedIso_apply, show (e (endpointSpatialFixedIso.symm v)).val =
      endpointStrongSpatialLeray (K.coefficientMul (endpointSpatialFixedIso.symm v).val) from
        congrArg (fun q : Fixed => q.val)
          (DFunLike.congr_fun he (endpointSpatialFixedIso.symm v)),
      endpointSpatialFixedIso_symm_apply]
  · have hBudget : 0 ≤ C * (4 + μ⁻¹ + ‖K.val.1‖ + L) ^ 145 :=
      (norm_nonneg (e.symm : Fixed →L[ℝ] Fixed)).trans hBound
    apply opNorm_le_bound _ hBudget
    intro v
    change ‖endpointSpatialFixedIso (e.symm (endpointSpatialFixedIso.symm v))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact ((e.symm : Fixed →L[ℝ] Fixed).le_of_opNorm_le hBound
      (endpointSpatialFixedIso.symm v)).trans_eq
        (by rw [LinearIsometryEquiv.norm_map])

/-- The instantaneous inverse exists on the common solenoidal space and has all
time derivatives carried by the coefficient curve. -/
theorem exists_endpointInstantaneousInverseFamily {I : Set ℝ} {n : ℕ∞ω}
    {K : ℝ → HalfHolder A (Vec3 →L[ℝ] Vec3)} {μ L M : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hc : ContDiffOn ℝ n K I)
    (hLip : ∀ t ∈ I, ∀ a b, ‖HalfHolder.eval a (K t) - HalfHolder.eval b (K t)‖ ≤ L * dist a b)
    (hPos : ∀ t ∈ I, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (hM : ∀ t ∈ I, ‖(K t).val.1‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ e : ℝ → S ≃L[ℝ] S,
      (∀ t ∈ I, ∀ v : S, e t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
      (∀ t ∈ I, ‖((e t).symm : S →L[ℝ] S)‖ ≤ C * (4 + μ⁻¹ + M + L) ^ 145) ∧
      ContDiffOn ℝ n (fun t => ((e t).symm : S →L[ℝ] S)) I := by
  classical
  obtain ⟨C, hC, hInv⟩ := exists_endpointSpatialSolenoidalInverse
  have hAt (t : ℝ) (ht : t ∈ I) := hInv (K t) hμ hL (hLip t ht) (hPos t ht)
  choose e he hb using hAt
  let g (t : ℝ) : S ≃L[ℝ] S := if ht : t ∈ I then e t ht else ContinuousLinearEquiv.refl ℝ S
  have hForward (t : ℝ) (ht : t ∈ I) (v : S) :
      g t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val) := by
    simpa only [g, dite_eq_left ht] using he t ht v
  refine ⟨C, hC, g, hForward, ?_, ?_⟩
  · intro t ht
    have ht₀ := hb t ht
    rw [show g t = e t ht by simp only [g, dite_eq_left ht]]
    apply ht₀.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hM t ht]) 145) hC
  · let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
    apply contDiffOn_endpointFixedInverse
    have hm := HalfHolder.contDiffOn_coefficientMul hc
    have hsm : ContDiffOn ℝ n (fun t => endpointStrongSpatialProjection.comp
        ((K t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL)) I :=
      contDiffOn_const.clm_comp (hm.clm_comp contDiffOn_const)
    exact hsm.congr (fun t ht => ContinuousLinearMap.ext (hForward t ht))

end

end TorusEuler
