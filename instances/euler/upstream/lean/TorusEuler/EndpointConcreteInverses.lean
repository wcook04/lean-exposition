import TorusEuler.EndpointConcreteProjection
import TorusEuler.EndpointStrongWeakAgreement
import TorusEuler.FreezingConcreteSolvability

/-! The concrete spatial and path-valued versions of the Appendix A freezing inverse. -/

open ContinuousLinearMap MeasureTheory Set UnitAddTorus
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "TimePaths(" T ")" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))
local notation "SpatialFixed" => freezingFixedSpace endpointStrongSpatialLeray
local notation "MixedFixed(" T ")" => freezingFixedSpace (endpointStrongMixedLeray T)

theorem endpointStrongSpatialLeray_fixedSpace :
    SpatialFixed = endpointHalfHolderSolenoidal := by
  apply Submodule.ext
  intro u
  rw [mem_freezingFixedSpace, endpointStrongSpatialLeray_fixed_iff]

/-- At a fixed time the actual real Leray compression of a positive Lipschitz
coefficient has a bounded inverse on the solenoidal half-Hölder fields. -/
theorem exists_endpointSpatialLerayInverse :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : HalfHolder A (Vec3 →L[ℝ] Vec3)) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a K - HalfHolder.eval b K‖ ≤ L * dist a b) →
      (∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a K v, v⟫_ℝ) →
      ∃ e : SpatialFixed ≃L[ℝ] SpatialFixed,
        (e : SpatialFixed →L[ℝ] SpatialFixed) =
          freezingCompression endpointStrongSpatialLeray K.coefficientMul
            endpointStrongSpatialLeray_idempotent ∧
        ‖(e.symm : SpatialFixed →L[ℝ] SpatialFixed)‖ ≤
          C * (4 + μ⁻¹ + ‖K.val.1‖ + L) ^ 145 := by
  obtain ⟨J, hJ, hspace, _⟩ := exists_angularProjection_annular_fiveJets
  obtain ⟨C, hC, hsolve⟩ := exists_concrete_freezingCompressionEquiv
    endpointSpatialComplexification angularLeray contDiffOn_angularLeray
    (fun _ hc ξ _ => angularLeray_pos_smul hc ξ) angularLeray_isSymmetricProjection
    (norm_angularLeray_le 0) hJ (fun n hn ξ hl _ => hspace n hn ξ hl) endpointStrongSpatialLeray
    endpointStrongSpatialLeray_idempotent endpointStrongSpatialLeray_complexCoefficient
    endpointStrongSpatialLeray_pairing
  exact ⟨C, hC, fun K _ _ hμ hL hLip hK =>
    hsolve K hμ hL hLip (fun a _ v _ => hK a v) (fun _ a => hK a _)⟩

set_option maxHeartbeats 3200000 in
/-- The mixed freezing inverse has one polynomial prefactor for every positive slab duration. -/
theorem exists_endpointMixedLerayInverse_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : ℝ} (hT : 0 < T) (B : HalfHolder A (TimePaths(T) →L[ℝ] TimePaths(T))) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a v, endpointIntegral T v = 0 → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      ∃ e : MixedFixed(T) ≃L[ℝ] MixedFixed(T),
        (e : MixedFixed(T) →L[ℝ] MixedFixed(T)) =
          freezingCompression (endpointStrongMixedLeray T) B.coefficientMul
            (endpointStrongMixedLeray_idempotent hT) ∧
        ‖(e.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤
          C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 := by
  obtain ⟨J, hJ, _, htime⟩ := exists_angularProjection_annular_fiveJets
  obtain ⟨C, hC, hSolve⟩ := exists_uniform_concrete_freezingCompressionEquiv hJ
  refine ⟨C, hC, ?_⟩
  intro T hT
  let X : EndpointComplexification TimePaths(T)
      (Lp ComplexEuclideanVec3 2 (volume.restrict (Ioc (0 : ℝ) T))) :=
    endpointL2Complexification (volume.restrict (Ioc 0 T))
  have hJets : ∀ n : ℕ, n ≤ 5 → ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (angularTimeLeray T) ξ‖ ≤ J ^ n :=
    fun n hn ξ hξ _ => htime T hT n hn ξ hξ
  have hsolve := hSolve
    (H := TimePaths(T))
    (Hc := Lp ComplexEuclideanVec3 2 (volume.restrict (Ioc (0 : ℝ) T)))
    X (angularTimeLeray T) (contDiffOn_angularTimeLeray T)
    (fun _ hc ξ _ => angularTimeLeray_pos_smul T hc ξ)
    (angularTimeLeray_isSymmetricProjection hT)
    ((isStarProjection_iff_isSymmetricProjection.mpr
      (angularTimeLeray_isSymmetricProjection hT 0)).norm_le)
    hJets (endpointStrongMixedLeray T) (endpointStrongMixedLeray_idempotent hT)
    (endpointStrongMixedLeray_complexCoefficient T) (endpointStrongMixedLeray_pairing hT)
  intro B μ L hμ hL hLip hB
  refine hsolve B hμ hL hLip (fun a ξ v hv => hB a v ?_) (fun v a => hB a _ ?_)
  · rw [← hv]
    exact endpointIntegral_angularTimeLeray hT ξ v
  · have hv := (mem_freezingFixedSpace _ _).mp v.property
    rw [← hv]
    exact endpointStrongMixedLeray_timeIntegral_eq_zero hT v.val a

set_option maxHeartbeats 1500000 in
/-- The mixed freezing inverse for a fixed positive slab duration. -/
theorem exists_endpointMixedLerayInverse {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : HalfHolder A (TimePaths(T) →L[ℝ] TimePaths(T))) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a v, endpointIntegral T v = 0 → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      ∃ e : MixedFixed(T) ≃L[ℝ] MixedFixed(T),
        (e : MixedFixed(T) →L[ℝ] MixedFixed(T)) =
          freezingCompression (endpointStrongMixedLeray T) B.coefficientMul
            (endpointStrongMixedLeray_idempotent hT) ∧
        ‖(e.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤
          C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 := by
  obtain ⟨C, hC, hSolve⟩ := exists_endpointMixedLerayInverse_uniform
  refine ⟨C, hC, ?_⟩
  intro B μ L hμ hL hLip hPos
  exact hSolve (T := T) hT B (μ := μ) (L := L) hμ hL hLip hPos

private theorem exists_projected_solve_of_equiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P B : E →L[ℝ] E) (hP : ∀ f, P (P f) = P f)
    (e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (he : (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) = freezingCompression P B hP)
    {M : ℝ} (hM : ‖(e.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ ≤ M)
    (f : E) : ∃ v : E, P v = v ∧ P (B v + f) = 0 ∧ ‖v‖ ≤ M * ‖P f‖ := by
  let pf : freezingFixedSpace P := ⟨P f, (mem_freezingFixedSpace P _).mpr (hP f)⟩
  let v := e.symm (-pf)
  have hEq : freezingCompression P B hP v = -pf :=
    (DFunLike.congr_fun he v).symm.trans (e.apply_symm_apply _)
  refine ⟨v.val, (mem_freezingFixedSpace P _).mp v.property, ?_, ?_⟩
  · have hEq' : P (B v.val) = -(P f) :=
      congrArg (fun x : freezingFixedSpace P => x.val) hEq
    rw [map_add, hEq', neg_add_cancel]
  · have h := (e.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).le_of_opNorm_le hM (-pf)
    rw [norm_neg] at h
    exact h

set_option maxHeartbeats 1500000 in
/-- The projected mixed solve with a norm bound uniform over positive time slabs. -/
theorem exists_endpointStrongMixedSolve_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : ℝ} (_hT : 0 < T) (B : HalfHolder A (TimePaths(T) →L[ℝ] TimePaths(T))) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a v, endpointIntegral T v = 0 → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      ∀ f : HalfHolder A TimePaths(T),
        ∃ v : HalfHolder A TimePaths(T),
          endpointStrongMixedLeray T v = v ∧
          endpointStrongMixedLeray T (B.coefficientMul v + f) = 0 ∧
          ‖v‖ ≤ C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 * ‖endpointStrongMixedLeray T f‖ := by
  obtain ⟨C, hC, hSolve⟩ := exists_endpointMixedLerayInverse_uniform
  refine ⟨C, hC, ?_⟩
  intro T hT B μ L hμ hL hLip hB f
  obtain ⟨e, he, hnorm⟩ := hSolve hT B hμ hL hLip hB
  exact exists_projected_solve_of_equiv (endpointStrongMixedLeray T) B.coefficientMul
    (endpointStrongMixedLeray_idempotent hT) e he hnorm f

set_option maxHeartbeats 1500000 in
/-- The projected mixed solve for a fixed positive time slab. -/
theorem exists_endpointStrongMixedSolve {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : HalfHolder A (TimePaths(T) →L[ℝ] TimePaths(T))) {μ L : ℝ}, 0 < μ → 0 ≤ L →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b) →
      (∀ a v, endpointIntegral T v = 0 → μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) →
      ∀ f : HalfHolder A TimePaths(T),
        ∃ v : HalfHolder A TimePaths(T),
          endpointStrongMixedLeray T v = v ∧
          endpointStrongMixedLeray T (B.coefficientMul v + f) = 0 ∧
          ‖v‖ ≤ C * (4 + μ⁻¹ + ‖B.val.1‖ + L) ^ 145 * ‖endpointStrongMixedLeray T f‖ := by
  obtain ⟨C, hC, hSolve⟩ := exists_endpointStrongMixedSolve_uniform
  refine ⟨C, hC, ?_⟩
  intro B μ L hμ hL hLip hPos f
  exact hSolve (T := T) hT B (μ := μ) (L := L) hμ hL hLip hPos f

end

end TorusEuler
