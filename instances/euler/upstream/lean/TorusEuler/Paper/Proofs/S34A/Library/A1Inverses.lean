import TorusEuler.Paper.S34A.Statements
import TorusEuler.EndpointMixedTimeRecovery

/-! Glue for the proof of **Theorem A.1** (package S34A): the fixed-time inverse of
Lemma A.2 (case `H = ℝ³`) on the divergence-free subspace, the instantaneous inverse
family, and the recovery of the continuous time representative of the mixed solve
from a supplied family (a parameterized copy of the row's own content lemma
`exists_endpointMixedTimeRecovery`). -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "Fixed" => freezingFixedSpace endpointStrongSpatialLeray
local notation "timeμ" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (timeμ T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1InvSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1InvSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- The fixed space of the strong spatial Leray projection is the divergence-free
subspace `S` (copy of the private `endpointSpatialFixedIso`,
EndpointInstantaneousInverse.lean:20; glue). -/
def spatialFixedIso : Fixed ≃ₗᵢ[ℝ] S where
  toLinearEquiv := LinearEquiv.ofEq _ _ endpointStrongSpatialLeray_fixedSpace
  norm_map' := fun _ => rfl

/-- `spatialFixedIso` does not change the underlying field. -/
theorem spatialFixedIso_apply (u : Fixed) : (spatialFixedIso u).val = u.val :=
  LinearEquiv.coe_ofEq_apply endpointStrongSpatialLeray_fixedSpace u

/-- The inverse of `spatialFixedIso` does not change the underlying field. -/
theorem spatialFixedIso_symm_apply (u : S) : (spatialFixedIso.symm u).val = u.val := by
  simpa only [spatialFixedIso_apply] using
    congrArg (fun q : S => q.val) (spatialFixedIso.apply_symm_apply u)

/-- Generic glue: a lower bound `‖v‖ ≤ M ‖e v‖` bounds the inverse, `‖e⁻¹‖ ≤ M`. -/
theorem norm_symm_le_of_lower_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (e : X ≃L[ℝ] X) {M : ℝ} (hM : 0 ≤ M) (h : ∀ v, ‖v‖ ≤ M * ‖e v‖) :
    ‖(e.symm : X →L[ℝ] X)‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro w
  have := h (e.symm w)
  rwa [e.apply_symm_apply] at this

/-- Generic glue: conjugation by a linear isometry equivalence `ι : E ≃ₗᵢ[ℝ] F` carries an
isomorphism `e` of `E` with the lower bound `‖v‖ ≤ M ‖e v‖` to the isomorphism
`w ↦ ι (e (ι⁻¹ w))` of `F`, with the same lower bound. -/
theorem exists_isometryConj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : E ≃ₗᵢ[ℝ] F) (e : E ≃L[ℝ] E) {M : ℝ}
    (hb : ∀ v, ‖v‖ ≤ M * ‖e v‖) :
    ∃ g : F ≃L[ℝ] F, (∀ w, g w = ι (e (ι.symm w))) ∧ ∀ w, ‖w‖ ≤ M * ‖g w‖ := by
  refine ⟨(ι.toContinuousLinearEquiv.symm.trans e).trans ι.toContinuousLinearEquiv,
    fun _ => rfl, fun w => ?_⟩
  calc ‖w‖ = ‖ι.symm w‖ := (ι.symm.norm_map w).symm
    _ ≤ M * ‖e (ι.symm w)‖ := hb _
    _ = M * ‖ι (e (ι.symm w))‖ := by rw [ι.norm_map]

/-- The spatial case of Lemma A.2 (`FreezingConclusion` with `H = ℝ³`, `R = P`), read on
the divergence-free subspace `S` instead of the fixed space of `P`: the map
`v ↦ P(B v)` is an isomorphism of `S` whose inverse is bounded by the constant of (A.5).
The isomorphism and its lower bound are those of the hypothesis `h` (supplied by `hA_2`);
they are moved to `S` by the generic lemmas `exists_isometryConj` (conjugation by the
isometry `spatialFixedIso`, the identity on fields) and `norm_symm_le_of_lower_bound`, and
the forward identity is `freezingCompression_val`. The higher-order clause of `h` is not
used. The proof uses no
content lemma of Lemma A.2: the inverse comes from the hypothesis `h`. -/
theorem exists_solenoidalInverse_of_freezing {C : ℝ} {p : ℕ} {B : K½} {μ Lip : ℝ}
    (hC : 0 ≤ C) (hμ : 0 < μ) (hLip : 0 ≤ Lip)
    (h : FreezingConclusion endpointStrongSpatialLeray endpointStrongSpatialLeray_idempotent
      C p B μ Lip) :
    ∃ e : S ≃L[ℝ] S,
      (∀ v : S, e v = endpointStrongSpatialProjection (B.coefficientMul v.val)) ∧
      ‖(e.symm : S →L[ℝ] S)‖ ≤ C * (2 + μ⁻¹ + ‖B.val.1‖ + Lip) ^ p := by
  obtain ⟨e, he, hb, -⟩ := h
  have hX : 0 ≤ C * (2 + μ⁻¹ + ‖B.val.1‖ + Lip) ^ p := by
    have := inv_nonneg.mpr hμ.le
    positivity
  obtain ⟨g, hg, hgb⟩ := exists_isometryConj spatialFixedIso e hb
  refine ⟨g, fun v => Subtype.ext ?_, norm_symm_le_of_lower_bound g hX hgb⟩
  have h1 := congrArg Subtype.val (DFunLike.congr_fun he (spatialFixedIso.symm v))
  rw [freezingCompression_val, spatialFixedIso_symm_apply] at h1
  rw [hg, spatialFixedIso_apply]
  exact h1

/-- From pointwise fixed-time inverses with a common bound, a family on a time set
`I` whose inverse is as smooth in time as the coefficient (the resolvent identity,
`contDiffOn_endpointFixedInverse`). Parameterized copy of
`exists_endpointInstantaneousInverseFamily` (EndpointInstantaneousInverse.lean:71),
which obtains the pointwise inverses itself; here they are supplied (from Lemma A.2). -/
theorem exists_instantaneousFamily_of_pointwise {I : Set ℝ} {n : ℕ∞ω} {K : ℝ → K½} {Ainv : ℝ}
    (hc : ContDiffOn ℝ n K I)
    (hAt : ∀ t ∈ I, ∃ e : S ≃L[ℝ] S,
      (∀ v : S, e v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
      ‖(e.symm : S →L[ℝ] S)‖ ≤ Ainv) :
    ∃ e : ℝ → S ≃L[ℝ] S,
      (∀ t ∈ I, ∀ v : S, e t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
      (∀ t ∈ I, ‖((e t).symm : S →L[ℝ] S)‖ ≤ Ainv) ∧
      ContDiffOn ℝ n (fun t => ((e t).symm : S →L[ℝ] S)) I := by
  classical
  choose e he hb using hAt
  let g (t : ℝ) : S ≃L[ℝ] S := if ht : t ∈ I then e t ht else ContinuousLinearEquiv.refl ℝ S
  have hForward (t : ℝ) (ht : t ∈ I) (v : S) :
      g t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val) := by
    simpa only [g, dite_eq_left ht] using he t ht v
  refine ⟨g, hForward, fun t ht => ?_, ?_⟩
  · rw [show g t = e t ht by simp only [g, dite_eq_left ht]]
    exact hb t ht
  · let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
    apply contDiffOn_endpointFixedInverse
    have hm := HalfHolder.contDiffOn_coefficientMul hc
    have hsm : ContDiffOn ℝ n (fun t => endpointStrongSpatialProjection.comp
        ((K t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL)) I :=
      contDiffOn_const.clm_comp (hm.clm_comp contDiffOn_const)
    exact hsm.congr (fun t ht => ContinuousLinearMap.ext (hForward t ht))

/-- Slices of `u - v + w` (copy of the private `ae_endpointSpatialSlice_sub_add`,
EndpointMixedTimeRecovery.lean:26; glue). -/
theorem ae_spatialSlice_sub_add {T : ℝ} (u v w : EndpointTorusL2 T) :
    ∀ᵐ t ∂timeμ T, endpointSpatialSlice (u - v + w) t =
      endpointSpatialSlice u t - endpointSpatialSlice v t + endpointSpatialSlice w t := by
  have huv := Lp.coeFn_sub u v
  have hall := Lp.coeFn_add (u - v) w
  filter_upwards [endpointSpatialSlice_apply_ae (u - v + w), endpointSpatialSlice_apply_ae u,
    endpointSpatialSlice_apply_ae v, endpointSpatialSlice_apply_ae w,
    Measure.ae_ae_of_ae_prod huv, Measure.ae_ae_of_ae_prod hall] with t h₁ hu hv hw hsub hadd
  apply Lp.ext
  filter_upwards [h₁, hu, hv, hw, hsub, hadd,
    Lp.coeFn_sub (endpointSpatialSlice u t) (endpointSpatialSlice v t),
    Lp.coeFn_add (endpointSpatialSlice u t - endpointSpatialSlice v t) (endpointSpatialSlice w t)]
    with a h₁a hua hva hwa hsuba hadda hSub hAdd
  rw [h₁a, hadda, hAdd]
  simp only [Pi.add_apply]
  rw [hsuba, hSub]
  simp only [Pi.sub_apply, hua, hva, hwa]

set_option maxHeartbeats 2400000 in
/-- The continuous time representative of a mixed solve (TeX proof of Theorem A.1,
sections/appA_mean_regularity.tex:208–237: the mean `c`, the instantaneous equation
(A.9), and the continuous representative `S(t)⁻¹ g(t)` with both endpoint conditions).
Parameterized copy of the row's own content lemma `exists_endpointMixedTimeRecovery`
(EndpointMixedTimeRecovery.lean:74): the instantaneous inverse family `e` (from Lemma
A.2, case `H = ℝ³`) with its bound and time continuity is an argument instead of being
built inside. -/
theorem exists_mixedTimeRecovery_of_family {T μ CL Ainv : ℝ} (hT : 0 < T)
    (Kmix Ωmix : MixedCoefficient(T)) (w Fmix : Mixed(T)) (K : ℝ → K½) (F : ℝ → C½)
    (hFixed : endpointStrongMixedLeray T w = w)
    (hProjected : endpointStrongMixedLeray T
      (endpointMixedProductOperator hT.le Kmix Ωmix w + Fmix) = 0)
    (hμ : 0 < μ)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (e : ℝ → S ≃L[ℝ] S)
    (he : ∀ t ∈ Icc 0 T, ∀ v : S,
      e t v = endpointStrongSpatialProjection ((K t).coefficientMul v.val))
    (hE : ∀ t ∈ Icc 0 T, ‖((e t).symm : S →L[ℝ] S)‖ ≤ Ainv)
    (hEc : ContinuousOn (fun t => ((e t).symm : S →L[ℝ] S)) (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T)) (hFBound : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ CL)
    (hKSlice : ∀ᵐ t ∂timeμ T,
      endpointSpatialSlice (endpointMixedToJoint T (Kmix.coefficientMul w)) t =
        endpointWeakCoefficient (K t) (endpointSpatialSlice (endpointMixedToJoint T w) t))
    (hFSlice : ∀ᵐ t ∂timeμ T,
      endpointSpatialSlice (endpointMixedToJoint T Fmix) t = endpointHalfHolderToL2 (F t)) :
    let Jw := Ωmix.coefficientMul w
    let R := endpointMixedProductOperator hT.le Kmix Ωmix w + Fmix
    let c := endpointStrongSpatialProjection
      (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) R)
    ∃ g : ℝ → S, ContinuousOn g (Icc 0 T) ∧
      (∀ t : Icc (0 : ℝ) T,
        endpointStrongSpatialProjection ((K t).coefficientMul (g t).val) =
          c + endpointStrongSpatialProjection (HalfHolder.map (endpointPrimitiveEvaluation t) Jw) -
            endpointStrongSpatialProjection (F t)) ∧
      ((fun t => endpointHalfHolderToL2 (g t).val) =ᵐ[timeμ T]
        endpointSpatialSlice (endpointMixedToJoint T w)) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t) := by
  classical
  intro Jw R c
  let P := endpointStrongSpatialProjection
  let joint := endpointMixedToJoint T
  let Ja : EndpointTorusL2 T := endpointProductPrimitive unitTorusMeasure hT.le (joint Jw)
  let ra : EndpointTorusL2 T := joint R
  have hFixedWeak : joint w ∈ endpointTorusSpace T := by
    rw [← hFixed]
    exact endpointStrongMixedLeray_mem_weak hT w
  let u : endpointTorusSpace T := ⟨joint w, hFixedWeak⟩
  have hra : ra = joint (Kmix.coefficientMul w) - Ja + joint Fmix := by
    change joint ((Kmix.coefficientMul w -
      endpointMixedIntegration hT.le (Ωmix.coefficientMul w)) + Fmix) = _
    rw [map_add, map_sub, endpointMixedToJoint_integration hT.le]
  have hrZero : endpointJointConstraintProjection T ra = 0 := by
    rw [← endpointStrongMixedLeray_agrees_L2 hT, hProjected, map_zero]
  have hrTest (z : endpointTorusSpace T) : ⟪ra, (z : EndpointTorusL2 T)⟫_ℝ = 0 := by
    let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
    have hp : ⟪endpointJointConstraintProjection T ra, (z : EndpointTorusL2 T)⟫_ℝ =
        ⟪ra, (z : EndpointTorusL2 T)⟫_ℝ :=
      (endpointTorusSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right z _
    rw [hrZero, inner_zero_left] at hp
    exact hp.symm
  let J (t : ℝ) : C½ :=
    if ht : t ∈ Icc 0 T then HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Jw else 0
  have hJ (t : Icc (0 : ℝ) T) : J t = HalfHolder.map (endpointPrimitiveEvaluation t) Jw := by
    simp only [J, dite_eq_left t.property]
  let post : (Paths(T) →L[ℝ] Vec3) →L[ℝ] (Mixed(T) →L[ℝ] C½) := HalfHolder.postcomp
  have ⟨hJc, hJB⟩ :=
    endpointMixedPrimitive_continuousOn_and_bound (T := T) (JΩ := J) post Jw hJ
  have hWeak : ∀ᵐ t ∂timeμ T,
      endpointWeakSpatialProjection
          (endpointWeakCoefficient (K t) (endpointSpatialSlice (joint w) t)) =
        endpointSolenoidalEmbedding (c + P (J t) - P (F t)) := by
    have hsl := ae_spatialSlice_sub_add (joint (Kmix.coefficientMul w)) Ja (joint Fmix)
    rw [← hra] at hsl
    have hmean := endpointWeakResidualProjected_eq_mean hT ra hrTest
    have hJa := endpointMixedProjectedPrimitive_compat hT.le P
      endpointStrongSpatialProjection_agrees_weak Jw
    have hma := endpointMixedResidual_projectedMean_compat hT.le P
      endpointStrongSpatialProjection_agrees_weak R
    filter_upwards [hsl, hmean, hJa, hKSlice, hFSlice] with t hsl hmean hJa hKs hFs
    obtain ⟨ht, hJa⟩ := hJa
    rw [hsl, map_add, map_sub, hKs, hJa, hFs, endpointStrongSpatialProjection_agrees_weak,
      hma] at hmean
    rw [hJ ⟨t, ht⟩, map_sub, map_add]
    let x := endpointWeakSpatialProjection
      (endpointWeakCoefficient (K t) (endpointSpatialSlice (joint w) t))
    let y := endpointSolenoidalEmbedding
      (P (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Jw))
    let z := endpointSolenoidalEmbedding (P (F t))
    change x - y + z = endpointSolenoidalEmbedding c at hmean
    change x = endpointSolenoidalEmbedding c + y - z
    calc
      _ = (x - y + z) + y - z := by abel
      _ = _ := by rw [hmean]
  have hBudget : 0 ≤ Ainv :=
    (norm_nonneg ((e 0).symm : S →L[ℝ] S)).trans (hE 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨g, hgc, hEq, hRep, _, hStart, hFinish, hDeriv⟩ :=
    exists_endpointTorusContinuousRepresentative hT u P endpointStrongSpatialProjection_agrees_weak
      K hμ hPos e he hEc c hJc hF hBudget hE hJB hFBound hWeak
  refine ⟨g, hgc, ?_, hRep, hStart, hFinish, hDeriv⟩
  intro t
  rw [← he t t.property, hEq t t.property, hJ t]

end

end TorusEuler.Paper.Lib.S34A
