import TorusEuler.Paper.Proofs.S34A.Library.A1Inverses
import TorusEuler.PaperMeanStatements

/-! Glue for the proof of **Theorem A.1** (package S34A): uniqueness of the projected
mixed solution and the mixed representation of a solution of (4.9) (public copies of
private lemmas of PaperMeanStatements.lean, unchanged up to names), and the unit-interval
solve of Theorem A.1 from supplied inverses (Lemma A.2). The solve is a copy, for `T = 1`,
of the source branch of `paperMeanIntegratedInverse_of_coercivity`
(PaperMeanStatements.lean:369), an own-content lemma of row A.1; see the docstring of
`exists_unitSolve_of_inverses`. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "Time" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" E "," T ")" => Lp E 2 (Time T)
local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1BaseSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1BaseSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance
local notation "Mixed(" T ")" => HalfHolder A (Path(Vec3,T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(Vec3,T) →L[ℝ] Path(Vec3,T))
local notation "P" => endpointStrongSpatialProjection
local notation "P[" T "]" => endpointStrongMixedLeray T
local notation "W[" T "]" => freezingFixedSpace (P[T])

/-- Continuity of the left side of (4.9) (copy of the private
`continuousOn_paperMeanIntegratedMomentum`, PaperMeanStatements.lean:161; glue). -/
theorem continuousOn_integratedMomentum {T : ℝ} {K Ω : ℝ → K½}
    {src : ℝ → C½}
    (hK : ContinuousOn K (Icc 0 T)) (hΩ : ContinuousOn Ω (Icc 0 T))
    (hsrc : ContinuousOn src (Icc 0 T)) {g : ℝ → S} (hg : ContinuousOn g (Icc 0 T)) :
    ContinuousOn (paperMeanIntegratedMomentum K Ω src g) (Icc 0 T) := by
  let gv : ℝ → C½ := fun t => (g t).val
  have hgc : ContinuousOn gv (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg
  have hKc := (HalfHolder.coefficientMulL.continuous.comp_continuousOn hK).clm_apply hgc
  have hΩc := (HalfHolder.coefficientMulL.continuous.comp_continuousOn hΩ).clm_apply hgc
  have hI : ContinuousOn (endpointPrimitive (fun r => (Ω r).coefficientMul (gv r))) (Icc 0 T) :=
    fun t ht => (hasDerivWithinAt_endpointPrimitive_of_continuousOn hΩc ht).continuousWithinAt
  exact (hKc.sub hI).add hsrc

/-- A continuous velocity with zero time mean gives a fixed point of the mixed
projection (copy of the private `paperMean_mixed_fixed`, PaperMeanStatements.lean:201;
glue). -/
theorem mixed_fixed {T : ℝ} (hT : 0 < T) {v : ℝ → S} {w : Mixed(T)}
    (hv : ContinuousOn v (Icc 0 T)) (hEnd : endpointPrimitive v T = 0)
    (hRep : EndpointMixedRepresents w (fun t => (v t).val)) :
    P[T] w = w := by
  let joint := endpointMixedToJoint T w
  have hvc : ContinuousOn (fun t => (v t).val) (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hv
  have hSlice := hRep.spatialSlice hT.le hvc
  have hConst (a : A) : (∫ t in (0 : ℝ)..T, HalfHolder.eval a (v t).val) = 0 := by
    let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
    let ev := (HalfHolder.eval a).comp endpointHalfHolderSolenoidal.subtypeL
    have hi : IntervalIntegrable v volume 0 T :=
      ContinuousOn.intervalIntegrable_of_Icc (u := v) hT.le hv
    change (∫ t in (0 : ℝ)..T, ev (v t)) = 0
    rw [ev.intervalIntegral_comp_comm hi]
    change ev (endpointPrimitive v T) = 0
    rw [hEnd, map_zero]
  have hMem : joint ∈ endpointTorusSpace T := by
    apply (mem_endpointTorusSpace_iff_slices T joint).mpr
    constructor
    · filter_upwards [endpointMixedToJoint_apply_ae w, hRep] with a hwa ha
      change (∫ t, joint (t, a) ∂Time T) = 0
      rw [integral_congr_ae (hwa.symm.trans ha), ← intervalIntegral.integral_of_le hT.le]
      exact hConst a
    · intro p
      filter_upwards [endpointSpatialSlice_apply_ae joint, hSlice,
        ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))] with t ht hst htm
      have hp := (mem_endpointSpatialSolenoidal (endpointHalfHolderToL2 (v t).val)).mp
        (v t).property p
      rw [← hst] at hp
      exact (integral_congr_ae (ht.symm.mono fun a ha => congrArg
        (fun q => ⟪endpointPotentialGradient p a, q⟫_ℝ) ha)).trans hp
  apply endpointMixedToJoint_injective T
  rw [endpointStrongMixedLeray_agrees_L2 hT, endpointJointConstraintProjection]
  let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
  exact Submodule.starProjection_eq_self_iff.mpr hMem

/-- A residual whose spatial projections are a constant `c` is annihilated by the mixed
projection (copy of the private `paperMean_mixed_projection_of_constant`,
PaperMeanStatements.lean:238; glue). -/
theorem mixed_projection_of_constant {T : ℝ} (hT : 0 < T)
    {r : Mixed(T)} {f : ℝ → C½}
    (hf : ContinuousOn f (Icc 0 T)) (hRep : EndpointMixedRepresents r f) (c : S)
    (hConstant : ∀ t ∈ Icc 0 T, P (f t) = c) : P[T] r = 0 := by
  let R := endpointMixedToJoint T r
  let C := endpointHalfHolderToL2 c.val
  have hSlice := hRep.spatialSlice hT.le hf
  have hOrth (v : endpointTorusSpace T) : ⟪R, (v : EndpointTorusL2 T)⟫_ℝ = 0 := by
    let w : EndpointTorusL2 T := v
    have hSol := ae_endpointSpatialSlice_solenoidal v.property
    have hEq : ∀ᵐ t ∂Time T,
        (∫ a, ⟪R (t, a), w (t, a)⟫_ℝ ∂unitTorusMeasure) = ⟪C, endpointSpatialSlice w t⟫_ℝ := by
      filter_upwards [endpointSpatialSlice_apply_ae R, endpointSpatialSlice_apply_ae w, hSlice,
        hSol, ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))]
        with t ha hb ht htSol hmem
      let : CompleteSpace endpointSpatialSolenoidal := isClosed_endpointSpatialSolenoidal.completeSpace_coe
      let y : endpointSpatialSolenoidal := ⟨endpointSpatialSlice w t, htSol⟩
      have hProj : endpointWeakSpatialProjection (endpointSpatialSlice R t) =
          endpointSolenoidalEmbedding c := by
        rw [ht, endpointStrongSpatialProjection_agrees_weak, hConstant t (Ioc_subset_Icc_self hmem)]
      have hi := endpointSpatialSolenoidal.inner_orthogonalProjectionOnto_eq_of_mem_right
        y (endpointSpatialSlice R t)
      change ⟪(endpointWeakSpatialProjection (endpointSpatialSlice R t) : Lp Vec3 2 unitTorusMeasure),
        endpointSpatialSlice w t⟫_ℝ = _ at hi
      rw [hProj] at hi
      change ⟪C, endpointSpatialSlice w t⟫_ℝ = ⟪endpointSpatialSlice R t, endpointSpatialSlice w t⟫_ℝ at hi
      rw [L2.inner_def (endpointSpatialSlice R t) (endpointSpatialSlice w t)] at hi
      refine (integral_congr_ae ?_).trans hi.symm
      filter_upwards [ha, hb] with a hfa hga
      rw [hfa, hga]
    have hm : endpointTorusTimeIntegral hT.le w = 0 := by
      apply (endpointTorusTimeIntegral_eq_zero_iff hT.le w).mpr
      filter_upwards [((mem_endpointTorusSpace_iff_slices T w).mp v.property).1] with a ha
      rw [intervalIntegral.integral_of_le hT.le]
      exact ha
    rw [L2.inner_def]
    change (∫ q, ⟪R q, w q⟫_ℝ ∂(Time T).prod unitTorusMeasure) = 0
    rw [integral_prod _ (L2.integrable_inner (𝕜 := ℝ) R w), integral_congr_ae hEq]
    have hSwap : (∫ t, ⟪C, endpointSpatialSlice w t⟫_ℝ ∂Time T) =
        ∫ t, ⟪endpointSpatialSlice w t, C⟫_ℝ ∂Time T :=
      integral_congr_ae (ae_of_all _ fun t => real_inner_comm _ _)
    rw [hSwap, integral_inner_endpointSpatialSlice hT.le, hm, inner_zero_left]
  apply endpointMixedToJoint_injective T
  rw [endpointStrongMixedLeray_agrees_L2 hT, map_zero]
  let : CompleteSpace (endpointTorusSpace T) := (isClosed_endpointTorusSpace T).completeSpace_coe
  let pr : endpointTorusSpace T := (endpointTorusSpace T).orthogonalProjectionOnto R
  have he := (endpointTorusSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right pr R
  change ⟪(pr : EndpointTorusL2 T), (pr : EndpointTorusL2 T)⟫_ℝ = _ at he
  rw [hOrth pr, real_inner_self_eq_norm_sq] at he
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)


/-- Uniqueness of the projected mixed solution given the isomorphism `eM` (copy of the
private `paperMean_mixed_solution_eq`, PaperMeanStatements.lean:290; glue). -/
theorem mixed_solution_eq {T : ℝ} (hT : 0 < T) (Kmix Ωmix : MixedCoefficient(T))
    (eM : W[T] ≃L[ℝ] W[T])
    (heM : (eM : W[T] →L[ℝ] W[T]) = freezingCompression P[T]
      (endpointMixedPathCoefficient hT.le Kmix Ωmix).coefficientMul (endpointStrongMixedLeray_idempotent hT))
    (f w z : Mixed(T)) (hw : P[T] w = w) (hz : P[T] z = z)
    (hProjW : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix w + f) = 0)
    (hProjZ : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix z + f) = 0) : w = z := by
  let a : W[T] := ⟨w, (mem_freezingFixedSpace P[T] w).mpr hw⟩
  let b : W[T] := ⟨z, (mem_freezingFixedSpace P[T] z).mpr hz⟩
  suffices h : eM a = eM b from congrArg (fun y : W[T] => y.val) (eM.injective h)
  apply Subtype.ext
  have calcEq (u : W[T]) (hu : P[T] (endpointMixedProductOperator hT.le Kmix Ωmix u.val + f) = 0) :
      (eM u).val = -(P[T] f) := by
    have hm := congrArg (fun x : W[T] => x.val) (DFunLike.congr_fun heM u)
    have hc := DFunLike.congr_fun (endpointMixedPathCoefficient_coefficientMul hT.le Kmix Ωmix) u.val
    rw [map_add] at hu
    exact hm.trans ((congrArg (P[T]) hc).trans (eq_neg_of_add_eq_zero_left hu))
  exact (calcEq a hProjW).trans (calcEq b hProjZ).symm

/-- A solution of (4.9) gives a fixed mixed field solving the projected mixed equation
(copy of the private `PaperMeanIntegratedSolution.exists_mixed_representation`,
PaperMeanStatements.lean:309; glue). -/
theorem exists_mixed_representation
    {T : ℝ} (hT : 0 < T) {K Ω : ℝ → K½} {src : ℝ → C½}
    (Kmix Ωmix : MixedCoefficient(T)) (f : Mixed(T))
    (hK : ContinuousOn K (Icc 0 T)) (hΩ : ContinuousOn Ω (Icc 0 T))
    (hsrc : ContinuousOn src (Icc 0 T))
    (hKmix : ∀ (a : A) (v : Path(Vec3,T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[Time T]
      fun t => HalfHolder.eval a (K t) (v t))
    (hΩmix : ∀ (a : A) (v : Path(Vec3,T)), (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[Time T]
      fun t => HalfHolder.eval a (Ω t) (v t))
    (hf : EndpointMixedRepresents f src) (s : PaperMeanIntegratedSolution T K Ω src) :
    ∃ w : Mixed(T), EndpointMixedRepresents w (fun t => (s.velocity t).val) ∧ P[T] w = w ∧
      P[T] (endpointMixedProductOperator hT.le Kmix Ωmix w + f) = 0 := by
  let gv : ℝ → C½ := fun t => (s.velocity t).val
  have hgc : ContinuousOn gv (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn s.continuous
  let M := endpointClosedTimeNorm T gv
  obtain ⟨w, _, hw, _⟩ := exists_endpointMixedSource hT.le
    (endpointClosedTimeNorm_nonneg hT.le gv) gv hgc
    (fun _ => norm_le_endpointClosedTimeNorm hgc)
  have hRep : EndpointMixedRepresents w gv := ae_of_all _ hw
  have hFixed := mixed_fixed hT s.continuous s.terminal hRep
  have hKrep := hRep.coefficientMul (ae_of_all _ hKmix)
  have hΩrep := hRep.coefficientMul (ae_of_all _ hΩmix)
  have hΩc := (HalfHolder.coefficientMulL.continuous.comp_continuousOn hΩ).clm_apply hgc
  have hRrep := (hKrep.sub (hΩrep.integration hT.le hΩc)).add hf
  have hRc := continuousOn_integratedMomentum hK hΩ hsrc s.continuous
  exact ⟨w, hRep, hFixed, mixed_projection_of_constant hT hRc hRrep s.constant s.projected⟩


set_option maxHeartbeats 4000000 in
/-- The unit-interval solve of **Theorem A.1** from supplied inverses, following
sections/appA_mean_regularity.tex:199–240. The mixed inverse `eM` of `P Q B`,
`B = K - JΩ` (Lemma A.2 with `H = L²(I;ℝ³)`) gives the unique solution
`v = eM⁻¹(-P Q L)` of the projected equation, with (A.8); its time mean gives `c`; the
instantaneous equation (A.9) and the fixed-time inverses `eS t` of `v ↦ P(K(t)v)`
(Lemma A.2 with `H = ℝ³`, continuous in `t`) give the continuous representative with
both endpoint conditions and the bound by `endpointPhysicalInverseBudget`. The two
inverses are arguments, so this lemma uses no content of Lemma A.2.

Provenance. The proof is a copy, for `T = 1`, of the source branch and the uniqueness
branch of `paperMeanIntegratedInverse_of_coercivity` (PaperMeanStatements.lean:369, branch
at :440–504; its docstring calls it "the integrated Hölder inverse of Theorem A.1", and the
A.1 content lemma `paperTheoremA1` is proved from it, PaperAppendixAInverse.lean:301). That
lemma is own content of row A.1. Changes: `T = 1`; the inverses `eS`, `eM` and their
bounds are arguments, instead of being taken from `exists_endpointPhysicalInverseCaps` and
`exists_endpointSpatialSolenoidalInverse`; `exists_endpointMixedTimeRecovery` is replaced by
the parameterized copy `exists_mixedTimeRecovery_of_family`; the bound inlines the body of
the A.1 content lemma `norm_endpointPhysicalTimeRepresentative_le`
(EndpointPhysicalJetEstimates.lean:349), with `g` itself in place of a second recovery;
the private uniqueness lemmas are replaced by their public copies `exists_mixed_representation`
and `mixed_solution_eq`; the `ContDiffOn 1` conjunct is dropped. -/
theorem exists_unitSolve_of_inverses {K Ω : ℝ → K½} {κ As Am : ℝ} (hκ : 0 < κ)
    (Kmix Ωmix : MixedCoefficient(1))
    (hK : ContinuousOn K (Icc 0 1)) (hΩ : ContinuousOn Ω (Icc 0 1))
    (kmix : ∀ (a : A) (v : Path(Vec3,1)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[Time 1]
      fun t => HalfHolder.eval a (K t) (v t))
    (omix : ∀ (a : A) (v : Path(Vec3,1)), (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[Time 1]
      fun t => HalfHolder.eval a (Ω t) (v t))
    (hEll : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a v, κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : S, eS t v = P ((K t).coefficientMul v.val))
    (hAs : ∀ t ∈ Icc (0 : ℝ) 1, ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (hEc : ContinuousOn (fun t => ((eS t).symm : S →L[ℝ] S)) (Icc 0 1))
    (eM : W[1] ≃L[ℝ] W[1])
    (heM : (eM : W[1] →L[ℝ] W[1]) = freezingCompression P[1]
      (endpointMixedPathCoefficient zero_le_one Kmix Ωmix).coefficientMul
      (endpointStrongMixedLeray_idempotent zero_lt_one))
    (hAm : ‖(eM.symm : W[1] →L[ℝ] W[1])‖ ≤ Am)
    (src : ℝ → C½) (hsrc : ContinuousOn src (Icc 0 1)) :
    ∃ s : PaperMeanIntegratedSolution 1 K Ω src,
      endpointPrimitive s.velocity 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (endpointPrimitive s.velocity) (s.velocity t) (Icc 0 1) t) ∧
      endpointClosedTimeNorm 1 s.velocity ≤
        endpointPhysicalInverseBudget zero_le_one Kmix Ωmix As Am *
          endpointClosedTimeNorm 1 src ∧
      ∀ u : PaperMeanIntegratedSolution 1 K Ω src,
        EqOn u.velocity s.velocity (Icc 0 1) ∧ u.constant = s.constant := by
  classical
  have hT : (0 : ℝ) < 1 := zero_lt_one
  let Csrc := endpointClosedTimeNorm 1 src
  have hCsrc : 0 ≤ Csrc := endpointClosedTimeNorm_nonneg hT.le src
  have hSbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖src t‖ ≤ Csrc :=
    norm_le_endpointClosedTimeNorm hsrc ht
  obtain ⟨f, _, hFrep, hFs⟩ := exists_endpointMixedSource hT.le hCsrc src hsrc hSbound
  let p : W[1] := ⟨P[1] f,
    (mem_freezingFixedSpace P[1] _).mpr (endpointStrongMixedLeray_idempotent hT f)⟩
  let w₁ := eM.symm (-p)
  let w := w₁.val
  have hFixed : P[1] w = w := (mem_freezingFixedSpace P[1] _).mp w₁.property
  have hProj : P[1] (endpointMixedProductOperator hT.le Kmix Ωmix w + f) = 0 := by
    have hEq : freezingCompression P[1]
        (endpointMixedPathCoefficient hT.le Kmix Ωmix).coefficientMul
        (endpointStrongMixedLeray_idempotent hT) w₁ = -p :=
      (DFunLike.congr_fun heM w₁).symm.trans (eM.apply_symm_apply _)
    have hP' : P[1] (endpointMixedProductOperator hT.le Kmix Ωmix w) = -(P[1] f) := by
      rw [← endpointMixedPathCoefficient_coefficientMul hT.le Kmix Ωmix]
      exact congrArg (fun x : W[1] => x.val) hEq
    rw [map_add, hP', neg_add_cancel]
  obtain ⟨g, hg, hEq, hRep, hStart, hEnd, hDeriv⟩ :=
    exists_mixedTimeRecovery_of_family hT Kmix Ωmix w f K src hFixed hProj hκ hEll eS heS hAs
      hEc hsrc hSbound
      (ae_endpointMixedCoefficient_spatialSlice_of_pathAction K Kmix hK (ae_of_all _ kmix) w) hFs
  let gv : ℝ → C½ := fun t => (g t).val
  have hgc : ContinuousOn gv (Icc 0 1) :=
    endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg
  have hWrep : EndpointMixedRepresents w gv :=
    EndpointMixedRepresents.of_spatialSlice hT.le hgc hRep
  have hΩrep := hWrep.coefficientMul (ae_of_all _ omix)
  have hΩc := (HalfHolder.coefficientMulL.continuous.comp_continuousOn hΩ).clm_apply hgc
  let c := P ((1 : ℝ)⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨1, hT.le, le_rfl⟩)
    (endpointMixedProductOperator hT.le Kmix Ωmix w + f))
  have hEquation (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      P (paperMeanIntegratedMomentum K Ω src g t) = c := by
    have hEt := hEq ⟨t, ht⟩
    rw [endpointMixedPrimitive_eq_endpointPrimitive _ hΩc hΩrep ⟨t, ht⟩] at hEt
    change P ((K t).coefficientMul (g t).val) =
      c + P (endpointPrimitive (fun r => (Ω r).coefficientMul (g r).val) t) - P (src t) at hEt
    unfold paperMeanIntegratedMomentum
    rw [map_add, map_sub, hEt]
    change c + _ - _ - _ + _ = c
    abel
  let s : PaperMeanIntegratedSolution 1 K Ω src := ⟨g, c, hg, hEnd, hEquation⟩
  refine ⟨s, hStart, hDeriv, ?_, ?_⟩
  · apply endpointClosedTimeNorm_le hT.le
    intro t ht
    have hFmix : EndpointMixedRepresents f src := ae_of_all _ hFrep
    have hFbound := hFmix.norm_le_of_continuousOn hT.le hCsrc hsrc hSbound
    have hAm₀ : 0 ≤ Am := (eM.symm : W[1] →L[ℝ] W[1]).opNorm_nonneg.trans hAm
    have hW : ‖w‖ ≤ Real.sqrt 1 * ((Am * ‖P[1]‖) * Csrc) := by
      calc
        _ ≤ Am * (‖P[1]‖ * ‖f‖) :=
          norm_endpointMixed_of_projectedResidual hT Kmix Ωmix w f eM heM hAm hFixed hProj
        _ ≤ Am * (‖P[1]‖ * (Real.sqrt 1 * Csrc)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hFbound (P[1]).opNorm_nonneg) hAm₀
        _ = _ := by ring
    let B := endpointMixedProductOperator hT.le Kmix Ωmix
    let O := Ωmix.coefficientMul
    have hInst := (heS t ht (g t)).trans (hEq ⟨t, ht⟩)
    have hNorm := norm_endpointRecoveredVelocity_le_of_mixed_sqrt_bounds hT
      endpointStrongSpatialProjection (eS t) (hAs t ht) B O ⟨t, ht⟩ (g t) w f (src t) hW
      hFbound hInst
    refine hNorm.trans ?_
    calc
      _ ≤ As * (‖P‖ * ((‖B‖ + 1 * ‖O‖) * ((Am * ‖P[1]‖) * Csrc) + Csrc + Csrc)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hSbound t ht))
          endpointStrongSpatialProjection.opNorm_nonneg)
          (((eS t).symm : S →L[ℝ] S).opNorm_nonneg.trans (hAs t ht))
      _ = _ := by unfold endpointPhysicalInverseBudget; dsimp only [B, O]; ring
  · intro u
    obtain ⟨w', hRep', hFixed', hProjected'⟩ := exists_mixed_representation hT Kmix Ωmix f hK hΩ
      hsrc kmix omix (ae_of_all _ hFrep) u
    have hEqW := mixed_solution_eq hT Kmix Ωmix eM heM f w' w hFixed' hFixed hProjected' hProj
    rw [hEqW] at hRep'
    have hu : ContinuousOn (fun t => (u.velocity t).val) (Icc 0 1) :=
      endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn u.continuous
    have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : u.velocity t = s.velocity t :=
      Subtype.ext ((hRep'.eqOn hT hu hgc hWrep) ht)
    refine ⟨hv, ?_⟩
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, hT.le⟩
    rw [← u.projected 0 h0, ← s.projected 0 h0]
    simp only [paperMeanIntegratedMomentum, endpointPrimitive, intervalIntegral.integral_same,
      sub_zero, hv 0 h0]

end

end TorusEuler.Paper.Lib.S34A
