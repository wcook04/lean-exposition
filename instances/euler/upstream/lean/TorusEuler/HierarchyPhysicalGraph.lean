import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.LabelFlowGeometry
import TorusEuler.HierarchyConcreteTransverse
import TorusEuler.PhysicalHierarchyResidual
import TorusEuler.HierarchyTwistedCompletion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Eulerian readout of smooth hierarchy profiles on the transported
phase graph. Time derivatives are taken on the closed parent slab. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

/-- The point where a profile is read at an Eulerian space-time point. -/
def hierarchyGraphPoint (A : Velocity) (k : Vec3) (t : ℝ) (x : Vec3) :
    HierarchyProfilePoint :=
  (t, A t x, ⟪k, A t x⟫_ℝ)

namespace HierarchySmoothProfile

variable {T : ℝ}

/-- Read the actual smooth profile on the transported graph. -/
def graphRead {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Velocity) (k : Vec3) (f : HierarchySmoothProfile T E) : ℝ → Vec3 → E :=
  transportedProfile A k (fun t a s => f.val (t, a, s))

/-- Graph evaluation preserves the full joint smoothness within the slab. -/
theorem contDiffOn_graphRead {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Velocity} (k : Vec3) (f : HierarchySmoothProfile T E)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (graphRead A k f))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  (smooth f).comp (contDiffOn_fst.prodMk (hA.prodMk ((innerSL ℝ k).contDiff.comp_contDiffOn hA)))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

end HierarchySmoothProfile

private def graphLabelInclusion : Vec3 →L[ℝ] HierarchyProfilePoint :=
  (inr ℝ ℝ (Vec3 × ℝ)).comp (inl ℝ Vec3 ℝ)

private theorem graphProfileDerivative_split {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : HierarchyProfilePoint →L[ℝ] E) :
    D = (toSpanSingleton ℝ (D (1, 0, 0))).coprod
      ((D.comp graphLabelInclusion).coprod (toSpanSingleton ℝ (D (0, 0, 1)))) := by
  apply ContinuousLinearMap.ext
  rintro ⟨t, a, s⟩
  change D (t, a, s) = t • D (1, 0, 0) + (D (0, a, 0) + s • D (0, 0, 1))
  rw [← map_smul, ← map_smul, ← map_add, ← map_add]
  simp

private theorem graphTimeLabelDerivative_split (D : (ℝ × Vec3) →L[ℝ] Vec3) :
    D = (toSpanSingleton ℝ (D (1, 0))).coprod (D.comp (inr ℝ ℝ Vec3)) := by
  apply ContinuousLinearMap.ext
  rintro ⟨t, a⟩
  change D (t, a) = t • D (1, 0) + D (0, a)
  rw [← map_smul, ← map_add]
  simp

/-- The joint derivative of the actual inverse parent flow has the
inverse-label time component and its exact spatial coframe. -/
theorem IsLabelFlowOn.hasFDerivWithinAt_inverseLabel_time_label
    {U : Velocity} {X : ℝ → Velocity} {T t : ℝ} (hX : IsLabelFlowOn U X (Icc 0 T))
    (hT : 0 < T) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hAreg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) (x : Vec3) :
    let A : Velocity := fun r => X r 0
    let Ax := fderiv ℝ (A t) x
    HasFDerivWithinAt (Function.uncurry A) ((toSpanSingleton ℝ (-(Ax (U t x)))).coprod Ax)
      (Icc 0 T ×ˢ univ) (t, x) := by
  let A : Velocity := fun r => X r 0
  let S : Set (ℝ × Vec3) := Icc 0 T ×ˢ univ
  let D := fderivWithin ℝ (Function.uncurry A) S (t, x)
  let Ax := fderiv ℝ (A t) x
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) S := hAreg
  have hd : HasFDerivWithinAt (Function.uncurry A) D S (t, x) :=
    ((hA.differentiableOn (by simp)) _ ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hsp := hd.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => show (t, y) ∈ S from ⟨ht, mem_univ _⟩)
  have hsp' : D.comp (inr ℝ ℝ Vec3) = Ax := hsp.fderiv.symm
  have hdtime := hd.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) x))
    (fun r hr => show (r, x) ∈ S from ⟨hr, mem_univ _⟩)
  have hTime : HasDerivWithinAt (fun r => A r x) (D (1, 0)) (Icc 0 T) t := hdtime
  have hI : UniqueDiffWithinAt ℝ (Icc 0 T) t := uniqueDiffOn_Icc hT t ht
  have hTime' := hX.hasDerivWithinAt_inverseLabel hT (hU.of_le (by simp)) hper
    (left_mem_Icc.mpr hT.le) ht x
  have hdt : D (1, 0) = -(Ax (U t x)) :=
    (hTime.derivWithin hI).symm.trans (hTime'.derivWithin hI)
  rw [graphTimeLabelDerivative_split D, hsp', hdt] at hd
  exact hd

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

private theorem graph_sum_coordinateDirection (v : Vec3) :
    (∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
  ext j
  let eval := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change eval (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v j
  rw [map_sum]
  simp [eval, EuclideanSpace.single, PiLp.single_apply]

private theorem labelGradient_graphEval (hT : 0 < T) (G : VPmap) (q : SP)
    {z : HierarchyProfilePoint} (hz : z ∈ hierarchyProfileSlab T) {qa : Vec3}
    (ha : ∀ v, fderivWithin ℝ q.val (hierarchyProfileSlab T) z (0, v, 0) = ⟪qa, v⟫_ℝ) :
    (labelGradient hT G q).val z = (G.val z).adjoint qa := by
  rw [labelGradient_apply hT G q hz]
  change (∑ i : Fin 3, fderivWithin ℝ q.val (hierarchyProfileSlab T) z
    (0, G.val z (EuclideanSpace.single i 1), 0) • EuclideanSpace.single i 1) = _
  simp only [ha, ← adjoint_inner_left, EuclideanSpace.inner_single_right, one_mul]
  exact graph_sum_coordinateDirection _

set_option maxHeartbeats 950000 in
/-- The actual Eulerian momentum equals the physical parent residual
plus the concrete profile momentum read on the transported phase graph. -/
theorem momentumResidual_graphRead (hT : 0 < T) (G M : VPmap) (κ W : VP) (q : SP)
    {U A : Velocity} {p : Pressure} {t : ℝ} {x k At : Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc 0 T)
    (hA : HasFDerivWithinAt (Function.uncurry A) ((toSpanSingleton ℝ At).coprod Ax)
      (Icc 0 T ×ˢ univ) (t, x))
    (htransport : At + Ax (U t x) = 0)
    (hUt : DifferentiableWithinAt ℝ (fun r => U r x) (Icc 0 T) t)
    (hUx : DifferentiableAt ℝ (U t) x) (hp : DifferentiableAt ℝ (p t) x)
    (hG : G.val (hierarchyGraphPoint A k t x) = Ax)
    (hM : M.val (hierarchyGraphPoint A k t x) = fderiv ℝ (U t) x)
    (hκ : κ.val (hierarchyGraphPoint A k t x) = Ax.adjoint k) :
    let O := hierarchyConcreteOperators hT G M κ
    momentumResidual (Icc 0 T) (U + graphRead A k W) (p + graphRead A k q) t x =
      graphRead A k (O.material W + O.labelAdv W W + O.phaseAdv W W +
        O.labelGrad q + O.phaseGrad q) t x + momentumResidual (Icc 0 T) U p t x := by
  let z := hierarchyGraphPoint A k t x
  let O := hierarchyConcreteOperators hT G M κ
  have hz : z ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  let DW := fderivWithin ℝ W.val (hierarchyProfileSlab T) z
  let Dq := fderivWithin ℝ q.val (hierarchyProfileSlab T) z
  let wt := DW (1, 0, 0)
  let ws := DW (0, 0, 1)
  let wa := DW.comp graphLabelInclusion
  let qs := Dq (0, 0, 1)
  let qa := (InnerProductSpace.toDual ℝ Vec3).symm (Dq.comp graphLabelInclusion)
  have hqa : innerSL ℝ qa = Dq.comp graphLabelInclusion :=
    (InnerProductSpace.toDual ℝ Vec3).apply_symm_apply _
  have hW : HasFDerivWithinAt W.val DW (hierarchyProfileSlab T) z :=
    ((smooth W).differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hWp : HasFDerivWithinAt W.val
      ((toSpanSingleton ℝ wt).coprod (wa.coprod (toSpanSingleton ℝ ws)))
      (hierarchyProfileSlab T) z :=
    graphProfileDerivative_split DW ▸ hW
  have hqD : HasFDerivWithinAt q.val Dq (hierarchyProfileSlab T) z :=
    ((smooth q).differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hq' := hqD.comp_hasFDerivAt z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t z.2)
    (Eventually.of_forall fun y : Vec3 × ℝ =>
      show (t, y) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩)
  have hdq : Dq.comp (inr ℝ ℝ (Vec3 × ℝ)) =
      (innerSL ℝ qa).coprod (toSpanSingleton ℝ qs) := by
    rw [hqa]
    apply ContinuousLinearMap.ext
    rintro ⟨a, s⟩
    change Dq (0, a, s) = Dq (0, a, 0) + s • Dq (0, 0, 1)
    rw [← map_smul, ← map_add]
    simp
  rw [hdq] at hq'
  have hMat : (O.material W).val z = wt + (fderiv ℝ (U t) x) (W.val z) := by
    rw [hierarchyConcreteOperators_material_apply hT G M κ W hz, hM]
  have hSlow : (O.labelAdv W W).val z = wa (Ax (W.val z)) := by
    change (advect hT (labelDirections G) W W).val z = _
    rw [advect_apply hT _ W W hz, labelDirections_apply G W hz, hG]
    rfl
  have hFast : (O.phaseAdv W W).val z = ⟪Ax.adjoint k, W.val z⟫_ℝ • ws := by
    change (advect hT (phaseDirections κ) W W).val z = _
    rw [advect_apply hT _ W W hz, phaseDirections_apply κ W hz, hκ]
    change DW (0, 0, ⟪Ax.adjoint k, W.val z⟫_ℝ) = _
    rw [← map_smul]
    simp
  have hSlowQ : (O.labelGrad q).val z = Ax.adjoint qa := by
    change (labelGradient hT G q).val z = _
    rw [labelGradient_graphEval hT G q hz (fun v => by
      change Dq (0, v, 0) = (innerSL ℝ qa) v
      rw [hqa]
      rfl), hG]
  have hFastQ : (O.phaseGrad q).val z = qs • Ax.adjoint k := by
    change (phaseGradient hT κ q).val z = _
    rw [phaseGradient_apply hT κ q hz, hκ]
  have hI : UniqueDiffWithinAt ℝ (Icc 0 T) t := uniqueDiffOn_Icc hT t ht
  change momentumResidual (Icc 0 T) (U + graphRead A k W) (p + graphRead A k q) t x =
    (O.material W + O.labelAdv W W + O.phaseAdv W W + O.labelGrad q + O.phaseGrad q).val z +
      momentumResidual (Icc 0 T) U p t x
  rw [graphRead, graphRead, momentumResidual_transportedHierarchy (p := p) ht hI hA htransport
    hUt.hasDerivWithinAt hUx hp hWp hq']
  simp only [Submodule.coe_add, Pi.add_apply, hMat, hSlow, hFast, hSlowQ, hFastQ,
    transportedProfile, add_apply, comp_apply, smulRight_apply, innerSL_apply_apply]
  dsimp only [z, hierarchyGraphPoint]
  abel

/-- The same momentum identity with the actual inverse parent
trajectory, coframe, strain and transported covector. -/
theorem momentumResidual_graphRead_parent
    {U : Velocity} {X : ℝ → Velocity} {p : Pressure} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (U r))
    (hAreg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (G M : VPmap) (κ W : VP) (q : SP) (k : Vec3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (hp : DifferentiableAt ℝ (p t) x)
    (hG : ∀ a s, G.val (t, a, s) = fderiv ℝ (X t 0) (X 0 t a))
    (hM : ∀ a s, M.val (t, a, s) = fderiv ℝ (U t) (X 0 t a))
    (hκ : ∀ a s, κ.val (t, a, s) = labelWaveVector X 0 a k t) :
    let A : Velocity := fun r => X r 0
    let O := hierarchyConcreteOperators hT G M κ
    momentumResidual (Icc 0 T) (U + graphRead A k W) (p + graphRead A k q) t x =
      graphRead A k (O.material W + O.labelAdv W W + O.phaseAdv W W +
        O.labelGrad q + O.phaseGrad q) t x + momentumResidual (Icc 0 T) U p t x := by
  let A : Velocity := fun r => X r 0
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hInv : X 0 t (A t x) = x := ((hX.inverse hLip (left_mem_Icc.mpr hT.le) ht).2 x)
  let D := Icc 0 T ×ˢ (univ : Set Vec3)
  have hUd : HasFDerivWithinAt (Function.uncurry U)
      (fderivWithin ℝ (Function.uncurry U) D (t, x)) D (t, x) :=
    ((hU.differentiableOn (by simp)) (t, x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hTime : DifferentiableWithinAt ℝ (fun r => U r x) (Icc 0 T) t := by
    have hTime' := hUd.comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) x))
      (fun r hr => show (r, x) ∈ D from ⟨hr, mem_univ x⟩)
    exact hTime'.differentiableWithinAt
  have hSpace : DifferentiableAt ℝ (U t) x :=
    (hUd.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
      (Eventually.of_forall fun y => mem_prod.mpr ⟨ht, mem_univ y⟩)).differentiableAt
  apply momentumResidual_graphRead hT G M κ W q ht
    (hX.hasFDerivWithinAt_inverseLabel_time_label hT hU hper hAreg ht x)
    (neg_add_cancel _) hTime hSpace hp
  · change G.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [hG, hInv]
  · change M.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [hM, hInv]
  · change κ.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [hκ, labelWaveVector, hInv]

end HierarchySmoothProfile

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

set_option maxHeartbeats 1300000 in
/-- The constructed skew-periodic hierarchy has exactly the retained
remainder and activation switches in Eulerian momentum. The physical
parent residual is the phase-independent profile pulled back by the
forward parent flow. -/
theorem momentumResidual_construct_graphRead
    {U : Velocity} {X : ℝ → Velocity} {p : Pressure} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (U r))
    (hAreg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (G M : VPmap) (κ : VP)
    (S : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    {P : ℕ} (hP : 2 ≤ P) (leadingSwitch completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hL : (twistedHierarchyOperators hT G M κ).material leading.V +
      (twistedHierarchyOperators hT G M κ).phaseGrad leading.p = leadingSwitch)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (hp : DifferentiableAt ℝ (p t) x)
    (hG : ∀ a s, G.val.val.val (t, a, s) = fderiv ℝ (X t 0) (X 0 t a))
    (hM : ∀ a s, M.val.val.val (t, a, s) = fderiv ℝ (U t) (X 0 t a))
    (hκ : ∀ a s, κ.val.val.val (t, a, s) = labelWaveVector X 0 a k t)
    (hRphys : ∀ a s, parentResidual.val.val.val (t, a, s) =
      momentumResidual (Icc 0 T) U p t (X 0 t a)) :
    let O := twistedHierarchyOperators hT G M κ
    let A : Velocity := fun r => X r 0
    let u := S.construct P completionSwitch parentResidual hR leading
    momentumResidual (Icc 0 T)
      (U + HierarchySmoothProfile.graphRead A k (u.velocity P).val.val)
      (p + HierarchySmoothProfile.graphRead A k (u.pressure P).val.val) t x =
        HierarchySmoothProfile.graphRead A k
          (O.remainder u P + (leadingSwitch + completionSwitch)).val.val t x := by
  let O := twistedHierarchyOperators hT G M κ
  let O₀ := HierarchySmoothProfile.hierarchyConcreteOperators hT G.val.val M.val.val κ.val.val
  let A : Velocity := fun r => X r 0
  let u := S.construct P completionSwitch parentResidual hR leading
  let W := u.velocity P
  let Q := u.pressure P
  let z := hierarchyGraphPoint A k t x
  have hm := S.construct_momentum hP leadingSwitch completionSwitch parentResidual hR leading hL
  have hEq := congrArg (fun F : VP => F.val.val) hm
  change O₀.material W.val.val + O₀.labelAdv W.val.val W.val.val + O₀.phaseAdv W.val.val W.val.val +
    O₀.labelGrad Q.val.val + O₀.phaseGrad Q.val.val + parentResidual.val.val =
    (O.remainder u P + (leadingSwitch + completionSwitch)).val.val at hEq
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hInv : X 0 t (A t x) = x := (hX.inverse hLip (left_mem_Icc.mpr hT.le) ht).2 x
  have hRz : parentResidual.val.val.val z = momentumResidual (Icc 0 T) U p t x := by
    change parentResidual.val.val.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [hRphys, hInv]
  change momentumResidual (Icc 0 T) (U + HierarchySmoothProfile.graphRead A k W.val.val)
    (p + HierarchySmoothProfile.graphRead A k Q.val.val) t x =
      HierarchySmoothProfile.graphRead A k (O.remainder u P + (leadingSwitch + completionSwitch)).val.val t x
  rw [HierarchySmoothProfile.momentumResidual_graphRead_parent hT hX hU hper hAreg
    G.val.val M.val.val κ.val.val W.val.val Q.val.val k ht x hp hG hM hκ, ← hRz]
  change (O₀.material W.val.val + O₀.labelAdv W.val.val W.val.val + O₀.phaseAdv W.val.val W.val.val +
    O₀.labelGrad Q.val.val + O₀.phaseGrad Q.val.val + parentResidual.val.val).val z =
      (O.remainder u P + (leadingSwitch + completionSwitch)).val.val.val z
  rw [hEq]

end HierarchyTwistedProfile

section GraphSymmetry

variable {E : Type*}

/-- Affine periodicity of the inverse labels and compatibility of the
profile with the carrier shift give periodicity on the Eulerian graph. -/
theorem spatiallyPeriodic_transportedProfile {A : Velocity} {k : Vec3}
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ}
    (hA : ∀ (n : Fin 3 → ℤ) x, A t (x + latticeVector n) = A t x + latticeVector n)
    (hf : ∀ (n : Fin 3 → ℤ) a s,
      f t (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) = f t a s) :
    SpatiallyPeriodic (transportedProfile A k f t) := by
  intro n x
  simpa only [transportedProfile, hA n x, inner_add_right] using
    hf n (A t x) ⟪k, A t x⟫_ℝ

/-- Reflection in the Eulerian variable reflects both the label and the phase. -/
theorem transportedProfile_neg_equivariant {A : Velocity} {k : Vec3}
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ} {R : E → E}
    (hA : Function.Odd (A t)) (hf : ∀ a s, f t (-a) (-s) = R (f t a s)) (x : Vec3) :
    transportedProfile A k f t (-x) = R (transportedProfile A k f t x) := by
  simpa only [transportedProfile, hA x, inner_neg_right] using hf (A t x) ⟪k, A t x⟫_ℝ

/-- Jointly odd velocity profiles give an odd Eulerian velocity. -/
theorem odd_transportedProfile [Neg E] {A : Velocity} {k : Vec3}
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ}
    (hA : Function.Odd (A t)) (hf : ∀ a s, f t (-a) (-s) = -f t a s) :
    Function.Odd (transportedProfile A k f t) :=
  transportedProfile_neg_equivariant (R := Neg.neg) hA hf

/-- Jointly even pressure profiles give an even Eulerian pressure. -/
theorem even_transportedProfile {A : Velocity} {k : Vec3}
    {f : ℝ → Vec3 → ℝ → E} {t : ℝ}
    (hA : Function.Odd (A t)) (hf : ∀ a s, f t (-a) (-s) = f t a s) :
    Function.Even (transportedProfile A k f t) :=
  transportedProfile_neg_equivariant (R := id) hA hf

end GraphSymmetry

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eulerian readout of a skew-periodic phase profile. -/
def graphRead (A : Velocity) (f : HierarchyTwistedProfile T k E) : ℝ → Vec3 → E :=
  HierarchySmoothProfile.graphRead A k f.val.val

theorem spatiallyPeriodic_graphRead (A : Velocity) (f : HierarchyTwistedProfile T k E) (t : ℝ)
    (hA : ∀ (n : Fin 3 → ℤ) x, A t (x + latticeVector n) = A t x + latticeVector n) :
    SpatiallyPeriodic (graphRead A f t) :=
  spatiallyPeriodic_transportedProfile (k := k) (f := fun r a s => f.val.val.val (r, a, s))
    hA (fun n a s => twistedSlice f t a s n)

/-- Actual inverse parent labels supply the affine lattice shift. -/
theorem spatiallyPeriodic_inverseParentGraphRead
    {U : Velocity} {X : ℝ → Velocity} (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (U r))
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    SpatiallyPeriodic (graphRead (fun r => X r 0) f t) := by
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  exact spatiallyPeriodic_graphRead _ f t
    (hX.add_latticeVector hLip hper ht (left_mem_Icc.mpr hT.le))

/-- Joint label-phase reflection gives the same parity on the graph. -/
theorem graphRead_reflection (A : Velocity) (f : HierarchyTwistedProfile T k E) {t : ℝ}
    (hA : Function.Odd (A t)) {sign : ℝ}
    (hf : HierarchyProfileReflectionParity sign f.val.val.val) (x : Vec3) :
    graphRead A f t (-x) = sign • graphRead A f t x :=
  transportedProfile_neg_equivariant (k := k) (f := fun r a s => f.val.val.val (r, a, s))
    (R := fun v : E => sign • v) hA (fun a s => hf (t, a, s)) x

/-- For an odd parent, the parity of the skew-periodic profile is
also its Eulerian spatial parity. -/
theorem inverseParentGraphRead_reflection
    {U : Velocity} {X : ℝ → Velocity} (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ r ∈ Icc 0 T, SpatiallyPeriodic (U r))
    (hodd : ∀ r ∈ Icc 0 T, Function.Odd (U r))
    (f : HierarchyTwistedProfile T k E) {sign : ℝ}
    (hf : HierarchyProfileReflectionParity sign f.val.val.val) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : Vec3) :
    graphRead (fun r => X r 0) f t (-x) = sign • graphRead (fun r => X r 0) f t x := by
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  exact graphRead_reflection (fun r => X r 0) f (t := t)
    (hX.odd hLip hodd ht (left_mem_Icc.mpr hT.le)) hf x

end HierarchyTwistedProfile

end
end TorusEuler

namespace TorusEuler.HierarchySmoothProfile

noncomputable section

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

private def profileTraceCLM : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => LinearMap.trace ℝ Vec3 D.toLinearMap
      map_add' := fun D E => (LinearMap.trace ℝ Vec3).map_add D.toLinearMap E.toLinearMap
      map_smul' := fun c D => (LinearMap.trace ℝ Vec3).map_smul c D.toLinearMap }

/-- The slow divergence contracts the label derivative with the inverse-flow
differential in the Eulerian directions. -/
def profileLabelDivergence (hT : 0 < T) (G : VPmap) : VP →ₗ[ℝ] SP :=
  (map profileTraceCLM).comp (((applyField.flip G).comp
    (map (compL ℝ Vec3 Vec3 Vec3))).comp (profileLabelDifferential hT))

theorem profileLabelDivergence_apply (hT : 0 < T) (G : VPmap) (W : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profileLabelDivergence hT G W).val (t, a, s) =
      LinearMap.trace ℝ Vec3
        (((fderiv ℝ (fun b => W.val (t, b, s)) a).comp (G.val (t, a, s))).toLinearMap) := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [profileLabelDivergence, LinearMap.comp_apply, LinearMap.flip_apply, map_apply _ _ hx,
    applyField_eval _ _ hx, profileLabelDifferential_apply_eq_fderiv hT W ht]
  rfl

/-- The fast divergence contracts the phase derivative with the transported covector. -/
def profilePhaseDivergence (hT : 0 < T) (κ : VP) : VP →ₗ[ℝ] SP :=
  (applyField (map (innerSL ℝ) κ)).comp (derivativeAlong hT (constant (0, 0, 1)))

theorem profilePhaseDivergence_apply (hT : 0 < T) (κ W : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profilePhaseDivergence hT κ W).val (t, a, s) =
      ⟪κ.val (t, a, s), deriv (fun r => W.val (t, a, r)) s⟫_ℝ := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [profilePhaseDivergence, LinearMap.comp_apply, map_apply _ _ hx,
    applyField_eval _ _ hx, derivativeAlong_apply _ _ _ hx, constant_apply _ hx,
    (hasDerivAt_profilePhase W ht a s).deriv]
  rfl

/-- The total divergence operator for a vector profile at arbitrary label and phase. -/
def profileTotalDivergence (hT : 0 < T) (G : VPmap) (κ : VP) : VP →ₗ[ℝ] SP :=
  profileLabelDivergence hT G + profilePhaseDivergence hT κ

theorem profileTotalDivergence_apply (hT : 0 < T) (G : VPmap) (κ W : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profileTotalDivergence hT G κ W).val (t, a, s) =
      (∑ i : Fin 3, (fderiv ℝ (fun b => W.val (t, b, s)) a
        (G.val (t, a, s) (EuclideanSpace.single i 1))) i) +
      ⟪κ.val (t, a, s), deriv (fun r => W.val (t, a, r)) s⟫_ℝ := by
  simp only [profileTotalDivergence, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    profileLabelDivergence_apply hT G W ht, profilePhaseDivergence_apply hT κ W ht]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/-- The profile divergence evaluated on the phase graph equals ordinary
Eulerian divergence, including at a time-slab endpoint. -/
theorem divergence_transportedSmoothProfile (hT : 0 < T) (G : VPmap) (κ W : VP)
    {A : Velocity} {k x : Vec3} {t : ℝ} (ht : t ∈ Icc 0 T)
    {Ax : Vec3 →L[ℝ] Vec3} (hA : HasFDerivAt (A t) Ax x)
    (hG : G.val (t, A t x, ⟪k, A t x⟫_ℝ) = Ax)
    (hκ : κ.val (t, A t x, ⟪k, A t x⟫_ℝ) = Ax.adjoint k) :
    divergence (transportedProfile A k (fun r a s => W.val (r, a, s)) t) x =
      (profileTotalDivergence hT G κ W).val (t, A t x, ⟪k, A t x⟫_ℝ) := by
  have hW := ((contDiff_labelPhase_slice W ht).differentiable (by simp)
    (A t x, ⟪k, A t x⟫_ℝ))
  rw [divergence_transportedHierarchy hA (hasFDerivAt_profile_partials hW)]
  simp only [profileTotalDivergence, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    profileLabelDivergence_apply hT G W ht, profilePhaseDivergence_apply hT κ W ht, hG, hκ]

/-- A zero profile divergence transports to zero Eulerian divergence. -/
theorem divergence_transportedSmoothProfile_eq_zero (hT : 0 < T) (G : VPmap) (κ W : VP)
    {A : Velocity} {k x : Vec3} {t : ℝ} (ht : t ∈ Icc 0 T)
    {Ax : Vec3 →L[ℝ] Vec3} (hA : HasFDerivAt (A t) Ax x)
    (hG : G.val (t, A t x, ⟪k, A t x⟫_ℝ) = Ax)
    (hκ : κ.val (t, A t x, ⟪k, A t x⟫_ℝ) = Ax.adjoint k)
    (hW : profileTotalDivergence hT G κ W = 0) :
    divergence (transportedProfile A k (fun r a s => W.val (r, a, s)) t) x = 0 := by
  rw [divergence_transportedSmoothProfile hT G κ W ht hA hG hκ, hW]
  rfl

/-- A completed transverse oscillation transports to a divergence-free field. -/
theorem divergence_transportedProfileCompletion_eq_zero (hT : 0 < T) (G : VPmap) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    {A : Velocity} {k x : Vec3} {t : ℝ} (ht : t ∈ Icc 0 T) (hA : ContDiff ℝ 2 (A t))
    (hG : ∀ y s, G.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ y s, κ.val (t, A t y, s) = (fderiv ℝ (A t) y).adjoint k)
    (htrans : ∀ a s, ⟪κ.val (t, a, 0), V.val (t, a, s)⟫_ℝ = 0) :
    let W := V + profileCompletion hT G κ hκ V
    divergence (transportedProfile A k (fun r a s => W.val (r, a, s)) t) x = 0 := by
  let s := ⟪k, A t x⟫_ℝ
  let W := V + profileCompletion hT G κ hκ V
  change divergence (transportedProfile A k (fun r a s => W.val (r, a, s)) t) x = 0
  rw [divergence_transportedSmoothProfile hT G κ W ht
    ((hA.differentiable (by simp) x).hasFDerivAt) (hG x s) (hκflow x s),
    profileTotalDivergence_apply hT G κ W ht, hG, hκflow]
  have hcancel := profileCompletion_slowFastDivergence hT G κ V hκ ht hA k hG
    (fun y => hκflow y 0) htrans x s
  change (∑ i : Fin 3, (fderiv ℝ (fun a => W.val (t, a, s)) (A t x)
    (fderiv ℝ (A t) x (EuclideanSpace.single i 1))) i) +
      ⟪κ.val (t, A t x, 0), deriv (fun r => W.val (t, A t x, r)) s⟫_ℝ = 0 at hcancel
  rwa [hκflow] at hcancel

/-- Every label is covered by the inverse chart, so the pointwise
curl cancellation is zero as a smooth profile. -/
theorem profileTotalDivergence_completion_eq_zero (hT : 0 < T) (G : VPmap) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    {A : Velocity} (k : Vec3)
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ t ∈ Icc 0 T, ∀ y s, κ.val (t, A t y, s) = (fderiv ℝ (A t) y).adjoint k)
    (htrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val (t, a, 0), V.val (t, a, s)⟫_ℝ = 0) :
    profileTotalDivergence hT G κ (V + profileCompletion hT G κ hκ V) = 0 := by
  apply HierarchySmoothProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  obtain ⟨x, rfl⟩ := hsurj t ht a
  let W := V + profileCompletion hT G κ hκ V
  change (profileTotalDivergence hT G κ W).val (t, A t x, s) = 0
  rw [profileTotalDivergence_apply hT G κ W ht, hG t ht x s, hκflow t ht x s]
  have hcancel := profileCompletion_slowFastDivergence hT G κ V hκ ht (hA t ht) k
    (hG t ht) (fun y => hκflow t ht y 0) (htrans t ht) x s
  change (∑ i : Fin 3, (fderiv ℝ (fun a => W.val (t, a, s)) (A t x)
    (fderiv ℝ (A t) x (EuclideanSpace.single i 1))) i) +
      ⟪κ.val (t, A t x, 0), deriv (fun r => W.val (t, A t x, r)) s⟫_ℝ = 0 at hcancel
  rwa [hκflow t ht x 0] at hcancel

/-- A phase-independent mean has zero profile divergence whenever its
Eulerian mean is solenoidal. The inverse chart covers the whole label space. -/
theorem profileTotalDivergence_eq_zero_of_meanGraph
    (hT : 0 < T) (G : VPmap) (κ B : VP) {A : Velocity} (k : Vec3)
    (hA : ∀ t ∈ Icc 0 T, Differentiable ℝ (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκ : ∀ t ∈ Icc 0 T, ∀ y s, κ.val (t, A t y, s) = (fderiv ℝ (A t) y).adjoint k)
    (hB : HierarchyPeriodicProfile.PhaseIndependent B)
    (hDiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (graphRead A k B t) x = 0) :
    profileTotalDivergence hT G κ B = 0 := by
  apply HierarchySmoothProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  obtain ⟨x, rfl⟩ := hsurj t ht a
  let r := ⟪k, A t x⟫_ℝ
  have hlabel : (fun b => B.val (t, b, s)) = fun b => B.val (t, b, r) :=
    funext fun b => hB (t, b, r) ⟨ht, mem_univ _⟩ s
  have hphase : (fun v => B.val (t, A t x, v)) = fun _ => B.val (t, A t x, r) :=
    funext (hB (t, A t x, r) ⟨ht, mem_univ _⟩)
  have hg := divergence_transportedSmoothProfile hT G κ B ht (k := k)
    ((hA t ht x).hasFDerivAt) (hG t ht x r) (hκ t ht x r)
  change divergence (graphRead A k B t) x =
    (profileTotalDivergence hT G κ B).val (t, A t x, r) at hg
  rw [hDiv t ht x] at hg
  change (profileTotalDivergence hT G κ B).val (t, A t x, s) = 0
  refine Eq.trans ?_ hg.symm
  rw [profileTotalDivergence_apply hT G κ B ht, profileTotalDivergence_apply hT G κ B ht,
    hG t ht x s, hG t ht x r, hlabel, hphase]
  simp

end

end TorusEuler.HierarchySmoothProfile

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "base" => HierarchySmoothProfile.profileTotalDivergence

/-- The constructed solenoidal hierarchy gives an Eulerian solenoidal
perturbation on its transported graph. The premises are the divergence
properties of the two concrete solver outputs. -/
theorem divergence_construct_graphRead
    (hT : 0 < T) (G M : VPmap) (κ : VP)
    (S : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    (P : ℕ) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hC : ∀ o : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ),
      base hT G.val.val κ.val.val (o.V + S.complete o.V).val.val = 0)
    (hB : ∀ f hf, base hT G.val.val κ.val.val (S.solveMean f hf).val.B.val.val = 0)
    {A : Velocity} {t : ℝ} (ht : t ∈ Icc 0 T) {x : Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) Ax x)
    (hG : G.val.val.val (hierarchyGraphPoint A k t x) = Ax)
    (hκ : κ.val.val.val (hierarchyGraphPoint A k t x) = Ax.adjoint k) :
    let u := S.construct P completionSwitch parentResidual hR leading
    divergence (graphRead A (u.velocity P) t) x = 0 := by
  let forget : VP →ₗ[ℝ] HierarchySmoothProfile T Vec3 :=
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype.comp
      (hierarchyTwistedProfileSubmodule T k Vec3).subtype
  let D := (base hT G.val.val κ.val.val).comp forget
  have hd := S.construct_divergence_eq_zero P completionSwitch parentResidual hR leading D hC hB
  exact HierarchySmoothProfile.divergence_transportedSmoothProfile_eq_zero hT G.val.val κ.val.val
    ((S.construct P completionSwitch parentResidual hR leading).velocity P).val.val ht hA hG hκ hd

end
end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

set_option maxHeartbeats 600000 in
/-- Vanishing fast advection on all twisted test profiles forces transversality.
A phase derivative can attain a nonzero prescribed direction at every point. -/
theorem transverse_of_phaseAdv_eq_zero (hT : 0 < T) (G M : VPmap) (κ u : VP)
    (hu : ∀ v : VP, (twistedHierarchyOperators hT G M κ).phaseAdv u v = 0) :
    ∀ x ∈ hierarchyProfileSlab T, ⟪κ.val.val.val x, u.val.val.val x⟫_ℝ = 0 := by
  rintro ⟨t, a, s⟩ hx
  let e : Vec3 := EuclideanSpace.single 0 1
  have he : e ≠ 0 := by simp [e, EuclideanSpace.single]
  let c : ℝ := s - ⟪k, a⟫_ℝ
  let f (y : HierarchyProfilePoint) : Vec3 :=
    Real.sin (2 * Real.pi * (y.2.2 - ⟪k, y.2.1⟫_ℝ - c)) • e
  have hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T) := by
    have harg : ContDiff ℝ ∞ (fun y : HierarchyProfilePoint => y.2.2 - ⟪k, y.2.1⟫_ℝ - c) :=
      (contDiff_snd.snd.sub ((innerSL ℝ k).contDiff.comp contDiff_snd.fst)).sub contDiff_const
    exact ((contDiff_const.mul harg).sin.smul contDiff_const).contDiffOn
  have hphase : Function.Periodic f hierarchyPhasePeriod := by
    rintro ⟨r, b, z⟩
    simp only [f, hierarchyPhasePeriod, Prod.mk_add_mk, add_zero]
    rw [show 2 * Real.pi * (z + 1 - ⟪k, b⟫_ℝ - c) =
      2 * Real.pi * (z - ⟪k, b⟫_ℝ - c) + 2 * Real.pi by ring, Real.sin_add_two_pi]
  have htwist (n : Fin 3 → ℤ) : Function.Periodic f (hierarchyLatticeShift k n) := by
    rintro ⟨r, b, z⟩
    simp only [add_hierarchyLatticeShift, f, inner_add_right]
    rw [show z + ⟪k, latticeVector n⟫_ℝ - (⟪k, b⟫_ℝ + ⟪k, latticeVector n⟫_ℝ) - c =
      z - ⟪k, b⟫_ℝ - c by ring]
  let v : VP := ofSmooth f hf hphase htwist
  have hv : (fun r => v.val.val.val (t, a, r)) = fun r =>
      Real.sin (2 * Real.pi * (r - ⟪k, a⟫_ℝ - c)) • e :=
    funext fun r => ofSmooth_eval hf hphase htwist ⟨hx.1, mem_univ _⟩
  have hD : HasDerivAt (fun r => Real.sin (2 * Real.pi * (r - ⟪k, a⟫_ℝ - c)) • e)
      ((2 * Real.pi) • e) s := by
    have h := (((hasDerivAt_id s).sub_const ⟪k, a⟫_ℝ).sub_const c).const_mul (2 * Real.pi)
    have hsin := h.sin.smul_const e
    simpa [c] using hsin
  have hD' : fderivWithin ℝ v.val.val.val (hierarchyProfileSlab T) (t, a, s) (0, 0, 1) =
      (2 * Real.pi) • e := by
    have h := HierarchySmoothProfile.hasDerivAt_profilePhase v.val.val hx.1 a s
    rw [hv] at h
    exact h.unique hD
  have hz := congrArg (fun w : VP => w.val.val.val (t, a, s)) (hu v)
  change ((twistedHierarchyOperators hT G M κ).phaseAdv u v).val.val.val (t, a, s) = 0 at hz
  rw [twistedHierarchyOperators_phaseAdv_val,
    HierarchyPeriodicProfile.periodicHierarchyOperators_phaseAdv_val] at hz
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val.val)
    u.val.val v.val.val).val (t, a, s) = 0 at hz
  rw [HierarchySmoothProfile.advect_apply hT _ u.val.val v.val.val hx,
    HierarchySmoothProfile.phaseDirections_apply κ.val.val u.val.val hx] at hz
  let b : ℝ := ⟪κ.val.val.val (t, a, s), u.val.val.val (t, a, s)⟫_ℝ
  have hb : ((0, 0, b) : HierarchyProfilePoint) = b • ((0, 0, 1) : HierarchyProfilePoint) := by simp
  change fderivWithin ℝ v.val.val.val (hierarchyProfileSlab T) (t, a, s) (0, 0, b) = 0 at hz
  rw [hb, map_smul, hD', smul_smul] at hz
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right he)).resolve_right
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)

/-- The concrete twisted completion gives the solenoidal input required
by `construct_divergence_eq_zero`. The transverse-output equation alone
supplies pointwise transversality via the skew-periodic probe. -/
theorem profileTotalDivergence_completedOutput_eq_zero
    (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (o : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ)) {A : Velocity}
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val.val.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ t ∈ Icc 0 T, ∀ y s,
      κ.val.val.val (t, A t y, s) = (fderiv ℝ (A t) y).adjoint k) :
    HierarchySmoothProfile.profileTotalDivergence hT G.val.val κ.val.val
      (o.V + complete hT G κ hκPhase hκ o.V).val.val = 0 := by
  have ho : profilePhaseAverage hT o.V = 0 := o.average_V
  have htrans := transverse_of_phaseAdv_eq_zero hT G M κ o.V o.phaseAdv_V
  change HierarchySmoothProfile.profileTotalDivergence hT G.val.val κ.val.val
    (o.V.val.val + (complete hT G κ hκPhase hκ o.V).val.val) = 0
  rw [complete_val_val_of_phaseMean_zero hT G κ hκPhase hκ o.V ho]
  apply HierarchySmoothProfile.profileTotalDivergence_completion_eq_zero
    hT G.val.val κ.val.val o.V.val.val hκ k hA hsurj hG hκflow
  intro t ht a s
  have he : κ.val.val.val (t, a, s) = κ.val.val.val (t, a, 0) :=
    hκPhase (t, a, 0) ⟨ht, mem_univ _⟩ s
  rw [← he]
  exact htrans (t, a, s) ⟨ht, mem_univ _⟩

end

end TorusEuler.HierarchyTwistedProfile
