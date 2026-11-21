import TorusEuler.HierarchyPhysicalGraph
import TorusEuler.LocalizedSeedRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Closed-slab differentiation on Eulerian time slices and transported profiles. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "SpaceTimeSlab(" T ")" => Set.prod (TimeSlab(T)) (univ : Set Vec3)

/-- The one-dimensional Leibniz rule for a continuous bilinear operation. -/
theorem iteratedDerivWithin_bilinear {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ → E} {g : ℝ → F} {S : Set ℝ} {t : ℝ} (hS : UniqueDiffOn ℝ S) (ht : t ∈ S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S) (q : ℕ) :
    iteratedDerivWithin q (fun r => B (f r) (g r)) S t = ∑ i ∈ Finset.range (q + 1),
      q.choose i • B (iteratedDerivWithin i f S t) (iteratedDerivWithin (q - i) g S t) := by
  induction q generalizing f g with
  | zero => simp
  | succ q ih =>
    have hf' := hf.derivWithin hS (m := ∞) (by simp)
    have hg' := hg.derivWithin hS (m := ∞) (by simp)
    have hderiv (r : ℝ) (hr : r ∈ S) :
        derivWithin (fun y => B (f y) (g y)) S r =
          B (f r) (derivWithin g S r) + B (derivWithin f S r) (g r) :=
      B.derivWithin_of_bilinear (hf.differentiableOn (by simp) r hr) (hg.differentiableOn (by simp) r hr)
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (fun r hr => hderiv r hr) ht]
    have hleft : ContDiffWithinAt ℝ q (fun r => B (f r) (derivWithin g S r)) S t :=
      ((B.contDiff.comp_contDiffOn hf).clm_apply hg').of_le (by simp) t ht
    have hright : ContDiffWithinAt ℝ q (fun r => B (derivWithin f S r) (g r)) S t :=
      ((B.contDiff.comp_contDiffOn hf').clm_apply hg).of_le (by simp) t ht
    change iteratedDerivWithin q ((fun r => B (f r) (derivWithin g S r)) +
      (fun r => B (derivWithin f S r) (g r))) S t = _
    rw [iteratedDerivWithin_add ht hS hleft hright, ih hf hg', ih hf' hg]
    simp only [← iteratedDerivWithin_succ']
    nth_rw 1 [Finset.sum_range_succ']
    nth_rw 2 [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib,
      Nat.choose_zero_right, one_nsmul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    nth_rw 3 [Finset.sum_range_succ]
    have hs (j : ℕ) (hj : j ∈ Finset.range q) : q - (j + 1) + 1 = q - j := by
      have := Finset.mem_range.mp hj
      omega
    simp +contextual [hs]
    abel

namespace HierarchySmoothProfile

variable {T : ℝ}

/-- At fixed label and phase this is the ordinary time derivative on the slab. -/
def slabTimePartial (hT : 0 < T) :
    HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T E :=
  derivativeAlong hT (constant (1,0,0))

theorem slabTimePartial_apply (hT : 0 < T) (f : HierarchySmoothProfile T E)
    {z : HierarchyProfilePoint} (hz : z ∈ hierarchyProfileSlab T) :
    (slabTimePartial hT f).val z = fderivWithin ℝ f.val (hierarchyProfileSlab T) z (1,0,0) := by
  rw [slabTimePartial, derivativeAlong_apply _ _ _ hz, constant_apply _ hz]

/-- Inverse-flow graph evaluation transforms the time derivative at fixed
label and phase to the Eulerian material derivative. -/
theorem slabTimePartial_graphRead (hT : 0 < T) (f : HierarchySmoothProfile T E)
    {U : Velocity} {X : ℝ → Velocity} (hX : IsLabelFlowOn U X TimeSlab(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) SpaceTimeSlab(T))
    (hper : ∀ r ∈ TimeSlab(T), SpatiallyPeriodic (U r))
    (k : Vec3) {t : ℝ} (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    let A : Velocity := fun r => X r 0
    derivWithin (fun r => graphRead A k f r x) TimeSlab(T) t +
        fderiv ℝ (graphRead A k f t) x (U t x) =
      graphRead A k (slabTimePartial hT f) t x := by
  let A : Velocity := fun r => X r 0
  let G : ℝ × Vec3 → HierarchyProfilePoint := fun z => hierarchyGraphPoint A k z.1 z.2
  let z := G (t,x)
  let DA := fderiv ℝ (A t) x
  let D := ((toSpanSingleton ℝ (-(DA (U t x)))).coprod DA)
  let DF := fderivWithin ℝ f.val (hierarchyProfileSlab T) z
  have hz : z ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hAreg := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hA : HasFDerivWithinAt (Function.uncurry A) D SpaceTimeSlab(T) (t,x) :=
    hX.hasFDerivWithinAt_inverseLabel_time_label hT hU hper hAreg ht x
  have hfst : HasFDerivWithinAt Prod.fst (fst ℝ ℝ Vec3) SpaceTimeSlab(T) (t,x) :=
    hasFDerivWithinAt_fst
  have hG' : HasFDerivWithinAt G
      ((fst ℝ ℝ Vec3).prod (D.prod ((innerSL ℝ k).comp D)))
      SpaceTimeSlab(T) (t,x) := hfst.prodMk
    (hA.prodMk ((innerSL ℝ k).hasFDerivAt.comp_hasFDerivWithinAt (t,x) hA))
  have hDF : HasFDerivWithinAt f.val DF (hierarchyProfileSlab T) z :=
    ((smooth f).differentiableOn (by simp) z hz).hasFDerivWithinAt
  let DG := (fst ℝ ℝ Vec3).prod (D.prod ((innerSL ℝ k).comp D))
  have hRead : HasFDerivWithinAt (Function.uncurry (graphRead A k f))
      (DF.comp DG) SpaceTimeSlab(T) (t,x) :=
    hDF.comp (t,x) hG' (fun r hr => show G r ∈ hierarchyProfileSlab T from ⟨hr.1, mem_univ _⟩)
  have htimeRaw := hRead.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t TimeSlab(T)).prodMk (hasDerivWithinAt_const t TimeSlab(T) x))
    (fun r hr => show (r,x) ∈ SpaceTimeSlab(T) from ⟨hr,mem_univ x⟩)
  have htime : HasDerivWithinAt (fun r => graphRead A k f r x) ((DF.comp DG) (1,0)) TimeSlab(T) t :=
    htimeRaw
  have hspace : HasFDerivAt (graphRead A k f t) ((DF.comp DG).comp (inr ℝ ℝ Vec3)) x :=
    hRead.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => ⟨ht, mem_univ y⟩)
  change derivWithin (fun r => graphRead A k f r x) TimeSlab(T) t +
    fderiv ℝ (graphRead A k f t) x (U t x) = (slabTimePartial hT f).val z
  rw [htime.derivWithin (uniqueDiffOn_Icc hT t ht), hspace.fderiv, slabTimePartial_apply hT f hz]
  change DF (DG (1,0)) + DF (DG (0,U t x)) = DF (1,0,0)
  rw [← map_add, ← map_add]
  change DF (DG ((1,0) + (0,U t x))) = DF (1,0,0)
  congr 1
  simp only [DG, prod_apply, Prod.fst_add, Prod.snd_add, add_zero, zero_add,
    comp_apply, D, coprod_apply, toSpanSingleton_apply, one_smul, neg_add_cancel, map_zero]
  change ((1 : ℝ) + 0, (0 : Vec3), (0 : ℝ)) = (1, 0, 0)
  rw [add_zero]

end HierarchySmoothProfile

end

end TorusEuler
