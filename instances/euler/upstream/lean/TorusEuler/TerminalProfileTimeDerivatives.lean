import TorusEuler.HierarchyTwistedProfiles
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-! Constant-direction derivatives and time jets of the actual slab profiles. -/

open Set ContinuousLinearMap
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A derivative in a fixed direction of the slab. -/
def directionDerivative (hT : 0 < T) (v : HierarchyProfilePoint) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E :=
  (map (ContinuousLinearMap.apply ℝ E v)).comp (derivative hT)

theorem directionDerivative_apply (hT : 0 < T) (v : HierarchyProfilePoint)
    (f : HierarchyTwistedProfile T k E) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) :
    (directionDerivative hT v f).val.val.val x =
      fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) x v := by
  simp [directionDerivative, HierarchyPeriodicProfile.map_val, HierarchySmoothProfile.map_apply,
    HierarchyPeriodicProfile.derivative_val, HierarchySmoothProfile.derivative_apply, hx]

/-- Differentiate in time with the label and independent phase fixed. -/
abbrev timeDerivative (hT : 0 < T) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E :=
  directionDerivative hT (1, 0, 0)

theorem timeDerivative_apply (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (timeDerivative hT f).val.val.val (t, x) =
      derivWithin (fun u => f.val.val.val (u, x)) (Icc 0 T) t := by
  rw [timeDerivative, directionDerivative_apply hT _ _ ⟨ht, mem_univ _⟩]
  let j : ℝ → HierarchyProfilePoint := fun u => (u, x)
  have hj : HasDerivAt j (1, 0, 0) t :=
    hasDerivAt_id t |>.prodMk (hasDerivAt_const t x)
  have hf := ((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp)
    (t, x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  exact (hf.comp_hasDerivWithinAt t hj.hasDerivWithinAt
    (show MapsTo j (Icc 0 T) (hierarchyProfileSlab T) from fun _ hu => ⟨hu, mem_univ _⟩)).derivWithin
      (uniqueDiffOn_Icc hT t ht) |>.symm

/-- The iterated time derivative as a linear profile operator. -/
def timeJet (hT : 0 < T) (i : ℕ) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E :=
  (timeDerivative hT) ^ i

@[simp] theorem timeJet_zero (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    timeJet hT 0 f = f := rfl

theorem timeJet_succ (hT : 0 < T) (i : ℕ) (f : HierarchyTwistedProfile T k E) :
    timeJet hT (i + 1) f = timeDerivative hT (timeJet hT i f) := by
  rw [timeJet, pow_succ']
  rfl

theorem timeJet_succ' (hT : 0 < T) (i : ℕ) (f : HierarchyTwistedProfile T k E) :
    timeJet hT (i + 1) f = timeJet hT i (timeDerivative hT f) := by
  rw [timeJet, pow_succ]
  rfl

/-- The profile derivative is the genuine one-variable closed-slab derivative. -/
theorem timeJet_apply (hT : 0 < T) (i : ℕ) (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (timeJet hT i f).val.val.val (t, x) =
      iteratedDerivWithin i (fun u => f.val.val.val (u, x)) (Icc 0 T) t := by
  induction i generalizing t with
  | zero => simp
  | succ n ih =>
    rw [timeJet_succ, timeDerivative_apply hT _ ht, iteratedDerivWithin_succ]
    exact derivWithin_congr (fun _ hu => ih hu) (ih ht)

/-- The second within-slab derivative commutes along any two fixed directions. -/
theorem directionDerivative_comm (hT : 0 < T) (v w : HierarchyProfilePoint)
    (f : HierarchyTwistedProfile T k E) :
    directionDerivative hT v (directionDerivative hT w f) =
      directionDerivative hT w (directionDerivative hT v f) := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  let S := hierarchyProfileSlab T
  let D := fderivWithin ℝ f.val.val.val S
  have hu := uniqueDiffOn_hierarchyProfileSlab hT
  have hd := (HierarchySmoothProfile.smooth f.val.val).fderivWithin hu (m := ∞) (by simp)
  have hInterior : (interior S).Nonempty := by
    refine ⟨(T / 2, 0, 0), ?_⟩
    change (T / 2, (0 : Vec3), (0 : ℝ)) ∈ interior (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ)))
    rw [interior_prod_eq, interior_Icc, interior_univ]
    exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hConvex : Convex ℝ S := (convex_Icc 0 T).prod convex_univ
  have hsym :=
    hConvex.second_derivative_within_at_symmetric (f := f.val.val.val) (f' := D) hInterior
      (fun y hy =>
        (((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp)
          y (interior_subset hy)).hasFDerivWithinAt).hasFDerivAt (mem_interior_iff_mem_nhds.mp hy))
      hx (((hd.differentiableOn (by simp) x hx).hasFDerivWithinAt).mono interior_subset) v w
  have hDeriv (a b : HierarchyProfilePoint) :
      (directionDerivative hT a (directionDerivative hT b f)).val.val.val x =
        fderivWithin ℝ D S x a b := by
    rw [directionDerivative_apply hT _ _ hx,
      fderivWithin_congr' (show EqOn (directionDerivative hT b f).val.val.val
        (fun y => D y b) S from fun y hy => directionDerivative_apply hT b f hy) hx]
    exact congrArg (fun L : HierarchyProfilePoint →L[ℝ] E => L a)
      (((ContinuousLinearMap.apply ℝ E b).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hd.differentiableOn (by simp) x hx).hasFDerivWithinAt)).fderivWithin (hu x hx))
  rw [hDeriv, hDeriv]
  exact hsym

/-- Arbitrary time jets commute with a fixed label, phase, or time direction. -/
theorem timeJet_directionDerivative (hT : 0 < T) (i : ℕ) (v : HierarchyProfilePoint)
    (f : HierarchyTwistedProfile T k E) :
    timeJet hT i (directionDerivative hT v f) = directionDerivative hT v (timeJet hT i f) := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [timeJet_succ, timeJet_succ, ih, directionDerivative_comm hT (1, 0, 0) v]

end

end TorusEuler.HierarchyTwistedProfile
