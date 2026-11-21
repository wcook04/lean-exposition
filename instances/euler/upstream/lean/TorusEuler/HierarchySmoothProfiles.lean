import TorusEuler.HierarchyCancellation
import TorusEuler.OscillatoryJointRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The differentiable profile space underlying the finite hierarchy on the time slab. -/

open ContinuousLinearMap Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

abbrev HierarchyProfilePoint := ℝ × Vec3 × ℝ

/-- The time, label and phase domain of the finite expansion. -/
def hierarchyProfileSlab (T : ℝ) : Set HierarchyProfilePoint :=
  Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))

theorem uniqueDiffOn_hierarchyProfileSlab {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (hierarchyProfileSlab T) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

section SmoothProfiles

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth slab profile is represented by its zero extension. Values of this
representative outside the slab do not enter any derivative or equation. -/
def hierarchySmoothProfileSubmodule (T : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (HierarchyProfilePoint → E) where
  carrier := {f | ContDiffOn ℝ ∞ f (hierarchyProfileSlab T) ∧
    ∀ x ∉ hierarchyProfileSlab T, f x = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, fun x hx => by simp only [Pi.add_apply, hf.2 x hx, hg.2 x hx, add_zero]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨contDiffOn_const.smul hf.1,
      fun x hx => by simp only [Pi.smul_apply, hf.2 x hx, smul_zero]⟩

abbrev HierarchySmoothProfile (T : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  hierarchySmoothProfileSubmodule T E

namespace HierarchySmoothProfile

variable {T : ℝ}

theorem smooth (f : HierarchySmoothProfile T E) :
    ContDiffOn ℝ ∞ f.val (hierarchyProfileSlab T) :=
  f.property.1

theorem eq_zero_outside (f : HierarchySmoothProfile T E) {x : HierarchyProfilePoint}
    (hx : x ∉ hierarchyProfileSlab T) : f.val x = 0 :=
  f.property.2 x hx

theorem ext {f g : HierarchySmoothProfile T E} (h : ∀ x ∈ hierarchyProfileSlab T, f.val x = g.val x) :
    f = g := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact h x hx
  · rw [eq_zero_outside f hx, eq_zero_outside g hx]

/-- Use the given smooth function on the closed slab and extend it by zero
for algebraic operations on profiles. -/
def ofSmooth (f : HierarchyProfilePoint → E) (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T)) :
    HierarchySmoothProfile T E := by
  classical
  refine ⟨fun x => if x ∈ hierarchyProfileSlab T then f x else 0, ?_, ?_⟩
  · exact hf.congr (fun x hx => ite_eq_left hx)
  · exact fun x hx => ite_eq_right hx

theorem ofSmooth_apply {f : HierarchyProfilePoint → E}
    (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T)) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) : (ofSmooth f hf).val x = f x := by
  simp [ofSmooth, hx]

/-- The actual Fréchet derivative of a profile within the closed time slab. -/
def derivative (hT : 0 < T) :
    HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T (HierarchyProfilePoint →L[ℝ] E) := by
  let B (f : HierarchySmoothProfile T E) :=
    ofSmooth (fderivWithin ℝ f.val (hierarchyProfileSlab T))
      ((smooth f).fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT) (m := ∞) (by simp))
  refine { toFun := B, map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply HierarchySmoothProfile.ext
    intro x hx
    change (B (f + g)).val x = (B f).val x + (B g).val x
    simp only [B, ofSmooth_apply _ hx, Submodule.coe_add]
    exact fderivWithin_add (uniqueDiffOn_hierarchyProfileSlab hT x hx)
      ((smooth f).differentiableOn (by simp) x hx) ((smooth g).differentiableOn (by simp) x hx)
  · intro c f
    apply HierarchySmoothProfile.ext
    intro x hx
    change (B (c • f)).val x = c • (B f).val x
    simp only [B, ofSmooth_apply _ hx, Submodule.coe_smul]
    exact fderivWithin_const_smul (uniqueDiffOn_hierarchyProfileSlab hT x hx)
      ((smooth f).differentiableOn (by simp) x hx) c

theorem derivative_apply (hT : 0 < T) (f : HierarchySmoothProfile T E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (derivative hT f).val x = fderivWithin ℝ f.val (hierarchyProfileSlab T) x :=
  ofSmooth_apply ((smooth f).fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT) (m := ∞)
    (by simp)) hx

/-- Postcomposition with a bounded linear map. -/
def map (Fmap : E →L[ℝ] F) : HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F where
  toFun f := ofSmooth (Fmap ∘ f.val) (Fmap.contDiff.comp_contDiffOn (smooth f))
  map_add' f g := by
    apply HierarchySmoothProfile.ext
    intro x hx
    simp only [ofSmooth_apply _ hx, Function.comp_apply, Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply HierarchySmoothProfile.ext
    intro x hx
    simp only [ofSmooth_apply _ hx, Function.comp_apply, Submodule.coe_smul, Pi.smul_apply,
      RingHom.id_apply, map_smul]

theorem map_apply (Fmap : E →L[ℝ] F) (f : HierarchySmoothProfile T E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (map Fmap f).val x = Fmap (f.val x) :=
  ofSmooth_apply (Fmap.contDiff.comp_contDiffOn (smooth f)) hx

/-- Pointwise application of a smooth operator profile to a smooth vector profile. -/
def applyField : HierarchySmoothProfile T (E →L[ℝ] F) →ₗ[ℝ]
    HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F := by
  let B (A : HierarchySmoothProfile T (E →L[ℝ] F)) (f : HierarchySmoothProfile T E) :=
    ofSmooth (fun x => A.val x (f.val x)) ((smooth A).clm_apply (smooth f))
  let B₁ (A : HierarchySmoothProfile T (E →L[ℝ] F)) :
      HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F :=
    { toFun := B A
      map_add' := by
        intro f g
        apply HierarchySmoothProfile.ext
        intro x hx
        simp only [B, ofSmooth_apply _ hx, Submodule.coe_add, Pi.add_apply, map_add]
      map_smul' := by
        intro c f
        apply HierarchySmoothProfile.ext
        intro x hx
        simp only [B, ofSmooth_apply _ hx, Submodule.coe_smul, Pi.smul_apply, map_smul,
          RingHom.id_apply] }
  refine { toFun := B₁, map_add' := ?_, map_smul' := ?_ }
  · intro A D
    apply LinearMap.ext
    intro f
    apply HierarchySmoothProfile.ext
    intro x hx
    simp only [B₁, B, LinearMap.coe_mk, AddHom.coe_mk, ofSmooth_apply _ hx,
      Submodule.coe_add, Pi.add_apply, add_apply, LinearMap.add_apply]
  · intro c A
    apply LinearMap.ext
    intro f
    apply HierarchySmoothProfile.ext
    intro x hx
    simp only [B₁, B, LinearMap.coe_mk, AddHom.coe_mk, ofSmooth_apply _ hx,
      Submodule.coe_smul, Pi.smul_apply, smul_apply, LinearMap.smul_apply, RingHom.id_apply]

theorem applyField_eval (A : HierarchySmoothProfile T (E →L[ℝ] F)) (f : HierarchySmoothProfile T E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (applyField A f).val x = A.val x (f.val x) :=
  ofSmooth_apply ((smooth A).clm_apply (smooth f)) hx

def constant (a : E) : HierarchySmoothProfile T E :=
  ofSmooth (fun _ => a) contDiffOn_const

theorem constant_apply (a : E) {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (constant (T := T) a).val x = a :=
  ofSmooth_apply contDiffOn_const hx

/-- The direction may depend smoothly on time, label and phase. -/
def derivativeAlong (hT : 0 < T) (D : HierarchySmoothProfile T HierarchyProfilePoint) :
    HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T E :=
  (applyField.flip D).comp (derivative hT)

theorem derivativeAlong_apply (hT : 0 < T) (D : HierarchySmoothProfile T HierarchyProfilePoint)
    (f : HierarchySmoothProfile T E) {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (derivativeAlong hT D f).val x = fderivWithin ℝ f.val (hierarchyProfileSlab T) x (D.val x) := by
  change (applyField (derivative hT f) D).val x = _
  rw [applyField_eval _ _ hx, derivative_apply hT f hx]

/-- A linear field of directions gives the actual bilinear advection on profiles. -/
def advect (hT : 0 < T)
    (D : HierarchySmoothProfile T F →ₗ[ℝ] HierarchySmoothProfile T HierarchyProfilePoint) :
    HierarchySmoothProfile T F →ₗ[ℝ] HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T E :=
  ((applyField.comp (derivative hT)).flip).comp D

theorem advect_apply (hT : 0 < T)
    (D : HierarchySmoothProfile T F →ₗ[ℝ] HierarchySmoothProfile T HierarchyProfilePoint)
    (a : HierarchySmoothProfile T F) (f : HierarchySmoothProfile T E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (advect hT D a f).val x = fderivWithin ℝ f.val (hierarchyProfileSlab T) x ((D a).val x) :=
  derivativeAlong_apply hT (D a) f hx

end HierarchySmoothProfile

end SmoothProfiles

end

end TorusEuler
