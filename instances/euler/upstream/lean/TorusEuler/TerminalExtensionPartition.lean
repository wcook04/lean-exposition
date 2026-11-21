import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Smooth gluing of local extensions on open subsets of finite-dimensional spaces. -/

noncomputable section

open Filter Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TorusEuler

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth local extension near every point of an open set gives a single smooth
extension there. The restrictions on the agreement set are affine, so a smooth
partition of unity preserves them. -/
theorem exists_contDiffOn_extension_of_local {D A : Set E} {f : E → F}
    (hD : IsOpen D)
    (hlocal : ∀ x ∈ D, ∃ (W : Set E) (g : E → F), IsOpen W ∧ x ∈ W ∧
      ContDiffOn ℝ ∞ g W ∧ EqOn g f (A ∩ W)) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g D ∧ EqOn g f (A ∩ D) := by
  classical
  let U : Opens E := ⟨D, hD⟩
  let : LocallyCompactSpace U := hD.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let target (x : U) : Set F := if (x : E) ∈ A then {f x} else univ
  have htarget : ∀ x, Convex ℝ (target x) := by
    intro x
    by_cases hx : (x : E) ∈ A
    · simp [target, hx, convex_singleton]
    · simp [target, hx, convex_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
      (I := 𝓘(ℝ, E)) (n := ⊤) htarget (by
    intro x
    rcases hlocal x x.2 with ⟨W, g, hW, hxW, hg, heq⟩
    refine ⟨Subtype.val ⁻¹' W, ?_, fun y => g y, ?_, ?_⟩
    · exact (hW.preimage continuous_subtype_val).mem_nhds hxW
    · intro y hy
      apply ContMDiffAt.contMDiffWithinAt
      apply contMDiffAt_subtype_iff.mpr
      exact (hg y hy).contDiffAt (hW.mem_nhds hy) |>.contMDiffAt
    · intro y hy
      by_cases hyA : (y : E) ∈ A
      · simpa [target, hyA] using heq ⟨hyA, hy⟩
      · simp [target, hyA])
  let G : E → F := Subtype.val.extend g 0
  have hG (x : U) : G x = g x := Subtype.val_injective.extend_apply _ _ _
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    let x' : U := ⟨x, hx⟩
    apply ContDiffAt.contDiffWithinAt
    apply ContMDiffAt.contDiffAt
    apply (contMDiffAt_subtype_iff (x := x')).mp
    have hEq : (fun z : U => G z) = (fun z : U => g z) := funext hG
    rw [hEq]
    exact g.contMDiff.contMDiffAt
  · intro x hx
    let x' : U := ⟨x, hx.2⟩
    change G (x' : E) = f (x' : E)
    rw [hG x']
    simpa [target, hx.1, x'] using hg x'

end TorusEuler
