import TorusEuler.Paper.Spine
import TorusEuler.Paper.Proofs.S5Bridge.Operators

/-!
# An explicit existence clause for Lemma 5.3(ii)

UNCOMPILED: this return environment has no Lean or Lake executable.
Target: authors' fd3a1588967810b9abe42a1dcf46ee662d6434e2,
Lean v4.34.0-rc2 and the pinned Mathlib in their lake-manifest.json.

The paper refers to "the solution" of the transverse equation.  Its one-to-one
statement supplies the estimate for every solution.  This supplement records
existence and uniqueness in that same profile space using the authors' existing
solver and uniqueness theorem.  It makes no claim to extend Lemma 5.3(i) from
whole-slab profiles to arbitrary fields given only on [t₀,T].
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TorusEuler.Paper.Fidelity

open HierarchyTwistedProfile

/-- Each zero-phase-mean source has exactly one normalized transverse solution. -/
theorem transverseSolution_existsUnique
    {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
    (d : ParentGeometry hT U X k) (f : HierarchyTwistedProfile T k Vec3)
    (hf : (S5.ops d).average f = 0) :
    ∃! z : HierarchyTwistedProfile T k Vec3 × HierarchyTwistedProfile T k ℝ,
      S5.TransverseSolution d f z.1 z.2 := by
  obtain ⟨V, q, hsol⟩ := Bridge.transverseSolvable d f hf
  refine ⟨(V, q), hsol, ?_⟩
  rintro ⟨V', q'⟩ hsol'
  obtain ⟨hV, hq⟩ := Bridge.TransverseSolution.unique d hsol' hsol
  exact Prod.ext hV hq

/-- Lemma 5.3, accompanied by explicit existence and uniqueness for its
transverse solves. All estimates and their quantifier order remain those of
the authors' statement. -/
theorem lemma_5_3_with_unique_transverse_solution :
    Statement.lemma_5_3 ∧
      ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
        (d : ParentGeometry hT U X k) (f : HierarchyTwistedProfile T k Vec3),
        (S5.ops d).average f = 0 →
          ∃! z : HierarchyTwistedProfile T k Vec3 × HierarchyTwistedProfile T k ℝ,
            S5.TransverseSolution d f z.1 z.2 := by
  refine ⟨TorusEuler.Paper.lemma_5_3, ?_⟩
  intro T hT U X k d f hf
  exact transverseSolution_existsUnique hT d f hf

end TorusEuler.Paper.Fidelity
