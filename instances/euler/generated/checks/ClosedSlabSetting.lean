import TorusEuler.Paper.Spine
import TorusEuler.Paper.Proofs.S678b.Library.Limit

/-!
# The full closed-slab conclusion in the opening of Section 8

REVIEW CANDIDATE — UNCOMPILED in this return environment.
Target: Lean v4.34.0-rc2 and the authors' pinned Mathlib at
fd3a1588967810b9abe42a1dcf46ee662d6434e2.

This file adds a reader-facing statement; it changes no author file and makes
no claim that the citation frontier of the original section8_setting node has
changed. The short proof uses Proposition 8.1 to satisfy the additional premise
of the already released closedSlab_velocity_limit library theorem. That premise
is used there only to identify the closed-slab limit with the Euler solution.

From the authors' built `lean/` directory, keeping this file outside their
package, run (replace the absolute path prefix):
    lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true /absolute/path/to/return_euler_r2_f7/lean/ClosedSlabSetting.lean
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace ReviewF7

open TorusEuler TorusEuler.Paper

/-- Every construction admitted by Section 8 has the continuous uniform
velocity limit asserted by the opening paragraph, including the terminal time.
The statement also records agreement with the smooth Euler solution before it. -/
theorem closedSlabLimit_of_theorem71
    {P : InductiveEulerParameters} {c : InductiveEulerConstruction P} {C T : ℝ}
    (h71 : Theorem71Conclusions c C T) :
    ∃ (u : Velocity) (p : Pressure) (w : Velocity),
      Proposition81Conclusions c T u p ∧
      ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (c.stages.velocity n))
        (Function.uncurry w) atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Ico 0 T, u t = w t := by
  obtain ⟨u, p, h81⟩ := TorusEuler.Paper.proposition_8_1 P c C T h71
  obtain ⟨w, hw, hU, hagree⟩ :=
    TorusEuler.Paper.Lib.S678b.closedSlab_velocity_limit h71 h81
  exact ⟨u, p, w, h81, hw, hU, hagree⟩

/-- The original setting plus the continuous uniform limit in the full
Section 8 opening paragraph (arxiv_flat.tex:4241–4246). -/
def ClosedSlabSetting : Prop :=
  ∃ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (C T : ℝ)
    (w : Velocity),
      Theorem71Conclusions c C T ∧
      ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (c.stages.velocity n))
        (Function.uncurry w) atTop (Icc 0 T ×ˢ (univ : Set Vec3))

theorem closedSlabSetting_of (h : Statement.Text.section8_setting) : ClosedSlabSetting := by
  obtain ⟨P, c, C, T, h71⟩ := h
  obtain ⟨_, _, w, _, hw, hU, _⟩ := closedSlabLimit_of_theorem71 h71
  exact ⟨P, c, C, T, w, h71, hw, hU⟩

theorem closedSlabSetting : ClosedSlabSetting :=
  closedSlabSetting_of TorusEuler.Paper.Text.section8_setting

end ReviewF7
