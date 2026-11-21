/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

Adapted from `CCPoint.Exact.hasFDerivAt_layerField` in
`sources/ccpoint-lean/CCPoint/Exact/Layer.lean`.
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace TorusEuler

/-- The spatial derivative used in the affine plane-wave calculation of Lemma 2.1. -/
theorem hasFDerivAt_planeWave (F : ℝ → ℝ) (a k x : EuclideanSpace ℝ (Fin 3))
    (dF : ℝ) (hF : HasDerivAt F dF ⟪k, x⟫_ℝ) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => F ⟪k, y⟫_ℝ • a)
      ((dF • innerSL ℝ k).smulRight a) x := by
  have hInner : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => ⟪k, y⟫_ℝ)
      (innerSL ℝ k) x :=
    (innerSL ℝ k).hasFDerivAt
  exact (hF.comp_hasFDerivAt x hInner).smul_const a

end TorusEuler
