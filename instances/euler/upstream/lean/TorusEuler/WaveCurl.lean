import TorusEuler.AffineWave
import TorusEuler.CurlProjection
import TorusEuler.Statement
import Mathlib.Tactic.FinCases

open scoped InnerProductSpace

namespace TorusEuler

theorem curlOfDerivative_smul (c : ℝ) (D : Vec3 →L[ℝ] Vec3) :
    curlOfDerivative (c • D) = c • curlOfDerivative D := by
  ext i
  fin_cases i <;> simp [curlOfDerivative, mul_sub]

/-- The spatial curl of the affine plane-wave perturbation in §2.1. -/
theorem curl_planeWave (F : ℝ → ℝ) (a k x : Vec3) (dF : ℝ)
    (hF : HasDerivAt F dF ⟪k, x⟫_ℝ) :
    curl (fun y => F ⟪k, y⟫_ℝ • a) x = dF • cross3 k a := by
  rw [curl, (hasFDerivAt_planeWave F a k x dF hF).fderiv]
  have h : ((dF • innerSL ℝ k).smulRight a) = dF • (innerSL ℝ k).smulRight a := by
    ext y
    simp [smul_smul]
  rw [h, curlOfDerivative_smul]
  exact congrArg (dF • ·) (coordinateCurl_rankOne a k)

end TorusEuler
