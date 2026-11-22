/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLowDegreeTest
import PCP.Algebraic.HadamardRowDecoding
import PCP.Algebraic.BinaryEncodingDistance

/-!
# Rejection bounds for the two branches of the binary low-degree test

Each branch's rejection probability is at most twice that of the combined test.
The generator constraint's soundness is supplied by `GeneratorLowDegreeTest`.
-/

namespace PCP.Algebraic.BinaryLowDegreeTest

open BinaryPolynomialSpace Hadamard

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F]
variable [Fintype F] [Fintype σ] [DecidableEq σ]
variable {c t r : ℕ}

/-- Each branch's rejection is at most twice the combined rejection. -/
theorem branch_rejectionRates_le_twice (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : Fin (c + 1) → F)
    (H : (σ → F) → Coefficients t r → ZMod 2) :
    averageRejectionRate hr H ≤ 2 * rejectionRate hr ρ a H ∧
      BinaryLagrangeConstraint.rejectionRate hr ρ a H ≤ 2 * rejectionRate hr ρ a H := by
  have havg := rejectionRate_eq_average hr ρ a H
  change rejectionRate hr ρ a H =
    (averageRejectionRate hr H + BinaryLagrangeConstraint.rejectionRate hr ρ a H) / 2 at havg
  have hη := averageRejectionRate_nonneg hr H
  have hβ : 0 ≤ BinaryLagrangeConstraint.rejectionRate hr ρ a H :=
    relativeDistance_nonneg _ _
  constructor <;> linarith

end PCP.Algebraic.BinaryLowDegreeTest
