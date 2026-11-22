/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateAgreement

/-!
# Explicit numerical constants for point-versus-line soundness

The estimates use a deliberately generous cubic field-size factor and a fixed
positive rejection threshold. This module verifies only the numerical bounds;
the probabilistic and algebraic hypotheses are discharged in the soundness assembly.
-/

namespace PCP.Algebraic.PointLineConstants

/-- The sufficient cubic field-size factor. -/
def fieldFactor : ℕ := 1000000

/-- The sufficient upper bound on point-versus-line rejection. -/
def smallError : ℚ := 1 / 4000000

/-- The threshold for applying the bivariate agreement theorem. -/
def agreementError : ℚ := 1 / 100

/-- The endpoint prediction error supplied by mixed-plane consistency. -/
def endpointError (δ : ℚ) (q : ℕ) : ℚ := 8 * (4 * δ + 1 / q) / agreementError

theorem smallError_pos : 0 < smallError := by norm_num [smallError]

theorem field_bounds {d q : ℕ} (hd : 0 < d) (hq : fieldFactor * d ^ 3 ≤ q) :
    1000 * d ^ 3 ≤ q ∧ 3 * d ≤ q ∧ 2 * d < q ∧ 1000000 ≤ q ∧
      6 * agreementError + 2 * ((d : ℚ) / q) < 1 / 2 := by
  have hbig : 1000 * d ^ 3 ≤ q := by
    dsimp [fieldFactor] at hq
    omega
  obtain ⟨_, h2, _, _, h20⟩ := BivariateAgreement.fieldSize_bounds hd hbig
  have hpow : 1 ≤ d ^ 3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hd))
  have hlarge : 1000000 ≤ q := by
    dsimp [fieldFactor] at hq
    nlinarith
  refine ⟨hbig, by omega, h2, hlarge, ?_⟩
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hfrac : (d : ℚ) / q ≤ 1 / 20 := by
    apply (div_le_iff₀ hqpos).mpr
    have h : (20 : ℚ) * d ≤ q := by exact_mod_cast h20
    linarith
  norm_num [agreementError]
  linarith

/-- The outer theorem's field hypothesis implies the weaker inner tester bound,
including degree zero. -/
theorem field_bound_linear {d q : ℕ} (hcard : 1 < q) (hq : fieldFactor * d ^ 3 ≤ q) :
    2 * d < q := by
  by_cases hd : d = 0
  · subst d
    omega
  · exact (field_bounds (Nat.pos_of_ne_zero hd) hq).2.2.1

/-- The combined exceptional-event budget leaves a positive probability of a good ruled surface. -/
theorem rigidity_budget {q : ℕ} (hq : 1000000 ≤ q) {δ : ℚ} (hδ : δ ≤ smallError) :
    (2 * (endpointError δ q + 2 * δ) + δ + 4 * δ + endpointError δ q + 2 / q) /
        agreementError + endpointError δ q < 1 := by
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqcast : (1000000 : ℚ) ≤ q := by exact_mod_cast hq
  have hinv : (1 : ℚ) / q ≤ 1 / 1000000 := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  dsimp [endpointError, agreementError, smallError] at *
  ring_nf at *
  linarith

end PCP.Algebraic.PointLineConstants
