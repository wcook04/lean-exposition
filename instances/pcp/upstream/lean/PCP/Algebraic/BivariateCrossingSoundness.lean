/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateAgreement
import PCP.Algebraic.PointLineCrossing

/-!
# Bivariate crossing consistency with the agreement premise discharged

The numerical crossing conclusion of ALMSS Corollary 70 follows from global
row/column approximation bounds and the two local crossing error bounds.
`BivariateAgreement` constructs the nearby bivariate polynomial needed by the
deterministic crossing argument. No comparison polynomial, clean rectangle,
error-locator certificate, or unproved agreement theorem is an input here.

The explicit sufficient constants are `d > 0`, `|F| ≥ 1000*d^3` and global
error `ε ≤ 1/100`, together with `5ε + ε' + 2d/|F| < 1/2` at the crossing.
Nearest polynomials are the actual classical choices from `PointLineTest`;
their ties do not require a coherent choice across slices.
-/

namespace PCP.Algebraic.BivariateCrossingSoundness

open PointLineTest

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- Nearest row and column polynomials agree at a crossing with sufficiently
small local errors, under the proved bivariate agreement theorem's hypotheses. -/
theorem crossing_bestApproximation_eq (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F) (f : F × F → F)
    (x₀ y₀ : F) {ε ε' : ℚ} (hε : ε ≤ 1 / 100)
    (hrows : relativeDistance f (fun z =>
      (bestApproximation d (fun y => f (z.1, y))).val.eval z.2) ≤ ε)
    (hcols : relativeDistance f (fun z =>
      (bestApproximation d (fun x => f (x, z.2))).val.eval z.1) ≤ ε)
    (hlrow : relativeDistance (fun y => f (x₀, y)) (fun y =>
      (bestApproximation d (fun x => f (x, y))).val.eval x₀) ≤ ε')
    (hlcol : relativeDistance (fun x => f (x, y₀)) (fun x =>
      (bestApproximation d (fun y => f (x, y))).val.eval y₀) ≤ ε')
    (hsmall : 5 * ε + ε' + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2) :
    (bestApproximation d (fun y => f (x₀, y))).val.eval y₀ =
      (bestApproximation d (fun x => f (x, y₀))).val.eval x₀ := by
  obtain ⟨P, hP, hnear⟩ := BivariateAgreement.exists_polynomial_of_row_column_agreement
    hd hq f
    (fun y => (bestApproximation d (fun x => f (x, y))).val)
    (fun x => (bestApproximation d (fun y => f (x, y))).val)
    (fun y => (bestApproximation d (fun x => f (x, y))).property)
    (fun x => (bestApproximation d (fun y => f (x, y))).property)
    hcols hrows hε
  exact PointLineCrossing.crossing_bestApproximation_eq_of_nearby_polynomial
    f P hP x₀ y₀ hrows hcols hnear hlrow hlcol hsmall

end PCP.Algebraic.BivariateCrossingSoundness
