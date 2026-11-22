/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineCorrection
import PCP.Algebraic.PointedLineSampling

/-!
# Plurality consistency from independent predictions

The finite majority step in the ALMSS correction argument. Plurality minimizes
error against constant words, so its error is at most the disagreement between
two independent predictions. More generally, comparison with another prediction
distribution controls both the plurality error and disagreement with its value.

The point-versus-line specialization uses the actual seeds `(v,t)` from
`PointLineTest.correction`. It requires neither coherent choices of nearest
polynomials nor covariance under affine reparametrization. Bounds on collisions
remain explicit inputs; no line soundness or polynomial existence is assumed.
-/

namespace PCP.Algebraic

open Finset
open scoped BigOperators

namespace Plurality

variable {R S A : Type*} [Fintype R] [Fintype S]
variable [Finite A] [Nonempty A] [DecidableEq A]

/-- The error of a plurality is at most disagreement with any independently
sampled prediction distribution. The comparison seed must be nonempty. -/
theorem error_le_cross_disagreement [Nonempty S] (p : S → A) (q : R → A) :
    relativeDistance q (fun _ => value q) ≤
      relativeDistance (fun sr : S × R => p sr.1) (fun sr => q sr.2) := by
  have hpoint (s : S) : relativeDistance q (fun _ => value q) ≤
      relativeDistance (fun _ : R => p s) q := by
    rw [relativeDistance_comm (fun _ : R => p s) q]
    exact minimizes q (p s)
  have hmean := expect_le_expect (s := univ) (fun s _ => hpoint s)
  rw [Fintype.expect_const, Fintype.expect_eq_sum_div_card] at hmean
  rw [relativeDistance_prod]
  exact hmean

omit [Fintype S] in
/-- Two independent samples of one distribution disagree at least as often as
a sample disagrees with its plurality. This bound has no factor-of-two loss. -/
theorem error_le_pair_disagreement [Nonempty R] (w : R → A) :
    relativeDistance w (fun _ => value w) ≤
      relativeDistance (fun rs : R × R => w rs.1) (fun rs => w rs.2) :=
  error_le_cross_disagreement w w

/-- Independent cross disagreement controls how often the first prediction
misses the second distribution's plurality. This is the factor-two step of
ALMSS Corollary 72, without any assumptions on how ties are resolved. -/
theorem distance_value_le_twice_cross_disagreement [Nonempty R]
    (p : S → A) (q : R → A) :
    relativeDistance p (fun _ => value q) ≤
      2 * relativeDistance (fun sr : S × R => p sr.1) (fun sr => q sr.2) :=
  distance_le_twice_prediction_error (fun _ : S => q) p

/-- Sufficiently small independent cross disagreement forces the two chosen
pluralities to coincide, regardless of their tie-breaking rules. -/
theorem value_eq_of_cross_disagreement_lt_quarter [Nonempty R] [Nonempty S]
    (p : S → A) (q : R → A)
    (h : relativeDistance (fun sr : S × R => p sr.1) (fun sr => q sr.2) < 1 / 4) :
    value p = value q := by
  apply value_eq_of_error_lt_half
  have hdist := distance_value_le_twice_cross_disagreement p q
  linarith

end Plurality

namespace PointLineTest

open AffineLineSampling

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {c : ℕ}

/-- At each fixed point, the error of the actual parameter-averaged correction
is bounded by disagreement between two independent full prediction seeds. -/
theorem prediction_error_correction_le_pair_error (table : LineTable F σ c)
    (x : σ → F) :
    relativeDistance (prediction table x) (fun _ => correction table x) ≤
      relativeDistance
        (fun s : ((σ → F) × F) × ((σ → F) × F) => prediction table x s.1)
        (fun s => prediction table x s.2) :=
  Plurality.error_le_pair_disagreement (prediction table x)

/-- A normalized collision bound transfers directly to pointwise prediction
error against correction, with no loss in its constant. -/
theorem prediction_error_correction_le_of_collision_bound
    (table : LineTable F σ c) (x : σ → F) {η : ℚ}
    (h : fraction (fun s : ((σ → F) × F) × ((σ → F) × F) =>
      prediction table x s.1 ≠ prediction table x s.2) ≤ η) :
    relativeDistance (prediction table x) (fun _ => correction table x) ≤ η := by
  apply (prediction_error_correction_le_pair_error table x).trans
  simpa only [fraction_ne_eq_relativeDistance] using h

/-- A collision bound below one half makes the corrected value a strict
majority of the full `(direction,parameter)` predictions. -/
theorem prediction_error_correction_lt_half_of_collision_bound
    (table : LineTable F σ c) (x : σ → F) {η : ℚ}
    (h : fraction (fun s : ((σ → F) × F) × ((σ → F) × F) =>
      prediction table x s.1 ≠ prediction table x s.2) ≤ η)
    (hη : η < 1 / 2) :
    relativeDistance (prediction table x) (fun _ => correction table x) < 1 / 2 :=
  (prediction_error_correction_le_of_collision_bound table x h).trans_lt hη

end PointLineTest

end PCP.Algebraic
