/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.CandidateCrossingProbability
import PCP.Algebraic.RuledSurfaceSampling
import PCP.Algebraic.PolynomialLineCharacterization

/-!
# Polynomial rigidity from endpoint prediction bounds

The modified ruled surface forces one fixed nearest polynomial on each target
line to agree with the target function at every parameter. The proof uses
actual finite sampling estimates and arbitrary candidate row polynomials;
changing the surface's zero column is never claimed to preserve a decoder.

Global proximity, endpoint prediction, whole-test rejection, and fixed-parameter
rejection bounds are explicit inputs. No polynomial existence or line soundness
is assumed. The resulting exact low-degree lines give an actual multivariate
polynomial by the proved total-degree characterization.
-/

namespace PCP.Algebraic.RuledSurface

open Finset PolynomialLine PointLineTest AffineLineSampling
open scoped BigOperators

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {d : ℕ}

/-- At every target-line parameter, its one fixed nearest polynomial agrees
with `g`, under the explicitly stated quantitative prediction bounds. -/
theorem bestApproximation_eval_eq_of_endpoint_bounds
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f g : (σ → F) → F) (T : LineTable F σ d) {η γ δ ℓ ε : ℚ}
    (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (hwhole : rejectionRate f T ≤ δ)
    (hfixed : ∀ t, relativeDistance (fun uv : Seed F σ => f (point uv.1 uv.2 t))
      (fun uv => (T uv).val.eval t) ≤ ℓ)
    (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (hbudget : (2 * (γ + η) + δ + ℓ + γ + 2 / Fintype.card F) / ε + γ < 1)
    (x h : σ → F) (y : F) :
    (bestApproximation d (fun t => g (point x h t))).val.eval y = g (point x h y) := by
  let β : Fin 5 → ℚ :=
    ![γ + η, δ + 1 / Fintype.card F, ℓ + 1 / Fintype.card F, γ, γ + η]
  have hmean (j : Fin 5) :
      (𝔼 s : Seed F σ,
        CandidateCrossing.errors (surface f g x h s) (rows T x h s) (columns g T x h s)
          y 0 j) ≤ β j := by
    fin_cases j
    · exact expect_global_row_error_le f g T hnear hendpoint x h
    · exact expect_global_column_error_le f g T hwhole x h
    · exact expect_local_row_error_le f g T hfixed x h y
    · exact expect_local_column_error_le f g T hendpoint x h
    · exact expect_own_row_error_le f g T hnear hendpoint x h y
  have hsum : (∑ j, β j) = 2 * (γ + η) + δ + ℓ + γ + 2 / Fintype.card F := by
    simp [β, Fin.sum_univ_succ]
    ring
  apply CandidateCrossing.value_eq_of_mean_errors hd hq
    (surface f g x h) (rows T x h) (columns g T x h)
    (rows_degree T x h) (columns_degree g T x h) y 0 hεpos hε
    (fun s p hp => ?_) hsmall β hmean (g (point x h y))
    ((bestApproximation d (fun t => g (point x h t))).val.eval y)
    (fun _ => by simp) (endpoint_error_le g T hendpoint x h y) (by rwa [hsum])
  simpa only [surface_zero, columns_zero] using bestApproximation_min d
    (fun t => g (point x h t)) p hp

/-- Quantitative endpoint predictions force genuine degree-`d` polynomials on
every affine line. All parameters are handled on the same target-line polynomial. -/
theorem hasLowDegreeLines_of_endpoint_bounds
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f g : (σ → F) → F) (T : LineTable F σ d) {η γ δ ℓ ε : ℚ}
    (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (hwhole : rejectionRate f T ≤ δ)
    (hfixed : ∀ t, relativeDistance (fun uv : Seed F σ => f (point uv.1 uv.2 t))
      (fun uv => (T uv).val.eval t) ≤ ℓ)
    (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (hbudget : (2 * (γ + η) + δ + ℓ + γ + 2 / Fintype.card F) / ε + γ < 1) :
    HasLowDegreeLines d g := by
  intro x h
  refine ⟨(bestApproximation d (fun t => g (point x h t))).val,
    (bestApproximation d _).property, ?_⟩
  exact bestApproximation_eval_eq_of_endpoint_bounds hd hq f g T hnear hendpoint hwhole
    hfixed hεpos hε hsmall hbudget x h

/-- The endpoint bounds construct a multivariate polynomial of ordinary total
degree at most `d`, rather than only separately low-degree coordinate slices. -/
theorem exists_polynomial_of_endpoint_bounds
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f g : (σ → F) → F) (T : LineTable F σ d) {η γ δ ℓ ε : ℚ}
    (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (hwhole : rejectionRate f T ≤ δ)
    (hfixed : ∀ t, relativeDistance (fun uv : Seed F σ => f (point uv.1 uv.2 t))
      (fun uv => (T uv).val.eval t) ≤ ℓ)
    (hεpos : 0 < ε) (hε : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (hbudget : (2 * (γ + η) + δ + ℓ + γ + 2 / Fintype.card F) / ε + γ < 1) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧ ∀ x, MvPolynomial.eval x P = g x := by
  apply exists_polynomial_of_hasLowDegreeLines_finite g
    (BivariateAgreement.fieldSize_bounds hd hq).2.1
  exact hasLowDegreeLines_of_endpoint_bounds hd hq f g T hnear hendpoint hwhole hfixed
    hεpos hε hsmall hbudget

end PCP.Algebraic.RuledSurface
