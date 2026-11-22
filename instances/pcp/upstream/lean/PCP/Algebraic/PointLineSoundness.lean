/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineEndpointConsistency
import PCP.Algebraic.PointLineConstants
import PCP.Algebraic.RuledSurfaceRigidity
import PCP.Algebraic.PointLineConstant

/-!
# Point-versus-line soundness in arbitrary dimension

For `|F| ≥ 1000000*d^3`, rejection at most `1/4000000` implies distance at most
twice rejection from an actual polynomial of ordinary total degree at most `d`.
The constants are absolute. The proof constructs the corrected function, proves
its endpoint consistency, uses ruled surfaces to prove exact low-degree lines,
and applies the total-degree characterization. Degree zero is covered separately.

This discharges the project's `PointLineSoundness` proposition, implementing the
mathematical guarantee of ALMSS Theorem 45 with explicit sufficient constants.
No soundness, agreement, or polynomial-existence premise remains.
-/

namespace PCP.Algebraic.PointLineTest

open PolynomialLine AffineLineSampling PointLineConstants

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {d : ℕ}

/-- With small rejection, the actual all-parameter correction is an ordinary
total-degree-bounded polynomial in every finite dimension. -/
theorem exists_polynomial_correction (hd : 0 < d)
    (hq : fieldFactor * d ^ 3 ≤ Fintype.card F) (f : (σ → F) → F)
    (hδ : rejectionRate f (decodedTable d f) ≤ smallError) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧
      ∀ x, MvPolynomial.eval x P = correction (decodedTable d f) x := by
  obtain ⟨hbig, h3, _, hlarge, hsmall⟩ := field_bounds hd hq
  apply RuledSurface.exists_polynomial_of_endpoint_bounds hd hbig f
    (correction (decodedTable d f)) (decodedTable d f)
    (η := 2 * rejectionRate f (decodedTable d f))
    (γ := endpointError (rejectionRate f (decodedTable d f)) (Fintype.card F))
    (δ := rejectionRate f (decodedTable d f))
    (ℓ := 4 * rejectionRate f (decodedTable d f)) (ε := agreementError)
    (distance_correction_le f _) ?_ le_rfl ?_
    (by norm_num [agreementError]) (by norm_num [agreementError]) hsmall
    (rigidity_budget hlarge hδ)
  · intro u t
    rw [fraction_ne_eq_relativeDistance]
    exact PointLineEndpointConsistency.endpoint_error_le hd hbig f u t
      (by norm_num [agreementError]) (by norm_num [agreementError]) hsmall
  · intro t
    exact rejectionAt_le_four_mul d f t h3

/-- General point-versus-line soundness with explicit absolute constants,
including degree zero and zero-dimensional spaces. -/
theorem exists_close_of_small_rejection
    (hq : fieldFactor * d ^ 3 ≤ Fintype.card F) (f : (σ → F) → F)
    (table : LineTable F σ d) (hδ : rejectionRate f table ≤ smallError) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * rejectionRate f table := by
  by_cases hd : d = 0
  · subst d
    exact exists_close_degree_zero f table
  · obtain ⟨P, hP, heval⟩ := exists_polynomial_correction (Nat.pos_of_ne_zero hd) hq f
      ((rejectionRate_decodedTable_le d f table).trans hδ)
    refine ⟨P, hP, ?_⟩
    simpa only [heval] using distance_decoded_correction_le f table

end PCP.Algebraic.PointLineTest

namespace PCP.Algebraic

open PointLineConstants

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The formerly open point-versus-line proposition, now proved in every dimension. -/
theorem pointLineSoundness_largeField (m c : ℕ)
    (hq : fieldFactor * c ^ 3 ≤ Fintype.card F) : PointLineSoundness F m c smallError := by
  intro f table δ _ hδ hrej
  obtain ⟨P, hP, hclose⟩ := PointLineTest.exists_close_of_small_rejection hq f table
    (hrej.trans hδ)
  exact ⟨P, hP, hclose.trans (mul_le_mul_of_nonneg_left hrej (by norm_num))⟩

end PCP.Algebraic
