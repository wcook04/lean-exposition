/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineTest
import PCP.Algebraic.FiniteDistance
import Mathlib.Data.Finset.Max

/-!
# Degree-zero point-versus-line soundness in every finite dimension

For a degree-zero lines table the answer at `(u,v)` is a constant. Compare
the two points with parameters `t` and `t+1` against that same constant.
Translation by one preserves the uniform parameter, while, for fixed `t`,
the two points are independent uniform points as `(u,v)` varies. The triangle
inequality therefore bounds independent-pair disagreement by twice rejection.
Some constant word is at least as close as this average pair disagreement.

This proves `PointLineSoundness F m 0 δ₀` without a field-size or small-error
assumption. It is an elementary boundary case; the positive-degree multivariate
ALMSS theorem is `pointLineSoundness_largeField` in `PointLineSoundness`. The proof
includes characteristic two, zero directions, and zero-dimensional domains, and
keeps the original tester's whole-field sampling.
-/

namespace PCP.Algebraic.PointLineTest

open Finset PolynomialLine

section ConstantApproximation

variable {V A : Type*} [Fintype V] [Nonempty V] [DecidableEq A]

/-- The discrepancy between two independently sampled values of one word. -/
def pairDisagreement (f : V → A) : ℚ :=
  relativeDistance (fun p : V × V => f p.1) (fun p => f p.2)

/-- Some constant word has error at most the mean discrepancy of two independent values. -/
theorem exists_constant_close (f : V → A) :
    ∃ a : A, relativeDistance f (fun _ => a) ≤ pairDisagreement f := by
  classical
  let e : V → ℚ := fun x => relativeDistance f (fun _ => f x)
  obtain ⟨x, _, hx⟩ := (univ : Finset V).exists_min_image e univ_nonempty
  refine ⟨f x, ?_⟩
  have havg : pairDisagreement f = (∑ y, e y) / Fintype.card V := by
    rw [pairDisagreement, relativeDistance_prod]
    congr 1
    apply sum_congr rfl
    intro y _
    exact relativeDistance_comm _ _
  rw [havg]
  have hc : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hc).mpr
  calc
    _ = ∑ _y : V, e x := by simp [e, mul_comm]
    _ ≤ _ := sum_le_sum (fun y hy => hx y hy)

end ConstantApproximation

section ConsecutiveParameters

variable {F σ : Type*} [Field F]

/-- Consecutive parameters send a uniform ordered center/direction pair to two uniform points. -/
def consecutivePointsEquiv (t : F) : ((σ → F) × (σ → F)) ≃ ((σ → F) × (σ → F)) where
  toFun uv := (point uv.1 uv.2 t, point uv.1 uv.2 (t + 1))
  invFun xy := (xy.1 - t • (xy.2 - xy.1), xy.2 - xy.1)
  left_inv uv := by
    apply Prod.ext <;> funext i <;> simp only [point_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring
  right_inv xy := by
    apply Prod.ext <;> funext i <;> simp only [point_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring

/-- Keep the sampled parameter while changing the center and direction into its two endpoints. -/
def consecutiveSamplesEquiv : (((σ → F) × (σ → F)) × F) ≃
    (((σ → F) × (σ → F)) × F) where
  toFun s := (consecutivePointsEquiv s.2 s.1, s.2)
  invFun s := ((consecutivePointsEquiv s.2).symm s.1, s.2)
  left_inv s := Prod.ext ((consecutivePointsEquiv s.2).symm_apply_apply s.1) rfl
  right_inv s := Prod.ext ((consecutivePointsEquiv s.2).apply_symm_apply s.1) rfl

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- The two consecutive observations have exactly the global independent-pair discrepancy. -/
theorem consecutive_distance_eq_pairDisagreement {A : Type*} [DecidableEq A]
    (f : (σ → F) → A) :
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
      (fun s => f (point s.1.1 s.1.2 (s.2 + 1))) = pairDisagreement f := by
  have h := relativeDistance_comp_equiv (consecutiveSamplesEquiv (F := F) (σ := σ))
    (fun s : ((σ → F) × (σ → F)) × F => f s.1.1) (fun s => f s.1.2)
  change relativeDistance _ _ =
    relativeDistance (fun s : ((σ → F) × (σ → F)) × F => f s.1.1)
      (fun s => f s.1.2) at h
  exact h.trans (relativeDistance_comp_fst (κ := F)
    (fun p : (σ → F) × (σ → F) => f p.1) (fun p => f p.2))

/-- A uniform parameter shifted by one has the same error against any constant line table. -/
theorem consecutive_error_eq {A : Type*} [DecidableEq A]
    (f : (σ → F) → A) (b : ((σ → F) × (σ → F)) → A) :
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 (s.2 + 1)))
      (fun s => b s.1) =
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
      (fun s => b s.1) := by
  exact relativeDistance_comp_equiv
    ((Equiv.refl ((σ → F) × (σ → F))).prodCongr (Equiv.addRight (1 : F)))
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
    (fun s => b s.1)

/-- A constant lines table controls the global discrepancy of independently sampled values. -/
theorem pairDisagreement_le_twice_lineError {A : Type*} [DecidableEq A]
    (f : (σ → F) → A) (b : ((σ → F) × (σ → F)) → A) :
    pairDisagreement f ≤ 2 * relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
      (fun s => b s.1) := by
  have h := relativeDistance_triangle
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
    (fun s => b s.1) (fun s => f (point s.1.1 s.1.2 (s.2 + 1)))
  rw [consecutive_distance_eq_pairDisagreement,
    relativeDistance_comm (fun s : ((σ → F) × (σ → F)) × F => b s.1),
    consecutive_error_eq] at h
  simpa only [two_mul] using h

end ConsecutiveParameters

section DegreeZero

variable {F σ : Type*} [Field F]

/-- Degree-zero table entries have the same value at every parameter. -/
theorem eval_degree_zero_table (table : LineTable F σ 0)
    (uv : (σ → F) × (σ → F)) (t : F) :
    (table uv).val.eval t = (table uv).val.coeff 0 := by
  have h := Polynomial.eq_C_of_natDegree_le_zero (table uv).property
  conv_lhs => rw [h]
  exact Polynomial.eval_C

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- The original all-parameter tester controls pair discrepancy when its table has degree zero. -/
theorem pairDisagreement_le_twice_rejectionRate_degree_zero
    (f : (σ → F) → F) (table : LineTable F σ 0) :
    pairDisagreement f ≤ 2 * rejectionRate f table := by
  rw [rejectionRate_eq_relativeDistance]
  simpa only [eval_degree_zero_table] using
    pairDisagreement_le_twice_lineError f (fun uv => (table uv).val.coeff 0)

/-- In every dimension, an arbitrary degree-zero table yields a nearby constant function. -/
theorem exists_constant_close_degree_zero (f : (σ → F) → F)
    (table : LineTable F σ 0) :
    ∃ a : F, relativeDistance f (fun _ => a) ≤ 2 * rejectionRate f table := by
  obtain ⟨a, ha⟩ := exists_constant_close f
  exact ⟨a, ha.trans (pairDisagreement_le_twice_rejectionRate_degree_zero f table)⟩

/-- The nearby function is represented by an actual formal polynomial of total degree zero. -/
theorem exists_close_degree_zero (f : (σ → F) → F) (table : LineTable F σ 0) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ 0 ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * rejectionRate f table := by
  obtain ⟨a, ha⟩ := exists_constant_close_degree_zero f table
  exact ⟨MvPolynomial.C a, by simp, by simpa only [MvPolynomial.eval_C] using ha⟩

/-- Unconditional degree-zero soundness, for arbitrary finite dimension and threshold. -/
theorem pointLineSoundness_degree_zero (m : ℕ) (δ₀ : ℚ) : PointLineSoundness F m 0 δ₀ := by
  intro f table δ _ _ hrej
  obtain ⟨P, hP, hclose⟩ := exists_close_degree_zero f table
  exact ⟨P, hP, hclose.trans (mul_le_mul_of_nonneg_left hrej (by norm_num))⟩

end DegreeZero

end PCP.Algebraic.PointLineTest
