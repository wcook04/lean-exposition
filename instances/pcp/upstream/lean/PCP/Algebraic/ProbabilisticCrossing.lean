/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateCrossingSoundness
import PCP.Algebraic.BivariateCleanRectangle

/-!
# Crossing consistency from four mean error bounds

The deterministic bivariate crossing theorem applies outside four exceptional
events. Markov's inequality bounds each event using its actual mean error.
The sampled grids and crossing coordinates may be correlated arbitrarily.
This is the probability assembly used in the random-plane consistency argument;
the means are explicit inputs here and are proved separately by affine sampling.
-/

namespace PCP.Algebraic.ProbabilisticCrossing

open Finset PointLineTest AffineLineSampling PointedLineSampling
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two global approximation errors and two transverse errors at a crossing. -/
noncomputable def errors (d : ℕ) (f : F × F → F) (x y : F) : Fin 4 → ℚ :=
  ![relativeDistance f (fun z =>
      (bestApproximation d (fun t => f (z.1, t))).val.eval z.2),
    relativeDistance f (fun z =>
      (bestApproximation d (fun t => f (t, z.2))).val.eval z.1),
    relativeDistance (fun t => f (x, t)) (fun t =>
      (bestApproximation d (fun s => f (s, t))).val.eval x),
    relativeDistance (fun t => f (t, y)) (fun t =>
      (bestApproximation d (fun s => f (t, s))).val.eval y)]

theorem errors_nonneg (d : ℕ) (f : F × F → F) (x y : F) (j : Fin 4) :
    0 ≤ errors d f x y j := by
  fin_cases j <;> exact relativeDistance_nonneg _ _

/-- Four bounded means control the probability that the nearest row and column
polynomials give different predictions at the sampled crossing. -/
theorem fraction_disagreement_le {S : Type*} [Fintype S] {d : ℕ}
    (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f : S → F × F → F) (x y : S → F) {ε β : ℚ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2)
    (hmean : ∀ j, (𝔼 s, errors d (f s) (x s) (y s) j) ≤ β) :
    fraction (fun s =>
      (bestApproximation d (fun t => f s (x s, t))).val.eval (y s) ≠
        (bestApproximation d (fun t => f s (t, y s))).val.eval (x s)) ≤
      4 * β / ε := by
  classical
  let E : Fin 4 → S → Prop := fun j s => ε ≤ errors d (f s) (x s) (y s) j
  have hbad : ∀ s,
      (bestApproximation d (fun t => f s (x s, t))).val.eval (y s) ≠
        (bestApproximation d (fun t => f s (t, y s))).val.eval (x s) →
      ∃ j ∈ (univ : Finset (Fin 4)), E j s := by
    intro s hs
    by_contra hn
    have hall (j : Fin 4) : errors d (f s) (x s) (y s) j ≤ ε := by
      have h : ¬ E j s := fun hj => hn ⟨j, mem_univ j, hj⟩
      exact (lt_of_not_ge h).le
    apply hs
    exact BivariateCrossingSoundness.crossing_bestApproximation_eq hd hq (f s)
      (x s) (y s) hεsmall (hall 0) (hall 1) (hall 2) (hall 3) (by linarith)
  have hmarkov (j : Fin 4) : fraction (E j) ≤ β / ε := by
    apply (fraction_ge_le (fun s => errors d (f s) (x s) (y s) j)
      (fun s => errors_nonneg d (f s) (x s) (y s) j) ε hε).trans
    exact div_le_div_of_nonneg_right (hmean j) hε.le
  calc
    _ ≤ fraction (fun s => ∃ j ∈ (univ : Finset (Fin 4)), E j s) :=
      fraction_mono _ _ hbad
    _ ≤ ∑ j : Fin 4, fraction (E j) :=
      BivariateCleanRectangle.fraction_exists_mem_le univ E
    _ ≤ ∑ _j : Fin 4, β / ε := sum_le_sum (fun j _ => hmarkov j)
    _ = _ := by simp; ring

end PCP.Algebraic.ProbabilisticCrossing
