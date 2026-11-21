/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointedLineSampling
import Mathlib.Data.Fintype.EquivFin

/-!
# Selecting good columns from small grid disagreement

The finite selection step preceding the Arora--Safra bivariate agreement
argument. Two grids close to one received word are close to each other on
average. A normalized finite Markov bound then supplies an actual embedding
of the desired number of good columns. Polynomial degree bounds play no role
in this selection.
-/

namespace PCP.Algebraic.BivariateColumnSelection

open Finset AffineLineSampling PointedLineSampling
open scoped BigOperators

section FiniteSelection

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A nonnegative function of mean at most half the threshold has enough good
coordinates to embed any finite set whose doubled size fits in the domain. -/
theorem exists_embedding_of_expect_le_half (X : α → ℚ) (hX : ∀ x, 0 ≤ X x)
    {a : ℚ} (ha : 0 < a) (hmean : (𝔼 x, X x) ≤ a / 2)
    (n : ℕ) (hn : 2 * n ≤ Fintype.card α) :
    ∃ b : Fin n ↪ α, ∀ i, X (b i) ≤ a := by
  classical
  have hbad : fraction (fun x => ¬ X x ≤ a) ≤ 1 / 2 := by
    calc
      _ ≤ fraction (fun x => a ≤ X x) :=
        fraction_mono _ _ (fun x hx => (lt_of_not_ge hx).le)
      _ ≤ (𝔼 x, X x) / a := fraction_ge_le X hX a ha
      _ ≤ 1 / 2 := (div_le_iff₀ ha).mpr (by linarith)
  let good : Finset α := univ.filter (fun x => X x ≤ a)
  let bad : Finset α := univ.filter (fun x => ¬ X x ≤ a)
  have hc : (0 : ℚ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [fraction_eq_card_filter] at hbad
  have hb : (bad.card : ℚ) ≤ (Fintype.card α : ℚ) / 2 := by
    have h := (div_le_iff₀ hc).mp hbad
    dsimp only [bad]
    linarith
  have hpartition : good.card + bad.card = Fintype.card α := by
    simpa only [card_univ] using (card_filter_add_card_filter_not (s := univ) (fun x => X x ≤ a))
  have hpartition' : (good.card : ℚ) + (bad.card : ℚ) = Fintype.card α := by
    exact_mod_cast hpartition
  have hn' : 2 * (n : ℚ) ≤ Fintype.card α := by exact_mod_cast hn
  have hgood : n ≤ good.card := by
    have h : (n : ℚ) ≤ good.card := by linarith
    exact_mod_cast h
  obtain ⟨b, hb⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin n) (by simpa only [Fintype.card_fin] using hgood)
  refine ⟨b, fun i => ?_⟩
  exact (mem_filter.mp (hb (Set.mem_range_self i))).2

end FiniteSelection

section Grids

variable {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq A]

/-- Two approximations to the same grid have small average column disagreement. -/
theorem mean_column_distance_le (f R C : I × J → A) {ε : ℚ}
    (hR : relativeDistance f R ≤ ε) (hC : relativeDistance f C ≤ ε) :
    (𝔼 x, relativeDistance (fun y => R (x, y)) (fun y => C (x, y))) ≤ 2 * ε := by
  rw [Fintype.expect_eq_sum_div_card, ← relativeDistance_prod]
  have h := relativeDistance_triangle R f C
  rw [relativeDistance_comm R f] at h
  linarith

end Grids

section PolynomialGrids

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Here `R y` is a polynomial in the horizontal coordinate, and `C x` is a
polynomial in the vertical coordinate. Their grid discrepancy averages over `x`. -/
theorem mean_column_error_le (f : F × F → F) (R C : F → Polynomial F) {ε : ℚ}
    (hR : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hC : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε) :
    (𝔼 x, relativeDistance (fun y => (R y).eval x) (C x).eval) ≤ 2 * ε :=
  mean_column_distance_le f (fun z => (R z.2).eval z.1)
    (fun z => (C z.1).eval z.2) hR hC

/-- Small global row and column errors provide `10*d` distinct columns, each
with row/column disagreement at most `1/10`. Degree bounds are unnecessary. -/
theorem exists_good_columns (f : F × F → F) (R C : F → Polynomial F) {ε : ℚ} {d : ℕ}
    (hR : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hC : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hε : ε ≤ 1 / 100) (hcard : 20 * d ≤ Fintype.card F) :
    ∃ a : Fin (10 * d) ↪ F,
      ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C (a i)).eval ≤ 1 / 10 := by
  apply exists_embedding_of_expect_le_half
    (fun x => relativeDistance (fun y => (R y).eval x) (C x).eval)
    (fun _ => relativeDistance_nonneg _ _) (by norm_num) ?_ (10 * d) ?_
  · have h := mean_column_error_le f R C hR hC
    linarith
  · omega

end PolynomialGrids

end PCP.Algebraic.BivariateColumnSelection
