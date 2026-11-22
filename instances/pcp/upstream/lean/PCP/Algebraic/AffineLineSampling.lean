/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialLine
import PCP.Algebraic.FiniteDistance
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Pairwise independence and concentration on random affine lines

The center and direction are sampled independently and uniformly, including
the zero direction. Two distinct field parameters give independent uniform
points. Consequently the variance of the fraction of a set on a line is exactly
`ε(1-ε)/|F|`, where `ε` is its global density. Rational Chebyshev bounds the
normalized fraction of lines whose error is at least `ε+a`.

The proofs use explicit finite bijections and mathlib's rational finite averages.
No independence assumption is supplied, and empty coordinate types are allowed.
-/

namespace PCP.Algebraic.AffineLineSampling

open Finset PolynomialLine
open scoped BigOperators

section Fractions

variable {α : Type*} [Fintype α]

/-- The normalized fraction of a finite type satisfying a predicate. -/
noncomputable def fraction (E : α → Prop) : ℚ := by
  classical
  exact 𝔼 x, if E x then 1 else 0

theorem fraction_eq_expect (E : α → Prop) [DecidablePred E] :
    fraction E = 𝔼 x, if E x then (1 : ℚ) else 0 := by
  unfold fraction
  congr 1
  funext x
  split_ifs <;> rfl

theorem fraction_eq_card_filter (E : α → Prop) [DecidablePred E] :
    fraction E = ((univ.filter E).card : ℚ) / Fintype.card α := by
  classical
  rw [fraction_eq_expect, Fintype.expect_eq_sum_div_card, ← natCast_card_filter]

theorem fraction_nonneg (E : α → Prop) : 0 ≤ fraction E := by
  classical
  exact expect_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem fraction_le_one [Nonempty α] (E : α → Prop) : fraction E ≤ 1 := by
  classical
  exact expect_le univ_nonempty (fun _ _ => by split_ifs <;> norm_num)

/-- Error predicates recover the project's normalized Hamming distance. -/
theorem fraction_ne_eq_relativeDistance {A : Type*} [DecidableEq A] (f g : α → A) :
    fraction (fun x => f x ≠ g x) = relativeDistance f g := by
  classical
  rw [fraction_eq_card_filter]
  rfl

/-- The variance of a finite indicator is its density times its complementary density. -/
theorem variance_indicator [Nonempty α] (E : α → Prop) [DecidablePred E] :
    (𝔼 x, ((if E x then (1 : ℚ) else 0) - fraction E) ^ 2) =
      fraction E * (1 - fraction E) := by
  classical
  calc
    _ = 𝔼 x, ((if E x then (1 : ℚ) else 0) -
        2 * fraction E * (if E x then 1 else 0) + fraction E ^ 2) := by
      apply expect_congr rfl
      intro x _
      split_ifs <;> ring
    _ = _ := by
      rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
      rw [← fraction_eq_expect]
      ring

/-- Rational Chebyshev for the upper deviation event, with arbitrary specified center. -/
theorem fraction_upper_deviation_le (X : α → ℚ) (μ a : ℚ) (ha : 0 < a) :
    fraction (fun x => μ + a ≤ X x) ≤ (𝔼 x, (X x - μ) ^ 2) / a ^ 2 := by
  classical
  have hpoint (x : α) :
      a ^ 2 * (if μ + a ≤ X x then (1 : ℚ) else 0) ≤ (X x - μ) ^ 2 := by
    split_ifs with hx
    · simp only [mul_one]
      exact sq_le_sq₀ ha.le (by linarith) |>.mpr (by linarith)
    · simp only [mul_zero]
      exact sq_nonneg _
  have hmean := expect_le_expect (s := univ) (fun x _ => hpoint x)
  rw [← mul_expect, ← fraction_eq_expect] at hmean
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  simpa only [mul_comm] using hmean

end Fractions

variable {F σ : Type*} [Field F]

/-- Evaluations at distinct parameters bijectively encode the center and direction. -/
def pointsEquiv (s t : F) (hst : s ≠ t) :
    ((σ → F) × (σ → F)) ≃ ((σ → F) × (σ → F)) where
  toFun uv := (point uv.1 uv.2 s, point uv.1 uv.2 t)
  invFun xy :=
    (xy.1 - s • ((t - s)⁻¹ • (xy.2 - xy.1)), (t - s)⁻¹ • (xy.2 - xy.1))
  left_inv uv := by
    have hts : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
    apply Prod.ext <;> funext i <;>
      simp only [point_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp <;> ring
  right_inv xy := by
    have hts : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
    apply Prod.ext <;> funext i <;>
      simp only [point_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp <;> ring

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- Every fixed parameter has the uniform point marginal, including parameter zero. -/
theorem expect_point (g : (σ → F) → ℚ) (t : F) :
    (𝔼 uv : (σ → F) × (σ → F), g (point uv.1 uv.2 t)) = 𝔼 x, g x := by
  classical
  rw [← univ_product_univ, expect_product, expect_comm]
  have h (v : σ → F) : (𝔼 u, g (point u v t)) = 𝔼 x, g x := by
    exact Fintype.expect_equiv (Equiv.addRight (t • v)) _ _ (fun _ => rfl)
  simp only [h, Fintype.expect_const]

/-- The two-point product identity expresses actual pairwise independence. -/
theorem expect_point_mul (g h : (σ → F) → ℚ) (s t : F) (hst : s ≠ t) :
    (𝔼 uv : (σ → F) × (σ → F), g (point uv.1 uv.2 s) * h (point uv.1 uv.2 t)) =
      (𝔼 x, g x) * 𝔼 y, h y := by
  classical
  calc
    _ = 𝔼 xy : (σ → F) × (σ → F), g xy.1 * h xy.2 :=
      Fintype.expect_equiv (pointsEquiv s t hst) _ _ (fun _ => rfl)
    _ = _ := by
      rw [← univ_product_univ, expect_product, ← Fintype.expect_mul_expect]

/-- The average of a rational-valued word over the parameters of one line. -/
def lineAverage (g : (σ → F) → ℚ) (uv : (σ → F) × (σ → F)) : ℚ :=
  𝔼 t, g (point uv.1 uv.2 t)

/-- The average line average is exactly the global average. -/
theorem expect_lineAverage (g : (σ → F) → ℚ) :
    (𝔼 uv, lineAverage g uv) = 𝔼 x, g x := by
  simp only [lineAverage]
  rw [expect_comm]
  simp only [expect_point, Fintype.expect_const]

/-- Pairwise independence gives the exact second moment for any centered word. -/
theorem expect_lineAverage_sq_of_mean_zero (g : (σ → F) → ℚ)
    (hg : (𝔼 x, g x) = 0) :
    (𝔼 uv, lineAverage g uv ^ 2) = (𝔼 x, g x ^ 2) / Fintype.card F := by
  classical
  have hpair (s t : F) :
      (𝔼 uv : (σ → F) × (σ → F), g (point uv.1 uv.2 s) * g (point uv.1 uv.2 t)) =
        if s = t then 𝔼 x, g x ^ 2 else 0 := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, ← sq]
      exact expect_point (fun x => g x ^ 2) s
    · rw [expect_point_mul g g s t hst, hg, ite_eq_right hst, zero_mul]
  calc
    _ = 𝔼 uv : (σ → F) × (σ → F),
        𝔼 s, 𝔼 t, g (point uv.1 uv.2 s) * g (point uv.1 uv.2 t) := by
      simp only [lineAverage, sq, Fintype.expect_mul_expect]
    _ = 𝔼 s : F, 𝔼 t : F, 𝔼 uv : (σ → F) × (σ → F),
        g (point uv.1 uv.2 s) * g (point uv.1 uv.2 t) := by
      rw [expect_comm]
      congr 1
      funext s
      rw [expect_comm]
    _ = 𝔼 s : F, 𝔼 t : F, if s = t then 𝔼 x, g x ^ 2 else 0 := by
      simp only [hpair]
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, sum_ite_eq, mem_univ, ↓reduceIte,
        sum_const, card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero)

/-- The variance of a random line average is the global variance divided by the field size. -/
theorem variance_lineAverage (g : (σ → F) → ℚ) :
    (𝔼 uv, (lineAverage g uv - 𝔼 x, g x) ^ 2) =
      (𝔼 x, (g x - 𝔼 y, g y) ^ 2) / Fintype.card F := by
  have hg : (𝔼 x, (g x - (𝔼 y, g y))) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const, sub_self]
  have hline (uv : (σ → F) × (σ → F)) :
      lineAverage (fun x => g x - 𝔼 y, g y) uv = lineAverage g uv - 𝔼 x, g x := by
    simp only [lineAverage, expect_sub_distrib, Fintype.expect_const]
  simpa only [hline] using
    expect_lineAverage_sq_of_mean_zero (fun x => g x - (𝔼 y, g y)) hg

/-- The fraction of parameters on one line whose point belongs to the specified set. -/
noncomputable def lineFraction (E : (σ → F) → Prop)
    (uv : (σ → F) × (σ → F)) : ℚ :=
  fraction (fun t => E (point uv.1 uv.2 t))

omit [Fintype σ] [DecidableEq σ] in
theorem lineFraction_eq_lineAverage (E : (σ → F) → Prop) [DecidablePred E]
    (uv : (σ → F) × (σ → F)) :
    lineFraction E uv = lineAverage (fun x => if E x then 1 else 0) uv := by
  unfold lineFraction lineAverage
  exact fraction_eq_expect _

/-- Random lines have exactly the original mean density. -/
theorem expect_lineFraction (E : (σ → F) → Prop) :
    (𝔼 uv, lineFraction E uv) = fraction E := by
  classical
  simp only [lineFraction_eq_lineAverage, expect_lineAverage, fraction_eq_expect]

/-- The exact indicator variance, with zero directions retained in the sample space. -/
theorem variance_lineFraction (E : (σ → F) → Prop) :
    (𝔼 uv, (lineFraction E uv - fraction E) ^ 2) =
      fraction E * (1 - fraction E) / Fintype.card F := by
  classical
  simpa only [← lineFraction_eq_lineAverage, ← fraction_eq_expect, variance_indicator] using
    variance_lineAverage (fun x => if E x then 1 else 0)

/-- Only a controlled fraction of lines can have density substantially above the global density. -/
theorem fraction_lineFraction_ge_le (E : (σ → F) → Prop) (a : ℚ) (ha : 0 < a) :
    fraction (fun uv => fraction E + a ≤ lineFraction E uv) ≤
      fraction E * (1 - fraction E) / (Fintype.card F * a ^ 2) := by
  have h := fraction_upper_deviation_le (lineFraction E) (fraction E) a ha
  rw [variance_lineFraction, div_div] at h
  exact h

omit [Fintype σ] [DecidableEq σ] in
/-- The line error is the normalized Hamming distance of the two restricted words. -/
theorem lineFraction_ne_eq_relativeDistance {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (uv : (σ → F) × (σ → F)) :
    lineFraction (fun x => f x ≠ g x) uv =
      relativeDistance (fun t => f (point uv.1 uv.2 t))
        (fun t => g (point uv.1 uv.2 t)) :=
  fraction_ne_eq_relativeDistance _ _

/-- Averaging line errors recovers the global normalized Hamming distance. -/
theorem expect_lineDistance {A : Type*} [DecidableEq A] (f g : (σ → F) → A) :
    (𝔼 uv : (σ → F) × (σ → F),
      relativeDistance (fun t => f (point uv.1 uv.2 t))
        (fun t => g (point uv.1 uv.2 t))) = relativeDistance f g := by
  simpa only [fraction_ne_eq_relativeDistance, lineFraction_ne_eq_relativeDistance] using
    expect_lineFraction (fun x => f x ≠ g x)

/-- Exact variance stated directly for errors between two restricted words. -/
theorem variance_lineDistance {A : Type*} [DecidableEq A] (f g : (σ → F) → A) :
    (𝔼 uv : (σ → F) × (σ → F),
      (relativeDistance (fun t => f (point uv.1 uv.2 t))
        (fun t => g (point uv.1 uv.2 t)) - relativeDistance f g) ^ 2) =
      relativeDistance f g * (1 - relativeDistance f g) / Fintype.card F := by
  simpa only [fraction_ne_eq_relativeDistance, lineFraction_ne_eq_relativeDistance] using
    variance_lineFraction (fun x => f x ≠ g x)

/-- A normalized concentration bound directly in terms of global and restricted error fractions. -/
theorem fraction_lineDistance_ge_le {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (a : ℚ) (ha : 0 < a) :
    fraction (fun uv : (σ → F) × (σ → F) => relativeDistance f g + a ≤
      relativeDistance (fun t => f (point uv.1 uv.2 t))
        (fun t => g (point uv.1 uv.2 t))) ≤
      relativeDistance f g * (1 - relativeDistance f g) / (Fintype.card F * a ^ 2) := by
  simpa only [fraction_ne_eq_relativeDistance, lineFraction_ne_eq_relativeDistance] using
    fraction_lineFraction_ge_le (fun x => f x ≠ g x) a ha

end Finite

end PCP.Algebraic.AffineLineSampling
