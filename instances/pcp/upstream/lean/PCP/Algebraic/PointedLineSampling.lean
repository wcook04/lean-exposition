/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.AffineLineSampling
import PCP.Algebraic.AffineSampling

/-!
# Error fractions on lines through a fixed point

Sampling a direction and requiring parameter `t₀` to equal `x` gives center
`x-t₀v`. Every other parameter samples a uniform point. The exact mean error
is therefore `(1-1/|F|)ε + 1[f x ≠ g x]/|F|`, including zero directions.
This yields a normalized Markov bound for independently sampled `(v,t₀)`.
-/

namespace PCP.Algebraic.PointedLineSampling

open Finset PolynomialLine AffineLineSampling
open scoped BigOperators

section Markov

variable {α : Type*} [Fintype α]

/-- Containment of events implies monotonicity of their normalized fractions. -/
theorem fraction_mono (E E' : α → Prop) (h : ∀ x, E x → E' x) :
    fraction E ≤ fraction E' := by
  classical
  simp only [fraction_eq_expect]
  apply expect_le_expect
  intro x _
  by_cases hx : E x
  · simp only [hx, h x hx, ↓reduceIte, le_refl]
  · simp only [hx, ↓reduceIte]
    split_ifs <;> norm_num

/-- A finite rational Markov bound with an explicit pointwise nonnegativity premise. -/
theorem fraction_ge_le (X : α → ℚ) (hX : ∀ x, 0 ≤ X x) (a : ℚ) (ha : 0 < a) :
    fraction (fun x => a ≤ X x) ≤ (𝔼 x, X x) / a := by
  classical
  have hpoint (x : α) : a * (if a ≤ X x then (1 : ℚ) else 0) ≤ X x := by
    split_ifs with hx
    · simpa only [mul_one] using hx
    · simpa only [mul_zero] using hX x
  have hmean := expect_le_expect (s := univ) (fun x _ => hpoint x)
  rw [← mul_expect, ← fraction_eq_expect] at hmean
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using hmean

end Markov

variable {F σ : Type*} [Field F]

/-- The center/direction pair whose value at parameter `t₀` is the specified point. -/
def pointedLine (x v : σ → F) (t₀ : F) : (σ → F) × (σ → F) :=
  (x - t₀ • v, v)

theorem point_pointedLine (x v : σ → F) (t₀ s : F) :
    point (pointedLine x v t₀).1 (pointedLine x v t₀).2 s = x + (s - t₀) • v := by
  funext i
  simp only [pointedLine, point_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem point_pointedLine_self (x v : σ → F) (t₀ : F) :
    point (pointedLine x v t₀).1 (pointedLine x v t₀).2 t₀ = x := by
  rw [point_pointedLine, sub_self, zero_smul, add_zero]

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- All parameters except the fixed point's parameter have the uniform point marginal. -/
theorem expect_point_of_ne (g : (σ → F) → ℚ) (x : σ → F) (t₀ s : F) (hs : s ≠ t₀) :
    (𝔼 v, g (point (pointedLine x v t₀).1 (pointedLine x v t₀).2 s)) = 𝔼 y, g y := by
  simp only [point_pointedLine]
  exact Fintype.expect_equiv (affineSamplingEquiv x (s - t₀) (sub_ne_zero.mpr hs))
    _ _ (fun _ => rfl)

/-- Exact mean over directions, for an arbitrary rational-valued word. -/
theorem expect_lineAverage_at (g : (σ → F) → ℚ) (x : σ → F) (t₀ : F) :
    (𝔼 v, lineAverage g (pointedLine x v t₀)) =
      (1 - 1 / Fintype.card F) * (𝔼 y, g y) + g x / Fintype.card F := by
  classical
  have hpoint (s : F) :
      (𝔼 v, g (point (pointedLine x v t₀).1 (pointedLine x v t₀).2 s)) =
        (𝔼 y, g y) + if s = t₀ then g x - (𝔼 y, g y) else 0 := by
    by_cases hs : s = t₀
    · subst s
      simp only [point_pointedLine_self, Fintype.expect_const, ↓reduceIte]
      ring
    · rw [expect_point_of_ne g x t₀ s hs, ite_eq_right hs, add_zero]
  simp only [lineAverage]
  rw [expect_comm]
  simp only [hpoint]
  rw [expect_add_distrib, Fintype.expect_const]
  have he : (𝔼 s : F, if s = t₀ then g x - (𝔼 y, g y) else 0) =
      (g x - (𝔼 y, g y)) / Fintype.card F := by
    simp only [Fintype.expect_eq_sum_div_card, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [he]
  ring

/-- Averaging the designated parameter as well does not change the exact mean. -/
theorem expect_lineAverage (g : (σ → F) → ℚ) (x : σ → F) :
    (𝔼 vt : (σ → F) × F, lineAverage g (pointedLine x vt.1 vt.2)) =
      (1 - 1 / Fintype.card F) * (𝔼 y, g y) + g x / Fintype.card F := by
  classical
  rw [← univ_product_univ, expect_product, expect_comm]
  simp only [expect_lineAverage_at, Fintype.expect_const]

/-- Exact mean restricted error when only the direction is random. -/
theorem expect_lineDistance_at {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) (t₀ : F) :
    (𝔼 v, relativeDistance (fun s => f (point (x - t₀ • v) v s))
      (fun s => g (point (x - t₀ • v) v s))) =
      (1 - 1 / Fintype.card F) * relativeDistance f g +
        (if f x ≠ g x then (1 : ℚ) else 0) / Fintype.card F := by
  classical
  simpa only [← lineFraction_eq_lineAverage, ← fraction_eq_expect,
    lineFraction_ne_eq_relativeDistance, fraction_ne_eq_relativeDistance, pointedLine] using
    expect_lineAverage_at (fun y => if f y ≠ g y then 1 else 0) x t₀

/-- Exact mean restricted error under the independent direction and parameter seed. -/
theorem expect_lineDistance {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) :
    (𝔼 vt : (σ → F) × F,
      relativeDistance (fun s => f (point (x - vt.2 • vt.1) vt.1 s))
        (fun s => g (point (x - vt.2 • vt.1) vt.1 s))) =
      (1 - 1 / Fintype.card F) * relativeDistance f g +
        (if f x ≠ g x then (1 : ℚ) else 0) / Fintype.card F := by
  classical
  simpa only [← lineFraction_eq_lineAverage, ← fraction_eq_expect,
    lineFraction_ne_eq_relativeDistance, fraction_ne_eq_relativeDistance, pointedLine] using
    expect_lineAverage (fun y => if f y ≠ g y then 1 else 0) x

/-- The exceptional fixed parameter increases mean error by at most one field-size reciprocal. -/
theorem expect_lineDistance_le {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) :
    (𝔼 vt : (σ → F) × F,
      relativeDistance (fun s => f (point (x - vt.2 • vt.1) vt.1 s))
        (fun s => g (point (x - vt.2 • vt.1) vt.1 s))) ≤
      relativeDistance f g + 1 / Fintype.card F := by
  rw [expect_lineDistance]
  have hfirst : (1 - 1 / (Fintype.card F : ℚ)) * relativeDistance f g ≤
      relativeDistance f g := by
    have h := mul_nonneg (show (0 : ℚ) ≤ 1 / Fintype.card F by positivity)
      (relativeDistance_nonneg f g)
    nlinarith
  have hlast : (if f x ≠ g x then (1 : ℚ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  exact add_le_add hfirst (div_le_div_of_nonneg_right hlast (by positivity))

/-- A supplied global proximity bound also controls the mean through each fixed point. -/
theorem expect_lineDistance_le_of_distance_le {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) {ε : ℚ} (hε : relativeDistance f g ≤ ε) :
    (𝔼 vt : (σ → F) × F,
      relativeDistance (fun s => f (point (x - vt.2 • vt.1) vt.1 s))
        (fun s => g (point (x - vt.2 • vt.1) vt.1 s))) ≤
      ε + 1 / Fintype.card F :=
  (expect_lineDistance_le f g x).trans (add_le_add hε le_rfl)

/-- Markov bounds the fraction of lines through a fixed point with large restricted error. -/
theorem fraction_lineDistance_ge_le {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) (a : ℚ) (ha : 0 < a) :
    fraction (fun vt : (σ → F) × F => a ≤
      relativeDistance (fun s => f (point (x - vt.2 • vt.1) vt.1 s))
        (fun s => g (point (x - vt.2 • vt.1) vt.1 s))) ≤
      (relativeDistance f g + 1 / Fintype.card F) / a := by
  apply (fraction_ge_le _ (fun _ => relativeDistance_nonneg _ _) a ha).trans
  exact div_le_div_of_nonneg_right (expect_lineDistance_le f g x) ha.le

/-- The same exceptional-line bound using any upper bound on global error. -/
theorem fraction_lineDistance_ge_le_of_distance_le {A : Type*} [DecidableEq A]
    (f g : (σ → F) → A) (x : σ → F) {ε : ℚ} (hε : relativeDistance f g ≤ ε)
    (a : ℚ) (ha : 0 < a) :
    fraction (fun vt : (σ → F) × F => a ≤
      relativeDistance (fun s => f (point (x - vt.2 • vt.1) vt.1 s))
        (fun s => g (point (x - vt.2 • vt.1) vt.1 s))) ≤
      (ε + 1 / Fintype.card F) / a := by
  exact (fraction_lineDistance_ge_le f g x a ha).trans
    (div_le_div_of_nonneg_right (add_le_add hε le_rfl) ha.le)

end Finite

end PCP.Algebraic.PointedLineSampling
