/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineDecoder
import PCP.Algebraic.AffineSampling

/-!
# Affine changes of line parameter

Invertible affine changes preserve polynomial degree, word distance, and the
minimum error attained by a bounded-degree polynomial. Consequently, the minimum
line error depends only on the parametrized line up to affine reparametrization.

The chosen nearest polynomial is proved to transform by composition only below
the strict half-distance radius, where it is unique. No covariance is asserted
for arbitrary classical choices among tied minimizers.
-/

namespace PCP.Algebraic.PointLineTest

open PolynomialLine

variable {F σ : Type*} [Field F] {c : ℕ}

/-- Compose a polynomial with the affine parameter change `t ↦ a + b*t`. -/
noncomputable def affineCompose (a b : F) (p : Polynomial F) : Polynomial F :=
  p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)

@[simp] theorem eval_affineCompose (a b : F) (p : Polynomial F) (t : F) :
    (affineCompose a b p).eval t = p.eval (a + b * t) := by
  simp [affineCompose, Polynomial.eval_comp]

/-- A nonzero change of scale preserves the exact degree, including constant polynomials. -/
theorem natDegree_affineCompose (a b : F) (hb : b ≠ 0) (p : Polynomial F) :
    (affineCompose a b p).natDegree = p.natDegree := by
  simp only [affineCompose, Polynomial.natDegree_comp, Polynomial.natDegree_C_add,
    Polynomial.natDegree_C_mul_X b hb, mul_one]

/-- Reparametrizing a line gives the same points at the corresponding old parameters. -/
theorem point_reparametrize (u v : σ → F) (a b t : F) :
    point (u + a • v) (b • v) t = point u v (a + b * t) := by
  ext i
  simp only [point_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [Fintype F] [DecidableEq F]

/-- Invertible changes of field parameter preserve normalized word distance. -/
theorem relativeDistance_affine_parameter (a b : F) (hb : b ≠ 0) (w z : F → F) :
    relativeDistance (fun t => w (a + b * t)) (fun t => z (a + b * t)) =
      relativeDistance w z :=
  relativeDistance_affineSampling a b hb w z

/-- The polynomial composition and the word reindexing preserve their disagreement exactly. -/
theorem relativeDistance_affineCompose (a b : F) (hb : b ≠ 0)
    (w : F → F) (p : Polynomial F) :
    relativeDistance (fun t => w (a + b * t)) (affineCompose a b p).eval =
      relativeDistance w p.eval := by
  have h := relativeDistance_affine_parameter a b hb w p.eval
  simpa only [eval_affineCompose] using h

/-- The least achievable normalized error against degree-`c` polynomials. -/
noncomputable def minimumError (c : ℕ) (w : F → F) : ℚ :=
  relativeDistance w (bestApproximation c w).val.eval

/-- Affine parameter changes preserve the optimal error, even when minimizing polynomials tie. -/
theorem minimumError_affine (c : ℕ) (w : F → F) (a b : F) (hb : b ≠ 0) :
    minimumError c (fun t => w (a + b * t)) = minimumError c w := by
  apply le_antisymm
  · have h := bestApproximation_min c (fun t => w (a + b * t))
      (affineCompose a b (bestApproximation c w).val)
      (by rw [natDegree_affineCompose a b hb]; exact (bestApproximation c w).property)
    rw [relativeDistance_affineCompose a b hb] at h
    exact h
  · let w' : F → F := fun t => w (a + b * t)
    let p := (bestApproximation c w').val
    have hp : p.natDegree ≤ c := (bestApproximation c w').property
    have h := bestApproximation_min c w (affineCompose (-b⁻¹ * a) b⁻¹ p)
      (by rw [natDegree_affineCompose _ _ (inv_ne_zero hb)]; exact hp)
    have hi := relativeDistance_affineCompose (-b⁻¹ * a) b⁻¹ (inv_ne_zero hb) w' p
    have hw : (fun t => w' (-b⁻¹ * a + b⁻¹ * t)) = w := by
      funext t
      dsimp only [w']
      congr 1
      field_simp
      ring
    rw [hw] at hi
    rw [hi] at h
    exact h

/-- Unique nearest polynomials transform by composition; the radius excludes ambiguous ties. -/
theorem bestApproximation_affine_of_close (c : ℕ) (w : F → F)
    (a b : F) (hb : b ≠ 0)
    (hradius : 2 * minimumError c w < 1 - (c : ℚ) / Fintype.card F) :
    (bestApproximation c (fun t => w (a + b * t))).val =
      affineCompose a b (bestApproximation c w).val := by
  apply bestApproximation_eq_of_close c _ _
    (by rw [natDegree_affineCompose a b hb]; exact (bestApproximation c w).property) hradius
  rw [relativeDistance_affineCompose a b hb]
  exact le_rfl

/-- The normalized minimum error is independent of an invertible affine line parameterization. -/
theorem decodedTable_error_reparametrize (c : ℕ) (f : (σ → F) → F)
    (u v : σ → F) (a b : F) (hb : b ≠ 0) :
    relativeDistance (fun t => f (point (u + a • v) (b • v) t))
        (decodedTable c f (u + a • v, b • v)).val.eval =
      relativeDistance (fun t => f (point u v t)) (decodedTable c f (u, v)).val.eval := by
  change minimumError c (fun t => f (point (u + a • v) (b • v) t)) =
    minimumError c (fun t => f (point u v t))
  simp only [point_reparametrize]
  exact minimumError_affine c (fun t => f (point u v t)) a b hb

/-- On uniquely decoded lines, the actual chosen formal polynomials transform correctly. -/
theorem decodedTable_reparametrize_of_close (c : ℕ) (f : (σ → F) → F)
    (u v : σ → F) (a b : F) (hb : b ≠ 0)
    (hradius : 2 * relativeDistance (fun t => f (point u v t))
      (decodedTable c f (u, v)).val.eval < 1 - (c : ℚ) / Fintype.card F) :
    (decodedTable c f (u + a • v, b • v)).val =
      affineCompose a b (decodedTable c f (u, v)).val := by
  simp only [decodedTable, point_reparametrize]
  exact bestApproximation_affine_of_close c (fun t => f (point u v t)) a b hb hradius

end PCP.Algebraic.PointLineTest
