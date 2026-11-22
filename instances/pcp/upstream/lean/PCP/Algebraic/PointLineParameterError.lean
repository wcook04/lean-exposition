/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineReparametrization
import PCP.Algebraic.PointedLineSampling

/-!
# Fixed-parameter rejection without coherent nearest-polynomial choices

Nearest polynomials chosen with arbitrary ties need not give the same rejection
probability at every fixed parameter. They do transform correctly on lines
inside the unique decoding radius. Comparing a fixed parameter with an independent
uniform parameter therefore loses only the fraction of lines outside that radius.

This proves a fixed-parameter error bound for the actual `decodedTable`, rather
than assuming the consistent geometric-line choices used in ALMSS Remark 63.
-/

namespace PCP.Algebraic.PointLineTest

open Finset PolynomialLine AffineLineSampling PointedLineSampling
open scoped BigOperators

variable {F σ : Type*} [Field F]

/-- Shift the line center so a fresh parameter reaches the original fixed point. -/
def parameterShiftEquiv (t : F) :
    (((σ → F) × (σ → F)) × F) ≃ (((σ → F) × (σ → F)) × F) where
  toFun s := ((s.1.1 + (t - s.2) • s.1.2, s.1.2), s.2)
  invFun s := ((s.1.1 - (t - s.2) • s.1.2, s.1.2), s.2)
  left_inv s := by
    apply Prod.ext
    · apply Prod.ext
      · exact add_sub_cancel_right _ _
      · rfl
    · rfl
  right_inv s := by
    apply Prod.ext
    · apply Prod.ext
      · exact sub_add_cancel _ _
      · rfl
    · rfl

@[simp] theorem point_parameterShift (u v : σ → F) (t s : F) :
    point (u + (t - s) • v) v s = point u v t := by
  funext i
  simp only [point_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Rejection against the actual nearest line polynomials at one fixed parameter. -/
noncomputable def rejectionAt (c : ℕ) (f : (σ → F) → F) (t : F) : ℚ :=
  relativeDistance (fun uv : (σ → F) × (σ → F) => f (point uv.1 uv.2 t))
    (fun uv => (decodedTable c f uv).val.eval t)

theorem rejectionAt_nonneg (c : ℕ) (f : (σ → F) → F) (t : F) :
    0 ≤ rejectionAt c f t := relativeDistance_nonneg _ _

/-- The mean of the fixed-parameter errors is exactly the all-parameter rejection. -/
theorem mean_rejectionAt_eq_rejectionRate (c : ℕ) (f : (σ → F) → F) :
    (𝔼 t, rejectionAt c f t) = rejectionRate f (decodedTable c f) := by
  rw [Fintype.expect_eq_sum_div_card, rejectionRate_eq_relativeDistance]
  have h := relativeDistance_comp_equiv
    (Equiv.prodComm F ((σ → F) × (σ → F)))
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
    (fun s => (decodedTable c f s.1).val.eval s.2)
  rw [relativeDistance_prod] at h
  exact h

/-- The minimum normalized error of one parametrized line. -/
noncomputable def decodedLineError (c : ℕ) (f : (σ → F) → F)
    (uv : (σ → F) × (σ → F)) : ℚ :=
  relativeDistance (fun t => f (point uv.1 uv.2 t)) (decodedTable c f uv).val.eval

/-- Averaging minimum line errors gives the actual all-parameter rejection rate. -/
theorem mean_decodedLineError_eq_rejectionRate (c : ℕ) (f : (σ → F) → F) :
    (𝔼 uv, decodedLineError c f uv) = rejectionRate f (decodedTable c f) := by
  rw [rejectionRate_eq_relativeDistance, relativeDistance_prod,
    Fintype.expect_eq_sum_div_card]
  rfl

/-- After the explicit center shift, the fresh parameter has exactly the tester distribution. -/
theorem shifted_parameter_error_eq_rejectionRate (c : ℕ) (f : (σ → F) → F) (t : F) :
    relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 t))
      (fun s => (decodedTable c f (s.1.1 + (t - s.2) • s.1.2, s.1.2)).val.eval s.2) =
      rejectionRate f (decodedTable c f) := by
  rw [rejectionRate_eq_relativeDistance]
  have h := relativeDistance_comp_equiv (parameterShiftEquiv (σ := σ) t)
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
    (fun s => (decodedTable c f s.1).val.eval s.2)
  simpa only [parameterShiftEquiv, Equiv.coe_fn_mk, point_parameterShift] using h

/-- A fixed parameter costs at most rejection plus the Markov bound for lines
outside any supplied unique-decoding radius. Equality at the radius is allowed. -/
theorem rejectionAt_le_add_div (c : ℕ) (f : (σ → F) → F) (t : F)
    {r : ℚ} (hr : 0 < r) (hradius : 2 * r ≤ 1 - (c : ℚ) / Fintype.card F) :
    rejectionAt c f t ≤ rejectionRate f (decodedTable c f) +
      rejectionRate f (decodedTable c f) / r := by
  have hmean : (𝔼 s : ((σ → F) × (σ → F)) × F, decodedLineError c f s.1) =
      rejectionRate f (decodedTable c f) := by
    rw [← univ_product_univ, expect_product]
    simp only [Fintype.expect_const]
    exact mean_decodedLineError_eq_rejectionRate c f
  have hchange : relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F =>
        (decodedTable c f (s.1.1 + (t - s.2) • s.1.2, s.1.2)).val.eval s.2)
      (fun s => (decodedTable c f s.1).val.eval t) ≤
      rejectionRate f (decodedTable c f) / r := by
    rw [← fraction_ne_eq_relativeDistance]
    apply (fraction_mono _ (fun s : ((σ → F) × (σ → F)) × F =>
      r ≤ decodedLineError c f s.1) ?_).trans
    · have h := fraction_ge_le
        (fun s : ((σ → F) × (σ → F)) × F => decodedLineError c f s.1)
        (fun _ => relativeDistance_nonneg _ _) r hr
      rwa [hmean] at h
    · intro s hne
      by_contra hbad
      have hclose : 2 * decodedLineError c f s.1 <
          1 - (c : ℚ) / Fintype.card F := by
        have hlt := lt_of_not_ge hbad
        linarith
      have h := decodedTable_reparametrize_of_close c f s.1.1 s.1.2
        (t - s.2) 1 one_ne_zero hclose
      simp only [one_smul] at h
      apply hne
      rw [h, eval_affineCompose, one_mul, sub_add_cancel]
  have htriangle := relativeDistance_triangle
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 t))
    (fun s => (decodedTable c f (s.1.1 + (t - s.2) • s.1.2, s.1.2)).val.eval s.2)
    (fun s => (decodedTable c f s.1).val.eval t)
  have hlift := relativeDistance_comp_fst (κ := F)
    (fun uv : (σ → F) × (σ → F) => f (point uv.1 uv.2 t))
    (fun uv => (decodedTable c f uv).val.eval t)
  rw [hlift, shifted_parameter_error_eq_rejectionRate] at htriangle
  exact htriangle.trans (add_le_add le_rfl hchange)

/-- The sharp unique-radius form of the fixed-parameter rejection bound. -/
theorem rejectionAt_le (c : ℕ) (f : (σ → F) → F) (t : F)
    (hgap : 0 < 1 - (c : ℚ) / Fintype.card F) :
    rejectionAt c f t ≤ rejectionRate f (decodedTable c f) +
      2 * rejectionRate f (decodedTable c f) / (1 - (c : ℚ) / Fintype.card F) := by
  have h := rejectionAt_le_add_div c f t
    (r := (1 - (c : ℚ) / Fintype.card F) / 2) (by positivity) (by linarith)
  simpa only [div_div_eq_mul_div, mul_comm] using h

/-- A convenient uniform constant when the field has at least three times the degree. -/
theorem rejectionAt_le_four_mul (c : ℕ) (f : (σ → F) → F) (t : F)
    (hcard : 3 * c ≤ Fintype.card F) :
    rejectionAt c f t ≤ 4 * rejectionRate f (decodedTable c f) := by
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hfrac : (c : ℚ) / Fintype.card F ≤ 1 / 3 := by
    apply (div_le_iff₀ hq).mpr
    have h : (3 : ℚ) * c ≤ Fintype.card F := by exact_mod_cast hcard
    linarith
  have h := rejectionAt_le_add_div c f t (r := 1 / 3) (by norm_num) (by linarith)
  convert h using 1
  ring

end PCP.Algebraic.PointLineTest
