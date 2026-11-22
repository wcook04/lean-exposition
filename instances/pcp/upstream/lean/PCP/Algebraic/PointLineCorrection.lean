/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineDecoder
import PCP.Algebraic.FiniteDistance
import Mathlib.Data.Finset.Max

/-!
# Plurality correction from parametrized line predictions

For each point `x`, take the plurality of the predictions at `x` from all
representations `(x - t • v, v, t)`. Averaging over both `v` and `t` is deliberate:
it matches the tester's distribution even when nearest-polynomial ties are not
resolved consistently under changes of line parameter. The resulting function is
within twice the rejection probability of the original word.

This proves the proximity part of the correction argument in arbitrary dimension
and degree. It does not assert that the corrected function is a polynomial; that
is established separately by the low-degree agreement argument in `PointLineSoundness`.
-/

namespace PCP.Algebraic

open Finset

namespace Plurality

variable {R A : Type*} [Fintype R] [Finite A] [Nonempty A] [DecidableEq A]

/-- A plurality value exists because the finite alphabet has a most frequent value. -/
theorem exists_minimizer (w : R → A) :
    ∃ a : A, ∀ b : A, relativeDistance w (fun _ => a) ≤
      relativeDistance w (fun _ => b) := by
  let := Fintype.ofFinite A
  obtain ⟨a, _, ha⟩ := (univ : Finset A).exists_min_image
    (fun a => relativeDistance w (fun _ => a)) univ_nonempty
  exact ⟨a, fun b => ha b (mem_univ b)⟩

/-- A most frequent value, with arbitrary ties. -/
noncomputable def value (w : R → A) : A := (exists_minimizer w).choose

/-- Plurality minimizes disagreement among all constant predictions. -/
theorem minimizes (w : R → A) (a : A) :
    relativeDistance w (fun _ => value w) ≤ relativeDistance w (fun _ => a) :=
  (exists_minimizer w).choose_spec a

/-- A strict majority is the chosen plurality, independently of tie breaking. -/
theorem value_eq_of_error_lt_half [Nonempty R] (w : R → A) (a : A)
    (h : relativeDistance w (fun _ => a) < 1 / 2) : value w = a := by
  by_contra hne
  have ht := relativeDistance_triangle (fun _ => value w) w (fun _ => a)
  rw [relativeDistance_const, ite_eq_right hne,
    relativeDistance_comm (fun _ : R => value w) w] at ht
  have hm := minimizes w a
  linarith

variable {X : Type*} [Fintype X]

/-- Rowwise plurality has no more prediction error than any proposed word. -/
theorem prediction_error_le (pred : X → R → A) (f : X → A) :
    relativeDistance (fun xr : X × R => pred xr.1 xr.2)
      (fun xr => value (pred xr.1)) ≤
    relativeDistance (fun xr : X × R => pred xr.1 xr.2) (fun xr => f xr.1) := by
  rw [relativeDistance_prod, relativeDistance_prod]
  exact div_le_div_of_nonneg_right
    (sum_le_sum (fun x _ => minimizes (pred x) (f x))) (Nat.cast_nonneg _)

/-- A word differs from the rowwise plurality on at most twice its prediction error. -/
theorem distance_le_twice_prediction_error [Nonempty R]
    (pred : X → R → A) (f : X → A) :
    relativeDistance f (fun x => value (pred x)) ≤
      2 * relativeDistance (fun xr : X × R => f xr.1)
        (fun xr => pred xr.1 xr.2) := by
  have ht := relativeDistance_triangle (fun xr : X × R => f xr.1)
    (fun xr => pred xr.1 xr.2) (fun xr => value (pred xr.1))
  rw [relativeDistance_comp_fst f (fun x => value (pred x))] at ht
  have hm := prediction_error_le pred f
  rw [relativeDistance_comm (fun xr : X × R => pred xr.1 xr.2)
    (fun xr => f xr.1)] at hm
  linarith

end Plurality

namespace PointLineTest

open PolynomialLine

variable {F σ : Type*} [Field F] {c : ℕ}

/-- Change the sampled center to the point whose value is being predicted. -/
def predictionSamplesEquiv : ((σ → F) × ((σ → F) × F)) ≃
    (((σ → F) × (σ → F)) × F) where
  toFun s := ((s.1 - s.2.2 • s.2.1, s.2.1), s.2.2)
  invFun s := (point s.1.1 s.1.2 s.2, (s.1.2, s.2))
  left_inv s := by
    apply Prod.ext
    · funext i
      simp only [point_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rfl
  right_inv s := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp only [point_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · rfl
    · rfl

/-- The prediction at `x` using the line centered at `x - t • v`. -/
def prediction (table : LineTable F σ c) (x : σ → F) (vt : (σ → F) × F) : F :=
  (table (x - vt.2 • vt.1, vt.1)).val.eval vt.2

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- The actual all-parameter rejection probability equals the error of these predictions. -/
theorem prediction_error_eq_rejectionRate (f : (σ → F) → F)
    (table : LineTable F σ c) :
    relativeDistance (fun s : (σ → F) × ((σ → F) × F) => f s.1)
      (fun s => prediction table s.1 s.2) = rejectionRate f table := by
  rw [rejectionRate_eq_relativeDistance]
  have h := relativeDistance_comp_equiv (predictionSamplesEquiv (F := F) (σ := σ))
    (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
    (fun s => (table s.1).val.eval s.2)
  simpa only [predictionSamplesEquiv, Equiv.coe_fn_mk, prediction, point,
    sub_add_cancel] using h

/-- Correct a point by the plurality of all line predictions through that point. -/
noncomputable def correction (table : LineTable F σ c) (x : σ → F) : F :=
  Plurality.value (prediction table x)

/-- Plurality correction is within twice the actual tester rejection probability. -/
theorem distance_correction_le (f : (σ → F) → F) (table : LineTable F σ c) :
    relativeDistance f (correction table) ≤ 2 * rejectionRate f table := by
  have h := Plurality.distance_le_twice_prediction_error (prediction table) f
  rw [prediction_error_eq_rejectionRate] at h
  exact h

/-- Correction using nearest line polynomials satisfies the same bound against any table. -/
theorem distance_decoded_correction_le (f : (σ → F) → F)
    (table : LineTable F σ c) :
    relativeDistance f (correction (decodedTable c f)) ≤ 2 * rejectionRate f table :=
  (distance_correction_le f _).trans
    (mul_le_mul_of_nonneg_left (rejectionRate_decodedTable_le c f table) (by norm_num))

/-- The corrected function has minimum prediction error for the fixed lines table. -/
theorem rejectionRate_correction_le (f : (σ → F) → F) (table : LineTable F σ c) :
    rejectionRate (correction table) table ≤ rejectionRate f table := by
  rw [← prediction_error_eq_rejectionRate, ← prediction_error_eq_rejectionRate]
  simpa only [correction, relativeDistance_comm] using
    Plurality.prediction_error_le (prediction table) f

/-- A strict majority of predictions determines the corrected value uniquely. -/
theorem correction_eq_of_error_lt_half (table : LineTable F σ c) (x : σ → F) (a : F)
    (h : relativeDistance (prediction table x) (fun _ => a) < 1 / 2) :
    correction table x = a :=
  Plurality.value_eq_of_error_lt_half _ a h

end PointLineTest

end PCP.Algebraic
