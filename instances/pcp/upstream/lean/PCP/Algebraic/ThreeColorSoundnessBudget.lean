/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.EncodedLineLowDegreeSoundness
import PCP.Algebraic.BinaryLocalCorrectionSoundness

/-!
# An explicit positive rejection budget for algebraic 3-color verification

The gap depends only on the fixed inner degree `c`. It simultaneously satisfies
the outer low-degree decoding threshold, the difference-polynomial consistency
threshold, and both derived zero-on-grid contradiction budgets. Field-size
losses remain explicit; `q ≥ 100*D*h`, with positive degree and grid cardinality,
is one sufficient condition for their numerical bounds.

This module proves arithmetic consequences of the established constants. It does
not assume or assert the correctness of an assembled graph verifier.
-/

namespace PCP.Algebraic.ThreeColorSoundnessBudget

open EncodedLineLowDegreeTest

/-- The rejection coefficient of the two-corrector grid check. -/
def gridCoefficient (c : ℕ) : ℚ := 1 + 2 * BinaryLocalCorrection.soundnessConstant c

/-- Rejection plus the three primary/difference proximity losses. -/
def differenceCoefficient (c : ℕ) : ℚ := 1 + 3 * soundnessConstant c

/-- The derived-grid error coefficient, including the multiplied replacement loss. -/
def gridErrorCoefficient (c : ℕ) : ℚ :=
  gridCoefficient c * (1 + 2 * soundnessConstant c) + 2 * soundnessConstant c

/-- A sufficient positive rejection gap independent of dimensions, degrees, and field size. -/
def gap (c : ℕ) : ℚ :=
  min (PointLineConstants.smallError / (lineErrorConstant c + 1))
    (min (1 / (16 * differenceCoefficient c)) (1 / (16 * (gridErrorCoefficient c + 1))))

theorem gridCoefficient_pos (c : ℕ) : 0 < gridCoefficient c := by
  have h := BinaryLocalCorrection.soundnessConstant_nonneg c
  unfold gridCoefficient
  linarith

theorem differenceCoefficient_pos (c : ℕ) : 0 < differenceCoefficient c := by
  have h := soundnessConstant_nonneg c
  unfold differenceCoefficient
  linarith

theorem gridErrorCoefficient_nonneg (c : ℕ) : 0 ≤ gridErrorCoefficient c := by
  unfold gridErrorCoefficient
  positivity [gridCoefficient_pos c, soundnessConstant_nonneg c]

/-- Every inner degree gives a strictly positive fixed gap. -/
theorem gap_pos (c : ℕ) : 0 < gap c := by
  have hA := lineErrorConstant_nonneg c
  have hB := differenceCoefficient_pos c
  have hC := gridErrorCoefficient_nonneg c
  unfold gap
  apply lt_min
  · exact div_pos PointLineConstants.smallError_pos (by linarith)
  · apply lt_min <;> positivity

/-- The outer low-degree theorem's closed small-error premise is satisfied. -/
theorem decoding_budget (c : ℕ) {κ : ℚ} (hκ : 0 ≤ κ) (hsmall : κ < gap c) :
    lineErrorConstant c * κ ≤ PointLineConstants.smallError := by
  have hA := lineErrorConstant_nonneg c
  have hden : 0 < lineErrorConstant c + 1 := by linarith
  have hlt : κ < PointLineConstants.smallError / (lineErrorConstant c + 1) :=
    hsmall.trans_le (min_le_left _ _)
  have hmul := (lt_div_iff₀ hden).mp hlt
  nlinarith

/-- The complete difference-consistency error is strictly below `1/16`. -/
theorem difference_error_lt (c : ℕ) {κ : ℚ} (hsmall : κ < gap c) :
    κ + 3 * (soundnessConstant c * κ) < 1 / 16 := by
  have hden : 0 < 16 * differenceCoefficient c := by
    positivity [differenceCoefficient_pos c]
  have hlt : κ < 1 / (16 * differenceCoefficient c) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmul := (lt_div_iff₀ hden).mp hlt
  unfold differenceCoefficient at hmul
  linarith

/-- The complete error coefficient of the derived grid check is strictly below `1/16`. -/
theorem grid_error_lt (c : ℕ) {κ : ℚ} (hκ : 0 ≤ κ) (hsmall : κ < gap c) :
    gridCoefficient c * (κ + 2 * (soundnessConstant c * κ)) +
      2 * (soundnessConstant c * κ) < 1 / 16 := by
  have hL := gridErrorCoefficient_nonneg c
  have hden : 0 < 16 * (gridErrorCoefficient c + 1) := by positivity
  have hlt : κ < 1 / (16 * (gridErrorCoefficient c + 1)) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmul := (lt_div_iff₀ hden).mp hlt
  have hbound : gridErrorCoefficient c * κ < 1 / 16 := by nlinarith
  unfold gridErrorCoefficient at hbound
  nlinarith

/-- The strict threshold needed to force equality of the difference polynomials. -/
theorem difference_budget (c : ℕ) {κ : ℚ} {D q : ℕ}
    (hsmall : κ < gap c) (hdegree : (D : ℚ) / q ≤ 1 / 4) :
    κ + 3 * (soundnessConstant c * κ) < (1 - (D : ℚ) / q) / 2 := by
  have h := difference_error_lt c hsmall
  linarith

/-- The derived zero-on-grid bound contradicts nonvanishing under these field losses. -/
theorem grid_budget (c : ℕ) {κ : ℚ} {D h q : ℕ}
    (hκ : 0 ≤ κ) (hsmall : κ < gap c)
    (hdegree : ((5 * D * h : ℕ) : ℚ) / q ≤ 1 / 4)
    (hcorrection : ((5 * D : ℕ) : ℚ) / (q - 1 : ℕ) ≤ 1 / 8) :
    gridCoefficient c * (κ + 2 * (soundnessConstant c * κ)) +
      2 * (soundnessConstant c * κ) + ((5 * D : ℕ) : ℚ) / (q - 1 : ℕ) <
        (1 - ((5 * D * h : ℕ) : ℚ) / q) / 2 := by
  have h := grid_error_lt c hκ hsmall
  linarith

/-- One simple field-size bound implies all three rational loss bounds.
Natural subtraction in `q-1` is handled explicitly. -/
theorem field_ratio_bounds {D h q : ℕ} (hD : 0 < D) (hh : 0 < h)
    (hq : 100 * D * h ≤ q) :
    (D : ℚ) / q ≤ 1 / 4 ∧
      ((5 * D * h : ℕ) : ℚ) / q ≤ 1 / 4 ∧
      ((5 * D : ℕ) : ℚ) / (q - 1 : ℕ) ≤ 1 / 8 := by
  have hDh : D ≤ D * h := Nat.le_mul_of_pos_right D hh
  have hqD : 100 * D ≤ q := by nlinarith
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqm : 40 * D ≤ q - 1 := by omega
  have hqmpos : (0 : ℚ) < (q - 1 : ℕ) := by
    exact_mod_cast (show 0 < q - 1 by omega)
  have hqD' : (100 : ℚ) * D ≤ q := by exact_mod_cast hqD
  have hq' : (100 : ℚ) * D * h ≤ q := by exact_mod_cast hq
  have hqm' : (40 : ℚ) * D ≤ (q - 1 : ℕ) := by exact_mod_cast hqm
  refine ⟨(div_le_iff₀ hqpos).mpr (by linarith), ?_, ?_⟩
  · apply (div_le_iff₀ hqpos).mpr
    push_cast
    linarith
  · apply (div_le_iff₀ hqmpos).mpr
    push_cast
    linarith

/-- The three rejection-error obligations, with a concrete field-size condition for their losses. -/
theorem sufficient_budget (c : ℕ) {κ : ℚ} {D h q : ℕ}
    (hκ : 0 ≤ κ) (hsmall : κ < gap c) (hD : 0 < D) (hh : 0 < h)
    (hq : 100 * D * h ≤ q) :
    lineErrorConstant c * κ ≤ PointLineConstants.smallError ∧
      κ + 3 * (soundnessConstant c * κ) < (1 - (D : ℚ) / q) / 2 ∧
      gridCoefficient c * (κ + 2 * (soundnessConstant c * κ)) +
        2 * (soundnessConstant c * κ) + ((5 * D : ℕ) : ℚ) / (q - 1 : ℕ) <
          (1 - ((5 * D * h : ℕ) : ℚ) / q) / 2 := by
  obtain ⟨h₁, h₂, h₃⟩ := field_ratio_bounds hD hh hq
  exact ⟨decoding_budget c hκ hsmall, difference_budget c hsmall h₁,
    grid_budget c hκ hsmall h₂ h₃⟩

end PCP.Algebraic.ThreeColorSoundnessBudget
