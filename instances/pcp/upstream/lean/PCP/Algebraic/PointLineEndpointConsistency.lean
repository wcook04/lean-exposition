/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.MixedPlaneSampling
import PCP.Algebraic.ProbabilisticCrossing
import PCP.Algebraic.PointLinePredictionConsistency

/-!
# Prediction consistency at a varying line endpoint

For each fixed center and parameter, a random direction gives a line prediction
at a varying endpoint. A mixed plane compares that prediction with an independent
full prediction seed through the endpoint. Its four actual mean error bounds
and bivariate crossing consistency give the comparison bound; rowwise plurality
then transfers it to the existing all-parameter correction.

The fixed-parameter rejection estimate uses uniqueness only on sufficiently good
lines. Arbitrary nearest-polynomial ties are retained throughout.
-/

namespace PCP.Algebraic.PointLineEndpointConsistency

open Finset PolynomialLine PointLineTest AffineLineSampling MixedPlaneSampling
open scoped BigOperators

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- The received word on a mixed plane with one independently shifted coordinate. -/
def mixedGrid (f : (σ → F) → F) (u : σ → F) (seed : MixedSeed F σ) : F × F → F :=
  fun yz => f (mixedPlanePoint u seed yz.1 yz.2)

theorem crossing_errors_eq (f : (σ → F) → F) (u : σ → F)
    (seed : MixedSeed F σ) (t : F) :
    ProbabilisticCrossing.errors d (mixedGrid f u seed) t seed.2.2 =
      ![mixedRowError f (decodedTable d f) u seed,
        mixedColumnError f (decodedTable d f) u seed,
        mixedLocalRowError f (decodedTable d f) u t seed,
        mixedLocalColumnError f (decodedTable d f) u seed] := by
  funext j
  fin_cases j
  · simp only [ProbabilisticCrossing.errors, Fin.zero_eta, Matrix.cons_val_zero, mixedGrid,
      mixedRowError, decodedTable, mixedPlanePoint_eq_row]
    congr 1
    funext yz
    exact congrArg f (mixedPlanePoint_eq_row u seed yz.1 yz.2)
  · simp only [ProbabilisticCrossing.errors, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, mixedGrid,
      mixedColumnError, decodedTable, mixedPlanePoint_eq_column]
    congr 1
    funext yz
    exact congrArg f (mixedPlanePoint_eq_column u seed yz.1 yz.2)
  · simp [ProbabilisticCrossing.errors, mixedGrid,
      mixedLocalRowError, decodedTable, mixedPlanePoint_eq_column]
  · simp [ProbabilisticCrossing.errors, mixedGrid,
      mixedLocalColumnError, decodedTable, mixedPlanePoint_eq_row]

theorem crossing_row_prediction (f : (σ → F) → F) (u : σ → F)
    (seed : MixedSeed F σ) (t : F) :
    (bestApproximation d (fun z => mixedGrid f u seed (t, z))).val.eval seed.2.2 =
      prediction (decodedTable d f) (point u seed.1 t) seed.2 := by
  simp only [mixedGrid, mixedPlanePoint_eq_row, mixedRowLine, prediction, decodedTable,
    point]

theorem crossing_column_prediction (f : (σ → F) → F) (u : σ → F)
    (seed : MixedSeed F σ) (t : F) :
    (bestApproximation d (fun y => mixedGrid f u seed (y, seed.2.2))).val.eval t =
      (decodedTable d f (u, seed.1)).val.eval t := by
  simp only [mixedGrid, mixedPlanePoint_eq_column, mixedColumnLine, sub_self,
    zero_smul, add_zero, decodedTable]

variable [Fintype σ] [DecidableEq σ]

/-- A prediction at a varying endpoint agrees with an independent full seed
through that endpoint. -/
theorem fraction_endpoint_disagreement_le (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F) (f : (σ → F) → F) (u : σ → F) (t : F)
    {ε : ℚ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2) :
    fraction (fun seed : MixedSeed F σ =>
      (decodedTable d f (u, seed.1)).val.eval t ≠
        prediction (decodedTable d f) (point u seed.1 t) seed.2) ≤
      4 * (4 * rejectionRate f (decodedTable d f) + 1 / Fintype.card F) / ε := by
  have hnonneg := rejectionRate_nonneg f (decodedTable d f)
  have hcard : 3 * d ≤ Fintype.card F := by
    have h := (BivariateAgreement.fieldSize_bounds hd hq).2.2.2.2
    omega
  have hmean (j : Fin 4) :
      (𝔼 seed : MixedSeed F σ,
        ProbabilisticCrossing.errors d (mixedGrid f u seed) t seed.2.2 j) ≤
          4 * rejectionRate f (decodedTable d f) + 1 / Fintype.card F := by
    simp only [crossing_errors_eq]
    fin_cases j
    · have h := expect_mixedRowError_le f (decodedTable d f) u
      exact h.trans (by linarith)
    · have h := expect_mixedColumnError_le f (decodedTable d f) u
      exact h.trans (by linarith)
    · exact expect_mixedLocalRowError_decoded_le d f u t hcard
    · have h := expect_mixedLocalColumnError_le f (decodedTable d f) u
      exact h.trans (by linarith)
  have h := ProbabilisticCrossing.fraction_disagreement_le hd hq (mixedGrid f u)
    (fun _ => t) (fun seed => seed.2.2) hε hεsmall hsmall hmean
  simpa only [crossing_row_prediction, crossing_column_prediction, ne_comm] using h

/-- The actual corrected function agrees with almost all predictions
at every fixed line parameter. -/
theorem endpoint_error_le (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F) (f : (σ → F) → F) (u : σ → F) (t : F)
    {ε : ℚ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2) :
    relativeDistance (fun v => (decodedTable d f (u, v)).val.eval t)
      (fun v => correction (decodedTable d f) (point u v t)) ≤
        8 * (4 * rejectionRate f (decodedTable d f) + 1 / Fintype.card F) / ε := by
  have h := fraction_endpoint_disagreement_le hd hq f u t hε hεsmall hsmall
  rw [fraction_ne_eq_relativeDistance] at h
  have hm := Plurality.distance_le_twice_prediction_error
    (fun v => prediction (decodedTable d f) (point u v t))
    (fun v => (decodedTable d f (u, v)).val.eval t)
  change relativeDistance (fun v => (decodedTable d f (u, v)).val.eval t)
    (fun v => correction (decodedTable d f) (point u v t)) ≤ _ at hm
  calc
    _ ≤ _ := hm
    _ ≤ 2 * (4 * (4 * rejectionRate f (decodedTable d f) + 1 / Fintype.card F) / ε) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end PCP.Algebraic.PointLineEndpointConsistency
