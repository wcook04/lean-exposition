/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.AffinePlaneSampling
import PCP.Algebraic.PointLineParameterError

/-!
# Mixed affine-plane sampling

One plane direction has a fixed parameter origin, while the transverse direction
has an independent uniform offset. Three mean errors recover all-parameter
rejection, up to the exceptional slice. The fourth uses the genuine fixed-parameter
error bound for the decoded table; covariance of arbitrary tied choices is not assumed.
-/

namespace PCP.Algebraic.MixedPlaneSampling

open Finset PolynomialLine AffineLineSampling PointedLineSampling PointLineTest
open AffinePlaneSampling
open scoped BigOperators

variable {F σ : Type*} [Field F]

/-- One direction and an independently shifted transverse direction. -/
abbrev MixedSeed (F σ : Type*) := (σ → F) × ((σ → F) × F)

/-- The crossing at `(t,s)` lies at `u+t*v`. -/
def mixedPlanePoint (u : σ → F) (seed : MixedSeed F σ) (y z : F) : σ → F :=
  u + y • seed.1 + (z - seed.2.2) • seed.2.1

/-- Actual parametrized row, varying the second plane coordinate. -/
def mixedRowLine (u : σ → F) (seed : MixedSeed F σ) (y : F) :
    (σ → F) × (σ → F) := (u + y • seed.1 - seed.2.2 • seed.2.1, seed.2.1)

/-- Actual parametrized column, varying the first plane coordinate. -/
def mixedColumnLine (u : σ → F) (seed : MixedSeed F σ) (z : F) :
    (σ → F) × (σ → F) := (u + (z - seed.2.2) • seed.2.1, seed.1)

theorem mixedPlanePoint_eq_row (u : σ → F) (seed : MixedSeed F σ) (y z : F) :
    mixedPlanePoint u seed y z =
      point (mixedRowLine u seed y).1 (mixedRowLine u seed y).2 z := by
  simp only [mixedPlanePoint, mixedRowLine, point, sub_smul]
  abel

theorem mixedPlanePoint_eq_column (u : σ → F) (seed : MixedSeed F σ) (y z : F) :
    mixedPlanePoint u seed y z =
      point (mixedColumnLine u seed z).1 (mixedColumnLine u seed z).2 y := by
  simp only [mixedPlanePoint, mixedColumnLine, point]
  abel

@[simp] theorem mixedPlanePoint_crossing (u : σ → F) (seed : MixedSeed F σ) (t : F) :
    mixedPlanePoint u seed t seed.2.2 = point u seed.1 t := by
  simp [mixedPlanePoint, point]

private theorem expect_pair {A B : Type*} [Fintype A] [Fintype B] (h : A × B → ℚ) :
    (𝔼 ab, h ab) = 𝔼 a, 𝔼 b, h (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ h

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- Mean row quantity, evaluated at the independent transverse offset. -/
def mixedRowMean (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (u : σ → F) (seed : MixedSeed F σ) : ℚ :=
  𝔼 y, h (mixedRowLine u seed y, seed.2.2)

/-- Mean column quantity, allowing an arbitrary fixed-parameter error as input. -/
def mixedColumnMean (h : ((σ → F) × (σ → F)) → ℚ)
    (u : σ → F) (seed : MixedSeed F σ) : ℚ :=
  𝔼 z, h (mixedColumnLine u seed z)

/-- Exact first-direction mean, including the exceptional zero slice. -/
theorem expect_mixedRowMean_at (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (u : σ → F) (ws : (σ → F) × F) :
    (𝔼 v, mixedRowMean h u (v, ws)) =
      (1 - 1 / Fintype.card F) * (𝔼 x, h ((x - ws.2 • ws.1, ws.1), ws.2)) +
        h ((u - ws.2 • ws.1, ws.1), ws.2) / Fintype.card F := by
  simpa only [mixedRowMean, mixedRowLine, lineAverage, pointedLine, zero_smul,
    sub_zero, point] using
    expect_lineAverage_at (fun x => h ((x - ws.2 • ws.1, ws.1), ws.2)) u (0 : F)

/-- The row mean has the complete tester distribution away from one exceptional slice. -/
theorem expect_mixedRowMean (h : (((σ → F) × (σ → F)) × F) → ℚ) (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedRowMean h u seed) =
      (1 - 1 / Fintype.card F) * (𝔼 uvt, h uvt) +
        (𝔼 ws : (σ → F) × F, h ((u - ws.2 • ws.1, ws.1), ws.2)) /
          Fintype.card F := by
  rw [expect_pair, expect_comm]
  simp only [expect_mixedRowMean_at]
  rw [expect_add_distrib, ← mul_expect, ← expect_div]
  have hglobal : (𝔼 ws : (σ → F) × F, 𝔼 x, h ((x - ws.2 • ws.1, ws.1), ws.2)) =
      𝔼 uvt, h uvt := by
    rw [expect_comm, ← expect_pair
      (fun p : (σ → F) × ((σ → F) × F) => h ((p.1 - p.2.2 • p.2.1, p.2.1), p.2.2))]
    exact Fintype.expect_equiv (predictionSamplesEquiv (F := F) (σ := σ))
      _ _ (fun _ => rfl)
  rw [hglobal]

/-- Exact column mean over the independently shifted transverse direction. -/
theorem expect_mixedColumnMean (h : ((σ → F) × (σ → F)) → ℚ) (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedColumnMean h u seed) =
      (1 - 1 / Fintype.card F) * (𝔼 uv, h uv) +
        (𝔼 v, h (u, v)) / Fintype.card F := by
  have hm (v : σ → F) (ws : (σ → F) × F) : mixedColumnMean h u (v, ws) =
      lineAverage (fun x => h (x, v)) (pointedLine u ws.1 ws.2) := by
    simp only [mixedColumnMean, mixedColumnLine, lineAverage, point_pointedLine]
  rw [expect_pair]
  simp only [hm, PointedLineSampling.expect_lineAverage]
  rw [expect_add_distrib, ← mul_expect, ← expect_div]
  congr 2
  rw [expect_comm, ← expect_pair h]

/-- A bounded row quantity loses at most `1/|F|` in its normalized mean. -/
theorem expect_mixedRowMean_le (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (h0 : ∀ uvt, 0 ≤ h uvt) (h1 : ∀ uvt, h uvt ≤ 1) (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedRowMean h u seed) ≤
      (𝔼 uvt, h uvt) + 1 / Fintype.card F := by
  rw [expect_mixedRowMean]
  have he0 : (0 : ℚ) ≤ 𝔼 uvt, h uvt := expect_nonneg (fun uvt _ => h0 uvt)
  have he1 : (𝔼 ws : (σ → F) × F, h ((u - ws.2 • ws.1, ws.1), ws.2)) ≤ (1 : ℚ) :=
    expect_le univ_nonempty (fun ws _ => h1 _)
  have hmul := mul_nonneg (show (0 : ℚ) ≤ 1 / Fintype.card F by positivity) he0
  have hdiv := div_le_div_of_nonneg_right he1 (show (0 : ℚ) ≤ Fintype.card F by positivity)
  nlinarith

/-- The column estimate applies to whole-line errors and to fixed-parameter errors alike. -/
theorem expect_mixedColumnMean_le (h : ((σ → F) × (σ → F)) → ℚ)
    (h0 : ∀ uv, 0 ≤ h uv) (h1 : ∀ uv, h uv ≤ 1) (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedColumnMean h u seed) ≤
      (𝔼 uv, h uv) + 1 / Fintype.card F := by
  rw [expect_mixedColumnMean, ← expect_fixed_rowMean h u]
  exact expect_fixed_rowMean_le h h0 h1 u

section Errors

variable [DecidableEq F] {c : ℕ}

/-- Global error against actual row polynomials. -/
def mixedRowError (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) : ℚ :=
  relativeDistance (fun yz : F × F => f (mixedPlanePoint u seed yz.1 yz.2))
    (fun yz => (table (mixedRowLine u seed yz.1)).val.eval yz.2)

/-- Global error against actual column polynomials. -/
def mixedColumnError (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) : ℚ :=
  relativeDistance (fun yz : F × F => f (mixedPlanePoint u seed yz.1 yz.2))
    (fun yz => (table (mixedColumnLine u seed yz.2)).val.eval yz.1)

/-- Transverse column predictions along the row through `(t,s)`. -/
def mixedLocalRowError (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (t : F) (seed : MixedSeed F σ) : ℚ :=
  relativeDistance (fun z => f (mixedPlanePoint u seed t z))
    (fun z => (table (mixedColumnLine u seed z)).val.eval t)

/-- Transverse row predictions along the column through `(t,s)`. -/
def mixedLocalColumnError (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) : ℚ :=
  relativeDistance (fun y => f (mixedPlanePoint u seed y seed.2.2))
    (fun y => (table (mixedRowLine u seed y)).val.eval seed.2.2)

omit [Fintype σ] [DecidableEq σ] in
theorem mixedRowError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) :
    mixedRowError f table u seed = mixedRowMean (fun uvt => lineError f table uvt.1) u seed := by
  simp only [mixedRowError, relativeDistance_prod, mixedRowMean,
    Fintype.expect_eq_sum_div_card, lineError, mixedPlanePoint_eq_row]

omit [Fintype σ] [DecidableEq σ] in
theorem mixedColumnError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) :
    mixedColumnError f table u seed = mixedColumnMean (lineError f table) u seed := by
  have h := relativeDistance_comp_equiv (Equiv.prodComm F F)
    (fun yz : F × F => f (mixedPlanePoint u seed yz.1 yz.2))
    (fun yz => (table (mixedColumnLine u seed yz.2)).val.eval yz.1)
  rw [mixedColumnError, ← h, relativeDistance_prod]
  simp only [mixedColumnMean, Fintype.expect_eq_sum_div_card, lineError,
    mixedPlanePoint_eq_column, Equiv.prodComm_apply, Prod.swap_prod_mk]

omit [Fintype σ] [DecidableEq σ] in
theorem mixedLocalColumnError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (seed : MixedSeed F σ) :
    mixedLocalColumnError f table u seed = mixedRowMean (pointError f table) u seed := by
  rw [mixedLocalColumnError, ← fraction_ne_eq_relativeDistance, fraction_eq_expect]
  simp only [mixedRowMean, pointError, mixedPlanePoint_eq_row]

omit [Fintype σ] [DecidableEq σ] in
theorem mixedLocalRowError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (t : F) (seed : MixedSeed F σ) :
    mixedLocalRowError f table u t seed =
      mixedColumnMean (fun uv => pointError f table (uv, t)) u seed := by
  rw [mixedLocalRowError, ← fraction_ne_eq_relativeDistance, fraction_eq_expect]
  simp only [mixedColumnMean, pointError, mixedPlanePoint_eq_column]

/-- Global mixed-plane row error has the all-parameter rejection mean. -/
theorem expect_mixedRowError_le (f : (σ → F) → F) (table : LineTable F σ c) (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedRowError f table u seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← mixedRowError_eq_mean, expect_lineError_unused_parameter] using
    expect_mixedRowMean_le (fun uvt => lineError f table uvt.1)
      (fun _ => relativeDistance_nonneg _ _) (fun _ => relativeDistance_le_one _ _) u

/-- Global mixed-plane column error has the same normalized bound. -/
theorem expect_mixedColumnError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedColumnError f table u seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← mixedColumnError_eq_mean, expect_lineError] using
    expect_mixedColumnMean_le (lineError f table)
      (fun _ => relativeDistance_nonneg _ _) (fun _ => relativeDistance_le_one _ _) u

/-- The random transverse offset also supplies the all-parameter local column mean. -/
theorem expect_mixedLocalColumnError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) :
    (𝔼 seed : MixedSeed F σ, mixedLocalColumnError f table u seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← mixedLocalColumnError_eq_mean, expect_pointError] using
    expect_mixedRowMean_le (pointError f table) (pointError_nonneg f table)
      (pointError_le_one f table) u

/-- The remaining local mean uses the actual fixed parameter, with no covariance assumption. -/
theorem expect_mixedLocalRowError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (u : σ → F) (t : F) :
    (𝔼 seed : MixedSeed F σ, mixedLocalRowError f table u t seed) ≤
      relativeDistance (fun uv : (σ → F) × (σ → F) => f (point uv.1 uv.2 t))
        (fun uv => (table uv).val.eval t) + 1 / Fintype.card F := by
  have he : (𝔼 uv : (σ → F) × (σ → F), pointError f table (uv, t)) =
      relativeDistance (fun uv : (σ → F) × (σ → F) => f (point uv.1 uv.2 t))
        (fun uv => (table uv).val.eval t) := by
    change (𝔼 uv : (σ → F) × (σ → F),
      if f (point uv.1 uv.2 t) ≠ (table uv).val.eval t then (1 : ℚ) else 0) = _
    rw [← fraction_eq_expect]
    exact fraction_ne_eq_relativeDistance _ _
  simpa only [← mixedLocalRowError_eq_mean, he] using
    expect_mixedColumnMean_le (fun uv => pointError f table (uv, t))
      (fun uv => pointError_nonneg f table (uv, t))
      (fun uv => pointError_le_one f table (uv, t)) u

/-- The actual decoded table controls the fixed-parameter mean by four times rejection. -/
theorem expect_mixedLocalRowError_decoded_le (c : ℕ) (f : (σ → F) → F)
    (u : σ → F) (t : F) (hcard : 3 * c ≤ Fintype.card F) :
    (𝔼 seed : MixedSeed F σ, mixedLocalRowError f (decodedTable c f) u t seed) ≤
      4 * rejectionRate f (decodedTable c f) + 1 / Fintype.card F :=
  (expect_mixedLocalRowError_le f (decodedTable c f) u t).trans
    (add_le_add (rejectionAt_le_four_mul c f t hcard) le_rfl)

end Errors
end Finite
end PCP.Algebraic.MixedPlaneSampling
