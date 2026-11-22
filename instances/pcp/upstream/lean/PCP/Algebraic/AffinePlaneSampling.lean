/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointedLineSampling
import PCP.Algebraic.PointLineDecoder
import PCP.Algebraic.PointLineCorrection

/-!
# Normalized sampling on affine planes

The sampled grid is `u+s*v+t*w`, with all centers, directions and parameters
included. Explicit changes of variables identify its rows and columns with the
actual parametrized affine-line tester. Fixed-center estimates retain the
exceptional zero slice and its `1/|F|` contribution.

Errors against whole line polynomials and errors at one fixed line parameter
are distinguished. No covariance of a table or of nearest-polynomial choices
under reparametrization is assumed.
-/

namespace PCP.Algebraic.AffinePlaneSampling

open Finset PolynomialLine AffineLineSampling PointedLineSampling PointLineTest
open scoped BigOperators

variable {F σ : Type*} [Field F]

/-- A parametrized affine plane, including dependent and zero directions. -/
def planePoint (u v w : σ → F) (s t : F) : σ → F := u + s • v + t • w

/-- Fix the first parameter and vary the second. -/
def rowLine (u v w : σ → F) (s : F) : (σ → F) × (σ → F) :=
  (point u v s, w)

/-- Fix the second parameter and vary the first. -/
def columnLine (u v w : σ → F) (t : F) : (σ → F) × (σ → F) :=
  (point u w t, v)

theorem planePoint_eq_row (u v w : σ → F) (s t : F) :
    planePoint u v w s t = point (rowLine u v w s).1 (rowLine u v w s).2 t := rfl

theorem planePoint_eq_column (u v w : σ → F) (s t : F) :
    planePoint u v w s t = point (columnLine u v w t).1 (columnLine u v w t).2 s := by
  simp only [planePoint, columnLine, point]
  abel

/-- Exchange the two plane parameters and their directions. -/
theorem planePoint_swap (u v w : σ → F) (s t : F) :
    planePoint u v w s t = planePoint u w v t s := by
  simp only [planePoint]
  abel

/-- A row and the unused first direction bijectively encode the original plane seed. -/
def rowSamplesEquiv (s : F) : ((σ → F) × ((σ → F) × (σ → F))) ≃
    (((σ → F) × (σ → F)) × (σ → F)) where
  toFun uvw := (rowLine uvw.1 uvw.2.1 uvw.2.2 s, uvw.2.1)
  invFun p := (p.1.1 - s • p.2, (p.2, p.1.2))
  left_inv uvw := by simp [rowLine, point]
  right_inv p := by simp [rowLine, point]

/-- A column and the unused second direction bijectively encode the original plane seed. -/
def columnSamplesEquiv (t : F) : ((σ → F) × ((σ → F) × (σ → F))) ≃
    (((σ → F) × (σ → F)) × (σ → F)) where
  toFun uvw := (columnLine uvw.1 uvw.2.1 uvw.2.2 t, uvw.2.2)
  invFun p := (p.1.1 - t • p.2, (p.1.2, p.2))
  left_inv uvw := by simp [columnLine, point]
  right_inv p := by simp [columnLine, point]

/-- Independent directions and offsets for a plane through one fixed point. -/
abbrev ShiftSeed (F σ : Type*) := ((σ → F) × F) × ((σ → F) × F)

/-- The crossing at the two sampled offsets is exactly `x`. -/
def shiftPlanePoint (x : σ → F) (seed : ShiftSeed F σ) (y z : F) : σ → F :=
  x + (y - seed.1.2) • seed.1.1 + (z - seed.2.2) • seed.2.1

/-- The actual center/direction of a shifted row, parametrized by the second coordinate. -/
def shiftRowLine (x : σ → F) (seed : ShiftSeed F σ) (y : F) :
    (σ → F) × (σ → F) :=
  (x + (y - seed.1.2) • seed.1.1 - seed.2.2 • seed.2.1, seed.2.1)

/-- The actual center/direction of a shifted column, parametrized by the first coordinate. -/
def shiftColumnLine (x : σ → F) (seed : ShiftSeed F σ) (z : F) :
    (σ → F) × (σ → F) :=
  (x + (z - seed.2.2) • seed.2.1 - seed.1.2 • seed.1.1, seed.1.1)

theorem shiftPlanePoint_eq_row (x : σ → F) (seed : ShiftSeed F σ) (y z : F) :
    shiftPlanePoint x seed y z =
      point (shiftRowLine x seed y).1 (shiftRowLine x seed y).2 z := by
  simp only [shiftPlanePoint, shiftRowLine, point, sub_smul]
  abel

theorem shiftPlanePoint_eq_column (x : σ → F) (seed : ShiftSeed F σ) (y z : F) :
    shiftPlanePoint x seed y z =
      point (shiftColumnLine x seed z).1 (shiftColumnLine x seed z).2 y := by
  simp only [shiftPlanePoint, shiftColumnLine, point, sub_smul]
  abel

@[simp] theorem shiftPlanePoint_crossing (x : σ → F) (seed : ShiftSeed F σ) :
    shiftPlanePoint x seed seed.1.2 seed.2.2 = x := by
  simp [shiftPlanePoint]

theorem shiftPlanePoint_swap (x : σ → F) (seed : ShiftSeed F σ) (y z : F) :
    shiftPlanePoint x seed y z = shiftPlanePoint x seed.swap z y := by
  simp only [shiftPlanePoint, Prod.fst_swap, Prod.snd_swap]
  abel

private theorem expect_pair {A B : Type*} [Fintype A] [Fintype B] (h : A × B → ℚ) :
    (𝔼 ab, h ab) = 𝔼 a, 𝔼 b, h (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ h

section Finite

variable [Fintype F] [Fintype σ] [DecidableEq σ]

/-- For each parameter, a row of a uniformly random plane is a uniform parametrized line. -/
theorem expect_rowLine (h : ((σ → F) × (σ → F)) → ℚ) (s : F) :
    (𝔼 uvw : (σ → F) × ((σ → F) × (σ → F)),
      h (rowLine uvw.1 uvw.2.1 uvw.2.2 s)) = 𝔼 uv, h uv := by
  classical
  calc
    _ = 𝔼 p : ((σ → F) × (σ → F)) × (σ → F), h p.1 :=
      Fintype.expect_equiv (rowSamplesEquiv s) _ _ (fun _ => rfl)
    _ = _ := by
      rw [← univ_product_univ, expect_product]
      simp only [Fintype.expect_const]

/-- The same uniform-line identity holds for columns. -/
theorem expect_columnLine (h : ((σ → F) × (σ → F)) → ℚ) (t : F) :
    (𝔼 uvw : (σ → F) × ((σ → F) × (σ → F)),
      h (columnLine uvw.1 uvw.2.1 uvw.2.2 t)) = 𝔼 uv, h uv := by
  classical
  calc
    _ = 𝔼 p : ((σ → F) × (σ → F)) × (σ → F), h p.1 :=
      Fintype.expect_equiv (columnSamplesEquiv t) _ _ (fun _ => rfl)
    _ = _ := by
      rw [← univ_product_univ, expect_product]
      simp only [Fintype.expect_const]

/-- Average a quantity over all rows of one parametrized plane. -/
def rowMean (h : ((σ → F) × (σ → F)) → ℚ) (u v w : σ → F) : ℚ :=
  𝔼 s, h (rowLine u v w s)

/-- Average a quantity over all columns of one parametrized plane. -/
def columnMean (h : ((σ → F) × (σ → F)) → ℚ) (u v w : σ → F) : ℚ :=
  𝔼 t, h (columnLine u v w t)

omit [Fintype σ] [DecidableEq σ] in
theorem columnMean_eq_rowMean_swap (h : ((σ → F) × (σ → F)) → ℚ) (u v w : σ → F) :
    columnMean h u v w = rowMean h u w v := rfl

/-- Mean row quantities exactly recover their global mean over parametrized lines. -/
theorem expect_rowMean (h : ((σ → F) × (σ → F)) → ℚ) :
    (𝔼 uvw : (σ → F) × ((σ → F) × (σ → F)), rowMean h uvw.1 uvw.2.1 uvw.2.2) =
      𝔼 uv, h uv := by
  simp only [rowMean]
  rw [expect_comm]
  simp only [expect_rowLine, Fintype.expect_const]

/-- Mean column quantities exactly recover their global mean over parametrized lines. -/
theorem expect_columnMean (h : ((σ → F) × (σ → F)) → ℚ) :
    (𝔼 uvw : (σ → F) × ((σ → F) × (σ → F)), columnMean h uvw.1 uvw.2.1 uvw.2.2) =
      𝔼 uv, h uv := by
  simp only [columnMean]
  rw [expect_comm]
  simp only [expect_columnLine, Fintype.expect_const]

/-- Away from the zero slice, even a fixed-center plane supplies a uniform row line. -/
theorem expect_fixed_rowLine_of_ne (h : ((σ → F) × (σ → F)) → ℚ)
    (u : σ → F) (s : F) (hs : s ≠ 0) :
    (𝔼 vw : (σ → F) × (σ → F), h (rowLine u vw.1 vw.2 s)) = 𝔼 uv, h uv := by
  exact Fintype.expect_equiv
    ((affineSamplingEquiv u s hs).prodCongr (Equiv.refl (σ → F))) _ _ (fun _ => rfl)

/-- Exact mean through a fixed center; the zero row retains its actual contribution. -/
theorem expect_fixed_rowMean (h : ((σ → F) × (σ → F)) → ℚ) (u : σ → F) :
    (𝔼 vw : (σ → F) × (σ → F), rowMean h u vw.1 vw.2) =
      (1 - 1 / Fintype.card F) * (𝔼 uv, h uv) +
        (𝔼 w, h (u, w)) / Fintype.card F := by
  classical
  have hslice (s : F) :
      (𝔼 vw : (σ → F) × (σ → F), h (rowLine u vw.1 vw.2 s)) =
        (𝔼 uv, h uv) + if s = 0 then (𝔼 w, h (u, w)) - (𝔼 uv, h uv) else 0 := by
    by_cases hs : s = 0
    · subst s
      simp only [rowLine, point_zero, ↓reduceIte]
      rw [← univ_product_univ, expect_product]
      simp only [Fintype.expect_const]
      ring
    · rw [expect_fixed_rowLine_of_ne h u s hs, ite_eq_right hs, add_zero]
  simp only [rowMean]
  rw [expect_comm]
  simp only [hslice]
  rw [expect_add_distrib, Fintype.expect_const]
  have he : (𝔼 s : F, if s = 0 then (𝔼 w, h (u, w)) - (𝔼 uv, h uv) else 0) =
      ((𝔼 w, h (u, w)) - (𝔼 uv, h uv)) / Fintype.card F := by
    simp only [Fintype.expect_eq_sum_div_card, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [he]
  ring

/-- Swapping the two random directions yields the same fixed-center column formula. -/
theorem expect_fixed_columnMean (h : ((σ → F) × (σ → F)) → ℚ) (u : σ → F) :
    (𝔼 vw : (σ → F) × (σ → F), columnMean h u vw.1 vw.2) =
      (1 - 1 / Fintype.card F) * (𝔼 uv, h uv) +
        (𝔼 v, h (u, v)) / Fintype.card F := by
  calc
    _ = 𝔼 vw : (σ → F) × (σ → F), rowMean h u vw.1 vw.2 :=
      Fintype.expect_equiv (Equiv.prodComm (σ → F) (σ → F)) _ _ (fun _ => rfl)
    _ = _ := expect_fixed_rowMean h u

/-- A quantity in `[0,1]` loses at most `1/|F|` from the exceptional fixed-center row. -/
theorem expect_fixed_rowMean_le (h : ((σ → F) × (σ → F)) → ℚ)
    (h0 : ∀ uv, 0 ≤ h uv) (h1 : ∀ uv, h uv ≤ 1) (u : σ → F) :
    (𝔼 vw : (σ → F) × (σ → F), rowMean h u vw.1 vw.2) ≤
      (𝔼 uv, h uv) + 1 / Fintype.card F := by
  rw [expect_fixed_rowMean]
  have he0 : (0 : ℚ) ≤ 𝔼 uv, h uv := expect_nonneg (fun uv _ => h0 uv)
  have he1 : (𝔼 w, h (u, w)) ≤ (1 : ℚ) := expect_le univ_nonempty (fun w _ => h1 (u, w))
  have hmul := mul_nonneg (show (0 : ℚ) ≤ 1 / Fintype.card F by positivity) he0
  have hdiv := div_le_div_of_nonneg_right he1 (show (0 : ℚ) ≤ Fintype.card F by positivity)
  nlinarith

/-- The fixed-center column estimate includes the same exceptional contribution. -/
theorem expect_fixed_columnMean_le (h : ((σ → F) × (σ → F)) → ℚ)
    (h0 : ∀ uv, 0 ≤ h uv) (h1 : ∀ uv, h uv ≤ 1) (u : σ → F) :
    (𝔼 vw : (σ → F) × (σ → F), columnMean h u vw.1 vw.2) ≤
      (𝔼 uv, h uv) + 1 / Fintype.card F := by
  rw [expect_fixed_columnMean, ← expect_fixed_rowMean h u]
  exact expect_fixed_rowMean_le h h0 h1 u

/-- Average a line quantity at its sampled parameter across shifted rows. -/
def shiftRowMean (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  𝔼 y, h (shiftRowLine x seed y, seed.2.2)

/-- Average the corresponding line quantity across shifted columns. -/
def shiftColumnMean (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  𝔼 z, h (shiftColumnLine x seed z, seed.1.2)

omit [Fintype σ] [DecidableEq σ] in
theorem shiftColumnMean_eq_rowMean_swap
    (h : (((σ → F) × (σ → F)) × F) → ℚ) (x : σ → F) (seed : ShiftSeed F σ) :
    shiftColumnMean h x seed = shiftRowMean h x seed.swap := rfl

/-- Exact mean over the first direction/offset pair with the second pair held fixed. -/
theorem expect_shiftRowMean_at (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (x : σ → F) (ws : (σ → F) × F) :
    (𝔼 vt : (σ → F) × F, shiftRowMean h x (vt, ws)) =
      (1 - 1 / Fintype.card F) * (𝔼 u, h ((u - ws.2 • ws.1, ws.1), ws.2)) +
        h ((x - ws.2 • ws.1, ws.1), ws.2) / Fintype.card F := by
  have hp (v : σ → F) (t y : F) : point (x - t • v) v y = x + (y - t) • v :=
    point_pointedLine x v t y
  have hm (vt : (σ → F) × F) : shiftRowMean h x (vt, ws) =
      lineAverage (fun u => h ((u - ws.2 • ws.1, ws.1), ws.2))
        (pointedLine x vt.1 vt.2) := by
    simp only [shiftRowMean, shiftRowLine, lineAverage, pointedLine, hp]
  simp only [hm]
  exact PointedLineSampling.expect_lineAverage _ x

/-- Both independent offsets restore the whole-field tester distribution.
The sole exceptional slice keeps its exact pointed-line contribution. -/
theorem expect_shiftRowMean (h : (((σ → F) × (σ → F)) × F) → ℚ) (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftRowMean h x seed) =
      (1 - 1 / Fintype.card F) * (𝔼 uvt, h uvt) +
        (𝔼 ws : (σ → F) × F, h ((x - ws.2 • ws.1, ws.1), ws.2)) / Fintype.card F := by
  rw [expect_pair, expect_comm]
  simp only [expect_shiftRowMean_at]
  rw [expect_add_distrib, ← mul_expect, ← expect_div]
  have hglobal : (𝔼 ws : (σ → F) × F, 𝔼 u, h ((u - ws.2 • ws.1, ws.1), ws.2)) =
      𝔼 uvt, h uvt := by
    rw [expect_comm, ← expect_pair
      (fun p : (σ → F) × ((σ → F) × F) => h ((p.1 - p.2.2 • p.2.1, p.2.1), p.2.2))]
    exact Fintype.expect_equiv (predictionSamplesEquiv (F := F) (σ := σ))
      _ _ (fun _ => rfl)
  rw [hglobal]

/-- The same exact formula holds after exchanging the two direction/offset pairs. -/
theorem expect_shiftColumnMean (h : (((σ → F) × (σ → F)) × F) → ℚ) (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftColumnMean h x seed) =
      (1 - 1 / Fintype.card F) * (𝔼 uvt, h uvt) +
        (𝔼 vt : (σ → F) × F, h ((x - vt.2 • vt.1, vt.1), vt.2)) / Fintype.card F := by
  calc
    _ = 𝔼 seed : ShiftSeed F σ, shiftRowMean h x seed :=
      Fintype.expect_equiv (Equiv.prodComm ((σ → F) × F) ((σ → F) × F)) _ _
        (fun _ => rfl)
    _ = _ := expect_shiftRowMean h x

/-- A shifted row quantity in `[0,1]` has mean at most its global mean plus `1/|F|`. -/
theorem expect_shiftRowMean_le (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (h0 : ∀ uvt, 0 ≤ h uvt) (h1 : ∀ uvt, h uvt ≤ 1) (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftRowMean h x seed) ≤
      (𝔼 uvt, h uvt) + 1 / Fintype.card F := by
  rw [expect_shiftRowMean]
  have he0 : (0 : ℚ) ≤ 𝔼 uvt, h uvt := expect_nonneg (fun uvt _ => h0 uvt)
  have he1 : (𝔼 ws : (σ → F) × F, h ((x - ws.2 • ws.1, ws.1), ws.2)) ≤ (1 : ℚ) :=
    expect_le univ_nonempty (fun ws _ => h1 _)
  have hmul := mul_nonneg (show (0 : ℚ) ≤ 1 / Fintype.card F by positivity) he0
  have hdiv := div_le_div_of_nonneg_right he1 (show (0 : ℚ) ≤ Fintype.card F by positivity)
  nlinarith

/-- The shifted column estimate has the same normalized exceptional-slice contribution. -/
theorem expect_shiftColumnMean_le (h : (((σ → F) × (σ → F)) × F) → ℚ)
    (h0 : ∀ uvt, 0 ≤ h uvt) (h1 : ∀ uvt, h uvt ≤ 1) (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftColumnMean h x seed) ≤
      (𝔼 uvt, h uvt) + 1 / Fintype.card F := by
  rw [expect_shiftColumnMean, ← expect_shiftRowMean h x]
  exact expect_shiftRowMean_le h h0 h1 x

section Errors

variable [DecidableEq F] {c : ℕ}

/-- The error fraction of one actual table polynomial on its parametrized line. -/
def lineError (f : (σ → F) → F) (table : LineTable F σ c)
    (uv : (σ → F) × (σ → F)) : ℚ :=
  relativeDistance (fun t => f (point uv.1 uv.2 t)) (table uv).val.eval

/-- The indicator of the actual point-versus-line rejection event. -/
noncomputable def pointError (f : (σ → F) → F) (table : LineTable F σ c)
    (uvt : ((σ → F) × (σ → F)) × F) : ℚ := by
  classical
  exact if f (point uvt.1.1 uvt.1.2 uvt.2) ≠ (table uvt.1).val.eval uvt.2 then 1 else 0

omit [Fintype F] [Fintype σ] [DecidableEq σ] in
theorem pointError_nonneg (f : (σ → F) → F) (table : LineTable F σ c)
    (uvt : ((σ → F) × (σ → F)) × F) : 0 ≤ pointError f table uvt := by
  unfold pointError
  split_ifs <;> norm_num

omit [Fintype F] [Fintype σ] [DecidableEq σ] in
theorem pointError_le_one (f : (σ → F) → F) (table : LineTable F σ c)
    (uvt : ((σ → F) × (σ → F)) × F) : pointError f table uvt ≤ 1 := by
  unfold pointError
  split_ifs <;> norm_num

theorem expect_lineError (f : (σ → F) → F) (table : LineTable F σ c) :
    (𝔼 uv, lineError f table uv) = rejectionRate f table := by
  rw [rejectionRate_eq_relativeDistance, relativeDistance_prod,
    Fintype.expect_eq_sum_div_card]
  rfl

theorem expect_lineError_unused_parameter (f : (σ → F) → F) (table : LineTable F σ c) :
    (𝔼 uvt : ((σ → F) × (σ → F)) × F, lineError f table uvt.1) =
      rejectionRate f table := by
  rw [expect_pair]
  simp only [Fintype.expect_const, expect_lineError]

theorem expect_pointError (f : (σ → F) → F) (table : LineTable F σ c) :
    (𝔼 uvt, pointError f table uvt) = rejectionRate f table := by
  rw [rejectionRate_eq_relativeDistance]
  change (𝔼 uvt : ((σ → F) × (σ → F)) × F, if f (point uvt.1.1 uvt.1.2 uvt.2) ≠
    (table uvt.1).val.eval uvt.2 then (1 : ℚ) else 0) = _
  rw [← fraction_eq_expect]
  exact fraction_ne_eq_relativeDistance
    (fun uvt : ((σ → F) × (σ → F)) × F => f (point uvt.1.1 uvt.1.2 uvt.2))
    (fun uvt => (table uvt.1).val.eval uvt.2)

/-- Global row error of the actual shifted plane against the actual lines table. -/
def shiftRowError (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  relativeDistance (fun yz : F × F => f (shiftPlanePoint x seed yz.1 yz.2))
    (fun yz => (table (shiftRowLine x seed yz.1)).val.eval yz.2)

/-- Global column error of the actual shifted plane. -/
def shiftColumnError (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  relativeDistance (fun yz : F × F => f (shiftPlanePoint x seed yz.1 yz.2))
    (fun yz => (table (shiftColumnLine x seed yz.2)).val.eval yz.1)

/-- Error of transverse column predictions along the row through the designated crossing. -/
def shiftLocalRowError (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  relativeDistance (fun z => f (shiftPlanePoint x seed seed.1.2 z))
    (fun z => (table (shiftColumnLine x seed z)).val.eval seed.1.2)

/-- Error of transverse row predictions along the column through the designated crossing. -/
def shiftLocalColumnError (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) : ℚ :=
  relativeDistance (fun y => f (shiftPlanePoint x seed y seed.2.2))
    (fun y => (table (shiftRowLine x seed y)).val.eval seed.2.2)

omit [Fintype σ] [DecidableEq σ] in
theorem shiftRowError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) :
    shiftRowError f table x seed = shiftRowMean (fun uvt => lineError f table uvt.1) x seed := by
  simp only [shiftRowError, relativeDistance_prod, shiftRowMean,
    Fintype.expect_eq_sum_div_card, lineError, shiftPlanePoint_eq_row]

omit [Fintype σ] [DecidableEq σ] in
theorem shiftColumnError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) :
    shiftColumnError f table x seed =
      shiftColumnMean (fun uvt => lineError f table uvt.1) x seed := by
  have h := relativeDistance_comp_equiv (Equiv.prodComm F F)
    (fun yz : F × F => f (shiftPlanePoint x seed yz.1 yz.2))
    (fun yz => (table (shiftColumnLine x seed yz.2)).val.eval yz.1)
  rw [shiftColumnError, ← h, relativeDistance_prod]
  simp only [shiftColumnMean, Fintype.expect_eq_sum_div_card, lineError,
    shiftPlanePoint_eq_column, Equiv.prodComm_apply, Prod.swap_prod_mk]

omit [Fintype σ] [DecidableEq σ] in
theorem shiftLocalColumnError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) :
    shiftLocalColumnError f table x seed = shiftRowMean (pointError f table) x seed := by
  rw [shiftLocalColumnError, ← fraction_ne_eq_relativeDistance, fraction_eq_expect]
  simp only [shiftRowMean, pointError, shiftPlanePoint_eq_row]

omit [Fintype σ] [DecidableEq σ] in
theorem shiftLocalRowError_eq_mean (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) (seed : ShiftSeed F σ) :
    shiftLocalRowError f table x seed = shiftColumnMean (pointError f table) x seed := by
  rw [shiftLocalRowError, ← fraction_ne_eq_relativeDistance, fraction_eq_expect]
  simp only [shiftColumnMean, pointError, shiftPlanePoint_eq_column]

/-- Average shifted-plane row error is at most global rejection plus the exceptional slice. -/
theorem expect_shiftRowError_le (f : (σ → F) → F) (table : LineTable F σ c) (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftRowError f table x seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← shiftRowError_eq_mean, expect_lineError_unused_parameter] using
    expect_shiftRowMean_le (fun uvt => lineError f table uvt.1)
      (fun _ => relativeDistance_nonneg _ _) (fun _ => relativeDistance_le_one _ _) x

/-- The corresponding global column-error estimate. -/
theorem expect_shiftColumnError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftColumnError f table x seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← shiftColumnError_eq_mean, expect_lineError_unused_parameter] using
    expect_shiftColumnMean_le (fun uvt => lineError f table uvt.1)
      (fun _ => relativeDistance_nonneg _ _) (fun _ => relativeDistance_le_one _ _) x

/-- Independent offsets give the actual whole-parameter distribution for local transverse errors. -/
theorem expect_shiftLocalColumnError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftLocalColumnError f table x seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← shiftLocalColumnError_eq_mean, expect_pointError] using
    expect_shiftRowMean_le (pointError f table) (pointError_nonneg f table)
      (pointError_le_one f table) x

/-- The local transverse row estimate also needs no covariance assumption on the table. -/
theorem expect_shiftLocalRowError_le (f : (σ → F) → F) (table : LineTable F σ c)
    (x : σ → F) :
    (𝔼 seed : ShiftSeed F σ, shiftLocalRowError f table x seed) ≤
      rejectionRate f table + 1 / Fintype.card F := by
  simpa only [← shiftLocalRowError_eq_mean, expect_pointError] using
    expect_shiftColumnMean_le (pointError f table) (pointError_nonneg f table)
      (pointError_le_one f table) x

end Errors

end Finite

end PCP.Algebraic.AffinePlaneSampling
