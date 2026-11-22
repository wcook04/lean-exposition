/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.AffinePlaneSampling

/-!
# Sampling the modified ruled surface

For a fixed target line `x+y*h`, the two uniform directions `v,w` give
`x+y*h+z*(v+y*w)`. Its zero column is replaced by the target function `g`.
All expectation identities below use actual finite sampling, including zero
directions and parameters; the exceptional zero column costs `1/|F|`.
-/

namespace PCP.Algebraic.RuledSurface

open Finset PolynomialLine PointLineTest AffineLineSampling AffinePlaneSampling
open scoped BigOperators

section Averaging

variable {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq K]

theorem relativeDistance_eq_expect (f g : A → K) :
    relativeDistance f g = 𝔼 a, if f a ≠ g a then (1 : ℚ) else 0 := by
  rw [← fraction_ne_eq_relativeDistance, fraction_eq_expect]

theorem expect_relativeDistance_swap (f g : A → B → K) :
    (𝔼 a, relativeDistance (f a) (g a)) =
      𝔼 b, relativeDistance (fun a => f a b) (fun a => g a b) := by
  simp only [relativeDistance_eq_expect]
  rw [expect_comm]

theorem relativeDistance_prod_eq_expect (f g : A × B → K) :
    relativeDistance f g = 𝔼 a, relativeDistance (fun b => f (a, b)) (fun b => g (a, b)) := by
  rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]

end Averaging

variable {F σ : Type*} [Field F]

/-- The two actual sampled directions; no independence among derived errors is asserted. -/
abbrev Seed (F σ : Type*) := (σ → F) × (σ → F)

def directionEquiv (y : F) : Seed F σ ≃ Seed F σ where
  toFun s := (s.1 + y • s.2, s.2)
  invFun s := (s.1 - y • s.2, s.2)
  left_inv s := by simp
  right_inv s := by simp

theorem ruledPoint_eq_column (x h v w : σ → F) (y z : F) :
    point (point x h y) (v + y • w) z = point (point x v z) (point h w z) y := by
  ext i
  simp only [point_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [DecidableEq F] {d : ℕ}

/-- The target line is substituted at `z=0`; every other entry is read from `f`. -/
def surface (f g : (σ → F) → F) (x h : σ → F) (s : Seed F σ) (yz : F × F) : F :=
  if yz.2 = 0 then g (point x h yz.1)
  else f (point (point x h yz.1) (s.1 + yz.1 • s.2) yz.2)

def rows (T : LineTable F σ d) (x h : σ → F) (s : Seed F σ) (y : F) : Polynomial F :=
  (T (point x h y, s.1 + y • s.2)).val

/-- Only the zero column uses a nearest polynomial to the target line. -/
noncomputable def columns [Fintype F] (g : (σ → F) → F) (T : LineTable F σ d)
    (x h : σ → F) (s : Seed F σ) (z : F) : Polynomial F :=
  if z = 0 then (bestApproximation d (fun y => g (point x h y))).val
  else (T (point x s.1 z, point h s.2 z)).val

omit [DecidableEq F] in
theorem rows_degree (T : LineTable F σ d) (x h : σ → F) (s : Seed F σ) (y : F) :
    (rows T x h s y).natDegree ≤ d := (T _).property

theorem columns_degree [Fintype F] (g : (σ → F) → F) (T : LineTable F σ d)
    (x h : σ → F) (s : Seed F σ) (z : F) : (columns g T x h s z).natDegree ≤ d := by
  unfold columns
  split_ifs
  · exact (bestApproximation d _).property
  · exact (T _).property

@[simp] theorem surface_zero (f g : (σ → F) → F) (x h : σ → F) (s : Seed F σ) (y : F) :
    surface f g x h s (y, 0) = g (point x h y) := by simp [surface]

@[simp] theorem columns_zero [Fintype F] (g : (σ → F) → F) (T : LineTable F σ d)
    (x h : σ → F) (s : Seed F σ) :
    columns g T x h s 0 = (bestApproximation d (fun y => g (point x h y))).val := by
  simp [columns]

theorem surface_of_ne (f g : (σ → F) → F) (x h : σ → F) (s : Seed F σ)
    (y z : F) (hz : z ≠ 0) :
    surface f g x h s (y, z) = f (point (point x s.1 z) (point h s.2 z) y) := by
  simp only [surface, ite_eq_right hz, ruledPoint_eq_column]

variable [Fintype F] [Fintype σ] [DecidableEq σ]

theorem distance_direction (y : F) (f g : (σ → F) → F) :
    relativeDistance (fun s : Seed F σ => f (s.1 + y • s.2))
      (fun s => g (s.1 + y • s.2)) = relativeDistance f g := by
  calc
    _ = relativeDistance (fun s : Seed F σ => f s.1) (fun s => g s.1) :=
      relativeDistance_comp_equiv (directionEquiv y) _ _
    _ = _ := relativeDistance_comp_fst _ _

omit [DecidableEq F] in
theorem expect_scaled_pair (x h : σ → F) (z : F) (hz : z ≠ 0)
    (k : Seed F σ → ℚ) :
    (𝔼 s : Seed F σ, k (point x s.1 z, point h s.2 z)) = 𝔼 uv, k uv :=
  Fintype.expect_equiv
    ((affineSamplingEquiv x z hz).prodCongr (affineSamplingEquiv h z hz)) _ _ (fun _ => rfl)

theorem distance_scaled_pair (x h : σ → F) (z : F) (hz : z ≠ 0)
    (k l : Seed F σ → F) :
    relativeDistance (fun s : Seed F σ => k (point x s.1 z, point h s.2 z))
      (fun s => l (point x s.1 z, point h s.2 z)) = relativeDistance k l :=
  relativeDistance_comp_equiv
    ((affineSamplingEquiv x z hz).prodCongr (affineSamplingEquiv h z hz)) k l

/-- A single exceptional field parameter contributes at most `1/|F|`. -/
theorem expect_le_add_exception (a : F → ℚ) {b : ℚ}
    (h : ∀ z, a z ≤ b + if z = 0 then 1 else 0) :
    (𝔼 z, a z) ≤ b + 1 / Fintype.card F := by
  have hm := expect_le_expect (s := univ) (fun z _ => h z)
  rw [expect_add_distrib, Fintype.expect_const] at hm
  have he : (𝔼 z : F, if z = 0 then (1 : ℚ) else 0) = 1 / Fintype.card F := by
    simp
  rwa [he] at hm

/-- The candidate row's prediction error at a fixed surface entry is controlled
by the endpoint bound and the global distance from `f` to `g`. -/
theorem row_point_error_le (f g : (σ → F) → F) (T : LineTable F σ d)
    {η γ : ℚ} (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (x h : σ → F) (y z : F) :
    relativeDistance (fun s : Seed F σ => surface f g x h s (y, z))
      (fun s => (rows T x h s y).eval z) ≤ γ + η := by
  have hη : 0 ≤ η := (relativeDistance_nonneg f g).trans hnear
  have hend : relativeDistance
      (fun s : Seed F σ => (rows T x h s y).eval z)
      (fun s => g (point (point x h y) (s.1 + y • s.2) z)) ≤ γ := by
    simp only [rows]
    rw [distance_direction y (fun v => (T (point x h y, v)).val.eval z)
      (fun v => g (point (point x h y) v z))]
    simpa only [fraction_ne_eq_relativeDistance] using hendpoint (point x h y) z
  have hdist : relativeDistance (fun s : Seed F σ => surface f g x h s (y, z))
      (fun s => g (point (point x h y) (s.1 + y • s.2) z)) ≤ η := by
    by_cases hz : z = 0
    · subst z
      simpa using hη
    · simp only [surface, ite_eq_right hz]
      rw [distance_direction y (fun v => f (point (point x h y) v z))
        (fun v => g (point (point x h y) v z))]
      exact (relativeDistance_affineSampling (point x h y) z hz f g).le.trans hnear
  have ht := relativeDistance_triangle (fun s : Seed F σ => surface f g x h s (y, z))
    (fun s => g (point (point x h y) (s.1 + y • s.2) z))
    (fun s => (rows T x h s y).eval z)
  rw [relativeDistance_comm
    (fun s : Seed F σ => g (point (point x h y) (s.1 + y • s.2) z))] at ht
  linarith

/-- The error of each selected candidate row has the same uniform mean bound. -/
theorem expect_own_row_error_le (f g : (σ → F) → F) (T : LineTable F σ d)
    {η γ : ℚ} (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (x h : σ → F) (y : F) :
    (𝔼 s : Seed F σ, relativeDistance (fun z => surface f g x h s (y, z))
      (rows T x h s y).eval) ≤ γ + η := by
  rw [expect_relativeDistance_swap]
  exact expect_le univ_nonempty (fun z _ => row_point_error_le f g T hnear hendpoint x h y z)

theorem expect_global_row_error_le (f g : (σ → F) → F) (T : LineTable F σ d)
    {η γ : ℚ} (hnear : relativeDistance f g ≤ η)
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (x h : σ → F) :
    (𝔼 s : Seed F σ, relativeDistance (surface f g x h s)
      (fun yz => (rows T x h s yz.1).eval yz.2)) ≤ γ + η := by
  simp only [relativeDistance_prod_eq_expect]
  rw [expect_comm]
  exact expect_le univ_nonempty (fun y _ => expect_own_row_error_le f g T hnear hendpoint x h y)

/-- Every nonzero column is an actual uniform center/direction pair. -/
theorem expect_column_error_of_ne (f g : (σ → F) → F) (T : LineTable F σ d)
    (x h : σ → F) (z : F) (hz : z ≠ 0) :
    (𝔼 s : Seed F σ, relativeDistance (fun y => surface f g x h s (y, z))
      (columns g T x h s z).eval) = rejectionRate f T := by
  simp_rw [surface_of_ne f g x h _ _ z hz]
  simp only [columns, ite_eq_right hz]
  exact (expect_scaled_pair x h z hz (lineError f T)).trans (expect_lineError f T)

/-- The global column mean has only the exceptional zero-column loss. -/
theorem expect_global_column_error_le (f g : (σ → F) → F) (T : LineTable F σ d)
    {δ : ℚ} (hwhole : rejectionRate f T ≤ δ) (x h : σ → F) :
    (𝔼 s : Seed F σ, relativeDistance (surface f g x h s)
      (fun yz => (columns g T x h s yz.2).eval yz.1)) ≤ δ + 1 / Fintype.card F := by
  have hδ : 0 ≤ δ := (rejectionRate_nonneg f T).trans hwhole
  have he (s : Seed F σ) : relativeDistance (surface f g x h s)
      (fun yz => (columns g T x h s yz.2).eval yz.1) =
      𝔼 z, relativeDistance (fun y => surface f g x h s (y, z))
        (columns g T x h s z).eval := by
    rw [← relativeDistance_comp_equiv (Equiv.prodComm F F), relativeDistance_prod_eq_expect]
    rfl
  simp only [he]
  rw [expect_comm]
  apply expect_le_add_exception
  intro z
  by_cases hz : z = 0
  · rw [ite_eq_left hz]
    exact (expect_le univ_nonempty (fun _ _ => relativeDistance_le_one _ _)).trans (by linarith)
  · rw [ite_eq_right hz, add_zero, expect_column_error_of_ne f g T x h z hz]
    exact hwhole

/-- At a fixed first parameter, a nonzero column has exactly the fixed-parameter
global rejection distribution. -/
theorem column_point_error_of_ne (f g : (σ → F) → F) (T : LineTable F σ d)
    (x h : σ → F) (y z : F) (hz : z ≠ 0) :
    relativeDistance (fun s : Seed F σ => surface f g x h s (y, z))
      (fun s => (columns g T x h s z).eval y) =
      relativeDistance (fun uv : Seed F σ => f (point uv.1 uv.2 y))
        (fun uv => (T uv).val.eval y) := by
  simp_rw [surface_of_ne f g x h _ y z hz]
  simp only [columns, ite_eq_right hz]
  exact distance_scaled_pair x h z hz (fun uv => f (point uv.1 uv.2 y))
    (fun uv => (T uv).val.eval y)

/-- The local row error uses the fixed-parameter rejection bound, not merely
the rejection averaged over all parameters. -/
theorem expect_local_row_error_le (f g : (σ → F) → F) (T : LineTable F σ d)
    {ℓ : ℚ}
    (hfixed : ∀ t, relativeDistance (fun uv : Seed F σ => f (point uv.1 uv.2 t))
      (fun uv => (T uv).val.eval t) ≤ ℓ) (x h : σ → F) (y : F) :
    (𝔼 s : Seed F σ, relativeDistance (fun z => surface f g x h s (y, z))
      (fun z => (columns g T x h s z).eval y)) ≤ ℓ + 1 / Fintype.card F := by
  have hℓ : 0 ≤ ℓ := (relativeDistance_nonneg _ _).trans (hfixed y)
  rw [expect_relativeDistance_swap]
  apply expect_le_add_exception
  intro z
  by_cases hz : z = 0
  · rw [ite_eq_left hz]
    exact (relativeDistance_le_one _ _).trans (by linarith)
  · rw [ite_eq_right hz, add_zero, column_point_error_of_ne f g T x h y z hz]
    exact hfixed y

omit [DecidableEq F] in
/-- The candidate prediction at a zero-column crossing is governed directly
by the endpoint hypothesis, including arbitrary chosen crossing parameters. -/
theorem endpoint_error_le (g : (σ → F) → F) (T : LineTable F σ d) {γ : ℚ}
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (x h : σ → F) (y : F) :
    fraction (fun s : Seed F σ => (rows T x h s y).eval 0 ≠ g (point x h y)) ≤ γ := by
  classical
  rw [fraction_ne_eq_relativeDistance]
  simp only [rows]
  have hd := distance_direction y (fun v => (T (point x h y, v)).val.eval 0)
    (fun _ => g (point x h y))
  rw [hd]
  simpa only [fraction_ne_eq_relativeDistance, point_zero] using hendpoint (point x h y) 0

/-- The modified zero column is close to the transverse candidate row predictions. -/
theorem expect_local_column_error_le (f g : (σ → F) → F) (T : LineTable F σ d) {γ : ℚ}
    (hendpoint : ∀ u t, fraction (fun v =>
      (T (u, v)).val.eval t ≠ g (point u v t)) ≤ γ)
    (x h : σ → F) :
    (𝔼 s : Seed F σ, relativeDistance (fun y => surface f g x h s (y, 0))
      (fun y => (rows T x h s y).eval 0)) ≤ γ := by
  rw [expect_relativeDistance_swap]
  apply expect_le univ_nonempty
  intro y _
  simp only [surface_zero]
  rw [relativeDistance_comm]
  simpa only [fraction_ne_eq_relativeDistance] using endpoint_error_le g T hendpoint x h y

end PCP.Algebraic.RuledSurface
