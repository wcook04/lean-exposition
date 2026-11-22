/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialLine
import PCP.Algebraic.PolynomialDistance

/-!
# The point-versus-line test and its soundness interface

The concrete tester of ALMSS, *Proof Verification and the Hardness of
Approximation Problems*, Theorem 45 (manuscript p. 27), samples the line
parameters `u, v` and an independent `t` from the **whole field**. Its second
oracle gives a formal univariate polynomial of degree at most `c` for each
ordered pair `(u, v)`. No consistency between different parameterizations is
assumed. The zero direction is included.

This file proves perfect completeness and defines the proposition
`PointLineSoundness`. The separate `PointLineSoundness` module proves that
proposition in arbitrary dimension for `|F| ≥ 1000000*c^3` and error at most
`1/4000000`, retaining the original theorem's factor `2`.
`PointLineConstant` proves degree zero in every finite dimension, with no
field-size or error assumption.

This differs from Theorem 2.12, whose tester samples a nonzero field
parameter and whose displayed conclusion has factor `4`. The production route
applies `PointLineTest.exists_close_of_small_rejection` directly. Normalized
rejection uses rational arithmetic; no random-bit or time bound is claimed.
-/

namespace PCP.Algebraic.PointLineTest

open PolynomialLine

variable {F σ : Type*} [Field F] {c : ℕ}

/-- A table of degree-bounded univariate polynomials, indexed by ordered line parameters. -/
abbrev LineTable (F σ : Type*) [Field F] (c : ℕ) :=
  ((σ → F) × (σ → F)) → {p : Polynomial F // p.natDegree ≤ c}

/-- The residual of the point-versus-line equality. Zero means acceptance. -/
def check (f : (σ → F) → F) (table : LineTable F σ c)
    (u v : σ → F) (t : F) : F :=
  f (point u v t) - (table (u, v)).val.eval t

/-- The honest lines table of a degree-bounded multivariate polynomial. -/
noncomputable def restrictionTable (P : MvPolynomial σ F) (hP : P.totalDegree ≤ c) :
    LineTable F σ c :=
  fun uv => ⟨restrict uv.1 uv.2 P, natDegree_restrict_le_of_totalDegree_le _ _ P hP⟩

/-- Pointwise completeness, including zero direction and zero evaluation parameter. -/
@[simp] theorem check_restrictionTable (P : MvPolynomial σ F)
    (hP : P.totalDegree ≤ c) (u v : σ → F) (t : F) :
    check (fun x => MvPolynomial.eval x P) (restrictionTable P hP) u v t = 0 := by
  simp [check, restrictionTable]

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Uniform rejection on `((u, v), t)`, with `t` ranging over all of `F`. -/
def rejectionRate (f : (σ → F) → F) (table : LineTable F σ c) : ℚ :=
  relativeDistance
    (fun s : ((σ → F) × (σ → F)) × F => check f table s.1.1 s.1.2 s.2)
    (fun _ => 0)

/-- Equivalently, rejection is disagreement between the two queried oracle answers. -/
theorem rejectionRate_eq_relativeDistance (f : (σ → F) → F)
    (table : LineTable F σ c) :
    rejectionRate f table = relativeDistance
      (fun s : ((σ → F) × (σ → F)) × F => f (point s.1.1 s.1.2 s.2))
      (fun s => (table s.1).val.eval s.2) := by
  simp only [rejectionRate, check, relativeDistance, hammingDist, sub_ne_zero]

theorem rejectionRate_nonneg (f : (σ → F) → F) (table : LineTable F σ c) :
    0 ≤ rejectionRate f table := relativeDistance_nonneg _ _

theorem rejectionRate_le_one (f : (σ → F) → F) (table : LineTable F σ c) :
    rejectionRate f table ≤ 1 := relativeDistance_le_one _ _

/-- The honest lines table has zero normalized rejection. -/
@[simp] theorem rejectionRate_restrictionTable (P : MvPolynomial σ F)
    (hP : P.totalDegree ≤ c) :
    rejectionRate (fun x => MvPolynomial.eval x P) (restrictionTable P hP) = 0 := by
  simp only [rejectionRate, check_restrictionTable, relativeDistance_self]

end PCP.Algebraic.PointLineTest

namespace PCP.Algebraic

/-- The explicit soundness proposition for the concrete all-field-parameter
point-versus-line tester at fixed field, dimension, degree, and error threshold.

This definition supplies no proof. `pointLineSoundness_degree_zero` in `PointLineConstant`
supplies degree zero; `pointLineSoundness_largeField` in `PointLineSoundness` proves it generally
with explicit absolute constants and a cubic field-size bound.
-/
def PointLineSoundness (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (m c : ℕ) (δ₀ : ℚ) : Prop :=
  ∀ (f : (Fin m → F) → F) (table : PointLineTest.LineTable F (Fin m) c) (δ : ℚ),
    0 ≤ δ → δ ≤ δ₀ → PointLineTest.rejectionRate f table ≤ δ →
      ∃ P : MvPolynomial (Fin m) F,
        P.totalDegree ≤ c ∧ relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ

end PCP.Algebraic
