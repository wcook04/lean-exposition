/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateAgreement
import PCP.Algebraic.PointLineCrossing

/-!
# Crossing rigidity for candidate rows

The selected row polynomial need not be a nearest polynomial to the received
row. Its own approximation error, together with the transverse column error,
forces agreement with the constructed bivariate polynomial. Only the selected
column uses nearestness. This avoids any claim that changing one received entry
preserves an arbitrarily chosen nearest polynomial.
-/

namespace PCP.Algebraic.CandidateCrossing

open PointLineCrossing PointLineTest

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- Five small errors force a candidate row and a nearest column to agree at
their crossing. The comparison bivariate polynomial is constructed by agreement. -/
theorem crossing_eq (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (M : F × F → F) (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d) (hC : ∀ z, (C z).natDegree ≤ d)
    (y₀ z₀ : F) {ε : ℚ} (hε : ε ≤ 1 / 100)
    (hrows : relativeDistance M (fun yz => (R yz.1).eval yz.2) ≤ ε)
    (hcols : relativeDistance M (fun yz => (C yz.2).eval yz.1) ≤ ε)
    (hrow : relativeDistance (fun z => M (y₀, z)) (fun z => (C z).eval y₀) ≤ ε)
    (hcol : relativeDistance (fun y => M (y, z₀)) (fun y => (R y).eval z₀) ≤ ε)
    (hown : relativeDistance (fun z => M (y₀, z)) (R y₀).eval ≤ ε)
    (hmin : ∀ p : Polynomial F, p.natDegree ≤ d →
      relativeDistance (fun y => M (y, z₀)) (C z₀).eval ≤
        relativeDistance (fun y => M (y, z₀)) p.eval)
    (hsmall : 6 * ε + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2) :
    (R y₀).eval z₀ = (C z₀).eval y₀ := by
  obtain ⟨P, hP, hnear⟩ :=
    BivariateAgreement.exists_polynomial_of_row_column_agreement hd hq M C R hC hR
      hcols hrows hε
  have hRP (y : F) : (rowPolynomial P y).natDegree ≤ d :=
    (natDegree_axisRestrict_le _ _ _).trans (hP 1)
  have hCP (z : F) : (columnPolynomial P z).natDegree ≤ d :=
    (natDegree_axisRestrict_le _ _ _).trans (hP 0)
  have hrowsP : relativeDistance (fun yz : F × F => (R yz.1).eval yz.2)
      (fun yz => (rowPolynomial P yz.1).eval yz.2) ≤ 5 * ε := by
    simp only [eval_rowPolynomial]
    have ht := relativeDistance_triangle (fun yz : F × F => (R yz.1).eval yz.2) M
      (fun yz => MvPolynomial.eval ![yz.1, yz.2] P)
    rw [relativeDistance_comm (fun yz : F × F => (R yz.1).eval yz.2) M] at ht
    linarith
  have hcolsP : relativeDistance (fun zy : F × F => (C zy.1).eval zy.2)
      (fun zy => (columnPolynomial P zy.1).eval zy.2) ≤ 5 * ε := by
    have ht := relativeDistance_triangle (fun yz : F × F => (C yz.2).eval yz.1) M
      (fun yz => MvPolynomial.eval ![yz.1, yz.2] P)
    rw [relativeDistance_comm (fun yz : F × F => (C yz.2).eval yz.1) M] at ht
    have h : relativeDistance (fun yz : F × F => (C yz.2).eval yz.1)
        (fun yz => (columnPolynomial P yz.2).eval yz.1) ≤ 5 * ε := by
      simp only [eval_columnPolynomial]
      linarith
    rw [← relativeDistance_comp_equiv (Equiv.prodComm F F)] at h
    exact h
  have hτ : (0 : ℚ) ≤ (d : ℚ) / Fintype.card F := by positivity
  have hc : C z₀ = columnPolynomial P z₀ :=
    eq_of_transverse_close R (rowPolynomial P) hR hRP
      (fun y => M (y, z₀)) (columnPolynomial P z₀) (C z₀) (hCP z₀) (hC z₀) z₀
      (fun y => by simp) hrowsP hcol (hmin _ (hCP z₀)) (by linarith)
  have htrans := polynomial_transverse_distance_le C (columnPolynomial P) hC hCP y₀
  have hlocal : relativeDistance (fun z => M (y₀, z)) (rowPolynomial P y₀).eval ≤
      6 * ε + (d : ℚ) / Fintype.card F := by
    have ht := relativeDistance_triangle (fun z => M (y₀, z))
      (fun z => (C z).eval y₀) (rowPolynomial P y₀).eval
    have he : (fun z => (columnPolynomial P z).eval y₀) = (rowPolynomial P y₀).eval := by
      funext z
      simp
    rw [he] at htrans
    linarith
  have hr : R y₀ = rowPolynomial P y₀ := by
    by_contra hne
    have hsep := univariate_distance_ge (R y₀) (rowPolynomial P y₀) (hR y₀) (hRP y₀) hne
    have ht := relativeDistance_triangle (R y₀).eval (fun z => M (y₀, z))
      (rowPolynomial P y₀).eval
    rw [relativeDistance_comm (R y₀).eval (fun z => M (y₀, z))] at ht
    linarith
  rw [hr, hc]
  simp

end PCP.Algebraic.CandidateCrossing
