import Mathlib
import Breakdown.CertCell.CertificateStatements

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

private theorem quadValue_add_forms {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (x : n → ℝ) :
    quadValue (A + B) x = quadValue A x + quadValue B x := by
  simp [quadValue, Matrix.add_mulVec, dotProduct_add]

private theorem quadValue_sub_forms {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (x : n → ℝ) :
    quadValue (A - B) x = quadValue A x - quadValue B x := by
  simp [quadValue, Matrix.sub_mulVec, dotProduct_sub]

private theorem quadValue_pivotDiagonal {n : Type*} [Fintype n] [DecidableEq n] (s : Finset n)
    (d x : n → ℝ) : quadValue (pivotDiagonal s d) x = ∑ j ∈ s, d j * x j ^ 2 := by
  rw [quadValue, pivotDiagonal, dotProduct]
  simp only [mulVec_diagonal]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ s)]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j => j ∈ s), x j * ((if j ∈ s then d j else 0) * x j)
      = ∑ j ∈ s, d j * x j ^ 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [if_pos hj]; ring
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ s), x j * ((if j ∈ s then d j else 0) * x j)
      = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [if_neg (Finset.mem_filter.mp hj).2]; ring
  rw [h1, h2, add_zero]

private theorem quadValue_pairMatrix {n p : Type*} [Fintype n] [Fintype p] (F : Matrix n p ℝ)
    (x : n → ℝ) : quadValue (F * Fᵀ) x = ∑ c, (∑ i, F i c * x i) ^ 2 := by
  rw [quadValue, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp [dotProduct, mulVec, sq]

private theorem two_abs_mul_le_weighted (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * (|a| * |b|) ≤ a ^ 2 * u / v + b ^ 2 * v / u := by
  rw [div_add_div _ _ hv.ne' hu.ne', le_div_iff₀ (mul_pos hv hu), ← sq_abs a, ← sq_abs b]
  nlinarith [sq_nonneg (|a| * u - |b| * v)]

private theorem neg_weighted_le_quadValue {n : Type*} [Fintype n] (D : Matrix n n ℝ)
    (hD : Dᵀ = D) (w r : n → ℝ) (hw : ∀ j, 0 < w j)
    (hr : ∀ i, w i * ∑ j, |D i j| / w j ≤ r i) (x : n → ℝ) :
    -∑ i, r i * x i ^ 2 ≤ quadValue D x := by
  have hsymm : ∀ i j, |D j i| = |D i j| := by
    intro i j
    have := congrFun (congrFun hD i) j
    rw [transpose_apply] at this
    rw [this]
  have h1 : quadValue D x = ∑ i, ∑ j, x i * (D i j * x j) := by
    simp [quadValue, dotProduct, mulVec, Finset.mul_sum]
  have h2 : |quadValue D x| ≤ ∑ i, ∑ j, |D i j| * (|x i| * |x j|) := by
    rw [h1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    rw [abs_mul, abs_mul]; ring
  have h3 : 2 * ∑ i, ∑ j, |D i j| * (|x i| * |x j|)
      ≤ ∑ i, ∑ j, |D i j| * (x i ^ 2 * w i / w j) + ∑ i, ∑ j, |D i j| * (x j ^ 2 * w j / w i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := two_abs_mul_le_weighted (x i) (x j) (w i) (w j) (hw i) (hw j)
    have hab := abs_nonneg (D i j)
    nlinarith [mul_le_mul_of_nonneg_left this hab]
  have h4 : ∑ i, ∑ j, |D i j| * (x j ^ 2 * w j / w i)
      = ∑ i, ∑ j, |D i j| * (x i ^ 2 * w i / w j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsymm i j]
  have h5 : ∑ i, ∑ j, |D i j| * (x i ^ 2 * w i / w j) ≤ ∑ i, r i * x i ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have he : ∑ j, |D i j| * (x i ^ 2 * w i / w j) = x i ^ 2 * (w i * ∑ j, |D i j| / w j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [he, mul_comm (r i)]
    exact mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)
  have h6 := neg_abs_le (quadValue D x)
  linarith

theorem signedSlackBound : SignedSlackBound := by
  intro n p q _ _ _ _ M S pivot δ w r Fp Fm hM hS hw hr x
  set D := slackRemainder M S pivot δ Fp Fm with hDdef
  have hdecomp : M = pivotDiagonal pivot δ + Fp * Fpᵀ - Fm * Fmᵀ + S + D := by
    rw [hDdef, slackRemainder]; abel
  have hDsym : Dᵀ = D := by
    rw [hDdef, slackRemainder, pivotDiagonal]
    simp only [transpose_sub, transpose_add, transpose_mul, transpose_transpose, diagonal_transpose,
      hM, hS]
  have hkey := neg_weighted_le_quadValue D hDsym w r hw hr x
  have hfp : 0 ≤ ∑ c, (∑ i, Fp i c * x i) ^ 2 := Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hsplit : ∑ j ∈ Finset.univ \ pivot, r j * x j ^ 2 + ∑ j ∈ pivot, r j * x j ^ 2
      = ∑ j, r j * x j ^ 2 := Finset.sum_sdiff (Finset.subset_univ pivot)
  have hdiff : ∑ j ∈ pivot, (δ j - r j) * x j ^ 2
      = ∑ j ∈ pivot, δ j * x j ^ 2 - ∑ j ∈ pivot, r j * x j ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  conv_rhs => rw [hdecomp]
  simp only [quadValue_add_forms, quadValue_sub_forms, quadValue_pivotDiagonal, quadValue_pairMatrix]
  rw [hdiff]
  linarith

end Breakdown.CertCell.Certificate
