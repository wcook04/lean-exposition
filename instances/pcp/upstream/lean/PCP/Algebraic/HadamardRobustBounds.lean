/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardCorrection
import PCP.Algebraic.FiniteDistance

/-!
# Transferring noisy Hadamard checks to an additive word

The probability estimates in Appendix B. A query may depend arbitrarily on a
finite outer sample. Averaging over an independent uniform correction seed costs
at most twice the distance to an additive word per corrected answer. The three
answers in the product check may share the same seed; no independence among their
error events is assumed.
-/

namespace PCP.Algebraic.Hadamard

variable {I V W : Type*} [Fintype I] [Nonempty I]
  [AddCommGroup V] [Fintype V] [AddCommGroup W] [DecidableEq W]

/-- The two-query error bound, averaged over any finite family of requested entries. -/
theorem selfCorrect_average_failure_le (L : V →+ W) (w : V → W) (Q : I → V) :
    relativeDistance (fun s : I × V => selfCorrect w (Q s.1) s.2)
      (fun s => L (Q s.1)) ≤ 2 * relativeDistance w L := by
  apply relativeDistance_prod_le
  intro i
  exact selfCorrect_failure_le L w (Q i)

/-- A consistency check on a query family transfers full-word proximity to that family. -/
theorem restriction_distance_le (L : V →+ W) (w : V → W) (Q : I → V) :
    relativeDistance (fun i => w (Q i)) (fun i => L (Q i)) ≤
      2 * relativeDistance w L +
        relativeDistance (fun s : I × V => selfCorrect w (Q s.1) s.2)
          (fun s => w (Q s.1)) := by
  have ht := relativeDistance_triangle
    (fun s : I × V => w (Q s.1))
    (fun s => selfCorrect w (Q s.1) s.2) (fun s => L (Q s.1))
  rw [relativeDistance_comp_fst (κ := V)
    (fun i => w (Q i)) (fun i => L (Q i))] at ht
  have hb := selfCorrect_average_failure_le L w Q
  rw [relativeDistance_comm
    (fun s : I × V => w (Q s.1)) (fun s => selfCorrect w (Q s.1) s.2)] at ht
  linarith

/-- The `3δ` restriction estimate used for degree-one queries in Lemma 3.10. -/
theorem restriction_distance_le_three (L : V →+ W) (w : V → W) (Q : I → V)
    {δ : ℚ} (hw : relativeDistance w L ≤ δ)
    (hc : relativeDistance (fun s : I × V => selfCorrect w (Q s.1) s.2)
      (fun s => w (Q s.1)) ≤ δ) :
    relativeDistance (fun i => w (Q i)) (fun i => L (Q i)) ≤ 3 * δ := by
  have ht := restriction_distance_le L w Q
  linarith

/-- A sufficiently reliable corrected check of one entry forces the additive target's value. -/
theorem eq_of_selfCorrect_check (L : V →+ W) (w : V → W) (P : V) (a : W)
    (h : 2 * relativeDistance w L +
      relativeDistance (selfCorrect w P) (fun _ => a) < 1) : L P = a := by
  by_contra hne
  have ht := relativeDistance_triangle (fun _ : V => L P) (selfCorrect w P) (fun _ => a)
  rw [relativeDistance_const, ite_eq_right hne,
    relativeDistance_comm (fun _ : V => L P) (selfCorrect w P)] at ht
  have hb := selfCorrect_failure_le L w P
  linarith

/-- In particular, error at most `δ < 1/3` in both proximity and the unit check forces the unit. -/
theorem eq_of_selfCorrect_check_of_le (L : V →+ W) (w : V → W) (P : V) (a : W)
    {δ : ℚ} (hδ : δ < (1 : ℚ) / 3) (hw : relativeDistance w L ≤ δ)
    (hc : relativeDistance (selfCorrect w P) (fun _ => a) ≤ δ) : L P = a := by
  apply eq_of_selfCorrect_check L w P a
  linarith

section Multiplication

variable {K : Type*} [AddCommGroup K] [Mul K] [DecidableEq K]

/-- Three corrected answers transfer a product check at a cost of at most six times the distance. -/
theorem multiplicative_defect_le (L : V →+ K) (w : V → K) (A B C : I → V) :
    relativeDistance (fun i => L (C i)) (fun i => L (A i) * L (B i)) ≤
      6 * relativeDistance w L +
        relativeDistance (fun s : I × V => selfCorrect w (C s.1) s.2)
          (fun s => selfCorrect w (A s.1) s.2 * selfCorrect w (B s.1) s.2) := by
  have hA := selfCorrect_average_failure_le L w A
  have hB := selfCorrect_average_failure_le L w B
  have hC := selfCorrect_average_failure_le L w C
  have hAB := relativeDistance_zipWith_le (fun a b : K => a * b)
    (fun s : I × V => selfCorrect w (A s.1) s.2) (fun s => L (A s.1))
    (fun s : I × V => selfCorrect w (B s.1) s.2) (fun s => L (B s.1))
  have ht₁ := relativeDistance_triangle
    (fun s : I × V => L (C s.1)) (fun s => selfCorrect w (C s.1) s.2)
    (fun s => L (A s.1) * L (B s.1))
  have ht₂ := relativeDistance_triangle
    (fun s : I × V => selfCorrect w (C s.1) s.2)
    (fun s => selfCorrect w (A s.1) s.2 * selfCorrect w (B s.1) s.2)
    (fun s => L (A s.1) * L (B s.1))
  rw [relativeDistance_comp_fst (κ := V)
      (fun i => L (C i)) (fun i => L (A i) * L (B i)),
    relativeDistance_comm (fun s : I × V => L (C s.1))
      (fun s => selfCorrect w (C s.1) s.2)] at ht₁
  linarith

/-- The `7δ` bound contradicts bilinear separation whenever `δ < 1/28`. -/
theorem multiplicative_defect_lt_quarter (L : V →+ K) (w : V → K) (A B C : I → V)
    {δ : ℚ} (hδ : δ < (1 : ℚ) / 28) (hw : relativeDistance w L ≤ δ)
    (hc : relativeDistance (fun s : I × V => selfCorrect w (C s.1) s.2)
      (fun s => selfCorrect w (A s.1) s.2 * selfCorrect w (B s.1) s.2) ≤ δ) :
    relativeDistance (fun i => L (C i)) (fun i => L (A i) * L (B i)) < (1 : ℚ) / 4 := by
  have ht := multiplicative_defect_le L w A B C
  linarith

end Multiplication

end PCP.Algebraic.Hadamard
