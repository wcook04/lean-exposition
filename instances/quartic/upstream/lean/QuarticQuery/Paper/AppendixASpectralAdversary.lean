module

public import QuarticQuery.Paper.AppendixAPerron
public import QuarticQuery.Paper.AppendixASensitivity

/-!
# Appendix A: the general nonnegative spectral adversary bound

Compiled as part of the `QuarticQuery` library target.

This module combines the arbitrary-matrix progress proof with the nonnegative
Perron vector and the existing adaptive-to-fixed-sequence simulation. The query
budget is preserved exactly. All matrix norms are the Euclidean operator norm.

The paper's absolute constant can be taken to be `1/35`. The rational inequality
`sqrt (2/9) ≤ 33/70` gives this value from the sharper progress constant
`(1 - 2 sqrt 2 / 3) / 2`.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Ledger: lem-A.2. General nonnegative symmetric adversary bound for an
adaptive algorithm of query cap `t`. The coordinate norms are bounded by `M`.
The constant-function case forces Γ to be zero. -/
theorem appendixA_matrixNorm_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) (Γ : AppendixAMatrix n)
    (hsym : ∀ x y, Γ x y = Γ y x) (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    appendixAMatrixNorm Γ ≤ 35 * (t : ℝ) * M := by
  rcases appendixA_QLe_total_cases hq with ⟨b, hb⟩ | ⟨W, _, U, ψ, S, hψ, hc⟩
  · have hΓzero : Γ = 0 := by
      ext x y
      exact hzero x y ((hb x).trans (hb y).symm)
    rw [hΓzero]
    simp only [appendixAMatrixNorm, map_zero, norm_zero]
    positivity
  · obtain ⟨v, hv⟩ := appendixA_perron Γ hsym hΓ
    exact appendixA_adversary_thirty_five_of_perron f Γ v U hψ t S hc
      hΓ hzero hv hM hcoord

/-- Ledger: lem-A.2. The general bound at the attained quantum-query minimum. -/
theorem appendixA_matrixNorm_le_Q (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (hsym : ∀ x y, Γ x y = Γ y x) (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    appendixAMatrixNorm Γ ≤ 35 * (Q (totalise f) : ℝ) * M :=
  appendixA_matrixNorm_le_of_QLe (QLe_Q _) Γ hsym hΓ hzero hM hcoord

/-- Ledger: def-Gamma-i. Maximum coordinate-mask norm, with value zero for an
empty coordinate set. NNReal supplies the finite supremum without an arbitrary
default value in ℝ. -/
noncomputable def appendixACoordinateMax (Γ : AppendixAMatrix n) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixAGammaCoord Γ i)‖₊) : NNReal) : ℝ)

/-- Ledger: def-Gamma-i. Every coordinate-mask norm is bounded by the maximum. -/
theorem appendixA_coord_le_max (Γ : AppendixAMatrix n) (i : Fin n) :
    appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ appendixACoordinateMax Γ := by
  change (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixAGammaCoord Γ i)‖₊ : ℝ) ≤
    ((Finset.univ.sup (fun j : Fin n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixAGammaCoord Γ j)‖₊) : NNReal) : ℝ)
  exact_mod_cast (Finset.le_sup (f := fun j : Fin n =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixAGammaCoord Γ j)‖₊) (Finset.mem_univ i))

/-- Ledger: def-Gamma-i. The maximum coordinate norm is nonnegative. -/
theorem appendixACoordinateMax_nonneg (Γ : AppendixAMatrix n) :
    0 ≤ appendixACoordinateMax Γ := by
  unfold appendixACoordinateMax
  exact NNReal.coe_nonneg _

/-- Ledger: lem-A.2. The Euclidean operator norm of a nonzero matrix is positive. -/
theorem appendixAMatrixNorm_pos {Γ : AppendixAMatrix n} (hΓ : Γ ≠ 0) :
    0 < appendixAMatrixNorm Γ := by
  apply norm_pos_iff.2
  intro h
  apply hΓ
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective (by simpa using h)

/-- Ledger: lem-A.2. A nonzero adversary has a positive denominator. The proof
also handles `n = 0`: the premises are then inconsistent, as required. -/
theorem appendixACoordinateMax_pos
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (hsym : ∀ x y, Γ x y = Γ y x) (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0) (hne : Γ ≠ 0) :
    0 < appendixACoordinateMax Γ := by
  have hb := appendixA_matrixNorm_le_Q f Γ hsym hΓ hzero
    (appendixACoordinateMax_nonneg Γ) (appendixA_coord_le_max Γ)
  have hn := appendixAMatrixNorm_pos hne
  have hM := appendixACoordinateMax_nonneg Γ
  by_contra hpos
  have hz : appendixACoordinateMax Γ = 0 := le_antisymm (le_of_not_gt hpos) hM
  rw [hz, mul_zero] at hb
  exact (not_le_of_gt hn) hb

/-- Ledger: lem-A.2. The paper's full nonnegative spectral-adversary lemma,
with the explicit absolute constant `c = 1/35`. Nonconstantness follows from
the nonzero matrix and the opposite-output support condition. -/
theorem appendixA_lemmaA2
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (hsym : ∀ x y, Γ x y = Γ y x) (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0) (hne : Γ ≠ 0) :
    (1 / 35 : ℝ) * (appendixAMatrixNorm Γ / appendixACoordinateMax Γ) ≤
      (Q (totalise f) : ℝ) := by
  have hM := appendixACoordinateMax_pos f Γ hsym hΓ hzero hne
  have hb := appendixA_matrixNorm_le_Q f Γ hsym hΓ hzero hM.le (appendixA_coord_le_max Γ)
  rw [← mul_div_assoc, div_le_iff₀ hM]
  nlinarith

end QuarticQuery.Paper
