module

public import QuarticQuery.Paper.AppendixAStar
public import QuarticQuery.Paper.AppendixAHuangRoute

/-!
# Appendix A: assembly of the universal quartic bound

Compiled as part of the `QuarticQuery` library target.

This second route uses the general nonnegative matrix adversary theorem for
both parts of Lemma A.3, the spectral form of Huang's inequality for Lemma A.4,
and Midrijanis's exact decision-tree bound for Lemma A.5. It does not invoke
`Cslib.Quantum.complexity_le_mul_pow_four` or the project's existing quartic
endpoint. The A.4 theorem used here passes through an actual degree-dimensional
face, the literal recursive Huang matrix, and extension by zero back to the
original sensitivity graph. The full-cube directional alternative is retained
in `AppendixAHuang.lean` and is not the A.4 supplier of this assembly.

The explicit coefficient of this route is `35^4 = 1500625`. An optional hybrid
uses the library's stronger polynomial-method block-sensitivity estimate and
gives `19600`. Its block-sensitivity proof has a different route from A.3.
These are constants of the present implementation, not novelty claims.
-/

public section

namespace QuarticQuery.Paper

open Cslib.QueryComplexity
open Cslib.BitString

variable {n : ℕ}

/-- Ledger: lem-A.4. The spectral inequality and the sensitivity-graph
adversary give a degree bound for the same adaptive query cap. -/
theorem appendixA_degree_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) : degree f ≤ 1225 * t ^ 2 := by
  have hspectral := appendixA_spectralSensitivity_adversary_le_of_QLe hq
  have hsq := pow_le_pow_left₀ (spectralSensitivity_nonneg f) hspectral 2
  have hdeg : (degree f : ℝ) ≤ 1225 * (t : ℝ) ^ 2 := by
    have h := appendixA4_paper_route f
    nlinarith
  exact_mod_cast hdeg

/-- Ledger: thm-A.1. The assembled A.2--A.5 route at an adaptive query cap.
The star estimate contributes `1225`, and the degree estimate contributes
another `1225`. Constants, including functions on the zero-dimensional cube,
are covered without adding one to the query budget. -/
theorem appendixA_D_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) : D (totalise f) ≤ 1500625 * t ^ 4 := by
  have hbs := appendixA_blockSensitivity_star_le_of_QLe hq
  have hdeg := appendixA_degree_le_of_QLe hq
  calc
    D (totalise f) ≤ blockSensitivity f * degree f := appendixA_lemmaA5 f
    _ ≤ (1225 * t ^ 2) * (1225 * t ^ 2) := Nat.mul_le_mul hbs hdeg
    _ = 1500625 * t ^ 4 := by ring

/-- Ledger: thm-A.1. The explicit quartic bound at the attained quantum
minimum, proved from the appendix lemmas. -/
theorem appendixA_D_le_Q_pow_four (f : TotalBool (Fin n)) :
    D (totalise f) ≤ 1500625 * Q (totalise f) ^ 4 :=
  appendixA_D_le_of_QLe (QLe_Q _)

/-- Ledger: thm-A.1. The paper's displayed form of Theorem A.1, including
the randomized simulation of a deterministic decision tree. -/
theorem appendixA_theoremA1 (f : TotalBool (Fin n)) :
    (R (totalise f) : ℝ) ≤ D (totalise f) ∧
      (D (totalise f) : ℝ) ≤
        1500625 * (1 + (Q (totalise f) : ℝ)) ^ 4 := by
  refine ⟨by exact_mod_cast R_le_D _, ?_⟩
  have h : (D (totalise f) : ℝ) ≤
      1500625 * (Q (totalise f) : ℝ) ^ 4 := by
    exact_mod_cast appendixA_D_le_Q_pow_four f
  have hq : (0 : ℝ) ≤ Q (totalise f) := Nat.cast_nonneg _
  refine h.trans ?_
  gcongr
  linarith

/-- Ledger: thm-A.1. Exponent four is admissible in the project's
definition, using the coefficient of the assembled appendix route. -/
theorem appendixA_universalPower_four : UniversalPower 4 := by
  refine ⟨by norm_num, 1500625, by norm_num, fun n _ f => ?_⟩
  obtain ⟨hRD, hD⟩ := appendixA_theoremA1 f
  have hp : Real.rpow (1 + (Q (totalise f) : ℝ)) 4 =
      (1 + (Q (totalise f) : ℝ)) ^ 4 := by
    rw [Real.rpow_eq_pow]
    exact_mod_cast Real.rpow_natCast (1 + (Q (totalise f) : ℝ)) 4
  rw [hp]
  exact hRD.trans hD

/-- Ledger: thm-A.1. Optional hybrid constant: polynomial-method block
sensitivity combined with the new spectral estimate. This is explicitly an
alternative to the star proof of the block-sensitivity part of A.3. -/
theorem appendixA_D_le_of_QLe_hybrid {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) : D (totalise f) ≤ 19600 * t ^ 4 := by
  have hbs := appendixA_blockSensitivity_le_of_QLe hq
  have hdeg := appendixA_degree_le_of_QLe hq
  calc
    D (totalise f) ≤ blockSensitivity f * degree f := appendixA_lemmaA5 f
    _ ≤ (16 * t ^ 2) * (1225 * t ^ 2) := Nat.mul_le_mul hbs hdeg
    _ = 19600 * t ^ 4 := by ring

/-- Ledger: thm-A.1. The optional hybrid bound at the attained minimum. -/
theorem appendixA_D_le_Q_pow_four_hybrid (f : TotalBool (Fin n)) :
    D (totalise f) ≤ 19600 * Q (totalise f) ^ 4 :=
  appendixA_D_le_of_QLe_hybrid (QLe_Q _)

end QuarticQuery.Paper
