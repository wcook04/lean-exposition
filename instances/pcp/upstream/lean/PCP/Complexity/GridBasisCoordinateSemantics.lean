import PCP.Complexity.GridBasisCoordinateLang
import PCP.Algebraic.FieldQueryArithmetic

/-!
# The coordinate program's exact Lagrange basis semantics
-/

namespace PCP.Lang.GridBasisCoordinate

open PCP.Algebraic BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

omit [NeZero t] in
/-- The initial alphabet's embedding is precisely the numeric node decoder. -/
theorem prefix_eq_node (n : ℕ) (hn : n ≤ 2 ^ t) (i : Fin n) :
    FiniteAlphabetIndex.prefixEmbedding (fieldEquiv t) hn i = GridFactor.node t i.val := by
  apply (fieldEquiv t).injective
  apply Fin.ext
  rw [FiniteAlphabetIndex.code_prefixEmbedding,
    GridFactor.code_node i.val (lt_of_lt_of_le i.isLt hn)]
  rfl

/-- Removing one grid node gives exactly the product computed by the counted program. -/
theorem value_eq_alphabet (z : BinaryMaterializedField.Element t) (n : ℕ)
    (hn : n ≤ 2 ^ t) (k : Fin n) :
    value z k.val n =
      ∏ b ∈ (FiniteAlphabetIndex.alphabet (fieldEquiv t) hn).erase (GridFactor.node t k.val),
        (z - b) / (GridFactor.node t k.val - b) := by
  rw [value, Finset.prod_range]
  conv_rhs => rw [FiniteAlphabetIndex.alphabet,
    ← prefix_eq_node n hn k, ← Finset.map_erase, Finset.prod_map]
  rw [← Finset.prod_erase Finset.univ (a := k) (by simp :
    (if k.val = k.val then (1 : BinaryMaterializedField.Element t)
      else (z + GridFactor.node t k.val) /
        (GridFactor.node t k.val + GridFactor.node t k.val)) = 1)]
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i.val ≠ k.val := fun he => (Finset.mem_erase.mp hi).1 (Fin.ext he)
  rw [ite_eq_right hne, prefix_eq_node n hn i, prefix_eq_node n hn k, sub_eq_add_neg,
    sub_eq_add_neg]
  rfl

end PCP.Lang.GridBasisCoordinate
