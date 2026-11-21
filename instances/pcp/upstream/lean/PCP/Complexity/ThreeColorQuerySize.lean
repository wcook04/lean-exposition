import PCP.Algebraic.ComputableThreeColorQueryAlgorithm
import PCP.Complexity.PolynomialPrefixLang

/-! Uniform polynomial storage bounds for the actual production query list. -/

namespace PCP.Lang.ThreeColorQuerySize

open PCP.Algebraic ThreeColorCanonicalVerifier

attribute [local irreducible] proofBound

theorem finite_codes_size (N : ℕ) (xs : List (Fin N)) :
    listSize (xs.map Fin.val) ≤ xs.length*(Nat.size N+1) := by
  induction xs with
  | nil => simp [listSize]
  | cons x xs ih =>
      have hx := Nat.size_le_size (Nat.le_of_lt x.isLt)
      simp only [List.map_cons, List.length_cons, listSize, List.sum_cons] at ih ⊢
      nlinarith

/-- The exact query list has at most 187 entries, each below the existing proof bound. -/
theorem queryList_size (x bits : List Bool) :
    listSize ((ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val) ≤
      187*(proofBound.eval x.length+1) := by
  have hs := finite_codes_size _ (ComputableThreeColorQueryAlgorithm.queryList x bits)
  have hl : (ComputableThreeColorQueryAlgorithm.queryList x bits).length ≤ 187 := by
    rw [ComputableThreeColorQueryAlgorithm.queryList_eq]
    exact ThreeColorQueryAlgorithm.queryList_length_le x bits
  have hw := (size_le_self _).trans (proofLength_le_bound x)
  exact hs.trans (Nat.mul_le_mul hl (Nat.add_le_add_right hw 1))

/-- Every physical address uses only polynomially many stored bits. -/
theorem query_size (x bits : List Bool) (q : ℕ)
    (hq : q ∈ (ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val) :
    Nat.size q ≤ proofBound.eval x.length := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  exact (size_le_self _).trans ((Nat.le_of_lt j.isLt).trans (proofLength_le_bound x))

/-- A uniform monomial bound, independent of the actual seed or answer history. -/
theorem polynomial_queryList_size : ∃ C d : ℕ, ∀ x bits : List Bool,
    listSize ((ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val) ≤
      C*(x.length+1)^d := by
  obtain ⟨C, d, hc⟩ := PolynomialPrefix.exists_eval_bound proofBound
  refine ⟨187*(C+1), d, fun x bits => (queryList_size x bits).trans ?_⟩
  have hp : 1 ≤ (x.length+1)^d := one_le_pow₀ (by omega)
  have h := hc x.length
  nlinarith

end PCP.Lang.ThreeColorQuerySize
