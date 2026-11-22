module

public import QuarticQuery.ForrelationLower.RealLeaves
public import QuarticQuery.ForrelationLower.Cascade

/-!
# The sharp Forrelation advantage bound for arbitrary bounded-real leaves

This extends the literal maintained declaration `advantage_le_sharp`, which
has a Boolean tree and one postprocessing map `Bool → ℝ`, to independent
real labels at every leaf.  The construction of `RealQueryTree` and its
convex representation supplies the missing model interface.

It does not change the Forrelation promise, the fixed-parameter separation,
or the proof of the existing Boolean endpoint.  All constants below are
identical to those of `advantage_le_sharp`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset

namespace QuarticQuery.ForrelationLower

variable {n : Type} [Fintype n] [DecidableEq n] {l : ℕ}

/-- The difference between the rounded-chain expectation and the uniform
expectation is a real linear functional on all functions on the finite cube. -/
noncomputable def chainGap (H : Matrix n n ℝ) :
    (((BC l n → Bool) → ℝ)) →ₗ[ℝ] ℝ where
  toFun g := (∫ u, ext g (wv H 1 u) ∂(gP (PC l n))) - ext g 0
  map_add' g h := by
    have hgi := (bcf_ext H g (s := 1) (by norm_num)).integrable
    have hhi := (bcf_ext H h (s := 1) (by norm_num)).integrable
    change (∫ u, ext (fun z => g z + h z) (wv H 1 u) ∂(gP (PC l n))) -
        ext (fun z => g z + h z) 0 = _
    simp only [ext_add]
    rw [integral_add hgi hhi]
    ring
  map_smul' c g := by
    change (∫ u, ext (fun z => c * g z) (wv H 1 u) ∂(gP (PC l n))) -
        ext (fun z => c * g z) 0 =
      c * ((∫ u, ext g (wv H 1 u) ∂(gP (PC l n))) - ext g 0)
    simp only [ext_smul]
    rw [integral_const_mul]
    ring

/-- The full bounded-real form of the sharp advantage theorem.
The tree is fixed before the input, its leaf values lie in `[-1,1]`,
and its cap is syntactic, hence covers every branch including repeated
queries and branches inconsistent with previous answers. -/
theorem advantage_le_sharp_real_leaves (H : Matrix n n ℝ)
    (hl : 0 < l) (hH : RowsOrth H) {ε : ℝ} (hε : 0 ≤ ε)
    (hHb : ∀ a b, |H a b| ≤ ε)
    {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * d * 2 ^ 2 * Λ)
    (hn : 1 ≤ Fintype.card (BC l n))
    (T : RealQueryTree (BC l n)) (hT : T.depth ≤ d)
    (hbounded : T.Bounded) :
    |∫ u, ext T.eval (wv H 1 u) ∂(gP (PC l n)) - ext T.eval 0| ≤
      ((3 / 16 : ℝ) * ε) ^ l *
        (K ^ (l + 1) + (Fintype.card (BC l n) * 2) ^ (l + 1) *
          ((4 * Fintype.card (BC l n) : ℝ) ^ (l + 1) * Real.exp (-Λ))) := by
  change |chainGap H T.eval| ≤ _
  apply T.linear_bound hbounded (chainGap H)
  intro S hS
  exact advantage_le_sharp H hl hH hε hHb hd hK hKsq hn S
    (hS.trans hT) RealQueryTree.answerSign
    (fun b => (RealQueryTree.abs_answerSign b).le)

end QuarticQuery.ForrelationLower
