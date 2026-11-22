module

public import QuarticQuery.ForrelationLower.RealLeaves
public import QuarticQuery.ForrelationLower.Cascade

/-! Direct theorem-type agreement target. The semantic definitions are shared
with the solution. Comparator agreement here is not independent model review;
independent expected answers are in Controls.lean and the rational checker. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Finset
namespace QuarticQuery.Independent.RealLeaves.Compare
open QuarticQuery.ForrelationLower

variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem growth {P : Type} [Fintype P] [DecidableEq P]
    (Lp : P → List ι) (hnd : ∀ p, (Lp p).Nodup) {k : ℕ}
    (hlen : ∀ p, (Lp p).length = k)
    (hinj : Function.Injective fun p => (Lp p).toFinset)
    {μ : ι → ℝ} (hμ : ∀ a, |μ a| ≤ 1 / 2)
    {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * d * 2 ^ 2 * Λ)
    (hn : 1 ≤ Fintype.card ι) (T : RealQueryTree ι)
    (hT : T.depth ≤ d) (hbounded : T.Bounded) :
    ∑ p, |ext (Dl (Lp p) T.eval) μ| ≤
      K ^ k + (Fintype.card ι * 2) ^ k *
        ((4 * Fintype.card ι : ℝ) ^ k * Real.exp (-Λ)) := by
  sorry

variable {n : Type} [Fintype n] [DecidableEq n] {l : ℕ}
theorem advantage (H : Matrix n n ℝ)
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
  sorry

end QuarticQuery.Independent.RealLeaves.Compare
