module

public import QuarticQuery.ForrelationLower.RealLeafGrowth
public import QuarticQuery.ForrelationLower.RealLeafAdvantage

/-! Deliberate guard mutation: proves the bound only for the zero leaf.
Expected rejection for the changed theorem type, not for a build failure. -/

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
    (hT : T.depth ≤ d) (hbounded : T = RealQueryTree.leaf 0) :
    ∑ p, |ext (Dl (Lp p) T.eval) μ| ≤
      K ^ k + (Fintype.card ι * 2) ^ k *
        ((4 * Fintype.card ι : ℝ) ^ k * Real.exp (-Λ)) := by
  have hb : T.Bounded := by rw [hbounded]; norm_num [RealQueryTree.Bounded]
  exact sum_abs_ext_Dl_le_real_leaves Lp hnd hlen hinj hμ hd hK hKsq hn T hT hb

end QuarticQuery.Independent.RealLeaves.Compare
