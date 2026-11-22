module

public import QuarticQuery.ForrelationLower.RealLeaves
public import QuarticQuery.ForrelationLower.TreeGrowth

/-!
# Derivative growth for arbitrary bounded-real decision-tree leaves

The independently specified real tree is transferred to the maintained
Boolean-tree estimate by a finite convex decomposition.  The analytical
constant and every derivative, bias, dimension and depth hypothesis are
preserved verbatim.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace QuarticQuery.ForrelationLower

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def differenceLinear (a : ι) :
    ((ι → Bool) → ℝ) →ₗ[ℝ] ((ι → Bool) → ℝ) where
  toFun g := D a g
  map_add' g h := by
    funext x
    simp only [D, Pi.add_apply]
    ring
  map_smul' c g := by
    funext x
    simp only [D, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

noncomputable def differencesLinear : List ι →
    ((ι → Bool) → ℝ) →ₗ[ℝ] ((ι → Bool) → ℝ)
  | [] => LinearMap.id
  | a :: L => (differencesLinear L).comp (differenceLinear a)

theorem differencesLinear_apply (L : List ι) (g : (ι → Bool) → ℝ) :
    differencesLinear L g = Dl L g := by
  induction L generalizing g with
  | nil => rfl
  | cons a L ih =>
      change differencesLinear L (D a g) = Dl L (D a g)
      exact ih _

noncomputable def extensionLinear (μ : ι → ℝ) : ((ι → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun g := ext g μ
  map_add' g h := ext_add g h μ
  map_smul' c g := ext_smul c g μ

noncomputable def derivativeExpectationLinear (L : List ι) (μ : ι → ℝ) :
    ((ι → Bool) → ℝ) →ₗ[ℝ] ℝ :=
  (extensionLinear μ).comp (differencesLinear L)

theorem derivativeExpectationLinear_apply (L : List ι) (μ : ι → ℝ)
    (g : (ι → Bool) → ℝ) :
    derivativeExpectationLinear L μ g = ext (Dl L g) μ := by
  change ext (differencesLinear L g) μ = _
  rw [differencesLinear_apply]

theorem sum_abs_ext_Dl_le_real_leaves {P : Type} [Fintype P] [DecidableEq P]
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
  simp_rw [← derivativeExpectationLinear_apply]
  apply T.sum_linear_bound hbounded (fun p => derivativeExpectationLinear (Lp p) μ)
  intro S hS
  simp_rw [derivativeExpectationLinear_apply]
  exact sum_abs_ext_Dl_le Lp hnd hlen hinj hμ hd hK hKsq hn S
    (hS.trans hT) RealQueryTree.answerSign
    (fun b => (RealQueryTree.abs_answerSign b).le)

end QuarticQuery.ForrelationLower
