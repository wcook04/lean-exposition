module

public import QuarticQuery.LowerBound.DirectProduct

/-!
# The hard distribution from finite minimax

From `¬ RLe f L`, the game between promised inputs and trees of depth at most
`L` gives a distribution on the promised inputs on which every such tree succeeds
with weight at most `2/3`. This distribution comes from minimax, never from the
Gaussian-derived mixture of Bansal and Sinha, which has mass off the promise.
With Lemma 4.1 this bounds guessing `r` independent answers.
-/

@[expose] public section

open Finset Convexity

namespace QuarticQuery

/-! ## Finite minimax from Sion -/

private theorem isLinearMap_sum_mul {I : Type} [Fintype I] (a : I → ℝ) :
    IsLinearMap ℝ fun x : I → ℝ => ∑ i, x i * a i :=
  ⟨fun x y => by simp [add_mul, Finset.sum_add_distrib],
    fun c x => by simp [Finset.mul_sum, mul_assoc]⟩

private theorem convex_range_weights (I : Type) [Fintype I] :
    Convex ℝ (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) := by
  rw [StdSimplex.range_toFun_comp_weights]
  refine Convex.inter (convex_iInter fun i => ?_) ?_
  · exact convex_halfSpace_ge ⟨fun x y => rfl, fun c x => rfl⟩ 0
  · simpa using convex_hyperplane (isLinearMap_sum_mul fun _ => (1 : ℝ)) 1

private theorem isCompact_range_weights (I : Type) [Fintype I] :
    IsCompact (Set.range fun p : StdSimplex ℝ I => (p.weights : I → ℝ)) :=
  isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous

/-- Finite minimax. If every mixed column has a row paying at most `c`, some
mixed row pays at most `c` against every column. Same proof as
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le` in
complexitylib, kept here so that this file needs Mathlib only. -/
theorem exists_mixed_row {I J : Type} [Fintype I] [Fintype J] [Nonempty I]
    (M : I → J → ℝ) {c : ℝ}
    (h : ∀ q : StdSimplex ℝ J, ∃ i, ∑ j, q.weights j * M i j ≤ c) :
    ∃ p : StdSimplex ℝ I, ∀ j, ∑ i, p.weights i * M i j ≤ c := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨.single (Classical.arbitrary I), fun j => isEmptyElim j⟩
  set φ : (I → ℝ) → (J → ℝ) → ℝ := fun x y => ∑ i, ∑ j, x i * y j * M i j
  have hφx (y : J → ℝ) : (fun x => φ x y) = fun x => ∑ i, x i * ∑ j, y j * M i j := by
    funext x
    simp only [φ, Finset.mul_sum, mul_assoc]
  have hφy (x : I → ℝ) : (fun y => φ x y) = fun y => ∑ j, y j * ∑ i, x i * M i j := by
    funext y
    simp only [φ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hcont : Continuous fun p : (I → ℝ) × (J → ℝ) => φ p.1 p.2 := by
    simp only [φ]
    fun_prop
  obtain ⟨a, ⟨p, rfl⟩, b, ⟨q, rfl⟩, hab⟩ := Sion.exists_isSaddlePointOn (f := φ)
    (Set.range_nonempty _) (convex_range_weights I) (isCompact_range_weights I)
    (fun y _ =>
      (hcont.comp (Continuous.prodMk_left y)).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ r => by
      rw [hφx]
      exact (convex_range_weights I).inter (convex_halfSpace_le (isLinearMap_sum_mul _) r))
    (convex_range_weights J) (Set.range_nonempty _) (isCompact_range_weights J)
    (fun x _ =>
      (hcont.comp (Continuous.prodMk_right x)).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ r => by
      rw [hφy]
      exact (convex_range_weights J).inter (convex_halfSpace_ge (isLinearMap_sum_mul _) r))
  obtain ⟨i, hi⟩ := h q
  refine ⟨p, fun j => ?_⟩
  have h₁ := hab _ ⟨.single i, rfl⟩ _ ⟨.single j, rfl⟩
  simp only [φ, StdSimplex.weights_single, Finsupp.single_apply] at h₁
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h₁
  exact h₁.trans hi

/-! ## The hard distribution -/

variable {κ : Type}

/-- There are finitely many trees of bounded depth. -/
theorem finite_depth_le [Finite κ] (n : ℕ) : {T : QueryTree κ | T.depth ≤ n}.Finite := by
  induction n with
  | zero =>
    refine (Set.finite_range (QueryTree.leaf (ι := κ))).subset ?_
    rintro (b | _) h
    · exact ⟨b, rfl⟩
    · simp [QueryTree.depth] at h
  | succ n ih =>
    have hq := ((Set.finite_univ (α := κ)).prod (ih.prod ih)).image
      fun p : κ × QueryTree κ × QueryTree κ => QueryTree.query p.1 p.2.1 p.2.2
    refine ((Set.finite_range (QueryTree.leaf (ι := κ))).union hq).subset ?_
    rintro (b | ⟨q, l, r⟩) h
    · exact Or.inl ⟨b, rfl⟩
    · simp only [Set.mem_ofPred_eq, QueryTree.depth] at h
      refine Or.inr ⟨(q, l, r), ⟨trivial, ?_, ?_⟩, rfl⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega

/-- A sum vanishing off a subtype is a sum over it. -/
theorem sum_eq_sum_subtype {α : Type} [Fintype α] (p : α → Prop) [Fintype (Subtype p)]
    (g : α → ℝ) (hg : ∀ x, ¬ p x → g x = 0) : ∑ x, g x = ∑ d : Subtype p, g d := by
  classical
  rw [← Finset.sum_subtype (univ.filter p) (by simp) g]
  exact (sum_filter_of_ne fun x _ hx => by_contra fun h => hx (hg x h)).symm

/-- Any finite mixture of trees is a `RandomizedProgram`: the zero weights are
discarded, since a program's weights are positive. -/
theorem exists_program_of_mixture {J : Type} [Fintype J] (t : J → QueryTree κ) (q : J → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) {L : ℕ} (ht : ∀ j, (t j).depth ≤ L) :
    ∃ A : RandomizedProgram κ, A.depth ≤ L ∧
      ∀ x b, A.success x b = ∑ j, q j * if (t j).eval x = b then 1 else 0 := by
  classical
  let e := Fintype.equivFin {j // 0 < q j}
  have hzero : ∀ j, ¬ 0 < q j → q j = 0 := fun j h => le_antisymm (not_lt.mp h) (hq j)
  refine ⟨⟨_, fun i => q (e.symm i), fun i => t (e.symm i), fun i => (e.symm i).2, ?_⟩, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm (fun s => q s), ← hq1]
    exact (sum_eq_sum_subtype _ q hzero).symm
  · exact Finset.sup_le fun i _ => ht _
  · intro x b
    unfold RandomizedProgram.success
    rw [Equiv.sum_comp e.symm (fun s => if (t s).eval x = b then q s else 0),
      sum_eq_sum_subtype (fun j => 0 < q j) (fun j => q j * if (t j).eval x = b then 1 else 0)
        fun j h => by simp [hzero j h]]
    exact sum_congr rfl fun s _ => by split_ifs <;> simp

variable [Fintype κ] [DecidableEq κ]

/-- Ledger: claim-minimax-mu. A probability weight on the domain of `f` on which
every tree of depth at most `L` has success at most `2/3`. An empty domain is
excluded by the hypothesis, since then every program satisfies `RLe` vacuously.
The hypothesis `1 ≤ L` in the paper is not needed. -/
theorem exists_hard_distribution {f : PartialBool κ} {L : ℕ} (h : ¬ RLe f L) :
    ∃ μ : BitInput κ → ℝ, (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 ∧ (∀ x, μ x ≠ 0 → promised f x) ∧
      ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ 2 / 3 := by
  classical
  have hD : Nonempty {x // promised f x} := by
    by_contra hD
    refine h ⟨⟨1, fun _ => 1, fun _ => .leaf false, by simp, by simp⟩, ?_, fun x b hb =>
      (hD ⟨⟨x, b, hb⟩⟩).elim⟩
    simp [RandomizedProgram.depth, QueryTree.depth]
  let : Fintype {T : QueryTree κ | T.depth ≤ L} := (finite_depth_le L).fintype
  let M : {x // promised f x} → {T : QueryTree κ | T.depth ≤ L} → ℝ :=
    fun x T => if f x.1 = some (T.1.eval x.1) then 1 else 0
  have key : ∀ q : StdSimplex ℝ {T : QueryTree κ | T.depth ≤ L},
      ∃ x, ∑ j, q.weights j * M x j ≤ 2 / 3 := by
    intro q
    by_contra hq
    simp only [not_exists, not_le] at hq
    obtain ⟨A, hA, hs⟩ := exists_program_of_mixture (fun j : {T : QueryTree κ | T.depth ≤ L} => j.1)
      q.weights q.weights_nonneg q.total_of_fintype fun j => j.2
    refine h ⟨A, hA, fun x b hb => ?_⟩
    have hx := hq ⟨x, b, hb⟩
    rw [hs]
    refine le_of_lt (hx.trans_eq (sum_congr rfl fun j _ => ?_))
    simp [M, hb, eq_comm]
  obtain ⟨p, hp⟩ := exists_mixed_row M key
  let μ : BitInput κ → ℝ := fun x => if hx : promised f x then p.weights ⟨x, hx⟩ else 0
  have hμ : ∀ d : {x // promised f x}, μ d = p.weights d := fun d => by simp [μ, d.2]
  refine ⟨μ, fun x => ?_, ?_, fun x hx => ?_, fun T hT => ?_⟩
  · simp only [μ]
    split_ifs
    exacts [p.weights_nonneg _, le_rfl]
  · rw [sum_eq_sum_subtype (promised f) μ fun x hx => by simp [μ, hx]]
    simpa only [hμ] using p.total_of_fintype
  · by_contra hn
    exact hx (by simp [μ, hn])
  · unfold treeSuccess
    rw [sum_eq_sum_subtype (promised f) _ fun x hx => by simp [μ, hx]]
    simpa only [hμ, M] using hp ⟨T, hT⟩

/-- Ledger: claim-address-guess. Under a hard distribution, a tree with separate
caps of `L` guesses `r` independent answers with weight at most `(2/3) ^ r`. -/
theorem address_guess_le {f : PartialBool κ} {μ : BitInput κ → ℝ} {L r : ℕ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ 2 / 3)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (hT : T.capped fun _ => L) :
    guessSuccess f (fun _ => μ) T ≤ (2 / 3) ^ r :=
  direct_product hμ hard T hT

/-- Ledger: claim-address-guess. The same with independent side information or
coins `s` drawn from `p`. -/
theorem address_guess_average {S : Type} [Fintype S] {f : PartialBool κ} {μ : BitInput κ → ℝ}
    {L r : ℕ} (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ 2 / 3)
    {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (T : S → OutTree (Fin r × κ) (Fin r → Bool)) (hT : ∀ s, (T s).capped fun _ => L) :
    ∑ s, p s * guessSuccess f (fun _ => μ) (T s) ≤ (2 / 3) ^ r :=
  direct_product_average hμ hard hp hp1 T hT

/-- Ledger: claim-address-guess. One distribution on the domain, from `¬ RLe f L`,
works for every `r` and every capped guesser. -/
theorem exists_address_guess_bound {f : PartialBool κ} {L : ℕ} (h : ¬ RLe f L) :
    ∃ μ : BitInput κ → ℝ, (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1 ∧ (∀ x, μ x ≠ 0 → promised f x) ∧
      ∀ (r : ℕ) (T : OutTree (Fin r × κ) (Fin r → Bool)), (T.capped fun _ => L) →
        guessSuccess f (fun _ => μ) T ≤ (2 / 3) ^ r := by
  obtain ⟨μ, h0, h1, hd, hard⟩ := exists_hard_distribution h
  exact ⟨μ, h0, h1, hd, fun _ T hT => address_guess_le h0 hard T hT⟩

end QuarticQuery
