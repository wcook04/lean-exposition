module

public import QuarticQuery.Statement

/-!
# The capped adaptive direct product (Lemma 4.1)

Weights are nonnegative functions on inputs, not conditional laws. `budgetValue`
is the best weighted success of a tree of bounded depth, computed by recursion.
The main bound is an induction on the multi-instance tree that changes one
weight and one budget at each query. This replaces the paper's supermartingale
wording with a shorter route: nothing conditions on anything, and adaptivity
across instances needs no separate argument.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-! ## Weighted success and its recursion -/

/-- Weighted success of guessing the constant `b`. -/
def constSuccess (f : PartialBool κ) (ν : BitInput κ → ℝ) (b : Bool) : ℝ :=
  ∑ x, ν x * if f x = some b then 1 else 0

/-- Weighted success of a decision tree. -/
def treeSuccess (f : PartialBool κ) (ν : BitInput κ → ℝ) (T : QueryTree κ) : ℝ :=
  ∑ x, ν x * if f x = some (T.eval x) then 1 else 0

/-- The part of a weight where the bit at `q` equals `b`. -/
def restrictWeight (ν : BitInput κ → ℝ) (q : κ) (b : Bool) : BitInput κ → ℝ :=
  fun x => if x q = b then ν x else 0

/-- The best weighted success of a tree of depth at most `c`. The option `none`
stops early; `some q` queries `q`. -/
noncomputable def budgetValue (f : PartialBool κ) : ℕ → (BitInput κ → ℝ) → ℝ
  | 0, ν => max (constSuccess f ν false) (constSuccess f ν true)
  | c + 1, ν => (univ : Finset (Option κ)).sup' ⟨none, mem_univ _⟩ fun o =>
      match o with
      | none => budgetValue f c ν
      | some q => budgetValue f c (restrictWeight ν q false) +
          budgetValue f c (restrictWeight ν q true)

theorem budgetValue_le_succ (f : PartialBool κ) (c : ℕ) (ν : BitInput κ → ℝ) :
    budgetValue f c ν ≤ budgetValue f (c + 1) ν := by
  rw [budgetValue]
  exact le_sup' (f := fun o : Option κ => match o with
    | none => budgetValue f c ν
    | some q => budgetValue f c (restrictWeight ν q false) +
        budgetValue f c (restrictWeight ν q true)) (mem_univ none)

theorem budgetValue_add_le (f : PartialBool κ) (c : ℕ) (ν : BitInput κ → ℝ) (q : κ) :
    budgetValue f c (restrictWeight ν q false) + budgetValue f c (restrictWeight ν q true)
      ≤ budgetValue f (c + 1) ν := by
  rw [budgetValue.eq_2]
  exact le_sup' (f := fun o : Option κ => match o with
    | none => budgetValue f c ν
    | some q => budgetValue f c (restrictWeight ν q false) +
        budgetValue f c (restrictWeight ν q true)) (mem_univ (some q))

theorem budgetValue_mono (f : PartialBool κ) {c d : ℕ} (h : c ≤ d) (ν : BitInput κ → ℝ) :
    budgetValue f c ν ≤ budgetValue f d ν := by
  induction d, h using Nat.le_induction with
  | base => exact le_rfl
  | succ d _ ih => exact ih.trans (budgetValue_le_succ f d ν)

theorem constSuccess_le_budgetValue (f : PartialBool κ) (c : ℕ) (ν : BitInput κ → ℝ) (b : Bool) :
    constSuccess f ν b ≤ budgetValue f c ν := by
  refine le_trans ?_ (budgetValue_mono f (Nat.zero_le c) ν)
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem constSuccess_nonneg (f : PartialBool κ) {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (b : Bool) : 0 ≤ constSuccess f ν b :=
  sum_nonneg fun x _ => mul_nonneg (hν x) (by split_ifs <;> norm_num)

theorem budgetValue_nonneg (f : PartialBool κ) (c : ℕ) {ν : BitInput κ → ℝ}
    (hν : ∀ x, 0 ≤ ν x) : 0 ≤ budgetValue f c ν :=
  (constSuccess_nonneg f hν false).trans (constSuccess_le_budgetValue f c ν false)

omit [Fintype κ] [DecidableEq κ] in
theorem restrictWeight_nonneg {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) (q : κ) (b : Bool) :
    ∀ x, 0 ≤ restrictWeight ν q b x := fun x => by
  unfold restrictWeight
  split_ifs
  exacts [hν x, le_rfl]

theorem treeSuccess_query (f : PartialBool κ) (ν : BitInput κ → ℝ) (q : κ)
    (l r : QueryTree κ) :
    treeSuccess f ν (.query q l r) =
      treeSuccess f (restrictWeight ν q false) l + treeSuccess f (restrictWeight ν q true) r := by
  unfold treeSuccess restrictWeight
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  cases hx : x q <;> simp [QueryTree.eval, hx]

/-- The recursion is attained by a tree. -/
theorem exists_tree_budgetValue_le (f : PartialBool κ) (c : ℕ) (ν : BitInput κ → ℝ) :
    ∃ T : QueryTree κ, T.depth ≤ c ∧ budgetValue f c ν ≤ treeSuccess f ν T := by
  induction c generalizing ν with
  | zero =>
    rw [budgetValue]
    rcases max_cases (constSuccess f ν false) (constSuccess f ν true) with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨.leaf false, le_rfl, by rw [h]; exact le_rfl⟩
    · exact ⟨.leaf true, le_rfl, by rw [h]; exact le_rfl⟩
  | succ c ih =>
    rw [budgetValue]
    obtain ⟨o, -, ho⟩ := exists_mem_eq_sup' (s := (univ : Finset (Option κ))) ⟨none, mem_univ _⟩
      (fun o => match o with
        | none => budgetValue f c ν
        | some q => budgetValue f c (restrictWeight ν q false) +
            budgetValue f c (restrictWeight ν q true))
    rw [ho]
    cases o with
    | none =>
      obtain ⟨T, hT, h⟩ := ih ν
      exact ⟨T, by omega, h⟩
    | some q =>
      obtain ⟨T₀, hT₀, h₀⟩ := ih (restrictWeight ν q false)
      obtain ⟨T₁, hT₁, h₁⟩ := ih (restrictWeight ν q true)
      refine ⟨.query q T₀ T₁, ?_, ?_⟩
      · simp only [QueryTree.depth]
        omega
      · rw [treeSuccess_query]
        exact add_le_add h₀ h₁

/-- A bound on every tree of depth at most `c` bounds the value. -/
theorem budgetValue_le_of_forall {f : PartialBool κ} {c : ℕ} {ν : BitInput κ → ℝ} {β : ℝ}
    (h : ∀ T : QueryTree κ, T.depth ≤ c → treeSuccess f ν T ≤ β) : budgetValue f c ν ≤ β := by
  obtain ⟨T, hT, hle⟩ := exists_tree_budgetValue_le f c ν
  exact hle.trans (h T hT)

/-- The value bounds every tree of depth at most `c`. -/
theorem treeSuccess_le_budgetValue (f : PartialBool κ) {c : ℕ} (ν : BitInput κ → ℝ)
    {T : QueryTree κ} (hT : T.depth ≤ c) : treeSuccess f ν T ≤ budgetValue f c ν := by
  induction T generalizing c ν with
  | leaf b => exact constSuccess_le_budgetValue f c ν b
  | query q l r ihl ihr =>
    obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by simp only [QueryTree.depth] at hT; omega⟩
    simp only [QueryTree.depth] at hT
    rw [treeSuccess_query]
    exact (add_le_add (ihl _ (by omega)) (ihr _ (by omega))).trans (budgetValue_add_le f c ν q)

/-! ## Multi-instance trees -/

/-- A decision tree with leaves in `β`. -/
inductive OutTree (ι β : Type) where
  | leaf (answer : β)
  | query (index : ι) (onFalse onTrue : OutTree ι β)

namespace OutTree

variable {ι β : Type}

def eval : OutTree ι β → BitInput ι → β
  | .leaf b, _ => b
  | .query i l r, x => if x i then r.eval x else l.eval x

def depth : OutTree ι β → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

end OutTree

/-- Each query to instance `h` spends one unit of `c h`, on every path. -/
def OutTree.capped {r : ℕ} {β : Type} :
    OutTree (Fin r × κ) β → (Fin r → ℕ) → Prop
  | .leaf _, _ => True
  | .query p l u, c => 0 < c p.1 ∧
      l.capped (Function.update c p.1 (c p.1 - 1)) ∧
      u.capped (Function.update c p.1 (c p.1 - 1))

omit [Fintype κ] [DecidableEq κ] in
/-- More budget never hurts. -/
theorem OutTree.capped_mono {r : ℕ} {β : Type} {T : OutTree (Fin r × κ) β} {c d : Fin r → ℕ}
    (hT : T.capped c) (h : ∀ j, c j ≤ d j) : T.capped d := by
  induction T generalizing c d with
  | leaf => trivial
  | query p l u ihl ihu =>
    obtain ⟨h0, hl, hu⟩ := hT
    have hd : ∀ j, Function.update c p.1 (c p.1 - 1) j ≤ Function.update d p.1 (d p.1 - 1) j := by
      intro j
      by_cases hj : j = p.1
      · subst hj
        simpa using Nat.sub_le_sub_right (h p.1) 1
      · simpa [Function.update_of_ne hj] using h j
    exact ⟨h0.trans_le (h p.1), ihl hl hd, ihu hu hd⟩

omit [Fintype κ] [DecidableEq κ] in
/-- A total cap implies the per-instance cap. -/
theorem OutTree.capped_of_depth_le {r : ℕ} {β : Type} {T : OutTree (Fin r × κ) β} {n : ℕ}
    {c : Fin r → ℕ} (hT : T.depth ≤ n) (hc : ∀ j, n ≤ c j) : T.capped c := by
  induction T generalizing n c with
  | leaf => trivial
  | query p l u ihl ihu =>
    simp only [OutTree.depth] at hT
    have hn : ∀ j, n - 1 ≤ Function.update c p.1 (c p.1 - 1) j := by
      intro j
      by_cases hj : j = p.1
      · subst hj
        simpa using Nat.sub_le_sub_right (hc p.1) 1
      · rw [Function.update_of_ne hj]
        exact (Nat.sub_le n 1).trans (hc j)
    exact ⟨by have := hc p.1; omega, ihl (by omega) hn, ihu (by omega) hn⟩

variable {r : ℕ}

/-- Weighted probability, over independent instances, that `T` outputs every
answer correctly. Each instance must lie in the domain of `f`. -/
def guessSuccess (f : PartialBool κ) (ν : Fin r → BitInput κ → ℝ)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) : ℝ :=
  ∑ U : Fin r → BitInput κ, (∏ h, ν h (U h)) *
    if ∀ h, f (U h) = some (T.eval (Function.uncurry U) h) then 1 else 0

theorem guessSuccess_leaf (f : PartialBool κ) (ν : Fin r → BitInput κ → ℝ) (s : Fin r → Bool) :
    guessSuccess f ν (.leaf s) = ∏ h, constSuccess f (ν h) (s h) := by
  unfold guessSuccess constSuccess
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun U _ => ?_
  simp only [OutTree.eval, prod_mul_distrib]
  congr 1
  by_cases h : ∀ j, f (U j) = some (s j)
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    simp only [h, ↓reduceIte]
    exact (prod_eq_zero (f := fun j => if f (U j) = some (s j) then (1 : ℝ) else 0)
      (mem_univ j) (by simp [hj])).symm

/-- One query splits the success into its two branches, changing one weight. -/
theorem guessSuccess_query (f : PartialBool κ) (ν : Fin r → BitInput κ → ℝ) (h : Fin r) (q : κ)
    (l u : OutTree (Fin r × κ) (Fin r → Bool)) :
    guessSuccess f ν (.query (h, q) l u) =
      guessSuccess f (Function.update ν h (restrictWeight (ν h) q false)) l +
        guessSuccess f (Function.update ν h (restrictWeight (ν h) q true)) u := by
  unfold guessSuccess
  rw [← sum_add_distrib]
  refine sum_congr rfl fun U _ => ?_
  have hsplit : ∀ b, ∏ j, Function.update ν h (restrictWeight (ν h) q b) j (U j) =
      (if U h q = b then 1 else 0) * ∏ j, ν j (U j) := by
    intro b
    rw [← mul_prod_erase univ _ (mem_univ h), ← mul_prod_erase univ (fun j => ν j (U j))
      (mem_univ h), Function.update_self, restrictWeight, ← mul_assoc]
    have : ∏ j ∈ univ.erase h, Function.update ν h (restrictWeight (ν h) q b) j (U j) =
        ∏ j ∈ univ.erase h, ν j (U j) :=
      prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [this]
    split_ifs <;> simp
  rw [hsplit, hsplit]
  cases hq : U h q <;> simp [OutTree.eval, Function.uncurry, hq]

/-- The main induction. The sum of the two branch products is the product with
factor `h` replaced by the sum of its branches, and the recursion absorbs that. -/
theorem guessSuccess_le_prod (f : PartialBool κ) (T : OutTree (Fin r × κ) (Fin r → Bool))
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ) (hν : ∀ h x, 0 ≤ ν h x) (hT : T.capped c) :
    guessSuccess f ν T ≤ ∏ h, budgetValue f (c h) (ν h) := by
  induction T generalizing ν c with
  | leaf s =>
    rw [guessSuccess_leaf]
    exact prod_le_prod₀ (fun h _ => constSuccess_nonneg f (hν h) _)
      fun h _ => constSuccess_le_budgetValue f _ _ _
  | query p l u ihl ihu =>
    obtain ⟨h, q⟩ := p
    obtain ⟨h0, hl, hu⟩ := hT
    simp only at h0 hl hu
    have hν' : ∀ b j x, 0 ≤ Function.update ν h (restrictWeight (ν h) q b) j x := by
      intro b j x
      by_cases hj : j = h
      · subst hj
        simpa using restrictWeight_nonneg (hν j) q b x
      · simpa [Function.update_of_ne hj] using hν j x
    set c' := Function.update c h (c h - 1) with hc'
    have hprod : ∀ b, ∏ j, budgetValue f (c' j) (Function.update ν h (restrictWeight (ν h) q b) j)
        = budgetValue f (c h - 1) (restrictWeight (ν h) q b) *
          ∏ j ∈ univ.erase h, budgetValue f (c j) (ν j) := by
      intro b
      rw [← mul_prod_erase univ _ (mem_univ h), hc', Function.update_self, Function.update_self]
      congr 1
      exact prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (ne_of_mem_erase hj), Function.update_of_ne (ne_of_mem_erase hj)]
    have hP : 0 ≤ ∏ j ∈ univ.erase h, budgetValue f (c j) (ν j) :=
      prod_nonneg fun j _ => budgetValue_nonneg f _ (hν j)
    rw [guessSuccess_query]
    calc _ ≤ _ := add_le_add (ihl _ c' (hν' false) hl) (ihu _ c' (hν' true) hu)
      _ = (budgetValue f (c h - 1) (restrictWeight (ν h) q false) +
            budgetValue f (c h - 1) (restrictWeight (ν h) q true)) *
          ∏ j ∈ univ.erase h, budgetValue f (c j) (ν j) := by
            rw [hprod, hprod, add_mul]
      _ ≤ budgetValue f (c h) (ν h) * ∏ j ∈ univ.erase h, budgetValue f (c j) (ν j) := by
            refine mul_le_mul_of_nonneg_right ?_ hP
            have := budgetValue_add_le f (c h - 1) (ν h) q
            rwa [Nat.sub_add_cancel h0] at this
      _ = ∏ j, budgetValue f (c j) (ν j) :=
        mul_prod_erase univ (fun j => budgetValue f (c j) (ν j)) (mem_univ h)

/-! ## Lemma 4.1 -/

/-- Ledger: lem-4.1. Separate caps of `L`, with queries interleaved adaptively.
Normalisation of `μ` is not needed. -/
theorem direct_product {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hβ : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (hT : T.capped fun _ => L) :
    guessSuccess f (fun _ => μ) T ≤ β ^ r := by
  refine (guessSuccess_le_prod f T _ _ (fun _ => hμ) hT).trans ?_
  calc _ ≤ ∏ _h : Fin r, β := prod_le_prod₀ (fun _ _ => budgetValue_nonneg f _ hμ)
        fun _ _ => budgetValue_le_of_forall hβ
    _ = β ^ r := by simp

/-- Ledger: lem-4.1. Independent side information or internal randomness: the
tree may depend on `s`, drawn from `p` independently of the instances. -/
theorem direct_product_average {S : Type} [Fintype S] {f : PartialBool κ} {μ : BitInput κ → ℝ}
    {L : ℕ} {β : ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hβ : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (T : S → OutTree (Fin r × κ) (Fin r → Bool)) (hT : ∀ s, (T s).capped fun _ => L) :
    ∑ s, p s * guessSuccess f (fun _ => μ) (T s) ≤ β ^ r := by
  calc _ ≤ ∑ s, p s * β ^ r := sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (direct_product hμ hβ _ (hT s)) (hp s)
    _ = β ^ r := by rw [← sum_mul, hp1, one_mul]

/-- Ledger: lem-4.1. Side information `s` and independent coins `w` together. -/
theorem direct_product_randomized {S Ω : Type} [Fintype S] [Fintype Ω] {f : PartialBool κ}
    {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hβ : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    {p : S → ℝ} {w : Ω → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hw : ∀ o, 0 ≤ w o) (hw1 : ∑ o, w o = 1)
    (T : S → Ω → OutTree (Fin r × κ) (Fin r → Bool))
    (hT : ∀ s o, (T s o).capped fun _ => L) :
    ∑ s, ∑ o, p s * w o * guessSuccess f (fun _ => μ) (T s o) ≤ β ^ r := by
  rw [← Fintype.sum_prod_type']
  refine direct_product_average hμ hβ (p := fun i : S × Ω => p i.1 * w i.2)
    (fun i => mul_nonneg (hp _) (hw _)) ?_ (fun i => T i.1 i.2) fun i => hT _ _
  rw [Fintype.sum_prod_type]
  simp [← mul_sum, hw1, hp1]

/-- Ledger: lem-4.1. A total cap of `L` queries across all instances. -/
theorem direct_product_of_depth_le {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hβ : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (hT : T.depth ≤ L) :
    guessSuccess f (fun _ => μ) T ≤ β ^ r :=
  direct_product hμ hβ T (OutTree.capped_of_depth_le hT fun _ => le_rfl)

end QuarticQuery
