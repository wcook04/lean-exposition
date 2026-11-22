module

public import QuarticQuery.Statement

/-!
# Basic facts about classical bit queries

Monotonicity of `RLe` and `DLe`, the read-all tree, attainment of `R` and `D`,
the characterisation of `t < R f` that every lower bound goes through, and
invariance under renaming coordinates. The tree helpers (`QueryTree.map`,
`QueryTree.graft`, `QueryTree.readList`) are kept general for later upper bounds.
-/

@[expose] public section

namespace QuarticQuery

variable {ι κ α : Type}

/-! ## Trees -/

namespace QueryTree

@[simp] theorem eval_leaf (b : Bool) (x : BitInput ι) : (leaf b : QueryTree ι).eval x = b := rfl

theorem eval_query (i : ι) (l r : QueryTree ι) (x : BitInput ι) :
    (query i l r).eval x = if x i then r.eval x else l.eval x := rfl

@[simp] theorem depth_leaf (b : Bool) : (leaf b : QueryTree ι).depth = 0 := rfl

@[simp] theorem depth_query (i : ι) (l r : QueryTree ι) :
    (query i l r).depth = 1 + max l.depth r.depth := rfl

/-- Relabel the queried coordinates along any map. -/
def map (e : ι → α) : QueryTree ι → QueryTree α
  | .leaf b => .leaf b
  | .query i l r => .query (e i) (l.map e) (r.map e)

theorem eval_map (e : ι → α) (t : QueryTree ι) (x : BitInput α) :
    (t.map e).eval x = t.eval fun i => x (e i) := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr => simp only [map, eval_query, ihl, ihr]

@[simp] theorem depth_map (e : ι → α) (t : QueryTree ι) : (t.map e).depth = t.depth := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr => simp only [map, depth_query, ihl, ihr]

/-- Run `t`, then continue with the tree its answer selects. -/
def graft : QueryTree ι → (Bool → QueryTree ι) → QueryTree ι
  | .leaf b, k => k b
  | .query i l r, k => .query i (l.graft k) (r.graft k)

theorem eval_graft (t : QueryTree ι) (k : Bool → QueryTree ι) (x : BitInput ι) :
    (t.graft k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf b => rfl
  | query i l r ihl ihr =>
    simp only [graft, eval_query, ihl, ihr]
    split <;> rfl

theorem depth_graft_le (t : QueryTree ι) (k : Bool → QueryTree ι) :
    (t.graft k).depth ≤ t.depth + max (k false).depth (k true).depth := by
  induction t with
  | leaf b => cases b <;> simp [graft]
  | query i l r ihl ihr =>
    simp only [graft, depth_query]
    omega

open Classical in
/-- Query the coordinates of `l` in order, recording the answers in `base`, and
answer with `g` of the completed input. -/
noncomputable def readList (g : BitInput ι → Bool) : List ι → BitInput ι → QueryTree ι
  | [], base => .leaf (g base)
  | i :: l, base =>
    .query i (readList g l (Function.update base i false))
      (readList g l (Function.update base i true))

open Classical in
theorem depth_readList_le (g : BitInput ι → Bool) (l : List ι) (base : BitInput ι) :
    (readList g l base).depth ≤ l.length := by
  induction l generalizing base with
  | nil => simp [readList]
  | cons i l ih =>
    have h0 := ih (Function.update base i false)
    have h1 := ih (Function.update base i true)
    simp only [readList, depth_query, List.length_cons]
    omega

open Classical in
/-- Once `l` covers every coordinate where `x` may differ from `base`, the tree
computes `g x`. Repeats in `l` are harmless. -/
theorem eval_readList (g : BitInput ι → Bool) (l : List ι) (base x : BitInput ι)
    (h : ∀ i, i ∉ l → x i = base i) : (readList g l base).eval x = g x := by
  induction l generalizing base with
  | nil =>
    have hb : base = x := funext fun i => (h i (by simp)).symm
    simp [readList, hb]
  | cons i l ih =>
    have key : ∀ j, j ∉ l → x j = Function.update base i (x i) j := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        simp
      · rw [Function.update_of_ne hji]
        exact h j (by simp [hji, hj])
    cases hx : x i
    · rw [hx] at key
      simpa [readList, eval_query, hx] using ih _ key
    · rw [hx] at key
      simpa [readList, eval_query, hx] using ih _ key

end QueryTree

/-! ## Randomized programs -/

namespace RandomizedProgram

/-- Relabel every tree of a mixture. -/
def map (e : ι → α) (A : RandomizedProgram ι) : RandomizedProgram α where
  size := A.size
  weight := A.weight
  tree j := (A.tree j).map e
  weight_pos := A.weight_pos
  weight_sum := A.weight_sum

@[simp] theorem depth_map (e : ι → α) (A : RandomizedProgram ι) :
    (A.map e).depth = A.depth := by
  change (Finset.univ.sup fun j : Fin A.size => ((A.tree j).map e).depth) = _
  simp [depth]

theorem success_map (e : ι → α) (A : RandomizedProgram ι) (x : BitInput α) (b : Bool) :
    (A.map e).success x b = A.success (fun i => x (e i)) b := by
  change (∑ j : Fin A.size, if ((A.tree j).map e).eval x = b then A.weight j else 0) = _
  simp only [success, QueryTree.eval_map]

/-- The one-tree mixture. -/
def ofTree (t : QueryTree ι) : RandomizedProgram ι where
  size := 1
  weight _ := 1
  tree _ := t
  weight_pos _ := one_pos
  weight_sum := by simp

@[simp] theorem depth_ofTree (t : QueryTree ι) : (ofTree t).depth = t.depth := by
  change (Finset.univ.sup fun _ : Fin 1 => t.depth) = t.depth
  simp

theorem success_ofTree (t : QueryTree ι) (x : BitInput ι) (b : Bool) :
    (ofTree t).success x b = if t.eval x = b then 1 else 0 := by
  change (∑ _ : Fin 1, if t.eval x = b then (1 : ℝ) else 0) = _
  simp

end RandomizedProgram

/-! ## Monotonicity and transport -/

/-- `RLe` is monotone in the budget. -/
theorem RLe.mono {f : PartialBool ι} {s t : ℕ} (h : RLe f s) (hst : s ≤ t) : RLe f t := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hA.trans hst, hc⟩

/-- `DLe` is monotone in the budget. -/
theorem DLe.mono {f : PartialBool ι} {s t : ℕ} (h : DLe f s) (hst : s ≤ t) : DLe f t := by
  obtain ⟨T, hT, hc⟩ := h
  exact ⟨T, hT.trans hst, hc⟩

/-- A smaller promise, or a pullback of the input along any coordinate map, cannot
cost more. This is the common form of restriction and renaming. -/
theorem RLe.comap {f : PartialBool κ} {g : PartialBool ι} {t : ℕ} (e : ι → κ)
    (hfg : ∀ x b, f x = some b → g (fun i => x (e i)) = some b) (h : RLe g t) : RLe f t := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A.map e, by simpa using hA, fun x b hx => ?_⟩
  rw [RandomizedProgram.success_map]
  exact hc _ b (hfg x b hx)

/-- The deterministic form of `RLe.comap`. -/
theorem DLe.comap {f : PartialBool κ} {g : PartialBool ι} {t : ℕ} (e : ι → κ)
    (hfg : ∀ x b, f x = some b → g (fun i => x (e i)) = some b) (h : DLe g t) : DLe f t := by
  obtain ⟨T, hT, hc⟩ := h
  refine ⟨T.map e, by simpa using hT, fun x b hx => ?_⟩
  rw [QueryTree.eval_map]
  exact hc _ b (hfg x b hx)

/-- Shrinking the promise cannot cost more. -/
theorem RLe.of_promise {f g : PartialBool ι} {t : ℕ}
    (hfg : ∀ x b, f x = some b → g x = some b) (h : RLe g t) : RLe f t :=
  h.comap id hfg

/-- Shrinking the promise cannot cost more. -/
theorem DLe.of_promise {f g : PartialBool ι} {t : ℕ}
    (hfg : ∀ x b, f x = some b → g x = some b) (h : DLe g t) : DLe f t :=
  h.comap id hfg

/-! ## Tree witnesses -/

/-- A tree that is correct on the promise witnesses its own depth. -/
theorem DLe_of_tree {f : PartialBool ι} (T : QueryTree ι)
    (h : ∀ x b, f x = some b → T.eval x = b) : DLe f T.depth :=
  ⟨T, le_rfl, h⟩

/-- A function decided by the continuation that a bounded tree selects. -/
theorem DLe_of_graft {f : PartialBool ι} (T : QueryTree ι) (k : Bool → QueryTree ι) {s : ℕ}
    (hk : ∀ c, (k c).depth ≤ s)
    (h : ∀ x b, f x = some b → (k (T.eval x)).eval x = b) : DLe f (T.depth + s) := by
  refine ⟨T.graft k, (QueryTree.depth_graft_le T k).trans ?_, fun x b hx => ?_⟩
  · have := max_le (hk false) (hk true)
    omega
  · rw [QueryTree.eval_graft]
    exact h x b hx

/-- Query one coordinate, then decide by the sub-function it selects. -/
theorem DLe_of_query {f g₀ g₁ : PartialBool ι} (i : ι) {s : ℕ}
    (h₀ : DLe g₀ s) (h₁ : DLe g₁ s)
    (hf : ∀ x b, f x = some b → (if x i then g₁ x else g₀ x) = some b) : DLe f (s + 1) := by
  obtain ⟨l, hl, cl⟩ := h₀
  obtain ⟨r, hr, cr⟩ := h₁
  refine ⟨.query i l r, ?_, fun x b hx => ?_⟩
  · have := max_le hl hr
    simp only [QueryTree.depth_query]
    omega
  · have := hf x b hx
    rw [QueryTree.eval_query]
    cases hxi : x i
    · simpa [hxi] using cl x b (by simpa [hxi] using this)
    · simpa [hxi] using cr x b (by simpa [hxi] using this)

/-- Ledger: def-D. Reading every listed coordinate decides `f` once the list is
complete, whatever the promise. -/
theorem DLe_length (f : PartialBool ι) (l : List ι) (hl : ∀ i, i ∈ l) : DLe f l.length := by
  refine ⟨QueryTree.readList (fun x => (f x).getD false) l fun _ => false,
    QueryTree.depth_readList_le _ _ _, fun x b hx => ?_⟩
  rw [QueryTree.eval_readList _ _ _ _ fun i hi => absurd (hl i) hi, hx]
  rfl

/-- Ledger: def-D. The read-all tree: `D f ≤ n`, including an empty promise and an
empty coordinate type. -/
theorem DLe_card [Fintype ι] (f : PartialBool ι) : DLe f (Fintype.card ι) := by
  have h := DLe_length f (Finset.univ : Finset ι).toList (by simp)
  simpa using h

/-- Ledger: def-R. A deterministic tree is a one-tree mixture with no error. -/
theorem DLe.toRLe {f : PartialBool ι} {t : ℕ} (h : DLe f t) : RLe f t := by
  obtain ⟨T, hT, hc⟩ := h
  refine ⟨.ofTree T, by simpa using hT, fun x b hx => ?_⟩
  rw [RandomizedProgram.success_ofTree]
  norm_num [hc x b hx]

/-! ## Attainment -/

section Attainment

variable [Fintype ι]

theorem DLe_set_nonempty (f : PartialBool ι) : {t : ℕ | DLe f t}.Nonempty :=
  ⟨_, DLe_card f⟩

/-- The set defining `R` is nonempty, so `sInf` in `R` is a true minimum. -/
theorem RLe_set_nonempty (f : PartialBool ι) : {t : ℕ | RLe f t}.Nonempty :=
  ⟨_, (DLe_card f).toRLe⟩

/-- Ledger: def-R. The infimum is attained. -/
theorem RLe_R (f : PartialBool ι) : RLe f (R f) :=
  Nat.sInf_mem (RLe_set_nonempty f)

/-- Ledger: def-D. The infimum is attained. -/
theorem DLe_D (f : PartialBool ι) : DLe f (D f) :=
  Nat.sInf_mem (DLe_set_nonempty f)

theorem R_le_of_RLe {f : PartialBool ι} {t : ℕ} (h : RLe f t) : R f ≤ t :=
  Nat.sInf_le h

theorem D_le_of_DLe {f : PartialBool ι} {t : ℕ} (h : DLe f t) : D f ≤ t :=
  Nat.sInf_le h

/-- Ledger: def-R. `R` is the least budget, so upper bounds are `RLe` witnesses. -/
theorem R_le_iff {f : PartialBool ι} {t : ℕ} : R f ≤ t ↔ RLe f t :=
  ⟨(RLe_R f).mono, R_le_of_RLe⟩

/-- Ledger: def-D. `D` is the least budget. -/
theorem D_le_iff {f : PartialBool ι} {t : ℕ} : D f ≤ t ↔ DLe f t :=
  ⟨(DLe_D f).mono, D_le_of_DLe⟩

/-- Randomized cost is at most deterministic cost. -/
theorem R_le_D (f : PartialBool ι) : R f ≤ D f :=
  R_le_of_RLe (DLe_D f).toRLe

/-- Deterministic cost is at most the number of coordinates. -/
theorem D_le_card (f : PartialBool ι) : D f ≤ Fintype.card ι :=
  D_le_of_DLe (DLe_card f)

/-- Randomized cost is at most the number of coordinates. -/
theorem R_le_card (f : PartialBool ι) : R f ≤ Fintype.card ι :=
  (R_le_D f).trans (D_le_card f)

/-- Ledger: def-R. The form every lower bound uses: `t < R f` says exactly that no
budget up to `t` suffices. -/
theorem lt_R_iff {f : PartialBool ι} {t : ℕ} : t < R f ↔ ∀ s ≤ t, ¬ RLe f s := by
  constructor
  · intro h s hs hR
    exact absurd ((R_le_of_RLe hR).trans hs) (not_le.mpr h)
  · intro h
    by_contra hle
    exact h _ (not_lt.mp hle) (RLe_R f)

/-- Ledger: def-R. By monotonicity, one failing budget is enough. -/
theorem lt_R_of_not_RLe {f : PartialBool ι} {t : ℕ} (h : ¬ RLe f t) : t < R f :=
  lt_R_iff.mpr fun _ hs hR => h (hR.mono hs)

/-- Ledger: def-D. The deterministic form of `lt_R_iff`. -/
theorem lt_D_iff {f : PartialBool ι} {t : ℕ} : t < D f ↔ ∀ s ≤ t, ¬ DLe f s := by
  constructor
  · intro h s hs hD
    exact absurd ((D_le_of_DLe hD).trans hs) (not_le.mpr h)
  · intro h
    by_contra hle
    exact h _ (not_lt.mp hle) (DLe_D f)

/-- Ledger: def-D. By monotonicity, one failing budget is enough. -/
theorem lt_D_of_not_DLe {f : PartialBool ι} {t : ℕ} (h : ¬ DLe f t) : t < D f :=
  lt_D_iff.mpr fun _ hs hD => h (hD.mono hs)

end Attainment

/-! ## Renaming coordinates -/

/-- Renaming there and back returns the function. -/
theorem reindex_symm_reindex (e : ι ≃ κ) (f : PartialBool ι) :
    reindex e.symm (reindex e f) = f := by
  funext x
  simp [reindex]

/-- Ledger: def-partial-query. Renaming coordinates makes no queries. -/
theorem RLe_reindex_iff (e : ι ≃ κ) {f : PartialBool ι} {t : ℕ} :
    RLe (reindex e f) t ↔ RLe f t := by
  constructor
  · intro h
    have := h.comap (f := reindex e.symm (reindex e f)) e.symm fun _ _ hx => hx
    rwa [reindex_symm_reindex] at this
  · exact RLe.comap e fun _ _ hx => hx

/-- Ledger: def-partial-query. Renaming coordinates makes no queries. -/
theorem DLe_reindex_iff (e : ι ≃ κ) {f : PartialBool ι} {t : ℕ} :
    DLe (reindex e f) t ↔ DLe f t := by
  constructor
  · intro h
    have := h.comap (f := reindex e.symm (reindex e f)) e.symm fun _ _ hx => hx
    rwa [reindex_symm_reindex] at this
  · exact DLe.comap e fun _ _ hx => hx

/-- Ledger: def-R. `R` does not see the names of the coordinates. -/
theorem R_reindex [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι) :
    R (reindex e f) = R f := by
  simp only [R, RLe_reindex_iff]

/-- Ledger: def-D. `D` does not see the names of the coordinates. -/
theorem D_reindex [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι) :
    D (reindex e f) = D f := by
  simp only [D, DLe_reindex_iff]

end QuarticQuery
