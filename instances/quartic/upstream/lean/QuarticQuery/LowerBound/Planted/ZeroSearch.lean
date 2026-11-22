module

public import QuarticQuery.LowerBound.Planted.Average
public import QuarticQuery.LowerBound.Planted.Coupling
public import QuarticQuery.LowerBound.Planted.Inputs

/-!
# Finding the removed zero (equation 19)

This does not follow the paper's conditional early/late bookkeeping, and it is
not the route suggested in the plan either. It is shorter than both. Fix one
column and everything outside it, and let the position `j` of the zero vary over
all `M` positions. Induction on the tree, with no conditioning, gives

  `M * #{j : the run with zero at j finds it} ≤ 2 * ∑ j, (queries to the column)`.

At a query to position `p`, the worlds with zero elsewhere all continue to the
same subtree and each pays one query, which is at least as much as the new
discovery costs. Averaging over `j` by `avg_resample` and adding over columns
gives `E Z ≤ 2 G / m`, so equation (19) holds with `2 G / m²`, a factor two better
than the paper's `4 G / m²`.
-/

@[expose] public section

open Finset

namespace QuarticQuery

section Abstract

variable {ι α : Type} [DecidableEq α]

/-- Ledger: eq-19. The worlds `x j`, `j ∈ U`, differ only on a column `e`, where
`x j` has its single zero at `j`. A run can be charged, over all worlds in `U`,
for at least half of `|U|` times the number of worlds in which it finds its zero. -/
theorem zero_search_sum (e : α → ι) (he : Function.Injective e) (c : ι → Bool)
    (hc1 : ∀ p, c (e p) = true) (hc2 : ∀ q, c q = true → ∃ p, e p = q)
    (x : α → BitInput ι) (hout : ∀ j j' q, c q = false → x j q = x j' q)
    (hin : ∀ j p, x j (e p) = decide (p ≠ j)) (T : QueryTree ι) (U : Finset α) :
    (U.card : ℝ) * ∑ j ∈ U, ind (e j ∈ T.path (x j)) ≤
      2 * ∑ j ∈ U, ((T.path (x j)).countP c : ℝ) := by
  induction T generalizing U with
  | leaf b => simp [ind_false]
  | query q l u ihl ihu =>
    by_cases hq : c q = true
    · obtain ⟨p, rfl⟩ := hc2 q hq
      have hne : ∀ j, j ≠ p → (QueryTree.query (e p) l u).path (x j) =
          e p :: u.path (x j) := fun j hj => by
        simp [QueryTree.path_query, hin, Ne.symm hj]
      have hind : ∀ j, j ≠ p → ind (e j ∈ (QueryTree.query (e p) l u).path (x j)) =
          ind (e j ∈ u.path (x j)) := fun j hj => by
        rw [hne j hj]
        have : e j ≠ e p := fun h => hj (he h)
        simp [List.mem_cons, this]
      have hcnt : ∀ j, j ≠ p → (((QueryTree.query (e p) l u).path (x j)).countP c : ℝ) =
          ((u.path (x j)).countP c : ℝ) + 1 := fun j hj => by
        rw [hne j hj, List.countP_cons]
        simp [hc1]
      by_cases hp : p ∈ U
      · have hcard : (U.card : ℝ) = ((U.erase p).card : ℝ) + 1 := by
          rw [card_erase_add_one hp |>.symm]
          push_cast
          ring
        have hN : ∑ j ∈ U, ind (e j ∈ (QueryTree.query (e p) l u).path (x j)) =
            1 + ∑ j ∈ U.erase p, ind (e j ∈ u.path (x j)) := by
          rw [← add_sum_erase U _ hp, ind_true (by simp [QueryTree.path_query])]
          congr 1
          exact sum_congr rfl fun j hj => hind j (ne_of_mem_erase hj)
        have hS : ∑ j ∈ U, (((QueryTree.query (e p) l u).path (x j)).countP c : ℝ) ≥
            1 + ∑ j ∈ U.erase p, (((u.path (x j)).countP c : ℝ) + 1) := by
          rw [← add_sum_erase U _ hp]
          have h1 : (1 : ℝ) ≤ (((QueryTree.query (e p) l u).path (x p)).countP c : ℝ) := by
            have : 1 ≤ ((QueryTree.query (e p) l u).path (x p)).countP c := by
              rw [QueryTree.path_query, List.countP_cons]
              simp [hc1]
            exact_mod_cast this
          have h2 : ∑ j ∈ U.erase p, (((QueryTree.query (e p) l u).path (x j)).countP c : ℝ) =
              ∑ j ∈ U.erase p, (((u.path (x j)).countP c : ℝ) + 1) :=
            sum_congr rfl fun j hj => hcnt j (ne_of_mem_erase hj)
          rw [h2]
          linarith
        have hS' : ∑ j ∈ U.erase p, (((u.path (x j)).countP c : ℝ) + 1) =
            ∑ j ∈ U.erase p, ((u.path (x j)).countP c : ℝ) + ((U.erase p).card : ℝ) := by
          rw [sum_add_distrib]
          simp
        have hbound : ∑ j ∈ U.erase p, ind (e j ∈ u.path (x j)) ≤ ((U.erase p).card : ℝ) := by
          calc _ ≤ ∑ _j ∈ U.erase p, (1 : ℝ) := sum_le_sum fun j _ => ind_le_one _
            _ = _ := by simp
        have hih := ihu (U.erase p)
        rw [hN, hcard]
        set N := ∑ j ∈ U.erase p, ind (e j ∈ u.path (x j))
        set M := ((U.erase p).card : ℝ)
        set S := ∑ j ∈ U.erase p, ((u.path (x j)).countP c : ℝ)
        rw [hS'] at hS
        nlinarith
      · have hmem : ∀ j ∈ U, j ≠ p := fun j hj h => hp (h ▸ hj)
        calc (U.card : ℝ) * ∑ j ∈ U, ind (e j ∈ (QueryTree.query (e p) l u).path (x j))
            = (U.card : ℝ) * ∑ j ∈ U, ind (e j ∈ u.path (x j)) := by
              rw [sum_congr rfl fun j hj => hind j (hmem j hj)]
          _ ≤ 2 * ∑ j ∈ U, ((u.path (x j)).countP c : ℝ) := ihu U
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (sum_le_sum fun j hj => ?_) (by norm_num)
              rw [hcnt j (hmem j hj)]
              linarith
    · have hq' : c q = false := by simpa using hq
      rcases U.eq_empty_or_nonempty with rfl | ⟨j0, hj0⟩
      · simp
      have hneq : ∀ j, e j ≠ q := fun j h => hq (h ▸ hc1 j)
      have hcase : ∀ (sub : QueryTree ι), (∀ j, (QueryTree.query q l u).path (x j) =
          q :: sub.path (x j)) →
          ((U.card : ℝ) * ∑ j ∈ U, ind (e j ∈ sub.path (x j)) ≤
            2 * ∑ j ∈ U, ((sub.path (x j)).countP c : ℝ)) →
          (U.card : ℝ) * ∑ j ∈ U, ind (e j ∈ (QueryTree.query q l u).path (x j)) ≤
            2 * ∑ j ∈ U, (((QueryTree.query q l u).path (x j)).countP c : ℝ) := by
        intro sub hsub hih
        have h1 : ∀ j, ind (e j ∈ (QueryTree.query q l u).path (x j)) =
            ind (e j ∈ sub.path (x j)) := fun j => by
          rw [hsub j]
          simp [List.mem_cons, hneq j]
        have h2 : ∀ j, (((QueryTree.query q l u).path (x j)).countP c : ℝ) =
            ((sub.path (x j)).countP c : ℝ) := fun j => by
          rw [hsub j, List.countP_cons]
          simp [hq']
        simpa only [h1, h2] using hih
      cases hb : x j0 q
      · exact hcase l (fun j => by
          simp [QueryTree.path_query, hout j j0 q hq', hb]) (ihl U)
      · exact hcase u (fun j => by
          simp [QueryTree.path_query, hout j j0 q hq', hb]) (ihu U)

end Abstract

section Concrete

variable {κ : Type} {ℓ r S : ℕ}

/-- The uniform weight on columns. -/
noncomputable def unif (ℓ : ℕ) (_ : Column ℓ) : ℝ := 1 / ((2 ^ ℓ : ℕ) : ℝ)

theorem colCard_pos (ℓ : ℕ) : (0 : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by positivity

theorem unif_nonneg (ℓ : ℕ) (c : Column ℓ) : 0 ≤ unif ℓ c := by
  unfold unif
  positivity

theorem sum_unif (ℓ : ℕ) : ∑ c, unif ℓ c = 1 := by
  have h := (colCard_pos ℓ).ne'
  simp only [unif, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem avg_unif (ℓ : ℕ) (g : Column ℓ → ℝ) :
    avg (unif ℓ) g = 1 / ((2 ^ ℓ : ℕ) : ℝ) * ∑ c, g c := by
  simp only [avg, unif, mul_sum]

/-- Ledger: eq-19. The run on `Y⁽⁰⁾` finds the zero of column `i`. -/
noncomputable def foundZero (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (i : Column ℓ) : ℝ :=
  ind (.inl (i, J i) ∈ T.path (dummy J A))

/-- Queries of the run on `Y⁽⁰⁾` to `X_i`. -/
noncomputable def xQueries (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (i : Column ℓ) : ℝ :=
  ((T.path (dummy J A)).countP (xColumn i) : ℝ)

/-- Ledger: eq-19. `zero_search_sum` for one column of the dummy input. -/
theorem column_zero_bound (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (i : Column ℓ) :
    ((2 ^ ℓ : ℕ) : ℝ) * ∑ j, foundZero T A (Function.update J i j) i ≤
      2 * ∑ j, xQueries T A (Function.update J i j) i := by
  have h := zero_search_sum (ι := BitLoc ℓ r S κ) (α := Column ℓ) (fun p => .inl (i, p))
    (fun a b h => by simpa using h) (xColumn i) (fun p => by simp [xColumn])
    (fun q hq => by
      rcases q with ⟨c, p⟩ | q
      · have : c = i := by simpa [xColumn] using hq
        subst this
        exact ⟨p, rfl⟩
      · simp [xColumn] at hq)
    (fun j => dummy (Function.update J i j) A)
    (fun j j' q hq => by
      rcases q with ⟨c, p⟩ | ⟨a, h, q⟩ | q
      · have hc : c ≠ i := by simpa [xColumn] using hq
        simp [dummy, Function.update_of_ne hc]
      · rfl
      · rfl)
    (fun j p => by simp [dummy]) T univ
  simpa [foundZero, xQueries, Fintype.card_fin] using h

variable (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)

/-- Ledger: eq-19. Column by column, after averaging over `J`. -/
theorem avg_foundZero_le (i : Column ℓ) :
    avg (prodW (unif ℓ)) (fun J => foundZero T A J i) ≤
      2 / ((2 ^ ℓ : ℕ) : ℝ) * avg (prodW (unif ℓ)) (fun J => xQueries T A J i) := by
  rw [avg_resample (sum_unif ℓ) i (fun J => foundZero T A J i),
    avg_resample (sum_unif ℓ) i (fun J => xQueries T A J i), ← avg_mul_left]
  refine avg_mono (prodW_nonneg (unif_nonneg ℓ)) fun J => ?_
  rw [avg_unif, avg_unif]
  have hm := colCard_pos ℓ
  have h := column_zero_bound T A J i
  set M : ℝ := ((2 ^ ℓ : ℕ) : ℝ)
  set Z := ∑ j, foundZero T A (Function.update J i j) i
  set Q := ∑ j, xQueries T A (Function.update J i j) i
  have hinv : 0 ≤ 1 / M * (1 / M) := by positivity
  calc 1 / M * Z = 1 / M * (1 / M) * (M * Z) := by field_simp
    _ ≤ 1 / M * (1 / M) * (2 * Q) := mul_le_mul_of_nonneg_left h hinv
    _ = 2 / M * (1 / M * Q) := by ring

/-- Ledger: eq-19. The number of queries bounds the sum over columns. -/
theorem sum_xQueries_le (J : Column ℓ → Column ℓ) :
    ∑ i, xQueries T A J i ≤ (T.depth : ℝ) := by
  have h := sum_countP_le_length (γ := Column ℓ) (fun i => xColumn (r := r) (S := S) (κ := κ) i)
    (fun a b q ha hb => by
      rcases q with ⟨c, p⟩ | q
      · have h1 : c = a := by simpa [xColumn] using ha
        have h2 : c = b := by simpa [xColumn] using hb
        exact h1.symm.trans h2
      · simp [xColumn] at ha) (T.path (dummy J A))
  have h' := h.trans (T.length_path_le _)
  have : (∑ i, (T.path (dummy J A)).countP (xColumn i) : ℕ) ≤ T.depth := h'
  unfold xQueries
  exact_mod_cast this

/-- Ledger: eq-19. Over `J` and the independent uniform `I`, the dummy run reaches
the removed zero with probability at most `2 G / m²`. -/
theorem avg_foundZero_I_le {G : ℕ} (hT : T.depth ≤ G) :
    avg (prodW (unif ℓ)) (fun J => avg (unif ℓ) (foundZero T A J)) ≤
      2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
  have hm := colCard_pos ℓ
  set M : ℝ := ((2 ^ ℓ : ℕ) : ℝ) with hM
  rw [avg_comm]
  calc avg (unif ℓ) (fun I => avg (prodW (unif ℓ)) fun J => foundZero T A J I)
      ≤ avg (unif ℓ) (fun I => 2 / M * avg (prodW (unif ℓ)) fun J => xQueries T A J I) :=
        avg_mono (unif_nonneg ℓ) (avg_foundZero_le T A)
    _ = 2 / M * avg (prodW (unif ℓ)) (fun J => avg (unif ℓ) (xQueries T A J)) := by
        rw [avg_mul_left, avg_comm (unif ℓ) (prodW (unif ℓ))]
    _ ≤ 2 / M * ((G : ℝ) / M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine avg_le_const (prodW_nonneg (unif_nonneg ℓ)) (sum_prodW (sum_unif ℓ)) fun J => ?_
        rw [avg_unif, ← hM]
        have h1 := sum_xQueries_le T A J
        have h2 : (T.depth : ℝ) ≤ G := by exact_mod_cast hT
        calc 1 / M * ∑ i, xQueries T A J i ≤ 1 / M * (G : ℝ) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
          _ = (G : ℝ) / M := by ring
    _ = 2 * (G : ℝ) / M ^ 2 := by field_simp

end Concrete

end QuarticQuery
