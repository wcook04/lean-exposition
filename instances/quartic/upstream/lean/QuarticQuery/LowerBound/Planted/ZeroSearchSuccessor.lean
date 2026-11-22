module

public import QuarticQuery.LowerBound.Planted.ZeroSearch

/-!
Compiled as part of the `QuarticQuery` library target.
A stronger finite-world charging invariant. The complete ordinary
induction and the exact finite tests are supplied separately.

-/

@[expose] public section
open Finset
namespace QuarticQuery
variable {ι α : Type} [DecidableEq α]

theorem zero_search_sum_successor (e : α → ι) (he : Function.Injective e) (c : ι → Bool)
    (hc1 : ∀ p, c (e p) = true) (hc2 : ∀ q, c q = true → ∃ p, e p = q)
    (x : α → BitInput ι) (hout : ∀ j j' q, c q = false → x j q = x j' q)
    (hin : ∀ j p, x j (e p) = decide (p ≠ j)) (T : QueryTree ι) (U : Finset α) :
    ((U.card : ℝ) + 1) * ∑ j ∈ U, ind (e j ∈ T.path (x j)) ≤
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
        calc ((U.card : ℝ) + 1) * ∑ j ∈ U, ind (e j ∈ (QueryTree.query (e p) l u).path (x j))
            = ((U.card : ℝ) + 1) * ∑ j ∈ U, ind (e j ∈ u.path (x j)) := by
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
          (((U.card : ℝ) + 1) * ∑ j ∈ U, ind (e j ∈ sub.path (x j)) ≤
            2 * ∑ j ∈ U, ((sub.path (x j)).countP c : ℝ)) →
          ((U.card : ℝ) + 1) * ∑ j ∈ U, ind (e j ∈ (QueryTree.query q l u).path (x j)) ≤
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

end QuarticQuery
