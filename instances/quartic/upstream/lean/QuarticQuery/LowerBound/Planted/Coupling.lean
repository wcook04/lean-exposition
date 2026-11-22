module

public import QuarticQuery.Statement

/-!
# Runs of a decision tree

`T.path x` is the list of locations `T` queries on `x`, repeats included. Two
inputs that agree along the run on the first have the same output: this is the
coupling step of equation (18). The last lemma charges each query to at most one
column, which both counting bounds use.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {ι : Type}

namespace QueryTree

/-- The locations queried on `x`, in order, repeats included. -/
def path : QueryTree ι → BitInput ι → List ι
  | .leaf _, _ => []
  | .query i l r, x => i :: (if x i then r.path x else l.path x)

@[simp] theorem path_leaf (b : Bool) (x : BitInput ι) : (leaf b : QueryTree ι).path x = [] := rfl

theorem path_query (i : ι) (l r : QueryTree ι) (x : BitInput ι) :
    (query i l r).path x = i :: (if x i then r.path x else l.path x) := rfl

theorem length_path_le (T : QueryTree ι) (x : BitInput ι) : (T.path x).length ≤ T.depth := by
  induction T with
  | leaf b => simp
  | query i l r ihl ihr =>
    simp only [path_query, depth, List.length_cons]
    split_ifs <;> omega

/-- Ledger: eq-18. Different outputs force a query at a location where the two
inputs differ, on the run of the first input. -/
theorem exists_mem_path_ne (T : QueryTree ι) {x y : BitInput ι} (h : T.eval x ≠ T.eval y) :
    ∃ q ∈ T.path x, x q ≠ y q := by
  induction T with
  | leaf b => exact absurd rfl h
  | query i l r ihl ihr =>
    by_cases hi : x i = y i
    · simp only [QueryTree.eval, ← hi] at h
      cases hx : x i
      · obtain ⟨q, hq, hne⟩ := ihl (by simpa [hx] using h)
        exact ⟨q, by simp [path_query, hx, hq], hne⟩
      · obtain ⟨q, hq, hne⟩ := ihr (by simpa [hx] using h)
        exact ⟨q, by simp [path_query, hx, hq], hne⟩
    · exact ⟨i, by simp [path_query], hi⟩

end QueryTree

/-- If each location belongs to at most one class `a`, the class counts of a list
add up to at most its length. -/
theorem sum_countP_le_length {γ : Type} [Fintype γ] (c : γ → ι → Bool)
    (hc : ∀ a b q, c a q = true → c b q = true → a = b) (l : List ι) :
    ∑ a, l.countP (c a) ≤ l.length := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hone : ∑ a, (if c a q = true then 1 else 0) ≤ 1 := by
      rw [← card_filter]
      exact card_le_one.mpr fun a ha b hb => hc a b q (by simpa using ha) (by simpa using hb)
    simp only [List.countP_cons, sum_add_distrib, List.length_cons]
    omega

end QuarticQuery
