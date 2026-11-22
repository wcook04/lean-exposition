module

public import QuarticQuery.LowerBound.DirectProduct

/-!
# Original-path cap event for initially uncapped finite trees

Compiled as part of the `QuarticQuery` library target.

The compiler clips before the first excess query, including on contradictory
formal branches. The next-action-at-zero rule preserves an original terminal
answer. The theorem bounds the joint event 'success AND actual compliance',
not success conditional on compliance.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}

namespace OutTree

/-- Retain every allowed query, and stop *before* the first query over budget.
The fallback is used only when the original action is an excess query. -/
def clip {β : Type} (fallback : β) :
    OutTree (Fin r × κ) β → (Fin r → ℕ) → OutTree (Fin r × κ) β
  | .leaf a, _ => .leaf a
  | .query p left right, c =>
      if 0 < c p.1 then
        .query p
          (clip fallback left (Function.update c p.1 (c p.1 - 1)))
          (clip fallback right (Function.update c p.1 (c p.1 - 1)))
      else .leaf fallback

/-- Every formal branch of the clipped tree obeys every separate cap. -/
theorem clip_capped {β : Type} (fallback : β)
    (T : OutTree (Fin r × κ) β) (c : Fin r → ℕ) :
    (clip fallback T c).capped c := by
  induction T generalizing c with
  | leaf a => simp [clip, OutTree.capped]
  | query p l u ihl ihu =>
    by_cases hp : 0 < c p.1
    · simp only [clip, if_pos hp, OutTree.capped]
      exact ⟨hp, ihl _, ihu _⟩
    · simp [clip, hp, OutTree.capped]

/-- Recursive semantics of compliance on this *actual* input. On a query,
only the branch observed on this input matters. -/
def actualComplies {β : Type} :
    OutTree (Fin r × κ) β → (Fin r → ℕ) →
      BitInput (Fin r × κ) → Prop
  | .leaf _, _, _ => True
  | .query p l u, c, x =>
      0 < c p.1 ∧
        (if x p then
          actualComplies u (Function.update c p.1 (c p.1 - 1)) x
        else
          actualComplies l (Function.update c p.1 (c p.1 - 1)) x)

/-- The original output is preserved whenever its *actual* path complies.
This result is intentionally about one input, not an all-branches cap. -/
theorem clip_eval_eq_of_actualComplies {β : Type}
    (fallback : β) (T : OutTree (Fin r × κ) β)
    (c : Fin r → ℕ) (x : BitInput (Fin r × κ))
    (hc : actualComplies T c x) :
    (clip fallback T c).eval x = T.eval x := by
  induction T generalizing c with
  | leaf a => rfl
  | query p l u ihl ihu =>
    obtain ⟨hp, ht⟩ := hc
    simp only [clip, if_pos hp, OutTree.eval]
    cases hbit : x p <;> simp only [hbit, ite_true, ite_false] at ht ⊢
    · exact ihl _ ht
    · exact ihu _ ht

/-- The exact, ordered actual query transcript, including repetitions. -/
def actualPath {β : Type} :
    OutTree (Fin r × κ) β → BitInput (Fin r × κ) → List (Fin r × κ)
  | .leaf _, _ => []
  | .query p l u, x =>
      p :: (if x p then actualPath u x else actualPath l x)

/-- On a complying run, the complete actual trace is unchanged. -/
theorem clip_path_eq_of_actualComplies {β : Type}
    (fallback : β) (T : OutTree (Fin r × κ) β)
    (c : Fin r → ℕ) (x : BitInput (Fin r × κ))
    (hc : actualComplies T c x) :
    (clip fallback T c).actualPath x = T.actualPath x := by
  induction T generalizing c with
  | leaf a => rfl
  | query p l u ihl ihu =>
    obtain ⟨hp, ht⟩ := hc
    simp only [clip, if_pos hp, actualPath]
    cases hbit : x p <;> simp only [hbit, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · rw [ihl _ ht]
    · rw [ihu _ ht]

/-- Count *each* query, including a repeated query. This is the externally
observable resource count; see the ordinary proof for equivalence to the
recursive `actualComplies` predicate. -/
def actualCount {β : Type}
    (T : OutTree (Fin r × κ) β) (x : BitInput (Fin r × κ))
    (h : Fin r) : ℕ :=
  (actualPath T x).countP (fun p => decide (p.1 = h))

end OutTree

open scoped Classical in
/-- Weighted success AND actual compliance on the *original* tree. -/
noncomputable def compliantSuccess
    (f : PartialBool κ) (μ : BitInput κ → ℝ)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (c : Fin r → ℕ) : ℝ :=
  ∑ U : Fin r → BitInput κ,
    (∏ h, μ (U h)) *
      if T.actualComplies c (Function.uncurry U) ∧
         (∀ h, f (U h) = some (T.eval (Function.uncurry U) h))
      then 1 else 0

/-- Structural clipping turns a compliant successful original path into a
successful clipped path, for every fixed input tuple. -/
theorem compliantSuccess_le_clipped
    (f : PartialBool κ) (μ : BitInput κ → ℝ)
    (hμ : ∀ x, 0 ≤ μ x)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (c : Fin r → ℕ)
    (fallback : Fin r → Bool) :
    compliantSuccess f μ T c ≤ guessSuccess f (fun _ => μ) (T.clip fallback c) := by
  unfold compliantSuccess guessSuccess
  apply sum_le_sum
  intro U _
  apply mul_le_mul_of_nonneg_left
  · by_cases hc : T.actualComplies c (Function.uncurry U)
    · have eqv := OutTree.clip_eval_eq_of_actualComplies fallback T c (Function.uncurry U) hc
      simp only [hc, true_and]
      simp [eqv]
    · simp only [hc, false_and, ↓reduceIte]
      split_ifs <;> norm_num
  · exact prod_nonneg fun h _ => hμ (U h)

/-- Deterministic initially-uncapped tree: the joint success/compliance event
obeys the product bound.  No `T.capped` hypothesis is imposed on T. -/
theorem direct_product_realized_caps
    {f : PartialBool κ} {μ : BitInput κ → ℝ}
    {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) :
    compliantSuccess f μ T (fun _ => L) ≤ β ^ r := by
  let fallback : Fin r → Bool := fun _ => false
  calc
    _ ≤ guessSuccess f (fun _ => μ) (T.clip fallback (fun _ => L)) :=
      compliantSuccess_le_clipped f μ hμ T (fun _ => L) fallback
    _ ≤ β ^ r := direct_product hμ hard _ (OutTree.clip_capped fallback T _)

/-- Finite advice and coins, jointly distributed but independent of the entire
input tuple. Their weights need not split as a product of separate sources. -/
theorem direct_product_realized_caps_average
    {S : Type} [Fintype S]
    {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (T : S → OutTree (Fin r × κ) (Fin r → Bool)) :
    ∑ s, p s * compliantSuccess f μ (T s) (fun _ => L) ≤ β ^ r := by
  calc
    _ ≤ ∑ s, p s * β ^ r :=
      sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (direct_product_realized_caps hμ hard (T s)) (hp s)
    _ = β ^ r := by rw [← sum_mul, hp1, one_mul]

end QuarticQuery
