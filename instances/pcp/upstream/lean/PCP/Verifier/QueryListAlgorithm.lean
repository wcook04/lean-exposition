/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CostModel
import PCP.Verifier.QueryList

/-!
# The answer-history procedure for finite query-list compilation

The procedure asks for the next listed address until all answers are available,
then applies the verdict to the collected answers extended by false. Updates
are nested in list order, so the earliest occurrence of a repeated address
takes precedence even in an inconsistent hypothetical history. Consequently
unfolding this procedure gives exactly the previously defined compiled tree,
not merely an equivalent evaluation on consistent oracle answers.

The supplied verdict functional is unrestricted. This construction and its exact
implementation identity make no computability or running-time claim about it.
-/

namespace PCP.QueryTree

/-- Consume addresses and answers together, retaining the compiler's update order. -/
def listStep : List ℕ → (ProofOracle → Bool) → List Bool → Bool ⊕ ℕ
  | [], f, _ => .inl (f (fun _ => false))
  | a :: _, _, [] => .inr a
  | a :: qs, f, b :: bs => listStep qs (fun π => f (Function.update π a b)) bs

/-- Collected answers with false defaults and earliest-occurrence precedence. -/
def answersOracle : List ℕ → List Bool → ProofOracle
  | [], _ => fun _ => false
  | _ :: _, [] => fun _ => false
  | a :: qs, b :: bs => Function.update (answersOracle qs bs) a b

/-- Before exhaustion, the next query is exactly the position indexed by history length. -/
theorem listStep_next (qs : List ℕ) (f : ProofOracle → Bool) (as : List Bool)
    (h : as.length < qs.length) : listStep qs f as = .inr qs[as.length] := by
  induction qs generalizing f as with
  | nil => simp at h
  | cons a qs ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      exact ih _ bs (by simpa using h)

/-- Once all queries have answers, the procedure returns the intended finite-history verdict. -/
theorem listStep_halt (qs : List ℕ) (f : ProofOracle → Bool) (as : List Bool)
    (h : qs.length ≤ as.length) : listStep qs f as = .inl (f (answersOracle qs as)) := by
  induction qs generalizing f as with
  | nil => rfl
  | cons a qs ih =>
    cases as with
    | nil => simp at h
    | cons b bs =>
      exact ih _ bs (by simpa using h)

/-- A fixed prefix can be moved from the unfolding state into the step function. -/
theorem ofStep_prefix (step : List Bool → Bool ⊕ ℕ) (history : List Bool)
    (d : ℕ) (as : List Bool) :
    ofStep step d (history ++ as) = ofStep (fun bs => step (history ++ bs)) d as := by
  induction d generalizing as with
  | zero => rfl
  | succ d ih =>
    simp only [ofStep]
    cases step (history ++ as) with
    | inl b => rfl
    | inr a =>
      simp only [List.append_assoc, ih]

/-- Consuming the first answer transforms the verdict exactly as the compiler does. -/
theorem ofStep_listStep_cons (a : ℕ) (qs : List ℕ) (f : ProofOracle → Bool)
    (b : Bool) (d : ℕ) (as : List Bool) :
    ofStep (listStep (a :: qs) f) d (b :: as) =
      ofStep (listStep qs (fun π => f (Function.update π a b))) d as := by
  exact ofStep_prefix (listStep (a :: qs) f) [b] d as

/-- Exact tree identity, requiring neither consistent histories nor a dependency hypothesis. -/
theorem ofStep_listStep (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) : ofStep (listStep qs f) d [] = compileBounded qs f h := by
  induction qs generalizing f d with
  | nil => cases d <;> simp [ofStep, listStep, compileBounded, compile, weaken]
  | cons a qs ih =>
    cases d with
    | zero => simp at h
    | succ d =>
      simp only [ofStep, listStep, List.nil_append, compileBounded, compile, weaken]
      congr 1
      · rw [ofStep_listStep_cons]
        exact ih _ (by simpa using h)
      · rw [ofStep_listStep_cons]
        exact ih _ (by simpa using h)

/-- The procedure's actual execution asks precisely the listed queries. -/
theorem queryTrace_ofStep_listStep (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) (π : ProofOracle) :
    (ofStep (listStep qs f) d []).queryTrace π = qs := by
  rw [ofStep_listStep qs f h, queryTrace_compileBounded]

/-- The finite-word adapter uses the same concrete history procedure. -/
def wordStep {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool) :
    List Bool → Bool ⊕ ℕ :=
  listStep (qs.map Fin.val) (fun π => f (wordOfOracle P π))

theorem ofStep_wordStep {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool)
    {d : ℕ} (h : qs.length ≤ d) :
    ofStep (wordStep qs f) d [] = compileWordBounded qs f h :=
  ofStep_listStep _ _ (by simpa using h)

end PCP.QueryTree
