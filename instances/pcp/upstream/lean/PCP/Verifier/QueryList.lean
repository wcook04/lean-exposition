/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Verifier.Definition

/-!
# Compiling a finite query list into a Boolean query tree

The compiler queries every listed address in order. At a leaf it evaluates the
verdict on the answers collected along that path, extending them by false at
unqueried addresses. If the verdict depends only on the listed addresses, this
tree has exactly the intended oracle semantics. Duplicate addresses are allowed.

The construction certifies bit-query depth and the set of possible addresses;
it does not certify the running time of the supplied verdict functional.
-/

namespace PCP.QueryTree

/-- The verdict is determined by agreement at every listed address. -/
def DependsOn (qs : List ℕ) (f : ProofOracle → Bool) : Prop :=
  ∀ π π', (∀ a ∈ qs, π a = π' a) → f π = f π'

/-- Read the given addresses, filling unqueried positions with false at each leaf. -/
def compile : (qs : List ℕ) → (ProofOracle → Bool) → QueryTree qs.length
  | [], f => .leaf (f (fun _ => false))
  | a :: qs, f => .query a
      (compile qs (fun π => f (Function.update π a false)))
      (compile qs (fun π => f (Function.update π a true)))

private theorem DependsOn.update {qs : List ℕ} {a : ℕ} {f : ProofOracle → Bool}
    (hf : DependsOn (a :: qs) f) (b : Bool) :
    DependsOn qs (fun π => f (Function.update π a b)) := by
  intro π π' h
  apply hf
  intro x hx
  by_cases hxa : x = a
  · subst x
    simp
  · simp only [Function.update_of_ne hxa]
    exact h x ((List.mem_cons.mp hx).resolve_left hxa)

/-- The compiled tree evaluates the actual verdict on every oracle. -/
theorem eval_compile (qs : List ℕ) (f : ProofOracle → Bool) (hf : DependsOn qs f)
    (π : ProofOracle) : (compile qs f).eval π = f π := by
  induction qs generalizing f with
  | nil =>
    exact hf (fun _ => false) π (by simp)
  | cons a qs ih =>
    simp only [compile, eval]
    cases h : π a
    · simp only [Bool.false_eq_true, ite_false]
      rw [ih _ (hf.update false)]
      simpa only [h] using congrArg f (Function.update_eq_self a π)
    · simp only [ite_true]
      rw [ih _ (hf.update true)]
      simpa only [h] using congrArg f (Function.update_eq_self a π)

/-- Every listed address occurs, and no other address occurs. -/
@[simp] theorem addresses_compile (qs : List ℕ) (f : ProofOracle → Bool) :
    (compile qs f).addresses = qs.toFinset := by
  induction qs generalizing f with
  | nil => rfl
  | cons a qs ih => simp [compile, addresses, ih]

theorem mem_addresses_compile_iff (qs : List ℕ) (f : ProofOracle → Bool) (a : ℕ) :
    a ∈ (compile qs f).addresses ↔ a ∈ qs := by simp

/-- Addresses read on a particular execution, retaining order and repetitions. -/
def queryTrace : {d : ℕ} → QueryTree d → ProofOracle → List ℕ
  | _, .leaf _, _ => []
  | _, .query a f t, π => a :: (if π a then queryTrace t π else queryTrace f π)

/-- Every execution queries exactly the supplied list, including duplicates. -/
@[simp] theorem queryTrace_compile (qs : List ℕ) (f : ProofOracle → Bool)
    (π : ProofOracle) : (compile qs f).queryTrace π = qs := by
  induction qs generalizing f with
  | nil => rfl
  | cons a qs ih => simp [compile, queryTrace, ih]

/-- Increase the depth bound without changing the tree's actual queries or leaves. -/
def weaken : {d e : ℕ} → d ≤ e → QueryTree d → QueryTree e
  | _, _, _, .leaf b => .leaf b
  | _ + 1, 0, h, .query _ _ _ => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, h, .query a f t =>
      .query a (weaken (Nat.le_of_succ_le_succ h) f) (weaken (Nat.le_of_succ_le_succ h) t)

@[simp] theorem eval_weaken {d e : ℕ} (h : d ≤ e) (T : QueryTree d) (π : ProofOracle) :
    (weaken h T).eval π = T.eval π := by
  induction T generalizing e with
  | leaf b => simp only [weaken, eval]
  | @query d a f t hf ht =>
    cases e with
    | zero => omega
    | succ e => simp only [weaken, eval, hf, ht]

@[simp] theorem addresses_weaken {d e : ℕ} (h : d ≤ e) (T : QueryTree d) :
    (weaken h T).addresses = T.addresses := by
  induction T generalizing e with
  | leaf b => simp only [weaken, addresses]
  | @query d a f t hf ht =>
    cases e with
    | zero => omega
    | succ e => simp only [weaken, addresses, hf, ht]

@[simp] theorem queryTrace_weaken {d e : ℕ} (h : d ≤ e) (T : QueryTree d)
    (π : ProofOracle) : (weaken h T).queryTrace π = T.queryTrace π := by
  induction T generalizing e with
  | leaf b => simp only [weaken, queryTrace]
  | @query d a f t hf ht =>
    cases e with
    | zero => omega
    | succ e => simp only [weaken, queryTrace, hf, ht]

/-- Compile a list whose length is at most the required common query budget. -/
def compileBounded (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) : QueryTree d := weaken h (compile qs f)

theorem eval_compileBounded (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) (hf : DependsOn qs f) (π : ProofOracle) :
    (compileBounded qs f h).eval π = f π := by
  rw [compileBounded, eval_weaken, eval_compile qs f hf]

@[simp] theorem addresses_compileBounded (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) : (compileBounded qs f h).addresses = qs.toFinset := by
  simp [compileBounded]

@[simp] theorem queryTrace_compileBounded (qs : List ℕ) (f : ProofOracle → Bool) {d : ℕ}
    (h : qs.length ≤ d) (π : ProofOracle) : (compileBounded qs f h).queryTrace π = qs := by
  simp [compileBounded]

/-- A bound on the supplied addresses is a bound on every reachable address. -/
theorem addresses_compileBounded_lt (qs : List ℕ) (f : ProofOracle → Bool) {d N : ℕ}
    (h : qs.length ≤ d) (hN : ∀ a ∈ qs, a < N) :
    ∀ a ∈ (compileBounded qs f h).addresses, a < N := by
  simpa only [addresses_compileBounded, List.mem_toFinset] using hN

/-- Restrict an ordinary proof oracle to a finite Boolean word. -/
def wordOfOracle (P : ℕ) (π : ProofOracle) : Fin P → Bool := fun a => π a.val

/-- A finite-word verdict depends only on the given finite-word addresses. -/
def WordDependsOn {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool) : Prop :=
  ∀ w w', (∀ a ∈ qs, w a = w' a) → f w = f w'

private theorem WordDependsOn.to_oracle {P : ℕ} {qs : List (Fin P)}
    {f : (Fin P → Bool) → Bool} (hf : WordDependsOn qs f) :
    DependsOn (qs.map Fin.val) (fun π => f (wordOfOracle P π)) := by
  intro π π' h
  apply hf
  intro a ha
  exact h a.val (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Compile a finite-word query list directly into the original natural-address tree. -/
def compileWordBounded {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool)
    {d : ℕ} (h : qs.length ≤ d) : QueryTree d :=
  compileBounded (qs.map Fin.val) (fun π => f (wordOfOracle P π)) (by simpa using h)

theorem eval_compileWordBounded {P : ℕ} (qs : List (Fin P))
    (f : (Fin P → Bool) → Bool) {d : ℕ} (h : qs.length ≤ d)
    (hf : WordDependsOn qs f) (π : ProofOracle) :
    (compileWordBounded qs f h).eval π = f (wordOfOracle P π) :=
  eval_compileBounded _ _ _ hf.to_oracle π

@[simp] theorem addresses_compileWordBounded {P : ℕ} (qs : List (Fin P))
    (f : (Fin P → Bool) → Bool) {d : ℕ} (h : qs.length ≤ d) :
    (compileWordBounded qs f h).addresses = (qs.map Fin.val).toFinset := by
  simp [compileWordBounded]

/-- The resulting tree reads only the finite word's actual positions. -/
theorem addresses_compileWordBounded_lt {P : ℕ} (qs : List (Fin P))
    (f : (Fin P → Bool) → Bool) {d : ℕ} (h : qs.length ≤ d) :
    ∀ a ∈ (compileWordBounded qs f h).addresses, a < P := by
  apply addresses_compileBounded_lt
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact b.isLt

/-- Finite-word compilation with exactly the list's length as its depth bound. -/
def compileWord {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool) :
    QueryTree qs.length := compileWordBounded qs f le_rfl

theorem eval_compileWord {P : ℕ} (qs : List (Fin P)) (f : (Fin P → Bool) → Bool)
    (hf : WordDependsOn qs f) (π : ProofOracle) :
    (compileWord qs f).eval π = f (wordOfOracle P π) :=
  eval_compileWordBounded qs f le_rfl hf π

end PCP.QueryTree
