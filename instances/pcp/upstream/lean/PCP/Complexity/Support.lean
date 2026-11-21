import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite symbol support

## The problem

`FinTM2` requires finitely many stack indices, labels and internal states, and a finite **input**
stack alphabet — but says nothing about the other stacks. An auxiliary alphabet may be infinite.

It does not follow that an execution can use infinitely many symbols. A symbol only ever reaches a
stack by being pushed, each push is a function `σ → Γ k` with `σ` finite, and there are finitely
many push occurrences across finitely many labels. So a *fixed finite* set of symbols suffices for
each stack, determined by the machine alone — not by the input, and not by how long it runs.

This module proves that. It is the prerequisite for recoding a machine over finite alphabets, which
is in turn what effective simulation needs.

## Why an inductive predicate

`Pushes` is an inductive relation rather than a `Set`-valued structural recursion. The recursion
would need `if h : k = j then h ▸ Set.range f else ∅` — a transport across a dependent family at
every push. The inductive's `here` constructor fixes the index by construction, so membership
proofs carry no casts, and those are what §5B uses constantly.

The price is paid once, in `pushSet_finite`, where inverting the relation at a *different* index
does
require a case split. That is the right place for it.

## Scope

This module is generic: mathlib only, no PCP encoder, no machine construction. It establishes a
finite over-approximation of the reachable symbols and its preservation along executions. It does
**not** recode anything — that is §5C — and a finite support is not by itself an effective
simulation.
-/

namespace PCP.Machine

open Turing Turing.TM2

attribute [local instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin
  Turing.FinTM2.ΛFin Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-! ## A: the symbols a statement can push

This is an **over-approximation**, deliberately. `Pushes` collects a push occurring under a branch
whose condition is never true, and collects a push function's value at *every* internal state,
including states no run ever enters. That is exactly what makes it determined by the program's push
functions over the finite internal state type, independently of any execution — and it is all the
support theorem needs.

"Determined by the program" is not "effectively enumerable". The push functions are arbitrary
mathematical fields of `FinTM2`, the alphabets are unrestricted, and the `Fintype` instance derived
from this finiteness is noncomputable. No executable collector is claimed or supplied; an effective
construction would need representation assumptions this module does not make.

No constructor recurses through labels: `goto` and `halt` push nothing, so the traversal stops
exactly where a counted step stops. -/

/-- `Pushes q k c` : executing statement `q` can push symbol `c` onto stack `k`. -/
inductive Pushes : Stmt Γ Λ σ → (k : K) → Γ k → Prop
  | here {k : K} (f : σ → Γ k) (q : Stmt Γ Λ σ) (v : σ) : Pushes (.push k f q) k (f v)
  | push {k j : K} (f : σ → Γ k) {q : Stmt Γ Λ σ} {c : Γ j} :
      Pushes q j c → Pushes (.push k f q) j c
  | peek {k j : K} (f : σ → Option (Γ k) → σ) {q : Stmt Γ Λ σ} {c : Γ j} :
      Pushes q j c → Pushes (.peek k f q) j c
  | pop {k j : K} (f : σ → Option (Γ k) → σ) {q : Stmt Γ Λ σ} {c : Γ j} :
      Pushes q j c → Pushes (.pop k f q) j c
  | load (a : σ → σ) {q : Stmt Γ Λ σ} {j : K} {c : Γ j} :
      Pushes q j c → Pushes (.load a q) j c
  | branchL (f : σ → Bool) {q₁ q₂ : Stmt Γ Λ σ} {j : K} {c : Γ j} :
      Pushes q₁ j c → Pushes (.branch f q₁ q₂) j c
  | branchR (f : σ → Bool) {q₁ q₂ : Stmt Γ Λ σ} {j : K} {c : Γ j} :
      Pushes q₂ j c → Pushes (.branch f q₁ q₂) j c

/-- The symbols a statement can push onto stack `j`. -/
def pushSet (q : Stmt Γ Λ σ) (j : K) : Set (Γ j) := {c | Pushes q j c}

@[simp] theorem pushSet_goto (f : σ → Λ) (j : K) : pushSet (Stmt.goto f) j = (∅ : Set (Γ j)) := by
  ext c; constructor
  · rintro ⟨⟩
  · exact fun h => h.elim

@[simp] theorem pushSet_halt (j : K) : pushSet (Stmt.halt : Stmt Γ Λ σ) j = (∅ : Set (Γ j)) := by
  ext c; constructor
  · rintro ⟨⟩
  · exact fun h => h.elim

/-- **Finite support.**  Each stack receives only finitely many distinct symbols from a fixed
statement — even when its alphabet is infinite — because `σ` is finite and there are finitely many
push occurrences. -/
theorem pushSet_finite [DecidableEq K] [Fintype σ] :
    ∀ (q : Stmt Γ Λ σ) (j : K), (pushSet q j).Finite
  | .push k f q, j => by
      by_cases h : k = j
      · subst h
        have hsub : pushSet (Stmt.push k f q) k ⊆ Set.range f ∪ pushSet q k := by
          rintro c hc
          cases hc with
          | here f q v => exact Or.inl ⟨v, rfl⟩
          | push f hq => exact Or.inr hq
        exact Set.Finite.subset ((Set.finite_range f).union (pushSet_finite q k)) hsub
      · have hsub : pushSet (Stmt.push k f q) j ⊆ pushSet q j := by
          rintro c hc
          cases hc with
          | here f q v => exact absurd rfl h
          | push f hq => exact hq
        exact Set.Finite.subset (pushSet_finite q j) hsub
  | .peek k f q, j => by
      refine Set.Finite.subset (pushSet_finite q j) ?_
      rintro c hc; cases hc with | peek f hq => exact hq
  | .pop k f q, j => by
      refine Set.Finite.subset (pushSet_finite q j) ?_
      rintro c hc; cases hc with | pop f hq => exact hq
  | .load a q, j => by
      refine Set.Finite.subset (pushSet_finite q j) ?_
      rintro c hc; cases hc with | load a hq => exact hq
  | .branch f q₁ q₂, j => by
      refine Set.Finite.subset ((pushSet_finite q₁ j).union (pushSet_finite q₂ j)) ?_
      rintro c hc
      cases hc with
      | branchL f hq => exact Or.inl hq
      | branchR f hq => exact Or.inr hq
  | .goto f, j => by simp
  | .halt, j => by simp

/-! ### Machine-wide support

A symbol is supported at stack `k` if the *syntax* allows it there: either it could arrive with the
input (only possible at `k₀`), or some label's program has a push whose function takes that value at
some internal state.

Again an over-approximation, and now for a second reason as well: a label may be unreachable. A
supported symbol need not occur in any run. -/

/-- Symbols that can occur on stack `k` of `tm`. -/
inductive Supported (tm : FinTM2) : (k : tm.K) → tm.Γ k → Prop
  | input (c : tm.Γ tm.k₀) : Supported tm tm.k₀ c
  | pushed {l : tm.Λ} {k : tm.K} {c : tm.Γ k} : Pushes (tm.m l) k c → Supported tm k c

/-- The support is finite for every stack, whatever the machine's auxiliary alphabets.

At the input stack this uses `Γk₀Fin`; elsewhere only the push sets contribute, and those are finite
by `pushSet_finite`. -/
theorem supported_finite (tm : FinTM2) (k : tm.K) : {c | Supported tm k c}.Finite := by
  classical
  by_cases h : k = tm.k₀
  · subst h
    exact Set.toFinite _
  · have hsub : {c | Supported tm k c} ⊆ ⋃ l : tm.Λ, pushSet (tm.m l) k := by
      rintro c hc
      cases hc with
      | input c => exact absurd rfl h
      | pushed hp => exact Set.mem_iUnion.mpr ⟨_, hp⟩
    exact Set.Finite.subset (Set.finite_iUnion fun l => pushSet_finite (tm.m l) k) hsub

/-- Away from the input stack, support can only come from a push.  Stated with `k` a *variable*:
inverting `Supported` at a concrete index makes the index unification fail. -/
theorem supported_iff_pushed {tm : FinTM2} {k : tm.K} (hk : k ≠ tm.k₀) (c : tm.Γ k) :
    Supported tm k c ↔ ∃ l, Pushes (tm.m l) k c := by
  constructor
  · intro h
    cases h with
    | input c => exact absurd rfl hk
    | pushed hp => exact ⟨_, hp⟩
  · rintro ⟨l, hp⟩
    exact Supported.pushed hp

/-! ## B: the invariant, and its preservation along executions -/

/-- Every symbol on every stack is supported. -/
def StackSupported (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) : Prop :=
  ∀ k, ∀ c ∈ S k, Supported tm k c

/-- Executing a statement preserves the invariant, provided the statement's own pushes are
supported.  A pop removes a symbol, a peek and a load leave the stacks alone, and a push contributes
exactly the symbol its membership hypothesis covers. -/
theorem stackSupported_stepAux (tm : FinTM2) :
    ∀ (q : Stmt tm.Γ tm.Λ tm.σ) (_hq : ∀ k c, Pushes q k c → Supported tm k c)
      (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (_hS : StackSupported tm S),
      StackSupported tm (stepAux q v S).stk
  | .push k f q, hq, v, S, hS => by
      refine stackSupported_stepAux tm q (fun j c hc => hq j c (Pushes.push f hc)) v _ ?_
      intro j c hc
      by_cases hj : j = k
      · subst hj
        rw [Function.update_self] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hq j (f v) (Pushes.here f q v)
        · exact hS j c hc
      · rw [Function.update_of_ne hj] at hc
        exact hS j c hc
  | .peek k f q, hq, v, S, hS =>
      stackSupported_stepAux tm q (fun j c hc => hq j c (Pushes.peek f hc)) _ S hS
  | .pop k f q, hq, v, S, hS => by
      refine stackSupported_stepAux tm q (fun j c hc => hq j c (Pushes.pop f hc)) _ _ ?_
      intro j c hc
      by_cases hj : j = k
      · subst hj
        rw [Function.update_self] at hc
        exact hS j c (List.mem_of_mem_tail hc)
      · rw [Function.update_of_ne hj] at hc
        exact hS j c hc
  | .load a q, hq, v, S, hS =>
      stackSupported_stepAux tm q (fun j c hc => hq j c (Pushes.load a hc)) _ S hS
  | .branch f q₁ q₂, hq, v, S, hS => by
      cases h : f v with
      | false =>
          simp only [stepAux, h, Bool.cond_false]
          exact stackSupported_stepAux tm q₂ (fun j c hc => hq j c (Pushes.branchR f hc)) v S hS
      | true =>
          simp only [stepAux, h, Bool.cond_true]
          exact stackSupported_stepAux tm q₁ (fun j c hc => hq j c (Pushes.branchL f hc)) v S hS
  | .goto f, _, v, S, hS => hS
  | .halt, _, v, S, hS => hS

/-- One machine step preserves the invariant.  The statement executed is `tm.m l` for some label,
whose pushes are supported by definition. -/
theorem stackSupported_step (tm : FinTM2) {c c' : tm.Cfg} (h : tm.step c = some c')
    (hc : StackSupported tm c.stk) : StackSupported tm c'.stk := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have h' : stepAux (tm.m l) v S = c' :=
        Option.some_inj.mp (show (some (stepAux (tm.m l) v S) : Option tm.Cfg) = some c' from h)
      subst h'
      exact stackSupported_stepAux tm (tm.m l) (fun _ _ hp => Supported.pushed hp) v S hc

/-- The initial configuration satisfies the invariant, for **every** raw input tape: input symbols
live on `k₀`, and every symbol of `Γ k₀` is supported there. -/
theorem stackSupported_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    StackSupported tm (initList tm s).stk := by
  intro k c hc
  by_cases h : k = tm.k₀
  · subst h; exact Supported.input c
  · simp only [initList, dite_eq_right h] at hc
    exact absurd hc (List.not_mem_nil)

/-- The invariant holds at every successful prefix of an execution. -/
theorem stackSupported_iterate (tm : FinTM2) : ∀ (n : ℕ) (c c' : tm.Cfg),
    (flip Bind.bind tm.step)^[n] (some c) = some c' → StackSupported tm c.stk →
    StackSupported tm c'.stk
  | 0, c, c', h, hc => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      exact h ▸ hc
  | n + 1, c, c', h, hc => by
      rw [Function.iterate_succ_apply] at h
      cases hstep : tm.step c with
      | none =>
          rw [show (flip Bind.bind tm.step) (some c) = none from hstep] at h
          have : ∀ m : ℕ, (flip Bind.bind tm.step)^[m] none = (none : Option tm.Cfg) := by
            intro m
            induction m with
            | zero => rfl
            | succ m ih => rw [Function.iterate_succ_apply]; exact ih
          rw [this] at h
          exact absurd h (by simp)
      | some c₁ =>
          rw [show (flip Bind.bind tm.step) (some c) = some c₁ from hstep] at h
          exact stackSupported_iterate tm n c₁ c' h (stackSupported_step tm hstep hc)

/-- **The support theorem.**  Every configuration reachable from any raw input uses only symbols
from a fixed finite set per stack, determined by the machine alone. -/
theorem reachable_stackSupported (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (n : ℕ) (c : tm.Cfg)
    (h : (flip Bind.bind tm.step)^[n] (some (initList tm s)) = some c) :
    StackSupported tm c.stk :=
  stackSupported_iterate tm n _ c h (stackSupported_initList tm s)

/-! ## A constraint to carry into the recoding step

Finite support does not *automatically* let a recoded machine be packaged as a
`TM2ComputableInPolyTime` witness. `TM2ComputableAux` requires equivalences

```text
inputAlphabet  : tm.Γ tm.k₀ ≃ Γ₀      outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁
```

for the **entire** alphabets. Restricting a stack to a subtype of its alphabet **may** lose such an
equivalence — but only when the chosen support actually omits symbols the external alphabet needs.
It is not an automatic obstruction:

* When the support at a stack is already everything, the restriction is an isomorphism and both
  equivalences transport through it.
* When the support omits a symbol of a finite external alphabet, no full-alphabet equivalence
  survives, and the support must be enlarged at that stack first. For the PCP predicates both
  external alphabets are the finite `Sym`, so the witness's own equivalences supply the finiteness
  needed to do so. This also covers `k₀ = k₁`.
* For a raw `FinTM2`, only the *input* alphabet is required finite. The output alphabet may be
  infinite while every supported output symbol lies in a fixed finite set. A generic wrapper
  preserving the same external alphabets must therefore assume output-alphabet finiteness, or offer
  a weaker output-decoding contract. It must not promise a finite alphabet equivalent to an infinite
  one.

This is why the recoding step is parameterised by *any* finite enlargement of `Supported`
(`SupportData`), rather than by `Supported` itself: the enlargement needed at an output stack is
then a different instance, not a second translator.

## Acceptance examples -/

section Examples

/-- A stack that is neither the input stack nor ever pushed to has empty support. -/
theorem supported_eq_empty_of_unused (tm : FinTM2) (k : tm.K) (hk : k ≠ tm.k₀)
    (hpush : ∀ (l : tm.Λ) (c : tm.Γ k), ¬ Pushes (tm.m l) k c) :
    {c | Supported tm k c} = ∅ := by
  ext c
  constructor
  · intro hc
    cases hc with
    | input c => exact absurd rfl hk
    | pushed hp => exact absurd hp (hpush _ _)
  · exact fun h => h.elim

/-- Stack `false` carries `Bool`; stack `true` carries `ℕ`, which is infinite.

Written by pattern match rather than `bif` so that `auxAlphabet true` reduces to `ℕ` and numerals
elaborate there. -/
def auxAlphabet : Bool → Type
  | false => Bool
  | true => ℕ

instance : Fintype (auxAlphabet false) := inferInstanceAs (Fintype Bool)

/-- A machine whose auxiliary alphabet is infinite, but which pushes only two values onto it. -/
def infiniteAuxTM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ := auxAlphabet
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := fun _ => Stmt.push true (fun v => (bif v then 7 else 3 : ℕ)) Stmt.halt

/-- Its auxiliary support is finite even though `ℕ` is not — which is the whole point of this
module. -/
example : {c | Supported infiniteAuxTM true c}.Finite := supported_finite infiniteAuxTM true

/-- Both values the push function can take are supported.

Note what this does **not** say. The machine starts in state `false` and halts after one push, so a
run from the initial configuration pushes `3` and never `7`; `7` is supported because the collector
looks at the push function at every internal state, reachable or not. That over-approximation is
deliberate — it is what makes the support depend on the syntax alone.

This example is about raw transitions. Its halt leaves the auxiliary stack nonempty, so it is not a
certificate for the cleanup contract of `TM2OutputsInTime`, and nothing here needs it to be. -/
example : Supported infiniteAuxTM true (3 : ℕ) :=
  Supported.pushed (l := ()) (Pushes.here (k := true) _ _ false)

example : Supported infiniteAuxTM true (7 : ℕ) :=
  Supported.pushed (l := ()) (Pushes.here (k := true) _ _ true)

end Examples

end PCP.Machine
