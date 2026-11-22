import PCP.Complexity.SeedConstruct

/-!
# Building the canonical-width seed: the loop, the endpoint, the certificate

## The loop's exact cost

```text
T(0)     = 1                                       the final, empty test (and its b cells)
T(m + 1) = (m + 1) + (m + 1) / 2 + 3 + T((m + 1) / 2)    exactly one `cw_pass`, then the rest
```

There is no connecting jump to add: a pass already returns at `cwTest`.

## The helper flag at the end

Only a nonempty test clears the parity; the final, empty test preserves it.  From zero markers the
incoming flag is therefore retained.  From any positive count the last pass starts from a single
marker, which leaves the parity **set**, and the final test keeps it — so a construction from an
input, which always starts at `n + 1` markers, finishes with the flag `true`, even when
`a = b = 0`.  No uncharged reset is inserted to hide this.

## The endpoint

From `cwCopy` with the source input `ofBits x` and an empty seed tape, the construction reaches an
active `cwDone` with the seed tape holding **exactly the first seed of canonical width**,
`ofBits (bitsOfFin (canonicalWidth a b x.length) 0)`, the source input restored in order, and both
work stacks empty.  Its recorded count is `2 · x.length + 2 + T(x.length + 1)`, and `T(m) ≤ 6m + 1`
bounds it by `8 · x.length + 9` — before any dispatch from `cwDone`.

What the construction does **not** do: it preserves the callee storage, history, prefix, call input,
depth and aggregate rather than establishing them.  Those belong to the wrapper's initialisation.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ### The loop's cost -/

/-- The exact number of steps from `cwTest` with `m` unary markers to `cwDone`. -/
def cwLoopSteps : ℕ → ℕ
  | 0 => 1
  | m + 1 => (m + 1) + (m + 1) / 2 + 3 + cwLoopSteps ((m + 1) / 2)
decreasing_by omega

theorem cwLoopSteps_zero : cwLoopSteps 0 = 1 := by rw [cwLoopSteps]

theorem cwLoopSteps_succ (m : ℕ) :
    cwLoopSteps (m + 1) = (m + 1) + (m + 1) / 2 + 3 + cwLoopSteps ((m + 1) / 2) := by
  rw [cwLoopSteps]

/-- **The loop is linear**: `T(m) ≤ 6m + 1`. -/
theorem cwLoopSteps_le : ∀ m : ℕ, cwLoopSteps m ≤ 6 * m + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · rw [cwLoopSteps_zero]
    · rw [cwLoopSteps_succ]
      have := ih ((m + 1) / 2) (by omega)
      omega

/-- The helper flag the loop leaves: the incoming one from zero markers, `true` otherwise. -/
def cwFlagOut (m : ℕ) (flag : Bool) : Bool := if m = 0 then flag else true

/-! ### The loop -/

section Loop

variable {tm : FinTM2} {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {q : ℕ} {U₀ : Type} [Fintype U₀] (a b : ℕ)
  (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
    (Bool × (Bool × DepthPay q (Bool × U₀))))

/-- **The halving loop**, by strong induction on the unary length, generalised over the seed
accumulator, the helper flag, the temporary and all preserved storage.

From `cwTest` with `m` markers and empty scratch, `T(m)` steps reach `cwDone` with both work stacks
empty, the temporary cleared, and `a · halvings m + b` seed cells prepended to whatever the seed
tape held — the accumulator need not consist of zero bits. -/
theorem cw_loop (m : ℕ) :
    ∀ (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : DepthPay q (Bool × U₀))
      (S : ∀ k, List (tm.Γ k)) (inp xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[cwLoopSteps m]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp (flag, (res, r)) S
          inp (List.replicate m Sym.sep) [] xt rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwDone)) v none
          (cwFlagOut m flag, (res, r)) S inp [] [] xt
          (List.replicate (a * halvings m + b) (Sym.bit false) ++ rt) at' wit pre g) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v temp flag res r S inp xt rt at' wit pre g
    rcases m with _ | m
    · rw [cwLoopSteps_zero, List.replicate_zero, halvings_zero, Nat.mul_zero, Nat.zero_add]
      exact cw_final a b eIn eOut p₀ rest v temp (flag, (res, r)) S inp xt rt at' wit pre g
    · have hlt : (m + 1) / 2 < m + 1 := by omega
      have hsplit : cwLoopSteps (m + 1)
          = cwLoopSteps ((m + 1) / 2) + ((m + 1) + (m + 1) / 2 + 3) := by
        rw [cwLoopSteps_succ]; omega
      have hflag : cwFlagOut ((m + 1) / 2) (decide ((m + 1) % 2 = 1)) = cwFlagOut (m + 1) flag := by
        simp only [cwFlagOut]
        split
        · simp; omega
        · simp
      have hseed : List.replicate (a * halvings ((m + 1) / 2) + b) (Sym.bit false)
            ++ (List.replicate a (Sym.bit false) ++ rt)
          = List.replicate (a * halvings (m + 1) + b) (Sym.bit false) ++ rt := by
        rw [halvings_succ, ← List.append_assoc, ← List.replicate_add]
        congr 2
        ring
      rw [hsplit, Function.iterate_add_apply,
        cw_pass a b eIn eOut p₀ rest m v temp flag res r S inp xt rt at' wit pre g,
        ih ((m + 1) / 2) hlt v none (decide ((m + 1) % 2 = 1)) res r S inp xt
          (List.replicate a (Sym.bit false) ++ rt) at' wit pre g,
        hflag, hseed]

/-! ### The whole construction -/

/-- The exact recorded count of the whole construction. -/
def cwSteps (n : ℕ) : ℕ := 2 * n + 2 + cwLoopSteps (n + 1)

/-- **Linear**: `8n + 9`, before any dispatch from `cwDone`. -/
theorem cwSteps_le (n : ℕ) : cwSteps n ≤ 8 * n + 9 := by
  have := cwLoopSteps_le (n + 1)
  simp only [cwSteps]; omega

/-- The all-false tape of canonical width is exactly the first seed of that width. -/
theorem replicate_canonicalWidth (a b n : ℕ) :
    List.replicate (a * halvings (n + 1) + b) (Sym.bit false)
      = ofBits (bitsOfFin (canonicalWidth a b n) ⟨0, Nat.two_pow_pos _⟩) := by
  rw [bitsOfFin_zero, ← canonicalWidth_eq_halvings]
  simp [ofBits, List.map_replicate]

/-- **The construction**, as a certificate on the whole loop machine.

From `cwCopy` with the source input `ofBits x`, empty work stacks and an empty seed tape, to an
active `cwDone`: the seed tape holds **exactly**
`ofBits (bitsOfFin (canonicalWidth a b x.length) 0)`, the source input is back in order, both work
stacks are empty, the temporary is cleared, and the helper flag is `true` — `x.length + 1` is
positive.  Everything else is preserved as it came, not established.  Built field by field, so its
count is `cwSteps x.length` definitionally. -/
def cwEvals (x : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (inp at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (wTM a b eIn eOut p₀ rest).step
      (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v temp (flag, (res, r)) S inp [] []
        (ofBits x) [] at' wit pre g)
      (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwDone)) v none (true, (res, r)) S inp
        [] [] (ofBits x) (ofBits (bitsOfFin (canonicalWidth a b x.length) ⟨0, Nat.two_pow_pos _⟩))
        at' wit pre g))
      (8 * x.length + 9) where
  steps := cwSteps x.length
  evals_in_steps := by
    have hloop := cw_loop a b eIn eOut p₀ rest (x.length + 1) v none flag res r S inp (ofBits x) []
      at' wit pre g
    rw [List.append_nil, replicate_canonicalWidth] at hloop
    have hunary := cw_unary a b eIn eOut p₀ rest (ofBits x) v temp (flag, (res, r)) S inp []
      at' wit pre g
    rw [length_ofBits] at hunary
    have hc : cwSteps x.length = cwLoopSteps (x.length + 1) + (2 * x.length + 2) := by
      simp only [cwSteps]; omega
    rw [hc, Function.iterate_add_apply, hunary, hloop]
    rfl
  steps_le_m := cwSteps_le x.length

@[simp] theorem cwEvals_steps (x : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (inp at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cwEvals a b eIn eOut p₀ rest x v temp flag res r S inp at' wit pre g).steps
      = cwSteps x.length := rfl

end Loop

end PCP.Machine
