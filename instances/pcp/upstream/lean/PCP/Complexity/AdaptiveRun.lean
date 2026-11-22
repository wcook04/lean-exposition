import PCP.Complexity.AdaptivePath

/-!
# The adaptive path: induction on remaining depth

`AdaptiveTurn.lean` runs one positive round; `AdaptivePath.lean` runs each terminal round and gives
the depth laws.  This module puts them together: from `prepA1` at any remaining depth, the machine
reaches an **active terminal boundary** — `decided` or `rejected` — carrying exactly

```text
runAdaptive (fun a => f (x, rs, a)) (oracleOfWitness w) i.val a.
```

## One machine throughout

`q`, `U`, the certified witness `hw`, the alphabet maps, the continuation and the initial payload
are fixed before the induction starts.  The induction is on the depth **value**; the finite control
type `Fin (q + 1)` never changes, so every round composes on the same machine.

## The two terminal storages stay distinct

A decision leaves the destination empty; a rejected query leaves `ofBits (Nat.bits addr)` on it.
`terminalLabel`, `terminalBit` and `terminalResid` read all three off the answer, so one endpoint
expression covers both without pretending their residual tapes agree.

## The helper flag is carried, not asserted

A terminal round reached with no preceding positive query leaves the incoming flag alone; a positive
iteration clears it.  `PathCert.flagOut` records which happened rather than claiming `false`.
Likewise an early decision keeps whatever depth was left: only `PathCert.budget` is promised.

## Saturation is not what stops the loop

`depthPred_zero` says the counter cannot go below zero; it does not by itself stop turnaround steps.
What stops them is the **branch**: at zero depth the dispatch statement sends a query to `rejected`,
so `lookup`, the search and the turnaround are never entered.  That is `aRejectEvals`, used in the
base case below.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ### Reading a terminal round off its answer -/

/-- The bit a terminal round selects. -/
def terminalBit : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr _ => false

/-- The active boundary it stops at. -/
def terminalLabel : Bool ⊕ ℕ → CallLabel
  | .inl _ => .decided
  | .inr _ => .rejected

/-- What it leaves on the destination: nothing after a decision, the untouched query numeral after
a rejection. -/
def terminalResid : Bool ⊕ ℕ → List Sym
  | .inl _ => []
  | .inr addr => ofBits (Nat.bits addr)

section Path

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The machine the whole path runs on: fixed before the induction and unchanged by it. -/
noncomputable abbrev pathTM (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U))) : FinTM2 :=
  aTM hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U) rest

/-- A round's starting configuration: the storage shape `aIterEvals` both needs and restores. -/
noncomputable def pathStart (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (i : Fin (q + 1)) (a : List Bool) (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) :
    (pathTM q U hw p₀ rest).Cfg :=
  tuCfg hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U) rest
    (some (.inr CallLabel.prepA1)) v temp (flag, (res, (i, u))) (fun _ => []) [] [] []
    (ofBits x) (ofBits rs) (ofBits a) (ofBits w) [] g

/-- A terminal configuration, read off the answer. -/
noncomputable def pathStop (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (ans : Bool ⊕ ℕ) (hist : List Bool) (dep : Fin (q + 1)) (fo : Bool) :
    (pathTM q U hw p₀ rest).Cfg :=
  tuCfg hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U) rest
    (some (.inr (terminalLabel ans))) hw.tm.initialState none (fo, (terminalBit ans, (dep, u)))
    (fun _ => []) (encodeTriple (x, rs, hist)) (terminalResid ans) []
    (ofBits x) (ofBits rs) (ofBits hist) (ofBits w) [] g

/-- **What a complete adaptive path delivers.**

Data — final history, remaining depth, the terminal answer, the helper flag actually left, and the
exact recorded step count — together with the facts a caller needs: the answer is the one the
algorithm gives on the final history, a rejection happened at exhausted depth, history and depth
still add up, the history only grew, the selected bit is the semantics, and the execution itself. -/
structure PathCert (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (i : Fin (q + 1)) (a : List Bool) (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) where
  /-- The history the terminal round ran on. -/
  hist : List Bool
  /-- The depth still unspent when it stopped. -/
  depth : Fin (q + 1)
  /-- The answer that stopped it. -/
  answer : Bool ⊕ ℕ
  /-- The helper flag actually left behind — *not* asserted to be `false`. -/
  flagOut : Bool
  /-- The exact recorded count: the sum of the constituent certificates' counts. -/
  steps : ℕ
  /-- The terminal answer is the one the algorithm gives on the final history. -/
  answer_eq : f (x, rs, hist) = answer
  /-- A query is only rejected when the budget is gone. -/
  reject_at_zero : ∀ addr, answer = Sum.inr addr → (depth : ℕ) = 0
  /-- Every answer recorded cost one unit of depth. -/
  budget : hist.length + (depth : ℕ) = a.length + (i : ℕ)
  /-- The history only ever grew, and at its far end. -/
  extends_hist : ∃ extra, hist = a ++ extra
  /-- The selected bit **is** the adaptive semantics at this depth and history. -/
  semantics : terminalBit answer
    = runAdaptive (fun c => f (x, rs, c)) (oracleOfWitness w) (i : ℕ) a
  /-- …and the machine actually runs there. -/
  run : (flip Bind.bind (pathTM q U hw p₀ rest).step)^[steps]
        (some (pathStart q U hw p₀ rest x rs w u g i a v temp flag res))
      = some (pathStop q U hw p₀ rest x rs w u g answer hist depth flagOut)

/-- **The adaptive path.**

Induction on the remaining depth's *value*; the machine, its control type and the continuation are
all fixed outside.  Three cases, split on the answer the algorithm actually gives:

* a decision ends the path at once, at whatever depth is left;
* a query at exhausted depth is rejected — `lookup` is never entered, so no search and no
  turnaround run, and the numeral is left untouched;
* a query with budget left runs a full positive iteration and recurses on the appended history and
  the decremented depth.

The recorded count is the exact sum of the constituent certificates' counts. -/
noncomputable def pathCert (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j)) :
    ∀ (d : ℕ) (i : Fin (q + 1)), (i : ℕ) = d → ∀ (a : List Bool) (v : hw.tm.σ)
      (temp : Option Sym) (flag res : Bool),
      PathCert q U hw p₀ rest x rs w u g i a v temp flag res
  | 0, i, hi, a, v, temp, flag, res =>
      match hans : f (x, rs, a) with
      | .inl b =>
          { hist := a, depth := i, answer := .inl b, flagOut := flag
            steps := (aDecideEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v
              temp flag res (i, u) (ofBits w) [] g).steps
            answer_eq := hans
            reject_at_zero := by intro addr h; exact absurd h (by simp)
            budget := rfl
            extends_hist := ⟨[], by simp⟩
            semantics :=
              (runAdaptive_decide (fun c => f (x, rs, c)) (oracleOfWitness w) (i : ℕ) a b hans).symm
            run := (aDecideEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v temp
              flag res (i, u) (ofBits w) [] g).evals_in_steps }
      | .inr addr =>
          { hist := a, depth := i, answer := .inr addr, flagOut := flag
            steps := (aRejectEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans v
              temp flag res (i, u) (by simp [depthZero, hi]) (ofBits w) [] g).steps
            answer_eq := hans
            reject_at_zero := fun _ _ => hi
            budget := rfl
            extends_hist := ⟨[], by simp⟩
            semantics := by
              rw [hi]
              exact (runAdaptive_reject (fun c => f (x, rs, c)) (oracleOfWitness w) a addr
                hans).symm
            run := (aRejectEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans v
              temp flag res (i, u) (by simp [depthZero, hi]) (ofBits w) [] g).evals_in_steps }
  | d + 1, i, hi, a, v, temp, flag, res =>
      match hans : f (x, rs, a) with
      | .inl b =>
          { hist := a, depth := i, answer := .inl b, flagOut := flag
            steps := (aDecideEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v
              temp flag res (i, u) (ofBits w) [] g).steps
            answer_eq := hans
            reject_at_zero := by intro addr h; exact absurd h (by simp)
            budget := rfl
            extends_hist := ⟨[], by simp⟩
            semantics :=
              (runAdaptive_decide (fun c => f (x, rs, c)) (oracleOfWitness w) (i : ℕ) a b hans).symm
            run := (aDecideEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a b hans v temp
              flag res (i, u) (ofBits w) [] g).evals_in_steps }
      | .inr addr =>
          let hpos : 0 < (i : ℕ) := by omega
          let bit := oracleOfWitness w addr
          let ih := pathCert q U hw p₀ rest x rs w u g d (depthPred q U (i, u)).1
            (by simp only [depthPred_fst]; omega) (a ++ [bit]) hw.tm.initialState none false bit
          { hist := ih.hist, depth := ih.depth, answer := ih.answer, flagOut := ih.flagOut
            steps := (aIterEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans w v
                temp flag res (i, u) g (depthZero_of_pos hpos u)).steps
              + ih.steps
            answer_eq := ih.answer_eq
            reject_at_zero := ih.reject_at_zero
            budget := by
              have hb := ih.budget
              have := depth_budget (q := q) (U := U) hpos u a bit (N := a.length + (i : ℕ)) rfl
              omega
            extends_hist := by
              obtain ⟨extra, hx⟩ := ih.extends_hist
              exact ⟨bit :: extra, by rw [hx]; simp⟩
            semantics := by
              have hstep := aIter_history (fun c => f (x, rs, c)) w
                ((depthPred q U (i, u)).1 : ℕ) a addr hans
              have hsucc : ((depthPred q U (i, u)).1 : ℕ) + 1 = (i : ℕ) := depthPred_succ hpos u
              rw [ih.semantics, ← hstep, hsucc]
            run := by
              have hc : (aIterEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans w
                    v temp flag res (i, u) g (depthZero_of_pos hpos u)).steps + ih.steps
                  = ih.steps + (aIterEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr
                      hans w v temp flag res (i, u) g (depthZero_of_pos hpos u)).steps :=
                Nat.add_comm _ _
              rw [hc, Function.iterate_add_apply]
              rw [show (pathStart q U hw p₀ rest x rs w u g i a v temp flag res)
                  = tuCfg hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U)
                      rest (some (.inr CallLabel.prepA1)) v temp (flag, (res, (i, u)))
                      (fun _ => []) [] [] [] (ofBits x) (ofBits rs) (ofBits a) (ofBits w) [] g
                from rfl,
                (aIterEvals hw p₀ (depthZero q U) (depthPred q U) rest x rs a addr hans w v temp
                  flag res (i, u) g (depthZero_of_pos hpos u)).evals_in_steps]
              exact ih.run }

end Path

end PCP.Machine
