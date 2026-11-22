import PCP.Complexity.CounterZero

/-!
# The counter's decrement, as a machine

Same layout as the zero test: the counter is on the call's destination stack, the scan uses call
scratch, and the payload is `Bool × Q`.  The flag's first component means "seen a set bit" during
the zero test and "borrow pending" during decrement; the two meanings stay local to their own
labels and invariants.

## One machine for both helpers

`counterRoute` is `ztRoute` over `dcRoute`, so **both** helpers run under a single program.  The
accepted `zt_trace` applies to it unchanged, at `rest := dcRoute …`; it is not re-proved for a
different program that merely agrees on labels.  A connecting jump between the two is the caller's
and must be charged where it occurs — nothing here folds one into the other.

## Ordering inside the scan step

The output bit and the outgoing borrow are both computed from the **old** borrow and the bit just
read: the push happens before the load that updates the borrow.  Resetting the temporary early, or
reading the updated borrow for the output, would corrupt the first set bit of a borrow chain.

## Counting

One initialisation step, a full-width scan of `bs.length + 1`, and a restoring scan of the same
length: `2 * bs.length + 3`, with both empty exits inside that count.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (Q : Type) [Fintype Q]

/-- One counted step: set the borrow pending, whatever the flag was. -/
def dcInitStmt : PrepStmt tm G Γg (Bool × Q) :=
  load (fun p => (p.1, (none, (true, p.2.2.2)))) (goto (fun _ => .inr .dcScan))

/-- The borrow scan.  The pushed bit and the new borrow both read the *old* borrow. -/
def dcScanStmt : PrepStmt tm G Γg (Bool × Q) :=
  pop (.inr (.inl .dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl .scratch))
        (fun p => Sym.bit (outBit p.2.2.1 (symIsTrue p.2.1)))
        (load (fun p => (p.1, (none, (nextBorrow p.2.2.1 (symIsTrue p.2.1), p.2.2.2))))
          (goto (fun _ => .inr .dcScan))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .dcRestore)))

/-- The restoring scan: order restored, borrow and `q` carried through to the done boundary. -/
def dcRestoreStmt : PrepStmt tm G Γg (Bool × Q) :=
  pop (.inr (.inl .scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl .dst)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .dcRestore))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .dcDone)))

/-- The decrement labels; everything else goes on. -/
def dcRoute (rest : CallLabel → PrepStmt tm G Γg (Bool × Q)) :
    CallLabel → PrepStmt tm G Γg (Bool × Q)
  | .dcInit => dcInitStmt tm G Γg Q
  | .dcScan => dcScanStmt tm G Γg Q
  | .dcRestore => dcRestoreStmt tm G Γg Q
  | l => rest l

/-- **One program for both helpers.** -/
def counterRoute (rest : CallLabel → PrepStmt tm G Γg (Bool × Q)) :
    CallLabel → PrepStmt tm G Γg (Bool × Q) :=
  ztRoute tm G Γg Q (dcRoute tm G Γg Q rest)

variable {tm G Γg Q}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × Q)
  (rest : CallLabel → PrepStmt tm G Γg (Bool × Q))

/-- **Initialisation**: the borrow is set pending whatever the flag was, and `q` survives. -/
theorem dc_step_init (v : tm.σ) (temp : Option Sym) (q : Q) (borrow : Bool) (dst scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcInit)) v temp
            (borrow, q) S inp (dst) (scr) t g)
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcScan)) v
          none (true, q) S inp (dst) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).m (Sum.inr
            CallLabel.dcInit)) (v, (temp, (borrow, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (dst) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, counterRoute, ztRoute, dcRoute, dcInitStmt,
    dcScanStmt, dcRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame,
    prepFrame]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.dcScan), (v, (none, (true, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- One scanned bit: the transformed bit is pushed using the **old** borrow, and only then does
the borrow update. -/
theorem dc_step_scan_cons (v : tm.σ) (temp : Option Sym) (q : Q) (borrow c : Bool) (dst
    scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcScan)) v temp
            (borrow, q) S inp (Sym.bit c :: dst) (scr) t g)
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcScan)) v
          none (nextBorrow borrow c, q) S inp (dst) (Sym.bit (outBit borrow c) :: scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).m (Sum.inr
            CallLabel.dcScan)) (v, (temp, (borrow, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (Sym.bit c :: dst) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, counterRoute, ztRoute, dcRoute, dcInitStmt,
    dcScanStmt, dcRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame,
    prepFrame,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.dcScan), (v, (none, (nextBorrow borrow c, q))), T⟩ : (callTM tm
        (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- Its empty exit hands the final borrow to the restoring scan. -/
theorem dc_step_scan_nil (v : tm.σ) (temp : Option Sym) (q : Q) (borrow : Bool) (scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcScan)) v temp
            (borrow, q) S inp ([]) (scr) t g)
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr
          CallLabel.dcRestore)) v none (borrow, q) S inp ([]) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).m (Sum.inr
            CallLabel.dcScan)) (v, (temp, (borrow, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp ([]) (scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, counterRoute, ztRoute, dcRoute, dcInitStmt,
    dcScanStmt, dcRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame,
    prepFrame,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.dcRestore), (v, (none, (borrow, q))), T⟩ : (callTM tm
        (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- The restoring scan moves one bit back, preserving the borrow. -/
theorem dc_step_restore_cons (v : tm.σ) (temp : Option Sym) (q : Q) (borrow : Bool) (c : Sym)
    (dst scr : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcRestore)) v
            temp (borrow, q) S inp (dst) (c :: scr) t g)
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr
          CallLabel.dcRestore)) v none (borrow, q) S inp (c :: dst) (scr)
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).m (Sum.inr
            CallLabel.dcRestore)) (v, (temp, (borrow, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (dst) (c :: scr)
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, counterRoute, ztRoute, dcRoute, dcInitStmt,
    dcScanStmt, dcRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame,
    prepFrame,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.dcRestore), (v, (none, (borrow, q))), T⟩ : (callTM tm
        (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- …and its empty exit reaches the decrement's own boundary. -/
theorem dc_step_restore_nil (v : tm.σ) (temp : Option Sym) (q : Q) (borrow : Bool) (dst : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcRestore)) v
            temp (borrow, q) S inp (dst) ([]) t g)
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr CallLabel.dcDone)) v
          none (borrow, q) S inp (dst) ([])
          t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).m (Sum.inr
            CallLabel.dcRestore)) (v, (temp, (borrow, q)))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp (dst) ([])
          (prepFrame G Γg t g)))) = _
  simp only [callTM, parentTM, callProgram, prepCont, counterRoute, ztRoute, dcRoute, dcInitStmt,
    dcScanStmt, dcRestoreStmt, symIsTrue, Turing.TM2.stepAux, embedStacks_inr, callFrame,
    prepFrame,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.dcDone), (v, (none, (borrow, q))), T⟩ : (callTM tm (TripleSlot ⊕ G)
        (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-! ### The two scans -/

theorem dc_scan : ∀ (bs : List Bool) (v : tm.σ) (temp : Option Sym) (borrow : Bool) (q : Q)
    (scr : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[bs.length + 1]
        (some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcScan)) v temp
            (borrow, q) S inp (ofBits bs) scr t g))
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcRestore)) v none
          (finalBorrow borrow bs, q) S inp []
          ((ofBits (transform borrow bs)).reverse ++ scr) t g)
  | [], v, temp, borrow, q, scr, S, t, inp, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcScan)) v temp
            (borrow, q) S inp [] scr t g) = _
      rw [dc_step_scan_nil eIn eOut p₀ rest v temp q borrow scr S t inp g]
      simp [ofBits]
  | c :: bs, v, temp, borrow, q, scr, S, t, inp, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[bs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
          (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcScan)) v temp
              (borrow, q) S inp (Sym.bit c :: ofBits bs) scr
            t g)) = _
      rw [dc_step_scan_cons eIn eOut p₀ rest v temp q borrow c (ofBits bs) scr S t inp g,
        dc_scan bs v none (nextBorrow borrow c) q (Sym.bit (outBit borrow c) :: scr) S t inp g]
      simp [transform_cons, finalBorrow_cons, ofBits]

theorem dc_restore : ∀ (rs : List Sym) (v : tm.σ) (temp : Option Sym) (borrow : Bool) (q : Q)
    (dst : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[rs.length + 1]
        (some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcRestore)) v temp
            (borrow, q) S inp dst rs t g))
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcDone)) v none
          (borrow, q) S inp (rs.reverse ++ dst) [] t g)
  | [], v, temp, borrow, q, dst, S, t, inp, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcRestore)) v temp
            (borrow, q) S inp dst [] t g) = _
      rw [dc_step_restore_nil eIn eOut p₀ rest v temp q borrow dst S t inp g]
      simp
  | c :: rs, v, temp, borrow, q, dst, S, t, inp, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[rs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
          (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcRestore)) v temp
              (borrow, q) S inp dst (c :: rs) t g)) = _
      rw [dc_step_restore_cons eIn eOut p₀ rest v temp q borrow c dst rs S t inp g,
        dc_restore rs v none borrow q (c :: dst) S t inp g]
      simp

/-! ### The complete decrement -/

/-- **The decrement.**  From `dcInit` with the counter holding `ofBits bs` and scratch empty:
`2 * bs.length + 3` steps leave the counter holding `ofBits (decrBits bs)` in bit order, scratch
empty, the temporary normalised and the **final borrow specified** — with every callee stack,
source tape, input, unrelated frame and the payload component `q` untouched.

This is total: it holds for every `bs`, including the underflow cases. -/
theorem dc_trace (bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[2 * bs.length + 3]
        (some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcInit)) v temp
            (flag, q) S inp (ofBits bs) [] t g))
      = some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcDone)) v none
          (finalBorrow true bs, q) S inp
          (ofBits (decrBits bs)) [] t g) := by
  have hsplit : 2 * bs.length + 3
      = ((ofBits (transform true bs)).reverse.length + 1) + ((bs.length + 1) + 1) := by
    simp only [List.length_reverse, length_ofBits, length_transform]; omega
  rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
  change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[(ofBits (transform
            true bs)).reverse.length + 1]
    ((flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step)^[bs.length + 1]
      ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
        (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
        (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcInit)) v temp
            (flag, q) S inp (ofBits bs) [] t g))) = _
  rw [dc_step_init eIn eOut p₀ rest v temp q flag (ofBits bs) [] S t inp g,
    dc_scan eIn eOut p₀ rest bs v none true q [] S t inp g, List.append_nil,
    dc_restore eIn eOut p₀ rest (ofBits (transform true bs)).reverse v none
      (finalBorrow true bs) q [] S t inp g]
  simp

/-- The certificate, with its count written out. -/
def dcEvals (bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) (Bool × Q) eIn eOut p₀
      (prepCont tm G Γg (Bool × Q) (counterRoute tm G Γg Q rest))).step
      (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcInit)) v temp (flag, q)
          S inp (ofBits bs) [] t g)
      (some (prepCfg eIn eOut p₀ (counterRoute tm G Γg Q rest) (some (.inr .dcDone)) v none
          (finalBorrow true bs, q) S inp
        (ofBits (decrBits bs)) [] t g))
      (2 * bs.length + 3) where
  steps := 2 * bs.length + 3
  evals_in_steps := dc_trace eIn eOut p₀ rest bs v temp flag q S t inp g
  steps_le_m := le_refl _

@[simp] theorem dcEvals_steps (bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag : Bool) (q : Q)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (dcEvals eIn eOut p₀ rest bs v temp flag q S t inp g).steps = 2 * bs.length + 3 := rfl

/-! ### Arithmetic corollaries

The execution above is total.  **Only** under positivity does it mean subtraction by one. -/

/-- On a positive counter the value drops by exactly one and the width is unchanged. -/
theorem dc_value_of_pos {bs : List Bool} (h : 0 < bitsValue bs) :
    bitsValue (decrBits bs) = bitsValue bs - 1 ∧ (decrBits bs).length = bs.length :=
  ⟨bitsValue_decrBits bs h, length_decrBits bs⟩

/-- **Underflow, stated rather than hidden.**  On a zero counter the result is all set bits of the
same width — an empty tape staying empty — and the final borrow is still pending in both cases. -/
theorem dc_underflow {bs : List Bool} (h : bitsValue bs = 0) :
    decrBits bs = bs.map (fun _ => true) ∧ finalBorrow true bs = true :=
  ⟨decrBits_of_value_zero h, by
    simp only [finalBorrow, List.all_eq_true]
    intro b hb
    simp [(bitsValue_eq_zero_iff bs).1 h b hb]⟩

/-- A cleared borrow does **not** mean the result is nonzero: decrementing one gives zero.  The
search loop must run the zero test again rather than reuse this Boolean. -/
example : finalBorrow true [true] = false ∧ bitsValue (decrBits [true]) = 0 := ⟨rfl, rfl⟩

end Steps

end

end PCP.Machine
