import PCP.Complexity.SeedRound
import PCP.Complexity.SeedBits

/-!
# Fixed-width seed increment, as a machine

`SeedBits.lean` says what incrementing a fixed-width seed *is*; this module proves a machine does
it.  The seed lives on the source seed tape, which `seedRoundEvals` preserves, so it is updated in
place on the same machine that runs the seed round — the increment's labels go into the cleanup
machine's continuation.

## One machine for every width

The width `k` is a tape length, never a control field: the program is the same fixed program for
every `k` — `incRoute` supplies three statements, `inInit`, `inScan` and `inBack`, and `inTest`
is its continuation boundary — and it finds the end of the seed by the empty exit of a pop.  The
carry is the one bit of finite control the scan needs, kept in the helper-flag slot — which
`inInit` **sets explicitly**, so whatever flag the seed round left behind cannot influence the
increment.  It is kept apart from the popped-symbol temporary throughout.

## The scan

`inScan` pops a cell off the seed tape and pushes `outBit carry c` — computed from the **old**
carry and the cell just read — onto scratch, then updates the carry to `nextCarry carry c`.
`inBack` moves scratch back, restoring the order.  The endpoint `inTest` is an active boundary with
the overflow in the helper flag; what to do with it is the enumerator's business.

## Counting

`1 + (k + 1) + (k + 1) = 2 * k + 3`: the initialisation, both passes and both empty exits.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- Set the carry — explicitly, whatever the helper flag held. -/
def inInitStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  load (fun p => (p.1, (none, (true, p.2.2.2)))) (goto (fun _ => .inr .inScan))

/-- Pass one: each seed cell onto scratch, transformed by the old carry; then the carry moves on. -/
def inScanStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inl TripleSlot.rs))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl CallSlot.scratch)) (fun p => Sym.bit (outBit p.2.2.1 (symIsTrue p.2.1)))
        (load (fun p => (p.1, (none, (nextCarry p.2.2.1 (symIsTrue p.2.1), p.2.2.2))))
          (goto (fun _ => .inr .inScan))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .inBack)))

/-- Pass two: scratch back onto the seed tape, restoring its order. -/
def inBackStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inl TripleSlot.rs))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .inBack))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .inTest)))

/-- The increment's labels.  `inTest` is its active boundary and dispatches through `rest`. -/
def incRoute (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .inInit => inInitStmt tm G Γg R
  | .inScan => inScanStmt tm G Γg R
  | .inBack => inBackStmt tm G Γg R
  | l => rest l

variable {tm G Γg R}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (dzero : R → Bool) (ddec : R → R) (dreset : R → R)
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-- The seed-round machine with the increment in its continuation. -/
abbrev iTM : FinTM2 := cTM eIn eOut p₀ dzero ddec dreset (incRoute tm G Γg R rest)

/-- A configuration of it. -/
def inCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k)) (inp dst scr : List Sym)
    (xt rt at' : List Sym) (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg :=
  clCfg eIn eOut p₀ dzero ddec dreset (incRoute tm G Γg R rest) l v temp pay S inp dst scr xt rt
    at' wit pre g

theorem in_bind_of_step {c c' : (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg}
    (h : (iTM eIn eOut p₀ dzero ddec dreset rest).step c = some c') :
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step) (some c) = some c' := h

/-! ### The one-step equations -/

/-- The carry is set, whatever the flag was. -/
theorem in_step_init (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).step
        (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inInit)) v temp
          (flag, (res, r)) S inp dst scr xt rt at' wit pre g)
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inScan)) v none
          (true, (res, r)) S inp dst scr xt rt at' wit pre g) :=
  rfl

/-- Pass one, one cell: the output uses the **old** carry. -/
theorem in_step_scan_cons (v : tm.σ) (temp : Option Sym) (carry res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (c : Bool) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).step
        (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inScan)) v temp
          (carry, (res, r)) S inp dst scr xt (Sym.bit c :: rt) at' wit pre g)
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inScan)) v none
          (nextCarry carry c, (res, r)) S inp dst (Sym.bit (outBit carry c) :: scr) xt rt at' wit
          pre g) := by
  simp only [iTM, cTM, aTM, qTM, inCfg, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram,
    prepCont, queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute,
    lkRoute, turnRoute, cleanRoute, incRoute, inScanStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.inScan), (v, (none, (nextCarry carry c, (res, r)))), T⟩ :
      (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf,
        symIsTrue]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass one's empty exit: the seed tape is exhausted — the only way the width is ever known. -/
theorem in_step_scan_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).step
        (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inScan)) v temp pay S inp
          dst scr xt [] at' wit pre g)
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v none pay S
          inp dst scr xt [] at' wit pre g) := by
  simp only [iTM, cTM, aTM, qTM, inCfg, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram,
    prepCont, queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute,
    lkRoute, turnRoute, cleanRoute, incRoute, inScanStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.inBack), (v, (none, pay)), T⟩ :
      (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass two, one cell. -/
theorem in_step_back_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).step
        (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v temp pay S inp
          dst (c :: scr) xt rt at' wit pre g)
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v none pay S
          inp dst scr xt (c :: rt) at' wit pre g) := by
  simp only [iTM, cTM, aTM, qTM, inCfg, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram,
    prepCont, queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute,
    lkRoute, turnRoute, cleanRoute, incRoute, inBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.inBack), (v, (none, pay)), T⟩ :
      (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass two's empty exit, at the increment's boundary. -/
theorem in_step_back_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (iTM eIn eOut p₀ dzero ddec dreset rest).step
        (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v temp pay S inp
          dst [] xt rt at' wit pre g)
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inTest)) v none pay S
          inp dst [] xt rt at' wit pre g) := by
  simp only [iTM, cTM, aTM, qTM, inCfg, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram,
    prepCont, queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute,
    lkRoute, turnRoute, cleanRoute, incRoute, inBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.inTest), (v, (none, pay)), T⟩ :
      (iTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-! ### The two passes -/

/-- **Pass one**, with an explicit incoming carry and an arbitrary scratch accumulator: the
transformed seed lands reversed on scratch and the carry left is `finalCarry`. -/
theorem in_scan (bs : List Bool) :
    ∀ (carry : Bool) (scr : List Sym) (v : tm.σ) (temp : Option Sym) (res : Bool) (r : R)
      (S : ∀ k, List (tm.Γ k)) (inp dst xt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[bs.length + 1]
        (some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inScan)) v temp
          (carry, (res, r)) S inp dst scr xt (ofBits bs) at' wit pre g))
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v none
          (finalCarry carry bs, (res, r)) S inp dst
          ((ofBits (incTransform carry bs)).reverse ++ scr) xt [] at' wit pre g) := by
  induction bs with
  | nil =>
    intro carry scr v temp res r S inp dst xt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one, ofBits_nil,
      in_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (in_step_scan_nil eIn eOut p₀ dzero ddec dreset rest v temp (carry, (res, r)) S inp dst scr
          xt at' wit pre g)]
    simp
  | cons c bs ih =>
    intro carry scr v temp res r S inp dst xt at' wit pre g
    change (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[(bs.length + 1) + 1]
      _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)
        (bs.length + 1) 1,
      Function.iterate_one, ofBits_cons,
      in_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (in_step_scan_cons eIn eOut p₀ dzero ddec dreset rest v temp carry res r S c inp dst scr xt
          (ofBits bs) at' wit pre g),
      ih (nextCarry carry c) (Sym.bit (outBit carry c) :: scr) v none res r S inp dst xt at' wit
        pre g,
      incTransform_cons, finalCarry_cons]
    simp

/-- **Pass two**, with an arbitrary seed-tape accumulator. -/
theorem in_back (scr : List Sym) :
    ∀ (rt : List Sym) (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
      (S : ∀ k, List (tm.Γ k)) (inp dst xt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[scr.length + 1]
        (some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inBack)) v temp pay S
          inp dst scr xt rt at' wit pre g))
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inTest)) v none pay S
          inp dst [] xt (scr.reverse ++ rt) at' wit pre g) := by
  induction scr with
  | nil =>
    intro rt v temp pay S inp dst xt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      in_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (in_step_back_nil eIn eOut p₀ dzero ddec dreset rest v temp pay S inp dst xt rt at' wit pre
          g)]
    simp
  | cons c scr ih =>
    intro rt v temp pay S inp dst xt at' wit pre g
    change (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[(scr.length + 1) + 1]
      _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)
        (scr.length + 1) 1,
      Function.iterate_one,
      in_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (in_step_back_cons eIn eOut p₀ dzero ddec dreset rest v temp pay S c inp dst scr xt rt at'
          wit pre g),
      ih (c :: rt) v none pay S inp dst xt at' wit pre g]
    simp

/-! ### The increment -/

/-- **The increment, on the seed-round machine.**  `2 * bs.length + 3` steps from `inInit` to the
active `inTest`: the seed tape holds `ofBits (incBits bs)` **in order**, scratch is empty again, the
temporary is cleared, and the helper flag holds the overflow `finalCarry true bs` — whatever it held
on entry.  The result bit, all of `R`, the source input tape, the history tape, the call storage,
the witness and the unrelated frame are untouched. -/
theorem in_trace (bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst xt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[2 * bs.length + 3]
        (some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inInit)) v temp
          (flag, (res, r)) S inp dst [] xt (ofBits bs) at' wit pre g))
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inTest)) v none
          (finalCarry true bs, (res, r)) S inp dst [] xt (ofBits (incBits bs)) at' wit pre g) := by
  have hsplit : 2 * bs.length + 3
      = ((ofBits (incTransform true bs)).reverse.length + 1) + ((bs.length + 1) + 1) := by
    simp only [List.length_reverse, length_ofBits, length_incTransform]; omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)
      ((ofBits (incTransform true bs)).reverse.length + 1) ((bs.length + 1) + 1),
    Function.iterate_add_apply (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)
      (bs.length + 1) 1,
    Function.iterate_one,
    in_bind_of_step eIn eOut p₀ dzero ddec dreset rest
      (in_step_init eIn eOut p₀ dzero ddec dreset rest v temp flag res r S inp dst [] xt
        (ofBits bs) at' wit pre g),
    in_scan eIn eOut p₀ dzero ddec dreset rest bs true [] v none res r S inp dst xt at' wit pre g,
    List.append_nil,
    in_back eIn eOut p₀ dzero ddec dreset rest (ofBits (incTransform true bs)).reverse [] v none
      (finalCarry true bs, (res, r)) S inp dst xt at' wit pre g]
  simp

/-- The same, read on seeds: without overflow the tape holds the **successor seed**. -/
theorem in_trace_bitsOfFin (k : ℕ) (j : Fin (2 ^ k)) (h : j.val + 1 < 2 ^ k) (v : tm.σ)
    (temp : Option Sym) (flag res : Bool) (r : R) (S : ∀ k, List (tm.Γ k))
    (inp dst xt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[2 * k + 3]
        (some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inInit)) v temp
          (flag, (res, r)) S inp dst [] xt (ofBits (bitsOfFin k j)) at' wit pre g))
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inTest)) v none
          (false, (res, r)) S inp dst [] xt (ofBits (bitsOfFin k ⟨j.val + 1, h⟩)) at' wit pre
          g) := by
  have := in_trace eIn eOut p₀ dzero ddec dreset rest (bitsOfFin k j) v temp flag res r S inp dst
    xt at' wit pre g
  rwa [length_bitsOfFin, finalCarry_bitsOfFin_of_lt k j h, incBits_bitsOfFin k j h] at this

/-- …and at the last seed the tape wraps to the first and the overflow is raised. -/
theorem in_trace_last (k : ℕ) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst xt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (iTM eIn eOut p₀ dzero ddec dreset rest).step)^[2 * k + 3]
        (some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inInit)) v temp
          (flag, (res, r)) S inp dst [] xt
          (ofBits (bitsOfFin k ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩)) at' wit
          pre g))
      = some (inCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.inTest)) v none
          (true, (res, r)) S inp dst [] xt (ofBits (bitsOfFin k ⟨0, Nat.two_pow_pos k⟩)) at' wit
          pre g) := by
  have := in_trace eIn eOut p₀ dzero ddec dreset rest
    (bitsOfFin k ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos⟩) v temp flag res r S inp
    dst xt at' wit pre g
  rwa [length_bitsOfFin, finalCarry_bitsOfFin_last, incBits_bitsOfFin_last] at this

end Steps

end

end PCP.Machine
