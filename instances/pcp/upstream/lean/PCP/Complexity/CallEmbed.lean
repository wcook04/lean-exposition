import PCP.Complexity.Bounds

/-!
# Embedding a callee's statements in a caller

The checker needs to call a fixed algorithm machine many times while keeping `(x, w, r, answers)`.
That means running a callee's program inside a larger machine which owns extra stacks and extra
control, and getting back a theorem that says the callee behaved exactly as it would alone.  This
module is the **statement-level** half of that: one `stepAux` equation, quantified over everything.

## Layout

| Component | Parent representation |
|---|---|
| stack indices | `tm.K ⊕ F` |
| stack alphabets | `tm.Γ k` on the left, arbitrary `Γf j` on the right |
| control state | `tm.σ × τ` |
| labels | `tm.Λ ⊕ L` |
| return destination | a specified `ret : L` |

The frame alphabets need no finiteness, no coding instance and no default symbol.  Nothing here
mentions `tm.k₀` or `tm.k₁`, so a callee whose input and output stacks **coincide** is covered; the
fixtures check that.  Anything unbounded belongs on a stack, never in `τ`.

## The return boundary

A source terminal configuration maps to a parent configuration whose label is `some (inr ret)` —
*active*, ready to run the caller's return continuation.  That is deliberate, and it is also why
this correspondence is about `stepAux` and, at the next stage, about steps from an **active source
label** only.  At a terminal source label `tm.step` is outer `none` while the parent has real work
left to do, so an unconditional semiconjugacy is false.  Translated `halt` is a `goto` to `inr ret`
and nothing else: it does not reset the state or touch a stack, because source `halt` does not
either.

## Equality instances

`stepAux` updates stacks through `DecidableEq` on the index type.  `embedStacks_update` below is
stated for the instance ambient on `tm.K ⊕ F`.  Any decidable-equality instance on that type gives
the same function, so this is an engineering choice rather than a mathematical restriction — but a
*different* instance would have to be reconciled explicitly before the rewrite applies.  The parent
`FinTM2` in `PCP/Complexity/CallTrace.lean` therefore takes its `kDecidableEq` field to be exactly
this one.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt

section

variable (tm : FinTM2) (F : Type) (Γf : F → Type)

/-- The parent's alphabet family: the callee's on its own stacks, the caller's on the frame.

`abbrev`, so that `embedΓ tm F Γf (.inl k)` reduces to `tm.Γ k` at reducible transparency: the
dependent stack updates below are rewritten by `rw`/`simp`, which match there. -/
abbrev embedΓ : tm.K ⊕ F → Type
  | .inl k => tm.Γ k
  | .inr j => Γf j

/-- The parent's stack family. -/
def embedStacks (S : ∀ k, List (tm.Γ k)) (frame : ∀ j : F, List (Γf j)) :
    ∀ i : tm.K ⊕ F, List (embedΓ tm F Γf i)
  | .inl k => S k
  | .inr j => frame j

@[simp] theorem embedStacks_inl (S : ∀ k, List (tm.Γ k)) (frame : ∀ j : F, List (Γf j))
    (k : tm.K) : embedStacks tm F Γf S frame (.inl k) = S k := rfl

@[simp] theorem embedStacks_inr (S : ∀ k, List (tm.Γ k)) (frame : ∀ j : F, List (Γf j))
    (j : F) : embedStacks tm F Γf S frame (.inr j) = frame j := rfl

variable {tm F Γf}

/-- **The dependent update equation**, settled once before the translator.  A callee-side update
becomes a parent-side update at the corresponding left index, and the frame is untouched. -/
theorem embedStacks_update [DecidableEq F] (S : ∀ k, List (tm.Γ k))
    (frame : ∀ j : F, List (Γf j)) (k : tm.K) (xs : List (tm.Γ k)) :
    embedStacks tm F Γf (Function.update S k xs) frame
      = Function.update (embedStacks tm F Γf S frame) (Sum.inl k) xs := by
  funext i
  rcases i with k' | j
  · by_cases h : k' = k
    · subst h
      rw [Function.update_self]
      exact Function.update_self ..
    · rw [Function.update_of_ne (by simpa using h)]
      exact Function.update_of_ne h _ _
  · rw [Function.update_of_ne (by simp)]
    rfl

/-- The companion for a **frame** update: the caller's own stacks change, the callee's do not. -/
theorem embedStacks_update_frame [DecidableEq F] (S : ∀ k, List (tm.Γ k))
    (frame : ∀ j : F, List (Γf j)) (j : F) (xs : List (Γf j)) :
    embedStacks tm F Γf S (Function.update frame j xs)
      = Function.update (embedStacks tm F Γf S frame) (Sum.inr j) xs := by
  funext i
  rcases i with k | j'
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases h : j' = j
    · subst h
      rw [Function.update_self]
      exact Function.update_self ..
    · rw [Function.update_of_ne (by simpa using h)]
      exact Function.update_of_ne h _ _

section Translate

variable {τ L : Type} (ret : L)

/-- The parent configuration a callee configuration sits inside.  A **terminal** callee
configuration becomes an *active* parent configuration at the return label. -/
def embedCfg (t : τ) (frame : ∀ j : F, List (Γf j)) (c : tm.Cfg) :
    Cfg (embedΓ tm F Γf) (tm.Λ ⊕ L) (tm.σ × τ) where
  l := match c.l with
    | some l => some (.inl l)
    | none => some (.inr ret)
  var := (c.var, t)
  stk := embedStacks tm F Γf c.stk frame

@[simp] theorem embedCfg_l_some (t : τ) (frame : ∀ j : F, List (Γf j)) (l : tm.Λ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) :
    (embedCfg (F := F) (Γf := Γf) ret t frame ⟨some l, v, S⟩).l = some (.inl l) := rfl

/-- **Translated `halt` lands on the return label** — active, with the state and every stack exactly
as `halt` found them. -/
@[simp] theorem embedCfg_l_none (t : τ) (frame : ∀ j : F, List (Γf j)) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) :
    (embedCfg (F := F) (Γf := Γf) ret t frame ⟨none, v, S⟩).l = some (.inr ret) := rfl

/-- Translate a callee statement.  Callbacks read and write only the callee's control component;
`halt` becomes a `goto` to the return label and performs no reset. -/
def liftStmt : Stmt tm.Γ tm.Λ tm.σ → Stmt (embedΓ tm F Γf) (tm.Λ ⊕ L) (tm.σ × τ)
  | .push k f q => .push (.inl k) (fun p => f p.1) (liftStmt q)
  | .peek k f q => .peek (.inl k) (fun p o => (f p.1 o, p.2)) (liftStmt q)
  | .pop k f q => .pop (.inl k) (fun p o => (f p.1 o, p.2)) (liftStmt q)
  | .load a q => .load (fun p => (a p.1, p.2)) (liftStmt q)
  | .branch g q₁ q₂ => .branch (fun p => g p.1) (liftStmt q₁) (liftStmt q₂)
  | .goto g => .goto (fun p => .inl (g p.1))
  | .halt => .goto (fun _ => .inr ret)

@[simp] theorem liftStmt_halt :
    liftStmt (tm := tm) (F := F) (Γf := Γf) (τ := τ) ret .halt = .goto (fun _ => .inr ret) := rfl

/-- **The statement-level correspondence.**  For *every* statement, callee state, caller control
value, callee stack family and caller frame: running the translated statement in the parent and
running the original in the callee agree on the complete configuration — label, both control
components, every callee stack, and every frame stack.

No reachability, no cleanup hypothesis, and no assumption that the callee's input and output stacks
differ. -/
theorem stepAux_liftStmt [DecidableEq F] (t : τ) (frame : ∀ j : F, List (Γf j)) :
    ∀ (q : Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      stepAux (liftStmt (F := F) (Γf := Γf) ret q) (v, t) (embedStacks tm F Γf S frame)
        = embedCfg ret t frame (stepAux q v S)
  | .push k f q, v, S => by
      simp only [liftStmt, stepAux, embedStacks_inl, ← embedStacks_update]
      exact stepAux_liftStmt t frame q v _
  | .peek k f q, v, S => by
      simp only [liftStmt, stepAux, embedStacks_inl]
      exact stepAux_liftStmt t frame q _ S
  | .pop k f q, v, S => by
      simp only [liftStmt, stepAux, embedStacks_inl, ← embedStacks_update]
      exact stepAux_liftStmt t frame q _ _
  | .load a q, v, S => by
      simp only [liftStmt, stepAux]
      exact stepAux_liftStmt t frame q _ S
  | .branch g q₁ q₂, v, S => by
      simp only [liftStmt, stepAux]
      cases g v
      · simpa using stepAux_liftStmt t frame q₂ v S
      · simpa using stepAux_liftStmt t frame q₁ v S
  | .goto g, v, S => rfl
  | .halt, v, S => rfl

/-! ## Supporting bounds

Translation replaces `halt` by one `goto` and inserts no push, so neither bound moves. -/

theorem opBound_liftStmt :
    ∀ q : Stmt tm.Γ tm.Λ tm.σ, opBound (liftStmt (F := F) (Γf := Γf) (τ := τ) ret q) = opBound q
  | .push _ _ q => congrArg (1 + ·) (opBound_liftStmt q)
  | .peek _ _ q => congrArg (1 + ·) (opBound_liftStmt q)
  | .pop _ _ q => congrArg (1 + ·) (opBound_liftStmt q)
  | .load _ q => congrArg (1 + ·) (opBound_liftStmt q)
  | .branch _ q₁ q₂ => by
      rw [liftStmt, opBound, opBound, opBound_liftStmt q₁, opBound_liftStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

theorem pushBound_liftStmt :
    ∀ q : Stmt tm.Γ tm.Λ tm.σ,
      pushBound (liftStmt (F := F) (Γf := Γf) (τ := τ) ret q) = pushBound q
  | .push _ _ q => congrArg (1 + ·) (pushBound_liftStmt q)
  | .peek _ _ q => pushBound_liftStmt q
  | .pop _ _ q => pushBound_liftStmt q
  | .load _ q => pushBound_liftStmt q
  | .branch _ q₁ q₂ => by
      rw [liftStmt, pushBound, pushBound, pushBound_liftStmt q₁, pushBound_liftStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

end Translate

end

end PCP.Machine
