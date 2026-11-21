import PCP.Complexity.CallEntry

/-!
# Tuple preparation: assemble `encodeTriple` without losing the source tapes

The algorithm's machine predicate is stated for `encodeTriple`, so before each call the checker must
build **exactly** `ofBits x ++ [sep] ++ ofBits r ++ [sep] ++ ofBits answers` on the call's input
stack, and still have `x`, `r` and `answers` afterwards.

## Precondition, stated rather than assumed away

The three source tapes are taken as **already separated canonical bit tapes** on three frame stacks.
Producing them from the checker's encoded input pair, and generating the seed, are separate later
obligations; nothing here decodes an arbitrary tape.

## Where it lives

The three tapes are ordinary *frame* stacks (`G := TripleSlot ⊕ G'`), which call entry and return
already preserve, so `callProgram` needs no change at all.  The preparation phases are `CallLabel`
constructors that dispatch through the supplied continuation exactly as `resume` does, so every
theorem about `callProgram` continues to apply.

## Updates at a variable slot index

The stack family is updated at `inr (inr (inl j))` with `j` a *variable* slot, and that is what
makes these proofs awkward: the resulting `dite`s carry dependent motives.

The route that works here is an early **`cases j`**, so every index in the proof is a constructor
and the `dite`s decide, together with trying `rfl` **before** simplification in each observation
branch — several residual equalities close definitionally, and `simp` was failing on some of them.
After the index cases are fixed, unfolding `Function.update` in the remaining branches is fine.  One
shared program and one shared theorem statement per phase are kept; only the proof script splits.

`prep_step_p1_nil` states its endpoint as `Function.update t j []` rather than `t`, so both sides
carry the same `dite` shape.  That is a proof interface, not a weakening: under `ht : t j = []` the
two are extensionally equal, and `prep_block` recovers `t` once, via `Function.update_eq_self`.

## Order and counting

The preserving copy *prepends* to its destination, so the blocks are assembled in reverse: answers,
separator, seed, separator, input.  Each block is the two-pass copy at `2 * length + 2` and each
separator is its own counted step, and `prep_trace` proves the total is exactly
`2 * (x.length + r.length + answers.length) + 8`.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The three source tapes the checker keeps across a call. -/
inductive TripleSlot | xs | rs | as
  deriving DecidableEq, Inhabited, Repr

instance : Fintype TripleSlot where
  elems := {TripleSlot.xs, TripleSlot.rs, TripleSlot.as}
  complete := by intro t; cases t <;> decide

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (P : Type) [Fintype P]

/-- `Sym` on the three source tapes, the caller's own alphabets on the rest of the frame. -/
abbrev prepΓ : TripleSlot ⊕ G → Type
  | .inl _ => Sym
  | .inr j => Γg j

/-- The frame: the three source tapes as one function, plus the unrelated frame. -/
def prepFrame (t : TripleSlot → List Sym) (g : ∀ j : G, List (Γg j)) :
    ∀ j : TripleSlot ⊕ G, List (prepΓ G Γg j)
  | .inl s => t s
  | .inr j => g j

/-- The statements have the same shape for each block, so they are built once. -/
abbrev PrepStmt : Type :=
  Stmt (embedΓ tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)))
    (tm.Λ ⊕ CallLabel) (tm.σ × CallState P)

/-- Phase one: drain source tape `j` onto scratch. -/
def prepP1 (j : TripleSlot) (self next : CallLabel) : PrepStmt tm G Γg P :=
  pop (.inr (.inr (.inl j))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl .scratch)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr self))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr next)))

/-- Phase two: drain scratch, pushing each symbol back onto source tape `j` **and** onto the call's
input.  The temporary is reset only after both pushes. -/
def prepP2 (j : TripleSlot) (self next : CallLabel) : PrepStmt tm G Γg P :=
  pop (.inr (.inl .scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inl j))) (fun p => p.2.1.getD Sym.sep)
        (push (.inr (.inl .input)) (fun p => p.2.1.getD Sym.sep)
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr self)))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr next)))

/-- A separator: one counted step. -/
def prepSepStmt (next : CallLabel) : PrepStmt tm G Γg P :=
  push (.inr (.inl .input)) (fun _ => Sym.sep) (goto (fun _ => .inr next))

/-- The continuation implementing preparation.  Everything outside the eight preparation labels is
routed to the supplied **label-indexed** continuation, so dispatch, rejection and lookup can run
different statements. -/
def prepCont (route : CallLabel → PrepStmt tm G Γg P) : CallLabel → PrepStmt tm G Γg P
  | .prepA1 => prepP1 tm G Γg P .as .prepA1 .prepA2
  | .prepA2 => prepP2 tm G Γg P .as .prepA2 .sepR
  | .sepR => prepSepStmt tm G Γg P .prepR1
  | .prepR1 => prepP1 tm G Γg P .rs .prepR1 .prepR2
  | .prepR2 => prepP2 tm G Γg P .rs .prepR2 .sepX
  | .sepX => prepSepStmt tm G Γg P .prepX1
  | .prepX1 => prepP1 tm G Γg P .xs .prepX1 .prepX2
  | .prepX2 => prepP2 tm G Γg P .xs .prepX2 .entry1
  | l => route l

/-- The canonical source tapes: the input, the seed, and the answers so far. -/
def tripleTapes (x r a : List Bool) : TripleSlot → List Sym
  | .xs => ofBits x
  | .rs => ofBits r
  | .as => ofBits a

variable {tm G Γg P}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
  (route : CallLabel → PrepStmt tm G Γg P)

/-- A configuration, with the three source tapes named as one function. -/
def prepCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (t : TripleSlot → List Sym)
    (g : ∀ j : G, List (Γg j)) : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg :=
  callCfg eIn eOut p₀ (prepCont tm G Γg P route) l v temp pay S inp dst scratch
    (prepFrame G Γg t g)

theorem prep_step_p1_cons (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self) = prepP1 tm G Γg P j self next)
    (v : tm.σ) (temp : Option Sym) (pay : P) (c : Sym) (rest : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (ht : t j = c :: rest)
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀ (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch t g)
      = some (prepCfg eIn eOut p₀ route (some (.inr self)) v none pay S inp dst
          (c :: scratch) (Function.update t j rest) g) := by
  cases j <;>
  · change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self)) (v, (temp, pay))
        (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
          (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst scratch (prepFrame G Γg t g)))) = _
    rw [hp]
    simp only [prepP1, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, ht,
      List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
    refine congrArg some (congrArg (fun T => (⟨some (.inr self), (v, (none, pay)), T⟩ :
      (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg)) ?_)
    funext i
    rcases i with k | cs | ts | j'
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases cs <;>
        first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases ts <;>
        first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, ht]
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-- Phase one's empty exit. -/
theorem prep_step_p1_nil (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self) = prepP1 tm G Γg P j self next)
    (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (ht : t j = [])
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀ (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch t g)
      = some (prepCfg eIn eOut p₀ route (some (.inr next)) v none pay S inp dst scratch
          (Function.update t j []) g) := by
  cases j <;>
  · change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self)) (v, (temp, pay))
        (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
          (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst scratch
            (prepFrame G Γg t g)))) = _
    rw [hp]
    simp only [prepP1, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame, ht,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    refine congrArg some (congrArg (fun T => (⟨some (.inr next), (v, (none, pay)), T⟩ :
      (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg)) ?_)
    funext i
    rcases i with k | cs | ts | j'
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases cs <;>
        first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases ts <;>
        first
          | rfl
          | (rw [dif_pos rfl]; simp_all [embedStacks, callFrame, prepFrame])
          | simp_all [Function.update, embedStacks, callFrame, prepFrame]
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]


/-- **The two-push preparation step.**  The popped symbol reaches source tape `j` *and* the call's
input, and the temporary is reset only afterwards. -/
theorem prep_step_p2_cons (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self) = prepP2 tm G Γg P j self next)
    (v : tm.σ) (temp : Option Sym) (pay : P) (c : Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀ (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst (c :: scratch)
          t g)
      = some (prepCfg eIn eOut p₀ route (some (.inr self)) v none pay S (c :: inp) dst
          scratch (Function.update t j (c :: t j)) g) := by
  cases j <;>
  · change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self)) (v, (temp, pay))
        (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
          (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst (c :: scratch)
            (prepFrame G Γg t g)))) = _
    rw [hp]
    simp only [prepP2, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame,
      List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
    refine congrArg some (congrArg (fun T => (⟨some (.inr self), (v, (none, pay)), T⟩ :
      (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg)) ?_)
    funext i
    rcases i with k | cs | ts | j'
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases cs <;>
        first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases ts <;>
        first
          | rfl
          | (rw [dif_pos rfl]; simp_all [embedStacks, callFrame, prepFrame])
          | simp_all [Function.update, embedStacks, callFrame, prepFrame]
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]


/-- Phase two's empty exit. -/
theorem prep_step_p2_nil (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self) = prepP2 tm G Γg P j self next)
    (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀ (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst [] t g)
      = some (prepCfg eIn eOut p₀ route (some (.inr next)) v none pay S inp dst [] t g) := by
  cases j <;>
  · change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self)) (v, (temp, pay))
        (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
          (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst []
            (prepFrame G Γg t g)))) = _
    rw [hp]
    simp only [prepP2, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame,
      List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    refine congrArg some (congrArg (fun T => (⟨some (.inr next), (v, (none, pay)), T⟩ :
      (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg)) ?_)
    funext i
    rcases i with k | cs | ts | j'
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases cs <;>
        first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
    · cases ts <;>
        first
          | rfl
          | (rw [dif_pos rfl]; simp_all [embedStacks, callFrame, prepFrame])
          | simp_all [Function.update, embedStacks, callFrame, prepFrame]
    · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]


/-- A separator push: **one** counted step. -/
theorem prep_step_sep (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).m (Sum.inr self) = prepSepStmt tm G Γg P next)
    (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀ (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch t g)
      = some (prepCfg eIn eOut p₀ route (some (.inr next)) v temp pay S (Sym.sep :: inp) dst
          scratch t g) := by
  change some (stepAux ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self)) (v, (temp, pay))
      (embedStacks tm (CallSlot ⊕ (TripleSlot ⊕ G)) (callΓ (TripleSlot ⊕ G) (prepΓ G Γg)) S
        (callFrame (TripleSlot ⊕ G) (prepΓ G Γg) inp dst scratch (prepFrame G Γg t g)))) = _
  rw [hp]
  simp only [prepSepStmt, Turing.TM2.stepAux, embedStacks_inr, callFrame, prepFrame]
  refine congrArg some (congrArg (fun T => (⟨some (.inr next), (v, (temp, pay)), T⟩ :
    (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
        (prepCont tm G Γg P route)).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame]

/-! ### The two accumulator invariants

Phase one keeps the update-shaped endpoint; the block lemma below is where the original family is
recovered, once. -/

theorem prep_phase_one (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self) = prepP1 tm G Γg P j self next) :
    ∀ (zs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P) (S : ∀ k, List (tm.Γ k))
      (t : TripleSlot → List Sym) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)),
      (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[zs.length + 1]
          (some (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch
            (Function.update t j zs) g))
        = some (prepCfg eIn eOut p₀ route (some (.inr next)) v none pay S inp dst
            (zs.reverse ++ scratch) (Function.update t j []) g)
  | [], v, temp, pay, S, t, inp, dst, scratch, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
          (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch
          (Function.update t j []) g) = _
      rw [prep_step_p1_nil eIn eOut p₀ route j self next hp v temp pay S _
        (by simp) inp dst scratch g, Function.update_idem]
      simp
  | z :: zs, v, temp, pay, S, t, inp, dst, scratch, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[zs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
            (prepCont tm G Γg P route)).step
          (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch
            (Function.update t j (z :: zs)) g)) = _
      rw [prep_step_p1_cons eIn eOut p₀ route j self next hp v temp pay z zs S _
        (by simp) inp dst scratch g, Function.update_idem,
        prep_phase_one j self next hp zs v none pay S t inp dst (z :: scratch) g]
      simp

theorem prep_phase_two (j : TripleSlot) (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self) = prepP2 tm G Γg P j self next) :
    ∀ (rs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P) (S : ∀ k, List (tm.Γ k))
      (t : TripleSlot → List Sym) (inp dst : List Sym) (g : ∀ j : G, List (Γg j)),
      (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[rs.length + 1]
          (some (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst rs t g))
        = some (prepCfg eIn eOut p₀ route (some (.inr next)) v none pay S
            (rs.reverse ++ inp) dst [] (Function.update t j (rs.reverse ++ t j)) g)
  | [], v, temp, pay, S, t, inp, dst, g => by
      change (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
          (prepCont tm G Γg P route)).step
        (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst [] t g) = _
      rw [prep_step_p2_nil eIn eOut p₀ route j self next hp v temp pay S t inp dst g]
      simp
  | c :: rs, v, temp, pay, S, t, inp, dst, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[rs.length + 1]
        ((callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
            (prepCont tm G Γg P route)).step
          (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst (c :: rs)
            t g)) = _
      rw [prep_step_p2_cons eIn eOut p₀ route j self next hp v temp pay c S t inp dst
          rs g,
        prep_phase_two j self next hp rs v none pay S (Function.update t j (c :: t j))
          (c :: inp) dst g]
      simp [Function.update_idem]

/-- **One block**: a preserving copy of source tape `j` onto the call input, leaving the whole
source family exactly as it was.  This is where the update-shaped phase-one endpoint is simplified
away, once. -/
theorem prep_block (j : TripleSlot) (l1 l2 next : CallLabel)
    (hp1 : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr l1) = prepP1 tm G Γg P j l1 l2)
    (hp2 : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr l2) = prepP2 tm G Γg P j l2 next)
    (zs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P) (S : ∀ k, List (tm.Γ k))
    (t : TripleSlot → List Sym) (ht : t j = zs) (inp dst : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[2 * zs.length + 2]
        (some (prepCfg eIn eOut p₀ route (some (.inr l1)) v temp pay S inp dst [] t g))
      = some (prepCfg eIn eOut p₀ route (some (.inr next)) v none pay S (zs ++ inp) dst []
          t g) := by
  have hsplit : 2 * zs.length + 2 = (zs.reverse.length + 1) + (zs.length + 1) := by
    rw [List.length_reverse]; omega
  have hres : Function.update t j zs = t := by rw [← ht]; exact Function.update_eq_self j t
  rw [hsplit, Function.iterate_add_apply, ← hres,
    prep_phase_one eIn eOut p₀ route j l1 l2 hp1 zs v temp pay S t inp dst [] g,
    List.append_nil,
    prep_phase_two eIn eOut p₀ route j l2 next hp2 zs.reverse v none pay S
      (Function.update t j []) inp dst g]
  simp [Function.update_idem, hres]

/-- The separator step at the optional-iteration level, so it composes with `Function.iterate`. -/
theorem prep_bind_sep (self next : CallLabel)
    (hp : (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).m (Sum.inr self) = prepSepStmt tm G Γg P next)
    (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)
        (some (prepCfg eIn eOut p₀ route (some (.inr self)) v temp pay S inp dst scratch t g))
      = some (prepCfg eIn eOut p₀ route (some (.inr next)) v temp pay S (Sym.sep :: inp) dst
          scratch t g) :=
  prep_step_sep eIn eOut p₀ route self next hp v temp pay S t inp dst scratch g

/-! ### The assembled triple

The blocks run answers, separator, seed, separator, input, because the copy *prepends*. -/

theorem prep_trace (x r a : List Bool) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step)^[2 * (x.length + r.length + a.length) + 8]
        (some (prepCfg eIn eOut p₀ route (some (.inr .prepA1)) v temp pay S [] dst []
          (tripleTapes x r a) g))
      = some (prepCfg eIn eOut p₀ route (some (.inr .entry1)) v none pay S
          (encodeTriple (x, r, a)) dst [] (tripleTapes x r a) g) := by
  have hsplit : 2 * (x.length + r.length + a.length) + 8
      = (2 * (ofBits x).length + 2) + (1 + ((2 * (ofBits r).length + 2)
          + (1 + (2 * (ofBits a).length + 2)))) := by simp only [length_ofBits]; omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn
        eOut p₀ (prepCont tm G Γg P route)).step) (2 * (ofBits x).length + 2)
      (1 + ((2 * (ofBits r).length + 2) + (1 + (2 * (ofBits a).length + 2)))),
    Function.iterate_add_apply (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn
        eOut p₀ (prepCont tm G Γg P route)).step) 1
      ((2 * (ofBits r).length + 2) + (1 + (2 * (ofBits a).length + 2))),
    Function.iterate_add_apply (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn
        eOut p₀ (prepCont tm G Γg P route)).step) (2 * (ofBits r).length + 2)
      (1 + (2 * (ofBits a).length + 2)),
    Function.iterate_add_apply (flip Bind.bind (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn
        eOut p₀ (prepCont tm G Γg P route)).step) 1 (2 * (ofBits a).length + 2),
    prep_block eIn eOut p₀ route .as .prepA1 .prepA2 .sepR rfl rfl (ofBits a) v temp pay S
      (tripleTapes x r a) rfl [] dst g,
    Function.iterate_one,
    prep_bind_sep eIn eOut p₀ route .sepR .prepR1 rfl v none pay S (tripleTapes x r a)
      (ofBits a ++ []) dst [] g,
    prep_block eIn eOut p₀ route .rs .prepR1 .prepR2 .sepX rfl rfl (ofBits r) v none pay S
      (tripleTapes x r a) rfl (Sym.sep :: (ofBits a ++ [])) dst g,
    prep_bind_sep eIn eOut p₀ route .sepX .prepX1 rfl v none pay S (tripleTapes x r a)
      (ofBits r ++ Sym.sep :: (ofBits a ++ [])) dst [] g,
    prep_block eIn eOut p₀ route .xs .prepX1 .prepX2 .entry1 rfl rfl (ofBits x) v none pay S
      (tripleTapes x r a) rfl (Sym.sep :: (ofBits r ++ Sym.sep :: (ofBits a ++ []))) dst g]
  simp [encodeTriple, List.append_assoc]

/-- The preparation certificate, with its count written out. -/
def prepEvals (x r a : List Bool) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM tm (TripleSlot ⊕ G) (prepΓ G Γg) P eIn eOut p₀
      (prepCont tm G Γg P route)).step
      (prepCfg eIn eOut p₀ route (some (.inr .prepA1)) v temp pay S [] dst []
        (tripleTapes x r a) g)
      (some (prepCfg eIn eOut p₀ route (some (.inr .entry1)) v none pay S
        (encodeTriple (x, r, a)) dst [] (tripleTapes x r a) g))
      (2 * (x.length + r.length + a.length) + 8) where
  steps := 2 * (x.length + r.length + a.length) + 8
  evals_in_steps := prep_trace eIn eOut p₀ route x r a v temp pay S dst g
  steps_le_m := le_refl _

@[simp] theorem prepEvals_steps (x r a : List Bool) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    (prepEvals eIn eOut p₀ route x r a v temp pay S dst g).steps
      = 2 * (x.length + r.length + a.length) + 8 := rfl

end Steps

/-! ## Handing the triple to an actual algorithm witness

Preparation's own theorem keeps `S` and `dst` arbitrary — it does **not** clear them.  The call's
precondition needs empty callee stacks, so the composition below specialises `S := fun _ => []`.
`dst` stays arbitrary and accumulates.

Both certificates use the *same* machine, the *same* alphabet equivalences and the *same*
continuation.  Their configuration types would coincide anyway; that alone would not make their step
functions agree, so the sharing is explicit. -/

section Handoff

variable (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type) (P : Type) [Fintype P]
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **Preparation followed by the call.**  From the preparation label with three canonical bit
tapes, every callee stack empty and an arbitrary destination, to the caller's `resume` boundary with
the algorithm's encoded answer prepended to that destination — every callee stack empty again, all
three source tapes, the payload and the unrelated frame preserved.

The recorded count is preparation's plus the call's own; the bound is preparation's plus the call
polynomial, evaluated at the **actual encoded triple length**.  The two are kept apart. -/
noncomputable def prepCallEvals
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (p₀ : P)
    (route : CallLabel → PrepStmt hw.tm G Γg P) (x r a : List Bool) (dst : List Sym) (v : hw.tm.σ)
    (temp : Option Sym) (pay : P) (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM hw.tm (TripleSlot ⊕ G) (prepΓ G Γg) P hw.inputAlphabet
      hw.outputAlphabet p₀ (prepCont hw.tm G Γg P route)).step
      (prepCfg hw.inputAlphabet hw.outputAlphabet p₀ route (some (.inr .prepA1)) v temp pay
        (fun _ => []) [] dst [] (tripleTapes x r a) g)
      (some (callCfg hw.inputAlphabet hw.outputAlphabet p₀ (prepCont hw.tm G Γg P route)
        (some (.inr .resume)) hw.tm.initialState none pay (fun _ => []) (encodeTriple (x, r, a))
        (encodeAnswer (f (x, r, a)) ++ dst) [] (prepFrame G Γg (tripleTapes x r a) g)))
      ((2 * (x.length + r.length + a.length) + 8)
        + (callPoly hw.tm hw.time).eval (encodeTriple (x, r, a)).length) where
  steps := (2 * (x.length + r.length + a.length) + 8)
    + ((callEvalsPoly (TripleSlot ⊕ G) (prepΓ G Γg) P hw p₀ (prepCont hw.tm G Γg P route)
        (x, r, a) dst v none pay (prepFrame G Γg (tripleTapes x r a) g)).steps)
  evals_in_steps := by
    have hfirst : (flip Bind.bind (callTM hw.tm (TripleSlot ⊕ G) (prepΓ G Γg) P
          hw.inputAlphabet hw.outputAlphabet p₀
          (prepCont hw.tm G Γg P route)).step)^[2 * (x.length + r.length + a.length) + 8]
          (some (prepCfg hw.inputAlphabet hw.outputAlphabet p₀ route (some (.inr .prepA1)) v
            temp pay (fun _ => []) [] dst [] (tripleTapes x r a) g))
        = some (prepCfg hw.inputAlphabet hw.outputAlphabet p₀ route (some (.inr .entry1)) v
            none pay (fun _ => []) (encodeTriple (x, r, a)) dst [] (tripleTapes x r a) g) :=
      prep_trace hw.inputAlphabet hw.outputAlphabet p₀ route x r a v temp pay
        (fun _ => []) dst g
    have hsecond := (callEvalsPoly (TripleSlot ⊕ G) (prepΓ G Γg) P hw p₀
      (prepCont hw.tm G Γg P route) (x, r, a) dst v none pay
      (prepFrame G Γg (tripleTapes x r a) g)).evals_in_steps
    have hsplit : (2 * (x.length + r.length + a.length) + 8)
        + ((callEvalsPoly (TripleSlot ⊕ G) (prepΓ G Γg) P hw p₀
            (prepCont hw.tm G Γg P route) (x, r, a) dst v none pay
            (prepFrame G Γg (tripleTapes x r a) g)).steps)
        = ((callEvalsPoly (TripleSlot ⊕ G) (prepΓ G Γg) P hw p₀
            (prepCont hw.tm G Γg P route) (x, r, a) dst v none pay
            (prepFrame G Γg (tripleTapes x r a) g)).steps)
          + (2 * (x.length + r.length + a.length) + 8) := by omega
    rw [hsplit, Function.iterate_add_apply, hfirst]
    exact hsecond
  steps_le_m :=
    Nat.add_le_add_left (callEvalsPoly (TripleSlot ⊕ G) (prepΓ G Γg) P hw p₀
      (prepCont hw.tm G Γg P route) (x, r, a) dst v none pay
      (prepFrame G Γg (tripleTapes x r a) g)).steps_le_m _

@[simp] theorem prepCallEvals_steps
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (p₀ : P)
    (route : CallLabel → PrepStmt hw.tm G Γg P) (x r a : List Bool) (dst : List Sym) (v : hw.tm.σ)
    (temp : Option Sym) (pay : P) (g : ∀ j : G, List (Γg j)) :
    (prepCallEvals G Γg P hw p₀ route x r a dst v temp pay g).steps
      = (2 * (x.length + r.length + a.length) + 8)
        + ((2 * (encodeTriple (x, r, a)).length + 2)
          + (hw.outputsFun (x, r, a)).steps
          + (2 * (encodeAnswer (f (x, r, a))).length + 2)) := rfl

end Handoff

end

end PCP.Machine
