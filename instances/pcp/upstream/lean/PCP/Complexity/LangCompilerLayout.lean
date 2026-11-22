import PCP.Complexity.LangBlockReframe

/-!
# Finite saved-counter layouts for the structured compiler

Only syntactic loops allocate saved-counter tapes. Siblings receive disjoint
finite sets; a loop adds one tape beside its body's private counters. Reframing
places a child on the parent's layout while its sibling or enclosing counter is
an arbitrary untouched caller frame. All maps and finite instances are ordinary
computable definitions.
-/

namespace PCP.Lang.Compiler

open PCP.Machine MachineLayout

variable {R Q : ℕ}

/-- One statically allocated private counter for each syntactic loop. -/
abbrev Counters : Stmt R Q → Type
  | .seq s t | .ite _ s t => Counters s ⊕ Counters t
  | .loop _ s => Unit ⊕ Counters s
  | .skip | .assign _ _ | .push _ _ | .pop _ _ _ | .len _ _ |
      .rev _ | .copy _ _ | .revApp _ _ => Empty

/-- Constructive equality on the finite syntactic counter tree. -/
@[instance_reducible]
def countersDecidableEq : (s : Stmt R Q) → DecidableEq (Counters s)
  | .seq s t | .ite _ s t => by
      letI := countersDecidableEq s
      letI := countersDecidableEq t
      exact inferInstanceAs (DecidableEq (Counters s ⊕ Counters t))
  | .loop _ s => by
      letI := countersDecidableEq s
      exact inferInstanceAs (DecidableEq (Unit ⊕ Counters s))
  | .skip | .assign _ _ | .push _ _ | .pop _ _ _ | .len _ _ |
      .rev _ | .copy _ _ | .revApp _ _ => inferInstanceAs (DecidableEq Empty)

/-- The entire private storage index set is finite before execution begins. -/
@[instance_reducible]
def countersFintype : (s : Stmt R Q) → Fintype (Counters s)
  | .seq s t | .ite _ s t => by
      letI := countersFintype s
      letI := countersFintype t
      exact inferInstanceAs (Fintype (Counters s ⊕ Counters t))
  | .loop _ s => by
      letI := countersFintype s
      exact inferInstanceAs (Fintype (Unit ⊕ Counters s))
  | .skip | .assign _ _ | .push _ _ | .pop _ _ _ | .len _ _ |
      .rev _ | .copy _ _ | .revApp _ _ => inferInstanceAs (Fintype Empty)

attribute [instance] countersDecidableEq countersFintype

/-- All private counters are empty at a compiled statement boundary. -/
def zeroFrame {C F : Type} (frame : F → List Sym) : C ⊕ F → List Sym
  | .inl _ => []
  | .inr j => frame j

/-- A compiled statement boundary includes its private counters and the external frame. -/
def boundary {F : Type} (s : Stmt R Q) (st : State R Q) (frame : F → List Sym) :
    Tapes R Q (Counters s ⊕ F) → List Sym := tapes st (zeroFrame frame)

/-- The first child sees the second child's private tapes in its caller frame. -/
def leftFrame (A B F : Type) : A ⊕ (B ⊕ F) ≃ (A ⊕ B) ⊕ F :=
  (Equiv.sumAssoc A B F).symm

/-- The second child sees the first child's private tapes in its caller frame. -/
def rightFrame (A B F : Type) : B ⊕ (A ⊕ F) ≃ (A ⊕ B) ⊕ F :=
  (Equiv.sumAssoc B A F).symm.trans (Equiv.sumCongr (Equiv.sumComm B A) (Equiv.refl F))

theorem zeroFrame_left {A B F : Type} (frame : F → List Sym) :
    (fun j => zeroFrame (C := A ⊕ B) frame (leftFrame A B F j)) =
      zeroFrame (C := A) (zeroFrame (C := B) frame) := by
  funext j
  rcases j with a | (b | j) <;> rfl

theorem zeroFrame_right {A B F : Type} (frame : F → List Sym) :
    (fun j => zeroFrame (C := A ⊕ B) frame (rightFrame A B F j)) =
      zeroFrame (C := B) (zeroFrame (C := A) frame) := by
  funext j
  rcases j with b | (a | j) <;> rfl

/-- Only the enclosing loop's private counter may be nonempty during a body call. -/
def loopFrame {C F : Type} (counter : List Sym) (frame : F → List Sym) :
    (Unit ⊕ C) ⊕ F → List Sym
  | .inl (.inl _) => counter
  | .inl (.inr _) => []
  | .inr j => frame j

/-- The body's private counters are empty, while the enclosing counter belongs to its frame. -/
theorem loopFrame_body {C F : Type} (counter : List Sym) (frame : F → List Sym) :
    (fun j => loopFrame (C := C) counter frame (rightFrame Unit C F j)) =
      zeroFrame (C := C) (fun j => match j with | .inl _ => counter | .inr j => frame j) := by
  funext j
  rcases j with c | (u | j) <;> rfl

/-- Exhausting the loop counter restores the full compiled-statement boundary. -/
theorem loopFrame_empty {C F : Type} (frame : F → List Sym) :
    loopFrame (C := C) [] frame = zeroFrame frame := by
  funext j
  rcases j with (u | c) | j <;> rfl

/-- Capturing or decrementing touches exactly the enclosing loop's counter. -/
theorem loopFrame_update {C F : Type} [DecidableEq C] [DecidableEq F]
    (xs ys : List Sym) (frame : F → List Sym) :
    Function.update (loopFrame (C := C) xs frame) (.inl (.inl ())) ys =
      loopFrame ys frame := by
  funext j
  rcases j with (u | c) | j
  · cases u; simp [loopFrame]
  · simp [loopFrame]
  · simp [loopFrame]

/-- A fixed polynomial coefficient, enlarged only for static composition overhead. -/
def coefficient : Stmt R Q → ℕ
  | .seq s t | .ite _ s t => coefficient s + coefficient t + 4
  | .loop _ s => coefficient s + 128
  | _ => 128

/-- Nested counted loops increase the compiler overhead degree by at most one each. -/
def degree : Stmt R Q → ℕ
  | .seq s t | .ite _ s t => max (degree s) (degree t)
  | .loop _ s => degree s + 1
  | _ => 2

theorem degree_ge_two (s : Stmt R Q) : 2 ≤ degree s := by
  induction s with
  | seq s t hs ht | ite x s t hs ht => exact hs.trans (Nat.le_max_left _ _)
  | loop x s hs => exact hs.trans (Nat.le_add_right _ _)
  | _ => exact le_rfl

end PCP.Lang.Compiler
