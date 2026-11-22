import PCP.Complexity.LangTapeEncoding
import PCP.Complexity.FiniteBlockMachine

/-!
# Shared materialized storage for compiled language statements

Natural registers and list registers occupy their own tapes. Eight fixed scratch
tapes are empty at statement boundaries; all further tapes form an arbitrary
caller frame, including saved counters of enclosing loops. This boundary format
makes source/destination aliases a semantic property of the actual data tapes.
-/

namespace PCP.Lang.MachineLayout

open PCP.Machine

/-- Eight reusable physical work tapes suffice for all arithmetic and list primitives. -/
abbrev Tapes (R Q : ℕ) (F : Type) := DataSlot R Q ⊕ (Fin 8 ⊕ F)

variable {R Q : ℕ} {F : Type}

/-- The physical natural-register tape. -/
def reg (x : Fin R) : Tapes R Q F := .inl (.inl x)

/-- The physical encoded-list tape. -/
def list (L : Fin Q) : Tapes R Q F := .inl (.inr L)

/-- Scratch positions depend only on the compiled program. -/
def work (i : Fin 8) : Tapes R Q F := .inr (.inl i)

/-- Caller storage is disjoint from all data and scratch tapes. -/
def framePort (j : F) : Tapes R Q F := .inr (.inr j)

/-- Canonical statement boundary, with materialized data and empty reusable scratch. -/
def tapes (st : State R Q) (frame : F → List Sym) : Tapes R Q F → List Sym
  | .inl d => stateTapes st d
  | .inr (.inl _) => []
  | .inr (.inr j) => frame j

@[simp] theorem tapes_reg (st : State R Q) (frame : F → List Sym) (x : Fin R) :
    tapes st frame (reg x) = natTape (st.regs x) := rfl

@[simp] theorem tapes_list (st : State R Q) (frame : F → List Sym) (L : Fin Q) :
    tapes st frame (list L) = encodeNats (st.lists L) := rfl

@[simp] theorem tapes_work (st : State R Q) (frame : F → List Sym) (i : Fin 8) :
    tapes st frame (work i) = [] := rfl

@[simp] theorem tapes_frame (st : State R Q) (frame : F → List Sym) (j : F) :
    tapes st frame (framePort j) = frame j := rfl

variable [DecidableEq F]

/-- The language's register update is exactly one physical tape replacement. -/
theorem tapes_setReg (st : State R Q) (frame : F → List Sym) (x : Fin R) (n : ℕ) :
    tapes (setReg st x n) frame = Function.update (tapes st frame) (reg x) (natTape n) := by
  funext k
  rcases k with (y | L) | (i | j)
  · by_cases h : y = x
    · subst y; simp [tapes, stateTapes, setReg, reg]
    · simp [tapes, stateTapes, setReg, reg, Function.update, h]
  · simp [tapes, stateTapes, setReg, reg]
  · simp [tapes, reg]
  · simp [tapes, reg]

/-- The language's list update is exactly one physical tape replacement. -/
theorem tapes_setList (st : State R Q) (frame : F → List Sym) (L : Fin Q) (xs : List ℕ) :
    tapes (setList st L xs) frame =
      Function.update (tapes st frame) (list L) (encodeNats xs) := by
  funext k
  rcases k with (x | M) | (i | j)
  · simp [tapes, stateTapes, setList, list]
  · by_cases h : M = L
    · subst M; simp [tapes, stateTapes, setList, list]
    · simp [tapes, stateTapes, setList, list, Function.update, h]
  · simp [tapes, list]
  · simp [tapes, list]

end PCP.Lang.MachineLayout
