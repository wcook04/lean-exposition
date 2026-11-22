import PCP.Complexity.Codec

/-!
# Fixed enumerations, range-checked symbol codes, and the nested head reader

## Why this layer exists

The interpreter that discharges NP-1b/NP-1c (`Bridge.lean`) runs on a uniform numerical
representation rather than on `tm.Cfg`, whose stacks are a *dependent* family
`∀ k, List (tm.Γ k)` over an arbitrary type. That is a route choice, not an impossibility
claim: a coding API for dependent configuration types could be developed instead, and is simply
not the shorter path here. The source semantics is reached
through explicit comparison maps. This module fixes the representation of a single **symbol** and of
a single **stack head**, which is where the error policy has to be decided.

## The three-case head reader

This module adopts a three-outcome error policy for reading the head of a coded stack. Other
computable conventions on malformed codes can also support a correct simulation, since correctness
is only ever claimed on the encoding image; keeping the three outcomes apart is what *this* policy
requires:

| `readHead` | Meaning | Interpreter action |
|---|---|---|
| `some none` | the stack is empty | run the source `peek`/`pop` callback on its legitimate `none` |
| `some (some n)` | a valid coded head | run the callback on the decoded symbol |
| `none` | the head code is out of range | interpreter error — outer `none` from the coded step |

Flattening the two layers with a `bind` would identify a malformed code with an empty stack, which
this policy forbids. So the reader's type is `Option (Option ℕ)` and stays that way. On a stack
whose alphabet is *empty* the
empty list still reads as `some none`, while any nonempty numerical stack has an invalid head.

Outer `none` from a coded step will therefore mean either a terminal label or an accessed malformed
code. That is sound because the simulation theorem is about **encoded source configurations**, where
`readHead_codeStack` below shows malformed codes cannot arise. That lemma is about *reading* an
encoded stack; that running the evaluator keeps a configuration encoded is a separate fact, and it
is the transition square `MachineCode.codeStep_encodeCfg` in `PCP/Complexity/CodeStep.lean` that
supplies it. No claim is made that an arbitrary numerical configuration represents a machine
execution.

## Ordinals are internal

`C.symbolCode` is a symbol's ordinal in *this machine's* chosen enumeration of *its own* stack's
alphabet. It is not `Encodable.encode`, and in particular it is unrelated to the `Sym ≃ Option Bool`
coding that `PCP/Complexity/Codec.lean` installs for the external alphabet. The two representations
meet only at the boundary maps in the last section, which are stated explicitly rather than being
arranged to coincide. Nothing here changes an external coding instance.

`MachineCode` carries equivalences obtained from classical finiteness, so `MachineCode.of` is
`noncomputable`. That is fine: the record is a *semantic comparison device*. Everything the
interpreter runs on is numerical, and the `Primrec` results below are about those numerical
functions.
-/

namespace PCP.Machine

open Turing

variable {tm : FinTM2}

/-! ## The fixed enumerations -/

/-- A frozen choice of enumerations for one machine: its stack indices, labels, internal states,
and each stack's alphabet.

Sizes are indexed by the **source** stack index `k`, so the equivalences need no transport;
`sizeCode` below re-indexes them numerically for the interpreter. -/
structure MachineCode (tm : FinTM2) where
  /-- how many stacks -/
  stackCount : ℕ
  /-- their enumeration -/
  stackEquiv : tm.K ≃ Fin stackCount
  /-- how many labels -/
  labelCount : ℕ
  /-- their enumeration -/
  labelEquiv : tm.Λ ≃ Fin labelCount
  /-- how many internal states -/
  stateCount : ℕ
  /-- their enumeration -/
  stateEquiv : tm.σ ≃ Fin stateCount
  /-- the size of each stack's alphabet, at the source index -/
  size : tm.K → ℕ
  /-- and its enumeration -/
  alphabetEquiv : ∀ k, tm.Γ k ≃ Fin (size k)

/-- Every machine whose alphabets are all finite has such a record.  Classical, hence
`noncomputable`; see the module header. -/
noncomputable def MachineCode.of (tm : FinTM2) (hΓ : ∀ k, Finite (tm.Γ k)) : MachineCode tm :=
  haveI : Fintype tm.K := tm.kFin
  haveI : Fintype tm.Λ := tm.ΛFin
  haveI : Fintype tm.σ := tm.σFin
  { stackCount := Nat.card tm.K
    stackEquiv := Finite.equivFin tm.K
    labelCount := Nat.card tm.Λ
    labelEquiv := Finite.equivFin tm.Λ
    stateCount := Nat.card tm.σ
    stateEquiv := Finite.equivFin tm.σ
    size := fun k => @Nat.card (tm.Γ k)
    alphabetEquiv := fun k => @Finite.equivFin (tm.Γ k) (hΓ k) }

namespace MachineCode

variable (C : MachineCode tm)

/-- The alphabet sizes re-indexed numerically: this is the table the interpreter consults. -/
def sizeCode (j : Fin C.stackCount) : ℕ := C.size (C.stackEquiv.symm j)

@[simp] theorem sizeCode_stackEquiv (k : tm.K) : C.sizeCode (C.stackEquiv k) = C.size k := by
  rw [sizeCode, Equiv.symm_apply_apply]

/-! ## Symbol codes -/

/-- A symbol's ordinal in its own stack's enumeration. -/
def symbolCode {k : tm.K} (c : tm.Γ k) : ℕ := (C.alphabetEquiv k c : ℕ)

theorem symbolCode_lt {k : tm.K} (c : tm.Γ k) : C.symbolCode c < C.size k :=
  (C.alphabetEquiv k c).isLt

/-- **Range-checked** symbol decoding.  Out-of-range codes are rejected rather than clamped: a
default symbol would not exist on a stack with an empty alphabet, and inventing one would let a
malformed code masquerade as a legitimate observation. -/
def decodeSymbol (k : tm.K) (n : ℕ) : Option (tm.Γ k) :=
  if h : n < C.size k then some ((C.alphabetEquiv k).symm ⟨n, h⟩) else none

@[simp] theorem decodeSymbol_symbolCode {k : tm.K} (c : tm.Γ k) :
    C.decodeSymbol k (C.symbolCode c) = some c := by
  rw [decodeSymbol, dite_eq_left (C.symbolCode_lt c)]
  exact congrArg some (by simp [symbolCode, (C.alphabetEquiv k).symm_apply_apply c])

/-- A code at or past the alphabet size is rejected.  In particular the code *equal* to the size —
the off-by-one a `≤` test would accept. -/
@[simp] theorem decodeSymbol_of_le {k : tm.K} {n : ℕ} (h : C.size k ≤ n) :
    C.decodeSymbol k n = none := dite_eq_right (Nat.not_lt.2 h)

theorem decodeSymbol_isSome_iff {k : tm.K} {n : ℕ} :
    (C.decodeSymbol k n).isSome ↔ n < C.size k := by
  by_cases h : n < C.size k
  · simp [decodeSymbol, h]
  · simp [decodeSymbol, h]

theorem decodeSymbol_eq_some_iff {k : tm.K} {n : ℕ} {c : tm.Γ k} :
    C.decodeSymbol k n = some c ↔ n = C.symbolCode c := by
  constructor
  · intro h
    by_cases hn : n < C.size k
    · rw [decodeSymbol, dite_eq_left hn] at h
      have := congrArg (C.alphabetEquiv k) (Option.some_inj.1 h)
      rw [Equiv.apply_symm_apply] at this
      exact congrArg Fin.val this
    · rw [decodeSymbol, dite_eq_right hn] at h; exact absurd h (by simp)
  · rintro rfl; exact C.decodeSymbol_symbolCode c

theorem symbolCode_injective {k : tm.K} : Function.Injective (C.symbolCode (k := k)) := by
  intro a b h
  have := C.decodeSymbol_symbolCode a
  rw [h, C.decodeSymbol_symbolCode b] at this
  exact (Option.some_inj.1 this).symm

/-! ## Coded stacks and the nested head reader -/

/-- A source stack as a list of ordinals. -/
def codeStack (k : tm.K) (s : List (tm.Γ k)) : List ℕ := s.map C.symbolCode

@[simp] theorem codeStack_nil (k : tm.K) : C.codeStack k [] = [] := rfl

@[simp] theorem codeStack_cons (k : tm.K) (c : tm.Γ k) (s : List (tm.Γ k)) :
    C.codeStack k (c :: s) = C.symbolCode c :: C.codeStack k s := rfl

@[simp] theorem length_codeStack (k : tm.K) (s : List (tm.Γ k)) :
    (C.codeStack k s).length = s.length := List.length_map ..

theorem codeStack_injective (k : tm.K) : Function.Injective (C.codeStack k) :=
  List.map_injective_iff.2 C.symbolCode_injective

/-- **The three-case head reader**, on a purely numerical stack.  See the table in the module
header: the two `Option` layers are the empty/nonempty distinction and the valid/invalid
distinction, and they are kept apart deliberately. -/
def readHead (j : Fin C.stackCount) : List ℕ → Option (Option ℕ)
  | [] => some none
  | n :: _ => if n < C.sizeCode j then some (some n) else none

@[simp] theorem readHead_nil (j : Fin C.stackCount) : C.readHead j [] = some none := rfl

theorem readHead_cons (j : Fin C.stackCount) (n : ℕ) (s : List ℕ) :
    C.readHead j (n :: s) = if n < C.sizeCode j then some (some n) else none := rfl

@[simp] theorem readHead_cons_of_lt {j : Fin C.stackCount} {n : ℕ} (h : n < C.sizeCode j)
    (s : List ℕ) : C.readHead j (n :: s) = some (some n) := ite_eq_left h

/-- An out-of-range head is an **error**, not an empty stack. -/
@[simp] theorem readHead_cons_of_le {j : Fin C.stackCount} {n : ℕ} (h : C.sizeCode j ≤ n)
    (s : List ℕ) : C.readHead j (n :: s) = none := ite_eq_right (Nat.not_lt.2 h)

/-- The two are genuinely different values, which is the whole point of the nesting. -/
theorem readHead_nil_ne_error (j : Fin C.stackCount) : C.readHead j [] ≠ none := by simp

/-- On a stack with an **empty** alphabet, every nonempty numerical stack is malformed — while the
empty stack still reads as an empty stack. -/
theorem readHead_of_size_zero {j : Fin C.stackCount} (h : C.sizeCode j = 0) (n : ℕ) (s : List ℕ) :
    C.readHead j (n :: s) = none := C.readHead_cons_of_le (h ▸ Nat.zero_le n) s

/-- **Encoded source stacks never produce the error.**  This is what confines the malformed-code
branch to configurations that are not images of `codeStack`. -/
@[simp] theorem readHead_codeStack (k : tm.K) (s : List (tm.Γ k)) :
    C.readHead (C.stackEquiv k) (C.codeStack k s) = some (s.head?.map C.symbolCode) := by
  cases s with
  | nil => rfl
  | cons c s =>
      rw [codeStack_cons, C.readHead_cons_of_lt (by simpa using C.symbolCode_lt c)]
      rfl

/-- And decoding the head recovers the source head, empty stack included. -/
theorem decode_readHead_codeStack (k : tm.K) (s : List (tm.Γ k)) :
    (C.readHead (C.stackEquiv k) (C.codeStack k s)).map (fun o => o.bind (C.decodeSymbol k))
      = some s.head? := by
  cases s with
  | nil => rfl
  | cons c s => rw [C.readHead_codeStack]; simp

/-! ## The reader is primitive recursive

The alphabet-size table has finite domain, so `dom_finite` supplies it; everything else is the
head of a list and a comparison. -/

theorem primrec_sizeCode : Primrec C.sizeCode := Primrec.dom_finite _

theorem primrec_readHead : Primrec₂ C.readHead := by
  have hsize : Primrec fun q : (Fin C.stackCount × List ℕ) × ℕ => C.sizeCode q.1.1 :=
    C.primrec_sizeCode.comp (Primrec.fst.comp Primrec.fst)
  have hbody : Primrec₂ fun (p : Fin C.stackCount × List ℕ) (n : ℕ) =>
      (if n < C.sizeCode p.1 then some (some n) else none : Option (Option ℕ)) :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.snd hsize)
      (Primrec.option_some.comp (Primrec.option_some.comp Primrec.snd))
      (Primrec.const (none : Option (Option ℕ)))
  exact (Primrec.option_casesOn (Primrec.list_head?.comp Primrec.snd)
      (Primrec.const (some (none : Option ℕ))) hbody).of_eq
    (by rintro ⟨j, s⟩; cases s <;> rfl)

/-! ## The boundary with the external `Sym` coding

Internal ordinals are *not* `Encodable.encode`, and these maps are where the two representations
meet.  They are stated for arbitrary alphabet equivalences, so they apply to any witness over `Sym`
— in particular to a recoded one, whose equivalences `PCP/Complexity/Recode.lean` supplies. -/

section Boundary

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)

/-- External symbol to internal ordinal at the input stack.  Finite domain. -/
def inputCode (c : Sym) : ℕ := C.symbolCode (eIn.symm c)

theorem primrec_inputCode : Primrec (C.inputCode eIn) := Primrec.dom_finite _

theorem inputCode_lt (c : Sym) : C.inputCode eIn c < C.size tm.k₀ := C.symbolCode_lt _

@[simp] theorem decodeSymbol_inputCode (c : Sym) :
    C.decodeSymbol tm.k₀ (C.inputCode eIn c) = some (eIn.symm c) := C.decodeSymbol_symbolCode _

/-- The output alphabet listed in ordinal order; the decoder is a lookup in it, which makes its
primitive recursiveness immediate and its range check automatic. -/
def outputTable : List Sym :=
  (List.finRange (C.size tm.k₁)).map fun i => eOut ((C.alphabetEquiv tm.k₁).symm i)

@[simp] theorem length_outputTable : (C.outputTable eOut).length = C.size tm.k₁ := by
  simp [outputTable]

/-- Internal ordinal to external symbol at the output stack, range-checked. -/
def outputDecode (n : ℕ) : Option Sym := (C.outputTable eOut)[n]?

theorem primrec_outputDecode : Primrec (C.outputDecode eOut) := Primrec.list_getElem?₁ _

theorem outputDecode_eq (n : ℕ) :
    C.outputDecode eOut n = (C.decodeSymbol tm.k₁ n).map eOut := by
  by_cases h : n < C.size tm.k₁
  · rw [outputDecode, List.getElem?_eq_getElem (by simpa using h), decodeSymbol, dite_eq_left h]
    simp [outputTable]
  · rw [outputDecode, List.getElem?_eq_none (by simpa using Nat.not_lt.1 h),
      C.decodeSymbol_of_le (Nat.not_lt.1 h), Option.map_none]

@[simp] theorem outputDecode_symbolCode (c : tm.Γ tm.k₁) :
    C.outputDecode eOut (C.symbolCode c) = some (eOut c) := by
  rw [outputDecode_eq, C.decodeSymbol_symbolCode, Option.map_some]

/-- A code at or past the alphabet size decodes to nothing. -/
@[simp] theorem outputDecode_of_le {n : ℕ} (h : C.size tm.k₁ ≤ n) :
    C.outputDecode eOut n = none := by
  rw [outputDecode_eq, C.decodeSymbol_of_le h, Option.map_none]

end Boundary

end MachineCode

end PCP.Machine
