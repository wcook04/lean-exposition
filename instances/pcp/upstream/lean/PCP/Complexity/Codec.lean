import PCP.Complexity.Encoding
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

/-!
# The codecs are primitive recursive

`PCP/Complexity/Encoding.lean` proves the encodings *faithful*: every decoder is a left inverse, so
distinct arguments reach the machine as distinct tapes. That is a semantic statement and its header
says so explicitly. It is not enough for the bridge.

One way this can go wrong: under encoders that send everything to the empty tape, a machine
that halts immediately computes *every* function, noncomputable ones included. That example is
about **lossy** encodings, and injectivity does rule it out — with an injective output encoder a
fixed immediately-halting machine's output determines at most one result per input, so it cannot
realise every function.

The claim to make is the weaker and more careful one: injectivity is not *sufficient*. A faithful
encoding can still be one whose encoding or decoding is itself uncomputable, and then a machine
certificate says nothing about computability of the function it is supposed to compute. So both
halves are needed, and both are now available: `Encoding.lean` supplies faithfulness, and this
module supplies effectiveness — `Primrec` for the input encoders and the output decoders, hence
`Computable`.

## Direction, and what is deliberately left out

The bridge runs *from* a machine certificate *to* `Computable f`. Composing

```text
a ↦ ea a ↦ encoded tape ↦ bounded evaluation ↦ output stack ↦ decode
```

needs the **input encoders** (`ofBits`, `encodePair`, `encodeTriple`) and the **output decoders**
(`decodeBool`, `decodeAnswer`, and `stripBits` beneath them) to be effective. It does not need
`decodePair`, `decodeTriple`, or computability of `Nat.bits`: after the simulation the result is
already identified by the existing semantic round trips, so no encoder is ever evaluated on an
unknown answer. Those are therefore off the critical path and are not proved here.

## Totality

Every decoder is total and has a fixed value on malformed tapes — `decodeBool` reads a separator or
an empty tape as `false`, `decodeAnswer` reads an empty tape as `Sum.inl false`. Totality is a Lean
convenience; correctness is only ever claimed on the image of an encoder, and the examples at the
end pin down both.
-/

namespace PCP.Machine

open Primrec

/-! ## `Sym` is primitively codable

Through `Option Bool` rather than `Fin 3`: the two constructors then *are* the two cases of
`Option`, so `Sym.bit` and the head decoders come out of the existing `Option` and `Bool` API
instead of a numeral-matching argument. -/

/-- `bit b ↦ some b`, `sep ↦ none`. -/
def symEquiv : Sym ≃ Option Bool where
  toFun := fun c => match c with | .bit b => some b | .sep => none
  invFun := fun o => match o with | some b => .bit b | none => .sep
  left_inv := by rintro (b | _) <;> rfl
  right_inv := by rintro (_ | b) <;> rfl

instance : Primcodable Sym := Primcodable.ofEquiv _ symEquiv

/-! ## Encoders

`Sym` is finite, so any function *out* of it is primitive recursive (`Primrec.dom_finite`); the
work is entirely in the list plumbing. -/

theorem primrec_bit : Primrec Sym.bit := Primrec.dom_bool _

theorem primrec_ofBits : Primrec ofBits :=
  (Primrec.list_map Primrec.id (primrec_bit.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_encodeBool : Primrec encodeBool := Primrec.dom_bool _

theorem primrec_encodePair : Primrec encodePair :=
  Primrec.list_append.comp (primrec_ofBits.comp Primrec.fst)
    (Primrec.list_cons.comp (Primrec.const Sym.sep) (primrec_ofBits.comp Primrec.snd))

/-- `++` is left-associative and binds looser than `::`, so the triple encoding groups as the pair
encoding followed by the third argument.  Stated because the `Primrec` proof has to match it. -/
theorem encodeTriple_eq (t : List Bool × List Bool × List Bool) :
    encodeTriple t = (ofBits t.1 ++ Sym.sep :: ofBits t.2.1) ++ (Sym.sep :: ofBits t.2.2) := rfl

theorem primrec_encodeTriple : Primrec encodeTriple :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (primrec_ofBits.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.const Sym.sep)
        (primrec_ofBits.comp (Primrec.fst.comp Primrec.snd))))
    (Primrec.list_cons.comp (Primrec.const Sym.sep)
      (primrec_ofBits.comp (Primrec.snd.comp Primrec.snd)))

/-! ## `stripBits`

Recast as a `flatMap` of a finite-domain function: one symbol contributes its bit, a separator
contributes nothing. -/

/-- A symbol's contribution to `stripBits`. -/
def symToBits : Sym → List Bool
  | .bit b => [b]
  | .sep => []

theorem stripBits_eq_flatMap (s : List Sym) : stripBits s = List.flatMap symToBits s := by
  induction s with
  | nil => rfl
  | cons c s ih => cases c <;> simp [stripBits, symToBits, ih]

theorem primrec_stripBits : Primrec stripBits :=
  (Primrec.list_flatMap Primrec.id ((Primrec.dom_finite symToBits).comp Primrec.snd).to₂).of_eq
    fun s => (stripBits_eq_flatMap s).symm

/-! ## Output decoders

Both decoders look at the head symbol and, in one case, at a number folded out of the tail.  The
head is an `Option Sym` — a **finite** type — so the primitive recursiveness of the case analysis
follows directly from `dom_finite`, and only the arithmetic needs an argument.  `dom_finite` is a
statement about primitive recursiveness alone; it yields no machine-time bound and no claim that
the case analysis is free. -/

/-- The Boolean reading of a head symbol.  A separator or an empty tape reads as `false`; this is
the fixed malformed-input value. -/
def headBool : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

/-- **The total Boolean output decoder.** -/
def decodeBool (s : List Sym) : Bool := headBool s.head?

@[simp] theorem decodeBool_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl

@[simp] theorem decodeBool_nil : decodeBool [] = false := rfl

@[simp] theorem decodeBool_sep (s : List Sym) : decodeBool (.sep :: s) = false := rfl

theorem primrec_decodeBool : Primrec decodeBool :=
  (Primrec.dom_finite headBool).comp Primrec.list_head?

/-- `Nat.bit b n` is `2 * n` with `b` appended as the new low bit. -/
theorem primrec_natBit : Primrec₂ Nat.bit :=
  have h2 : Primrec (fun p : Bool × ℕ => 2 * p.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  (Primrec.cond Primrec.fst (Primrec.succ.comp h2) h2).of_eq fun p => by
    cases p with | mk b n => cases b <;> simp [Nat.bit]

/-- The address folded out of a tape's tail: least-significant bit first, as `Nat.bits` produces
it. -/
def tailAddress (s : List Sym) : ℕ := (stripBits s.tail).foldr Nat.bit 0

theorem primrec_tailAddress : Primrec tailAddress :=
  Primrec.list_foldr (primrec_stripBits.comp Primrec.list_tail) (Primrec.const 0)
    (primrec_natBit.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

/-- `decodeAnswer` splits on whether the head is the separator. -/
theorem decodeAnswer_eq (s : List Sym) :
    decodeAnswer s =
      cond (s.head? == some Sym.sep) (Sum.inr (tailAddress s)) (Sum.inl (headBool s.head?)) := by
  cases s with
  | nil => rfl
  | cons c s => cases c <;> rfl

theorem primrec_decodeAnswer : Primrec decodeAnswer :=
  (Primrec.cond
      ((Primrec.dom_finite (fun c : Option Sym => c == some Sym.sep)).comp Primrec.list_head?)
      (Primrec.sumInr.comp primrec_tailAddress)
      (Primrec.sumInl.comp primrec_decodeBool)).of_eq fun s => (decodeAnswer_eq s).symm

/-! ## The `Computable` forms

These are the shapes the bridge consumes; `Primrec.to_comp` is the only step. -/

theorem computable_ofBits : Computable ofBits := primrec_ofBits.to_comp

theorem computable_encodePair : Computable encodePair := primrec_encodePair.to_comp

theorem computable_encodeTriple : Computable encodeTriple := primrec_encodeTriple.to_comp

theorem computable_encodeBool : Computable encodeBool := primrec_encodeBool.to_comp

theorem computable_stripBits : Computable stripBits := primrec_stripBits.to_comp

theorem computable_decodeBool : Computable decodeBool := primrec_decodeBool.to_comp

theorem computable_decodeAnswer : Computable decodeAnswer := primrec_decodeAnswer.to_comp

/-! ## Acceptance

Both Boolean outcomes, both answer constructors, address zero through the bare separator, and the
fixed behaviour on malformed tapes. -/

example : decodeBool (encodeBool true) = true := rfl
example : decodeBool (encodeBool false) = false := rfl

example (b : Bool) : decodeAnswer (encodeAnswer (.inl b)) = .inl b := decodeAnswer_encodeAnswer _
example (a : ℕ) : decodeAnswer (encodeAnswer (.inr a)) = .inr a := decodeAnswer_encodeAnswer _

/-- Address `0` is the bare separator, and it decodes back to `0` — the case a decoder that read
"no bits" as "no address" would get wrong. -/
example : decodeAnswer [Sym.sep] = .inr 0 := rfl

example : decodeAnswer (encodeAnswer (.inr 0)) = .inr 0 := by
  rw [encodeAnswer_inr_zero]; rfl

/-- A nonzero address, to check the fold's bit order is the one `Nat.bits` produces. -/
example : encodeAnswer (.inr 6) = [Sym.sep, Sym.bit false, Sym.bit true, Sym.bit true] := by
  decide +kernel

example : decodeAnswer [Sym.sep, Sym.bit false, Sym.bit true, Sym.bit true] = .inr 6 := by
  decide +kernel

example : decodeBool [] = false := rfl
example : decodeBool [Sym.sep] = false := rfl
example : decodeAnswer [] = .inl false := rfl

end PCP.Machine
