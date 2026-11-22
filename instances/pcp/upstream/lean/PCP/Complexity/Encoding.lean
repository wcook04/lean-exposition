import PCP.Complexity.Machine

/-!
# Bit encodings for the concrete machine model

Encodings and length bounds used by witness checkers and verifier algorithms.
-/

namespace PCP.Machine

/-! ## Decoders -/

/-- Drop separators and read the remaining symbols as bits. -/
def stripBits : List Sym → List Bool
  | [] => []
  | .bit b :: xs => b :: stripBits xs
  | .sep :: xs => stripBits xs

@[simp] theorem stripBits_ofBits (x : List Bool) : stripBits (ofBits x) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [ofBits, stripBits] using ih

/-- Split at the first separator: the bits before it, and everything after. -/
def splitFirst : List Sym → List Bool × List Sym
  | [] => ([], [])
  | .sep :: xs => ([], xs)
  | .bit b :: xs => let (x, rest) := splitFirst xs; (b :: x, rest)

@[simp] theorem splitFirst_ofBits_sep (x : List Bool) (rest : List Sym) :
    splitFirst (ofBits x ++ .sep :: rest) = (x, rest) := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa [ofBits, splitFirst] using congrArg (fun p => (b :: p.1, p.2)) ih

/-- Total decoder for an argument pair. -/
def decodePair (s : List Sym) : List Bool × List Bool :=
  let (x, rest) := splitFirst s
  (x, stripBits rest)

/-- Total decoder for an argument triple. -/
def decodeTriple (s : List Sym) : List Bool × List Bool × List Bool :=
  let (x, rest) := splitFirst s
  let (r, rest) := splitFirst rest
  (x, r, stripBits rest)

/-- Total decoder for an algorithm answer. -/
def decodeAnswer : List Sym → Bool ⊕ ℕ
  | .sep :: xs => .inr ((stripBits xs).foldr Nat.bit 0)
  | .bit b :: _ => .inl b
  | [] => .inl false

/-! ## Round trips, and hence injectivity -/

theorem decodePair_encodePair (p : List Bool × List Bool) : decodePair (encodePair p) = p := by
  simp [decodePair, encodePair]

theorem decodeTriple_encodeTriple (t : List Bool × List Bool × List Bool) :
    decodeTriple (encodeTriple t) = t := by
  simp [decodeTriple, encodeTriple, List.append_assoc]

/-- `Nat.bits` is a faithful binary representation. -/
theorem fold_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp [Nat.bits_append_bit n b h, ih]

theorem decodeAnswer_encodeAnswer (a : Bool ⊕ ℕ) : decodeAnswer (encodeAnswer a) = a := by
  cases a <;> simp [decodeAnswer, encodeAnswer, fold_bits]

theorem encodePair_injective : Function.Injective encodePair :=
  Function.LeftInverse.injective decodePair_encodePair

theorem encodeTriple_injective : Function.Injective encodeTriple :=
  Function.LeftInverse.injective decodeTriple_encodeTriple

theorem encodeAnswer_injective : Function.Injective encodeAnswer :=
  Function.LeftInverse.injective decodeAnswer_encodeAnswer

theorem encodeBool_injective : Function.Injective encodeBool := by
  intro a b h
  simpa [encodeBool] using h

/-! ## Valid encodings, and behaviour off them

The round-trip theorems are statements about the *images* of the encoders. A machine handed
arbitrary tape contents is not handed an encoded argument, and nothing above says otherwise. -/

/-- `s` is a genuine encoded argument pair. -/
def ValidPair (s : List Sym) : Prop := ∃ p, s = encodePair p

/-- `s` is a genuine encoded argument triple. -/
def ValidTriple (s : List Sym) : Prop := ∃ t, s = encodeTriple t

theorem validPair_encodePair (p : List Bool × List Bool) : ValidPair (encodePair p) := ⟨p, rfl⟩

theorem validTriple_encodeTriple (t : List Bool × List Bool × List Bool) :
    ValidTriple (encodeTriple t) := ⟨t, rfl⟩

/-- On a valid pair, decoding recovers the arguments exactly. -/
theorem decodePair_of_valid {s : List Sym} (h : ValidPair s) : encodePair (decodePair s) = s := by
  obtain ⟨p, rfl⟩ := h
  rw [decodePair_encodePair]

theorem decodeTriple_of_valid {s : List Sym} (h : ValidTriple s) :
    encodeTriple (decodeTriple s) = s := by
  obtain ⟨t, rfl⟩ := h
  rw [decodeTriple_encodeTriple]

@[simp] theorem splitFirst_ofBits (x : List Bool) : splitFirst (ofBits x) = (x, []) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [ofBits, List.map_cons] at ih ⊢
      simp [splitFirst, ih]

/-- Malformed input, made concrete: with no separator at all, `decodePair` reads the whole tape as
the first argument and returns an empty second one. This is a *definition* of the total decoder's
behaviour, not a claim that a machine can recognise the situation without cost. -/
theorem decodePair_of_no_sep (x : List Bool) : decodePair (ofBits x) = (x, []) := by
  simp [decodePair, stripBits]

/-- A tape containing only bit symbols is never a valid pair encoding: a valid encoding always
contains its separator, whatever the two arguments are. -/
theorem not_validPair_ofBits (x : List Bool) : ¬ ValidPair (ofBits x) := by
  rintro ⟨⟨y, z⟩, h⟩
  have hmem : Sym.sep ∈ ofBits x := by
    rw [h]; simp [encodePair]
  simp [ofBits] at hmem

/-- Address `0` encodes as the bare separator: `Nat.bits 0 = []`. -/
@[simp] theorem encodeAnswer_inr_zero : encodeAnswer (.inr 0) = [Sym.sep] := by
  simp [encodeAnswer, ofBits]

end PCP.Machine
