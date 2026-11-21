import PCP.Verifier.Definition
import PCP.Complexity.CostModel
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits

/-!
# Concrete polynomial-time semantics

The relation and verifier predicates use mathlib's finite multi-stack Turing
machine model, with a polynomial step bound in the encoded input length.
The encodings explicitly represent bit strings, argument separators and binary
proof addresses. `PCP.Complexity.StandardModel` supplies the concrete cost model.
-/

namespace PCP.Machine

/-- The tape alphabet: a bit, or a separator between arguments.

A separator is needed because the machine takes one input list, while our relations and algorithms
take two or three bit strings. Self-delimiting encodings would avoid it at the cost of a length
prefix; a separator symbol is the simpler convention and is fixed here once. -/
inductive Sym
  | bit (b : Bool)
  | sep
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- A bit string as tape symbols. -/
def ofBits (x : List Bool) : List Sym := x.map .bit

@[simp] theorem length_ofBits (x : List Bool) : (ofBits x).length = x.length := by
  simp [ofBits]

/-- Encoding of an argument pair: `x`, separator, `w`. -/
def encodePair (p : List Bool × List Bool) : List Sym :=
  ofBits p.1 ++ .sep :: ofBits p.2

/-- Encoding of an argument triple: input, random string, answers so far. -/
def encodeTriple (t : List Bool × List Bool × List Bool) : List Sym :=
  ofBits t.1 ++ .sep :: ofBits t.2.1 ++ .sep :: ofBits t.2.2

/-- Encoding of a verifier algorithm's answer.  A halt decision is one bit; a query is the
separator followed by the address in binary. -/
def encodeAnswer : Bool ⊕ ℕ → List Sym
  | .inl b => [.bit b]
  | .inr a => .sep :: ofBits (Nat.bits a)

/-- Encoding of a Boolean result. -/
def encodeBool (b : Bool) : List Sym := [.bit b]

@[simp] theorem length_encodePair (p : List Bool × List Bool) :
    (encodePair p).length = p.1.length + p.2.length + 1 := by
  simp [encodePair, ofBits]; omega

@[simp] theorem length_encodeTriple (t : List Bool × List Bool × List Bool) :
    (encodeTriple t).length = t.1.length + t.2.1.length + t.2.2.length + 2 := by
  simp [encodeTriple, ofBits]; omega

/-! ## The two polynomial-time predicates

These are the definitions the forward target is stated about. Note what they are *not*: they are
not fields of a structure, not parameters, and not constrained by axioms. They are properties of a
concrete machine, so no instantiation can make them degenerate. -/

/-- A binary relation on bit strings is polynomial-time when some `FinTM2` machine computes it
within a polynomial number of steps in the encoded input length. -/
def PolyTimeRel (R : List Bool → List Bool → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodePair encodeBool (fun p => R p.1 p.2))

/-- A verifier algorithm is polynomial-time when some `FinTM2` machine computes its step function
within a polynomial number of steps in the encoded input length. -/
def PolyTimeAlg (alg : VerifierAlg) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeTriple encodeAnswer
    (fun t => alg t.1 t.2.1 t.2.2))

/-! ### Obligation NP-1 — discharged downstream

`exists_standardCostModel`, the statement that the concrete model satisfies the `CostModel`
interface with *these* two predicates, is proved in `PCP/Complexity/StandardModel.lean`, under the
same full name `PCP.Machine.exists_standardCostModel` and with the same type:

```text
∃ M : CostModel, M.PolyTimeRel = PolyTimeRel ∧ M.PolyTimeAlg = PolyTimeAlg
```

It cannot live here.  Its closure field is the finite-witness checker machine, whose construction
imports this file, and its coherence fields are the bridge of `Bridge.lean`, which imports this file
too; stating and proving it here would be an import cycle.  The equalities are still what give the
statement content: an arbitrary model cannot satisfy it, because both predicates are pinned to the
machine definitions above. -/

/-! ## The computability bridge, stated for *these* encodings

`CostModel` needs exactly two implications. They are stated for the concrete encodings above, not
for encodings in general, and that restriction is essential rather than convenient:
Under encoders which send everything to the empty tape, a machine that halts immediately would
compute *every* function, noncomputable ones included.  That example is about *lossy* encodings
and injectivity does exclude it, but injectivity is still not sufficient — a faithful encoding
may have uncomputable encoding or decoding maps. So the bridge needs both halves, and the effective
one is what `PCP/Complexity/Codec.lean` supplies.

A theorem generic over encodings is possible with explicit effective-encoding hypotheses;
`PCP.Machine.computable_of_polyTime` is that theorem for external alphabet `Sym`.

Discharging these did not require the full unbounded `TM2Computable → Computable` development. The
route actually taken was a *bounded* simulation of a polynomial-time witness — iterate the
transition for the certified bound and decode — built in five blocks:

* `PCP/Complexity/BoundedEval.lean` — iterating for the polynomial budget retains a configuration
  reached before it, so a simulator that knows only the input length still sees the answer.
* `PCP/Complexity/Codec.lean` — the input encoders and output decoders above are `Primrec`, hence
  `Computable`. This is the half that the empty-tape example shows is indispensable.
* `PCP/Complexity/SymbolCode.lean` and `CodeCfg.lean` — a uniform numerical representation of
  symbols, stacks and configurations, with the dependent update transported.
* `PCP/Complexity/CodeStep.lean` — a primitive-recursive evaluator with a transition square.
* `PCP/Complexity/Simulate.lean` and `Bridge.lean` — the assembly, and the two theorems.

**The two coherence theorems now live downstream**, in `PCP/Complexity/Bridge.lean`, under the same
names `PCP.Machine.polyTimeRel_computable` and `PCP.Machine.polyTimeAlg_computable` and with the
same types. They could not stay here: their proofs need `PCP/Complexity/Codec.lean`, which imports
this file, so stating *and* proving them here would be an import cycle.

The quantitative closure field, and with it `exists_standardCostModel`, is discharged in
`PCP/Complexity/StandardModel.lean`.  The comparison with the reference definition of NP is in
`PCP/Complexity/ReferenceNPConverse.lean`. -/

end PCP.Machine
