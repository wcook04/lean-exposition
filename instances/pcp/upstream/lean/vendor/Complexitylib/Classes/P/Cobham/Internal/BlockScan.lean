/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Cobham.Internal.Vec

/-!
# What the block scanners compute — proof internals

The two total parsers of a self-delimiting block — `pairFst` decodes the
leading block's payload, `pairSnd` returns the suffix after it (both defined in
`Complexitylib.Encoding.Pairing`) — and the control states their scanners
share. `Complexity.pairSplitCoreTM` handles only valid pair inputs, so the total
decoders need machines of their own; those are `Internal.SndBlock`,
`Internal.FstBlock` and `Internal.Cat`, one per machine.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- Stripping the head component of an encoded vector yields the encoded tail.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`pairFst_pair`.) -/
theorem fstBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    pairFst (encodeVec v) = encodeVec (Fin.tail v) := by
  simp

/-- The suffix of an encoded vector is its head component.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`pairSnd_pair`.) -/
theorem sndBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    pairSnd (encodeVec v) = v 0 := by
  simp

/-- Control states of the block-decoding scanners. -/
inductive ScanPhase where
  | skip | scanA | scanBfalse | scanBtrue | emit | done
  deriving DecidableEq

instance : Fintype ScanPhase where
  elems := {.skip, .scanA, .scanBfalse, .scanBtrue, .emit, .done}
  complete := fun x => by cases x <;> simp

end Cobham

end Complexity
