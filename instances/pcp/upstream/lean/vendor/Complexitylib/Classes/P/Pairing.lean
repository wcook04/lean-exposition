/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Encoding.Pairing
import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Preimage

/-!
# Polynomial-time pairing and unpairing

The pairing codec `pair` of `Complexitylib.Encoding.Pairing` is the library's
canonical way to hand a machine two strings at once. This file records that the
codec is polynomial-time in both directions: pairing two polynomial-time values
is polynomial-time, and so are the projections `pairFst` / `pairSnd`, whose
scanners are the block machines of Cobham's algebra.

## Main results

- `pairFst_mem_FP`, `pairSnd_mem_FP` — the projections are polynomial-time
- `mem_FP_pair` — pairing two polynomial-time functions is polynomial-time
- `mem_FP_pair_right` — pairing a polynomial-time value with the input itself
- `mem_P_preimage_pairFst`, `mem_P_preimage_pairSnd` — deciding a language of
  one component of a pair is polynomial-time
-/

@[expose] public section

namespace Complexity

/-! ## Polynomial-time facts -/

/-- **The first projection is polynomial-time.** -/
theorem pairFst_mem_FP : pairFst ∈ FP := Cobham.fstBlock_mem_FP

/-- **The second projection is polynomial-time.** -/
theorem pairSnd_mem_FP : pairSnd ∈ FP := Cobham.sndBlock_mem_FP

/-- **Pairing is polynomial-time**: two polynomial-time functions can be
evaluated on a common input and paired in polynomial time. -/
theorem mem_FP_pair {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => pair (a z) (b z)) ∈ FP :=
  Cobham.pairFn_mem_FP ha hb

/-- Pairing the input on the right of a polynomial-time value is polynomial-time.
This is `mem_FP_pairWithInput`; the mirror image is `mem_FP_pair id_mem_FP hf`. -/
theorem mem_FP_pair_right {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun x => pair (f x) x) ∈ FP :=
  mem_FP_pairWithInput hf

/-- A language of the first component of a pair is polynomial-time decidable. -/
theorem mem_P_preimage_pairFst {L : Language} (hL : L ∈ P) : pairFst ⁻¹' L ∈ P :=
  mem_P_preimage pairFst_mem_FP hL

/-- A language of the second component of a pair is polynomial-time decidable. -/
theorem mem_P_preimage_pairSnd {L : Language} (hL : L ∈ P) : pairSnd ⁻¹' L ∈ P :=
  mem_P_preimage pairSnd_mem_FP hL

end Complexity
