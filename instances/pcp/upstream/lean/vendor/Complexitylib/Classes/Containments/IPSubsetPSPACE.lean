/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.Containments.Internal.IPSubsetPSPACE
public import Complexitylib.Classes.Containments.Internal.IPAssemble
public import Complexitylib.Classes.P.Defs

/-!
# `IP ⊆ PSPACE`

⚠️ Unreviewed by Bolton

The easy half of `IP = PSPACE`.

The value of an interactive protocol on an input is the acceptance probability against an optimal
prover, and that value is the root of a finite game tree: the prover's moves maximize, the
verifier's coins average. Polynomial space evaluates the tree depth-first, holding one path of
messages at a time — the tree is exponentially wide but only polynomially deep, since both the
round count and the message lengths are polynomially bounded.

## How the proof runs

Three steps, none of which builds a machine by hand.

**The maximum over prover strategies becomes a finite recursion.** A strategy is a function on
*all* transcripts, so the supremum `IP` quantifies is a priori a supremum over an infinite set.
`Protocol.gval` (in `Internal.IPGameTree`) *is* that maximum, written as a recursion down the
transcript tree: at a node the coins still in play are those consistent with the verifier messages
recorded above it, a round splits them by the verifier's next message
(`Protocol.consFinset_append`), and the prover picks, for each such message, the reply maximizing
the count below. `Protocol.sval_le_gval` says no bounded strategy beats it and
`Protocol.sval_optStrategy` says one attains it, so `Protocol.mem_iff_gval` turns membership into
one comparison, `2 ^ coins(|x|) < 2 · gval(x)`. That the value never exceeds the coin space
(`Protocol.gval_le_card`) is what keeps every count inside `coins(|x|) + 1` bits.

**The recursion becomes a walk.** `Protocol.gvalR_zero_enum` and `Protocol.gvalR_succ_enum` write
it as two counter loops, and `Complexity.IPM.step` (in `Internal.IPSem`) walks it on a stack: one
frame per round carrying the two message counters, a running sum and a running maximum, with a
leaf frame carrying the coin counter and its tally. `IPM.run_frame` proves every pushed frame
comes back with its subtree's value, within `IPM.runBound` steps.

**The walk becomes a machine.** `IPM.ipStep` is that walk written inside the polynomial-time
algebra, `IPM.ipStep_encSst` proves the square commutes, and
`Complexity.SpaceIter.mem_PSPACE_of_iterate` supplies the machine — the same last step Savitch's
theorem takes. The leaf test is a single scan: carrying each frame's transcript body inside the
frame makes the consistency check a per-frame condition, so it may be taken in any order, even
though `Protocol.replay` runs the rounds in the opposite order to the stack.

## Main results

- `Protocol.transcript_congr` — strategy extensionality for the transcript
- `Protocol.mem_iff_gval` — membership is a comparison of the game-tree value
- `Protocol.walk_decides` — the stack walk ends with the membership bit
- `IP_subset_PSPACE` — the containment
-/

@[expose] public section

namespace Complexity

/-- **`IP ⊆ PSPACE`**: the optimal prover's acceptance probability is the value of a
polynomially deep game tree, evaluated depth-first in polynomial space. -/
theorem IP_subset_PSPACE : IP ⊆ PSPACE := IP_subset_PSPACE_internal

/-- **What the game tree computes.** `Protocol.gval` is the number of coin strings on which the
best bounded prover convinces the verifier; membership is that count exceeding half the coin
space. -/
theorem IP_membership_is_game_value {L : Language} (hL : L ∈ IP) :
    ∃ prot : Protocol, ∀ x : List Bool, x ∈ L ↔
      2 ^ prot.coins x.length
        < 2 * prot.gval x (prot.coins x.length) (prot.msgLen x.length)
            (prot.rounds x.length) [] := by
  obtain ⟨prot, _, _, _, _, _, _, hcomp, hsound⟩ := hL
  exact ⟨prot, fun x => Protocol.mem_iff_gval prot x hcomp hsound⟩

/-- Shamir's theorem needs only the other half now. -/
theorem IP_eq_PSPACE_of_pspace_subset_ip (h : PSPACE ⊆ IP) : IP = PSPACE :=
  subset_antisymm IP_subset_PSPACE h

end Complexity
