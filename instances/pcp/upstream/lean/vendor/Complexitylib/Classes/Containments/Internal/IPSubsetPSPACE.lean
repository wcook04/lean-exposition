/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive

/-!
# `IP ⊆ PSPACE` — the strategy space is finite

⚠️ Unreviewed by Bolton

A prover strategy is a function on *all* transcripts, of which there are infinitely many, so the
supremum over strategies that `IP` quantifies is a supremum over an infinite set. A machine
cannot search that. The first thing to establish is therefore that the quantifier is really
finite: a run of `prot.rounds n` rounds only ever consults the strategy on transcripts of length
below `2 · rounds n`, so two strategies agreeing there are indistinguishable.

That is what these lemmas say. Together with the message-length bound carried by
`ProverStrategy.Bounded`, they cut the search down to a finite game tree of polynomial depth,
which is the object a depth-first polynomial-space evaluation walks.

## Main results

- `Protocol.transcript_length` — a run of `n` rounds produces `2 n` messages
- `Protocol.transcript_congr` — **strategy extensionality** for the transcript
- `Protocol.accepts_congr`, `Protocol.acceptEvent_congr` — and for acceptance
-/

@[expose] public section

namespace Complexity

namespace Protocol

/-- A run of `n` rounds appends two messages per round. -/
theorem transcript_length (prot : Protocol) (S : ProverStrategy) (x r : List Bool) :
    ∀ n, (prot.transcript S x r n).length = 2 * n
  | 0 => rfl
  | n + 1 => by
      rw [transcript]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [transcript_length prot S x r n]
      omega

/-- **Strategy extensionality.** The run consults the strategy only on the transcripts it
actually produces, all of which have length below `2 n`; two strategies agreeing there yield the
same transcript. -/
theorem transcript_congr (prot : Protocol) {S S' : ProverStrategy} (x r : List Bool) :
    ∀ n, (∀ τ : Transcript, τ.length ≤ 2 * n → S τ = S' τ) →
      prot.transcript S x r n = prot.transcript S' x r n
  | 0, _ => rfl
  | n + 1, h => by
      have ih := transcript_congr prot x r n (fun τ hτ => h τ (by omega))
      rw [transcript, transcript, ih]
      have hlen : (prot.transcript S' x r n).length = 2 * n :=
        transcript_length prot S' x r n
      rw [h _ (by rw [List.length_append, hlen]; simp)]

/-- Acceptance depends on the strategy only through its values on the transcripts the run
produces. -/
theorem accepts_congr (prot : Protocol) {S S' : ProverStrategy} (x r : List Bool)
    (h : ∀ τ : Transcript, τ.length ≤ 2 * prot.rounds x.length → S τ = S' τ) :
    prot.Accepts S x r ↔ prot.Accepts S' x r := by
  rw [Accepts, Accepts, transcript_congr prot x r (prot.rounds x.length) h]

/-- The accepting coin set — and hence the acceptance probability — depends on the strategy only
through those values. -/
theorem acceptEvent_congr (prot : Protocol) {S S' : ProverStrategy} (x : List Bool)
    (h : ∀ τ : Transcript, τ.length ≤ 2 * prot.rounds x.length → S τ = S' τ) :
    prot.acceptEvent S x = prot.acceptEvent S' x := by
  classical
  refine Finset.filter_congr fun r _ => ?_
  simpa using accepts_congr prot x (BitString.toList r) h

end Protocol

end Complexity
