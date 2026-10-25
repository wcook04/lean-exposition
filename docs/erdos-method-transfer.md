# Methods from eight Erdős problem corpora

These public Erdős sources are historical bootstrap examples for the existing
[authoring stages](authoring.md). The complete working method lives in this
repository's [four skills](../skills/README.md); consulting or cloning the
earlier repository is optional. The [contracts](contracts.md) own evidence and
document bindings.

The sources below belong to the eight problem corpora in
[`wcook04/plectis-erdos` at `a0878310`](https://github.com/wcook04/plectis-erdos/tree/a0878310af794d7a0f76cc11f4de3a20c795dc60).
The pinned [paper registry](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/docs/papers/corpus.json)
distinguishes active research papers, long records, the #257 exposition and
retired manuscripts. These selections concern writing methods; they are not
new verification of the cited mathematics.

## Choose a model by the decision it explains

| Problem and public source | Useful authoring decision |
| --- | --- |
| [#68 long record][long68], “Limits of the recurrences and clearing factors used here” | Separate a counterexample to incomplete recurrence conditions from failure of one denominator-clearing choice. Neither rules out every method. |
| [#243 long record][long243], “A scalar profile need not satisfy the recurrences” | Exhibit the first arithmetic incompatibility in a tempting scalar model, instead of listing the route as unsuccessful. |
| [#249 research paper][short249], abstract and “Integral relations” | Distinguish the stronger prior independence theorem from the explicit integral relations being developed; give a worked instance of the construction. |
| [#251 research paper][short251], proof of Proposition `res:sparserationalisation` | Explain both how each next correction can be chosen and why the resulting infinite construction attains its target. |
| [#257 exposition][exposition257], “Erdős's question and the theorem” | Put the terms in the hypothesis and the terms in the conclusion side by side. Convergence of the series is different from the extra condition used to prove irrationality. |
| [#269 research paper][short269], “Recovering the prime-power jumps” | State the separation estimate needed for deterministic recovery before using a finite set of tails to deduce periodicity. |
| [#1041 evidence record][evidence1041], critical-value separation passage | A checked theorem that assumes a geometric construction does not establish that construction. Identify the ordinary proof input at the point where the formal theorem uses it. |
| [#1049 evidence record][evidence1049], geometric moment determinants | Explain a formal specialization by matching definitions and hypotheses; exclude a broader nearby remark that the declaration does not support. |

Read the complete local argument around a selected passage before adapting
its explanatory choice.

## Make a long record recoverable

For a change of representation, write the defining formula, the identity it
preserves and the reason for the normalization or indexing choice. The #243
[tail-numerator derivation][tail243] obtains two coupled recurrences from a
rational tail. Reducing fractions separately would lose information used by
the argument.

For a failed route, record three things: which conditions the candidate meets,
the first condition or identity it fails, and the conclusion that remains open.
In the #243 [scalar-profile example][failure243], the proposed numerator values
include 5, 10 and 17. The exact recurrences would successively force divisibility
by 5 at a denominator, at the next denominator, and then at 17. That contradiction
explains why the scalar estimates alone do not construct an admissible orbit.
It is not a counterexample to the original problem.

These examples make steps 3 and 6 of
[graph-to-long](../skills/graph-to-long/SKILL.md) concrete.

## Shorten by preserving the decisive transition

In [#249][short249], the stronger affine independence theorem is credited to
Martin. The direct separation proof earns space because its construction also
serves the later residue-series argument. This gives
[long-to-short](../skills/long-to-short/SKILL.md) a practical selection test:
what does a retained proof contribute beyond the cited result?

The [#251 application][prime-bound251] shows how to move an auxiliary proof
without losing its job. The short paper retains the polynomial prime bound,
explains that it supplies convergence, and points to the
[long derivation][prime-bound-long251]. Convergence is then available when the
main proposition is applied.
Within the [#251 construction][construction251], overlapping remaining-choice
intervals permit each next digit; their remaining total tending to zero proves
attainment. Both steps survive the shortening.

## Teach why the hypotheses matter

The [#269 separation argument][separation269] first shows why the coarse bound
on a normalized tail is insufficient. Disjoint affine images require an upper
bound below `9/10`; spacing of powers of five supplies `13/15`. The sharper bound
allows the next jump to be recovered. The estimate's purpose precedes its proof.

For [record-to-expository](../skills/record-to-expository/SKILL.md), the #257
[changed-parameter question][changed257] and [answer][answer257] test more than
recognition of a hypothesis. Changing a modulus from 16 to 64 forces a tail
cutoff to be chosen again. A later averaging length still works, but must be
rechecked. This makes parameter dependence an observable reader task.

## Carry a review forward at its actual scope

The [editorial exchange implementation][refinement] binds edits to frozen source
bytes and requires changed statements to be declared. Its transport check leaves
mathematical review outstanding. Lean Exposition's existing graph, passage and
bundle bindings provide the place to apply this method.

For statement correspondence, the [public evidence checker][evidence-checker]
compares prose statement and Lean declaration identities before reusing an
authored relation. Together with the #1041/#1049 records, this supplies three
review questions: what is the declaration's role, what premises remain, and
was this exact statement pair reviewed?

The [#257 revision record][review257] illustrates a useful review boundary.
It corrects two observation summaries: a finite computation cannot support an
infinite threshold, and a computable sufficient horizon is not necessarily
the prescribed horizon. It records the two passages inspected and reconciles
the affected long-paper projection without claiming a full-paper review.

The [reviewed-revision guide][review-guide] separates accepting a local correction
from adopting a new general rule. Reuse a rule already covered by the existing
skills rather than adding a parallel procedure for each example.

## Worked applications in the QAOA / SK drafts

The [QAOA / SK graph](../examples/qaoa-sk/evidence-graph.json) names the
full-support target, the scalar-value target and the broader manuscript claim
separately. The authored drafts now supply examples of the transfers above:

- The [long record's curvature section](../papers/qaoa-sk/long/reasoning-record.md#curvature-and-gap-certificate)
  defines its changed variables and derives the derivative correction whose
  expectation vanishes. Its [Gaussian approximation](../papers/qaoa-sk/long/reasoning-record.md#finite-gaussian-approximation)
  explains why errors must be controlled as vectors: convergence in each
  coordinate alone would not control a sum with increasing length.
- The [short paper](../papers/qaoa-sk/short/paper.md), Sections 3–5, retains the
  strict integrated inequality and separates positive, zero, initial and
  terminal gaps. It gives named long-record destinations for the certificate,
  gap elimination, value identities, Gaussian approximation and circuit route.
  This is selection of a proof mechanism with recoverable supporting detail.
- The [exposition](../papers/qaoa-sk/expository/main.md), Sections 2 and 6, gives
  an admissible function with an interior plateau without calling it a minimizer.
  Its changed-case calculation distinguishes ordinary from strict convexity
  by preserving endpoint values while changing the sign of the missing area.
  The broader scalar and circuit arguments remain in the long record. This
  applies the same selection principle at a different reader level: retain
  what explains the chosen result, with precise routes to further results.

The full-support interface remains conditional on an admissible minimizer;
the scalar-value clauses retain their own minimizer and diffusion premises.
Neither interface establishes the whole QAOA convergence argument. In that
manuscript claim, system size tends to infinity with depth and deterministic
angles fixed, before depth increases. These applications show choices made in
draft text; they do not supply a fresh Lean replay or a reader-comprehension
result. The graph retains the actual evidence states.

The cited manuscript sources are by Will Cook and declare CC-BY-4.0; the cited
Python implementations declare Apache-2.0. Check each linked source's own notice
before reuse. These are independently written method notes with links to the
pinned primary sources.

[long68]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos68/core.tex#L3011-L3039
[long243]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos243/core.tex
[tail243]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos243/core.tex#L182-L210
[failure243]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos243/core.tex#L3358-L3366
[short249]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/249/erdos-249-binary-totient-series.tex
[short251]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/251/erdos-251-prime-gap-dyadic-series.tex
[prime-bound251]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/251/erdos-251-prime-gap-dyadic-series.tex#L396-L402
[prime-bound-long251]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/251/erdos251-prime-gap-reasoning-surface.tex#L2117-L2151
[construction251]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/251/erdos-251-prime-gap-dyadic-series.tex#L261-L279
[exposition257]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/257/erdos257-expository-sums-never-fractions.tex
[changed257]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/257/erdos257-expository-sums-never-fractions.tex#L1037-L1041
[answer257]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/257/erdos257-expository-sums-never-fractions.tex#L1108-L1114
[short269]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/269/erdos-269-three-prime-running-lcm.tex
[separation269]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/269/erdos-269-three-prime-running-lcm.tex#L179-L216
[evidence1041]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/evidence/erdos-1041-lemniscate-newton-flow.md#L244-L246
[evidence1049]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/evidence/erdos-1049-rational-base-lambert.md#L55-L97
[evidence-checker]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/paper_evidence.py#L831-L848
[refinement]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/paper_refinement.py
[review257]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/docs/papers/exposition-method/reviews/erdos257-release-polish-20261006.json
[review-guide]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/docs/papers/exposition-method/README.md
