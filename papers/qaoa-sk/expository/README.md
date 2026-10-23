# Expository paper: the SK order parameter

Read [Why the SK order parameter has no gaps](main.md). The draft starts
with two spins and an admissible function with a plateau, explains the
variational no-gap argument, and develops its scalar value consequences
before introducing the separate QAOA claim.

The reader is assumed to know calculus, expectations and elementary linear
algebra. The conditional theorem now precedes the zero-coefficient feasible
descent example. A source-adapted area figure and a polynomial model make the
gap contradiction visible and calculable. A small two-limit array shows why
QAOA needs one fixed word before the size limit.
The difficult analytic estimates retain exact proof destinations. Answered
changed cases test strict convexity, minimisation, support and limit order.

[Correspondence](correspondence.json) binds fifteen passages to the
[evidence graph](../../../examples/qaoa-sk/evidence-graph.json), source
citations, assumptions and unresolved checks. Its canonical bundle path is
`papers/expository.md`; this checked-in manuscript is `main.md`. The paper
uses pinned public mathematical-source URLs so its citations remain usable
when the exact manuscript bytes are assembled into a portable bundle.

The paper is a draft. Source and agent review checked the displayed
statements, examples and reconstructed inference chain. The complete
analytic proofs, fresh Lean/Comparator execution and human reader
understanding have not been independently assessed here. The mapping's
review notes describe the actual scope and remaining review.

The gap diagram adapts [Figure 1 of OpenAI's full-support source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex)
from the [Apache-2.0-licensed source collection](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE).
It relabels the endpoints and uses grayscale shading; the curve is schematic.

The [long reasoning record](../long/reasoning-record.md) supplies a fuller
argument, while the [short paper](../short/paper.md) gives a compressed
research presentation. The [authoring guide](../../../docs/authoring.md)
explains the binding and assembly workflow; the generic templates remain
empty scaffolds.

The public [Erdős method transfer](../../../docs/erdos-method-transfer.md)
identifies the exposition examples that informed the reader order,
proof warrants and changed-case checks. Those writing methods are not
evidence for the SK theorem.
