# Expository paper: the SK order parameter

Read [Why the SK order parameter has no gaps](main.md). The draft starts
with two spins and an admissible function with a plateau, explains the
variational no-gap argument, and develops its scalar value consequences
before developing the separate QAOA claim. The opening states the motivating
question: whether depth and angles fixed before the system-size limit can
approach the optimal expected energy per spin. The no-gap reading route ends
with the scalar value in Section 6; the circuit route continues through the
finite correlation construction and the additional operator theorems.

The first route asks a reader comfortable with calculus proofs, Gaussian
expectations and conditional expectation to reconstruct the no-gap
contradiction and scalar energy cancellation from identified analytic inputs.
The circuit continuation assumes complex inner products and tensor products;
it explains the additional construction's inputs, outputs and quantifiers,
while retaining its operator theorems as source results.

A paired plot distinguishes a positive cumulative value from increment mass.
The existing area figure and exact polynomial model explain the gap
contradiction. The one-step Gaussian example now uses an asymmetric cutoff
that detects an index error, and the continuation derives the actual
measurement probability from first and second moments. Section 9 contains
answered teaching checks; Section 10 retains supporting analytic and
convention calculations after their applications. No reader study is claimed.

[Correspondence](correspondence.json) binds the authored passages to the
[evidence graph](../../../examples/qaoa-sk/evidence-graph.json), source
citations, assumptions and unresolved checks. Its canonical bundle path is
`papers/expository.md`; this checked-in manuscript is `main.md`. The paper
uses pinned public mathematical-source URLs so its citations remain usable
when the exact manuscript bytes are assembled into a portable bundle.

The paper is a draft. Source and agent review checked the displayed
statements, examples and reconstructed inference chain. Complete independent audit of the
analytic proofs, successful research Comparator replay and human reader
understanding have not been independently assessed here. The mapping's
review notes describe the actual scope and remaining review.

The gap diagram and paired cumulative/increment plot adapt [Figure 1 of OpenAI's full-support source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex)
from the [Apache-2.0-licensed source collection](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE).
The gap diagram relabels the endpoints and uses grayscale shading; its curve
is schematic. The paired plot shows the exact piecewise-linear candidate
and its density, so its constant interval can be compared on aligned axes.

The [long reasoning record](../long/reasoning-record.md) supplies a fuller
argument, while the [short paper](../short/paper.md) gives a compressed
research presentation. The [authoring guide](../../../docs/authoring.md)
explains the binding and assembly workflow; the generic templates remain
empty scaffolds.

The public [Erdős method transfer](../../../docs/erdos-method-transfer.md)
identifies the exposition examples that informed the reader order,
proof warrants and changed-case checks. Those writing methods are not
evidence for the SK theorem.
