# Expository paper: the SK order parameter

Read [Why the SK order parameter has no gaps](main.md). This exposition
teaches one result: an admissible minimiser cannot be constant on an interval.
It starts from the finite spin problem, introduces the variational objects,
and explains how minimality and curvature force the no-gap contradiction.
Initial and terminal gaps receive their own arguments.

The intended reader knows calculus and elementary probability. The necessary
stochastic identities are explained where they enter and identified as source
inputs. The paired cumulative/increment plot distinguishes a positive function
from a measure with full support; the area picture shows the contradiction.
The paper's task is to make that argument understandable, not to teach every
result retained in the source corpus.

Density, scalar-value and quantum-algorithm consequences have a brief outlook.
Their detailed arguments remain in the [long reasoning record](../long/reasoning-record.md):
§§5.1–5.2 treat density, §6 the scalar value, §7 its finite Gaussian
approximation and §9 the circuit construction. Having these sources in a
review packet does not make them required chapters of the exposition.

[Correspondence](correspondence.json) binds the authored passages to the
[evidence graph](../../../examples/qaoa-sk/evidence-graph.json), source
citations, assumptions and unresolved checks. Its canonical bundle path is
`papers/expository.md`; this checked-in manuscript is `main.md`. The paper
uses pinned public mathematical-source URLs so its citations remain usable
when the exact manuscript bytes are assembled into a portable bundle.

The paper is a draft. Source and agent review checked the displayed
statements, examples and reconstructed inference chain. A further sequential
agent review checked first-use explanations, purpose before construction and
the inference joining successive steps. Complete independent audit of the
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
