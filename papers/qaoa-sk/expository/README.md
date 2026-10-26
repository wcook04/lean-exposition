# Expository paper: the SK order parameter

Read [Why the SK order parameter has no gaps](main.md). This exposition
teaches one result: an admissible minimiser cannot be constant on an interval.
It starts from the finite spin problem, introduces the variational objects,
and explains how minimality and curvature force the no-gap contradiction.
Initial and terminal gaps receive their own arguments.

The intended reader knows algebra and elementary calculus. Gaussian
expectation is taught as a weighted integral, and two finite masses prepare
the cumulative measure and its later tail-cost calculation. The zero
coefficient gives an expected payoff and the elementary half-time calculation
$q_0(1/2)=1/3$ before the general moment identity is used. The paired
cumulative/increment plot distinguishes positive height from full support;
the area picture shows the contradiction. A known feedback rule is distinguished
from its random responses, and changed-case questions test when the area
argument applies and how the spin conclusion uses sign reversal.

The main route accepts precisely stated analytic inputs and develops their
no-gap consequence. Contact uses scaling of existing mass, including diffuse
mass. The terminal case uses finite-interval convexity and the existing bound
$q\le1$; the stronger quantitative terminal estimate remains in the long
record. Two finite chords exclude empty support using the same available
inputs. Section 7 collects the optional zero-candidate, PDE, Itô and curvature
calculations after the proof and its return to spins.

The ending returns to the spins: a separate landscape theorem and full
support give near-optimal pairs at each prescribed approximate overlap.
Density, scalar-value and quantum-algorithm consequences have a brief outlook.
Their detailed arguments remain in the [long reasoning record](../long/reasoning-record.md):
§§9.1–9.2 treat density, §9.3 the overlap-pair consequence, §6 the scalar
value, §7 its finite Gaussian approximation and §8 the circuit construction. Having these sources in a
review packet does not make them required chapters of the exposition.

[Correspondence](correspondence.json) binds the authored passages to the
[evidence graph](../../../examples/qaoa-sk/evidence-graph.json), source
citations, assumptions and unresolved checks. Its canonical bundle path is
`papers/expository.md`; this checked-in manuscript is `main.md`. The paper
uses pinned public mathematical-source URLs so its citations remain usable
when the exact manuscript bytes are assembled into a portable bundle.

The paper is a draft. Source and agent review checked the displayed
statements, examples and reconstructed inference chain. The revised scaling
and terminal arguments were checked as ordinary mathematical deductions.
Agent review of the reading sequence checked first-use explanations, optional
reading routes and the inference joining successive steps. Complete independent audit of the
analytic proofs, successful research Comparator replay and human reader
understanding have not been independently assessed here. The mapping's
review notes describe the actual scope and remaining review.

The gap diagram adapts [Figure 1 of OpenAI's full-support source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex)
from the [Apache-2.0-licensed source collection](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE).
The gap diagram relabels the endpoints and uses grayscale shading; its curve
is schematic. The paired plot reuses the source axes and guides to show the exact
piecewise-linear candidate and its density on aligned axes.

The [long reasoning record](../long/reasoning-record.md) supplies a fuller
argument, while the [short paper](../short/paper.md) gives a compressed
research presentation. The [authoring guide](../../../docs/authoring.md)
explains the binding and assembly workflow; the generic templates remain
empty scaffolds.

The public [Erdős method transfer](../../../docs/erdos-method-transfer.md)
identifies the exposition examples that informed the reader order,
proof warrants and changed-case checks. Those writing methods are not
evidence for the SK theorem.

The finite-model explanations also draw on introductory lectures by
[Dmitry Panchenko at IAS](https://www.youtube.com/watch?v=1xZ6AAew3Y4)
and [Chandan Dasgupta at ICTS](https://www.youtube.com/watch?v=oBj_-AX6hUE),
read through their full available caption transcripts. Their teaching
of overlap, fixed couplings and frustration informed the presentation;
the paper's mathematical claims follow its cited research sources.
