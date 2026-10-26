# Long reasoning record: QAOA and the SK value

Read [From Parisi full support to deterministic QAOA circuits](reasoning-record.md).
The draft reconstructs the support-gap contradiction, the scalar martingale
value identity and its finite Gaussian approximation, then reconstructs the
additional construction in the QAOA manuscript, its fixed-word sampling
consequence and the limits of quantitative depth claims.

The source is OpenAI's two public manuscripts and formal interfaces at
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. The
[source collection](../../../examples/qaoa-sk/README.md) gives source hashes,
licences and pinned build metadata. The retained formal targets are
conditional on an admissible minimizer and do not assert QAOA circuit
convergence.

## Reading routes

- Support theorem: [dependencies](reasoning-record.md#argument-map), [variation](reasoning-record.md#feasible-variation), [global scaling alternative](reasoning-record.md#global-scaling-contact), [curvature calculation](reasoning-record.md#curvature-algebra), [approximation](reasoning-record.md#plateau-limit), then [all gap cases](reasoning-record.md#gap-elimination). The terminal case retains the quantitative boundary-layer proof and a [short qualitative alternative](reasoning-record.md#qualitative-terminal-gap), including [empty support](reasoning-record.md#empty-support-chord).
- Density: [smoothness](reasoning-record.md#smooth-density-consequence) and [strict positivity](reasoning-record.md#positive-density), after full support.
- Value and finite construction: [martingale identity](reasoning-record.md#scalar-value-identities), [coefficient budget](reasoning-record.md#coefficient-budget), [finite Gaussian function](reasoning-record.md#finite-gaussian-approximation), [error budget](reasoning-record.md#scalar-error-budget), and [one-step example](reasoning-record.md#one-step-example).
- Circuit theorem: [target and choices](reasoning-record.md#qaoa-construction), [rooted energy](reasoning-record.md#rooted-energy), [helper contraction](reasoning-record.md#helper-contraction), [seed removal](reasoning-record.md#seed-removal), [fixed-word transfer](reasoning-record.md#fixed-word-transfer), [finite-observable error](reasoning-record.md#finite-formula-energy-error), and [assembly](reasoning-record.md#qaoa-assembly-detail).
- Further comparisons: [positive temperature](reasoning-record.md#positive-temperature-route), [sampling](reasoning-record.md#fixed-word-probability), [sampled finite-instance optimum](reasoning-record.md#sampled-finite-instance), [depth quantifiers](reasoning-record.md#depth-quantifiers), and [finite-size bounds](reasoning-record.md#finite-size-comparison).
- Evidence: [formal interfaces](reasoning-record.md#formal-interfaces) and [source checks](reasoning-record.md#verification).

## Reading and evidence

| File | Purpose |
| --- | --- |
| [reasoning-record.md](reasoning-record.md) | Authored long manuscript; source links and correspondence obligations |
| [reasoning-record.json](reasoning-record.json) | Draft stage mapping, source graph hash and exact passage bindings |
| [references.bib](references.bib) | Primary literature, exact editions and distinct citation keys |
| [check_certificate.py](check_certificate.py) | Reproducible rational polynomial identity from the full-support manuscript |

The mapping uses canonical bundle path papers/long.md; the authored source
keeps its descriptive filename here. Manuscript links use immutable public
source destinations so they survive bundle relocation. Companion drafts:
[short paper](../short/paper.md) and [exposition](../expository/main.md).

This authoring pass inspected the full-support variational proof and
certificate, scalar consequences, exact top-level formal types and selected
proof dependencies, and the QAOA manuscript's argument and error-allocation
structure. Bounded source and adversarial readings informed the draft.
Independent mathematical acceptance, accepted research replay and a reader
reconstruction study remain pending. The mapping therefore stays draft with
review_state needs_revision.

The source comparison distinguishes the sampled convex-chord declaration
from the manuscript's full right-derivative statement. Coefficient convexity
gives an ordinary bridge for the same support functional; the Lean declaration
itself remains sequential. The record also compares half-line quotient
integration with smooth extensions at zero, and keeps SKSupport and SKValue
as separate representations. These are correspondence questions, not
demonstrated source theorem defects.

## Finite certificate check

With Python 3.11+ and SymPy available, run from the repository root:

    python3 papers/qaoa-sk/long/check_certificate.py

SymPy 1.14.0 re-expands the published identity exactly: all 22 remainder
coefficients match and are positive, with surplus 140507/1521000000 above
the required 1/1000 coefficient of v⁴. This checks finite algebra only.
PDE signs, integrability, vanishing boundary flux and approximation remain
analytic inputs. SymPy is not a runtime dependency of the core CLI.

The manuscript and mapping can be checked with the repository's artifact
validator. Assembly validates the exact authored bytes against the current
graph; it does not create a mathematical acceptance judgment.

## Bibliographic choices

The bibliography distinguishes two papers called AC2015 in the two source
manuscripts: *On properties of Parisi measures* and *The Parisi formula has a
unique minimizer*. The cited Lopatto edition is arXiv v3, submitted 16 July
2026; its later v4 is not silently substituted. The arXiv revision of
Auffinger–Chen–Zeng cited here postdates its 2020 journal publication.
Montanari's article appeared online in 2021 and in the 2025 journal issue.

Primary metadata and selected theorem hypotheses were inspected.
This is not a claim that every cited proof was independently checked.
The manuscript follows the writing discipline of the public Erdős papers:
state the exact theorem, develop its decisive step, and keep formal and
circuit conclusions distinct. Writing models are not mathematical inputs.

The [historical full-support attempt](../../../examples/qaoa-sk/verification/full-support-build-failure-20261023.json)
and [original diagnostic log](../../../examples/qaoa-sk/verification/full-support-build-failure-20261023.log)
record challenge build/export followed by an implementation-build failure.
They concern the earlier configuration, and do not establish acceptance of the
current sources or a completed corrected replay.
