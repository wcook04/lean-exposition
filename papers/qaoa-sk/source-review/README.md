# Source review for the QAOA–SK drafts

The two selected formal interfaces describe full support of an admissible
zero-temperature SK minimizer and scalar ground-state value consequences.
These notes trace their definitions and proof mechanisms to the public
OpenAI manuscripts at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

| Read for | Review input |
| --- | --- |
| Exact full-support hypotheses and conclusion | [Full-support interface](full-support-interface.md) |
| Why contact and curvature exclude support gaps | [Full-support proof](full-support-proof.md) |
| Value identities, terminal limits and finite Gaussian coefficients | [Scalar-value interface](scalar-value-interface.md) |
| The further steps leading to the QAOA claim | [QAOA dependency chain](qaoa-dependency-chain.md) |
| Attribution, primary literature and adversarial checks | [References and adversarial review](references-and-adversarial-review.md) |
| Machine-readable source paths, hashes and statement locators | [Correspondence index](correspondence.json) |

The [source lock](../../../examples/qaoa-sk/source-lock.json) owns the
upstream bytes and their attribution. The
[evidence graph](../../../examples/qaoa-sk/evidence-graph.json) owns the
selected goal IDs and verification records. The correspondence index is an
authored reading aid; it does not add extracted Lean edges or change evidence
statuses. A formal interface is the theorem statement to check, while its
implementing proof is retained in a separate `OAI` source tree.

These records report source reading and mathematical correspondence analysis.
They supply neither a fresh Lean build or Comparator replay nor independent
expert acceptance. The two Comparator configurations permit `propext`,
`Quot.sound`, and `Classical.choice`, with `enable_nanoda=false`; that policy
is distinct from an observed axiom audit.

When using a passage in a draft, retain its exact hypotheses and source
locator. In particular, full relative support is on `[0,1)`, minimizer
existence is not part of the full-support conclusion, the two formal APIs
use different representations, and the manuscript's QAOA convergence needs
additional circuit arguments. The individual notes identify the precise
mathematical and evidential boundaries.

After exporting drafts, open their full-proof destinations from the exported
document locations. Repository-relative links in these review inputs assume
the source checkout. Graph and text hashes alone do not establish that a
reader of a separate bundle can reach the linked proof or source.

## Reconstruction and retained run history, 25 October 2026

The [long record](../long/reasoning-record.md) now reconstructs compact-strip
recovery (§2.4), the complete contact argument (§3), the rational certificate
and analytic transfer (§4), every support-gap case and the smooth positive
density consequence (§5), scalar finite-accuracy choices (§7), the independent
scalar formal route (§8), and the circuit construction (§9). These are
source-based mathematical reconstructions, not an independent proof acceptance.

The [23 October partial-observation receipt](../../../examples/qaoa-sk/verification/full-support-build-failure-20261023.json)
and [retained log](../../../examples/qaoa-sk/verification/full-support-build-failure-20261023.log)
record a later full-support attempt after the earlier unavailable-Comparator
event. That attempt built and exported the admitted challenge, then failed
while building the solution because the imported `Diffusion/AbsIncrement`
object was missing. It did not export the solution or reach comparison.
The subsequent derived-configuration repair is separate from this historical
observation; this receipt supplies no terminal result for the repaired target.
The separate [24 October scalar-value receipt](../../../examples/qaoa-sk/verification/scalar-value-build-failure-20261024.json)
and [log](../../../examples/qaoa-sk/verification/scalar-value-build-failure-20261024.log)
record the original scalar invocation's terminal outcome: its admitted
challenge built and exported, then the solution build failed because the
imported `IntegralPositiveMulGaussian` object was missing. This invocation
also used the pre-repair build configuration and reached neither solution
export nor kernel/comparison checking. No successful replay of the corrected
configuration has been recorded for either target.

| Selected target and input edition | Challenge build/export | Solution build | Solution export, kernel check and comparison |
| --- | --- | --- | --- |
| Full support, historical pre-repair inputs | Completed | Failed: missing `AbsIncrement.olean` | Not reached |
| Scalar value, historical pre-repair inputs | Completed | Failed: missing `IntegralPositiveMulGaussian.olean` | Not reached |
| Full support, corrected subtree-glob inputs | Build confirmed; exporter observed live | Unknown | Unknown |
| Scalar value, corrected subtree-glob inputs | Not observed | Unknown | Unknown |

The [25 October interruption summary](../../../examples/qaoa-sk/verification/corrected-replay-interruption-20261025.json)
records the later corrected replay separately. Its controller stopped without
a recovered terminal research result. Comparator and research v2 extraction
outcomes remain unknown, neither rejected nor accepted. The full reconciliation
is retained under the summary's source-observation digest. This curated summary
does not substitute for target process logs, kernel/quotient results or actual
axiom inventories.

The graph separately identifies the active derived Lake file and lockfile by
their exact digests. These are input identities, not a replacement for the
historical records. The public source lock continues to distinguish the
original upstream configuration from this derived configuration.
