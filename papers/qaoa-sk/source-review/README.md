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
