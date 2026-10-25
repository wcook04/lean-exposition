# Mathematical papers

The QAOA / SK drafts develop three complementary accounts of the selected
mathematics: a detailed reasoning record, a short paper selecting the main
argument, and an exposition introducing its objects and mechanisms.

Their starting point is the [pinned source corpus](../examples/qaoa-sk/README.md)
and its [evidence graph](../examples/qaoa-sk/evidence-graph.json). The graph
distinguishes the full-support and scalar-value formal interfaces from the
broader QAOA manuscript. Source correspondence and unresolved obligations
belong beside each draft's mathematical claims.

The package's [authoring skills](../skills/README.md) describe the transitions.
Its default templates remain empty so another project can use the same workflow.

## Read the drafts

Choose one entrance; reading every account in order is unnecessary.

| Paper | What you can reconstruct | Inputs and next destination |
| --- | --- | --- |
| [Exposition](qaoa-sk/expository/main.md) · [PDF](qaoa-sk/expository/main.pdf) | Feasible mass changes, contact and the area contradiction, with separate endpoint cases and a finite-spin payoff | Calculus, measures and expectation; accepts stated stochastic and analytic inputs. Visit long §§3–5 for their proofs. |
| [Short paper](qaoa-sk/short/paper.md) · [PDF](qaoa-sk/short/paper.pdf) | How one quantitative inequality excludes support gaps and then gives positive density | Stochastic calculus and variational arguments; imports the shape comparisons and certificate. Visit long §4 for those inputs or §7 for the finite Gaussian construction. |
| [Long reasoning record](qaoa-sk/long/reasoning-record.md) · [PDF](qaoa-sk/long/reasoning-record.pdf) | Selected analytic, scalar and circuit arguments with local hypotheses and source destinations | Enter at a named proof obligation. Substantial imported circuit theorems and formal-model transport boundaries remain identified. |

The [source correspondence review](qaoa-sk/source-review/README.md) records the
retained formal interfaces and the manuscript arguments they are meant to represent.
These are drafts of explanations of existing results. Their mappings retain the
remaining review obligations and the source graph's formal-check status.

For an introduction to how the repository connects proofs, papers and recorded
checks, read the separate [architectural companion](architecture/README.md)
or its [PDF](architecture/paper.pdf). It explains the local workflow and its
limits for a reader entering through the mathematics.

## Assemble the authored bundle

After installing the package, run from the repository root:

```sh
lean-exposition assemble examples/qaoa-sk/evidence-graph.json \
  --long papers/qaoa-sk/long/reasoning-record.md papers/qaoa-sk/long/reasoning-record.json \
  --short papers/qaoa-sk/short/paper.md papers/qaoa-sk/short/correspondence.json \
  --expository papers/qaoa-sk/expository/main.md papers/qaoa-sk/expository/correspondence.json \
  --out build/qaoa-sk-authored
lean-exposition check-bundle build/qaoa-sk-authored
lean-exposition export build/qaoa-sk-authored --out build/qaoa-sk-authored.zip
lean-exposition inspect-bundle build/qaoa-sk-authored.zip
```

Assembly preserves the exact source graph, Markdown and mapping bytes. The bundle
contains eight files: a manifest, the graph and three Markdown/mapping pairs.
PDFs, bibliographies and calculation scripts remain companions in this checkout.
Manuscript citations use public source URLs. Companion references link to the
other manuscript in the checkout; the PDF renderer selects the corresponding
PDF destination. Preserve the `expository/`, `short/` and `long/` directories
when distributing a human reading edition, with each source and PDF together.
The existing `scripts/paper_anchors.lua` filter preserves the manuscripts'
bookmarks and chooses the appropriate companion destination.

The eight-file bundle is an exact archival capture, with flattened paper names;
it carries neither the PDFs nor the checkout's directory layout. Its raw
Markdown retains source-relative references and is not a relocated reading
edition. A consuming reading view must resolve companion references against
the captured paper identities and anchors without modifying the stored bytes.
Test that derived view separately from source and PDF navigation.

The [consumer guide](../docs/bundle-consumers.md) explains how other applications
can inspect this directory or ZIP without treating structural validation as a
mathematical review.
