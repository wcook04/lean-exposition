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

| Paper | Purpose |
| --- | --- |
| [Long reasoning record](qaoa-sk/long/reasoning-record.md) | Derivations, source destinations and the additional steps toward the QAOA claim |
| [Short paper](qaoa-sk/short/paper.md) · [PDF](qaoa-sk/short/paper.pdf) | The full-support argument and its scalar consequence |
| [Exposition](qaoa-sk/expository/main.md) | The model, contact mechanism and examples that test understanding |

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
Manuscript citations use public source URLs; their local README files provide
clickable navigation between the companion documents.

The [consumer guide](../docs/bundle-consumers.md) explains how other applications
can inspect this directory or ZIP without treating structural validation as a
mathematical review.
