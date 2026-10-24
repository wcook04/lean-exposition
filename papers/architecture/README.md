# Architectural companion: from Lean source to explanation

[Read the revised paper](paper.md) · [Rendered PDF](paper.pdf)

This companion is for a mathematician entering the repository through its
papers. It traces one selected theorem from pinned source through an evidence
graph, three authored explanations and a versioned bundle, then explains what
a consumer can inspect. It is a **revised draft without independent human acceptance**; it does not
upgrade any Lean, Comparator, platform or mathematical-review status.

The [QAOA/SK source example](../../examples/qaoa-sk/README.md) provides the
worked mathematical case. The [bundle contract](../../docs/bundle-consumers.md)
and [graph contract](../../docs/contracts.md) specify the machine-readable
details. The [read-only Prove2Me adapter](../../docs/prove2me.md) describes the
external metadata boundary.

## Try the route locally

Install the repository as instructed in its [top-level README](../../README.md).
With a selected local graph, the command-line route is:

```sh
lean-exposition validate path/to/graph.json
lean-exposition inspect path/to/graph.json --view arguments --goal GOAL_ID
lean-exposition inspect path/to/graph.json --view declarations --goal DECLARATION_ID
lean-exposition scaffold path/to/graph.json --out path/to/empty-draft-directory
```

`scaffold` creates placeholders. After authors have written the three texts
and their passage maps, `assemble` creates an eight-file bundle. Its required
`--long`, `--short` and `--expository` arguments each take a Markdown path and
a mapping path; see `lean-exposition assemble --help`. Then run
`lean-exposition check-bundle BUNDLE_DIRECTORY` and
`lean-exposition inspect-bundle BUNDLE_DIRECTORY`. The latter reports structural
validity and `semantic_certification: false`; source files and verification
receipts remain external.

To begin at the short paper's support theorem rather than a graph ID, run:

```sh
lean-exposition inspect-bundle BUNDLE_DIRECTORY --paper short --passage main-result
```

The paper view returns its outline and mapped text in reading order, exact
byte/line spans, links to the recorded claims and their prerequisite support,
and unmapped segments plus passages omitted by the selector. Reading order does not assert a proof
dependency. `--paper` also accepts `long` and `expository`; without
`--passage`, the selected paper's full mapped view is returned. This is a
projection of the existing eight files, not a new stored document.

The bundle's eight persistent files are: the manifest, the graph, and three
Markdown/mapping pairs. The manifest hashes the other files; the graph keeps
typed evidence; each mapping binds one text's passages and review state to
the exact graph and text bytes. The local PDF is a reading view of this
companion and is not a ninth bundle member. An immutable review decision
requires the manifest digest and exact source edition, not only a bundle name.

## Figure provenance and rendering

The seven TikZ figures in `paper.md` begin with an inverted reader funnel
adapted from Will Cook's existing mathematics-map visual. Its widths indicate
editorial selection, not page length or proof strength; the return arrow
marks claim-site links to exact evidence. The workflow, correspondence and review figures adapt the *authored
records/derived views*, *three versions with shared support*, *registered
supports*, *two correspondences* and *refinement* compositions in Will Cook's
[active Plectis Erdős systems paper](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
(figures `fig:lifecycle`, `fig:hypothesis`, `fig:theorem`, `fig:checks`
and `fig:refinement`; source licence
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). This
companion redraws their content for the Lean Exposition contracts; each
connector names its workflow, mapping, argument or review relation. The
additional concrete gap-argument figure adapts the same shared-support
composition to two actual ingredients, under the positive-plateau guard.

Render with the repository's paper toolchain:

```sh
paper_build_dir=$(mktemp -d)
pandoc papers/architecture/paper.md \
  --from markdown+raw_tex+tex_math_dollars --to latex --standalone \
  -V fontsize=11pt -V geometry:margin=1in -M lang=en-GB \
  --output "$paper_build_dir/paper.tex"
tectonic "$paper_build_dir/paper.tex" --outdir "$paper_build_dir"
cp "$paper_build_dir/paper.pdf" papers/architecture/paper.pdf
```

The exact source-to-paper claim remains unreviewed. A successful render or
bundle schema check establishes only its own narrow result.
