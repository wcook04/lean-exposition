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

Choose the reading task before opening a graph:

- For the mathematical result and decisive proof, start with the
  [short paper](../qaoa-sk/short/paper.md#model-and-result).
- To recover the strict-curvature input, enter the
  [long derivation](../qaoa-sk/long/reasoning-record.md#curvature-and-gap-certificate),
  then return to the [gap proof](../qaoa-sk/short/paper.md#gap-elimination)
  and identify where that input combines with endpoint contact.
- For the objects and the area argument, read the
  [exposition](../qaoa-sk/expository/main.md) in order at its stated prerequisites.

The queries below answer where the recorded claims occur and what support is
linked to them. Reading the linked argument answers how those ingredients are
used. Keep those two tasks separate when reporting a review.

## Try the route locally

Install the repository as instructed in its [top-level README](../../README.md),
then use the [complete authored-bundle command](../../docs/bundle-consumers.md#start-with-the-authored-support-theorem)
to package the supplied mathematical papers. Start at their theorem:

```sh
lean-exposition query-papers build/qaoa-sk-authored \
  --paper short --passage main-result --format text
lean-exposition query-papers build/qaoa-sk-authored \
  --node support.positive_curvature --relation prerequisites --format text
```

The first query opens the main theorem's mapped claims and hypotheses. The
second finds passages using the recorded curvature ingredient and shows the
typed paths. Omit `--format text` for complete machine-readable JSON. Both
formats use one validated capture and preserve the distinct evidence outcomes.
The existing `scaffold` command is for starting empty documents; it is not
needed to read these authored papers. Source files and verification receipts
remain external to the eight-file bundle.

You can also start from a source and find its recorded uses. For the curvature
source, follow incoming provenance references by one step:

```sh
lean-exposition query-corpus build/qaoa-sk-authored \
  --record sources support_tex_curvature --family provenance \
  --direction incoming --max-depth 1 --max-records 40 --format text
```

The result includes the claim `support.positive_curvature`, citations and
evidence records. Its direct paper mappings include `long / curvature`,
`short / gap-proof` and `expository / contact-and-gap`. Inspect the long passage
and its recorded support:

```sh
lean-exposition inspect-bundle build/qaoa-sk-authored \
  --paper long --passage curvature
```

Incoming browsing preserves the stored arrow direction. Relations between
reached records retain cross-links and cycles; the separate witnesses give
routes into that subgraph. `--paper short` restricts traversal to the short
paper's recorded support membership. The frontier reports whether a neighbour
was excluded by that membership, depth or record budget. Supplementary endpoint
and link-owner records provide context beyond the selected-record budget.
Use the JSON output for exact references, source locators and paper bindings.

To begin at the short paper's support theorem rather than a graph ID, run:

```sh
lean-exposition inspect-bundle build/qaoa-sk-authored --paper short --passage main-result
```

The paper view returns its outline and mapped text in reading order, exact
byte/line spans, links to the recorded claims and their prerequisite support,
and unmapped segments plus passages omitted by the selector. Reading order does not assert a proof
dependency. `--paper` also accepts `long` and `expository`; without
`--passage`, the selected paper's full mapped view is returned. This is a
projection of the existing eight files, not a new stored document.

To start from a text selection, `query-papers --byte-range START END` uses
half-open UTF-8 Markdown byte positions and requires `--paper` and
`--expect-manifest`. It returns overlapping mapped content with the whole
passage's requirements; whitespace, markers and unmapped text create no match.
PDF highlights, browser character offsets and external source locators need
their own coordinate mapping.

The bundle's eight persistent files are: the manifest, the graph, and three
Markdown/mapping pairs. The manifest hashes the other files; the graph keeps
typed evidence; each mapping binds one text's passages and review state to
the exact graph and text bytes. The local PDF is a reading view of this
companion and is not a ninth bundle member. An immutable review decision
requires the manifest digest and exact source edition, not only a bundle name.

## Figure provenance and rendering

The three TikZ figures in `paper.md` explain a positive-gap argument, the
writing funnel and the distinct evidence channels. The inverted funnel adapts
Will Cook's existing mathematics-map visual. Its widths indicate editorial
selection, not page length or proof strength; its return arrow follows
claim-site links to exact evidence. The argument and evidence figures adapt
the shared-support and two-correspondence compositions in Will Cook's
[active Plectis Erdős systems paper](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
(source licence
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). This
companion redraws their content for the Lean Exposition contracts; each
connector names its workflow, mapping, argument or review relation. The
concrete gap-argument figure adapts the shared-support composition to two
actual ingredients, under the positive-plateau guard.
Its endpoint slope bounds and strict curvature are shown jointly supplying
the contradiction. None of these arrows asserts a new Lean dependency.

Render with the repository's paper toolchain:

```sh
paper_build_dir=$(mktemp -d)
pandoc papers/architecture/paper.md \
  --from markdown+raw_tex+tex_math_dollars --to latex --standalone \
  --lua-filter scripts/paper_anchors.lua \
  -V fontsize=11pt -V geometry:margin=1in -M lang=en-GB \
  --output "$paper_build_dir/paper.tex"
tectonic "$paper_build_dir/paper.tex" --outdir "$paper_build_dir"
cp "$paper_build_dir/paper.pdf" papers/architecture/paper.pdf
```

The exact source-to-paper claim remains unreviewed. A successful render or
bundle schema check establishes only its own narrow result.
