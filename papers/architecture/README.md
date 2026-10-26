# One argument, several ways to read it

[Read the companion](paper.md) · [Rendered PDF](paper.pdf)

This paper is for an interested mathematician who wants to understand why
Lean Exposition maintains several accounts of the same mathematics. It explains
how a shared record connects the papers without dictating their reading order,
then follows the SK no-gap argument from a short proof to its missing analytic
detail and original source. It distinguishes explanation, formal evidence and
navigation, and describes the useful scope and cost of the present system.
Section 6 follows a recorded correction: a two-chord proof makes a main
reading route independent of an optional calculation, while preserving the
stronger material elsewhere. It separates this local repair from a claim
that an authoring method improved learning. The
[shared procedure](../../docs/authoring.md#use-and-improve-the-transition-skills)
and [transition skills](../../skills/README.md) contain the operational steps.

The companion adds a reading guide to the architecture. It does not replace the
[exposition](../qaoa-sk/expository/main.md), [specialist paper](../qaoa-sk/short/paper.md)
or [long reasoning record](../qaoa-sk/long/reasoning-record.md). The drafts remain
subject to mathematical and reader review; this rewrite establishes no new
formal acceptance or independent human acceptance.

## Use the tools

Agents start at [AGENTS.md](../../AGENTS.md). Developers use
[CONTRIBUTING.md](../../CONTRIBUTING.md) for installation and checks.
The [consumer guide's worked journey](../../docs/bundle-consumers.md#start-with-the-authored-support-theorem)
assembles the papers, opens the theorem and finds the different uses of its
curvature input. [Contracts](../../docs/contracts.md) define the record and
query boundaries. These guides own operational detail; the paper can be read
without installing the software.

## Figures and reading-copy links

The three figures have separate jobs: identify a claim shared by selected
passages, expose the joint inputs to a contradiction, and distinguish the two
fuller explanations of one estimate. They adapt the parallel-record and local
selection compositions (figures 2 and 3) in `paper.md` at local commit `fde01ef`,
and the shared-support composition (figure 1) at `4246d4e`. These draw on
Will Cook's
[*A Repository-Based System for Research and Publication*](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). The revisions use
current passage identities, keep the branch-specific hypotheses, and add the
two authored expansion links with their citation route. Figure 3 adapts the
native TikZ excursion study of 26 October 2026, with shorter labels and
orthogonal connectors; it retains that study's intentional absence of a direct
claim mapping from the finite-step explanation. The paper retains its existing
Pandoc/TikZ renderer and typography.

| Figure and label | Source relationships shown |
| --- | --- |
| 1, `fig:shared-claim` | Long `gaps`, short `main-result` and exposition `full-support-statement` directly map `support.full_relative_support_curvature`. This ordinary claim is distinct from the formal-interface goal `full_support`. |
| 2, `fig:joint-inputs` | The bounded positive-gap contradiction uses contact and strict curvature for the same moment curve. The joint-use label is an explanatory annotation, not an extracted logical record. |
| 3, `fig:excursion-return` | Long `curvature` and `fixed-time-coercivity` each `expand` short `curvature`. Only the latter long passage and the short passage directly map `support.positive_curvature`; its `citation_ids` names `support_curvature_source`, whose `source_id` is `support_tex_curvature`. |

The third figure's source is original Proposition 5.1, `curvature.tex` lines
9–52, at OpenAI/math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Its arrows retain stored directions: readers travel against an expansion
arrow to visit the fuller treatment. Source-field references are not proof
dependencies. The wider `fixed-time-coercivity` passage also treats zero
coefficients; the displayed §4.5 destination selects its positive-plateau use.

The former funnel, generic evidence channels and review-state diagram remain
outside this edition. Their useful distinctions are expressed in the
independent account roles, scoped evidence and concrete repair. They add no
missing relationship to the selected journeys. The reading website renders
these figures through [its figure registry](../../site/src/figures/registry.ts);
caption or semantic changes must be carried into those existing components.

The Markdown links to local papers and guides. The standalone PDF keeps those
references as descriptive paper-and-section text, with clickable public source
URLs and any internal links. Its `portable-local-links` metadata selects this
policy in the existing [Pandoc filter](../../scripts/paper_anchors.lua).
It embeds no local launch actions that would break when the PDF is moved.
If distributing the full repository or a packet, provide its own reading index;
do not assume a copied PDF retains its former directory neighbours. The
[consumer guide](../../docs/bundle-consumers.md#distribute-reading-copies-with-working-links)
explains the distinction between source mappings and rendition links.

## Render and inspect

Use Pandoc and Tectonic from the repository root. Put intermediate output in a
fresh directory outside the checkout; set `paper_build_dir` to a preferred
scratch-storage path if needed. Only copy the final inspected PDF back.

```sh
paper_build_dir=$(mktemp -d "${TMPDIR:-/tmp}/lean-exposition-paper.XXXXXX")
pandoc papers/architecture/paper.md \
  --from markdown+raw_tex+tex_math_dollars --to latex --standalone \
  --lua-filter scripts/paper_anchors.lua \
  -V fontsize=11pt -V geometry:margin=1in -M lang=en-GB \
  --output "$paper_build_dir/paper.tex"
tectonic "$paper_build_dir/paper.tex" --outdir "$paper_build_dir"
pdfinfo "$paper_build_dir/paper.pdf"
pdftoppm -r 110 -png "$paper_build_dir/paper.pdf" "$paper_build_dir/page"
```

Inspect **every** page at reading size, especially figure labels, arrowheads,
page breaks and link text. Check the PDF annotations after copying it to a
different directory: public links should remain URLs, internal links should
resolve, and this companion should have no local file actions. Poppler supplies
`pdfinfo` and `pdftoppm`; PyMuPDF can inspect PDF annotations. These are optional
paper-production tools, not runtime dependencies. The rendering tests also
check that this opt-in policy leaves other papers and HTML output unchanged.

After inspection:

```sh
cp "$paper_build_dir/paper.pdf" papers/architecture/paper.pdf
```
