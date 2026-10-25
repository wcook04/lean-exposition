# One argument, several ways to read it

[Read the companion](paper.md) · [Rendered PDF](paper.pdf)

This paper is for an interested mathematician who wants to understand why
Lean Exposition maintains several accounts of the same mathematics. It explains
how a shared record connects the papers without dictating their reading order,
then follows the SK no-gap argument from a short proof to its missing analytic
detail and original source. It distinguishes explanation, formal evidence and
navigation, and describes the useful scope and cost of the present system.

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

The two figures answer different questions: why three papers share one corpus,
and which two ingredients a particular contradiction uses. They adapt the
parallel-record and shared-support TikZ compositions in `paper.md` at local
commit `4246d4e`, whose source is Will Cook's
[*A Repository-Based System for Research and Publication*](https://github.com/wcook04/plectis-erdos/blob/61fb590921e3b5a100dc264bed052c9cf6959daf/paper/systems/claim-faithful-publication-systems-paper.tex)
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). The first replaces
the linear funnel with three accounts mapped to shared support. The second
retains the two-input argument and makes their different hypotheses explicit.
The evidence-channel figure has been replaced by prose, where its distinctions
can be explained without another overview. Every connector states its relation.

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
