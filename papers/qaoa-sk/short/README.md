# Short paper: full support and positive density

[Read the draft](paper.md) · [Rendered PDF](paper.pdf) ·
[Passage correspondence](correspondence.json) · [Bibliography](references.bib)

## Read alongside the original

| OpenAI's full-support manuscript | This short reconstruction |
| --- | --- |
| [Original PDF](../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf) | [Draft PDF](paper.pdf) |
| [Original TeX](../../../examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex) | [Editable Markdown](paper.md) |

The [source guide](../../../examples/qaoa-sk/README.md#read-the-source-and-the-short-paper)
identifies the two OpenAI manuscripts and distinguishes them from this repository's
writing and the separate Prove2Me metadata example.

The paper states the full-support theorem (H.-B. Chen, July 2026; OpenAI,
September 2026) and OpenAI's strict positivity of the density, and gives an
account of OpenAI's quantitative proof for readers who know the earlier
crossing argument. Its introduction compares the two proofs: the crossing
property is conditional on a zero of the second derivative of the consistency
function, while the quantitative bound holds on every positive constant
interval of every order parameter and passes to a limit of shrinking intervals.

Section 3 carries the main estimate. It evaluates an explicitly solvable case
(one step with terminal value `log(2 cosh x)`), where the integrand is negative
on a set of probability 0.56 at `t = 1/2` and the best constant is 2/5; states
the shape inequalities; prints the rational identity of OpenAI's Lemma 4.1 with
all 22 coefficients of its remainder; and relates the inequalities to the
slope-coordinate inequalities of Lopatto and Chen. Section 4 states the
coercive inequality at a fixed time as a separate proposition and proves strict
positivity. Section 5 states the value identity, the classical algorithm and
the QAOA consequence, and routes the circuit construction to the long record.

The intended reader knows the Parisi variational theory at zero temperature.
The shape inequalities and the compact-strip approximation are cited inputs.
The document is a draft explanation of existing public results, with the
original authors and antecedents credited. It is not a new theorem or a fresh
Lean/Comparator check.

## Files and evidence

`paper.md` is the editable manuscript. `correspondence.json` uses the repository's
artifact schema, binds the exact Markdown and source-graph bytes, and names
`papers/short.md` as its location in an assembled bundle. Its state remains
`draft`; its review notes describe bounded source checks and remaining review.
`references.bib` retains the cited primary-source entries. `paper.pdf` is
the rendered edition of the Markdown. `check_solvable_case.py` re-expands the
identity exactly as printed, recomputes the numbers of Section 3.1 and checks
the change of variables of Section 3.5 (SymPy and mpmath; about half a minute).

The selected formal declarations are
`OAI.ZeroTemperatureSK.full_support` and
`OAI.SKValue.value_consequences`. Their exact scope, source versions, historical
unavailable startup, later failed solution builds, and lack of an accepted research-target replay
are recorded in the [source example](../../../examples/qaoa-sk/README.md).
A source-bound local build of the Support implementation completed on
26 October 2026, and dependency extraction recorded its conditional
full-support root; dependencies outside the selected extraction scope remain
boundaries. Our own Comparator run and scalar-target build did not complete.
Two outside reruns report that Comparator accepts both proofs (MathVet,
8 October 2026; C. Toledo, 10 October 2026), and the paper's "Formal
verification" section cites them. The history of the local builds is in the
long record's §13.
The [long record](../long/reasoning-record.md) retains the broader recovery route.

| Short-paper argument | Companion section in the long record |
| --- | --- |
| Pointwise obstruction for the terminal value `|x|` | [§4.1](../long/reasoning-record.md#pointwise-curvature-obstruction) |
| Shape inequalities | [§4.3](../long/reasoning-record.md#shape-comparisons) |
| Passage to integrable order parameters | [§4.5](../long/reasoning-record.md#plateau-limit) |
| Terminal gap and the boundary estimate | [§5](../long/reasoning-record.md#terminal-gap) |
| Smooth positive density | [§§9.1–9.2](../long/reasoning-record.md#smooth-density-consequence) |
| Scalar value identity | [§6](../long/reasoning-record.md#scalar-value-identities) |
| Finite Gaussian approximation | [§7](../long/reasoning-record.md#finite-gaussian-approximation) |
| Circuit construction | [§§8.1–8.6](../long/reasoning-record.md#qaoa-construction) |
| Formal statements and checks | [§12](../long/reasoning-record.md#formal-interfaces), [§13](../long/reasoning-record.md#verification) |

The paper uses companion section names and immutable public manuscript URLs
so those references remain meaningful in the eight-file bundle. This README
provides the clickable checkout routes.

## Rendering

The PDF uses Pandoc's installed LaTeX article template and Tectonic, with the
11-point Latin Modern mathematics and one-inch margins of the exact upstream
full-support manuscript. The title and section content come from this Markdown.
The paper has one table and no figure.

From the repository root, with Pandoc and Tectonic installed:

```sh
paper_build_dir=$(mktemp -d)
pandoc papers/qaoa-sk/short/paper.md \
  --from markdown+tex_math_dollars --to latex --standalone \
  --lua-filter scripts/paper_anchors.lua \
  -V fontsize=11pt -V geometry:margin=1in -M lang=en-GB \
  --output "$paper_build_dir/paper.tex"
tectonic "$paper_build_dir/paper.tex" --outdir "$paper_build_dir"
cp "$paper_build_dir/paper.pdf" papers/qaoa-sk/short/paper.pdf
```

Recheck passage and document hashes after editing the Markdown. A successful
render or schema check does not judge the mathematical argument. The PDF's
public source links work independently of this checkout.
