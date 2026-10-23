# Short paper: the support-gap argument

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

This short research-style reconstruction explains OpenAI's proof that an
admissible integrable zero-temperature SK minimizer has full relative
Stieltjes support. Its central argument is the contradiction between
variational contact at the endpoints of a support gap and strict curvature
inside that gap. The scalar value identity and the connection to the separate
QAOA manuscript follow after that argument.

The intended reader knows elementary stochastic calculus and variational
arguments. The analytic sign propagation, rational polynomial certificate and
compact-strip approximation remain explicitly cited inputs. The document is a
draft explanation of existing public results, with the original authors and
antecedents credited. It is not a new theorem or a fresh Lean/Comparator check.

## Files and evidence

`paper.md` is the editable manuscript. `correspondence.json` uses the repository's
artifact schema, binds the exact Markdown and source-graph bytes, and names
`papers/short.md` as its location in an assembled bundle. Its state remains
`draft`; its review notes describe bounded source checks and remaining review.
`references.bib` retains the five cited primary-source entries. `paper.pdf` is
the rendered edition of the Markdown.

The selected formal declarations are
`OAI.ZeroTemperatureSK.full_support` and
`OAI.SKValue.value_consequences`. Their exact scope, source versions, historical
unavailable startup, and lack of a completed research-target replay
are recorded in the [source example](../../../examples/qaoa-sk/README.md).
The [long record](../long/reasoning-record.md) retains the broader recovery route.

| Short-paper argument | Companion section in the long record |
| --- | --- |
| Integrated curvature estimate | [§4: Strict curvature on a constant interval](../long/reasoning-record.md#curvature-and-gap-certificate) |
| The three kinds of support gap | [§5: Excluding terminal, interior and initial gaps](../long/reasoning-record.md#gap-elimination) |
| Scalar value identity | [§6: Recovering the value from a martingale](../long/reasoning-record.md#scalar-value-identities) |
| Finite Gaussian approximation | [§7: A finite Gaussian spin and its adjacent correlations](../long/reasoning-record.md#finite-gaussian-approximation) |
| Further circuit construction | [§9: From the scalar formula to one ordinary QAOA word](../long/reasoning-record.md#qaoa-construction) |

The paper uses companion section names and immutable public manuscript URLs
so those references remain meaningful in the eight-file bundle. This README
provides the clickable checkout routes.

## Rendering

The PDF uses Pandoc's installed LaTeX article template and Tectonic, with the
11-point Latin Modern mathematics and one-inch margins of the exact upstream
full-support manuscript. The title and section content come from this Markdown.
No diagram or new illustration is introduced.

From the repository root, with Pandoc and Tectonic installed:

```sh
paper_build_dir=$(mktemp -d)
pandoc papers/qaoa-sk/short/paper.md \
  --from markdown+tex_math_dollars --to latex --standalone \
  -V fontsize=11pt -V geometry:margin=1in -M lang=en-GB \
  --output "$paper_build_dir/paper.tex"
tectonic "$paper_build_dir/paper.tex" --outdir "$paper_build_dir"
cp "$paper_build_dir/paper.pdf" papers/qaoa-sk/short/paper.pdf
```

Recheck passage and document hashes after editing the Markdown. A successful
render or schema check does not judge the mathematical argument. The PDF's
public source links work independently of this checkout.
