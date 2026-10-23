# Selected source readings

This annex retains two publisher PDFs and a small licensed implementation
selection that informed the QAOA drafts and authoring methods. The
[reference records](../references.json) own their source URLs, exact editions,
hashes, licences and applied decisions. These are reading materials, not
dependencies of the CLI or evidence of a new formal check.

## QAOA publisher papers

Both PDFs are unmodified copies retrieved on 23 October 2026. Their original
notices remain in the files. They are distributed under
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/);
the [legal code](CC-BY-4.0.txt) is retained locally. The notes below are original
and separate from the papers.

### Basso, Farhi, Marwaha, Villalonga and Zhou (2022)

[The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on
Large-Girth Regular Graphs and the Sherrington-Kirkpatrick
Model](basso-et-al-2022-qaoa-high-depth.pdf), by Joao Basso, Edward Farhi, Kunal
Marwaha, Benjamin Villalonga and Leo Zhou. TQC 2022, LIPIcs 232, article 7,
pages 7:1–7:21. Copyright the authors.
[DOI and publisher licence record](https://doi.org/10.4230/LIPIcs.TQC.2022.7).

Reading scope: Section 4, Theorem 1, and Section 5, equation (5.2), together
with their definitions and discussion. The fixed-depth performance identity
and the conjectured increasing-depth optimality have different status. The
drafts therefore preserve the order of limits and do not cite the identity
as a proof of eventual Parisi optimality.

The proceedings sends the theorem's proof to Section 6 of the full preprint.
That proof was not independently checked in this reading. Equation numbers
from the full preprint must cite that edition: proceedings Section 6 instead
discusses Max-q-XORSAT. This retained PDF cannot substitute for a full-version
locator merely because the title and authors match.

### Farhi, Goldstone, Gutmann and Zhou (2022)

[The Quantum Approximate Optimization Algorithm and the Sherrington-Kirkpatrick
Model at Infinite Size](farhi-et-al-2022-qaoa-infinite-size.pdf), by Edward Farhi,
Jeffrey Goldstone, Sam Gutmann and Leo Zhou. Quantum 6, 759.
[DOI and publisher licence record](https://doi.org/10.22331/q-2022-07-07-759).

Reading scope: the model in Section 3 and the theorem, concentration corollary
and variance argument in Section 4, equations (13)–(17). The first two limiting
moments imply concentration at fixed depth and angles; they do not justify
depth or angle choices varying with system size. This supports the drafts'
fixed-word boundary, without supplying the increasing-depth construction.
The paper minimizes energy. Transferring a signed formula or numerical value
to a maximizing convention also requires an explicit sign and normalization
comparison.

## LeanArchitect implementation

The [selected LeanArchitect files and reading notes](leanarchitect/README.md)
explain its authored metadata, dependency projection and output paths. The
selection has its own Apache-2.0 licence and retained source headers. It is
read-only reference material here, not a complete buildable checkout.

## Coverage and reuse

The other mathematical references remain links and metadata in
[the literature guide](../literature.md); their PDFs are not redistributed.
The QAOA example's own upstream corpus is independently governed by its
[source lock](../../examples/qaoa-sk/source-lock.json). Neither this annex nor
the citations extend the scope of the two retained Lean targets. The paper
bundle contains its declared graph, manuscripts and mappings; it does not
automatically include this annex.
