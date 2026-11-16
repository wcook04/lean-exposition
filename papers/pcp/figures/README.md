# PCP navigation figures

The [long account's proof map](../long/proof-map.svg) shows selected mathematical
uses leading to the verifier and its resource bounds. Each arrow names what the
source supplies: an error bound, fixed nearby polynomials, completeness and soundness, or
resource and reduction guarantees. These arrows are authored
explanatory relations, not an extracted Lean dependency graph. Bounds (B15),
(B16) and (B25) are the equation labels in that account. The reverse inclusion
is explained in the adjacent text, rather than drawn as a consequence of the
three-colouring verifier.

The [exposition's table/check matrix](../expository/table-checks.svg) records which
of the eight physical tables each check may query. The entries follow
`ThreeColorVerifier.branchTest` and `branchQueries` at the pinned Lean revision
`a0ce13ed0fa264f051c1278e039596ce65557fa4`. A dot is not a query count. Column 5
connects the worked example to the vertex zero-on-grid test; that example omits the inner-test
reads and does not execute the complete verifier. Public adjacency is computed
from the input graph.

## Rebuild

Install Matplotlib and CairoSVG, including Cairo's native library. Then run from
the repository root:

```sh
python3 papers/pcp/figures/render.py
```

On a Homebrew installation where Cairo is not discovered automatically, prefix
the command with `DYLD_FALLBACK_LIBRARY_PATH=/opt/homebrew/lib`. The script writes
editable SVG and 300-dpi or equivalently sized PNG beside the owning manuscript.
The manuscript uses PNG so Pandoc/Tectonic and the web reader share the same
rendered bytes. No font download or network access occurs during rendering.
Rebuild the PDFs with the [paper renderer](../README.md#render-the-pdfs), then
inspect the figures at page width and in the reader, including image zoom on a
phone. Successful compilation alone does not establish legibility.

## Adapted implementations

- Proof map: the two-layer card component, title/subtitle hierarchy, arrow
  marker and rounded orthogonal connectors from
  [diagram-design's architecture example](https://github.com/cathrynlavery/diagram-design/blob/f4547ee95f88e5b28a52517feff6b6c11cc657f9/skills/diagram-design/assets/example-architecture.html).
  The web-stack labels, decorative background and numerals were removed;
  dimensions, serif type and relationships were adapted for the paper.
  The [MIT notice](diagram-design-LICENSE) is retained.
- Matrix: the `cellText`/`colLabels` table construction from
  [Matplotlib 3.10.0's table example](https://github.com/matplotlib/matplotlib/blob/v3.10.0/galleries/examples/misc/table_demo.py).
  Its stacked bars and numerical series were replaced by the source-checked
  table-use relation. Row names occupy an explicit first column so they cannot
  be clipped behind data cells. The [Matplotlib notice](matplotlib-LICENSE) is
  retained.

Both figures preserve their meaning in grayscale. The shaded column is also
identified by number and words. Figure captions state the limits; the source
and reader links carry the formal declarations.
