# Revised specialist PDF review

Status: visual PASS for every page of this edition. Companion-link validation is partially pending the parent’s combined build; the expected temporary absence of the new long PDF is not classified as a defect.

## Artifact identity

- Manuscript: `work/lean-exposition/papers/pcp/short/paper.md`.
- Manuscript SHA256: `c1f177680bbe01f2e4b7bdee82cd9fedf276cecb9ae0f258a2b6e5fe3115c377` (matches the frozen revision supplied by the parent).
- PDF: `work/pdf-build-humanized/short/paper.pdf`.
- PDF SHA256: `3dcc5fa9cadbbd3f3343ba8f2bd83cf20cad22d8282faf0610aa3f4d06789cf5`.
- Length and format: 11 pages; US letter, 612 × 792 points; native Pandoc/Tectonic article renderer, 11-point Latin Modern text and mathematics with one-inch margins.

This is a fresh review of the revised PDF, not an extension of the earlier edition’s approval. The old receipt at `work/pcp-reviews/short-pdf-review.md` was left unchanged.

## Method and page observations

Applied the already-read PDF skill in read-only mode and the visual-explanation-authoring production/acceptance method. Opened all 11 newly rendered page images individually at 1102 × 1426 pixels (1.8× PDF scale, about 130 dpi). A contact sheet was not used as a substitute for reading-scale inspection. Independently rendered every page from this PDF in memory: all 11 inspected PNGs match the new PDF pixel-for-pixel. The SHA256 of their concatenated RGB pixels is `13e741e73aa39a9693a5bb079e4bd775c1e9845b04ec47c85b61e8b0d142bb65`.

| Page | Actual content inspected | Finding |
| --- | --- | --- |
| 1 | Title, revised abstract, theorem, seed formula, historical attribution and encoding overview | Pass. Title hierarchy and mathematics are clear; added citations wrap inside the text width. |
| 2 | Companion-paper paragraph, colouring equations, grid vanishing and identities (1)–(2) | Pass. The three stacked colouring equations are legible; certificate identities fit above the footer. |
| 3 | Degree-reduction and Boolean-value encodings, displays (3)–(7), new source references | Pass. Sum/product indices, superscripts and labels are readable; citations do not crowd equations. |
| 4 | Label transformations, correction identity and weighted test, displays (8)–(10) | Pass. Fractions, generator powers and the final double sum fit; no clipping at the page bottom. |
| 5 | Weighted-test literature, obsolete-test calculation, BLR/Hadamard discussion | Pass. Added multi-author citations and longer paragraphs wrap normally; inline accents and formulas display correctly. |
| 6 | Constants and outer decoding, point-versus-line literature and probability estimate | Pass. Long probability display and explicit constants are readable. The final sentence introduces a display on the next page without lost content. |
| 7 | Display (13), nonuniform correction, bound (14), ZERO setup | Pass. Header spacing, fractional bounds and probability notation are clear; paragraph continuation remains readable. |
| 8 | ZERO inequalities (15)–(16), section 6, consistency check and (18) | Pass. Long inequalities fit the column; equation labels and section heading do not overlap body text. |
| 9 | Constraint inequality (19), gap minimum (20), concrete parameters and seed estimates | Pass. Large braces, fractions, nested exponents and ceiling-log glyphs remain legible. |
| 10 | Query sum, explicit rejection gap, implementation/reduction/converse | Pass. Large integer denominator and polynomial-padding inequality fit; margins and footer are clear. |
| 11 | Revised credits and all nine references | Pass. Every reference is present and readable. Hanging-number layout, author accents, italic titles, page ranges and the longer source/version notes wrap cleanly; the last reference remains well above the footer. |

No clipping, overlap, missing glyphs, black-square placeholders, cut-off formulas or unreadably small mathematical text were observed. Supporting extraction found no replacement/square glyph markers and no text spans outside the page bounds. These scans supplement the actual image inspection.

## Companion links

The new specialist PDF contains 11 companion-link annotations: one plain long-paper link, one plain exposition link, and nine section-specific long-paper annotations (some wrapped link text produces repeated annotations for the same destination).

At review time, `../expository/main.pdf` resolves to the new 18-page companion. The new `../long/reasoning-record.pdf` is not present yet because its rendering is still in progress. The parent explicitly owns the combined check after that build. Therefore these ten long-paper annotations remain pending, without importing the old edition’s destination check or treating a planned temporary absence as a new failure.

The requested long-paper section names are:

- `2-the-corrected-short-low-degree-test`;
- `4-bivariate-agreement` (two annotations);
- `5-point-versus-line-soundness`;
- `correcting-an-outer-value-at-a-prescribed-point`;
- `checking-that-a-polynomial-vanishes-on-a-grid`;
- `the-polynomial-time-implementation` (two annotations);
- `source-and-verification-account`.

Scope: complete visual/layout review of this specialist PDF. Mathematical preservation is covered by the separate accepted preservation review. No manuscript or renderer edits, external-network link checks or interactive PDF-viewer click tests were performed by this reviewer.
