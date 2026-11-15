# Exposition PDF review

## Exact edition and method

- PDF: `work/pdf-build/expository/main.pdf`.
- SHA-256: `412ae4a82e7987c592b4b2e6dc7318119a4b2c44b3a9f9951ca6b1cc245409fb`.
- Accepted mathematical source: `papers/pcp/expository/main.md`, SHA-256 `2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`.
- Actual PDF count: 18 pages, confirmed with `pypdf`. Viewed every PNG `work/pdf-build/expository/pages/01.png` through `18.png`, sequentially, at the supplied 1102 × 1426 resolution. This was individual full-page inspection at readable scale, not a contact-sheet-only check.
- Read the PDF skill in read-only mode. No artifact authoring marker was run, and no manuscript or render source was edited by this reviewer.
- This supplements the mathematical/source review in `work/pcp-reviews/exposition-reader-review.md`. It is an AI editorial inspection, not a human comprehension study or new formal verification.

## All-page visual coverage

| PDF page | Inspected content and outcome |
| --- | --- |
| 1 | Title, audience, attribution, K4 motivation and dilution fraction. Legible type and hierarchy; no clipping. |
| 2 | Precise theorem, quantifiers, resource bullets, exhaustive-seed bound. Symbols and exponential formula are readable. The NP=PCP display is separated from its introductory sentence across the following page break. |
| 3 | NP=PCP display, mod-5 table, multivariate distance bound, interpolation entry. Table columns and all displayed symbols align. |
| 4 | Lagrange weights and grid extension, characteristic-two colour equations, residual matrix. Products, indices, hats and table rows are readable; no overlap. |
| 5 | Residual polynomials, ambient/grid distinction, grid certificate and added quotient-degree bound. All equations, including the bottom-page M definition, are complete. |
| 6 | Added degree-M consequence, two certificate identities, numerical M example, Question 1, point-line theorem. The two identities and constants render correctly. |
| 7 | Base-3 digit construction, arbitrary decoded-degree bound, generator definition. Superscripts and subscripts remain distinguishable. The weighted-test introductory sentence is split from its display on page 8. |
| 8 | Weighted-test equation, correction bound, binary-message word and distance argument. The eight-bit vector is complete. The BLR equation is split from its introducing line on page 9. |
| 9 | BLR test/count, Hadamard correction, Question 2 and cubic-label definition. The count 18/64, exceptional x=0 case and labels are readable. |
| 10 | Cubic-label caveat, Section 8, weighted labels, common decoded object and K/E/S/C constants. The aligned constants have correct grouping. Combined-theorem hypotheses continue at the top of page 11 after a final “and” on page 10. |
| 11 | Combined-theorem conditions and conclusion, outer-correction inequality, ZERO identities and correction-to-grid transition. All factors and denominators render faithfully. The random-label and refusal qualifications remain adjacent to the corrector bound. |
| 12 | Four primary objects/eight tables, seven tests, completeness capacity, soundness outline and start of quantitative argument. The list is intact. The error-budget subsection has several lines before the page break, rather than an isolated heading. |
| 13 | Full quantitative soundness repair. Verified the displayed difference threshold, the factor `(1+2C)(κ+2ε)`, the extra `2ε`, the root term `5D/(Q−1)`, all three field ratios, both `<1/16` conditions, and the strict contradiction using `3/8` and `3/16`. No lost factor, ambiguous fraction, clipped term or broken display. Question 3 follows cleanly. |
| 14 | Production parameters, address budget, honest capacity and field checks, bit sampling, concrete gap. The nested exponents and large gap denominator are complete and legible. |
| 15 | Repetition, tableau reduction, mismatch flags and three-clause OR equations. Negations and OR symbols render correctly. The NAE pair is separated from “such that” by the following page break. |
| 16 | NAE pair, colouring gadget, Questions 4–5, Answers 1–4. New Question 5 is complete and readable. Answer 4's first sentence is alone at the page bottom, with its remaining explanation on page 17. |
| 17 | Rest of Answer 4, Answer 5, reconstruction task, old-test counterexample, finite-field arithmetic. The fresh task's `7/32<12/32=3/8` and equality boundary are intact; the fourth-power calculations and field-family exponents are readable. |
| 18 | Sources, evidence boundary and further reading. Attribution and verification limitations remain visible; no placeholder citations, broken glyphs or unexplained tool tokens. |

## Findings sent to the parent

No mathematical rendering defect was found: no missing or clipped equation terms, table corruption, font substitution boxes, overlap, margin overflow or absent page numbers. The repaired Sections 8–9 can be read continuously in the PDF, and their exact quantities match the accepted source.

One repeated layout issue remains in this PDF edition: displayed equations start a page while their introducing sentence ends the preceding page. Exact transitions are 2→3 (NP=PCP), 7→8 (weighted test), 8→9 (BLR), 10→11 (combined-theorem hypotheses), and 15→16 (NAE pair). These are recoverable on a page turn, but they unnecessarily interrupt the inference. Requested render-only correction: keep the final introducing line with the following display. This does not call for changing the mathematical manuscript. The split of Answer 4 across 16→17 is a smaller related paragraph-placement issue.

## Link inspection

Inspected PDF annotations with `pypdf` on pages 1, 10, 11 and 18. Companion links are remote-PDF actions to `../long/reasoning-record.pdf` and `../short/paper.pdf`, with a page-one fit destination, rather than stale Markdown paths. Public references include the specified arXiv v2, pinned Lean repository, original PCP papers, BLR DOI, textbook and reading guide. This checks stored destinations, not a live browser click or the final package's filesystem placement.

## Disposition

Mathematical legibility: accepted for this exact PDF. Layout: requested one targeted correction to the repeated display introductions before final delivery. Awaiting the parent's rerender; any successor PDF needs its own hash and page review. No claim is made that the existing 18 page images describe a later file.

## Successor PDF: final acceptance

The parent applied a render-only keep-display-leads filter. The successor PDF at the same path has SHA-256 `03e5b8db4f8008f0cd4777b343880fe83056c8cf6c7a56e4c87c532ceb513b2f`. The mathematical Markdown source remains exactly `2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`; both hashes were independently read back after inspection.

Verified 18 PDF pages and 18 newly generated page PNGs, all newer than the successor PDF before starting the visual pass. Viewed every new page 01–18 individually at the same 1102 × 1426 reading resolution. Since the render change reflowed later material, this was a complete second visual pass rather than only sampling the initially defective page boundaries.

All five reported equation-introduction splits are corrected. The NP equality now has its final introducing line on page 3; the weighted test has its introducing lines on page 8; the BLR test has its complete introducing sentence on page 9; the combined theorem's hypothesis and lead now share page 11; and the NAE pair and its lead share page 16. Answer 4 is now intact on page 17. Normal continuing paragraphs remain across some boundaries, including Answer 2, without isolated display equations or isolated answer labels.

The central quantitative argument is especially clear in the successor: the difference threshold, ZERO inequality, three field requirements, two small-error requirements and strict contradiction all fit on page 13. Rechecked their actual glyphs, factors and fraction grouping. The complete source theorem, both numerical tables, grid certificates, code examples, production parameters, repetition bound, OR/NAE reduction, new exercise/answer, old-test counterexample and source statements remain readable throughout. No clipping, overlap, missing symbol, broken table, altered mathematical expression or new display-lead defect was observed in any of the 18 pages.

Rechecked all remote-PDF annotations after rerender: the stored companion destinations remain `../long/reasoning-record.pdf` and `../short/paper.pdf`, with no stale Markdown target in those actions. The parent separately reports a full link check; this review's independent check remains the stored PDF annotation destinations.

Final disposition: **accepted for mathematical legibility and layout at PDF hash `03e5b8db4f8008f0cd4777b343880fe83056c8cf6c7a56e4c87c532ceb513b2f`**. No further manuscript or render change is requested by this review. Acceptance does not extend to later bytes without readback and does not establish human learning or formal proof coverage beyond the separate evidence records.
