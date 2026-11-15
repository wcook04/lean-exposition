# Specialist PDF visual and link review

Status: PASS. All 11 pages pass visual inspection; all 10 companion-link annotations now resolve structurally, including all eight section destinations.

Reviewed source: `work/lean-exposition/papers/pcp/short/paper.md`, SHA256 `72d165920fbc02aa7b58bc626c3e6899cd2f099089a80cb10efa792279127577`.

Final reviewed PDF: `work/pdf-build/short/paper.pdf`, SHA256 `db3ca0fe7ef9b4a2bf3df977f5e6e6520d09f2c19d674f8c5dda51dbeaa00d4d`; 11 US-letter pages, 612 × 792 points. Native Pandoc/Tectonic article output, 11-point Latin Modern text/math, one-inch margins. The generated TeX template and parent-owned renderer were retained; no manuscript or renderer edits were made by this reviewer.

Method: read the PDF skill in read-only mode and the visual-explanation-authoring canonical production/acceptance method. Opened every full-page PNG separately at 1102 × 1426 pixels (1.8× PDF scale, approximately 130 dpi), rather than judging only a contact sheet. Independently rerendered each page in memory and checked all 11 inspected PNGs pixel-for-pixel against this PDF; every comparison matched. Text extraction and span bounds were supporting checks only.

| Page | Content inspected | Visual result |
| --- | --- | --- |
| 1 | Title, author-credit subtitle, abstract, theorem, logarithmic seed formula | Pass: clear hierarchy; all mathematical glyphs readable; title and text inside margins. |
| 2 | Three-colouring equations, numbered display (1), grid-vanishing certificate | Pass: aligned equations and degree exponents; ordinary paragraph continues to next page without clipping. |
| 3 | Certificate identities, degree reduction, Boolean encoding, equations (2)–(7) | Pass: product/sum indices, blackboard-bold field glyphs and equation numbers readable. |
| 4 | Label transformations, two-query correction, weighted interpolation | Pass: fractions, subscripts and generator powers readable; section heading spacing sufficient. |
| 5 | Weighted grid sum, obsolete-test counterexample, Hadamard/BLR argument | Pass: dense text stays readable; large sums and superscripts do not collide. |
| 6 | Decoding constants, point-versus-line estimates, equations (11)–(13) | Pass: multiline displays and probability subscripts clear; bottom display above footer. |
| 7 | Nonuniform correction, equation (14), ZERO setup | Pass: fraction denominators and homogeneous-error notation clear; no overlapping lines. |
| 8 | ZERO inequalities (15)–(16), seven checks, equations (17)–(19) | Pass: long inequalities fit; section transition and bottom formula legible; no clipping. |
| 9 | Gap minimum (20), parameter family and resource estimates | Pass: large brace/minimum expression, powers and ceiling-log glyphs readable. |
| 10 | Query sum, explicit constants, runtime/reduction/converse, credits heading | Pass: large integer denominator, exponents and padding inequality fit; heading has following text. |
| 11 | Credits and five references | Pass: reference wrapping and punctuation readable; final page's unused lower space is normal. |

No visible clipping, overlap, missing glyph, black-square placeholder or unreadably small formula was observed. An independent scan found no replacement/square glyph markers and no text spans outside a page. These scans support, but do not substitute for, the actual image inspection.

## Navigation finding sent to the parent

All eight section-specific annotations from the specialist PDF to the long PDF have correct-looking `/GoToR` actions, but their named destinations do not exist in the initial long PDF. The target file contains 145 named destinations such as `section*.11`; its Markdown heading identifiers appear as LaTeX labels without corresponding PDF named destinations. Thus the issue is in destination generation, not the section text.

| Specialist page | Requested destination in long PDF | Initial generated heading destination |
| --- | --- | --- |
| 5 | `2-the-corrected-short-low-degree-test` | `section*.11` (long page 6) |
| 6 | `4-bivariate-agreement` | `section*.22` (long page 9) |
| 6 | `5-point-versus-line-soundness` | `section*.29` (long page 12) |
| 7 | `correcting-an-outer-value-at-a-prescribed-point` | `section*.62` (long page 24) |
| 8 | `checking-that-a-polynomial-vanishes-on-a-grid` | `section*.66` (long page 25) |
| 10, twice | `the-polynomial-time-implementation` | `section*.83` (long page 36) |
| 11 | `source-and-verification-account` | `section*.87` (long page 41) |

The plain relative link to `../long/reasoning-record.pdf` resolves to the existing 43-page companion. The plain link to `../expository/main.pdf` had no file at review time; the parent was still producing that companion.

Parent acknowledged the defect and is adding native header hypertargets aligned with the Markdown identifiers, then regenerating the PDFs. The final regeneration and recheck below closes this finding. This review did not test external websites or interactive clicks in a PDF viewer.

## Final regeneration recheck

The parent added explicit native header hypertargets, then regenerated all three companion PDFs. The specialist manuscript source hash is unchanged. Its final PDF hash is `db3ca0fe7ef9b4a2bf3df977f5e6e6520d09f2c19d674f8c5dda51dbeaa00d4d`; the initial inspected PDF was `787df62b09fe7b0a2b37275944913505d46a2e87cf6d5d50121a07bccf11d95a`.

All 11 final pages, rendered independently at the same 1.8× scale, are pixel-for-pixel identical to the 11 pages already inspected. The concatenated RGB pixel SHA256 is `2d9b3990ca3de72ff772c4c5a75a4a9f628e68817732f1f883133b1488743847` before and after. The refreshed PNGs also match the final PDF on every page. Therefore the repaired navigation preserves the accepted visual layout without an uninspected pixel change.

Every requested long-paper destination now appears in its PDF name tree, on the expected pages listed above. All eight section annotations resolve; the repeated runtime destination resolves for both annotations. The plain long-paper link resolves to its 43-page PDF, and the plain exposition link now resolves to its 18-page PDF. Total: 10/10 companion-link annotations resolve structurally.

Acceptance scope: complete visual review of the specialist PDF and structural validation of its companion-file and section targets. External-network link availability, final distribution-folder relocation, and interactive PDF-reader click behavior remain outside this read-only review.
