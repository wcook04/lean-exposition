# Long manuscript preservation receipt

Final source: `work/lean-exposition/papers/pcp/long/reasoning-record.md`.

- Original SHA-256: `cc9fc82c4525c6977040666e2f8fe6a0dfc3ca4514af49b16b81d007011f42bd`.
- First humanized SHA-256: `1d9cf0f3d38363daaad2f363804372c3b8534de23aeb7a0638bc5485debd3736`.
- Final successor SHA-256: `1d09db7bfda9d8f7cb2a4b8cf14421c8bf8b2edb7d0391655fb8715c1dce1588`.

The first pass made bounded prose edits, added point-of-use classical attribution and edition distinctions, and moved the full explanatory-author credit to the final source account. The paragraph ledger retains all original decisions and first-pass revised text. `literature-moves.md` records the actual primary passages used. The proposal to loosen the named `GoodNodes` condition was rejected; that mathematical hypothesis remains unchanged.

Rendered review then found thirty orphaned citation-label fragments left by removal of repeated “Lean:” prefixes. The sole successor change makes those labels grammatical sentences and joins paired references. `citation-repair.json` contains exact replacements and binds both hashes. It changes no mathematical expression, URL, passage marker, heading or proof claim. No further editorial cycle or score target was introduced.

## Mechanical preservation

`preservation-check.json` compares the original with the final successor. All 170 displayed mathematical blocks are byte-for-byte identical. All original inline mathematics remains; the only added inline expressions are the characteristic `p` and the explicit Friedl–Sudan condition `q-q/p-1\ge d`. All original URLs remain; eight additional URL occurrences provide source attribution or the readable immutable source link. The ordered 144 passage markers, 33 headings, tables and front matter are unchanged. `preservation-check-first-pass.json` preserves the earlier result rather than overwriting its historical identity.

These mechanical checks complement the mathematical review; they do not establish mathematical equivalence by themselves. The independent AI foundations reviewer accepted the first humanized freeze after checking the mathematical contract and added citations against retained primary passages. The same reviewer separately compared the bounded citation-only successor with the accepted freeze and carried the mathematical-preservation acceptance to the final hash. The exact disposition is recorded in `work/pcp-humanizer/mathematical-preservation-review.md`, section “Long citation-only successor”. No human review is claimed here.

## Complete final reading

The revising agent then read the entire final 1,931-line source sequentially, including the bibliography and reference definitions. `final-sequential-read.md` gives actual coverage, the reread of truncated output, and located observations. This was a warm final reading. No further manuscript change was needed, and the final hash remained stable.

## Register measurements

The installed register tool profiled two native-TeX extended-proof regions from independent works. Paragraph extraction was inspected; damaged PDF candidates were excluded from numerical comparison while remaining qualitative sources. Matched manuscript regions exclude YAML, link definitions, source-account apparatus and bibliography. The final successor was compared with the original using that same fixed profile. `register-metrics-public.json` contains only aggregate corpus numbers and before/after manuscript numbers, without reference-corpus excerpts or specimen text.

For orientation, status vocabulary changed from 9.73 to 6.88 per thousand prose words, meta-narration from 0.67 to 0.44, contrast markers from 1.34 to 0.74, and negation from 8.02 to 7.17. Mean paragraph length changed from 44.56 to 44.81 words and mean sentence length from 13.23 to 13.28. These are diagnostics, not targets. Necessary mathematical negations, exact quantifiers and uneven proof lengths were retained. The two-work corpus provides limited statistical evidence; no authorship or quality conclusion is inferred from a score.

## Delivery boundary and archive

This pass did not rerun Lean, change source declarations, edit graph or passage mappings, render or publish the reader, or commit. The parent owns the successor rendering, mapping and bundle binding. The independent reviewer subsequently inspected all 43 pages of the successor PDF and accepted the rendered result; that separate receipt is `work/pcp-humanizer/long-pdf-review.md`, section “Successor final visual disposition”. It binds the final source hash above to PDF SHA-256 `87d000671158d1161c7e7f2ca4dbbad77dfce9775c95810e8637ce0553481e2b`. This receipt reports that separate review without claiming that the revising agent performed it.

Public-safe audit files are `paragraph-review.json`, `review-notes.md`, `preservation-check.json`, `preservation-check-first-pass.json`, `citation-repair.json`, `corpus-manifest.json`, `register-metrics-public.json`, `final-sequential-read.md`, `literature-moves.md`, and this receipt. They contain metadata, original manuscript prose, original review prose and numerical diagnostics, not protected third-party proof excerpts. Keep `corpus/`, PDFs, scans, extraction dumps, full comparison files with specimens, and local authoring scripts private.
