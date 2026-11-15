# Prose and literature revision

This archive records a paragraph-level revision of all three PCP papers. The
purpose is to make the prose more precise and the literature attribution more
useful while preserving the mathematical argument. A numerical style score is
not a measure of correctness, authorship or reader comprehension.

Current status: all three sources are frozen, all three final source reads and
independent preservation reviews are complete, and all 72 new PDF pages have
passed visual review. A separate reader-correspondence review found overly
broad passage mappings; they were corrected and rechecked against the pinned
source statements. The [corrected canonical bundle](bundle-validation-corrected.json)
passed validation. The earlier
[bundle validation](bundle-validation.json) records a structural success, not
acceptance of those semantic associations. All three paper states remain
`draft`, extraction is `not_run` and semantic certification is false.

| Paper | Paragraph decisions and reading | Descriptive comparison and preservation |
| --- | --- | --- |
| Full argument | [Block-by-block decisions and successor repair](long/paragraph-review.json); [complete final warm reading](long/final-sequential-read.md) | [Literature moves](long/literature-moves.md); [matched-region metrics](long/register-metrics-public.json), [corpus metadata](long/corpus-manifest.json); [final preservation receipt](long/final-preservation-receipt.md) |
| Specialist | [81 paragraph decisions, 23 changes](short/paragraph-review-final.json); [complete revised-source reading](short/sequential-review.md) | [Literature and register decisions](short/literature-register.md); [before](short/before-profile-public.json), [after](short/after-profile-public.json), [reference metadata and numeric profile](short/profile-public.json); [preservation](short/preservation-checks.json) |
| Exposition | [158 paragraph decisions, 38 changes](expository/paragraph-review.json); [complete revised-source reading](expository/sequential-review.md) | [Teaching-source comparison](expository/literature-review.md); [matched-region measurements](expository/measurements.md); [metrics-only projection](expository/metrics-summary.json); [preservation](expository/fidelity-receipt.json) |

The logs retain deliberate decisions to leave paragraphs unchanged. Mathematical
displays, tables and theorem conditions are protected material, not prose to
shorten for a metric. The author records and the independent reviews identify
which complete texts or changed passages were read and whether the reviewer had
already seen the argument or exercises. None is a blind human learning study.

The two portable finite-example scripts were [rerun against the final manuscript
hashes](ordinary-checks-rerun.json) and passed. Their calculations test the
displayed small examples; they do not certify the general soundness argument.
The coordinating agent also reran the [source-package suite](package-tests.json):
710 tests, OK with two opt-in Lean tests skipped. No runtime code changed in this
revision. These software checks are separate from the correspondence review.

The [literature-grounding audit](literature-grounding-audit.md) identifies the
sources and the scope of its findings. The exposition's
[independent preservation and sequential reader review](exposition-preservation-reader-review.md)
records its accepted source edition. It retains the history of the review,
including earlier pending stages, rather than rewriting them as uninterrupted
acceptance.

The [independent long/specialist review](mathematical-preservation-review.md)
also records the precise literature boundaries. In particular, the unrestricted
linearity-distance statement is cited in the modern paper's Appendix B,
Theorem B.1; BCHKS's Theorem 1.2 has its own distance range. BLR remains credited
for the test. The weighted-test antecedents do not remove the present
generator/weight conditions, and the explicit agreement constants belong to
the formalized formulation rather than to an implicit-constant historical
statement. Those qualifications were preserved while adding citations.

The [bibliographic graph review](graph-review.md) records four new reference-only
citations and their exact source editions. These are attribution relationships,
not extracted Lean dependencies or claims of identical formal statements. The
[specialist PDF review](short-pdf-review.md) and
[exposition PDF review](exposition-pdf-review.md) identify the new renders they
inspected, as does the [long successor PDF review](long-pdf-review.md).
[Canonical](canonical-pdf-check.json) and
[relocated](delivery-pdf-check.json) packet checks agree on all three PDF hashes
and all 20 companion annotations. Those PDF links are distinct from the
paragraph-to-Lean associations checked in the separate correspondence review.

The [historical mapping snapshot](history/pre-correction-mappings/README.md)
preserves the three pre-correction mapping JSONs exactly as captured in bundle
`81ce6157`. The [initial mapping report](history/mapping-review-initial.md) and
[pre-correction successor report](history/mapping-review-pre-correction.md) are
also retained byte-identically as superseded evidence. Structural package
validation did not establish that each linked theorem directly matched its
passage. The [corrected mapping review](mapping-review-corrected.md) identifies
local source statements and retains the distinction between direct and
recorded-prerequisite matches. The bounded
[algebra](reader-algebra-correspondence-review.md) and
[theorem/specialist](reader-theorem-correspondence-review.md) rechecks record
their accepted source-data scope separately from rendered-reader inspection.
Reader links are selected entry points. The current reader cannot quote-anchor
display mathematics, so formula-only direct links are omitted there while the
declarations remain indexed and manuscript source hyperlinks remain available.
Canonical whole-passage mappings follow a separate contract and can include
those mathematical displays. Neither surface promises exhaustive statement
matching. The final selection has 46 full-argument, 12 specialist and 16
exposition links. The [reader refresh receipt](reader-refresh-review.md) records
the exact omissions, final source/data hashes, validation and screenshot scope.
It also records the omitted eight-table structure and quotes the reader could
not bind reliably; their pinned sources and manuscript links remain available.
The reader's 112 Python tests, 11 web source checks and 380 browser-journey checks
passed. Deployment evidence is maintained separately in the release record.

The comparisons use selected regions suited to each paper's genre. In particular,
the exposition compares its PCP opening and Hadamard teaching passages with
Arora–Barak's January 2007 textbook draft; the specialist comparison uses
research-paper passages. Extraction and sample-size limitations are recorded.
Paragraph or sentence segmentation from a poorly extracted PDF is not treated
as a reliable measured property of its author's prose. Whole-document figures
are context where the comparison regions differ.

The specialist profiles use [portable locator projections](short/profile-projection-provenance.json): six local-path fields changed, while all numeric data and manuscript specimens are identical. Raw originals remain privately retained and hash-bound.

The public files contain original-manuscript paragraph logs, audit prose,
numerical profiles and source locators. Third-party PDFs, page images, OCR dumps,
long source excerpts and copied reference texts remain outside this repository.
The exposition's public metrics file is an explicitly labelled projection;
the omitted teaching excerpts are not silently presented as absent evidence.

The [initial assembly](../assembly-initial.json),
[initial archive index](../review-archive-initial.json) and
[initial review summary](../review-summary-initial.md) preserve the first edition.
The [current assembly record](../assembly.json) describes revision of an already
assembled long manuscript. The [current review index](../review-archive.json)
binds each public record to its bytes and distinguishes its edition.
