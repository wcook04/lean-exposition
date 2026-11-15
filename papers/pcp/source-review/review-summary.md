# PCP source and manuscript reviews

## Prose and literature revision

The three papers have received paragraph-level prose reviews and closer
comparison with the cited literature. All three revised sources are frozen and
independent mathematical preservation is accepted. Final sequential source
reads and all 72 PDF-page reviews are complete. A separate reader-correspondence
review found overly broad paragraph-to-Lean associations, including use of a
downstream weighted-proximity theorem for exact-line characterization and an
unrelated row-decoding fallback in Hadamard/correction passages. Those mappings
were corrected against the pinned source statements and rechecked. The
manuscripts and reviewed PDFs were unchanged by that repair.

| Account | Accepted source prefix | Accepted PDF prefix | Pages |
| --- | --- | --- | --- |
| Full argument | `1d09db7bfda9` | `87d000671158` | 43 |
| Specialist | `c1f177680bbe` | `3dcc5fa9cadb` | 11 |
| Exposition | `4fc575eb9827` | `8827a957fa76` | 18 |

The complete source and PDF hashes are bound by the
[revision archive](humanizer/README.md). Its records distinguish paragraph
decisions, final sequential reading, descriptive comparisons with the literature,
independent mathematical preservation and rendered-page inspection. The
[canonical](humanizer/canonical-pdf-check.json) and
[relocated](humanizer/delivery-pdf-check.json) PDF packets have identical hashes;
all 20 companion annotations resolve. Both [finite-example scripts](humanizer/ordinary-checks-rerun.json)
passed at the final source hashes. The [current source-package suite](humanizer/package-tests.json)
ran 710 tests, OK with two opt-in pinned Lean fixtures skipped.

The reader provides selected source entry points, not an exhaustive matching of
every mathematical statement. Its present format cannot anchor a quote to
display mathematics, so formula-only direct links are omitted there; the
declarations remain indexed and the manuscripts retain their source hyperlinks.
Canonical passage mappings can cover those complete passages under their own
contract. The repaired reader retains 46 full-argument, 12 specialist and 16
exposition links. The [algebra](humanizer/reader-algebra-correspondence-review.md)
and [theorem/specialist](humanizer/reader-theorem-correspondence-review.md)
receipts distinguish bounded source-data review from the coordinating agent's
rendered-reader inspection. The [reader refresh receipt](humanizer/reader-refresh-review.md)
lists the selected data hashes and further omissions, including the eight-table
structure and quotes that could not be bound reliably. It records 112 Python
tests, 11 web source checks and 380 browser-journey checks passing. These records
do not claim a complete formal audit; deployment evidence remains separate.

The [corrected mapping review](humanizer/mapping-review-corrected.md) and
[bundle receipt](humanizer/bundle-validation-corrected.json) bind the final
canonical package, ZIP prefix `8ac76496d9d9`. Assembly, bundle checking, export,
all seven payload hashes and ZIP integrity passed. Consumer queries exercised
direct matches, recorded prerequisites and source neighborhoods; the receipt
retains an initial failed guessed-source query and its correction. Paper states
remain `draft`, extraction is `not_run` and semantic certification is false.

The [pre-correction bundle](humanizer/bundle-validation.json) passed structural
validation at final long-source hash `1d09db7`. That did not establish semantic
matching. Its three mappings are retained in the
[superseded mapping snapshot](humanizer/history/pre-correction-mappings/README.md).

The [acquisition record](acquisition-status.json) separately reports that 21 of
the corrected paper's 24 bibliographic entries were obtained or already
available, including the implementation and existing Lean repositories.
DeMillo–Lipton, Ore and Schwartz remain unacquired for the recorded access
reasons. The retained-item inventory is not a count of bibliography coverage;
it also includes versions and supplementary sources.

The records below concern the first edition. Its reports remain byte-identical
historical evidence; they do not certify the revised source or PDF bytes. The
[initial assembly](assembly-initial.json) and
[initial archive index](review-archive-initial.json) are retained alongside the
[current revision lineage](assembly.json). Release and deployment evidence is
owned separately by [the release-check record](release-checks.json).

## First edition: historical source and manuscript reviews

The [three papers](../README.md) were reconstructed from the corrected primary
paper, earlier literature and Troy Lee's Lean sources at
`a0ce13ed0fa264f051c1278e039596ce65557fa4`. Separate AI agents reviewed the
mathematical chapters and specialist paper; another agent read the exposition
sequentially and attempted its exercises. These are source-based mathematical
and reader reviews. They are not a fresh Lean build, an exhaustive audit of
every dependency, independent human expert acceptance or a human learning study.

**Completed for the recorded editions:** bounded AI source and reader review,
finite example checks, bundle validation and all-page PDF visual review. The
individual reports retain the exact revisions they reviewed, including
successor-PDF rechecks after rendering repairs. The graph still reports
`extraction_status: not_run` and `semantic_certification: false`.

The [release-check record](release-checks-initial.json) binds the subsequent fresh-clone
installation and bundle reproduction to the tested commit. It also records the
successful Proof Reader deployment and byte-for-byte comparison of all three
published reading copies with the inspected build.

## Review findings and dispositions

| Account | Finding and correction | Retained review |
| --- | --- | --- |
| Algebra chapter | Added the crossing lemma's positive-degree and field-size hypotheses; replaced wording that could imply unnecessary statistical independence. The reviewer rechecked both changes. | [Algebra mathematical review](algebra-math-review.md) |
| Binary chapter | Added honest primary and auxiliary tables to ZERO completeness, separated generator-test nodes from the corrector's `GoodNodes`, and made the derived expression's polynomiality and degree hypotheses explicit. The reviewer rechecked all three. | [Binary mathematical review](binary-math-review.md) |
| Final theorem chapter | Specified palette vertices for constant literals in the colouring gadget and corrected two source destinations. The reviewer rechecked the construction and links. | [Theorem mathematical review](theorem-math-review.md) |
| Specialist paper | Corrected the domain of the binary label in its composition identity and made the coordinate conversion explicit. The final source revision was rechecked. | [Specialist mathematical review](specialist-math-review.md) |
| Worked exposition | Added the quantitative soundness budget, its strict contradiction, compatible capacity and field bounds, certificate-degree calculation, generator definition and actual prefix-mismatch clause reduction. The reviewer rechecked the changed passages and connected proof routes at final source revision `2e2333ca`. | [Sequential reader review](exposition-reader-review.md) |
| Historical scalar test | Accepted the stated infinite family against the old v1 unit-weight scalar test, with its source and scope boundaries. This is not a counterexample to v2, the whole PCP theorem or the pinned Lean theorem. | [Counterexample review](old-test-counterexample.md), [disposition](counterexample-disposition.json) |

The accepted exposition source hash is
`2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`.
Its reviewer read the original draft in full, then the revised passages and
their connected proof routes. This was not a fresh blind reading of the whole
successor edition. The exposition review records that a preliminary outline command exposed the
opening lines of its exercise answers. Later attempts preceded the full answers,
but were not pristine blind attempts. It also records the model's prior PCP
knowledge. Preserving that limitation is part of the review, not evidence of
human comprehension. A new changed-budget exercise was attempted before its
answer was supplied; the report preserves the response and the prior assistance.
The [exposition authoring record](exposition-authoring.md)
and [specialist authoring record](specialist-authoring.md) explain the chosen
prerequisites, worked examples and proof omissions.

The final rechecked chapter hashes are recorded in their reports and in
[the initial assembly record](assembly-initial.json). The first long manuscript combines those
chapters; its full-file hash is distinct from any chapter hash. The
[mapping review](mapping-review.md) owns passage-to-source correspondence and
its subsequent revisions. No review is silently extended to text it did not see.

## Evidence and ordinary computations

The [review archive index](review-archive.json) records byte hashes for copies of
the independent reports, authoring records and source evidence. These copies
retain their original paths and author-turn status wording. Those historical
paths are provenance, not commands to run in a fresh checkout. This summary
separately reports later integration state.

The chapter evidence lists exact source declarations and public locators:
[algebra](algebra-evidence.json), [binary](binary-evidence.json),
[theorem assembly](theorem-evidence.json), and [specialist selection](short-evidence.json).
These authored records do not add kernel-checked statuses or inferred Lean
dependency edges to the [curated evidence graph](../../../examples/pcp/evidence-graph.json).
The graph's `supports` edges are authored proof-stage navigation. A source-level
signature can retain implicit variables from a surrounding Lean section; it
must not be treated as an independently elaborated type.

On 15 November 2026, both current ordinary Python example programs were rerun
and their stdout matched the retained outputs exactly. The
[ordinary-check record](ordinary-checks.json) binds the executed script hashes,
including expanded checker revision `b1c375fa`, to their output hashes:

```sh
python3 papers/pcp/expository/check_examples.py
python3 papers/pcp/expository/check_exposition_examples.py
```

Run these from the repository root, without Python's `-O` option. The
[initial output](../expository/examples-output.txt) covers the finite weighted
interpolation, old-test example, Hadamard correction, grid, colour and repetition
calculations. The [expanded output](../expository/exposition-examples-output.txt)
covers the additional teaching examples, prefix-mismatch flags and strict
error-budget comparison. Their small fields do not satisfy all
production parameters of the full verifier. The infinite counterexample family
has a separate symbolic proof and source review.

The existing CLI accepted `examples/pcp/evidence-graph.json`, while explicitly
reporting `extraction_status: not_run` and `semantic_certification: false`.
The documented `assemble` and `check-bundle` options were checked against the
installed command. Structural graph validation, source-byte matching, finite
computations, mathematical review and rendered-reader inspection answer
different questions. The [papers guide](../README.md#assemble-a-reader-bundle)
contains the reproducible bundle commands.

The [final bundle-validation record](bundle-validation.json) reports successful
assembly, `check-bundle`, export, ZIP integrity and exact agreement with all seven
payload hashes. The three paper states remain `draft`, with
`extraction_status: not_run` and `semantic_certification: false`. These are
intentional evidence boundaries, not failures concealed by packaging.

The coordinating agent reports the full Python suite result as **710 tests run,
OK with 2 skipped**, alongside 11 web source checks and 380 reader journeys.
It also inspected the reader's initial view, repaired header, quantitative
soundness view and source display, including exact-quote checks. These exercise
the package and reader; they do not supply a fresh full Lean run. The
documentation archive did not rerun those suites.

## First edition: historical PDF and reader inspection

| PDF | Full-page visual review | Final PDF SHA-256 |
| --- | --- | --- |
| [Full argument](../long/reasoning-record.pdf) | [43 pages, including regenerated successor](long-pdf-review.md) | `41ba323b4241960a1631a987b845bb7d062179e91a27f730fa19beb7ab215264` |
| [Specialist paper](../short/paper.pdf) | [11 pages; final pages match the inspected rendering](short-pdf-review.md) | `db3ca0fe7ef9b4a2bf3df977f5e6e6520d09f2c19d674f8c5dda51dbeaa00d4d` |
| [Worked exposition](../expository/main.pdf) | [18 pages, rechecked after display-introduction repair](exposition-pdf-review.md) | `03e5b8db4f8008f0cd4777b343880fe83056c8cf6c7a56e4c87c532ceb513b2f` |

The reviewers inspected all 72 pages individually at reading scale. The
coordinating agent additionally inspected exposition pages 1 and 13, specialist
page 1 and full-argument page 3. The
[companion-link check](companion-link-check.json) passed all 19 remote-PDF
annotations, including the named long-paper destinations. The same portable
checker was rerun against the PDFs in this checkout and returned the same
results and hashes. The [relocated delivery-packet check](delivery-pdf-check.json)
also agrees on all three hashes and all 19 annotations. Preserve the three
relative folders when relocating them.

These records establish the stated visual inspection and structural navigation
checks for these bytes. They do not claim live availability of every external
reference, exhaustive interactive clicking in every PDF application, human
learning outcomes or formal proof certification. The separate reader inspection
and source-display checks have the scope reported above.

## Sources, credit and redistribution

The principal reference is Amireddy, Behera, Srinivasan, Sudan and Willumsgaard,
[*A Simple Algebraic Proof of the PCP Theorem*, arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2),
22 October 2026. The code is
[Troy Lee's pinned formalization](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4).
Its [PCP README](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp/README.md)
describes the revised SOSA route and formal departures. It does not establish
that its mathematical input is byte-identical to the public v2. The manuscripts
retain differences in the Hadamard test, label domains, sampling and concrete
parameters rather than identifying nonidentical statements.

The [source inventory](sources.json) records exact editions, hashes, public URLs
and observed rights. The primary v1/v2 papers carry CC BY 4.0; several earlier
papers have restricted or unestablished redistribution rights. Downloaded PDFs
remain in the private working annex and are not copied into this package.
Reference-only records and public links allow inspection without treating
access permission as redistribution permission. The source code retains its
upstream authorship and Apache-2.0 attribution.

No whole-library `.olean` extraction, axiom audit or Comparator replay was
performed for this reconstruction. A source read or a small available interface
object does not establish any of those outcomes. The original authors' results,
the upstream formalization, and this task's explanatory reviews remain distinct.
