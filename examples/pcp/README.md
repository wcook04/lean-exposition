# Algebraic PCP evidence graph

Read the [PCP papers guide](../../papers/pcp/README.md) for the full argument,
specialist paper and exposition with worked examples. The
[review summary](../../papers/pcp/source-review/review-summary.md) links the
mathematical reviews and distinguishes them from finite computations and
structural package checks.

`evidence-graph.json` is a curated map of the source at
[troyjlee/tcs-formalizations commit a0ce13ed](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4),
full revision `a0ce13ed0fa264f051c1278e039596ce65557fa4`, alongside the corrected
paper [arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2) and selected earlier
sources. The forward theorem, concrete converse and reference NP equivalence
are separate selected goals. The declaration nodes contain source-level
signatures and source lines, with formal hypotheses intact; ordinary claim
nodes identify the separate finite computations and old-test counterexample.
The preceding `variable` lines are an aid to source navigation, not an elaborated
binder list: declarations can cross section boundaries and lines can continue.
Consult the linked source and an actual elaborated type for exact implicit
quantification. No declaration has fresh `kernel_checked` status.

All 29 `supports` edges are authored proof-stage navigation. They are not extracted Lean expression dependencies or individually certified premise-discharge applications. In particular, an edge to a conditional intermediate result does not establish that all its hypotheses have been supplied for the same objects. The graph records a proof outline, not a complete verified dependency extraction or a mathematical review. Some source-level declarations have prior section variables; the boundaries explicitly retain that limitation. The ZERO lower bound is not asserted positive without parameter hypotheses. The paper citations identify related material, while node boundaries and the pinned repository's `docs/pcp/README.md` identify nonidentical statements and algorithms.

The hash-bearing sources are reference-only. Lean sources resolve in the pinned checkout and the paper PDFs in the task's separate `work/pcp-sources/{core,foundations}` directory; these files are not copied here. Literature with unverified redistribution rights is marked `NOASSERTION`. The paper's public v2 is dated 22 October 2026; the Lean README describes following a revised SOSA version but does not establish byte identity with v2.

The initial graph passed `lean-exposition validate`, and all 98 source hashes were checked against the local source bytes on 15 November 2026. These checks test structure and bytes, not correctness of the mathematical support relations. No proof build, expression extraction or historical whole-library receipt is asserted. Complete proof `.olean` files were not found in the pinned checkout; an alternate checkout contains only four interface `.olean` files. Do not use those as a substitute for proof-module extraction.

The finite examples were rerun and stdout matched the retained output; that finite calculation is separate from the ordinary, non-Lean v1 infinite-family counterexample. The v1 counterexample has its own source-bound claim and paper citation.

The coverage pass adds the declaration locations in the three chapter evidence manifests. Those additional declarations are intentionally not given inferred proof edges or paper citation equivalences. A source excerpt is not a full elaborated type, especially where an inductive or structure body is represented by its opening line.

Both the original and expanded exposition checkers were rerun with stdout matching their retained outputs; the expanded finite checks have a distinct ordinary claim and execution record.

After [installing the package](../../CONTRIBUTING.md#setup), inspect the graph
from the repository root:

```sh
lean-exposition validate examples/pcp/evidence-graph.json
lean-exposition inspect examples/pcp/evidence-graph.json
```

Validation retains `extraction_status: not_run` and
`semantic_certification: false`. The [papers guide](../../papers/pcp/README.md#assemble-a-reader-bundle)
gives the existing `assemble` and `check-bundle` commands for the three authored
papers. The final source revisions, all 72 PDF pages and the captured bundle have
their respective review or validation records. The review summary identifies
their exact scope; the graph remains source-level and unextracted.
