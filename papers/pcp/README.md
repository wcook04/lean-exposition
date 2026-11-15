# Three accounts of the algebraic PCP proof

These papers explain why every NP language has a verifier that reads a constant
number of bits of a polynomial-length proof and uses logarithmically many random
bits. For an input in the language, some proof is accepted with certainty. For
an input outside it, every fixed purported proof is accepted with probability
at most one half. They follow the algebraic construction of
Amireddy, Behera, Srinivasan, Sudan and Willumsgaard and the route formalized in
Lean by Troy Lee.

| Read | Purpose and prerequisites |
| --- | --- |
| [Exposition with worked examples](expository/main.md) · [PDF](expository/main.pdf) | Begins with graph colouring, interpolation and small finite-field calculations; builds toward the encoding, correction and soundness argument. |
| [Specialist paper](short/paper.md) · [PDF](short/paper.pdf) | Gives the construction and its quantitative error bounds for a reader familiar with finite fields and low-degree testing. Links to the longer proofs it omits. |
| [Full argument](long/reasoning-record.md) · [PDF](long/reasoning-record.pdf) | Reconstructs the algebraic tests, binary encodings, local correction, grid certificates, verifier soundness and complexity-theoretic assembly. Lower-level machine implementation theorems remain identified source inputs. |

The [source map](../../examples/pcp/README.md) connects the papers to Lean
declarations. The [review summary](source-review/review-summary.md) records what
was checked and the limits of those checks. AI agents researched, drafted and reviewed
these explanations under Will Cook's direction. They are accounts of existing
results, not a new PCP theorem or an independent human expert's acceptance.

Read the same accounts beside the linked Lean in Proof Reader:
[full argument](https://wcook04.github.io/proof-reader/#/pcp-full-argument),
[specialist paper](https://wcook04.github.io/proof-reader/#/pcp-specialist), and
[worked exposition](https://wcook04.github.io/proof-reader/#/pcp-exposition).
The [previous release checks](source-review/release-checks.json) retain the earlier
clean-clone installation and deployment evidence. The current edition has its
own [revision receipt](source-review/review-round-3/validation.json).

## Exact sources and scope

The formal source is
[troyjlee/tcs-formalizations at a0ce13ed](https://github.com/troyjlee/tcs-formalizations/tree/a0ce13ed0fa264f051c1278e039596ce65557fa4),
full revision `a0ce13ed0fa264f051c1278e039596ce65557fa4`. The principal mathematical
reference is [*A Simple Algebraic Proof of the PCP Theorem*, arXiv:2608.17429v2](https://arxiv.org/abs/2608.17429v2),
dated 22 October 2026. Version 1 is retained only for the comparison of its older
scalar low-degree test with the corrected generator-and-Lagrange-weight test.

The [pinned Lean README](https://github.com/troyjlee/tcs-formalizations/blob/a0ce13ed0fa264f051c1278e039596ce65557fa4/docs/pcp/README.md)
describes a revised SOSA proof. This does not establish byte identity with arXiv
v2. The papers identify actual differences: the formal degree-three Hadamard
test uses ten queries, its auxiliary proximity guarantee concerns homogeneous
linear labels, and its derived queries use fresh randomness with an explicit
rejection-transfer bound.

The three formal endpoints are kept separate: `PCP.np_subset_pcp`,
`PCP.pcp_subset_np_concrete`, and `PCP.ReferenceNP.inNP_iff_mem`. Their source-level
signatures and selected proof bodies were read. No fresh full-library build,
kernel dependency extraction, or Comparator acceptance is claimed for this run.
The graph's authored proof-stage edges are navigation aids, not extracted Lean
expression dependencies.

## Checks and review state

The [latest revision](source-review/review-round-3/README.md) preserves the 133
prior repair verdicts and records the further changes. The full argument now
starts with the assembled verifier; the specialist paper introduces its tables
before the tests; the exposition carries one colouring example through to bit
reads. The final PDFs have 46, 13 and 24 pages, including references and optional
appendices. The [PDF check](source-review/review-round-3/pdf-checks.json) verifies
named destinations for the companion links.

The canonical bundle includes 38 authored reading relations between passages.
These editorial relations are separate from proof dependencies. Source cards
retain their source-reading or compilation evidence, and new procedure links
are distinguished from directly matching theorem claims. The
[validation receipt](source-review/review-round-3/validation.json) records exact
hashes and check outcomes. Earlier reports retain their own edition's evidence.
No fresh full-library Lean build or human expert acceptance is claimed.

Run the finite examples from the repository root with ordinary Python 3:

```sh
python3 papers/pcp/expository/check_examples.py
python3 papers/pcp/expository/check_exposition_examples.py
python3 papers/pcp/expository/check_trace.py
python3 papers/pcp/expository/check_changed_cases.py
```

Their retained outputs are [the initial calculations](expository/examples-output.txt)
[the expanded exposition calculations](expository/exposition-examples-output.txt),
[the colouring-to-bits trace](expository/trace-output.json), and
[the changed-case checks](expository/changed_cases-output.json).
These small examples do not instantiate the large-field hypotheses of the full
verifier. The [unbounded counterexample to the old scalar test](source-review/old-test-counterexample.md)
is a separate ordinary mathematical argument, not a conclusion proved by a
finite enumeration or a counterexample to the corrected theorem.

## Final editorial polish

The [final polish record](source-review/final-polish-20261115/README.md) records
consistent credits, a clearer specialist opening, and two new navigation
figures. The current PDFs have 47, 13 and 25 pages. The
[figure sources and rebuild instructions](figures/README.md) explain their
provenance and limits. The table/check matrix follows the actual seven branches;
the long proof map shows selected mathematical uses, not extracted Lean edges.
The [current PDF check](source-review/final-polish-20261115/pdf-checks.json)
validates the companion destinations for this edition.

## Assemble a reader bundle

After the [package setup](../../CONTRIBUTING.md#setup), run from the repository root:

```sh
lean-exposition validate examples/pcp/evidence-graph.json
lean-exposition assemble examples/pcp/evidence-graph.json \
  --long papers/pcp/long/reasoning-record.md papers/pcp/long/reasoning-record.json \
  --short papers/pcp/short/paper.md papers/pcp/short/correspondence.json \
  --expository papers/pcp/expository/main.md papers/pcp/expository/correspondence.json \
  --out build/pcp-authored
lean-exposition check-bundle build/pcp-authored
lean-exposition inspect-bundle build/pcp-authored
```

`assemble` checks and packages existing text and mappings. It does not write the
papers or certify the mathematics. Follow the [bundle consumer guide](../../docs/bundle-consumers.md)
and [website guide](../../site/README.md) to serve the captured papers and graph.
Generated bundles belong under `build/`; the authored sources remain here.

## Render the PDFs

Install Pandoc and Tectonic, then run the maintained renderer from the repository
root. Choose an output directory outside this checkout:

```sh
python3 papers/pcp/render.py --out /outside/checkout/pcp-pdfs
```

The renderer reuses the repository's Pandoc/Tectonic route and bookmark filter.
It writes intermediate TeX and PDFs under `long/`, `short/` and `expository/`
within the chosen output directory. Preserve those three directories when
sharing a reading edition: the PDF companion links use their relative locations.
Inspect the pages and links before copying PDFs into the maintained paper
directories. A successful rendering command alone does not establish visual
acceptance; the included PDFs have separate, hash-bound review records.

For an optional structural check of a relocated packet, install PyMuPDF in the
project's virtual environment and point the checker at the directory containing
all three companion folders:

```sh
.venv/bin/python -m pip install pymupdf
.venv/bin/python papers/pcp/check_pdfs.py /path/to/pcp-pdfs
```

This checks file presence, PDF hashes and named companion destinations. It does
not inspect typography, test external websites, or replace an actual reading of
the rendered pages.

The [source inventory](source-review/sources.json) records retained items, hashes,
public URLs and redistribution status. The separate
[bibliography acquisition record](source-review/acquisition-status.json) reports
21 of the corrected paper's 24 references obtained or already available,
including two code repositories. DeMillo–Lipton, Ore and Schwartz remain
unacquired; the record gives the exact items and failed access attempts. This
coverage count differs from the inventory's count of source files and versions.
Reference PDFs were retained in a separate working
annex for this reconstruction; they are not bundled with these papers. Permission
to download a source does not by itself permit redistribution. Sources marked
`NOASSERTION` remain reference-only until their rights are established. The
public paper and pinned code links above let a reader obtain the primary sources
directly.
