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
The [release checks](source-review/release-checks.json) record the clean-clone
installation, bundle reproduction and deployed-reader verification.

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

The [archived reviews](source-review/review-summary.md) distinguish source-based
mathematical checks, finite Python calculations, bundle validation and reader
review. The algebra, binary, theorem and specialist reviews record corrections
and rechecks of their named revisions. The exposition's consequential
source-level findings were resolved and rechecked at revision `2e2333ca`.
All 72 final PDF pages were visually reviewed, the 19 companion annotations
passed structural checks, and the assembled reader bundle passed validation.
The [review summary](source-review/review-summary.md) gives the exact revisions
and the scope of the reader inspection. A review of an earlier revision does
not automatically cover later edits.

Run the finite examples from the repository root with ordinary Python 3:

```sh
python3 papers/pcp/expository/check_examples.py
python3 papers/pcp/expository/check_exposition_examples.py
```

Their retained outputs are [the initial calculations](expository/examples-output.txt)
and [the expanded exposition calculations](expository/exposition-examples-output.txt).
These small examples do not instantiate the large-field hypotheses of the full
verifier. The [unbounded counterexample to the old scalar test](source-review/old-test-counterexample.md)
is a separate ordinary mathematical argument, not a conclusion proved by a
finite enumeration or a counterexample to the corrected theorem.

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

The [source inventory](source-review/sources.json) records hashes, public URLs
and redistribution status. Reference PDFs were retained in a separate working
annex for this reconstruction; they are not bundled with these papers. Permission
to download a source does not by itself permit redistribution. Sources marked
`NOASSERTION` remain reference-only until their rights are established. The
public paper and pinned code links above let a reader obtain the primary sources
directly.
