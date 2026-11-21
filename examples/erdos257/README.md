# Erdős Problem #257: irrationality criteria for Lambert subseries

This example holds the evidence graph, vendored Lean sources and recorded checks for three papers by W. Cook on Erdős Problem #257:

- the short paper *Irrationality criteria for Lambert subseries* (26 pages);
- the exposition *Why certain sums of 1/(2^n-1) are irrational* (16 pages);
- the long record *Reciprocal Mersenne subseries: support criteria, finite arithmetic and conditional orbit problems* (153 pages).

Problem #257 asks whether $X_A(2)=\sum_{a\in A}1/(2^a-1)$ is irrational for every infinite set $A$ of positive integers. It is open. The papers prove sufficient conditions for irrationality; none of them characterises the supports in the problem.

## Pins

| What | Repository | Commit |
| --- | --- | --- |
| Papers, evidence mapping, vendored Lean | [wcook04/plectis-erdos](https://github.com/wcook04/plectis-erdos) | `3368d1e69467aec111eb3244843ad3542171ff96` (16 November 2026) |
| Long record source, PDF and reader copy (six statements corrected) | same | `d9c43b26d1686523e95e09ab0014aaadb1903d03` (21 November 2026, pull requests 432, 433 and 434) |
| Lean pin cited by the evidence mapping | same | `436f55ebdafa67e4af0fff79f621c13f2ded12bf` |
| Comparator corpus and replay run 35935225572 | [wcook04/plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean) | `cc7e541cf2081c6fef5a5e377d52e365e33b01eb` |

At `d9c43b2` the long record's Proposition 2.5 states $1\notin A$, and five other sentences, among them Proposition 11.4 on squarefree certificates and the rejection of O1' in Section 12, say what their Lean proves; the graph's `paper.long.pdf` and `paper.long.tex` and the statements of `long.prop-collapse` and `long.prop-squarefree` follow that commit, and every other record, the evidence mapping and the vendored Lean are unchanged from `3368d1e`, whose Lean trees `d9c43b2` keeps. The Git tree hashes of `lean/ErdosProblems/Erdos257`, `lean/ErdosProblems/Erdos249` and `lean/Erdos249257` are the same at `436f55e` and `3368d1e` (checked with the GitHub contents API), so the vendored bytes are the Lean the evidence mapping cites. Toolchain `leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

## Files

- [source-lock.json](source-lock.json): 244 locked files with URL, SHA-256 and byte length: the 239 Lean files that form the import closure, inside the repository, of every declaration the short paper's and the long record's evidence mapping cites (124 under `lean/ErdosProblems/Erdos257`, 114 under `lean/Erdos249257`, 1 under `lean/ErdosProblems/Erdos249`), and the repository's `LICENSE`, `REUSE.toml`, `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. `lean_roots` names the two top-level Lean directories for the Lean index. The vendored subset is not a complete Lake package.
- [upstream/](upstream/): the locked bytes, unmodified, at their repository paths.
- [evidence-graph.json](evidence-graph.json): graph schema 1.2, built by [tools/build_graph.py](tools/build_graph.py).
- [authored/argument.json](authored/argument.json): the steps of the proofs and which step uses which, with a warrant for each use.
- [authored/evidence-status.json](authored/evidence-status.json): per record, the evidence mapping's `lean.status`, `relation_note`, `reason` and Comparator status for each paper that prints the result. The graph schema has no field for these.
- [verification/](verification/): the receipt files the graph's evidence records bind by `receipt_path` and `receipt_sha256`.
- [tools/vendor_sources.py](tools/vendor_sources.py): copies the closure and writes the source lock.

## What is mechanical and what an AI agent wrote

Copied mechanically from the papers' evidence mapping (`evidence/paper_evidence.json`, schema `plectis-paper-evidence/2`):

- one record per printed result: the short paper's 11 and the long record's 175, with the paper's own title, label, printed number and page;
- one `declaration` record per Lean declaration the mapping cites (448), plus the 10 definitions those statements unfold to;
- the 493 `formalizes` edges from results to declarations. Each cites a `semantic_review` record whose tool reads "Copied from the papers' evidence mapping (plectis-paper-evidence/2); no review by this example".

Two short-paper results have the same statements as long-record results and share one record each: Theorem 3.1 with long Theorem 1.3, and Theorem 4.1 with long Theorem 1.4. Short Theorem 1.2 and long Theorem 1.1 rest on the same declaration but state different things (the long one adds cofinal returns; the short one adds the base-two condition (W) and heredity), so they are two records joined by a `cites` edge whose note says so. The schema offers no "restates" or "strengthens" edge; `cites` is a reference relation and adds nothing to the argument closure. Only these three pairs share a Lean declaration; other short and long results were not compared statement by statement.

Written by Claude (Anthropic), an AI agent, from the pinned papers, recorded in `authored/argument.json`, and not reviewed by anyone else:

- 27 step records of the short paper's argument (`step.*`) and one context record (`context.sufficient_not_necessary`), from the displacement identity (D) to the limits in Section 6, each quoting the paper and citing its equation number as printed in the PDF;
- 7 step records of the exposition (`exp.step.*`), where it takes a different route with explicit cutoffs, and its Theorem 1 (`exp.thm-main`);
- 5 records of cited literature (`lit.*`, status `external`), and 7 open records (`problem.erdos257`, `open.*`, Problems D.4 to D.7, status `open`);
- 57 `supports` edges (consumer to prerequisite) and 12 `cites` edges. Every one has its own `semantic_review` record, status `not_run`, whose details give the warrant with a quotation from the paper and the sentence "written by Claude (Anthropic), an AI agent ... no independent review of this edge has been recorded."

## Selected goals

In this order: Theorem 4.1 (mixed weighted and cover supports), Theorem 1.2 (weighted condition), Theorem 3.1 (summable divisor cover), Theorem A.1 (reciprocal-summable supports, the statement Erdős gave in 1968, p. 222, without details) and Theorem B.1 (exact denominator period). Theorem 4.1 combines the two criteria and is the paper's main result; Theorems 1.2 and 3.1 are its two ingredients; Theorem A.1 is the case Erdős stated and the subject of the exposition; Theorem B.1 is the one finite-support result the other appendices build on.

## Status discipline

`contracts.py` allows `kernel_checked` only on a declaration with a passed `lean_build` and a passed `extraction` record of this tool bound to its source bytes, with matching module and source hashes. A passed `lean_build` or `comparator` record must embed this tool's process receipt (return code 0, `source_changed: false`, the command, `source_hashes` including `lean-toolchain`). This example ran neither a build nor an extraction, and the builds and Comparator runs we hold were made by other repositories' workflows, whose receipts have a different format and were not observed by this tool. The strictest reading follows:

- every declaration and result record has status `unverified`; the problem and the open questions have status `open`; cited literature has status `external`;
- the local `lean_build`, `comparator` and `extraction` records have status `not_run`, with the reason in [verification/not-run-locally.json](verification/not-run-locally.json);
- the Comparator replay receipts and the GitHub Actions runs are `platform_observation` records, with the outcome the platform recorded (`passed` for success, `failed` for failure, `unavailable` for cancelled). The contracts keep platform and local evidence apart, and these are outside observations;
- no passage can use `evidence_class: formal_result`.

No validator was changed.

## What ran

Run here, on 19 November 2026:

- `lean-exposition audit-sources examples/erdos257/source-lock.json --root examples/erdos257`: passed for all 244 files, 5,144,102 bytes ([receipt](verification/audit-sources.json)).
- `lean-exposition lean-index examples/erdos257/upstream/lean`: 239 modules and 6,010 declarations (4,398 theorems, 369 lemmas, 1,190 definitions, 34 structures, 13 instances, 3 abbreviations, 3 inductive types), 20,673 dependency rows. The index is a source-text scan, not an elaboration; names reached through notation, tactics or elaboration are absent.

Not run here: `lake build` (about 3 GB of free disk), Comparator (no `comparator`, `landrun` or `lean4export` installed), `lean-exposition extract`.

Recorded by others and kept as `platform_observation` records:

- 51 Comparator replay receipts of run 35935225572 on `wcook04/plectis-erdos-lean` at `cc7e541`, copied byte for byte into [verification/comparator/](verification/comparator/): the 50 `E257_*` receipts and `E249_06`, which checks a shared `Erdos249257` declaration. Each record names the declarations the evidence mapping associates with that entry. Every receipt records outcome `passed`, acceptance by the Lean default kernel and by nanoda, and the permitted axioms `propext`, `Quot.sound` and `Classical.choice`. The receipts were written with `leanprover/lean4:v4.30.0` and Comparator's `v4.34.0-rc1`, not the papers' `v4.29.1`. The run's first attempt failed in shard-03, which holds `E1049` entries; the second attempt re-ran that shard and succeeded. [verification/comparator-replay-35935225572.json](verification/comparator-replay-35935225572.json) indexes the receipts with run id, URL, commit, date, outcome, kernels and axioms.
- GitHub Actions runs, indexed in [verification/actions-runs.json](verification/actions-runs.json) with run id, URL, commit, dates, conclusion and jobs: on `wcook04/plectis-erdos`, Lean CI runs 36470042155, 37928349409 and 43881701663, the paper-coverage builds 36476634814, 37929526198 and 38054633018, and the cache-warm build 43910511985, all at commits whose three Lean trees equal the pin's; on `wcook04/plectis-erdos-lean` at `cc7e541`, the corpus builds 35935225568 and 35935275618, the release gate 35935275645, and both attempts of replay 35935225572. No run exists at `436f55e` itself. The build log of run 36470042155 reports `targets=Erdos249257,ErdosProblems; 0 stale/missing module(s)`, so its outputs came from a cache; 63 of the 239 vendored modules are outside the import closure of those two root modules. Run records therefore name no declaration subjects.

Left out, with the reason: run 43483288629 (its Lean jobs were skipped), the Corollary 5.2 Comparator runs 41870626546 and 41870626253 and Lean CI 41870760772 (branch `codex/257-corollary-52-verification-20261018`, whose `Erdos257` tree differs from the pin; PR #426 is unmerged), the Formal Conjectures and Prove2Me runs on other commits (the Formal Conjectures pull request 6529, which adds the reciprocal-summable variant, was merged on 9 October 2026; its runs check a frozen copy, not the pinned tree), and cache-warm, coverage and replay runs at other commits.

Each run's evidence record binds its own `verification/actions/<key>.json` (`record_type: "github_actions_run"`, the shape in `site/src/instances/erdos257/README.md`), and each Comparator record binds its own replay receipt. The two index files are `verification/actions-runs.json` (`runs[]`: `repository`, `run_id`, `url`, `name`, `event`, `head_branch`, `head_sha`, `created_at`, `updated_at`, `conclusion`, `run_attempt`, `jobs[]`) and `verification/comparator-replay-35935225572.json` (`run`, `entries[]`: `entry`, `receipt_path`, `receipt_sha256`, `run_id`, `run_attempt`, `url`, `commit`, `date`, `outcome`, `kernels`, `axioms`, `lean_toolchain`, `comparator_lean_toolchain`, `theorem_count`, `declarations`, `pairs`, `not_established`).

## Alignment and paper mappings

[alignment/](alignment/) is checked by `lean-exposition check-alignment examples/erdos257/alignment`. It is written by [tools/build_alignment.py](tools/build_alignment.py), except `dictionary.json`, `names.json` and `main-theorem.json`, which an AI agent wrote by hand.

- `m1-short-and-front.json` and `m2-long.json` (mechanical, `origin: "evidence_record"`): one row per result record. Lean rows come from the evidence mapping. An `exact` result gives `relation: "states"`, `fidelity: "same"`, `fidelity_source: "recorded"`. For the short paper's eight `exact_or_stronger` results and long Theorems 1.1, 1.3 and 1.4, an AI agent read the printed statement and each Lean statement side by side and set `relation`, `fidelity` and `fidelity_note` (`fidelity_source: "ai"`, notes beginning "Read side by side by an AI author"). Short Theorem 3.1's note records that the mapping calls it `exact` for the short paper and `exact_or_stronger` for long Theorem 1.3. The other long-record `exact_or_stronger` rows were classified from the recorded relation note, not from a fresh reading: the note is kept verbatim as `fidelity_note`, and `fidelity` is `stronger` only where the note's words say the Lean adds or widens something (the rule `WIDER` in the script), otherwise `same`. Where a theorem's statement unfolds one `def ... : Prop`, `clause_file` and `clause_name` point at the definition. Each statement runs from the bold heading after the result's anchor to the end of the italic statement.
- `references-{short,long,expository}.json`: written by [tools/build_references.py](tools/build_references.py). The reader copies write every internal reference as a Markdown link to an explicit anchor, so each row is one link, with its target taken from the link and its label from `papers/erdos257/numbering.json`; citations take their source from the paper's own reference list. Erdős 1948 and Erdős 1975 have no web address in the bibliography, so their source address is the paper's own reference-list anchor.
- `a1-exposition.json`: the exposition's Theorem 1 tied to `Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal` with `fidelity: "stronger"` and `fidelity_source: "ai"`: the Lean states every integer base $b\ge2$ and sets $A\subseteq\mathbb N$, where the exponent $0$ contributes $0$, as the exposition's Appendix A.6 says.
- `a2-steps.json` (`origin: "ai"`): the display or sentence that states each authored step. Three steps of Theorem A.1's proof carry Lean rows found by reading `Erdos249257/ReciprocalSupportIrrationality.lean`, which `AllBaseReciprocalSupportIrrationality.lean` imports: the gcd-orbit mean (8), dominated convergence for a fixed modulus and the lcm limit (9). Each is the base-two case (`fidelity: "weaker"`): the Lean proof reaches other bases by bounding each base-$b$ displacement by twice the binary one, and its majorant is $2(Q+1)/d$ where the paper writes $(Q+2)/d$. The other steps have `"lean": []` and a note: the Lean proof of Theorem 1.2 runs through dyadic means and a mixed-gauge estimate whose lines were not matched to the paper's displays.
- `main-theorem.json`: Theorem A.1 against `irrational_erdosSupportSeries_of_summable_reciprocal` and Theorem 4.1 against `MixedSupportClaim`, clause by clause, each Lean clause a byte-exact span of the declaration.

- `references-*.json` also carry the long record's plain self-references that the paper prints without a link ("Sections 5–8", "Section 13"), each to the section whose printed number it names; a reference to a page or "of" another work stays text.
- [tools/build_forward.py](tools/build_forward.py) writes `site/src/instances/erdos257/forward-map.json` and `forward/erdos_257.html` (the old problem page's fragments and where each lands in the reader) from the static edition and the vendored Lean module list.

- `alignment/phrases-{short,expository,long}.json`: the phrase ties the reader marks. Each ties a Lean declaration to the exact words of one paper that state it (a `from`/`to` quotation, no two overlapping), groups the ties of the paper under eight or nine topics (the long record in two parts, Parts I–II and Parts III–V, each with its own topics, prefixed `p1-` and `p2-`), and gives each declaration a plain title and a reading note in that paper's register, with whether the Lean states the same as the phrase, more, less or something different. An AI agent drafted all of it; no mathematician has reviewed it. `lean-exposition check-alignment` checks that each phrase occurs once in its paragraph, cuts no formula, overlaps no other phrase, and that every declaration it names has a title, a note and a topic. [scripts/import_phrase_returns.py](../../scripts/import_phrase_returns.py) writes these files from the reviewed returns and lists each Lean pointer it corrected (`corrections`).

The paper mappings `papers/erdos257/{short/correspondence.json, long/reasoning-record.json, expository/correspondence.json}` are written by [tools/build_sidecars.py](tools/build_sidecars.py) from the reader copies, their `passages.json` and this graph: state `draft`, review state `not_reviewed`, every passage `source_argument`, `open_question` or `context`.

## Corollary 5.2

The evidence mapping records no Lean proof of the whole statement of Corollary 5.2: "the new host existence claim has not been formalised; the mixed implication it invokes is already checked". The graph keeps this as the open record `open.cor52_lean`. A theorem `exists_strict_mixed_support_host` exists only on the unmerged branch named above and is not part of these sources.

## Rebuild

```sh
python3 -m venv /path/to/venv && /path/to/venv/bin/pip install -e .
python examples/erdos257/tools/vendor_sources.py --export EXPORT --root-files ROOT --closure lean-closure.json --acquired-at 2026-11-19T21:40:00+00:00
lean-exposition audit-sources examples/erdos257/source-lock.json --root examples/erdos257
python examples/erdos257/tools/build_graph.py --export EXPORT --whatran WHATRAN
lean-exposition validate examples/erdos257/evidence-graph.json
lean-exposition lean-index examples/erdos257/upstream/lean --out /tmp/erdos257-index.json
```

`EXPORT` is `git archive` of `wcook04/plectis-erdos` at `3368d1e`; `ROOT` holds the five root files from `raw.githubusercontent.com` at the same commit; `WHATRAN` holds `workflow_runs.json` and `receipts.json`, the run records gathered with `gh` on 19 November 2026. Rerunning `build_graph.py` on the same inputs gives the same bytes.

## Licences

The vendored files are Apache-2.0: the repository's `REUSE.toml` annotates every path with Apache-2.0 except listed PDFs and figures (CC-BY-4.0) and one skills directory (MIT-0), and no vendored file is among the exceptions. None of the vendored Lean files carries an in-file SPDX header. The papers are CC-BY-4.0 and are bound by hash as reference-only sources. Cited literature is recorded with licence `NOASSERTION`.
