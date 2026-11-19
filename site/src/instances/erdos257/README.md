# The `erdos257` instance

The reading site built for Erdős problem #257, selected with
`LX_INSTANCE=erdos257`. The SK site is the default instance (`qaoa-sk`); both
share every page, and each instance supplies only what is its own
(`../types.ts`, `../types.ui.ts`):

| File | What it holds |
| --- | --- |
| `site.ts` | Paths, PDFs, published README and `llms.txt`, route titles, the sentences shared pages say about this example |
| `copy.ts` | Every sentence the author writes, as named slots (below) |
| `hero.ts` | The first screen: title, opening, credit, the main theorem clause by clause with a verdict column |
| `FrontPage.tsx`, `AboutPage.tsx`, `LeanLanding.tsx`, `ChecksIntro.tsx` | The pages whose structure is this example's |
| `figures.ts` | No drawn figures: a figure shows its own image file |
| `theme.ts`, `wide.css` | Styles only this instance loads (wide-window layout, verdicts, runs table, image figures) |
| `elsewhereLinks.ts`, `Elsewhere.tsx` | The "Elsewhere" block on the front page and About: the problem, the Lean on GitHub, each paper's PDF and TeX, the Maths Map and the overview page (`OVERVIEW_URL`, one constant) |
| `forward-map.json`, `forward/erdos_257.html` | The old problem page's fragments and where each lands in this reader, and the forwarding page that will replace that page. Both are written by `examples/erdos257/tools/build_forward.py` from the static edition; the page's reader address is one constant, and on localhost only `?reader=<address>` points it at a local copy |

## Build it

```sh
# from the repository root, once examples/erdos257/ and papers/erdos257/ exist
lean-exposition assemble examples/erdos257/evidence-graph.json \
  --long papers/erdos257/long/reasoning-record.md papers/erdos257/long/reasoning-record.json \
  --short papers/erdos257/short/paper.md papers/erdos257/short/correspondence.json \
  --expository papers/erdos257/expository/main.md papers/erdos257/expository/correspondence.json \
  --out build/erdos257-edition
python site/scripts/export-static.py build/erdos257-edition \
  --lean-tree examples/erdos257/upstream/lean --alignment examples/erdos257/alignment
cd site
LX_INSTANCE=erdos257 npm test
LX_INSTANCE=erdos257 LX_SITE_URL=https://<host>/<path>/ VITE_BASE_PATH=/<path>/ VITE_STATIC_EDITION=true npm run build
```

The build stops, naming the file, if the graph, the alignment folder, a
`references-<paper>.json` or a PDF is missing. It warns about every copy slot
still holding `TODO(copy)`, about receipts an evidence record names that are
missing, and when `LX_SITE_URL` is unset (then the README and `llms.txt` use
relative links and no `sitemap.xml` is written). No SK address is used.

Inputs it reads, in the same layout as the SK example:

```
examples/erdos257/evidence-graph.json
examples/erdos257/alignment/{*.json, ties-<paper>.json, names.json, dictionary.json, references-<paper>.json}
examples/erdos257/upstream/lean/            (the "Any sorry" text scan)
examples/erdos257/<receipt_path of each evidence record>
papers/erdos257/long/reasoning-record.pdf, short/paper.pdf, expository/main.pdf
papers/erdos257/<paper>/figures/*.{svg,png,jpg,webp}   (published as paper-figures/<paper>/)
```

The main theorem is Theorem A.1 of the short paper (record
`short.res-reciprocal-support`, Lean `Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`),
named in `site.ts` (`theorem`, `mainGoal`, `lean.mainTheorem`); its statement in the
short paper is that record's slice matching `theorem.pattern`. No other #257
identifier is typed in the site.

## Fields the data emits

### Comparisons: `fidelity` on a Lean row

Optional on any Lean row of a record (batch files) or of a statement (`ties-*.json`),
and carried through to `/alignment` and, for a tie's first Lean row, to `/ties/<paper>`:

```json
{ "file": "ErdosProblems/Erdos257/Main.lean", "name": "erdos_257_variant", "relation": "states",
  "note": "…",
  "fidelity": "same",
  "fidelity_note": "One or two plain sentences: where the two differ, or that they do not.",
  "fidelity_source": "recorded" }
```

- `fidelity`: `"same"` | `"stronger"` (the Lean says more than the paper) | `"weaker"` (the Lean says less).
- `fidelity_note`: plain words, shown after the verdict.
- `fidelity_source`: `"recorded"` = copied from the source repository's own evidence
  record (for #257, `evidence/paper_evidence.json`'s `lean.status`/`relation_note`);
  `"ai"` = written by an AI agent for this site.

Shown as "The Lean statement says the same as the paper." / "…says more than the
paper." / "…says less than the paper.", then the note, then who compared them, in
Compare, the step view and the Lean panel a tick opens. Absent: no line.

### Who made a tie: `origin` on a statement

Optional on every statement slice (batch `statements[]` and `ties-*.json` rows),
carried to `/alignment` statements and to each tie in `/ties/<paper>`:

```json
{ "record": "…", "paper": "short", "role": "statement", "from": "…", "to": "…",
  "origin": "evidence_record" }
```

- `"evidence_record"`: the link from the printed result to its Lean declaration is
  copied from the papers' published evidence mapping.
- `"ai"`: an AI agent read both sides and made the link for this site.

The reader's Lean panel says which in words; the front page, What ran and
`llms.txt` give both counts from `/ties/<paper>`. Absent: today's wording.

**Dependency.** The Python resolver (`src/lean_exposition/alignment.py`) currently
rejects unknown keys: `_check_keys` must accept `fidelity`, `fidelity_note`,
`fidelity_source` on Lean rows and `origin` on statements, `resolve_alignment`
must copy them into the resolved rows, and `_tie` must copy `origin` (and the
first Lean row's `fidelity*`) into each tie. Until it does, the site shows
neither, exactly as the SK site does.

### Runs: receipts named by evidence records

The What ran page's table of runs reads every evidence record of the graph that
has a `receipt_path`, plus every `lean_build`, `comparator` and `extraction`
record without one, and publishes each receipt under `verification/<path>`. The
record's own `status` (`passed | failed | unavailable | not_run`) is the outcome;
the receipt adds the rest. `receipt_path` is relative to `examples/erdos257/`.
Three receipt shapes are read; any other JSON gives a row from the evidence
record's own fields.

**A GitHub Actions run**

```json
{
  "record_type": "github_actions_run",
  "workflow": "Warm the main Lean cache",
  "repository": "wcook04/plectis-erdos",
  "run_id": 43910511985,
  "run_attempt": 1,
  "url": "https://github.com/wcook04/plectis-erdos/actions/runs/43910511985",
  "commit": "<40 hex>",
  "branch": "main",
  "event": "push",
  "started_at": "2026-11-16T10:00:00Z",
  "completed_at": "2026-11-16T10:40:00Z",
  "conclusion": "success",
  "shows": "What this run establishes, in one sentence.",
  "does_not_show": "What it leaves open, in one sentence."
}
```

`conclusion` is GitHub's: `success | failure | startup_failure | cancelled |
timed_out | skipped | action_required | stale`, or `unavailable` when the run
could not be read back. Set the evidence record's `status` to match (`success` →
`passed`, `failure` → `failed`, cancelled/timed out/skipped → `unavailable`).
`url` may be left out when `repository` and `run_id` are given.

**A Comparator replay receipt**, as the replay workflow writes it
(`palomar_replay_receipt_v1`; the fields read are `entry`, `generated_at`,
`github.{repository, run_id, sha, workflow}`, `theorem_names`,
`permitted_axioms`, `kernel_acceptance`, `verification.{outcome, failure_stage}`),
or the generic form:

```json
{
  "record_type": "comparator_receipt",
  "entry_id": "E257_01",
  "run": { "repository": "wcook04/plectis-erdos-lean", "run_id": 35935225572, "commit": "<40 hex>", "date": "2026-09-24", "url": "…" },
  "theorem_pairs": [ { "challenge": "Erdos257.erdos_257.variants.summable_reciprocal_support", "solution": "…" } ],
  "kernels": ["Lean’s default kernel", "nanoda"],
  "axioms": ["propext", "Quot.sound", "Classical.choice"],
  "outcome": "accepted",
  "shows": "optional; a default sentence is written from the kernels and axioms",
  "does_not_show": "optional; default: whether the challenge statements say what the papers say"
}
```

`outcome`: `accepted | rejected | error | unavailable` (or `passed | failed`).

**Many receipts under one record.** The graph allows one `receipt_path` per
record. For a replay with one receipt per entry (about 50 for #257), either give
each its own evidence record, or point one record at an index:

```json
{ "record_type": "receipt_index", "receipts": ["receipt-E257_01.json", "receipt-E257_02.json"] }
```

Paths in `receipts` are relative to the index's folder. Each listed receipt is a
row with the outcome its own `verification.outcome` gives. A kind with more than
eight rows is shown as one summary row (count, outcomes, commit, dates) with a list
that opens.

## Copy slots (`copy.ts`)

Each holds `TODO(copy): <slot>` until written. Inline TeX between single dollar
signs is typeset. No number or identifier belongs in a slot: the pages around
them supply every count.

| Slot | Where it shows |
| --- | --- |
| `siteName` | The bar, browser tabs, the published README's title |
| `title` | Front page heading, the tab on the front page, link previews, `llms.txt` |
| `strapline` | The line above the title; link preview description |
| `opening` | The paragraph under the title; the page description |
| `credit` | Under the opening, and About's "Who made this site": who proved what, who formalised it, who made the site |
| `asked[]` (`asked`, `proved`, `open`, `goal`) | "What was asked, what was proved and what stays open": one entry per question; `goal` is an optional graph id for its map link |
| `proofSteps[]` (`title`, `text`) | "How the proof goes", in order |
| `levels.lean.who` | The levels band's line for the Lean |
| `levels.<paper>.short`, `.job`, `.reader` | Each paper's name in the bar and shelf, what it does, who it is for |
| `clauses.heading`, `clauses.intro` | The heading and paragraph beside the clause table |
| `clauses.rows[]` (`lean`, `tex`, `note`, `verdict`, `record`) | One row per clause: the exact Lean clause, the short paper's statement as TeX, a note, `same`/`stronger`/`weaker`, and an optional graph id Compare opens |
| `about[]` (`heading`, `paragraphs[]`) | About's own sections |
| `llms` | The summary line of `llms.txt` |

## Records in the papers' terms

`site.ts` sorts each record of the graph (`recordKind`): a Lean declaration, an open question
(status `open`), a cited result (status `external`), a proof step an AI agent wrote out from the
papers (ids `step.`, `exp.step.`, `context.`), or a result printed in a paper. The levels band, the
map's header, What ran and `llms.txt` count records in these terms, each count read from the
edition. `levelGoals` draws the exposition's own Theorem 1 at its level of the levels band,
because the exposition proves Theorem A.1 at base two in its own steps.
