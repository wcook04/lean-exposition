# Round 3 reader backend check

## F39: companion navigation

The round 2 long review reports two failed ordinary clicks in one connected desktop Chrome session: long account → specialist and specialist → long account's bivariate section. It explicitly leaves the frozen static build unassessed and does not identify an event-handling cause (`long/review.md`, lines 203–207; `support/browser_observations.json`, B01–B05).

I exercised both exact `href` paths in fresh Playwright Chromium against the current local production build and `https://wcook04.github.io/proof-reader/`. Each ordinary click navigated to the intended paper and added one browser history entry. The bivariate link landed with the long account's section 4 heading at the top of the paper pane. Back restored the source paper's scroll position. The tested widths were 1440 and 1920 pixels. The review's session failure remains a valid observation of that session; the current checks do not reproduce it or establish its cause.

The reader already delegates cross-paper links to the browser in `web/src/paper/ReadingPane.tsx` and saves the current entry before navigation. No application change is justified by the available reproduction. I added the two paths and Back assertions to the existing `tests/journey.py::companions` journey.

## F09: generator theorem selection

The current association owner is `papers/pcp-full-argument/links.json`, passage `pcp-long-algebra-generator-soundness`. It quotes only the lead-in “Apply this result to (A6), with $n=c+1$. If” from `papers/pcp-full-argument/paper.md` line 302, for `PCP.Algebraic.GeneratorLowDegreeTest.exists_close`. The later rigidity-budget mapping targets a different theorem.

The source declaration in `papers/pcp-full-argument/lean/PCP/Algebraic/GeneratorLowDegreeTest.lean`, line 274, assumes `2*c < Fintype.card F`, a primitive root of order `q-1`, `rejectionRate c ζ f ≤ δ`, and `δ < 1/(2(c+2)^2)`. It concludes a formal `P` of total degree at most `c` with `relativeDistance f (eval P) ≤ 2δ`. The correct mapping update is a complete single-paragraph theorem assertion inside the same passage, followed by a matching `quote` in `links.json`. The exact proposed assertion appears in `long/replacement_sections.md` §4. Paper and mapping edits are reserved to the parent author.

The parent subsequently authored that paragraph in the canonical long paper. The reader copy and `pcp-long-algebra-generator-soundness` association now use the complete assertion, and the reader checks below pass.

## Checks

- `python3 -m unittest discover -s tests`: 115 passed.
- `python3 tools/paper.py check contextual-embeddings`: passed.
- `cd web && npm run test:source`: 11 passed.
- `cd web && VITE_BASE_PATH=/proof-reader/ npm run build`: passed.
- `tests/journey.py` using the existing `work/pcp-reader-qa-env` Python and installed Playwright Chromium: 416 checks passed, including the new local companion cases.
- `tests/journey.py --only companions --url https://wcook04.github.io/proof-reader/`: 36 checks passed.
- At the initial F39 check, `git diff --check` passed and only `tests/journey.py` was modified. The subsequent reader integration below deliberately changed the three paper copies, associations, source indexes, module lists and header CSS. No register, deployment or commit was changed by this agent.

## Round 3 reader integration

The three reader `paper.md` files are byte-identical copies of the current canonical long, specialist and exposition Markdown. `links.json` now selects the moved text by its new heading and source block. In particular, `pcp-long-algebra-generator-soundness` selects the complete single-paragraph assertion beginning “Suppose $q>2c$” and ending with relative size at most $2\delta$. The source pane targets `GeneratorLowDegreeTest.exists_close`, whose pinned source declaration is at line 274. The specialist's same-$U$ selection is the new standalone summary after equation (11), not the old incomplete context sentence.

The source-read index was extended through `extend_source_index.py`, adapted from the prior `refresh_source_data.py` owner. It reads exact spans from the pinned Lean tree and updates the edition's module list and `paper.toml` together. It does **not** invoke Lean or assert new extracted dependencies or axiom reports. Added source excerpts cover `SetMultilinear.evaluationPoint`, `SetMultilinear.eval_encode`, `SetMultilinear.totalDegree_encode_le`, `EncodedLineLowDegreeTest.Auxiliary`, and `ThreeColorVerifier.Proof`/`Query`/`read` where used. The exposition also retains `BinaryLocalCorrection.run` as a source-read procedure. The canonical finite trace remains a worked finite calculation verified by its linked checker; its sole new Lean association has role `uses` and points to `BinaryLocalCorrection.run` for the reused inner direction. No link presents the finite calculation as a direct Lean theorem.

The new long implementation-contracts association has role `uses` and links the query-tree semantics to `Verifier.ImplementedBy` and `QueryTree.ofStep`. The specialist's proof-table selection links the exact eight-field `Proof` structure, while its primary-address selection treats `Query` and `read` as source prerequisites. The exposition's general digit-encoding paragraph links the separate total-degree and evaluation statements, so each part of its selection has source support.

N04 was reproduced at 1363×936: a long Back label extended 64 pixels into the title column after Graph closed. The existing `.back` control now allows flex shrink and ellipsis within its column. `tests/journey.py::narrow_header` checks the same history state, title space and nonoverlap. The rendered narrow screenshot and a monitor reading screenshot were inspected at their actual sizes in `shots/`.

## Final validation after canonical sync

From `work/proof-reader`:

- `cmp -s ../lean-exposition/papers/pcp/long/reasoning-record.md papers/pcp-full-argument/paper.md` (and the analogous short and exposition pairs): all three byte-equal.
- `python3 ../pcp-round3-backend/reanchor.py`: zero reanchored and zero unresolved for all three editions.
- `python3 tools/paper.py check pcp-full-argument`, `python3 tools/paper.py check pcp-specialist`, `python3 tools/paper.py check pcp-exposition`, plus checks of `contextual-embeddings` and `axiom-of-choice`: all five pass. Declared-linked counts are long 57/81, specialist 16/42, exposition 23/49; statuses are the retained compilation and source-read mix.
- `python3 -m unittest discover -s tests`: 115 passed.
- `cd web && npm run test:source`: 11 passed.
- `python3 tools/paper.py build`: all five editions built.
- `cd web && VITE_BASE_PATH=/proof-reader/ npm run build`: passed.
- `../pcp-reader-qa-env/bin/python tests/journey.py`: 419 checks passed in 108 seconds.
- `git diff --check`: passed.

Inspected screenshots: `shots/pcp-narrow-header-1363.png`, `shots/pcp-reading-1920.png`, `shots/pcp-proof-type-1440.png`; `shots/pcp-reading-1440.png` is also available. Six new passage deep links were opened at 1440px; each rendered its Lean pane without page errors, and Graph toggled on the new exposition and specialist proof-type links.

The twelve changed reader paths are the three paper copies, their three `links.json` files, the specialist and exposition `generated/lean.json` and `paper.toml` pairs, `tests/journey.py`, and `web/src/app/app.css`. No unsupported changed selection remains in the three PCP editions. No commit or deployment was made.

## Revised finite-trace table sync

After the parent changed the canonical exposition table to separate Call, Step and $z$ and assigned wider Markdown separator columns to the point fields, `papers/pcp-exposition/paper.md` was copied again byte-for-byte. The existing associations required no reanchor: `reanchor.py` reported zero reanchored and zero unresolved for all three editions. `python3 tools/paper.py check pcp-exposition`, `python3 tools/paper.py build pcp-exposition`, `cd web && VITE_BASE_PATH=/proof-reader/ npm run build`, `cmp -s` against the canonical exposition Markdown, and `git diff --check` all passed.

The browser inspection script `inspect_trace_table.py` served the built reader and captured the table at 1440×900, 780×900 and 390×844. At 1440 and 780 pixels the full table fits within the reading pane without horizontal overflow; at 390 pixels its 504-pixel contents scroll through the existing 326-pixel semantic table viewport. A second mobile screenshot at scroll position 178/178 shows the remaining columns and sums. No page errors occurred. I inspected `shots/pcp-trace-table-1440.png`, `shots/pcp-trace-table-780.png`, `shots/pcp-trace-table-390.png`, and `shots/pcp-trace-table-390-scrolled.png` at intended sizes. The layout is legible and needs no reader CSS change.

The first viewport captures raced the reader's initial position restoration and could show the opening instead of the table; the table element crops were correct. I corrected the capture order and replaced the viewport screenshots. The final 1440 and 780 captures visibly show the complete table in the reader. Their route is `#/pcp-exposition/@pcp-expository-worked-correction-source` (statement 17/23), with table bounds at vertical pixels 345–601 and 357–588 respectively. The final mobile capture is at `#/pcp-exposition/@b-168`, with table bounds 314–594. All bounds are within the captured viewport, and all three captures had zero page errors.
