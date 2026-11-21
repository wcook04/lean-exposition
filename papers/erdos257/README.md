# Erdős Problem #257: the three papers as reader Markdown

These files transcribe three published papers by Will Cook for this repository's reader: [`short/paper.md`](short/paper.md) (*Irrationality
criteria for Lambert subseries*, 26 pages), [`expository/main.md`](expository/main.md) (*Why certain sums of 1/(2^n-1) are irrational*, 16 pages)
and [`long/reasoning-record.md`](long/reasoning-record.md) (*Reciprocal Mersenne Subseries*, 153 pages), each beside its unchanged PDF. The source is
`wcook04/plectis-erdos` at commit `a5e7700e30374e3aaeeeff0284ec2ec0d2322fc3` (21 November 2026, pull request 432, which corrects four statements of the long record; the short paper and the exposition are byte-identical to `3368d1e`). [`SOURCES.json`](SOURCES.json) gives every input and output sha256.
Licence: the source's `paper/README.md` says "The manuscript layer (the `.tex` sources and rendered PDFs) is licensed CC-BY-4.0", and its
`REUSE.toml` gives the three PDFs `SPDX-FileCopyrightText = "2026 Will Cook"` and `SPDX-License-Identifier = "CC-BY-4.0"`. These transcriptions
are offered under CC-BY-4.0 with that attribution. The full-text Markdown they start from falls under that repository's Apache-2.0 blanket entry.

Words come from `docs/papers/full-text/*.md`, numbers from the `.aux` of a Tectonic compile of exactly these sources, and front matter and
bibliography labels from the TeX. Nothing is reworded. The rules are:
1. Math: `` $`x`$ `` becomes `$x$`, and a ```` ``` math ```` fence becomes a `$$` block. `\label` is removed. An `equation` loses its wrapper and gains
   `\tag{n}`, with the counted number checked against every label. `equation*` loses its wrapper and keeps its `\tag`, and `align*` becomes `aligned`.
   The one numbered `align` is kept, because KaTeX accepts a `\tag` per row. `site/src/reader/math.ts` gives KaTeX no macro table. Pandoc had
   already expanded the preamble macros, leaving two: `\ensuremath{X}` becomes `X` (braced after `^`/`_`) and `\ref{label}` its printed number.
2. Numbers: result heads, references and headings carry the PDF's numbers (Theorem 1.2, (W), A.6), from the aux and toc. Unlabelled results use
   the same counters, which are checked against every labelled one. Levels follow the SK papers: `#` title, `##` section, `###` subsection. The long
   record also has parts, so its parts are `##`, sections `###` and subsections `####`, with `#####` and `######` below them.
3. Blocks: `<div id="X" class="K">` becomes `<a id="X"></a>`, and `</div>` is dropped. Ids keep their colons, which the reader accepts. Heads read
   `**Theorem 1.2 (title).**`, because the reader's run-in rule needs the period inside the bold. `evidence-marks` lines are removed, and their
   URLs are kept in [`evidence-marks.json`](evidence-marks.json).
4. Citations are numeric as in the PDF (`\[[7](#ref-erdos1968), p. 222\]`). The entries are split by the TeX `\bibitem`s, and each starts
   `<a id="ref-KEY"></a>\[n\]`. The full text's stray `99`/`9` is dropped, and a `## References` heading is added.
5. Links: PDF `nameddest` links go to the companion Markdown anchor (`../long/reasoning-record.md#record257:…`), or to `#anchor` within the
   same paper. Other repository paths become pinned blob URLs. Absolute links are unchanged.
6. Figure: the figure is a ```` ```{=latex} ```` block (TikZ and caption) as in the SK exposition, followed by a line linking to PDF page 9 and
   to `expository/figures/cycle-mean.svg`, made by `tools/cycle-mean-standalone.tex`, Tectonic and `pdftocairo -svg`. The reader shows that SVG
   in the figure's place (`site/src/instances/erdos257/figures.ts`, keyed by the label `fig:cycle-mean`).
7. Front matter comes from `\title`, `\subtitle`, `\author`, `\date` and the provenance note, and the abstract opens with `**Abstract.**`. Each
   section is a `<!-- passage:NAME -->` named by its anchor, as is each subsection of a long-record section over 300 lines (`<level>/passages.json`).

8. Table cells: the full text moves long table cells of the long record into "Detail note N." paragraphs after the table; the PDF prints them in
   the cell. Each note's content goes back into its cell and the note paragraph is dropped. Pandoc's empty comment between an inline formula and a
   digit (`$\sim$<!-- -->1246`) becomes a space (`convert.source_fixes`, applied to the source by both scripts).

Rerun: `python3 tools/convert.py <export-root> <aux-dir> .` then `python3 tools/check.py <export-root> <aux-dir> . [scratch-dir]` (standard
library only; the KaTeX check needs `npm ci` in `site/`). The check canonicalises the rule-changed places on both sides and requires equal
source and output token sequences. It also requires front matter equal to the TeX, and every formula rendered by the reader's `math.ts` with
`throwOnError`, with as many formulas as the source. Links must resolve, printed numbers must equal the aux, toc and `paper_evidence.json`, every
body line must sit in one passage, and two runs must be byte-identical. It does not show that the full text equals the PDF. The full text omits the
"Verification concordance" tables, drops "Table 1:" from a caption, and nests one link in another
(short paper, Appendix F). External URLs were not fetched, the full reader app was not run, and `lean-exposition scaffold`/`check-bundle` (which
need an evidence graph) were not run.
