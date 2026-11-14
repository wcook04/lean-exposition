---
name: register
description: Review every paragraph of a short paper, exposition or long record against relevant cited literature. Runs after drafting and critique repair; selects genre-matched comparisons, inspects measured prose, edits for a stated reader benefit, re-measures and reads the rendered paper. Preserves successful prose, mathematics, hypotheses and attribution.
---

# Register: write better than the field's own papers

Use this skill whenever a draft exists: after [long to short](../long-to-short/SKILL.md)
or [record to exposition](../record-to-expository/SKILL.md) produces or revises a
paper, after [graph to long](../graph-to-long/SKILL.md) revises the long record, and
after every critique round has been repaired. Nobody needs to ask for it; a draft
is not ready to send until this stage has run on it.

This stage applies the [three paper purposes and their deliverables](../../docs/authoring.md#what-makes-each-kind-of-paper-good),
including [standard terminology and literature-grounded prose](../../docs/authoring.md#mathematical-register-and-literature-grounded-prose).
Name the reader capability each proposed language edit should improve. A
specialist needs precise compression, a learner needs the operation behind the
term, and a complete record needs explicit inferences throughout its longer
proofs. Use accumulated review diagnoses to select those needs; do not collect
every proposed addition into the next draft.

The papers a manuscript cites set the floor for its prose. The aim is higher:
prose that a strong referee in that field would single out as better written than
the source preprint it explains. Mathematical care does not deliver this on its
own. Drafts produced with AI assistance have a recognisable register (even
sentences and paragraphs, a document announcing its own structure, contrast
frames, chains of negations, status sentences after every theorem, intensifiers),
and can distract from the argument. A detector cannot establish a referee's
response. Learn the moves the field's papers make and review every paragraph
for its reader's task; a word ban or an improved rate cannot establish clarity.

The general method is the rule set in
[`register_rules.json`](../../src/lean_exposition/resources/register/rules.json):
26 rules, each naming the failure it fights, the move that replaces it, a limit,
specimens from published papers in three fields, and the local cases it was
learned from. `lean-exposition register rules --scope short --format markdown`
prints the rules for one stage.

## What this stage never changes

Statements, hypotheses, quantifier order, constants, proofs, citations, credit and
the evidence class of every claim stay exactly as the earlier transition left
them. If the line edit exposes a weakness in any of these, record it and return
to the transition that owns it (see the [skill index](../README.md)). A sentence
may move, merge or split; its mathematical content may not change. Check every
edited statement against the long record before finishing.

## Procedure

### 1. Choose the reference papers from the paper's own citations

Choose a small set of cited works close to the manuscript in genre: for a short
paper, research papers proving results of the same kind; for an exposition, the
field's surveys and lecture notes where the citations include them; for a long
record, extended arguments and reference treatments. If no matched teaching
source exists, use research passages as a qualitative comparison and state
the mismatch. Add the source preprint the paper explains. Choose one declared
edition per work for a numeric baseline; keep other editions for source
comparison. A mixed literature shelf is useful context, not a common target
distribution for all three documents. Use the full text (a
`pdftotext` extraction or the TeX source); the profiler reads `.tex`, `.md` and
`.txt`, and a directory's `extracted.md`.

### 2. Extract the moves, with specimens

Read the opening and a relevant proof section of each reference paper. For a
teaching difficulty, also read the passage that teaches the same operation;
an arbitrary page sample may miss it. Record the actual inspected scope. For each
move below, write how the papers make it, with one quoted specimen of at most 25
words and its location: the first sentence of the abstract and of the
introduction; how and where the main result is announced; how prior work is
introduced; how a proof is narrated; how notation is introduced; section titles
and organisation; how limitations and open questions are stated; how computation
or verification is reported; sentence length and variety, "we", parentheses;
what they have that the draft lacks (an organisation paragraph, acknowledgements
at the end, a notation paragraph, numbered cross-references, a comparison table).
`lean-exposition register specimens <papers> --feature section_opening` (or
`paragraph_opening`, `result_announcement`, any feature name) collects candidate
specimens across the papers.

### 3. Measure the draft

```sh
lean-exposition register profile <reference papers or dirs> --name "<field> citations" --out profile.json
lean-exposition register compare --profile profile.json --format text <draft>
```

The report gives, per feature, the draft's value, the corpus median and IQR, the
distance in IQR units, the rules whose detector names that feature, and the
sentences that contribute most. It is a detector: it says where to look. A good
paper can sit outside the range on a feature for a reason, and a paper inside
every range can still read badly. Use `register dump <draft>` to see exactly
which prose was read. Inspect representative extracted paragraphs against their
source pages before interpreting segmentation or punctuation statistics. Exclude
damaged extraction, slides and nonprose blocks from paragraph comparisons, or
report that comparison as unavailable. Compare like regions: the argument,
captions and evidence appendix have different jobs. Separate them for the
comparison when relevant, retaining the whole-document profile as context.
The threshold flag concerns distance from the median in IQR units (or the
reported floor); being beyond the observed corpus minimum and maximum is a
different observation. Neither is a z-score, significance test or quality score.

### 4. Line-edit every paragraph

Work through the rendered order of the manuscript, every paragraph, including
the abstract, captions and the verification paragraph. For each paragraph write
down three things before editing it:

- **What it is for**: the one job this paragraph does for this reader.
- **What needs attention**: a specific reader difficulty, informed by the moves
  from step 2 and the rules for this stage. A flagged word may instead carry a
  quantifier, attribution or useful comparison; preserve that function.
- **The decision**: retain, move, shorten, split or explain, with the revised
  paragraph when a change improves its job.

Review every sentence; changing every sentence is not an objective. A precise
paragraph that already supplies its inference is a successful keep decision.
Retain standard terms consistently rather than cycling through synonyms or
inventing house names. Explain unfamiliar operations at the audience's level.
Use a humanizer skill, when available, within this paragraph review to remove
stock rhetoric and ambiguous referents. Its generic preferences cannot override
the mathematical register, meaningful contrasts or necessary qualifications.
The [shared language audit](../../docs/authoring.md#mathematical-register-and-literature-grounded-prose)
states the complete procedure when no such skill is installed. Re-read the
whole revised manuscript in sequence; a detector or changed word count cannot
perform that review.
For consequential edits, check the objects, quantifiers, events, conditioning,
resource guarantees and credit before and after, following the
[active-object checks](../../docs/authoring.md#check-the-active-objects-and-claims).
Imitate moves, never text: never copy a sentence from
the literature and never imitate a named author's voice. Keep this edit log with
the revision record (the companion mapping's review notes, or the round's
adjudication file).

Rules that most often decide a short paper's first impression: the abstract
states the result first (RG-03); the introduction opens with the object or the
field's question (RG-04); formal verification is one ordinary paragraph with
readable link text, and no hashes, commands, receipts, review-status disclaimers
or repository metadata appear in the paper (RG-20); acknowledgements and AI use
come at the end (RG-24); empty rhetorical contrasts are removed while meaningful
comparisons survive (RG-17). Author preferences are not tests of comprehension.

### 5. Measure again

Re-run `compare` with `--baseline <previous edition>` and report both runs. The
aim is to repair the stated reader difficulty while preserving meaning. Report
metric movement descriptively. A useful worked explanation may move farther
from a research-paper median; judge it by the operation it now enables.

### 6. Cold-read the rendered PDF at reading size

Render the paper as it will be read and read it in order at normal size, as a
reader new to the project would. Check that the first page states the result,
that repository apparatus stays in its designated reference region, that link text reads as ordinary words,
that headings name mathematics and that nothing announces the paper's own
quality. Fix what you find and re-render.
Read the densest table, longest link labels and reference appendix at the
delivered size. No clipping or page overflow is only a geometric check: cramped
wrapping, long identifier strings and several sentences in narrow status columns
can still be unreadable. Keep compact tables that support an actual comparison;
move extended explanations into full-width paragraphs with natural-language
links resolved by the existing index. Preserve exact declaration metadata behind
those links. A receiving editor inspects the revised output, and user rejection
supersedes an earlier agent acceptance. Re-render and reinspect the affected
pages after the repair; prose conversion alone is not proof of readability.

### 7. Report

Report: the reference papers and editions used; the moves and their source
locations; the before and after
measurement with the features that moved; the paragraph edit log; any finding
returned to an earlier transition; and any rule that helped, failed or needs a
limit. A lesson that holds in a second field goes into `register_rules.json` as
a candidate instance under the general rule it refines, or as a new rule only
when it changes a decision none of the existing rules covers. Corpus occurrence
is descriptive transfer evidence. Editorial judgment, agent reconstruction and
observed reader performance are separate kinds of evidence; report only the
kind actually obtained. Test a proposed generalisation on two differently
shaped cases and an exception using the shared [review loop](../../docs/authoring.md#assess-revise-generalise-and-check).

## Where this stage sits in the funnel

```text
sources -> graph -> long record -> short paper / exposition -> critique rounds
                        |                 |                          |
                    register          register                   register
```

It runs on the long record after `graph-to-long`, on each companion after its
transition, and again after every critique round, before the next packet is
built. A critique packet carries the rule set and this stage's measurement of the
drafts (see [the critique request](../../src/lean_exposition/resources/templates/critique-request.md)
and `lean-exposition register packet`). Reviewers judge the whole reading route
first, then use the paragraph review to find the edits that most improve it.

## Completion question

Would a strong referee in this field, reading the rendered paper cold, find its
prose at least as good as the best paper it cites, with every mathematical
statement unchanged?
