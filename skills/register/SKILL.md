---
name: register
description: Line-edit a short paper, exposition or long record until its prose meets and then exceeds the register of the papers it cites. Runs after every long-to-short and record-to-expository draft and after every critique round; measures the draft against a profile of its own cited literature, edits every paragraph, re-measures and cold-reads the rendered PDF. Never changes mathematics, hypotheses or attribution.
---

# Register: write better than the field's own papers

Use this skill whenever a draft exists: after [long to short](../long-to-short/SKILL.md)
or [record to exposition](../record-to-expository/SKILL.md) produces or revises a
paper, after [graph to long](../graph-to-long/SKILL.md) revises the long record, and
after every critique round has been repaired. Nobody needs to ask for it; a draft
is not ready to send until this stage has run on it.

The papers a manuscript cites set the floor for its prose. The aim is higher:
prose that a strong referee in that field would single out as better written than
the source preprint it explains. Mathematical care does not deliver this on its
own. Drafts produced with AI assistance have a recognisable register (even
sentences and paragraphs, a document announcing its own structure, contrast
frames, chains of negations, status sentences after every theorem, intensifiers),
and a referee discounts the paper within a paragraph of seeing it. Word bans do
not fix this. Learning the moves the field's own papers make, and editing every
paragraph with them, does.

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

Pick at least three cited papers closest to the manuscript in genre: for a short
paper, research papers proving results of the same kind; for an exposition, the
field's surveys and lecture notes where the citations include them, and otherwise
the best-written research papers; for a long record, the longest careful papers
cited. Add the source preprint the paper explains. Use the full text (a
`pdftotext` extraction or the TeX source); the profiler reads `.tex`, `.md` and
`.txt`, and a directory's `extracted.md`.

### 2. Extract the moves, with specimens

Read the first four pages and one proof section of each reference paper. For each
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
which prose was read.

### 4. Line-edit every paragraph

Work through the rendered order of the manuscript, every paragraph, including
the abstract, captions and the verification paragraph. For each paragraph write
down three things before editing it:

- **What it is for**: the one job this paragraph does for this reader.
- **What is weak**: the specific sentences, measured against the moves from step 2
  and the rules for this stage. Start with the sentences the report quoted.
- **The rewrite**: the new paragraph, in the moves of the reference papers.

There is always something to improve in a sentence. Leave a paragraph unchanged
only with a stated reason. Imitate moves, never text: never copy a sentence from
the literature and never imitate a named author's voice. Keep this edit log with
the revision record (the companion mapping's review notes, or the round's
adjudication file).

Rules that most often decide a short paper's first impression: the abstract
states the result first (RG-03); the introduction opens with the object or the
field's question (RG-04); formal verification is one ordinary paragraph with
readable link text, and no hashes, commands, receipts, review-status disclaimers
or repository metadata appear in the paper (RG-20); acknowledgements and AI use
come at the end (RG-24); no em dashes and no "not X, but Y" (RG-17).

### 5. Measure again

Re-run `compare` with `--baseline <previous edition>` and report both runs. The
aim is movement toward the literature on the features the edit addressed, and no
new distance elsewhere; entering every range is never the target.

### 6. Cold-read the rendered PDF at reading size

Render the paper as it will be read and read it in order at normal size, as a
reader new to the project would. Check that the first page states the result,
that no repository apparatus is visible, that link text reads as ordinary words,
that headings name mathematics and that nothing announces the paper's own
quality. Fix what you find and re-render.

### 7. Report

Report: the reference papers used; the moves table; the before and after
measurement with the features that moved; the paragraph edit log; any finding
returned to an earlier transition; and any rule that helped, failed or needs a
limit. A lesson that holds in a second field goes into `register_rules.json` as
a candidate instance under the general rule it refines, or as a new rule only
when it changes a decision none of the existing rules covers.

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
and `lean-exposition register packet`), so reviewers judge sentences and
paragraphs first and evidence presentation last.

## Completion question

Would a strong referee in this field, reading the rendered paper cold, find its
prose at least as good as the best paper it cites, with every mathematical
statement unchanged?
