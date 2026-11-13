# The register stage

The package turns a formal result and its sources into three papers: a long
record, a short research paper and an exposition. Mathematical care makes them
correct. It does not by itself make their arguments clear or their prose useful
to the field's readers.
The register stage makes writing quality a built-in step of the funnel: every
draft is compared with suitable passages from the papers it cites, reviewed
paragraph by paragraph, measured again and read in sequence before it goes to readers or to a
critique round.

```text
sources -> graph -> long record -> short paper / exposition -> critique rounds
                        |                 |                          |
                    register          register                   register
```

The procedure is the [register skill](../skills/register/SKILL.md). It never
changes mathematics, hypotheses or attribution; a weakness there returns to the
transition that owns it.

## Three parts

- **A rule set**, [`register_rules.json`](../src/lean_exposition/resources/register/rules.json).
  Twenty-six general rules form one writing method. Each names the writing
  failure it fights, the move that replaces it, a limit, the stages it applies to
  (short, expository, long), an optional detector, specimens of at most 25 words
  from published papers, the result of a test in three fields, and the local
  rules it was generalised from, with their before-and-after examples.
  `lean-exposition register rules --scope short --format markdown` prints the
  rules for one stage.
- **A profiler**, [`register.py`](../src/lean_exposition/register.py), standard
  library only. It reads TeX, Markdown, plain text and `pdftotext` extractions,
  builds a profile of any set of papers, and reports how far a draft sits from
  that profile on each of 37 prose features (in units of the corpus
  inter-quartile range), naming the rules whose detector covers each feature and
  quoting the sentences that contribute most. It is a detector, never a gate.
- **A critique contract**, [`critique-request.md`](../src/lean_exposition/resources/templates/critique-request.md).
  Reviewers judge the whole paper against its reader's task, then locate
  consequential problems through paragraph review against the cited literature.
  `lean-exposition register packet` writes the rules, the profile, the
  measurement of every draft and the filled request into a packet directory, so
  every round carries them without anyone remembering to ask.

```sh
lean-exposition register profile literature/*/ --name "cited papers" --out profile.json
lean-exposition register compare --profile profile.json --format text paper.md
lean-exposition register packet --draft short paper.md --draft expository exposition.md \
    --literature literature/*/ --title "Round 7: writing" --out packet/
```

## Three fields, one method

The rules were learned in three domains. Their retained probes describe corpus
occurrences or feature distributions; they do not establish improved reader
understanding or prove that a rule is suitable everywhere:

- **Number theory**: a short paper and a long record on Erdős problem #257
  (irrationality of Lambert-type series), with critique rounds over several
  Erdős problems;
- **Probability**: the short paper, exposition and long record on full support
  of the zero-temperature Sherrington–Kirkpatrick order parameter in
  [`papers/qaoa-sk/`](../papers/qaoa-sk/);
- **Theoretical computer science**: an expert companion, exposition and long
  record on the nearly quartic separation between randomized and quantum query
  complexity, with a literature register built from its cited query-complexity papers.

The local rules from these cases (about two hundred from the Erdős rounds and
twenty-five from the quartic register) repeated one another in different
clothes. Each was read as evidence of the failure it was fighting, and the set
was rewritten as general rules: where many local rules were one principle they
were merged, and where one local rule held two principles it was split (where
verification is reported versus the named-input exception; the mathematical
"we" versus sentence rhythm; collecting verification once versus reporting a
computation with its range). Every local rule survives as an instance under its
general rule, so no specimen or example is lost; the `history` list records
which local rules each general rule absorbs.

Each general rule was then tested against the cited literature of all three
fields: a move the rule prescribes was searched for in each corpus, or a
detector's corpus median was checked against the direction the rule asks for.
The results are stored in each rule's `domain_test`, together with the measured
distance of our own drafts. These are descriptive transfer checks, not tests of
effectiveness. A move's occurrence in several fields supports investigating it;
its task and exception determine where to use it. The appendix
rule for the long record was not found in the probability citations and stays a
candidate scoped to the long record; the lecture-note voice is scoped to the
exposition; the verification-paragraph rule is scoped to the short paper and
exposition, with the long record's apparatus governed separately.

The three short papers, each measured against a profile of its own cited
papers (8, 4 and 42 papers with at least 800 words of prose), sat far from their
literature on the same features. Distances are in corpus inter-quartile ranges:

| Feature | Number theory | Probability | Computer science |
| --- | --- | --- | --- |
| Status vocabulary (Lean, Comparator, receipt, recorded) | +9.2 | +2.8 | +8.8 |
| "We" per 1000 words (draft against corpus median) | 2.0 against 18.0 | 2.8 against 13.2 | 5.5 against 18.0 |
| Variation of sentence length | -1.8 | -3.2 | -1.4 |
| Variation of paragraph length | -1.1 | -2.9 | -1.7 |
| Negations | +6.1 | +5.2 | +0.7 |
| Sentences opening with a connective | -1.3 | -0.1 | -1.1 |

The computer-science companion had already been through a round of register
repair, which is why its negation distance is small. Those shared distances are
why those passages were selected for editorial inspection. They do not make a
particular rate a writing objective. A mathematical negation can be essential,
and a reference appendix can properly contain substantial verification detail.

## Adopted directives

Six rules are adopted directives rather than candidates: the literature as the
floor and a strong referee's admiration as the target; a paragraph-by-paragraph
review in every round; removal of empty rhetorical contrast with punctuation
preferences distinguished from mathematical clarity; formal
verification as one ordinary paragraph with readable links, no hashes, commands,
receipts or review-status disclaimers, and metadata in the repository; a
conditional result naming its input beside the statement; acknowledgements and
AI use at the end. Candidate rules are guidance for writers and reviewers; a
candidate is adopted when readers prefer papers written with it.

## Maintaining the rules

`rules.json` is the source of truth and is edited by hand; nothing generates it.
`python scripts/register_rules.py validate` checks it: unique ids, valid scopes,
a limit for every rule, specimens of at most 25 words with no extraction damage
(placeholders for removed mathematics or citations, stranded punctuation),
detector features that exist, and no local paths. The package test suite runs
the same validation.

Each rule stores a `probe`, the literature test behind its `domain_test`.
`python scripts/register_rules.py domain-test --field NAME CORPUS_DIR CITATIONS_JSON`
re-runs every probe against a field's cited papers (a directory of
`pdftotext` or TeX extractions, kept outside the repository with the
citation each should carry) and prints whether each rule holds, with up to two
candidate specimens that pass `register.clean_specimen` and their PDF page or
section. The script writes nothing. A reviewer reads every candidate in its
source before copying it into `specimens` or `domain_test`: the filter rejects
damaged text, and only a reader can reject a sentence that is clean but does not
show the move. Rules with no clean specimen say so in `specimens_note`.

## Extending the rules

A lesson from a new paper or critique round goes into `rules.json` as
an instance under the general rule it refines. It becomes a new rule only when it
changes a decision none of the existing rules covers, and it becomes general only
after testing its decision on two differently shaped cases and an exception.
Read the relevant literature passages, retain the locators and distinguish a
source precedent from an observed reader outcome. The shared
[review loop](authoring.md#assess-revise-generalise-and-check) owns that test.

Compare each document with a declared genre and region of prose. Group editions
of the same work for a numerical baseline; inspect extraction against source
pages; keep slides, damaged text and metadata out of paragraph comparisons.
A whole-document profile can remain as context. A detector nominates a passage
for inspection; its mathematical or instructional job decides the edit, and
retaining a successful paragraph is a positive outcome.

A review export must preserve the complete active rule inventory and resolve
every rule ID referenced by its measurements and supplied skills. If private
specimens or history are omitted, remove those fields individually and disclose
the omission. Do not remove the enclosing rule. An intentionally selected
subset must identify itself and supply the referenced operative rule bodies.
