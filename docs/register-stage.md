# The register stage

The package turns a formal result and its sources into three papers: a long
record, a short research paper and an exposition. Mathematical care makes them
correct. It does not make them read like the field's own papers, and a referee
who meets machine cadence in the first paragraph discounts everything after it.
The register stage makes writing quality a built-in step of the funnel: every
draft is measured against the papers it cites, line-edited paragraph by
paragraph, measured again and read cold before it goes to readers or to a
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
  Its first criterion is sentence- and paragraph-level writing against the rules
  and the cited literature; evidence presentation is ranked last.
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

The rules were learned in three domains and kept general only where they held
in all three:

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
distance of our own drafts. Rules found in every field stay general. The appendix
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
why the verification, voice, rhythm and negation rules are general.

## Adopted directives

Six rules are adopted directives rather than candidates: the literature as the
floor and a strong referee's admiration as the target; a paragraph-by-paragraph
line edit in every round; no em dashes and no rhetorical contrast; formal
verification as one ordinary paragraph with readable links, no hashes, commands,
receipts or review-status disclaimers, and metadata in the repository; a
conditional result naming its input beside the statement; acknowledgements and
AI use at the end. Candidate rules are guidance for writers and reviewers; a
candidate is adopted when readers prefer papers written with it.

## Extending the rules

A lesson from a new paper or critique round goes into `register_rules.json` as
an instance under the general rule it refines. It becomes a new rule only when it
changes a decision none of the existing rules covers, and it becomes general only
after the move is found in the literature of a second field. Run
`lean-exposition register rules` to validate the file: it rejects quotes longer
than 25 words, em dashes in rule text, unknown detector features and local paths.
