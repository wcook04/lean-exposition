# {title}

This packet holds drafts of papers about one mathematical result, produced from
its sources and, where one exists, its formal proof:

{documents}

Execute the assignment now, in one sustained response, and return a ZIP. Do not
return only a plan or an acknowledgement.

## What this pass is for

Read as a panel of experts from the community the drafts cite. For each panel
member, adopt the background and priorities of the authors of one cited paper
("a reader with the background of the authors of the paper on X"). Do not
attribute opinions, quotations or reactions to any real, named person; each
perspective is anchored in what a cited paper shows its authors know and care
about. Use the supplied literature to make each perspective concrete and to check
every attribution the drafts make.

Judge the drafts against these criteria, **in this order of weight**:

1. **Sentence- and paragraph-level writing.** Is every paragraph doing one job
   for this reader, and is every sentence as good as the best sentences in the
   cited papers? Work paragraph by paragraph: for each weak paragraph quote it,
   say what it is for, what is weak, and the direction of the rewrite. Use
   `register/REGISTER_RULES.md` (the general rules, with specimens from the
   literature) and `register/measurement.txt` (the measured distance of each
   draft from a profile of the cited papers, with the sentences that contribute
   most). The cited literature's register is the floor; the target is prose a
   strong referee would admire. The measurement points at sentences to reread;
   it never passes or fails a paper.
2. **Context, purpose and route.** Does each document give the question, the
   prior position, the key idea and what is new before technical detail, and say
   who it is for and what comes next?
3. **Weighting.** Where do the drafts overweight what these readers already know
   and underweight what is new, surprising or delicate to them? Estimate page
   share now against page share deserved.
4. **What they would ask.** For each section, figure, table, example and
   appendix: what is it for, does it earn its place, why is a proof done this way
   and not the obvious way, why is a step spelled out or skipped.
5. **Credit and contribution.** Is each prior result credited by author and
   precise statement at its use, and is a new explanation kept distinct from new
   mathematics?
6. **Statement fidelity.** For every result linked to a formal statement, does
   the document say whether the formal statement is the same, stronger or
   weaker, and does each shortened or explained statement keep its hypotheses?
7. **Evidence presentation.** Is verification reported the way the literature
   reports a computation, in one ordinary paragraph with readable links, with
   versions and receipts left to the repository and the long record?

Also say what would make these readers stop reading and where, and what they
would admire and must survive any revision. Where a weakness comes from the
writing method in `skills/` rather than this instance, say so in
`method_findings.json`, naming the skill or register rule it would change.

## State of the evidence

Do not spend findings re-verifying receipts; the packet records which checks ran
and their outcomes. Do judge whether the drafts present the evidence in a way
these readers would trust and use. If you believe you have found a mathematical
error, mark it `error` and give the exact step and why it fails.

## This packet's assignment

{job}

## Return format

Return one ZIP containing:

1. `findings.json`: an object with `packet`, `panel` (the perspectives adopted,
   each with the cited paper it is anchored in and what that reader already
   knows) and `findings`, a list. Each finding has `id`; `paper`; `perspective`;
   `locator` (`section` and `quote`, an exact phrase of at most 25 words from the
   current text, optional `pdf_page`); `criterion` (1 to 7 above); `kind`
   (`line_edit`, `question`, `overweighted`, `underweighted`, `missing`,
   `misplaced`, `unclear`, `credit`, `error`, `evidence_presentation` or `keep`);
   `severity`; `finding`; `why_it_matters`; `suggested_direction`; optional
   `evidence` locators in the literature or formal source.
2. `line_edits.md`: for every paragraph of the short paper and the exposition,
   and for the weakest twenty paragraphs of a long record: the quote, what it is
   for, what is weak, and the direction of the rewrite, ranked by how much each
   would improve a cold reading.
3. `register_rules.json` returns: any rule you relied on that the packaged set
   lacks, with specimens of at most 25 words, its scope and a limit.
4. `method_findings.json`: weaknesses in the method, each with the rule it would
   change.
5. `verdict.md`: at most one page: would this panel read to the end, the five
   changes that matter most, and what must be kept.

Aim for several dozen findings, most of them under criterion 1. Every finding
must quote the current text. State which sources you read in full and which you
only sampled.
