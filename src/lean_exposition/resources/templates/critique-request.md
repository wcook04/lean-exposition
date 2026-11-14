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

First judge each draft as a whole. Use the cited passage and the draft's declared
prerequisites to say what this reader can supply and where they will need help.
Follow the argument in order. Can a specialist assess the decisive inference,
a learner use the operation in a changed case, or a reader of the complete record
reconstruct the proof with its conditions? A line edit earns priority when it
improves that reading. Use these criterion numbers to classify findings:

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
2. **Context, purpose and route.** Read each edition in order before proposing
   line edits. From a decisive result, follow the intervening pages to its next
   use. Name both passages and say what the reader must carry between them.
   Identify where the sequence breaks, or what makes the connection work.
3. **Weighting.** Try a specific cut or move across that sequence. Say what
   the later passage adds under its own hypotheses. Keep a second application
   that proves a new claim. Check what the specialist can cite, the learner
   still needs to do, or the reconstructor must be able to recover. When a prior
   edition is supplied, consider restoring stronger wording if it still fits.
4. **What they would ask.** At a decisive choice, pose the problem as it stood
   before the device was named. Withhold the chosen object and the method cue.
   What could this reader propose, and why would it meet the constraints?
   In the verdict distinguish selecting a method from checking one shown.
   Record prior exposure. If independent selection was untested, say so. Accept
   a justified alternative. A failed shortcut alone cannot establish uniqueness
   or optimality. Apply this probe where design is part of the paper's purpose.
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
   and for up to twenty consequential passages of a long record: give the quote,
   its purpose, and a reason to keep or revise it. Rank proposed revisions by
   how much each would improve a cold reading.
3. `register_rules.json` returns: any rule you relied on that the packaged set
   lacks, with specimens of at most 25 words, its scope and a limit.
4. `method_findings.json`: weaknesses in the method, each with the rule it would
   change.
5. `verdict.md`: at most one page. For each paper, give the
   consequential edit with its two passage locations, or explain why the
   sequence should stand. State what must survive and how far you actually read.

Rank findings by the difference a repair would make to the intended reader.
Give a finding only where the quoted passage supports it. State which sources
you read in full and which you only sampled.
