# Writing methods

These are four written methods, and one stage applied to every draft, for turning a mathematical result and its sources
into three papers: a detailed record, a short research paper and an exposition.
A person can read and follow them, or an AI assistant can be given them as
instructions. Follow them in the order of the table below, because each method
uses what the earlier ones produced.

The methods teach decisions that the command-line tool cannot make. Each one is
a `SKILL.md` file, which a human can read or which can be copied into an agent's
supported skill directory. The Python package does not load or execute them.
A shared **review-and-refinement loop** improves the methods from evidence
gathered while using them.

This directory and the linked local guides contain the complete working method.
No other repository, home-directory skill installation or network service is
required. Historical examples and writing references explain where choices came
from; following those external links is optional. If copying a method, preserve
its relative links or copy this directory with `docs/` and the selected example.

| Starting point | Task | Method |
| --- | --- | --- |
| Identified source files | Record claims, assumptions and their support | [Source to graph](source-to-graph/SKILL.md) |
| Selected Lean corpus, original arguments, literature and evidence graph | Reconstruct the complete selected argument | [Graph to long record](graph-to-long/SKILL.md) |
| All those sources plus the long record | Select a contribution for an expert and retain its decisive proof | [Long record to short paper](long-to-short/SKILL.md) |
| All those sources plus the long record and short paper | Teach one meaningful result in a short exposition for a specified reader | [Record to exposition](record-to-expository/SKILL.md) |
| Any draft, and every critique round | Measure the draft against its cited literature, line-edit every paragraph, re-measure and cold-read the PDF; critique packets carry the rules and measurements | [Register](register/SKILL.md) |

Use the [authoring guide](../docs/authoring.md) for the shared evidence and
review contract. These steps may expose a mathematical gap. Record that gap
and return to research; a writing step cannot fill it by changing the
claim's wording.

Inputs accumulate; the scope of the paper need not. Load the matching method
before selecting material, then apply its review questions to the actual
document. Record consequential choices and observed failures in the existing
review account. The [maintenance loop](../docs/authoring.md#use-and-improve-the-transition-skills)
explains how a revision can improve these instructions without treating every
local preference as a general rule.

## Apply the methods to another problem

1. Choose the result, its current evidence and the reader's task. Identify the
   actual sources and available checks; record missing material explicitly.
2. Start at the earliest affected step in the table. Read its method,
   reconstruct or revise that output, then inspect the downstream accounts
   that use the changed claim. A new exposition does not require rewriting an
   unchanged long proof; a corrected hypothesis does require checking its uses.
3. Review the result in reading order and follow its proof destinations. Use
   the step's completion question below, alongside the local structural checks.
4. Apply the [review-and-refinement loop](../docs/authoring.md#use-and-improve-the-transition-skills).
   Repair the current account, then test whether the lesson belongs in the
   responsible method. Preserve a local choice as local when it does not transfer.
5. Retain the reviewed edition, decisions and method version in the existing
   review record. Begin the next problem with the revised local method, rather
   than requiring its author to rediscover a lesson in old review archives.

The [authoring guide's transfer examples](../docs/authoring.md#check-transfer-beyond-the-current-problem)
show how to test a lesson outside the SK example, including a case where a
teaching repair cannot replace a proof. These are worked method checks, not
claims of improved human learning.

## Worked instances

The skills are written for any formalised result: a paper, a Lean development,
a Comparator challenge and a long reasoning record. Lessons particular to one
result are marked as instance notes in the skills or kept here.

- **SK (QAOA and the Parisi measure).** The first instance, in
  [`papers/qaoa-sk/`](../papers/qaoa-sk/). It taught statement fidelity across
  changes of mathematical setting, exact proof destinations into the long
  record, and plain words hyperlinked to pinned Lean line ranges in place of
  identifiers in prose.
- **Erdős #257.** The [method transfer](../docs/erdos-method-transfer.md)
  records the irrationality exposition and the changed-case checks it taught.
- **Quartic query separation** (OpenAI's total functions with
  R(F) ≥ Q(F)^(4−o(1))). An editorial review of the first expert companion
  and exposition found no mathematical error, yet neither was fit to send. They
  never gave the one-line reason for the exponent (R ≈ m·L with
  L ≈ m^(1−1/k), against Q ≈ √m), never placed the result after the earlier
  exponents 5/2, 8/3 and 3 with their authors, under-credited the cheat-sheet
  and Forrelation papers the construction inherits from, spent pages
  re-deriving Grover search, minimax and the Forrelation lower bound that the
  authors of the cited query-complexity literature already know, and named
  implementation theorems in place of the Comparator challenge those readers
  would audit. That case added the reader-modelling step to
  [long to short](long-to-short/SKILL.md) and the frame-before-examples rule
  to [record to exposition](record-to-expository/SKILL.md). It also showed the
  value of a short table of natural shortcuts that fail, one counterexample
  per row: it tells those readers what to take as known and what to check.

  A later round of emulated classical, quantum, formal-methods and teaching
  readers found the opposite pressure. The "Checking the statement" appendix
  grew to about 2.35 pages, longer than the classical proof it served; the
  shortcut table had grown to eight pitfalls of unequal value; the
  exposition's overview ran to about 1.8 pages with exact constants before the
  mechanism; an opening route table still called required a proof that a later
  section let readers bypass; a corrected cell-visit argument was still
  summarised in its old form in the opening; a running board kept its geometry
  while its probability law changed; a direct-product lemma was called
  necessary before the classical theorem had been tried at the actual query
  cap; and a fidelity label kept a reason that the edited lemma no longer
  supported. With the author's direction that short papers look like ordinary
  papers of the literature, this replaced the appendix by one verification
  paragraph with a statement audit in the long record, and added the priority,
  propagation, route-agreement, example-reset, instantiation and line-edit
  rules in the three skills.

## Where reader feedback goes

Fold every reader report, referee return or editorial critique back through
the [review-and-refinement loop](../docs/authoring.md#use-and-improve-the-transition-skills).
Repair the paper first, starting from a line edit of every paragraph, and
rank the findings: mathematics and hypotheses, then the reader's route and
examples, then prose, then the presentation of evidence. When a repair changes
a fact or an inference, find every abstract, opening, caption, reading guide
and absence claim across the companions that still teaches the old version.
Then route the lesson to the transition that made the
decision: reader model, selection and Lean linking to `long-to-short`;
teaching order and examples to `record-to-expository`; missing arguments to
`graph-to-long`; wrong credit or evidence status to `source-to-graph`. Edit
the existing rule when one was missed or too weak, and add a rule only when it
changes an identifiable decision. A lesson true of one result goes under
**Worked instances** above. Record which edition and reader produced it.

The long record must make its selected argument recoverable. The expert paper
must make its contribution and decisive reasoning assessable. The exposition
must let its intended reader understand and use one meaningful result. These
are different completion tests, not page-count targets. They share sources and
claim boundaries, but may have different entry points and stopping points.

The source context includes definitions, proof bodies, Lean and Comparator
receipts, original arguments and the relevant literature. A graph index or an
earlier paper is a route back to that material, not a replacement for reading
it. Each writer chooses a coherent scope, reads the resulting account in order,
and checks the exact destinations of omitted proofs. Record source-assisted
review separately from an unassisted reading attempt.

The long record preserves the selected reasoning; the expert paper selects its
contribution; the exposition teaches a narrower entry when useful. None of these
steps can mechanically verify a prose implication, upgrade a pending
check or inherit acceptance from an earlier edition. Graph-associated views
reuse the authoritative Markdown and mappings without becoming another editable
prose store.

A reader built on these documents shows what the authors wrote and what Lean
reports (axioms, dependency graph, statement types); the model's role is to
link prose to code. A wrong link is still a misattribution of support: it can
say that the wrong theorem proves a claim, or that a built declaration was
compared. Label each link and graph edge with its kind, direction and origin:
extracted from structured Lean output, or proposed by a model and how it was
checked. A long record linked to from shorter papers opens with a reading
guide that separates the required proof path from optional routes and
evidence, and that agrees with every later skip permission and bypass; every
linked destination opens with the statement it proves.

Formal bookkeeping (commit hashes, toolchains, commands, receipts, Comparator
categories and review status) lives in the long record's
[statement audit](graph-to-long/SKILL.md#audit-the-formal-statement) and the
repository metadata. The short paper and exposition report verification in one
ordinary paragraph with readable link text, as the literature reports a
computation. Their register is the literature's at its best, and the aim is
prose a strong referee would admire. The [register stage](register/SKILL.md)
applies this to every draft with the general rules in
[`register/rules.json`](../src/lean_exposition/resources/register/rules.json).
