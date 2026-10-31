# Writing methods

These are four written methods for turning a mathematical result and its sources
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
