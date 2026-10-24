---
name: graph-to-long
description: Reconstruct a long reasoning record from a selected Lean corpus and original arguments, using the evidence graph to preserve statements, proof dependencies, citations and unresolved steps.
---

# Evidence graph to long reasoning record

Use this skill to explain and preserve an argument already represented by
source records. Organize the reasoning record around the argument's dependencies
and the reader's needs.

The record is a citable mathematical document: exact statements, reconstructible
derivations, source references and identified checks. Give substantive results
and unresolved steps stable destinations. Its length follows the detail needed
to recover the argument.

## Preconditions and inputs

For a formally grounded record, read the selected Lean declarations, their
definitions and proof dependencies, the original mathematical arguments and
literature, and the source-bound checking receipts. The graph locates these
inputs. It does not replace them. Distinguish an unavailable source from one
read and found insufficient; report the scope of the corpus actually inspected.

Read the selected goal, its prerequisite closure, exact source statements and
evidence records. Run `lean-exposition validate GRAPH`. Resolve conflicting
claims before drafting, or record the competing statements and the specific
check still needed. A structurally valid graph may contain an incorrect
interpretation.

Choose the reader and assumed background. Identify the result to explain,
its evidence class and its relation to the motivating question. Inputs include
the graph, source passages, ordinary arguments, relevant computations and the
citation record. Access to a source is not evidence that its proof was read.

For each necessary step, inspect the statement, its definitions and hypotheses,
and the actual argument or proof source. If only an endpoint or outline is
available, identify the missing inference and keep that proof section empty.
If sources disagree, name the conflicting versions and the comparison needed
to resolve them. Continue with sections whose support is unaffected. A name,
dependency list, source hash or platform status cannot supply a derivation.

## Procedure

Before drafting, compare the supported candidate results and choose the question
this record will answer. Prefer a coherent, useful mathematical contribution
with recoverable support over a large declaration count. Select its necessary
proof closure, useful alternative arguments and informative obstructions;
unrelated corpus material remains available without becoming a chapter.

1. State the question and exact current result. Explain the central mechanism
   and name the step that still needs work, if any. Do not let an incomplete
   research route read as a completed proof.
2. Make two brief maps: the result's relation to nearby literature, and the
   logical dependencies of its argument. Source order and tactic order need
   not be the best reading order.
3. Explain each load-bearing transition through what is already known, what
   the next step requires, and the local argument that connects them. A graph
   edge or the word “therefore” cannot supply a missing inference.
   When changing variables, normalization or indices, give the map and derive
   the identities used. State what information it preserves; justify a reverse
   implication separately when an equivalence is claimed.
4. At each assumption's use, say what it permits. Check domains, endpoint
   cases, signs, parameter dependence and witness choices. If several premises
   require one witness, show that the same witness meets them together.
5. Separate constructing a sequence from proving its limiting conclusion.
   Identify the estimate or theorem that justifies a limit, infinite sum or
   interchange of operations. Expose a missing justification as an obligation.
   Likewise, an infimum formula does not supply an attaining minimizer. Before
   choosing one, identify the existence argument and its exact source location.
6. Keep complete derivations and subsidiary cases at named destinations.
   Preserve a failed route when it explains an obstruction or the necessity
   of an assumption. Record what failed and what that failure leaves possible.
   Identify the first condition the route violates while retaining the
   hypotheses it does satisfy. Preserve a subsidiary proof for a stated role,
   and point to any stronger argument that supersedes its conclusion.
7. Give computations their mathematical inputs, finite scope and role in the
   argument. Put reproducibility commands, dependency versions and run receipts
   in a verification section rather than interrupting every proof step.
8. Bind each material claim and explanatory passage to graph IDs and source
   locations in the companion mapping. Include the assumptions and citations
   the passage actually uses. Mark new conjectures and unexplained bridges.
   For formal support, compare the exact Lean type and relevant definitions
   with the prose statement. Explain the object correspondence and any ordinary
   argument needed to join formal ingredients; cite the applicable receipts.
9. Run `lean-exposition check-bundle DIR`. Review the argument separately,
   then inspect the delivered Markdown or rendered paper and its references.

## Output contract

Produce the long record and its stage mapping. Preserve `selected_goal_ids`,
`claim_ids`, `citation_ids`, `assumption_ids`, `unresolved_ids` and the graph
hash. Record passage-level correspondence rather than treating a document-wide
source list as support for every sentence.

Use ordinary section anchors for proof destinations. Passage markers bind
authored text separately. The current mapping has no cross-document-link or
per-passage evidence-ID field: put exact destinations and explanations in the
prose and `rationale`, and follow claim nodes to their evidence records.

The record must let another reader recover the principal proof, the role of
each essential assumption, the precise citations and the unfinished work.
Keep formal proofs, ordinary proofs, finite checks and external inputs distinct.
Do not mark semantic or reader review as performed merely because a checker
passed. A generated scaffold stays `scaffold` until someone authors it.

## Checks and example

For the illustrative natural-number claim “if `n = 0`, then `n + 1 = 1`”, the
argument substitutes the assumption into the sum to obtain `0 + 1 = 1`.
The record should make that use of the guard explicit. A declaration inventory
listing addition and equality would locate ingredients without explaining the step.

If an argument repeatedly chooses a legal next step, ask what proves that
the resulting infinite object has the claimed property. The record must name
that additional argument or list it as unresolved. The existence of every
finite choice alone does not explain completion.

Have a cold reader reconstruct the result, the hard transition and one
assumption's use without consulting the author. Record the exact point where
reconstruction stops and the review's coverage. A sampled review cannot stand
for the whole record. Repair the affected claim or explanation, then recheck
its dependent passages.

Use [long-to-short](../long-to-short/SKILL.md) for a research paper, or
[record-to-expository](../record-to-expository/SKILL.md) for a teaching paper.

Retain the selected inputs, decisions and observed reconstruction failures in
the existing review record, following [skill use and maintenance](../../docs/authoring.md#use-and-improve-the-transition-skills).
The [Erdős method transfer](../../docs/erdos-method-transfer.md) supplies worked
cases of argument selection, complete construction and informative failures.
