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

Use tables for comparisons a reader needs to make across compact entries,
such as coefficients or a short case split. A hypothesis, construction or
argument needing several sentences belongs in full-width prose, with a named
paragraph or lemma where useful. Inspect the most text-heavy material at the
delivered reading size: tall narrow text columns and largely empty neighbours
are a reason to change the form, not shrink the type.

## Preconditions and inputs

For a formally grounded record, read the selected Lean declarations, their
definitions and proof dependencies, the original mathematical arguments and
literature, and the source-bound Lean and Comparator checking receipts. Retain
access to the full selected source corpus while reporting what was actually
read. Failed, pending and unavailable checks remain those outcomes. The graph
locates these inputs. It does not replace them. Distinguish an unavailable source
from one read and found insufficient; report the scope of the corpus actually inspected.

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

Read an existing draft from beginning to end before repairing isolated passages.
At each first-use difficulty, record what the text has established and what the
next inference needs. Then consult the sources. A later definition or an author's
explanation may resolve the difficulty for the reviewer without repairing the
reading order. Keep that first response separate from the assisted reread.

1. State the question and exact current result. Explain the central mechanism
   and name the step that still needs work, if any. Do not let an incomplete
   research route read as a completed proof.
2. Make two brief maps: the result's relation to nearby literature, and the
   logical dependencies of its argument. Source order and tactic order need
   not be the best reading order. Separate a necessary input, an alternative
   proof, a later consequence and a comparison. Their position in consecutive
   sections is not an implication. State the role of a cited result at its use;
   a source pointer may supply a proof, a hypothesis or only context.
3. Explain each load-bearing transition through what is already known, what
   the next step requires, and the local argument that connects them. A graph
   edge or the word “therefore” cannot supply a missing inference.
   When changing variables, normalization or indices, give the map and derive
   the identities used. State what information it preserves; justify a reverse
   implication separately when an equivalence is claimed. Identify the finite
   observable before taking its limit: different finite expressions can converge
   to the same value, so limiting agreement cannot determine an index or map.
4. At each assumption's use, say what it permits. Check domains, endpoint
   cases, signs, parameter dependence and witness choices. If several premises
   require one witness, show that the same witness meets them together.
5. Separate constructing a sequence from proving its limiting conclusion.
   Identify the estimate or theorem that justifies a limit, infinite sum or
   interchange of operations. Expose a missing justification as an obligation.
   Likewise, an infimum formula does not supply an attaining minimizer. Before
   choosing one, identify the existence argument and its exact source location.
   Check negative scope claims as carefully as positive conclusions. A finite
   bound for each chosen witness need not be uniform over a family of witnesses.
   Before saying two results cannot be combined, write the order of choices and
   allowed parameter dependence: the fixed-witness consequence may hold while a
   uniform rate remains unavailable. Conversely, a family-wide conclusion cannot
   inherit a uniform bound from separate finite bounds without an argument.
   Distinguish the qualitative condition that makes an argument work from the
   quantitative margin used to pass strictness through a limit or control an
   approximation. State which step needs the magnitude and how its bound depends
   on the fixed inputs. Before declaring a bound unavailable, check consequences
   of existing identities and limit that claim to the argument or sources inspected.
6. Keep complete derivations and subsidiary cases at named destinations.
   Preserve a failed route when it explains an obstruction or the necessity
   of an assumption. Record what failed and what that failure leaves possible.
   Identify the first condition the route violates while retaining the
   hypotheses it does satisfy. Preserve a subsidiary proof for a stated role,
   and point to any stronger argument that supersedes its conclusion.
   At a substantial proof entry, recall the local objects and hypotheses,
   state the conclusion this section supplies and identify its next use.
   A reader arriving from a shorter paper should be able to enter, recover the
   omitted inference and return. Test that route as well as the sequential read.
   Check coverage in both directions: from each promised conclusion to its
   derivation, and from each load-bearing source mechanism to its written
   destination. An endpoint paragraph does not explain the construction supplying
   it. Split a large mapped passage at a change of mathematical interface when
   readers need to enter those arguments separately; do not make one passage
   for every implementation lemma.
7. Give computations their mathematical inputs, finite scope and role in the
   argument. Put reproducibility commands, dependency versions and run receipts
   in a verification section rather than interrupting every proof step.
   Use small calibrations to test signs, normalization and indexing across
   representations. Separate agreement in a finite example from the theorem
   transferring the general construction. Before passing signed quantities to
   an expectation limit, exhibit the actual integrability, domination or
   nonnegative-correction argument; almost-sure convergence alone is insufficient.
8. Bind each material claim and explanatory passage to graph IDs and source
   locations in the companion mapping. Include the assumptions and citations
   the passage actually uses. Mark new conjectures and unexplained bridges.
   For formal support, compare the exact Lean type and relevant definitions
   with the prose statement. Explain the object correspondence and any ordinary
   argument needed to join formal ingredients; cite the applicable receipts.
   Distinguish unfolding a definition, choosing a convention and proving a
   correspondence. When an identification uses a map, specify the map and the
   property it preserves that the next step needs. Existence of an isomorphism
   alone does not specify the map used by a later calculation. If only an invariant
   is needed, state that weaker fact; do not promise interchangeable objects.
   Name the observable and conditioning in an expectation identity. Equal means
   need not identify states, laws or operations; inspect the composition or higher
   moment actually needed by the next step.
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

Markdown remains the prose authority. A graph-associated reading view may reuse
its exact mapped passages, with their original order and surrounding unmapped
text, but traversing a graph is not a procedure for composing a proof. Preserve
headings, definitions, references and boundary cases when presenting excerpts.
The current paper view's `document_parts` provides the complete source-order
partition. `reconstruct_paper` checks the expected manifest and unchanged parts
and returns the original Markdown bytes; it cannot accept a new proof order.
Any reordered synthesis is a new authored account requiring its own review;
do not store a second editable copy of each paragraph in graph nodes.

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

For the SK gap argument, an algebraic positivity certificate supplies only one
input. The record must also locate the analytic signs, boundary flux control,
approximation and endpoint contact needed to use it. Distinct recorded links
help locate these obligations; the writer must check the inference joining
them. A writing skill cannot verify that inference merely by requiring a map.

The SK record's [formal-interface discussion](../../papers/qaoa-sk/long/reasoning-record.md#formal-interfaces)
illustrates another correspondence check: a sampled-chord limit and an ordinary
right derivative are different statements, and a convexity argument bridges
them. Preserve that argument rather than describing the difference as notation.
Kevin Buzzard's
[discussion of mathematical equality](https://www.youtube.com/watch?v=MPaJP5DI574&t=1089s)
(2024, 18:09–20:35) provides a related warning: the identification needed for
a calculation can require more information than a shared invariant does.

Use [long-to-short](../long-to-short/SKILL.md) for a research paper, or
[record-to-expository](../record-to-expository/SKILL.md) for a teaching paper.

Retain the selected inputs, decisions and observed reconstruction failures in
the existing review record, following [skill use and maintenance](../../docs/authoring.md#use-and-improve-the-transition-skills).
The [Erdős method transfer](../../docs/erdos-method-transfer.md) supplies worked
cases of argument selection, complete construction and informative failures.
