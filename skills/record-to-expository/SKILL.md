---
name: record-to-expository
description: Teach a selected result using the Lean corpus, complete long record and short paper, choosing prerequisites, examples and proof detail for a specified reader without weakening assumptions or evidence boundaries.
---

# Research record to expository paper

Use this skill when the goal is to help a reader understand and use an already
established result. In the three-paper funnel, use the Lean corpus, original
sources and receipts, the long record and the short paper together. The short
paper identifies the contribution; the long record supplies complete arguments;
the original evidence fixes what can be claimed. The exposition derives its
mathematical authority from that argument and evidence, not from easier language.

Keep the Lean and Comparator outcomes and the relevant source literature
available throughout. They constrain the account; they do not choose its
teaching order or prove that a reader understands it.

## Preconditions and inputs

Choose an established result and read its complete argument, source statement,
assumptions, citations and recorded evidence. Identify the intended reader and
the background they can reasonably supply. State what they should be able to
reconstruct or do after reading.

Read the short paper to identify the result and its position, then follow its
proof destinations through the long record and original sources. Compare the
selected formal statement and definitions with the account being taught. Keep
all upstream context available, but report the passages actually inspected.
For a standalone exposition without a short paper, explicitly select the result
and scope that the short paper would otherwise supply; do not invent that input.

Select one central result and its explanatory endpoint before drafting. A rich
source corpus is context for the author, not a requirement to teach every
consequence in one article. Include a prerequisite, example or proof detail
when it helps the reader understand that result. Route substantial further
results to the existing long record and give only the outlook needed to place
the selected result. Length follows the explanation; do not equate exposition
with an expanded version of the entire research record. Aim for a short,
complete route into one meaningful result. If its prerequisites make that
impossible for the stated reader, narrow the result or state a stronger reader
prerequisite rather than appending every upstream chapter.

Name the operations and results the reader is assumed to know, not just a
level such as “graduate”. Separate those from what the exposition must teach.
For each unfamiliar prerequisite used in the proof, find its first use and
decide whether to explain it there or supply a precise accessible reference.
Knowing a lemma does not imply knowing why this argument needs it.

If the argument is incomplete, either select an established part or make the
unresolved step an explicit subject of the exposition. Do not introduce a new
research claim as though explaining it made it established.

## Procedure

1. State the mathematical question and exact result in language the reader can
   parse. Explain unfamiliar prerequisites in an order that makes their later
   purpose visible. Keep the headline theorem easy to find.
2. Choose a small, nontrivial example that reveals the mechanism or a necessary
   assumption. Show the operation, what changes and what stays fixed. Say which
   aspects of the general theorem the example does not represent. Choose its
   size to expose the difficulty: a case where all values are distinct cannot
   teach why multiplicities matter. Work through the relevant calculation or
   construction, including the checks that make the example admissible.
3. Move from that example to the general argument. Explain why a construction
   or estimate is needed before introducing its machinery. Keep the hard
   inference visible: write down the last established fact, the next required
   conclusion and the local argument joining them. Identify the hypothesis
   used and what later choices may depend on. State the needed accuracy before
   choosing a bound or parameter. For an iterative construction, explain both
   why the next choice exists and why the choices reach the stated conclusion.
   A named technique or an analogy does not supply that connection. If the
   complete source argument does not supply it, refer the gap for research review.
   An imported estimate may remain an explicitly stated input: teach what it
   guarantees and how it is used, with a full-proof destination. Do not replace
   it with an intuitive picture that quietly claims to prove the estimate.
4. Introduce symbols and terminology by their mathematical roles. Keep standard
   terms when their definitions fit. Avoid importing local research nicknames
   that require a separate glossary to decipher the statement.
5. Attach material assertions to the same graph claims, assumptions, evidence
   and citations used by the research record. Mark additional teaching examples
   and verify them. An example illustrating a theorem is not a separate proof
   of the theorem. Check its map against the example's actual hypotheses as
   well as its words. A conditional calculation with a nonminimising coefficient
   cannot select a minimiser-only convergence theorem merely because both use
   the same construction.
6. Add a changed-case task: alter one hypothesis, parameter or example and ask
   the reader what survives, keeping the other conditions explicit. Choose a
   change that requires using the key inference, not repeating its wording.
   Recheck choices that depend on the changed parameter; holding them fixed
   is itself a condition to justify.
   Give a justified answer separately from the question, or mark it open.
   Distinguish a false conclusion from an inconclusive test or a proof that no
   longer applies. An open question can teach the boundary, but cannot supply
   a correctness verdict on the reader's answer.
7. Distinguish explanatory reconstruction from discovery history. Credit source
   theorems, borrowed constructions and teaching models by their actual roles.
   A helpful stylistic comparison does not justify the local mathematics.
8. Ask a reader to state the result with its assumptions, reconstruct the key
   inference and apply it to the changed case. Record the document version,
   task, response and any hints or access to the answer. Where reconstruction
   stops, identify what the reader had established and what the next step
   needed; revise that passage and record any subsequent attempt separately.
   Say whether this was author self-review, agent review or an independent
   reader attempt. If no reader took part, leave that check unperformed.
   One successful attempt does not establish improved learning in general.
   First read the complete exposition in sequence at the declared prerequisite
   level. Record first-use stalls before looking at a glossary, long proof or
   answer; then use those sources to diagnose them. Reorder or explain at the
   point of need. An assisted reader finding the answer later does not establish
   that the original sequence worked.
9. Run `lean-exposition check-bundle DIR`, inspect the delivered document and
   follow each proof and citation destination. If diagrams are added, inspect
   them at the intended viewing size and verify their mathematical conventions.

## Output contract

Produce an expository paper and its stage mapping. Retain the selected goal,
claim, assumption, citation and unresolved IDs, graph hash and passage-level
links. Record the reader prerequisites, the purpose of each worked example and
the changed-case questions with their answers or explicit open status.

Use the existing mapping's `review_notes` strings for the review performed,
its scope, observed difficulties and remaining checks; do not add teaching or
review fields to the schema. The [authoring guide](../../docs/authoring.md)
defines passage markers, hashes and review states. Keep prerequisites and
teaching content in the document; keep the review account in its mapping.

Keep the same evidence class and claim boundary as the source record. If the
pass discovers a new theorem or a defect, record it for research review and
update the source authority before advertising a changed conclusion.

Record why this result was selected, what supporting material was taught or
routed to the long record, and where a sequential reading stopped. Follow
[skill use and maintenance](../../docs/authoring.md#use-and-improve-the-transition-skills)
when a revision suggests a general improvement to these instructions.

## Checks and example

For the natural-number claim “if `n = 0`, then `n + 1 = 1`”, first let the
reader substitute zero. Then ask whether the conclusion still holds when
`n = 1`. It does not: the sum is two. This elementary changed case checks that
the reader noticed the guard; it does not establish understanding of a larger proof.

Suppose an example uses a value strictly inside the theorem's permitted range.
Also consider an endpoint or excluded value when it clarifies a hypothesis.
If the proof uses a strict inequality there, explain why the endpoint needs a
different argument. Do not infer the endpoint conclusion from the interior
picture or silently enlarge the theorem's domain.

Accept the teaching pass only for the review actually performed. A checked
example, a compiled document and a reader's successful reconstruction answer
different questions. Preserve those distinctions in the review record.

The [method sources](../../docs/authoring.md#method-sources-and-redistribution)
identify the pinned public writing guides and their licences. In the compact
guide, instructions 4–7 and 14 inform the dependency, example and reconstruction
checks here; the long guide's reading, worked-revision and practice sections
explain their limits. This skill supplies authoring instructions, not evidence
that a reader has understood a particular paper.

The [Erdős method transfer](../../docs/erdos-method-transfer.md) gives inspected
cases behind these instructions, including changed parameters and restrictive
hypotheses. A case whose hypothesis fails need not refute the conclusion.
