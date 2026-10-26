---
name: source-to-graph
description: Build a versioned evidence graph from identified Lean or research sources, preserving exact claims, assumptions, citation roles and the limits of recorded checks.
---

# Source to evidence graph

Use this skill when source material needs an inspectable map before writing.
It records the research that exists. Proof search, mathematical review and
new theorem development remain separate tasks.

## Preconditions and inputs

- Identify the source repository, immutable revision and relevant file bytes.
  Record local edits separately rather than describing them as that commit.
- Read the actual declaration or argument, including definitions, parameters
  and assumptions that affect its meaning. A search result is a locator.
- Establish permission to include each source. A public URL alone is not a
  redistribution license. Include source bytes only under compatible terms.
- Obtain the graph contract from `docs/contracts.md`. Check the installed
  CLI with `lean-exposition --help` before using a command from another edition.

Inputs are sources, a stated research question, any recorded verification
results, and the literature passages actually inspected. A Lean receipt must
identify the checked statement and source environment. If it is unavailable,
keep execution status unknown; do not infer a successful check from a file.

## Procedure

1. Give sources stable IDs and content hashes. Keep source identity distinct
   from a run or review performed on that source.
2. Record the target as a goal. Represent declarations, reportable claims and
   additional assumptions as their own nodes. Do not replace the target by a
   convenient sufficient condition without recording their logical relation.
3. For each claim, write its domain, hypotheses, quantifier order and conclusion.
   Attach `assumption_ids`, `evidence_ids` and `citation_ids` where applicable.
   Distinguish a theorem's explicit hypothesis from an additional unproved input.
   Lean hypotheses remain in the recorded type; transitive axioms are separate
   assumption nodes. Do not replace a quantified hypothesis by a freestanding
   assertion that it holds.
4. Add edges from the consumer to its prerequisite. Keep Lean type dependencies,
   Lean value dependencies, platform decomposition and authored support relations
   in their separate categories. Dependency extraction is not a proof review.
5. For each support relation, explain what the support establishes and what
   remains to connect it to the claim. A nearby theorem with different domains
   or guards does not establish the advertised statement.
   Distinguish a conditional theorem from its application to a supplied witness.
   Keep the theorem's proof ingredients reachable and record which supplier
   discharges each premise for that same witness. Use the supported application
   contract rather than changing a logical ingredient into a citation to hide
   a premise. An ordinary-model premise and a formal-interface premise remain
   different until a source-supported transport identifies them.
   Compare entry through an assembled endpoint with entry through its explanatory
   passage. Directly selecting a conditional helper and its premises can make
   supplied obligations appear free again. Select the endpoint for endpoint
   prose; give the generic helper its own passage when its conditions are being
   explained. Test both journeys against the actual caller hypotheses. A
   deliberately conditional statement must still retain its unsupplied premises.
6. Record citations by exact version and passage. Distinguish a theorem used in
   the proof, historical credit, an adapted construction and an explanatory
   comparison. A citation may have more than one role, each stated explicitly.
   The current schema puts the version on the source, the passage in citation
   `locator`, and the local role in identified graph `notes` or a later passage's
   `rationale`. It does not define extra citation-role or edge-rationale fields.
7. Preserve useful failures with the attempted implication, assumptions,
   counterexample or unsuccessful check, and the precise conclusion it excludes.
   An unrun check is unknown; a failed approach need not refute the goal.
   Connect later observations to their actual subjects while retaining earlier
   plans and outcomes. A stopped controller without a recovered terminal result
   establishes neither proof rejection nor acceptance. Test that the ordinary
   evidence query reaches the observation; placing a receipt on disk alone does
   not make it available through the graph.
8. Run `lean-exposition validate GRAPH`. Inspect errors and repair the owning
   records. Select a goal with
   `lean-exposition select GRAPH --goal NODE --out SELECTED_GRAPH` when the
   next task needs only its prerequisite closure.

## Output contract

Produce one graph with `sources`, `citations`, `nodes`, `edges`, `evidence` and
`selected_goals`, plus the supporting files the bundle is permitted to carry.
Every selected claim must have a recoverable route to its source, applicable
assumptions, evidence and unresolved step. State what was inspected, sampled,
unavailable or left unreviewed in the authoring record.

Graph validation checks recorded structure and bindings. It does not establish
the adequacy of an argument, mathematical novelty, independent review or reader
understanding. A platform status must retain the platform and task it describes.

## Checks and example

Suppose a declaration proves a conclusion under an assumption `A`. Record `A`
even if a later application is expected to supply it. A claim that removes `A`
needs its own argument or remains unresolved. Linking the original declaration
to both claims does not justify the stronger one.

As a small ordinary-arithmetic example, let `n` be a natural number and record
“if `n = 0`, then `n + 1 = 1`”. The guard `n = 0` belongs with the claim.
Removing it changes the statement; `n = 1` then gives a counterexample. This
example illustrates the recording task and asserts no Lean execution.

Before handoff, check one complete consumer-to-prerequisite route by reading its
sources. Graph validation checks missing assumption and citation references;
it does not open the source files. Run `audit-sources LOCK --root SOURCE_ROOT`
when there is a compatible source lock to check the recorded bytes. Otherwise
identify the hash check actually performed. Separately ask a reviewer
whether each authored support relation is mathematically sound. Keep those two
results distinct.

Continue with [graph-to-long](../graph-to-long/SKILL.md) after selecting the
result and fixing its current claim ceiling.

## Close the transition and improve the method

Use the shared [review-and-refinement loop](../../docs/authoring.md#use-and-improve-the-transition-skills).
Record the sources inspected, graph edition, skill version and unresolved
questions in the existing review account. When a review exposes a mistaken
claim, edge, source role or checking status, repair that record and inspect its
paper uses. Test a general recording lesson outside this problem before adding
it here. A later prose improvement cannot repair an incorrect source relation.
