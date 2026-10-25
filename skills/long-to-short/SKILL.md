---
name: long-to-short
description: Select a short research paper using the Lean corpus, original sources and complete long record, retaining the contribution, decisive proof, hypotheses, attribution and full-proof destinations.
---

# Long reasoning record to short paper

Use this skill when an existing argument needs a coherent research paper.
Shortening is a choice of contribution and explanation. It cannot strengthen
the mathematics or upgrade its evidence.

## Preconditions and inputs

Keep the Lean corpus and its original-source and checking context available
alongside the long record, including exact Lean and Comparator outcomes and
the relevant literature editions. For the selected result, inspect the formal
statements and definitions again; the long record's interpretation is a claim
to compare, not a substitute for that check. Use the long record for the full
argument and omitted cases, the literature for credit and position, and actual
receipts for the scope of formal assurance.

Read the current long record, selected graph, principal statements and their
supporting arguments. Compare the closest prior results. Identify the intended
reader, the principal contribution and the mechanism worth explaining. Fix the
claim ceiling before editing prose; new mathematical discoveries return to
research and review first.

Use the closest literature to calibrate the expert reader's needs: what is
already known, what terminology and conventions they expect, and which step
deserves space. Distinguish a new theorem from a new proof, reconstruction or
explanation. A novel presentation cannot take credit for an antecedent result.
Read an existing short draft in order and retain the first point where its
promised inference cannot yet be recovered before opening supporting material.

Select claims for their supported contribution and source passages for the
explanation they supply. Keep the claim's graph identity distinct from those
passage locations. An expository model can guide wording without proving the
claim; identify the mathematical input that does.

Check that the long record actually contains the proof the short paper will
cite. A matching title, label or file is insufficient. Record unavailable
material as unavailable rather than assuming a link's destination is adequate.

## Procedure

1. Select one connected argument. State what changes relative to prior work
   and what the result enables or clarifies. Counts of lemmas or declarations
   cannot choose the contribution.
   Compare plausible focal results before choosing. Retain a secondary result
   when it advances the same argument or explains its use. For each substantial
   cut, identify the full-proof destination; do not give every available result
   equal space merely because it has a formal declaration.
2. Draft the title, abstract and main theorem against the exact same statement.
   Retain the domain, every essential hypothesis, quantifier order, dependence
   of witnesses on parameters and direction of implication.
   Explain the force of a restrictive hypothesis with familiar cases where known.
3. Put the mechanism early, then allocate detail to the inference that makes
   it work. Introduce definitions when their purpose can be understood. Use
   notation only when it reduces repeated explanation. Keep the short paper
   within its chosen mathematical scope; a further application with different
   hypotheses belongs in a separate argument, even when it motivates this one.
   When shortening a construction to an identification or equivalence, retain
   the map or convention needed by the next calculation. If the argument uses
   only a shared invariant, name that invariant instead of claiming more.
4. Give an intelligible proof or explicitly label a sketch. For every omitted
   argument, give the long record's version and exact theorem or section, then
   read that destination. Check that its proof supplies the missing inference
   with the required assumptions and translated notation. A working link to a
   nearby theorem is insufficient. Identify the result obtained at that
   destination and where the reader returns. Test one complete short-to-long
   journey, including a boundary case when the omitted proof has cases.
5. Before cutting a passage, decide where its useful content will remain.
   Preserve the complete long argument; never rebuild it from the shortened
   paper. Independent routes may stay there. Essential assumptions,
   attribution and the reason for the decisive step stay beside their uses.
6. Reconcile the shared statements in both directions: corrections in the
   short paper must reach the long record, and assumptions revealed by the
   long argument must reach the short paper. Resolve differing evidence labels
   from source and receipts rather than copying the stronger label.
7. Update passage mappings and citation roles. Preserve credit for prior proofs,
   adapted constructions, supplied ideas and corrections at their actual uses.
   Carry still-used inputs and credit into the surviving passages; remove a
   citation only when its role has gone.
   Gather toolchain details and run history in one verification destination.
8. Run `lean-exposition check-bundle DIR`. Inspect links and the rendered paper.
   Review mathematical meaning before sentence polish. A successful bundle
   check is not semantic acceptance or independent review.

## Output contract

Produce an authored short paper, its mapping and any required corrections to
the long record's shared statements. Every claim has its graph identity,
assumptions, evidence class and citation use preserved; every omitted proof has
an exact destination. Use the existing mapping fields and passage `rationale`
under the [authoring contract](../../docs/authoring.md#preserve-correspondence).
List the exact remaining question. Report review scope and unresolved issues
without presenting the scaffold or an unchecked draft as a finished paper.

## Checks and example

If the long record establishes “under `A`, conclusion `B` follows”, an abstract
that states only `B` may overclaim. Retain `A` in the compressed claim unless
a separately reviewed argument removes it. Moving `A` to a distant limitation
does not repair an unconditional main theorem.

For example, shortening the natural-number statement “if `n = 0`, then
`n + 1 = 1`” to “`n + 1 = 1`” creates a false universal claim: `n = 1` refutes
it. The proof by substitution is short enough to retain together with its guard.

Read three routes: title through main theorem; theorem through its decisive
proof step; and one short-paper reference through the full argument it names.
Check that all three preserve the same statement. Then ask a cold reader to
explain the mechanism and identify an excluded case where known. Preserve
specific failed reconstruction attempts as revision evidence.

Also read the entire revised short paper sequentially, without using the long
record to fill unannounced gaps. A compact proof may legitimately invoke a named
external theorem; say what it supplies and keep its hypotheses visible. Full
support of a measure, for example, does not by itself imply a strictly positive
density. A paper retaining both conclusions must retain the further argument
or its exact proof destination, and must not transfer formal status from one
conclusion to the other.

Record the input versions, contribution selected, consequential cuts and their
destinations under [skill use and maintenance](../../docs/authoring.md#use-and-improve-the-transition-skills).
The [Erdős method transfer](../../docs/erdos-method-transfer.md) illustrates
selection by mathematical purpose and preservation of the decisive inference.
