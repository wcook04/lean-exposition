---
name: long-to-short
description: Select a short research paper for a named expert reader from any formalised result (Lean corpus, Comparator check, original sources and complete long record), carrying the one point that reader needs, the decisive proof, hypotheses, attribution, linked Lean evidence and full-proof destinations.
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

## Model the reader and find the one point

Do this before selecting material. Write the answers in the review brief.

1. **Who reads it.** The readers of a short paper are the authors of the
   works it cites and builds on. They will check it, build on it, referee it
   and cite it.
2. **What they already know.** Read those cited papers. List what their
   authors will find obvious (the standard models, the algorithms and lemmas
   of their own papers) and what the new result asks them to learn: the new
   construction, the steps where a natural shortcut fails, quantifier order,
   and whether the formal statement says what the theorem says. Known
   material becomes a cited statement with its hypotheses, never a page of
   re-derivation.
3. **The one point.** State in one or two lines why the result is true: the
   mechanism, and where an exponent or bound comes from when there is one.
   Say what stopped the previous method and what the new idea changes. If you
   cannot write this line, the source is not yet understood; return to the
   long record rather than drafting.
4. **The history.** Place the result in the sequence of earlier results it
   improves or refutes, with authors, years and the exact previous bounds,
   checked against the sources. Cite each prior work correctly and say what
   the new work inherits from it.

Allocate pages from this model: most space to what the new result asks the
cited authors to learn, least to what their own papers already contain.
Abstract, opening section and Theorem 1 carry the one point and the history;
a reader should meet both on page one.

## Procedure

1. Select one connected argument. State what changes relative to prior work
   and what the result enables or clarifies. Counts of lemmas or declarations
   cannot choose the contribution.
   Compare plausible focal results before choosing. Retain a secondary result
   when it advances the selected explanation or its promised use. If a downstream
   application introduces another mathematical setting, choose between a precise
   imported consequence and a second explanatory objective. Ask what the reader
   must now be able to calculate; a chain of implications alone does not require
   teaching every construction. Keep the new construction central when it is the
   contribution. For each substantial cut, identify the full-proof destination;
   do not give every available result equal space merely because it has a formal
   declaration.
2. Draft the title, abstract and main theorem against the exact same statement.
   Retain the domain, every essential hypothesis, quantifier order, dependence
   of witnesses on parameters and direction of implication.
   Explain the force of a restrictive hypothesis with familiar cases where known.
3. Put the mechanism early, then allocate detail to the inference that makes
   it work. Introduce definitions when their purpose can be understood. Use
   notation only when it reduces repeated explanation. Keep the short paper
   within its chosen mathematical scope; a further application with different
   hypotheses belongs in a separate argument, even when it motivates this one.
   When a construction changes mathematical setting, give enough of its local
   statement for this reader to identify the input objects, output object,
   preserved observable and remaining approximation. Define the needed map or
   state a precise imported theorem, then route its construction to the long
   record. A formula and citation alone may leave the new objects unidentified.
   Retain the finite identifying formula: equal scalar limits do not identify
   a finite observable, circuit, algorithm or geometric object. If only a shared
   invariant is used, say why it suffices without claiming interchangeable
   objects. Routine renaming within the reader's existing setting needs no new
   theorem interface.
4. Give an intelligible proof or explicitly label a sketch. For every omitted
   argument, give the long record's version and exact theorem or section, then
   read that destination. Check that its proof supplies the missing inference
   with the required assumptions and translated notation. A working link to a
   nearby theorem is insufficient. Identify the result obtained at that
   destination and where the reader returns. Test one complete short-to-long
   journey, including a boundary case when the omitted proof has cases.
   Inspect the delivered PDF as well as the source: a reference should name the
   companion and section even when its link cannot be followed. Test local links
   from the actual reading-copy directory after relocation, including the named
   destination inside each PDF. A source label or existing target file does not
   establish that destination. Check the portable Markdown bundle separately;
   its contents and the PDF reading edition can differ. Do not invent a public
   URL for an unpublished file.
5. Before cutting a passage, decide where its useful content will remain.
   Preserve the complete long argument; never rebuild it from the shortened
   paper. Independent routes may stay there. Essential assumptions,
   attribution and the reason for the decisive step stay beside their uses.
   Compare alternative proofs by hypotheses and exact conclusions, including
   rates, before calling one indispensable or superseded. A shorter argument
   may settle the selected question while losing a stronger bound or wider
   domain. Companions can use different proofs; state which route each uses
   and do not transfer a formal check to an alternative ordinary argument.
6. Reconcile the shared statements in both directions: corrections in the
   short paper must reach the long record, and assumptions revealed by the
   long argument must reach the short paper. Resolve differing evidence labels
   from source and receipts rather than copying the stronger label.
7. Update passage mappings and citation roles. Preserve credit for prior proofs,
   adapted constructions, supplied ideas and corrections at their actual uses.
   Carry still-used inputs and credit into the surviving passages; remove a
   citation only when its role has gone.
   If a stronger estimate serves a later use, say why that use needs its margin
   or broader hypotheses. A qualitative condition may already suffice for the
   first conclusion. Preserve that distinction when explaining the contribution.
   Gather toolchain details and run history in one verification destination.
8. Run `lean-exposition check-bundle DIR`. Inspect links and the rendered paper.
   Review mathematical meaning before sentence polish. A successful bundle
   check is not semantic acceptance or independent review.

## Reference the Lean and Comparator evidence

Link Lean the way a citation is linked. Write the claim in plain mathematical
words and hyperlink those words to the declaration or statement at an
immutable commit with a pinned line range (`.../blob/<commit>/<file>#L12-L40`).
Do not put dotted typewriter identifiers in the prose. Every formally
supported claim should be attributable to its Lean or Comparator evidence by
one such link; claims supported only by an ordinary argument, a build without
comparison, or a cited paper say so in the same plain words.

When a Comparator challenge exists, end the short paper with a one-page
appendix, "Checking the statement", so the reader can answer whether the
statement was encoded correctly in about fifteen minutes:

- one sentence of purpose: the checker confirms that the proof has the stated
  type; this page lists what that type says;
- the challenge file, its size and imports, with a line-range map linking each
  block of definitions (inputs, models, measures, the function, the headline
  quantity);
- each compared theorem in mathematical notation beside its linked name,
  stating which constants are compared and which come only from built,
  uncompared theorems;
- the few modelling choices a reader should check: error conventions, what
  the model may access, promises, degenerate cases such as an infimum over an
  empty set, and the quantifier order;
- what the comparison establishes and what it does not: a modelling error
  shared by challenge and solution passes; uncompared theorems are only built;
  whether runs were sandboxed; whether any person has reviewed the definitions;
- commit, toolchain and the command whose output is quoted.

Gather all other run history in the long record's verification section.
Write any formal status that is still being rebuilt or reviewed conditionally.

## Register and the rendered pages

The reading copy contains no provenance notes, scratch paths, session remarks,
relative links into unpublished folders, or workflow vocabulary. Agents and
tools are never the subject of a sentence; mathematicians, theorems and
proofs are. Do not use em dashes, rhetorical "not X, but Y" contrasts or
taglines. Give the responsible author and the AI assistance in a byline and
credit the theorem's originators there. Fix notation collisions before
submission. Render the paper and look at every page at reading size: overfull
lines, figures, tables, links and the reference list.

A revision pass refines the existing text. Replace or tighten a passage
instead of appending another one; a review that adds pages to a paper whose
complaint was misallocation has not repaired it.

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
density (SK instance). A paper retaining both conclusions must retain the further argument
or its exact proof destination, and must not transfer formal status from one
conclusion to the other.

Record the input versions, contribution selected, consequential cuts and their
destinations under [skill use and maintenance](../../docs/authoring.md#use-and-improve-the-transition-skills).
The [Erdős method transfer](../../docs/erdos-method-transfer.md) illustrates
selection by mathematical purpose and preservation of the decisive inference.

## Close the transition and improve the method

Apply the shared [review-and-refinement loop](../../docs/authoring.md#use-and-improve-the-transition-skills).
If selection hid an assumption, mechanism or proof destination, repair the
short account and read the complete round trip to its support. Record why the
material was retained, relocated or cut. Generalise the decision criterion
only after testing it on different results; this paper's preferred length or
section order is not a rule for every expert audience.
