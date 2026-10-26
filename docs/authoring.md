# Writing from recorded evidence

The graph records what the sources and checks support. A long reasoning record
makes the argument recoverable. A short research paper selects and explains
one contribution. An expository paper teaches an established result to a
specified reader. These are different authoring tasks; the CLI supplies
bindings and empty scaffolds, while a writer supplies the mathematics and prose.

Start with the [transition skills](../skills/README.md) and the machine
[contracts](contracts.md). Authors working through this funnel load the matching
skill before selecting or revising material. These are instructions for people
and agents, not runtime dependencies or a claim of measured writing benefit.

## Choose a transition

| Transition | Required input | Authored output | Principal review question |
| --- | --- | --- | --- |
| Source to graph | Identified source bytes, question, permissions, available checks | Claims, assumptions, citation roles and typed relations | Does each relation mean what the source actually establishes? |
| Graph to long record | Selected Lean corpus, definitions, original arguments, literature and source-bound evidence | Complete selected argument, informative failures and reproducibility account | Can another reader recover every load-bearing step? |
| Long record to short paper | All original context plus the complete long record | One contribution and its decisive proof, with exact full-proof destinations | Did selection preserve the statement, hard step and credit? |
| Record to exposition | All original context, long record, short paper and reader profile | An explanation of the selected result, with necessary prerequisites and examples | Can this reader reconstruct and use the result? |

Each writer retains access to the upstream context and chooses what the present
reader needs. This is not a requirement to repeat every upstream result. For a
standalone exposition without a short paper, explicitly select its result and
scope from the complete argument. A mathematical gap sends the affected claim
back to research and review; it does not become a writing task merely because
it appears in prose.

## Use and improve the transition skills

This is the shared **review-and-refinement loop** for the four authoring
transitions. A pass can improve the current papers and the method used on the
next problem. Those are separate outcomes: a sound local revision need not
yield a new general rule, and a method edit does not establish better writing.

### Start a pass

Record a short brief in the existing review account: the selected result and
claim boundary; reader and intended takeaway; exact input and output editions;
transition skill/version; and the question this pass should resolve. Reuse the
current brief when these have not changed. Do not equate access to an annex,
Lean corpus or review packet with having read its contents.

Begin with the relevant skill and the current source versions. Choose the
mathematical question, supported result and intended reader before choosing
sections. Rank candidate material by its contribution to that purpose: a proof
step, necessary prerequisite, useful consequence or revealing example. Keep
essential assumptions and credit beside their uses. Preserve useful omitted
detail at an exact long-record destination. Availability, declaration counts
and page quotas do not decide what belongs in a paper.

Calibrate expert prose against original passages in nearby mathematical papers:
their vocabulary, notation, order of definitions, theorem and proof structure,
citations, and allocation of detail to the difficult step. Match the source
edition and mathematical setting before transferring a convention or comparison.
Preserve the field's useful terms and explain their operations at the reader's
level. A specialist source may assume background that an exposition must teach.
Compare its prerequisites and purpose before adopting its order or compression;
write the explanation independently rather than copying its prose. Distinguish
the chronology of results and source editions from the order chosen to explain
them. Companion papers can share a statement without sharing a proof route.
Record the passage and the editorial decision it informed; neither a literature
shelf nor a reviewer's description establishes that its practice was inspected.

Apply the skill to the document, then read the delivered result in order. In the
existing mapping's `review_notes` or source-review record, identify the skill
version or repository commit, inputs actually inspected, significant selection
decisions, passages revised, review performed and remaining limitations. The
presence of a skill file proves neither its use nor improved comprehension.
Use the current fields; no separate skill-execution service is required.

### Find the decision that needs repair

When review finds a failure, repair the passage and inspect its consumers first.
Then improve the method at the transition that made the decision. Keep one
shared maintenance loop here; the four skills own their stage-specific choices.
The working instructions are local and complete. The [Erdős method transfer](erdos-method-transfer.md)
records their bootstrap examples, not a dependency on another checkout.

Route the lesson to the decision that produced the problem, even when a later
paper first exposed it:

- **Source to graph:** a claim's meaning, source edition, credit, dependency,
  premise supplier or checking outcome was recorded incorrectly or incompletely.
- **Graph to long:** the selected argument lacks a recoverable inference,
  construction, boundary case or correspondence between mathematical settings.
- **Long to short:** selection lost a necessary assumption, contribution,
  decisive mechanism or reachable full-proof destination.
- **Record to exposition:** the chosen reader cannot yet perform an operation,
  recognise an object, follow the order, or explain why a construction is needed.

A lesson shared by several transitions belongs in this guide; link to it from
the skills rather than repeating a growing checklist. A runtime defect belongs
with its implementation and regression check. An unresolved mathematical claim
returns to research. Treat conflicting reviews as claims to adjudicate against
the sources and reader task, not as instructions to combine indiscriminately.

### Assess, revise, generalise and check

Use this loop for each substantive review batch:

1. Preserve the reviewed edition and distinguish the reader's first response
   from later source-assisted diagnosis. Review suggestions are evidence to
   assess, not instructions to execute or votes on mathematical truth.
   A first sequential reading is not necessarily unprimed. If the reader has
   already seen a focus brief or earlier critique, record that exposure and
   continue honestly; do not manufacture a blind-reading claim by restarting.
2. Group findings by the underlying inference or reader difficulty. Check
   competing explanations against the original sources; record what is already
   correct and should survive. A repaired passage may answer several reviews.
3. Revise the appropriate account, its source relations and dependent accounts.
   Test both continuous reading and entry at the affected proof destination.
4. Decide whether an existing instruction was missed or a reusable rule is
   absent. Repair a missed route or acceptance check instead of restating the
   same instruction. Add a rule only when it changes an identifiable decision.
5. State the rule's trigger, action, reason, observable check and exception.
   Try it on two differently shaped cases and one case where it must not apply.
   Retain it at that demonstrated scope; do not turn a preferred section order
   or one mathematical example into a universal requirement.
6. Validate the revised artifacts and bind the review to their exact edition.
   Record the disposition in the existing mapping `review_notes` and source
   review account. Reopen the decision if later evidence contradicts it.

Check two directions before closing: a changed source claim reaches all its
recorded uses, and every revised paper claim still reaches adequate support.
The graph locates candidates; read the affected passages to decide what needs
changing. Keep unaffected prose and earlier review records intact. A batch is
closed when its findings have reasoned dispositions, the affected outputs have
been inspected, and any unresolved issue has an exact next check or owner.
Neither a quota of edits nor another review packet is a completion condition.

A compact method record should identify the observed difficulty, source check,
before/after passage, owning skill, reused or changed instruction, transfer cases,
exception, validation and remaining question. This record belongs with the
review, not in the mathematical reading path. Mark the result as **refined**,
**existing rule applied**, **local choice only**, or **unresolved**. Author,
agent and independent reader reviews remain separate; successful revision and
structural checks do not establish improved learning without reader evidence.

Keep historical method versions intact. Changing a skill does not mean it was
used to write an older paper. Record the new version only after applying it to
the identified passages, and state the scope of that application. The current
validators check document and graph bindings; they do not execute skills or
verify these review-note assertions. A reusable procedure is maintained through
author practice and review, without inventing a second runtime workflow.

### Check transfer beyond the current problem

Consider the lesson: **when a reader cannot perform an unfamiliar operation,
teach that operation in a small case before its first consequential use, then
reuse it in the argument**. Its owner is the exposition skill. It is conditional
on the reader and the operation, not a requirement that every paper begin with
an example. Two elementary transfer trials expose its useful scope:

**Weighted averaging.** A reader knows arithmetic but has not used weights.
For values 1 and 4 with weights 2 and 1, calculate
\((2\cdot1+1\cdot4)/(2+1)=2\) before writing
\(\sum_i w_i x_i/\sum_i w_i\). Explain why the denominator is the total
weight. Changing the weights to 1 and 2 gives 3; multiplying both weights by
the same positive number leaves the average unchanged. These changes test
the operation rather than memorisation of the first answer. State the domain:
nonnegative weights with positive total. The example does not justify an
infinite-sum interchange or a signed-weight probability law.

**Induction.** A reader knows sums and algebra but not induction. Compute the
first three sums of consecutive odd numbers, obtaining 1, 4 and 9. Define what
the index counts, then show that adding the next term changes \(n^2\) to
\(n^2+(2n+1)=(n+1)^2\). The long record retains the base case and the
universal induction step; an expert account may state that argument directly.
The exposition uses the examples to teach the step, then asks for the next
increment and why the proof reaches every positive integer.

**Rejection case.** Three correct numerical sums do not prove the identity for
every index. If the induction step is absent from the source argument, adding
examples cannot close that proof gap. Return to graph-to-long or research.
Likewise, a reader already fluent in these operations may need the decisive
theorem first; impose no remedial worked example on that expert account.

These are author-executed transfer checks with explicit expected answers, not
observed reader responses. Record actual attempts using the
[reader-review procedure](reader-review.md). When a new lesson fails a transfer
case, narrow or reject it before treating it as reusable.

## Establish that the inputs suffice

Read the current account from the beginning before consulting explanations of
its difficult passages. Record what an unfamiliar reader has actually been
told at each inference. Define a quantity before using it and explain the job
it will do; a later definition does not repair the earlier reading experience.
Then follow each omitted-proof destination into the long record, check its
local hypotheses and conclusion, and return to the shorter account. This tests
both sequential reading and entry at a particular proof step. A consequence,
alternative proof or comparison should not appear to be a prerequisite merely
because it occupies the next section.

A long reasoning record is a citable derivation with exact statements, proof
steps, source destinations and checking evidence. Before writing a proof section,
read the relevant argument and definitions. Declaration metadata and a dependency
graph locate ingredients; they do not supply the inference joining them. If only
an endpoint or outline is available, identify the missing step and leave its
proof section empty. Sources that disagree need a stated comparison or check;
sections with independent support can still proceed.

Keep the generic templates empty. Authored examples are separate documents whose
mapping records say `draft` until the stated review has happened. A draft may
explain established parts and visibly incomplete arguments without upgrading the
unresolved conclusion.

### Check the active objects and claims

When an argument returns from an example, changes representation or recombines
earlier constructions, identify the object now fixed, the changes permitted,
the facts already available and the next goal. An announced theorem is still
a target in its proof. At a linked proof destination, restore the small
dictionary an incoming reader needs to parse its first inference. An
uninterrupted calculation with unchanged objects needs no repeated inventory.

Classify a reused property as a definition, hypothesis, proved conclusion or
precisely stated input. A normalization proved later for an optimum cannot be
moved into the admissible class without checking how it changes the available
variations. Likewise, a property of one example cannot silently become a fact
about the general object. Perform this audit in the review account; put only
the needed reminder or derivation in the reading path. Check the repaired
passage from its actual entry point, without borrowing later conclusions.

## Preserve correspondence

Choose each paper's goals deliberately. Mapping schema `1.1` lets the long
record, short paper and exposition select different existing graph nodes as
their focus. A passing mention or future application need not become a selected
goal. Keep its actual passage correspondence and applicable conditions anyway.
Legacy `1.0` mappings retain the graph-wide goal rule. The complete graph remains
available in either case; selecting less for a paper never deletes source evidence.

For every material claim, keep its exact statement, object domain, hypotheses,
quantifier order and conclusion recoverable. Record the graph claim ID and the
assumptions, evidence and citations it uses. The same identity can occur in
several documents, but each occurrence still needs an accurate statement.

Keep two relationships distinct:

- A statement's support: the ordinary argument, checked formal declaration,
  finite computation or external input that establishes its stated scope.
- A passage's sources: the exact text locations and evidence used for that
  explanation, with a reason for the connection.

When a graph cites an authored companion, bind its actual current bytes in the
source checksum, revision and citation URL, then rebind every affected paper
mapping and source-review index to the new graph hash. Changing a companion without refreshing these
self-citations leaves a stale edition even when the bundle hashes agree.

Matching hashes establish agreement with recorded bytes. They do not establish
that a source entails a sentence. A nonempty rationale must still be judged.
Likewise, a dependency path can locate ingredients without proving that their
composition establishes the advertised conclusion.

The companion mapping records `stage`, `state`, `selected_goal_ids`, `claim_ids`,
`citation_ids`, `assumption_ids`, `unresolved_ids`, `passages`, `review_state`
and `graph_sha256`. Use the supported values from the current schema. A generated
mapping begins with `state: scaffold` and `review_state: not_reviewed`. Authoring
and review must occur before those fields can describe a later state. Packaging
must preserve the actual state; it cannot confer acceptance.

When authoring a scaffold, remove its `EMPTY SCAFFOLD` marker and set the mapping
to `draft`. Enclose each mapped passage in unique explicit markers:

```md
<!-- passage:main-result -->
The authored statement or explanation belongs here.
<!-- /passage:main-result -->
```

The passage row's `anchor` is `main-result`; its `text_sha256` hashes the exact
UTF-8 bytes between the markers, including newlines. The row also gives
`claim_ids`, `citation_ids`, `assumption_ids`, `evidence_class` and `rationale`.
The document's `content_sha256` hashes the complete file. Update those bindings
after an edit and review the changed meaning; replacing a stale hash does not
establish correctness. A `reviewed` artifact requires `review_state: accepted`
and nonempty `review_notes`, which must describe review actually performed.

At passage level, retain enough correspondence to locate the claim, applicable
assumptions, citations and evidence. Account for an unexplained bridge as
unresolved. Do not treat a bibliography or a document-wide ID list as proof
that every passage has support.

Check a worked example against the hypotheses of each directly selected claim.
An example using an admissible coefficient that is not a minimiser may illustrate
conditional rounding, but it does not instantiate a convergence theorem whose
premise is minimality. Select the applicable claim and explain the contrast in
the rationale. Setting `evidence_class: example` does not remove assumptions
inherited through the selected graph relations. Inspect the resulting passage
query as well as the prose after changing its map.

In the current graph schema, a citation's `source_id` resolves its version and
hash through the source record, while `locator` identifies the theorem, section
or passage. Put the citation's local role in the prose and passage `rationale`.
For graph-only intake, use a graph note naming the relevant IDs. Curated edge
justifications likewise belong in identified graph notes or the relevant
semantic-review record; edges have no free-form rationale field. Do not invent
fields that the schema rejects.

Ordinary section anchors locate full proofs across documents; `passage:` markers
bind exact authored text. Keep proof destinations in the prose and `rationale`.
Artifact `1.2` can additionally encode reading links between mapped passages,
as described below. Read both ends after a revision. Check that substantive
claims outside declared passage markers have not escaped mapping: the checker
cannot discover them by interpreting prose.

The consumer's ordered `document_parts` view retains passage blocks and every
surrounding byte. Its [guarded reconstruction](bundle-consumers.md#reconstruct-the-recorded-manuscript)
can recover the exact captured Markdown, with the existing passage references
leading to graph correspondence. Markdown remains the prose authority.
Dependency traversal cannot choose a sufficient exposition order or generate a
missing proof. A reordered or rewritten account is a new draft for review.

When producing LaTeX/PDF with Pandoc, include
`--lua-filter scripts/paper_anchors.lua`. It preserves the manuscripts' HTML
bookmarks as LaTeX destinations; Pandoc otherwise drops the raw HTML while
retaining links that refer to it. Check the resulting PDF destinations and
links as well as Markdown links. The filter does not modify the manuscript.

## Describe the role of a passage

Use artifact `schema_version: "1.2"` for optional reading annotations. On a
passage, `treatments` is a list of objects with `claim_id`, `kinds` and
`rationale`. The claim must already appear in that passage's `claim_ids`;
each claim has at most one treatment entry, with a nonempty list of distinct
kinds drawn from `statement`, `derivation`, `explanation`, `application`,
`illustration` and `reference`.

Choose roles by reading the passage. For example, a paragraph that directs
the reader to a density argument is a `reference`; sharing its claim ID with
a derivation does not make the paragraph itself a derivation. A passage can
have several roles. Missing annotations remain unspecified. These labels
record editorial judgement, not accepted proof or reader comprehension.

Mapping-level `reading_links` contain objects with these fields:

```json
{
  "from_anchor": "worked-answer",
  "from_text_sha256": "<exact source passage hash>",
  "to_stage": "expository",
  "to_anchor": "exercise",
  "to_text_sha256": "<exact target passage hash>",
  "kind": "answers",
  "rationale": "Works through the endpoint and integral checks asked in the exercise."
}
```

The hash placeholders stand for 64 lowercase hexadecimal characters. The
source anchor belongs to this mapping; the target belongs to the named
`long`, `short` or `expository` mapping. `expands` points from a fuller account
to the passage it expands; `illustrates` from an example to the passage it
illustrates; `answers` from an answer to its question. Links can stay within
one paper. Duplicate source/target/kind combinations are rejected.

An exercise or example may deliberately have empty `claim_ids`: it can teach
an operation without meeting the hypotheses of a recorded theorem. A reading
link does not change that selection. Do not add a claim merely to create a
navigation route. Neither treatment annotations nor reading links change
assumptions, proof edges, unresolved obligations or review state.

When either passage changes, review the relationship before updating its
endpoint hash. The bundle checker rejects stale endpoints, including incoming
links authored in another paper. Older mappings remain readable without these
annotations; versions `1.0` and `1.1` reject the new fields. See the
[reading query](bundle-consumers.md#follow-reading-guidance-between-passages)
and [website journeys](web-api.md#follow-an-explanation-a-derivation-or-an-answer)
to inspect what a consumer receives.

## Keep evidence classes separate

A formal theorem is checked against the proposition supplied to the kernel.
Its interpretation in a research question and its representation in prose
still require review. Record the checked source, environment and receipt
before reporting that check. Source presence or a successfully resolved name
does not establish execution.

Compare the complete formal statement and its relevant definitions with the
informal claim: domains, parameters, implicit and explicit hypotheses, quantifier
order and conclusion. Record the comparison in graph notes or an actual
`semantic_review` record's `details`. A `formalizes` edge records an asserted
correspondence; validation does not certify equivalence. When a declaration
supplies an ingredient, use `supports` and expose the remaining bridge.

Extracted `assumption_ids` identify discovered axioms. Quantified hypotheses
remain in the Lean `statement`; additional unproved inputs can be separate
assumption nodes. Explain all applicable restrictions in the prose. An empty
axiom list does not make a theorem unconditional.

An ordinary proof can be valid without a complete formalization. Identify its
formal ingredients separately from the steps supplied by the ordinary argument.
A later ordinary deduction may remove a hypothesis; retain that hypothesis when
describing an unchanged Lean declaration and identify the additional argument.
A finite computation has its finite domain and checker; an infinite conclusion
requires an argument reducing it to that computation. A conditional implication
may itself have either ordinary or formal proof, while its additional input
remains unproved.

Keep platform decomposition separate from Lean dependency extraction. Preserve
the platform, selected task, source version and outcome rather than treating a
platform label as proof, independent review, novelty or community acceptance.

## Track assumptions and citations through a rewrite

For each assumption, identify the dependent claim and where the argument uses
it. Check whether a compressed sentence still states it. Distinguish an
assumption in the theorem from an additional premise not established by the
record. When two premises need one witness, show that one witness satisfies
both; separate existence claims cannot be silently merged.

For each citation, record the work, version, exact passage and local role.
Possible roles include a proof input, historical priority, adapted construction,
correction, standard terminology and explanatory comparison. State the role in
the prose. A formal declaration link does not replace credit to earlier
mathematics, and a writing model does not prove the target argument.

After a move or cut, follow the reference to the actual destination. Compare
its statement, assumptions and notation with the claim that now depends on it.
Reconcile short and long versions in both directions. A correction in one may
require an update in the other even when their labels and URLs still resolve.

After changing a statement, assumption or cited input, find its consuming claims
and passages in every maintained version, including exposition. Follow edges
back from prerequisites to consumers: goal selection computes prerequisites,
not affected dependants. Record each document's disposition. Where a previous
acceptance no longer applies, use `state: draft` and `review_state: needs_revision`
until targeted review is complete. Updating bindings does not itself invalidate
an acceptance, so the author must revisit it.

## Review a transition

### Read the paper in order

Read each mathematical draft from its first sentence, without consulting its
mapping or using knowledge from later pages. At each transition, track
the question being answered, the objects and assumptions already available,
and the inference that the next sentence asks the reader to make. A term may
be defined yet still be unmotivated; a formula may be correct yet arrive before
the problem it solves. Record the first point where the available explanation
does not support the next step. Repair the sequence by explaining the purpose, moving
the construction or supplying the missing inference. Adding a glossary or a
forward reference does not by itself repair that dependence. Apply this review
to every paper at its declared prerequisite level, including abstracts,
captions, examples and the links between sections.

Better grounding need not make a paper longer. First try a more precise word,
a concrete description of the operation, or a change in sentence order. Introduce
a specialist term beside the object it names, at the reader’s stated prerequisite
level. Add explanation when it supplies a missing inference; cut repeated
announcements and definitions that the argument no longer needs. Review the
whole sequence for this failure class rather than repairing only the example
that exposed it.

The short paper should state one result with its hypotheses, explain the
mechanism, give the decisive argument and delimit its reach. The long record
should let a reader reconstruct every argument it promises; an exact external
proof destination must be described honestly when it supplies a substantial
step. The exposition should teach the necessary objects through connected
explanation and worked examples before asking the reader to use them. Assess
these deliverables separately rather than awarding a single quality score.

Use ordinary mathematical names, theorem and section references, and literature
citations in the reading path. Repository paths, declaration identifiers, hashes
and execution history belong in the companion mappings and verification record.
A compact formal-source link may support a statement without turning its proof
into software documentation. Remove object-role inventories and workflow labels
when a mathematical paragraph explains their relationship more naturally.

Before a long calculation, say what question it answers and where its result
will be used. If an example tests a theorem's hypothesis, state that theorem
first. After dense notation, work one small literal case before taking a limit.
Explain what an operation does to the mathematical objects before relying on
its symbolic form. Examples should separate the intended statement from a
plausible false inference, not merely repeat a definition with new letters.

Give each figure a specific explanatory job. Place it beside the inference it
shows, define its variables and explain the relation between its geometry and
the argument. Label schematic curves as schematic and credit adapted source
figures. Inspect the rendered page at reading size and in grayscale; successful
compilation does not establish that the reader can follow the picture.
Every connector must name the relation it depicts, with a clear direction where
direction matters. Keep proof dependencies, passage correspondence, reading order
and workflow transitions distinct. Give labels room before shrinking them; split
a crowded overview into connected views with explicit shared referents.

### Compare the revision with its sources

Freeze the input graph and source versions before a substantial revision. Keep
the proposed text, changed statements and affected mappings recoverable. Review
meaning before fluency, then accept, repair, reject or defer each substantive
proposal with a source-located reason. A mathematical discovery needs its own
review before it becomes an editorial correction.

Use three complementary checks:

1. **Structural:** run the graph and bundle checkers. Inspect missing IDs,
   stale hashes, broken destinations and inconsistent stage mappings.
2. **Mathematical:** compare the complete statement and each consequential
   transition with the actual proof, assumptions and cited inputs.
3. **Reader:** ask someone to reconstruct the result and hard step, apply it
   to an example and identify an excluded case where known. Record the attempt
   and where reconstruction stops.

Graph validation checks recorded structure; it does not reopen source files or
resolve citation locators. For sources with a compatible lock, run `audit-sources`
against the source root. Inspect citation and proof destinations separately.

State which sources and sections were assessed, sampled, unavailable or not
reviewed. An author's cold reread is useful but differs from an independent
reader test. A successful compile checks the production process; inspect the
delivered pages, formulas, bibliography and reference destinations separately.

Judge tables by the comparison they enable. Compact numerical data and short
case distinctions can benefit from rows and columns. Multi-sentence arguments
usually need full-width paragraphs or local lemma statements. If one column
becomes a tall strip of prose beside mostly empty cells, change the form and
inspect the replacement at reading size. Do not preserve a poor layout by
shrinking the text. Check other instances of the same treatment after a reader
rejects one of them.

Use the [bounded reader-review procedure](reader-review.md) to freeze one edition,
retain the reader's first response and distinguish later assistance. No schema or
hash check can establish that a previous acceptance applies to revised prose.

Useful negative checks include removing an essential hypothesis, replacing a
conditional sentence with an unconditional claim, changing an implication to
an equivalence, reusing evidence for different source bytes, or pointing a
proof reference at a nearby but insufficient theorem. Some are mechanically
detectable. Others require mathematical judgment. Report the check that
actually caught the defect rather than attributing it to the whole workflow.

## Use the local tools

After installing the package, inspect `lean-exposition --help` for this edition.
The core authoring sequence is:

```sh
lean-exposition validate graph.json
lean-exposition select graph.json --goal GOAL_ID --out selected.json
lean-exposition scaffold selected.json --out draft
lean-exposition check-bundle draft
lean-exposition export draft --out draft.zip
```

Replace `GOAL_ID` with a goal actually present in the graph. Scaffold generation
does not write completed results. After authoring the documents in `draft/papers/`,
update their mappings and perform the corresponding reviews. Keep each mapping's
`path` equal to `papers/long.md`, `papers/short.md` or `papers/expository.md` as
appropriate. Bind `graph_sha256` to the exact `draft/graph.json` bytes, then
update the complete-document and passage hashes. Supply all three pairs,
including stages still at scaffold state, to the assembler:

```sh
lean-exposition assemble draft/graph.json \
  --long draft/papers/long.md draft/papers/long.json \
  --short draft/papers/short.md draft/papers/short.json \
  --expository draft/papers/expository.md draft/papers/expository.json \
  --out assembled
lean-exposition check-bundle assembled
lean-exposition export assembled --out authored.zip
```

The output directory must be empty. Assembly validates the supplied bindings
without repairing stale hashes or rewriting prose, then creates a new manifest
whose hashes and `status` match those exact files. Editing a scaffold in place
leaves its old manifest stale; `check-bundle` cannot finalize those edits.
See [bundle consumers](bundle-consumers.md) for the corresponding Python API.
Export preserves a draft's recorded limits; it does not turn it into a reviewed
publication. Follow the README's minimal example for concrete files.

## Method sources and redistribution

The [Erdős method transfer](erdos-method-transfer.md) traces specific choices to
the eight public long, short and expository papers. Use its source-located cases
when a particular transition needs work; they do not impose every technique on
every paper. The [reference records](references.json) preserve retrieved method
source hashes and licence evidence. The [selected source readings](annex/README.md)
retain two licensed QAOA publisher papers and implementation excerpts, with the
specific decisions they informed. Match every theorem and equation locator to
the cited edition; a proceedings paper can number sections differently from
its full preprint.

These skills and templates were independently written for this repository.
Their design was informed by the following public sources at revision
`a0878310af794d7a0f76cc11f4de3a20c795dc60` of `wcook04/plectis-erdos`:

- Will Cook, [Writing a Good Mathematical Paper](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/exposition/writing-a-good-mathematical-paper.tex): exact statements, difficult transitions, source roles and delivered-document checks.
- Will Cook, [Writing Mathematics from the Literature and Reviewed Revisions](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/exposition/writing-mathematics-from-reviewed-revisions.tex), especially the linked reading, review and practice sections: local proof warrants, bounded revision lessons and reconciliation of short and long documents.
- Will Cook, [A Repository-Based System for Research and Publication](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/systems/claim-faithful-publication-systems-paper.tex), sections on records, proof and publication checks, and revision: distinct statement and passage bindings, frozen inputs and review boundaries.
- The public [writing skill](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/skills/public-mathematical-writing/SKILL.md), [editorial exchange](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/paper_refinement.py), [short-paper writer](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/short_paper_writer.py) and [evidence resolver](https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/paper_evidence.py): implementation examples of source bindings and review responsibilities.

The cited manuscripts declare CC-BY-4.0; the cited Python implementations
declare Apache-2.0. This repository does not bundle their text or code. If you
add such material, preserve its actual license and attribution. Permissions
for a source must also cover any bytes included in an exported bundle.

These references document design inputs. They do not establish independent
mathematical review, a comparison with other tools or improved reader learning.
