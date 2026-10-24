# Writing from recorded evidence

The graph records what the sources and checks support. A long reasoning record
makes the argument recoverable. A short research paper selects and explains
one contribution. An expository paper teaches an established result to a
specified reader. These are different authoring tasks; the CLI supplies
bindings and empty scaffolds, while a writer supplies the mathematics and prose.

Start with the [transition skills](../skills/README.md) and the machine
[contracts](contracts.md). The skills are optional instructions for people and
agents. They are not runtime dependencies or a claim of measured writing benefit.

## Choose a transition

| Transition | Required input | Authored output | Principal review question |
| --- | --- | --- | --- |
| Source to graph | Identified source bytes, question, permissions, available checks | Claims, assumptions, citation roles and typed relations | Does each relation mean what the source actually establishes? |
| Graph to long record | Selected goal closure and readable supporting arguments | Complete argument, informative failures and reproducibility account | Can another reader recover every load-bearing step? |
| Long record to short paper | Current complete record and principal contribution | Coherent research paper with exact full-proof destinations | Did selection preserve the statement, hard step and credit? |
| Record to exposition | Established result, full argument and reader profile | Prerequisite teaching, examples and changed-case tasks | Can this reader reconstruct and use the result? |

Exposition may start from the long record directly. A short paper is not a
mandatory stage. A mathematical gap sends the affected claim back to research
and review; it does not become a writing task merely because it appears in prose.

## Establish that the inputs suffice

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

## Preserve correspondence

For every material claim, keep its exact statement, object domain, hypotheses,
quantifier order and conclusion recoverable. Record the graph claim ID and the
assumptions, evidence and citations it uses. The same identity can occur in
several documents, but each occurrence still needs an accurate statement.

Keep two relationships distinct:

- A statement's support: the ordinary argument, checked formal declaration,
  finite computation or external input that establishes its stated scope.
- A passage's sources: the exact text locations and evidence used for that
  explanation, with a reason for the connection.

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
bind exact authored text. Cross-document proof destinations belong in the text
and `rationale`; the artifact schema does not encode such links. Read both ends
after a revision. Check that substantive claims outside declared passage markers
have not escaped mapping: the checker cannot discover them by interpreting prose.

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
mapping or anticipating a later definition. At every transition, identify what
the reader already knows, why the next object is needed, and what justifies the
next inference. Record the first point where a definition, motivation, argument
or citation arrives too late. A coherent overview does not repair a broken
sequence of paragraphs.

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
