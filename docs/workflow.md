# Workflow

This guide explains why the project produces three papers, how to apply its tool and writing methods to another result, and how to package and serve the papers. For a first run, start with the [project introduction](../README.md).

## Why this project exists

As more mathematics is developed with AI and formal proof tools, the amount of machine-checked material can grow faster than people can understand it.
A mathematician rarely learns from a long list of definitions and lemmas which idea deserves attention. A short summary can leave out the condition on which an argument depends.

Different readers need different accounts of the same mathematics. A specialist
wants the result, its relation to the literature and the main proof. Someone
learning the subject needs the objects introduced, examples they can calculate,
and an explanation of why each step is useful. Someone examining a difficult step needs enough detail to reconstruct it.

The aim is to make all three accounts useful while keeping their mathematical claims consistent. This repository has the writing methods, tools that record sources and test runs, and drafts written with them.

## Three documents, three jobs

| Document | What it helps you do |
| --- | --- |
| **Long reasoning record** | Reconstruct the argument, including supporting derivations, assumptions, source references and unresolved questions. |
| **Short research paper** | See the main result and proof in the language of the relevant literature, with links to the details. |
| **Expository paper** | Learn a selected result through definitions, examples and the ideas behind the proof, with prerequisites stated at the outset. |

These are different writing tasks with no fixed page counts. An exposition may use the detailed record and original sources. Shortening an argument
must preserve the conditions under which it is valid.

## Apply the workflow to another result

Start with one result you want to explain and identify the sources and arguments
it depends on. Record those relationships in an **evidence graph**: a structured
file connecting mathematical claims to their assumptions, citations and recorded test runs. A writer can use the graph as a map of the sources, and a reviewer can follow a passage back to its support.

Each paper also has a [graph view](bundle-consumers.md#view-one-paper-as-a-graph):
its sections and passages in reading order, connected to their recorded claims,
sources and test runs. The three papers share the same underlying evidence, so an
application can move between a passage, its support and another account of the
same result. A [view of every record](bundle-consumers.md#view-the-whole-recorded-corpus)
holds one shared pool of records, so an application can look up which papers and passages use each record. Papers can select different goals while retaining
their necessary assumptions and sources. A [query from any record](bundle-consumers.md#start-at-any-record-and-follow-its-neighbourhood)
starts from a source, citation, evidence record or claim, follows links labelled by kind
in either direction, and reports where the selected view stops. Exact text
selections can also find mapped passages and their support. The local API
supplies these operations for readers, agents and frontends, including the
repository's reading website.

The [reading API](web-api.md#follow-an-explanation-a-derivation-or-an-answer)
also distinguishes an authored derivation, explanation, example or reference.
It connects fuller accounts, illustrations and exercise answers with explicit
reading links, keeping those recommendations separate from shared claims and
proof dependencies. The text at both ends of a reading link belongs to the one assembled copy of the papers being served.

The [authoring guide](authoring.md) and [writing methods](../skills/README.md)
divide the writing into four steps: record the sources, reconstruct the
argument, select the expert paper and teach a result to a stated audience.
Four written methods in this repository guide those decisions. Their
[review-and-refinement loop](authoring.md#use-and-improve-the-transition-skills)
turns a tested revision into a specific lesson for the next problem: repair the
paper, test what generalises, and improve the method responsible. The complete
method is in this repository; the [Erdős examples](erdos-method-transfer.md)
are earlier examples of the method, and following it needs no other repository.

The software is a local Python command-line tool. It collects exact source
versions, extracts dependencies from Lean projects, validates the graph and packages authored papers with their source mappings. A human or an AI assistant supplies
the mathematics and prose. The `scaffold` command creates empty writing templates;
`assemble` packages documents that have already been written.

Review has two distinct questions: does the writing faithfully describe the
mathematics, and can its intended reader follow it? Use answers to revise both
the document and the writing method. The [reader-review guide](reader-review.md)
describes how to run one review session on a stated question and an exact version of the papers. Automated tests find missing references and changed text and cannot answer those two questions.

## Package and serve papers

To create an empty writing bundle:

```sh
lean-exposition scaffold examples/minimal/evidence-graph.json --out build/minimal
lean-exposition check-bundle build/minimal
lean-exposition export build/minimal --out build/minimal.zip
```

The ZIP contains the graph, three Markdown templates, their mapping records and
a manifest listing the files and hashes. To package the existing authored papers
instead, follow the [assembly commands](../papers/README.md#assemble-the-authored-bundle).
The [guide to reading bundles](bundle-consumers.md) explains how another application
can read a bundle without depending on this CLI.

To serve an assembled bundle to a website or another application:

```sh
lean-exposition serve build/qaoa-sk-authored --port 8000
```

The [web API guide](web-api.md) covers shared graph navigation, aligned
paper passages, comparison, search, text selections in one exact version of
the papers, and the `witness` field, which gives one recorded path connecting two records. Summary cards, compact graph maps and matches-only passage
queries let a frontend load detail as readers select it. The backend supplies
the data; a frontend can choose its own graph renderer and reading interface.

The repository's own [reading website](../site/README.md) is one such frontend.
The papers come first: a graph follows the sentence you are reading, and any
marked statement opens its Lean. **Map** draws the whole argument, with the main
theorem at the top and any result unfolding into what it uses. **Compare** is the
proof as a table: each row is one step, set side by side at every level from the
Lean declaration through the long record and short paper to the exposition. The
Lean index at the back opens OpenAI's source with each central name explained in
the papers' notation. It runs against a local `serve` process or as a static
copy; its guide gives the commands.

Two read-only data files make that comparison exact. The
[Lean index](web-api.md) lists every declaration of the vendored source
with its text and the names it mentions, and the
[record alignment](record-alignment.md) points each record to its Lean
declarations, to the exact slice of each paper that states it, and to the
sentences and Lean lines tied together inside that slice. A program confirms that both ends of each exist in the pinned files; neither says the mathematics matches.
