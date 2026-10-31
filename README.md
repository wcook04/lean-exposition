# lean-exposition

[Read the interactive website](https://wcook04.github.io/lean-exposition-site/) ·
[Website development and publishing](site/README.md)

**From formal proofs to mathematics people can understand.**

The worked example is a theorem about the Sherrington–Kirkpatrick model without an
external field: every minimiser of the zero-temperature Parisi functional has full
support on [0,1). Starting from the Lean proof OpenAI published with this result, the project gives three papers whose marked statements open their Lean.

[Lean](https://lean-lang.org/) is a programming language and proof assistant whose compiler rejects a proof with a wrong step. A reader of a compiled proof still has to work out what the question is, which idea makes the proof work and why the result matters.

With lean-exposition, authors turn a selected result and its supporting sources
into three complementary documents: a detailed reasoning record, a focused
research paper, and an explanation for readers learning the subject. Each links back to the statements, assumptions and sources it uses. You can read
the [worked papers](#read-the-worked-example) without installing anything.

## Read a paper beside its Lean

On the [website](https://wcook04.github.io/lean-exposition-site/read/short/) you
read a paper as you would read any paper, with a graph of its argument beside it that moves as you scroll. Click a statement with a dark tick and its Lean opens at the exact lines, with
links to the same step in the other papers. Back takes you to the sentence you left.

[![A paper on the left with Theorem 1 highlighted, and on the right the Lean statement it refers to, opened under the graph of the argument.](site/public/stills/reader-theorem-1-light-1440.webp)](https://wcook04.github.io/lean-exposition-site/read/short/)

An AI agent read each sentence and its Lean and linked the two. No independent
mathematician has reviewed these links and no program tests whether they say the same thing, and the site says so beside each link.

## Why this project exists

As more mathematics is developed with AI and formal proof tools, the amount of machine-checked material can grow faster than people can understand it.
A mathematician rarely learns from a long list of definitions and lemmas which idea deserves attention. A short summary can leave out the condition on which an argument depends.

Different readers need different accounts of the same mathematics. A specialist
wants the result, its relation to the literature and the main proof. Someone
learning the subject needs the objects introduced, examples they can calculate,
and an explanation of why each step is useful. Someone examining a difficult step needs enough detail to reconstruct it.

The aim is to make all three accounts useful while keeping their mathematical claims consistent. The project has writing methods, tools that record sources and test runs, and worked drafts in which the methods are applied.

## Three documents, three jobs

| Document | What it helps you do |
| --- | --- |
| **Long reasoning record** | Reconstruct the argument, including supporting derivations, assumptions, source references and unresolved questions. |
| **Short research paper** | See the main result and proof in the language of the relevant literature, with routes to the details. |
| **Expository paper** | Learn a selected result through definitions, examples and the ideas behind the proof, with prerequisites stated at the outset. |

These are different writing tasks with no fixed page counts. An exposition may use the detailed record and original sources. Shortening an argument
must preserve the conditions under which it is valid.

## Read the worked example

Imagine choosing an up or down direction for each of many interacting spins.
Some pairs favour the same direction; others favour opposite directions. Finding
the best arrangement is an optimisation problem. The **Sherrington–Kirkpatrick
(SK) model** studies a random version of this problem. The **Quantum Approximate
Optimization Algorithm (QAOA)** is a quantum algorithm for seeking good solutions
to optimisation problems.

The example starts from the manuscripts and Lean sources accompanying OpenAI's
[QAOA and SK result](https://lowrank.github.io/latent-seminar/OpenAI-Math/281-qaoa-sk-parisi-support).
The broader manuscript studies whether this algorithm can approach the model's
best attainable energy. Our drafts concentrate on a mathematical ingredient:
the function used to calculate that value. Under the stated hypotheses, an optimal
choice of this function cannot be flat across any interval below its endpoint.
The drafts explain why this property matters and how the argument works.

Start with the account that suits your purpose:

- **[Exposition](papers/qaoa-sk/expository/main.md):** begin with a two-spin
  calculation, then build up the objects and the no-gap argument. It assumes
  calculus, expectations and elementary linear algebra.
- **[Short paper](papers/qaoa-sk/short/paper.md) · [PDF](papers/qaoa-sk/short/paper.pdf):**
  follow the full-support argument and its scalar consequence. This is the
  specialist account, using stochastic calculus and variational arguments.
- **[Long reasoning record](papers/qaoa-sk/long/reasoning-record.md):** inspect
  the derivations, source destinations and further steps needed for the broader
  QAOA claim.

These are drafts of explanations of existing results; mathematical and reader
review remain open. The retained Lean interfaces cover the full-support and
scalar-value statements, not the whole QAOA convergence claim. The
[source guide](examples/qaoa-sk/README.md) identifies their exact scope and
recorded test runs. See the [papers guide](papers/README.md) to assemble the
three drafts into one portable bundle.

The separate [architectural companion](papers/architecture/README.md) ·
[PDF](papers/architecture/paper.pdf) gives the reasons for the three accounts, how a reader can take different routes through their shared graph, and how to follow a short claim to its assumptions,
detailed argument and original or formal sources.

### YouTube walkthroughs

[How different can two nearly best answers be?](https://www.youtube.com/watch?v=IUAhxUriDVw)
starts with four magnets and explains the mathematical question.
[Read a maths paper beside its argument map](https://www.youtube.com/watch?v=sYMDcT7vyng)
shows how to follow the papers, assumptions, results and sources on the reading website.

[Introduction V3](https://www.youtube.com/watch?v=MBmVMMogXTA) explains how the projects
fit together. All websites, code and videos are on [my home page](https://wcook04.github.io/).

## Use the workflow for another result

Start with one result you want to explain and identify the sources and arguments
it depends on. Record those relationships in an **evidence graph**: a structured
file connecting mathematical claims to their assumptions, citations and recorded test runs. With it a writer has a map of the sources and a reviewer can follow a passage back to its support.

Each paper also has a [graph view](docs/bundle-consumers.md#view-one-paper-as-a-graph):
its sections and passages in reading order, connected to their recorded claims,
sources and test runs. The three papers share the same underlying evidence, so an
application can move between a passage, its support and another account of the
same result. A [whole-corpus view](docs/bundle-consumers.md#view-the-whole-recorded-corpus)
holds one shared pool of records, so an application can look up which papers and passages use each record. Papers can select different goals while retaining
their necessary assumptions and sources. A [record-neighbourhood query](docs/bundle-consumers.md#start-at-any-record-and-follow-its-neighbourhood)
starts from a source, citation, evidence record or claim, follows typed links
in either direction, and reports where the selected view stops. Exact text
selections can also find mapped passages and their support. The local API
supplies these operations for readers, agents and frontends, including the
repository's reading website.

The [reading API](docs/web-api.md#follow-an-explanation-a-derivation-or-an-answer)
also distinguishes an authored derivation, explanation, example or reference.
It connects fuller accounts, illustrations and exercise answers with explicit
reading links, keeping those recommendations separate from shared claims and
proof dependencies. Both endpoint texts are bound to the captured edition.

The [authoring guide](docs/authoring.md) and [writing methods](skills/README.md)
call these steps **authoring transitions**: record the sources, reconstruct the
argument, select the expert paper and teach a result to a stated audience.
Four local transition skills guide those decisions. Their
[review-and-refinement loop](docs/authoring.md#use-and-improve-the-transition-skills)
turns a tested revision into a bounded lesson for the next problem: repair the
paper, test what generalises, and improve the responsible skill. The complete
working method lives here; the [Erdős examples](docs/erdos-method-transfer.md)
record its bootstrap rather than a dependency on another repository.

The software is a local Python command-line tool. It collects exact source
versions, extracts dependencies from Lean projects, validates the graph and packages authored papers with their source mappings. A human or an AI assistant supplies
the mathematics and prose. The `scaffold` command creates empty writing templates;
`assemble` packages documents that have already been written.

Review has two distinct questions: does the writing faithfully describe the
mathematics, and can its intended reader follow it? Use answers to revise both
the document and the writing method. The [reader-review guide](docs/reader-review.md)
describes how to run one bounded session against an exact edition. Automated tests find missing references and changed text and cannot answer those two questions.

## First run

Python 3.11 or newer is required. From a checkout:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install .
lean-exposition validate examples/minimal/evidence-graph.json
lean-exposition inspect examples/minimal/evidence-graph.json
```

After installation, these two commands work offline without Lean. They read a
saved extraction of a small proof: from “P and Q”, conclude “Q and P”. The JSON
output shows the selected result, its helper lemma and the recorded build and
extraction runs. Imported definitions remain explicitly outside the inspected
module. The [minimal example](examples/minimal/README.md) explains how to rerun
the extraction with the pinned Lean toolchain.

To create an empty writing bundle:

```sh
lean-exposition scaffold examples/minimal/evidence-graph.json --out build/minimal
lean-exposition check-bundle build/minimal
lean-exposition export build/minimal --out build/minimal.zip
```

The ZIP contains the graph, three Markdown templates, their mapping records and
a manifest listing the files and hashes. To package the existing authored papers
instead, follow the [assembly commands](papers/README.md#assemble-the-authored-bundle).
The [consumer guide](docs/bundle-consumers.md) explains how another application
can read a bundle without depending on this CLI.

To serve an assembled bundle to a website or another application:

```sh
lean-exposition serve build/qaoa-sk-authored --port 8000
```

The [web API guide](docs/web-api.md) covers shared graph navigation, aligned
paper passages, connection witnesses, comparison, search and exact-edition
text selections. Summary cards, compact graph maps and matches-only passage
queries let a frontend load detail as readers select it. The backend supplies
the data; a frontend can choose its own graph renderer and reading interface.

The repository's own [reading website](site/README.md) is one such frontend.
The papers come first: a graph follows the sentence you are reading, and any
marked statement opens its Lean. **Map** draws the whole argument, with the main
theorem at the top and any result unfolding into what it uses. **Compare** is the
proof as a table: each row is one step, set side by side at every level from the
Lean declaration through the long record and short paper to the exposition. The
Lean index at the back opens OpenAI's source with each central name explained in
the papers' notation. It runs against a local `serve` process or as a static
edition; its guide gives the commands.

Two read-only sidecars make that comparison exact. The
[Lean index](docs/web-api.md) lists every declaration of the vendored source
with its text and the names it mentions, and the
[record alignment](docs/record-alignment.md) points each record to its Lean
declarations, to the exact slice of each paper that states it, and to the
sentences and Lean lines tied together inside that slice. A program confirms that both ends of each exist in the pinned bytes; neither says the mathematics matches.

## Sources and verification

The [examples guide](examples/README.md) covers three starting points:
a local Lean project, a pinned collection of manuscripts and formal sources,
or a public theorem on [Prove2Me](docs/prove2me.md).

The Prove2Me adapter preserves public theorem identifiers, decomposition links
and platform status. Its intake is partial: it does not download proof bodies
or turn a platform's “Proved” label into a local proof run.

For local sources, the [verification guide](docs/verification.md) explains Lean
builds, dependency extraction and the optional Comparator tool. The saved minimal
example has an actual build and extraction. The larger QAOA / SK graph is curated
from source. It retains planned runs and a separate startup-unavailable attempt;
later invocations built and exported the full-support and scalar-value
challenges before their solution builds failed. No accepted research replay or elaborated research extraction
is established by those records. A source hash,
a successful build and a mathematical review answer different questions; the
records preserve those distinctions.

## Repository map

| Location | What you will find |
| --- | --- |
| [papers/](papers/) · [reading guide](papers/README.md) | The three mathematical accounts, source mappings and architectural companion |
| [examples/](examples/) · [example guide](examples/README.md) | The small Lean proof, pinned QAOA / SK corpus, Prove2Me intake and independent bundle reader |
| [docs/](docs/) · [documentation guide](docs/README.md) | Authoring, architecture, verification, integration and research references |
| [skills/](skills/) · [writing methods](skills/README.md) | Four reusable methods for moving from sources to mathematical writing |
| [src/lean_exposition/](src/lean_exposition/) | Python CLI, read-only [web backend](src/lean_exposition/web.py), consumer library, packaged schemas and templates |
| [site/](site/) · [site guide](site/README.md) | The reading website: the argument map, side-by-side Compare, the papers beside the map, the Lean index and the recorded checks, all read from the web API |
| [lean/](lean/) | Lean extractor entry and integration guide |
| [tests/](tests/) | Regression tests for evidence, source intake, packaging and layout |
| [scripts/](scripts/) | Repository layout/link checks, the [web benchmark](scripts/benchmark_web.py) and the [paper bookmark filter](scripts/paper_anchors.lua) |
| [.github/](.github/) | Continuous integration checks |

## Development and licence

This repository owns the papers, tools and website source. Its
[publishing workflow](.github/workflows/pages.yml) builds the reading edition
and sends the generated files to
[lean-exposition-site](https://github.com/wcook04/lean-exposition-site), which
serves the [website](https://wcook04.github.io/lean-exposition-site/) through
GitHub Pages. Make source changes here; the deployment repository is build output.

Agents start at [AGENTS.md](AGENTS.md), which routes setup, writing, queries and
validation to their owners. The [contribution guide](CONTRIBUTING.md) covers setup and validation; the
[architecture and contracts](docs/contracts.md) describe the software's boundaries.
Run `python scripts/check_layout.py`, `python scripts/check_links.py` and
`python -m unittest discover -s tests -v` after a change. Use
`python scripts/check_layout.py --index` to check the staged tree before committing.

Will Cook made this project for [Plectis](https://wcook04.github.io/practical-formal-verification/),
his projects on researching mathematics with AI and on tools that help people
follow what AI produces. His videos, including walkthroughs of results, are on
[YouTube](https://www.youtube.com/@willcook2004).

Original code and documentation are Apache-2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). Included upstream sources retain their own licences and credit.
The [source lock](examples/qaoa-sk/source-lock.json) identifies exact revisions
and content hashes. [Research references](docs/literature.md) and the
[licensed readings](docs/annex/README.md) provide the supporting literature.
