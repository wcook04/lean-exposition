# lean-exposition

**From formal proofs to mathematics people can understand.**

[Lean](https://lean-lang.org/) is a language and proof assistant that checks
precisely stated mathematical arguments. A checked proof gives a reader something
valuable to inspect, but understanding it still takes work: what is the question,
which idea makes the proof work, and why does the result matter?

lean-exposition helps authors turn a selected result and its supporting sources
into three complementary documents: a detailed reasoning record, a focused
research paper, and an explanation for readers learning the subject. Each keeps
a route back to the statements, assumptions and sources it uses. You can read
the [worked papers](#read-the-worked-example) without installing anything.

## Why this project exists

As more mathematics is developed with AI and formal proof tools, the amount of
checkable material can grow faster than people's ability to understand it.
A long list of definitions and lemmas rarely tells a mathematician which idea
deserves their attention. A short summary can hide the very condition on which
an argument depends.

Different readers need different accounts of the same mathematics. A specialist
wants the result, its relation to the literature and the main proof. Someone
learning the subject needs the objects introduced, examples they can calculate,
and an explanation of why each step is useful. Someone checking a difficult step
needs enough detail to reconstruct it.

The aim is to make all three accounts useful while keeping their mathematical
claims consistent. The project combines writing methods, tools for tracking
sources and checks, and worked drafts that show how the methods can be applied.

## Three documents, three jobs

| Document | What it helps you do |
| --- | --- |
| **Long reasoning record** | Reconstruct the argument, including supporting derivations, assumptions, source references and unresolved questions. |
| **Short research paper** | See the main result and proof in the language of the relevant literature, with routes to the details. |
| **Expository paper** | Learn a selected result through definitions, examples and the ideas behind the proof, with prerequisites stated at the outset. |

These are different writing tasks, not fixed page counts. An exposition may draw
directly on the detailed record and original sources. Shortening an argument
must preserve the conditions under which it is valid.

## Read the worked example

Imagine choosing an up or down direction for each of many interacting spins.
Some pairs favour the same direction; others favour opposite directions. Finding
the best arrangement is an optimisation problem. The **Sherrington–Kirkpatrick
(SK) model** studies a random version of this problem. The **Quantum Approximate
Optimization Algorithm (QAOA)** is a quantum algorithm for seeking good solutions
to optimisation problems.

The example starts from the manuscripts and Lean sources accompanying OpenAI's
[QAOA / SK result](https://lowrank.github.io/latent-seminar/OpenAI-Math/281-qaoa-sk-parisi-support).
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
recorded check status. See the [papers guide](papers/README.md) to assemble the
three drafts into one portable bundle.

The separate [architectural companion](papers/architecture/README.md) ·
[PDF](papers/architecture/paper.pdf) explains how the sources, papers and checks
fit together and what another application can inspect.

### YouTube walkthrough — coming soon

A planned walkthrough will start with a concrete example, explain the question
and the key proof idea, then show how to follow the same mathematics through the
papers and Lean sources. The video link will appear here once it is available.

## Use the workflow for another result

Start with one result you want to explain and identify the sources and arguments
it depends on. Record those relationships in an **evidence graph**: a structured
file connecting mathematical claims to their assumptions, citations and recorded
checks. It gives the writer a source map and lets a reviewer follow a passage
back to its support.

Each paper also has a [graph view](docs/bundle-consumers.md#view-one-paper-as-a-graph):
its sections and passages in reading order, connected to their recorded claims,
sources and checks. The three papers share the same underlying evidence, so an
application can move between a passage, its support and another account of the
same result. The local API supplies these views for a future front end.

The [authoring guide](docs/authoring.md) and [writing methods](skills/README.md)
cover selecting the material, reconstructing an argument, writing for specialists
and teaching it to a stated audience. They include methods illustrated by
[eight Erdős problem corpora](docs/erdos-method-transfer.md).

The software is a local Python command-line tool. It collects exact source
versions, extracts dependencies from Lean projects, checks the graph and packages
authored papers with their source mappings. A human or an AI assistant supplies
the mathematics and prose. The `scaffold` command creates empty writing templates;
`assemble` packages documents that have already been written.

Review has two distinct questions: does the writing faithfully describe the
mathematics, and can its intended reader follow it? Use answers to revise both
the document and the writing method. The [reader-review guide](docs/reader-review.md)
shows how to run one bounded session against an exact edition. Automated checks catch missing references
and changed text; they cannot answer those questions for the reader.

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
extraction checks. Imported definitions remain explicitly outside the inspected
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

## Sources and verification

The [examples guide](examples/README.md) covers three starting points:
a local Lean project, a pinned collection of manuscripts and formal sources,
or a public theorem on [Prove2Me](docs/prove2me.md).

The Prove2Me adapter preserves public theorem identifiers, decomposition links
and platform status. Its intake is partial: it does not download proof bodies
or turn a platform's “Proved” label into a local proof check.

For local sources, the [verification guide](docs/verification.md) explains Lean
builds, dependency extraction and the optional Comparator tool. The saved minimal
example has an actual build and extraction. The larger QAOA / SK graph is curated
from source. It retains planned checks and a separate startup-unavailable attempt;
no completed research replay or elaborated research extraction is established by
those records. A source hash,
a successful build and a mathematical review answer different questions; the
records preserve those distinctions.

## Repository map

| Location | What you will find |
| --- | --- |
| [papers/](papers/) · [reading guide](papers/README.md) | The three mathematical accounts, source mappings and architectural companion |
| [examples/](examples/) · [example guide](examples/README.md) | The small Lean proof, pinned QAOA / SK corpus, Prove2Me intake and independent bundle reader |
| [docs/](docs/) · [documentation guide](docs/README.md) | Authoring, architecture, verification, integration and research references |
| [skills/](skills/) · [writing methods](skills/README.md) | Four reusable methods for moving from sources to mathematical writing |
| [src/lean_exposition/](src/lean_exposition/) | Python CLI and library, with packaged schemas and templates |
| [lean/](lean/) | Lean extractor entry and integration guide |
| [tests/](tests/) | Regression tests for evidence, source intake, packaging and layout |
| [scripts/](scripts/) | Repository layout and link checks |
| [.github/](.github/) | Continuous integration checks |

## Development and licence

The [contribution guide](CONTRIBUTING.md) covers setup and validation; the
[architecture and contracts](docs/contracts.md) describe the software's boundaries.
Run `python scripts/check_layout.py`, `python scripts/check_links.py` and
`python -m unittest discover -s tests -v` after a change. Use
`python scripts/check_layout.py --index` to check the staged tree before committing.

Original code and documentation are Apache-2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). Included upstream sources retain their own licences and credit.
The [source lock](examples/qaoa-sk/source-lock.json) identifies exact revisions
and content hashes. [Research references](docs/literature.md) and the
[licensed readings](docs/annex/README.md) provide the supporting literature.
