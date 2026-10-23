# lean-exposition

Turn a selected Lean goal and its checking evidence into a traceable starting point
for mathematical writing. The local CLI collects pinned sources, extracts declaration
dependencies, validates an evidence graph, prepares **empty** long-record,
short-paper and expository-paper scaffolds, and packages authored papers with their
claim and citation mappings.

Start by reading the [QAOA / SK source example](examples/qaoa-sk/README.md), or run
the offline workflow below. The example keeps OpenAI's full-support and scalar-value
formal targets separate from the manuscript's broader QAOA convergence argument.

The worked drafts develop that example as a
[long reasoning record](papers/qaoa-sk/long/reasoning-record.md), a
[short mathematical paper](papers/qaoa-sk/short/paper.md), and an
[exposition](papers/qaoa-sk/expository/main.md). See the
[paper bundle workflow](papers/README.md) to assemble all three.

[Contracts](docs/contracts.md) · [Authoring skills](skills/README.md) ·
[Lean and Comparator](docs/verification.md) · [Prove2Me](docs/prove2me.md) ·
[Bundle consumers](docs/bundle-consumers.md) · [Research sources](docs/literature.md)

## First run

Python 3.11 or newer is required. From a checkout:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install .
lean-exposition audit-sources examples/qaoa-sk/source-lock.json --root examples/qaoa-sk
lean-exposition validate examples/qaoa-sk/evidence-graph.json
lean-exposition scaffold examples/qaoa-sk/evidence-graph.json --out build/qaoa-sk
lean-exposition check-bundle build/qaoa-sk
lean-exposition export build/qaoa-sk --out build/qaoa-sk.zip
```

After installation, these commands need no network or Lean installation. The first
command checks every locked source and derived configuration. The resulting bundle
contains a graph, three empty Markdown templates, their correspondence records and a
hashed manifest. The paper state is `scaffold`; no paper or mathematical review has
been generated. The checked-in QAOA graph is a curated source intake, with extraction
and formal replay explicitly marked `not_run`.

To choose the companion formal target or the whole manuscript's question, use
`select` before `scaffold`:

```sh
lean-exposition select examples/qaoa-sk/evidence-graph.json --goal scalar_value --out build/value-selection.json
```

See the graph's `nodes` for available IDs. Selection retains all evidence and computes
the relevant closure; it does not delete inconvenient open obligations.

## From Lean to evidence

The [minimal example](examples/minimal/README.md) proves a conjunction swap using
only Lean's standard library. With its pinned toolchain installed:

```sh
lean-exposition extract examples/minimal --module Minimal --goal Minimal.result --build --timeout 600 --out build/minimal-graph.json
lean-exposition scaffold build/minimal-graph.json --out build/minimal
```

The extractor reads elaborated expressions. It records separate references from
statement types, proof values and inductive structure, plus transitive axioms.
Dependencies outside the chosen module prefixes remain visible boundary nodes.
This is not a tactic trace or an automatically reconstructed mathematical argument.
The [saved minimal extraction](examples/minimal/evidence-graph.json) records an
actual run, with the two local declarations checked and imported dependencies
retained as external boundaries. Its [receipts](examples/minimal/receipts/)
keep build, extraction and Comparator outcomes separate.

Comparator is an optional real tool, with version and platform requirements:

```sh
lean-exposition comparator examples/minimal --config comparator.json --out build/comparator.json
```

A nonpassing invocation writes its receipt and exits nonzero. On platforms without
the required sandbox, it reports `unavailable`. The OpenAI corpus uses an earlier
Lean version and the standalone Comparator interface; read the
[verification guide](docs/verification.md) before attempting it. Source hashes,
Lean builds, Comparator checks, mathematical review and reader understanding remain
separate kinds of evidence.

## From Prove2Me

The optional adapter reads a public theorem and its public decomposition into the
same evidence graph. Supply an existing API key through `PROVE2ME_API_KEY` or a
credential file outside this repository:

```sh
lean-exposition prove2me https://prove2.me/theorems/e9f7d6cb-af95-435c-b432-ce5018f08276 --out build/prove2me
```

It preserves platform IDs, the upstream source link, the platform environment and
the observation date. A platform's `Proved` label is recorded as platform evidence;
it does not become a local Lean or Comparator result. Proof bodies are not downloaded,
so the result is explicitly partial. The [adapter guide](docs/prove2me.md) explains
authentication, limits and how to scaffold its graph. There is no upload operation.

## Writing stages

| Transition and instructions | Current implementation |
| --- | --- |
| [Sources and checks → graph](skills/source-to-graph/SKILL.md) | Intake, extraction and validation |
| [Graph → long reasoning record](skills/graph-to-long/SKILL.md) | Empty template and claim mappings |
| [Long record → short paper](skills/long-to-short/SKILL.md) | Empty template and selection method |
| [Source-backed record → exposition](skills/record-to-expository/SKILL.md) | Empty template and reader review method |

Writers supply the argument and prose. A passage records its claims, assumptions,
citations and exact text hash. Shortening a paper may omit routine detail, but it
must preserve the selected result, its validity conditions and a route to the full
argument. The checker catches missing references and stale bindings; it does not
judge whether a fluent sentence faithfully explains a theorem.

The offline workflow needs only Python and the installed package. The bundle is a
local interface that another application can consume.

Use `lean-exposition inspect GRAPH` to read a goal's evidence and dependencies,
or `lean-exposition inspect-bundle BUNDLE` for a validated directory or ZIP. The
[consumer guide](docs/bundle-consumers.md) includes an independent reader and the
`assemble` command for packaging authored Markdown and mapping pairs. The
[Erdős method examples](docs/erdos-method-transfer.md) show concrete approaches
to selecting, preserving and explaining an argument.

## Repository map

| Location | Owner |
| --- | --- |
| [src/lean_exposition/](src/lean_exposition/) | CLI, contracts, intake, bundle and Lean/Prove2Me adapters; packaged schemas/templates |
| [examples/](examples/) | Small Lean proof and licensed pinned QAOA / SK corpus |
| [lean/](lean/) | Extractor entry and its boundary |
| [papers/](papers/) | Long, short and expository mathematical drafts with source correspondence |
| [skills/](skills/) | Four portable transition methods and routing index |
| [docs/](docs/) | Contracts, authoring, verification, layout policy and [licensed research readings](docs/annex/) |
| [tests/](tests/) | Offline contract, source, packaging and layout regressions |
| [scripts/](scripts/) | Repository checks |
| [.github/](.github/) | CI definition; no publishing workflow |

## Development and licence

Run `python scripts/check_layout.py` and `python -m unittest discover -s tests -v`.
Use `python scripts/check_layout.py --index` before committing staged changes.
[CONTRIBUTING.md](CONTRIBUTING.md) explains checks and source intake.

Original code and documentation are Apache-2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). Vendored sources retain their own licences and attribution.
The [source lock](examples/qaoa-sk/source-lock.json) records exact public URLs,
revisions and content hashes. The literature annex records redistribution decisions.
