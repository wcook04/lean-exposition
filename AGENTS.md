# Agent entry

This file owns agent routing. [README.md](README.md) explains the project to
human readers; [CONTRIBUTING.md](CONTRIBUTING.md) owns development setup and checks.
Use the task table to open the relevant source before editing. Read the
[contracts and architecture](docs/contracts.md) for changes to runtime behaviour,
evidence or file formats.

## Start here

Work from this repository's root. Confirm the current branch, revision and dirty
paths before editing; preserve other work. Follow [development setup](CONTRIBUTING.md#setup)
to install the CLI in a virtual environment, then run the offline minimal
example there. No agent-skill installation is required to use the package.

For the maintained mathematical papers, follow the [authored-bundle journey](docs/bundle-consumers.md#start-with-the-authored-support-theorem).
It assembles existing writing, opens a theorem, distinguishes direct mappings
from prerequisite use, and follows a source back to its paper passages. Start
there before inventing a new graph or duplicating an index. Use `--help` on the
installed command when changing options. [Query choice](docs/bundle-consumers.md#choose-the-entry-for-your-question)
separates paper, graph, corpus and record-level operations.

## Route the task

| Task | Read and work here | Verify with |
| --- | --- | --- |
| Select sources and record a result | [Source-to-graph skill](skills/source-to-graph/SKILL.md), [intake](src/lean_exposition/intake.py), [graph contracts](src/lean_exposition/contracts.py) | `audit-sources`, `validate`; intake and graph tests |
| Extract or check Lean declarations | [Verification guide](docs/verification.md), [verification](src/lean_exposition/verification.py), [extraction](src/lean_exposition/extraction.py), [packaged Lean helper](src/lean_exposition/resources/lean/Extract.lean) | Verification tests and the affected pinned Lean example; retain actual outcomes |
| Read a Prove2Me theorem | [Adapter guide](docs/prove2me.md), [adapter](src/lean_exposition/prove2me.py) | Prove2Me tests; preserve partial intake and platform evidence |
| Write or revise the long record | [Graph-to-long skill](skills/graph-to-long/SKILL.md), [authoring contract](docs/authoring.md), selected paper under [papers/](papers/) | Graph and passage mappings, source review, `assemble` and `check-bundle` |
| Select a short paper | [Long-to-short skill](skills/long-to-short/SKILL.md), the existing long record and original sources | Same claim conditions, literature credit and routes to omitted details; bundle checks |
| Explain a result to a reader | [Record-to-exposition skill](skills/record-to-expository/SKILL.md), original argument and selected reader prerequisites | Source review and an actual sequential reader review; bundle checks |
| Assimilate reviews or improve the writing method | [Review-and-refinement loop](docs/authoring.md#use-and-improve-the-transition-skills), [transition owners](skills/README.md), [reader review](docs/reader-review.md) | Repair the affected account; test a general lesson on two different cases and an exception; retain the applied method version |
| Package or consume authored papers | [Consumer guide](docs/bundle-consumers.md), [bundle](src/lean_exposition/bundle.py), [consumer](src/lean_exposition/consumer.py) | Bundle, consumer and adversarial tests; independent reader under [examples/consumer/](examples/consumer/) |
| Navigate source, claim or paper neighbourhoods | [Record query](docs/bundle-consumers.md#start-at-any-record-and-follow-its-neighbourhood), [consumer](src/lean_exposition/consumer.py); `query-corpus` and `query-papers` | Corpus-query and paper-range tests; preserve stored directions, exact editions and explicit query boundaries |
| Change a command | [CLI](src/lean_exposition/cli.py) and its owning module above | CLI tests and the documented command |
| Serve the graph and papers to a website | [Web API](docs/web-api.md), [transport](src/lean_exposition/web.py), existing consumer and bundle owners | HTTP, capture and consumer tests; installed `serve` and an actual HTTP request |
| Revise the architectural companion | [Companion source](papers/architecture/paper.md), [render and link policy](papers/architecture/README.md#render-and-inspect); keep commands in the technical guides | Render and inspect every PDF page; check relocated PDF links and rendering tests |
| Improve human documentation or repository layout | [Folder map](README.md#repository-map), [documentation guide](docs/README.md), [layout policy](docs/repository_layout.json) | Link and layout checks; run changed examples and inspect rendered prose |

The [skill index](skills/README.md) describes when each writing method applies.
Load the matching skill before its transition. Mathematical gaps return to
research; changing prose cannot close a proof obligation. Runtime code must remain
independent of these instructions and skills.

## Preserve the boundaries

- Keep one CLI and the existing module owners. Packaged schemas, templates and
  the Lean helper live under `src/lean_exposition/resources/`; do not fork them
  into a second active copy.
- Preserve source revisions, byte hashes, licences and attribution. Keep fetched
  source bytes distinct from explicitly derived configuration.
- Keep builds, extraction, Comparator, platform labels, mathematical review and
  reader review separate. Failed or unavailable checks remain visible outcomes.
- Dependency edges run from consumer to prerequisite. Keep Lean expression,
  curated argument, citation and platform relationships distinct.
- Preserve hypotheses, unresolved obligations and the scope of each claim when
  shortening or explaining it. `scaffold` creates empty templates; `assemble`
  packages authored documents. Inspect the current mapping states before reporting
  a paper as reviewed.
- If text or source mappings change, update the affected bindings deliberately
  and reassemble. Hash validation establishes byte consistency, not semantic truth.
- Coordinate exact write paths, preserve unrelated changes and stage only owned
  files. Do not edit frozen upstream sources to satisfy local style checks.

## Validate and finish

Run from the repository root in the installed Python environment:

```sh
python scripts/check_layout.py
python scripts/check_links.py
python -m unittest discover -s tests
lean-exposition validate examples/minimal/evidence-graph.json
lean-exposition inspect examples/minimal/evidence-graph.json
```

Run the affected integration or authored-bundle commands from the guides above.
For an installation or entry-route change, run the [fresh-clone smoke test](CONTRIBUTING.md#check-a-fresh-clone) and exercise the documented query journey.
Source intake changes also require `audit-sources`; Lean changes require the
pinned toolchain and an actual run. Keep generated bundles and scratch work out
of maintained source paths.

Before committing, inspect the staged file list and run
`python scripts/check_layout.py --index`. Report the changed result, checks run,
remaining limitations and commit state. Keep these instructions concise; detailed
contracts and writing methods stay with their linked owners.
