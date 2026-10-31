# Lean Exposition

Lean Exposition lets you read a mathematical paper beside the proof written in Lean, a language in which a computer checks each step of a mathematical argument. Click a linked statement in the paper to open the corresponding Lean code.

**[Open Theorem 1 with its Lean proof](https://wcook04.github.io/lean-exposition-site/read/short/?l=b5970-6319&n=full_support#main-result).** No installation is needed. Statements with a dark tick have a link to the code. You can also [explore the proof steps](https://wcook04.github.io/lean-exposition-site/map/) or [read the recorded check results](https://wcook04.github.io/lean-exposition-site/checks/).

This repository contains the website, three example papers, a Python tool and four writing guides. The guides describe how to explain a Lean proof at different levels of detail. A person or an AI assistant writes the papers; the tool checks the supplied files and packages them for reading.

**Run the tool** (Python 3.11 or newer; Lean is not needed):

```sh
git clone https://github.com/wcook04/lean-exposition
cd lean-exposition
python3 -m venv .venv
. .venv/bin/activate
python -m pip install .
lean-exposition validate examples/minimal/evidence-graph.json
```

The last command checks a small saved example and prints JSON: text with named fields. It does not run Lean again. In the output:

- `selected_goals` contains the result being examined, `Minimal.result`.
- `argument_closure` lists that result and the statements it uses.
- `unresolved` lists four built-in Lean names whose definitions are outside the saved example.

To use the tool with the research paper shown below, follow [Inspect one result](#inspect-one-result).

[![A paper on the left with Theorem 1 highlighted, and on the right the Lean statement it refers to, opened under the graph of the argument.](site/public/stills/reader-theorem-1-light-1440.webp)](https://wcook04.github.io/lean-exposition-site/read/short/?l=b5970-6319&n=full_support#main-result)

## The worked example

The example uses a proof from [OpenAI's mathematics release](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md). The papers concern a mathematical model of interacting spins, called the Sherrington–Kirkpatrick model. The introductory explanation begins with just two spins; the other papers give the specialist argument and its detailed calculations.

<details>
<summary>Exact mathematical statement</summary>

For the pure, zero-field Sherrington–Kirkpatrick (SK) model at zero temperature, the Stieltjes measure of every integrable minimiser of the Parisi functional has full support on [0,1).

</details>

OpenAI supplied the original manuscripts and Lean proof. This project adds three explanations and links their statements to the Lean code:

| Paper | For | Read |
| --- | --- | --- |
| Exposition | Readers with calculus, expectations and elementary linear algebra. It begins with a two-spin calculation. | [On the website](https://wcook04.github.io/lean-exposition-site/read/expository/) · [Markdown](papers/qaoa-sk/expository/main.md) · [PDF](papers/qaoa-sk/expository/main.pdf) |
| Short paper | Specialists in stochastic calculus and variational arguments. It gives the full-support argument and its scalar consequence. | [On the website](https://wcook04.github.io/lean-exposition-site/read/short/) · [Markdown](papers/qaoa-sk/short/paper.md) · [PDF](papers/qaoa-sk/short/paper.pdf) |
| Long reasoning record | Readers examining a step. It contains the derivations, source references and steps still needed for the separate claim about quantum circuits. | [On the website](https://wcook04.github.io/lean-exposition-site/read/long/) · [Markdown](papers/qaoa-sk/long/reasoning-record.md) · [PDF](papers/qaoa-sk/long/reasoning-record.pdf) |

These are drafts of explanations of existing results; mathematical and reader review remain open. Will Cook directs the project and is not a mathematician. AI agents did most of the research and drafting.

The Lean covers the full-support and scalar-value statements, and only the full-support tree has a successful build on record. Neither Lean theorem asserts that Quantum Approximate Optimization Algorithm (QAOA) circuit energies converge, which is a claim of OpenAI's separate manuscript. The [source guide](examples/qaoa-sk/README.md) gives the exact scope.

## Inspect one result

Start with [Theorem 1 of the short paper](papers/qaoa-sk/short/paper.md#model-and-result). Its Lean statement is `OAI.ZeroTemperatureSK.full_support` in [Main.lean, line 35](examples/qaoa-sk/upstream/lean/OAI/Probability/SKSupport/Main.lean#L35). It assumes a minimiser has been supplied; existence of a minimiser is a separate input.

The [saved check record](examples/qaoa-sk/verification/full-support-build-extraction-observation-20261026.json) says that `lake build OAI.Probability.SKSupport.Main` completed successfully on 26 October 2026, using Lean v4.34.1 and the recorded OpenAI revision. Cached dependencies may have been reused. Lean reported three standard axioms—assumptions available to the proof—named `propext`, `Classical.choice` and `Quot.sound`. It reported no `sorryAx`, which would indicate reliance on a missing proof.

Comparator checks a proposed Lean proof against a specified statement. Attempts to run it here did not reach a verdict: it has neither accepted nor rejected either theorem. Their results are listed on [What ran](https://wcook04.github.io/lean-exposition-site/checks/).

Checking Lean code does not establish that an English sentence means the same thing, or that a result is new or significant. AI agents added the links between these papers and the Lean. No independent mathematician has reviewed those links, mathematical review of the papers remains open, and no program checks the English against the Lean. The website states this beside each link.

To query the same result from the command line, run these after the [install commands](#lean-exposition) above:

```sh
lean-exposition assemble examples/qaoa-sk/evidence-graph.json \
  --long papers/qaoa-sk/long/reasoning-record.md papers/qaoa-sk/long/reasoning-record.json \
  --short papers/qaoa-sk/short/paper.md papers/qaoa-sk/short/correspondence.json \
  --expository papers/qaoa-sk/expository/main.md papers/qaoa-sk/expository/correspondence.json \
  --out build/qaoa-sk-authored
lean-exposition query-papers build/qaoa-sk-authored \
  --paper short --passage main-result --format text
```

`assemble` writes the papers and their links into `build/qaoa-sk-authored` and prints a list of the packaged files. `query-papers` then prints the claims and assumptions linked to the theorem, their prerequisites, the review state of the passage and the recorded test runs, including the failed and unavailable ones. `lean-exposition audit-sources examples/qaoa-sk/source-lock.json --root examples/qaoa-sk` checks that the 387 included OpenAI files still match the saved copies byte for byte.

## What you can run, and what is private

| In this repository | What it does |
| --- | --- |
| [Command-line tool](src/lean_exposition/) | Records which source versions were used, checks whether source files have changed, lists which Lean statements use which others, checks the saved links, and packages papers for reading. Run `lean-exposition --help` for the commands. |
| [Writing methods](skills/README.md) | Four sets of written instructions, for a person or an AI assistant, covering each step from sources to the three papers. The tool does not load or run them. |
| [Papers and sources](papers/README.md) | The three drafts, their links and the pinned OpenAI files. |
| [Website source](site/README.md) | The code for the reading website. |

No command writes mathematics or prose. A human or an AI assistant supplies both: `scaffold` creates empty templates and `assemble` packages documents already written. The larger environment in which Will Cook runs AI agents on these methods is private and is not in this repository. You can follow the methods and run the tool without it.

The [workflow guide](docs/workflow.md) explains how to apply the tool and guides to another result, and how to package the papers and read them through a local website.

## Sources and verification

The [examples guide](examples/README.md) covers three starting points:
a local Lean project, a pinned collection of manuscripts and formal sources,
or a public theorem on [Prove2Me](docs/prove2me.md).

The Prove2Me import records the theorem names, links between proof steps and
status shown on that website. It does not download the proofs or check them
locally. A “Proved” label remains a report of the website's status.

For your own Lean project, the [verification guide](docs/verification.md)
explains how to run Lean and record which statements each proof uses. It also
covers the optional Comparator checker. The small example includes a saved successful Lean run and the data
extracted from it. For the larger QAOA / SK example, the saved list of statements
and their links was assembled from the sources. Comparator could build and
export the two challenge files but could not finish building the proposed
solutions; it has no accepted run for this example. The records retain those
failed attempts. Checking that a source file is unchanged, running Lean
successfully, and reviewing the mathematics answer different questions.

## Repository map

| Location | What you will find |
| --- | --- |
| [papers/](papers/) · [reading guide](papers/README.md) | The three papers and a separate [paper on the design](papers/architecture/README.md) |
| [examples/](examples/) · [example guide](examples/README.md) | The small Lean proof, the pinned OpenAI sources, a Prove2Me intake and a standalone bundle reader |
| [skills/](skills/) · [writing methods](skills/README.md) | The four writing methods |
| [src/lean_exposition/](src/lean_exposition/) | The Python command-line tool, read-only [web backend](src/lean_exposition/web.py), schemas and templates |
| [site/](site/) · [site guide](site/README.md) | The reading website's source |
| [docs/](docs/) · [documentation guide](docs/README.md) | Guides to authoring, verification, the file formats and research references |
| [lean/](lean/) | A guide to the Lean extractor |
| [tests/](tests/) | The Python test suite |
| [scripts/](scripts/) | Layout and link tests, a [web benchmark](scripts/benchmark_web.py) and a [paper bookmark filter](scripts/paper_anchors.lua) |
| [.github/](.github/) | Continuous integration |

## Videos

In [How different can two nearly best answers be?](https://www.youtube.com/watch?v=IUAhxUriDVw), Will Cook starts with four magnets and explains the mathematical question. In [Read a maths paper beside its argument map](https://www.youtube.com/watch?v=sYMDcT7vyng), he goes through the website. In [Introduction V3](https://www.youtube.com/watch?v=MBmVMMogXTA), he explains how his projects fit together.

## Related projects

- [Proof Reader](https://github.com/wcook04/proof-reader) displays an existing paper beside its authors' Lean, using the argument map developed here. Lean Exposition also supplies methods for writing new explanations of a proof.
- [Plectis's Erdős research](https://github.com/wcook04/plectis-erdos) collects papers, proofs and research records for eight Erdős problems. Its [mathematics website](https://wcook04.github.io/practical-formal-verification/maths/) is a separate research collection from this repository's Sherrington–Kirkpatrick example.

## Development and licence

The [contribution guide](CONTRIBUTING.md) covers setup and validation, the [architecture and contracts](docs/contracts.md) describe the software's boundaries, and agents start at [AGENTS.md](AGENTS.md). After a change, run `python scripts/check_layout.py`, `python scripts/check_links.py` and `python -m unittest discover -s tests -v`. Run `python scripts/check_layout.py --index` on the staged tree before committing.

The [publishing workflow](.github/workflows/pages.yml) builds the website from this repository and sends the generated files to [lean-exposition-site](https://github.com/wcook04/lean-exposition-site), which GitHub Pages serves. Make source changes here.

Will Cook directs this project. His other websites, code and videos are listed on [his home page](https://wcook04.github.io/).

Original code and documentation are Apache-2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). Included upstream sources retain their own licences and credit.
The [source lock](examples/qaoa-sk/source-lock.json) identifies exact revisions
and content hashes. [Research references](docs/literature.md) and the
[licensed readings](docs/annex/README.md) provide the supporting literature.
