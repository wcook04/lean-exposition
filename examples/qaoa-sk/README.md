# QAOA, the SK value, and Parisi full support

This example contains the two Lean source trees selected by [OpenAI's family 281 scope statement](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md). It provides 347 public Lean modules, their Comparator interfaces, and pinned build metadata for developing explanations tied to actual declarations.

The source pin is `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, the initial public commit of 6 October 2026. The selected source trees, interfaces, build metadata, and manuscript directories were unchanged at public main `1581d4cbdd69a0faf34b2089614fe2a814316a6a` when checked on 23 October 2026.

## Read the source and the short paper

The short paper reconstructs the full-support argument and its scalar consequence.
Use these links to read it alongside the corresponding OpenAI manuscript:

| OpenAI release | This repository's short reconstruction |
| --- | --- |
| [Full-support manuscript (PDF)](upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf) | [Short paper (PDF)](../../papers/qaoa-sk/short/paper.pdf) |
| [Original TeX source](upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex) | [Editable Markdown](../../papers/qaoa-sk/short/paper.md) |
| Original statement and argument | Draft explanation with [passage-to-source mappings](../../papers/qaoa-sk/short/correspondence.json) |

OpenAI supplied the original manuscripts and Lean sources. This repository adds
the explanatory drafts, source mappings and local tooling. The separate
[Prove2Me intake](../prove2me/README.md) records public platform metadata and
decomposition links; its platform status stays distinct from local verification.

The [papers guide](../../papers/README.md) also leads to the detailed reasoning
record and exposition. The broader QAOA manuscript is a separate source; the
scope table below distinguishes its claim from the two retained formal targets.

## Mathematical scope

| Object | Boundary |
| --- | --- |
| `OAI.ZeroTemperatureSK.full_support` | Every admissible integrable minimizer in the pure zero-field SK model has full relative Stieltjes support on `[0,1)`. The conclusion includes a diffusion and selected moment identities. Minimizer existence is not a separate conclusion. |
| `OAI.SKValue.value_consequences` | Parisi ground-state value identities and finite Gaussian coefficient approximations, conditional on an admissible minimizer and, where required, its associated diffusion. |
| QAOA thermodynamic-first convergence | A claim of the linked manuscript. Neither retained Lean target asserts convergence of QAOA circuit energies. |

The QAOA manuscript takes system size to infinity before increasing circuit depth. Its finite depth and deterministic angles may depend on the desired accuracy; the statement supplies no quantitative depth bound or efficient angle-selection procedure. Keep this manuscript claim distinct from the two formal interfaces.

## Source map

- [source-lock.json](source-lock.json): immutable public URLs, SHA-256 hashes, byte lengths, source licences, target declarations, and the exact inline contents of the two derived configurations. File paths are relative to this example directory.
- [evidence-graph.json](evidence-graph.json): a manually curated intake with full support selected by default, separate scalar-value and QAOA manuscript goals, and explicit unrun checks. Its two interface mappings are not extracted Lean dependency edges.
- [upstream/lean/OAI/Probability/SKSupport/](upstream/lean/OAI/Probability/SKSupport/): the full-support proof tree, 135 modules and 989,995 source bytes.
- [upstream/lean/OAI/Probability/SKValue/](upstream/lean/OAI/Probability/SKValue/): the scalar-value proof tree, 212 modules and 1,487,979 source bytes.
- [upstream/lean/ComparatorChallenges/](upstream/lean/ComparatorChallenges/): the two admitted challenge statements and their original verification configurations. The implementing proofs are in the `OAI` trees.
- [upstream/lean/docs/281.md](upstream/lean/docs/281.md): the upstream description of formal coverage.
- [upstream/preprints/](upstream/preprints/): both exact public manuscript directories, including the original PDFs, TeX/BibTeX sources, and attribution READMEs. The QAOA directory has 12 files (929,329 bytes); full support has 14 (619,968 bytes).
- [upstream/provenance/](upstream/provenance/): original build configurations and dependency metadata, retained as data.
- [references.bib](references.bib): manuscript citations with immutable upstream links.
- [verification/preflight.py](verification/preflight.py): source and dependency-pin checks plus an inventory of local replay prerequisites. Its [recorded preflight](verification/preflight-observed.json) and [unavailable Comparator invocation](verification/comparator-unavailable.json) preserve the actual local outcomes.

A static scan followed every `OAI` import from the two `Main` modules. Every imported `OAI` module lies in these two trees; the only external import name is `Mathlib`. This checks source coverage only. The local verification attempts and their limits are recorded below.

## Build configuration

The runnable package is [upstream/lean/lakefile.lean](upstream/lean/lakefile.lean). It preserves Lean `v4.34.1`, the upstream `autoImplicit := false` setting, and mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. Its default library has exactly the two retained `Main` modules as roots.

The original OpenAI package resolves 42 package entries and runs compatibility-patch hooks for other parts of its large library. The derived package declares only mathlib and retains its eight transitive package pins. Each pin matches the original OpenAI lockfile. Its [derived lockfile](upstream/lean/lake-manifest.json) therefore contains nine packages. The original Lake configuration and lockfile remain under `upstream/provenance/` and are not the active package configuration.

After installing the Python package, check this corpus without triggering a toolchain installation:

```sh
python examples/qaoa-sk/verification/preflight.py --out /tmp/qaoa-sk-preflight.json
```

Exit 0 means the listed prerequisites are present; exit 2 means unavailable;
exit 1 means an input check failed. Even exit 0 does not check executable
compatibility, dependency checkout contents, sandbox functionality, or a proof.
The only subprocess probe is `elan toolchain list`. Lean and Lake shims can
install a missing toolchain when invoked, so a version probe is not a harmless
substitute for that inventory.

The recorded 23 October 2026 run passed all 387 source and two derived-file
hash checks, and all nine dependency-pin comparisons. Lean `v4.34.1` and the
standalone Comparator tools were unavailable on that host. The attempted
full-support Comparator invocation could not start because `comparator` was
not installed. No research-corpus build, extraction, axiom audit or statement
comparison was performed; the scalar-value Comparator invocation remains unrun.

With the exact toolchain and dependencies provisioned, run from the repository root:

```sh
cd examples/qaoa-sk/upstream/lean
lake exe cache get
lake build
```

The retained [Comparator instructions](upstream/provenance/comparator-README.md) require `comparator`, `landrun`, and `lean4export`. After installing those tools separately, check the selected interfaces from the same directory:

```sh
lake env comparator ComparatorChallenges/SKFullSupport.json
lake env comparator ComparatorChallenges/SKValue.json
```

Both configurations permit only `propext`, `Quot.sound`, and `Classical.choice`; `enable_nanoda` is false. A successful build, a Comparator result, and a mathematical review answer different questions and should have separate receipts.

The historical published Comparator/exporter pair is pinned to Lean `v4.34.0`;
compatibility with this corpus's `v4.34.1` has not been tested here. The commands
above describe trusted-corpus use. See the [verification guide](../../docs/verification.md)
for exact checker pins, source/cache limits and the additional legacy sandbox
requirements for adversarial submissions. Do not upgrade this corpus to the
minimal example's Lean 4.35 toolchain just to obtain `lake comparator`.

The public Prove2Me metadata example uses Lean `v4.33.1` and a different Mathlib
revision. A matching displayed theorem name does not transfer its platform
status into local verification of these pinned source bytes.

## Attribution and redistribution

Vendored OpenAI files were downloaded directly from immutable public URLs and retain the upstream [Apache-2.0 licence](upstream/LICENSE), also supplied at [upstream/lean/LICENSE](upstream/lean/LICENSE). Its redistribution clause covers source and object forms. The repository root, `preprints/` ancestor, both exact manuscript trees, their READMEs, and source headers were checked for additional licensing restrictions; none were found in this selected scope. The licence evidence and complete manuscript inventories are recorded in [source-lock.json](source-lock.json). Both manuscript trees are retained without modification, including their original attribution.

The retained mathlib dependency metadata is Apache-2.0; its [licence copy](upstream/provenance/mathlib-LICENSE) is included. Dependencies themselves are fetched by Lake and retain their own notices. The two derived package configuration files are identified separately in the source lock; they are modifications for this selected corpus.

The selected dependency root licences were also checked at their immutable pins:
Mathlib and seven transitive packages use Apache-2.0; the
[Cli dependency uses MIT](https://raw.githubusercontent.com/leanprover/lean4-cli/e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204/LICENSE).
This root-licence inventory does not audit every asset bundled in those dependencies.

OpenAI is the credited author of both manuscripts:

- [QAOA attains the SK ground-state energy in the thermodynamic-first limit](upstream/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf), 25 September 2026. [TeX source](upstream/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/main.tex) and [references](upstream/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/references.tex).
- [Full support of the zero-temperature Sherrington–Kirkpatrick order parameter](upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf), 27 September 2026. [TeX source](upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex) and [bibliography](upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/references.bib).

[QAOA and the SK optimum: Parisi support and the order of limits](https://lowrank.github.io/latent-seminar/OpenAI-Math/281-qaoa-sk-parisi-support), dated 7 October 2026, is a useful secondary reading route. Its text is not part of this vendored corpus.
