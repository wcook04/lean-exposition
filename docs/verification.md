# Lean verification and dependency extraction

The optional Lean adapter executes local tools and retains their output and
exit code. The Python-only workflow does not require Lean. Install the
toolchain named by a project's `lean-toolchain` before running its code.
Extraction evaluates trusted Lean source in the local process; it is not an
isolation boundary for untrusted submissions.

The synthetic example requires no Mathlib or other package. Its toolchain is
pinned to `leanprover/lean4:v4.35.0-rc2`:

```sh
cd examples/minimal
lake build Minimal
```

Then, from the repository root or an installed environment:

```python
from lean_exposition.verification import extract_dependencies

report = extract_dependencies(
    "examples/minimal", "Minimal", ["Minimal.result"],
    module_prefixes=["Minimal"],
)
```

`Minimal.result` uses `Minimal.swap`. Lean's elaborated proof body identifies
that edge. `And`, its constructor, and its projections are explicitly external
to the selected `Minimal` module prefix.

The [recorded real extraction](../examples/minimal/receipts/extraction.json)
returns both theorems, their source ranges, empty transitive axiom lists and
available proof bodies. `Minimal.result` has a proof-value edge to `Minimal.swap`.
Its selected module scope is complete. The resulting
[evidence graph](../examples/minimal/evidence-graph.json) contains six nodes and
eight typed edges; its overall status remains `partial` because four
`Init.Prelude` declarations are explicit external boundaries.

This run used the pinned toolchain and a byte-checked copy of its required
import artifacts in faster scratch storage, supplied through `LEAN_PATH`.
It repaired an incorrect qualification of `Lean.Core.CoreM.toIO'` in the
driver. The earlier [timeout receipt](../examples/minimal/receipts/extraction-attempt.json)
is retained as a separate attempt. Build, expression extraction and the
Comparator fixture checks below remain distinct evidence classes.

The extractor template is packaged at
[`Extract.lean`](../src/lean_exposition/resources/lean/Extract.lean), so extraction
does not depend on the source checkout remaining present after installation.

## Python API

- `extract_dependencies(project, module, roots, *, module_prefixes=None,
  lean_command=None, timeout=120, max_declarations=1000)` returns the raw
  extraction object plus its process receipt. The default command is
  `lake env lean --run`, followed by the generated driver's filename.
  An override supplies the command prefix before that filename.
- `check_build(project, module, *, lake_command=("lake",), timeout=120)`
  builds the specified module and returns a `lean_build` receipt.
- `verify_comparator(project, config, *, command=None, timeout=120)`
  appends the config path to a command prefix. The default prefix is
  `lake comparator --config`. For legacy Comparator, pass
  `command=["comparator"]` after installing compatible binaries.

An extraction failure raises `VerificationError`; `.receipt` carries the
command, return code, stdout and stderr. Other operations return receipts
with `passed`, `failed`, `unavailable`, or `timed_out`. Comparator's documented
exit code 2 in the integrated default command means it could not start, so it
is `unavailable`. Supplied legacy or custom commands retain nonzero exits as
`failed`; they do not inherit the integrated checker's exit-code convention.
Exit code 1 also covers build, export and operational errors in the integrated
tool. Read its diagnostic before describing the outcome as a rejected proof.

Extraction and build receipts bind the selected module and SHA-256 hashes of
the project's Lean sources and environment files before execution. The adapter
checks those hashes again afterward; a change invalidates passing evidence.
Imported package source outside the project is represented by the dependency
lock and graph's external boundary. This does not certify arbitrary compiled
dependency artifacts or prevent a file being changed and restored between the
two observations.

## What the extracted graph means

The report has `schema_version: 1` and these fields:

| Field | Meaning |
| --- | --- |
| `module`, `roots`, `module_prefixes` | Requested module, declarations and traversal boundary |
| `declarations` | In-scope constants reached from the roots |
| `type_dependencies` | Constants in each elaborated type |
| `value_dependencies` | Constants in each elaborated body, including opaque theorem bodies when available |
| `structural_dependencies` | Inductive families, constructors and recursor rules needed in addition to expression references |
| `axioms`, `has_sorry` | Transitive axiom names from Lean's `collectAxioms`; `sorryAx` is recorded explicitly |
| `source` | Defining logical module and available declaration range; line numbers are one based |
| `type_rendering` | The expression renderer used for types; the lightweight driver uses Lean's debug expression rendering |
| `external_dependencies` | Referenced declarations outside the selected module prefixes, without expanding their bodies |
| `missing_declarations`, `unexpanded_declarations` | Unresolved references and declarations stopped by the size limit |
| `unavailable_bodies` | In-scope definitions or theorems whose bodies were unavailable for traversal |
| `scope_complete` | Whether the selected scope was exhausted; external boundaries remain explicit |
| `receipt` | Actual command output, exit code and generated extractor digest |

Edges run from a declaration to its prerequisite. The module boundary defaults
to the requested module and its child module names. Select a wider project
prefix explicitly when helper modules live elsewhere. A bounded report can
still have complete transitive root axiom lists, because Lean collects those
independently of this graph's presentation boundary.

This is an expression dependency graph. It does not identify which source
tactics, macros or elaborator extensions were needed to generate a term, nor
which dependencies carry the mathematical idea. Missing source ranges are
null rather than invented. An elaborated dependency report is distinct from
a successful source build, kernel replay, statement comparison, manuscript
equivalence review and reader review.

The implementation uses Lean's
[`FoldConsts`](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/Lean/Util/FoldConsts.lean)
and
[`CollectAxioms`](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/Lean/Util/CollectAxioms.lean)
APIs. Structural cases follow the public Apache-2.0 implementation in
[`Comparator/Util.lean`](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Util.lean).
The analogous traversal in
[`import-graph`](https://github.com/leanprover-community/import-graph/blob/e928b72544873815af278d38681b31c0293588e3/ImportGraph/Imports/RequiredModules.lean)
also warns that constant dependencies do not suffice to reconstruct imports
used by source tactics and syntax.

The driver imports the target through `Lean.importModules` with private body
data and environment extensions enabled. It can inspect legacy sources and
module-system sources without rewriting them. The compiler API imports remain
separate from the target environment; target initializers run as trusted local
code.

The current graph translator resolves logical module `M.N` to `M/N.lean`
under the project root. Projects using a non-default Lake `srcDir` are not
resolved automatically and fail with “selected module source is unavailable”.
This is a source-location limitation, even if Lean successfully extracted a
report from the project. The checked-in examples use the supported layout.

For this narrow operation, the existing Lean APIs avoid an additional tracing
framework. The deprecated original LeanDojo and its successor
[LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2/tree/baed5eae6e87a65a446d9f54af07aab2154e7599)
provide richer tactic-state and premise tracing. The successor also carries
training and inference dependencies unnecessary here. Its README says MIT,
while its actual
[`LICENSE`](https://github.com/lean-dojo/LeanDojo-v2/blob/baed5eae6e87a65a446d9f54af07aab2154e7599/LICENSE)
contains Apache-2.0; no LeanDojo code is copied or installed by this project.

## Comparator

Lean 4.35 integrates Comparator as `lake comparator`, and kernel replay as
`lake check`. Its default sandbox uses Linux `bubblewrap`:

```sh
cd examples/minimal
lake comparator --config comparator.json
lake comparator --config comparator-negative.json
```

The positive config asks for `Minimal.result` with the standard three-axiom
budget. The negative solution retains `sorry` and must be rejected because
`sorryAx` is outside that budget. The challenge intentionally has a hole;
the checker compares its statement with the supplied proof.

Comparator exports several standard primitive declarations independently of
the selected proof. Its solution wrapper imports the modules containing those
primitives (`Init.Core`, `Init.Data.Nat.Gcd` and
`Init.Data.Nat.Bitwise.Basic`), even though the extraction fixture needs only
`Init.Prelude`.

On systems without that sandbox, the default command reports unavailable.
For a trusted synthetic fixture only, the operator can explicitly invoke
`lake comparator --inadvisably-no-sandbox --config comparator.json`.
The receipt records that flag. This weaker local experiment does not establish
the documented security guarantee for untrusted projects. The adapter never
adds the flag automatically.

The checked-in synthetic
[`positive receipt`](../examples/minimal/receipts/comparator-positive.json)
records exit 0; the
[`negative receipt`](../examples/minimal/receipts/comparator-negative.json)
records exit 1 for the proof containing `sorryAx`. Both are explicit
no-sandbox local experiments on the pinned toolchain. Their diagnostic streams
are represented by SHA-256 digests in the receipts.
The separate
[`default invocation receipt`](../examples/minimal/receipts/comparator-sandbox-unavailable.json)
records that the sandboxed checker could not start on that platform.

The [current Comparator README](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/README.md)
deprecates the standalone project in favour of core Lean 4.35. Older toolchains
need a compatible Comparator and `lean4export`; the old documented sandbox
uses `landrun` and `systemd-run`. Do not use the fake development sandbox as
security evidence. Export-only checking also does not establish that an export
matches the source project unless that binding is checked independently.

Comparator compares exported Lean statements and the declarations on which
their meanings depend; it is not a mathematical equivalence prover for
different formulations. The historical checker matches declaration names,
universe parameters and elaborated types using Lean expression alpha-equivalence,
and compares non-hole dependencies recursively. Selected proof bodies may differ.
See its pinned [comparison implementation](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Compare.lean)
and [expression equality](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Expr.lean#L804).
Definition holes require an additional check of the
intended construction: a well-typed replacement can satisfy the formal
challenge while avoiding its intended mathematical question. The two family
281 configs below contain no definition holes. Their permitted-axiom lists are
an upper bound, not a report of which axioms the proofs actually use.

For historical version selection, Comparator commit
`d03acab154d269c06e60e4de7e4cc85deebff94b` pins Lean `v4.34.0` and exporter
`076e8e57707e813375e8f9da8bf989799ace9680`. Those are source-observed pins,
not a tested compatibility claim for Lean `v4.34.1`. Comparator, the exporter,
Lean and optional Nanoda use Apache-2.0; Landrun uses MIT. Keep each adopted
component's notices and validate the exact selected binary pair.

The historical exporter imports built modules from Lean's search path. Its
[export parser](https://github.com/leanprover/lean4export/blob/076e8e57707e813375e8f9da8bf989799ace9680/Export/Parse.lean#L487)
discards the version metadata line; it does not use that line to establish
compatibility. A valid export or unchanged source digest therefore does not
independently authenticate cached compiled modules. The standalone
[security contract](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md)
also requires trusted challenge/configuration/imports, appropriate cache
provenance, Landrun isolation and the documented `systemd-run` wrapper for
adversarial submissions. The bare legacy commands below describe trusted-corpus
use, not that complete security setup.

## OpenAI family 281

The pinned public release
[`openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a)
uses Lean `v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with Apache-2.0 source licensing.
Its selected Comparator configurations target
`OAI.SKValue.value_consequences` and `OAI.ZeroTemperatureSK.full_support`.
Both permit only `propext`, `Quot.sound` and `Classical.choice`; neither
enables the optional Nanoda checker.

The public [family scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md)
states the exact boundary: selected Parisi value identities and finite Gaussian
approximations are conditional on an admissible minimizer and diffusion;
the full-support result concerns an admissible minimizer and does not separately
assert its existence. These selected formal statements do not assert convergence
of QAOA circuit energies. A Comparator pass for them cannot certify the whole
QAOA manuscript. The
[Latent Seminar article](https://lowrank.github.io/latent-seminar/OpenAI-Math/281-qaoa-sk-parisi-support)
also explicitly reports that its notes did not perform a Lean build, axiom audit
or manuscript equivalence check.

The whole OpenAI repository has many pinned dependencies and compatibility
patches. Importing the two top-level files alone is not a runnable extraction.
Build the relevant pinned source and transitive dependencies before requesting
elaborated graphs. This repository's small synthetic example demonstrates the
mechanism without claiming a fresh replay of those research proofs.

The corpus's [preflight command](../examples/qaoa-sk/verification/preflight.py)
checks locked input bytes, selected dependency pins, the exact installed Lean
toolchain and required executable availability. It does not invoke Lean or
Comparator. Its [observed receipt](../examples/qaoa-sk/verification/preflight-observed.json)
reports passed source/pin checks and unavailable replay prerequisites.
The separate [Comparator receipt](../examples/qaoa-sk/verification/comparator-unavailable.json)
records a real attempt to execute `comparator ComparatorChallenges/SKFullSupport.json`:
the executable was absent, so no checker process began. The scalar-value check
was not attempted. These receipts establish neither a research-proof pass nor
a research-proof rejection.

The unavailable invocation used the Python API with the explicit standalone
prefix, avoiding an auto-installing Lake shim:

```python
from lean_exposition.verification import verify_comparator

receipt = verify_comparator(
    "examples/qaoa-sk/upstream/lean",
    "ComparatorChallenges/SKFullSupport.json",
    command=["comparator"],
)
```

The published receipt retains project-relative source hashes and the config
hash. Diagnostic streams are represented by SHA-256 digests and a short factual
summary. For a real legacy replay, first provision the pinned environment and
compatible checker, then use the documented `lake env comparator` route so
the project library search path is available. Keep failed and unavailable
receipts alongside successful ones and bind each to its selected target.
