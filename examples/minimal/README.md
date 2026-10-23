This synthetic project has no external Lean packages. It pins the toolchain
used for the local experiment; install that version with `elan` if needed.

```sh
lake build Minimal
```

`Minimal.result` uses `Minimal.swap`. Its statement needs the conjunction
type, while its proof needs the helper theorem. These provide a small example
of distinct statement and proof dependencies.

The [actual extraction report](receipts/extraction.json) records both theorems,
their available proof bodies and empty transitive axiom lists. The
[derived evidence graph](evidence-graph.json) preserves the proof edge from
`Minimal.result` to `Minimal.swap`, plus explicit external nodes for `And`
and its constructor/projections. Its selected scope is complete; the graph is
marked partial because those external declarations are not expanded.

After installing the Python package, inspect that saved graph without Lean:

```sh
lean-exposition validate examples/minimal/evidence-graph.json
```

To reproduce extraction from the repository root with the pinned toolchain:

```sh
lean-exposition extract examples/minimal --module Minimal --goal Minimal.result --build --timeout 600 --out /tmp/minimal-graph.json
```

Use a fresh output path. The recorded run used an exact copy of the pinned
compiler's import artifacts in scratch storage; its receipt binds the source
snapshot, generated driver and returned report. These observations concern
this synthetic proof, not the research corpus in `examples/qaoa-sk`.

The optional comparison configs both name `Minimal.result`. The positive
solution module is `ComparatorSolution.lean`, which imports the proof from
`Minimal.lean` and the standard primitive modules required by the exporter. The separate
`NegativeSolution.lean` deliberately
contains `sorry` and is outside the default build target. It must fail the
three-axiom Comparator budget. `Challenge.lean` intentionally has the same
statement with a hole.

```sh
lake comparator --config comparator.json
lake comparator --config comparator-negative.json
```

These commands require Linux sandbox support. See
[`docs/verification.md`](../../docs/verification.md) for platform limits and
the explicit trusted-fixture option. The receipt of a failed or unavailable
tool invocation is not a successful proof check.
