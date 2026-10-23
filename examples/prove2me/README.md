# Prove2Me public metadata example

The [full-support snapshot](full-support/graph.json) is a real read-only intake of
[OAI.ZeroTemperatureSK.full_support](https://prove2.me/theorems/e9f7d6cb-af95-435c-b432-ce5018f08276).
It preserves public platform identifiers and observations, plus filtered snapshot
hashes and the raw-response hashes observed during collection.

```sh
lean-exposition validate examples/prove2me/full-support/graph.json
lean-exposition scaffold examples/prove2me/full-support/graph.json --out build/prove2me-example
```

The platform's `Proved` labels coexist with local `unverified` status. This is a
partial platform dependency view: definition dependencies, proof bodies, Lean
replay and assumption audit are not checked. The separate
[QAOA / SK source example](../qaoa-sk/README.md) is a pinned upstream source intake;
do not conflate the two environments or treat this snapshot as an equivalence
check. The [adapter guide](../../docs/prove2me.md) explains the retained fields,
field selection, authentication and traversal limits.

To refresh, run the documented `prove2me` command into a new empty output directory
and review the new public metadata before replacing this example. The observation
timestamps record when the API was read; they are not upstream Git revisions.
