# Read a bundle without the package

[`read_bundle.py`](read_bundle.py) is a small consumer of exported
lean-exposition ZIPs. It uses only Python 3.11+ standard-library modules and
does not import the package, run Lean, fetch sources or extract archive files.
You can copy this script alongside a bundle and run it independently.

From a checkout with `lean-exposition` installed, create and read an example:

```sh
lean-exposition scaffold examples/qaoa-sk/evidence-graph.json --out build/consumer-example
lean-exposition export build/consumer-example --out build/consumer-example.zip
python3 -I examples/consumer/read_bundle.py build/consumer-example.zip
```

The last command needs no installation. It prints JSON containing the selected
goal IDs and labels, the graph's scope and notes, every recorded evidence kind/status/detail, and each
paper's authoring state, review state and review notes. The sample papers remain
empty scaffolds. Draft and mixed-state bundles are also readable. A failed
read prints a JSON error to stderr and exits with status 1.

For another Python application, load or copy the script and call
`read_bundle(pathlib.Path("bundle.zip"))`. It returns the same dictionary;
invalid bundles raise `BundleError`, and filesystem failures raise `OSError`.

## Checks and limits

The reader accepts manifest schema `1.0`, graph and mapping schemas `1.0` or
`1.1`, and bundle version `0.1.0`. Mapping `1.0` requires the graph-selected
goals; mapping `1.1` permits its own nonempty selection of existing graph nodes.
The reader reports each paper’s selected goals and mapping version. It requires
the exact eight-file archive, checks the seven manifest hashes against raw
file bytes, and verifies the graph identity and paper mappings' graph hashes,
document hashes, selected goals, stage paths and aggregate authoring state.
It reports the observed archive and manifest SHA-256 values too. The manifest
does not hash itself; these observed hashes require a separately trusted value
if a consumer needs to establish origin.

Duplicate, missing, extra or unsafe member names, nonregular members such as
symlinks, encrypted members, malformed ZIP/JSON and unsupported versions are
rejected. JSON must use UTF-8, unique object keys and finite numbers. Only stored
and deflated ZIP members are accepted. The limits match the package: 32 MiB per
member, 64 MiB total uncompressed data and 65 MiB for the complete ZIP.

`transport_integrity: true` means these byte and metadata checks passed. The
script does not reproduce the complete graph and artifact validators: it does
not validate dependency semantics, evidence receipts or passage correspondence.
Use the installed `lean-exposition check-bundle` command for full contract
validation, as described in the [bundle consumer guide](../../docs/bundle-consumers.md).
The output always sets `full_contract_validation` and `semantic_certification`
to `false`. Evidence statuses and review notes are reported records; neither
these checks nor full contract validation establish mathematical correctness,
independent review or reader understanding.
