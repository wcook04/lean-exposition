# Contributing

## Setup

Use Python 3.11 or newer. From this repository's root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -e .
lean-exposition --help
lean-exposition validate examples/minimal/evidence-graph.json
lean-exposition inspect examples/minimal/evidence-graph.json
```

Installation needs the declared Python dependencies. The two minimal-example
commands then run offline without Lean, reading a retained extraction rather
than rerunning a proof. Runtime use does not require installing the writing
skills. To read the supplied authored papers through the CLI, continue with
the [consumer guide's complete journey](docs/bundle-consumers.md#start-with-the-authored-support-theorem).
`scaffold` creates empty documents; `assemble` packages existing writing.

## Validate a change

In the same environment and working directory:

```sh
python scripts/check_layout.py
python scripts/check_links.py
python -m unittest discover -s tests -v
lean-exposition audit-sources examples/qaoa-sk/source-lock.json --root examples/qaoa-sk
```

Run changed commands too. For paper mappings, assemble the authored bundle and
run `check-bundle`; read the selected passages and original sources before
reporting semantic correspondence. For the architecture paper, follow its
[render and inspection route](papers/architecture/README.md#render-and-inspect),
including every page and the delivered PDF's links. Pandoc, Tectonic and
Poppler are optional paper tools; tests explicitly skip Pandoc checks when it
is absent. A skipped check is not a pass.

Before a commit, stage only owned paths, inspect the staged list, and run:

```sh
git diff --cached --name-only
python scripts/check_layout.py --index
```

Keep README's map and commands aligned with the implementation. CI runs offline
contract/source checks after installation. Lean integration requires the
explicitly pinned toolchain and its [verification procedure](docs/verification.md).
Retain failed or unavailable outcomes with their exact scope.

## Check a fresh clone

For changes to installation or the agent/documentation entry route, test the
committed candidate in a disposable clone. This is a validation copy; continue
editing in the original checkout. The recipe uses local Git history and needs
no remote. Choose external scratch storage for `smoke_root` when appropriate.

```sh
checkout_root=$PWD
smoke_root=$(mktemp -d "${TMPDIR:-/tmp}/lean-exposition-smoke.XXXXXX")
git clone --no-local "$checkout_root" "$smoke_root/checkout"
python3 -m venv "$smoke_root/venv"
. "$smoke_root/venv/bin/activate"
python -m pip install "$smoke_root/checkout"
cd "$smoke_root/checkout"
python scripts/check_layout.py
python scripts/check_links.py
python -I -m unittest discover -s tests -v
lean-exposition validate examples/minimal/evidence-graph.json
lean-exposition inspect examples/minimal/evidence-graph.json
lean-exposition audit-sources examples/qaoa-sk/source-lock.json --root examples/qaoa-sk
```

From that clone, run the [authored-bundle journey](docs/bundle-consumers.md#start-with-the-authored-support-theorem):
assembly, validation, direct/prerequisite queries, source-neighbourhood query
and directory/ZIP reading. Follow the returned passage and original-source
locators. Verify an expected manifest when reopening a captured edition. Record
the tested commit and results outside the source tree, and check `git status
--short` in the clone. This exercises the installed package rather than an
editable import from the original checkout.

Layout and staged-layout checks apply to a Git checkout. A wheel installs the
runtime and its packaged resources; it does not include the research corpus or
developer test fixtures. A source distribution is a packaging input, not a claim
to contain the complete example repository. Use a fresh Git clone for the full
contribution and source-audit workflow, and test the installed wheel separately
when packaging changes.

## Sources and writing

For a new source, verify its public origin, revision, permissions and attribution.
Record immutable URLs and actual byte hashes. Preserve upstream notices and
keep frozen source bytes separate from derived configuration. Add negative
fixtures for missing, stale or incorrectly linked evidence when changing the
corresponding validator. Report a new source's limitations next to its result.

Read the matching [transition skill](skills/README.md) before changing an
authoring contract. Prefer one clear check to a new orchestration layer.
Mathematical and reader review remain separate from machine validation.
