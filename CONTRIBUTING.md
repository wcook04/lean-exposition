# Contributing

Use Python 3.11+ and install the project into a virtual environment. Run:

```sh
python scripts/check_layout.py
python scripts/check_links.py
python -m unittest discover -s tests -v
lean-exposition audit-sources examples/qaoa-sk/source-lock.json --root examples/qaoa-sk
```

Before a commit, stage only owned paths and run the layout check with `--index`.
Keep README's map and commands aligned with the implementation. CI runs offline
contract/source checks after installation. Lean integration checks require the
explicitly pinned toolchain; a skipped or unavailable tool is not a passed check.

Layout and staged-layout checks apply to a Git checkout. A wheel installs the
runtime and its packaged resources; it does not include the research corpus or
developer test fixtures. A source distribution is a packaging input, not a claim
to contain the complete example repository. Use a fresh Git clone for the full
contribution and source-audit workflow, and test the installed wheel separately.

For a new source, verify its public origin, revision, permissions and attribution.
Record immutable URLs and actual byte hashes. Preserve upstream notices. Add
synthetic negative fixtures for evidence that is missing, stale or incorrectly linked.
Report a new source's limitations next to its result.

Read the matching transition skill before changing an authoring contract. Prefer
one clear check to a new orchestration layer. Mathematical and reader review remain
separate from machine validation.
