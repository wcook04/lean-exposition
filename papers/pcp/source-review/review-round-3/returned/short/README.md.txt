# Specialist review: substantive return and edited manuscript

Start with **review.md**. The central mathematical argument is now substantially reconstructible; the main remaining problem is how the earlier material is organized. The return includes a complete revised manuscript as a separate proposal, not a copy of the original input archive.

## Contents

- **review.md** — sustained judgment, source-based proof checks, exact remaining problems, literature comparison, explanation of the revision and concrete reconstruction criteria.
- **repair_audit.json** — all 49 original IDs, with independent verdicts, current evidence, reader consequences and next actions. Counts: 30 fixed, 15 retained correctly, 2 partly fixed, 1 not fixed, 1 successful alternative. These assess the supplied edition, not the proposal.
- **proposed/papers/short/paper.md** — complete edited specialist manuscript, titled *From local bit tests to one colouring*.
- **proposed-specialist.diff** — exact patch from the supplied primary Markdown to that proposed manuscript.
- **paragraph_map.md** and **paragraph_decisions.json** — complete paragraph-role coverage, with adjacent decisions grouped for reading.
- **first_reading.md** — the lead reviewer's account saved before inspecting the author repair ledger and old reviews; prior priming is disclosed.
- **coverage.md** — exact editions, actual source-reading scope, browser surface, executions and limits.
- **checks.py** and **checks-output.json** — reproducible finite diagnostics and exact arithmetic; run with standard-library Python.
- **execution_results.json** — supplied-check stdout, actual browser observations and command-capture details.
- **package_validation.json** — final audit-ID, diff, equation-tag and payload-integrity checks.
- **response_manifest.json** — hashes of this return's files.

## Using the proposed manuscript

It is an edit candidate for the original source tree's `papers/short/paper.md`. Its companion paths intentionally retain that repository-relative layout. Copy it to that location or apply the diff in a working copy of the source tree to use those links. The original supplied edition has not been changed. The proposal has been checked as prose/mathematics against inspected sources, but it has not been typeset as a final PDF or integrated into the reader.

The draft brings the table inventory forward, makes the auxiliary row type explicit, gives the supplier theorems clear contracts, preserves the local correction and same-witness assembly, and adds the row-to-table averaging explanation. The historic defective scalar-test example remains in Appendix A. This is a reallocation of explanatory space, not a claim of a dramatically shorter paper or a new PCP theorem.

No fresh Lean replay, human learning outcome, endorsement, sending or publication is implied.
