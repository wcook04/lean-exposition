# Worked-exposition review response

Start with **[review.md](review.md)**. It gives the whole-paper verdict, the new findings, the mathematical constraints on revision, a replacement opening and route, and a prioritized revision with observable reconstruction tasks.

The response is a new review deliverable. The supplied paper, PDFs, Lean sources and published reader remain unchanged.

## Main files

| File | Role |
| --- | --- |
| [review.md](review.md) | Sustained main critique and concrete redesign |
| [repair_audit.json](repair_audit.json) | Every original finding: 29 fixed, 11 retained correctly, 2 successful alternatives, 2 partly fixed |
| [coverage.md](coverage.md) | Exact edition, actual reading/execution, first-reading exposure and limits |
| [replacement_trace.md](replacement_trace.md) | One colouring constraint through its certificate, encodings and actual bit reads |
| [proposed_changes.patch](proposed_changes.patch) | Conservative textual corrections, not the full structural rewrite |
| [patch_notes.md](patch_notes.md) | Patch scope, application and validation |
| [paragraph_map.md](paragraph_map.md) | 56 grouped decisions covering all 181 prose/list blocks |
| [paragraph_ledger.json](paragraph_ledger.json) | Full paragraph-level coverage data |
| [mathematical_audit.md](mathematical_audit.md) | Detailed source, quantifier and resource checks |

`checks/` contains executable standard-library finite checks, derivations, actual stdout and independent arithmetic verification. `first_reading/` preserves reading-order and exercise-exposure records. `evidence/` contains custody, audit, patch, source-coverage and execution records. `manifest.json` inventories the response files and their hashes.

## Reproducing the new finite examples

From this response folder:

```bash
python3 checks/worked_trace/check_trace.py
python3 checks/changed_cases/check_changed_cases.py
```

The saved outputs record the executions performed during this review. These checks illustrate particular operations and changed assumptions. They do not replay Lean or prove the general PCP theorem. To inspect the proposed text changes, apply the patch only to a copy of the exact supplied packet as described in `patch_notes.md`.
