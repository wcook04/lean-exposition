# Final editorial polish, 15 November 2026

This pass addressed four suggestions in the user's latest returned assessment:
clarify the specialist account's purpose; connect the eight tables to the seven
checks and worked example; supply a proof map; and align the credits. The
assessment's praise and ratings were not adopted as evidence of expert approval.

The specialist abstract now identifies encoding, fixed-target correction and
soundness estimates as its explanatory focus, with the formal variant's resource
accounting kept distinct from the source paper. All three openings use the same
attribution to Will Cook's directed reconstruction, the original five authors
and Troy Lee's formalization. The long account adds a one-page map. The
exposition adds a table-use matrix beside the seven-check assembly. It marks
the worked trace as one branch with the inner-test queries omitted.

## Prose and preservation

The root editor wrote the manuscript changes. The humanizer and local register
methods were applied to the changed openings, figure captions and adjacent
explanations. The source preprint's introduction and local-correction opening
were reread: useful moves were to name the precise deliverable and then explain
the observations the verifier needs. Their wording was not copied. Earlier
genre-specific profiles were retained for descriptive before/after comparisons;
the `register-*.json` files are diagnostics, not quality or authorship scores.

The prior complete paragraph review remains applicable to the unchanged proof
text. This pass retained those paragraphs and reviewed the additions in their
reading context. No theorem, hypothesis, displayed formula, query cap, random
sampling rule or proof was changed. An independent source audit checked the
matrix against the pinned branch definitions and query lists, and checked the
map's selected uses. It found no mathematical issue. That audit did not run Lean.

The figure implementation and fidelity record are in
[figures](../../figures/README.md). The initial matrix render clipped row names;
an explicit first column repaired this before acceptance. The proof-map labels
were corrected to the account's equation numbers, rather than calling them
theorem numbers. The user then asked for edge semantics. Every proof-map arrow now names its
mathematical contribution, with standard terms retained in the humanizer pass.
Both repaired images and the final PDF pages were inspected.

## Evidence boundary

The pinned formal source and graph are unchanged. Existing source-read records
remain source-read records; the new source links for branch seeds, branch tests
and their conjunction do not claim elaboration, extracted proof dependencies,
axiom analysis or human expert acceptance. The latest render and check outcomes
are recorded in [validation.json](validation.json) and
[pdf-checks.json](pdf-checks.json). Earlier review directories describe their own
editions and remain unmodified.
