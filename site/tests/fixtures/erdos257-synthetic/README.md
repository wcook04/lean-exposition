# Synthetic Erdős #257 fixture

A small made-up edition for the site's unit tests. It exercises the fields the
`erdos257` instance adds, before the real #257 data exists: `fidelity`,
`fidelity_note` and `fidelity_source` on Lean rows, `origin` on statements and
ties, GitHub Actions run receipts (passed, failed, cancelled), Comparator replay
receipts listed by an index (more than the table shows one by one, one of them
failed), a generic Comparator receipt, and an exposition with an image figure.

Every identifier, name and number here is invented for the tests. None of it is
a claim about Erdős problem #257. The shapes are those documented in
`site/src/instances/erdos257/README.md`.

- `example/` stands where `examples/erdos257/` will: the graph and its receipts.
- `edition/` stands where `site/public/edition/` will: `index.json` and the
  responses the build reads (`/ties/<paper>`, `/alignment`, `/overview`).
- `papers/expository/main.md` and `papers/expository/figures/` stand where
  `papers/erdos257/expository/` will.
