# Bibliographic graph review

The four directly cited historical sources now have reference-only source records with exact retained-PDF SHA-256, edition and passage citations in `examples/pcp/evidence-graph.json`. They are attached using node `citation_ids`, the contract's direct citation mechanism, rather than fabricated Lean dependency or support edges:

- `citation:bchks` → `PCP.Algebraic.BLR.exists_linearMap_distance_le_of_rejection_le`: characteristic-two quantitative linearity antecedent, retained author manuscript Theorem 1.2 (printed p. 5).
- `citation:rubinfeld-sudan` → `PCP.Algebraic.WeightedConstraint.correction_satisfies`: robust-characterization antecedent, §4 Theorem 5 in the retained prepublication manuscript; published paper numbering cited as Theorem 4.1.
- `citation:kaufman-sudan` → the same weighted correction node: Theorem 2.9 for linear-invariant families having a two-ary independent local characterization; no claim that arbitrary weights satisfy its hypotheses.
- `citation:friedl-sudan` → `PCP.Algebraic.PolynomialLine.exists_polynomial_of_hasLowDegreeLines`: exact-line characterization antecedent, corrected arXiv 1307.3975v1 Lemma 4; the cited and Lean conditions differ.

These associations represent source attribution, not exact formal-statement identity, premise discharge, or mathematical review of a manuscript. The manuscript passages remain individually mapped by their authoring owners. No compiled dependency, support edge or Lean status was added. Copyright and redistribution permissions for these PDFs are not established here, so they remain reference-only with `NOASSERTION` license.

All four PDF hashes were independently recomputed and matched the retained source manifest. `lean-exposition validate` passed. Graph SHA-256 at this review: `b7d92ed2314221ece705e8f7dfe676869f22937d64aa1ca47cb425cbee651cb0`; extraction remains `not_run`, semantic certification false. The citations correspond to actual short-paper discussion and long/expository attributions as documented in `literature-grounding-audit.md`; citation presence alone does not validate the prose or prove each paper theorem is identical to its Lean counterpart.
