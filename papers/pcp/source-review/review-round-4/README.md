# Third review round: writing refinement

This edition revises the wording, terminology, notation and structure of the three accounts. Its mathematical content is that of the previous edition, with the corrections listed below.

## What changed

Stated results are numbered and named in all three papers, and a result is stated before it is used. The full argument keeps its order, with the assembled verifier first: the lemmas the assembly relies on are stated there and proved later under the same numbers. Section titles name the mathematics. Each paper has one roadmap, and a closing section, "Formalization and sources", that says what the Lean development proves, where it differs from the paper of Amireddy, Behera, Srinivasan, Sudan and Willumsgaard, and whom each result is due to. Differences between Lee's formalization and that paper are stated in a remark directly after the result concerned.

Terms follow the cited literature: points tables and lines tables, the line through a point with a given slope, the low-degree extension, self-correction, local correction, the zero-on-grid test, the Schwartz–Zippel lemma, the set-multilinear encoding and the vanishing certificate. Four terms have no counterpart in that literature and are defined where they first appear: label, base point, nearby polynomial and half-distance identity. The field size is $q$ and the query bound $\ell$ in all three papers. The [decisions](decisions.md.txt) record every term and symbol with its source.

| Paper | Pages | Prose words |
| :-------------------- | :--------- | :--------------- |
| Full argument | 47, unchanged | 15,048 to 13,868 |
| Specialist paper | 13 to 12 | 4,333 to 3,722 |
| Worked exposition | 25 to 23 | 9,162 to 7,712 |

## Corrections to statements

Each of these was checked against the Lean source and the cited literature before adoption; the [ledger](math-flag-ledger.md.txt) has the evidence for all 42 reviewer proposals.

- The additive labels are the homogeneous linear labels, and the coordinate map is an $\mathbb F_2$-linear isomorphism; a zero constant term alone does not make a label additive.
- The lines tables use affine labels, constant term included, which is what the stated count $2^{t+1}$ already assumed.
- Completeness needs a positive digit radix and distinct nonzero interpolation and correction nodes, now stated before the completeness argument.
- The Markov step in the point-versus-line argument needs a positive radius.
- The reverse inclusion requires a polynomial-time implementation of the verifier; an edit in this round had dropped that hypothesis and the independent read restored it.
- A line polynomial of degree at most $d$ has $d+1$ coefficients.
- The exposition's reconstruction exercise now states the soundness assumptions its solution uses.
- The threshold $1/28$ and the factor $28$ in the Hadamard test, the field-size condition $q>2c$, sampling the line parameter from the whole field, the fair coin in the inner low-degree test and independent seeds for the two corrector calls are Lee's choices; such results are now cited as "cf." with the difference stated.
- The plurality correction is cited to Kaufman and Sudan, Lemma 3.1.

## How the revision was made and checked

Five outside reviews were received, two for the full argument, one for the specialist paper and two for the exposition ([intake](intake.json); the reviews are under [returned/](returned/)). The second review of the specialist paper did not arrive, and its checks of statements, credit and citations were made during integration.

Every reviewer proposal that could change a statement was checked against the Lean source and the cited papers. Each revised paper was then read front to back by a reader who had not edited it, against the previous edition, the Lean declarations and the sources ([full argument, assembly](long/independent-read-1.md.txt); [full argument, proofs](long/independent-read-2.md.txt); [specialist paper](short/independent-read.md.txt); [exposition](expository/independent-read.md.txt)). The [literature comparison](literature-conventions.md.txt) and the [comparison with the QAOA/SK papers](companion-set-conventions.md.txt) informed the structure.

Every passage marker, equation label, reference and link of the previous edition is present. Each displayed equation of the previous edition equals one of this edition under the recorded symbol renames. All 113 passage-to-Lean associations were [re-checked](passage-association-check.md.txt) against the revised text; twelve were corrected, four of which were already imprecise in the previous edition, and two reading links were retargeted. The [validation receipt](validation.json) records hashes and the checks run.

The reviews, the checks and the independent reads were made by AI models under Will Cook's direction. Lean declarations were read in this round and not compiled; the Comparator result for the three headline statements belongs to the reader edition and is unaffected by prose changes. Troy Lee has not reviewed these papers.
