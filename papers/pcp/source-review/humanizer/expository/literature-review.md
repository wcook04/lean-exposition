# Exposition: teaching and source-grounding review

This is an AI editorial review of the frozen exposition, not evidence of human
learning. The audience remains a mathematically literate reader who knows
polynomial arithmetic, finite sums and elementary probability, but not
complexity theory, coding theory or Lean. No new prerequisite was introduced.

## Editions and inspected scope

The teaching comparison uses Sanjeev Arora and Boaz Barak's **January 2007 web
draft** of *Computational Complexity: A Modern Approach*, not the published
edition's numbering. The inspected passages are Chapter 18's opening and
Section 18.1 (printed draft pp.18.1–18.3, PDF pp.367–369), and Section 18.4.1
on Walsh–Hadamard encoding, local testing and local decoding (printed
pp.18.13–18.15, PDF pp.379–381). Definition 18.1 is the draft's PCP verifier
definition; Theorem 18.23 is its linearity-testing statement. Text extraction
was compared with source-page images for PDF pages 367, 368, 379, 380 and 381.
The source is retained at
work/pcp-sources/foundations/arora-barak-book.pdf and its adjacent .txt.

The mathematical source is Amireddy, Behera, Srinivasan, Sudan and
Willumsgaard, *A Simple Algebraic Proof of the PCP Theorem*,
version 2. I reread the abstract and introduction; the grid-certificate
passage in Section 2, Lemma 2.9 and Corollary 2.10; Section 3.1's digit
encoding and Claim 3.2; Section 3.2's weighted test and correction,
Lemmas 3.3–3.4; and Appendix B, Theorem B.1. The retained source files are
work/pcp-sources/core/source-v2/main.tex, intro.tex,
preliminaries.tex, technical_tools.tex, and
appendix_-_hadamard_test.tex. This research paper is a **qualitative**
comparison for the exposition: its specialist genre was not pooled into
the teaching-profile distribution.

The sharp linearity-testing credit was checked in Bellare, Coppersmith,
Håstad, Kiwi and Sudan, *Linearity Testing in Characteristic Two*,
Theorem 1.2, printed manuscript p.5 / PDF p.7. The source is
work/pcp-sources/algebra/bchks.pdf and its adjacent extraction.
The source-agent literature audit independently identified this attribution.
Version 2 Appendix B, Theorem B.1 cites both the original BLR paper and
BCHKS. The exposition now separates invention of the test from the sharp
distance-versus-rejection bound.

## Moves applied or deliberately retained

| Source location | Explanatory move | Decision in this exposition |
| --- | --- | --- |
| Arora–Barak, Chapter 18 opening, p.18.1 | Begin with a proposed solution and the operation for checking it before introducing PCP. | Keep the finite graph/colouring opening and K4 dilution calculation. Replace a theorem's “promise” with its existence statement in P001–P003. |
| Arora–Barak, Section 18.1, pp.18.2–18.3 | Define access to proof locations separately from the verifier's input and computational budget. | Retain the proof-bit/input distinction, explicit verifier and seed order, polynomial proof length, and exact theorem. |
| Arora–Barak, Section 18.4.1, p.18.13 | Define a code through the function it tabulates, then count its entries and explain distance. | Keep the eight-entry parity word and pairing proof. P072 now states the half-distance property directly. |
| Arora–Barak, Section 18.4.1, p.18.14 | Explain why local testing promises closeness rather than exact equality before the robust theorem. | Preserve the arbitrary-table and proximity warnings. No negative sentence carrying a failed implication was removed. |
| Arora–Barak, Section 18.4.1, pp.18.14–18.15 | Identify the chosen target as possibly corrupt, then randomize two query locations and use their marginal distributions. Its brief diagnosis starts “The problem is that”. | Keep the special-point warning, the zero-target case, and the deterministic-shift exercise. P081 names random self-correction and cites this teaching passage. |
| Version 2, Section 3.1 and Claim 3.2 | Work an exponent representation before the general encoding, then give the substitution that recovers an evaluation. | Preserve the complete base-three calculation, variable groups and substitution. Add the definition/claim locator to P061. |
| Version 2 introduction, “A new multivariate encoding” | Distinguish honest set-multilinear encodings from arbitrary low-degree tables that pass a weaker test. | Keep P062–P063, including the larger decoded degree bound. Replace only the metaphor of a proof “carrying” its bound. |
| Version 2, Lemma 2.9 / Corollary 2.10 | Give a polynomial identity that certifies vanishing, then combine the quotient polynomials into one certificate. | P042 and P044 state those operations literally and locate their source. All quotient/certificate degree arguments remain. |
| Version 2, Section 3.2 | State honest acceptance, robust testing and fixed-target correction separately. | Preserve all three contracts and their hypotheses. The new citation explicitly says the displayed bounds are the formal development's; it does not attribute the stronger formal field threshold to the paper. |
| BCHKS, Theorem 1.2; version 2, Appendix B Theorem B.1 | Attribute the exact quantitative input at its use. | P074 credits BLR's test; P076 credits BCHKS's sharp bound and identifies its use in version 2. |
| Version 2 abstract/introduction | State the verifier's two resource targets, then locate the operation that threatens them. | P056 begins with the coefficient count; P120 names proof length, randomness and queries rather than saying oversized tables would produce a “different theorem”. |

The book uses meaningful questions, negations and contrasts. Those features
were not treated as defects merely because a detector can count them. The
fixed-point obstruction, failure of the old test, homogeneous/full label
distinction, common witness and strict soundness boundary all remain.
Neither source is a template for the exposition's prose rhythm or voice.
The checked examples are this project's teaching examples, not examples
borrowed from the book or a claim of novelty in the theorem.

## Measurement regions and extraction limits

The numeric reference is **one edition of one teaching source**, represented
by 11 selected paragraphs (833 extracted prose words, 44 sentences). It covers
the PCP opening/access definition and Hadamard testing/correction, the same
operations as exposition paragraphs P001–P020 and P069–P081. It is not a
representative field corpus. The reference's zero IQR makes the profiler use
floors; its distance flags are not significance, authorship or quality scores.

The retained book extraction contains broken formula positioning and page
headers. The private measurement input replaces inline formulas with
LaTeX-delimited equivalents checked against the page images, omits displays,
headers, footnotes and captions, resolves the displayed equation reference
as “the identity”, and restores paragraph joins. Its literal wording is not
being proposed for publication. A source misprint in the two-codeword sentence
was reduced to the words “the encodings” for the measurement input. These
normalizations affect measured token counts slightly; source PDFs, not the
measurement input, remain the authority for quotation and mathematics.

The register extraction dump was inspected for both the book sample and final
exposition. Inline formulas become MATH; links contribute their visible prose.
The formula-rich full exposition is not a like-for-like paragraph-length
sample: its display continuations and lists are segmented differently from the
selected continuous book prose. Whole-document figures are context only.
The matched region is the more useful descriptive comparison, but it too
contains shorter worked calculations than the book. No change was made to
move a number toward the reference.

Source-page images, the normalized teaching extract, its preparation script
and its extraction dump stay outside the public repository. The public audit
may retain this source/locator discussion and the **metrics-only projection**.
It must not copy the third-party excerpts or source scans.
