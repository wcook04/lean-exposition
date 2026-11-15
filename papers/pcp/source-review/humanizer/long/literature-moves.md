# Literature grounding in the long account

This records point-of-use changes made during the long manuscript's register and humanizer pass. The primary passages were read from retained source files, with page images used where extraction damaged mathematical text. The resulting manuscript wording is original explanatory prose. This record includes no verbatim primary-source excerpts; third-party PDFs, source files, extracted passages and scans stay in the private working annex.

## Corrected PCP source

The operative primary paper is ABSSW, arXiv:2608.17429v2, 22 October 2026. Relevant rereads included `technical_tools.tex` lines 1–145 (Fact 2.7 and Section 3.2, Lemma 3.3 and its attribution), `low_degree_test.tex` lines 1–110, and `appendix_-_hadamard_test.tex` lines 1–90 (Appendix B, Theorem B.1). These are retained under `work/pcp-sources/core/source-v2/`. The manuscript preserves the generator and Lagrange-weight formulation and distinguishes the pinned Lean constants, table distributions and implementations from v2. Historical v1 is used only for the earlier unit-weight test and its failure analysis. The source-version note continues to decline an identification of public v2 with an uninspected final proceedings edition.

## Exact polynomiality from lines

Friedl–Sudan, *Some Improvements to Total Degree Tests*, corrected arXiv:1307.3975v1 (2013), Lemma 4, p. 2, is the exact-line antecedent. The source's condition is `q − q/p − 1 ≥ d`, with `p` the characteristic. The manuscript now states this beside the direct argument under `q > 2d` used in the pinned development. It does not attribute that stronger sufficient hypothesis to the classical statement or replace the reconstructed proof with a citation. Sections 2–3 of the native TeX, lines 1115–1633 of the retained decompressed source, were also read for the extended proof register. Source: `work/pcp-sources/algebra/friedl-sudan.pdf` and `friedl-sudan-source.tar` (a gzip-compressed single TeX file despite its suffix).

## Weighted constraints and plurality

Rubinfeld–Sudan, *Robust Characterizations of Polynomials with Applications to Program Testing*, retained manuscript Section 4, Theorem 5 and Lemmas 6–8, pp. 10–12, supplies the plurality, affine interpolation and pair-uniformity antecedent. The manuscript now identifies those steps after its complete weighted proof. The primary PCP paper cites the published SIAM Journal on Computing result as Theorem 4.1; the differing numbering is disclosed rather than silently transferred. Source: `work/pcp-sources/algebra/rubinfeld-sudan.pdf`; pp. 10–12 were read as rendered images because extraction was damaged. The published bibliography metadata was checked against v2's `references.bib` entry.

Kaufman–Sudan, *Algebraic Property Testing: The Role of Invariance*, conference manuscript Theorem 2.9, p. 5, is a broader antecedent. The new sentence preserves its requirement of a 2-ary independent local formal characterization. It does not claim that an arbitrary weighted constraint meets those hypotheses. Source: `work/pcp-sources/algebra/kaufman-sudan.pdf`.

## Bivariate agreement and point-versus-line testing

ALMSS, *Proof Verification and the Hardness of Approximation Problems*, author-hosted journal manuscript, Theorem 69 and Corollary 70 in Appendix A (retained PDF pp. 48–49), was reread at the bivariate statement and crossing argument. The prose now distinguishes nearest row/column approximants and implicit constants in Theorem 69 from the arbitrary approximants and explicit `q ≥ 1000 d³`, `ε ≤ 1/100` formulation reconstructed here. The proof sequence is identified through Lemma 66, Theorem 69, Corollary 70 and Lemmas 71–73. The fixed-parameter tie choices and candidate-row variant remain explicit formalization-specific adaptations. Source: `work/pcp-sources/foundations/almss-journal.pdf`.

Arora–Safra, *Probabilistic Checking of Proofs: A New Characterization of NP*, journal-format copy, Section 5.2, especially Lemmas 5.2.2, 5.2.5, 5.2.7 and Corollary 5.2.3, supplies the error-locator, interpolation and rectangle antecedents. The relevant extended argument was reread, including the rendered page numbered 110. The manuscript now explains the purpose of the locator before constructing it and cites the specific antecedents at that construction. The proof's kernel, determinant, degree and common-rectangle deductions remain intact. Source: `work/pcp-sources/foundations/arora-safra-jacm.pdf`.

## Binary linearity testing

Blum–Luby–Rubinfeld, *Self-Testing/Correcting with Applications to Numerical Problems*, retained author manuscript Section 4.2, is cited for the three-query test. Bellare–Coppersmith–Håstad–Kiwi–Sudan, *Linearity Testing in Characteristic Two*, retained author manuscript Theorem 1.2 and Section 2, is cited for the sharp characteristic-two Fourier bound. The prose now distinguishes these roles at the bound's statement. The orthogonality, Parseval and cubic-moment proof remains written out. ABSSW v2 Appendix B, Theorem B.1, confirms the corresponding use in the PCP paper. Sources: `work/pcp-sources/foundations/blr-author.pdf`, `work/pcp-sources/algebra/bchks.pdf`, and the v2 appendix above.

## Finite-field construction and runtime

Shoup, *A Computational Introduction to Number Theory and Algebra*, first electronic edition, Version 1, 15 January 2005, Section 20.2, Theorem 20.11, and Section 21.1, supplies finite-field existence and irreducibility/field-construction background. Those passages were reread. The new comparison expressly separates the randomized textbook construction from the pinned formalization's deterministic bounded search and explicit costs. No particular Lean cost estimate is attributed to the textbook. Source: `work/pcp-sources/algebra/shoup-2005.pdf`.

## Register corpus and extraction quality

The numerical reference corpus uses two independent works and one edition per work: the native TeX proof regions of ABSSW v2 and Friedl–Sudan's corrected source. Introductions, bibliographies and historical text within disabled TeX `remove` macros were excluded. ALMSS, Arora–Safra and Shoup were used for qualitative proof and prose comparison but excluded from numerical paragraph comparisons because their PDF extraction damaged formulas or paragraph boundaries. This is a small, genre-matched diagnostic corpus, not a statistical quality test or an authorship detector. The private extraction evidence and exact region manifest are retained. The public metrics projection includes numbers only.
