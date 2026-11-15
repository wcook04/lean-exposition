# Preservation and reader review of the revised PCP exposition

## Review boundary

This is a new review of the humanizer/literature-grounding revision. Earlier source and PDF acceptance does not cover this edition. The reviewer is an AI agent with prior PCP background and extensive exposure to the previous exposition, all its exercises and their answers, the fuller argument's relevant proof passages, and the earlier review. This is a preservation and assisted sequential editorial review, not a blind reader experiment or evidence of human learning.

Before snapshot: `work/pcp-humanizer/before/expository/main.md`, SHA-256 `2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`. Canonical manuscript review began only after the author explicitly froze it. No canonical file was edited by this reviewer. The new manuscript PDF is covered by a separate review below.

Method: mathematical reasoning and the repository's record-to-expository/reader-review contracts govern truth and sequence; the humanizer's Mathematical boundary governs prose-only cleanup. The latter prohibits changing claims, hypotheses, notation, authority and proof structure through a stylistic edit. Mechanical formula/marker checks are used to nominate differences, not certify mathematical equivalence. The complete revised text will be read sequentially after freeze, with the diff and relevant primary sources then used to diagnose changes.

## Literature evidence inspected before the revised manuscript

Read `work/pcp-humanizer/literature-grounding-audit.md` in full. This is inherited audit evidence, not an independent verification of everything it lists. Independently inspected:

- Downloaded v2 source `work/pcp-sources/core/source-v2/technical_tools.tex`, the standard low-degree theorem and following lineage paragraph (around lines 57–83). It explicitly identifies Rubinfeld–Sudan Theorem 4.1 as a proof antecedent and Kaufman–Sudan Theorem 2.9 as a general theorem. The displayed v2 lemma has its own characteristic-two/large-field hypotheses; a citation must not silently identify it with the stronger formal theorem's exact assumptions.
- `work/pcp-sources/core/source-v2/appendix_-_hadamard_test.tex`, the complete statement of the BLR linearity theorem and its use in the Hadamard argument. The source cites both BLR and BCHKS and states distance at most rejection for the Boolean linear functional. The retained PDF-page text `work/pcp-humanizer/source-checks/pcp-v2-49.txt` confirms those named citations in the published rendering.
- Retained BCHKS page text `work/pcp-humanizer/source-checks/bchks-7.txt`, Theorem 1.2 and context, giving the rejection-versus-distance bound by Fourier analysis. The extraction is typographically poor; the modern paper's explicit theorem supplies a directly readable cross-check of the exact attribution.
- `work/pcp-sources/algebra/kaufman-sudan.txt`, the beginning of Section 3 and its explanation that Theorem 2.9 concerns linear-invariant families with a 2-ary independent local formal characterization. It does not authorize arbitrary node/weight systems.
- `work/pcp-sources/algebra/friedl-sudan.txt`, Lemma 4, whose condition is q−q/p−1≥d and whose conclusion is the exact-line-to-total-degree characterization. The formalized q>2d argument is a different sufficient formulation, not a quotation of that lemma.
- `work/pcp-humanizer/expository/book-teaching-extract.md`, the retained teaching passages on PCP witnesses, Walsh–Hadamard encoding/distance and local correction. Checked the downloaded textbook text's January 2007 edition statement and Chapter 18/Section 18.4 entries. The excerpts exemplify framing an operation, an explicit obstruction to naive point reads and then the correction calculation; they do not validate the current exposition's teaching effectiveness.

## Frozen revised edition and sequential review

Author explicitly froze the canonical source at SHA-256 `4fc575eb9827c6253c457bcae3a55547a15f709efacbc3f65443cdf2c84fe303`; independently confirmed that digest and 1292 source lines before reading. The author supplied a protected-content summary, but it will be independently checked after the sequential pass. No revised text has yet been accepted.

### Sequential encounter: lines 1–270

Read the opening, Sections 1–3 and most of Section 4 in order. The exact PCP quantifiers, fixed-proof condition, two resource budgets, perfect completeness and soundness statements remain explicit. The K4 dilution calculation still supplies the reason to change certificate representation; the two obligations of coherent objects and colouring validity remain distinct. The NP converse has the same polynomial seed-enumeration calculation. Finite-field arithmetic, the distance input and interpolation are still introduced before their use.

The revised interpolation prose refers to the basis products, rather than suggesting the table-value summands must be nonzero. That is precise even when the selected table value is zero. The examples remain fully worked, with the invalid fourth colour still demonstrating why the vertex constraint is necessary. No first-use definition loss or unsupported new inference was encountered in this block. Knowledge available at the transition: the reader can evaluate/interpolate small field tables and encode graph constraints, but must still learn grid certificates, low-degree testing and bit access. No later section or source was needed to repair this part of the sequence.

### Sequential encounter: lines 271–540

Read the rest of Section 4, the full grid-certificate section, degree reduction, weighted testing/correction, and the beginning of the binary encoding. The substantive distinctions survive: grid vanishing versus ambient vanishing; both M identities; honest degree capacity versus arbitrary decoded degree; nonzero generator nodes; uniform correction marginals without an independence assumption; field queries versus bit queries. The previously repaired quotient bound and degree-M implication remain at their point of use. Question 1 remains separated from its answer.

New local source locators occur at the grid-decomposition lemma, its packaging corollary, the set-multilinear evaluation identity and the weighted-test subsection. They support specific operations rather than decorating the opening. The weighted-test passage explicitly attributes the displayed bounds to the formal development, so it does not identify the source paper's field-size hypothesis with the stronger formal statement. I will verify those numbered locators after the sequential pass. No new first-use stall or mathematical omission observed. The reader now has the actual correction operation needed for special grid-certificate points and knows why binary observations are next.

### Sequential encounter: lines 541–830

Read the BLR example/attribution, local correction, cubic labels, combined theorem and most of the seven-test soundness argument. The new citation distinguishes the BLR test from the BCHKS Fourier bound; the finite eight-point example remains this manuscript's calculation rather than an attributed historical example. The added textbook reference names the same two-query operation and its actual draft section.

The earlier substantive repair survives: one decoded polynomial serves both label families; both distances average over points and labels; the corrector may reject; its theorem is averaged over a homogeneous label and does not assume trustworthy line data or small rejection. The revised closing summary correctly retains the corrector's actual rejection rate as well as global closeness. The separate difference table is now explicitly identified with the decoded colour difference only under the soundness high-acceptance hypothesis. This is a useful clarification of scope rather than a stronger conclusion.

The complete quantitative contracts remain visible before the proof consumes them. The eight-table/seven-check inventory, honest-capacity guard, fresh correction and contrapositive are intact. The following error budget is still needed to discharge the qualitative phrases “very close” and “much greater”; the section now immediately supplies it, as in the accepted prior edition. No new inference gap identified in this block.

### Sequential encounter: lines 831–1060

Read the full difference/zero error budget, all production parameters, repetition and most of the NP reduction. The actual numerical contradiction and the complete factor multiplying the derived-read error are preserved. The same field still satisfies all three requirements; the honest and decoded degree bounds are kept separate. The explanation of the nonzero-sampling workaround still multiplies rejection, and amplification still quantifies over one fixed proof with independent seeds. The explicit OR-flag and three-clause construction remains, so the previous bounded-arity reduction gap has not reappeared.

The prose cuts do not remove the purpose of the resource calculation: it now states directly that polynomial proof length, logarithmic randomness and constant queries are simultaneous requirements. The warning that the enormous constants give no practical protocol is retained. No changed mathematical conclusion or new prerequisite gap observed.

### Sequential encounter: lines 1061–1292

Read the completion of the NAE reduction, Questions 4–5, every answer, the reconstruction task, the earlier low-degree-test counterexample and all source/verification disclosures. The hypothetical error budget retains the strict versus non-strict boundary: κ≤1/32 contradicts false grid vanishing, while κ≤1/16 permits equality and yields no conclusion. The GF16 arithmetic and 256-versus-16 count, unbounded-field family and separation of the old lemma's failure from the PCP theorem remain intact. The final disclosures still distinguish finite checks, ordinary mathematical deduction, formal proof and reader evidence.

All exercises and their answers were already known to this reviewer from the earlier round. This pass therefore verifies their preservation and placement; it supplies no new unaided exercise attempt. The full source was read in order before the complete diff was inspected. No source correction is requested.

## Independent preservation and source checks

Compared the complete before/after sources, not only the author's paragraph log. An independent ordered-sequence comparison found all 521 mathematical spans, 21 headings, 36 passage markers, 9 table rows and the sole inline revision-code token byte-identical and in the same order. All existing reference-link definitions are unchanged. The only added link definition is the BCHKS primary paper. Read the complete unified diff; after a tool-output truncation, separately reread its omitted middle portion. The sequential reading above checked quantifiers and scope carried in prose, which literal formula equality cannot certify.

The canonical finite-check scripts retain their previously inspected and successfully run hashes:

- `papers/pcp/expository/check_examples.py`: `743563475ac1fb850d79537fb89291a03980a182d80115a94169988be30ee118`.
- `papers/pcp/expository/check_exposition_examples.py`: `b1c375fa0c8ab21ed9f415cbe375ac449252bdeefc074094539925e6e8016cfe`.

Those unchanged scripts and preserved calculations did not require another run for this prose revision. This is reuse of recorded finite-check evidence, not a new test claim.

Checked the new numbered source locators against `work/pcp-sources/core/paper-v2.txt`: Lemma 2.9 states grid vanishing iff a sum of coordinate vanishing polynomials times bounded-degree quotients exists; Corollary 2.10 packages the quotients into M with degree at most deg P and the two stated identities; Claim 3.2 is the set-multilinear evaluation identity. Their uses in the revised exposition are accurate. The source's weighted-test field-size statement was checked separately above; the exposition correctly identifies its own displayed bounds with the formal development instead of attributing those exact bounds to the paper.

Checked the downloaded January 2007 Arora–Barak text at Section 18.4.1 (around lines 18210–18299): its local decoder chooses a uniform point and its translate and adds the two reported values. Both marginals are uniform, enabling the same union bound. The exposition cites the same operation rather than claiming the textbook has identical hypotheses. Checked BCHKS's title/authors and rejection/distance definitions as well as its Theorem 1.2 and the modern paper's Appendix B attribution. Distinguishing the original BLR test from the BCHKS quantitative bound is justified. No new literature claim found unsupported within this review's scope.

## Judgment and limits

Accepted this revision for mathematical preservation, source attribution and the specified reader sequence, conditional on the exact canonical SHA-256 `4fc575eb9827c6253c457bcae3a55547a15f709efacbc3f65443cdf2c84fe303`. Rechecked that hash after the full read and diff/source checks; the baseline remains `2e2333ca4727a5f8d510f5de8f184a4139f33122ae2d12ca3d29f2b9bec4d913`. No blocking or substantive nonblocking defect remains from this review.

The revision preserves the previously repaired route from high acceptance through one decoded polynomial, corrected special-point reads, the difference identity, both vanishing-certificate identities and a strict accumulated-error contradiction. A reader can reconstruct the constant-query soundness argument conditional on the clearly stated combined decoding and correction theorems. The exposition does not prove those deep theorems from elementary prerequisites, and this AI review does not establish that a human reader can reconstruct them or has learned the argument. It also does not independently replay Lean or certify prose from a Lean build.

The new PDF is a separate deliverable reviewed in `work/pcp-humanizer/exposition-pdf-review.md`; no previous PDF approval is inherited.
