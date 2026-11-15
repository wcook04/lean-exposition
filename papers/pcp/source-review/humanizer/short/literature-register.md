# Specialist-paper language and literature review

The target is a self-contained specialist account for complexity theorists. The reader should be able to reconstruct the encoding strategy, follow the common decoding argument, and locate every longer proof. This review changes prose and source attribution, not the theorem or its proof.

Baseline: `72d165920fbc02aa7b58bc626c3e6899cd2f099089a80cb10efa792279127577`.
Revised manuscript: `c1f177680bbe01f2e4b7bdee82cd9fedf276cecb9ae0f258a2b6e5fe3115c377`.

## Method and boundaries

Applied the host humanizer's mathematical boundary and literal-language rules, the avoid-ai-writing editing contract and full pattern catalogue, and the repository's register skill and all 26 short-paper rules. The full-paper formal-exposition references were already read during authoring: `the-deliverable.md`, `mathematical-writing-mechanics.md`, and `full-exposition-guide.md`. Mathematical reasoning remained the authority for truth and hypotheses; the language skills supplied no authority to weaken them.

The protected objects were the theorem's quantifier order, all displayed and inline formulas, degree and field conditions, query counts, sampling domains, error events, common decoded witnesses, attribution, formal-versus-ordinary evidence, headings, passage identifiers and existing links. The user explicitly authorized better literature grounding, so four references were added at actual uses. This authorization does not make the literature's numerical constants interchangeable with those in Lee's formalized variant.

Every one of the original 81 prose blocks received a purpose, attention item and keep/change decision before the first edit; see `paragraph-decisions-before-edits.json`. After the first prose pass, a corrective pass restored a proximity qualification and retained the original qualification about impractical numerical bounds. Subsequent parent/reviewer corrections were limited to exact source attribution: Friedl–Sudan's sufficient field hypothesis, the formalized variant of ALMSS's line test, and the unrestricted BLR conclusion as stated in v2 Theorem B.1. The final log has 23 changed blocks, including the bibliography, and 58 retained blocks. There was no minimum edit target.

## Genre-matched reference corpus

The numerical profile uses one full edition per work, all research papers proving algebraic PCP results:

| Work | Edition and retained input | Role |
| --- | --- | --- |
| Amireddy, Behera, Srinivasan, Sudan, Willumsgaard | arXiv:2608.17429v2, 22 October 2026; TeX inputs expanded in source order into `reference-text/amireddy-et-al-v2.tex` | The proof being explained; encodings, nonuniform correction, complete verifier |
| Arora–Safra | JACM 45(1), 1998; `work/pcp-sources/foundations/arora-safra-jacm.txt` | Earlier algebraic PCP proof and bivariate agreement construction |
| Arora–Lund–Motwani–Sudan–Szegedy | Author-hosted journal manuscript, JACM 45(3), 1998; `work/pcp-sources/foundations/almss-journal.txt` | Constant-query theorem and point-versus-line test |

The full-text corpus is used for a descriptive whole-document profile, not as a single target distribution for every passage. The specialist paper includes a short formal-correspondence paragraph; the older papers contain longer introductions, appendices and bibliographies. There is no claim of a perfectly matched theorem/proof-region numerical experiment. Actual proof passages, identified below, govern the editorial comparison.

Representative extraction was inspected against the retained text. The expanded v2 TeX preserves ordinary paragraph boundaries. The ALMSS extractor splits several physical abstract lines into separate apparent paragraphs, and both historical PDFs contain formula and pagination debris. Consequently, paragraph lengths, paragraph-end rates, abstract length against the corpus, and sentence rhythm against the corpus are unavailable as reliable comparative evidence. The unmodified profiler outputs are retained to expose those defects, not to conceal them. BCHKS and Rubinfeld–Sudan were excluded from the numerical corpus because their extraction has more severe character damage. They were read for the mathematics and prose moves below.

## Inspected passages and transferable moves

The short quotations in this table are specimens of moves, not prose copied into the manuscript. Total quotation from each work is below 25 words.

| Move | Actual source and specimen | Decision for this paper |
| --- | --- | --- |
| Abstract announces the mathematical result | ALMSS abstract opens “We show”; v2 abstract opens “We give” and then states the graph-colouring resources | Keep all verifier resources first. Remove the repeated sentence announcing that this account is an explanatory reconstruction; the abstract's verb and credits already say so. |
| Introduction identifies the field's question | Arora–Safra §1 begins “Problems involving combinatorial optimization”; v2 §1 proceeds from the simplification question to precise randomness and query costs | Keep the theorem before history, then identify the cost of a field-valued query. No generic survey opening was added. |
| State the result's quantifiers before discussing its mechanism | ALMSS abstract says “there exists a proof” and distinguishes yes- and no-instances | Retain the entire theorem and common quantifier-order paragraph verbatim. |
| Credit the precise predecessor | ALMSS abstract says “Our result builds upon” and explicitly says Arora–Safra has a nonconstant query bound | Attribute the constant-query theorem to ALMSS, building on Arora–Safra. The former wording grouped both without this distinction. |
| Narrate proof choices as mathematical choices | Rubinfeld–Sudan prepublication §4, pp. 10–11, begins its plurality construction “We define”; ALMSS Appendix A defines nearest line polynomials before using their common correction | Replace the claim that tests choose polynomials by an explicit application of (13), followed by fixed choices. Preserve the distinction between analytical decoding and the verifier's executable operations. |
| Introduce notation through the object it describes | Arora–Safra §5.2 says “For clarity” before arranging values as a matrix; v2 §3.1 defines the digit substitution and immediately evaluates it | Retain the digit formulas and their direct substitution calculation. Cite Definition 3.1 and Claim 3.2 beside them. |
| Organize around the operations needed later | v2 §3 is “Two Encodings”; ALMSS §7.2 joins “Testing and correcting” | Preserve the existing mathematical headings and the progression from encoding to testing, correction and assembly. No process-status headings were added. |
| State a limitation at the step it affects | v2 §1's multivariate-encoding discussion says the “degree guarantee is weaker” and explains why the larger decoded degree suffices | Keep the honest degree below the capacity separate from the larger decoded degree, and make the field-size consequence explicit. |
| Report implementation without interrupting the proof | v2 §1 reports that the constructions were “implemented in Python” and credits Lee's Lean proof; its abstract locates the pseudocode | Keep one formal-correspondence paragraph at the end, with normal mathematical links. Retain exact implementation variants beside the affected arguments. |
| Permit useful parenthetical qualifications and ordinary mathematical agency | ALMSS Definition 68 says “we pick one arbitrarily” when nearest row polynomials tie; Kaufman–Sudan §3 starts its notation reduction with “We start” | Use “we” only for proof choices and calculations. Keep tie-breaking, arbitrary advice, fixed-witness and nonuniformity qualifications. Do not manufacture variation to resemble a metric. |

The present pass reread v2's abstract and introduction, §3.1's set-multilinear construction, §3.2's weighted test and its antecedent paragraph, the Hadamard characterization and Appendix B Theorem B.1. The complete relevant v2 proof and all three reconstructed long chapters had been read during original authoring. The current historical-paper comparison read AS's opening and §5.2, especially Lemmas 5.2.1–5.2.2 and the interpolation setup; ALMSS's opening, §7.2 with Theorem 45, and Appendix A around Theorem 69 and the final proof of Theorem 65. These passages expose proof operations, not merely publication titles.

## Added citations and their exact functions

- **BCHKS, Theorem 1.2.** Retained author manuscript `work/pcp-sources/algebra/bchks.pdf`; text around the characteristic-two theorem and its Fourier proof was read. Its stated rejection-versus-distance theorem is formulated for distance at most one half. The specialist passage therefore cites both this antecedent and the unrestricted linear-functional conclusion exactly as stated in v2 Appendix B, Theorem B.1. BLR remains credited for the test. The manuscript's bound is unchanged.
- **Rubinfeld–Sudan, §4.** The retained prepublication PDF is `work/pcp-sources/algebra/rubinfeld-sudan.pdf`. Its original extraction is unreadable. Pages 8–11 were rasterized and OCR-read locally; pp. 10–11 contain Theorem 5, plurality correction, the distance argument and the comparison of predictions. The linked edition numbers the robust-characterization theorem as Theorem 5; v2 §3.2 cites Theorem 4.1 of the published paper. The bibliography makes that edition difference explicit. The old result's prime-field interpolation setting is not passed off as the present generator-based theorem over extension fields.
- **Kaufman–Sudan, Theorem 2.9.** Retained conference manuscript `work/pcp-sources/algebra/kaufman-sudan.pdf`; Definition 2.5, Theorem 2.9 and §3 were inspected. The cited generality is a linear-invariant family with a two-ary independent local characterization. Its rejection threshold is not substituted for the explicit weighted bound used in this paper. The citation identifies the general testability method, as v2 §3.2 does.
- **Friedl–Sudan, Lemma 4.** Retained corrected arXiv:1307.3975v1 manuscript `work/pcp-sources/algebra/friedl-sudan.pdf`. The lemma assumes the exact finite-field condition involving the order and characteristic; the specialist text explicitly describes its own field hypothesis as a stronger sufficient one. This is the conversion from exact degree bounds on every line to a total-degree bound, not an attribution of the weighted test to that lemma.

Other new source locators point to definitions and lemmas already used: v2 Lemma 2.9 for grid vanishing, Definitions 3.1 and 3.5–3.6 for the encodings, Claim 3.2 for recovery, and §1 for the precise sense in which composition is avoided. ALMSS Theorem 45 is identified as the source line test, with the quantitative and oriented-line statement explicitly described as Lee's formalized variant. The source manifests retain URLs, editions and PDF hashes.

## Measurements and decisions

Commands and complete outputs are in `prepare_profile.py`, `profile.json`, `before-profile.{json,txt}` and `after-profile.{json,txt}`. The after comparison uses the original paper as its explicit baseline. The profiler counted 3,566 versus 3,616 prose words; the increase is principally attribution at the mathematical uses. The abstract decreased from 138 to 122 counted words. Nominalization flags fell from 70.4 to 69.1 per thousand words, intensifier flags from 2.52 to 2.21, and negation flags from 6.45 to 5.81. Conversely, the triad rate rose from 3.37 to 3.87, and the nominal AI-lexicon rate rose from 0.28 to 0.55 when the legitimate robust-characterization terminology was added. These are descriptive lexical measurements, not authorship probabilities or readability scores.

The triad flags include the theorem's resource tuple, shared quantifier statement and the three tested errors in (12); those lists do mathematical work and were retained. Negations distinguishing full-label from homogeneous-label proximity, an arbitrary auxiliary table from an honest one, and average error from a fixed target remain. The semicolons joining a root-bound example or a degree comparison remain where they express the logical relation. No punctuation, sentence-length or vocabulary quota was pursued. Source papers themselves contain promotional and stock phrasing; the review transfers their mathematical exposition moves, not every stylistic habit.

The general rule that helped most was to identify the actor and operation in a soundness proof without attributing an existential decoding computation to the verifier. The strongest limit on a generic humanizer was the need to retain technical vocabulary and logically essential contrasts. This local pass supplies no new cross-field evidence for changing the register rules.

## Preservation and delivery boundary

`preservation-checks.json` records exact equality of all 38 display blocks, all 275 inline-math spans in order, the 14 paired passage IDs, headings, main theorem and quantifier text, existing links and six Lean link definitions. The quote normalizer ran on changed prose only and made no change needed in the manuscript; see `marks-check.json`. The avoid-ai-writing validator passed mechanical preservation, with numerical warnings caused by citation-number changes and four new bibliography entries. Those warnings are reviewed source additions, not changed mathematical constants.

The full revised source was read sequentially after editing; see `sequential-review.md`. Independent mathematical preservation was accepted by the foundations reviewer at the revised hash. That acceptance is distinct from this author's checks. The parent owns the rendered-paper inspection, map rebinding and publication; none is claimed completed by this language pass. No Lean theorem was edited or newly compiled here.
