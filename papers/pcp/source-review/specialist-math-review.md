# Independent specialist PCP paper review

Reviewed `work/lean-exposition/papers/pcp/short/paper.md` at SHA-256 `75e21f6017db44f4bd699b3542eb6fb86e181cd92278468e8645ab83011144a6`, against the long chapters and selected pinned Lean statements. Reviewed algebra revision `5d22ab32ab81f127bb8e13a63d746948cb894f6f294f8fabee1198598c08c093` separately; its prior crossing-hypothesis finding is resolved. `PCP/Algebraic` in the local checkout is unchanged relative to pinned commit a0ce13ed0fa264f051c1278e039596ce65557fa4. This is not a build, complete check of all formal dependencies, or a review of uninspected edits to the specialist manuscript after that hash.

## Actionable finding

**Label domain inconsistent in (8).** `pcp-short-hadamard-encoding` defines homogeneous linear labels as $L:F\to\mathbb F_2$, but (8) evaluates $L(\rho(A(u)))$, whose argument lies in $\mathbb F_2^t$. This does not type-check. Choose one convention: either define binary-coordinate labels $L:\mathbb F_2^t\to\mathbb F_2$ and express multiplication relabeling as $L\circ\rho\circ(\eta\cdot)\circ\rho^{-1}$; or keep field-domain labels and write $L(A(u))$ in (8), using the corresponding binary-coordinate expression only to define $\Lambda_{A,L}$. Match that choice in the difference check (17) and the weighted statements. The source `HadamardComposition.lean` composes through the isomorphism and `HadamardWeights.lean` proves the induced permutation. Author and parent notified.

## Checked claims

- The PCP theorem has the right quantifier order, fixed proof before seed, polynomial address bound, and converse finite-witness argument. Three-colour vertex and edge constraints both matter; the F4/K4 example and degree bounds are valid.
- Honest set-multilinear encoding and general decoded degree≤cb^c are distinct; old unit-weight counterexample is confined to the v1 scalar test and not represented as a full cheating proof or a new formal theorem. Corrected version and credit are identified.
- Exact half distance, same witness for full and homogeneous distances, fair-coin factor, row-decoding constants K,J,S and restriction caveat are consistent with the reviewed binary argument. Fixed-target local correction averages over its requested label; (14) includes rejection as failure.
- ZERO coupling preserves shared-label dependence and multiplies the fresh derived-read error by 1+2C. In assembly a single chosen polynomial per table is retained; support and label half-distance yield (18), and the use of 5D in (19) is a valid common bound.
- For c=4, K=105408, J=1054138, S=1054166, C=1054082 and T=4444715947277. Equation (20) gives g=1/71115455156448, so the fair-bit nonzero filter factor 1/16 yields exactly 1/1137847282503168, as stated. The resource bounds and 187 reads match `ThreeColorBinaryVerifier.lean:85–100, 253–258` and the long argument; equal table query budgets include derived reads.
- Full versus homogeneous label distinction and whole-field outer sampling are explicit. Bivariate and ruled-surface mechanisms are summarized with a linked long proof rather than presented as an unexplained standard inference. The formal correspondence names the independent implementation and attribution, with no claim of a new theorem.

## Scope

This review did not replay Lean, validate the complete machine simulation, inspect every source theorem or the final publication rendering, or assert mathematical consensus/novelty. Its source-specific observations are limited to the cited constants and theorem interfaces and the long proofs independently reviewed in this task. Recheck the final author's hash after edits.

## Final revision recheck

Rechecked `paper.md` at SHA-256 `72d165920fbc02aa7b58bc626c3e6899cd2f099089a80cb10efa792279127577`. The label domain and (8) are now type-consistent, and the weighted and difference-check notation follows the same field-domain convention. The v1 example now explicitly specifies m≥1 and the agreement fraction on F^m. The newly linked `ReferenceNP.inNP_iff_mem` statement was inspected and matches the claimed class equivalence; its file also matches the pinned tracked version. The previously identified issue is resolved, with no remaining real error identified in the reviewed transitions. This acceptance is limited to the source and mathematical review described above; it is not a Lean build, exhaustive proof audit, or rendered-output review.
