# From the Parisi value to one ordinary QAOA word

The manuscript **QAOA attains the SK ground-state energy in the thermodynamic-first limit**, credited to OpenAI, states and supplies an ordinary mathematical proof of
\[
\lim_{p\to\infty}\sup_{\gamma,\beta\in\mathbb R^p}
\lim_{n\to\infty}\frac1n
\mathbb E_J\langle\psi_{n,p,J}(\gamma,\beta),C_{n,J}\psi_{n,p,J}(\gamma,\beta)\rangle
=P_*.
\]
Its construction first obtains a finite classical formula near the Parisi value, compiles that formula using a Gaussian longitudinal field, and removes that field to obtain one finite cost–mixer word. The selected public Lean interfaces cover the zero-temperature support and scalar-value inputs. They do not state the circuit convergence theorem. This note reconstructs the source argument and its interfaces; it reports no new Lean replay, Comparator result, or independent mathematical acceptance. [Main theorem and scope][intro-model] [Public formalization scope][scope]

All manuscript and Lean links below refer to **openai/math at revision adc7f1241b42e322a6451854ab7e4b4c146bf78a**. Line numbers refer to that edition's source. The manuscript's title, attribution, abstract, and input order are in [main.tex, lines 51–100][main]. The regular-MaxCut proof is Section 7 even though its filename begins with 08; the positive-temperature construction is Appendix A even though its filename begins with 07.

## 1. The exact statement and its quantifiers

For independent standard real Gaussians \(J_{ij}\), the manuscript uses
\[
h_{n,J}(\sigma)=n^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j,\qquad
C_{n,J}=n^{-1/2}\sum_{i<j}J_{ij}Z_iZ_j,\qquad B_n=\sum_iX_i.
\]
Here \(P_*=\lim_n n^{-1}\mathbb E_J\max_\sigma h_{n,J}(\sigma)\) is the **positive maximum** convention for the SK ground-state constant. The cost gate is \(e^{-i\gamma_j C_{n,J}}\), the mixer gate is \(e^{-i\beta_jB_n}\), and the initial state is \(|+\rangle^{\otimes n}\). The limiting value \(v_p(\gamma,\beta)\) averages disorder as well as the quantum energy expectation; \(Q_p\) is the supremum of those fixed-angle limits. [Section 1.1, labels `eq:sk-model`–`eq:qaoa-value`][intro-model]

Theorem `thm:main` has the equivalent existential form
\[
\forall\varepsilon>0\quad
\exists p\ge1\quad
\exists\gamma,\beta\in\mathbb R^p\quad
v_p(\gamma,\beta)\ge P_*-\varepsilon,
\]
where the same deterministic angles work for the entire sequence of system sizes and are independent of the realization of \(J\). The choices may depend on \(\varepsilon\). The circuit length, signs, and sizes of the angles are unrestricted except for finiteness. Negative and zero angles are allowed.

The order of the displayed operations matters:

- \(n\to\infty\) occurs at each fixed \(p,\gamma,\beta\).
- The supremum is taken over these limiting values. It is not an asserted interchange between a supremum and the system-size limit.
- The subsequent \(p\to\infty\) follows from the existence of good finite words at every accuracy, together with \(Q_{p+1}\ge Q_p\) by zero-angle padding and \(Q_p\le P_*\) by measurement in the computational basis.

No maximizer of the angle supremum is required. No single finite word is asserted to attain \(P_*\) exactly. The theorem supplies neither a quantitative \(p(\varepsilon)\), a finite-size rate, nor an efficient method for finding the angles. It states expected energy, rather than a per-instance or single-measurement guarantee. The introduction explicitly distinguishes its quantifiers from fixed-instance optimality as depth increases. [Section 1, lines 34–43 and 111–133][intro-order]

The first- and second-moment theorem of Farhi–Goldstone–Gutmann–Zhou,
[arXiv:1910.08187v4, §4, (13)–(22)](https://arxiv.org/abs/1910.08187v4),
uses the same negative-exponential gate convention and permits arbitrary real
angles. For each fixed word it supplies joint disorder-and-measurement
\(L^2\) concentration about its limiting value. Combined with a word
chosen at accuracy \(\varepsilon/2\), this gives one sampled output
above \(P_*-\varepsilon\) with joint probability tending to one.
This is an additional ordinary consequence, not a clause of the main
source theorem or selected formal interfaces. The two variance terms,
typical-instance meaning and nonconstructive padded diagonal are proved
in the [long record, §§11.2–11.3](../long/reasoning-record.md#fixed-word-probability).

The tree degree \(D+1\) is a separate auxiliary parameter. For a **fixed ordinary word** \(W\), Proposition `prop:tree-transfer` imports the identity
\[
v_W=\lim_{D\to\infty}\frac{\sqrt D}{2}
\langle W_D\Omega,Z_iZ_jW_D\Omega\rangle
\]
for the tree cost \(D^{-1/2}\sum_{\{i,j\}}Z_iZ_j\). It attributes this to Basso–Farhi–Marwaha–Villalonga–Zhou, with a bipartition conjugation accounting for the tree-cost sign. This is an equality between two separately defined fixed-word limits. It is not a joint \(n,D,p\) limit and does not extend the cited SK transfer to temporary seeded or controlled gates. [Section 2, `prop:tree-transfer` and its proof][tree-transfer]

## 2. The argument's dependency structure

The following table lists consumers and their prerequisites. These are mathematical support relations in the manuscript, not extracted Lean dependency edges.

| Consumer | Required input and output | Source status and exact locator |
| --- | --- | --- |
| Theorem `thm:main` | A finite ordinary word with energy within \(\varepsilon\) of \(P_*\); fixed-word tree-to-SK transfer; upper bound and padding monotonicity | Manuscript assembly: [Section 6, lines 7–34][assembly]; external transfer: [Section 2, lines 17–45][tree-transfer] |
| Theorem `thm:seed-simulation` | One already fixed finite seeded word; construction of ordinary cost–mixer words approaching its rooted energy | Manuscript theorem and proof: [Section 5, lines 10–48][seed-theorem], [lines 976–1006][seed-finish] |
| Theorem `thm:classical-synthesis` | Bounded odd seed-only formulas with receiver and ancestor exclusions and fixed positive helper probabilities; insertion approximation off helpers | Manuscript theorem: [Section 4, lines 38–79][synthesis-theorem]; proof: [lines 1012–1119][synthesis-order] |
| Proposition `prop:classical-near-optimum` | A near-optimal finite scalar Gaussian formula, bounded trigonometric approximation, and small-cost type exclusion | Manuscript proposition and parameter choices: [Section 3, lines 553–608][classical-finish] |
| Lemma `lem:gaussian-rooted-realization` | Exact independent Gaussian law, predictable normalized columns, and the rooted first-chaos formula | Manuscript construction: [Section 3, lines 123–218][rooted-realization] |
| Scalar coefficient and value inputs | A fixed admissible minimizer, its diffusion, full contact/moment identities, curvature value formula, and fixed-\(T\) coefficient convergence | Imported companion results stated in [Section 3, lines 15–121][scalar-input]; scalar formal interface discussed below |
| Rooted energy and replacement calculus | Common occupation embeddings; strong convergence with occupation bounds; controlled-gate and adjoint convergence in fixed contexts | Manuscript proofs: [Section 2, `prop:energy`][energy], [`thm:gate-calculus`][gate-calculus], [`cor:additive-response`][additive-response] |
| Alternative classical proposition | Positive-temperature Parisi/support facts, finite-step tree analysis, strong realization, and clipping | Imported inputs and manuscript deductions in [Appendix A][positive-input], ending in [`prop:classical-near-optimum-positive-temperature`][positive-finish] |
| Regular-MaxCut corollary | Main theorem and fixed-word transfer; local tree cones; short-cycle and random-regular optimum theorems | [Section 1.3 statement][maxcut-statement]; [Section 7 proof][maxcut-proof] |

A full-support statement is not by itself an algorithm or a circuit theorem. Its role is to make the scalar self-consistency identities hold over the full time interval below one. The value and coefficient identities then identify a finite classical target with the correct energy. The quantum conclusions require the remaining constructions in Sections 2–5.

## 3. The primary scalar route: the same minimizer, diffusion, and coefficients

### From variational support to a numerical target

Section 3 fixes one nonnegative, nondecreasing, right-continuous, integrable coefficient \(\gamma:[0,1)\to[0,\infty)\) minimizing
\[
\mathcal P(\gamma)=\Phi_\gamma(0,0)-\tfrac12\int_0^1t\gamma(t)\,dt,
\qquad
\Phi_t=-\tfrac12(\Phi_{xx}+\gamma\Phi_x^2),\quad \Phi(1,x)=|x|.
\]
The minimizer hypothesis is substantive: arbitrary admissible coefficients do not supply the contact identities. The manuscript invokes Auffinger–Chen for the ground-state variational formula **and attainment**, then fixes a minimizer. The two selected Lean targets are conditional on minimizers and do not themselves assert existence of one. [Section 3, lines 23–48][scalar-input] [Scope, lines 10–16][scope]

Writing \(u=\Phi_x\), \(a=\Phi_{xx}\), the same coefficient defines
\[
dX_t=\gamma(t)u(t,X_t)\,dt+dB_t,\qquad X_0=0.
\]
The imported companion conclusions are
\[
\mathbb Eu(t,X_t)^2=t,\qquad \mathbb Ea(t,X_t)^2=1,\qquad
P_*=\int_0^1\mathbb Ea(t,X_t)\,dt.
\]
The manuscript also uses oddness of \(u\), evenness and nonnegativity of \(a\), \(|u|\le1\), and bounded spatial derivatives on each fixed strip ending before one. It identifies the companion's Theorem 1.1, Lemmas 2.1–2.2, Corollary 7.1, and Proposition 7.2 as its scalar sources. Neither smooth density of the zero-temperature Stieltjes measure nor derivative bounds uniform up to \(t=1\) are required here. The Stieltjes convention is \(\mu_\gamma([0,t])=\gamma(t)\), so “full support” is relative to \([0,1)\), not a claim about an endpoint atom at one. [Section 3, `eq:scalar-consistency-value`–`eq:scalar-terminal-loss`][scalar-input]

Nonnegative curvature and its unit second moment give
\[
0\le P_*-\int_0^T\mathbb Ea(t,X_t)\,dt\le1-T.
\]
This lets the argument choose a finite \(T<1\) first. The covariance convention is checked explicitly: the unordered-pair Hamiltonian has covariance \(nR_{12}^2/2-1/2\); adding a configuration-independent centered Gaussian of variance \(1/2\) supplies \(n\xi(R_{12})\), with \(\xi(t)=t^2/2\), without changing the expected maximum. [Section 3, lines 43–75][scalar-input]

### From the scalar diffusion to one finite Gaussian function

For this fixed \(T\), put \(\Delta=T/N\), \(t_j=j\Delta\), and use independent standard normals \(Z_1,\ldots,Z_{N+1}\):
\[
Y_0=0,\quad
Y_j=Y_{j-1}+\sqrt\Delta Z_j+
\Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),
\]
\[
c_j=\bigl(\mathbb Ea(t_{j-1},Y_{j-1})^2\bigr)^{-1/2},
\qquad g_j=c_ja(t_{j-1},Y_{j-1})Z_j.
\]
All \(c_j\) are positive and finite for sufficiently large \(N\). The rounded output and coefficients are
\[
F_N=\operatorname{sgn}\!\left(u(T,Y_N)+2\Phi_{\mathrm G}(Z_{N+1})-1\right),
\quad
A_j=\mathbb E[F_Ng_j],\quad B_i=\mathbb E[F_NZ_i],\quad A_0=0.
\]
The independent rounding coordinate is essential: conditionally on the first \(N\) variables, its transformed value is uniform on \((-1,1)\), giving \(\mathbb E[F_N\mid Z_1,\ldots,Z_N]=u(T,Y_N)\) and a null sign-discontinuity event. The imported finite formula is the **shifted** sum
\[
\lim_{N\to\infty}\sum_{j=0}^N A_jB_{j+1}
=\int_0^T\mathbb Ea(t,X_t)\,dt.
\]
Replacing \(B_{j+1}\) by \(B_j\), changing the rounding coordinate, or removing normalization would change the input being used. The mesh limit is at fixed \(T\); no simultaneous limit \(N\to\infty,T\uparrow1\) is supplied. [Section 3, `eq:scalar-euler`–`eq:scalar-coefficient-limit`][scalar-finite]

### Why the finite scalar value is the rooted energy

The manuscript does not infer energy from the marginal distribution of \(F_N\). It constructs all its Gaussian coordinates in one recursive real Hilbert space. A centered child vector \(f\) defines a parent Gaussian position \(\mathsf G(f)=q(f)\), with covariance \(\langle f,g\rangle\) and
\[
\|(\mathsf G(f)-\mathsf G(g))\Omega\|=\|f-g\|.
\]
The root seed is independent of the child-Fock coordinates. All vectors of different finite heights are embedded compatibly in one common height before comparison. [Section 2.3, `eq:classical-gaussian-isometry` and `eq:classical-first-chaos`][gaussian-space]

Starting with a root seed \(g_0=S\), set \(Z_{j+1}=\mathsf G(g_j)\). The induction shows that \(g_0,\ldots,g_N\) are orthonormal:

1. Predictability makes the coefficient multiplying \(Z_j\) measurable in the earlier \(Z\)'s.
2. The newest independent normal centers \(g_j\) and makes it orthogonal to earlier columns.
3. The prescribed \(c_j\) gives norm one.
4. Independence of the receiving-root seed gives orthogonality to \(g_0\).

The induction realizes the **same joint Gaussian law** used to define the normalizers and coefficients, rather than selecting different approximations for each moment. The root-shift operator \(\mathsf L\) places a vector in one child with a constant new root seed. Consequently
\[
\mathsf L^*F_N=\sum_{j=0}^N B_{j+1}g_j,\qquad
\mathcal E(F_N)=\operatorname{Re}\langle F_N,\mathsf LF_N\rangle
=\sum_{j=0}^N A_jB_{j+1}.
\]
The \(g_0\) coefficient contributes zero because \(F_N\) is independent of the receiving-root seed. This first-chaos calculation is the bridge from scalar coefficients to energy, not an additional claim of finite-degree convergence for the raw sign formula. [Section 3, `lem:gaussian-rooted-realization`][rooted-realization]

### Making the target compilable

At fixed \(T,N\), replace the sign by \(\tanh(kH_N)\). The null zero set and dominated convergence give \(L^2\) convergence. The inequality
\[
|\mathcal E(f)-\mathcal E(g)|\le(\|f\|+\|g\|)\|f-g\|
\]
then controls energy. Only afterwards are unbounded transmitted columns replaced by bounded odd functions and finite trigonometric maps. The approximation proceeds from the output toward the leaves: each outer Lipschitz map is fixed before its input tolerance is chosen. A uniform Lipschitz bound over the entire approximation sequence is not assumed. [Section 3, lines 220–337, `lem:classical-trigonometric-density`][bounded-formula]

Colors and the Gaussian input are encoded as measurable functions of the **same raw Gaussian seed**, preserving even color parity, odd Gaussian parity, product law, and root-shift energy. The encoding can be discontinuous in the raw seed; the smoothness requirements concern the continuous aggregate inputs. [Section 3, `eq:raw-seed-reencoding`][color-encoding]

Receiver and ancestor color exclusions turn a descendant calculation into an orientation-free neighbor rule suitable for gates. The estimate
\[
\|f^{\mathrm{col}}-f\|^2\le C(\alpha+p_H)
\]
holds with \(C\) depending on the fixed uncolored formula but not on the number of colors; \(\alpha\) is the maximum nonhelper color probability and \(p_H\) the total helper probability. Disjoint masks are combined before applying the original finite-input Lipschitz bounds. Flattening all source-color fields into separate coordinates need not preserve constants uniform in color count. Formula branches sharing descendants are never declared independent. [Section 3, `lem:classical-color-exclusion`][color-exclusion]

This yields a finite bounded odd output \(m=\sum_c1_c\sin(2\theta_c)\), zero on helpers, with \(\mathcal E(m)\ge P_*-\varepsilon_{\mathrm{cl}}\). The uncolored formula, color law, helper probabilities, depth, and all coefficients are fixed independently of degree, system size, and disorder. [Section 3, `prop:classical-near-optimum`][classical-finish]

## 4. The rooted calculus and classical synthesis carry additional obligations

For an ordinary word, the manuscript identifies its limiting energy with \(\mathcal E(v_Z)\), where \(v_Z=u^*Zu\Omega\) is the rooted insertion vector. Strong convergence of these vectors alone is insufficient for scaled edge energy. Proposition `prop:energy` also requires a uniform expected top-generation occupation bound. Its finite-degree decomposition has a remainder bounded by
\[
|\varepsilon_D|\le\frac{\langle f_D,N_{D+1}f_D\rangle}{D+1}.
\]
Multiplication by \(\sqrt D/2\) then makes that remainder vanish. Lemma `lem:ordinary-updates` and Theorem `thm:gate-calculus` supply the necessary occupation control through stronger weighted bounds. [Section 2, lines 191–267][energy] [Ordinary updates, lines 723–782][ordinary-updates]

The root-map calculus uses convergence of operators **and their adjoints**, parameter derivatives, common commuting controls, and weighted domains. The small-unitary product lemma retains a scalar second-order term; after substitution of operator-valued controls, that term can become an operator and cannot simply be dropped. Exclusion gates must use parameters from a common commuting algebra, exclude their targets from cross-edge dependencies, and preserve joint spin/seed symmetry. These are hypotheses of the replacement mechanism, not consequences of mere boundedness of the final classical output. [Section 2, `lem:unitary-clt`][unitary-clt] [`def:exclusion-gate`–`thm:gate-calculus`][gate-calculus] [Product and context proof, lines 1221–1316][gate-proof]

Theorem `thm:classical-synthesis` states, for the fixed formulas and any \(\eta>0\), the existence of one finite seeded circuit with
\[
\|1_{H^c}(v-v_{\mathrm{cl}})\|<\eta,\qquad
|\mathcal E(v)-\mathcal E(m)|\le2\eta+2\sqrt{p_H}.
\]
It uses the same independent Gaussian labels at every seed gate and averages them in the seeded tree value. The ideal rotation has insertion
\(v_{\mathrm{cl}}=m|+\rangle+\cos(2\theta)|-\rangle\); the second term contributes no rooted energy because of root-spin and child-spin orthogonality. The helper loss follows from \(\|1_Hv\|=\sqrt{p_H}\), with the remaining projected insertion error costing at most \(2\eta\). [Statement][synthesis-theorem] [Energy proof, lines 1088–1119][synthesis-energy]

The difficult operation is propagation of a lower seed-only formula through a neighbor sum. A receiver–sender–helper–sender commutator construction retains returning paths and suppresses paths using two distinct senders. The argument requires more than a heuristic cancellation:

- A common helper mask \(K\), with fixed \(p_K>0\), is unused by the entire surrounding word and is pinned at \(X=1\) throughout its descendant subspaces.
- Refine sender masks \(J_l\) while keeping the lower formula and its finite channel list fixed.
- With \(p_l=\Pr(J_l)\), the corrections are controlled by
  \(\rho=(\sum_l p_l^2)^{1/2}\) and \(\max_l\sqrt{p_l}\), both tending to zero as the largest part shrinks.
- At a helper root, subtract the same-neighbor covariance from
  \(\sum_lq(d_l)q(e_l)\). Orthogonal masks give a Hilbert–Schmidt kernel bound uniform in the number of parts.
- Cuts inside the lower formula retain mixed first and second responses. Their smallness follows through a fixed finite response recursion; it is not inferred from independence of lower channels.
- The remaining root-seed scalar phase cancels in the descendant Heisenberg conjugations.

These are the content of Proposition `prop:helper-contraction`, Lemma `lem:orthogonal-quadratics`, and the lower-cut response calculation. [Section 4, lines 291–352][helper-theorem] [Quadratic estimate, lines 417–492][helper-quadratics] [Lower responses, lines 679–854][helper-responses] [Uniformity and iteration, lines 856–959][helper-iteration]

Compilation proceeds from highest expression rank inward. At each rank the proof first fixes finite pointwise approximations, then refines sender partitions for exact helper contractions, then fixes finite commutator products. Those finite products may rotate an already used helper; the next lower rank uses a different, still untouched helper. All masked elementary controls are replaced by raw seeded controls only after these contraction choices. A finite inner word is chosen in an already fixed outer context. There is no uniform estimate in inverse helper density, generated word length, or the number of repeated lower-formula calls. [Section 4, lines 1012–1086][synthesis-order]

## 5. Removing seeds requires one common approximation of the whole word

Theorem `thm:seed-simulation` starts with a **whole finite seeded word**. Its conclusion approximates that word's limiting tree energy by a finite ordinary word. Independent simulations of individual seed gates with fresh Gaussians would not meet this interface: the original word reuses the same Gaussian at every seed gate. [Section 5, lines 10–40][seed-theorem]

The manuscript fixes a small \(b>0\), then uses \(r\downarrow0\) with initialization cost \(b/r\). An exact decomposition retains a component of norm \(r\), with large coherent displacements, alongside an order-one component. The normalized special insertion direction \(w_r\) has norm one. The initial high directions \(w_r,\ell_r\) become orthogonal to each other and to bounded families of vectors with controlled top occupation moments. Large displacements themselves are not claimed to have uniformly bounded occupation. [Section 5, `lem:seed-packet-estimates` and initialization][seed-packets] [`lem:seed-high-directions`][seed-initial]

Selective probes have two separate tasks: rotate each of finitely many displaced components in the same way, and cancel first-order action on every ordinary component. Lemma `lem:seed-ensemble-control` supplies a **finite exact** product giving one common X rotation, with separate zero clock sums for the two axes. Equal or opposite nonzero centres are allowed; arbitrary independent rotations are not asserted. The actual insertion directions move during the pulses. Lemma `lem:seed-selective-accuracy` controls that motion, proves net \(o(r)\) error on ordinary packets, and \(o(1)\) error on normalized special packets. Uniformity over bounded tail families, including spin-inserted tails, is needed for later insertion comparisons. [Section 5, lines 287–503][seed-selective]

The singular echo uses cost \(t/r\), a selective special flip, cost \(-t/r\), and the undoing flip. Its central estimate is
\[
v'_r-v_r=-2rw_r+o(r),
\qquad
\frac{t}{r}(v'_r-v_r)=-2tw_r+o(1).
\]
The proof combines the two huge costs using their **actual** insertion directions before dividing by \(r\). A generic \(O(r)\) approximation of each insertion would leave an uncontrolled \(O(1)\) error after division. Ordinary \(o(r)\) remainders are carried through the large unitary costs by norm preservation; the proof does not apply an unbounded field to a discarded remainder. [Section 5, `lem:seed-one-echo`, especially `eq:seed-flip-change` and `eq:seed-exact-echo-cancellation`][seed-echo]

A finite Gram induction interprets the limiting \(w_r\) mode as one reusable standard Gaussian \(q(w)\), independent across vertices. The second external mode \(q(\ell)\) appears only in the initialization and is removed by choosing \(b\) small. The echo with \(t=\sigma/2\) implements the requested seed angle \(\sigma\). The manuscript separately proves convergence of root-shift energy: a finite Weyl-sum first-particle calculation shows that the external modes pair to zero against the endogenous child insertion. Gram convergence or a correct marginal Gaussian law alone does not establish this energy statement. [Section 5, lines 735–868, `lem:seed-gram-induction` and `eq:seed-energy-weyl-sum`][seed-gram]

The pulse lists also require simultaneous nonzero visibility conditions. The proof considers all probe starts of the fixed word, treats every target angle as an independent variable, and gives one common test point—every target angle zero—at which all the relevant analytic projections equal \(4bz e^{-8b^2}\ne0\). It perturbs the entire target angle vector outside the finite union of analytic zero sets and zero seed-angle hyperplanes, then constructs probe lists successively. Each list uses projection limits established at earlier stages; no list presupposes the limit of its own implementation. The same perturbed word satisfies all visibility constraints. [Section 5, lines 902–974][seed-visibility]

The resulting choice order is therefore
\[
\text{fixed seeded word}
\;\to\; b
\;\to\; \text{one small angle perturbation}
\;\to\; \text{all finite probe lists}
\;\to\; r>0
\;\to\; \text{one finite ordinary word}.
\]
The three energy errors are initialization, angle perturbation, and the \(r\)-approximation. They are chosen successively to have a prescribed small total. No uniformity as \(b\downarrow0\) is required of the subsequent \(r\)-estimates. Once \(r\) is chosen, the large angles are finite and fixed. [Section 5, proof of `thm:seed-simulation`][seed-finish]

## 6. A common error schedule closes the theorem

The assembly makes the same choices feed all subsequent estimates:

| Choice, in order | What is fixed | Error used in Section 6 |
| --- | --- | --- |
| Classical construction | One minimizer and diffusion, \(T<1\), finite mesh, smoothing, bounded formulas, colors, helpers | \(\mathcal E(m)\ge P_*-\varepsilon/4\) |
| Helper budget | The same helper union used by synthesis, with \(0<p_H<(\varepsilon/8)^2\) | \(2\sqrt{p_H}<\varepsilon/4\) |
| Seeded synthesis | One finite word implementing those formulas with \(\eta=\varepsilon/8\) | \(2\eta=\varepsilon/4\) |
| Seed removal | The whole selected seeded word, with the finite parameter choices of Section 5 | Energy loss \(<\varepsilon/4\) |
| Ordinary transfer | One deterministic finite cost–mixer word, with all angles now frozen | Its tree energy equals \(v_p(\gamma,\beta)\) |

Thus the seeded value exceeds \(P_*-3\varepsilon/4\), and the ordinary value exceeds \(P_*-\varepsilon\). [Section 6, lines 7–34][assembly]

Within the classical construction there is another nested allocation. For a requested classical tolerance \(\delta\), the proof takes initial scalar error \(\delta/3\), trigonometric output norm error \(<\delta/12\) costing \(<\delta/6\) in energy, and color-exclusion output error \(<\delta/6\) costing \(<\delta/3\). The sum is \(<\delta\). Crucially, the entire uncolored bounded formula is fixed before making the color and helper probabilities small. [Section 3, lines 583–608][classical-finish]

The qualitative limiting statements are used as **finite choices**, not as one uncontrolled simultaneous limit. For example, at the selected \(T\), eventual positivity of all mesh normalizers and convergence of the shifted sum can be satisfied by one sufficiently large \(N\): both conditions are eventual properties for that same fixed scalar data. A sign-smoothing parameter is then chosen for that \(N\). In later steps, every finite list of required accuracies is satisfied in one already fixed surrounding circuit.

The source's complete primary schedule is: accuracy; fixed minimizer and \(T<1\); finite mesh; finite smoothing; bounded/trigonometric approximation; type exclusions; helper contractions and finite commutator approximations; elementary seed compilation; \(b\); generic perturbation; finite probe lists; positive \(r\); one ordinary word; thermodynamic limit. Auxiliary degree limits establish the rooted calculus for fixed formulas and fixed words. The final tree-to-SK identity is invoked after all approximation parameters have been frozen. [Section 6, `rem:order-of-choices`][choice-order]

## 7. The independent positive-temperature route and the MaxCut consequence

Appendix A supplies an alternative proof of the **same classical synthesis input**. It is independent of the zero-temperature companion, but shares the bounded approximation and color-exclusion lemmas and all later quantum constructions. Its external inputs are the positive-temperature Parisi formula, Lopatto's positive-temperature full-support result in the cited version, and the finite-step tree calculation of El Alaoui–Montanari–Sellke. The references to Montanari and the broader El Alaoui–Montanari–Sellke optimization framework also explain the construction's antecedents; the appendix explicitly uses the finite-tree calculation rather than importing a zero-temperature near-optimality theorem. [Appendix A, lines 1–28 and 211–216][positive-intro] [External assumptions, lines 30–122][positive-input]

For fixed finite \(\beta_0>1\), the support is \([0,q_{\beta_0}]\), and the PDE terminal value is \(\beta_0^{-1}\log(2\cosh(\beta_0x))\). The manuscript derives
\[
\int_0^T\mathbb Ea(t,X_t)\,dt
\ge P_*-\frac{1/4+\log2}{\beta_0}-(q_{\beta_0}-T),
\quad
\mathbb Ea(t,X_t)^2=1,\quad 1-q_{\beta_0}\le\beta_0^{-1}.
\]
The order is large but finite \(\beta_0\), then \(T<q_{\beta_0}\), then small mesh \(\delta\), with \(L=\lfloor T/\delta\rfloor\). Constants in the mesh estimates may depend on the fixed temperature and cutoff. [`lem:positive-temperature-bound`][positive-bound] [`lem:eams-positive-continuum`][positive-continuum]

The finite-degree messages use a one-step lag: \(A^{r-1}u^r\) has conditional mean zero given the earlier cavity history. Conditional variance may depend on that history; successive finite-degree messages are not asserted independent. At fixed \(\delta,L\), the manuscript obtains a joint independent-Gaussian limit, moment convergence, convergence of degree-dependent deterministic normalizers, and
\[
\lim_{D\to\infty}\frac{D+1}{2\sqrt D}\mathbb Ez_o^Lz_v^L
=\delta\sum_{r=1}^{L-1}c_{\delta,r}\mathbb Ea(t_r,X_r^\delta).
\]
Its source discussion corrects the finite-sum endpoints and a same-time normalization display relative to the cited EAMS text, basing the calculation on that paper's Proposition 2.1. These are source-attributed indexing corrections, not new checks of the external paper in this note. [Appendix A, `lem:eams-finite-step` and its proof, lines 218–450][positive-finite]

Lemma `lem:classical-strong-limit` then supplies **norm convergence in occupation embeddings and a uniform occupation moment**, beyond the distributional CLT. It identifies the same rooted vector's energy with the finite-tree edge limit. Only after that identification does the diffusion coupling bound the clipping error \(\|z^\delta-\pi(z^\delta)\|=O(\sqrt\delta)\). Thus the scalar law controls the clipping error, while the stronger realization controls energy. The shared bounded and color approximations finish Proposition `prop:classical-near-optimum-positive-temperature`. [Appendix A, lines 549–728][positive-strong] [lines 733–788][positive-finish]

The regular-MaxCut corollary has its own quantifiers:
\[
\forall\eta>0\ \exists p,\gamma,\beta,D_0\
\forall D\ge D_0\ \forall G
\quad
q_{p,G}(2\gamma/\sqrt D,\beta)
\ge\tfrac12+\frac{P_*-\eta}{\sqrt D},
\]
where \(G\) is finite, simple, unweighted, \((D+1)\)-regular, and has girth \(>2p+1\). The normalized \(\gamma,\beta\) are independent of \(D\) and \(G\); the usual MaxCut cost angles have the displayed degree scaling. This is a lower bound for high-girth graphs, not an optimality statement for every such graph. [Section 1.3, `cor:regular-maxcut`][maxcut-statement]

For uniform simple regular graphs, the same chosen word satisfies
\[
\lim_{D\to\infty}
\limsup_{\substack{n\to\infty\\n(D+1)\ {\rm even}}}
\Pr_G\!\left[
\sqrt D\bigl(\operatorname{OPT}(G_{n,D+1})-
q_{p,G_{n,D+1}}(2\gamma/\sqrt D,\beta)\bigr)>\eta
\right]=0.
\]
The inner limit fixes \(D,p,\gamma,\beta\), and the probability is over graphs only; the quantum measurement has already been averaged. Section 7 uses local tree cones, the short-cycle theorem of McKay–Wormald–Wysocka, and Dembo–Montanari–Sen's optimum asymptotics. It does not claim a joint size–degree limit, fixed-degree optimality, or a degree-uniform two-qubit gate depth. [Statement, lines 232–255][maxcut-statement] [Section 7, lines 12–85][maxcut-proof]

## 8. What the two Lean interfaces actually say

### Full support

The public statement `OAI.ZeroTemperatureSK.full_support` quantifies over a Brownian system \(W\) and an admissible order parameter \(\gamma\), assumes `IsMinimizer W γ`, and concludes `FullSupportConclusion W γ`. That conclusion contains:

- existence of a relative Stieltjes measure and an associated diffusion;
- full support for every measure satisfying the Stieltjes representation;
- strict increase between every pair of distinct times below one;
- the two self-consistency moment identities for **every** associated diffusion.

This last universal clause matters for witness compatibility: one may choose the diffusion supplied by the existence clause and apply both identities to it, rather than combining unrelated existential diffusions. The actual implementation also uses diffusion uniqueness when transporting moments from its constructed diffusion to another one. [Comparator interface, lines 65–92][lean-support-interface] [Implementation, lines 35–59][lean-support-main]

### Scalar value and finite Gaussian approximation

The statement `OAI.SKValue.value_consequences` is a conjunction of three universally quantified implications:

1. For \(W,\gamma,X\), minimizer and diffusion hypotheses imply `ScalarValueConclusion W γ X`.
2. For the same kind of data and every \(0<T<1\), those hypotheses imply `FiniteGaussianConclusion W γ X T`.
3. For \(W,\gamma\), the minimizer hypothesis implies `groundStateValue = parisi W γ`.

The first conclusion includes convergence of the finite-system expected optimum and **one terminal variable \(U\)** with all of its martingale, almost-sure, \(L^2\), and scalar identities. The same \(U\) is used in
\(P_*=\mathbb E[UB_1]\), and the same \(\gamma,X\) appear in the terminal and curvature formulas. The second conclusion includes eventual positivity of all mesh normalizers, convergence of the literal shifted coefficient sum at fixed \(T\), and convergence of curvature integrals as the terminal time increases to one. [Comparator interface, lines 106–170][lean-value-interface]

The finite Gaussian definitions are explicit: Euler steps use zero-based Gaussian coordinates, the extra coordinate with index \(N\) supplies sign rounding, `coefficientA` returns zero at index zero, and `shiftedCoefficientSum` uses `coefficientB ... (j+1)`. This matches the manuscript's one-based \(Z_1,\ldots,Z_{N+1}\) convention after shifting coordinate indices; a downstream bridge must preserve that indexing. [Interface definitions, lines 120–161][lean-value-finite]

The challenge files end their target statements with `sorry` because they are interfaces. The implementing declarations are in the OAI proof trees. The existence of those source implementations is distinct from a build or Comparator receipt; the present note treats them as source, without upgrading the checking status. [Support implementation][lean-support-main] [Value implementation, lines 16–24][lean-value-main]

### The informal chain is not a direct Lean import chain

The two interfaces use different representations. `ZeroTemperatureSK` takes an order parameter on the subtype \([0,1)\), a Brownian system on an externally supplied space, and a nonnegative-time diffusion. `SKValue` uses a real-domain coefficient, a bundled Brownian space, and a real-time diffusion. A direct application across these namespaces would require transport of the coefficient, control value, filtration, minimizer predicate, derivative definitions, and diffusion law; matching names do not supply those equalities. [Support definitions, lines 12–79][lean-support-defs] [Value definitions, lines 33–88][lean-value-defs]

The visible value endpoint actually takes a different source route. `value_consequences` assembles `scalar_value_target`, `finite_gaussian_target`, and `ground_state_parisi_target`. Those wrappers use `IsMinimizer.gradient_moment_contact` and the value tree's own diffusion construction. The contact theorem proves the gradient moment identity in the `SKValue` representation; it is not an application of `ZeroTemperatureSK.full_support`. The contact assembly derives scalar identities and finite Gaussian conclusions from this common contact premise and strip regularity. Accordingly, “full support supplies the scalar mechanism” is an informal mathematical explanation, not evidence of a direct Lean edge from the value endpoint to the support endpoint. [Value endpoint][lean-value-main] [Ground-state wrappers, lines 13–27][lean-value-wrappers] [Contact theorem, lines 75–82][lean-value-contact] [Contact assembly, lines 21–72][lean-contact-assembly]

## 9. The remaining bridge obligations and review limits

A circuit formalization extending these endpoints would have to make the following interfaces literal. These are gaps between the **selected formal statements** and the manuscript theorem, not findings that the manuscript's supplied proofs are false.

| Bridge obligation | Why the scalar endpoints alone do not settle it | Manuscript locator |
| --- | --- | --- |
| Produce admissible minimizing data in the representation used downstream | Both endpoints quantify conditionally over minimizers. The manuscript's existential start uses external attainment. | [Section 3, lines 23–48][scalar-input] |
| Realize finite Gaussian formulas with the correct rooted energy | Equal distributions do not determine a root-shift quadratic form. The normalizers, orthogonal columns, first chaos, and shifted sum must be identified together. | [`lem:gaussian-rooted-realization`][rooted-realization] |
| Preserve energy under bounded approximation and exclusions | The output and all transmitted columns have different boundedness requirements; covariance and shared descendants must be preserved. | [Bounded approximation][bounded-formula], [type exclusion][color-exclusion] |
| Compile the entire excluded formula | The helper contraction needs count-uniform quadratic bounds and lower-cut responses inside fixed contexts, followed by the specified order of finite approximations. | [Helper estimates][helper-quadratics], [responses][helper-responses], [compilation][synthesis-order] |
| Remove the same seed family across all gates | Marginal Gaussian replacement is insufficient. Actual insertion differences must be \(o(r)\)-accurate before a \(1/r\) echo, and energy needs its own first-particle calculation. | [Echo][seed-echo], [Gram and energy calculation][seed-gram] |
| Identify the ordinary word with the physical SK circuit | An ordinary fixed-word transfer must use the same gate signs, normalizations, angles, and order; seeded transfer cannot be assumed. | [`prop:tree-transfer`][tree-transfer], [assembly][assembly] |
| Obtain algorithmic resource bounds | Existence of a finite approximation at each accuracy supplies no depth, angle-size, finite-size, or computational complexity bounds. | [Introduction, lines 131–133][intro-model], [order of choices][choice-order] |

The additional analytic regularity used in the manuscript is also not interchangeable with the bare endpoint statements. Smoothness, parity, moment bounds, and controlled compositions require the appropriate supporting lemmas or a new formal interface; an endpoint's scalar equality does not export all of them. The value source does use a named strip-regularity input in its contact assembly, so this is a requirement to identify and transport the right existing facts, rather than a claim that every such fact is absent from the proof tree. [Contact assembly][lean-contact-assembly]

This reading does not independently establish the weighted-domain and self-adjointness arguments, the operator-valued Fourier substitution, uniformity of helper quadratics and lower-cut responses, the packet estimates through the singular echo, or the external theorems as cited. Their hypotheses and claimed uses are reconstructed above from the public source. Those analytic arguments remain the main subjects for a specialist proof audit; the scalar Lean endpoint statements do not discharge them. [Smooth substitution][commuting-substitution] [Helper estimates][helper-quadratics] [Lower responses][helper-responses] [Echo][seed-echo]

The cited external theorems have distinct roles. Auffinger–Chen supplies the primary route's variational value and attainment; the OpenAI companion supplies the scalar support, regularity, and coefficient package; Basso and coauthors supplies the final ordinary-word identity; the positive-temperature and random-regular results enter only their respective routes. References to spin–boson numerics, truncated-Wigner heuristics, ensemble-control antecedents, and refocusing methods are not substitutes for the manuscript's rooted, synthesis, or seed-removal proofs. These distinctions are visible in the [introduction][intro-context] and the [pinned bibliography][bibliography].

The construction's hardest transitions are therefore concrete: scalar coefficients to a rooted energy, helper contraction in a changing surrounding circuit, and singular seed removal with simultaneous visibility and a shared Gaussian mode. The manuscript supplies arguments at each of these transitions. This source reconstruction identifies what those arguments must carry and where they are written; it does not confer independent proof acceptance, extend the selected Lean coverage to QAOA circuits, or supply the quantitative algorithmic guarantees the manuscript expressly leaves unspecified.

[main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/main.tex#L51-L100
[intro-model]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L74-L133
[intro-order]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L34-L133
[intro-context]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L1-L72
[scope]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md#L8-L23
[tree-transfer]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L11-L45
[energy]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L178-L267
[gaussian-space]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L282-L358
[ordinary-updates]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L723-L782
[unitary-clt]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L554-L699
[commuting-substitution]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L794-L929
[gate-calculus]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L970-L1050
[gate-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L1221-L1316
[additive-response]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L1318-L1444
[scalar-input]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L15-L121
[scalar-finite]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L84-L121
[rooted-realization]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L123-L218
[bounded-formula]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L220-L337
[color-encoding]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L392-L436
[color-exclusion]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L438-L551
[classical-finish]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L553-L608
[synthesis-theorem]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L38-L79
[synthesis-order]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L1012-L1119
[synthesis-energy]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L1088-L1119
[helper-theorem]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L291-L352
[helper-quadratics]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L417-L492
[helper-responses]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L679-L854
[helper-iteration]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L856-L959
[seed-theorem]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L10-L48
[seed-packets]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L50-L158
[seed-initial]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L160-L270
[seed-selective]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L287-L503
[seed-echo]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L605-L733
[seed-gram]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L735-L868
[seed-visibility]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L902-L974
[seed-finish]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L976-L1006
[assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/06-assembly.tex#L7-L34
[choice-order]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/06-assembly.tex#L36-L53
[positive-intro]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L1-L28
[positive-input]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L30-L122
[positive-bound]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L139-L209
[positive-finite]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L218-L450
[positive-continuum]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L462-L532
[positive-strong]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L549-L728
[positive-finish]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex#L733-L788
[maxcut-statement]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L200-L255
[maxcut-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/08-regular-maxcut.tex#L12-L85
[lean-support-defs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L12-L79
[lean-support-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L65-L92
[lean-support-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L19-L59
[lean-value-defs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L33-L88
[lean-value-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L106-L171
[lean-value-finite]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L120-L161
[lean-value-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16-L24
[lean-value-wrappers]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/GroundState/MainConclusions.lean#L13-L27
[lean-value-contact]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/MinimizerContact.lean#L75-L82
[lean-contact-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/ContactAssembly.lean#L21-L72
[bibliography]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/references.tex#L6-L162


## Consequences and quantifiers reconstructed on 24 October 2026

Long §§8.1–8.6 give the operator and energy argument in detail: root-shift
first chaos, occupation control of the scaled edge remainder, the unitary
second-response identity with its nonzero cut baseline, helper compression
with mixed lower-cut responses, and seed removal using the actual insertion
direction and external Gaussian mode. The seed-vector decomposition need not
be orthogonal, and a displaced component need not have bounded occupation;
its occupation tail is what the source controls. Marginal Gaussian laws,
vacuum compression or state-norm convergence alone cannot replace these
statements. Their source owners remain Q/sections/02-foundations.tex,
04-classical-synthesis.tex and 05-seed-simulation.tex as linked above.

Long §11.2 uses Farhi–Goldstone–Gutmann–Zhou, arXiv:1910.08187v4,
equations (13)–(14), to derive $L^2$ concentration of one measurement for
each fixed word, jointly over disorder and measurement. This ordinary
consequence combines with the near-optimal word before taking $n\to\infty$;
it is neither a selected formal endpoint nor a growing-depth concentration
theorem. Long §11.3 proves the padded existence schedule and distinguishes
quadratic SK from higher-spin overlap-gap results. Long §11.4 preserves the
source's separate high-girth lower bound and random-regular optimality limits.

Long §11.1 includes the exact fixed-temperature change of variables from
Lopatto's PDE and the uniform entropy estimate. The scalar free-energy
values therefore permit a joint size–temperature limit, while the circuit
construction still fixes its word first. Long §11.5 quotes the later
arXiv:2609.40309v1 Corollary S3.1 with every parameter restriction and derives
its sufficient bounded-angle regime $p\log p=o(\log\log n)$. This source
postdates the QAOA manuscript's displayed date; it is context, not an input
silently added to its proof. Its finite-size theorem is quoted at the stated
edition, without claiming an independent audit of its entire derivation.

The depth qualification in the higher-spin comparison is material. Goh,
[arXiv:2404.06087v6, Theorem 4.2 and Corollary 4.2.1, pp. 11–12](https://arxiv.org/abs/2404.06087v6),
states a logarithmic-depth obstruction for sparse random-regular Max-q-XORSAT
with even q at least four. Its dense spin-glass corollary is explicitly
conditional on swapping limits. The following discussion says the sparse/dense
equivalence is established only at fixed depth and does not establish a dense
logarithmic-depth obstruction. None of these hypotheses includes quadratic SK.

## Local method credits and two support consequences

The following primary-source passages were checked against the long record's
uses. This reading checks their stated roles and the displayed normalization
arguments; it is not an independent audit of every cited external proof.

- [Boulebnane et al., arXiv:2505.07929v2, Theorem 2 (informal), equations
  (10)–(11), p. 3](https://arxiv.org/abs/2505.07929v2), supplies the earlier
  fixed-depth spin–boson representation. Long §8.1 now credits it before
  explaining the further occupation, insertion and surrounding-circuit
  estimates. The source's attribution is in its [§2, lines 47–63](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L47-L63).
- [Jones and Knill, arXiv:quant-ph/9905008v1, §II, p. 2](https://arxiv.org/abs/quant-ph/9905008v1),
  explains orthogonal-sign refocusing. Its role in long §8.3 is isolation
  of commuting Ising subcosts, as credited in the source's
  [§4, lines 184–205](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L184-L205).
  It does not supply the subsequent helper-contraction estimates.
- [Li and Khaneja, arXiv:quant-ph/0510012v1, §II, Examples 1–2,
  pp. 2–3](https://arxiv.org/abs/quant-ph/0510012v1), supplies the Lie-bracket
  and polynomial-approximation antecedent, with its parameter-sign
  restrictions. Long §8.4 distinguishes this method from the source's
  [finite-family exact zero-clock lemma and subsequent accuracy argument](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L272-L343).
- [Talagrand, Theorem 1.1, pp. 222–223](https://doi.org/10.4007/annals.2006.163.221),
  supplies the positive-temperature Parisi formula in long §11.1.
  Hypotheses (1.3)–(1.5) admit the fixed-temperature covariance error
  $\beta_0^2/(2n)$; partition sum (1.14) is unnormalized. This input
  is separate from the zero-temperature variational formula and attainment.
- [Farhi, Goldstone and Gutmann, arXiv:1411.4028v1, §VI,
  pp. 10–11](https://arxiv.org/abs/1411.4028v1), gives the adiabatic/Trotter
  explanation of fixed-instance convergence. Long §8 places this credit
  beside the different size-independent-word quantifier.

Long §9.3 applies [Auffinger–Chen–Zeng, arXiv:1703.06872v2,
Proposition 1, equation (5), p. 5, proof pp. 15–16](https://arxiv.org/abs/1703.06872v2)
at every fixed overlap in the full-support measure. Its common-Gaussian
covariance completion and Gaussian tail calculation were checked directly.
This is an imported ordinary pair-existence consequence, with constants
depending on the fixed overlap and tolerances, not a typical-pair theorem,
an algorithm, or an additional selected formal statement.

Long §2.3 makes the two limit topologies in [Chen, arXiv:2607.18032v1,
Remarks 1.4–1.5, p. 3](https://arxiv.org/abs/2607.18032v1), explicit.
The probability-measure example there has full interval support before the
limit but a gap in the scaled vague limit, even with cumulative-coefficient
$L^1$ error at most $3/(2n)$. Its normalization, endpoint atom, support,
vague and weak limits, and error estimate were checked directly. It is
explicitly not a sequence of Parisi minimizers.

The [scalar-value historical receipt](../../../examples/qaoa-sk/verification/scalar-value-build-failure-20261024.json)
and its [log](../../../examples/qaoa-sk/verification/scalar-value-build-failure-20261024.log)
now record the terminal solution-build failure of the original invocation,
after challenge build and export. The missing imported object is
`Gaussian/IntegralPositiveMulGaussian`. The corrected build configuration
has not been replayed, and no solution export, kernel acceptance or
comparison acceptance is established by this event. This chronology is
also stated in long §13.
