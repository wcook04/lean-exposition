# The scalar-value interface

The selected source theorem, `OAI.SKValue.value_consequences`, identifies the limiting expected SK maximum per spin with the Parisi value of any admissible minimizer, gives three equivalent diffusion formulas for that value, and supplies finite Gaussian coefficient sums converging to it through two successive limits. Its three branches have different hypotheses: the first two accept a diffusion; the third constructs one internally. This is a static review of the public source at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with manuscript correspondence rather than a new Lean, Comparator, or independent acceptance result.

The implementing statement is [Main, lines 16–24][main]. Its type text agrees exactly with the [challenge statement, lines 163–170][challenge]; the proof bodies differ. The definitions in [Model, lines 1–161][model] agree exactly with the corresponding challenge definitions. Exact repository-relative source paths are collected below.

## Model and hypotheses

The order parameter is a real function on all of ℝ whose restriction to \([0,1)\) is nonnegative, nondecreasing, and right-continuous. It must be Lebesgue integrable on \((0,1]\). This representation permits an integrable singularity as time approaches one; it imposes neither a smooth density nor a bound uniform up to one. Values outside the stated domain are not constrained by these order-parameter fields. These are the zero-temperature scalar coefficients, not QAOA cost angles. [Model, lines 33–39][order]

A `BrownianSpace` supplies a probability space, a real Brownian process indexed by nonnegative times, and strong measurability of each evaluation. The filtration used by the theorem is the natural filtration of that Brownian process. The control defining the value function is progressive for the natural filtration of the increments starting at time \(t\), and obeys \(|\alpha_s(\omega)|\leq1\) for every \(s,\omega\). [Model, lines 40–60][brownian]

For \(0\leq t\leq1\), the source defines the control value

\[
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_0^{1-t}\gamma(t+s)\alpha_s\,ds\right|
-\frac12\int_0^{1-t}\gamma(t+s)\alpha_s^2\,ds\right].
\]

It then defines \(u=\partial_x\Phi_\gamma\), \(a=\partial_xu\), and

\[
\mathcal P(\gamma)=\Phi_\gamma(0,0)-\frac12\int_0^1t\gamma(t)\,dt.
\]

Thus the formal value function is defined by the control problem; a PDE interpretation is not an extra hypothesis of `value_consequences`. `IsMinimizer W γ` means \(\mathcal P(\gamma)\leq\mathcal P(\eta)\) for every order parameter \(\eta\) on this same Brownian space. Minimization is a substantive hypothesis, not a property of every admissible coefficient. The selected theorem has no branch asserting that a minimizer exists. [Model, lines 62–81][control]

`IsDiffusion W γ X` requires adaptation of the stopped process \(X_{\min(t,1)}\) to that natural filtration. On a single event of probability one, the path is continuous on \([0,1]\) and satisfies, simultaneously for every \(t\) in this interval,

\[
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds.
\]

This is the integral form of \(dX_t=\gamma(t)u(t,X_t)dt+dB_t\), with \(X_0=0\) almost surely. There is no arbitrary initial condition or separate user-supplied terminal value. [Model, lines 83–88][diffusion]

## Hamiltonian normalization

For positive spin-system size \(n\), the source uses

\[
h_{n,J}(\sigma)=\frac1{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j,
\qquad
e_n=\frac1n\mathbb E_J\max_{\sigma\in\{-1,1\}^n}h_{n,J}(\sigma).
\]

Each \(J_{ij}\) is standard real Gaussian. Formally the Gaussian product has a coordinate for every ordered pair, but the Hamiltonian uses only \(i<j\); unused diagonal and reverse-pair coordinates do not contribute. Booleans encode spins by `true ↦ 1`, `false ↦ −1`. The sign is the positive maximum convention. `groundStateValue` is defined using `limUnder atTop groundStateSequence`; that total definition alone is not a proof of convergence. The first branch explicitly asserts convergence of the real sequence \(e_n\). It does not assert almost-sure convergence of a random finite-system optimum. [Model, lines 90–100][hamiltonian]

This matches the QAOA manuscript's `eq:sk-model` and `eq:parisi-constant`. For two configurations with overlap \(R\), the covariance is \(nR^2/2-1/2\). As the manuscript explains, adding an independent centered Gaussian of variance \(1/2\), common to every configuration, yields covariance \(n\xi(R)\) with \(\xi(R)=R^2/2\) without changing the expected maximum. The factors \(n^{-1/2}\), \(n^{-1}\), and \(1/2\) therefore belong to the statement. [Introduction, lines 76–91][intro]; [classical optimization, lines 43–48][qaoa-normalization]

## All three branches

**1. Scalar value and terminal martingale.** For every Brownian space, admissible minimizer, and diffusion satisfying the preceding hypotheses, `ScalarValueConclusion` gives \(e_n\to P_*\), where \(P_*\) denotes `groundStateValue`, and a random variable \(U\) such that:

- The process equal to \(u(t,X_t)\) for \(t<1\) and to \(U\) for \(t\geq1\) is a martingale for the natural Brownian filtration.
- Almost surely, \(|U|\leq1\), \(U^2=1\), and \(u(t,X_t)\to U\) as \(t\uparrow1\). The convergence also satisfies \(\mathbb E[(u(t,X_t)-U)^2]\to0\).
- All three identities hold:

\[
P_*=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt
=\mathbb E[UB_1]
=\int_0^1\mathbb E[a(t,X_t)]\,dt.
\]

- The function \(t\mapsto\mathbb E[a(t,X_t)]\) is interval-integrable between zero and one.

These are every component of the conjunction in [Model, lines 102–118][scalar]. In particular, the terminal formula subtracts the **full** integral \(\int t\gamma\), although the definition of \(\mathcal P\) subtracts half of that integral. The assertion about \(U\) is an almost-sure statement. The interface does not additionally state the pointwise identity \(U=\operatorname{sgn}(X_1)\).

**2. Finite Gaussian approximation.** For the same minimizer and diffusion, and for every fixed real \(T\) with \(0<T<1\), `FiniteGaussianConclusion` asserts:

1. For all sufficiently large mesh counts \(N\), every normalizer with index \(0\leq j<N\) is strictly positive.
2. The specified coefficient sum tends, as \(N\to\infty\), to \(\int_0^T\mathbb E[a(t,X_t)]dt\).
3. The latter curvature integral tends to \(P_*\) as its upper endpoint approaches one from below.

The threshold for \(N\) may depend on \(W,\gamma,T\); positivity holds for all active indices at once. There is no positivity assertion for every finite mesh, no convergence rate, and no uniform-in-\(T\) or prescribed diagonal limit in this interface. [Model, lines 155–161][finite]

**3. Parisi identity without an input diffusion.** For every Brownian space and admissible minimizer,

\[
P_*=\mathcal P(\gamma).
\]

Only `IsMinimizer` is an explicit hypothesis of this branch. The proof invokes the separately constructed `diffusionProcess W γ`; `diffusionProcess_isDiffusion` is stated for **every** order parameter, without a minimizer hypothesis. This removes a need to supply \(X\) in branch 3; it does not remove the minimizer hypothesis. [Main, lines 22–24][main]; [MainConclusions, lines 21–27][targets]; [DiffusionExistence, lines 74–79][existence]

## What the finite Gaussian formula means

The mesh count \(N\) is distinct from the spin-system size \(n\). Fix \(0<T<1\), put \(\Delta=T/N\), and let \(Z_1,\ldots,Z_{N+1}\) be independent standard normals. For positive \(N\), the source definitions translate to

\[
\begin{aligned}
Y_0&=0,\\
Y_j&=Y_{j-1}+\sqrt\Delta Z_j
+\Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),\qquad t_j=j\Delta,\\
c_j&=\left(\mathbb E[a(t_{j-1},Y_{j-1})^2]\right)^{-1/2},\\
g_j&=c_j a(t_{j-1},Y_{j-1})Z_j\qquad(1\leq j\leq N),\\
F_N&=\operatorname{sgn}\!\left(u(T,Y_N)+2\Phi_{\rm G}(Z_{N+1})-1\right),\\
A_0&=0,\quad A_j=\mathbb E[F_Ng_j],\quad B_i=\mathbb E[F_NZ_i],\\
\lim_{N\to\infty}\sum_{j=0}^{N}A_jB_{j+1}
&=\int_0^T\mathbb E[a(t,X_t)]\,dt.
\end{aligned}
\]

Here \(\Phi_{\rm G}\) is the standard Gaussian distribution function, \(1\leq j\leq N\) in \(A_j\), and \(1\leq i\leq N+1\) in \(B_i\). Expectations defining these coefficients are on the finite Gaussian product, not the original Brownian sample space. The Brownian space enters through \(u\) and \(a\). [Model, lines 10–31 and 120–159][model]

The indexing must be preserved when relating code to prose:

| Lean expression | Manuscript quantity |
| --- | --- |
| `coordinate N k` for `0 ≤ k ≤ N` | \(Z_{k+1}\) |
| `eulerPath W γ T N z j` | \(Y_j\) |
| `rawCoefficient W γ T N k` | \(a(t_k,Y_k)\) |
| `normalizer W γ T N k` | \(c_{k+1}\) |
| `gaussianIncrement W γ T N k` | \(g_{k+1}\), with **no** \(\sqrt\Delta\) factor |
| `coefficientA … j` | \(A_j\), including the explicit zero at \(j=0\) |
| `coefficientB … i` for `1 ≤ i ≤ N+1` | \(B_i\) |
| `shiftedCoefficientSum W γ T N` | \(\sum_{j=0}^{N}A_jB_{j+1}\) |

The coordinate function uses reduction modulo \(N+1\), but no wrapping occurs in these active ranges. The Euler path uses the first \(N\) coordinates; rounding uses the independent final coordinate. The coefficients are noncomputable mathematical integrals. Their definition is not an efficient numerical procedure or a finite-spin algorithm.

The companion explains the mechanism: the last Gaussian gives a uniform random variable, so sign rounding preserves \(u(T,Y_N)\) as its conditional mean. Euler convergence makes \(c_j\) approach one, while the two correlation vectors approximate the appropriate martingale coefficients. Pairing adjacent indices gives a curvature Riemann sum; the final term \(A_NB_{N+1}\) vanishes. The argument therefore preserves the **shift** in \(B_{j+1}\), including the rounding-coordinate boundary term. This is a description of the companion's proof, not an additional conclusion inserted into the interface. [Consequences, lines 124–196][consequences-proof]

## Manuscript correspondence and proof owners

| Manuscript location | Corresponding scalar source |
| --- | --- |
| QAOA `eq:sk-model`, `eq:parisi-constant`, introduction lines 78–90 | `hamiltonian`, `groundStateSequence`, `groundStateValue`, and the convergence component of `ScalarValueConclusion` |
| QAOA `eq:scalar-consistency-value`, classical optimization lines 56–60 | The curvature-value equality is exported by `ScalarValueConclusion`. The two moment identities on the same manuscript line have separate source owners: `IsMinimizer.gradient_moment_contact` and `IsDiffusion.curvature_unit_moment_of_contact`. They are not additional conjuncts of `value_consequences`. |
| QAOA `eq:scalar-terminal-loss`, lines 69–72 | The displayed bound \(0\leq P_*-\int_0^T\mathbb E a\leq1-T\) uses nonnegative curvature and its unit second moment. The selected finite conclusion itself exports endpoint convergence, not this bound. |
| QAOA `eq:scalar-euler`, `eq:scalar-columns`, lines 84–96 | `euler`, `eulerPath`, `rawCoefficient`, `normalizer`, and `gaussianIncrement` |
| QAOA `eq:scalar-rounding`, `eq:scalar-coefficients`, lines 97–112 | `roundedSign`, `coefficientA`, and `coefficientB` |
| QAOA `eq:scalar-coefficient-limit`, lines 113–121 | `shiftedCoefficientSum` and `FiniteGaussianConclusion`; the manuscript explicitly takes the mesh limit at fixed \(T\) |
| Companion `cor:value`, `eq:value-identities`, consequences lines 14–28 | `ScalarValueConclusion`, including the terminal martingale, mean-square convergence, and three value formulas |
| Companion `prop:gaussian`, `eq:euler`, `eq:normalized-increment`, `eq:finite-value`, lines 92–122 | The finite Gaussian definitions and all three components of `FiniteGaussianConclusion` |

The full QAOA scalar passage is [classical optimization, lines 23–121][qaoa-scalar]; the companion statements are [consequences, lines 14–122][consequences]. The source proof follows these owners:

- `Main` assembles the three results from `GroundState/MainConclusions.lean`. Its first two branches use the minimizer's moment-contact identity \(\mathbb E[u(t,X_t)^2]=t\). [MainConclusions, lines 13–27][targets]; [MinimizerContact, lines 75–82][contact]
- `ContactAssembly` obtains strip regularity, derives \(\mathbb E[a(t,X_t)^2]=1\), and invokes the finite-mesh and value-assembly results. The strip bounds are established inside the proof rather than supplied as extra hypotheses of the selected theorem. [ContactAssembly, lines 21–72][assembly]; [GradientSquareIntegral, lines 84–90][curvature-moment]
- The lower-level fixed-strip lemma explicitly takes curvature bounds, time-space Lipschitz estimates, and the unit curvature moment. Its conclusion gives eventual positivity and the mesh limit. This is the source location for checking how the analytic strip assumptions enter the approximation. [FiniteGaussianFixedStrip, lines 29–49][fixed-strip]
- `groundState_eq_parisi_of_contact` combines a ground-state upper bound by the Parisi value with a lower bound from finite Gaussian coefficient sums and passage to the terminal endpoint. `parisi_value_assembly` supplies the terminal martingale and equivalent value expressions. [ContactAssembly, lines 36–59][assembly]; [IntegralPrimitiveTerminal, lines 37–52][value-assembly]

This scalar theorem supplies an input to the later rooted Gaussian construction. It contains no circuit, depth, angle schedule, rooted-space realization, or assertion about QAOA circuit energies. That boundary agrees with the upstream [family 281 scope statement, lines 10–16][scope].

## Static trust boundary

The challenge proof ends in `sorry` at line 171. It is the admitted comparison target; the implementing `Main` theorem has the proof `⟨scalar_value_target, finite_gaussian_target, ground_state_parisi_target⟩`. Reading these source bodies and comparing their statement text is useful, but it does not establish that a compiler or Comparator accepted them.

The retained [Comparator configuration, lines 1–14][config] selects this one theorem, lists `propext`, `Quot.sound`, and `Classical.choice` as permitted axioms, has an empty `definition_names` list, and sets `enable_nanoda` to `false`. These are configuration facts, not an observed axiom report or a successful comparison. The mathematical hypotheses above remain hypotheses even if a comparison succeeds.

A static traversal from `OAI.Probability.SKValue.Main` resolves 212 imported `OAI` modules in the retained scalar-value tree; its only external import name is `Mathlib`. It does not import the `SKSupport` tree: the manuscript's connection between the two targets is not a cross-target Lean import edge. A textual scan of the scalar closure finds no occurrences of the tokens `axiom`, `sorry`, `sorryAx`, `admit`, `unsafe`, or `native_decide`. This limited observation does not inspect elaborated terms, establish a transitive axiom set, inspect all of mathlib, or replace kernel checking. The source proof uses mathematical infrastructure from Lean and mathlib, and their trust boundary remains visible.

The pinned upstream toolchain is Lean `v4.34.1`, and the original package pins mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`. [Toolchain, line 1][toolchain]; [original Lake file, lines 85–86][lakefile] No new build, elaborated dependency extraction, axiom audit, Comparator run, or independent mathematical acceptance is claimed by this note.

## Exact source locators

Every link below is fixed to the OpenAI commit stated at the start. Paths are relative to this repository; line numbers refer to the retained source bytes.

| Source | Repository-relative path and inspected lines |
| --- | --- |
| [Implementing theorem][main] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Main.lean:16–24` |
| [Challenge][challenge] | `examples/qaoa-sk/upstream/lean/ComparatorChallenges/SKValue.lean:163–171` |
| [Definitions][model] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Model.lean:10–161` |
| [Branch assembly][targets] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/GroundState/MainConclusions.lean:13–27` |
| [Minimizer moment identity][contact] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Variation/MinimizerContact.lean:75–82` |
| [Value and mesh assembly][assembly] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Variation/ContactAssembly.lean:15–72` |
| [Diffusion construction][existence] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Processes/DiffusionExistence.lean:74–79` |
| [Curvature moment][curvature-moment] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Processes/GradientSquareIntegral.lean:84–90` |
| [Fixed-strip approximation][fixed-strip] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Processes/FiniteGaussianFixedStrip.lean:29–49` |
| [Terminal value assembly][value-assembly] | `examples/qaoa-sk/upstream/lean/OAI/Probability/SKValue/Evolution/IntegralPrimitiveTerminal.lean:37–52` |
| [Comparator configuration][config] | `examples/qaoa-sk/upstream/lean/ComparatorChallenges/SKValue.json:1–14` |
| [Scope][scope] | `examples/qaoa-sk/upstream/lean/docs/281.md:10–16` |
| [QAOA normalization][intro] | `examples/qaoa-sk/upstream/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex:76–91` |
| [QAOA scalar input][qaoa-scalar] | `examples/qaoa-sk/upstream/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex:23–121` |
| [Companion statements and argument][consequences-all] | `examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex:14–196` |
| [Toolchain][toolchain] | `examples/qaoa-sk/upstream/lean/lean-toolchain:1` |
| [Original mathlib requirement][lakefile] | `examples/qaoa-sk/upstream/provenance/lakefile.lean:85–86` |

[main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16-L24
[challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L163-L171
[model]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L1-L161
[order]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L33-L39
[brownian]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L40-L60
[control]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L62-L81
[diffusion]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L83-L88
[hamiltonian]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L90-L100
[scalar]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L102-L118
[finite]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Model.lean#L155-L161
[targets]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/GroundState/MainConclusions.lean#L13-L27
[contact]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/MinimizerContact.lean#L75-L82
[assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/ContactAssembly.lean#L15-L72
[existence]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Processes/DiffusionExistence.lean#L74-L79
[curvature-moment]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Processes/GradientSquareIntegral.lean#L84-L90
[fixed-strip]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Processes/FiniteGaussianFixedStrip.lean#L29-L49
[value-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Evolution/IntegralPrimitiveTerminal.lean#L37-L52
[config]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.json#L1-L14
[scope]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md#L10-L16
[intro]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex#L76-L91
[qaoa-normalization]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L43-L48
[qaoa-scalar]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L23-L121
[consequences]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex#L14-L122
[consequences-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex#L124-L196
[consequences-all]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex#L14-L196
[toolchain]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/lean-toolchain#L1
[lakefile]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/lakefile.lean#L85-L86


## Additional source-level reconstruction

Long §8.3 reconstructs the scalar tree's independent proof of moment contact:
`Variation/ContactIntegral.lean` forces a constant coefficient on each positive
component of $G$; `Coercivity/GapBoundary.lean` uses convexity of $q'-1$ for a
positive constant; `Coercivity/ZeroGapHump.lean` uses convexity of $q-t$ for a
zero constant. The right endpoint may be one, where $q(t)-t\le1-t$ replaces
contact. `Variation/ContactAssembly.lean` then assembles the scalar identities.
This route does not import the separate support endpoint.

Long §8.2 spells out the eventual-normalizer order
$\exists N_0\,\forall N\ge N_0\,\forall j<N$ at each fixed $0<T<1$.
It also separates the Euler coordinates $0,\ldots,N-1$ from the final
rounding coordinate $N$. The product identity $UX_1=|X_1|$ places no
restriction on $U$ on the event $X_1=0$ beyond its already proved spin values;
no atomlessness premise is needed. Compact-strip regularity and intermediate
continuity conditions are supplied inside the proof tree, rather than new
hypotheses silently appended to `value_consequences`.
