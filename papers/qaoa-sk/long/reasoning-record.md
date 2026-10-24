# From Parisi full support to deterministic QAOA circuits

## A long reasoning record

Draft, 24 October 2026. Mathematical sources: OpenAI's full-support
manuscript of 27 September 2026 and QAOA manuscript of 25 September 2026,
at the [pinned public revision](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).

<!-- passage:overview -->
The full-support manuscript proves that an admissible integrable minimizer
of the zero-temperature Parisi functional for the pure zero-field
Sherrington–Kirkpatrick model has Stieltjes support equal to every overlap
scale in [0,1). The proof turns a hypothetical support gap into a constant
interval for the order parameter. Variational contact at the ends of that
interval conflicts with a strict curvature inequality inside it. Full
support then makes the gradient diffusion's second moment equal to time,
and its correlation with Brownian motion represents the ground-state value.
The manuscript's further argument gives a smooth Stieltjes density, strictly
positive on $(0,1)$, and no atom at zero. Sections 5.1–5.2 derive this stronger
ordinary conclusion separately from the selected formal support statement.

This record reconstructs those arguments and follows the finite Gaussian
approximation into the separate QAOA manuscript. The latter claims that
finite deterministic circuits approach the SK optimum when system size tends
to infinity before circuit depth increases. Its circuit construction needs
additional approximation, synthesis, seed-removal and transfer arguments.
The two formal statements concern full support and scalar value
consequences; neither states QAOA circuit convergence. Their verification
scope is described at the end. See [OpenAI (2026a), §§1–2][fs-main] and
[OpenAI (2026b), Theorem 1.1][q-intro].
<!-- /passage:overview -->

The support and scalar arguments assume real analysis, stochastic calculus
and variational minimization. Section 9 additionally uses Hilbert-space
tensor products, symmetric Fock space, unbounded operators and quantum
control. Its weighted-domain and control estimates are additional analytic
inputs from the QAOA manuscript; the text gives their precise uses and
proof destinations. The companion short paper concentrates on the support
theorem, while the exposition introduces its objects through examples.
References to OpenAI (2026a) and OpenAI (2026b) distinguish the two
manuscripts throughout.

<a id="model-and-three-targets"></a>

## 1. Model, normalization and three targets

<!-- passage:model -->
For independent standard Gaussian couplings $J_{ij}$, put

$$
H_n(\sigma)=\frac1{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j,\qquad
\sigma\in\{-1,1\}^n,\qquad
P_*=\lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma).
$$

For overlap $R_{12}=n^{-1}\sum_i\sigma_i^1\sigma_i^2$, the covariance is
$nR_{12}^2/2-1/2$. Thus the convention is $\xi(t)=t^2/2$, with
$\xi''=1$. A centered Gaussian of variance $1/2$, common to all
configurations, removes the final constant without changing the expected
maximum. Every normalization below uses this convention.

Let $\mathcal U$ consist of nonnegative, nondecreasing, right-continuous
functions $\gamma:[0,1)\to[0,\infty)$ with
$\int_0^1\gamma(t)\,dt<\infty$. Their Stieltjes measures satisfy
$\mu_\gamma([0,t])=\gamma(t)$, including
$\mu_\gamma(\{0\})=\gamma(0)$. They are locally finite, but need not be
probability measures or have finite total mass. Support is relative to [0,1).

Let $B$ be standard Brownian motion. The control value and Parisi
functional are

$$
\Phi_\gamma(t,x)=\sup_{|\alpha|\le1}\mathbb E\left[
 \left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
 -\frac12\int_t^1\gamma(s)\alpha_s^2\,ds\right],
$$
$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)-\frac12\int_0^1t\gamma(t)\,dt.
$$

Controls are progressively measurable for Brownian increments after $t$.
For a general admissible coefficient, the solution and its spatial derivatives
are locally absolutely continuous in time on compact strips; the time equation
holds almost everywhere. The control formula fixes the solution. The PDE is
$\Phi_t=-\tfrac12(\Phi_{xx}+\gamma\Phi_x^2)$, with
$\Phi(1,x)=|x|$. Auffinger and Chen's zero-temperature Parisi formula and
attainment identify $P_*$ with $\min_{\gamma\in\mathcal U}\mathcal P(\gamma)$.
The support theorem itself assumes a minimizer and proves a property of it;
it does not separately supply one. See [OpenAI (2026a), §§1–2][fs-main]
and [Auffinger and Chen (2017), Theorem 1 and proof of Lemma 3][ac2017].
<!-- /passage:model -->

<!-- passage:targets -->
Write $u=\Phi_x$, $a=\Phi_{xx}$, and
$dX_t=\gamma(t)u(t,X_t)\,dt+dB_t$, $X_0=0$.
The first result assumes an admissible minimizer. It constructs its
Stieltjes measure and an associated diffusion, proves
$\operatorname{supp}\mu_\gamma=[0,1)$ and strict increase of $\gamma$,
and obtains $\mathbb E u(t,X_t)^2=t$ and
$\mathbb E a(t,X_t)^2=1$ for every associated diffusion. The selected
formal statement has exactly this conditional scope; it does not assert a
smooth density.
Its [Lean implementation at the fixed source revision][support-main] implements the
[separately stated formal challenge][support-type]. The
[Comparator configuration][support-config] identifies the intended
comparison; the evidence retained with this draft does not establish
a successful research-target replay.

The second result concerns the scalar value. A bounded martingale ends
at a spin-valued random variable whose Brownian correlation represents
$P_*$. Finite Gaussian coefficients approximate that correlation at each
fixed $T<1$, followed by $T\uparrow1$. Its formal statement is separate
and retains the minimizer and diffusion hypotheses where needed. The QAOA
theorem goes further: for each requested accuracy it selects one finite
deterministic circuit, independent of size and disorder, whose limiting
expected energy approaches $P_*$. Neither formal statement asserts that
circuit conclusion.
The scalar clauses are in a [separate Lean implementation][value-main], with their
own [formal challenge][value-type] and [Comparator configuration][value-config].
Those links identify the selected statements, not a completed replay
receipt for either research target.
<!-- /passage:targets -->

<a id="argument-map"></a>

## 2. Dependencies and prior work

<!-- passage:dependencies -->

### 2.1 What each stage supplies

The proof begins with regularity on strips bounded away from terminal
time. It makes the gradient diffusion and its moment function $q$
available, so a first variation can show where the minimizer is in
contact. On a constant interval, the shape inequalities and the rational
certificate give the strict curvature needed to contradict that contact.
The zero-interval case uses a separate heat argument, and the possible
terminal plateau needs its own exclusion. These steps lead to full support
and the two moment equalities.

In this manuscript route, the value argument then uses bounded-martingale convergence and
the attained Parisi formula to express $P_*$ as a terminal Brownian
correlation and an integral of expected curvature. Section 6 defines
the terminal martingale variable and proves these equalities.
The fixed-$T$ Gaussian approximation recovers this integral through
Euler coupling, orthogonal normalization and mean-preserving rounding.
The QAOA theorem additionally requires rooted energy identification,
classical synthesis, removal of temporary seeds and transfer to fixed
angles. Sections 3–9 explain the transitions in that order. The original analytic details are in [OpenAI (2026a), §§2–7][fs-main],
and the circuit construction is in [OpenAI (2026b), §§2–6][q-intro].

The density theorem in §§5.1–5.2 is a further consequence of support and
the PDE, not a premise of the scalar or circuit construction. The
positive-temperature route in §9.7 independently supplies the same bounded
classical input used for synthesis. The probability consequence in §9.8
requires a separate fixed-word second-moment theorem. These branches
explain why the two selected formal statements are not a formal proof of
the complete circuit theorem.

### 2.2 The regularity available before the proof starts

On each fixed strip $[0,T]\times\mathbb R$, $T<1$, the source gives
bounded, jointly continuous spatial derivatives of every positive finite order,
and uniform convergence of these derivatives under $L^1$ coefficient
approximation with smooth terminal data. Time derivatives need only exist
almost everywhere across coefficient jumps. On an open constant interval,
the heat formula supplies the additional time smoothness used in §4.
The terminal estimate is
$$
|x|\le\Phi_\gamma(t,x)
\le |x|+\sqrt{2(1-t)/\pi}+\frac12\int_t^1\gamma(s)\,ds.
$$
It controls approach to $|x|$ without differentiating that cusp. The strip
estimates justify the interior calculations and finite meshes; the terminal
bound and integrability justify the later endpoint limits. The two roles
must remain separate. [OpenAI (2026a), §2][fs-reg].

The hypotheses also have distinct uses. Zero field supplies evenness,
$u(0,0)=0$ and reflection in the shape argument. The convention
$\xi''=1$ fixes the curvature coefficients. Monotonicity gives bounded
coefficients before time one and nonnegative coefficient jumps; it also
turns a support gap into a constant interval. Integrability controls
terminal tails and Fubini interchanges, while local finiteness of the
Stieltjes measure is enough for compact mass removal. Minimality first
enters through the variational inequality in §3; the constant-interval
curvature estimate itself applies to an admissible coefficient without
assuming it is a minimiser. [OpenAI (2026a), §§1–2][fs-main];
[OpenAI (2026a), §2][fs-reg]; [OpenAI (2026a), §6][fs-var].

### 2.3 Which prior results play which role

The imported ground-state formula supplies two facts with different uses. Auffinger and Chen's Theorem 1 identifies the ground-state limit with an infimum over $\mathcal U$. To choose a coefficient attaining that infimum, one must also use their construction in the proof of Lemma 3. In the cited arXiv v2, the theorem is on p. 3, the compactness construction is on pp. 7–9, and the lower-bound proof is on pp. 11–12.

Here is the part of that construction which supplies the witness. Let $\alpha_\beta$ be a positive-temperature Parisi distribution function. The source bounds $\beta\alpha_\beta(t)$ uniformly on each interval ending before one. Helly selection and a diagonal subsequence produce a nonnegative, nondecreasing right-continuous limit $\gamma_0$. In the SK normalization, the source's weighted integral bound also controls $\int_0^1\beta\alpha_\beta(t)\,dt$. For every nonnegative nondecreasing $h$, splitting at $1/2$ gives $\int_0^1 h(t)\,dt\le4\int_0^1t h(t)\,dt$: the first half is bounded by $h(1/2)/2$, and on the second half $t\ge1/2$. Fatou's lemma then gives $\gamma_0\in\mathcal U$.

Mass can concentrate at time one during this limit, so compact convergence alone does not identify the limiting control problem. Write the limiting measure of the time coefficients as
$$
\nu_0(dt)=\gamma_0(t)\,dt+m\delta_1(dt),\qquad m\geq0.
$$
For an arbitrary admissible control, let $S$ denote its terminal state with coefficient $\gamma_0$. To see why the terminal choice is admissible, let the original control be
$\alpha$ and put $S_s=B_s+\int_0^s\gamma_0(r)\alpha_r\,dr$.
For a cutoff $\tau<1$ use $\alpha_s$ before $\tau$ and
$g_k(S_s)$ afterwards, where $g_k$ is a continuous function bounded by
one and converging pointwise to the sign with $\operatorname{sgn}(0)=1$.
This control uses only information available at time $s$. At fixed
$\tau,k$, first take the temperature limit; then let $\tau\uparrow1$
and $k\to\infty$. The continuous terminal evaluation has thereby
approached $\operatorname{sgn}(S)$ without anticipating a future state. The endpoint atom then contributes
$$
|S+m\operatorname{sgn}(S)|-|S|=m
$$
to the reward and
$$
\tfrac12m\bigl(\operatorname{sgn}(S)^2+1\bigr)=m
$$
to the combined control and Parisi penalties. These contributions cancel. Taking the supremum over the remaining controls proves $P_*\geq\mathcal P(\gamma_0)$. The upper bound proved earlier in that paper gives $P_*\leq\inf_{\gamma\in\mathcal U}\mathcal P(\gamma)$. Therefore
$$
P_*\leq\inf_{\gamma\in\mathcal U}\mathcal P(\gamma)
\leq\mathcal P(\gamma_0)\leq P_*.
$$
Thus $\gamma_0$ attains the infimum. The cancellation is a step in the imported existence proof; it is not an additional assumption about the Stieltjes measure $d\gamma_0$. In particular, $\nu_0$ here is the limit of coefficient-times-Lebesgue measures, not the order parameter's Stieltjes measure. The two measures must not be identified. [Auffinger and Chen, arXiv:1606.05335v2, pp. 7–12][ac17].

The cited theorem is stated for the almost-sure normalized maximum. Its expected-value formulation used here follows from Gaussian concentration. For
$L_n=n^{-1}\max_\sigma H_n(\sigma)$, the Lipschitz constant in the Gaussian couplings is
$\sqrt{(n-1)/(2n^2)}$. Hence $L_n-\mathbb E L_n\to0$ in probability. Since the almost-sure limit is the deterministic Parisi value, the deterministic sequence $\mathbb E L_n$ has the same limit. The full-support theorem below remains conditional on a minimizer; neither of the selected formal interfaces constructs one. [OpenAI full-support manuscript, Introduction, ground-state formula and its footnote][fs-main].

Auffinger–Chen–Zeng's infinite support does not exclude an interior gap.
Their terminal-plateau observation anticipates one endpoint obstruction;
the argument below supplies the quantitative boundary-layer proof used here.
The full-support manuscript develops a rational coercivity route and credits
Chen's 2026 theorem for the same full-support conclusion and smooth absolute
continuity. Chen's Proposition 4.2 has the conditional crossing form
$q''(t)=0\Rightarrow q'''(t)>0$; the cited rational certificate gives $q'''(t)>0$
throughout a positive constant interval. These are different sufficient
mechanisms, and this record makes no priority claim for full support.
[Auffinger, Chen and Zeng (2020), Theorem 1 and Remark 7][acz];
[Chen (2026), Theorem 1.3 and Proposition 4.2][chen2026];
[OpenAI (2026a), §§1–2][fs-main]. The transformed
density comparisons also have antecedents in Lopatto's positive-temperature
analysis and Chen's zero-temperature analysis; the rational coercive
identity is the different step in the full-support proof. Zhou's positive-temperature
interval-support result applies near the critical temperature, whereas
Lopatto's cited theorem covers the low-temperature zero-field phase.
Neither transfers full Stieltjes support to zero temperature on its own:
for the minimizers, $\beta\mu_\beta$ converges vaguely on $[0,1)$ to
the zero-temperature Stieltjes measure, while the unscaled Parisi
probability measures converge weakly on $[0,1]$ to $\delta_1$.
These are different measures and topologies. Convergence
without an interval-specific lower bound can lose support information.
The direct zero-temperature gap proof
below is therefore essential. [Chen (2026), Remarks 1.4–1.5][chen2026];
[OpenAI (2026a), §§1–2][fs-main].

Two later editions sharpen the comparison without entering the pinned
September proof. [Lopatto, arXiv:2607.11756v4, Proposition 5.1 and
(5.8)–Corollary 5.6](https://arxiv.org/abs/2607.11756v4), proves a
conditional curvature crossing on a positive constant interval. Its
integrating factor makes a transformed curvature derivative strictly
increasing, so the associated contact derivative decreases and then
increases; it does not assert an unconditional positive third derivative.
[Lopatto, arXiv:2610.00127v1, Theorem 2.3 and §8](https://arxiv.org/abs/2610.00127v1),
works at positive temperature and positive external field. Its comparison
requires one-sided bounds on the coefficient before and after the chosen
time, a moment inequality and a stationarity equality. The subsequent
moment bootstrap yields smooth, strictly positive density on a nontrivial
support interval; a singleton support is a separate case. Neither theorem
removes the hypotheses of the zero-temperature argument below.

Here is an explicit example of the information lost in such a limit.
It concerns admissible measures, not Parisi minimizers. Put
$g=\mathbf1_{[0,1/3]\cup[2/3,1)}$ and $q_n=1-n^{-2}$, and for $n\ge2$ define
$$
\mu_n(dt)=\frac{g(t)+n^{-1}}n\mathbf1_{[0,q_n]}(t)\,dt
+\left(1-\frac1n\int_0^{q_n}(g(t)+n^{-1})\,dt\right)\delta_{q_n}(dt).
$$
The continuous part has mass at most $(2/3+1/n)/n<1$, so these are
probability measures with a positive endpoint atom. Their density is
positive throughout $[0,q_n]$, giving $\operatorname{supp}\mu_n=[0,q_n]$.
Their continuous mass tends to zero and $q_n\to1$, hence
$\mu_n\Rightarrow\delta_1$ weakly on $[0,1]$.
For a compactly supported continuous test function on $[0,1)$, the endpoint
atom eventually lies outside its support. Consequently
$n\mu_n\to g(t)\,dt$ vaguely there, although the limit vanishes on
$(1/3,2/3)$. Even the cumulative coefficients converge in the topology
used for the PDE: with $\gamma_n(t)=n\mu_n([0,t])$ and
$\gamma(t)=\int_0^t g(s)\,ds$, their difference is $t/n$ below $q_n$,
and $\gamma_n=n$ on the terminal strip of length $n^{-2}$. Thus
$$
\|\gamma_n-\gamma\|_{L^1(0,1)}\le\frac1{2n}+\frac1n\longrightarrow0.
$$
Every $\gamma_n$ is admissible, but $d\gamma$ has an interior gap.
Minimality and the gap argument supply information that these convergences
alone do not. An atom added at time one is likewise invisible to the
coefficient on $[0,1)$ and hence to its PDE and variational functional;
the zero-temperature problem does not select an endpoint mass.

Control and gradient-martingale methods have antecedents in
[Auffinger–Chen](https://doi.org/10.1007/s00220-014-2254-z) and
[Jagannath–Tobasco](https://arxiv.org/abs/1502.04398v4). A finite-temperature
theorem with smooth terminal value $\log\cosh$ does not alone establish
the result with terminal cusp $|x|$. The required compact-strip and
terminal estimates are supplied in [OpenAI (2026a), §2][fs-reg];
[Chen–Handschy–Lerman](https://arxiv.org/abs/1609.04368v4) supplies earlier
zero-temperature regularity, control and uniqueness results (Theorem 4
for uniqueness). This is distinct from the earlier finite-temperature
uniqueness result of Auffinger and Chen.
[Montanari](https://arxiv.org/abs/1812.10897v2) and
[El Alaoui–Montanari–Sellke](https://arxiv.org/abs/2001.00904v1) inform
normalised discretisation and optimisation. The particular shifted Gaussian
coefficient identity used here is proved in [OpenAI (2026a), §7][fs-cons].
<!-- /passage:dependencies -->

### 2.4 Recovering the compact-strip estimates

<!-- passage:strip-recovery -->
The curvature argument needs estimates uniform over the approximating
coefficients. Here is the route from the control formula to those estimates;
all bounds are taken on a fixed strip ending before time one.

For finite-step coefficients and a smooth, even, convex, one-Lipschitz
terminal function $\psi$, the evolution through a step of height $c$ is
$$
\Phi(t,x)=
\begin{cases}
c^{-1}\log P_{b-t}(e^{c\Phi(b,\cdot)})(x),&c>0,\\
P_{b-t}\Phi(b,\cdot)(x),&c=0,
\end{cases}
$$
where $P_h$ denotes convolution with a centred Gaussian of variance $h$.
The heat formula preserves evenness, convexity and the spatial Lipschitz
bound. Along a controlled path $dY_s=\gamma(s)\alpha_s\,ds+dB_s$, the drift
of the value minus the accumulated control cost is
$-\gamma(s)(\alpha_s-\Phi_x(s,Y_s))^2/2$. It is nonpositive, and is zero
for the feedback control. This proves the stated control formula for the
smooth step problem, including attainability by its feedback diffusion.

Using the same control in two such problems and then taking suprema gives
$$
\|\Phi_{\gamma,\psi}-\Phi_{\widetilde\gamma,\widetilde\psi}\|_\infty
\le \|\psi-\widetilde\psi\|_\infty
       +\frac32\|\gamma-\widetilde\gamma\|_{L^1(0,1)}.
$$
The drift part costs at most the coefficient difference in $L^1$, by the
terminal Lipschitz bound; the quadratic cost contributes another half of
that difference. The supremum norm is of the difference of the values,
which is bounded even though each value grows linearly in $x$.
With $\psi_M(x)=M^{-1}\log(2\cosh Mx)$,
$0\le\psi_M-|x|\le(\log2)/M$. Choose simultaneously $\gamma_m\to\gamma$ in $L^1$ and $M_m\to\infty$.
These are two distinct requirements: $M_m\ge\|\gamma_m\|_\infty$ alone
does not force terminal convergence. This compatible approximation
determines a unique uniform limiting value. Its terminal bound,
given in §2.2, also follows directly: choose the zero control for the lower
bound, and use $|\alpha|-\alpha^2/2\le1/2$ for the upper bound.

To obtain spatial derivatives, choose $T<b<1$. Monotonicity gives the
uniform coefficient estimate
$$
\gamma(t)\le\frac{\|\gamma\|_1}{1-b}\quad(0\le t\le b).
$$
An $L^1$-convergent family thus has a common coefficient bound $\Gamma$ on
this larger strip. For its smooth step approximants, put $U=\Phi_x$.
The differentiated mild equation is
$$
U(t)=P_{b-t}U(b)+\int_t^b\gamma(s)P_{s-t}[U(s)U_x(s)]\,ds.
$$
Since $\|U\|_\infty\le1$ and
$\|\partial_xP_hF\|_\infty\le Ch^{-1/2}\|F\|_\infty$,
$$
\|U_x(t)\|_\infty\le\frac C{\sqrt{b-t}}
 +C\Gamma\int_t^b\frac{\|U_x(s)\|_\infty}{\sqrt{s-t}}\,ds.
$$
Substituting this inequality once into its own integral uses
$\int_t^s((r-t)(s-r))^{-1/2}\,dr=\pi$. It reduces the estimate to an
ordinary backward Gronwall inequality with integrable forcing. This bounds
$U_x$ uniformly on $[0,T]$ without any terminal derivative bound. Repeating
on successively smaller strips bounds each higher spatial derivative: put
one derivative on the heat kernel and the rest on $UU_x$; only the term
$U\partial_x^mU$ contains the new highest derivative. The remaining products
have already been bounded.

Uniform convergence of the values then yields convergence of every
positive spatial derivative. For a bounded twice differentiable difference
$F$ with bounded second derivative, Taylor's formula gives
$$
\|F'\|_\infty\le \frac{2\|F\|_\infty}{h}
                         +\frac h2\|F''\|_\infty\qquad(h>0).
$$
First choose $h$ small using the common second-derivative bound, then make
$\|F\|_\infty$ small. Iterate on derivative differences. Passing to the
integral form of the differentiated PDE proves local absolute continuity
in time and its almost-everywhere equations. No classical time derivative
at a coefficient jump, and no derivative of $|x|$ at its cusp, is being
assumed.

Finally, couple all feedback diffusions with the same Brownian motion.
On $[0,T]$, let $L$ be a common spatial Lipschitz bound for their drifts.
The difference of the two integral equations gives, for example,
$$
\sup_{s\le T}|X_s^n-X_s|
\le e^{LT}\left(\|\gamma_n-\gamma\|_1
 +\|\gamma_n\|_1\|u_n-u\|_{\infty,[0,T]\times\mathbb R}\right)
 \longrightarrow0.
$$
This is a deterministic bound under the coupling. The derivative bounds
one order higher ensure uniform continuity when derivatives are evaluated
at these moving points. Every fixed polynomial in the bounded derivatives
therefore converges in expectation. This is precisely the convergence
needed for the integrated curvature expression in §4; none of the forward
density scores or their quotients need converge.
[OpenAI (2026a), Lemmas 2.1–2.3][fs-reg].
<!-- /passage:strip-recovery -->

<!-- passage:approximation-choices -->

### 2.5 The approximation choices used below

The same symbol for a small error must not conceal changing background
objects. The following account fixes those objects before the indicated
limit. A single admissible minimiser and its associated diffusion are
retained throughout the scalar construction.

| Step | Objects held fixed | Approximation and its control |
| --- | --- | --- |
| Compact-strip regularity | Derivative order $k\ge1$, $T<1$, and a common coefficient $L^1$ bound | Coefficients converge in $L^1$ within the mass bound; spatial derivatives converge uniformly on the strip. |
| Shape inequalities on a plateau | Plateau height $c>0$ and a closed interior neighbourhood | Choose step coefficients equal to $c$ there and smooth terminal values with $M_m\ge\|\gamma_m\|_\infty$, $M_m\to\infty$. Coefficient and terminal approximations may be chosen as one compatible sequence. |
| First variation | $\gamma$, a feasible $\eta\in L^1$, and initially $\epsilon>0$ | Remove the terminal cutoff, then let $\epsilon\downarrow0$. The terminal remainder divided by $\epsilon$ is bounded by an $L^1$ tail of $\eta$. |
| Terminal value | The chosen minimiser and diffusion | Use bounded-martingale convergence and integrability of $\gamma$ as $t\uparrow1$; no terminal derivative bound is needed. |
| Finite Gaussian coefficients | $\gamma,X$ and $T<1$ | Refine $N$ using fixed-strip bounds; then control the remaining value tail by $1-T$. |

For the plateau transfer, tail estimates for a fixed approximant may depend
on that approximant. The passage to the limit uses the integrated
polynomial in $v,w,z$ and the common strip bounds; it does not require
uniform bounds on the auxiliary density scores. Sections 3 and 4 explain
the variation and plateau-transfer arguments, and §7 gives a complete scalar error
budget. The further choices used to produce a circuit appear in §9.6.
[OpenAI (2026a), Lemma 2.1, Lemma 6.1, Proposition 5.1 and
Proposition 7.2][fs-main].
<!-- /passage:approximation-choices -->

<a id="variational-signs"></a>

## 3. From minimality to contact

<!-- passage:contact -->
The minimisation takes place over nonnegative Stieltjes measures with an
integrable cumulative function. Their total mass is free. We first derive
the variation of the functional, then use changes of measure which preserve
this admissible class. The result will be contact on the *existing* support;
the exclusion of gaps comes afterwards.

### 3.1 The moment function before minimisation

Fix any $\gamma\in\mathcal U$, without yet assuming that it minimises
$\mathcal P$. Compact-strip regularity and Itô's formula give
$$
u(t,X_t)=\int_0^t a(s,X_s)\,dB_s,\qquad
q(t):=\mathbb E u(t,X_t)^2
     =\int_0^t\mathbb E a(s,X_s)^2\,ds.
$$
The initial term vanishes because zero field makes $\Phi$ even and
$u(0,0)=0$. Thus $q(0)=0$, $0\le q(t)\le1$, and
$$
q'(t)=\mathbb E a(t,X_t)^2\qquad(0\le t<1),
$$
with a right derivative at zero. The integrand is continuous on each
compact time strip, so $q\in C^1[0,1)$. These facts hold for every
admissible coefficient. They do not yet say that $q(t)=t$.
The source proves them by smooth approximation on $[0,T]$, $T<1$;
it never differentiates the terminal cusp $|x|$ at time one.
[OpenAI (2026a), Lemmas 2.1–2.2][fs-reg].

### 3.2 The feasible right derivative

Let $\eta\in L^1(0,1)$ and suppose that
$\gamma+\varepsilon\eta\in\mathcal U$ for
$0\le\varepsilon\le\varepsilon_0$, where $\varepsilon_0>0$.
This is a feasibility hypothesis: an arbitrary signed bump in $\gamma$
need not preserve monotonicity. Since $\mathcal U$ is convex, it is enough
to check that the endpoint $\gamma+\varepsilon_0\eta$ is admissible.

For $0<\varepsilon\le\varepsilon_0$, put
$\beta=\gamma+\varepsilon\eta$,
$\widetilde u=\Phi_{\beta,x}$ and $D=\Phi_\beta-\Phi_\gamma$.
Subtracting the two PDEs gives
$$
D_t=-\frac12D_{xx}
    -\frac12\beta(\widetilde u+u)D_x
    -\frac{\varepsilon}{2}\eta u^2.
$$
The choice of diffusion
$$
dY_t^\varepsilon
 =\frac12\beta(t)(\widetilde u+u)(t,Y_t^\varepsilon)\,dt+dB_t,
\qquad Y_0^\varepsilon=0,
$$
cancels the first-order spatial term when Itô's formula is applied to
$D(t,Y_t^\varepsilon)$. Its drift has absolute value at most $\beta(t)$,
which is integrable. On $[0,T]$ the resulting identity is
$$
D(0,0)=\mathbb E D(T,Y_T^\varepsilon)
 +\frac{\varepsilon}{2}\int_0^T
       \eta(t)\mathbb E[u(t,Y_t^\varepsilon)^2]\,dt.
$$
At coefficient jumps the time derivatives need only exist almost
everywhere. The source obtains this identity by approximating both
coefficients by monotone step functions with the same smooth terminal
datum, and then passing to the limit using the compact-strip estimates.

The control representation, applied with the same control on each side,
gives the time-local difference bound
$$
\sup_x|D(T,x)|\le\frac{3\varepsilon}{2}
                         \int_T^1|\eta(t)|\,dt.
$$
Hence $T\uparrow1$, at fixed $\varepsilon$, removes the terminal term
even after division by $\varepsilon$. We obtain the exact finite-change
identity
$$
\frac{\Phi_{\gamma+\varepsilon\eta}(0,0)-\Phi_\gamma(0,0)}
     {\varepsilon}
 =\frac12\int_0^1\eta(t)
                       \mathbb E[u(t,Y_t^\varepsilon)^2]\,dt.
$$
As $\varepsilon\downarrow0$, the coefficients converge in $L^1$ and have
uniformly bounded $L^1$ norms. On each fixed strip, their gradients converge
uniformly and have common spatial Lipschitz bounds. Coupling with the same
Brownian motion and applying Gronwall's inequality therefore gives
$Y^\varepsilon\to X$ uniformly on that strip. The integrand converges to
$\eta(t)q(t)$ for each $t<1$, and its absolute value is at most
$|\eta(t)|$. Dominated convergence, followed by subtraction of the linear
Parisi penalty, now yields
$$
D_+\mathcal P(\gamma)[\eta]
 :=\lim_{\varepsilon\downarrow0}
     \frac{\mathcal P(\gamma+\varepsilon\eta)-\mathcal P(\gamma)}
          {\varepsilon}
 =\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$
If $\gamma$ is a minimiser, this derivative is nonnegative for every
feasible direction. It need not vanish: the minimisation has one-sided
constraints. [OpenAI (2026a), Lemma 6.1, equations (6.1)–(6.2)][fs-var].

### 3.3 Which changes of measure are allowed?

Write $\mu=\mu_\gamma$ and $S=\operatorname{supp}\mu$, with support
relative to $[0,1)$. Tonelli's theorem gives the useful identity
$$
\int_0^1\gamma(t)\,dt
 =\int_{[0,1)}\!\int_s^1dt\,\mu(ds)
 =\int_{[0,1)}(1-s)\,\mu(ds)<\infty.
$$
This is weighted finiteness, not a bound on $\mu([0,1))$. In particular,
there is no normalisation constraint requiring mass added at one point to
be removed elsewhere.

Define the tail potential
$$
G(s)=\int_s^1(q(t)-t)\,dt\qquad(0\le s<1).
$$
It is continuous, satisfies $|G(s)|\le1-s$, and has
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$ on compact strips, with one-sided
interpretations at zero. The following two competitors suffice.

| Change to the Stieltjes measure | Direction in the cumulative function | Allowed parameter | Consequence at a minimiser |
| --- | --- | --- | --- |
| Add $\varepsilon\delta_s$, $0\le s<1$ | $\eta(t)=\mathbf1_{[s,1)}(t)$ | $\varepsilon\ge0$ | $G(s)\ge0$ |
| Remove $\varepsilon\nu$, where $\nu=\mu|_K$ and $K\subset[0,1)$ is compact | $\eta_K(t)=-\nu([0,t])$ | $0\le\varepsilon\le1$ | $\int_KG(s)\,\mu(ds)\le0$ |

For atom addition, the new cumulative function is nonnegative,
nondecreasing and right-continuous. Its integral increases by
$\varepsilon(1-s)$, so it remains in $\mathcal U$. This includes $s=0$:
an atom there adds a constant to $\gamma$ on all of $[0,1)$. The point
$1$ is outside the measure's domain and is not an additional competitor.
The derivative formula gives
$D_+\mathcal P(\gamma)[\mathbf1_{[s,1)}]=G(s)/2$, proving
$G\ge0$ everywhere below one.

For removal, choose $T<1$ with $K\subset[0,T]$. Then
$\nu(K)\le\gamma(T)<\infty$. The measure
$\mu-\varepsilon\nu$ is nonnegative for $0\le\varepsilon\le1$,
so its cumulative function is nonnegative, nondecreasing and
right-continuous. It lies between zero and $\gamma$, hence is integrable;
also $|\eta_K|\le\nu(K)$. Fubini is justified quantitatively by
$$
\int_K\!\int_s^1|q(t)-t|\,dt\,\mu(ds)
 \le\int_K(1-s)\,\mu(ds)\le\nu(K)<\infty.
$$
It follows that
$$
0\le D_+\mathcal P(\gamma)[\eta_K]
 =-\frac12\int_0^1\nu([0,t])(q(t)-t)\,dt
 =-\frac12\int_KG(s)\,\mu(ds).
$$
Since $G\ge0$, its integral on every compact $K$ is zero. The compact
intervals $[0,T]$ exhaust $[0,1)$, so $G=0$ $\mu$-almost everywhere.
If a support point $s$ had $G(s)>0$, continuity would give a relative
neighbourhood on which $G$ stays positive. After restricting to a compact
interval containing that neighbourhood, the defining property of support
would give it positive $\mu$-mass, contradicting the zero integral.
Therefore
$$
G(s)=0\qquad(s\in S).
$$
This step applies to atoms, diffuse mass and singular continuous mass.
Removing individual atoms alone would not establish it.
[OpenAI (2026a), Lemma 6.2][fs-var].

### 3.4 Contact values and endpoint slopes

At $s\in S\cap(0,1)$, the function $G$ has an interior minimum of
value zero. Thus $G'(s)=0$ and $G''(s)\ge0$, giving
$$
q(s)=s,\qquad q'(s)\le1.
$$
If $0\in S$, the argument needs the zero-field initial condition in
addition to the one-sided minimum. We have $G(0)=0$ and $q(0)=0$, so
$$
G(h)=G(0)+\int_0^h(t-q(t))\,dt
     =\frac12(1-q'(0))h^2+o(h^2).
$$
Nonnegativity for $h>0$ implies $q'(0)\le1$. This works whether or not
zero is an atom. The equality $q(0)=0$ comes from symmetry, rather than
from differentiating a one-sided minimum. If $0\notin S$, no condition
$G(0)=0$ has been obtained or used.
[OpenAI (2026a), Lemma 6.2][fs-var].

We have now proved, without any no-gap assumption,
$$
G\ge0\text{ on }[0,1),\qquad G=0\text{ on }S,\qquad
q(s)=s\text{ and }q'(s)\le1\text{ for }s\in S.
$$
These are precisely the contact data used in §5. They make no assertion
that every zero of $G$ belongs to $S$, or that $q(t)=t$ at a point outside
$S$. Terminal, interior and initial gaps remain to be excluded.

### 3.5 What the first-order criterion does, and does not, establish

For the actual moment function associated with $\gamma$, the two
potential conditions $G\ge0$ and $G=0$ on $S$ are also sufficient for
minimality. This ordinary deduction explains exactly how much variational
information has been extracted. For another admissible coefficient
$\beta$, let $\nu=\mu_\beta$. The weighted identity above and
$|G(s)|\le1-s$ make both measure integrals absolutely convergent, even
when either measure has infinite total mass. Fubini gives
$$
2D_+\mathcal P(\gamma)[\beta-\gamma]
 =\int_{[0,1)}G(s)\,\nu(ds)
  -\int_{[0,1)}G(s)\,\mu(ds)\ge0.
$$
Here the second integral is zero because $\mu$ is concentrated on its
relative support. The control formula also shows that $\mathcal P$ is
convex in its coefficient: for a fixed control, the terminal absolute
value is convex in the coefficient and both penalties are linear; taking
the supremum over the same control class preserves convexity. Therefore
$$
\mathcal P(\beta)-\mathcal P(\gamma)
 \ge D_+\mathcal P(\gamma)[\beta-\gamma]\ge0.
$$
This proves the converse. It agrees with the chord optimality criterion
of [Chen, Handschy and Lerman, arXiv:1609.04368v4, Proposition 4,
printed p. 14](https://arxiv.org/abs/1609.04368v4).
Chen's zero-temperature treatment obtains the same contact integral by
testing $0$ and $2\gamma$ and then using weighted Fubini
[Chen (2026), Proposition 3.2, equations (3.11)–(3.12)][chen2026].
The compact-removal proof above keeps the local mass operation explicit.

The converse concerns $G$ built from the PDE and diffusion of the same
$\gamma$. It does not say that an arbitrary curve with these contact
properties comes from a Parisi solution. Nor does it prove full support:
the missing input is the strict curvature on an interval where the
coefficient is constant, established next. The formal chord statement and
the ordinary derivative bridge are distinguished in §8.1.
<!-- /passage:contact -->

<a id="curvature-and-gap-certificate"></a>

## 4. Strict curvature on a constant interval

<!-- passage:curvature -->
The gap argument needs a property of the derivative $q'$, rather than
convexity of the spatial function $\Phi$. We establish the following
analytic input before using minimality. Let $\gamma\in\mathcal U$ be
constant with value $c$ on an open interval $I\subset(0,1)$, and let $X$
be its diffusion started at zero. Then

$$
\begin{cases}
q'''(t)\ge \dfrac1{1000c^2}
  \mathbb E\bigl[(c\Phi_{xx}(t,X_t))^4\bigr]>0,&c>0,\\[4pt]
q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0,&c=0,
\end{cases}\qquad t\in I.
$$

Thus $q'$ is strictly convex for $c>0$ and strictly increasing for
$c=0$. The coefficient may jump outside $I$ and may be unbounded near
one, provided it is nonnegative, nondecreasing, right-continuous and
integrable. No support property or minimising assumption enters this
statement. The positive-time restriction matters when a diffusion
density is used; interval endpoints are handled later by continuity.
[OpenAI (2026a), Proposition 5.1][fs-curv].

We first calculate for a positive monotone finite-step coefficient and
smooth terminal data. For those data, the shape comparisons and boundary
estimates justify an exact polynomial correction with zero expectation.
We then pass the integrated inequality to the original coefficient and
establish its strictness. This order keeps each analytic premise separate
from the finite algebra which uses it.

### 4.1 Why the uncorrected expression has no pointwise sign

On a positive constant interval put
$r=c\Phi_x$, $v=r_x$, $w=r_{xx}$ and $z=r_{xxx}$.
In forward time,
$r_t=-\tfrac12r_{xx}-rr_x$ and $dX_t=r(t,X_t)\,dt+dB_t$.
Differentiating the PDE and applying Itô's formula gives

$$
dr(t,X_t)=v(t,X_t)\,dB_t,
$$
$$
dv(t,X_t)=-v(t,X_t)^2\,dt+w(t,X_t)\,dB_t,
\qquad
dw(t,X_t)=-3v(t,X_t)w(t,X_t)\,dt+z(t,X_t)\,dB_t.
$$

Since $q'=c^{-2}\mathbb E v^2$, the drift of $v^2$ yields
$c^2q''=\mathbb E(w^2-2v^3)$. The drifts of $w^2$ and $v^3$ are,
respectively, $z^2-6vw^2$ and $3vw^2-3v^4$. Therefore

$$
c^2q'''=\mathbb E\bigl[z^2-12vw^2+6v^4\bigr].
$$

These are interior-time identities. On a smaller constant interval the
heat formula gives classical time smoothness and bounded spatial
derivatives of sufficiently high order, so the local martingale terms
have zero mean and the expectation differentiations are justified.
Nothing here assigns a sign to $q''$.
[OpenAI (2026a), Lemma 2.3][fs-reg].

There is a concrete obstruction to reading the last display pointwise.
For the smooth finite-step problem $c=M=1$ on $[0,1)$, with terminal
value $\log(2\cosh x)$, the exact solution is

$$
\Phi(t,x)=\log(2\cosh x)+\frac{1-t}{2},\qquad r=\tanh x.
$$

Indeed, $\Phi_{xx}+\Phi_x^2=1$. Writing $R=r^2$ gives
$v=1-R$, $w=-2rv$ and $z=-2v^2+4Rv$. At $R=1/2$,
$v=1/2$, $w^2=1/2$ and $z=1/2$, so

$$
z^2-12vw^2+6v^4=-\frac{19}{8}<0.
$$

This example lies in the smooth analytic class used below. Its diffusion
density is $f_t(x)=e^{-t/2}\cosh(x)p_t(x)$, obtained from the heat
transition formula, and integrates to one because
$\mathbb E\cosh(B_t)=e^{t/2}$. It illustrates the necessity of the
integration argument; it uses a smooth terminal value and makes no claim
to be the zero-temperature minimiser. The displayed negative value is an
exact elementary calculation. The heat formula itself is
[OpenAI (2026a), Lemma 2.1][fs-reg].

### 4.2 The smooth finite-step problem and its boundary control

Take $0=t_0<\cdots<t_N=1$,
$0<c_1\le\cdots\le c_N\le M$, and
$\gamma(t)=c_i$ on $[t_{i-1},t_i)$. The terminal value is
$M^{-1}\log(2\cosh Mx)$. On a step of height $c$, set $l=c\Phi$ and
$h=e^l$. Then $h_t=-\tfrac12h_{xx}$. For $a<t$ in that step the
diffusion transition density is

$$
p_{t-a}(x-y)\frac{h(t,x)}{h(a,y)},\qquad
p_t(x)=(2\pi t)^{-1/2}e^{-x^2/(2t)}.
$$

Its mass is one by $h(a,\cdot)=P_{t-a}h(t,\cdot)$. Factoring the
positive-time density as $f=e^l g$ gives $g_t=\tfrac12g_{xx}$ on each
step. Put $s=-\partial_x\log g$. On the first step,
$g(t,x)=p_t(x)e^{-l(0,0)}$ and $s=x/t$. At a forward jump
$\delta=c_+-c_-\ge0$, continuity of $f$ gives
$g_+=g_-e^{-\delta\Phi}$. The functions $r$ and $s$ are odd.
[OpenAI (2026a), §3, before Lemma 3.1][fs-signs].

The comparison arguments take place on unbounded spatial domains, so
the boundary estimates must precede the signs. For these fixed smooth
data, Gaussian convolution and the finite jump rules give, as
$x\to+\infty$,

$$
l(t,x)=cx+C(t)+O(e^{-\kappa x}),
$$
$$
g(t,x)=\exp\!\left(-\frac{x^2}{2t}+\beta(t)x+C_0(t)\right)
       (1+O(e^{-\kappa x})).
$$

The errors may be differentiated any fixed finite number of times;
the estimates are uniform on each closed step, with positive time
bounded away from zero for the forward estimate. Their constants may
depend on the step data. For example, after completing the square in a
Gaussian convolution, the error is an expectation at
$Y_x=\lambda x+b+\sqrt VZ$ with $\lambda$ bounded below by a positive
constant. Split at $Y_x=\mathbb EY_x/2$. The first part inherits the
exponential tail; on the second, the Gaussian probability dominates the
permitted exponential growth of the error and all its specified
derivatives. This proves the differentiated estimates by finite induction
through heat evolution and jumps. In particular,
$s=x/t-\beta(t)+O(e^{-\kappa x})$, $s_x=1/t+O(e^{-\kappa x})$ and
$s_{xx}=O(e^{-\kappa x})$.
[OpenAI (2026a), Lemma 3.1][fs-signs].

The comparison principle used below is also explicit. If
$U_\tau-\tfrac12U_{xx}-bU_x-dU\ge0$ on a compact cylinder,
$d\le C$, the initial values are nonnegative and the lateral values are
at least $-\varepsilon$, then
$U\ge-\varepsilon e^{(\max(C,0)+1)(\tau-\tau_0)}$.
Multiply by the corresponding decreasing exponential and apply the
minimum principle. Exhaustion is legitimate when the upper bound for
$d$ is independent of the cylinder and the lateral errors tend to zero.
The first-order coefficient need only be bounded on each cylinder.
This observation permits the $1/x$ coefficients which appear below.
[OpenAI (2026a), comparison preceding Lemma 3.2][fs-signs].

### 4.3 Backward and forward comparisons, including jumps

Use backward time $\tau$ on a single step. The equation is
$r_\tau=\tfrac12r_{xx}+rr_x$. The logarithmic heat formula preserves
strict positivity of $v$: its second spatial derivative is the tilted
mean of the old second derivative plus the tilted variance of the old
first derivative. Initially $v=cM\operatorname{sech}^2(Mx)>0$, and
positive rescaling at a backward jump preserves this property.
Consequently $r(x)>0$ for $x>0$.

Twice differentiating gives
$w_\tau=\tfrac12w_{xx}+rw_x+3vw$. At the terminal endpoint
$w=-2cM^2\operatorname{sech}^2(Mx)\tanh(Mx)\le0$ for $x>0$.
The boundary value at zero is zero, and the differentiated tails make
the far boundary tend uniformly to zero. Comparison applied to $-w$
gives $w\le0$ on the positive half-line.

Define

$$
H=\frac{r_\tau}{r}=\frac{w}{2r}+v.
$$

Oddness and $r_x(0)=v(0)>0$ make $w/r$, hence $H$, smooth and even
at zero. Direct differentiation gives

$$
H_\tau=\tfrac12H_{xx}+(v/r+r)H_x+vH,
$$
$$
(H_x)_\tau=\tfrac12(H_x)_{xx}+(v/r+r)(H_x)_x
             +((v/r)_x+2v)H_x+wH.
$$

The terminal signs are
$H=(cM-M^2)\operatorname{sech}^2(Mx)\le0$ and $H_x\ge0$ on
$x>0$, using $M\ge c$. For the first comparison write
$v/r+r=1/x+\eta(x)$, where $\eta$ is smooth and odd near zero.
The radial extension $H(|y|)$ to $\mathbb R^3$ turns
$\tfrac12H_{xx}+x^{-1}H_x$ into $\tfrac12\Delta H$.
It is smooth at the origin, as is the extra drift, and $H$ tends
uniformly to zero at infinity. Comparison on expanding balls proves
$H\le0$.

For the second comparison, $wH\ge0$ and
$(v/r)_x=w/r-v^2/r^2<0$, so the zeroth-order coefficient has upper
bound $2\sup v$. On $[\varepsilon,A]$, the two lateral errors are
$H_x(\varepsilon)=O(\varepsilon)$ and $H_x(A)=o_A(1)$, uniformly
on the closed step. Taking $\varepsilon\downarrow0$ and
$A\to\infty$ gives $H_x\ge0$. At a backward jump
$r_{\rm new}=\alpha r_{\rm old}$ with $0<\alpha\le1$,

$$
H_{\rm new}=H_{\rm old}-(1-\alpha)v_{\rm old},\qquad
(H_x)_{\rm new}=(H_x)_{\rm old}-(1-\alpha)w_{\rm old}.
$$

Thus both signs survive every jump.
[OpenAI (2026a), Lemma 3.2][fs-signs].

For the forward score use $a_s=s_x$, temporarily distinguishing it
from the Hessian $a=\Phi_{xx}$. The forward heat equation gives

$$
s_t=\tfrac12s_{xx}-ss_x,\qquad
(a_s)_t=\tfrac12(a_s)_{xx}-s(a_s)_x-a_s^2,
$$
$$
(s_{xx})_t=\tfrac12(s_{xx})_{xx}-s(s_{xx})_x-3a_s s_{xx}.
$$

The first step has $s=x/t$. Thereafter $a_s-1/t$ satisfies the
linear equation with drift $-s$ and zeroth-order coefficient
$-(a_s+1/t)$. For fixed smooth data this coefficient is bounded above
on a closed step, independently of spatial truncation; this uses the
tail bound and continuity, before asserting its sign. Comparison gives
$a_s\ge1/t$. The last displayed equation then gives $s_{xx}\le0$
on $x>0$. At a forward jump,

$$
s_+=s_-+\delta\Phi_x,\quad
(a_s)_+=(a_s)_-+\delta\Phi_{xx},\quad
(s_{xx})_+=(s_{xx})_-+\delta\Phi_{xxx}.
$$

The backward signs and $\delta\ge0$ preserve the forward signs.

A further comparison, not concavity alone, is needed. On $x>0$ set
$d_s=s_x/s$, $d_r=r_x/r$ and $\rho=d_s-d_r$.
The heat equation gives $s_t=\tfrac12s_{xx}-ss_x$, whereas $r_t=-rH$.
Taking logarithmic derivatives yields
$$
(d_s)_t=\tfrac12(d_s)_{xx}+d_s(d_s)_x-s_{xx},\qquad
(d_r)_t=-H_x.
$$
Since $\tfrac12(d_r)_{xx}+d_r(d_r)_x=\tfrac12(w/r)_x=H_x-w$,
substitution of $d_s=d_r+\rho$ gives its equation

$$
\rho_t=\tfrac12\rho_{xx}+d_s\rho_x+(d_r)_x\rho
                      +2H_x-w-s_{xx}.
$$

All three terms in the source are nonnegative by the comparisons
already proved, and $(d_r)_x<0$. On the first step, concavity gives
$r(x)=\int_0^xv(y)\,dy\ge xv(x)$, so
$\rho=1/x-v/r\ge0$. Odd Taylor expansions give
$d_s=1/x+O(x)$, $d_r=1/x+O(x)$ and $\rho=O(x)$ near zero;
the tail estimates give $\rho\to0$ at infinity. Comparison on
$[\varepsilon,A]$ therefore proves $\rho\ge0$ on each subsequent
step provided its initial sign is preserved. Define

$$
j=s\rho=s_x-(s/r)v.
$$

At a forward jump, with
$\alpha=c_+/c_-$ and $\lambda=(c_+-c_-)/c_-$,
$r_+=\alpha r_-$, $v_+=\alpha v_-$,
$s_+=s_-+\lambda r_-$ and $(s_x)_+=(s_x)_-+\lambda v_-$.
Substitution cancels the added terms and gives $j_+=j_-$.
Since $s_+>0$ on $x>0$, the sign of $\rho$ is preserved.
The quotient $s/r$ extends smoothly and evenly across zero, with
$j(0)=0$; reflection gives $j\ge0$ everywhere.
[OpenAI (2026a), Lemma 3.3][fs-signs].

### 4.4 How the signs make a correction with zero expectation useful

At a fixed positive time inside a step define

$$
R=r^2,\quad K=rs,\quad b=-w/r,\quad B=b-2v,
\quad L=-rs_{xx},\quad S_1=z+bv-2Rb.
$$

The subscript on $S_1$ distinguishes it from the support set. The
previous comparisons give

$$
R,K,v,B,j,L,S_1\ge0,\qquad b=B+2v\ge0,\qquad Rb^2=w^2,
$$

because $B=-2H$ and $S_1=2rH_x$. Here $s=-\partial_x\log g$
belongs to the forward heat factor, while $\partial_x\log f=r-s$
is the logarithmic derivative of the diffusion density. The signs have
separate sources: $B\ge0$ comes from $H\le0$, $S_1\ge0$ from
$H_x\ge0$ on the positive half-line, $j=s\rho\ge0$ from the
relative-slope comparison, and $L=-rs_{xx}\ge0$ from forward concavity.
Reflection extends these signs. The quantities are even and
extend smoothly at zero. In particular,
$b(0)=-z(0)/v(0)$, $j(0)=0$ and $S_1(0)=0$.

For $\mathcal D=r\partial_x$, direct differentiation gives

$$
\mathcal D(R,K,v,b,j)
 =(2Rv,\ 2vK+Rj,\ -Rb,\ -z-bv,\ -jv+Kb-L).
$$

Also $f_x/f=r-s$. Hence
$\mathcal W(F)=\mathcal DF+(v+R-K)F$ satisfies

$$
f\mathcal W(F)=\partial_x(rfF).
$$

This identity does not itself make the integral vanish. The tails give
$r=O(1)$; exponential decay of $v,w,z,b$ and their derivatives;
$s=x/t+O(1)$; $j=1/t+O((1+x)e^{-\kappa x})$; and $K=O(1+x)$.
Every polynomial $F$ in $R,K,v,b,j$ and its differentiated expression
therefore has at most polynomial growth. Meanwhile
$f(t,x)\le C\exp(-x^2/(2t)+C|x|)$. Thus every term used below is
absolutely integrable and $rfF\to0$ at both infinities. Smooth
extension across zero prevents an interior boundary term. Integrating
on $[-A,A]$ and taking $A\to\infty$ now gives
$\mathbb E_f\mathcal W(F)=0$.
[OpenAI (2026a), Lemma 3.4][fs-signs].

Here is the complete finite correction. Set

$$
(A,C,k,T_0,g_0,h)=
\left(\frac1{13},\frac{53}{24},\frac{19}{16},\frac{73}{48},
      \frac{2331}{10000},\frac{87}{2500}\right),
$$
$$
(x_0,y,m,n_0)=
\left(\frac{4663}{5000},\frac{6853}{10000},
      -\frac{1051}{400},-\frac{1073}{500}\right).
$$

Define

$$
Q=Avb+Cv^2+kKv-2kRb+T_0Rv,\qquad T_1=v(g_0R+hj),
$$
$$
\begin{aligned}
F_2={}&(Av-2kR)b^2
 +b\bigl(2Cv^2+2kKv+(g_0+2T_0)Rv+hjv\bigr)\\
 &+x_0v^2j+yv^3+mKv^2+n_0Rv^2.
\end{aligned}
$$

The choice is motivated by the terms containing $z$. The square
$(z+Q)^2$ and the nonnegative product $S_1T_1$ have combined
$z$ coefficient $2Q+T_1$. Only $\mathcal Db=-z-bv$ contains $z$,
and $\partial_bF_2=2Q+T_1$. Therefore subtracting
$(z+Q)^2+S_1T_1+\mathcal W(F_2)$ from the curvature expression
cancels every term involving $z$. The other favourable derivative is
$\partial_jF_2=x_0v^2+hbv\ge0$: the $-L$ in $\mathcal Dj$
leaves a nonnegative correction.

Put

$$
\begin{aligned}
P_0&=Rj(b-7v)^2,&
P_1&=RB(b-\tfrac73v)^2,\\
P_2&=Kv(b-\tfrac92v)^2,&
P_3&=vB(K+\tfrac14R-\tfrac17v)^2,\\
P_4&=(vb-\tfrac{14}{5}v^2-\tfrac{13}{4}Kv+\tfrac43Rv)^2,
\end{aligned}
$$
$$
(p_0,p_1,p_2,p_3,p_4)=
\left(\frac{337}{10000},\frac{183}{2500},\frac{411}{10000},
      \frac{11461}{5000},\frac{647}{10000}\right).
$$

Exact expansion, with $b=B+2v$, gives

$$
z^2-12Rvb^2+6v^4
 =(z+Q)^2+S_1T_1+\sum_{i=0}^4p_iP_i
   +\mathcal W(F_2)+L(x_0v^2+hbv)+P_{\rm rem}.
$$

For completeness, the entire remainder is specified by this table;
every unlisted coefficient is zero.

| Monomial | Coefficient | Monomial | Coefficient |
| --- | ---: | --- | ---: |
| $R^2v^2$ | $223/160000$ | $R^2vB$ | $4007/240000$ |
| $R^2B^2$ | $1097/120000$ | $RKv^2$ | $83/80000$ |
| $RKvB$ | $3343/24000$ | $Rv^3$ | $16259/23400000$ |
| $Rv^2B$ | $30179/5460000$ | $Rv^2j$ | $26/625$ |
| $RvB^2$ | $107/15000$ | $RvBj$ | $3/2500$ |
| $RB^3$ | $121/32500$ | $RB^2j$ | $11/10000$ |
| $K^2v^2$ | $579/20000$ | $K^2vB$ | $207/2500$ |
| $Kv^3$ | $911/975000$ | $Kv^2B$ | $349/420000$ |
| $Kv^2j$ | $5011/5000$ | $KvB^2$ | $133/130000$ |
| $KvBj$ | $87/2500$ | $v^4$ | $1661507/1521000000$ |
| $v^3B$ | $633799/621075000$ | $v^2B^2$ | $10657/1690000$ |

All square prefactors $Rj,RB,Kv,vB,1$ are nonnegative, as are
$S_1T_1$, $L(x_0v^2+hbv)$ and every remainder monomial. Integration
removes only $\mathcal W(F_2)$, giving

$$
\mathbb E_f[z^2-12vw^2+6v^4]
 \ge\frac{1661507}{1521000000}\mathbb E_fv^4
 \ge\frac1{1000}\mathbb E_fv^4.
$$

The surplus of the first coefficient over $1/1000$ is exactly
$140507/1521000000>0$. The rational identity and positive table can
be checked by finite arithmetic. Their application to this diffusion
also uses the signs, quotient behaviour, integrability and vanishing
flux proved above. [OpenAI (2026a), Lemma 4.1 and Proposition 4.2][fs-cert].

### 4.5 Passing the integrated inequality to an integrable coefficient

Return to an arbitrary $\gamma\in\mathcal U$ which equals $c>0$
on $I$, and fix $t\in I$. Choose a closed neighbourhood of $t$
inside $I$. Truncate and discretise separately on its left and right,
retaining the exact value $c$ on the neighbourhood. A positive lower
cutoff less than $c$, tending to zero, makes every step coefficient
positive without destroying monotonicity. Choose smooth terminal
parameters $M_n\ge\|\gamma_n\|_\infty$ with $M_n\to\infty$.
The coefficients converge in $L^1(0,1)$ and have uniformly bounded
$L^1$ norms. This construction is available even when $\gamma$ has
infinite terminal height.

On a fixed strip containing $t$ and ending before one, compact-strip
regularity gives uniform spatial convergence and bounds through order
four. The next derivative bounds give a common spatial Lipschitz
constant for those derivatives. Coupling with the same Brownian motion
and applying Gronwall gives a deterministic bound
$\sup_{s\le T}|X_s^n-X_s|\to0$. If $D_k^n=\partial_x^k\Phi_n$
and $D_k=\partial_x^k\Phi$, then, for $1\le k\le4$,

$$
|D_k^n(t,X_t^n)-D_k(t,X_t)|
\le\|D_k^n-D_k\|_{\infty,[0,T]\times\mathbb R}
   +C_{k,T}|X_t^n-X_t|\longrightarrow0.
$$

After the nonnegative terms are discarded, the two surviving integrands
$z_n^2-12v_nw_n^2+6v_n^4$ and $v_n^4$ are uniformly bounded,
with $v_n=cD_2^n$, $w_n=cD_3^n$ and $z_n=cD_4^n$. Dominated convergence therefore passes their expectations
to the limit. For completeness, let $V,W,Z$ bound both the limiting and approximating
$v,w,z$, and let $e_v,e_w,e_z$ bound their coupled evaluation errors.
Uniform spatial convergence and the path bound above give these errors
with $e_v,e_w,e_z\to0$. Difference-of-powers identities give
$$
\begin{aligned}
|\mathbb E\mathcal C(v_n,w_n,z_n)-\mathbb E\mathcal C(v,w,z)|
 &\le(12W^2+24V^3)e_v+24VW e_w+2Ze_z,\\
|\mathbb E v_n^4-\mathbb E v^4|&\le4V^3e_v,
\end{aligned}
$$
where $\mathcal C(v,w,z)=z^2-12vw^2+6v^4$. These constants depend
on the common strip and coefficient mass bound, not on plateau width.
This transfer requires neither convergence of $s_n$ or
$j_n$ nor a uniform bound on their tail constants: those auxiliary
quantities have already disappeared after integration.
[OpenAI (2026a), Lemmas 2.1–2.3][fs-reg];
[Proposition 5.1][fs-curv].

Passing a positive inequality to a limit gives only a nonnegative
inequality in general. We therefore establish strictness for the limit
itself. Choose $b\in I$ later than $t$ and put
$\psi=\Phi_\gamma(b,\cdot)$. This is smooth, convex, even and a
bounded distance from $|x|$, so $\psi'$ cannot be constant. The
Cole–Hopf formula gives

$$
\Phi_{xx}(t,x)
=\mathbb E^{\rm tilt}_{t,x}\psi''
  +c\operatorname{Var}^{\rm tilt}_{t,x}(\psi'),
$$
$$
\nu_{t,x}(dy)=
\frac{e^{c\psi(y)}p_{b-t}(y-x)}
 {\int_{\mathbb R}e^{c\psi(z)}p_{b-t}(z-x)\,dz}\,dy.
$$

The tilted density is positive everywhere. Its variance of the
nonconstant continuous function $\psi'$ is strictly positive; its
mean of $\psi''$ is nonnegative. Thus $v(t,x)>0$ for every $x$, and
$\mathbb E v(t,X_t)^4>0$. Combining the limiting inequality with
the differentiated identity proves
$q'''(t)\ge(1000c^2)^{-1}\mathbb E v(t,X_t)^4>0$.
This proves strict convexity of $q'$ on $I$.
[OpenAI (2026a), Lemma 2.3][fs-reg]; [Proposition 5.1][fs-curv].

### 4.6 Why the zero interval remains a separate case

When $c=0$, the heat equation gives
$q''(t)=\mathbb E\Phi_{xxx}(t,X_t)^2$ without division by $c$.
Start the drift-free evolution at an earlier point of $I$; its
Gaussian transition kernel makes the law of $X_t$ have a positive
density everywhere. If the expectation were zero, continuity would
force $\Phi_{xxx}(t,\cdot)\equiv0$. Then $\Phi(t,\cdot)$ would
be an even quadratic polynomial. Its one-Lipschitz bound forces that
polynomial to be constant, contradicting its bounded distance from
$|x|$. Therefore $q''(t)>0$, giving strict increase of $q'$.
[OpenAI (2026a), Lemma 2.3][fs-reg].

The analytic certificate is thus a proved input to the gap argument in
this source, with the stated model and regularity assumptions. An
abstract polynomial or flux lemma assumes those analytic hypotheses;
the finite-step comparisons and the transfer argument discharge them.
Inspection of the corresponding Lean sources records that construction,
while a source-bound build, Comparator replay and transitive axiom audit
remain separate verification tasks, as explained in §§8 and 11.
<!-- /passage:curvature -->

<a id="gap-elimination"></a>

## 5. Excluding terminal, interior and initial gaps

<!-- passage:gaps -->
Keep the same minimiser, diffusion and moment function $q$ throughout.
Section 3 has established $G\ge0$, $G=0$ on the support
$S=\operatorname{supp}\mu_\gamma$, and the contact conditions
$q(s)=s$, $q'(s)\le1$ at support points. At zero, the value identity
comes from symmetry, and the slope bound requires $0\in S$.
Section 4 supplies curvature on constant intervals for every admissible
coefficient. These premises are available before any support gap is
excluded. We first deal with the endpoint at one, then use the curvature
estimate on the remaining intervals.

**Why a terminal plateau violates the variational inequality.**

Suppose that $\gamma=c$ on $(a,1)$, where $0\le a<1$ and
$c\ge0$ is finite. The endpoint $1$ is outside the support domain, so
there is no contact condition there to complete an endpoint-chord
argument. Instead we will prove
$$
1-q(t)\ge C\sqrt{1-t}
\tag{5.1}
$$
for some $C>0$ and every $t$ sufficiently close to one. The proof
separates two facts: the diffusion puts positive probability density
near zero, and the smoothed terminal slope has a definite deficit from
$\pm1$ in a shrinking window around zero.

Fix $s\in(a,1)$ and let $\rho_s$ be the law of $X_s$. Choose
$R<\infty$ such that $p_0=\rho_s([-R,R])>0$. For $c>0$, set
$$
h(t,y)=\mathbb E e^{c|y+\sqrt{1-t}Z|},\qquad
\Phi(t,y)=c^{-1}\log h(t,y),
$$
where $Z$ is standard normal. The drift on this interval is
$c\Phi_x=h_x/h$, and the transition density is
$$
k_{s,t}(x,y)=p_{t-s}(y-x)\frac{h(t,y)}{h(s,x)},\qquad
p_v(z)=(2\pi v)^{-1/2}e^{-z^2/(2v)}.
\tag{5.2}
$$
The heat-semigroup identity normalises this kernel; equivalently, for
Brownian motion started at $(s,x)$, $h(t,B_t)/h(s,x)$ is the positive
mean-one change of measure which adds the drift $h_x/h$. For $c=0$,
the same kernel formula applies
with $h=1$, and the value function is the ordinary heat evolution of
$|x|$. [OpenAI (2026a), Lemma 6.3, proof of (6.6)][fs-var].

Put $L=1-s$ and $\delta=L/2$. For
$s+\delta\le t<1$, $|x|\le R$ and $|y|\le1$,
$$
p_{t-s}(y-x)\ge
(2\pi L)^{-1/2}e^{-(R+1)^2/(2\delta)}=:k_*>0,
$$
while $h(t,y)\ge1$ and
$h(s,x)\le e^{cR}\mathbb E e^{c\sqrt L|Z|}=:M<\infty$.
Integrating (5.2) over the part of $\rho_s$ in $[-R,R]$ therefore
gives a density $f_t$ of $X_t$ with
$$
f_t(y)\ge p_0k_*/M=:m>0
\quad(s+\delta\le t<1,\ |y|\le1).
\tag{5.3}
$$
Only positive mass of a compact set was needed at time $s$; no density
assumption on $\rho_s$ has entered.

Now write $\varepsilon=1-t$ and restrict to
$|y|\le\sqrt\varepsilon$. Differentiating the terminal heat formula
gives, with the unweighted interpretation for $c=0$,
$$
u(t,y)=
\frac{\mathbb E[\operatorname{sgn}(y+\sqrt\varepsilon Z)
                     e^{c|y+\sqrt\varepsilon Z|}]}
     {\mathbb E e^{c|y+\sqrt\varepsilon Z|}}.
$$
The denominator is at most
$D=e^c\mathbb E e^{c|Z|}<\infty$. Each sign has unnormalised
mass at least $p_*:=\mathbb P(Z\ge1)>0$: the threshold
$|y/\sqrt\varepsilon|$ is at most one, and the exponential weight
is at least one. Hence each sign has tilted probability at least
$\theta=p_*/D\in(0,1/2)$. It follows that
$$
|u(t,y)|\le1-2\theta,\qquad
1-u(t,y)^2\ge4\theta(1-\theta)=:\kappa>0.
$$
Multiplying this uniform deficit by the density lower bound (5.3)
and the window width $2\sqrt\varepsilon$ yields
$$
1-q(t)=\int_{\mathbb R}(1-u(t,y)^2)f_t(y)\,dy
\ge 2m\kappa\sqrt{1-t}.
$$
This proves (5.1) with $C=2m\kappa$.
[OpenAI (2026a), Lemma 6.3, density and terminal-window estimates][fs-var].

The sign of the contradiction is now explicit. For $s'$ sufficiently
close to one, the estimate holds at every $t\in[s',1)$, so
$$
\begin{aligned}
G(s')&=\int_{s'}^1(q(t)-t)\,dt\\
&\le\frac{(1-s')^2}{2}
       -\frac{2C}{3}(1-s')^{3/2}<0.
\end{aligned}
$$
The final inequality holds once $\sqrt{1-s'}<4C/3$. It contradicts
the nonnegative cost of adding an atom at $s'$. This proof covers
$c=0$ as well as $c>0$. In particular, empty support is impossible:
then $\mu_\gamma=0$ and $\gamma=0$ on all of $[0,1)$.
The terminal-plateau conclusion was already recorded in
[Auffinger, Chen and Zeng (2020), Remark 7][acz]; the estimates above
supply the quantitative argument needed here.

**The remaining gaps have a finite right contact point.**

The support is relatively closed in $[0,1)$. Its complement is a union
of relative open intervals, and the Stieltjes measure vanishes on each
such interval. For $x<y$ in one interval,
$$
\gamma(y)-\gamma(x)=\mu_\gamma((x,y])=0,
$$
so $\gamma$ is constant there. The terminal argument excludes a component
ending at one. Every remaining component therefore ends at a point
$b<1$ of $S$.

First consider a gap $(a,b)$ with both endpoints in $S$, allowing
$a=0$. Compact-strip regularity gives continuity of $q'$ on $[a,b]$,
even if $\gamma$ jumps at an endpoint. Contact gives
$$
q(a)=a,\qquad q(b)=b,\qquad q'(a),q'(b)\le1.
\tag{5.4}
$$
If the constant coefficient is $c>0$, Section 4 makes $q'$ strictly
convex in the gap. Continuity extends the chord comparison to its
endpoints, giving
$$
q'(t)<\frac{b-t}{b-a}q'(a)+\frac{t-a}{b-a}q'(b)\le1,
\qquad a<t<b.
\tag{5.5}
$$
Integrating contradicts $q(b)-q(a)=b-a$. Equivalently, the mean value
theorem applied to (5.4) requires an interior point with $q'=1$,
whereas (5.5) excludes every such point. The endpoint derivatives need
only be at most one; equality has not been assumed. With $h=q'$ and
$C_{a,b}$ its endpoint chord, the contradiction is the exact area identity
$$
(b-a)-\int_a^b h
=(b-a)\left(1-\frac{h(a)+h(b)}2\right)
 +\int_a^b(C_{a,b}-h)>0.
$$
The first term is nonnegative; strict convexity makes the second positive.
Only continuity of $q'$ is needed at the ends. For example, a jump
$\Delta\gamma$ at $s$ gives the one-sided identity
$$
q''(s+)-q''(s-)=-2\Delta\gamma\,\mathbb E a(s,X_s)^3.
$$
It follows by applying Itô's formula to $a^2$ and using continuity of
its derivative moments on a compact strip. Taking $\gamma=0$ before
$s=1/2$ and $\gamma=1/2$ afterward makes this jump strictly negative;
the terminal Cole–Hopf solution has positive Hessian. Thus continuity
of $q'$ does not license classical higher time derivatives across
coefficient jumps. [OpenAI (2026a), proof of Corollary 6.4][fs-density].

If $c=0$, the separate heat argument in Section 4 makes $q'$ strictly
increasing. Then $q'(t)<q'(b)\le1$ for $a<t<b$, and the same
contradiction follows. The left slope bound is unnecessary in this case.
[OpenAI (2026a), proof of Theorem 1.1 after Lemma 6.3][fs-var].

There are two distinct possibilities at the left endpoint. If
$(0,b)$ is a gap and $0\in S$, the preceding proof applies using
the one-sided contact slope bound at zero. Because $(0,b)$ contains
no mass, the support condition at zero forces an atom there and hence
$c=\gamma(0)>0$. Its absence has not been proved at this stage.
If instead the complementary component is $[0,b)$ with $0\notin S$,
there is no mass anywhere in $[0,b)$. Thus $\gamma=0$ there.
The identity $q(0)=0$ comes from zero-field symmetry, and the
right endpoint gives $q(b)=b$, $q'(b)\le1$. Strict increase again
forces $q'<1$ throughout $(0,b)$, an impossibility.

**Full support and the moment identities.**

The cases are exhaustive, so $S=[0,1)$. Only now can contact be
applied at every $0<t<1$, giving $q(t)=t$ throughout the domain;
the value at zero was already known. Differentiating and using the
gradient-martingale identity gives
$$
\mathbb E a(t,X_t)^2=q'(t)=1,\qquad 0\le t<1,
$$
with the right derivative at zero. Finally, every nonempty open
subinterval $(a,b)$ receives positive mass. Therefore
$$
\gamma(b)-\gamma(a)=\mu_\gamma((a,b])>0
\qquad(0\le a<b<1).
$$
The proof establishes full support, strict increase and the two
moment identities. Smooth absolute continuity, including the later
conclusion $\gamma(0)=0$, uses the source's further argument from
saturated consistency; it has not been assumed to obtain contact
or to exclude an initial gap. [OpenAI (2026a), conclusion of the
proof of Theorem 1.1][fs-var].
A weaker analytic condition suffices for the bounded-gap contradiction.
If $h\in C([a,b])\cap C^2((a,b))$ has the displayed endpoint and
integral data, then $h'=0\Rightarrow h''>0$ is already impossible:
either $h\le1$ everywhere, forcing $h\equiv1$ by its integral, or it
attains an interior maximum above one, where $h'=0$ and $h''\le0$.
This is an elementary deduction from these premises. Chen's conditional
crossing theorem, with its own hypotheses, is of this form; §4 proves
the stronger $q'''>0$ throughout a positive plateau, without a minimizer
premise. See [Chen, arXiv:2607.18032v1, Proposition 4.2 and the proof
of Proposition 4.3][chen26]. Neither statement supplies terminal contact
at the excluded endpoint one.
<!-- /passage:gaps -->

<!-- passage:density -->
<a id="smooth-density-consequence"></a>

### 5.1 A further manuscript consequence: smooth density

Full support does not by itself prove that the Stieltjes measure has a density. In the source manuscript, that conclusion uses the PDE again after the gap contradiction has established
$\mathbb E a(t,X_t)^2=1$. We reconstruct the additional argument here because it explains a further conclusion of the original paper. It is not a clause of the selected full-support formal statement.

Put $f_k=\partial_x^k\Phi_\gamma$, so $f_1=u$ and $f_2=a$. All formulas in this subsection are on a fixed compact time strip, where every finite collection of spatial derivatives is bounded. Differentiating the PDE and applying Itô's formula along the associated diffusion gives
$$
df_k(t,X_t)=
-\frac{\gamma(t)}2\sum_{j=1}^{k-1}\binom{k}{j}
 f_{j+1}(t,X_t)f_{k-j+1}(t,X_t)\,dt
+f_{k+1}(t,X_t)\,dB_t.
$$
The sum is empty when $k=1$. This identity needs no derivative of $\gamma$. For an initially nonsmooth coefficient, apply it to finite-step approximations and pass to the integrated identity: the coefficient converges in $L^1$, the spatial factors converge uniformly, and the stochastic integrals converge by the Itô isometry. [OpenAI full-support manuscript, smooth-density proof, lines 35–50][fs-density].

Set $b=f_3$. The case $k=2$ gives
$da=-\gamma a^2dt+b\,dB_t$, and consequently
$$
0=\frac d{dt}\mathbb E a^2
 =\mathbb E b^2-2\gamma(t)\mathbb E a^3
\quad\text{for almost every }t<1.
$$
Convexity gives $a\geq0$; the already established second moment gives
$\mathbb E a^3\geq(\mathbb E a^2)^{3/2}=1$. Thus the quotient
$$
\widetilde\gamma(t)=\frac{\mathbb E b(t,X_t)^2}
                         {2\mathbb E a(t,X_t)^3}
$$
is well defined and continuous, before any continuity of $\gamma$ is known. It equals $\gamma$ almost everywhere. Approaching an arbitrary $t<1$ from the right through the full-measure equality set, continuity of $\widetilde\gamma$ and right continuity of $\gamma$ give equality at that $t$ as well. This proves continuity of $\gamma$. At zero, $X_0=0$, and evenness of $\Phi(0,\cdot)$ gives $b(0,0)=0$; hence $\gamma(0)=0$. [OpenAI full-support manuscript, lines 52–66][fs-density]; [Chen, Proposition 4.6, pp. 25–26][chen26].

The bootstrap must treat all polynomial moments simultaneously. For a polynomial $P$ in finitely many variables, write
$$
M_P(t)=\mathbb E P(f_1(t,X_t),\ldots,f_m(t,X_t)).
$$
The preceding stochastic identities and Itô's product rule provide polynomials $Q_P,R_P$, involving only finitely many additional derivatives, such that
$$
M_P(t)-M_P(0)=\int_0^t\bigl(M_{Q_P}(s)+\gamma(s)M_{R_P}(s)\bigr)\,ds.
$$
Explicitly, if
$$
D_k(y)=-\tfrac12\sum_{j=1}^{k-1}\binom{k}{j}y_{j+1}y_{k-j+1},
$$
then
$$
Q_P=\tfrac12\sum_{k,l}\partial_{kl}P\,y_{k+1}y_{l+1},
\qquad R_P=\sum_k\partial_kP\,D_k.
$$
All these moments start continuous. Once $\gamma$ is continuous, the integral formula makes every moment $C^1$, and the quotient formula makes $\gamma$ itself $C^1$. If all moments and $\gamma$ are $C^r$, the same argument makes them $C^{r+1}$. Induction proves $\gamma\in C^\infty([0,1))$, with derivatives at zero taken from the right. Since $\gamma(0)=0$, there is no atom at zero; its Stieltjes measure is $\gamma'(t)\,dt$, and monotonicity gives $\gamma'\geq0$. This is the polynomial-moment method credited by the source to Auffinger–Chen and to Chen's zero-temperature treatment. [OpenAI full-support manuscript, lines 68–101][fs-density]; [Auffinger and Chen, proof of Theorem 2(ii), p. 16][ac-properties]; [Chen, Appendix B.6, p. 38][chen26].

The exact arXiv edition of Auffinger–Chen's polynomial-moment proof has
a local display discrepancy: p. 16 of arXiv:1303.3573v1 prints a square
in $F_3$ below (40), whereas Proposition 3, p. 9, has the cube.
The identity $d(a^2)=(-2\gamma a^3+b^2)dt+2ab\,dB$ requires the
cube used above; the moment induction itself is unchanged.

<!-- /passage:density -->

<!-- passage:density-positive -->

### 5.2 Why the density is strictly positive away from zero

A smooth increasing function can have zero derivative at an interior point. For example,
$g(t)=(t-\tfrac12)^3+\tfrac18$ on $[0,1)$ is nonnegative and strictly increasing, and $dg$ has full support, although $g'(\tfrac12)=0$. Thus strict positivity of the minimizing density requires a further estimate.

Let $d=f_4$. The same moment identities give
$$
\frac d{dt}\mathbb E b^2=\mathbb E d^2-6\gamma\mathbb E(ab^2),
\qquad
\frac d{dt}\mathbb E a^3=3\mathbb E(ab^2)-3\gamma\mathbb E a^4.
$$
Differentiate $\mathbb E b^2=2\gamma\mathbb E a^3$, now justified by the bootstrap, to obtain
$$
2\gamma'(t)\mathbb E a^3
=\mathbb E d^2-12\gamma(t)\mathbb E(ab^2)+6\gamma(t)^2\mathbb E a^4.
$$
Fix $t\in(0,1)$, and set $c=\gamma(t)>0$; positivity follows from full support and $\gamma(0)=0$. Replace $\gamma$ on a shrinking interval about $t$ by the constant $c$. Monotonicity is preserved because values to the left are at most $c$ and values to the right are at least $c$. One explicit approximation starts with
$h_n=\max\{\epsilon_n,\min\{K_n,\eta_n\lfloor\gamma/\eta_n\rfloor\}\}$,
where $0<\epsilon_n<c$, $\epsilon_n,\eta_n\downarrow0$ and
$K_n\uparrow\infty$ with $K_n>c$. On the left of
$[t-\delta_n,t+\delta_n)$ use $\min(c,h_n)$, on that interval use
$c$, and on the right use $\max(c,h_n)$. These are positive,
nondecreasing finite-step functions. Continuity of $\gamma$ gives
$$
\|\gamma_n-\gamma\|_1
\le\epsilon_n+\eta_n+\int_0^1(\gamma-K_n)_+\,ds
       +2\delta_n\sup_{|s-t|\le\delta_n}|\gamma(s)-c|\longrightarrow0.
$$
Choose $M_n\ge\max(n,K_n)$ for the smooth terminal data. Fix
$t<T<T'<1$ independently of $\delta_n$. Their common $L^1$ bound
$M$ implies $\gamma_n(T')\le M/(1-T')$, so the regularity estimates
on $[0,T]$ do not deteriorate as the artificial plateau shrinks.

Apply the integrated certificate at $t$ to the scaled derivatives
$v_n=ca_n,w_n=cb_n,z_n=cd_n$. After dividing by $c^2$, it says
$$
\mathbb E[d_n^2-12ca_nb_n^2+6c^2a_n^4]
\geq\frac{c^2}{1000}\mathbb E a_n^4.
$$
The compact-strip derivative and diffusion convergence estimates depend on the common coefficient $L^1$ bound and the distance from time one, not on the width of the inserted plateau. They therefore pass this inequality to the limit at the fixed time $t$. Combining it with the preceding identity yields
$$
2\gamma'(t)\mathbb E a^3
\geq\frac{\gamma(t)^2}{1000}\mathbb E a^4>0,
\qquad 0<t<1.
$$
The final strict inequality uses $\mathbb E a^4\geq(\mathbb E a^2)^2=1$. Cauchy–Schwarz also gives
$\mathbb E a^3\le\sqrt{\mathbb E a^2\mathbb E a^4}
=\sqrt{\mathbb E a^4}\le\mathbb E a^4$. Therefore the same estimate proves
the quantitative ordinary consequence
$$
\gamma'(t)\ge\frac{\gamma(t)^2}{2000}>0\quad(0<t<1),\qquad
\mu_\gamma((r,s])\ge\frac{s-r}{2000}\gamma(r)^2
\quad(0<r<s<1).
$$
The second inequality follows by integration and monotonicity. Its lower
bound depends on this minimizer and the left endpoint; it is not a
uniform mass estimate for a family of finite-temperature measures. This argument proves only $\gamma'(0)\geq0$ at the left endpoint. It does not claim that the minimizing coefficient itself is constant on a neighbourhood, and it does not pass the approximants' third time derivatives to the limit. Only a spatial-derivative expectation is transferred. [OpenAI full-support manuscript, lines 102–152][fs-density].
<!-- /passage:density-positive -->

### 5.3 Near-ground configurations at a prescribed overlap

<!-- passage:overlap-pairs -->
Full support also gives a geometric consequence for the finite-disorder
energy landscape. For every fixed $r\in[0,1)$ and $\varepsilon,\eta>0$,
there is a constant $K=K(r,\varepsilon,\eta)>0$, independent of $n$, such that
$$
\mathbb P\left(\exists\sigma,\tau\in\{-1,1\}^n:
\left|\frac1n\sum_{i=1}^n\sigma_i\tau_i-r\right|<\varepsilon,
\quad \frac{H_n(\sigma)}n,\frac{H_n(\tau)}n\ge P_*-\eta\right)
\ge1-Ke^{-n/K},\qquad n\ge1.
$$
The probability is over the SK couplings; the configurations may depend on
them. This is the specialization of [Auffinger–Chen–Zeng, Proposition 1,
equation (5), p. 5][acz] to the full-support minimizer above. Their theorem
applies to each point of its Stieltjes support. Its proof, on pp. 15–16,
uses the coupled free energy constrained to a neighbourhood of that
overlap, passes to the coupled maximum and applies Gaussian concentration.
The coupled maximum approaches $2P_*$, while the unrestricted maximum
approaches $P_*$; these two facts force both members of a maximizing pair
to be near ground energy.

The covariance normalization needs one small adjustment. Writing
$R=n^{-1}\sum_i\sigma_i\tau_i$, our Hamiltonian has covariance
$nR^2/2-1/2$. Adjoin a common independent Gaussian $C$ of variance $1/2$.
Then $\widetilde H_n(\sigma)=H_n(\sigma)+C$ has covariance
$n\xi(R)$ with $\xi(t)=t^2/2$, as in the cited mixed-spin theorem.
Its expected maximum equals that of $H_n$, so its ground-state limit is
the same $P_*$. Apply the theorem with energy tolerance $\eta/2$.
On $|C|\le\eta n/2$, the resulting pair also satisfies the displayed
energy inequalities for $H_n$. The omitted event has probability at most
$2e^{-\eta^2n^2/4}$, which can be absorbed into $Ke^{-n/K}$ by enlarging
$K$. Since the conclusion for $H_n$ depends only on its couplings,
this also removes the auxiliary Gaussian from the probability statement.

This ordinary consequence uses an external landscape theorem together with
full support and the attained Parisi formula. It is outside the two selected
formal statements in §8. It asserts existence for each fixed target overlap;
it neither describes a typical sampled pair nor gives a procedure for
finding the pair, and it asserts no event simultaneously indexed by every
real overlap. The separate algorithmic consequence is in §7.4.
<!-- /passage:overlap-pairs -->

<a id="scalar-value-identities"></a>

## 6. Recovering the value from a martingale

<!-- passage:value -->
The bounded martingale $u(t,X_t)$ converges almost surely and in $L^2$
to $U_1$. Its second moment tends to one because $q(t)=t$.
Since $|U_1|\le1$, $\mathbb E U_1^2=1$ forces $U_1^2=1$ almost surely.
Uniform integrability identifies $u(t,X_t)=\mathbb E[U_1\mid\mathcal F_t]$,
which is the conditional-expectation identity used below.

The drift bound $|\gamma u|\le\gamma\in L^1$ gives convergence of $X_t$
to $X_1$. Uniform terminal convergence of $\Phi$ to $|x|$, together
with convexity, gives $u(t,x_t)\to\operatorname{sgn}(x)$ when
$x_t\to x\ne0$. Thus $U_1X_1=|X_1|$, including when $X_1=0$;
no proof that this event has probability zero is needed.

Itô's formula gives
$$
\mathbb E\Phi(t,X_t)=\Phi(0,0)+\frac12\int_0^t\gamma(s)s\,ds.
$$
The terminal limit first gives
$\Phi(0,0)=\mathbb E|X_1|-\tfrac12\int_0^1s\gamma(s)ds$.
Subtracting the second half from the definition of the functional yields
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1s\gamma(s)\,ds$.
The ground-state Parisi formula identifies this with $P_*$.
The diffusion equation, conditional expectation and Fubini give
$$
\mathbb E[U_1X_1]=\mathbb E[U_1B_1]
 +\int_0^1\gamma(s)\mathbb E[u(s,X_s)^2]\,ds.
$$
Bounded $u,U_1$ and integrable $\gamma$ justify these terms.
Combining the identities and using stochastic integral covariance gives
$$
P_*=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt
 =\mathbb E[U_1B_1]=\int_0^1\mathbb E a(t,X_t)\,dt.
$$
The last integral is absolutely bounded by one because
$\mathbb E|a|\le(\mathbb E a^2)^{1/2}=1$.
Full support supplies $\mathbb E a^2=1$, whereas the value uses
$\int\mathbb E a$. Substituting the second moment into the value identity
would change the assertion. [OpenAI (2026a), §7][fs-cons].
The prediction error and the energy tail have different sizes:
$$
\|U_1-u(T,X_T)\|_2^2=1-T,
$$
$$
P_*-\int_0^T\mathbb E a(t,X_t)\,dt
=\mathbb E[(U_1-u(T,X_T))(B_1-B_T)]\in[0,1-T].
$$
The first identity is orthogonal projection onto $\mathcal F_T$.
Martingale orthogonality removes the past Brownian component in the
second; Cauchy–Schwarz bounds the product by $1-T$, and convexity
makes it nonnegative. No uniform terminal curvature bound is needed.
The stochastic value calculation has a direct antecedent in
[Sellke, arXiv:2105.03506v4, Definition 1.3 and Lemma 3.11](https://arxiv.org/abs/2105.03506v4).
There, “optimizable” means the contact identity $\mathbb E u(t,X_t)^2=t$
on $[q,1)$, with $q$ the infimum of the support of the coefficient
function. Lemma 3.11 derives the finite-cutoff value identity by applying
Itô's formula to $\Phi$ and $xu$, before taking the terminal limit.
This is the same value-recovery mechanism used here, specialized to
zero field and $\xi''=1$.

A cutoff must retain the full Parisi penalty. Set
$\Psi(T,x)=\Phi(T,x)-xu(T,x)$ and
$I(T)=\int_0^T\mathbb E a(t,X_t)\,dt$. Subtracting the complete penalty
from the finite-time Itô identity gives
$$
\mathcal P(\gamma)-I(T)
 =\mathbb E\Psi(T,X_T)
  +\frac12\int_0^T\gamma(t)(q(t)-t)\,dt
  -\frac12\int_T^1t\gamma(t)\,dt.
$$
Under contact the middle term vanishes. The final term is absent from
the displayed equality in [El Alaoui, Montanari and Sellke,
arXiv:2001.00904v1, §6.2, pp. 32–33][eams20]. Its sign is nonpositive,
so the upper bound by $\mathbb E\Psi(T,X_T)$ used there remains valid;
its magnitude tends to zero by integrability. This finite-cutoff
correction is consistent with the exact terminal identity above.
<!-- /passage:value -->

<a id="finite-gaussian-approximation"></a>

## 7. A finite Gaussian spin and its adjacent correlations

<!-- passage:gaussian -->
Fix $0<T<1$, then a mesh $N\ge1$, $\Delta=T/N$, $t_j=j\Delta$.
On independent standard normals $Z_1,\ldots,Z_{N+1}$, set
$$
Y_0=0,\quad Y_j=Y_{j-1}+\sqrt\Delta Z_j+
 \Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),
$$
$$
c_j=(\mathbb E a(t_{j-1},Y_{j-1})^2)^{-1/2},\qquad
g_j=c_ja(t_{j-1},Y_{j-1})Z_j.
$$
For sufficiently large $N$, all $c_j$, $1\le j\le N$, are finite
and positive. Couple the increments to Brownian motion. On the fixed
strip, the gradient and curvature are bounded and Lipschitz. Monotonicity
gives, for the left-grid projection $\pi_N$,
$$
\int_0^T|\gamma(s)-\gamma(\pi_N(s))|\,ds
 \le\Delta(\gamma(T)-\gamma(0)).
$$
Drift error estimates and discrete Gronwall yield
$\mathbb E\max_{j\le N}|Y_j-X_{t_j}|^2\to0$, hence
$\max_j|c_j-1|\to0$. The $g_j$ are orthonormal in $L^2$:
they have unit variance and conditional mean zero given their past.
Their predictable multipliers may depend on earlier coordinates, so
orthonormality does not assert independence.

With $F_{\rm G}$ the standard Gaussian distribution function, define
$$
F_N=\operatorname{sgn}(u(T,Y_N)+2F_{\rm G}(Z_{N+1})-1).
$$
$$
A_j=\mathbb E[F_Ng_j],\quad B_i=\mathbb E[F_NZ_i],\quad A_0=0.
$$
The extra coordinate is independent and its distribution function is uniform.
For any $v\in[-1,1]$, the random sign of $v+2U-1$ has mean $v$.
Therefore
$\mathbb E[F_N\mid Z_1,\ldots,Z_N]=u(T,Y_N)$ exactly.
A deterministic sign of the gradient would not preserve this conditional
mean. Rounding preserves correlations with functions of the first $N$
coordinates, which is exactly what the two coefficient vectors need.
It does not make the whole rounded spin close in $L^2$ to that conditional
mean. Indeed, with $m_N=u(T,Y_N)$,
$$
 \mathbb E[(F_N-m_N)^2]=1-\mathbb E m_N^2\longrightarrow1-T.
$$
Here $m_N\to u(T,X_T)$ in $L^2$ at fixed $T$ and full support gives
$\mathbb E u(T,X_T)^2=T$. The independent rounding variance disappears
only in the later endpoint limit.

The approximation
$$
M_N=\sum_{j=1}^N\sqrt\Delta\,a(t_{j-1},Y_{j-1})Z_j
 =u(T,Y_N)+o_{L^2}(1)
$$
gives a common residual for both coefficient families. In
$\mathbb E[M_NZ_i]$, a summand with $j<i$ is independent of centered
$Z_i$; one with $j>i$ vanishes on conditioning on the first $j-1$
coordinates; and the $j=i$ term is
$\sqrt\Delta\,\mathbb E a(t_{i-1},Y_{i-1})$.
Also $\mathbb E[M_Ng_j]=\sqrt\Delta/c_j$ by orthonormality.
Bessel's inequality applied to that one residual gives the vector estimates
$$
(A_j)_{j=1}^N=(\sqrt\Delta/c_j)_{j=1}^N+o_{\ell^2}(1),
$$
$$
(B_i)_{i=1}^N=
(\sqrt\Delta\,\mathbb E a(t_{i-1},Y_{i-1}))_{i=1}^N+o_{\ell^2}(1).
$$
Coordinatewise errors would not control a sum of growing length. Put
$$
e_N=\|u(T,Y_N)-M_N\|_2,\quad
\alpha_j=\sqrt\Delta/c_j,\quad
\beta_j=\sqrt\Delta\,\mathbb E a(t_{j-1},Y_{j-1})
\quad(1\le j\le N).
$$
The fixed-$T$ Euler argument gives $e_N\to0$. Bessel's inequality gives
$\|A_{1:N}-\alpha\|_2,\|B_{1:N}-\beta\|_2\le e_N$.
Also $\|B_{1:N}\|_2\le1$ and $\|\alpha\|_2\le C_T$ for sufficiently
large $N$, with $C_T$ independent of the mesh. The shifted interior
pairing therefore differs by at most $(1+C_T)e_N$.
The rounding coordinate contributes at most
$|A_NB_{N+1}|\le e_N+\sqrt\Delta/c_N$. Thus the
dimension-free estimate is
$$
\left|\sum_{j=0}^NA_jB_{j+1}
 -\Delta\sum_{j=1}^{N-1}\frac{\mathbb E a(t_j,Y_j)}{c_j}\right|
\le(2+C_T)e_N+\frac{\sqrt\Delta}{c_N}\longrightarrow0.
$$
The index shift selects the Hessian at $t_j$; $Z_{N+1}$ serves
rounding rather than another Euler increment. This estimate is a
fixed-strip scalar correspondence, not a circuit energy identity.
Hence
$$
\sum_{j=0}^NA_jB_{j+1}
 =\Delta\sum_{j=1}^{N-1}\frac{\mathbb E a(t_j,Y_j)}{c_j}+o(1)
 \longrightarrow\int_0^T\mathbb E a(t,X_t)\,dt.
$$
Only afterward let $T\uparrow1$, obtaining $P_*$.
The mesh count $N$ is unrelated to the spin-system size $n$.
As in [OpenAI (2026a), Proposition 7.2][fs-cons], these coefficients
describe a finite Gaussian function, not yet a circuit on finite SK
disorder.

The QAOA scalar input also uses the tail estimate
$0\le P_*-\int_0^T\mathbb E a(t,X_t)\,dt\le1-T$, from nonnegative
curvature and $\mathbb E a^2=1$. This estimate and the fixed-strip
regularity facts must be retained beside the coefficient limit; they are
not all clauses of the selected finite-Gaussian statement. They enter
the construction in [OpenAI (2026b), §3][q-classical].
<!-- /passage:gaussian -->

<!-- passage:gaussian-error-budget -->

### 7.1 A scalar error budget with its dependencies exposed

The preceding proof can be written as a finite inequality. This is an
ordinary deduction from the source estimates, not an additional clause of
the selected formal statement. Write
$S_{T,N}=\sum_{j=0}^N A_jB_{j+1}$ and
$f(t)=\mathbb E a(t,X_t)$, so $0\le f(t)\le1$. On the fixed strip let
$K_T=\sup_{t\le T,x}|a(t,x)|$ and choose a spatial Lipschitz constant
$L_T$ for $a$. Define
$$
 \delta_N=\max_{0\le j\le N}\|Y_j-X_{t_j}\|_2,\qquad
 d_N=\max_{1\le j\le N}
 \left|\mathbb E a(t_{j-1},Y_{j-1})^2-1\right|.
$$
These errors have a rate at each fixed strip, even if $\gamma$ has jumps.
Put $\Gamma=\gamma(T)$ and $V=\gamma(T)-\gamma(0)$. Bounded spatial
derivatives and the PDE give temporal Lipschitz constants
$$
J=\tfrac12\|u_{xx}\|_\infty+\Gamma K_T,\qquad
H=\tfrac12\|a_{xx}\|_\infty+\Gamma(K_T^2+L_T)
$$
for $u$ and $a$, respectively, on this strip. No derivative of $\gamma$
is used. Brownian coupling gives
$\|X_s-X_{\pi_N(s)}\|_2\le\sqrt\Delta+\Gamma\Delta$.
Subtract the Euler and diffusion equations, take a pathwise maximum over
grid times, then apply Minkowski and discrete Gronwall. With
$$
R_N=\Gamma TK_T\sqrt\Delta+
 [\Gamma T(J+\Gamma K_T)+V]\Delta,
$$
the result is
$$
\delta_N\le\left\|\max_{j\le N}|Y_j-X_{t_j}|\right\|_2
\le e^{\Gamma K_TT}R_N.
$$
Indeed the maximal norm through index $j$ is at most
$\Gamma K_T\Delta$ times the sum of its preceding values plus $R_N$;
the term $V\Delta$ is exactly the monotone quadrature bound. For the
martingale residual, Itô isometry and the same increment estimate give
$$
e_N\le K_T\delta_N+
\sqrt T\{L_T\delta_N+L_T\sqrt\Delta+(H+\Gamma L_T)\Delta\}.
$$
Thus $\delta_N,e_N=O_{\gamma,T}(\sqrt\Delta)$.
These are deductions from the compact-strip bounds and stochastic
identities, not quantitative clauses of the selected Lean statement.

Since $a$ is bounded and Lipschitz,
$d_N\le2K_TL_T\delta_N\to0$. Whenever $d_N\le1/2$,
$$
 \sqrt{2/3}\le c_j\le\sqrt2,\qquad
 |1/c_j-1|\le d_N,\qquad
 \|\alpha\|_2\le\sqrt{T(1+d_N)}.
$$
These estimates give an explicit sufficient condition for all the required
normalisers to be positive. They do not assume positivity for every
coarse mesh.

Let
$\omega_f(h)=\sup\{|f(t)-f(s)|:s,t\in[0,T],\,|t-s|\le h\}$.
The same increment bound gives
$\omega_f(\Delta)\le L_T\sqrt\Delta+(H+\Gamma L_T)\Delta$;
in particular this modulus tends to zero.
The difference between the shifted interior sum and the integral is bounded by
$$
 \left|\Delta\sum_{j=1}^{N-1}
       \frac{\mathbb E a(t_j,Y_j)}{c_j}-\int_0^T f(t)\,dt\right|
 \le TK_Td_N+TL_T\delta_N+T\omega_f(\Delta)+\Delta.
$$
The first two terms replace the normalisers and Euler positions. For the
last two, compare with the right Riemann sum over $j=1,\ldots,N$,
then remove its single terminal term $\Delta f(T)$.
Combining this with the vector and rounding-endpoint estimate gives
$$
 \begin{aligned}
 |S_{T,N}-P_*|
 \le{}&(1-T)
   +\bigl(2+\sqrt{T(1+d_N)}\bigr)e_N
   +\sqrt{\Delta(1+d_N)}\\
 &+TK_Td_N+TL_T\delta_N+T\omega_f(\Delta)+\Delta .
 \end{aligned}
$$
In particular, for each fixed minimizer and $T<1$ there are finite
$C_{\gamma,T}$ and $N_0(\gamma,T)$ such that
$$
|S_{T,N}-P_*|\le1-T+C_{\gamma,T}\sqrt{T/N}
\qquad(N\ge N_0(\gamma,T)).
$$
The constants are not uniform as $T\uparrow1$, and no numerical bound
on the minimizing coefficient has been supplied. All terms after $1-T$
tend to zero at each fixed $T<1$. Given a scalar
tolerance $\zeta>0$, first choose $T$ with $1-T<\zeta/2$, then choose
$N_0(\gamma,T,\zeta)$ so that their sum is below $\zeta/2$ for every
$N\ge N_0$. This is the required finite choice of a Gaussian spin.
The formula exposes the errors; it does not supply numerical values of
$K_T,L_T,\delta_N,e_N$ or an effective mesh threshold.
[OpenAI (2026a), Lemma 2.1][fs-reg];
[OpenAI (2026a), Proposition 7.2][fs-cons].

A diagonal can be chosen using these thresholds. For prescribed
$T_m\uparrow1$, choose increasing $N_m$ large enough to make the
mesh-dependent part of the fixed-$T_m$ bound less than $1/m$. An arbitrary increasing mesh schedule
does not follow from the iterated limit alone. For example, the scalar
array
$$
 h(T,N)=\min\{1,[N(1-T)]^{-1}\}
$$
tends to zero in $N$ at every fixed $T<1$, but
$h(1-1/N,N)=1$ for every $N\ge2$. This is an illustration of the
quantifier issue, not an asserted error law for the SK construction.
<!-- /passage:gaussian-error-budget -->

<!-- passage:gaussian-sanity-check -->

### 7.2 What fails without a minimizer

The admissible coefficient $\gamma_0=0$ makes the use of minimality in
the normalization step explicit. Its diffusion is $X_t=B_t$, and the
[zero-coefficient heat formula][fs-reg] gives

$$
u_0(t,x)=2F_{\mathrm G}\!\left(\frac{x}{\sqrt{1-t}}\right)-1,
\qquad
a_0(t,x)=\sqrt{\frac2\pi}\frac{e^{-x^2/(2(1-t))}}{\sqrt{1-t}}.
$$

Since $\mathbb E e^{-\lambda B_t^2}=(1+2\lambda t)^{-1/2}$,

$$
\mathbb E a_0(t,B_t)=\sqrt{\frac2\pi},\qquad
\mathbb E a_0(t,B_t)^2=\frac2{\pi\sqrt{1-t^2}},\qquad
q_0(t)=\frac2\pi\arcsin t.
$$

The last identity follows by integrating $q_0'=\mathbb E a_0^2$
from $q_0(0)=0$. This heat and late-step variation argument is the
zero-field specialization of [Chen, Handschy and Lerman, Theorem 6
and its proof, arXiv:1609.04368v4, pp. 13–16](https://arxiv.org/abs/1609.04368v4).
Strict convexity of $\arcsin$ gives $q_0(t)<t$
for $0<t<1$. Thus $G_0(s)=\int_s^1(q_0(t)-t)\,dt<0$ for
every $s<1$. Inserting an atom at $s$ is admissible, and its
[first variation][fs-var] is $G_0(s)/2<0$. In particular, the derivative for inserting
mass at zero is $1/4-1/\pi<0$. Hence this coefficient does not
minimize. The expository companion's §4.1 gives the same descent
directly from the constant-coefficient heat formula.

Here the Euler scheme is exact: $Y_j=B_{t_j}$ under the Brownian
coupling. Nevertheless its normalizers are

$$
c_j=\sqrt{\frac\pi2}\,(1-t_{j-1}^2)^{1/4},
$$

so they approximate this nonconstant function of time, rather than
converging uniformly to one. Already $c_1=\sqrt{\pi/2}$ for every
mesh. The directions $g_j$ remain orthonormal by construction and the
rounding still preserves conditional means; the missing input to the
value limit is the minimizing identity $\mathbb E a(t,X_t)^2=1$.

The terminal spin also survives:
$U_1=\operatorname{sgn}(B_1)$ almost surely. But its correlation is

$$
\mathbb E[U_1B_1]=\sqrt{\frac2\pi}=\mathcal P(\gamma_0),
$$

the value of this nonminimizing candidate. The negative first variation
proves that this value is strictly above $P_*$. Admissibility, exact
Euler sampling, and a spin-valued terminal martingale therefore do not
supply the minimizing normalization or identify the ground-state value.
<!-- /passage:gaussian-sanity-check -->

<!-- passage:gaussian-one-step-example -->

### 7.3 An exact one-step calculation

For a finite check of the definitions, use the admissible heat coefficient
$\gamma_0\equiv0$, whose solution has
$$
 u_0(t,x)=2F_{\rm G}\bigl(x/\sqrt{1-t}\bigr)-1,\qquad
 a_0(0,0)=\sqrt{2/\pi}.
$$
This coefficient is not a minimiser; the calculation tests the construction
and its indices, not the minimiser-dependent convergence theorem.
Take $T=4/5$ and $N=1$. Then
$$
 Y_1=\frac2{\sqrt5}Z_1,\qquad
 c_1=\sqrt{\pi/2},\qquad g_1=Z_1,\qquad
 m_1=u_0(T,Y_1)=2F_{\rm G}(2Z_1)-1.
$$
Strict monotonicity and symmetry of the Gaussian distribution function give
$$
 F_1=\operatorname{sgn}\bigl(F_{\rm G}(2Z_1)+F_{\rm G}(Z_2)-1\bigr)
     =\operatorname{sgn}(2Z_1+Z_2)
$$
almost surely. Thus the additional Gaussian is visibly the rounding
coordinate. Set $V=(2Z_1+Z_2)/\sqrt5$, a standard normal. Gaussian
regression gives $\mathbb E[Z_1\mid V]=2V/\sqrt5$ and
$\mathbb E[Z_2\mid V]=V/\sqrt5$. Since
$\mathbb E|V|=\sqrt{2/\pi}$,
$$
 A_0=0,\qquad A_1=B_1=2\sqrt{\frac{2}{5\pi}},\qquad
 B_2=\sqrt{\frac{2}{5\pi}}.
$$
Consequently
$$
 \sum_{j=0}^1A_jB_{j+1}=\frac4{5\pi}
 \quad\hbox{whereas}\quad A_1B_1=\frac8{5\pi}.
$$
Dropping the index shift changes the answer by a factor of two.
At $N=1$ the interior Riemann sum is empty and the entire product comes
from the rounding endpoint. Its later disappearance is an asymptotic
statement, not an exact finite-mesh identity. The displayed coefficients follow from exact Gaussian regression; no
numerical quadrature or finite computation is needed for this example.
<!-- /passage:gaussian-one-step-example -->

<!-- passage:algorithm -->
<a id="classical-algorithm-consequence"></a>

### 7.4 The separate finite-disorder optimization consequence

The scalar Gaussian construction is not itself an algorithm on the matrix of SK couplings. A finite-disorder algorithm is obtained by importing the theorem of El Alaoui, Montanari and Sellke. In their cited preprint, Assumption 2 asks for a strictly increasing minimizer of the zero-temperature Parisi functional on $\mathcal U$. The support theorem gives this property, and the imported attainment argument supplies the minimizer. Their Corollary 2.2 then returns, for each fixed $\varepsilon>0$, a randomized spin configuration within $\varepsilon n$ of the finite-instance maximum with probability tending to one. Its operation count is the one in the displayed Theorem 3 on p. 7; the preprint's running references call that result “Theorem 3.2.” [El Alaoui, Montanari and Sellke, arXiv:2001.00904v1, pp. 7–8][eams20].

To match that theorem's Gaussian input exactly, form a symmetric matrix with
$$
A_{ij}=J_{ij}/\sqrt n\quad(i<j),\qquad
A_{ii}=\sqrt{2/n}\,G_i,
$$
where the $G_i$ are additional independent standard Gaussians. For $\widehat H_n(x)=\tfrac12x^{\mathsf T}Ax$,
$$
\mathbb E\widehat H_n(\sigma)\widehat H_n(\tau)
=\frac{(\sigma^{\mathsf T}\tau)^2}{2n},
\qquad
\widehat H_n(\sigma)=H_n(\sigma)+\frac1{\sqrt{2n}}\sum_iG_i.
$$
The final term is the same for all spin configurations. Therefore the maximizing spin and every optimization gap are unchanged. The extra diagonal randomness is included in the algorithm's randomness. This checks the input convention without changing the target optimization problem. [OpenAI full-support manuscript, algorithm application, lines 30–47][fs-algorithm].

The imported operation count is
$C(\varepsilon)(\chi+n)+n\chi_1$, where $\chi$ is the cost of evaluating the full gradient and $\chi_1$ is the cost of one coordinate of the distinct-index gradient. Here $\nabla\widehat H_n(x)=Ax$ costs $O(n^2)$, and one coordinate of $\nabla H_n(x)$ costs $O(n)$. The resulting count is $C(\varepsilon)n^2$, with $C(\varepsilon)$ independent of $n$. Real sums and multiplications have unit cost in the cited model; the scalar functions and normalizers prescribed for the chosen accuracy are part of that construction. This statement supplies neither a bound for their numerical preprocessing nor a finite-precision bit-complexity bound. [El Alaoui, Montanari and Sellke, Remark 2.1 and Theorem 3, p. 7][eams20]; [OpenAI full-support manuscript, lines 1–11 and 49–59][fs-algorithm].

A distinct classical construction is [Jekel, Sandhu and Shi,
*Potential Hessian Ascent*, arXiv:2408.02360v3, Assumption 1.4 and
Theorem 1.5](https://arxiv.org/abs/2408.02360v3).
Its hypothesis is finite-temperature interval support
$\operatorname{supp}\mu_\beta=[0,q_\beta^*]$, with $q_\beta^*\to1$.
Its inputs include oracles for the Parisi PDE, its derivatives and the
minimizer's distribution function. For each fixed accuracy the stated
runtime is polynomial in $n$, with an exponential dependence on inverse
accuracy; it does not include implementing those oracles. Its Ginibre
Hamiltonian has covariance $nR^2$: on spins it has the law
$\sqrt2 H_n$ plus a Gaussian term independent of the configuration. Thus its energy
and accuracy must be divided by $\sqrt2$ to compare with this paper's
normalization. This is a separate algorithm theorem with separate
analytic inputs, rather than another interpretation of the finite
Gaussian spin in §7.

The consequence is classical. It does not supply an efficient construction of QAOA angles, a quantum depth bound, or a clause of either selected Lean interface. The proof of the separate QAOA statement still requires its rooted energy, synthesis, seed-removal and transfer arguments.
<!-- /passage:algorithm -->

<a id="formal-interfaces"></a>

## 8. What the formal statements establish

<!-- passage:formal -->

### 8.1 The support statement and the derivative bridge

The first formal statement assumes a Brownian system and an admissible
minimizer. It supplies a Stieltjes measure, an associated diffusion, full
relative support and strict increase, and the two moment identities for
every associated diffusion. Its proof assembles contact, exclusion of a
terminal plateau, curvature for positive and zero constant intervals,
and uniqueness to transfer the moments between associated diffusions.
This describes the inspected proof's mathematical route; no successful
research-target replay is claimed. Its quantifiers are
$\forall W\,\forall\gamma$, followed by the minimizer hypothesis;
it supplies both witnesses on the given Brownian system. The moment
conclusion is universal over every diffusion satisfying the specified
equation, and covers exactly $0\le t<1$. The diffusion equation itself
holds through time one, simultaneously for all those times outside
one null set. Controls are progressive for the natural filtration of
Brownian increments and bounded by one pointwise. These are not
additional regularity or minimizer-existence assumptions. See the
[exact support statement][support-type] and the companion
source-interface review.

There is one useful distinction between the manuscript's first variation
and its formal counterpart. The formal result initially gives a derivative
along chord lengths $1/(n+1)$. For this particular control functional,
that sampled limit determines the ordinary feasible right derivative.
With a control fixed, the terminal absolute value is convex in the
coefficient while the penalty is linear. The supremum over the same
control class, and then subtraction of the linear Parisi penalty,
preserve convexity. The secant slopes therefore vary monotonically as
the chord shortens; each intervening chord lies between two successive
sampled chords and has the same limiting slope. If $\eta$ is an
integrable feasible direction, choose $\varepsilon_0>0$ so that
$\gamma+\varepsilon_0\eta$ is admissible and rescale the chord. This
bridge is an ordinary deduction from the definitions and sampled limit,
not an additional formally named theorem.

At the origin, the manuscript smoothly extends auxiliary quotient
variables. The formal density proof instead works on the positive
half-line, controls the zero flux at the origin and reflects. What must
agree is the resulting integrated inequality; auxiliary values at zero
need not coincide. In particular, the declared generic flux lemma has
a global derivative hypothesis that is not the supplier used here:
the finite-density proof uses the Gaussian half-line coercivity lemma
and reflection. A totalized quotient value at zero cannot silently
satisfy the generic global hypothesis. The precise source spans are in
the correspondence record.

### 8.2 The separate scalar statement

The second formal statement has three clauses. Given a minimizer and an
associated diffusion, it establishes convergence of the finite-spin
ground-state values, a bounded martingale with a spin-valued terminal
limit, convergence of the gradient and the value identities. Under the
same hypotheses and fixed $0<T<1$, it gives eventual positivity of the
Gaussian normalizers and convergence of the finite coefficient sum.
Its final clause identifies ground-state and Parisi values assuming a
minimizer alone: the proof constructs a diffusion for that clause. None
of the clauses constructs a minimizer. The separate convergence clause
establishes existence of the finite-spin limit.

The index match in the Gaussian statement is exact. For
$\Delta=T/N$ and $t_j=j\Delta$, the Euler path uses
$Z_1,\ldots,Z_N$ and produces $Y_0,\ldots,Y_N$.
The source normalizer indexed from zero corresponds to manuscript
$c_1,\ldots,c_N$; its eventual positivity covers precisely those
normalizers. A separate $Z_{N+1}$ performs mean-preserving rounding:
it enters $B_{N+1}$, not another Euler increment. Thus the finite sum is
$\sum_{j=0}^{N}A_jB_{j+1}$ with $A_0=0$, using exactly the displayed
index ranges. Total definitions at $N=0$ make no extra mathematical
claim about the construction for $N\ge1$. More explicitly, the
zero-based formal quantities `coordinate N j`, `rawCoefficient ... j`
and `normalizer ... j` correspond to $Z_{j+1}$,
$a(t_j,Y_j)$ and $c_{j+1}$ for $0\le j<N$. The positivity quantifiers
are $\exists N_0\,\forall N\ge N_0\,\forall j<N$, simultaneously over
the growing mesh, for each already fixed $T$. The extra coordinate
with formal index $N$ is $Z_{N+1}$. The formal martingale stops at its
terminal random variable $U$ for all later times; $U^2=1$ almost surely,
and the gradient converges to $U$ almost surely and in $L^2$ from below
one. The internal terminal-gradient lemma proves $UX_1=|X_1|$
without requiring $X_1$ to have no atom at zero. That identity is used
inside the implementation; it is not an extra conjunct of the endpoint. See the [scalar statement][value-type] and its
complete dictionary.

### 8.3 A separate route to scalar contact

The scalar implementation does not import the full-support development.
Its input is the same kind of variational moment identity, but it proves
that identity by a different deterministic contradiction. This source
route explains why the two selected theorem statements can be separately
implemented even before any formal translation between their models.

In the scalar model put $q(t)=\mathbb E[u(t,X_t)^2]$,
$f(t)=q(t)-t$ and $G(t)=\int_t^1f(s)\,ds$. The source first obtains
$G\ge0$, $G(1)=0$, $q(0)=0$ and $G'=-f$. Compact-mass variations
also show that on any interval where $G>0$ the coefficient is constant:
if its cumulative mass increased between two points there, integration
of the strictly positive $G$ against that positive increment would
contradict the mass-removal variational inequality. This is the content
of the [scalar contact-integral argument][scalar-contact-integral].

Suppose now that $G(x)>0$ for some $0<x<1$. Choose the component
$(a,b)$ of this positivity set containing $x$, allowing $a=0$ or
$b=1$. Its coefficient is constant, say $c\ge0$, and $G(b)=0$.
At the left endpoint, $f(a)=0$: this is the contact derivative when
$a>0$, and $q(0)=0$ when $a=0$.

If $c>0$, one also has $G(a)=0$. The only extra case is $a=0$:
right continuity gives $\gamma(0)=c>0$, so the mass-removal condition
at that initial atom forces $G(0)=0$. The mean-value theorem on
$[a,x]$ and $[x,b]$ now provides points $r<s$ with
$f(r)<0<f(s)$. There is a later point $z\le b$, with $z<1$, for
which $f(z)\le f(s)$. For $b<1$ take $z=b$, since contact gives
$f(b)=0$. For $b=1$, choose $z$ sufficiently close to one and use
$f(z)=q(z)-z\le1-z<f(s)$.

The three intervals $[a,r]$, $[r,s]$ and $[s,z]$ therefore have
secant slopes for $f$ of signs respectively negative, positive and
nonpositive. Applying the mean-value theorem once more gives three
ordered points where $f'$ has those signs. This is impossible when
$f'=q'-1$ is convex: its middle value cannot exceed the larger of
its two exterior values. The scalar source supplies precisely this
nonstrict convexity on a constant interval. See
[the positive-hump argument and its endpoint condition][scalar-hump]
and [the curvature-moment convexity lemma][scalar-convexity].

If $c=0$, the source instead gives convexity of $f=q-t$. A mean-value
argument between $x$ and $b$ gives $f(s)>0$; the same right-endpoint
argument produces $z>s$ with $f(z)\le f(s)$. Since $f(a)=0$,
$$
\frac{f(s)-f(a)}{s-a}>0\ge
\frac{f(z)-f(s)}{z-s},
$$
contradicting monotonicity of adjacent secant slopes of a convex
function. This case does not need $G(a)=0$; see
[the zero-coefficient hump lemma][scalar-zero-hump].

Thus $G$ cannot have a positive component, and $G\equiv0$ on
$(0,1)$. Differentiation gives $q(t)=t$ there, with the origin supplied
separately. The [scalar assembly][scalar-contact-assembly] then obtains
the unit curvature moment, finite Gaussian approximation and terminal
value identities from this contact equality. Nonstrict convexity suffices
for this scalar route. The strict curvature estimate in Sections 4–5
has the further job of excluding gaps in Stieltjes support. These are
source-level proof reconstructions, not a fresh Lean acceptance or a
claim that the two formal models have been composed.

### 8.4 Relating the two statements

To claim a formal composition of the full-support and scalar statements,
one would have to identify the coefficients on $[0,1)$, Brownian laws
and filtrations, and associated diffusion laws. One would also have to
change variables between absolute-time and elapsed-time control integrals
while preserving admissibility, payoff and supremum. Equality of the
resulting values would then have to transport derivatives and minimisation,
with the same minimiser and diffusion witnesses. These translation
theorems are not supplied by mathematical resemblance alone. The two
separate implementations and the manuscript's mathematical sequence in
Sections 3–7 remain meaningful without asserting that formal composition.

### 8.5 The scalar implementation's own upper and lower bounds

The scalar implementation constructs its regularity constants and contact
identities internally. Its finite-spin limit follows from superadditivity
and a uniform upper bound. A finite-profile Gaussian interpolation gives
the upper bound $P_*\le\mathcal P(\gamma)$ for every admissible
coefficient. In the other direction, the normalized rounded finite
Gaussian sum is bounded above by $P_*$; contact and the fixed-strip
mesh limit give $\int_0^T\mathbb E a\le P_*$. Terminal assembly then
gives $\mathcal P(\gamma)\le P_*$ at the minimizer, and antisymmetry
yields equality. Thus its proof route is not simply an invocation of the
literature's Parisi formula used in §6. The third endpoint clause
constructs its diffusion before applying this equality. The exact
suppliers can be read in the pinned
[upper-bound proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/GroundState/WeakGuerra.lean#L117-L142),
[finite-sum lower bound](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/GroundState/LiteralLower.lean#L14-L27)
and [contact assembly][scalar-contact-assembly], with the hypotheses
explained in §§8.2–8.3. These are source-inspection conclusions, with
the replay outcome in §11.
<!-- /passage:formal -->

<a id="qaoa-construction"></a>

## 9. From the scalar formula to one ordinary QAOA word

<!-- passage:qaoa -->
On a single spin, let $Z=\operatorname{diag}(1,-1)$ and
$X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$; $Z_i$ and $X_i$ act on spin $i$
and as the identity on the other spins. Also set
$Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ and
$|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$.
Then $X|\pm\rangle=\pm|\pm\rangle$ and $Z|+\rangle=|-\rangle$. The cost and mixer are
$$
C_{n,J}=n^{-1/2}\sum_{i<j}J_{ij}Z_iZ_j,\qquad B_n=\sum_iX_i.
$$
The cost is diagonal in the spin basis with eigenvalues $H_n(\sigma)$.
A depth-$p$ state is
$$
|\psi_{n,p,J}(\boldsymbol\gamma,\boldsymbol\beta)\rangle
=e^{-i\beta_pB_n}e^{-i\gamma_pC_{n,J}}\cdots
 e^{-i\beta_1B_n}e^{-i\gamma_1C_{n,J}}|+\rangle^{\otimes n}.
$$
Here the real angle vectors $\boldsymbol\gamma,\boldsymbol\beta$ are
deterministic; $\boldsymbol\gamma$ is separate from the Parisi coefficient
$\gamma(t)$. A *word* means a finite ordered product of cost and mixer
exponentials. Its pattern and angles are fixed independently of $n,J$;
its cost operator depends on $n,J$. Define
$$
v_p(\boldsymbol\gamma,\boldsymbol\beta)
=\lim_{n\to\infty}\frac1n\mathbb E_J
 \langle\psi_{n,p,J}|C_{n,J}|\psi_{n,p,J}\rangle,
\qquad Q_p=\sup_{\boldsymbol\gamma,\boldsymbol\beta\in\mathbb R^p}v_p.
$$
The fixed-depth, fixed-angle infinite-size limit is the input from
Farhi, Goldstone, Gutmann and Zhou; it does not contain the later depth
conclusion; see [Farhi, Goldstone, Gutmann and Zhou (2022)](https://arxiv.org/abs/1910.08187v4).
The source target is
$\lim_{p\to\infty}Q_p=P_*$. A cost expectation is bounded above by its
maximum eigenvalue, and zero-angle padding makes $Q_p$ nondecreasing.
It therefore suffices to construct one finite word for every accuracy.
Fixed-instance convergence at increasing depth is a different quantifier
order. Farhi, Goldstone and Gutmann's original QAOA argument obtains that
convergence by adiabatic evolution and its Trotter approximation, with depth
allowed to depend on the instance; it does not supply the size-independent
word required here. [Farhi–Goldstone–Gutmann (2014), equation (10) and
§VI, pp. 10–11](https://arxiv.org/abs/1411.4028v1);
[OpenAI (2026b), Theorem 1.1][q-intro].

<!-- /passage:qaoa -->

<!-- passage:qaoa-rooted -->

### 9.1 Rooted realisation and the observable it preserves

The fixed-depth spin–boson representation has an antecedent in
[Boulebnane et al., Theorem 2 (informal), equations (10)–(11), p. 3][spin-boson]:
as the degree grows with depth fixed, the symmetric tree state converges
to a spin coupled to finitely many bosonic modes. The manuscript credits
that representation, then proves the occupation, insertion and
surrounding-circuit estimates needed below. Its additional task is to
control the energy observable and substitutions inside a circuit, beyond
identifying a limiting state. [OpenAI (2026b), §2][q-fock].

On a rooted tree, factor a circuit as $U=(\bigotimes_jU_j)u$,
where each $U_j$ contains operations wholly in child subtree $j$.
Conjugating a root observable $P$ reduces to $u^*Pu$; its insertion
vector is $u^*Pu\,\mathrm{vac}$, centered when its vacuum mean is zero.
This factorization is why child operations enter the recursion below.
The first change of setting preserves a specified quadratic form. At
height zero the pointed space is
$\mathsf k=\mathbb C^2\otimes L^2(\text{seed})$, with distinguished vector
$\omega=|+\rangle\otimes1$. Recursively,
$$
\mathcal H_0=\mathsf k,\qquad
\mathcal H_{h+1}=\mathsf k\otimes\Gamma_s(\mathcal H_h^\circ),
$$
where $\mathcal H_h^\circ$ is the orthogonal complement of the
vacuum and $\Gamma_s$ is symmetric Fock space. A particle here is one
child subtree whose state differs from its vacuum. It is not one
physical spin. The occupation embedding identifies a symmetric state
with $m$ nonvacuum children among $D$ available children with its
$m$-particle vector, using the factor $\binom Dm^{-1/2}$.
Adding empty descendants gives compatible embeddings between heights.
[OpenAI (2026b), §2, pointed spaces and occupation embeddings][q-fock].

For a child direction $f$, write
$q(f)=a^*(f)+a(f)$ and $W(f)=e^{iq(f)}$. Explicitly,
$\Gamma_s(H)=\bigoplus_{m\ge0}H^{\otimes_s m}$, with vacuum $\Omega$
in sector zero. On sector $m$,
$a^*(f)\psi=\sqrt{m+1}\operatorname{Sym}(f\otimes\psi)$, and $a(f)$
is its adjoint. The number operator is multiplication by $m$; more
generally $d\Gamma(A)$ sums $A$ over those $m$ child factors. The
vacuum characteristic function
$\langle\Omega,e^{itq(f)}\Omega\rangle=e^{-t^2\|f\|^2/2}$ fixes the
Gaussian normalization.
In the real classical sector, a centred child vector $f$ produces a
parent Gaussian position $\mathsf G(f)=q(f)$ with
$$
\mathbb E[\mathsf G(f)\mathsf G(g)]=\langle f,g\rangle,
\qquad
\|[\mathsf G(f)-\mathsf G(g)]\mathrm{vac}\|=\|f-g\|.
$$
The receiving root's own seed is a separate, independent tensor factor.
The root shift
$$
\mathsf Lf=\omega\otimes a^*(f)\Omega
$$
is an isometry on centred vectors, and is extended by zero on the
vacuum. Its adjoint extracts the root-vacuum, one-child component,
including a constant receiving-root seed. For a classical function of
orthonormal Gaussian positions, this is its first Gaussian chaos.
These covariance, independence and projection properties have distinct
roles in the next calculation.
[OpenAI (2026b), §2, root shift and classical first chaos][q-root-energy]
[OpenAI (2026b), §2, classical Gaussian positions][q-gaussian].

Start with the standard root seed $g_0=S$ and recursively set
$Z_{j+1}=\mathsf G(g_j)$. Suppose $g_0,\ldots,g_{j-1}$ are centred
orthonormal vectors. The covariance identity gives independent standard
normals $Z_1,\ldots,Z_j$. In the scalar construction of §7, the multiplier
of $Z_j$ in $g_j$ depends only on its predecessors. Conditional centring
therefore makes $g_j$ orthogonal to $g_1,\ldots,g_{j-1}$, and the chosen
normaliser $c_j$ gives unit norm. Independence of the receiving-root
seed gives orthogonality to $g_0$. This closes the induction. Compatible
height embeddings ensure that the earlier variables are the same
variables when the formula is embedded at greater height.

Oddness of $u$ and evenness of $a$ make $Y_j$ and $g_j$ odd under
simultaneous seed reversal. The extra centred rounding variable
$2F_{\rm G}(Z_{N+1})-1$ is odd as well, so $F_N$ is centred. It is
independent of the receiving-root seed, hence
$\langle F_N,g_0\rangle=0=A_0$. With $A_j,B_{j+1}$ as in §7,
first-chaos projection gives
$$
\mathsf L^*F_N=\sum_{j=0}^NB_{j+1}g_j,\qquad
\mathcal E(F_N):=\operatorname{Re}\langle F_N,\mathsf LF_N\rangle
 =\sum_{j=0}^NA_jB_{j+1}.
$$
Thus the construction identifies both the scalar law and the required
rooted energy. The Gaussian covariance rule does not declare distinct
calculations on shared descendant subtrees independent.
[OpenAI (2026b), §3, “A finite Gaussian formula and its rooted energy”][q-rooted-classical].

The connection to an edge observable is another statement. Let $f_D$ be
centred, invariant under rooted permutations of complete child
subtrees, and supported at a fixed finite radius. Suppose its occupation
embedding converges strongly to $v$, with a uniformly bounded expected
top-generation occupation $\langle f_D,\mathsf Nf_D\rangle$. Put
$M=D+1$ and $R_M=\sqrt{1-\mathsf N/M}$. The source's exact edge
decomposition is
$$
\langle f_{D,i},f_{D,j}\rangle
 =\frac2{\sqrt M}\operatorname{Re}\langle\mathsf L^*f_D,R_Mf_D\rangle
   +\varepsilon_D,
\qquad
|\varepsilon_D|\le\frac{\langle f_D,\mathsf Nf_D\rangle}{M}.
$$
Vacuum deletion also gives
$\|R_Mf_D-f_D\|^2\le M^{-1}\langle f_D,\mathsf Nf_D\rangle$.
Consequently,
$$
\lim_{D\to\infty}\frac{\sqrt D}{2}
 \langle f_{D,i},f_{D,j}\rangle=\mathcal E(v).
$$
Strong convergence alone does not control the scaled remainder. The
occupation estimate is supplied later for the relevant finite circuits.
The occupation assumption cannot be dropped merely because vectors
converge in norm. For orthogonal unit vectors $e_m$ in sector $m$,
$\psi_k=\sqrt{1-1/k}\,\Omega+k^{-1/2}e_{k^2}$ tends to $\Omega$
in norm, whereas $\langle\psi_k,\mathsf N\psi_k\rangle=k$.

The elementary continuity bound
$$
|\mathcal E(v)-\mathcal E(w)|
 \le(\|v\|+\|w\|)\|v-w\|
$$
will control every subsequent approximation after the observable has
been identified. [OpenAI (2026b), §2, “Energy as a root shift,” including
its exact finite-degree decomposition][q-root-energy].

<!-- /passage:qaoa-rooted -->

<!-- passage:qaoa-regularization -->

### 9.2 Finite regularisation and the calculus needed for compilation

Fix $T,N$ first. The independent continuous rounding coordinate makes
the event at the sign discontinuity null. Bounded continuous odd
approximations to that sign therefore converge in $L^2$ by dominated
convergence. If the bounded output is $m^*$, shrink it to
$(1-\kappa)m^*$, with fixed $0<\kappa<1$, before taking
$\theta_\kappa=\tfrac12\arcsin((1-\kappa)m^*)$. This margin keeps
the derivative of inverse sine bounded on its used range; the output
loss is at most $\kappa$ in $L^2$. Then truncate the transmitted
functions and approximate the resulting bounded maps by trigonometric
polynomials. The source makes these choices from output
toward leaves: each outer Lipschitz function is fixed before its inputs
are approximated. The Gaussian isometry above converts an error in a
transmitted child vector into the same $L^2$ error in its receiving
position. Energy continuity then bounds the accumulated loss. The
bounded output has the form $m=\sin(2\theta)$; it is the transmitted
columns that are bounded, while the Gaussian fields themselves remain
unbounded. [OpenAI (2026b), §3, bounded trigonometric approximation][q-bounded-classical].

Finite vertex types make the calculation suitable for controls on a
physical tree. Every aggregation excludes the receiver's type, the
ancestor types along its active branch, and reserved helper types.
The target spins are disjoint from the types supplying their cross-edge
parameters. This makes the all-neighbour calculation agree with the
intended descendant calculation. The types can be encoded together
with a Gaussian seed in one raw Gaussian variable: its sign supplies
the odd symmetry, while disjoint binary digits of a uniform transform
of its absolute value supply independent coordinates. The resulting
finite type label is even and the Gaussian seed is odd under reversal.
The associated pullback preserves vacuum, parity and $\mathsf L$.
Thus adding types preserves the energy identification, rather than
assuming an additional circuit resource. [OpenAI (2026b), §3, colours,
exclusions and helpers][q-colors].

For the already fixed formula, the exclusion estimate is
$$
\|m^{\rm col}-m\|^2\le C(\alpha+p_H),
$$
where $\alpha$ is the largest nonhelper type mass and $p_H$ is the total
helper mass. Its constant is independent of the number of types. The
proof uses orthogonality of the disjoint masks before applying the
Lipschitz estimate in the original, fixed list of formula coordinates.
Treating the refined types as an arbitrary growing list of independent
arguments would not provide this bound. The resulting classical
near-optimality proposition supplies a finite bounded odd formula,
zero on helpers, with energy as close to $P_*$ as required.
[OpenAI (2026b), §3, “Type exclusion at small cost” and “Classical
near-optimality in synthesis form”][q-colors].

**Which convergence permits the later substitutions?**
The gate calculus uses recursive weights
$\mathsf W_{h+1}=\mathsf W_0+d\Gamma(\Lambda_h)$, where
$\Lambda_h$ is the previous weight restricted to the centred child
space. The local weight includes the unbounded raw seed when needed.
Its smooth domain is the intersection of all weighted domains. Smooth
bounds mean polynomial bounds, with a finite loss of weight powers,
for the maps, their adjoints and every specified parameter derivative.
The finite height, fixed expression and fixed number of channels matter
in these estimates. Strong convergence together with uniform stronger
weighted bounds gives convergence in each weaker weighted norm by a
spectral cutoff. This is the topology in which one replaces a gate
inside a fixed surrounding circuit.
[OpenAI (2026b), §2, weights and the topology of convergence][q-weights].

One of the essential inputs retains a term beyond the Gaussian field.
Let $K_D(x)$ be a smooth unitary family with $K_D(0)=1$, uniformly
controlled derivatives and adjoint derivatives that converge smoothly
in the stated weighted topology to those of a limiting family $K$,
and centred first vacuum derivatives. Write
$K_\alpha=\partial_\alpha K(0)=iT_\alpha$ and
$K_{\alpha\lambda}=\partial_\alpha\partial_\lambda K(0)$.
For a fixed finite parameter list $a$, the source proves
$$
K_D(a/\sqrt D)^{\otimes D}\longrightarrow
\exp\!\left\{
 i\sum_\alpha a_\alpha q(T_\alpha\mathrm{vac})
 +\frac12\sum_{\alpha,\lambda}a_\alpha a_\lambda
 \left\langle K_{\alpha\lambda}
             +\tfrac12\{T_\alpha,T_\lambda\}\right\rangle_0
\right\}.
$$
The second term is imaginary by unitarity. It survives because a
second-order change of size $D^{-1}$ occurs in each of $D$ children.
Its scalar coefficients become a possibly nonconstant controlled
operator when commuting signals replace $a$. For example,
$K(x)=e^{ix^2}$ has zero first derivative at zero but
$K(a/\sqrt D)^D=e^{ia^2}$ exactly. Keeping only the first derivative
would miss even this elementary contribution. The example explains
why the term is necessary; the source's weighted product lemma supplies
the general convergence and domain bounds.
[OpenAI (2026b), §2, “Products of small unitaries”][q-unitary].

Commuting substitution is justified through a joint spectral calculus
and Fourier estimates. It requires the physical control algebra, the
self-adjoint signal operators and receiving seed to strongly commute,
with joint exponential and weighted derivative bounds as stated in the
source. This is stronger than a formal commutator identity on one domain. It does not require a nonsingular
covariance matrix or an inverse Gram matrix. Exclusions establish that
commuting algebra before a preceding circuit is conjugated through it;
conjugation preserves commutation even when the signals share
descendants. [OpenAI (2026b), §2, “Smooth commuting substitution”][q-substitution].

The exact cut recursion records the effect of such shared lower
calculations. Let $y$ be the incoming boundary data, $V(y)$ the root
matrix, and $m(y)$ its outgoing signals in the current frame. Factoring
out the operations wholly inside each child gives
$$
E^{[d]}(y)=V(y)\prod_{j\ \mathrm{child}}
 K_j^{[d-1]}(D^{-1/2}m(y)),\qquad
K^{[d]}(y)=u^*E^{[d]}(0)^*E^{[d]}(y)u.
$$
Every ratio $K^{[d]}$ equals one at zero. Nevertheless $m(0)$ generally
does not vanish, because removing the parent input leaves the root's
own signals. The actual zero-boundary root update is
$u_{\rm new}=E^{[d]}(0)u$. It is not recovered by setting the entire
ratio to one and discarding the baseline operation. Applying the
unitary product lemma to this recursion, and then commuting
substitution, is the source's smooth gate calculus. Its replacement
statement covers a fixed finite surrounding sequence and its required
parameter derivatives; it does not assert uniformity for arbitrary
sequences whose length or channel count grows.
[OpenAI (2026b), §2, smooth gate calculus and its cut recursion][q-gate-calculus].

<!-- /passage:qaoa-regularization -->

<!-- passage:qaoa-synthesis -->

### 9.3 Seeded synthesis: helper contraction and nested responses

Temporarily add longitudinal seed gates
$\exp(-it\sum_i s_iZ_i)$, using an independent Gaussian $s_i$ at each
vertex and reusing that same variable whenever a later seed gate acts
there. The synthesis theorem turns the finite classical formula into
a finite word of these gates, costs and mixers. Its ideal local
$Y$ rotations have $Z$ insertion
$$
v_{\rm cl}=|+\rangle m+|-\rangle n,\qquad m=\sin(2\theta).
$$
The second term does not contribute to $\mathcal E$: $\mathsf L$ puts
the root spin in $|+\rangle$, and shifting the $|-\rangle$ term puts a
spin excitation into a child, orthogonal to the classical sector.
Thus $\mathcal E(v_{\rm cl})=\mathcal E(m)$.
[OpenAI (2026b), §2, classical rotations][q-root-energy]
[OpenAI (2026b), §4, “Classical synthesis”][q-synthesis-statement].

There are two different approximation operations. First, seed
conjugations of $X$ generate $\cos(2ts)X$ and $\sin(2ts)Y$.
Trigonometric approximation and matrix commutators give the required
bounded measurable masked spin controls. Sign averaging of masked
$X$ flips isolates an interaction between chosen types; the cost
terms commute, so this isolation is exact. This sign averaging is the
refocusing method of [Jones and Knill (1999), §II, p. 2](https://arxiv.org/abs/quant-ph/9905008v1):
orthogonal sign rows cancel unwanted Ising couplings, while identical
rows retain a selected coupling. The source applies it to the finite
partition of seed masks. Finite commutator products
then approximate the desired pointwise matrices with smooth bounds.
They can be substituted after the surrounding circuit has been fixed.
The local masks are measurable functions of the seed; smoothness is
required in the continuous aggregate inputs, not in the mask labels.
[OpenAI (2026b), §4, elementary masked controls and matrix products][q-masked-controls].

The second operation implements an aggregation. Let $I$ be the
receiver region, $J$ the sender region, and $K$ an unused helper region
of fixed positive probability $p_K$. They are disjoint. The lower
seed-only formula $f$ excludes these regions along its cross-edge
paths. With $A_{ij}=D^{-1/2}1_{i\sim j}$, the desired propagation has
generator
$$
H=\sum_{i\in I,j\in J}P_iA_{ij}f_j.
$$
Partition $J$ into parts $J_l$ of probabilities $p_l$. Two levels of
spin commutators generate the commuting Hamiltonian
$$
\widetilde H_{\mathcal P}
 =\frac1{p_K}\sum_l\sum_{i\in I,\,j,j'\in J_l,\,k\in K}
 P_iA_{ij}X_jA_{jk}X_kA_{kj'}X_{j'}f_{j'}.
$$
When $j=j'$, the two sender factors cancel. If the helper spin has
$X_k=1$, this backtracking path reproduces $H$, multiplied by the
ratio $\#\{\text{helper neighbours}\}/(Dp_K)$, which tends to one.
Terms with $j\ne j'$ are simple paths and must disappear under
partition refinement. The factor $1/p_K$ is harmless only after a
positive helper mass has been fixed.
[OpenAI (2026b), §4, helper generators and contraction][q-helper-statement].

Helper pinning is a statement about every helper spin in the light
cone. Its finite-degree projection is
$$
\Pi_{K,V}=\prod_{v\in V}
 \left[1-1_K(s_v)\frac{1-X_v}{2}\right].
$$
It retains the seed variables and helper-labelled descendant spaces
while fixing the helper spins in $|+\rangle$. The ideal propagation,
the exact Hamiltonian $\widetilde H_{\mathcal P}$, and the surrounding
gates that avoid $K$ preserve this compressed space. Multiplying an
insertion by $1_{K^c}(s_o)$ only masks the root label and does not impose
this descendant condition. Individual finite commutator factors may
leave the compressed space. Accordingly, the proof first establishes
the exact contraction there, then chooses finite commutator products
on the full space to approximate it. [OpenAI (2026b), §4,
“Simultaneous helper contraction”][q-helper-statement].

The estimate controlling a growing partition is
$$
\rho^2=\sum_l p_l^2\le p_J\max_l p_l\longrightarrow0.
$$
At a helper root, each part supplies two commuting fields with columns
$d_l,e_l$ on disjoint sender masks, of weighted norm at most
$C\sqrt{p_l}$. The remaining correction is a sum of centred quadratics
$$
\sum_l\bigl[q(d_l)q(e_l)-\langle d_l,e_l\rangle\bigr].
$$
Normal ordering and disjoint-mask orthogonality bound its quadratic
kernels by $C\rho$ in Hilbert–Schmidt norm. The source separately
bounds the exponentials in the weighted topology, uniformly in the
number of parts. Smallness of the generator on smooth vectors alone
would not justify inserting its exponential into the surrounding
circuit. [OpenAI (2026b), §4, “Quadratics with many orthogonal
columns”][q-helper-quadratics].

The helper estimate alone does not control all cuts. Put
$\epsilon_{\mathcal P}=\max_l\sqrt{p_l}$. The receiver and helper
corrections have weighted size $O(\rho)$; a sender correction is
$O(\sqrt{p_l})$ conditional on its label. The remaining lower-formula
responses have size $O(\epsilon_{\mathcal P})$. Both quantities tend
to zero with $f$, the number of lower channels and $p_K>0$ fixed.

There remains a response inside the lower formula $f$. A cut can pass
through a descendant used to compute $f$, rather than through one of
the displayed three-edge paths. The source first writes the exact
difference of the affected Hamiltonian terms before applying the
preceding subtree circuit. That circuit is fixed with respect to the
new cut input. Exclusions ensure that the downward coefficients are
independent of that active boundary argument. The resulting additive
cut-response rule retains both first derivatives and mixed second
derivatives:
$$
\sum_\alpha a_\alpha q(H_\alpha\mathrm{vac})
 +\frac12\sum_{\alpha,\lambda}a_\alpha a_\lambda
       \langle H_{\alpha\lambda}\rangle_0.
$$
Here $H_\alpha$ is centred by parity; no limit of the extensive
zero-input Hamiltonian is required. The self-adjoint generator is
obtained from the limiting time group of cut ratios.
[OpenAI (2026b), §2, “Additive cut responses”][q-additive-response].

After substituting the signals of a lower formula, a boundary
difference contains, in particular,
$$
\begin{aligned}
&\sum_\alpha[m_\alpha(y)-m_\alpha(0)]q(r_\alpha)\\
&\quad+\frac12\sum_{\alpha,\lambda}
 [m_\alpha(y)m_\lambda(y)-m_\alpha(0)m_\lambda(0)]
 c_{\alpha\lambda}.
\end{aligned}
$$
The mixed coefficients $c_{\alpha\lambda}$ must remain even when two
channels share descendants. At the actual root there is no parent
input to subtract: the corresponding unsubtracted $m(0)$ terms enter
the root update. The source propagates small terminal responses
through the fixed depth and fixed list of lower channels. It refines
the calling sender mask while keeping those lower formulas fixed.
This is what controls all cuts in a simultaneous replacement of
several calls. A root-seed scalar phase may remain on helper labels;
it cancels in insertions and child conjugations.
[OpenAI (2026b), §4, lower-formula responses and completion of the
contraction proof][q-helper-responses].

Compilation now proceeds from outer aggregations to inner ones.
Reserve a separate unused helper type for each aggregation rank. At
a given rank, establish the simultaneous exact contraction, fix the
sender partitions, and only then choose finite commutator
approximations. Subsequent inner calls use their own helpers, which
remain unused. Each inner accuracy is chosen after its surrounding
finite sequence is fixed. This order avoids assuming uniformity over
all helper masses, ranks or circuit lengths.
[OpenAI (2026b), §4, order of compilation][q-compilation].

If the resulting insertion $v$ obeys
$\|1_{H^c}(v-v_{\rm cl})\|<\eta$, seed commutation and unitarity give
$\|1_Hv\|=\sqrt{p_H}$. First omit the helper part of $v$, at energy cost at most
$2\sqrt{p_H}$. Compare the two insertions projected off helpers;
their norm difference is below $\eta$, so their energies differ by
at most $2\eta$. The projected classical insertion still has energy
$\mathcal E(m)$ because $m=0$ on helpers. Thus
$$
|\mathcal E(v)-\mathcal E(m)|\le2\eta+2\sqrt{p_H}.
$$
All projected insertion vectors have norm at most one. This completes the
interface from a bounded classical formula to a finite seeded word.
It uses the source's smooth gate and helper-contraction theorems; it
is not a consequence of the scalar theorem or of a finite-degree
central limit theorem alone.
[OpenAI (2026b), §4, synthesis statement and its proof][q-synthesis-statement].

<!-- /passage:qaoa-synthesis -->

<!-- passage:qaoa-seed -->

### 9.4 Removing the seed controls without changing their joint law

Seed removal must simulate one Gaussian variable per vertex, reused
at all seed gates. Replacing each occurrence with a fresh independent
Gaussian would change the circuit. The source proves a theorem for
any already fixed finite seeded word and any energy tolerance, producing
one finite ordinary word. Its proof works in the fixed-word tree
limit; it does not take a degree limit simultaneously with its small
parameter. [OpenAI (2026b), §5, “Removal of seed controls”][q-seed-statement].

**A small component supplies a large response.**
An initialization with parameters $b>0$ and $r>0$ uses costs of order
$b/r$, a mixer angle $\arcsin r$, an inverse cost, and a fixed mixer.
It has an exact decomposition into an ordinary component and a
special component of norm $r$. The special component's displacement
is of order $1/r$. The decomposition is exact but need not be orthogonal.
The displaced component itself need not have bounded occupation moments;
only its undisplaced tail does. Norm remainders are transported through
subsequent unitaries without assigning them occupation bounds. Two centred unit directions $\ell_r,w_r$ escape
every fixed occupation sector and become asymptotically orthogonal
to each other and to vectors with uniformly bounded occupation
moments. In the ordinary part the surviving bounded displacement is
$2b\ell_r+o(1)$. The large displacements and the bounded tails are
tracked separately; the special part is not discarded merely because
its norm tends to zero. [OpenAI (2026b), §5, packet estimates and
initial high directions][q-seed-packets].

A packet has the form $W(d_r/r)\eta_r$, where the scaled centre $d_r$
is bounded and the tail $\eta_r$ has uniformly bounded occupation
moments. Packets with centres separated by a fixed positive amount
have overlap smaller than every fixed power of $r$. A short probe
along a Pauli axis $P$ sees a finite rotation determined by
$-2\operatorname{Im}\langle v_P,d_r\rangle$, as well as a small
Weyl displacement. The direction $v_P=u^*Pu\,\mathrm{vac}$ is the
actual current insertion. Toggling a cost rotates both its root Pauli
axis and this direction; they cannot be selected independently.
[OpenAI (2026b), §5, packet estimates][q-seed-packets].

For the finite list of nonzero special centres $h_j\in\mathbb R^2$,
the source constructs the same rotation $e^{-i\theta X}$ at every
centre, with *zero clocks*: the signed pulse durations on each of two
perpendicular axes in the $ZY$ plane sum exactly to zero. Choose the
axes so that $c_{j,a}=h_j\cdot P_a\ne0$, and the square pairs
$(c_{j,1}^2,c_{j,2}^2)$ are distinct except for equal or opposite centres.
Brackets have zero clock components and generate $iX$ coefficients
$c_{j,1}c_{j,2}F(c_{j,1}^2,c_{j,2}^2)$. Polynomial interpolation makes
all these coefficients one. Equal or opposite centres have the same
product, so they cause no obstruction to this common rotation.

This does not give arbitrary independent rotations: opposite centres
obey $U_{-h}=XU_hX$. Exact finite reachability of the required common
rotation follows by taking finitely many reachable conjugates spanning
the generated Lie algebra; their product map contains an identity
neighbourhood, and subdivision reaches the whole one-parameter path.
Closure alone would not give exact cancellation. The Lie-bracket and
polynomial method follows [Li and Khaneja (2005), §II, Examples 1–2,
pp. 2–3](https://arxiv.org/abs/quant-ph/0510012v1); the finite-family,
equal/opposite-centre and exact-clock assertions are proved in the
QAOA source itself.
The separate accuracy lemma then follows the actual insertion drift
through every probe prefix. Its ordinary-component error is $o(r)$;
the error on the normalised special component is $o(1)$ and hence
also contributes $o(r)$ to the state. These bounds are uniform over
the bounded-tail families needed for insertions, and their constants
refer to the chosen finite pulse list.
[OpenAI (2026b), §5, “Selective rotations with zero clocks” and
“Accuracy of selective probes”][q-seed-selective].

The shared seed family is essential even for a single spin. Two gates
$e^{-itSZ}$ applied to $|+\rangle$, with the same standard Gaussian $S$,
give mean $X$ expectation $\mathbb E\cos(4tS)=e^{-8t^2}$.
Replacing the second seed by an independent copy gives $e^{-4t^2}$.
Agreement of marginal seed laws does not preserve a circuit's value.

**The echo amplifies a controlled difference.**
Consider a forward cost $t/r$, a selective flip of the special
component, the reverse cost $-t/r$, and a selective undoing of that
flip. The packet invariant transports the special component so that
its contribution to the insertion changes sign. For the actual
insertion directions before and after the first flip, it gives
$$
v'_r-v_r=-2r\,w_r+o(r).
$$
The Weyl product of the two costs is formed with these actual
directions before making any approximation. Their large centres
cancel, leaving a bounded displacement
$$
\frac tr(v'_r-v_r)=-2t\,w_r+o(1).
$$
Approximating each direction by a low component with merely $O(r)$
error before this subtraction would leave an uncontrolled order-one
error. The remaining scalar Weyl phase is independent of the root
spin and cancels in insertions; it need not itself converge. The
second flip restores the transported special component so that the
same construction can be used again. Mixers receive analogous
selective compensations. [OpenAI (2026b), §5, packet invariant,
insertion approximation and “One echo”][q-seed-echo].

In the limit, $\ell_r$ and $w_r$ become two orthogonal external real
Gaussian modes at each root. The initialization uses $q(\ell)$ and
every simulated seed gate uses the same $q(w)$: choosing
$t=\sigma/2$ implements $e^{-i\sigma Zq(w)}$. Different vertices
have independent local copies. This is the required joint law of the
seeded word. A finite induction uses the Weyl identity
$$
\langle W(f)\Omega,W(g)\Omega\rangle
 =\exp\!\left(-\tfrac12\|g-f\|^2
                  +i\operatorname{Im}\langle f,g\rangle\right)
$$
to match the relevant finite Gram matrices. Escaping high directions
supply precisely the vanishing pairings between the new external
modes and endogenous child directions.
[OpenAI (2026b), §5, external-mode limit][q-seed-gram].

Energy requires an additional pairing. For a centred low insertion
$h=\sum_j s_j\otimes W(f_j)\Omega$, the one-particle coefficient of
$W(f_j)\Omega$ is $i e^{-\|f_j\|^2/2}f_j$. Hence
$$
\langle h,\mathsf Lh\rangle
 =-i\sum_j\langle s_j,+\rangle e^{-\|f_j\|^2/2}
                      \langle f_j,h\rangle.
$$
In the seeded representation, $\mathsf L$ places the root-seed factor
in its vacuum and creates $h$ only in the endogenous child space.
External components therefore contribute zero to the last pairing.
The high-direction estimate yields the same zeros in the actual
limit. The actual insertion differs from its low insertion by $O(r)$,
so energy continuity completes the comparison. Matching Gram
matrices without this one-particle calculation would not identify
$\mathsf L$ or its energy. [OpenAI (2026b), §5, “Finite Gram
induction,” including the energy calculation][q-seed-gram].

**Why the selective rotations are available at every required stage.**
The limiting projection of each special centre must be nonzero. The
source imposes finitely many visibility conditions on the angles of
the formal seeded word. At each relevant standard stage they have
form
$$
-2\operatorname{Im}\langle v_Z^{\rm form},
        -2bz\,e+yD^{\rm form}\rangle\ne0,
\qquad z,y\in\{\pm1\},
$$
where $e=Z\mathrm{vac}$ and $D^{\rm form}$ accumulates echoes whose
reverse costs have already occurred. These functions are real
analytic by the finite Weyl formulas. Setting all target angles to
zero, while retaining initialization, gives
$4bz e^{-8b^2}\ne0$, so none is identically zero. An arbitrarily small
angle perturbation avoids their finite union of zero sets and the
zero echo-time hyperplanes. The huge-cost stages need a separate
transverse-projection estimate; their limiting projection pairs then
also have a nonzero coordinate. Finite pulse lists can now be chosen
successively from limits already established at earlier stages.
No list is chosen from a limit that assumes its own successful
implementation. [OpenAI (2026b), §5, huge-stage transverse projection,
visibility and construction order][q-seed-visibility].

The choices are therefore nested: make $b$ small to control
initialization; perturb the fixed target angles to ensure visibility;
choose all finite probe lists; finally choose $r$ small. A value of
$r$ fixes every large angle and every finite product. The theorem
allows those angles to be large or negative. It makes no claim of
uniform bounds as the target word length grows or as the tolerance
tends to zero. [OpenAI (2026b), §5, proof of seed removal][q-seed-visibility].

<!-- /passage:qaoa-seed -->

<!-- passage:qaoa-transfer -->

### 9.5 Transfer of the resulting ordinary word

After all these choices there is one finite ordinary word $W$, fixed
independently of degree, size and disorder. On the $(D+1)$-regular
tree use
$C_D=D^{-1/2}\sum_{\{i,j\}\in E}Z_iZ_j$, counting each edge once.
The source applies the fixed-word transfer theorem
$$
v_W=\lim_{D\to\infty}\frac{\sqrt D}{2}
 \langle+|W_D^*Z_iZ_jW_D|+\rangle.
$$
The [full preprint of Basso et al., arXiv:2110.14206v3](https://arxiv.org/abs/2110.14206v3),
Theorem 1, equates the limiting tree recursion with the infinite-size
SK recursion for every fixed depth and fixed angle vector. Its proof
is in §6, especially (6.6)–(6.31), with the symmetry statement proved
in Appendix B and the iteration stabilisation in Appendix A.4. The
shorter proceedings edition states the theorem but refers to this
full preprint for the proof.

Basso et al. use a negative tree cost in (2.3). Conjugation by $X$
on one bipartition reverses each edge term, fixes the plus state and
commutes with the mixer. It also reverses the measured edge term,
converting their cut convention in (2.6) to the positive energy above.
Their SK cost (6.1) already has the positive convention used here.
The result applies after seed removal; it does not directly transfer
an arbitrary seeded or controlled word. It also supplies no joint
limit in which depth or angles change with $D$ or $n$.
[OpenAI (2026b), §2, “Fixed-word transfer”][q-transfer].

For an ordinary cost or mixer the root updates are, respectively,
$$
u\longmapsto e^{-itZq(v_Z)}u,
\qquad
u\longmapsto e^{-i\beta X}u,
\qquad v_Z=u^*Zu\,\mathrm{vac}.
$$
The source proves smooth convergence for these updates, their
adjoints and fixed angle derivatives. The resulting occupation
bounds supply the hypothesis of the root-shift energy proposition
in §9.1. Thus its energy is the scaled edge limit required for
transfer. Finally merge consecutive gates of the same type and
insert zero-angle gates where needed to express $W$ in alternating
QAOA form. [OpenAI (2026b), §2, “Ordinary root updates”][q-ordinary-updates].

<!-- /passage:qaoa-transfer -->

<!-- passage:qaoa-assembly -->

### 9.6 Fixing the word before the thermodynamic limit

Allocate errors after choosing the desired $\varepsilon>0$. Apply the
classical near-optimality proposition with the two tolerances
$\varepsilon/4$ and $\eta_H=(\varepsilon/8)^2$. It supplies one
formula and its helper law together, with classical loss below
$\varepsilon/4$ and $0<p_H<\eta_H$. In its proof the uncoloured
formula is fixed first, then the small positive helper probabilities
and the excluded-colour approximation are selected. Thus changing a
helper law does not silently preserve an already fixed formula. With
$\eta=\varepsilon/8$, synthesis gives
$$
\mathcal E(v)\ge\mathcal E(m)-2\eta-2\sqrt{p_H}
 >P_*-3\varepsilon/4.
$$
Seed removal uses less than $\varepsilon/4$. The resulting fixed
ordinary word therefore satisfies $v_W>P_*-\varepsilon$ after the
fixed-word transfer. Its thermodynamic limit is taken only after
all approximation choices have been made. Since $Q_p\le P_*$ and
zero padding makes $Q_p$ nondecreasing, this proves the source's
thermodynamic-first conclusion from its stated analytic inputs.
[OpenAI (2026b), §6][q-assembly].

The order is: accuracy; minimizer and fixed $T<1$; finite scalar mesh;
smoothing and bounded approximations; finite types and positive helper
masses; exact helper contractions and finite commutator products; one
fixed seeded word; initialization size; generic angle perturbation;
finite selective pulse lists; sufficiently small $r$; one ordinary
word; its $n\to\infty$ limit. The degree limits identify the rooted
calculus and the transferred value for each already fixed word; they
do not license changing that word with the finite instance.

The reconstruction makes the source's circuit mechanisms explicit,
but the evidence classes remain separate. The scalar construction
and its formal interfaces in §§6–8 do not by themselves establish the
weighted unitary calculus, simultaneous helper contraction or seed
removal. Those analytic theorems are additional inputs from the QAOA
manuscript, with the domain, commutation and uniformity hypotheses
specified above. No quantitative depth bound, finite-size rate,
efficient angle-selection procedure, or independent formal
verification of this entire circuit construction follows from the
selected formal statements.

<!-- /passage:qaoa-assembly -->

<!-- passage:alternative -->

### 9.7 The separate positive-temperature route

The positive-temperature appendix supplies a separate classical input to
the same synthesis and seed-removal theorems. Fix $\beta_0>1$, let
$\mu_{\beta_0}$ be its Parisi measure, and write
$q=q_{\beta_0}=\max\operatorname{supp}\mu_{\beta_0}$.
Here $\gamma(t)=\beta_0\mu_{\beta_0}([0,t])$,
$m=\phi_{\beta_0,x}$, $a=\phi_{\beta_0,xx}$ and $X$ belong to the
positive-temperature PDE, whose terminal value is
$\beta_0^{-1}\log(2\cosh(\beta_0x))$. They are distinct from the
zero-temperature objects in §§1–8. The input credited to
[Lopatto, arXiv:2607.11756v3, Theorem 1.1](https://arxiv.org/pdf/2607.11756v3)
gives $\operatorname{supp}\mu_{\beta_0}=[0,q]$ for $\beta_0>1$;
its smooth density below $q$ gives the regularity used on a fixed
$[0,T]$ with $0<T<q$.

The normalization can be checked directly against Lopatto's PDE.
Writing $\widehat\Phi_{\beta_0}(t,y)$ for his solution with terminal
value $\log\cosh y$ and covariance factor $\beta_0^2$, set
$$
\phi_{\beta_0}(t,x)
 =\frac{\widehat\Phi_{\beta_0}(t,\beta_0x)+\log2}{\beta_0},
\quad m=\widehat\Phi_y(t,\beta_0x),\quad
 a=\beta_0\widehat\Phi_{yy}(t,\beta_0x).
$$
His diffusion $\widehat X$ has noise coefficient $\beta_0$; hence
$X=\widehat X/\beta_0$ has unit noise and drift
$\beta_0\mu_{\beta_0}([0,t])m$. His identity
$\beta_0^2\mathbb E\widehat\Phi_{yy}(t,\widehat X_t)^2=1$
is exactly $\mathbb E a(t,X_t)^2=1$. This is a fixed-temperature
change of variables, not convergence of either Parisi measure as
$\beta_0\to\infty$. [Lopatto, arXiv:2607.11756v3, equations
(1.3), (2.1)–(2.2) and Lemma 2.2](https://arxiv.org/abs/2607.11756v3).

The source derives $\mathbb E a(t,X_t)^2=1$ on $[0,q]$ and
$1-q\le\beta_0^{-1}$. The value estimate is
$$
\int_0^T\mathbb E a(t,X_t)\,dt
\ge P_*-\frac{1/4+\log2}{\beta_0}-(q-T).
$$
To recover its constants, martingale contact first gives
$\int_0^t\mathbb E a(s,X_s)^2ds=t$ on $[0,q]$; continuity yields
unit second moment including the endpoints. On $[q,1]$, $\gamma=\beta_0$,
so Cole–Hopf gives
$$
\phi(q,x)=\beta_0^{-1}\log(2\cosh\beta_0x)+\beta_0(1-q)/2,
\quad m(q,x)=\tanh(\beta_0x),\quad a(q,x)=\beta_0\operatorname{sech}^2(\beta_0x).
$$
Hence $1-q=\mathbb E\operatorname{sech}^2(\beta_0X_q)\le\beta_0^{-1}$.
Itô's product rule and the value evolution give
$$
\int_0^q\mathbb E a=\mathbb E[X_qm(q,X_q)]-\int_0^qt\gamma(t)dt,
\quad
\mathbb E\phi(q,X_q)=\phi(0,0)+\tfrac12\int_0^qt\gamma(t)dt.
$$
Using $x\tanh(\beta_0x)\ge\beta_0^{-1}\log(2\cosh\beta_0x)
-\beta_0^{-1}\log2$ and retaining the penalty on $[q,1]$ yields
$$
\int_0^q\mathbb E a\ge F_{\beta_0}
-\frac{\beta_0(1-q)^2}{4}-\frac{\log2}{\beta_0}.
$$
The cutoff removes at most $q-T$, because $0\le\mathbb E a\le1$.
This proves the displayed estimate. Choose first a sufficiently large
finite $\beta_0$, then $T<q$ close enough to $q$. This route obtains the existence and value of the
ground-state limit from the positive-temperature Parisi formula of
[Talagrand (2006), Theorem 1.1, pp. 222–223](https://doi.org/10.4007/annals.2006.163.221).
At each fixed $\beta_0$, his covariance hypotheses (1.3)–(1.5) hold with
$\xi(t)=\beta_0^2t^2/2$ and error $c(n)=\beta_0^2/(2n)$.
His partition sum (1.14) is unnormalized; dividing its logarithmic
free energy by $\beta_0$ gives the convention here, including the
$\log2/\beta_0$ entropy term. With
$F_{n,\beta_0}=(n\beta_0)^{-1}\mathbb E\log\sum_\sigma e^{\beta_0H_n(\sigma)}$, use
$$
F_{n,\beta_0}-(\log2)/\beta_0\le n^{-1}\mathbb E\max H_n\le F_{n,\beta_0}.
$$
It does not invoke the zero-temperature companion
to justify that step. Write $M_n=n^{-1}\mathbb E\max H_n$. The same
uniform entropy bound gives
$$
|F_{n,\beta_0}-P_*|\le |M_n-P_*|+\frac{\log2}{\beta_0}.
$$
Thus arbitrary joint $n,\beta_0\to\infty$ are permitted for these scalar
free-energy values. This says nothing about joint convergence of measures,
PDE derivatives, message calculations or circuit words.
[OpenAI (2026b), Appendix A][q-positive].

The remaining limits have distinct tasks. At fixed
$\beta_0,T,\delta,L$, with $\delta>0$, integer $L\ge1$ and $L\delta\le T$, the degree limit $D\to\infty$ identifies the
finite message law and its edge value. Let $U_0,U_1,\ldots$ be independent
standard normals. Put
$$
X_0^\delta=\sqrt\delta\,U_0,\qquad
X_{r+1}^\delta=X_r^\delta+\delta\gamma(r\delta)m(r\delta,X_r^\delta)
                   +\sqrt\delta\,U_{r+1},\qquad
c_{\delta,r}=(\mathbb E a(r\delta,X_r^\delta)^2)^{-1/2}.
$$
The finite-degree output is a message calculation on the $(D+1)$-regular
tree, where $\partial i$ is the set of neighbours of vertex $i$.
Write $t_r=r\delta$ and $b(t,x)=\gamma(t)m(t,x)$.
Initialise independent standard normal labels $g_i$, with
$u^0_{i\to j}=u_i^0=g_i$, $A^{-1}_{i\to j}=1$ and
$x^0_{i\to j}=x_i^0=\sqrt\delta\,g_i$. For $0\le r<L$ set
$$
u^{r+1}_{i\to j}=D^{-1/2}\!\sum_{\substack{v\in\partial i\\v\ne j}}
 A^{r-1}_{v\to i}u^r_{v\to i},\qquad
u^{r+1}_i=(D+1)^{-1/2}\!\sum_{v\in\partial i}
 A^{r-1}_{v\to i}u^r_{v\to i}.
$$
Each $x$ then takes the Euler step
$x^{r+1}=x^r+\delta b(t_r,x^r)+\sqrt\delta\,u^{r+1}$ with its corresponding
directed-edge or vertex message. The directed-edge law fixes the common
normaliser:
$$
c_{D,r}=(\mathbb E a(t_r,x^r_{i\to j})^2)^{-1/2},\quad
A^r_{i\to j}=c_{D,r}a(t_r,x^r_{i\to j}),\quad
B_i^r=c_{D,r}a(t_r,x_i^r),\quad
z_i^L=\sqrt\delta\sum_{r=1}^{L}B_i^{r-1}u_i^r.
$$
The one-step lag in $A^{r-1}u^r$ gives conditional centring from the new
outer Gaussian layer; successive finite-degree messages need not be
independent. At fixed $\delta,L$, the joint vertex messages converge to
the independent $U_r$ above, and $z_i^L$ converges to
$\sqrt\delta\sum_{r=1}^Lc_{\delta,r-1}a(t_{r-1},X^\delta_{r-1})U_r$.
The source's separate edge calculation gives
$$
\lim_{D\to\infty}\frac{D+1}{2\sqrt D}\mathbb E[z_o^Lz_v^L]
  =\delta\sum_{r=1}^{L-1}c_{\delta,r}\mathbb E a(r\delta,X_r^\delta),
\qquad o\sim v.
$$
Only afterwards take $\delta\downarrow0$ with $L=\lfloor T/\delta\rfloor$.
The source bounds the discrepancy from
$\int_0^T\mathbb E a(t,X_t)\,dt$ by $C(\beta_0,T)\sqrt\delta$.
A separate norm-convergence argument with a uniform first occupation
moment identifies this edge limit with the rooted energy. A
finite-dimensional central limit theorem alone does not identify that
observable. [OpenAI (2026b), Appendix A][q-positive].

<!-- /passage:alternative -->

<!-- passage:weighted-tree -->
<a id="eams-finite-comparison"></a>

**The finite source comparison.** The comparison in this paragraph is with
[El Alaoui–Montanari–Sellke, arXiv:2111.06813v2, 3 February 2023](https://arxiv.org/abs/2111.06813v2).
Proposition 2.1 (p. 7) sums the adjacent-time term over
$\ell=2,\ldots,L$. Applying Lemma 4.3, equation (4.6) (p. 14),
replaces the expectation in that summand by the coefficient at
$r=\ell-1$, so the resulting range is $r=1,\ldots,L-1$.
The displayed ranges in (4.5) (p. 13) and (4.18) (p. 16) are instead
$2,\ldots,L$. Separately, the same-time display (2.21) in Lemma 2.8
(p. 9) omits a factor $1/k$ that is present in its proof and in
Proposition 2.1. The QAOA manuscript's Appendix A already uses the latter proposition,
the reindexed sum and spatial Lipschitz bounds for both $a$ and $b$.
The two following calculations establish the finite discrepancies and
their precise scope. They do not compare formulae in the journal edition.

**The test weights expose the missing factor.** Work on the $k$-regular
tree, $k\ge2$, and let all initial labels $g_i$ be independent standard
Gaussians. In particular, the adjacent vertices $o,v$ have distinct
labels $g_o,g_v$. Set $u_i^0=u_{i\to j}^0=g_i$,
$A_{i\to j}^{-1}=1$, and use constant algorithmic update functions
$F_r=H_r=1$. These satisfy EAMS Assumption 2 and its later boundedness
Assumption 3. For the auxiliary tests in Lemma 2.8 choose
$Y_o^r=g_o$ and $\widetilde Y_v^r=g_v$ for every $r\ge0$.
Each test is measurable with respect to its required initial-label
sigma-field, and all moments are finite. The tests are separate from
the constant update functions.

At $t=1$, the recursion gives
$$
u_o^1=k^{-1/2}\sum_{x\sim o}g_x,\qquad
u_v^1=k^{-1/2}\sum_{y\sim v}g_y.
$$
Hence
$$
\mathbb E[u_o^1u_v^1g_og_v]
=\frac1k\sum_{x\sim o,\,y\sim v}\mathbb E[g_xg_yg_og_v]
=\frac1k.
$$
Only $x=v,y=o$ survives. The printed right side of (2.21) is
$\mathbb E[g_v^2g_o^2]=1$; multiplying it by $1/k$ agrees with the
calculation. Both initial labels matter. With both test weights equal
to one, both sides are zero; with just the neighbouring test omitted,
the left side is an odd Gaussian moment and is again zero.

A bounded version uses $Y_o^r=\operatorname{sgn}(g_o)$ and
$\widetilde Y_v^r=\operatorname{sgn}(g_v)$. Only the same edge pair
survives, so
$$
\mathbb E[u_o^1u_v^1\operatorname{sgn}(g_o)\operatorname{sgn}(g_v)]
=\frac1k(\mathbb E|g|)^2=\frac{2}{\pi k},
$$
whereas the printed right side is $2/\pi$. These tests are bounded
and initial-label measurable. Both witnesses concern the auxiliary
weighted identity; neither substitutes arbitrary test weights into a
Parisi output theorem.

**The shifted endpoint violates the printed uniform finite bound.**
For a separate test retain the initial labels and set
$$
\delta=\varepsilon=\frac14,\qquad L=2,\qquad b(t,x)=0,
\qquad
a(t,x)=
\begin{cases}
1,&0\le t<3/8,\\
-1,&3/8\le t<1.
\end{cases}
$$
Use the source's actual initial states
$x_i^0=x_{i\to j}^0=\sqrt\delta\,g_i$ and its definitions
$A_{i\to j}^r=a(r\delta,x_{i\to j}^r)$,
$B_i^r=a(r\delta,x_i^r)$. The state initialization has not been set
to zero; it drops out of these coefficients because $a$ is independent
of $x$. This fixed function is bounded by $K=1$, has spatial
Lipschitz constant zero, and satisfies $a^2=1$, so all directed-edge
normalizers are exactly one. The drift has Lipschitz constant $M=0$,
and $L\delta=1/2\le1-\varepsilon$. It therefore meets the printed
hypotheses of Theorem 4.1 and Assumptions 2–3. That finite theorem
does not require temporal continuity or positivity of $a$.

At the mesh points, $a_0=a_1=1$ and $a_2=-1$. Thus
$$
u_i^2=\frac1{\sqrt{k(k-1)}}
 \sum_{w\sim i}\sum_{y\sim w,\,y\ne i}g_y,
\qquad z_i^2=\sqrt\delta\,(u_i^1+u_i^2).
$$
The equal-time covariances across the edge are zero. Each adjacent-time
covariance is $\sqrt{k-1}/k$: exactly $k-1$ labels occur in both sums,
and their product normalization is $k\sqrt{k-1}$. Therefore
$$
k\mathbb E[z_o^2z_v^2]=2\delta\sqrt{k-1},\qquad
\frac{k}{2\sqrt{k-1}}\mathbb E[z_o^2z_v^2]=\delta.
$$
The target printed in (4.5) uses $a(2\delta,x_o^2)=-1$, so it is
$-2\delta\sqrt{k-1}$. Its absolute error is
$4\delta\sqrt{k-1}$, which is unbounded as $k\to\infty$ while all
arguments of the claimed constant $C(M,K,\delta,\varepsilon)$ remain
fixed. This refutes auxiliary Theorem 4.1 as printed. The example is
not a Parisi curvature: it changes sign. Consequently it is not by
itself a counterexample to the specialized assertion (4.18) in
Proposition 4.7; the endpoint correction there comes from the exact
proposition and reindexing explained above. Neither test refutes the
main EAMS Theorem 1.7.

**A finite estimate with the required hypotheses.** The source argument
does provide a usable replacement. Fix $\delta>0$, $L\ge1$ and
$L\delta<1$. Allow the coefficients $a_k,b_k$ to depend on degree, but
require bounds independent of $k$ at the finitely many mesh times:
$|a_k|\le K$ with $K\ge1$, and spatial Lipschitz constants $L_a,L_b$
for $a_k,b_k$. Use the original initialization and the same normalized
function for node and directed-edge coefficients, with
$\mathbb E(A_{i\to j}^r)^2=1$. Then
$$
\left|k\mathbb E[z_o^Lz_v^L]
 -2\sqrt{k-1}\,\delta\sum_{r=1}^{L-1}\mathbb E B_o^r\right|
 \le C(K,L_a,L_b,\delta,L).
$$
The constant is independent of $k$, and the sum is empty when $L=1$.
The coefficient expectation on the right uses the vertex law; its
normalization was defined using the directed-edge law. The following
proof keeps the two laws distinct. It reconstructs the finite estimate
from EAMS Proposition 2.1 and Lemmas 3.2–3.4 and 4.2–4.3; it is not
a claim that changing an index alone repairs every hypothesis of the
printed theorem.

Put $D=k-1$. Conditional on the earlier cavity labels, the new
message is centered Gaussian with variance $(\tau^r)^2$. Its recursion is
$$
(\tau_{i\to j}^{r+1})^2=\frac1D
\sum_{\substack{w\in\partial i\\w\ne j}}(A_{w\to i}^{r-1})^2(\tau_{w\to i}^r)^2,
\qquad \tau^0=1.
$$
This conditional Gaussianity gives
$\Delta_r=\mathbb E[((\tau^r)^2-1)^2]\le V_r/D$, where
$$
V_0=0,\qquad V_{r+1}=2K^4V_r+2(K^4+1).
$$
Indeed, split the conditional-variance recursion into the average of
$(A^{r-1})^2((\tau^r)^2-1)$ and the average of $(A^{r-1})^2-1$.
Jensen bounds the first square, while independence of child cavities
and exact coefficient normalization bound the second by a constant
over $D$. The moment recursion also gives
$\mathbb E(u_{i\to j}^r)^2\le K^{2r}$.

Splitting off the missing neighbour as in the source gives
$\mathbb E|u_i^r-u_{i\to j}^r|^2\le4K^{2r}/k$.
Subtract the node and directed-edge Euler recursions. Their equal
initial states and the drift Lipschitz bound give
$$
\mathbb E|x_i^r-x_{i\to j}^r|^2\le d_r/k,
\quad d_0=0,\qquad
d_{r+1}=2(1+\delta L_b)^2d_r+8\delta K^{2(r+1)}.
$$
The bound
$\|B_i^r-A_{i\to j}^r\|_2\le L_a\sqrt{d_r/k}$
now uses spatial Lipschitzness of $a$. This property is invoked in the
proof of EAMS Lemma 4.2 but omitted from the printed hypotheses of
Theorem 4.1; it is available in the QAOA manuscript's compact-strip application.

For $s=\ell-1$, the adjacent-time summand of Proposition 2.1 is
$$
Q_s=\mathbb E[A_{v\to o}^{s-1}(u_{v\to o}^s)^2B_v^{s-1}B_o^s].
$$
Let $\mathcal G_{i\to j}^{r,+}$ be the labels within distance $r$
of $i$ in its cavity after removing edge $ij$. Condition on
$\mathcal G_{v\to o}^{s-1,+}\vee\mathcal G_{o\to v}^{s,+}$.
The three coefficient factors are measurable there: their vertex balls
split into these two disjoint cavity balls. The newest layer driving
$u_{v\to o}^s$ is outside this field; adding the initial label at $v$
to the source's minus field does not change the conditional law, since
that message and its variance exclude that label. Conditioning therefore replaces $(u_{v\to o}^s)^2-1$ by $(\tau_{v\to o}^s)^2-1$.
Its contribution is bounded by $K^3\sqrt{V_s/D}$. Replacing the two
node coefficients by directed-edge coefficients then costs at most
$K^2L_a(\sqrt{d_{s-1}}+\sqrt{d_s})/\sqrt k$.
The two directed-edge trees are independent; exact normalization
reduces their product expectation to $\mathbb E A_{o\to v}^s$.
One final comparison with $\mathbb E B_o^s$ proves
$$
|Q_s-\mathbb E B_o^s|\le\frac{C_s}{\sqrt D},\quad
C_s=K^3\sqrt{V_s}+K^2L_a\sqrt{d_{s-1}}
                         +(K^2+1)L_a\sqrt{d_s}.
$$
For the same-time remainder in that proposition,
$|R_\ell|\le K^{2\ell+2}$ by boundedness and Cauchy–Schwarz. Hence
the asserted finite bound holds, for example, with
$$
C=2\delta\sum_{s=1}^{L-1}C_s
                  +\delta\sum_{\ell=1}^LK^{2\ell+2}.
$$
No constant uniform in increasing horizon, temperature or terminal
cutoff has been asserted.

**Why the continuum value survives the correction.** The QAOA manuscript already checks
the convergence and uniform boundedness of its finitely many
degree-dependent normalizers, and supplies both spatial Lipschitz
bounds, before taking the degree limit. Its limiting coefficient
$m_r=c_{\delta,r}\mathbb E a(t_r,X_r^\delta)$ satisfies $|m_r|\le1$
by Cauchy–Schwarz and the definition of $c_{\delta,r}$. The shifted
and corrected sums differ exactly by
$$
\delta\sum_{r=2}^Lm_r-\delta\sum_{r=1}^{L-1}m_r
=\delta(m_L-m_1),\qquad |\delta(m_L-m_1)|\le2\delta.
$$
Thus the error in the printed unnormalized finite theorem can grow
like $\sqrt{k}$ at fixed mesh even though the correction disappears
in the subsequent normalized continuum limit. The fixed-temperature
coupling and separate strong realization in the QAOA manuscript justify that limiting
application. These checks neither reject nor independently certify
the whole EAMS or QAOA theorem. [OpenAI (2026b), Appendix A][q-positive].
<!-- /passage:weighted-tree -->

<!-- passage:alternative-assembly -->
After clipping and bounded approximation, the result enters the same
synthesis and seed-removal route as the primary construction. Its source
dependencies and fixed-temperature choice of parameters remain separate
from the retained zero-temperature formal interfaces.
[OpenAI (2026b), Appendix A][q-positive].

### 9.7.1 Where the temperature routes meet

Both routes produce a bounded finite classical calculation whose rooted
energy is close to $P_*$. They reach that common input by different
theorems and different finite approximations.

| Question | Zero-temperature route | Positive-temperature route |
| --- | --- | --- |
| Which variational object is fixed? | An attained minimizer $\gamma\in\mathcal U$ for terminal value $|x|$. | A fixed finite $\beta_0>1$ and its Parisi probability measure, with terminal value $\beta_0^{-1}\log(2\cosh\beta_0x)$. |
| What fills the overlap interval? | Full relative Stieltjes support on $[0,1)$ from the zero-temperature source. | Lopatto's interval-support result on $[0,q_{\beta_0}]$. |
| What is the scalar loss before discretization? | At most $1-T$, with $T<1$. | At most $(1/4+\log2)/\beta_0+(q_{\beta_0}-T)$, with $T<q_{\beta_0}$. |
| How is finite energy identified? | The explicit Gaussian coefficient sum is identified with $\operatorname{Re}\langle F_N,\mathsf L F_N\rangle$ by a first-chaos projection. | A finite-degree message and edge calculation is followed by a rooted norm/occupation argument. |
| Which approximation order matters? | Fix $T$ before refining the scalar mesh; choose a finite mesh before regularization and synthesis. | Fix $\beta_0,T,\delta,L$ for the message degree limit; then refine $\delta$ at fixed $\beta_0,T$. |
| What is shared after this point? | The bounded approximation, exclusions, seeded synthesis, seed removal and fixed-word transfer. | The same quantum construction, with its classical input supplied independently. |

Here the displayed positive-temperature estimate is exactly the one
derived above, rather than an assertion of convergence of zero-temperature
supports. One can choose $\beta_0$ and $T$ finitely for the required
error and then stop. The later circuit argument needs that finite
choice; it never asks for a joint limit of the temperature, message
mesh, graph degree and circuit depth. [OpenAI (2026b), Appendix A,
Proposition “The independent positive-temperature construction”][q-positive];
[§6][q-assembly].
<!-- /passage:alternative-assembly -->

<!-- passage:gibbs-comparison -->

### 9.7.2 Finite-temperature values and exact Gibbs samples

For one fixed instance, let $L_n=\max_\sigma H_{n,J}(\sigma)/n$,
$\mathcal F_{n,\beta}=(n\beta)^{-1}\log\sum_\sigma e^{\beta H_{n,J}(\sigma)}$,
and let $\mathcal U_{n,\beta}$ be the mean energy per spin under the
Gibbs law proportional to $e^{\beta H_{n,J}(\sigma)}$. Then
$$
0\le\mathcal F_{n,\beta}-L_n\le\frac{\log2}{\beta},\qquad
0\le L_n-\mathcal U_{n,\beta}\le\frac{\log2}{\beta}.
$$
The first is the log-sum bound. The second uses
$\mathcal F=\mathcal U+S/(n\beta)$, where the Gibbs entropy satisfies
$0\le S\le n\log2$, together with $\mathcal U\le L_n\le\mathcal F$.
Thus both disorder averages approach $P_*$ along every joint
$n\to\infty$, $\beta\to\infty$, by the already established
convergence of $\mathbb E L_n$.

There is also a finite probability estimate. Every configuration has
Gaussian coefficient-vector norm $\sqrt{(n-1)/(2n^2)}$ after division
by $n$, and their maximum has the same Lipschitz bound. Gaussian
concentration gives, for $n\ge2$,
$$
\Pr_J(|L_n-\mathbb E L_n|>s)
\le2\exp\{-n^2s^2/(n-1)\}.
$$
For an exact Gibbs draw $\Sigma^{\rm G}$, count the at most $2^n$
configurations with deficit at least $s$ and bound the partition sum
below by its maximal term. This gives, for every instance,
$$
\Pr\{H_{n,J}(\Sigma^{\rm G})/n\le L_n-s\mid J\}
\le\min\{1,e^{n(\log2-\beta s)}\}.
$$
The lower tail below $P_*-s$ is bounded by
$\Pr_J(L_n<P_*-s/2)+\min\{1,e^{n(\log2-\beta s/2)}\}$;
the upper tail is at most the upper tail of $L_n$. Hence an exact
Gibbs sample also approaches $P_*$ in joint probability. These are
elementary scalar consequences of the Gibbs law, entropy and Gaussian
concentration. They supply neither an efficient sampler nor QAOA angles;
the Born law in the next subsection is a separate distribution.
<!-- /passage:gibbs-comparison -->

<!-- passage:qaoa-quantifiers -->

### 9.8 What is averaged, and a fixed-word probability consequence

The theorem in §9 is an existence statement about limiting expected
energy. There are two random choices behind that expectation. First the
couplings $J$ are sampled; then a computational-basis measurement of the
state produces a spin string $\Sigma$. For the single word $W$ already
chosen, put
$$
E_n(J,\Sigma)=H_{n,J}(\Sigma)/n,\qquad
\overline E_n(J)=\mathbb E[E_n(J,\Sigma)\mid J].
$$
The quantity defining $v_W$ is $\mathbb E_J\overline E_n(J)$.
It is neither the energy of every measured string nor a worst-disorder
guarantee. The temporary Gaussian labels used during synthesis are not
an extra source of randomness in the final angle vectors.

There is, however, an additional conclusion available from the cited
fixed-parameter theorem. Farhi, Goldstone, Gutmann and Zhou prove, with
the same Hamiltonian and gate-sign convention, that for every fixed word
$$
\mathbb E_{J,\Sigma}E_n\longrightarrow v_W,
\qquad
\mathbb E_{J,\Sigma}E_n^2\longrightarrow v_W^2.
$$
Their second expression is the quantum expectation of $(C_{n,J}/n)^2$
averaged over disorder, not merely the square of the conditional mean.
Consequently
$$
\mathbb E_{J,\Sigma}(E_n-v_W)^2\longrightarrow0,
\qquad
\Pr_{J,\Sigma}(|E_n-v_W|>s)\longrightarrow0
\quad(s>0).
$$
The law of total variance separates what vanishes:
$$
\mathbb E(E_n-v_W)^2=
\mathbb E_J\operatorname{Var}(E_n\mid J)
 +\mathbb E_J(\overline E_n(J)-v_W)^2.
$$
Both terms are nonnegative and hence tend to zero. Concentration of the
conditional mean alone would not control a measured string.
This is the elementary second-moment deduction from [Farhi et al.,
arXiv:1910.08187v4, §4, equations (13)–(22)][fggz].

Now run the circuit construction with accuracy $\varepsilon/2$ and
freeze its resulting word. Since $v_W\ge P_*-\varepsilon/2$,
$$
\Pr_{J,\Sigma}\{E_n<P_*-\varepsilon\}
\le \frac{4}{\varepsilon^2}
       \mathbb E_{J,\Sigma}(E_n-v_W)^2\longrightarrow0.
$$
This is a consequence of the expected-value construction **together
with** the external second-moment theorem. It is not a clause of either
selected formal interface. If
$b_n(J)=\Pr(E_n<P_*-\varepsilon\mid J)$, then for every fixed
$\tau>0$,
$$
\Pr_J\{b_n(J)>\tau\}
\le\mathbb E_J b_n(J)/\tau\longrightarrow0.
$$
Thus the same word also has small conditional measurement-failure
probability for most disorder instances, in this precise sense. No
claim is made for every instance, for arbitrarily varying depths, or
with a quantitative size threshold.

For $K$ fresh state preparations at the same disorder instance, the
conditional failures are independent, so their joint failure probability
is $\mathbb E_J b_n(J)^K$, not $(\mathbb E_J b_n(J))^K$.
A fraction $\alpha$ of instances that always fail gives $\alpha$ for
the former at every $K$. A bound $b_n(J)\le\tau$ on a particular
instance does give $\tau^K$ there. Repeatedly measuring an already
collapsed state is a different experiment.

<!-- /passage:qaoa-quantifiers -->

<!-- passage:qaoa-depth -->

### 9.9 Depth, angle choice and the order of quantifiers

The complete witness is a finite ordered word, including every real
angle. Its existence for each error tolerance asserts uniformity in
system size and disorder that fixed-instance convergence does not provide.
The two forms should be read literally:

| Assertion | What may depend on the instance or size? |
| --- | --- |
| The source theorem: for every $\varepsilon>0$, there is one finite $W_\varepsilon$ with $\lim_{n\to\infty}\mathbb E E_n(W_\varepsilon)\ge P_*-\varepsilon$ | The cost operator uses $J,n$; the word and its angles do not. |
| Fixed-instance QAOA convergence | The chosen depth and angles may depend on the fixed finite cost matrix and the accuracy. |
| A prescribed family of nonzero angles with $p=p(n)\to\infty$ | Its performance needs further estimates; a depth allowance alone can be met by the padded existence construction below. |

The distinction already occurs for the elementary array
$a_{n,p}=p/(n+p)$. For each fixed $n$, its limit as $p\to\infty$
is one; for each fixed $p$, its limit as $n\to\infty$ is zero.
This is a quantifier example, not a model of QAOA. The finite-dimensional
convergence theorem of [Binkowski, Koßmann, Ziegler and Schwonnek,
arXiv:2302.04968v1, Theorem 12][binkowski] fixes the optimization
problem before selecting a sufficiently long circuit. It does not
replace the construction of a size-independent word here.

There is a narrower diagonal consequence for sampled output. Choose
$W_k$ with $P_*-1/k\le v_{W_k}\le P_*$. Fixed-word second-moment
convergence supplies $N_k$ so that, for every $n\ge N_k$,
$\mathbb E(E_n(W_k)-v_{W_k})^2\le k^{-2}$. Given any prescribed
integer depth allowance $d(n)\to\infty$, enlarge these strictly
increasing thresholds until $d(n)\ge\operatorname{depth}(W_k)$
for every $n\ge N_k$. On $N_k\le n<N_{k+1}$, use $W_k$ padded
with zero-angle layers to depth $d(n)$. Padding changes no state, and
$$
\mathbb E(E_n(W_k)-P_*)^2\le
2\mathbb E(E_n(W_k)-v_{W_k})^2+2(v_{W_k}-P_*)^2\le4/k^2.
$$
Thus a suitable schedule approaches the optimum in joint $L^2$, even
under an arbitrarily slowly diverging allowance. The word family and
thresholds are selected nonconstructively. This says nothing about an
independently prescribed family of nonzero angles, and is not an
interchange of limits or an effective depth bound.

Nor does a supremum over angles assert that an optimizing angle vector
exists at any particular depth. The proof constructs a sufficiently
good word directly; monotonicity from identity padding then gives the
limit of $Q_p$. Each QAOA round contains a full cost evolution and a
mixer evolution. In the dense SK model a cost evolution involves all
$\binom n2$ pair couplings, so the round count is not itself a bound on
two-qubit gate depth, connectivity cost, precision or physical runtime.

Three computational questions remain distinct. Evaluating the limiting
energy at supplied angles is one task; finding suitable angles is
another; implementing and sampling the resulting quantum circuit is a
third. The [Basso et al. iteration][bfmvz] evaluates the fixed-angle
limit in $O(p^2 4^p)$ arithmetic time. That is not a bound on the
search needed to find the existence theorem's angles. Spin–boson
representations provide another route to evaluation. The earlier
[Boulebnane et al. mapping, arXiv:2505.07929v2][spin-boson], and the
later [mixed-spin decoupling paper, arXiv:2609.40309v1, §§II–III and
Supplement S2.1][decoupling], must be distinguished: the latter is a
separate work, not the reference called BKL2026 in the original QAOA
manuscript. Its fixed-depth mapping and numerical tensor-network
performance do not supply an efficient angle-selection theorem for
the present construction. Its discussion also gives fixed-word
finite-size estimates; the absence of a finite-size rate **in the
construction here** is not a claim that the wider literature contains
none.

The statement is specific to the quadratic, zero-field SK model.
The pure even higher-spin model has a different thermodynamic-first
conclusion. For every even interaction order $q\ge4$, [Basso,
Gamarnik, Mei and Zhou, arXiv:2204.10306v2, Theorem 4, (3.15),
and its proof in §4.2](https://arxiv.org/abs/2204.10306v2) show
$$
v_p^{(q)}(\boldsymbol\theta,\boldsymbol\beta)
\le\eta_{\mathrm{OGP}}(G_q)<\eta_{\mathrm{OPT}}(G_q)
$$
for every finite $p$ and every fixed angle vector, in that source's
normalization. The same ceiling bounds their supremum over all finite
$p$ and angles. The proof combines its dense–sparse value identity
with the coupled-overlap-gap obstruction of [Chou, Love, Sandhu and Shi,
arXiv:2108.06049v3, Parameter 4.1 and Corollary 4.4](https://arxiv.org/abs/2108.06049v3).
That local-algorithm obstruction applies to sparse random signed
Max-$q$-XOR for even $q\ge4$, at sufficiently large fixed degree and
under the source's logarithmic-depth bound. The Basso–Gamarnik–Mei–Zhou
transfer above only needs the resulting obstruction at each fixed depth.
It requires no interchange of depth and system size. The exclusion
$q\ge4$ is essential; this is not an obstruction for the SK two-spin
model treated here.

For comparison, [Goh, arXiv:2404.06087v6, Theorem 4.2 and
Corollary 4.2.1][goh], treats even interaction order at least four.
Its logarithmic-depth obstruction concerns sparse random-regular
Max-q-XORSAT; the dense spin-glass corollary is explicitly conditional
on swapping limits. The source states on p. 12 that its sparse/dense
equivalence is only established at fixed depth, so it does not prove
a dense logarithmic-depth obstruction. These hypotheses do not include
quadratic SK. Neither a conclusion for all mixed spin glasses nor a
general quantum advantage follows from §9.

### 9.10 The regular-MaxCut consequence has its own limits

The original manuscript also gives a consequence for MaxCut. For each
$\eta>0$ it selects one finite depth and normalized angles, and then
a degree threshold, such that every finite simple unweighted $(D+1)$-regular graph of
girth greater than $2p+1$ has expected cut fraction at least
$$
\frac12+\frac{P_*-\eta}{\sqrt D}
$$
for all sufficiently large $D$. The usual MaxCut cost is
$H_{\rm MC}=\frac12\sum_{\{i,j\}}(I-Z_iZ_j)$, so its angles are
$2\boldsymbol\gamma/\sqrt D$: the normalized angles are fixed,
while these physical cost angles depend on degree. The sign conversion
uses a bipartition of the relevant tree neighbourhood of each edge;
the whole graph need not be bipartite.

The further optimality comparison is for a uniform simple labelled
$(D+1)$-regular graph $G_{n,D+1}$, along sizes with $n(D+1)$ even.
Write $\operatorname{OPT}(G)$ for the maximum cut size divided by $|E(G)|$,
$q_{p,G}$ for the circuit's expected cut fraction, and
$\Delta_D(G)=\operatorname{OPT}(G)-q_{p,G}(2\boldsymbol\gamma/\sqrt D,
\boldsymbol\beta)$. The same word can be chosen so that
$$
\lim_{D\to\infty}
\limsup_{\substack{n\to\infty\\n(D+1)\ \mathrm{even}}}
\Pr_G\{\sqrt D\,\Delta_D(G_{n,D+1})>\eta\}=0.
$$
Size goes to infinity first at fixed degree and word. The probability is
over the random graph; the cut fraction has already averaged the quantum
measurement. For fixed $D,p$, [McKay, Wormald and Wysocka (2004),
Theorem 1](https://doi.org/10.37236/1819), gives tight counts of cycles
of lengths at most $2p+3$. Every edge with a nontree neighbourhood is
within bounded distance of one of these cycles, so their fraction tends
to zero. The optimum is supplied separately by [Dembo, Montanari and
Sen, arXiv:1503.03923v2, Theorem 1.6(b)](https://arxiv.org/abs/1503.03923v2):
dividing their cut size per vertex by $(D+1)/2$ gives the leading cut
fraction $1/2+P_*/\sqrt{D+1}$, with an error $o(D^{-1/2})$ in the
stated iterated regime. A high-girth lower bound alone would not prove
optimality on every high-girth graph. See [OpenAI
(2026b), Corollary 1.2 and its complete proof][q-maxcut]. This separate
consequence is recorded to preserve the source's scope; it is not a
new selected formal endpoint or a joint size–degree limit.

<!-- /passage:qaoa-depth -->

<!-- passage:qaoa-finite-size -->

### 9.11 A later finite-size estimate and its limited depth consequence

A separate, later source gives a quantitative comparison with the
fixed-angle limit. Boulebnane, Khan, Subrahmanya, Herman, Farhi,
Villalonga and Shaydulin, [arXiv:2609.40309v1, Corollary S3.1,
pp. 46–47][decoupling], use the ordered-tuple Gaussian mixed-spin cost
with covariance polynomial $\xi(t)=\sum_q c_q^2t^q$ of finite degree.
Let $\Gamma>0$ bound every cost angle in a depth-$p$ word. Choose
$x>0$ bounding $\xi(2),\xi'(1),\xi''(33)$, with
$\Gamma^2p^2x\ge1$. No bound on the mixer angles is needed. Set
$$
B_p=256p^4(2e\Gamma^2p^2x)^p,\qquad
E_p=70\Gamma^2p^2x+p\log2,\qquad
R_p=(2E_p/\log2)^{2p}.
$$
For
$$
0<\varepsilon\le4\Gamma px
 \min\{e^{-1/2},2^{-(8p^2+3)/100}\},
$$
the source asserts $|\nu_n-\nu_\infty|\le\varepsilon$ whenever
$$
n\ge T_p:=\max\left\{
2^{8p^2+3}B_p
 \left(\frac{2^{\deg\xi+4}\Gamma^2p^2x^2}{\varepsilon^2}\right)^{R_p}
 \left[2\log_2\frac{4\Gamma px}{\varepsilon}+\deg\xi\right]^2,
\frac{16\Gamma px}{\varepsilon}\right\}.
$$
Here $\nu_n$ is the disorder-averaged energy per spin. This quoted
result is not an ingredient of the earlier QAOA manuscript and is not
covered by either selected formal statement.

For SK take $c_2=1/\sqrt2$. Combining the two ordered off-diagonal
couplings recovers our standard Gaussian $J_{ij}$; the diagonal adds
an independent scalar Gaussian of variance $1/2$. That scalar changes
the circuit by a global phase and has zero mean, so the expected-energy
comparison uses the same normalization. A fixed
$x\ge\max\{2,\Gamma^{-2}\}$ satisfies the above bounds for every
$p\ge1$.

For fixed mixture, $\Gamma$ and $x$, put $\varepsilon_p=e^{-p^2}$.
The small-error condition holds eventually, and direct logarithms give
$$
\log R_p=4p\log p+O(p),\qquad
\log\log T_p=4p\log p+O(p+\log p).
$$
Consequently, for any deterministic sequence of words $W_n$ with
depths $p(n)\to\infty$, one common cost-angle bound $\Gamma$,
and $p(n)\log p(n)=o(\log\log n)$, the displayed hypotheses hold
and $|\nu_n(W_n)-\nu_\infty(W_n)|\le e^{-p(n)^2}$ eventually.
This is a uniform comparison along that specified bounded-angle class.
It does not establish that the near-optimal words constructed in §9.6
have a uniform cost-angle bound, that their angles can be found
efficiently, or that a quantum measurement concentrates for this
growing-depth regime. The fixed-word second-moment theorem in §9.8
has separate quantifiers.
<!-- /passage:qaoa-finite-size -->

<a id="obligations"></a>

## 10. Logical limits of the argument

<!-- passage:obligations -->
The full-support theorem and scalar-value theorem use related but
different formal representations. Their mathematical conclusions can be
discussed together, but a direct formal implication would require the
coefficient, Brownian law, control value and diffusion translations
described in §8, with common witnesses. The finite Gaussian result
also needs its rooted energy identification before it says anything
about a QAOA circuit. The boundedness, regularization, synthesis and
transfer estimates in §9 are additional steps, with temperature-specific
hypotheses where the positive-temperature route is used.

Infinite support allows gaps. An indefinite curvature identity does not imply
strict convexity before expectation is controlled. An algebraic certificate
does not establish its analytic hypotheses. Coordinatewise convergence does
not control a growing coefficient sum. A finite-dimensional Gaussian law
does not identify an energy observable without its operator argument.
Separate witnesses cannot be merged silently. The order
$\forall\varepsilon\ \exists\text{finite word}\ \lim_{n\to\infty}$
cannot be replaced by a fixed-instance depth limit.

The local comparison in §9.7 concerns two printed finite-step displays;
it neither replaces the cited theorem's hypotheses nor supplies the
remaining circuit estimates.
<!-- /passage:obligations -->

<a id="verification"></a>

## 11. Source checks and finite calculation

<!-- passage:verification -->
The source collection retains the two manuscripts, formal statements,
their implementations and build metadata. The derived project specifies
Lean 4.34.1 and a pinned mathlib revision. The proof-assistant and library
infrastructure is described by [de Moura and Ullrich (2021), *The Lean 4
Theorem Prover and Programming Language*](https://doi.org/10.1007/978-3-030-79876-5_37)
and [The mathlib Community (2020), *The Lean Mathematical Library*](https://doi.org/10.1145/3372885.3373824).
These references credit the software; the retained project metadata identifies
the versions used for this source. The retained polynomial computation
in §4 uses exact rational arithmetic. Its expansion matches
all 22 positive remainder
coefficients. The surplus of the $v^4$ coefficient above $1/1000$ is
$140507/1521000000$. This finite check does not establish the PDE
signs, integrability, boundary flux or limiting argument.

The source-byte audit verified the inspected edition; it did not prove
its claims. Paper assembly checked identifiers, declared scope and
document bindings, not semantic correspondence or reader understanding.
Tool-compatibility checks and synthetic fixtures exercised their stated
cases, not either selected SK theorem. Reading of the mathematical and
formal sources supports the bounded comparisons reported here, without
a complete independent proof acceptance or transitive axiom audit.

The retained observations must be kept separate. The original graph records
unrun plans and an earlier full-support attempt that could not start
because the Comparator executable was unavailable. A later retained
attempt, observed on 23 October 2026, built and exported the challenge,
then stopped while building the implementing solution. The retained
partial-observation receipt and log preserve that event: the imported
object for `Diffusion/AbsIncrement` was missing. The challenge is an
admitted specification, so its successful build and export are not a
proof of the theorem. There was no successful solution export or
research-target comparison in that observation.

The scalar-value invocation in the same original two-target run reached
a terminal failure observed on 24 October 2026. Its challenge built and
exported, but its solution build stopped because the imported object for
`Gaussian/IntegralPositiveMulGaussian` was missing. The retained scalar
receipt and log establish no solution export, kernel acceptance or
comparison acceptance. The companion source review locates both records.
Both failures concern the original build configuration. A subsequent
repair to the derived configuration was recorded; the corrected
configuration has not been replayed.

The later observation is additional run history, not a replacement for
the earlier event or a mathematical rejection of the theorem. Neither
research target has a successful source-bound comparison and transitive
axiom audit established here. Permitted axioms and checker settings
describe configuration; source names and tool-fixture receipts cannot
supply the missing target result. The full-support receipt remains a
historical partial observation; the scalar receipt is a terminal failure
of its original invocation. Neither is a replay of the subsequently
repaired source configuration.

No additional QAOA/SK Lean build or Comparator run was performed for this
editorial revision. Detailed reading coverage, exact finite-check
results, preserved unsuccessful observations and the remaining obligations
are recorded in the companion source review. This remains a draft after source-based agent review; independent mathematical acceptance and a human reconstruction study have not been performed.
<!-- /passage:verification -->

## References

- Auffinger and Chen (2015), “On properties of Parisi measures,”
  *Probability Theory and Related Fields* **161**, 817–850. Inspected
  preprint: [arXiv:1303.3573v1](https://arxiv.org/abs/1303.3573v1).
- Farhi, Goldstone and Gutmann (2014), *A Quantum Approximate Optimization
  Algorithm*, [arXiv:1411.4028v1](https://arxiv.org/abs/1411.4028v1).
- Binkowski, Koßmann, Ziegler and Schwonnek (2023), *Elementary Proof of
  QAOA Convergence*, [arXiv:2302.04968v1](https://arxiv.org/abs/2302.04968v1).
- Basso, Gamarnik, Mei and Zhou (2022), *Performance and limitations of
  the QAOA at constant levels on large sparse hypergraphs and spin glass
  models*, [arXiv:2204.10306v2](https://arxiv.org/abs/2204.10306v2).
- Boulebnane, Khan, Liu, Larson, Herman, Shaydulin and Pistoia (2026),
  *Spin–Boson Mapping of the Quantum Approximate Optimization Algorithm*,
  [arXiv:2505.07929v2](https://arxiv.org/abs/2505.07929v2).
- Boulebnane, Khan, Subrahmanya, Herman, Farhi, Villalonga and Shaydulin
  (2026), *Decoupling of the QAOA into independent spin-boson systems and
  high-depth performance on pure and mixed spin glasses*,
  [arXiv 2609.40309, version 1](https://arxiv.org/abs/2609.40309v1).
- Goh (2025), *The Overlap Gap Property limits limit swapping in the
  QAOA*, [arXiv:2404.06087v6](https://arxiv.org/abs/2404.06087v6).

- OpenAI (2026a), *Full support of the zero-temperature
  Sherrington–Kirkpatrick order parameter*, manuscript, 27 September 2026.
- OpenAI (2026b), *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*, manuscript, 25 September 2026.
- Auffinger and Chen (2017), “Parisi formula for the ground state energy
  in the mixed $p$-spin model,” *Annals of Probability* **45**, 4617–4631.
- Auffinger and Chen (2015), “The Parisi formula has a unique minimizer,”
  *Communications in Mathematical Physics* **335**, 1429–1444.
- Auffinger, Chen and Zeng (2020), “The SK model is infinite step replica
  symmetry breaking at zero temperature,” *Communications on Pure and
  Applied Mathematics* **73**, 921–943.
- Jagannath and Tobasco (2016), “A dynamic programming approach to the
  Parisi functional,” *Proceedings of the American Mathematical Society*
  **144**, 3135–3150.
- Chen, Handschy and Lerman (2018), “On the energy landscape of the mixed
  even $p$-spin model,” *Probability Theory and Related Fields* **171**,
  53–95.
- Montanari (2025), “Optimization of the Sherrington–Kirkpatrick
  Hamiltonian,” *SIAM Journal on Computing* **54**, FOCS19-1–FOCS19-38.
- El Alaoui, Montanari and Sellke (2021), “Optimization of mean-field spin
  glasses,” *Annals of Probability* **49**, 2922–2960.
- Farhi, Goldstone, Gutmann and Zhou (2022), “The Quantum Approximate
  Optimization Algorithm and the Sherrington–Kirkpatrick Model at Infinite
  Size,” *Quantum* **6**, 759.
- Basso, Farhi, Marwaha, Villalonga and Zhou (2022), “The Quantum
  Approximate Optimization Algorithm at High Depth for MaxCut on
  Large-Girth Regular Graphs and the Sherrington–Kirkpatrick Model,”
  *LIPIcs* **232**, 7:1–7:21.
- El Alaoui, Montanari and Sellke (2023), “Local algorithms for Maximum
  Cut and Minimum Bisection on locally treelike regular graphs of large
  degree,” *Random Structures and Algorithms* **63**, 689–715.
- Chen (2026), *FRSB in the SK spin glass: convergence to full-interval
  support at zero temperature*, arXiv:2607.18032v1.
- Lopatto (2026), *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*, arXiv:2607.11756v3.
- Zhou (2026), “Existence of full replica symmetry breaking for the
  Sherrington–Kirkpatrick model at low temperature,” *Communications on
  Pure and Applied Mathematics* **79**, 1746–1770.

- Sellke (2021), *Optimizing Mean Field Spin Glasses with External
  Field*, [arXiv:2105.03506v4](https://arxiv.org/abs/2105.03506v4).
- Jekel, Sandhu and Shi (2026), *Potential Hessian Ascent: The
  Sherrington–Kirkpatrick Model*,
  [arXiv:2408.02360v3](https://arxiv.org/abs/2408.02360v3).
- Chou, Love, Sandhu and Shi (2022), *Limitations of Local Quantum
  Algorithms on Random Max-k-XOR and Beyond*,
  [arXiv:2108.06049v3](https://arxiv.org/abs/2108.06049v3).
- Lopatto (2026), *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*,
  [arXiv:2607.11756v4](https://arxiv.org/abs/2607.11756v4).
  This later comparison is distinct from the v3 input cited above.
- Lopatto (2026), *Parisi measure of the Sherrington–Kirkpatrick model
  with external field*, [arXiv:2610.00127v1](https://arxiv.org/abs/2610.00127v1).
- Jones and Knill (1999), “Efficient Refocussing of One Spin and Two
  Spin Interactions for NMR Quantum Computation,” *Journal of Magnetic
  Resonance* **141**, 322–325. Inspected preprint:
  [arXiv:quant-ph/9905008v1](https://arxiv.org/abs/quant-ph/9905008v1).
- Li and Khaneja (2005), *Noncommuting vector fields, polynomial
  approximations and control of inhomogeneous quantum ensembles*,
  [arXiv:quant-ph/0510012v1](https://arxiv.org/abs/quant-ph/0510012v1).
- Talagrand (2006), “The Parisi formula,” *Annals of Mathematics*
  **163**, 221–263. [Published article](https://doi.org/10.4007/annals.2006.163.221).
- Dembo, Montanari and Sen (2017), “Extremal Cuts of Sparse Random
  Graphs,” *Annals of Probability* **45**, 1190–1217. Inspected
  preprint: [arXiv:1503.03923v2](https://arxiv.org/abs/1503.03923v2).
- McKay, Wormald and Wysocka (2004), “Short Cycles in Random Regular
  Graphs,” *Electronic Journal of Combinatorics* **11**, R66.
  [Published article](https://doi.org/10.37236/1819).

- de Moura and Ullrich (2021), “The Lean 4 Theorem Prover and
  Programming Language,” *CADE 28*, 625–635.
  [Published article](https://doi.org/10.1007/978-3-030-79876-5_37).
- The mathlib Community (2020), “The Lean Mathematical Library,”
  *CPP 2020*, 367–381.
  [Published article](https://doi.org/10.1145/3372885.3373824).

[scope]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md
[support-type]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92
[support-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L19-L61
[support-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.json
[value-type]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L20-L173
[value-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16-L27
[value-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.json
[chord]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/VariationIntegrals.lean#L152-L175
[parameter-chords]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Regularity/ParameterChords.lean#L12-L56
[support-definitions]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Model.lean#L12-L79
[shifted-pairing]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Equations/ShiftedPairing.lean#L47-L91
[density-origin]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Density/GaussianLogDensity.lean#L106-L166
[fs-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/main.tex
[fs-reg]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex
[fs-signs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/signs.tex
[fs-cert]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex
[fs-curv]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex
[fs-var]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex
[fs-cons]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex
[q-intro]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex
[q-foundations]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex
[q-classical]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex
[q-synthesis]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex
[q-seeds]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex
[q-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/06-assembly.tex
[q-positive]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex
[ac2017]: https://arxiv.org/abs/1606.05335v2
[acz]: https://arxiv.org/abs/1703.06872v2
[chen2026]: https://arxiv.org/abs/2607.18032v1
[method-269]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos269/core.tex
[method-243]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/reasoning-parts/erdos243/core.tex#L3358-L3366
[method-skill]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/skills/public-mathematical-writing/SKILL.md
[method-audit]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/scripts/reasoning_record_audit.py

[ac17]: https://arxiv.org/abs/1606.05335v2
[ac-properties]: https://arxiv.org/abs/1303.3573v1
[chen26]: https://arxiv.org/abs/2607.18032v1
[eams20]: https://arxiv.org/abs/2001.00904v1
[fs-density]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/order-parameter-regularity.tex
[fs-algorithm]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/algorithm-application.tex
[fs-variation]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex
[scalar-contact-integral]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/ContactIntegral.lean#L65-L125
[scalar-hump]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Coercivity/GapBoundary.lean#L84-L153
[scalar-convexity]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Coercivity/CurvatureMoment.lean#L75-L133
[scalar-zero-hump]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Coercivity/ZeroGapHump.lean#L8-L26
[scalar-contact-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Variation/ContactAssembly.lean#L21-L72
[q-fock]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L53-L149
[q-root-energy]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L150-L280
[q-gaussian]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L282-L365
[q-rooted-classical]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L123-L255
[q-bounded-classical]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L256-L338
[q-colors]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex#L384-L608
[q-weights]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L366-L503
[q-unitary]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L504-L701
[q-substitution]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L784-L950
[q-gate-calculus]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L951-L1317
[q-synthesis-statement]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L38-L112
[q-masked-controls]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L113-L206
[q-helper-statement]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L207-L353
[q-helper-quadratics]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L354-L488
[q-additive-response]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L1318-L1459
[q-helper-responses]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L489-L960
[q-compilation]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex#L961-L1119
[q-seed-statement]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L1-L49
[q-seed-packets]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L50-L271
[q-seed-selective]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L272-L504
[q-seed-echo]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L505-L734
[q-seed-gram]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L735-L873
[q-seed-visibility]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex#L874-L1006
[q-transfer]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L1-L52
[q-ordinary-updates]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex#L702-L783
[fggz]: https://arxiv.org/abs/1910.08187v4
[bfmvz]: https://arxiv.org/abs/2110.14206v3
[binkowski]: https://arxiv.org/abs/2302.04968v1
[spin-boson]: https://arxiv.org/abs/2505.07929v2
[decoupling]: https://arxiv.org/abs/2609.40309v1
[goh]: https://arxiv.org/abs/2404.06087v6
[q-maxcut]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/08-regular-maxcut.tex
