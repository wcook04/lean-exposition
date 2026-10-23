# From Parisi full support to the QAOA question

## A long reasoning record

Draft, 23 October 2026. Mathematical sources: OpenAI's full-support
manuscript of 27 September 2026 and QAOA manuscript of 25 September 2026,
at revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.

<!-- passage:overview -->
The full-support manuscript proves that an admissible integrable minimizer
of the zero-temperature Parisi functional for the pure zero-field
Sherrington–Kirkpatrick model has Stieltjes support equal to every overlap
scale in [0,1). The proof turns a hypothetical support gap into a constant
interval for the order parameter. Variational contact at the ends of that
interval conflicts with a strict curvature inequality inside it. Full
support then makes the gradient diffusion's second moment equal to time,
and its correlation with Brownian motion represents the ground-state value.

This record reconstructs those arguments and follows the finite Gaussian
approximation into the separate QAOA manuscript. The latter claims that
finite deterministic circuits approach the SK optimum when system size tends
to infinity before circuit depth increases. Its circuit construction needs
additional approximation, synthesis, seed-removal and transfer arguments.
The two retained Lean targets concern full support and scalar value
consequences; neither states QAOA circuit convergence. Their local formal
checks remain unrun. The record is a source reconstruction with explicit
correspondence obligations, not a completed independent proof review.
[FS, Theorem thm:full-support][fs-main]; [Q, Theorem thm:main][q-intro];
[formal scope][scope].
<!-- /passage:overview -->

The intended reader knows real analysis, elementary stochastic calculus and
variational minimization. The central gap contradiction is given in full;
the lengthy PDE estimates and quantum constructions retain source destinations.
The companion short paper and exposition offer complementary reading routes.
Source keys **FS** and **Q** refer to
the two manuscripts above.

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

The control value and Parisi functional are

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
it does not separately supply one. [FS, eq:model-control through
eq:model-ground-state][fs-main]; [Auffinger–Chen, Theorem 1 and the proof of Lemma 3][ac2017].
<!-- /passage:model -->

<!-- passage:targets -->
Write $u=\Phi_x$, $a=\Phi_{xx}$, and
$dX_t=\gamma(t)u(t,X_t)\,dt+dB_t$, $X_0=0$.
The three targets concern different objects:

| Target | Content | Evidence represented here |
| --- | --- | --- |
| Full support | Given an admissible minimizer, $\operatorname{supp}\mu_\gamma=[0,1)$, strict increase of $\gamma$, $\mathbb E u(t,X_t)^2=t$, and $\mathbb E a(t,X_t)^2=1$ | Manuscript argument and retained formal interface; local formal checks unrun |
| Scalar value | A spin-valued terminal variable of a bounded martingale represents $P_*$; finite Gaussian coefficients converge at fixed $T<1$, then $T\uparrow1$ | Separate formal interface, conditional on a minimizer and, for its first two clauses, a diffusion |
| QAOA | For every accuracy, a finite deterministic circuit, independent of size and disorder, approaches $P_*$ in limiting expected energy | Broader manuscript claim; no retained circuit-convergence declaration |

The support interface additionally supplies a Stieltjes measure and a
diffusion, and quantifies the moment identities over every associated
diffusion. Smooth density and algorithmic consequences are not conclusions
of that selected declaration. [SKFullSupport, lines 81–92][support-type].
<!-- /passage:targets -->

<a id="argument-map"></a>

## 2. Dependencies and prior work

<!-- passage:dependencies -->
The argument order is determined by what each step needs.

| Conclusion | Inputs | Source destination |
| --- | --- | --- |
| Compact-strip regularity and diffusion identities | Heat approximation, integrable monotone coefficient, bounded gradient, terminal smoothing | [FS regularity][fs-reg], lem:regularity, lem:diffusion, lem:constant-transfer |
| Variational contact | First variation; addition and removal of Stieltjes mass | [FS variation][fs-var], lem:first-variation, lem:contact |
| Strict positive-step curvature | Backward and forward shape inequalities; derivative correction; rational certificate; compact-strip passage | [FS signs][fs-signs], [certificate][fs-cert], [curvature][fs-curv] |
| Full support | Contact, strict curvature, zero-step monotonicity, separate terminal-plateau exclusion | [FS variation][fs-var], proof of thm:full-support |
| Scalar value | Full-support moments, martingale convergence, terminal control, integrability | [FS consequences][fs-cons], cor:value |
| Finite Gaussian coefficients | Euler convergence, orthogonal normalization, mean-preserving rounding, vector error estimates | [FS consequences][fs-cons], prop:gaussian |
| Ordinary QAOA word | Rooted realization, bounded regularization, synthesis, seed removal, fixed-word transfer | [Q §§2–6][q-foundations], [assembly][q-assembly] |

Auffinger–Chen–Zeng's infinite support does not exclude an interior gap.
Their terminal-plateau observation excludes an endpoint obstruction only.
The full-support manuscript develops a rational coercivity route and credits
Chen's 2026 theorem for the same full-support conclusion and smooth absolute
continuity. This record makes no priority claim for full support.
[ACZ, Theorem 1 and Remark 7][acz]; [Chen, Theorem 1.3][chen2026];
[FS introduction][fs-main].

Control and gradient-martingale methods have antecedents in
[Auffinger–Chen](https://doi.org/10.1007/s00220-014-2254-z) and
[Jagannath–Tobasco](https://arxiv.org/abs/1502.04398v4). A finite-temperature
theorem with smooth terminal value $\log\cosh$ does not alone establish
the result with terminal cusp $|x|$. The FS manuscript supplies its own
[compact-strip approximation][fs-reg];
[Chen–Handschy–Lerman](https://arxiv.org/abs/1609.04368v4) supplies earlier
zero-temperature regularity and control results.
[Montanari](https://arxiv.org/abs/1812.10897v2) and
[El Alaoui–Montanari–Sellke](https://arxiv.org/abs/2001.00904v1) inform
normalized discretization and optimization. The particular shifted Gaussian
coefficient identity used here is proved in [the 2026 companion][fs-cons].
These citation roles must survive a shortened account.
<!-- /passage:dependencies -->

<a id="variational-signs"></a>

## 3. From minimality to contact

<!-- passage:contact -->
Compact-strip analysis gives the bounded martingale
$$
u(t,X_t)=\int_0^t a(s,X_s)\,dB_s,\qquad
q(t):=\mathbb E u(t,X_t)^2,\qquad q'(t)=\mathbb E a(t,X_t)^2.
$$
Zero field gives evenness of $\Phi$, hence $u(0,0)=0$ and $q(0)=0$.
The derivative at zero is from the right. One does not differentiate the
nonsmooth terminal function at time one.

For an integrable direction $\eta$ with
$\gamma+\epsilon\eta\in\mathcal U$ for small nonnegative $\epsilon$,
the source proves
$$
D\mathcal P(\gamma)[\eta]
 =\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$
It subtracts the two value PDEs, evaluates the difference along a diffusion
with averaged gradient drift, then removes the terminal cutoff. Bounded
gradients and $\eta\in L^1$ permit dominated convergence. Minimality
makes the one-sided derivative nonnegative.

Set $G(s)=\int_s^1(q(t)-t)\,dt$ and
$S=\operatorname{supp}\mu_\gamma$.
Adding an atom at $s$ uses $\eta=\mathbf1_{[s,1)}$, giving $G(s)\ge0$.
For compact $K\subset[0,1)$, restrict the measure to $\nu=\mu_\gamma|_K$
and remove a fraction of it. The admissible direction is
$\eta_K(t)=-\nu([0,t])$, so Fubini gives
$$
0\le D\mathcal P(\gamma)[\eta_K]
 =-\frac12\int_KG(s)\,\mu_\gamma(ds).
$$
Local finiteness justifies the interchange even if total Stieltjes mass is
infinite. Nonnegativity forces $G=0$ almost everywhere for the measure;
continuity gives $G=0$ on its support. Removing atoms alone would not
cover a diffuse or singular continuous measure.

At an interior support point, $G$ has a minimum. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$,
$$
q(s)=s,\qquad q'(s)\le1.
$$
If $0\in S$, use $G(0)=q(0)=0$ and
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$ to obtain $q'(0)\le1$.
A support point need not be an atom. [FS, lem:first-variation and
lem:contact][fs-var].
<!-- /passage:contact -->

<a id="curvature-and-gap-certificate"></a>

## 4. Strict curvature on a constant interval

<!-- passage:curvature -->
On an interval with $\gamma=c>0$, put
$$
r=c\Phi_x,\quad v=r_x,\quad w=r_{xx},\quad z=r_{xxx}.
$$
Along the diffusion, the drift/diffusion pairs of $r,v,w$ are
$(0,v)$, $(-v^2,w)$ and $(-3vw,z)$, respectively. Since
$q'=c^{-2}\mathbb E v^2$, Itô's formula first gives
$$
c^2q''=\mathbb E(w^2-2v^3).
$$
The drift of $w^2$ is $z^2-6vw^2$; that of $v^3$ is
$3vw^2-3v^4$. Subtracting twice the latter gives
$$
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].
$$
This explains the coefficients in the curvature expression and identifies
the differentiated quantity: $q'''>0$ makes $q'$ strictly convex, without
requiring a fixed sign for $q''$.
The negative term prevents a pointwise positivity argument. The proof
uses both the backward PDE and the forward diffusion density.

For positive finite-step coefficients with smooth terminal value
$M^{-1}\log(2\cosh Mx)$, choose $M\geq\|\gamma_{\rm step}\|_\infty$.
This condition supplies the initial sign
$H=(cM-M^2)\operatorname{sech}^2(Mx)\leq0$.
Let $l=c\Phi$, $f=e^lg$, and
$s=-\partial_x\log g$. Inside a step, $e^l$ solves the backward heat
equation and $g$ the forward heat equation. At a forward jump
$\delta\ge0$, $g_+=g_-e^{-\delta\Phi}$. On $x>0$, the source proves
$$
v>0,\quad w\le0,\quad H:=w/(2r)+v\le0,\quad H_x\ge0,
\qquad s_x\ge1/t,\quad s_{xx}\le0,\quad j:=s_x-(s/r)v\ge0.
$$
Oddness and Taylor expansions resolve the ratios at zero. The quantity
$j$ is unchanged at a coefficient jump. Spatial-tail estimates justify
comparison on expanding bounded domains; the differential equations alone
do not supply global signs. [FS, shape:backward, shape:forward,
shape:ibp][fs-signs].

Define
$$
R=r^2,\quad K=rs,\quad b=-w/r,\quad B=b-2v,\quad L=-rs_{xx},
\quad S_1=z+bv-2Rb.
$$
Here $S_1$ is a polynomial variable, distinct from the support set.
All of $R,K,v,B,j,L,S_1$ are nonnegative and $Rb^2=w^2$. For
$\mathcal D=r\partial_x$,
$$
\mathcal D(R,K,v,b,j)
 =(2Rv,\ 2vK+Rj,\ -Rb,\ -z-bv,\ -jv+Kb-L).
$$
If $\mathcal W(F)=\mathcal DF+(v+R-K)F$, then
$f\mathcal W(F)=\partial_x(rfF)$. Integrability and vanishing boundary
values give $\mathbb E_f\mathcal W(F)=0$.

The rational certificate chooses a polynomial $F_2$, a polynomial $Q$,
a nonnegative $T_1=v(g_0R+hj)$, and weighted squares $P_i$ satisfying
$$
z^2-12Rvb^2+6v^4
 =(z+Q)^2+S_1T_1+\sum_{i=0}^4p_iP_i+\mathcal W(F_2)
  +L(x_0v^2+hbv)+P_{\rm rem}.
$$
Every one of the 22 coefficients of $P_{\rm rem}(R,K,v,B,j)$ is positive.
Its $v^4$ coefficient is $1661507/1521000000>1/1000$. Integration
removes $\mathcal W(F_2)$, while the other terms are nonnegative:
$$
\mathbb E[z^2-12vw^2+6v^4]\ge\frac1{1000}\mathbb E v^4.
$$
The complete polynomials, derivative rules and remainder table are at
[FS cert:polynomials–cert:table][fs-cert]. The accompanying
check_certificate.py re-expands the identity and compares
every remainder coefficient. This finite calculation does not establish
the analytic signs or the integration-by-parts hypotheses.

To pass to an integrable coefficient, use positive nondecreasing step
approximants remaining exactly $c$ near the selected interior time.
Compact-strip convergence controls derivatives through order four and
coupled diffusion paths. Only $v,w,z$ occur in the resulting integrated
inequality, so convergence of the density scores or ratios is unnecessary.
Strict positivity of $v$ gives
$$
q'''(t)\ge\frac1{1000c^2}\mathbb E v(t,X_t)^4>0.
$$
Thus $q'$ is strictly convex on positive constant intervals.
For $c=0$, the heat equation gives
$q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$ at interior times.
The diffusion has a positive Gaussian-mixture density. If the expectation
vanished, continuity would force $\Phi_{xxx}$ to vanish everywhere in
space; then $\Phi$ would be an even quadratic. Its one-Lipschitz bound
and bounded distance from $|x|$ exclude this. Hence $q'$ is strictly
increasing. Division by $c^2$ cannot cover this case.
[FS, prop:gap-curvature][fs-curv].
<!-- /passage:curvature -->

<a id="gap-elimination"></a>

## 5. Excluding terminal, interior and initial gaps

<!-- passage:gaps -->
First suppose $\gamma=c$ on a terminal interval $(a,1)$, with finite
$c\ge0$. Fix $s>a$. The Cole–Hopf transition kernel there is
$$
k_{s,t}(x,y)=p_{t-s}(y-x)\frac{h(t,y)}{h(s,x)},\qquad
h(t,y)=\mathbb E e^{c|y+\sqrt{1-t}Z|};
$$
for $c=0$, take $h=1$. A compact set carries positive mass of the law
of $X_s$. Restricting to that set gives a uniform positive lower bound
for the density of $X_t$ on $|y|\le1$, for $t$ near one. On
$|y|\le\sqrt{1-t}$, the two signs of $y+\sqrt{1-t}Z$ both retain
positive mass under the tilt. Thus $|u(t,y)|$ stays uniformly below one
in a window of width proportional to $\sqrt{1-t}$. Consequently
$$
1-q(t)\ge C\sqrt{1-t},\qquad
q(t)-t\le(1-t)-C\sqrt{1-t}<0
$$
near one. This makes $G(s')<0$ for $s'$ near one, contradicting
minimality. No initial density assumption for $X_s$ is used.
This covers the zero plateau and excludes empty support.
[FS, lem:no-terminal-plateau][fs-var].

An interior complementary interval has endpoints $a<b<1$ in the support.
The coefficient is constant, and contact gives
$$
q(a)=a,\quad q(b)=b,\quad q'(a),q'(b)\le1.
$$
If its constant is positive, strict convexity implies
$$
q'(t)<\frac{b-t}{b-a}q'(a)+\frac{t-a}{b-a}q'(b)\le1
\quad(a<t<b).
$$
Integration contradicts $q(b)-q(a)=b-a$. If the constant is zero,
strict increase instead gives $q'(t)<q'(b)\le1$, with the same
contradiction. When zero is a support point bordering a gap, the
one-sided contact argument gives the needed slope bound.

The remaining case is an initial gap [0,b) with zero outside the support.
There is no Stieltjes mass there, so the coefficient is zero.
Again $q'(t)<q'(b)\le1$, whereas $q(0)=0$ and $q(b)=b$.
Integration is impossible. Relative closedness makes the cases exhaustive.

Hence the support is [0,1). Contact gives $q(t)=t$; differentiation gives
$\mathbb E a(t,X_t)^2=1$, including at zero from the right.
Every nonempty open subinterval (a,b), with 0≤a<b<1, has positive measure, so
$\gamma(b)-\gamma(a)=\mu_\gamma((a,b])>0$.
Smooth absolute continuity is a further result in the source manuscript;
it is not supplied by this gap contradiction alone.
[FS, proof of thm:full-support][fs-var].
<!-- /passage:gaps -->

<a id="scalar-value-identities"></a>

## 6. Recovering the value from a martingale

<!-- passage:value -->
The bounded martingale $u(t,X_t)$ converges almost surely and in $L^2$
to $U_1$. Its second moment tends to one because $q(t)=t$.
Since $|U_1|\le1$, $\mathbb E U_1^2=1$ forces $U_1^2=1$ almost surely.

The drift bound $|\gamma u|\le\gamma\in L^1$ gives convergence of $X_t$
to $X_1$. Uniform terminal convergence of $\Phi$ to $|x|$, together
with convexity, gives $u(t,x_t)\to\operatorname{sgn}(x)$ when
$x_t\to x\ne0$. Thus $U_1X_1=|X_1|$, including when $X_1=0$;
no proof that this event has probability zero is needed.

Itô's formula gives
$$
\mathbb E\Phi(t,X_t)=\Phi(0,0)+\frac12\int_0^t\gamma(s)s\,ds.
$$
Letting $t\uparrow1$ and subtracting the functional penalty yields
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
would change the assertion. [FS, cor:value][fs-cons].
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
mean.

The approximation
$$
M_N=\sum_{j=1}^N\sqrt\Delta\,a(t_{j-1},Y_{j-1})Z_j
 =u(T,Y_N)+o_{L^2}(1)
$$
and Bessel's inequality give the vector estimates
$$
(A_j)_{j=1}^N=(\sqrt\Delta/c_j)_{j=1}^N+o_{\ell^2}(1),
$$
$$
(B_i)_{i=1}^N=
(\sqrt\Delta\,\mathbb E a(t_{i-1},Y_{i-1}))_{i=1}^N+o_{\ell^2}(1).
$$
Coordinatewise errors would not control a sum of growing length. Bounded
vector norms and Cauchy–Schwarz do. Pairing $A_j$ with $B_{j+1}$
selects the Hessian at $t_j$; the extra endpoint contributes at most
$|A_N|=o(1)$, since $|B_{N+1}|\le1$. Hence
$$
\sum_{j=0}^NA_jB_{j+1}
 =\Delta\sum_{j=1}^{N-1}\frac{\mathbb E a(t_j,Y_j)}{c_j}+o(1)
 \longrightarrow\int_0^T\mathbb E a(t,X_t)\,dt.
$$
Only afterward let $T\uparrow1$, obtaining $P_*$.
The mesh count $N$ is unrelated to the spin-system size $n$.
These coefficients describe a finite Gaussian function, not yet a circuit
on finite SK disorder. [FS, prop:gaussian][fs-cons].

The QAOA scalar input also uses the tail estimate
$0\le P_*-\int_0^T\mathbb E a(t,X_t)\,dt\le1-T$, from nonnegative
curvature and $\mathbb E a^2=1$. This estimate and the fixed-strip
regularity facts must be retained beside the coefficient limit; they are
not all fields of the selected finite-Gaussian conclusion.
[Q, eq:scalar-terminal-loss][q-classical].
<!-- /passage:gaussian -->

<a id="formal-interfaces"></a>

## 8. The retained formal interfaces

<!-- passage:formal -->
The support target takes a measurable sample space, a BrownianSystem, an
OrderParameter and IsMinimizer. FullSupportConclusion packages measure
existence, diffusion existence, full relative support for every measure
realizing the specified cumulative function, strict increase, and both
moment identities for every associated diffusion.
The challenge is an admitted specification; the implementing proof is in
OAI/Probability/SKSupport/Main.lean. [Interface][support-type];
[implementation][support-main].

The source proof assembles contact, absence of terminal plateaus, positive
and zero gap curvature, deterministic closure, and uniqueness to transfer
the moment identities to an arbitrary associated diffusion. This is a
source-inspected proof route, not an extracted dependency graph.
Two intermediate differences deserve explicit treatment:

- The manuscript states a right derivative in every admissible integrable
  direction. The formal parisi_chord_derivative uses a discrete sequence
  of convex chords between admissible parameters, sufficient for its
  minimizer inequality. [VariationIntegrals, lines 152–175][chord].
- The manuscript extends quotient variables smoothly at zero. The formal
  density argument uses raw quotients on the positive half-line, zero
  flux at the origin and reflection. Auxiliary values at zero need not
  coincide; the integrated inequality is the relevant consequence.
  [GaussianLogDensity, lines 106–166][density-origin].

The value target is a conjunction of three universally quantified statements:

1. A minimizer and an associated diffusion imply ScalarValueConclusion:
   convergence of the finite-spin ground-state sequence, a stopped
   martingale with spin-valued terminal limit, almost-sure and mean-square
   gradient convergence, three value identities and interval integrability.
2. The same hypotheses with $0<T<1$ imply FiniteGaussianConclusion:
   eventual positivity of all normalizers $j<N$, the coefficient-sum
   limit at fixed $T$, and the endpoint-integral limit.
3. A minimizer alone implies groundStateValue = parisi W γ.

The final branch constructs a diffusion internally; it does not construct a
minimizer. The definition of groundStateValue uses limUnder, which alone
does not assert convergence. The explicit Tendsto clause supplies it.
The zero-indexed formal coordinate $j-1$ corresponds to manuscript $Z_j$;
coordinate $N$ supplies the extra rounding Gaussian. Definitions are total
even at $N=0$, but positivity is only eventual in $N$.
[Value interface, lines 20–173][value-type]; [implementation][value-main].

The two APIs represent the model differently. The support coefficient is
defined on the subtype [0,1) and extended by zero. The value coefficient is
defined on all real times with interval hypotheses. Brownian structures,
control time variables and diffusion predicates differ as well.
The SKValue proof derives its own moment-contact identity; the selected
source trees do not import one another. A similarity of mathematics is not
a formal conversion lemma. Independent existence claims also do not identify
witnesses. Composition needs translations preserving value functions,
derivatives, minimization and diffusion laws.
<!-- /passage:formal -->

<a id="qaoa-construction"></a>

## 9. From the scalar formula to one ordinary QAOA word

<!-- passage:qaoa -->
The cost and mixer are
$$
C_{n,J}=n^{-1/2}\sum_{i<j}J_{ij}Z_iZ_j,\qquad B_n=\sum_iX_i.
$$
Starting from $|+\rangle^{\otimes n}$, a depth-$p$ circuit alternates
their exponentials with deterministic angles. Hold those angles fixed
while $n\to\infty$, obtaining limiting expected energy per spin $v_p$, and let
$Q_p$ be its supremum over angles. The source target is
$\lim_{p\to\infty}Q_p=P_*$. A cost expectation is bounded above by its
maximum eigenvalue, and zero-angle padding makes $Q_p$ nondecreasing.
It therefore suffices to construct one finite word for every accuracy.
Fixed-instance convergence at increasing depth is a different quantifier
order. [Q, thm:main][q-intro].

**Rooted realization.** In the large-degree tree Hilbert space, normalized
child calculations generate Gaussian directions. In this realization define
$g_0=S$, the receiving-root standard Gaussian seed, and recursively
$Z_{j+1}=\mathsf G(g_j)$, where $\mathsf G$ forms the normalized child
Gaussian field. The root seed is a separate tensor factor; $F_N$ is
independent of it, so $\langle F_N,g_0\rangle=0=A_0$.
An orthogonality induction establishes the joint Gaussian law. If $\mathsf L$ is the root-shift operator,
the first-chaos calculation gives
$$
\mathsf L^*F_N=\sum_{j=0}^NB_{j+1}g_j,\qquad
\mathcal E(F_N)=\operatorname{Re}\langle F_N,\mathsf LF_N\rangle
 =\sum_{j=0}^NA_jB_{j+1}.
$$
The root's own seed is a separate factor. This does not make arbitrary
calculations on a shared descendant subtree independent.
This energy identification is an additional bridge beyond the scalar theorem.
[Q, lem:gaussian-rooted-realization, lines 132–218][q-classical].

**Finite regularization.** First fix $T,N$, then smooth the sign and
truncate transmitted functions. The energy estimate
$$
|\mathcal E(f)-\mathcal E(g)|\le(\|f\|+\|g\|)\|f-g\|
$$
controls the loss. Bounded trigonometric approximations are chosen from
output toward leaves, so each outer Lipschitz map is fixed before its
inputs are approximated. Finite vertex types exclude receiver and ancestor
types and a small helper set. The source proves
$\|f^{\rm col}-f\|^2\le C(\alpha+p_H)$, where $\alpha$ is the largest
nonhelper type mass, with $C$ independent of the number of types for
the already fixed formula. The output is $m=\sin(2\theta)$.
[Q, lem:classical-trigonometric-density and lem:classical-color-exclusion][q-classical].

**Seeded synthesis.** Cost and mixer gates, temporarily augmented by a
Gaussian longitudinal field, implement that finite calculation.
Helper paths return through the same sender to give the desired
aggregation. Refining sender types suppresses paths through different
senders; the proof must also control responses inside nested lower
calculations. Its partition estimate uses
$\rho^2=\sum_l p_l^2\le p_J\max_l p_l$, with a fixed number of lower
channels during refinement. Helpers of total mass $p_H$ and insertion
error $\eta$ give
$$
|\mathcal E(v)-\mathcal E(m)|\le2\eta+2\sqrt{p_H}.
$$
This is a theorem about a fixed surrounding circuit, not a uniform bound
over arbitrarily growing circuits. [Q, thm:classical-synthesis and
prop:helper-contraction][q-synthesis].

**Seed removal.** A further theorem approximates any fixed finite seeded
word by an ordinary cost/mixer word. A small component of norm $r$ is
given displacement of order $1/r$. Selective rotations change it while
cancelling their leading action on ordinary components. An echo with costs
of size $t/r$ amplifies the difference. The source needs
$$
v'_r-v_r=-2r\,w_r+o(r),\qquad
(t/r)(v'_r-v_r)=-2t\,w_r+o(1).
$$
An $O(r)$ replacement before dividing by $r$ would leave an uncontrolled
order-one error. The proof cancels the actual insertion directions first,
then estimates. A separate one-particle calculation identifies energy;
matching Gram matrices alone is not used as its justification.
Initialization, angle perturbation and finite probe lists are fixed before
choosing sufficiently small $r$. [Q, thm:seed-simulation,
lem:seed-one-echo and lem:seed-gram-induction][q-seeds].

**Transfer.** After every approximation is fixed, the circuit is one finite
word independent of degree, size and disorder. The fixed-word tree-to-SK
identity gives its fixed-parameter SK value. Strong convergence in the tree
calculus also requires occupation control for energy: the source bounds an
edge remainder by $\langle\mathsf N\rangle/(D+1)$, using a uniformly bounded
first occupation moment. Arbitrarily large and inverse angles are allowed.
Consecutive equal gate types can be merged and identities inserted to obtain
the alternating form. [Q, prop:tree-transfer and energy lemma][q-foundations].

The final proof allocates errors explicitly. Choose classical error
$\varepsilon/4$ and $2\sqrt{p_H}<\varepsilon/4$.
With $\eta=\varepsilon/8$, synthesis gives
$$
\mathcal E(v)\ge\mathcal E(m)-2\eta-2\sqrt{p_H}
 >P_*-3\varepsilon/4.
$$
Seed removal spends less than $\varepsilon/4$. Only then take the
thermodynamic limit of the resulting fixed word. The order is:
accuracy; minimizer and $T<1$; finite scalar mesh; smoothing and bounded
approximations; types; helpers and commutators; fixed seeded word; seed-removal
parameters; one ordinary word; $n\to\infty$.
No interchange of limits, quantitative depth bound, finite-size rate or
efficient angle-selection procedure is supplied.
[Q §6, rem:order-of-choices][q-assembly].
<!-- /passage:qaoa -->

<!-- passage:alternative -->
The positive-temperature appendix supplies an alternative classical input.
Let $\mu_{\beta_0}$ be the positive-temperature Parisi measure and
$q_{\beta_0}=\max\operatorname{supp}\mu_{\beta_0}$. In this paragraph,
$a=\phi_{\beta_0,xx}$ and $X$ refer to the rescaled positive-temperature
PDE and its diffusion, with terminal value
$\beta_0^{-1}\log(2\cosh(\beta_0 x))$, rather than the zero-temperature
objects above. The route first fixes a sufficiently large finite
$\beta_0$, then a cutoff
$T<q_{\beta_0}$, then a finite message-passing discretization. Lopatto's
cited interval-support theorem supplies the positive-temperature support
hypothesis. The source derives
$$
\int_0^T\mathbb E a(t,X_t)\,dt
 \ge P_*-\frac{1/4+\log2}{\beta_0}-(q_{\beta_0}-T).
$$
At fixed temperature, cutoff and horizon, the finite-degree edge calculation
precedes the continuum limit. A separate strong occupation convergence
argument identifies that edge value with rooted Hilbert-space energy.
A finite-dimensional central limit theorem alone would not do so.

The appendix records corrections to two displayed finite-step formulas in
its cited message-passing source, including the sum endpoints
$1,\ldots,L-1$. These deserve an exact-edition comparison during independent
review; the source explains that the endpoint difference disappears in the
later continuum limit. The resulting bounded formula enters the same
synthesis and seed-removal route. This route is independent of the
zero-temperature companion, not a second consequence of the retained
full-support theorem. [Q appendix, lem:eams-finite-step,
lem:eams-positive-continuum, lem:classical-strong-limit][q-positive].
<!-- /passage:alternative -->

<a id="obligations"></a>

## 10. Correspondence obligations and excluded shortcuts

<!-- passage:obligations -->
The following are obligations of this reconstruction and its formal
correspondence. They do not assert defects in the source theorems.

| ID | Obligation | What would discharge it |
| --- | --- | --- |
| O1 | Match the two formal model representations | Translations for coefficients, controls, Brownian systems and diffusions preserving values, derivatives and minimization |
| O2 | Establish local formal-check status | Source-bound build and transitive axiom audit, then selected Comparator challenges |
| O3 | Check the analytic foundation in full | Independent review of terminal approximation, derivative convergence, shape comparisons, tail estimates and transfer |
| O4 | Match scalar statements to QAOA use | Index-by-index Gaussian/normalizer/rounding correspondence, auxiliary regularity and tail estimates, consistent witnesses |
| O5 | Review the circuit construction | Rooted energy identity, finite regularization, growing-type uniformity, nested synthesis errors, seed removal and transfer |
| O6 | Verify external applications | Exact theorem editions and hypotheses, covariance scaling, admissible classes, and separate temperature routes |
| O7 | Test reader reconstruction | A reader recovers the gap contradiction, the extra Gaussian's purpose and the additional circuit obligations |

Infinite support allows gaps. An indefinite curvature identity does not imply
strict convexity before expectation is controlled. An algebraic certificate
does not establish its analytic hypotheses. Coordinatewise convergence does
not control a growing coefficient sum. A finite-dimensional Gaussian law
does not identify an energy observable without its operator argument.
Separate witnesses cannot be merged silently. The order
$\forall\varepsilon\ \exists\text{finite word}\ \lim_{n\to\infty}$
cannot be replaced by a fixed-instance depth limit.

These observations explain why particular shortcuts would be insufficient;
they are not an invented history of failed proof attempts. The evidence graph
retains the claims as unverified. Passage hashes preserve which explanation
was assessed, not whether it proves the theorem.
<!-- /passage:obligations -->

<a id="verification"></a>

## 11. Source checks and finite calculation

<!-- passage:verification -->
The [source collection][scope] retains 347 OAI
modules, the two manuscripts, challenge interfaces and build metadata.
The derived project uses Lean v4.34.1 and mathlib revision
d13f23b723b8a846827a245b89c10fc7d3f11612.

The source-checkout polynomial check reproduces the certificate identity using
exact rational arithmetic. Run from the repository root, not from an exported
paper bundle:

    python3 papers/qaoa-sk/long/check_certificate.py

With SymPy 1.14.0, the expansion matches all 22 positive remainder
coefficients. The surplus of the $v^4$ coefficient above $1/1000$ is
$140507/1521000000$. SymPy is optional for this paper computation and is
not a core CLI dependency. The script checks no analytic assumptions.

Source inspection, source-byte checks, this finite calculation, formal replay
and semantic review are different kinds of evidence. This record does not
report a fresh QAOA/SK Lean build, transitive axiom audit, Comparator run or
complete independent proof review. Comparator's permitted axioms
(propext, Quot.sound, Classical.choice) and disabled Nanoda setting are
configuration, not an observed audit result. Detailed reading coverage and
draft status are preserved in the long-stage mapping.
<!-- /passage:verification -->

## 12. Source and method notes

The source-checkout bibliography references.bib records the original literature
and exact manuscript editions. The standard paper bundle does not contain that
bibliography file or the polynomial-check script; its source citations remain
in the text and evidence graph. Section-specific source links carry the load-bearing
citations; a general bibliography is not a substitute for them.

This record adapts public long-record practices from Will Cook's
[Erdős #269 record][method-269] and [writing skill][method-skill]:
separate neighboring questions before proving them, explain the decisive
transition, retain subsidiary proof destinations and reconcile short and long
statements. The [public correspondence audit][method-audit] distinguishes
source-span agreement from mathematical validation. The [#243 record][method-243]
shows how to retain the precise reason a proposed implication fails; §10
uses that practice for logical shortcuts, without inventing research history.
These are writing and evidence methods, not mathematical inputs to SK.
The text is newly authored.



[scope]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/281.md
[support-type]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92
[support-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L19-L61
[value-type]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L20-L173
[value-main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16-L27
[chord]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/VariationIntegrals.lean#L152-L175
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
