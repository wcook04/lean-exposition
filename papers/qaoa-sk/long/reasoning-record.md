# From Parisi full support to the QAOA question

## A long reasoning record

Draft, 23 October 2026. Mathematical sources: OpenAI's full-support
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

The intended reader knows real analysis, elementary stochastic calculus and
variational minimization. The central gap contradiction is given in full;
the lengthy PDE estimates and quantum constructions retain source destinations.
The companion short paper and exposition offer complementary reading routes.
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

Only then does the value argument use bounded-martingale convergence and
the attained Parisi formula to express $P_*$ as a terminal Brownian
correlation and an integral of expected curvature. Section 6 defines
the terminal martingale variable and proves these equalities.
The fixed-$T$ Gaussian approximation recovers this integral through
Euler coupling, orthogonal normalization and mean-preserving rounding.
The QAOA theorem additionally requires rooted energy identification,
classical synthesis, removal of temporary seeds and transfer to fixed
angles. Sections 3–9 explain the transitions in that order. The original analytic details are in [OpenAI (2026a), §§2–7][fs-main],
and the circuit construction is in [OpenAI (2026b), §§2–6][q-intro].

### 2.2 The regularity available before the proof starts

On each fixed strip $[0,T]\times\mathbb R$, $T<1$, the source gives
bounded, jointly continuous spatial derivatives of every finite order,
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
[OpenAI (2026a), §2][fs-reg]; [OpenAI (2026a), §§3 and 6][fs-var].

### 2.3 Which prior results play which role

Auffinger–Chen's ground-state formula identifies an infimum. Its attainment
construction is in the proof of Lemma 3; this is why both that proof and
Theorem 1 are cited when choosing a minimiser. In the cited arXiv v2 these
destinations are printed p. 3 and pp. 10–12, respectively. The support
statement itself remains conditional on a minimiser. See
[Auffinger and Chen (2017), Theorem 1 and proof of Lemma 3][ac2017].

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
the scaling examines $\beta\mu_\beta$ vaguely on $[0,1)$, while
unscaled Parisi probability measures may converge weakly toward
$\delta_1$. These are different measures and topologies. Convergence
without an interval-specific lower bound can lose support information.
The direct zero-temperature gap proof
below is therefore essential. [OpenAI (2026a), §§1–2][fs-main].

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
A support point need not be an atom. [OpenAI (2026a), §§3 and 6][fs-var].
<!-- /passage:contact -->

<a id="curvature-and-gap-certificate"></a>

## 4. Strict curvature on a constant interval

<!-- passage:curvature -->
The contact conditions will rule out a positive constant interval once
$q'$ is strictly convex there. The analytic claim needed for this purpose
holds for every admissible $\gamma$ that is constant on the interval;
minimality is not one of its hypotheses. Fix such an interval with
$\gamma=c>0$, and put
$$
r=c\Phi_x,\qquad v=r_x,\qquad w=r_{xx},\qquad z=r_{xxx}.
$$
The proof has four stages: identify the curvature expectation, establish
shape inequalities for smooth finite-step data, remove its negative term
by an exact identity and an integration by parts, then pass the integrated
inequality to the original coefficient. [OpenAI (2026a), Proposition 5.1][fs-curv].
The transformed-density method has antecedents in Chen's zero-temperature
comparison and Lopatto's positive-temperature analysis. The full-support proof's
particular strict polynomial certificate is identified below.

### 4.1 The differentiated quantity

Along the diffusion, the drift/diffusion
pairs of $r,v,w$ are $(0,v)$, $(-v^2,w)$ and $(-3vw,z)$, respectively.
Since $q'=c^{-2}\mathbb E v^2$, Itô's formula gives
$$
c^2q''=\mathbb E(w^2-2v^3).
$$
The drift of $w^2$ is $z^2-6vw^2$; that of $v^3$ is
$3vw^2-3v^4$. Subtracting twice the latter gives
$$
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].
$$
Thus a positive lower bound for this expectation makes $q'$ strictly
convex, without requiring a fixed sign for $q''$. The negative middle
term prevents a pointwise positivity argument. Bounded higher spatial
derivatives on a smaller constant interval justify the differentiations.
[OpenAI (2026a), §2][fs-reg].

### 4.2 The analytic input to the certificate

First take a positive,
nondecreasing finite-step coefficient and terminal value
$M^{-1}\log(2\cosh Mx)$, with $M\ge\|\gamma_{\rm step}\|_\infty$.
On a step of height $c$, write $l=c\Phi$ and factor the density of $X_t$
as $f=e^l g$. The function $e^l$ solves the backward heat equation,
while $g$ solves the forward heat equation. Write
$p_t(x)=(2\pi t)^{-1/2}\exp(-x^2/(2t))$ for the heat kernel, $t>0$.
On the first step,
$g(t,x)=p_t(x)e^{-l(0,0)}$, so its logarithmic score is
$s=-\partial_x\log g=x/t$. At a forward jump $\delta=c_+-c_-\ge0$,
continuity of $f$ gives $g_+=g_-e^{-\delta\Phi}$.
[OpenAI (2026a), §4][fs-signs].

For $x>0$, the backward and forward comparisons prove
$$
v>0,\quad w\le0,\quad H:=w/(2r)+v\le0,\quad H_x\ge0,
\qquad s_x\ge1/t,\quad s_{xx}\le0,\quad
j:=s_x-(s/r)v\ge0.
$$
Here the smoothing constraint supplies the terminal signs
$H=(cM-M^2)\operatorname{sech}^2(Mx)\le0$ and $H_x\ge0$.
Backward coefficient rescaling preserves them. The forward ratio
comparison uses the already established signs through
$2H_x-w-s_{xx}\ge0$, and $j$ is unchanged at a forward jump.
These are global comparisons: differentiated tail estimates control
spatial infinity, while odd Taylor expansions control the quotient
expressions at zero. The differential equations alone would not establish
the signs on the whole line. [OpenAI (2026a), §4][fs-signs].

Define
$$
R=r^2,\quad K=rs,\quad b=-w/r,\quad B=b-2v,\quad
L=-rs_{xx},\quad S_1=z+bv-2Rb.
$$
The subscript distinguishes $S_1$ from the support set. The sign conversion
is explicit:
$$
B=-2H\ge0,\qquad S_1=2rH_x\ge0\quad(x>0),\qquad Rb^2=w^2.
$$
Since $r,s$ are odd, $r_x=v>0$ and $s_x\ge1/t$, they are both positive
on $x>0$, so $K\ge0$ and $L\ge0$ there. Together with $R,v,j\ge0$,
this gives all certificate signs. The quantities $R,K,v,b,B,j,L,S_1$ are even; smooth extension and continuity carry the signs across zero and to
the negative half-line. In particular, the extended values satisfy
$b(0)=-z(0)/v(0)$, $j(0)=0$ and $S_1(0)=0$.
[OpenAI (2026a), §4][fs-signs].

For $\mathcal D=r\partial_x$ the derivative rules are
$$
\mathcal D(R,K,v,b,j)
 =(2Rv,\ 2vK+Rj,\ -Rb,\ -z-bv,\ -jv+Kb-L).
$$
Because $f_x/f=r-s$, the operator
$\mathcal W(F)=\mathcal DF+(v+R-K)F$ satisfies
$$
f\mathcal W(F)=\partial_x(rfF).
$$
The tail estimates make every polynomial term used below integrable and
make $rfF$ vanish at both infinities. Hence
$\mathbb E_f\mathcal W(F)=0$. This analytic fact is what permits a
polynomial correction to change pointwise signs without changing the
expectation. [OpenAI (2026a), §4][fs-signs].

### 4.3 Why this derivative correction works

The certificate sets
$$
Q=Avb+Cv^2+kKv-2kRb+T_0Rv,\qquad T_1=v(g_0R+hj),
$$
where $g_0,h>0$ and the exact rational constants are specified in the cited certificate. The later coefficient $x_0$ is positive as well. It seeks a
square $(z+Q)^2$ and the nonnegative product $S_1T_1$.
Their combined coefficient of $z$ is $2Q+T_1$. Among the derivative
rules above, only $\mathcal D b=-z-bv$ contains $z$, so the coefficient
of $z$ in $\mathcal W(F)$ is $-\partial_bF$. Choosing
$$
\partial_bF_2=2Q+T_1
$$
therefore cancels every $z$ term in
$z^2-12Rvb^2+6v^4-(z+Q)^2-S_1T_1-\mathcal W(F_2)$.
This is the purpose of the first two lines of the source polynomial
$F_2$; its remaining terms are independent of $b$.
The last derivative rule also gives
$\partial_jF_2=x_0v^2+hbv$, retaining the favourable term
$L(x_0v^2+hbv)$. [OpenAI (2026a), Lemma 4.1][fs-cert].

The resulting rational identity is
$$
z^2-12Rvb^2+6v^4
 =(z+Q)^2+S_1T_1+\sum_{i=0}^4p_iP_i+\mathcal W(F_2)
   +L(x_0v^2+hbv)+P_{\rm rem}.
$$
The $p_i$ are positive rational numbers. The $P_i$ are squares
multiplied respectively by $Rj,RB,Kv,vB,1$, all nonnegative.
Every one of the 22 coefficients of $P_{\rm rem}(R,K,v,B,j)$ is
positive, and its $v^4$ coefficient is
$1661507/1521000000>1/1000$. Integration removes
$\mathcal W(F_2)$ and leaves
$$
\mathbb E[z^2-12vw^2+6v^4]
 \ge\frac{1661507}{1521000000}\mathbb E v^4
 \ge\frac1{1000}\mathbb E v^4.
$$
The exact constants, complete polynomials and remainder table remain at
[OpenAI (2026a), Lemma 4.1][fs-cert]. An exact rational expansion checks
this finite identity and all remainder coefficients. It establishes
neither the analytic signs nor the boundary and integrability hypotheses.

### 4.4 Transfer and strictness

Fix an interior time of the original positive
constant interval. Use positive nondecreasing step approximants that remain
exactly $c$ on a closed neighbourhood of that time. The finite-step
inequality just proved holds for each approximant. Compact-strip
convergence controls spatial derivatives through order four, and coupling
with the same Brownian motion controls the diffusion paths. Higher spatial
derivative bounds give the uniform continuity needed when evaluating those
derivatives along the paths. Thus the integrated inequality passes to the
limit. Only $v,w,z$ occur in it; convergence of density scores, ratios or
approximation-uniform tail constants is unnecessary.
[OpenAI (2026a), §2][fs-reg]; [OpenAI (2026a), Proposition 5.1][fs-curv].

Strict positivity survives by a separate argument. At a later time $b$
in the same constant interval, the function $\psi=\Phi(b,\cdot)$ is convex,
even and a bounded distance from $|x|$, so $\psi'$ is not constant.
Differentiating the Cole–Hopf formula gives
$$
\Phi_{xx}(t,x)
 =\mathbb E^{\rm tilt}_{t,x}\psi''
    +c\operatorname{Var}^{\rm tilt}_{t,x}(\psi')>0.
$$
The expectations use the probability density
$$
\nu_{t,x}(dy)=
\frac{e^{c\psi(y)}p_{b-t}(y-x)}
     {\int_{\mathbb R}e^{c\psi(z)}p_{b-t}(z-x)\,dz}\,dy.
$$
It is positive everywhere; since $\psi'$ is not constant, the variance is
strictly positive. Consequently
$$
q'''(t)\ge\frac1{1000c^2}\mathbb E v(t,X_t)^4>0.
$$
This proves the required strict convexity of $q'$.
[OpenAI (2026a), §2][fs-reg]; [OpenAI (2026a), Proposition 5.1][fs-curv].

For $c=0$, use the heat equation separately:
$$
q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0.
$$
At an interior time the diffusion has a positive Gaussian-mixture density.
If the expectation vanished, continuity would force $\Phi_{xxx}$ to vanish
everywhere; then $\Phi$ would be an even quadratic. Its one-Lipschitz
bound and bounded distance from $|x|$ exclude that possibility. Hence
$q'$ is strictly increasing on a zero interval. Division by $c^2$ cannot
cover this case. [OpenAI (2026a), §2][fs-reg].
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
[OpenAI (2026a), §§3 and 6][fs-var].

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
Every nonempty open subinterval $(a,b)$, with $0\le a<b<1$, has positive measure, so
$\gamma(b)-\gamma(a)=\mu_\gamma((a,b])>0$.
Smooth absolute continuity is a further result in the source manuscript;
it is not supplied by this gap contradiction alone.
[OpenAI (2026a), §§3 and 6][fs-var].
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
would change the assertion. [OpenAI (2026a), §7][fs-cons].
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
research-target replay is claimed.

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
need not coincide. The precise source spans for both comparisons are in
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
claim about the construction for $N\ge1$.

### 8.3 Relating the two statements

The scalar proof independently derives its moment-contact identity; it
does not require the full-support proof as an imported premise. To claim
a formal composition of the two statements, one would have to identify
the coefficients on $[0,1)$, the Brownian laws and filtrations, and the
associated diffusion laws. One would also have to change variables
between absolute-time and elapsed-time control integrals while
preserving admissibility, payoff and supremum. Equality of the resulting
values would then have to transport derivatives and minimization, with
the same minimizer and diffusion witnesses. These translation theorems
are not supplied by mathematical resemblance alone. The separate
scalar proof and the manuscript's mathematical sequence in §§3–7 remain
valid descriptions without asserting such a formal composition.
<!-- /passage:formal -->

<a id="qaoa-construction"></a>

## 9. From the scalar formula to one ordinary QAOA word

<!-- passage:qaoa -->
On a single spin, let $Z=\operatorname{diag}(1,-1)$ and
$X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$; $Z_i$ and $X_i$ act on spin $i$
and as the identity on the other spins. Write
$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$. The cost and mixer are
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
order. [OpenAI (2026b), Theorem 1.1][q-intro].

### 9.1 Rooted realisation

This step changes the setting while preserving
specified inner products. In the source's real classical rooted space,
a centred child vector $f$ produces a parent Gaussian position
$\mathsf G(f)$ with
$\mathbb E[\mathsf G(f)\mathsf G(h)]=\langle f,h\rangle$.
The receiving root's own seed is an independent tensor factor. The root
shift $\mathsf L$ moves a centred vector into the new root's one-child
sector with constant root seed; it is an isometry. Its adjoint extracts
the constant-root-seed first Gaussian chaos. These are separate properties
of the rooted model, established in [OpenAI (2026b), §2][q-foundations].

Start with the standard root seed $g_0=S$ and recursively set
$Z_{j+1}=\mathsf G(g_j)$. To see that the scalar construction of §7
applies, suppose $g_0,\ldots,g_{j-1}$ are centred orthonormal vectors.
The covariance rule gives independent standard normals $Z_1,\ldots,Z_j$.
The multiplier of $Z_j$ in $g_j$ depends only on its predecessors, so
conditional mean zero gives orthogonality to $g_1,\ldots,g_{j-1}$;
the chosen $c_j$ gives unit norm. Independence of the receiving-root
seed gives orthogonality to $g_0$. This closes the induction, using the
same variables at each height through the source's compatible
empty-descendant embeddings.

Oddness of $u$ and evenness of $a$ make $Y_j$ and $g_j$ odd under
simultaneous seed reversal. The centred rounding variable
$2F_{\rm G}(Z_{N+1})-1$ is odd too, so $F_N$ is centred. It depends on
the child Gaussian positions and is independent of the receiving-root
seed; hence $\langle F_N,g_0\rangle=0=A_0$. Projection onto the first
chaos now gives the energy, beyond identifying the Gaussian law:
$$
\mathsf L^*F_N=\sum_{j=0}^NB_{j+1}g_j,\qquad
\mathcal E(F_N)=\operatorname{Re}\langle F_N,\mathsf LF_N\rangle
 =\sum_{j=0}^NA_jB_{j+1}.
$$
This is an identity in the limiting rooted space. Independence of its
receiving-root seed does not make arbitrary calculations on a shared
descendant subtree independent. [OpenAI (2026b), §3][q-classical].

### 9.2 Finite regularisation

First fix $T,N$, then smooth the sign and
truncate transmitted functions. The energy estimate
$$
|\mathcal E(f)-\mathcal E(g)|\le(\|f\|+\|g\|)\|f-g\|
$$
controls the loss. Bounded trigonometric approximations are chosen from
output toward leaves, so each outer Lipschitz map is fixed before its
inputs are approximated. Finite vertex types exclude receiver and ancestor
types and a small helper set, whose total probability mass is $p_H$.
The source proves
$\|f^{\rm col}-f\|^2\le C(\alpha+p_H)$, where $\alpha$ is the largest
nonhelper type mass, with $C$ independent of the number of types for
the already fixed formula. The output is $m=\sin(2\theta)$.
[OpenAI (2026b), §3][q-classical].

### 9.3 Seeded synthesis

Cost and mixer gates, temporarily augmented by a
Gaussian longitudinal field, implement that finite calculation.
Helper paths return through the same sender to give the desired
aggregation. Refining sender types suppresses paths through different
senders; the proof must also control responses inside nested lower
calculations. Its partition estimate uses
$\rho^2=\sum_l p_l^2\le p_J\max_l p_l$, where the sender region $J$
is partitioned into parts of masses $p_l$ and $p_J=\sum_l p_l$.
The number of lower channels stays fixed during refinement.
Helpers of total mass $p_H$ and insertion
error $\eta$ give
$$
|\mathcal E(v)-\mathcal E(m)|\le2\eta+2\sqrt{p_H}.
$$
This is a theorem about a fixed surrounding circuit, not a uniform bound
over arbitrarily growing circuits. [OpenAI (2026b), §4][q-synthesis].

### 9.4 Seed removal

A further theorem approximates any fixed finite seeded
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
choosing sufficiently small $r$. [OpenAI (2026b), §5][q-seeds].

### 9.5 Transfer

Fix all approximations before taking the thermodynamic
limit. The result is one finite ordinary word $W$, independent of degree,
size and disorder. On the $(D+1)$-regular tree use
$C_D=D^{-1/2}\sum_{\{i,j\}\in E}Z_iZ_j$, counting each edge once.
For this fixed word, the source applies
$$
v_W=\lim_{D\to\infty}\frac{\sqrt D}{2}
 \langle +|W_D^*Z_iZ_jW_D|+\rangle.
$$
The cited theorem of Basso et al. uses the negative tree cost;
conjugation by $X$ on one bipartition reverses every edge term, fixes the
plus state and commutes with the mixer, giving the displayed positive-cost
convention. The [full preprint of Basso et al. (2022)](https://arxiv.org/html/2110.14206v3), Theorem 1 and
(2.3), (2.6), (6.1)–(6.3), supplies the exact-edition destination.
Its shorter proceedings edition states the theorem but refers to the
full preprint for the proof. [OpenAI (2026b), §2][q-foundations].

Identifying a strongly convergent rooted vector with that edge limit needs
an additional estimate. For the finite-degree root vector $f_D$,
let $\mathsf N$ count children whose subtree state differs from its
initial, or vacuum, state. Its expectation is
$\langle\mathsf N\rangle=\langle f_D,\mathsf N f_D\rangle$;
the occupation number counts excited child factors, not physical spins.
The source bounds the unscaled edge remainder by
$\langle\mathsf N\rangle/(D+1)$; multiplication by $\sqrt D/2$
still makes it vanish when the first occupation moment is uniformly
bounded. Ordinary root updates and the gate calculus supply this control
for the fixed word. Arbitrarily large and inverse angles are permitted.
Merge consecutive equal gate types and insert identities to write $W$ in
the alternating QAOA form. [OpenAI (2026b), §2][q-foundations].

### 9.6 Fixing the word before the thermodynamic limit

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
[OpenAI (2026b), §6][q-assembly].
<!-- /passage:qaoa -->

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
[Lopatto, arXiv:2607.11756v3, Theorem 1.1](https://arxiv.org/html/2607.11756v3)
gives $\operatorname{supp}\mu_{\beta_0}=[0,q]$ for $\beta_0>1$;
its smooth density below $q$ gives the regularity used on a fixed
$[0,T]$ with $0<T<q$.

The source derives $\mathbb E a(t,X_t)^2=1$ on $[0,q]$ and
$1-q\le\beta_0^{-1}$. The value estimate is
$$
\int_0^T\mathbb E a(t,X_t)\,dt
\ge P_*-\frac{1/4+\log2}{\beta_0}-(q-T).
$$
Choose first a sufficiently large finite $\beta_0$, then $T<q$ close
enough to $q$. This route obtains the existence and value of the
ground-state limit from the positive-temperature Parisi formula. With
$F_{n,\beta_0}=(n\beta_0)^{-1}\mathbb E\log\sum_\sigma e^{\beta_0H_n(\sigma)}$, use
$$
F_{n,\beta_0}-(\log2)/\beta_0\le n^{-1}\mathbb E\max H_n\le F_{n,\beta_0}.
$$
It does not invoke the zero-temperature companion
to justify that step. [OpenAI (2026b), Appendix A][q-positive].

The remaining limits have distinct tasks. At fixed
$\beta_0,T,\delta,L$, with $L\ge1$ and $L\delta\le T$, the degree limit $D\to\infty$ identifies the
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

The finite-step source comparison can be made precise.
[El Alaoui–Montanari–Sellke, arXiv:2111.06813v2](https://arxiv.org/abs/2111.06813v2),
Proposition 2.1 (p. 7), sums the adjacent-time term over
$\ell=2,\ldots,L$. Lemma 4.3, equation (4.6) (p. 14), replaces its
expectation by the coefficient at $r=\ell-1$, giving
$r=1,\ldots,L-1$. The printed sums in (4.5) (p. 13) and (4.18)
(p. 16) instead use $2,\ldots,L$. Also, the same-time display (2.21)
in Lemma 2.8 (p. 9) omits the factor $1/k$ retained in its proof and
Proposition 2.1. These local display discrepancies are visible in the
cited v2 original; Q uses the proposition and the reindexed sum, with
$k=D+1$, and explicitly supplies spatial Lipschitz bounds for both $a$
and the drift in its application. Boundedness on the fixed strip makes the two endpoint terms
$O(\delta)$, so the endpoint correction does not change the ensuing
continuum value. This comparison neither audits the whole message-passing
paper, repairs its general theorem statement, nor proves the quantum construction.

The missing factor can be checked on a $k$-regular tree with constant
messages $F_\ell=H_\ell=1$ at the first time: the same-time term is
$1/k$, while the printed (2.21) gives $1$. For the endpoint shift,
at two steps with $\delta=\varepsilon=1/4$, $b=0$ and a time-dependent
coefficient changing from $1$ to $-1$ at $t=3/8$, the scaled edge term
is $\delta$ whereas the printed (4.5) gives $-\delta$.
These are bounded checks of the displays, not counterexamples to the
general theorem. The source application's compact-strip spatial
Lipschitz bounds also supply the regularity used in the cited finite-step
lemma. [OpenAI (2026b), Appendix A][q-positive].

After clipping and bounded approximation, the result enters the same
synthesis and seed-removal route as the primary construction. Its source
dependencies and fixed-temperature choice of parameters remain separate
from the retained zero-temperature formal interfaces.
[OpenAI (2026b), Appendix A][q-positive].
<!-- /passage:alternative -->

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
Lean 4.34.1 and a pinned mathlib revision. The polynomial computation
in §4 was repeated with exact rational arithmetic. Its expansion matches
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

The original planned checks remain unrun, while a distinct historical
full-support Comparator attempt was unavailable before checker startup.
No successful source-bound research replay receipt
for either target accompanies this revision. Its transitive axiom
audit is not established by inspecting source names or Comparator
configuration. The recorded permitted axioms and checker settings describe
configuration, not an observed audit result. Successful tool receipts
concern their stated fixtures and must not be promoted to research-target
evidence.

This record reports no fresh QAOA/SK Lean build, Comparator run or complete
independent proof review. Detailed reading coverage, exact finite-check
results, preserved unsuccessful observations and the remaining obligations
are recorded in the companion source review. This remains an unreviewed draft.
<!-- /passage:verification -->

## References

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
