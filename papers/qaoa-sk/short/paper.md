# Full support and positive density in the zero-temperature SK model

*One lower bound, two consequences · A reconstruction of OpenAI's argument · 24 October 2026*

<!-- passage:abstract -->
**Abstract.** The Sherrington–Kirkpatrick (SK) model assigns a random energy to
each list of signs, called a spin configuration. The Parisi formula
expresses its limiting maximum energy per spin as a minimum over
nondecreasing functions. For this pair-interaction model with no external field, every integrable
minimiser has an increment measure with full support on $[0,1)$:
every interval of positive length receives positive mass. This measure also has
a smooth density, strictly positive on $(0,1)$. We reconstruct OpenAI's
argument for these two conclusions. A gap in the measure's support
would be an interval where the minimising function is constant.
The proof associates a curve with the minimiser. Minimality forces
this curve to equal time at the gap's endpoints. A quantitative lower
bound makes its derivative strictly convex on a positive constant interval,
producing an impossible area deficit; zero coefficients and endpoints
have separate arguments. Once all gaps are excluded, the same bound
passes through an approximation at a fixed time and forces the density
to be positive. Chen had already proved full support and smooth absolute
continuity. The contribution here is an account of the two uses of the
quantitative bound, with their analytic inputs and attribution retained.
<!-- /passage:abstract -->

<a id="model-and-result"></a>

## 1. The result and the mechanism

<!-- passage:model -->
A configuration of $n$ spins is a list of signs
$\sigma_1,\ldots,\sigma_n\in\{-1,1\}$. For each pair $i<j$, choose
an independent Gaussian weight $J_{ij}$ with mean zero and variance one;
these weights are called couplings. The
[Sherrington–Kirkpatrick optimization problem][SK] is to maximise
the energy
$$
H_n(\sigma)=n^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j,
\qquad \sigma\in\{-1,1\}^n.
$$
Write $P_*:=\lim_{n\to\infty}n^{-1}\mathbb E\max_\sigma H_n(\sigma)$
for the limiting optimum per spin. The Parisi formula expresses this
value as a minimum over nondecreasing functions (see [Auffinger and Chen
(2017), Theorem 1 and proof of Lemma 3][AC]). The parameter $t$ ranges
over nonnegative overlap scales: for two spin configurations
$\sigma,\tau$, their overlap $R=n^{-1}\sum_i\sigma_i\tau_i$
measures their agreement, with $R=1$ when they coincide and $R=-1$
when every sign is reversed. We explain why a minimising function
has no interval of constancy, and why the measure defined by its
increments has positive density in the interior.

This is the analytic part of one proof about the quantum approximate
optimization algorithm (QAOA), which prepares spin configurations by a
sequence of quantum operations. For each desired accuracy, that proof
chooses one finite sequence whose expected energy per spin approaches
$P_*$ to that accuracy as $n\to\infty$.
The absence of intervals on which the minimising function is constant
supplies identities for expectations along a Brownian-driven random
process. These identities construct a near-optimal classical input for
the quantum operations. Positive density is a further conclusion.
Section 5 explains this connection
and points to the separate circuit argument. The proofs here use
Itô calculus and standard martingale convergence, with the required
estimates for the Parisi partial differential equation (PDE) stated where they enter.

The model has only pair interactions (pure SK) and no one-spin
bias term (zero external field). Its covariance function is
$\xi(t)=t^2/2$: for configurations with overlap $R$,
$\mathbb E[H_n(\sigma)H_n(\tau)]=nR^2/2-1/2$.
Adding the same independent centred Gaussian of variance $1/2$ to
every configuration's energy gives covariance $n\xi(R)$ and leaves
the expected maximum unchanged. This matches the convention in the
Parisi formula.

Let $\mathcal U$ consist of the nonnegative, nondecreasing,
right-continuous functions $\gamma:[0,1)\to[0,\infty)$ satisfying
$\int_0^1\gamma(t)\,dt<\infty$. Define the locally finite Stieltjes
measure by
$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\leq t<1.
$$
Thus $\mu_\gamma((s,t])=\gamma(t)-\gamma(s)$: the measure records
the increments of $\gamma$. A point mass (atom) of size $\gamma(0)$
is allowed at zero, and the total mass need not be finite or equal
to one. The support consists of points whose every neighbourhood
in $[0,1)$ has positive mass. A support gap is a relatively open interval of positive length
with zero mass, on which $\gamma$ is constant. When the measure has
a density $\rho$, its mass on an interval is the integral of $\rho$
there. All support statements are relative to $[0,1)$.

The Parisi functional $\mathcal P(\gamma)$ is defined using an
auxiliary value function $\Phi_\gamma(t,x)$, where $x\in\mathbb R$
is a spatial variable and $t$ is the overlap parameter, treated as
time in the equation. Write $\Phi=\Phi_\gamma$ and use subscripts
for partial derivatives. The backward equation, terminal condition
and functional are
$$
\Phi_t=-\tfrac12\bigl(\Phi_{xx}+\gamma(t)\Phi_x^2\bigr),
\qquad \Phi(1,x)=|x|,
\qquad
\mathcal P(\gamma)=\Phi_\gamma(0,0)-\tfrac12\int_0^1t\gamma(t)\,dt.
$$
For an integrable coefficient, the solution is interpreted by
approximation from bounded monotone coefficients. The exact control
definition and stability theorem are [OpenAI (2026a), §1 and
Lemmas 2.1–2.2][FS]. To turn minimality of $\mathcal P$ into a
condition on $\gamma$, we use a random process whose gradient moment
measures the first-order cost of changing $\gamma$. Write $u=\Phi_x$ for the spatial gradient
and $a=\Phi_{xx}$ for its spatial derivative. Let $B$ be standard
Brownian motion and define the diffusion $X$ and the moment $q$ by
$$
dX_t=\gamma(t)u(t,X_t)\,dt+dB_t,\qquad X_0=0,
\qquad q(t)=\mathbb E[u(t,X_t)^2].
$$
Thus $q$ is the expected square of the gradient along the diffusion.
The diffusion exists and is unique for the fixed Brownian motion.
We use stochastic calculus on
compact time intervals below one; the required analytic inputs are
stated in §2.
<!-- /passage:model -->

<!-- passage:main-result -->
[Chen (2026), Theorem 1.3][Chen] had already proved full support and
smooth absolute continuity. The following formulation and quantitative
proof are from OpenAI; the positive-density consequence is treated
separately in §4.

**Theorem 1 (full support; [OpenAI (2026a), Theorem 1.1][FS]).**
If $\gamma\in\mathcal U$ minimises $\mathcal P$, then
$$
\operatorname{supp}\mu_\gamma=[0,1),\qquad
\gamma(t_2)>\gamma(t_1)\quad(0\leq t_1<t_2<1).
$$
For every associated diffusion and every $0\leq t<1$,
$$
q(t)=t,\qquad \mathbb E[a(t,X_t)^2]=1.
$$

Its Stieltjes measure has a smooth density, strictly positive at every
interior time; Corollary 3 gives the precise stronger statement.
Existence of a minimiser is a separate input from
[Auffinger and Chen (2017), Theorem 1 and the proof of Lemma 3][AC].
Integrability allows $\gamma$ to grow near one. Zero field gives
$u(0,0)=0$, and $\xi''=1$ is used in the curvature calculation;
the theorem here does not extend these hypotheses to nonzero field
or a general mixed-spin covariance.

The proof compares two demands on a hypothetical gap. Minimality
forces $q$ to agree with time at its endpoints, with endpoint slopes
at most one. On a positive constant interval a quantitative estimate
makes $q'$ strictly convex, so its integral is smaller than the
interval's length. This contradicts the required change in $q$.
After excluding all gaps, the identity $q'=1$ supplies the equation
from which the same estimate will force $\gamma'>0$.

The support conclusion has a history distinct from this proof.
[Auffinger, Chen and Zeng (2020), Theorem 1][ACZ] proved infinite
support, which can still have gaps: consider
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$, where $\delta_x$ is unit
mass at the point $x$.
We follow OpenAI's quantitative argument and credit its antecedents
at the steps where they enter.
<!-- /passage:main-result -->

<a id="contact"></a>

## 2. Minimality gives contact; curvature excludes gaps

<!-- passage:contact -->
For an admissible coefficient, $\Phi$ is even, convex and one-Lipschitz
in space. Its positive-order spatial derivatives are bounded and
continuous on each strip $[0,T]\times\mathbb R$, $T<1$; the PDE
holds almost everywhere in time. The compact-strip approximation
theorem justifies the following Itô calculations even when $\gamma$
has jumps (see [OpenAI (2026a), Lemmas 2.1–2.2][FS]). The control method
has antecedents in [Jagannath and Tobasco (2016)][JT] at positive
temperature and [Chen, Handschy and Lerman (2018), Proposition 2
and Theorem 5][CHL] at zero temperature.

Fix a minimiser. Itô's formula cancels the drift of $u(t,X_t)$:
$$
du(t,X_t)=a(t,X_t)\,dB_t,
\qquad q(0)=0,\qquad q'(t)=\mathbb E[a(t,X_t)^2].
$$
In particular $q'$ is continuous across coefficient jumps. Minimality
means that every allowed one-sided change has nonnegative first-order
cost. The one-sided variation formula gives the rate of change of the functional
when $\gamma$ is replaced by $\gamma+\varepsilon\eta$ as
$\varepsilon\downarrow0$:
$$
D_+\mathcal P(\gamma)[\eta]
=\tfrac12\int_0^1\eta(t)(q(t)-t)\,dt,                 \tag{1}
$$
for every integrable direction $\eta$ for which
$\gamma+\varepsilon\eta\in\mathcal U$ for all sufficiently small
$\varepsilon\geq0$ (see [OpenAI (2026a), Lemma 6.1][FS]). Earlier
zero-temperature variation and support identities appear in
[Chen, Handschy and Lerman (2018), Propositions 3–4][CHL].

Adding an atom at $s$ changes the cumulative function by
$\eta=\mathbf1_{[s,1)}$. Thus
$$
G(s):=\int_s^1(q(t)-t)\,dt\geq0.
$$
Here $G(s)/2$ is the first-order cost of the added atom. Conversely,
let $\nu$ be the restriction of $\mu_\gamma$ to a compact
$K\subset[0,1)$. Removing a fraction of this mass is feasible, so
$$
0\leq D_+\mathcal P(\gamma)[-\nu([0,\cdot])]
=-\tfrac12\int_K G(s)\,d\mu_\gamma(s).
$$
The change of integration order is justified by $|q-t|\leq1$ and
$\mu_\gamma(K)<\infty$. Since $G\geq0$, it vanishes almost
everywhere for $\mu_\gamma$, and continuity makes it vanish on
$S=\operatorname{supp}\mu_\gamma$. This removes diffuse mass as
well as atoms; no density or probability constraint is assumed.

At a support point $s>0$, $G$ has a minimum. Hence
$$
G'(s)=s-q(s)=0,\qquad G''(s)=1-q'(s)\geq0,
\quad\text{so}\quad q(s)=s,\quad q'(s)\leq1.       \tag{2}
$$
If $0\in S$, then $G(0)=q(0)=0$ and
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$; nonnegativity gives the
same slope bound at zero. These are the contact conditions of
[OpenAI (2026a), Lemma 6.2][FS].
<!-- /passage:contact -->

<a id="gap-elimination"></a>

<!-- passage:gap-proof -->
**Lemma 2 (constant-interval curvature; [OpenAI (2026a),
Proposition 5.1][FS]).** Let $\gamma\in\mathcal U$, with its
associated diffusion and moment $q$. If $\gamma=c$ on an open
interval $I\subset(0,1)$, called a plateau, then for $t\in I$
$$
q'''(t)\geq\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\quad\text{if }c>0.                               \tag{3}
$$
If $c=0$, then $q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$.

Minimality is not a hypothesis of this lemma. Its integrated
coercive estimate is explained in §3. We first show what it buys.

Suppose $(\ell,r)$ is a support gap with endpoints in $S$ and $r<1$.
The coefficient is constant there. If its value is positive, strict
convexity of $q'$ and (2) give
$$
q'(t)<\frac{r-t}{r-\ell}q'(\ell)
       +\frac{t-\ell}{r-\ell}q'(r)\leq1
\qquad(\ell<t<r).
$$
Integrating contradicts $q(r)-q(\ell)=r-\ell$. The geometric
obstruction is an area deficit under $q'$. If the constant is zero,
strict increase gives $q'(t)<q'(r)\leq1$ and the same contradiction.
An initial gap $[0,r)$ with $0\notin S$, $r\in S$ and $r<1$ has
coefficient zero and no atom at zero. Use $q(0)=0$ and contact at $r$, without assuming
contact at zero.

A terminal gap cannot use contact at one, which is outside the
support domain. On a constant interval ending at one,
[OpenAI (2026a), Lemma 6.3][FS] instead proves
$$
1-q(t)\geq C\sqrt{1-t}
$$
for some $C>0$ and $t$ sufficiently close to one. Evolving the
terminal condition $|x|$ backwards smooths its corner at zero.
On the assumed plateau, this keeps its gradient $u$ uniformly away
from $\pm1$ in a window of width
$\sqrt{1-t}$ around zero. The diffusion density has a uniform
positive lower bound on that window, under the assumed plateau;
integrating $1-u^2$ gives the estimate. Thus
$q(t)-t\leq(1-t)-C\sqrt{1-t}<0$ near one, making $G(s)<0$
there. This contradicts minimality and also excludes empty support. The
zero-coefficient heat argument and late-step variation already appear
in [Chen, Handschy and Lerman (2018), Theorem 6 and its proof][CHL].
Terminal-plateau exclusion was already recorded by
[Auffinger, Chen and Zeng (2020), Remark 7][ACZ].

These cases exhaust the complement of the relatively closed set $S$.
Consequently $S=[0,1)$, contact gives $q(t)=t$, and differentiation
gives $\mathbb E a^2=1$, including the right-hand value at zero.
Moreover,
$\gamma(t_2)-\gamma(t_1)=\mu_\gamma((t_1,t_2])>0$.
This proves Theorem 1 using the stated analytic inputs.
<!-- /passage:gap-proof -->

<a id="curvature"></a>

## 3. The estimate behind strict curvature

<!-- passage:curvature -->
On a plateau with $\gamma=c>0$, put $r=c\Phi_x$, $v=r_x$,
$w=r_{xx}$ and $z=r_{xxx}$. In expectations below, these functions
are evaluated at $(t,X_t)$. Along the diffusion, the drift and diffusion pairs
for $r,v,w$ are $(0,v)$, $(-v^2,w)$ and $(-3vw,z)$.
Starting with $c^2q'=\mathbb E v^2$, Itô's formula gives
$$
c^2q''=\mathbb E[w^2-2v^3],\qquad
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].                 \tag{4}
$$
For example, the drifts of $w^2$ and $v^3$ are
$z^2-6vw^2$ and $3vw^2-3v^4$, respectively. The negative
mixed term is the obstacle. Convexity, which gives $v\geq0$,
does not control it.

The required estimate is an inequality after integration against
the actual diffusion density. We first prove it for finite-step
coefficients: on each constant step the equation can be transformed
into a heat equation, making the needed shape restrictions accessible.
We then pass to general integrable coefficients by approximation.
Begin with a positive nondecreasing
finite-step coefficient $\gamma_{\rm step}$: a function constant
on each interval of a finite partition. Replace the terminal value
$|x|$ by the smooth approximation $M^{-1}\log(2\cosh Mx)$, with
$M\geq\|\gamma_{\rm step}\|_\infty$.
At a positive time on a step of height $c$, let $f$ be the probability
density of $X_t$. It factors as $f=e^{c\Phi}g$,
where $g$ solves the forward heat equation. For $s=-\partial_x\log g$,
the source proves joint shape restrictions: on $x>0$, $r$ and $s$
are increasing and concave, $w/(2r)+v\leq0$ is nondecreasing,
and $s/r$ is nondecreasing. The ratios extend through zero.
These are analytic conclusions of [OpenAI (2026a), §3][FS],
not consequences of the polynomial in (4).

The factorisation of the density gives $f_x/f=r-s$. For a suitable
expression $F$ in the shape quantities, define
$$
\mathcal W(F)=r\partial_xF+(v+r^2-rs)F.
$$
Then $f\mathcal W(F)=\partial_x(rfF)$, so the source's tail estimates
give $\mathbb E_f\mathcal W(F)=0$, where $\mathbb E_f$ denotes
integration against $f(x)\,dx$. The point is to choose $F$ so
that subtracting this zero-mean correction from
$z^2-12vw^2+6v^4$ permits a decomposition into a square and terms
nonnegative under the joint shape restrictions, with remainder at
least $10^{-3}v^4$. The correction changes the integrand while
preserving its expectation. The conclusion is
$$
\int_{\mathbb R}(z^2-12vw^2+6v^4)f\,dx
\geq\frac1{1000}\int_{\mathbb R}v^4f\,dx.           \tag{5}
$$
The exact identity is [OpenAI (2026a), Lemma 4.1][FS]; the
shape hypotheses, correction and boundary justification are assembled
in its Proposition 4.2. The long reasoning record, §4.4,
“How the signs make a correction with zero expectation useful”,
defines every auxiliary variable and reproduces the certificate.
Thus (5) is a cited analytic input here, with its mechanism exposed;
it is not a pointwise assertion for arbitrary $v,w,z$.

To obtain Lemma 2 for an integrable coefficient, choose positive
monotone step approximations retaining the plateau near a fixed
interior time, and send the terminal-smoothing parameter to infinity.
Spatial derivatives through order four converge uniformly on a fixed
strip below one, and the diffusions driven by the same Brownian
motion converge
(see [OpenAI (2026a), Lemmas 2.1–2.2 and Proposition 5.1][FS]). Only
$v,w,z$ remain in (5), so no convergence theorem for the auxiliary
logarithmic derivative $s$ is needed. Dividing by $c^2$ gives (3); strictness follows from
$\Phi_{xx}>0$ on the plateau (see [OpenAI (2026a), Lemma 2.3][FS]). The zero plateau has the separate
heat identity in Lemma 2. Its strictness uses a positive diffusion
density and the fact that $\Phi_{xxx}$ cannot vanish identically:
an even quadratic profile would contradict the one-Lipschitz bound
and $|x|+O(1)$ growth.

The exponential change of variables that converts each constant-step
equation to a heat equation (the Cole–Hopf representation), together
with the rules joining successive steps, has antecedents in [Lopatto (2026),
Propositions 3.6, 7.1 and 9.1][Lopatto] and [Chen (2026), §§3–4][Chen].
OpenAI's estimate also uses the joint restriction
$r\,\partial_x(s/r)\geq0$, beyond separate monotonicity and concavity.
Chen's Proposition 4.2 proves the
crossing implication $q''(t)=0\Rightarrow q'''(t)>0$ on a
hypothetical positive gap of the minimiser. In contrast, (3) is
quantitative and holds throughout every positive plateau of any
admissible coefficient. Chen's Appendix C distinguishes earlier
shared estimates from the parallel crossing proofs.
<!-- /passage:curvature -->

<a id="positive-density"></a>

## 4. A second use: the density cannot vanish inside the interval

<!-- passage:density-consequence -->
Full support does not force pointwise positive density. For instance,
$\gamma(t)=\int_0^t(s-\tfrac12)^2\,ds$ has full Stieltjes
support but $\gamma'(\tfrac12)=0$. The quantitative remainder
in (5) rules this out for a minimiser.

**Corollary 3 (smooth positive density; [OpenAI (2026a),
Corollary 6.4][FS]).** Under the hypotheses of Theorem 1,
$\gamma(0)=0$ and $\gamma\in C^\infty([0,1))$, with derivatives
at zero taken from the right. Its Stieltjes measure is
$\mu_\gamma(dt)=\gamma'(t)\,dt$, and
$$
2\gamma'(t)\mathbb E[a(t,X_t)^3]
\geq\frac{\gamma(t)^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(0<t<1).                                    \tag{6}
$$
Only nonnegativity of the density at zero is asserted.

Write $b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$; all spatial factors
in expectations below are evaluated at $(t,X_t)$. Since
$da=-\gamma a^2\,dt+b\,dB$, Itô's formula applied to $a^2$ gives, for almost every $t$,
$0=\frac{d}{dt}\mathbb E a^2=\mathbb E b^2-2\gamma\mathbb E a^3$.
Here the left side vanishes because full support gives $\mathbb E a^2=1$.
Solving for the coefficient yields
$$
\gamma(t)=\frac{\mathbb E b^2}{2\mathbb E a^3}.      \tag{7}
$$
Initially (7) holds almost everywhere. Its denominator is at least
two, because $a\geq0$ and
$\mathbb E a^3\geq(\mathbb E a^2)^{3/2}=1$.
The moments are continuous; right continuity of $\gamma$ extends
(7) to every time and proves continuity of $\gamma$. Evenness
gives $b(0,0)=0$, hence $\gamma(0)=0$.

For smoothness, consider expectations of polynomials in finitely
many spatial derivatives of $\Phi$; these are the polynomial moments.
Apply Itô's formula to this family of moments at once. The derivative of each
moment is another such moment plus $\gamma$ times such a moment.
Continuity makes these moments $C^1$; (7) then makes $\gamma$
$C^1$. Repeating proves smoothness without presupposing time
derivatives of the coefficient. This is the quotient-and-moment
argument of [Chen (2026), Proposition 4.6 and Appendix B.6][Chen],
using the polynomial-moment method of [Auffinger and Chen (2015),
Lemma 2 and the proof of Theorem 2(ii)][AC-properties].

Now the two differentiated moments are
$$
\frac{d}{dt}\mathbb E b^2=\mathbb E[d^2-6\gamma ab^2],
\qquad
\frac{d}{dt}\mathbb E a^3=\mathbb E[3ab^2-3\gamma a^4].
$$
Differentiating $\mathbb E b^2=2\gamma\mathbb E a^3$ gives
$$
2\gamma'\mathbb E a^3
=\mathbb E[d^2-12\gamma ab^2+6\gamma^2a^4].          \tag{8}
$$
The expression from the plateau calculation has returned. The
minimiser is not constant on an interval, so applying the plateau
lemma directly would be invalid. Here is the needed transfer.

Fix $t\in(0,1)$ and $c=\gamma(t)>0$. For
$0<\delta<\min(t,1-t)$ define
$$
\gamma_\delta(s)=
\begin{cases}
c,&t-\delta\leq s<t+\delta,\\
\gamma(s),&\text{otherwise}.
\end{cases}
$$
Both joins preserve monotonicity, and this remains an admissible
coefficient. Moreover,
$$
\|\gamma_\delta-\gamma\|_1
\leq2\delta\,[\gamma(t+\delta)-\gamma(t-\delta)]
\longrightarrow0.
$$
Use a subscript $\delta$ for its value-function derivatives and
diffusion. Lemma 2 and (4), already extended to integrable
coefficients, give at the fixed time $t$
$$
\mathbb E[d_\delta^2-12c\,a_\delta b_\delta^2
                         +6c^2a_\delta^4]
\geq\frac{c^2}{1000}\mathbb E[a_\delta^4].           \tag{9}
$$
Choose a single $T$ with $t<T<1$. Compact-strip derivative
stability and convergence of the diffusions driven by the same
Brownian motion pass each
spatial moment in (9) to its counterpart for $\gamma$; the
estimates do not depend on the plateau width
(see [OpenAI (2026a), Lemmas 2.1–2.2 and Corollary 6.4][FS]). Combining
the limiting inequality with (8) proves (6). Strictness follows
from $c>0$ and $\mathbb E a^4\geq(\mathbb E a^2)^2=1$.
In particular, Cauchy–Schwarz gives
$\mathbb E a^3\leq\sqrt{\mathbb E a^4}\leq\mathbb E a^4$,
so the same inequality implies
$\gamma'(t)\geq\gamma(t)^2/2000$ for $0<t<1$.

We have passed spatial moments, not the time derivatives
$q_\delta'''$. Indeed the limiting minimiser has $q(t)=t$ and
$q'''=0$; the coefficient derivative in (8) is exactly what the
constant-interval formula omits. The long record, §§5.1–5.2,
retains the full moment bootstrap and fixed-time transfer.
<!-- /passage:density-consequence -->

<a id="value-and-qaoa"></a>

## 5. The scalar consequence and a separate circuit theorem

<!-- passage:scalar-value -->
Full support also recovers the scalar value $P_*$ defined in §1.
This maximum-energy limit is called the ground-state value in the
sign convention used here. The argument does not use the density
corollary. For a minimiser,
the ground-state Parisi formula gives $P_*=\mathcal P(\gamma)$
(see [Auffinger and Chen (2017), Theorem 1][AC]).

The bounded martingale $M_t=u(t,X_t)=\int_0^t a\,dB$ has
$\mathbb E M_t^2=t$. It converges almost surely and in $L^2$ to a variable $U$.
Since $|M_t|\leq1$ and $\mathbb E M_t^2\to1$, we have
$|U|\leq1$ and $\mathbb E U^2=1$, hence $|U|=1$ almost surely. The bound $|\gamma u|\leq\gamma$
gives $X_t\to X_1$ almost surely and in $L^2$. The terminal estimate
$$
0\leq\Phi_\gamma(t,x)-|x|
\leq\sqrt{2(1-t)/\pi}+\tfrac12\int_t^1\gamma(s)\,ds
$$
and the convex difference-quotient bounds force
$u(t,X_t)\to\operatorname{sign}(X_1)$ on $\{X_1\ne0\}$.
Thus $UX_1=|X_1|$, also when $X_1=0$.
Itô's formula for $\Phi(t,X_t)$ and passage to time one yield
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt$.
Multiplying $X_1=B_1+\int_0^1\gamma M_t\,dt$ by $U$ then
cancels the penalty, because $\mathbb E[UM_t]=t$:
$$
P_*=\mathbb E[UB_1]
   =\int_0^1\mathbb E[a(t,X_t)]\,dt.                \tag{10}
$$
Fubini uses $|UM_t|\leq1$ and $\gamma\in L^1$; the final
covariance identity for stochastic integrals uses $\mathbb E\int_0^1a^2\,dt=1$.
This first-moment integral is different from $\mathbb E a^2=1$.
The argument is [OpenAI (2026a), Corollary 7.1][FS]; the long
record, §6, “Recovering the value from a martingale”, supplies
the endpoint details. The gradient martingale and moment identities
have antecedents in [Montanari, preprint v2, Lemmas 3.2–3.4][Montanari],
under its positive-temperature support assumption. The zero-temperature
martingale and value calculations are in [El Alaoui, Montanari and
Sellke, preprint v1, Lemmas 6.5 and 6.13][EAMS]. These are method
antecedents, distinct from the finite-Gaussian construction below.

Here is the role of full support in the circuit proof. The identity
$\mathbb E a^2=1$ permits normalised Gaussian increments weighted by
$a=\Phi_{xx}$, while (10) identifies their target value. At fixed
$T<1$, discretising the diffusion gives a terminal gradient depending
on finitely many Gaussians. This gradient lies in $[-1,1]$, whereas
a spin must be $-1$ or $1$. Rounding with an independent random
variable produces such a sign-valued (Boolean) output while preserving
the gradient as its conditional mean, and therefore preserving its
correlations with the preceding Gaussian variables. A specified sum of products of its correlations with the driving
Gaussians and the normalised increments converges to $\int_0^T\mathbb E a(t,X_t)\,dt$
as the mesh is refined; taking $T\uparrow1$ then brings its value
to $P_*$. This is the additional finite construction of
[OpenAI (2026a), Proposition 7.2][FS], reconstructed in the long
record, §7, “A finite Gaussian spin and its adjacent correlations”.
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
There is also a separate circuit theorem. QAOA begins with equal
quantum amplitudes on all spin configurations. Each layer alternates
a phase change determined by $H_n$ (cost evolution) and single-spin
rotations that mix the signs (transverse-field mixing). The depth is
the number of layers; their angles specify the strengths of these
operations (see [Farhi, Goldstone and Gutmann (2014)][FGG]). For every
$\varepsilon>0$, [OpenAI (2026b), Theorem 1.1][Q] constructs a
finite depth and deterministic angles, independent of system size
$n$ and the couplings $J_{ij}$, whose limiting expected energy per
spin is at least
$P_*-\varepsilon$. The angles and depth may depend on $\varepsilon$;
the limit $n\to\infty$ is taken with them fixed. Fixed-parameter
limits are due to [Farhi, Goldstone, Gutmann and Zhou (2022)][FGGZ],
whose arbitrary-fixed-angle theorem uses this Hamiltonian and gate
convention directly. The eventual-optimality conclusion was conjectured by
[Basso et al. (2022), §7, equation (7.2)][BFMVZ]. The circuit
argument must preserve that correlation value, not just reproduce
a scalar number. It realises the finite Gaussian construction in
a recursive space organised by a root and its descendants, approximates
the bounded output by quantum gates, removes auxiliary random inputs,
and transfers the resulting single finite gate sequence to SK. These are additional theorems, reconstructed in
the long record, §9, “From the scalar formula to one ordinary QAOA
word”, from [OpenAI (2026b), §§2–6 and Appendix A][Q]. Neither
positive density nor (10) alone proves them. The selected construction
gives no quantitative depth bound, finite-size rate or efficient
angle-selection procedure.
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## 6. Source and formal scope

<!-- passage:evidence-scope -->
This AI-assisted article reconstructs the cited results; it asserts
no new theorem. The original analytic proofs are in OpenAI's
manuscripts, with the prior mathematical sources identified above.
The central imported input is the integrated estimate (5), including
its analytic shape and approximation hypotheses.

Lean is a proof assistant: it checks proofs written in its formal
language. For the support result, the linked files contain the
[proof implementation][support-lean],
[theorem specification (challenge)][support-challenge] and
[comparison-tool settings][support-config]. These files
concern measure and diffusion existence, full support, strict increase
and both moment identities, conditional on a minimiser. The
[scalar implementation][value-lean], [challenge][value-challenge]
and [configuration][value-config] select a separate formal interface:
its scalar and finite-Gaussian clauses assume a minimiser and an
associated diffusion, while its ground-state/Parisi equality assumes
only the minimiser. Their formal models have not been transported
into one another in this record. Neither selected statement includes
Corollary 3 or QAOA convergence.

The formal developments use Lean and its mathematical library, mathlib;
we credit the system description by [de Moura and Ullrich (2021)][Lean4]
and [The mathlib Community (2020)][mathlib]. These scholarly references
describe the tools; the accompanying source record identifies the exact
versions used for the selected developments.

Source-integrity checks passed. After an earlier unavailable Comparator
startup, later invocations built and exported the admitted full-support
and scalar-value challenges. Both stopped during the implementing solution
build because imported compiled modules were missing. No successful
replay of the corrected build configuration is recorded. Challenge export,
tool-fixture success and the exact polynomial calculation establish no
research-target acceptance, transitive axiom audit or independent human
review. Exact versions, the failed attempts and remaining obligations are
retained in the companion source review.
<!-- /passage:evidence-scope -->

## References
- de Moura, L. and Ullrich, S. (2021). “The Lean 4 Theorem Prover and
  Programming Language (System Description).” *CADE 28*.
  [System description][Lean4].
- The mathlib Community (2020). “The Lean Mathematical Library.”
  *Certified Programs and Proofs (CPP '20)*. [Library description][mathlib].
- OpenAI (2026a). *Full support of the zero-temperature Sherrington–Kirkpatrick
  order parameter*. 27 September 2026. [Manuscript][FS], fixed revision.
  Theorem 1.1; §§2–6; Corollaries 6.4 and 7.1; Proposition 7.2.
- OpenAI (2026b). *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*. 25 September 2026. [Manuscript][Q], fixed
  revision. Theorem 1.1; §§2–6 and Appendix A.
- Auffinger, A. and Chen, W.-K. (2017). “Parisi formula for the ground
  state energy in the mixed $p$-spin model.” *Annals of Probability*
  **45**, 4617–4631. [Preprint v2][AC]: Theorem 1 and proof of Lemma 3.
- Auffinger, A., Chen, W.-K. and Zeng, Q. (2020). “The SK model is
  infinite step replica symmetry breaking at zero temperature.”
  *Communications on Pure and Applied Mathematics* **73**, 921–943.
  [Preprint v2][ACZ]: Theorem 1 and Remark 7.
- Chen, H.-B. (2026). *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][Chen],
  20 July 2026. Theorem 1.3; Propositions 4.2 and 4.6; Appendices B.6 and C.
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv version 3][Lopatto], revised
  16 July 2026. Propositions 3.6, 7.1 and 9.1; related Cole–Hopf, density
  and crossing arguments.
- Sherrington, D. and Kirkpatrick, S. (1975). “Solvable Model of a Spin-Glass.”
  *Physical Review Letters* **35**, 1792–1796. [Original model][SK].
- Jagannath, A. and Tobasco, I. (2016). “A dynamic programming approach
  to the Parisi functional.” *Proceedings of the AMS* **144**, 3135–3150.
  [Preprint v4][JT]. Positive-temperature control methods.
- Chen, W.-K., Handschy, M. and Lerman, G. (2018). “On the energy
  landscape of the mixed even $p$-spin model.” *Probability Theory and
  Related Fields* **171**, 53–95. [Preprint v4][CHL]: Proposition 2,
  Theorem 5, Lemma 3 and Propositions 3–4.
- Auffinger, A. and Chen, W.-K. (2015). “On properties of Parisi
  measures.” *Probability Theory and Related Fields* **161**, 817–850.
  [Preprint v1][AC-properties]: Lemma 2 and proof of Theorem 2(ii).
- Montanari, A. (2025). “Optimization of the Sherrington–Kirkpatrick
  Hamiltonian.” *SIAM Journal on Computing* **54**, FOCS19-1–FOCS19-38.
  [Preprint v2, 2019][Montanari]: §§2–3.
- El Alaoui, A., Montanari, A. and Sellke, M. (2021). “Optimization of
  mean-field spin glasses.” *Annals of Probability* **49**, 2922–2960.
  [Preprint v1][EAMS]: §§5–6.
- Farhi, E., Goldstone, J. and Gutmann, S. (2014). *A Quantum Approximate
  Optimization Algorithm*. [Preprint v1][FGG]. Algorithm definition;
  §VI concerns the fixed-instance depth limit.
- Farhi, E., Goldstone, J., Gutmann, S. and Zhou, L. (2022). “The Quantum
  Approximate Optimization Algorithm and the Sherrington–Kirkpatrick
  Model at Infinite Size.” *Quantum* **6**, 759. [Preprint v4][FGGZ].
- Basso, J., Farhi, E., Marwaha, K., Villalonga, B. and Zhou, L. (2022).
  “The Quantum Approximate Optimization Algorithm at High Depth for
  MaxCut on Large-Girth Regular Graphs and the Sherrington–Kirkpatrick
  Model.” *TQC 2022*, 7:1–7:21. [Full preprint v3][BFMVZ]: transfer
  theorem and §7, equation (7.2); the full preprint has separate numbering.


[Lean4]: https://doi.org/10.1007/978-3-030-79876-5_37
[mathlib]: https://doi.org/10.1145/3372885.3373824
[FS]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
[Q]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf
[AC]: https://arxiv.org/abs/1606.05335v2
[ACZ]: https://arxiv.org/abs/1703.06872v2
[Chen]: https://arxiv.org/abs/2607.18032v1
[Lopatto]: https://arxiv.org/abs/2607.11756v3
[support-lean]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35
[support-challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92
[support-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.json
[value-lean]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16
[value-challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L163
[value-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.json

[SK]: https://doi.org/10.1103/PhysRevLett.35.1792
[JT]: https://arxiv.org/abs/1502.04398v4
[CHL]: https://arxiv.org/abs/1609.04368v4
[AC-properties]: https://arxiv.org/abs/1303.3573v1
[Montanari]: https://arxiv.org/abs/1812.10897v2
[EAMS]: https://arxiv.org/abs/2001.00904v1
[FGG]: https://arxiv.org/abs/1411.4028v1
[FGGZ]: https://arxiv.org/abs/1910.08187v4
[BFMVZ]: https://arxiv.org/abs/2110.14206v3
