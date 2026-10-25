# Full support and positive density in the zero-temperature SK model

*One lower bound, two consequences · A reconstruction of OpenAI's argument · 25 October 2026*

<!-- passage:abstract -->
**Abstract.** Every integrable minimiser of the zero-temperature Parisi
functional for the pure, zero-field Sherrington–Kirkpatrick model has
full Stieltjes support on $[0,1)$ and a smooth density that is strictly
positive on $(0,1)$. We reconstruct two uses of the quantitative
estimate in OpenAI's proof. On a positive interval of constancy, the
estimate makes the derivative of a gradient moment strictly convex;
variational contact at the endpoints then forces an impossible area
deficit. A separate boundary estimate excludes terminal intervals.
After full support gives the moment identities and smoothness, a local
constant replacement transfers the same inequality to the minimiser
at a fixed time and forces its density to be positive. Chen previously
proved full support and smooth nonnegative density. The contribution
of this account is to explain the quantitative argument, its second
use and its relation to the separate quantum approximate optimization
algorithm (QAOA) construction, while identifying
the analytic estimates imported from the original sources.
<!-- /passage:abstract -->

<a id="model-and-result"></a>

## 1. The result and the mechanism

<!-- passage:model -->
For independent standard Gaussian couplings $J_{ij}$, the pure,
zero-field [Sherrington–Kirkpatrick (SK) Hamiltonian][SK] is
$$
H_n(\sigma)=n^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j,
\qquad \sigma\in\{-1,1\}^n.
$$
A spin configuration $\sigma$ assigns one sign to each of the $n$ sites.
The zero-temperature problem concerns the limiting maximum energy per
spin,
$$
P_*:=\lim_{n\to\infty}n^{-1}\mathbb E\max_\sigma H_n(\sigma).
$$
The Parisi formula expresses $P_*$ as a minimum over nondecreasing
functions. Our subject is the structure of a minimiser: its increments
charge every interval of overlap scales below one, and in fact have
strictly positive density at each interior scale. The proof uses one
quantitative bound twice, first to exclude constant intervals and then,
after an approximation, to prove pointwise positivity.

For two configurations, their overlap is
$R(\sigma,\tau)=n^{-1}\sum_i\sigma_i\tau_i$. We use the covariance
convention $\xi(t)=t^2/2$, so $\xi''=1$. The finite Hamiltonian has
covariance $nR^2/2-1/2$; adding one independent centred Gaussian of
variance $1/2$ to every configuration's energy gives covariance
$n\xi(R)$ and leaves the expected maximum unchanged. This is the
normalisation of the ground-state Parisi formula of
[Auffinger and Chen (2017), Theorem 1][AC]. There are no higher-order
interactions and no external field.

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
The discrepancy $q(t)-t$ enters the first variation of $\mathcal P$;
minimality will force $q(t)=t$ on the support of $\mu_\gamma$.
The diffusion exists uniquely for the fixed Brownian motion. All
stochastic calculations below take place on compact time intervals
ending before one, unless an endpoint limit is justified explicitly.
<!-- /passage:model -->

<!-- passage:main-result -->
[Auffinger, Chen and Zeng (2020), Theorem 1][ACZ] proved infinite
support. This need not be full support: the measure
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$ has infinitely many atoms
and many gaps. [Chen (2026), Theorem 1.3][Chen] subsequently proved
full support and smooth nonnegative density. We follow OpenAI's
quantitative proof of the support conclusion and its further
strict-positivity result. The feature used twice is a lower bound
valid throughout every positive constant interval of an admissible
coefficient, without a minimising assumption.

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

The support identities also supply the normalisation used in a proof
of asymptotic optimality for the quantum approximate optimization
algorithm (QAOA). Section 5 states that separate theorem and the finite
Gaussian correlation quantity it uses. The density conclusion is not
needed for that construction. We assume Itô calculus and martingale
convergence; the nontrivial PDE and integrated estimates are identified
at their uses.
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

Adding a unit atom at $s$ raises the cumulative function at every
$t\geq s$, so its direction is $\eta=\mathbf1_{[s,1)}$. The
first-order cost is therefore a tail integral:
$$
G(s):=\int_s^1(q(t)-t)\,dt\geq0.
$$
Here $G(s)/2$ is the first-order cost of the added atom. Conversely,
let $\nu=\mu_\gamma|_K$ for a compact $K\subset[0,1)$.
For $0\leq\varepsilon\leq1$, the measure
$\mu_\gamma-\varepsilon\nu=(1-\varepsilon\mathbf1_K)\mu_\gamma$
is nonnegative, and its cumulative function is
$\gamma-\varepsilon\nu([0,\cdot])\in\mathcal U$. Minimality gives
$$
0\leq D_+\mathcal P(\gamma)[-\nu([0,\cdot])]
=-\tfrac12\int_K G(s)\,d\mu_\gamma(s).
$$
The change of integration order is justified by $|q-t|\leq1$ and
$\mu_\gamma(K)<\infty$. Since $G\geq0$, it vanishes almost
everywhere for $\mu_\gamma$, and continuity makes it vanish on
$S=\operatorname{supp}\mu_\gamma$. The variation removes a fraction of
all mass in $K$, not only atoms; no density or probability constraint is assumed.

At a support point $s>0$, $G$ has a minimum. Hence
$$
G'(s)=s-q(s)=0,\qquad G''(s)=1-q'(s)\geq0,
\quad\text{so}\quad q(s)=s,\quad q'(s)\leq1.       \tag{2}
$$
If $0\in S$, contact gives $G(0)=0$; independently, zero field
gives $q(0)=0$. Hence $G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$; nonnegativity gives the
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

Minimality is not a hypothesis of this lemma. Section 3 derives its
moment polynomial and explains the integrated estimate imported from
the source. We first use the lemma to exclude gaps. A complementary
interval with two support endpoints admits two contact conditions;
an initial interval without support at zero has coefficient zero;
a terminal interval requires a boundary estimate.

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
An initial gap $[0,r)$ with $0\notin S$ and $r\in S$ has no
mass, hence $\gamma=0$ there. Its right endpoint gives $q(r)=r$
and $q'(r)\leq1$, while zero field gives $q(0)=0$. The same
integral contradiction follows without assuming $G(0)=0$. A gap
$(0,r)$ with $0\in S$ is already covered by the two-contact case.

A terminal gap cannot use contact at one, which lies outside the
support domain. Its exclusion was recorded by
[Auffinger, Chen and Zeng (2020), Remark 7][ACZ]. The quantitative
argument in [OpenAI (2026a), Lemma 6.3][FS] proves, on any supposed
constant interval ending at one,
$$
1-q(t)\geq C\sqrt{1-t}
$$
for some $C>0$ and all $t$ sufficiently close to one. Two estimates
produce this scale. The heat representation of the terminal value
$|x|$ gives $1-u(t,x)^2\geq\kappa>0$ on
$|x|\leq\sqrt{1-t}$. A transition-kernel comparison from a fixed
earlier time gives a density $f_t(x)\geq m>0$ on the fixed window
$|x|\leq1$, uniformly as $t\uparrow1$. Thus
$$
1-q(t)=\int_{\mathbb R}(1-u(t,x)^2)f_t(x)\,dx
\geq2m\kappa\sqrt{1-t}.
$$
The time-uniform density estimate, proved in Lemma 6.3, equations
(6.6)–(6.7), is essential; pointwise positivity of each density would
not suffice. For $h=1-t<C^2$, we have $q(t)-t\leq h-C\sqrt h<0$,
so $G(s)<0$ for $s$ sufficiently close to one. This contradicts
minimality and also excludes empty support. The zero-coefficient heat
argument and late-step variation have antecedents in
[Chen, Handschy and Lerman (2018), Theorem 6 and its proof][CHL].

These cases exhaust the complement of the relatively closed set $S$.
Consequently $S=[0,1)$, contact gives $q(t)=t$, and differentiation
gives $\mathbb E a^2=1$, including the right-hand value at zero.
Moreover,
$\gamma(t_2)-\gamma(t_1)=\mu_\gamma((t_1,t_2])>0$.
This proves Theorem 1 using the stated analytic inputs.
<!-- /passage:gap-proof -->

<a id="curvature"></a>

## 3. The integrated estimate

<!-- passage:curvature -->
On a plateau with $\gamma=c>0$, put $r=c\Phi_x=c u$,
$v=r_x=c a$, $w=r_{xx}$ and $z=r_{xxx}$. This rescaling makes
the derivative identities polynomial. The PDE becomes
$r_t=-\tfrac12r_{xx}-rr_x$, and the diffusion has spatial generator
$\tfrac12\partial_{xx}+r\partial_x$. Differentiating in space and
applying Itô's formula gives the drift and diffusion pairs
$(0,v)$, $(-v^2,w)$ and $(-3vw,z)$ for $r,v,w$, respectively.
All expectations in this section evaluate spatial functions at
$(t,X_t)$. Starting with $c^2q'=\mathbb E v^2$, Itô's formula gives
$$
c^2q''=\mathbb E[w^2-2v^3],\qquad
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].                 \tag{4}
$$
For example, the drifts of $w^2$ and $v^3$ are
$z^2-6vw^2$ and $3vw^2-3v^4$, respectively. The negative
mixed term is the obstacle. Convexity, which gives $v\geq0$,
does not control it.

The required lower bound holds after integration against the law of
$X_t$. We derive the moment polynomial (4) here; the shape comparisons
and rational identity yielding its lower bound are imported from
[OpenAI (2026a), §§3–4][FS]. They are first established for finite-step
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
and
$$
j:=s_x-(s/r)v=r\,\partial_x(s/r)\geq0.
$$
The last inequality couples the backward gradient to the forward
density; separate monotonicity and concavity do not supply it.
The ratios extend smoothly through zero because $r,s,w$ are odd
and $r_x(0)>0$. These are analytic conclusions of [OpenAI (2026a), §3][FS],
not consequences of the polynomial in (4).

The factorisation of the density gives $f_x/f=r-s$. For a suitable
expression $F$ in the shape quantities, define
$$
\mathcal W(F)=r\partial_xF+(v+r^2-rs)F.
$$
Then $f\mathcal W(F)=\partial_x(rfF)$. The smooth extensions
avoid an interior boundary term at zero, and the source's differentiated
Gaussian tail estimates give $rfF\to0$ at both spatial infinities
for the polynomial correction used below. Hence
$\mathbb E_f\mathcal W(F)=0$, where $\mathbb E_f$ denotes integration
against $f(x)\,dx$.

The remaining step is algebra under these analytic restrictions.
[OpenAI (2026a), Lemma 4.1][FS] gives an explicit polynomial $F_2$
for which subtracting $\mathcal W(F_2)$ from
$z^2-12vw^2+6v^4$ leaves a sum of weighted squares, nonnegative
products and a polynomial with positive coefficients. For example,
one square has the nonnegative weight $r^2j$; this is where the
joint comparison enters. The remainder's $v^4$ coefficient is
$1661507/1521000000>1/1000$. Integration therefore gives
$$
\int_{\mathbb R}(z^2-12vw^2+6v^4)f\,dx
\geq\frac1{1000}\int_{\mathbb R}v^4f\,dx.           \tag{5}
$$
We use (5) as an imported analytic estimate. The full polynomial and
its decomposition are in [Lemma 4.1 and Table 1][certificate];
Proposition 4.2 integrates them using the signs and zero boundary
flux supplied by Lemma 3.4. The long record, §4.4,
“How the signs make a correction with zero expectation useful”,
reproduces those definitions and the complete identity. A pointwise
sign assertion for arbitrary $v,w,z$ would be false.

To obtain Lemma 2 for an integrable coefficient, choose positive
monotone step coefficients $\gamma_n$ retaining the plateau near a
fixed interior time, with $\|\gamma_n-\gamma\|_1\to0$, and terminal
parameters $M_n\geq\|\gamma_n\|_\infty$ with $M_n\to\infty$.
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
The common heat and density methods should be distinguished from the
strength of the resulting estimate. Under the minimiser convention of
Chen's §3.1, Proposition 4.2 proves the crossing implication $q''(t)=0\Rightarrow q'''(t)>0$ on a
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
support but $\gamma'(\tfrac12)=0$: every interval of positive length
has a positive integral, although the integrand vanishes at one point.
The quantitative remainder
in (5) rules this out for a minimiser. First, the identity
$\mathbb E a^2=1$ expresses $\gamma$ as a quotient of continuous
moments and then gives smoothness. Only afterwards do we transfer
(5) from a locally constant comparison coefficient to obtain
$\gamma'>0$.

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

For smoothness, fix $T<1$ and consider all polynomial moments
$$
M_P(t)=\mathbb E P(\Phi_x(t,X_t),\ldots,\partial_x^m\Phi(t,X_t)),
$$
where $P$ is a polynomial in any finite number $m$ of variables.
Spatial differentiation of the PDE and Itô's product rule give
polynomials $Q_P,R_P$, involving finitely many further spatial
derivatives, such that
$$
M_P(t)-M_P(0)=\int_0^t
 [M_{Q_P}(s)+\gamma(s)M_{R_P}(s)]\,ds.
$$
No derivative of $\gamma$ enters this identity. Bounded spatial
derivatives on the fixed strip make every moment continuous.
The integral identity then makes all moments $C^1$, and (7) makes
$\gamma$ $C^1$. Repetition proves smoothness. This is the
quotient-and-moment argument of [Chen (2026), Proposition 4.6
and Appendix B.6][Chen], using the polynomial-moment method of
[Auffinger and Chen (2015), Lemma 2 and the proof of Theorem 2(ii)][AC-properties].
The explicit polynomials and the passage from initially nonsmooth
coefficients are in [OpenAI (2026a), proof of Corollary 6.4][FS]
and the long record, §5.1.

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
The spatial polynomial from (4) has returned. We need the integrated
inequality underlying that calculation: applying the conclusion
$q^{(3)}>0$ directly to the minimiser would be invalid, since $q(t)=t$.
We transfer the spatial moments at a fixed time instead.

Fix $t\in(0,1)$ and $c=\gamma(t)>0$. For
$0<\delta<\min(t,1-t)$ define
$$
\gamma_\delta(s)=
\begin{cases}
c,&t-\delta\leq s<t+\delta,\\
\gamma(s),&\text{otherwise}.
\end{cases}
$$
The inequalities $\gamma(t-\delta)\leq c\leq\gamma(t+\delta)$
make both joins nondecreasing. Thus $\gamma_\delta\in\mathcal U$;
it need not minimise $\mathcal P$. Moreover,
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
Choose a single $T$ with $t<T<1$. Lemma 2.1 of [OpenAI (2026a)][FS]
gives uniform convergence in space and uniform bounds for
$a_\delta,b_\delta,d_\delta$ on $[0,T]$, with the next spatial
derivatives bounded as well. Lemma 2.2 couples the diffusions using
the same Brownian motion and gives
$\sup_{s\leq T}|X_s^\delta-X_s|\to0$. The derivative bounds control
evaluation on these paths, so the integrands in (9) converge and
are uniformly bounded. Dominated convergence passes their expectations
to the limit. The common coefficient $L^1$ bound and the fixed distance
from time one determine these estimates; the shrinking plateau width
does not. Combining the limiting inequality with (8) proves (6).
Strictness follows from $c>0$ and
$\mathbb E a^4\geq(\mathbb E a^2)^2=1$.
In particular, Cauchy–Schwarz gives
$$
\mathbb E a^3\leq\sqrt{\mathbb E a^2\,\mathbb E a^4}
=\sqrt{\mathbb E a^4}\leq\mathbb E a^4,
$$
so the same inequality implies
$\gamma'(t)\geq\gamma(t)^2/2000$ for $0<t<1$.

We have passed spatial moments, not the time derivatives
$q_\delta'''$. Indeed the limiting minimiser has $q(t)=t$ and
$q'''=0$; the coefficient derivative in (8) is exactly what the
constant-interval formula omits. The long record, §§5.1–5.2,
retains the smoothness argument and fixed-time transfer.
<!-- /passage:density-consequence -->

<a id="value-and-qaoa"></a>

## 5. The scalar consequence and a separate circuit theorem

<!-- passage:scalar-value -->
Full support gives the two identities used in the algorithmic
construction. The second moment $\mathbb E a^2=1$ normalises the
stochastic increments, while the first moment recovers the value:
$$
P_*=\mathbb E[UB_1]
   =\int_0^1\mathbb E[a(t,X_t)]\,dt.                \tag{10}
$$
Here $U$ is the almost-sure and $L^2$ limit of the bounded martingale
$M_t=u(t,X_t)$. Since $\mathbb E M_t^2=t$, its limit satisfies
$U^2=1$ almost surely. To see the cancellation behind (10), the
terminal PDE estimate gives $UX_1=|X_1|$, while Itô's formula gives
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt$.
Multiplying $X_1=B_1+\int_0^1\gamma(t)M_t\,dt$ by $U$ cancels
that integral because $\mathbb E[UM_t]=t$. The Parisi formula then
gives (10). The endpoint limits and stochastic-integral covariance
are proved in [OpenAI (2026a), Corollary 7.1][FS] and the long
record, §6, “Recovering the value from a martingale”. This argument
uses full support, not the density corollary.

The gradient-martingale and value methods have antecedents in
[Montanari, preprint v2, Lemmas 3.2–3.4][Montanari], under its
positive-temperature support assumption, and in the zero-temperature
calculations of [El Alaoui, Montanari and Sellke, preprint v1,
Lemmas 6.5 and 6.13][EAMS].

The circuit proof needs a finite correlation construction as well as
the scalar equality. For fixed $0<T<1$, [OpenAI (2026a),
Proposition 7.2][FS] constructs, for all sufficiently large $N$,
from independent standard normals $Z_1,\ldots,Z_{N+1}$, a sign-valued
function $F_N$ and normalised
increments
$g_j=h_j(Z_1,\ldots,Z_{j-1})Z_j$, $1\leq j\leq N$, with
$\mathbb E g_j^2=1$, such that
$$
\lim_{N\to\infty}\sum_{j=1}^N
 \mathbb E[F_Ng_j]\,\mathbb E[F_NZ_{j+1}]
 =\int_0^T\mathbb E[a(t,X_t)]\,dt.                 \tag{11}
$$
The multipliers $h_j$ are normalised Hessians along the Euler
approximation to $X$. The extra variable $Z_{N+1}$ rounds its
terminal gradient to a sign while preserving the conditional mean,
and hence its correlations with the preceding Gaussian variables.
This explains the two coefficient families in (11). The mesh limit
is taken at fixed $T$; only then does $T\uparrow1$ give $P_*$.
The construction and its error estimates are in the long record,
§7, “A finite Gaussian spin and its adjacent correlations”.
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
QAOA alternates evolution under the cost Hamiltonian with transverse-field
mixing, starting from the uniform superposition of spin configurations
[Farhi, Goldstone and Gutmann (2014)][FGG]. Each pair of operations
is a layer, and their durations are its angles. For every
$\varepsilon>0$, [OpenAI (2026b), Theorem 1.1][Q] constructs a
finite depth and deterministic angles, independent of $n$ and the
couplings $J_{ij}$, whose limiting disorder-averaged expected energy
per spin is at
least $P_*-\varepsilon$. The depth and angles may depend on
$\varepsilon$; $n\to\infty$ is taken with them fixed.
[Farhi, Goldstone, Gutmann and Zhou (2022)][FGGZ] established the
fixed-angle thermodynamic limits in this convention. The
eventual-optimality conclusion was conjectured by
[Basso, Farhi, Marwaha, Villalonga and Zhou (2022), §7, equation (7.2)][BFMVZ].

The additional circuit argument must realise the correlation value
in (11). Its recursive construction, gate approximation, removal of
auxiliary randomness and transfer to finite SK systems are separate
steps, reconstructed in the long record, §9, “From the scalar formula
to one ordinary QAOA word”, from [OpenAI (2026b), §§2–6 and Appendix A][Q].
The selected argument gives no quantitative depth bound, finite-size
rate or efficient procedure for finding the angles.
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## 6. Source and formal scope

<!-- passage:evidence-scope -->
This AI-assisted article reconstructs existing results. The ordinary
analytic arguments are in the cited manuscripts; the integrated
estimate (5), its shape hypotheses and the compact-strip approximation
are substantial imported inputs.

The selected [full-support formal statement][support-challenge]
asserts the support and moment conclusions conditional on an admissible
minimiser, and constructs its associated diffusion. A separate
[scalar formal statement][value-challenge] covers value identities and
finite Gaussian approximation, with minimiser and diffusion premises
for those clauses. The two formal models have not been transported
into one another in this record. Neither statement includes the
positive-density corollary or QAOA convergence. The corresponding
[full-support][support-lean] and [scalar][value-lean] implementations
use [Lean][Lean4] and [mathlib][mathlib].

No completed research-target acceptance by Comparator is recorded for
this edition. File-integrity checks and exported theorem specifications
do not establish acceptance of their implementations. Exact versions,
build attempts and the correspondence with the mathematical statements
are retained in the companion source review and the long record,
§8, “What the formal statements establish”, and §11, “Source checks
and finite calculation”.
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

[certificate]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex#L117-L199
