# Full support and positive density in the zero-temperature SK model

*Will Cook · An account of the quantitative proof of OpenAI (2026a) · 19 November 2026*

**AI assistance.** Will Cook directed the work. AI agents based on large
language models produced and revised this manuscript.

<!-- passage:abstract -->
**Abstract.** For the pure, zero-field Sherrington–Kirkpatrick model at
zero temperature, the Stieltjes measure of the minimiser of the
Parisi functional has full support on $[0,1)$ and a smooth
density that is strictly positive on $(0,1)$. Full support and
smoothness are due to H.-B. Chen; strict positivity is due to OpenAI,
whose proof we present. It rests on one coercive inequality for spatial
moments of the Parisi solution along its diffusion, valid for every
order parameter. We print the rational identity behind the inequality in
full, evaluate it in an explicitly solvable case, where the best
constant is $2/5$ against the general $1/1000$, and relate its
hypotheses to the inequalities of Lopatto and Chen.
<!-- /passage:abstract -->

<a id="model-and-result"></a>

## 1. The model and the result

<!-- passage:model -->
For independent standard Gaussian couplings $J_{ij}$, the pure,
zero-field [Sherrington–Kirkpatrick (SK) Hamiltonian][SK] is
$$
H_n(\sigma)=n^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j,
\qquad \sigma\in\{-1,1\}^n.
$$
With the maximisation convention, its limiting ground-state energy per
spin is
$$
P_*:=\lim_{n\to\infty}n^{-1}\mathbb E\max_\sigma H_n(\sigma).
$$
The overlap of two configurations is
$R(\sigma,\tau)=n^{-1}\sum_i\sigma_i\tau_i$, and it determines the
energy covariance, $\mathbb E[H_n(\sigma)H_n(\tau)]=nR^2/2-1/2$.
We use the covariance convention $\xi(t)=t^2/2$, so $\xi''=1$.
Adding one independent centred Gaussian of variance $1/2$ to every
configuration's energy gives covariance $n\xi(R)$ and leaves the
expected maximum unchanged, which is the normalisation of the
ground-state Parisi formula of [Auffinger and Chen (2017), Theorem 1][AC].
The model has no higher-order interactions and no external field.

Let $\mathcal U$ consist of the nonnegative, nondecreasing,
right-continuous functions $\gamma:[0,1)\to[0,\infty)$ satisfying
$\int_0^1\gamma(t)\,dt<\infty$. An element of $\mathcal U$ is an order
parameter, and its locally finite Stieltjes measure is defined by
$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\leq t<1.
$$
Thus $\mu_\gamma((s,t])=\gamma(t)-\gamma(s)$. The measure may have an
atom of size $\gamma(0)$ at zero, and its total mass need not be finite
or equal to one. Support statements refer to the relative topology of
$[0,1)$. A gap is a relatively open interval of positive length and zero
mass, and $\gamma$ is constant on it.

For $\gamma\in\mathcal U$ the Parisi functional is defined through the
solution $\Phi=\Phi_\gamma$ of the Parisi equation with terminal value
$|x|$:
$$
\Phi_t=-\tfrac12\bigl(\Phi_{xx}+\gamma(t)\Phi_x^2\bigr),
\qquad \Phi(1,x)=|x|,
\qquad
\mathcal P(\gamma)=\Phi_\gamma(0,0)-\tfrac12\int_0^1t\gamma(t)\,dt.
$$
The terminal value $|x|$ is the zero-temperature value of one spin
in a field $x$. For an integrable order parameter, the solution is
defined by its stochastic control representation, or equivalently by
approximation from bounded monotone coefficients.
[OpenAI (2026a), §1 and Lemmas 2.1–2.2][FS] give the exact control
definition and the stability theorem. The Parisi formula at zero
temperature states that $P_*=\min_{\gamma\in\mathcal U}\mathcal P(\gamma)$
([Auffinger and Chen (2017), Theorem 1 and the proof of Lemma 3][AC]),
and the minimiser is unique
([Chen, Handschy and Lerman (2018), Theorem 4][CHL]).

Write $u=\Phi_x$ and $a=\Phi_{xx}$. Let $B$ be standard Brownian
motion, and define the controlled diffusion $X$ and the consistency
function $q$ by
$$
dX_t=\gamma(t)u(t,X_t)\,dt+dB_t,\qquad X_0=0,
\qquad q(t)=\mathbb E[u(t,X_t)^2].
$$
The SDE has a unique strong solution. Unless an endpoint limit is
justified explicitly, all stochastic calculations below take place on
compact time intervals ending before one.
<!-- /passage:model -->

<!-- passage:main-result -->
The support of the minimiser is infinite by
[Auffinger, Chen and Zeng (2020), Theorem 1][ACZ]. Infinite support
still allows gaps: the measure $\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$
has infinitely many atoms and many gaps. At positive temperature,
[Lopatto (2026), Theorem 1.1][Lopatto] proved full replica symmetry
breaking throughout the low-temperature phase: the Parisi measure has
support $[0,q_\beta]$. At zero temperature, full support and a smooth
nonnegative density were proved in
[H.-B. Chen (2026), Theorem 1.3][Chen].

**Theorem 1 (full support;
[H.-B. Chen (2026), Theorem 1.3][Chen];
[OpenAI (2026a), Theorem 1.1][FS]).**
If $\gamma\in\mathcal U$ minimises $\mathcal P$, then
$$
\operatorname{supp}\mu_\gamma=[0,1),\qquad
\gamma(t_2)>\gamma(t_1)\quad(0\leq t_1<t_2<1).
$$
For the solution of the displayed SDE and every $0\leq t<1$,
$$
q(t)=t,\qquad \mathbb E[a(t,X_t)^2]=1.
$$

**Corollary 2 (smooth positive density;
[OpenAI (2026a), Corollary 6.4][FS]).** Under the hypotheses of
Theorem 1, $\gamma(0)=0$ and $\gamma\in C^\infty([0,1))$, with
derivatives at zero taken from the right, so that
$\mu_\gamma(dt)=\gamma'(t)\,dt$. Moreover
$$
\gamma'(t)\geq\frac{\gamma(t)^2}{2000}>0\qquad(0<t<1).
$$

Smoothness and $\gamma(0)=0$ are already in Chen's theorem. The strict
lower bound is new in OpenAI's corollary, which states it in the form
(10) below, and the explicit bound $\gamma^2/2000$ is deduced here. Only
nonnegativity of the density at zero is asserted. Integrability allows $\gamma$ to grow near one.
Zero field gives
$u(0,0)=0$, and the curvature calculation uses $\xi''=1$, so both
statements concern only the pure SK covariance at zero field.

Full support has the following interpretation for near-ground states.
For each fixed $\rho\in[0,1)$ and $\delta,\eta>0$, with probability
tending to one there are configurations $\sigma,\tau$ with
$|R(\sigma,\tau)-\rho|<\delta$ whose energies are both at least
$n(P_*-\eta)$. This follows from
[Auffinger, Chen and Zeng (2020), Proposition 1, equation (5)][ACZ]
in the Gaussian normalisation above. Strict increase of $\gamma$ is also
the no-overlap-gap assumption under which the algorithm of El Alaoui,
Montanari and Sellke finds near-ground states (§5.2).

**The two proofs.** Both proofs start from the first variation of
$\mathcal P$. At the minimiser it gives $q(s)=s$ and $q'(s)\leq1$ at
every point $s$ of the support, the consistency and stability
conditions. On an interior gap the order parameter is a positive
constant $c$, and a contradiction with these endpoint conditions must
come from the behaviour of $q$ inside the gap. There
$$
c^2q''=\mathbb E[w^2-2v^3],\qquad
c^2q'''=\mathbb E[z^2-12vw^2+6v^4],
$$
where $v,w,z$ are the second, third and fourth spatial derivatives of
$c\Phi$ along the diffusion.

Chen's proof establishes the crossing property
$q''(t)=0\Rightarrow q'''(t)>0$ on the gap
([Chen (2026), Proposition 4.2][Chen]), in parallel with the
positive-temperature argument of
[Lopatto (2026), v3, Proposition 9.1][Lopatto]. Hence $q''$ changes sign at most
once, from negative to positive, and this is incompatible with the
endpoint conditions.

OpenAI's proof establishes the unconditional bound
$$
c^2q'''(t)\geq\frac1{1000}\,\mathbb E\,v(t,X_t)^4>0
$$
on every positive constant interval of every order parameter
([OpenAI (2026a), Proposition 5.1][FS]). The polynomial
$z^2-12vw^2+6v^4$ takes negative values, so the bound is not pointwise.
It follows from an exact polynomial identity with rational coefficients
which, after one integration by parts against the density of $X_t$,
writes the expectation as a sum of nonnegative terms and
$\kappa\,\mathbb E v^4$ with $\kappa>1/1000$.

The bound is stronger than the crossing property in two respects, and
the proof of Corollary 2 uses both. It needs no hypothesis on $q''$, and
it is a non-strict inequality with an explicit constant between spatial
moments at one time. If
$\gamma$ is replaced by the constant $\gamma(t)$ on a short interval
around $t$, the bound holds for the modified order parameter at time
$t$, although that order parameter does not minimise, and it passes to the limit as the interval shrinks. This gives
Proposition 5 of §4: at each $0<t<1$ with $\gamma(t)>0$,
$$
\mathbb E\bigl[\Phi_{xxxx}^2-12\gamma\,\Phi_{xx}\Phi_{xxx}^2
 +6\gamma^2\Phi_{xx}^4\bigr]
\geq\frac{\gamma(t)^2}{1000}\,\mathbb E\,\Phi_{xx}^4 .
$$
For a smooth order parameter the left side equals
$q'''+2\gamma'\mathbb E a^3$. At the minimiser $q'''=0$, and
Corollary 2 follows.

**Organisation.** Section 2 derives the consistency and stability
conditions and proves Theorem 1 from the curvature bound, stated there
as Lemma 3. Section 3 proves the main estimate. It works out an
explicitly solvable case first, then states the shape inequalities, the
rational identity in full (equation (5) and Table 1) and the passage
to integrable order parameters, and ends with the relation to the
inequalities of Lopatto and Chen. Section 4 proves Proposition 5 and
Corollary 2. Section 5 states the consequences for optimisation, which
use Theorem 1 only. The final section records what the Lean
formalisation covers.

Sections 2–4 assume Itô calculus and the regularity theory of the
Parisi equation. Proofs that we omit are in OpenAI's manuscript at the
places cited, and in *From Parisi full support to deterministic
QAOA circuits: A long reasoning record*, the <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf">[companion edition of 19 November 2026](../long/reasoning-record.md)</span>,
cited below as the companion.
<!-- /passage:main-result -->

<a id="contact"></a>

## 2. The variational conditions and the exclusion of gaps

<!-- passage:contact -->
For $\gamma\in\mathcal U$, the solution $\Phi$ is even, convex and one-Lipschitz
in space. Its spatial derivatives of positive order are bounded and
continuous on each strip $[0,T]\times\mathbb R$, $T<1$, and the PDE
holds for almost every time. The compact-strip regularity and stability results of
[OpenAI (2026a), Lemmas 2.1–2.2][FS] justify the Itô calculations
below even when $\gamma$ has jumps. These facts go back to
[Jagannath and Tobasco (2016)][JT] at positive temperature and to
[Auffinger and Chen (2017), Theorem 2 and Corollary 2][AC] and
[Chen, Handschy and Lerman (2018), Proposition 2 and Theorem 5][CHL]
at zero temperature.

We fix the minimiser. Itô's formula cancels the drift of $u(t,X_t)$:
$$
du(t,X_t)=a(t,X_t)\,dB_t,
\qquad q(0)=0,\qquad q'(t)=\mathbb E[a(t,X_t)^2].
$$
In particular, $q'$ is continuous across jumps of the coefficient.
When $\gamma$ is replaced by $\gamma+\varepsilon\eta$ and
$\varepsilon\downarrow0$, the functional changes at the rate
$$
D_+\mathcal P(\gamma)[\eta]
=\tfrac12\int_0^1\eta(t)(q(t)-t)\,dt,                 \tag{1}
$$
for every integrable direction $\eta$ for which
$\gamma+\varepsilon\eta\in\mathcal U$ for all sufficiently small
$\varepsilon\geq0$ (see [OpenAI (2026a), Lemma 6.1][FS], and
[Chen, Handschy and Lerman (2018), Propositions 3–4][CHL] for the
earlier zero-temperature form).

Adding a unit atom at $s$ raises the cumulative function at every
$t\geq s$, so its direction is $\eta=\mathbf1_{[s,1)}$. Minimality
makes the corresponding tail integral nonnegative:
$$
G(s):=\int_s^1(q(t)-t)\,dt\geq0.
$$
Mass can also be removed. Let $\nu=\mu_\gamma|_K$ for a compact
$K\subset[0,1)$. For $0\leq\varepsilon\leq1$, the measure
$\mu_\gamma-\varepsilon\nu=(1-\varepsilon\mathbf1_K)\mu_\gamma$
is nonnegative, and its cumulative function is
$\gamma-\varepsilon\nu([0,\cdot])\in\mathcal U$. Minimality gives
$$
0\leq D_+\mathcal P(\gamma)[-\nu([0,\cdot])]
=-\tfrac12\int_K G(s)\,d\mu_\gamma(s).
$$
The bounds $|q-t|\leq1$ and $\mu_\gamma(K)<\infty$ justify the
change in the order of integration. Since $G\geq0$, it vanishes almost
everywhere for $\mu_\gamma$, and by continuity it vanishes on
$S=\operatorname{supp}\mu_\gamma$. No probability constraint is
involved, since $\mathcal U$ carries none.

At a support point $s>0$, the function $G$ has a minimum. Hence
$$
G'(s)=s-q(s)=0,\qquad G''(s)=1-q'(s)\geq0,
\quad\text{so}\quad q(s)=s,\quad q'(s)\leq1.       \tag{2}
$$
If $0\in S$, then $G(0)=0$, and zero field gives
$q(0)=0$ independently. Consequently
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$, and nonnegativity gives the
same slope bound at zero. These are the consistency and stability
conditions, in the form of [OpenAI (2026a), Lemma 6.2][FS]
(compare [Chen (2026), Proposition 3.2][Chen]).
<!-- /passage:contact -->

<a id="gap-elimination"></a>

<!-- passage:gap-proof -->
**Lemma 3 (curvature on a constant interval; [OpenAI (2026a),
Proposition 5.1][FS]).** Let $\gamma\in\mathcal U$, with its
diffusion and consistency function $q$. If $\gamma=c$ on an open
interval $I\subset(0,1)$, then for $t\in I$
$$
q'''(t)\geq\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\quad\text{if }c>0.                               \tag{3}
$$
If $c=0$, then $q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$.

The lemma holds for every order parameter, minimising or not.
Section 3 is devoted to its proof.

**Proof of Theorem 1, assuming Lemma 3.** We treat the intervals of the
complement of $S$ by type.

Suppose first that $(\ell,\ell')$ is a gap with endpoints in $S$
and $\ell'<1$. The coefficient is a positive constant there, because
support at $\ell$ and the absence of mass immediately to its right
force $\mu_\gamma([0,\ell])>0$. Strict convexity of $q'$ and (2) give
$$
q'(t)<\frac{\ell'-t}{\ell'-\ell}q'(\ell)
       +\frac{t-\ell}{\ell'-\ell}q'(\ell')\leq1
\qquad(\ell<t<\ell').
$$
Integrating contradicts $q(\ell')-q(\ell)=\ell'-\ell$.

An initial gap $[0,\ell')$ with $0\notin S$ and $\ell'\in S$ carries no
mass, hence $\gamma=0$ there. Its right endpoint gives $q(\ell')=\ell'$
and $q'(\ell')\leq1$, and zero field gives $q(0)=0$. The second part of
Lemma 3 gives $q''>0$, hence $q'(t)<q'(\ell')\leq1$, and the same
integral contradiction follows without assuming $G(0)=0$. A gap
$(0,\ell')$ with $0\in S$ is already covered by the first case.

A terminal gap $(\ell,1)$ with nonempty support has $\ell\in S$ and a
positive constant $c$. Suppose that $q(t)\geq t$ for some $\ell<t<1$.
Strict convexity of $q'$ and $q'(\ell)\leq1$ give
$$
t-\ell\leq\int_\ell^t q'(s)\,ds
<\frac{t-\ell}{2}\bigl(q'(\ell)+q'(t)\bigr),
$$
so $q'(t)>1$. Convexity then gives $q'(s)>q'(t)>1$ for $s>t$, and
consequently $q(s)>t+(s-t)q'(t)>1$ for $s<1$ sufficiently close
to one, contrary to $q\leq1$. Thus $q(t)<t$ on $(\ell,1)$,
and $G(\ell)<0$ contradicts minimality. This case uses the conditions (2)
only at the left endpoint.

If $S$ is empty, then $\gamma=0$. Lemma 3 makes $q$ strictly
convex, and $q(0)=0$ and $q\leq1$ give $q(t)<(t/b)q(b)\leq t/b$ for
$0<t<b<1$. Letting $b\uparrow1$ gives $q(t)\leq t$. Strict convexity
applied once more with $t<b<1$ now gives $q(t)<(t/b)q(b)\leq t$, so
$G(0)<0$.

These cases exhaust the complement of the relatively closed set $S$.
Consequently $S=[0,1)$, the conditions (2) give $q(t)=t$, and
differentiation gives $\mathbb E a^2=1$, including the right-hand value
at zero. Moreover,
$\gamma(t_2)-\gamma(t_1)=\mu_\gamma((t_1,t_2])>0$. $\qquad\square$

**Remarks on the endpoints.** The exclusion of a terminal gap was noted
in [Auffinger, Chen and Zeng (2020), Remark 7][ACZ]. The argument above
uses only the curvature needed for the other gaps. The proof of
[OpenAI (2026a), Lemma 6.3][FS] gives the stronger boundary
estimate $1-q(t)\geq C\sqrt{1-t}$ for any order parameter constant
near one, and
[Chen (2026), Proposition 4.5, equations (4.27)–(4.38)][Chen]
gives the square-root asymptotic under the terminal-gap hypothesis. Both
are discussed in the companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="terminal-gap">[§5](../long/reasoning-record.md#terminal-gap)</span>.
At the left endpoint, Chen takes $0\in S$ from
[Chen, Handschy and Lerman (2018)][CHL]
(see [Chen (2026), Proposition 3.2 and Remark 4.4][Chen]). The proof
above treats an initial gap directly through the heat equation, for
which antecedents appear in
[Chen, Handschy and Lerman (2018), Theorem 6][CHL].

**Comparison with the crossing argument.** In
[Chen (2026), Proposition 4.3][Chen] an internal gap $(\ell,\ell')$ is
excluded as follows. The crossing property shows that $q''$ has at
most one zero in the gap. The equalities $G(\ell)=G(\ell')=0$ and
$q(\ell)=\ell$, $q(\ell')=\ell'$ give
$\int_\ell^{\ell'}(t-\ell)(\ell'-t)\,q''(t)\,dt=0$, so $q''$ is negative and then
positive, and a second integration yields
$q(\ell')-q(\ell)<(\ell'-\ell)q'(\ell+)\leq \ell'-\ell$. Only the stability condition
at the left endpoint is used. With (3) available, strict convexity of
$q'$ replaces the analysis of the sign changes of $q''$, at the price of
using stability at both endpoints.
<!-- /passage:gap-proof -->

<a id="curvature"></a>

## 3. The coercive inequality on a constant interval

<!-- passage:curvature -->
On an interval where $\gamma=c>0$, put $r=c\Phi_x$,
$v=r_x$, $w=r_{xx}$ and $z=r_{xxx}$. The PDE becomes
$r_t=-\tfrac12r_{xx}-rr_x$, and the diffusion has spatial generator
$\tfrac12\partial_{xx}+r\partial_x$. Differentiating in space and
applying Itô's formula gives the drift and diffusion pairs
$(0,v)$, $(-v^2,w)$ and $(-3vw,z)$ for $r,v,w$, respectively.
All expectations in this section evaluate spatial functions at
$(t,X_t)$. Starting from $c^2q'=\mathbb E v^2$, Itô's formula gives
$$
\begin{aligned}
c^2q''&=\mathbb E[w^2-2v^3],\\
c^2q'''&=\mathbb E[z^2-12vw^2+6v^4].
\end{aligned}                                      \tag{4}
$$
For example, the drifts of $w^2$ and $v^3$ are
$z^2-6vw^2$ and $3vw^2-3v^4$, respectively. Lemma 3 for $c>0$ is
therefore the inequality
$\mathbb E[z^2-12vw^2+6v^4]\geq\mathbb E v^4/1000$. The equation for
$r$ is invariant under $r(t,x)\mapsto\lambda r(\lambda^2t,\lambda x)$,
which multiplies $v,w,z$ by $\lambda^2,\lambda^3,\lambda^4$, and the
polynomial is homogeneous of weight eight for this scaling.

### 3.1 An explicitly solvable case

The proof of the inequality works with finite-step coefficients and the
smooth terminal value $M^{-1}\log(2\cosh Mx)$, where $M$ bounds the
coefficient. Its simplest instance is a single step with $c=M$, and by
the scaling we may take $c=M=1$. Then
$$
\Phi(t,x)=\log(2\cosh x)+\tfrac{1-t}2,\qquad r=\tanh x,
$$
so the drift does not depend on time, and $X_t$ has the law
$\tfrac12N(t,t)+\tfrac12N(-t,t)$. With $\theta=\tanh^2x$ we have
$v=1-\theta$, $w^2=4\theta(1-\theta)^2$ and $z=(1-\theta)(6\theta-2)$,
hence
$$
z^2-12vw^2+6v^4=(1-\theta)^2\,(90\theta^2-84\theta+10).
$$
This is negative for $(7-2\sqrt6)/15<\theta<(7+2\sqrt6)/15$, that is,
for $0.140<\theta<0.793$, and it equals $-19/8$ at $\theta=1/2$.
At $t=1/2$ the diffusion lies in the negative region with probability
$0.56$. Convexity of $\Phi$, which gives $v\geq0$, therefore does not
control the mixed term.

The expectation is nevertheless positive. The density of $X_t$ is
$$
f(t,x)=\frac{\cosh x}{\sqrt{2\pi t}}\,e^{-x^2/(2t)-t/2},
$$
and
$\rho(t):=\mathbb E[z^2-12vw^2+6v^4]/\mathbb E v^4$ has the limits
$$
\lim_{t\downarrow0}\rho(t)=10,\qquad
\lim_{t\to\infty}\rho(t)
=\frac{\int(16\operatorname{sech}^3x-96\operatorname{sech}^5x
        +90\operatorname{sech}^7x)\,dx}
       {\int\operatorname{sech}^7x\,dx}
=\frac{\pi/8}{5\pi/16}=\frac25 .
$$
The first holds because $X_0=0$, and the second by dominated
convergence, since $\sqrt{2\pi t}\,e^{t/2}f(t,x)\to\cosh x$.

Moreover $\rho(t)>2/5$ for every $t>0$. Put
$$
F(x)=16\operatorname{sech}^3x-96\operatorname{sech}^5x
     +\tfrac{448}5\operatorname{sech}^7x
    =\tfrac15\cosh x\,(1-\theta)^2\,(448\theta^2-416\theta+48),
$$
so that $\rho(t)-2/5$ is a positive multiple of
$\int_0^\infty F(x)e^{-x^2/(2t)}\,dx$. The quadratic has two roots in
$(0,1)$, so $F$ is positive, then negative, then positive on
$(0,\infty)$, and the integrals of powers of $\operatorname{sech}$ give
$\int_0^\infty F\,dx=0$ and $\int_0^\infty x^2F\,dx=-52\pi/225$.
Hence $G(x)=\int_0^xF$ is positive and then negative, with
$G(\infty)=0$, and $K(x)=\int_0^xyG(y)\,dy$ increases and then decreases
to $K(\infty)=-\tfrac12\int_0^\infty x^2F\,dx>0$, so $K>0$ on
$(0,\infty)$. Two integrations by parts give
$\int_0^\infty F(x)e^{-x^2/(2t)}\,dx
=t^{-2}\int_0^\infty K(x)\,x\,e^{-x^2/(2t)}\,dx>0$.
For these data the best constant
in the integrated inequality, (6) of §3.3, is therefore $2/5$, not
attained, against the $1/1000$ of the general proof. Numerically
$\rho(1/2)=2.39$, and this value is decomposed term by term in §3.3.

The same pointwise obstruction occurs for the terminal value $|x|$.
For $\gamma\equiv c$ and $\tau=1-t$, an expansion at small $c$ gives
$z^2-12vw^2+6v^4=-12c^3a_0^3/\tau+O(c^4)<0$ at $x=\sqrt\tau$, where
$a_0=\sqrt{2/(\pi\tau)}\,e^{-1/2}$
(<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="pointwise-curvature-obstruction">[companion, §4.1](../long/reasoning-record.md#pointwise-curvature-obstruction)</span>).

### 3.2 The two heat equations and the shape inequalities

We now take a positive nondecreasing finite-step coefficient
$\gamma_{\rm step}$, that is, a function constant on each interval of a
finite partition, and the terminal value $M^{-1}\log(2\cosh Mx)$ with
$M\geq\|\gamma_{\rm step}\|_\infty$.
On a step of height $c$, set $h=e^{c\Phi}$. Then
$h_t=-h_{xx}/2$ and $r=h_x/h$, the Cole–Hopf transformation. The same
exponential removes the drift from the equation for the density $f$ of
$X_t$. Indeed, writing $f=hg$ gives
$$
\begin{aligned}
f_t&=\tfrac12(hg)_{xx}-(h_xg)_x\\
   &=-\tfrac12h_{xx}g+\tfrac12hg_{xx}
    =h_tg+\tfrac12hg_{xx}.
\end{aligned}
$$
Comparison with $f_t=h_tg+hg_t$ yields $g_t=g_{xx}/2$. Thus
$f=hg$ with $h$ a solution of the backward heat equation and $g$ a
solution of the forward one. The factor $g$ is the transformed density
of [Lopatto (2026), Proposition 7.1][Lopatto] and the function $Q$ of
[Chen (2026), §3.2][Chen]. Its score is $s=-\partial_x\log g$, so that
$f_x/f=r-s$. On the first step $s=x/t$.

The functions $r$ and $s$ are odd and positive on $x>0$. On $x>0$,
at every time of every step,
[OpenAI (2026a), Lemmas 3.2–3.3][FS] prove
$$
\begin{gathered}
v>0,\qquad w\leq0,\qquad H:=\frac{w}{2r}+v\leq0,\qquad H_x\geq0,\\
s_x\geq\frac1t,\qquad s_{xx}\leq0,\qquad
j:=s_x-\frac sr\,v=r\,\partial_x\Bigl(\frac sr\Bigr)\geq0 .
\end{gathered}
$$
Thus $r$ and $s$ are increasing and concave, and the ratio $s/r$ of the
two scores is nondecreasing. Since
$r_t=-\tfrac12w-rv=-rH$, we have $H=-\partial_t\log\Phi_x$, and
$H\leq0$ says that the gradient $\Phi_x(t,x)$ at a fixed $x>0$ is
nondecreasing in $t$ within a step.

Each sign is propagated within a step by a parabolic comparison and
checked at the jumps. For the ratio, concavity of $r$ gives $j\geq0$ on
the first step, where $s=x/t$. At a forward jump with
$k=c_+/c_-\geq1$, continuity of $\Phi$ and $f$ gives
$$
r_+=kr_-,\qquad s_+=s_-+(k-1)r_-,\qquad
j_+=(s_x)_+-\frac{s_+}{r_+}(r_x)_+=j_-.
$$
Thus $j$ is unchanged at jumps of the coefficient.
The quotients $w/r$ and $s/r$ extend smoothly through zero because
$r,s,w$ are odd and $r_x(0)>0$. The ratio inequality is the one that
has no counterpart in the crossing arguments (§3.5). It also follows
from [Zhou (2026), Appendix E.3, (E.37) and (E.41)][zhou-gardner], after
rescaling the smoothed finite-step problem
(<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="shape-comparisons">[companion, §4.3](../long/reasoning-record.md#shape-comparisons)</span>).

In the case of §3.1, $H\equiv0$, $s=x/t$ and
$j=t^{-1}(1-2x/\sinh2x)$. The backward inequalities for $H$ are
equalities there, and $H$ measures the departure of a general step from
the profile $\tanh$.

### 3.3 The rational identity

The inequalities are used through nonnegative even quantities.
Following [OpenAI (2026a), §3.4][FS], set
$$
R=r^2,\quad K=rs,\quad b=-\frac wr,\quad
B=b-2v=-2H,\quad S=z+bv-2Rb=2rH_x,\quad L=-rs_{xx},
$$
together with $v$ and $j$. All eight are nonnegative on the line, and
$Rb^2=w^2$. The letters are those of OpenAI (2026a), so that the identity
(5) below can be compared with its Table 1. Within §§3.3–3.5 they replace
the earlier meanings of $B$, $S$, $R$ and $K$, and $Q$ and $T$ denote
the polynomials defined below. For the scaling at the beginning of this
section, $R,K,v,b,j,B$ have weight two and $z,S,L$ weight four. For $\mathcal D=r\partial_x$
one has
$$
\mathcal D(R,K,v,b,j)
=\bigl(2Rv,\ 2vK+Rj,\ -Rb,\ -z-bv,\ -jv+Kb-L\bigr),
$$
so $\mathcal D$ maps polynomials in $R,K,v,b,j$ to polynomials in
$R,K,v,b,j,z,L$. For such a polynomial $F$ put
$$
\mathcal W(F)=\mathcal DF+(v+R-K)F .
$$
Since $f_x/f=r-s$, we have $f\,\mathcal W(F)=\partial_x(rfF)$. The
smooth extensions
avoid an interior boundary term at zero, and the differentiated
Gaussian tail estimates give $rfF\to0$ at both spatial
infinities. Hence
$\mathbb E_f\mathcal W(F)=0$, where $\mathbb E_f$ denotes integration
against $f(x)\,dx$ ([OpenAI (2026a), Lemma 3.4][FS]).

The problem is thus to find a polynomial $F$ such that
$z^2-12vw^2+6v^4-\mathcal W(F)$ is a sum of squares and of products of
the nonnegative quantities, with a positive multiple of $v^4$
among them. By homogeneity $F$ is a cubic form in $R,K,v,b,j$. The terms containing $z$ are arranged first. The only rule of $\mathcal D$ that produces $z$ is
$\mathcal Db=-z-bv$, so the coefficient of $z$ in $\mathcal W(F)$ is
$-\partial_bF$. Choose
$$
\begin{aligned}
Q&=\tfrac1{13}vb+\tfrac{53}{24}v^2+\tfrac{19}{16}Kv
   -\tfrac{19}{8}Rb+\tfrac{73}{48}Rv,\\
T&=v\bigl(\tfrac{2331}{10000}R+\tfrac{87}{2500}j\bigr),
\end{aligned}
$$
and let $F_2$ satisfy $\partial_bF_2=2Q+T$:
$$
\begin{aligned}
F_2={}&\bigl(\tfrac1{13}v-\tfrac{19}{8}R\bigr)b^2
 +b\bigl(\tfrac{53}{12}v^2+\tfrac{19}{8}Kv
        +\tfrac{98243}{30000}Rv+\tfrac{87}{2500}jv\bigr)\\
 &+\tfrac{4663}{5000}v^2j+\tfrac{6853}{10000}v^3
  -\tfrac{1051}{400}Kv^2-\tfrac{1073}{500}Rv^2 .
\end{aligned}
$$
Then $z^2-(z+Q)^2-ST-\mathcal W(F_2)$ contains no $z$. The last line
of $F_2$ does not involve $b$ and is free for the remaining terms.

**Lemma 4 (rational identity; [OpenAI (2026a), Lemma 4.1][certificate]).** As polynomials
over $\mathbb Q$ in $R,K,v,b,j,z,L$, with $B=b-2v$ and $S=z+bv-2Rb$,
$$
\begin{aligned}
z^2-12Rvb^2+6v^4={}&\mathcal W(F_2)+(z+Q)^2+ST
 +\tfrac{4663}{5000}Lv^2+\tfrac{87}{2500}Lbv\\
&+\tfrac{337}{10000}Rj(b-7v)^2
 +\tfrac{183}{2500}RB\bigl(b-\tfrac73v\bigr)^2
 +\tfrac{411}{10000}Kv\bigl(b-\tfrac92v\bigr)^2\\
&+\tfrac{11461}{5000}vB\bigl(K+\tfrac14R-\tfrac17v\bigr)^2
 +\tfrac{647}{10000}v^2\bigl(b-\tfrac{14}5v-\tfrac{13}4K
   +\tfrac43R\bigr)^2
 +P_{\rm rem},
\end{aligned}                                          \tag{5}
$$
where $P_{\rm rem}$ is the polynomial in $R,K,v,B,j$ with the 22
positive coefficients of Table 1.

| Monomial | Coefficient | Monomial | Coefficient |
|:---------|------------:|:---------|------------:|
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

*Table 1. The coefficients of $P_{\rm rem}$
([OpenAI (2026a), Table 1][certificate]).*

The identity is verified by expanding both sides. Each term on the
right other than $\mathcal W(F_2)$ is nonnegative, and each inequality
of §3.2 enters at an identifiable place: $H_x\geq0$ only through
$ST$; concavity of the forward score only through the two terms with
$L$, the second of which also uses $b\geq0$; the ratio inequality through $T$, the square with prefactor $Rj$
and five monomials of the table; and $H\leq0$ through the prefactors
$RB$, $vB$ and the monomials containing $B$. Since $Rb^2=w^2$, the left
side is $z^2-12vw^2+6v^4$. Integration against $f$ removes
$\mathcal W(F_2)$ and keeps the coefficient of $v^4$:
$$
\int_{\mathbb R}(z^2-12vw^2+6v^4)f\,dx
\geq\kappa\int_{\mathbb R}v^4f\,dx,
\qquad
\kappa=\frac{1661507}{1521000000}>\frac1{1000}.     \tag{6}
$$
This is [OpenAI (2026a), Proposition 4.2][FS].

In the case of §3.1 we have $B=S=L=0$ and $b=2v$, and (5) reduces to
$(z+Q)^2$, the squares with prefactors $Rj$, $Kv$ and $v^2$, and
the eight monomials of the table without $B$. At $t=1/2$ their
expectations are $0.580$, $0.036$, $0.030$, $0.135$ and $0.115$, with
sum $0.896=\mathbb E[z^2-12vw^2+6v^4]$, while
$\kappa\,\mathbb E v^4=0.0004$. Most of the expectation is carried by
the square $(z+Q)^2$, and $\kappa$ is the coefficient guaranteed for
all finite-step data.

OpenAI (2026a) does not say how the coefficients were found. The form of
(5) is that of a sum-of-squares certificate modulo integration by
parts: once the admissible products are fixed, the coefficients of
$F_2$ and of the remainder enter linearly and the squares give a
semidefinite constraint, so that the search is a finite-dimensional
feasibility problem. Certificates of this form are constructed
systematically for entropy inequalities in
[Jüngel and Matthes (2006)][JM]. The identity itself is part of the
Lean formalisation (see the final section).

### 3.4 Integrable order parameters

To obtain Lemma 3 for $\gamma\in\mathcal U$ with $\gamma=c>0$ on $I$,
fix $t\in I$ and choose positive
monotone step coefficients $\gamma_n$ equal to $c$ on a fixed
neighbourhood of $t$, with $\|\gamma_n-\gamma\|_1\to0$, and terminal
smoothing parameters $M_n\geq\|\gamma_n\|_\infty$ with $M_n\to\infty$.
Spatial derivatives through order four then converge uniformly on a
fixed strip below one, and the diffusions driven by the same Brownian
motion converge
(see [OpenAI (2026a), Lemmas 2.1–2.3 and Proposition 5.1][FS]). Only
$v,w,z$ remain in (6), so no convergence of $s$, $j$ or $w/r$ is
needed. Dividing by $c^2$ gives (3), and
strictness follows from $\Phi_{xx}>0$ on the interval.
The approximants and their common strip bounds are specified in the
companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="plateau-limit">[§4.5](../long/reasoning-record.md#plateau-limit)</span>.

For $c=0$ the equation on $I$ is the heat equation and
$q''=\mathbb E\,\Phi_{xxx}^2$. Its
strictness uses a positive diffusion density and the fact that
$\Phi_{xxx}$ cannot vanish identically, since an even quadratic profile
cannot differ from $|x|$ by a bounded function.

### 3.5 The slope coordinates of Lopatto and Chen

The crossing arguments record the shape of $\Phi$ on a constant
interval $\gamma=m$ in the slope coordinate $\Phi_x$
([Lopatto (2026), v2, Proposition 3.6][Lopatto-v2];
[Chen (2026), Propositions 3.10 and 3.11][Chen]). With
$\mathsf c=\Phi_{xx}$ regarded as a function of the slope,
$\mathsf z=-\tfrac12\partial_{\Phi_x}\mathsf c$,
$\mathsf K=\mathsf z/\Phi_x-m$ and
$\mathsf J=\partial_{\Phi_x}(\Phi_x\mathsf K)$, they prove
$\mathsf K,\partial_{\Phi_x}\mathsf K,\mathsf J,
\partial_{\Phi_x}\mathsf J\geq0$ and
$\mathsf c\,\partial_{\Phi_x}\mathsf J\leq3\mathsf z\mathsf J$ for
nonnegative slopes. Since
$\partial_{\Phi_x}=\Phi_{xx}^{-1}\partial_x$, a direct calculation with
$c=m$ gives, for $x>0$,
$$
\mathsf K=-\frac{H}{\Phi_{xx}}=\frac{cB}{2v},\qquad
\partial_{\Phi_x}\mathsf K=\frac{c^2\,(BRb-Sv)}{2rv^3},\qquad
\mathsf J=\frac{c\,\bigl(B(v^2+Rb)-Sv\bigr)}{2v^3}.
$$
Thus $\mathsf K\geq0$ is the inequality $H\leq0$, and
$\partial_{\Phi_x}\mathsf K\geq0$ is the upper bound $Sv\leq BRb$, which
is not used in (5). The certificate uses instead the lower bound
$S\geq0$. For the smooth finite-step data of §3.2, to which both
families apply, they give together
$$
0\leq Sv\leq BRb .
$$
On the forward side, Chen writes $\Gamma$ for $q$, $Q$ for $g$,
$\mathfrak r$ for $s$ and $H$ for $g_{xx}/g=s^2-s_x$. For the
finite-step data, the log-concavity of $g$ and the monotonicity of
$g_{xx}/g$ on $x>0$, which
[Chen (2026), Proposition 3.7][Chen] proves for the terminal value
$|x|$, follow from $s\geq0$,
$s_x>0$ and $s_{xx}\leq0$, because
$\partial_x(s^2-s_x)=2ss_x-s_{xx}$. The inequalities for
$\partial_{\Phi_x}\mathsf J$ involve the fifth derivative of $\Phi$ and
have no counterpart in (5), and the ratio inequality $j\geq0$ has none
in the slope-coordinate family. The inequalities for $\mathsf K$ and
$\mathsf J$ originate in
[Lopatto (2026), v2, Proposition 3.6][Lopatto-v2], and the transformed
density appears in [Lopatto (2026), v3, Proposition 7.1][Lopatto]. The
inequalities $H_x\geq0$ and $j\geq0$ are proved in
[OpenAI (2026a), Lemmas 3.2–3.3][FS].
<!-- /passage:curvature -->

<a id="positive-density"></a>

## 4. The coercive inequality at a fixed time and positivity of the density

<!-- passage:density-consequence -->
For $\gamma\in\mathcal U$ and $0<t<1$ set
$$
\mathcal C_\gamma(t)
=\mathbb E\bigl[\Phi_{xxxx}^2-12\gamma(t)\,a\,\Phi_{xxx}^2
 +6\gamma(t)^2a^4\bigr],
$$
with the spatial factors evaluated at $(t,X_t)$. On an interval where
$\gamma=c$ this is $q'''(t)$, by (4). The definition involves no time
derivative of $\gamma$.

**Proposition 5 (coercive inequality at a fixed time).** Let
$\gamma\in\mathcal U$ and $0<t<1$,
and suppose that $c=\gamma(t)>0$. For its diffusion,
$$
\mathcal C_\gamma(t)\geq\frac{c^2}{1000}
                       \mathbb E[a(t,X_t)^4].
$$
Neither minimality, nor continuity of $\gamma$ at $t$, nor a constant
neighbourhood of $t$ is required.

The statement is implicit in
[OpenAI (2026a), proof of Corollary 6.4][FS]. We state it separately
because it is the form in which the inequality is used at the minimiser.

**Proof.** For
$0<\delta<\min(t,1-t)$ define
$$
\gamma_\delta(s)=
\begin{cases}
c,&t-\delta\leq s<t+\delta,\\
\gamma(s),&\text{otherwise}.
\end{cases}
$$
The inequalities $\gamma(t-\delta)\leq c\leq\gamma(t+\delta)$
make both joins nondecreasing, so $\gamma_\delta\in\mathcal U$, although
it need not minimise $\mathcal P$. Moreover,
$$
\|\gamma_\delta-\gamma\|_1
\leq2\delta\,[\gamma(t+\delta)-\gamma(t-\delta)]
\longrightarrow0.
$$
We use a subscript $\delta$ for its value function, its derivative
$a_\delta$ and its diffusion. Lemma 3 and (4) give at the fixed time $t$
$$
\mathcal C_{\gamma_\delta}(t)
\geq\frac{c^2}{1000}\mathbb E[a_\delta(t,X^\delta_t)^4].   \tag{7}
$$
Choose $t<T<1$. Lemma 2.1 of
[OpenAI (2026a)][FS] gives uniform convergence in space and uniform
bounds for the second, third and fourth spatial derivatives of
$\Phi_{\gamma_\delta}$ on $[0,T]$, with the next
spatial derivatives bounded as well. By Lemma 2.2, the diffusions
coupled through the same Brownian motion satisfy
$\sup_{s\leq T}|X_s^\delta-X_s|\to0$. The derivative bounds control
evaluation along these paths, so the integrands in (7) converge and
are uniformly bounded, and dominated convergence passes their
expectations to the limit. These estimates depend only on the common
$L^1$ bound on the coefficient and the fixed distance from time one,
whatever the width of the constant interval. The result is
$\mathcal C_\gamma(t)\ge\gamma(t)^2\mathbb E a^4/1000$. $\qquad\square$

The limit is taken in spatial moments at the single time $t$. It does
not identify $q_\delta'''(t)$ with a derivative of the limiting
consistency function, and no such identification holds: for the
minimiser $q'''=0$.

Full support alone does not force a pointwise
positive density. For instance,
$\gamma(t)=\int_0^t(s-\tfrac12)^2\,ds$ has full Stieltjes
support but $\gamma'(\tfrac12)=0$.

**Proof of Corollary 2.** All spatial factors in the expectations below are evaluated
at $(t,X_t)$. Since $da=-\gamma a^2\,dt+\Phi_{xxx}\,dB$, Itô's formula
applied to $a^2$ gives, for almost every $t$,
$0=\frac{d}{dt}\mathbb E a^2
=\mathbb E\,\Phi_{xxx}^2-2\gamma\mathbb E a^3$,
where the left side vanishes because full support gives
$\mathbb E a^2=1$. Solving for the coefficient yields
$$
\gamma(t)=\frac{\mathbb E\,\Phi_{xxx}^2}{2\mathbb E a^3}.      \tag{8}
$$
At first (8) holds almost everywhere. Its denominator is at least
two, because $a\geq0$ and
$\mathbb E a^3\geq(\mathbb E a^2)^{3/2}=1$.
The moments are continuous, so right continuity of $\gamma$ extends
(8) to every time and proves that $\gamma$ is continuous. Evenness
gives $\Phi_{xxx}(0,0)=0$, hence $\gamma(0)=0$.

Smoothness follows by induction, as in
[Chen (2026), Proposition 4.6 and Lemma 3.14][Chen]. Fix $T<1$ and
consider the polynomial moments
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
The identity involves $\gamma$ and none of its derivatives. Bounded
spatial derivatives on the fixed strip make every moment continuous.
If $\gamma\in C^k([0,T])$ and every $M_P$ is $C^k$, the integral
identity makes every $M_P$ of class $C^{k+1}$, and then (8) makes
$\gamma$ of class $C^{k+1}$. The case $k=0$ has just been proved, so
$\gamma\in C^\infty([0,T])$ for every $T<1$. The method of polynomial
moments is that of
[Auffinger and Chen (2015), Lemma 2 and the proof of Theorem 2(ii)][AC-properties],
and the companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="smooth-density-consequence">[§9.1](../long/reasoning-record.md#smooth-density-consequence)</span>,
gives the polynomials explicitly.

The two differentiated moments are now
$$
\frac{d}{dt}\mathbb E\,\Phi_{xxx}^2
=\mathbb E[\Phi_{xxxx}^2-6\gamma a\Phi_{xxx}^2],
\qquad
\frac{d}{dt}\mathbb E a^3=\mathbb E[3a\Phi_{xxx}^2-3\gamma a^4].
$$
For a smooth order parameter, differentiating
$q''=\mathbb E\,\Phi_{xxx}^2-2\gamma\mathbb E a^3$ therefore gives
$$
q'''+2\gamma'\,\mathbb E a^3
=\mathcal C_\gamma(t).                              \tag{9}
$$
On a constant interval $\gamma'=0$, and (9) is the second line of (4).
For the minimiser $q=t$, so $q'''=0$ and the left
side is $2\gamma'\mathbb E a^3$. Strict increase and
$\gamma(0)=0$ give $\gamma(t)>0$ for $t>0$, so Proposition 5 applies
and gives
$$
2\gamma'(t)\,\mathbb E[a(t,X_t)^3]
\geq\frac{\gamma(t)^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(0<t<1).                                    \tag{10}
$$
Cauchy–Schwarz and $\mathbb E a^4\geq(\mathbb E a^2)^2=1$ give
$$
\mathbb E a^3\leq\sqrt{\mathbb E a^2\,\mathbb E a^4}
=\sqrt{\mathbb E a^4}\leq\mathbb E a^4,
$$
so (10) implies
$\gamma'(t)\geq\gamma(t)^2/2000$ for $0<t<1$. $\qquad\square$

**Remarks.** (i) *The crossing property and positivity.* By (9), at
the smooth minimiser both $q''$ and $q'''$ vanish identically, and
$\gamma'(t)>0$ is equivalent to $\mathcal C_\gamma(t)>0$. The crossing
property does not give this. As stated,
[Chen (2026), Proposition 4.2][Chen] concerns the minimiser, and
$\gamma_\delta$ is not one. Moreover $q_\delta''(t)=0$ need not hold for
any $\delta>0$, and even if it did, the strict conclusion
$\mathcal C_{\gamma_\delta}(t)>0$ would yield only
$\mathcal C_\gamma(t)\geq0$ as $\delta\to0$. Proposition 5 needs neither
hypothesis, and its right side converges to
$\gamma(t)^2\,\mathbb E a^4/1000>0$.

(ii) *The constant.* Integrating $\gamma'\geq\gamma^2/2000$ gives
$\gamma(s)^{-1}-\gamma(t)^{-1}\geq(t-s)/2000$ for $0<s<t<1$. The
constant is not sharp: for the data of §3.1 the best constant in (6)
is $2/5$.

(iii) *Related arguments at a fixed time.*
[Lopatto's v4, Proposition 5.1 and Corollary 5.6][Lopatto-v4] give
qualitative crossing for arbitrary positive-temperature probability
measures. [Lopatto's external-field paper, Theorem 2.3 and §8][Lopatto-field]
uses a spatial inequality at a fixed time for support and positive
density at positive temperature, and its Appendix B gives the strict
positivity of the density at zero field. In unit-noise coordinates the
positive-temperature coefficient is $\beta\alpha_\nu$, where
$\alpha_\nu(t)=\nu([0,t])$, and the terminal value is
$\beta^{-1}\log\cosh(\beta x)$. Every bounded $\gamma\in\mathcal U$ has
this form, so the estimates differ only in the terminal value and the
explicit constant. Proposition 5 treats the terminal value $|x|$ with an
explicit lower bound. The rescaling and
the comparison of hypotheses are in the companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="finite-temperature-dictionary">[§2.3](../long/reasoning-record.md#finite-temperature-dictionary)</span>.
<!-- /passage:density-consequence -->

<a id="value-and-qaoa"></a>

## 5. Consequences for optimisation

<!-- passage:scalar-value -->
The results of this section use Theorem 1 only. Strict positivity of
the density is not needed.

### 5.1 A martingale formula for the ground-state energy

Set $M_t=u(t,X_t)$, the bounded gradient martingale, which satisfies
$dM_t=a(t,X_t)\,dB_t$. Its quadratic variations distinguish the two
moments of $a$:
$$
d\langle M\rangle_t=a(t,X_t)^2\,dt,
\qquad d\langle M,B\rangle_t=a(t,X_t)\,dt.
$$
Full support gives $\mathbb E a(t,X_t)^2=1$, so each increment
$M_t-M_s$ has unconditional variance $t-s$. The first moment of $a$
gives instead the
covariance with the driving noise. Let $U$ be the almost-sure and
$L^2$ limit of $M_t$. The value identity is
$$
P_*=\mathbb E[UB_1]
   =\int_0^1\mathbb E[a(t,X_t)]\,dt.                \tag{11}
$$
Boundedness gives $|U|\leq1$, while $\mathbb E M_t^2\to1$ gives
$\mathbb E U^2=1$, so $U^2=1$ almost surely.

The cancellation behind (11) runs as follows. Terminal convergence of
the convex value functions gives $UX_1=|X_1|$ (the equality is
automatic on $X_1=0$), and Itô's formula gives
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt$.
Multiplying $X_1=B_1+\int_0^1\gamma(t)M_t\,dt$ by $U$ cancels
that integral, because $\mathbb E[UM_t]=t$, and the Parisi formula
then gives (11). [OpenAI (2026a), Corollary 7.1][FS] and the
companion, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="scalar-value-identities">[§6](../long/reasoning-record.md#scalar-value-identities)</span>, prove the endpoint limits and the
stochastic-integral covariance. Moreover, convexity and
Cauchy–Schwarz give $0\leq\mathbb E a\leq1$, so
$$
0\leq P_*-\int_0^T\mathbb E[a(t,X_t)]\,dt\leq1-T.
$$

The gradient-martingale and value methods have antecedents in
[Montanari, preprint v2, Lemmas 3.2–3.4][Montanari], under its
positive-temperature support assumption, and in the zero-temperature
calculations of [El Alaoui, Montanari and Sellke, preprint v1,
Lemmas 6.5 and 6.13][EAMS]. [Sellke, preprint v4,
Proposition 3.10 and Lemma 3.11, p. 17][Sellke] gives the closely
related finite-cutoff cancellation by applying Itô's formula to $\Phi$
and $x\Phi_x$.

### 5.2 The classical algorithm

Theorem 1 gives a strictly increasing minimiser in $\mathcal U$, which
is the no-overlap-gap condition, Assumption 2
of [El Alaoui, Montanari and Sellke, preprint v1][EAMS]. Their
Corollary 2.2 then gives, for every fixed $\varepsilon>0$, a randomised
algorithm that returns a configuration within $\varepsilon n$ of the
finite SK maximum with probability tending to one over couplings and
algorithmic randomness. It costs $C(\varepsilon)n^2$ real-arithmetic
operations when the prescribed scalar functions and normalisers are
available. This count includes no separate bound for numerical
preprocessing or finite precision.
[OpenAI (2026a), Corollary 7.3][FS] and the companion, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="classical-algorithm-consequence">[§9.4](../long/reasoning-record.md#classical-algorithm-consequence)</span>,
work out the Gaussian convention and the operation count. Chen already
notes this consequence in [§1, p. 4][Chen]. In the notation of El Alaoui,
Montanari and Sellke the martingale multiplier is $a$ and the drift is
$\gamma u$, and $\mathbb E a^2=1$ is the variance normalisation that
their incremental approximate message passing requires.
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
### 5.3 A fixed QAOA circuit before the thermodynamic limit

Let $\widehat Z_i,\widehat X_i$ be Pauli operators, and define the cost
and mixer by
$$
C_{n,J}=\frac1{\sqrt n}\sum_{i<j}J_{ij}\widehat Z_i\widehat Z_j,
\qquad B_n=\sum_i\widehat X_i.
$$
The eigenvalues of the cost are $H_n(\sigma)$. QAOA alternates cost
evolution and mixing, starting from the uniform state
$|+\rangle^{\otimes n}$ ([Farhi, Goldstone and Gutmann (2014)][FGG]).
For a fixed sequence of angles
$W=(\theta_1,\beta_1,\ldots,\theta_p,\beta_p)$, write
$$
|\psi_{n,J}(W)\rangle
=e^{-i\beta_p B_n}e^{-i\theta_p C_{n,J}}\cdots
 e^{-i\beta_1 B_n}e^{-i\theta_1 C_{n,J}}|+\rangle^{\otimes n},
$$
$$
v(W)=\lim_{n\to\infty}\frac1n\mathbb E_J
\langle\psi_{n,J}(W)|C_{n,J}|\psi_{n,J}(W)\rangle.
$$
[Farhi, Goldstone, Gutmann and Zhou (2022)][FGGZ] established this
limit for fixed angles. [OpenAI (2026b), Theorem 1.1][Q] proves that for
every $\varepsilon>0$ there is one finite $W$ with
$v(W)\geq P_*-\varepsilon$, whose depth and angles depend on
$\varepsilon$ but not on $n$ or $J$. This was conjectured in
[Basso, Farhi, Marwaha, Villalonga and
Zhou (2022), §7, equation (7.2)][BFMVZ]. The order of limits differs
from the fixed-instance depth limit in
[Farhi, Goldstone and Gutmann, §VI][FGG], which permits
instance-dependent choices.

The proof uses Theorem 1 only through the following finite quantity. Fix
the minimiser and its diffusion,
a cutoff $0<T<1$, and a mesh $t_j=j\Delta$ with $\Delta=T/N$.
From independent standard normals $Z_1,\ldots,Z_{N+1}$, form the Euler
scheme and the normalised increments
$$
\begin{aligned}
Y_0&=0,\\
Y_j&=Y_{j-1}+\sqrt\Delta Z_j+
       \Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),\\
h_j&=\frac{a(t_{j-1},Y_{j-1})}
 {\sqrt{\mathbb E a(t_{j-1},Y_{j-1})^2}},\qquad g_j=h_jZ_j
 \quad(1\leq j\leq N),
\end{aligned}
$$
and the randomly rounded spin
$F_N=\operatorname{sgn}\{u(T,Y_N)+2\Phi_{\rm G}(Z_{N+1})-1\}$, where
$\Phi_{\rm G}$ is the standard normal distribution function, so that
$\mathbb E[F_N\mid Z_1,\ldots,Z_N]=u(T,Y_N)$.
[OpenAI (2026a), Proposition 7.2][FS] proves that the denominators
are positive for all sufficiently large $N$ and that
$$
S_{T,N}:=\sum_{j=1}^N
 \mathbb E[F_Ng_j]\,\mathbb E[F_NZ_{j+1}]
\;\longrightarrow\;
I_T:=\int_0^T\mathbb E[a(t,X_t)]\,dt
\qquad(N\to\infty).                                 \tag{12}
$$
Since $h_j$ depends only on $Z_1,\ldots,Z_{j-1}$, the $g_j$ are centred
and orthonormal in $L^2$. The denominators are the counterparts in the
Euler scheme of $\mathbb E a(t,X_t)^2=1$. The proof of (12) is
reconstructed in the companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="finite-gaussian-approximation">[§7](../long/reasoning-record.md#finite-gaussian-approximation)</span>.

**Proposition 6 (circuit approximation; a consequence of
[OpenAI (2026b), §§2–5][Q]).** For each fixed $T,N$ in the preceding
construction with finite positive normalisers, and every $\eta>0$,
there is a finite sequence of angles $W$,
independent of $n$ and $J$, such that
$$
|v(W)-S_{T,N}|<\eta.
$$

We do not reproduce its proof, which occupies the companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="qaoa-construction">[§§8.1–8.6](../long/reasoning-record.md#qaoa-construction)</span>.
Near-optimality follows from the decomposition
$$
P_*-v(W)\leq
 (P_*-I_T)+|I_T-S_{T,N}|+|S_{T,N}-v(W)|.            \tag{13}
$$
Choose $T$ so that $1-T<\varepsilon/3$, then $N$ so that the
second term is below $\varepsilon/3$, and finally apply Proposition 6
with $\eta<\varepsilon/3$. These finite choices give
$v(W)>P_*-\varepsilon$ before $n$ tends to infinity.
The construction gives no bound on the depth or on the
magnitudes of the angles in terms of the accuracy, and no efficient
procedure for finding the angles.

**Corollary 7 (a measured configuration on the same instance).**
For every $\varepsilon>0$ there is a finite sequence of angles
$W_\varepsilon$, chosen independently of $n$ and $J$, such that one
computational-basis measurement $\Sigma$ satisfies
$$
\Pr_{J,\Sigma}\!\left\{
\max_\sigma H_{n,J}(\sigma)-H_{n,J}(\Sigma)\leq\varepsilon n
\right\}\longrightarrow1
\qquad(n\to\infty).                               \tag{14}
$$

**Proof.** For a fixed $W$, put
$Y_n=H_{n,J}(\Sigma)/n$ and
$K_n=\max_\sigma H_{n,J}(\sigma)/n$.
[Farhi, Goldstone, Gutmann and Zhou, §4, equations (13)–(22)][FGGZ]
prove
$$
\mathbb E_{J,\Sigma}Y_n\to v(W),\qquad
\mathbb E_{J,\Sigma}Y_n^2\to v(W)^2.
$$
The second moment is $\mathbb E_J\langle(C_{n,J}/n)^2\rangle$,
so it includes measurement variance as well as disorder fluctuations.
Thus $Y_n\to v(W)$ in joint $L^2$. Gaussian concentration of the
maximum and its defining mean limit give $K_n\to P_*$ in probability.
Choose $W$ with $P_*-v(W)<\varepsilon/3$. With probability tending
to one, both $K_n-P_*<\varepsilon/3$ and
$v(W)-Y_n<\varepsilon/3$, which proves (14). The two energies use
the same $J$, and the argument needs no independence between them.
$\qquad\square$
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## Formal verification

<!-- passage:evidence-scope -->
The proofs above do not rely on the formalisation. OpenAI's
formalisation in [Lean][Lean4] with [mathlib][mathlib] contains two
statements that bear on them. The
[formal statement of full support][support-challenge] asserts the
support and moment conclusions of Theorem 1, with an admissible
minimiser as its hypothesis, and constructs the associated diffusion.
Its [proof][support-lean] includes the rational identity (5) and the
integrated inequality (6). A separate
[formal statement of the scalar consequences][value-challenge] covers
the value identity (11) and the finite Gaussian limit (12), again with
a minimiser as hypothesis, and has its own [proof][value-lean].

Both statements are published as challenges for Comparator, a tool
that checks that a Lean proof establishes a stated theorem. Two
independent reruns report that Comparator accepts OpenAI's proofs of
both:
[MathVet][mathvet-run], on 8 October 2026, and
[C. Toledo][toledo-run], on 10 October 2026, the latter also with a
second proof checker. We rebuilt the proof of full support only
(companion,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="verification">[§13](../long/reasoning-record.md#verification)</span>).

The formalisation has three limitations. Neither formal statement covers
the strict positivity of the density, the inequality at a fixed time
or the convergence of QAOA. The two
statements use separate models of the order parameter, which have not
been related to each other, and the companion compares each with the
printed statement in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="formal-interfaces">[§12](../long/reasoning-record.md#formal-interfaces)</span>.
Finally, in the reading edition of this paper each passage is linked to
Lean declarations. These links were made by AI agents and have not been
checked by a mathematician, and they do not certify that a passage and a
declaration agree.

The identity (5), with Table 1, and the numerical values of §3 are
reproduced by two short scripts,
[one for the identity][check-identity] in exact rational arithmetic and
[one for the solvable case][check-model].
<!-- /passage:evidence-scope -->

## References

- Auffinger, A. and Chen, W.-K. (2015). “On properties of Parisi
  measures.” *Probability Theory and Related Fields* **161**, 817–850.
  [Preprint v1][AC-properties]: Lemma 2 and proof of Theorem 2(ii).
- Auffinger, A. and Chen, W.-K. (2017). “Parisi formula for the ground
  state energy in the mixed $p$-spin model.” *Annals of Probability*
  **45**, 4617–4631. [Preprint v2][AC]: Theorem 1 and proof of Lemma 3.
- Auffinger, A., Chen, W.-K. and Zeng, Q. (2020). “The SK model is
  infinite step replica symmetry breaking at zero temperature.”
  *Communications on Pure and Applied Mathematics* **73**, 921–943.
  [arXiv:1703.06872v2][ACZ]: Theorem 1, Proposition 1 and Remark 7.
- Basso, J., Farhi, E., Marwaha, K., Villalonga, B. and Zhou, L. (2022).
  “The Quantum Approximate Optimization Algorithm at High Depth for
  MaxCut on Large-Girth Regular Graphs and the Sherrington–Kirkpatrick
  Model.” *TQC 2022*, 7:1–7:21. [Full preprint v3][BFMVZ]: transfer
  theorem and §7, equation (7.2); the full preprint has separate numbering.
- Chen, H.-B. (2026). *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [arXiv:2607.18032v1][Chen],
  20 July 2026. §1, p. 4; Theorem 1.3; Propositions 3.2, 3.7, 3.10 and
  3.11; Lemma 3.14; Propositions 4.2, 4.3, 4.5 and 4.6; Remark 4.4.
- Chen, W.-K., Handschy, M. and Lerman, G. (2018). “On the energy
  landscape of the mixed even $p$-spin model.” *Probability Theory and
  Related Fields* **171**, 53–95. [Preprint v4][CHL]: Proposition 2,
  Theorems 4–6, Lemma 3 and Propositions 3–4.
- de Moura, L. and Ullrich, S. (2021). “The Lean 4 Theorem Prover and
  Programming Language (System Description).” *CADE 28*.
  [System description][Lean4].
- El Alaoui, A., Montanari, A. and Sellke, M. (2021). “Optimization of
  mean-field spin glasses.” *Annals of Probability* **49**, 2922–2960.
  [arXiv:2001.00904v1][EAMS]: Theorem 2, p. 6; Remark 2.1 and Theorem 3, p. 7;
  Assumption 2 and Corollary 2.2, p. 8; §§5–6.
- Farhi, E., Goldstone, J. and Gutmann, S. (2014). *A Quantum Approximate
  Optimization Algorithm*. [Preprint v1][FGG]. Algorithm definition;
  §VI concerns the fixed-instance depth limit.
- Farhi, E., Goldstone, J., Gutmann, S. and Zhou, L. (2022). “The Quantum
  Approximate Optimization Algorithm and the Sherrington–Kirkpatrick
  Model at Infinite Size.” *Quantum* **6**, 759. [arXiv:1910.08187v4][FGGZ].
- Jagannath, A. and Tobasco, I. (2016). “A dynamic programming approach
  to the Parisi functional.” *Proceedings of the AMS* **144**, 3135–3150.
  [Preprint v4][JT]. Positive-temperature control methods.
- Jüngel, A. and Matthes, D. (2006). “An algorithmic construction of
  entropies in higher-order nonlinear PDEs.” *Nonlinearity* **19**,
  633–659. [Journal article][JM].
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv:2607.11756v2][Lopatto-v2],
  15 July 2026. Proposition 3.6 and equation (3.39).
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv:2607.11756v3][Lopatto], revised
  16 July 2026. Theorem 1.1; Propositions 7.1 and 9.1.
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv:2607.11756v4][Lopatto-v4], revised
  5 October 2026. Proposition 5.1 and Corollary 5.6; qualitative
  crossing for arbitrary probability measures.
- Lopatto, P. (2026). *Parisi measure of the Sherrington–Kirkpatrick
  model with external field*. [arXiv:2610.00127v1][Lopatto-field].
  Theorem 2.3, §8 and Appendix B.
- The mathlib Community (2020). “The Lean Mathematical Library.”
  *Certified Programs and Proofs (CPP '20)*. [Library description][mathlib].
- Montanari, A. (2025). “Optimization of the Sherrington–Kirkpatrick
  Hamiltonian.” *SIAM Journal on Computing* **54**, FOCS19-1–FOCS19-38.
  [Preprint v2, 2019][Montanari]: §§2–3.
- OpenAI (2026a). *Full support of the zero-temperature Sherrington–Kirkpatrick
  order parameter*. 27 September 2026. [Manuscript][FS], fixed revision.
  Theorem 1.1; §§2–6; Corollaries 6.4 and 7.1; Proposition 7.2.
- OpenAI (2026b). *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*. 25 September 2026. [Manuscript][Q], fixed
  revision. Theorem 1.1; §§2–6 and Appendix A.
- Sellke, M. (2021). *Optimizing Mean Field Spin Glasses with External Field*.
  [Preprint v4][Sellke], 6 October 2021. Proposition 3.10 and
  Lemma 3.11, p. 17.
- Sherrington, D. and Kirkpatrick, S. (1975). “Solvable Model of a Spin-Glass.”
  *Physical Review Letters* **35**, 1792–1796. [Original model][SK].
- Zhou, Y. (2026). “On the Gardner Transition in the Ising Pure p-Spin Glass II”.
  [arXiv:2608.06523v1][zhou-gardner], Appendix E.3, (E.37), (E.41).

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
[value-lean]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16
[value-challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L163
[mathvet-run]: https://github.com/mathvet/mathvet/blob/14c7f918cd336d0da03a02aae5a0eed4a429d4db/reviews/openai-math/challenge-status.csv
[toledo-run]: https://github.com/carlostoledo1891/cert-machine/blob/9814e4c06281e34a113ce853d7d99ccce160b750/certs/openai-math-kernel.json
[check-identity]: https://github.com/wcook04/lean-exposition/blob/main/papers/qaoa-sk/long/check_certificate.py
[check-model]: https://github.com/wcook04/lean-exposition/blob/main/papers/qaoa-sk/short/check_solvable_case.py

[SK]: https://doi.org/10.1103/PhysRevLett.35.1792
[JT]: https://arxiv.org/abs/1502.04398v4
[CHL]: https://arxiv.org/abs/1609.04368v4
[AC-properties]: https://arxiv.org/abs/1303.3573v1
[Montanari]: https://arxiv.org/abs/1812.10897v2
[EAMS]: https://arxiv.org/abs/2001.00904v1
[FGG]: https://arxiv.org/abs/1411.4028v1
[FGGZ]: https://arxiv.org/abs/1910.08187v4
[BFMVZ]: https://arxiv.org/abs/2110.14206v3
[JM]: https://doi.org/10.1088/0951-7715/19/3/006

[certificate]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex#L117-L199

[Lopatto-v2]: https://arxiv.org/abs/2607.11756v2
[Lopatto-v4]: https://arxiv.org/abs/2607.11756v4
[Lopatto-field]: https://arxiv.org/abs/2610.00127v1

[Sellke]: https://arxiv.org/abs/2105.03506v4

[zhou-gardner]: https://arxiv.org/abs/2608.06523v1
