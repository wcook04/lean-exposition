# Full support and positive density in the zero-temperature SK model

*A reconstruction of OpenAI's quantitative argument · 26 October 2026*

<!-- passage:abstract -->
**Abstract.** The Stieltjes measure of every integrable minimiser of the
zero-temperature Parisi functional for the pure, zero-field
Sherrington–Kirkpatrick model has full support on $[0,1)$ and a smooth
density that is strictly positive on $(0,1)$. We reconstruct OpenAI's quantitative
argument, organised around two uses of one spatial-moment inequality.
On a positive constant interval, it makes the derivative of the gradient
second moment strictly convex, contradicting the endpoint conditions
imposed by minimality. The same curvature and the bounded gradient
also exclude terminal gaps. Full support then gives moment identities and
smoothness; a local constant replacement transfers the inequality to the minimiser and
forces its density to be positive. H.-B. Chen previously proved full support
and smooth nonnegative density. We isolate the fixed-time spatial moment
and the positive margin that survives local replacement, while importing its
shape comparisons and full polynomial identity. We also derive the scalar value identity and
state the classical optimisation consequence and the additional steps
leading to asymptotically optimal quantum approximate optimization
algorithm (QAOA) circuits.
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
The limiting ground-state energy per spin, with the maximisation
convention, is
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
$R(\sigma,\tau)=n^{-1}\sum_i\sigma_i\tau_i$. It determines the
energy covariance: $\mathbb E[H_n(\sigma)H_n(\tau)]=nR^2/2-1/2$.
Thus the Gaussian law of the energies is encoded by the overlaps.
We use the covariance convention $\xi(t)=t^2/2$, so $\xi''=1$;
adding one independent centred Gaussian of
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
to one. All support statements use the relative topology of $[0,1)$.
A support gap is a relatively open interval of positive length with
zero mass; the cumulative coefficient is constant on such an interval.

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
The terminal value $|x|$ is the zero-temperature value of one spin
in a field $x$. For an integrable
coefficient, the PDE solution is interpreted by approximation from
bounded monotone coefficients. The exact control
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
The SDE has a unique strong solution. All
stochastic calculations below take place on compact time intervals
ending before one, unless an endpoint limit is justified explicitly.
<!-- /passage:model -->

<!-- passage:main-result -->
[Auffinger, Chen and Zeng (2020), Theorem 1][ACZ] proved infinite
support. This need not be full support: the measure
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$ has infinitely many atoms
and many gaps. [H.-B. Chen (2026), Theorem 1.3][Chen] subsequently proved
full support and smooth nonnegative density. We follow OpenAI's
quantitative proof of the support conclusion and its further
strict-positivity result. The feature used twice is a lower bound
valid throughout every positive constant interval of an admissible
coefficient, without a minimising assumption.

**Theorem 1 (full support; quantitative proof following
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

Corollary 4 in §4 gives the smooth density and its strict positivity
at every interior point.

Existence of a minimiser is a separate input from
[Auffinger and Chen (2017), Theorem 1 and the proof of Lemma 3][AC].
Integrability allows $\gamma$ to grow near one. Zero field gives
$u(0,0)=0$, and $\xi''=1$ is used in the curvature calculation;
the theorem here does not extend these hypotheses to nonzero field
or a general mixed-spin covariance.

Our purpose is to isolate the spatial moment common to the support and
density arguments, explain why it needs an integrated estimate, and
identify what survives the local-replacement limit. The conclusions
and the quantitative method are those of the cited sources.
The proof compares two demands on a gap with two support endpoints.
Minimality forces $q$ to agree with time there, with endpoint slopes
at most one. On a positive constant interval a quantitative estimate
makes $q'$ strictly convex, so its integral is smaller than the
interval's length. This contradicts the required change in $q$.
After excluding all gaps, the identity $q'=1$ supplies the equation
from which the same estimate will force $\gamma'>0$. This second use
needs the estimate for a local constant replacement that need not
minimise, without requiring $q''=0$ at the comparison time. Its explicit
positive margin must also survive the replacement's limit.

Section 5 derives the scalar value formula and identifies the finite
Gaussian observable used by the separate QAOA theorem. These optimisation
consequences use full support; strict density positivity is a further
analytic conclusion. The analytic argument assumes Itô calculus and martingale
convergence. The circuit construction in §5.3 is a separate imported theorem;
we identify its finite input and the energy it approximates. Omitted
proofs are linked to *From Parisi full support to deterministic QAOA
circuits: A long reasoning record*, the <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf">[companion edition of 26 October 2026](../long/reasoning-record.md)</span>; original-source citations remain beside
the imported inputs.
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
temperature and [Auffinger and Chen (2017), Theorem 2 and
Corollary 2][AC] at zero temperature; see also [Chen, Handschy and
Lerman (2018), Proposition 2 and Theorem 5][CHL].

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
the source.

**Proof of Theorem 1, assuming Lemma 2.** A complementary
interval with two support endpoints admits two contact conditions;
an initial interval without support at zero has coefficient zero.
For terminal gaps, the bound $q\leq1$ replaces the missing right
contact condition.

Suppose $(\ell,r)$ is a support gap with endpoints in $S$ and $r<1$.
The coefficient is a positive constant there: support at $\ell$ and
absence of mass immediately to its right force
$\mu_\gamma([0,\ell])>0$. Strict convexity of $q'$ and (2) give
$$
q'(t)<\frac{r-t}{r-\ell}q'(\ell)
       +\frac{t-\ell}{r-\ell}q'(r)\leq1
\qquad(\ell<t<r).
$$
Integrating contradicts $q(r)-q(\ell)=r-\ell$. The geometric
obstruction is an area deficit under $q'$.
An initial gap $[0,r)$ with $0\notin S$ and $r\in S$ has no
mass, hence $\gamma=0$ there. Its right endpoint gives $q(r)=r$
and $q'(r)\leq1$, while zero field gives $q(0)=0$.
The zero-plateau identity gives $q''>0$, hence $q'(t)<q'(r)\leq1$.
The same
integral contradiction follows without assuming $G(0)=0$. A gap
$(0,r)$ with $0\in S$ is already covered by the two-contact case.

A terminal gap $(r,1)$ with nonempty support has $r\in S$ and
positive plateau height. Suppose $q(t)\geq t$ for some $r<t<1$.
Strict convexity of $q'$ and $q'(r)\leq1$ give
$$
t-r\leq\int_r^t q'(s)\,ds
<\frac{t-r}{2}\bigl(q'(r)+q'(t)\bigr),
$$
so $q'(t)>1$. Convexity then gives $q'(s)>q'(t)>1$ for $s>t$.
Consequently $q(s)>t+(s-t)q'(t)>1$ for $s<1$ sufficiently
close to one, contrary to $q\leq1$. Thus $q(t)<t$ on $(r,1)$,
and $G(r)<0$ contradicts minimality. This uses no contact at one.

If $S$ is empty, then $\gamma=0$. Lemma 2 makes $q$ strictly
convex, and $q(0)=0$, $q\leq1$ give, for $0<t<b<1$,
$q(t)<(t/b)q(b)\leq t/b$. Letting $b\uparrow1$ gives
$q(t)\leq t$. Applying strict convexity again with $t<b<1$
now gives $q(t)<(t/b)q(b)\leq t$, so $G(0)<0$.

The terminal exclusion was already recorded by
[Auffinger, Chen and Zeng (2020), Remark 7][ACZ]. The argument
here uses only the curvature needed for the other gaps;
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="qualitative-terminal-gap">[long §5, “A shorter qualitative exclusion”](../long/reasoning-record.md#qualitative-terminal-gap)</span>
gives the full endpoint discussion. The stronger boundary estimate
$1-q(t)\geq C\sqrt{1-t}$ for arbitrary coefficients constant
near one is proved in [OpenAI (2026a), Lemma 6.3][FS] and
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="terminal-gap">[long §5, terminal boundary estimate](../long/reasoning-record.md#terminal-gap)</span>;
[Chen (2026), Proposition 4.5, equations (4.27)–(4.38)][Chen]
gives the square-root asymptotic under the terminal-gap hypothesis.
The zero-coefficient heat argument and late-step variation have
antecedents in [Chen, Handschy and Lerman (2018), Theorem 6][CHL].

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
The quantity used in both arguments is a spatial moment. Write
$b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$, and, for $0<t<1$, set
$$
\mathcal C_\gamma(t)
=\mathbb E\bigl[d^2-12\gamma(t)ab^2+6\gamma(t)^2a^4\bigr],
$$
with the spatial factors evaluated at $(t,X_t)$.
Its definition requires spatial regularity but no time derivative of
$\gamma$. The estimate we need can therefore be stated at one time.

**Proposition 3 (fixed-time spatial-moment estimate).** Let
$\gamma\in\mathcal U$, let $0<t<1$ be a continuity point of $\gamma$,
and suppose that $c=\gamma(t)>0$. For its associated diffusion,
$$
\mathcal C_\gamma(t)\geq\frac{c^2}{1000}
                       \mathbb E[a(t,X_t)^4].
$$
Neither minimality nor a constant neighbourhood of $t$ is required.
This is the consequence of [OpenAI (2026a), Proposition 5.1 and
Lemmas 2.1–2.2][FS] stated in the companion's
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="fixed-time-coercivity">[Proposition 4.1, §4.5](../long/reasoning-record.md#fixed-time-coercivity)</span>.
We first explain the positive-plateau estimate, then obtain this
fixed-time form by inserting a short plateau.

For a smooth coefficient the identity connecting the two applications is
$$
q'''+2\gamma'\mathbb E a^3=\mathcal C_\gamma.
$$
On a plateau, $\gamma'=0$; at a smooth minimiser, full support gives
$q=t$ and hence $q'''=0$. Section 4 proves the required smoothness
before using the second identity.

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
\begin{aligned}
c^2q''&=\mathbb E[w^2-2v^3],\\
c^2q'''&=\mathbb E[z^2-12vw^2+6v^4]
       =c^2\mathcal C_\gamma(t).
\end{aligned}                                      \tag{4}
$$
For example, the drifts of $w^2$ and $v^3$ are
$z^2-6vw^2$ and $3vw^2-3v^4$, respectively. The negative
mixed term is the obstacle. Convexity, which gives $v\geq0$,
does not control it. Indeed, for the smooth auxiliary terminal value
$\log(2\cosh x)$ and coefficient $\gamma\equiv1$, the solution is
$\Phi(t,x)=\log(2\cosh x)+(1-t)/2$. Thus $r=\tanh x$;
at $r^2=1/2$, the polynomial in (4) equals $-19/8$.
This is a finite-step smoothing example, not a minimiser of the
absolute-value-terminal problem; its calculation is given in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="curvature-moments">[long §4.1](../long/reasoning-record.md#curvature-moments)</span>.
The same section gives a negative pointwise value with the actual
$|x|$ terminal datum for a small positive constant coefficient
(<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="pointwise-curvature-obstruction">[long §4.1, pointwise obstruction](../long/reasoning-record.md#pointwise-curvature-obstruction)</span>).

The proof subtracts a weighted divergence whose expectation under the
law of $X_t$ is zero. The resulting expression has a positive
fourth-moment remainder. The backward value function and the forward
density must satisfy joint shape restrictions for this decomposition
to have the required signs. Those comparisons and the exact polynomial
identity are the substantial inputs from
[OpenAI (2026a), §§3–4][FS]. We explain their roles first for finite-step
coefficients, then pass the integrated inequality to an integrable
coefficient by approximation.

Begin with a positive nondecreasing finite-step coefficient $\gamma_{\rm step}$: a function constant
on each interval of a finite partition. Replace the terminal value
$|x|$ by the smooth approximation $M^{-1}\log(2\cosh Mx)$, with
$M\geq\|\gamma_{\rm step}\|_\infty$.
On a step of height $c$, set $h=e^{c\Phi}$. Then
$h_t=-h_{xx}/2$ and $r=h_x/h$. The same exponential removes the
drift from the forward density equation. Indeed, writing $f=hg$ gives
$$
\begin{aligned}
f_t&=\tfrac12(hg)_{xx}-(h_xg)_x\\
   &=-\tfrac12h_{xx}g+\tfrac12hg_{xx}
    =h_tg+\tfrac12hg_{xx}.
\end{aligned}
$$
Comparison with $f_t=h_tg+hg_t$ yields $g_t=g_{xx}/2$.
Thus one backward heat factor and one forward heat factor determine
the law against which the moment polynomial is integrated.
For $s=-\partial_x\log g$,
the source proves joint shape restrictions: on $x>0$, $r_x>0$ and
$s_x\geq1/t$, both $r$ and $s$ are concave, and
$H:=w/(2r)+v\leq0$ is nondecreasing. They also give
$$
j:=s_x-(s/r)v=r\,\partial_x(s/r)\geq0.
$$
The last inequality couples the backward gradient to the forward
density; separate monotonicity and concavity do not supply it.
On the first step, $s=x/t$, so concavity of $r$ gives $j\geq0$.
A parabolic comparison propagates the sign within each step.
At a forward jump with $k=c_+/c_-\geq1$, continuity of $\Phi$ and $f$
gives
$$
r_+=kr_-,\qquad s_+=s_-+(k-1)r_-,\qquad
j_+=(s_x)_+-\frac{s_+}{r_+}(r_x)_+=j_-.
$$
The joint sign therefore survives coefficient jumps as well.
The quotients $w/r$ and $s/r$ extend smoothly through zero because
$r,s,w$ are odd
and $r_x(0)>0$. The comparison's boundary controls and these extensions
are analytic inputs from [OpenAI (2026a), Lemmas 3.2–3.4][FS],
reconstructed in <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="shape-comparisons">[long §4.3](../long/reasoning-record.md#shape-comparisons)</span>.

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
The correction polynomial below is chosen by first arranging a square
and other nonnegative terms containing the highest derivative $z$,
then cancelling their linear terms in $z$ through the weighted divergence.
The residual depends only on lower derivatives and the shape quantities.
[OpenAI (2026a), Lemma 4.1][FS] supplies an explicit polynomial $F_2$
and a decomposition
$$
z^2-12vw^2+6v^4
=\mathcal W(F_2)+\kappa v^4+\mathcal R,
\qquad
\mathcal R\geq0,\qquad
\kappa=\frac{1661507}{1521000000}>\frac1{1000}.
$$
The coefficients of $F_2$ have both signs; no sign of $F_2$ or
$\mathcal W(F_2)$ is needed, since the correction integrates to zero.
In contrast, the shape inequalities make every term of $\mathcal R$
nonnegative. Two of its actual terms are
$$
\frac{337}{10000}\,r^2j\,(-w/r-7v)^2,
\qquad
(2rH_x)v\left(\frac{2331}{10000}r^2+\frac{87}{2500}j\right).
$$
The first needs the joint comparison $j\geq0$; the second also
uses $H_x\geq0$ on the positive half-line. Reflection preserves
these signs on the negative half-line. The remaining terms use
$H\leq0$, forward concavity and the other shape bounds. Thus the
decomposition is positive on the shapes supplied by the PDE, not
on arbitrary spatial derivatives.
Integration removes $\mathcal W(F_2)$ and keeps the fourth-moment
margin, giving
$$
\int_{\mathbb R}(z^2-12vw^2+6v^4)f\,dx
\geq\frac1{1000}\int_{\mathbb R}v^4f\,dx.           \tag{5}
$$
We use (5) as an imported analytic estimate. The full polynomial and
its decomposition are in [Lemma 4.1 and Table 1][certificate];
Proposition 4.2 integrates them using the signs and zero boundary
flux supplied by Lemma 3.4. <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="curvature-algebra">[Long §4.4, “How the signs make a correction with zero expectation useful”](../long/reasoning-record.md#curvature-algebra)</span> reproduces the definitions and complete identity.

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
$\Phi_{xx}>0$ on the plateau (see [OpenAI (2026a), Lemma 2.3][FS]). The plateau-preserving approximants and their common strip bounds are
specified in <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="plateau-limit">[long §4.5](../long/reasoning-record.md#plateau-limit)</span>. The zero plateau has the separate
heat identity in Lemma 2. Its strictness uses a positive diffusion
density and the fact that $\Phi_{xxx}$ cannot vanish identically:
an even quadratic profile would contradict the one-Lipschitz bound
and $|x|+O(1)$ growth.

**Passage to a fixed time.** Now let $\gamma\in\mathcal U$ be continuous
at $t\in(0,1)$, with $c=\gamma(t)>0$. For
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
\mathcal C_{\gamma_\delta}(t)
=\mathbb E[d_\delta^2-12c\,a_\delta b_\delta^2+6c^2a_\delta^4]
\geq\frac{c^2}{1000}\mathbb E[a_\delta^4].           \tag{6}
$$
Choose $t<T<T_1<1$. Monotonicity gives the common coefficient bound
$$
\sup_{s\leq T_1}\gamma_\delta(s)
\leq\frac{\|\gamma_\delta\|_1}{1-T_1}.
$$
This is the first uniform estimate; the spatial derivative bounds require
the smoothing theorem. Lemma 2.1 of [OpenAI (2026a)][FS]
gives uniform convergence in space and uniform bounds for
$a_\delta,b_\delta,d_\delta$ on $[0,T]$, with the next spatial
derivatives bounded as well. Lemma 2.2 couples the diffusions using
the same Brownian motion and gives
$\sup_{s\leq T}|X_s^\delta-X_s|\to0$. The derivative bounds control
evaluation on these paths, so the integrands in (6) converge and
are uniformly bounded. Dominated convergence passes their expectations
to the limit. The common coefficient $L^1$ bound and the fixed distance
from time one determine these estimates; the shrinking plateau width
does not. The result is
$\mathcal C_\gamma(t)\ge\gamma(t)^2\mathbb E a^4/1000$.
This proves Proposition 3. No time derivative of the
coefficient or minimising assumption has entered the limit.

A qualitative crossing criterion already suffices for a bounded gap:
if $q''=0$ implies $q'''>0$, then $q'$ cannot attain an interior
maximum. The endpoint slope bounds therefore give $q'<1$ inside
the gap and the same strict area deficit. Proposition 3 supplies more
for the next argument: it applies at the chosen comparison time
without assuming $q''=0$, and its fourth-moment lower bound survives
the local replacement. Bare strict positivity could be lost in that
limit.
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
moments and then gives smoothness. Only afterwards do we apply
the fixed-time spatial estimate to obtain
$\gamma'>0$.

**Corollary 4 (smooth positive density; [OpenAI (2026a),
Corollary 6.4][FS]).** Under the hypotheses of Theorem 1,
$\gamma(0)=0$ and $\gamma\in C^\infty([0,1))$, with derivatives
at zero taken from the right. Its Stieltjes measure is
$\mu_\gamma(dt)=\gamma'(t)\,dt$, and
$$
2\gamma'(t)\mathbb E[a(t,X_t)^3]
\geq\frac{\gamma(t)^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(0<t<1).                                    \tag{7}
$$
Only nonnegativity of the density at zero is asserted.

**Proof.** All spatial factors in expectations below are evaluated at $(t,X_t)$.
Since
$da=-\gamma a^2\,dt+b\,dB$, Itô's formula applied to $a^2$ gives, for almost every $t$,
$0=\frac{d}{dt}\mathbb E a^2=\mathbb E b^2-2\gamma\mathbb E a^3$.
Here the left side vanishes because full support gives $\mathbb E a^2=1$.
Solving for the coefficient yields
$$
\gamma(t)=\frac{\mathbb E b^2}{2\mathbb E a^3}.      \tag{8}
$$
Initially (8) holds almost everywhere. Its denominator is at least
two, because $a\geq0$ and
$\mathbb E a^3\geq(\mathbb E a^2)^{3/2}=1$.
The moments are continuous; right continuity of $\gamma$ extends
(8) to every time and proves continuity of $\gamma$. Evenness
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
The integral identity then makes all moments $C^1$, and (8) makes
$\gamma$ $C^1$. Repetition proves smoothness. This is the
quotient-and-moment argument of [Chen (2026), Proposition 4.6
and Appendix B.6][Chen], using the polynomial-moment method of
[Auffinger and Chen (2015), Lemma 2 and the proof of Theorem 2(ii)][AC-properties].
The explicit polynomials and the passage from initially nonsmooth
coefficients are in [OpenAI (2026a), proof of Corollary 6.4][FS]
and <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="smooth-density-consequence">[long §9.1](../long/reasoning-record.md#smooth-density-consequence)</span>.

Now the two differentiated moments are
$$
\frac{d}{dt}\mathbb E b^2=\mathbb E[d^2-6\gamma ab^2],
\qquad
\frac{d}{dt}\mathbb E a^3=\mathbb E[3ab^2-3\gamma a^4].
$$
For a smooth time coefficient, differentiating
$q''=\mathbb E b^2-2\gamma\mathbb E a^3$ therefore gives
$$
q^{(3)}+2\gamma'\mathbb E a^3
=\mathcal C_\gamma(t).                              \tag{9}
$$
This identity displays the two uses of the same spatial moment.
On a plateau, $\gamma'=0$ and $(v,w,z)=c(a,b,d)$ recover (4).
For the now smooth minimiser, $q=t$, so $q^{(3)}=0$ and the left
side is $2\gamma'\mathbb E a^3$. Proposition 3 supplies
the lower bound for this spatial moment.

Apply Proposition 3 to the now smooth minimiser. Strict
increase and $\gamma(0)=0$ give $\gamma(t)>0$ for $t>0$; (9)
therefore gives (7). Strictness follows from $\gamma(t)>0$ and
$\mathbb E a^4\geq(\mathbb E a^2)^2=1$.
In particular, Cauchy–Schwarz gives
$$
\mathbb E a^3\leq\sqrt{\mathbb E a^2\,\mathbb E a^4}
=\sqrt{\mathbb E a^4}\leq\mathbb E a^4,
$$
so the same inequality implies
$\gamma'(t)\geq\gamma(t)^2/2000$ for $0<t<1$.

Proposition 3 passes spatial moments, so its proof does not identify
$q_\delta'''$ with the third derivative of the limiting moment.
Indeed the minimiser has $q(t)=t$ and
$q'''=0$; the coefficient derivative in (9) is exactly what the
constant-interval formula omits. <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="smooth-density-consequence">[Long §§9.1–9.2](../long/reasoning-record.md#smooth-density-consequence)</span> retain the smoothness argument and
fixed-time transfer, including the common approximation bounds.

**Relation to earlier estimates.** The backward shape comparisons,
transformed density and positive-temperature gap-crossing argument
appear in [Lopatto (2026), v3, Propositions 3.6, 7.1 and 9.1][Lopatto].
[H.-B. Chen (2026), Proposition 4.2][Chen] proves the zero-temperature
crossing implication $q''=0\Rightarrow q'''>0$ under the minimiser
convention of §3.1. [Lopatto's v4, Proposition 5.1 and
Corollary 5.6][Lopatto-v4] give qualitative crossing for arbitrary
positive-temperature probability measures. In unit-noise coordinates,
their cumulative coefficient is $\gamma_\beta=\beta\alpha_\nu$,
where $\alpha_\nu(t)=\nu([0,t])$, and the terminal value is
$\beta^{-1}\log\cosh(\beta x)$. Every bounded $\gamma\in\mathcal U$
has this form: choose $\beta>0$ with $\beta\geq\sup\gamma$
and put the remaining probability mass at one. Thus the coefficient
classes alone do not distinguish the estimates; the terminal datum and the quantitative
control through its zero-temperature limit matter.

[Lopatto's external-field paper, Theorem 2.3 and §8][Lopatto-field]
also uses a fixed-time spatial inequality for support and positive
density. At a continuity point, monotonicity supplies its one-sided
coefficient bounds; on a smooth full-support interval of the minimiser,
its scalar conditions become equalities. Appendix B gives the positive-temperature,
zero-field strict-density result. The bound used here instead applies at a
nonstationary comparison time and retains an explicit fourth-moment
margin through the local replacement with terminal datum $|x|$.
The rescaling and exact hypothesis comparisons are in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="finite-temperature-dictionary">[long §2.3, finite-temperature dictionary](../long/reasoning-record.md#finite-temperature-dictionary)</span>.
<!-- /passage:density-consequence -->

<a id="value-and-qaoa"></a>

## 5. Consequences for optimisation

<!-- passage:scalar-value -->
### 5.1 A martingale formula for the ground-state value

The support identities give a scalar representation of $P_*$. Set
$M_t=u(t,X_t)$, the bounded gradient martingale satisfying
$dM_t=a(t,X_t)\,dB_t$.
The quadratic variations distinguish the two Hessian moments:
$$
d\langle M\rangle_t=a(t,X_t)^2\,dt,
\qquad d\langle M,B\rangle_t=a(t,X_t)\,dt.
$$
Full support gives $\mathbb E a(t,X_t)^2=1$, hence each increment
$M_t-M_s$ has unconditional variance $t-s$. This normalises the
discrete increments below. The first moment of $a$ instead gives
covariance with the driving noise. Let $U$ be the almost-sure and
$L^2$ limit of $M_t$. The value identity is
$$
P_*=\mathbb E[UB_1]
   =\int_0^1\mathbb E[a(t,X_t)]\,dt.                \tag{10}
$$
Boundedness gives
$|U|\leq1$, while $\mathbb E M_t^2\to1$ gives $\mathbb E U^2=1$;
therefore $U^2=1$ almost surely. To see the cancellation behind (10), the
terminal convergence of the convex value functions gives $UX_1=|X_1|$
(the equality is automatic on $X_1=0$), while Itô's formula gives
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt$.
Multiplying $X_1=B_1+\int_0^1\gamma(t)M_t\,dt$ by $U$ cancels
that integral because $\mathbb E[UM_t]=t$. The Parisi formula then
gives (10). The endpoint limits and stochastic-integral covariance
are proved in [OpenAI (2026a), Corollary 7.1][FS] and the long
record, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="scalar-value-identities">[§6, “Recovering the value from a martingale”](../long/reasoning-record.md#scalar-value-identities)</span>. This argument
uses full support, not the density corollary. In particular, convexity
and Cauchy–Schwarz give $0\leq\mathbb E a\leq1$, so
$$
0\leq P_*-\int_0^T\mathbb E[a(t,X_t)]\,dt\leq1-T.
$$
One can therefore fix the terminal cutoff before discretising the diffusion.

The gradient-martingale and value methods have antecedents in
[Montanari, preprint v2, Lemmas 3.2–3.4][Montanari], under its
positive-temperature support assumption, and in the zero-temperature
calculations of [El Alaoui, Montanari and Sellke, preprint v1,
Lemmas 6.5 and 6.13][EAMS]. [Sellke, preprint v4,
Proposition 3.10 and Lemma 3.11, p. 17][Sellke] gives the closely related
finite-cutoff cancellation by applying Itô's formula to $\Phi$ and $x\Phi_x$.

### 5.2 The classical algorithm

Full support and existence give an attained, strictly increasing
minimiser in the monotone zero-temperature class. This is Assumption 2 of
[El Alaoui, Montanari and Sellke, preprint v1][EAMS]. Their Corollary 2.2
then gives, for every fixed $\varepsilon>0$, a randomised algorithm
returning a configuration within $\varepsilon n$ of the finite SK
maximum with probability tending to one over couplings and algorithmic
randomness. Its cost is $C(\varepsilon)n^2$ real-arithmetic operations
with the prescribed scalar functions and normalisers available; this
includes no separate numerical-preprocessing or finite-precision bound.
[OpenAI (2026a), Corollary 7.3][FS] and <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="classical-algorithm-consequence">[long §9.4](../long/reasoning-record.md#classical-algorithm-consequence)</span>
check the Gaussian convention and operation count. Chen already records
the classical consequence in [§1, p. 4][Chen].
In their incremental approximate message-passing construction, the
noise and drift coefficients are, in our notation,
$$
u_{\rm EAMS}(t,x)=a(t,x),\qquad
v_{\rm EAMS}(t,x)=\gamma(t)u(t,x).
$$
Thus their noise multiplier is the Hessian, whereas our $u$ is the
gradient. The bounded martingale $M_t$ and $\mathbb E a^2=1$ give
the required variance normalisation. With the fixed-strip regularity
and discretisation estimates, [their Theorem 2][EAMS] achieves energy
arbitrarily close to the truncated first-moment integral in (10).
Strict positivity of the density is unnecessary.

<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
### 5.3 A fixed QAOA circuit before the thermodynamic limit

The remaining consequence uses a separate circuit approximation theorem,
stated as Proposition 5 below. We give its finite Gaussian input and
identify the energy it approximates. Its operator and control
construction is developed in the companion; the support and density
proofs above do not require those additional prerequisites.

Let $\widehat Z_i,\widehat X_i$ be Pauli operators, and define the cost
and mixer by
$$
C_{n,J}=\frac1{\sqrt n}\sum_{i<j}J_{ij}\widehat Z_i\widehat Z_j,
\qquad B_n=\sum_i\widehat X_i.
$$
The cost eigenvalues are $H_n(\sigma)$. QAOA alternates cost evolution
and mixing from the uniform state $|+\rangle^{\otimes n}$
([Farhi, Goldstone and Gutmann (2014)][FGG]). For a fixed sequence
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
fixed-angle limit. [OpenAI (2026b), Theorem 1.1][Q] proves that for
every $\varepsilon>0$ there is one finite $W$ with
$v(W)\geq P_*-\varepsilon$, whose depth and angles depend on
$\varepsilon$ but not on $n$ or $J$. The instance still determines
$C_{n,J}$. Here depth counts global cost–mixer layers; their elementary
gate counts depend on the implementation. This order of limits differs
from the fixed-instance depth limit in [Farhi, Goldstone and Gutmann,
§VI][FGG], which permits instance-dependent choices. The common-circuit
conclusion was conjectured by [Basso, Farhi, Marwaha, Villalonga and
Zhou (2022), §7, equation (7.2)][BFMVZ].

**The finite Gaussian input.** Fix the minimiser and its diffusion,
a cutoff $0<T<1$, and a mesh $t_j=j\Delta$, $\Delta=T/N$.
The mesh count $N$ is distinct from the number of spins $n$.
From independent standard normals $Z_1,\ldots,Z_{N+1}$, form
$$
\begin{aligned}
Y_0&=0,\\
Y_j&=Y_{j-1}+\sqrt\Delta Z_j+
       \Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),\\
h_j&=\frac{a(t_{j-1},Y_{j-1})}
 {\sqrt{\mathbb E a(t_{j-1},Y_{j-1})^2}},\qquad g_j=h_jZ_j
 \quad(1\leq j\leq N).
\end{aligned}
$$
[OpenAI (2026a), Proposition 7.2][FS] proves that the denominators
are positive for all sufficiently large $N$. Since $h_j$ depends
only on $Z_1,\ldots,Z_{j-1}$, the $g_j$ are centred and
orthonormal in $L^2$. They need not be independent Gaussians.
With $\Phi_{\rm G}$ the standard normal distribution function, set
$$
\begin{aligned}
F_N&=\operatorname{sgn}\{u(T,Y_N)+2\Phi_{\rm G}(Z_{N+1})-1\},\\
\mathbb E[F_N\mid Z_1,\ldots,Z_N]&=u(T,Y_N).
\end{aligned}
$$
The second equality follows because $\Phi_{\rm G}(Z_{N+1})$ is
uniform on $[0,1]$: this random rounding preserves every correlation
with a function of the preceding coordinates. The finite quantity
needed by the circuit construction is the adjacent pairing
$$
\begin{aligned}
S_{T,N}&:=\sum_{j=1}^N
 \mathbb E[F_Ng_j]\,\mathbb E[F_NZ_{j+1}],\\
\lim_{N\to\infty}S_{T,N}
&=I_T:=\int_0^T\mathbb E[a(t,X_t)]\,dt.
\end{aligned}                                      \tag{11}
$$
The same proposition proves this limit. The Euler approximation and
the gradient martingale give
$$
\left\|u(T,Y_N)-\sum_{j=1}^N\sqrt\Delta\,
 a(t_{j-1},Y_{j-1})Z_j\right\|_2\longrightarrow0.
$$
Conditional-mean preservation transfers these correlations to $F_N$
for the first $N$ coordinates. Rounding itself has squared $L^2$
error $\mathbb E(F_N-u(T,Y_N))^2\to1-T$, so it is not the
vanishing residual. Bessel's inequality, applied separately to $(g_j)$
and $(Z_j)$, controls the errors of both correlation vectors in $\ell^2$.
Their bounded norms control the growing pairing by Cauchy–Schwarz.
The terms with $j<N$ give a Riemann sum, and the last
rounding-coordinate term vanishes. All these limits keep $T$
fixed; only afterwards does $T\uparrow1$ give $P_*$.
The construction and estimates are in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="finite-gaussian-approximation">[long §7, “A finite Gaussian spin and its adjacent correlations”](../long/reasoning-record.md#finite-gaussian-approximation)</span>.

**Proposition 5 (circuit approximation; a consequence of
[OpenAI (2026b), §§2–5][Q]).** For each fixed $T,N$ in the preceding
construction with finite positive normalisers, and every $\eta>0$,
there is a finite ordinary QAOA word $W$, with deterministic angles
independent of $n$ and $J$, such that
$$
|v(W)-S_{T,N}|<\eta.
$$

**Why the adjacent pairing is the energy.** We use the rooted Gaussian
representation of [OpenAI (2026b), §2 and Lemma 3.1][Q], building on
the spin–boson description of [Boulebnane et al. (2026)][spin-boson].
Its classical sector consists of square-integrable functions built
recursively from a local Gaussian seed and child-generated Gaussian
coordinates, with inner product given by expectation.
A centred real child direction $f$ gives a Gaussian coordinate
$\mathsf G(f)$ at the receiving root, with
$$
\mathbb E[\mathsf G(f)\mathsf G(g)]=\langle f,g\rangle.
$$
The receiving root's seed is independent of these coordinates;
compatible embeddings preserve them as the recursive depth grows.
The root shift $\mathsf L$ inserts a child direction into the first
Gaussian chaos (the linear Gaussian part) with constant receiving-root
state. Its adjoint projects onto that part and returns the child direction. The
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="depth-one-calibration">[depth-one calculation in long §8.1.1](../long/reasoning-record.md#depth-one-calibration)</span>
checks this representation's energy against the finite SK circuit
before the general construction in §8.1.

Start with a standard normal receiving-root seed $g_0$ and recursively put
$Z_{j+1}=\mathsf G(g_j)$. The orthonormal child directions give
independent standard Gaussian lifts, reproducing the scalar law.
The finite spin $F_N$ depends only on those lifts. Projection therefore
gives the exact rooted-energy identity
$$
\begin{aligned}
\mathsf L^*F_N&=\sum_{j=0}^N\mathbb E[F_NZ_{j+1}]g_j,\\
\mathcal E(F_N):=\operatorname{Re}\langle F_N,\mathsf L F_N\rangle
&=\sum_{j=0}^N\mathbb E[F_Ng_j]\,\mathbb E[F_NZ_{j+1}]
 =S_{T,N}.
\end{aligned}                                     \tag{12}
$$
Independence of the receiving-root seed removes the $j=0$ term.
This identity concerns the finite Gaussian formula in a limiting
rooted space, not a finite-$n$ circuit. The unshifted pairing can
have the same scalar limit without identifying this energy.
The construction and projection are proved in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="rooted-energy">[long §8.1](../long/reasoning-record.md#rooted-energy)</span>.

**Construction underlying Proposition 5.** Smooth approximation of the final sign, followed by
Lemma 3.2, gives a bounded smooth odd formula with bounded transmitted
functions; smoothing the sign alone is insufficient. Definition 3.3
and Lemma 3.4 then partition the seed into classes and exclude
the receiving seed class, its path-ancestor classes and all reserved
helper classes from each dependency, preventing return through an
already traversed branch. The output is zero on helper classes,
one per positive aggregation depth, whose total probability is small
but positive during synthesis.

Theorem 4.1 realises the prepared formula with temporary Gaussian
controls, reusing the same sitewise seeds throughout the word.
Theorem 5.1 removes these controls with arbitrarily small energy
error, and Proposition 2.1 identifies the fixed ordinary word's
limiting energy with $v(W)$. All these errors are absolute, so the
argument applies to each fixed $S_{T,N}$, before it is chosen close
to $P_*$. The output preserved by Proposition 5 is energy;
the measured-configuration conclusion below uses a further
concentration theorem. The complete error bound is in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="finite-formula-energy-error">[long §8.6, finite-formula energy approximation](../long/reasoning-record.md#finite-formula-energy-error)</span>,
with the constructions and their hypotheses in
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="qaoa-construction">[long §§8.1–8.6](../long/reasoning-record.md#qaoa-construction)</span>.

The deduction of near-optimality is now explicit:
$$
P_*-v(W)\leq
 (P_*-I_T)+|I_T-S_{T,N}|+|S_{T,N}-v(W)|.            \tag{13}
$$
Choose $T$ so that $1-T<\varepsilon/3$, then $N$ so that the
second term is below $\varepsilon/3$, and finally use Proposition 5
with $\eta<\varepsilon/3$. These finite choices give
$v(W)>P_*-\varepsilon$ before $n$ tends to infinity. The source's
Appendix A supplies an alternative positive-temperature input to the
same synthesis. The selected construction supplies no quantitative
depth bound, finite-size rate or efficient procedure for finding angles.

**Corollary 6 (a measured configuration on the same instance).**
For every $\varepsilon>0$ there is a finite ordinary QAOA word
$W_\varepsilon$, chosen independently of $n$ and $J$, such that one
computational-basis measurement $\Sigma$ satisfies
$$
\Pr_{J,\Sigma}\!\left\{
\max_\sigma H_{n,J}(\sigma)-H_{n,J}(\Sigma)\leq\varepsilon n
\right\}\longrightarrow1
\qquad(n\to\infty).                               \tag{14}
$$

**Proof.** For a fixed word, put
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
the same $J$; no independence between them is needed.
The companion's
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="fixed-word-probability">[§11.2, “What is averaged, and a fixed-word probability consequence”](../long/reasoning-record.md#fixed-word-probability)</span>
gives the concentration argument and its further probability consequences.
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## Formal scope

<!-- passage:evidence-scope -->
This AI-assisted article reconstructs the cited analytic arguments.
The integrated estimate (5), its shape hypotheses and compact-strip
approximation are substantial imported inputs.

The [full-support formal statement][support-challenge]
asserts the support and moment conclusions conditional on an admissible
minimiser, and constructs its associated diffusion. A separate
[scalar formal statement][value-challenge] covers value identities and
finite Gaussian approximation, with minimiser and diffusion premises
for those clauses. Its third clause identifies the ground-state and
Parisi values from a minimiser, constructing the diffusion internally.
The two formal models have not been transported
into one another in this record. Neither statement includes the
positive-density corollary or QAOA convergence. Their
[full-support][support-lean] and [scalar][value-lean] implementations
use [Lean][Lean4] and [mathlib][mathlib].

Acceptance by Comparator and extraction of the selected formal
statements remain unknown. Source inspection alone establishes neither.
Exact versions, checking outcomes and correspondence are retained in the
long record's <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="formal-interfaces">[§12, “What the formal statements establish”](../long/reasoning-record.md#formal-interfaces)</span> and <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="verification">[§13, “Source checks and finite calculation”](../long/reasoning-record.md#verification)</span>.
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
  [Preprint v2][ACZ]: Theorem 1 and Remark 7.
- Basso, J., Farhi, E., Marwaha, K., Villalonga, B. and Zhou, L. (2022).
  “The Quantum Approximate Optimization Algorithm at High Depth for
  MaxCut on Large-Girth Regular Graphs and the Sherrington–Kirkpatrick
  Model.” *TQC 2022*, 7:1–7:21. [Full preprint v3][BFMVZ]: transfer
  theorem and §7, equation (7.2); the full preprint has separate numbering.
- Boulebnane, S., Khan, A., Liu, M., Larson, J., Herman, D., Shaydulin, R.
  and Pistoia, M. (2026). *Spin–Boson Mapping of the Quantum Approximate
  Optimization Algorithm*. [Preprint v2][spin-boson]: Theorem 2
  (informal) and equations (10)–(11).
- Chen, H.-B. (2026). *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][Chen],
  20 July 2026. §1, p. 4; Theorem 1.3; Propositions 4.2, 4.5 and 4.6;
  Appendices B.6 and C.
- Chen, W.-K., Handschy, M. and Lerman, G. (2018). “On the energy
  landscape of the mixed even $p$-spin model.” *Probability Theory and
  Related Fields* **171**, 53–95. [Preprint v4][CHL]: Proposition 2,
  Theorem 5, Lemma 3 and Propositions 3–4.
- de Moura, L. and Ullrich, S. (2021). “The Lean 4 Theorem Prover and
  Programming Language (System Description).” *CADE 28*.
  [System description][Lean4].
- El Alaoui, A., Montanari, A. and Sellke, M. (2021). “Optimization of
  mean-field spin glasses.” *Annals of Probability* **49**, 2922–2960.
  [Preprint v1][EAMS]: Theorem 2, p. 6; Remark 2.1 and Theorem 3, p. 7;
  Assumption 2 and Corollary 2.2, p. 8; §§5–6.
- Farhi, E., Goldstone, J. and Gutmann, S. (2014). *A Quantum Approximate
  Optimization Algorithm*. [Preprint v1][FGG]. Algorithm definition;
  §VI concerns the fixed-instance depth limit.
- Farhi, E., Goldstone, J., Gutmann, S. and Zhou, L. (2022). “The Quantum
  Approximate Optimization Algorithm and the Sherrington–Kirkpatrick
  Model at Infinite Size.” *Quantum* **6**, 759. [Preprint v4][FGGZ].
- Jagannath, A. and Tobasco, I. (2016). “A dynamic programming approach
  to the Parisi functional.” *Proceedings of the AMS* **144**, 3135–3150.
  [Preprint v4][JT]. Positive-temperature control methods.
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv version 3][Lopatto], revised
  16 July 2026. Propositions 3.6, 7.1 and 9.1; related Cole–Hopf, density
  and crossing arguments.
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv version 4][Lopatto-v4], revised
  5 October 2026. Proposition 5.1 and Corollary 5.6; qualitative
  crossing for arbitrary probability measures.
- Lopatto, P. (2026). *Parisi measure of the Sherrington–Kirkpatrick
  model with external field*. [arXiv version 1][Lopatto-field].
  Theorem 2.3 and Appendix B; related positive-temperature two-use argument.
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

[Lopatto-v4]: https://arxiv.org/abs/2607.11756v4
[Lopatto-field]: https://arxiv.org/abs/2610.00127v1

[Sellke]: https://arxiv.org/abs/2105.03506v4

[spin-boson]: https://arxiv.org/abs/2505.07929v2
