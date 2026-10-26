---
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
    \usepackage{needspace}
---

# Why the SK order parameter has no gaps

## A variational argument from contact to strict curvature

Expository draft, 26 October 2026

<!-- passage:opening -->
The Sherrington–Kirkpatrick (SK) model asks us to choose signs that
maximise a random sum of pair interactions. The Parisi formula expresses
the limiting maximum through a nondecreasing function, the **order
parameter**. We explain why a minimising order parameter cannot be
constant on any interval below one.

The proof compares two consequences of a hypothetical gap. Minimality
fixes the values and bounds the slopes of an auxiliary curve at its
endpoints. An analytic estimate makes the derivative strictly convex
between them, leaving too little area to connect the required values.
Initial and terminal gaps need separate arguments. We then return to
the spins: a theorem about their energies gives nearly optimal sign
choices differing on any prescribed positive fraction of positions up to one half,
with arbitrarily small error in that fraction.

We follow the quantitative proof in [OpenAI (2026a)][support-manuscript];
[Hong-Bin Chen (2026), Theorem 1.3][chen-support] had already proved
full support by a different method. The estimate used here makes the
final contradiction a direct comparison of areas. We assume algebra
and elementary calculus, and introduce probability and cumulative mass
through calculations. The deeper analytic facts are stated where the
proof needs them. By the end of Sections 1–6, the reader should be able
to reconstruct how minimality and those inputs exclude each kind of gap,
then translate the result into a statement about spin configurations.
Section 7 gives optional calculations and answers to the short questions
in the text; the full analytic proofs remain in the cited sources.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. The finite optimisation problem

At each of $n$ positions, or **sites**, we choose a sign $\sigma_i\in\{-1,1\}$,
called a **spin**. A configuration is the vector
$\sigma=(\sigma_1,\ldots,\sigma_n)$.
For each unordered pair choose an independent standard Gaussian
$J_{ij}$, a normal random variable with mean zero and variance one.
Independence means that learning the other couplings does not change
the probability distribution of this one.
These coefficients, or **couplings**, are drawn once and then held
fixed while we maximise the energy, or **Hamiltonian**,

$$
H_n(\sigma)=\frac1{\sqrt n}\sum_{1\le i<j\le n}J_{ij}\sigma_i\sigma_j.
$$

A positive coupling rewards equal signs; a negative one rewards opposite
signs. For example, positive couplings on pairs $12$ and $23$ favour
$\sigma_1=\sigma_2=\sigma_3$, which conflicts with a negative coupling
on pair $13$. This inability to maximise every pair's contribution
simultaneously is called **frustration**. The factor $n^{-1/2}$ fixes
the model's scale.

For two spins, $H_2(\sigma)=J_{12}\sigma_1\sigma_2/\sqrt2$.
Choosing equal or opposite signs according to the sign of $J_{12}$ gives
$\max_\sigma H_2(\sigma)=|J_{12}|/\sqrt2$.

\Needspace{9\baselineskip}

To average over the couplings, we first need their probabilities.
A **probability density** assigns probability by area. For a standard
Gaussian random variable $Z$, the density is
$\varphi(z)=(2\pi)^{-1/2}e^{-z^2/2}$; it is nonnegative, has total
integral one, and for $a\le b$ gives

$$
\Pr(a\le Z\le b)=\int_a^b\varphi(z)\,dz.
$$

In particular, a single point has probability zero. The density's height
is not the probability of that point. To average a score $f(Z)$, weight
it by this same density. Its **expectation** is

$$
\mathbb E f(Z)=\int_{\mathbb R}f(z)\varphi(z)\,dz.
$$

For the standard Gaussian, $\mathbb EZ=0$ and $\mathbb EZ^2=1$.
For a mean-zero random variable, its **variance** is this mean square;
thus $\sqrt h Z$ has variance $h$ for $h>0$. Symmetry gives the zero mean, whereas
$\mathbb E|Z|=2\int_0^\infty z\varphi(z)\,dz=\sqrt{2/\pi}$.
Thus the expected two-spin maximum is $1/\sqrt\pi$. For any signs
chosen before seeing the coupling, the expected energy is instead zero.
The order matters: we choose signs for each realised coupling, then average
the achieved maximum. For many spins, we seek the limiting expected
maximum **per spin**,

$$
P_*:=\lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma),
$$

where expectation averages over the couplings after taking the maximum.
**Zero temperature**, or **ground-state value**, refers here to this
maximisation problem. The model is **pure** because every term contains
exactly two spins, and has **zero external field** because there is
no additional term $h\sum_i\sigma_i$.

The maximum is one question; the arrangement of nearly optimal choices
is another. To compare two configurations for the *same couplings*,
define their **overlap**
$R(\sigma,\tau)=n^{-1}\sum_i\sigma_i\tau_i$, their average agreement
with a disagreement counted as $-1$. If they disagree at $k$ positions,
then $R=1-2k/n$. For example, $(+,+,+,+)$ and $(+,+,+,-)$ have
overlap $1/2$; two disagreements would give zero. We will ask whether
two nearly optimal configurations can differ on roughly one quarter
of their sites, and more generally at any prescribed fraction up to
one half.

Our normalisation gives the covariance function $\xi(t)=t^2/2$ in the
variational problem below. **Optional normalisation calculation.**
For fixed $\sigma,\tau$, put $v_i=\sigma_i\tau_i$. When we expand the product
of energies, different couplings have mean product zero by independence
and their zero means; a coupling multiplied by itself has mean one.
Together with $v_i^2=1$, this gives

$$
\mathbb E[H_n(\sigma)H_n(\tau)]
=\frac1n\sum_{i<j}v_iv_j
=\frac{(\sum_i v_i)^2-n}{2n}
=\frac n2 R(\sigma,\tau)^2-\frac12.
$$

Dividing by $n$ gives the limiting covariance
$\xi(t)=t^2/2$. For exact covariance
$n\xi(R)$, add the same independent centred Gaussian of variance $1/2$
to every energy; this leaves the expected maximum unchanged.

**Back to the spin question.** Reversing one configuration's signs
preserves its energy and reverses its
overlap with another. We next define deterministic candidate values
indexed by nonnegative overlap scales $t$. The Parisi theorem in
Section 3 identifies their minimum with the limiting spin optimum;
that connection is an external input, not a change of variables in
the finite maximisation.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

A candidate order parameter records accumulated weight. Begin with a
finite example: place weight two at scale $1/4$ and weight one at scale
$3/4$. The cumulative function is zero, then two, then three:

$$
\gamma(t)=
\begin{cases}
0,&0\le t<1/4,\\
2,&1/4\le t<3/4,\\
3,&3/4\le t<1.
\end{cases}
$$

Its area is $2(1/2)+3(1/4)=7/4$. We can count the same area by following
each weight: the first persists for three quarters of the interval and
the second for one quarter, giving $2(3/4)+1(1/4)=7/4$ again.
Write $\delta_s$ for one unit of mass at $s$ and
$\mu=2\delta_{1/4}+\delta_{3/4}$ for these weights. Integration against
this measure is a weighted sum:

$$
\int F(s)\,\mu(ds)=2F(1/4)+F(3/4).
$$

The weights total three, so this integral is not a probability average.
We will reuse this accounting when each weight has a cost.

In general, an admissible **order parameter** is a function
$\gamma:[0,1)\to[0,\infty)$ that is nondecreasing, right-continuous
and has finite integral. Right-continuity includes a jump's new value
at the scale where the jump occurs, as in the example. The associated
**Stieltjes measure** records the increments:

$$
\mu_\gamma([0,t])=\gamma(t),\qquad
\mu_\gamma((a,b])=\gamma(b)-\gamma(a).
$$

These cumulative values determine the measure uniquely. The first
equation permits mass $\gamma(0)$ at zero. Mass concentrated at one
point is an **atom**. The weights need not be probabilities of
finite-system overlaps, and their total need not be one or even finite.
They are finite on each $[0,T]$ with $T<1$. Admissibility requires
instead the weighted finiteness

$$
\int_0^1\gamma(t)\,dt
=\int_{[0,1)}(1-s)\,\mu_\gamma(ds)<\infty.
$$

This is the same two ways of counting area as above: a unit at $s$
contributes at every later time, for a total length $1-s$. The general
identity uses the integration theorem that nonnegative contributions
may be summed in either order. A mass at one would change none of the
cumulative values below one, so one is excluded from the domain.

The **support** consists of points whose every neighbourhood carries
positive mass. A neighbourhood here is an interval around the point,
clipped to $[0,1)$. Full support means
that every nonempty relative open interval carries mass. Equivalently,
$\gamma$ is strictly increasing: full support gives a positive increment
on each $(a,b]$ with $a<b$, and a positive increment on a smaller interval
inside any neighbourhood gives positive mass there.

\Needspace{13\baselineskip}

For example, the admissible candidate

$$
\gamma(t)=
\begin{cases}
t,&0\le t\le1/3,\\
1/3,&1/3\le t\le2/3,\\
t-1/3,&2/3\le t<1
\end{cases}
$$

has zero increment from $2/5$ to $3/5$, but increment $1/8$ from
$1/8$ to $1/4$. Its measure has density one outside $(1/3,2/3)$
and zero inside: the mass of a set is the integral of this density
there. Both endpoints of the gap remain in the support because every
neighbourhood of either reaches a region carrying positive mass. The upper curve in Figure 1 stays positive across the gap;
it is its *increments* that vanish. This candidate has infinitely many
support points, including points arbitrarily close to one, yet still
has a middle gap. Those two weaker properties do not give full support.

```{=latex}
% Modified 2026-10-25. Derived from OpenAI/math Figure 1 (Apache-2.0).
% Axes and dotted guides adapt the pinned build/gap-convexity.tex
% in examples/qaoa-sk/upstream/preprints/Full-support-of-the-zero-temperature-
% Sherrington-Kirkpatrick-order-parameter-September-27-2026/.
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[x=1cm,y=.8cm,font=\small,line cap=round]
  \fill[black!6] (2.666667,0) rectangle (5.333333,2.9);
  \draw[->] (-.45,0) -- (8.5,0) node[right] {$t$};
  \draw[->] (0,-.05) -- (0,3.15) node[above] {$\gamma(t)$};
  \draw[densely dashed,gray!70] (0,1.333333) -- (5.333333,1.333333);
  \draw[very thick] (0,0) -- (2.666667,1.333333)
    -- (5.333333,1.333333) -- (8,2.666667);
  \fill[white] (8,2.666667) circle (2.3pt);
  \draw (8,2.666667) circle (2.3pt);
  \node[left] at (0,1.333333) {$1/3$};
  \node[left] at (0,2.666667) {$2/3$};
  \node at (4,2.2) {positive but flat};
  \node[below left] at (0,0) {$0$};
  \foreach \x/\lab in {2.666667/{1/3},5.333333/{2/3},8/{1}}
    {\draw (\x,0) -- (\x,-.08); \node[below=3pt] at (\x,0) {$\lab$};}
  \begin{scope}[yshift=-3.45cm]
    \fill[black!6] (2.666667,0) rectangle (5.333333,1.85);
    \fill[black!18] (0,0) rectangle (2.666667,1.35);
    \fill[black!18] (5.333333,0) rectangle (8,1.35);
    \draw[->] (-.45,0) -- (8.5,0) node[right] {$t$};
    \draw[->] (0,-.05) -- (0,1.95) node[above] {density of $\mu_\gamma$};
    \draw[very thick] (0,1.35) -- (2.666667,1.35);
    \draw[very thick] (2.666667,0) -- (5.333333,0);
    \draw[very thick] (5.333333,1.35) -- (8,1.35);
    \draw[dotted,gray!80] (2.666667,0) -- (2.666667,1.35);
    \draw[dotted,gray!80] (5.333333,0) -- (5.333333,1.35);
    \fill[white] (8,1.35) circle (2.3pt);
    \draw (8,1.35) circle (2.3pt);
    \node[left] at (0,1.35) {$1$};
    \node at (4,.8) {no mass here};
    \node[below left] at (0,0) {$0$};
    \foreach \x/\lab in {2.666667/{1/3},5.333333/{2/3},8/{1}}
      {\draw (\x,0) -- (\x,-.08); \node[below=3pt] at (\x,0) {$\lab$};}
  \end{scope}
\end{tikzpicture}
\caption{The same candidate in two representations. The upper curve is the
piecewise-linear $\gamma$ from Section 2; the lower plot shows the density
of its Stieltjes measure. On $(1/3,2/3)$ the cumulative value stays positive
while its increments vanish. The endpoints $1/3$ and $2/3$ still belong
to the support: every neighbourhood of either contains positive mass.
The lower density belongs to this example; a general Stieltjes measure
need not have one. Open circles mark the excluded endpoint $1$.
The candidate is not a computed minimiser. Axes and guides adapt
OpenAI (2026a), Figure 1; the paired example is constructed here.}
\label{fig:support-increments}
\end{figure}
```

A constant candidate $\gamma(t)=c>0$ makes the distinction sharper:
its measure is $c\delta_0$, supported only at zero. Positivity of the
function is not the conclusion we seek. Nor does full support alone
assert a density: a measure with summable positive masses at a dense countable
set has full support. The further-reading note returns to the stronger
density conclusion.

<a id="question-1"></a>

**Question 1: allowed changes.** Return to the two weights
$2\delta_{1/4}+\delta_{3/4}$. For $0<\varepsilon<1$, which changes
leave an admissible cumulative function: adding $\varepsilon$ mass at
$1/2$, removing it at $1/4$, removing it at $1/2$, or multiplying
both weights by $1-\varepsilon$? Check monotonicity as well as
nonnegativity. [Answer 1](#answer-1).
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

To rule out a candidate, we will look for an allowed change that lowers
its value. Adding mass at one scale changes the cumulative coefficient
at every later scale. We therefore need both a value for each candidate
and a way to compute the cost of that change. The auxiliary optimisation
below supplies the value; its response to the starting state will enter
the first-variation formula in Section 5.1.

### 3.1 First evaluate the zero coefficient

The variational problem assigns each $\gamma$ a value by a one-dimensional
auxiliary optimisation. Its final reward at state $x$ is $|x|$: this is
the best one-spin score $\max_{\sigma\in\{-1,1\}}x\sigma$.
First take $\gamma=0$, when only noise changes the state. The
normalisation $\xi(t)=t^2/2$ gives $\xi''=1$, so the auxiliary noise accumulated over an interval of length $h$ has variance
$h$, the variance of $\sqrt hZ$. Starting at
time $t$ in state $x$, the remaining noise is therefore distributed
as $\sqrt{1-t}Z$. The expected final reward is

$$
\Phi_0(t,x)=\mathbb E|x+\sqrt{1-t}Z|
=\int_{\mathbb R}|x+\sqrt{1-t}z|\varphi(z)\,dz.
$$

At $(t,x)=(0,0)$ this is the calculation already performed:
$\Phi_0(0,0)=\sqrt{2/\pi}$. At $t=1$ no noise remains and the
value is $|x|$. The function gives an expected payoff at a specified
starting state; it is not a probability density.

### 3.2 Allowing a response to the noise

For a general $\gamma$, a response can bias the future state, with a
quadratic cost. Here the overlap scale $t$ plays the role of time;
the path is auxiliary, not a motion of the spins.
The noise is **Brownian motion** $B$: a continuous random path starting
at zero. Its increments over disjoint time intervals are independent;
over an interval of length $h$, an increment has the same distribution
as the centred Gaussian $\sqrt h Z$.

A **control** $\alpha_s\in[-1,1]$ chooses a response at each time
using only noise already observed since the starting time. The whole
deterministic schedule $\gamma$ is known, but future noise is not.
A rule chosen in advance can still give different responses on different
observed paths. To see why this matters,
let a sign $W=\pm1$, each with probability $1/2$, be revealed after
a single choice $v\in[-1,1]$.
The expected score $|W+v|-v^2/2$ is $1-v^2/2$, maximised at $v=0$.
A choice $v=W$ would score $3/2$, but uses information unavailable at
the time of choice. The continuous control problem repeats decisions
with this same restriction; the finite example only illustrates that
restriction.

For a starting position $x$, the value is

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

Inside the absolute value, noise and the accumulated bias change the
state before its final reward is paid. The second integral is the
running control cost.
The supremum chooses the best permitted rule; its formal information
condition is progressive measurability. Expectation now averages over
Brownian paths for a fixed $\gamma$, rather than over spin couplings.
At $\gamma=0$ both control terms vanish, recovering Section 3.1.

The **Parisi functional** subtracts an explicit correction from this
optimised value:

$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
-\frac12\int_0^1t\gamma(t)\,dt.
$$

The inner supremum chooses a response for fixed $\gamma$; the outer
problem minimises $\mathcal P$ over $\gamma$. The ground-state Parisi
formula and attainment give

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

Each candidate supplies an upper bound, and minimisation finds the
sharpest one. This equality and attainment are external inputs from
[Auffinger–Chen (2017), Theorem 1 and the proof of Lemma 3][auffinger-chen];
Gaussian concentration gives the expected-value form used here.
The no-gap theorem assumes a minimiser and proves a property of it.
The value $\mathcal P(0)=\sqrt{2/\pi}$ alone does not establish
that the zero candidate minimises.

### 3.3 The response, the state and the averaged square

First consider the value as a function of the starting state, holding
$t$ and $\gamma$ fixed; we also write $\Phi=\Phi_\gamma$.
For any permitted control, use the same
responses to each Brownian history at two starting states $x$ and $y$.
The costs are unchanged, and the triangle inequality bounds the change
in the terminal reward by $|x-y|$. Taking the supremum over controls gives

$$
|\Phi_\gamma(t,x)-\Phi_\gamma(t,y)|\le |x-y|.
$$

The value is also **convex**: between two states its graph lies at or
below the chord joining their values. Indeed,
each fixed-control payoff is an average of translated absolute-value
functions, hence convex. Its chord lies at or below the chord of the
best endpoint payoffs; taking the supremum preserves that upper bound.

[OpenAI (2026a), Lemmas 2.1–2.2][support-regularity] supply spatial
differentiability below time one. Let $u(t,x)=\partial_x\Phi_\gamma(t,x)$ be the slope
as the starting state changes. A small shift $\delta$ changes the
best expected payoff by approximately $u(t,x)\delta$. Write
$a(t,x)=\partial_{xx}\Phi_\gamma(t,x)$ for the rate at which that
slope changes. The displayed bound gives $|u|\le1$, and convexity
gives $a\ge0$. These are spatial derivatives: time is held fixed.

For the zero coefficient, the slope can be computed directly. Put
$F_{\mathrm G}(z)=\Pr(Z\le z)=\int_{-\infty}^z\varphi(y)\,dy$.
Moving $x$
slightly raises $|x+\sqrt{1-t}Z|$ when the final state is positive
and lowers it when the final state is negative. Consequently

$$
u_0(t,x)=2F_{\mathrm G}\!\left(\frac{x}{\sqrt{1-t}}\right)-1.
$$

Differentiating the integral is legitimate: the difference quotients
of the absolute value are bounded by one, and the Gaussian has zero
probability of hitting its corner. Thus the slope is the probability
of a positive final state minus the probability of a negative one.

For general $\gamma$, the control theorem says that the slope response
attains the value. To see why this is the right response, consider a
short step of length $h$ from $(t,x)$. A response $v$ adds displacement
$h\gamma(t)v$, whose first-order contribution to the continuation value
is $h\gamma(t)vu(t,x)$. Its running cost is $h\gamma(t)v^2/2$.
The response-dependent gain per unit time is therefore

$$
\gamma vu-\tfrac12\gamma v^2
=\tfrac12\gamma u^2-\tfrac12\gamma(v-u)^2.
$$

Since $\gamma\ge0$ and $|u|\le1$, $v=u$ attains its maximum.
The optimised contribution $\gamma u^2/2$ also explains why a squared
slope will enter the sensitivity to $\gamma$. The control theorem and
the first-variation formula in Section 5.1 make these connections rigorous; the square
completion alone does not justify differentiating an optimised value.
The control representation and feedback are justified for integrable
coefficients in [OpenAI (2026a), Lemmas 2.1–2.2][support-regularity];
see also [Auffinger–Chen, Corollary 2 and the extension after (13)][auffinger-chen].

We first fix $\gamma$ and obtain the deterministic value and slope by
optimising the expected future payoff. We then use that slope as a rule along a
random path. Computing an expected future payoff does not reveal future
noise: at time $t$, the rule needs only $t$ and the state already reached.
Following it generates the state

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

This is the **associated diffusion**. The cited regularity theorem
gives its existence and uniqueness for a fixed Brownian motion. The
rule is called **feedback** because it uses the slope at the currently
reached state. With $\gamma$ and $u$ supplied, a short forward step of length $h$ from state $x$
at time $t$, with $t+h<1$, is approximated by

$$
x+h\gamma(t)u(t,x)+\sqrt h Z.
$$

The response is evaluated before the fresh independent noise $Z$ is
observed. This discrete approximation explains the order of operations;
the integral equation defines the continuous process. Its drift accumulates
through time, so even a jump of $\gamma$ does not make $X$ jump.

Fix $\gamma$, follow a path to $X_t$, evaluate the slope there, square
it, and average over paths. This defines a deterministic curve

$$
q(t):=\mathbb E[u(t,X_t)^2].
$$

Here $\Phi_\gamma$ and $u$ are deterministic functions; $X_t$ and
the response evaluated at it are random. Squaring before averaging
retains the size of both positive and negative responses.

\Needspace{22\baselineskip}

**A calculation at half time.** For $\gamma=0$, $X_t=B_t$ and
$B_{1/2}$ has the same distribution as $Z/\sqrt2$. We can average
over paths by grouping them according to the state reached. At half
time the reached state has density $e^{-x^2}/\sqrt\pi$. This density
describes its **law**, assigning probability to positions on the real line. The law has
total mass one even though the order-parameter measure $\mu_0$ is
zero. The two measures describe different objects.

Average $u_0(1/2,x)^2$ with this density. Substituting $x=z/\sqrt2$
gives

$$
\begin{aligned}
q_0(1/2)
&=\int_{\mathbb R}(2F_{\mathrm G}(z)-1)^2\varphi(z)\,dz\\
&=\int_0^1(2v-1)^2\,dv=\frac13,
\qquad v=F_{\mathrm G}(z),\quad dv=\varphi(z)\,dz.
\end{aligned}
$$

The response at zero is zero, but its mean square at the random state
is $1/3$. Thus $q(t)=t$ is not automatic. Although every control is
optimal at $\gamma=0$, $q_0$ uses the value slope $u_0$.
Section 7.1 uses the whole curve to find a feasible decrease of
$\mathcal P(0)$; a discrepancy at one time does not suffice.

<a id="question-2"></a>

**Question 2: change the time.** Still take $\gamma=0$ everywhere,
but now set $t=1/4$. What variance has the state accumulated, and
what variance remains in its future reward? Write the Gaussian integral
for $q_0(1/4)$ without evaluating it. [Answer 2](#answer-2).

The analytic facts needed in the proof are

$$
q\in C^1([0,1)),\qquad q(0)=0,\qquad 0\le q(t)\le1,
\qquad q'(t)=\mathbb E[a(t,X_t)^2].
$$

Here $C^1$ means continuously differentiable, with derivatives at zero
from the right. In particular, $q'$ stays continuous across jumps of
$\gamma$. Spatial curvature controls the growth of the squared response.
These facts hold for every admissible candidate and follow from
[OpenAI (2026a), Lemmas 2.1–2.2][support-regularity]. The initial value
has a direct symmetry explanation: reflecting the starting state, noise history
and response rule together preserves reward and cost, so $\Phi_\gamma(t,x)$
is even in $x$. Hence $u(t,0)=0$, and the zero-field starting state
$X_0=0$ gives $q(0)=0$. Section 7.2 explains the stochastic calculation
for $q'$. In Section 5, $q(t)-t$ will determine the first-order cost
of changing cumulative weight. An added mass persists at every later time,
so its cost requires a tail integral.
<!-- /passage:value-and-diffusion -->

<!-- passage:full-support-statement -->
## 4. The full-support theorem

**Source theorem ([OpenAI (2026a), Theorem 1.1][support-manuscript]).**
In the pure, zero-field model with $\xi(t)=t^2/2$, let $\gamma$ be an
admissible integrable minimiser of $\mathcal P$. Its Stieltjes measure
has full relative support on $[0,1)$, and $\gamma$ is strictly increasing.
For every associated diffusion and every $0\le t<1$,

$$
\mathbb E[u(t,X_t)^2]=t,\qquad
\mathbb E[a(t,X_t)^2]=1.
$$

The theorem requires a minimiser,
not merely an admissible candidate. Zero field supplies $q(0)=0$;
$\xi''=1$ enters the curvature estimate. The statement does not cover
nonzero field or general mixed-spin covariance functions.
<!-- /passage:full-support-statement -->

<!-- passage:first-variation -->
## 5. Why a flat interval cannot minimise

We now prove the theorem. The identities $q=t$ and $q'=1$ are
conclusions still to be established. We begin with the first-order cost
of an allowed change, obtain conditions at support points, and then
exclude every possible gap.

### 5.1 Allowed changes and their first-order cost

The **first variation** in a direction $\eta$ is the derivative at
zero of $\varepsilon\mapsto\mathcal P(\gamma+\varepsilon\eta)$.
At a minimum its right derivative is nonnegative whenever small
$\varepsilon\ge0$ leave the candidate admissible. It need not vanish:
the opposite change may violate nonnegativity or monotonicity.
Precisely, let $\eta\in L^1(0,1)$, meaning $\int_0^1|\eta(t)|\,dt<\infty$, and suppose
$\gamma+\varepsilon\eta$ stays admissible for every
$0\le\varepsilon\le\varepsilon_0$, for some $\varepsilon_0>0$.
The formula is

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

Here $q$ belongs to the unperturbed candidate $\gamma$.
The term $-t/2$ comes from the outer correction in $\mathcal P$;
$q(t)/2$ is the sensitivity of the reoptimised control value. The latter
is the analytic content of the formula, not differentiation with a fixed
control. [Chen–Handschy–Lerman (2018), Proposition 4][chl-optimality]
gives the derivative along the segment joining any two admissible
coefficients. Taking the second endpoint to be
$\gamma+\varepsilon_0\eta$ and rescaling the segment parameter gives
the formula above. The detailed proof in
[OpenAI (2026a), Lemma 6.1][support-variation] compares value functions
and bounds the terminal remainder by the $L^1$ tail of $\eta$.
<!-- /passage:first-variation -->

<!-- passage:contact-and-gap -->

Adding a small atom at scale $s$ raises the cumulative function at
*every* later scale. It is always allowed: the total mass is not
fixed, so no compensating removal is required. Its direction is
$\eta(t)=\mathbf1_{[s,1)}(t)$, equal to zero before $s$ and one
from $s$ onward. Thus

$$
D\mathcal P(\gamma)[\mathbf1_{[s,1)}]
=\frac12\int_s^1(q(t)-t)\,dt=:\frac12G(s).
$$

For the candidate in Figure 1, adding $\varepsilon$ mass at $s=1/2$
creates a jump of height $\varepsilon$ there and raises the entire
remaining curve by $\varepsilon$. The coefficient changes only on
that tail, but its optimised value and feedback must be recomputed:
earlier starting states also face a changed future control problem. The
first-variation theorem accounts for this dependence. Its formula
has a tail integral because that is where the coefficient changes:
$G(s)/2$ is the marginal cost of placing mass at $s$. At a minimiser,
$G(s)\ge0$ for every $s<1$.

For the two weights in Section 2, the same accounting gives

$$
\int_0^1\gamma(t)(q(t)-t)\,dt
=2G(1/4)+G(3/4).
$$

Each weight is charged for its entire remaining tail. The $q$ and $G$
in this identity belong to that candidate; no optimality has been assumed.
Reducing both weights by a fraction $\varepsilon$ multiplies the
cumulative function by $1-\varepsilon$.

Suppose temporarily that this two-weight candidate minimised
$\mathcal P$. Addition would give two nonnegative costs,
$G(1/4)\ge0$ and $G(3/4)\ge0$, while the allowed reduction would give

$$
0\le-\frac12\bigl(2G(1/4)+G(3/4)\bigr).
$$

Both costs must be zero: their positive-weighted sum is nonnegative,
and the reduction forces it to be nonpositive. This is a necessary
condition under the temporary minimiser assumption, not a claim that
the two-weight candidate attains the minimum.

Now fix a general minimiser $\gamma$ and its own $q$, $G$ and
$\mu_\gamma$. The same argument replaces the finite sum by an integral.
The direction $\eta=-\gamma$
is integrable, and $(1-\varepsilon)\gamma$ remains admissible for
$0\le\varepsilon\le1$. It scales all existing mass by the same
factor. For the continuous candidate in Figure 1, it multiplies the
two nonzero slopes and the plateau height by $1-\varepsilon$;
it works for diffuse mass as well as atoms. To see the order of
integration, each weight at $s$ contributes for exactly the times
$t\ge s$:

$$
\begin{aligned}
\int_0^1\gamma(t)(q(t)-t)\,dt
&=\int_0^1\int_{[0,1)}\mathbf1_{\{s\le t\}}(q(t)-t)\,\mu_\gamma(ds)\,dt\\
&=\int_{[0,1)}G(s)\,\mu_\gamma(ds).
\end{aligned}
$$

Thus the allowed reduction gives

$$
0\le D\mathcal P(\gamma)[-\gamma]
=-\frac12\int_{[0,1)}G(s)\,\mu_\gamma(ds).
$$

The exchange of integration order is valid even if the total mass is
infinite. Its absolute integral is bounded by the area from Section 2:

$$
\int_{[0,1)}\int_s^1|q(t)-t|\,dt\,\mu_\gamma(ds)
=\int_0^1\gamma(t)|q(t)-t|\,dt
\le\int_0^1\gamma(t)\,dt<\infty.
$$

Since $G\ge0$, its integral must be zero. If $G$ were positive at a
support point, continuity would bound it below by a positive number
on a neighbourhood carrying positive mass, contradicting that zero
integral. Hence $G=0$ on the support. This is **contact**: the
nonnegative function touches zero there. The scaling argument is the
variational argument of [Chen, Proposition 3.2, equations (3.11)–(3.12)][chen-support],
applied with the integrable-direction formula above.

Scaling removes only mass that exists. In Figure 1, even the supported
point $1/4$ has no atom: intervals around it carry mass, but the point
itself does not. Subtracting $\varepsilon\delta_{1/4}$ would create a
downward jump. For $0<\varepsilon<1/4$ the cumulative values would
remain nonnegative, but the function would no longer be nondecreasing.
Support alone does not permit atom removal. We have proved contact
on the support, not that every zero of $G$ must carry mass.

### 5.2 Contact gives endpoint conditions

We need information about $q$ at the ends of a possible gap. An interior
support point $s$ is a minimum of $G$. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$, ordinary calculus gives

$$
q(s)=s,\qquad q'(s)\le1.
$$

At zero, if it belongs to the support, contact and symmetry give
$G(0)=q(0)=0$. If $q'(0)>1$, continuity would give $q'(t)>1$
for small positive $t$. Integration would then give $q(t)>t$, so
$G'(t)=t-q(t)<0$. Starting from $G(0)=0$, this would force $G(t)<0$,
a contradiction. Hence $q'(0)\le1$. This one-sided argument includes
an atom at zero.

### 5.3 Strict curvature creates an impossible integral

The support is relatively closed in $[0,1)$. Starting at a missing
point, enlarge its mass-free interval until it reaches support or a
boundary of the domain. Such a maximal interval has two
support endpoints, starts at zero outside the support, or reaches one.
We treat these three cases in order; the last includes empty support.

First suppose $(r,s)$ has both endpoints in the support, with
$0\le r<s<1$. Its constant height $c$ is necessarily positive:
for $t$ inside the gap, a small relative neighbourhood of $r$ lies in
$[0,t]$ and has positive mass, so $c=\mu_\gamma([0,t])>0$.
If $r=0$, this mass is an atom at zero. Contact imposes

$$
q(r)=r,\quad q(s)=s,\quad q'(r)\le1,\quad q'(s)\le1.
$$

The first two conditions require area $s-r$ under $q'$ across the gap.
A calculus model shows how strict convexity can prevent this. On the
earlier interval $[1/3,2/3]$, put $x=3t-1$ and consider the slope
$1-x(1-x)$. Its endpoints equal one, but

$$
\int_{1/3}^{2/3}[1-(3t-1)(2-3t)]\,dt
=\frac13\int_0^1[1-x(1-x)]\,dx=\frac5{18}.
$$

The missing area is $1/3-5/18=1/18$. This is a calculus model, not a
computed SK moment curve. The next input forces the actual $q'$ below
its endpoint chord in the same way.

**Strict-curvature input ([OpenAI (2026a), Proposition 5.1][support-curvature]).**
For any admissible coefficient equal to $c>0$ on an open interval,
its moment curve satisfies, strictly inside that interval,

$$
q'''(t)\ge\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(r<t<s).
$$

Section 7.3 explains how this sign is obtained after expectation.
The gap argument uses its strict sign; it does not use the particular
number $1/1000$.
The final inequality uses $a(t,x)>0$, proved by Gaussian smoothing
on the constant interval ([OpenAI (2026a), Lemma 2.3][support-regularity]);
convexity of $\Phi$ alone would only give $a\ge0$.
Because $q'''=(q')''$, the function $q'$ is strictly convex: between
two points its graph lies strictly below their joining chord.
The moment identity makes $q'$ continuous at the endpoints, even if
$\gamma$ jumps there; higher derivatives are needed only inside the gap.
Hence

$$
q'(t)<\frac{s-t}{s-r}q'(r)+\frac{t-r}{s-r}q'(s)\le1
\qquad(r<t<s).
$$

<!-- Modified 2026-10-25: equal endpoint slopes isolate strictness. -->
\begin{figure}[H]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,font=\small,line cap=round]
  \fill[black!8] (0,3.1) -- (8,3.1) -- (8,3.1)
     .. controls (5.333333,2.066667) and (2.666667,2.066667) .. (0,3.1) -- cycle;
  \draw[->] (-1.9,0) -- (8.7,0) node[right] {$t$};
  \draw[->] (-1.9,0) -- (-1.9,3.8) node[above] {$q'(t)$};
  \draw[gray!70] (-1.9,3.1) -- (0,3.1);
  \node[left] at (-1.9,3.1) {$1$};
  \draw[densely dashed,gray!75] (0,3.1) -- (8,3.1)
    node[midway,above=3pt,text=black,fill=white,inner sep=1pt]
       {endpoint chord $=1$};
  \draw[very thick,black] (0,3.1)
    .. controls (2.666667,2.066667) and (5.333333,2.066667) .. (8,3.1);
  \draw[dotted,gray!80] (0,0) -- (0,3.1);
  \draw[dotted,gray!80] (8,0) -- (8,3.1);
  \fill (0,3.1) circle (1.6pt);
  \fill (8,3.1) circle (1.6pt);
  \node[below] at (0,0) {$r$};
  \node[below] at (8,0) {$s$};
  \node[above left=3pt] at (0,3.1) {$q'(r)=1$};
  \node[above right=3pt] at (8,3.1) {$q'(s)=1$};
  \node[below] at (4,2.12) {strictly convex $q'$};
  \node at (4,2.8) {missing area};
\end{tikzpicture}
\caption{The case where strictness is indispensable: both endpoint
slopes equal one, so the chord alone loses no area. A strictly convex
slope lies below it. Contact would require zero shaded area, but
$\int_r^s(1-q'(t))\,dt>0$. The drawn calculus model is
$1-x(1-x)$ with $x=(t-r)/(s-r)$; its mean is $5/6$, while the constant
slope one has mean one. Neither is asserted to be an SK moment curve.
The proof also allows unequal endpoint slopes, each at most one. Adapted from
\href{https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex}{Figure 1 of OpenAI (2026a)}, OpenAI/math (Apache 2.0).}
\end{figure}

Integration gives $q(s)-q(r)<s-r$, contradicting contact. For the candidate in Section 2,
a minimising plateau on $(1/3,2/3)$ would require the same increment
to be both equal to and strictly less than $1/3$.

<!-- /passage:contact-and-gap -->

<!-- passage:endpoints -->
### 5.4 The remaining initial and terminal gaps

**Initial gap with zero outside the support.** Suppose $[0,s)$ is
missing and $s<1$ is the first support point. Then $\gamma=0$ there,
so the positive-coefficient bound supplies no strictness. Instead the
zero-coefficient heat identity gives

$$
q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0\qquad(0<t<s).
$$

Here is why the inequality is strict. On this interval $X_t=B_t$,
whose density is positive everywhere at positive times. If the expected
square were zero, continuity would force $\Phi_{xxx}(t,x)=0$ for
every $x$: a nonzero value would give a small interval on which the
square is positive, and that interval has positive probability.
Then $\Phi(t,\cdot)$ would be a quadratic polynomial, and its bounded
slope would make it affine, a linear function plus a constant.
But choosing zero control gives
$\Phi_\gamma(t,x)\ge\mathbb E|x+B_1-B_t|\ge|x|$: the average
absolute value is at least the absolute value of the average. This
rules out an affine value: domination of $|x|$ in the positive tail
requires slope at least one, while the negative tail requires slope
at most minus one. The heat identity and the needed regularity are
in [OpenAI (2026a), Lemmas 2.2–2.3][support-regularity].

Thus $q'$ is strictly increasing, and right contact gives
$q'(t)<q'(s)\le1$ for $0<t<s$. Symmetry supplies $q(0)=0$,
while contact gives $q(s)=s$. Integrating again gives too little area.
Strictness was needed only at positive times; symmetry can make the
third spatial derivative vanish at $(0,0)$.

Although the forward path is Brownian here, the backward value receives
data $\Phi_\gamma(s,\cdot)$ from the later coefficient. The formula
for the globally zero candidate cannot be reused on this initial
interval. The case where zero itself is supported was already included
in Section 5.3, using its atom and the one-sided slope bound.

```{=latex}
\noindent\begin{minipage}{\linewidth}
```

**Empty support.** This would mean $\gamma=0$ everywhere. The preceding
heat argument now gives $q''>0$ throughout $(0,1)$: it is $q$ itself
that is strictly convex. Recall that $q(0)=0$ and $q\le1$. For
$0<t<s<1$, the chord from zero to $s$ gives

$$
q(t)\le\frac ts q(s)\le\frac ts.
$$

Letting $s$ increase to one gives $q(t)\le t$; only the numerical
bound $t/s$ is taken to a limit. To obtain strictness, choose $t<v<1$
and compare with the chord ending at $v$:

$$
q(t)<\frac tv q(v)\le t.
$$

Hence $G(0)=\int_0^1(q(t)-t)\,dt<0$, contrary to the allowed
addition of mass at zero. No value or derivative at one was used.
Section 7.1 also computes the exact first variation
$D\mathcal P(0)[1]=1/4-1/\pi$.

```{=latex}
\end{minipage}
```

**Terminal gap.** Now suppose a maximal missing interval is $(r,1)$.
Its left endpoint $r<1$ is supported, and its constant height is
positive, by the same mass argument as in Section 5.3. We have
$q(r)=r$ and $q'(r)\le1$, and $q'$ is strictly convex on $(r,1)$.
There is no contact condition at one. We use the bound $q\le1$
instead. We will show that $q$ stays below the diagonal throughout
the gap, which makes the tail cost $G(r)$ negative. If it reached
the diagonal, the area comparison would force its slope above one;
convexity would preserve enough of that excess to violate $q\le1$.

Put $h(t)=q'(t)-1$, so $h(r)\le0$. If $q(t)\ge t$ at some
$r<t<1$, strict integration below the chord on the finite interval
$[r,t]$ would give

$$
0\le q(t)-t=\int_r^t h(v)\,dv
<\frac{t-r}{2}\bigl(h(r)+h(t)\bigr)
\le\frac{t-r}{2}h(t).
$$

Hence $h(t)>0$. To control a later slope, use the same chord rule
on the larger interval $[r,s]$, where $t<s<1$. At its interior
point $t$ this gives

$$
h(t)\le\frac{s-t}{s-r}h(r)+\frac{t-r}{s-r}h(s).
$$

Solving for the right endpoint gives

$$
h(s)\ge h(t)+\frac{s-t}{t-r}\bigl(h(t)-h(r)\bigr)\ge h(t)>0.
$$

The bound holds at every time after $t$, so integration gives
$q(s)\ge t+(s-t)(1+h(t))$. Choose any time

$$
t+\frac{1-t}{1+h(t)}<s<1.
$$

Such a choice exists because $h(t)>0$, and the lower bound now gives
$q(s)>1$, contradicting $q(s)\le1$ strictly before time one.
Thus $q(t)<t$ throughout $(r,1)$, giving
$G(r)=\int_r^1(q(t)-t)\,dt<0$, contrary to the addition test.
Only finite-interval convexity and the bound on $q$ were used; no
value for $q'(1)$ was assumed.

The source's different terminal argument proves the stronger estimate
$1-q(t)\ge C\sqrt{1-t}$ near one for any finite constant terminal
coefficient, without the left contact data used here. Its proof is
[OpenAI (2026a), Lemma 6.3][support-variation] and is retained in the
*Long Reasoning Record*,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="terminal-gap">[§5, terminal estimate](../long/reasoning-record.md#terminal-gap)</span>.
[Auffinger–Chen–Zeng, Remark 7][acz] had already recorded the absence
of terminal plateaus.

These cases exhaust the complement of the support. Contact now gives
$q(t)=t$ for every interior time, and symmetry includes zero.
Differentiating gives $\mathbb E[a(t,X_t)^2]=1$, completing the theorem.
<!-- /passage:endpoints -->

<!-- passage:changed-cases -->
### 5.5 Two checks on the gap argument

<a id="question-3"></a>

**Question 3: tilt the chord.** Suppose a differentiable function $f$ on $[2,5]$ has
$f(2)=2$, $f(5)=5$, $f'(2)=1/2$ and $f'(5)=3/2$. If $f'$ is
strictly convex, can these data hold? What changes if strict convexity
is weakened to convexity? The endpoint chord is now tilted, so a
pointwise comparison with the constant one is unavailable. Finally,
keep the endpoint values and left slope fixed but change $f'(5)$ to
$2$. Are these data compatible with strict convexity of $f'$?

<a id="question-4"></a>

**Question 4: the missing right endpoint.** In the terminal proof,
why does a point with $q(t)\ge t$ force $h(t)>0$? Which inequality
keeps the later slopes above one, and where does the bound $q\le1$
enter? Explain the two stages without assigning any value to $q'(1)$.

[Answers 3](#answer-3) and [4](#answer-4).
<!-- /passage:changed-cases -->

<!-- passage:overlap-payoff -->
<!-- pdf-page-break -->

## 6. Return to the spins

At a fixed finite size, almost surely the only exact maximisers are
a configuration and its global reversal. Indeed, two configurations
that are neither equal nor global reversals differ in some pair product.
Their energy difference is then a Gaussian with positive variance, so a tie has
probability zero; there are only finitely many pairs. Intermediate
separations become possible when we allow a small loss per spin and
let the system grow.

A separate theorem
of [Auffinger–Chen–Zeng, Proposition 1, equation (5)][acz] applies at
each point in the minimiser's support. Combining it with full support:
for every fixed overlap $r\in[0,1)$ and tolerances $\varepsilon,\eta>0$,
with probability over the couplings tending to one exponentially fast
as $n\to\infty$, there exist configurations $\sigma,\tau$ with

$$
|R(\sigma,\tau)-r|<\varepsilon,
\qquad H_n(\sigma)/n,\ H_n(\tau)/n\ge P_*-\eta.
$$

If $k$ sites differ, $k/n=(1-R)/2$. The overlap tolerance therefore gives

$$
\left|\frac{k}{n}-\frac{1-r}{2}\right|<\frac\varepsilon2.
$$

For example, fix an energy loss $\eta>0$ per spin and take
$r=1/2$ and $\varepsilon=0.02$. With probability tending to one
exponentially fast, the same instance has two configurations with
energies per spin at least $P_*-\eta$ and a differing-site fraction
between $0.24$ and $0.26$. No numerical threshold for $n$ is asserted.
At target zero, the differing-site fraction can be arbitrarily close
to one half.
The pair may depend on the chosen target and the couplings. This is
existence for each fixed target, not a statement about
typically sampled pairs or a procedure for finding them. The companion
*Long Reasoning Record*,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="near-ground-overlaps">[§9.3, “Near-ground configurations at a prescribed overlap”](../long/reasoning-record.md#near-ground-overlaps)</span>,
gives the probability bound, covariance adjustment and exact finite-size
comparison. The threshold $P_*-\eta$ refers to the limiting value,
whereas an exact maximiser attains its particular finite instance's maximum.

<a id="question-5"></a>

**Question 5: use the spin conclusion.** Fix an energy loss $\eta>0$.
How can the theorem give two configurations differing on between 69%
and 71% of sites, although it is stated for nonnegative overlap targets?
Which earlier symmetry is needed? Does the stated theorem also permit
the choice $\eta=1/n$? [Answer 5](#answer-5).
<!-- /passage:overlap-payoff -->

## 7. Optional calculations

The no-gap argument and the return to spins are complete. Section 7.1
checks the zero-candidate descent by Gaussian calculus using the stated
moment identity. Section 7.2 explains the value equation and stochastic
chain rule behind that identity. Section 7.3 describes the mechanism
of the strict-curvature estimate; its full proof remains in the sources.
Section 7.4 gives the answers to the earlier questions.

<!-- passage:zero-candidate -->
\Needspace{11\baselineskip}

### 7.1 Why the zero candidate does not minimise

Return to the Gaussian value and slope from Section 3. With $\gamma=0$,
the state is $B_t$. Differentiating the slope once more gives

$$
X_t=B_t,\qquad
u_0(t,x)=2F_{\mathrm G}\!\left(\frac{x}{\sqrt{1-t}}\right)-1,
\qquad
a_0(t,x)=\sqrt{\frac2{\pi(1-t)}}e^{-x^2/(2(1-t))}.
$$

A Gaussian integral gives
$\mathbb E e^{-B_t^2/(1-t)}=\sqrt{(1-t)/(1+t)}$. Substituting
into $q_0'=\mathbb E[a_0(t,B_t)^2]$ and integrating from zero yields

$$
q_0'(t)=\frac2{\pi\sqrt{1-t^2}},\qquad
q_0(t)=\frac2\pi\arcsin t.
$$

This recovers the half-time value $1/3$. It also shows that
$q_0(t)\to1$ while $q_0'(t)\to\infty$: convergence of a function
at one does not bound its derivative there.
The constant direction $\eta=1$ is admissible and adds an atom at zero.
Its cost is

$$
D\mathcal P(0)[1]
=\frac12\int_0^1\left(\frac2\pi\arcsin t-t\right)dt
=\frac14-\frac1\pi<0.
$$

So a small positive constant coefficient improves the zero candidate.
This calculation uses the heat and variation formulas, not a minimiser
hypothesis; see also [Chen–Handschy–Lerman, proof of Theorem 6][chl-optimality].
<!-- /passage:zero-candidate -->

<!-- passage:control-derivations -->
### 7.2 The value equation and the moment identity

At $t=1$ there is no noise or response left to accumulate, so the value
is $|x|$. At earlier times it includes the best remaining response.
Its partial differential equation (PDE) runs backward from that final value:

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

With the spatial derivatives $u$ and $a$ defined in Section 3.3,
the equation expresses
a recursive choice: choose a response for a short first step, then
use the best continuation from the state reached. At a continuity
point of $\gamma$, this gives the formal first-order relation

$$
\Phi_\gamma(t,x)
=\sup_{|v|\le1}\left\{
\mathbb E\Phi_\gamma(t+h,x+\gamma(t)vh+\sqrt hZ)
-\tfrac12\gamma(t)v^2h\right\}+o(h).
$$

Subtract the present value, divide by $h$, and Taylor-expand.
The identities $\mathbb EZ=0$ and $\mathbb EZ^2=1$ give

$$
0=\Phi_t+\tfrac12\Phi_{xx}
  +\sup_{|v|\le1}\gamma(t)(v\Phi_x-v^2/2).
$$

The square completion from Section 3.3 gives a supremum of
$\gamma u^2/2$, attained at $v=u$, and hence the stated PDE. This calculation explains the equation;
justifying the recursion and the Taylor expansion requires the
control representation and regularity results. See
[Auffinger–Chen, Theorem 2 and Corollary 2][auffinger-chen] for the zero-temperature
control formula and [Jagannath–Tobasco, Lemma 18][jt-control] for the
control method with finite-temperature terminal data. The extension after
Auffinger–Chen's Corollary 2 covers integrable coefficients. The regularity
used here is in
[OpenAI (2026a), Lemmas 2.1–2.2][support-regularity].

Itô's rule is the chain rule for Brownian paths. Along
$dX_t=b_t\,dt+dB_t$, the coefficient of $dt$ (the **drift**)
in a smooth $f(t,X_t)$ is
$f_t+b_tf_x+f_{xx}/2$, and its noise term is $f_x\,dB_t$.
Differentiate the PDE in $x$ and take $b_t=\gamma u$. The drift of
the slope cancels:

$$
du(t,X_t)
=\underbrace{(u_t+\gamma u u_x+u_{xx}/2)}_{0}\,dt
+a(t,X_t)\,dB_t.
$$

Thus $M_t=u(t,X_t)$ is a bounded **martingale**: its conditional
expected later value, given observations up to time $t$, is its present
value. Zero field gives symmetry and $M_0=u(0,0)=0$. Applying Itô's rule once more
to $M_t^2$ gives

$$
d(M_t^2)=2M_ta(t,X_t)\,dB_t+a(t,X_t)^2\,dt.
$$

The noise term has mean zero because its coefficient is nonanticipating
and bounded on each strip ending before one. Taking expectations and
integrating yields $q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds$,
which gives the asserted derivative. Since $\mathbb EM_t=0$,
$q(t)$ is also the variance of the slope response.

For each fixed $T<1$, the required spatial derivatives are bounded on
$[0,T]\times\mathbb R$, and step-coefficient and smooth-terminal
approximations justify the identities. The bounds depend on the coefficient
and strip. The PDE holds almost everywhere in time. These are not
bounds up to time one.
<!-- /passage:control-derivations -->

<!-- passage:curvature-mechanism -->
### 7.3 Where the strict-curvature input comes from

The proof in Section 5 used strict curvature on a positive constant
interval. This calculation explains how that expectation acquires a sign;
the full analytic proof remains in the cited sources. Take any admissible
coefficient with $\gamma=c>0$ on an open interval, without assuming
minimality. Set $b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$ there.
Differentiating the PDE and applying Itô's rule gives

$$
q''=\mathbb E[b^2-2ca^3],\qquad
q'''=\mathbb E[d^2-12cab^2+6c^2a^4].
$$

The negative middle term prevents a pointwise positivity argument.
The source instead averages with the spatial probability density
$f_t(x)$ of $X_t$ at positive time. As in the half-time example,
for any integrable function $F$, grouping paths by their reached position gives

$$
\mathbb E[F(X_t)]=\int_{\mathbb R}F(x)f_t(x)\,dx.
$$

These are probability weights on states $x$, distinct from the
Stieltjes weights $\mu_\gamma(ds)$ on overlap scales. The proof needs
bounds relating this density to the spatial derivatives of the value.
The factorisation and comparison arguments establishing those bounds
are given in [OpenAI (2026a), §3][support-signs].

\Needspace{8\baselineskip}

The operation can be written directly for the positive density $f_t$.
For a smooth function $F$ with integrable terms and vanishing boundary
product $Ff_t$,

$$
\mathbb E\!\left[F'(X_t)+F(X_t)\frac{f_t'(X_t)}{f_t(X_t)}\right]
=\int_{\mathbb R}(Ff_t)'(x)\,dx=0.
$$
<!-- /passage:curvature-mechanism -->

<!-- passage:correction-example -->
For a small example of this operation, let $Z$ be standard normal and
$F(x)=2x$. Its density has logarithmic derivative $-x$, so
$\mathbb E[2-2Z^2]=0$. Although $2x^2-1$ is negative near zero,
adding that zero-mean correction gives

$$
(2x^2-1)+(2-2x^2)=1.
$$

Hence $\mathbb E[2Z^2-1]=1>0$. The boundary term vanishes because a
polynomial times the Gaussian density tends to zero. This illustrates
how a correction changes the visible sign without changing the
expectation; it supplies none of the SK-specific sign estimates.
<!-- /passage:correction-example -->

<!-- passage:curvature-transfer -->

The source first uses positive nondecreasing finite-step coefficients
with terminal approximation $M^{-1}\log(2\cosh(Mx))$, choosing
$M$ at least as large as every step height. The source's sign
comparisons use this bound as well as smoothness. At this stage, write
$R_c=d^2-12cab^2+6c^2a^4$. The source constructs a correction
$C$ from the spatial derivatives and density, with

$$
\mathbb E[C(t,X_t)]=0,\qquad
R_c(t,x)+C(t,x)\ge\frac{c^2}{1000}a(t,x)^4.
$$

A rational polynomial identity gives the second inequality by writing
the remainder as a sum of nonnegative terms. The density bounds and vanishing boundary
products justify the first. Consequently

$$
q'''(t)=\mathbb E[R_c(t,X_t)]
=\mathbb E[(R_c+C)(t,X_t)]
\ge\frac{c^2}{1000}\mathbb E[a(t,X_t)^4].
$$

This is how the correction produces a useful lower bound for the
expectation even though $R_c$ can be negative at particular states.

To reach an arbitrary admissible coefficient, fix a time inside the
plateau and approximate in $L^1$ by step coefficients, keeping the same
value $c$ near that time.
Uniform convergence of spatial derivatives through order four on a
fixed strip below one, together with convergence of the coupled
paths, passes the quantitative inequality to the limit. Strictness is
then established for the limit itself: the constant-coefficient heat
formula expresses $a$ as a nonnegative mean plus $c$ times a strictly
positive variance of a nonconstant slope under a positively weighted
Gaussian law. Hence $a(t,x)>0$ and its fourth moment is
positive. Positivity of the approximants alone would not suffice.
The auxiliary logarithmic derivatives need not converge: they have
already been removed by integration.

The analytic details are [OpenAI (2026a), §§3–5][support-manuscript]
and the companion *Long Reasoning Record*,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="curvature-algebra">[§4.4, “How the signs make a correction with zero expectation useful”](../long/reasoning-record.md#curvature-algebra)</span>,
and <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="plateau-limit">[§4.5, “A fixed-time inequality and its plateau application”](../long/reasoning-record.md#plateau-limit)</span>.
<!-- /passage:curvature-transfer -->

<!-- passage:changed-case-answer -->
### 7.4 Answers to the questions

<a id="answer-1"></a>

**[Question 1](#question-1).** Adding mass at $1/2$ gives cumulative heights
$0,2,2+\varepsilon,3+\varepsilon$, in their successive intervals;
removing it at $1/4$ gives heights $0,2-\varepsilon,3-\varepsilon$.
Both functions remain nonnegative and nondecreasing. Removing mass at
$1/2$ instead lowers the height from $2$ to $2-\varepsilon$ there,
creating a downward jump, so it is forbidden even though all values
remain nonnegative. Scaling both weights preserves all admissibility
conditions. These tests concern allowed candidates; a smaller ordinary
area alone does not establish a smaller Parisi value.

<a id="answer-2"></a>

**[Question 2](#question-2).** The state has accumulated variance $1/4$, so it is
distributed as $Z/2$. The remaining noise has variance $3/4$, and
its standard deviation in the value-slope formula is $\sqrt3/2$.
Thus

$$
q_0(1/4)=\int_{\mathbb R}
\left(2F_{\mathrm G}(z/\sqrt3)-1\right)^2\varphi(z)\,dz.
$$

The two variances agree at half time, but not here. For nonzero $z$,
the magnitude of the response is now smaller, so $q_0(1/4)<1/3$.
The arcsine formula in Section 7.1 also gives this comparison.

<a id="answer-3"></a>

**[Question 3](#question-3).** A strictly convex $f'$ lies below its endpoint chord.
That chord has mean height $(1/2+3/2)/2=1$, hence integral three.
Therefore $f(5)-f(2)=\int_2^5f'(t)\,dt<3$, contradicting the
prescribed values. With non-strict convexity the data are possible:
$f(t)=2+(t-2)/2+(t-2)^2/6$ has affine derivative and satisfies all
four endpoint values. The argument needs a strict loss of area; the
common endpoint upper bound of one in Figure 2 is convenient, not essential. This is a
calculus example, not a candidate SK moment function.

With the right slope changed to $2$, the chord has mean $5/4$,
so a strict loss of area can leave the required mean one. Indeed,

$$
f(t)=2+\frac{t-2}{2}+\frac{(t-2)^3}{18}
$$

has the required endpoint values, slopes $1/2$ and $2$, and
$(f')''=1/3>0$. Thus these changed data are compatible.
Strict convexity produces the contradiction only when the chord
cannot supply enough area.

<a id="answer-4"></a>

**[Question 4](#question-4).** Since $q(r)=r$, reaching or passing the diagonal at
$t$ means $\int_r^t h\ge0$. Strict convexity places $h$ below its
endpoint chord, so that integral is less than
$(t-r)(h(r)+h(t))/2$. With $h(r)\le0$, this forces $h(t)>0$.
The chord rule on $[r,s]$, solved for $h(s)$, keeps every later value
at least $h(t)$. Integrating gives
$q(s)\ge t+(s-t)(1+h(t))>1$ for a suitable $s<1$, violating the
bound. If $q$ never reaches the diagonal, then $G(r)<0$ instead.
Thus both possibilities contradict the conditions on a minimiser.

<a id="answer-5"></a>

**[Question 5](#question-5).** Choose $r=0.4$ and $\varepsilon=0.02$.
The theorem gives a pair differing on between 29% and 31% of sites.
Reverse every sign of the second configuration. Its energy is unchanged,
its overlap changes sign, and the differing-site fraction becomes its
complement, between 69% and 71%. This operation uses the same successful
instance and causes no further probability loss. The theorem fixes
$\eta>0$ before $n$ grows; it supplies no rate justifying $\eta=1/n$.
This stronger choice is not established by the stated result.
<!-- /passage:changed-case-answer -->

### Further reading

<!-- passage:density-and-approximation -->
Full support alone does not give a density. Additional differentiation
of the identities $q=t$ and $\mathbb E[a^2]=1$, followed by
another use of the integrated curvature estimate on locally constant
comparison coefficients, proves that $\gamma$
is smooth, $\gamma(0)=0$, and
$\mu_\gamma=\gamma'(t)\,dt$ with $\gamma'(t)>0$ for $0<t<1$
([OpenAI (2026a), Corollary 6.4][support-density]). The *Long Reasoning
Record*, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="smooth-density-consequence">[§§9.1–9.2](../long/reasoning-record.md#smooth-density-consequence)</span>, supplies this additional argument; Chen's earlier
theorem had already given smooth nonnegative density and full support.
<!-- /passage:density-and-approximation -->

<!-- passage:scalar-identities -->
Further martingale arguments recover the ground-state value from the
terminal slope response. They use the first curvature moment
$\mathbb E[a]$, distinct from the second moment $\mathbb E[a^2]=1$
used here. See [OpenAI (2026a), Corollary 7.1][support-consequences]
and the *Long Reasoning Record*, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="scalar-value-identities">[§6](../long/reasoning-record.md#scalar-value-identities)</span>.
<!-- /passage:scalar-identities -->

<!-- passage:qaoa-boundary -->
The separate circuit theorem in [OpenAI (2026b)][qaoa-manuscript]
resolves the eventual-optimality conjecture for the Quantum Approximate
Optimization Algorithm (QAOA) in
[Basso–Farhi–Marwaha–Villalonga–Zhou, §7, equation (7.2)][bfmvz].
The *Long Reasoning Record*, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="qaoa-construction">[§8](../long/reasoning-record.md#qaoa-construction)</span>, develops its circuit construction and
the order of limits. It requires additional arguments beyond full support.
<!-- /passage:qaoa-boundary -->

<!-- passage:source-record -->
## Sources and scope of verification

This account reconstructs selected parts of OpenAI's analytic manuscript.
The global scaling argument for contact follows Chen's variational proof.
The empty-support and terminal convexity arguments in Section 5.4 are
ordinary deductions from the stated analytic inputs; the finite no-tie
argument in Section 6 follows from the Gaussian Hamiltonian. These
arguments are not claimed to have been replayed in Lean.
The Lean [implementation][support-proof],
[challenge statement][support-interface] and [Comparator configuration][support-config]
concern a minimiser's support and moment identities. The support
statement assumes a minimiser; it does not prove the external Parisi formula or attainment.
The separate scalar [implementation][value-proof] and [statement][value-interface]
concern the value identity and finite Gaussian approximation. Neither
selected statement covers positive density, the external near-ground
overlap theorem used in Section 6, or the complete QAOA circuit theorem.
The implementations use [Lean 4 (de Moura–Ullrich, 2021)](https://doi.org/10.1007/978-3-030-79876-5_37)
and [mathlib (The mathlib Community, 2020)](https://doi.org/10.1145/3372885.3373824).

Comparator acceptance and research-v2 extraction remain unknown; see the
*Long Reasoning Record*, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="verification">[§13](../long/reasoning-record.md#verification)</span>. Kernel checking establishes a declared statement
under its definitions and axioms. Its correspondence with the analytic theorem,
independent proof review and reader comprehension are separate questions.
The links below select the editions used.

- **OpenAI (2026a).** *Full support of the zero-temperature
  Sherrington–Kirkpatrick order parameter*, 27 September 2026.
  [Pinned manuscript][support-manuscript]. §2 supplies regularity,
  Proposition 5.1 the strict curvature estimate, §6 the support proof,
  and Corollary 6.4 the additional density conclusion.
- **Hong-Bin Chen (2026).** *FRSB in the SK spin glass: convergence to full-interval
  support at zero temperature*. [Version 1][chen-support],
  Theorem 1.3 for earlier full support and smooth nonnegative density;
  Proposition 3.2 for contact by scaling the coefficient. Strictly positive
  density in the further-reading note uses the separate OpenAI corollary.
- **Antonio Auffinger and Wei-Kuo Chen (2017).** *Parisi formula for
  the ground state energy in the mixed p-spin model*, Annals of
  Probability 45(6B), 4617–4631. [Version 2][auffinger-chen].
  The variational formula and attainment used in Section 3.2.
- **Aukosh Jagannath and Ian Tobasco (2016).** *A dynamic programming
  approach to the Parisi functional*, Proceedings of the American
  Mathematical Society 144, 3135–3150. [Version 4][jt-control].
  The control method, with finite-temperature terminal data; it is not
  by itself the zero-temperature regularity theorem used here.
- **Wei-Kuo Chen, Madeline Handschy and Gilad Lerman (2018).** *On the
  energy landscape of the mixed even p-spin model*, Probability Theory
  and Related Fields 171, 53–95. [Version 4][chl-optimality].
  Proposition 4 gives the first-variation formula used in Section 5.1;
  the proof of Theorem 6 gives the zero-candidate descent.
- **Antonio Auffinger, Wei-Kuo Chen and Qiang Zeng (2020).** *The SK model
  is infinite step replica symmetry breaking at zero temperature*.
  [Version 2][acz], Proposition 1 and Remark 7. Near-ground overlap pairs
  and the earlier terminal-plateau observation.
- **OpenAI (2026b).** *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*, 25 September 2026.
  [Pinned manuscript][qaoa-manuscript]. The separate circuit theorem.
- **Joao Basso, Edward Farhi, Kunal Marwaha, Benjamin Villalonga and
  Leo Zhou (2022).** *The Quantum Approximate Optimization Algorithm
  at High Depth for MaxCut on Large-Girth Regular Graphs and the
  Sherrington-Kirkpatrick Model*. [Full preprint, version 3][bfmvz],
  §7, equation (7.2). The eventual-optimality conjecture.
<!-- /passage:source-record -->

[support-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean
[support-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35
[support-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.json
[value-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean
[value-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16
[support-manuscript]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
[support-regularity]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex
[support-signs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/signs.tex
[support-certificate]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex
[support-curvature]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex
[support-variation]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex
[support-consequences]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex
[qaoa-manuscript]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf
[auffinger-chen]: https://arxiv.org/abs/1606.05335v2
[chen-support]: https://arxiv.org/abs/2607.18032v1
[support-density]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/order-parameter-regularity.tex
[bfmvz]: https://arxiv.org/abs/2110.14206v3
[chl-optimality]: https://arxiv.org/abs/1609.04368v4
[jt-control]: https://arxiv.org/abs/1502.04398v4

[acz]: https://arxiv.org/abs/1703.06872v2
