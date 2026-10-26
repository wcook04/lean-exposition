---
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
---

# Why the SK order parameter has no gaps

## A variational argument from contact to strict curvature

Expository draft, 25 October 2026

<!-- passage:opening -->
The Sherrington–Kirkpatrick (SK) model asks us to choose signs that
maximise a random sum of pair interactions. The Parisi formula expresses
the limiting maximum through a nondecreasing function, the **order
parameter**. We explain why a minimising order parameter cannot be
constant on any interval below one: its increment measure has no gaps.

The proof compares two consequences of a hypothetical gap. Minimality
fixes the values and bounds the slopes of an auxiliary curve at its
endpoints. An analytic estimate makes the derivative strictly convex
between them, leaving too little area to connect the required values.
Initial and terminal gaps need separate arguments. We then return to
the spins: a theorem about their energy landscape gives nearly optimal
configurations at every prescribed approximate overlap.

We follow the quantitative proof in [OpenAI (2026a)][support-manuscript];
[Hong-Bin Chen (2026), Theorem 1.3][chen-support] had already proved
full support by a different method. The estimate used here makes the
final contradiction a direct comparison of areas. We assume calculus,
integration against measures and expectation. With that background,
the reader can reconstruct the no-gap argument from the analytic
inputs stated at their uses. The stochastic calculation in Section 3.3
and the explanation of strict curvature in Section 7 are optional;
the full analytic proofs remain in the cited sources.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. The finite optimisation problem

At each of $n$ positions, or **sites**, we choose a sign $\sigma_i\in\{-1,1\}$,
called a **spin**. A configuration is the vector
$\sigma=(\sigma_1,\ldots,\sigma_n)$.
For each unordered pair choose an independent standard Gaussian
$J_{ij}$, a normal random variable with mean zero and variance one.
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
$\max_\sigma H_2(\sigma)=|J_{12}|/\sqrt2$. For many spins, we seek
the limiting expected maximum per spin,

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

Overlap is also the quantity that determines the energy covariance.
For fixed $\sigma,\tau$, put $v_i=\sigma_i\tau_i$. Independence
of the couplings and $v_i^2=1$ give

$$
\mathbb E[H_n(\sigma)H_n(\tau)]
=\frac1n\sum_{i<j}v_iv_j
=\frac{(\sum_i v_i)^2-n}{2n}
=\frac n2 R(\sigma,\tau)^2-\frac12.
$$

Dividing by $n$ gives the limiting covariance
$\xi(t)=t^2/2$. For exact covariance
$n\xi(R)$, add the same independent centred Gaussian of variance $1/2$
to every energy; this leaves the expected maximum unchanged. Reversing
one configuration's signs preserves its energy and reverses its
overlap with another. We next define deterministic candidate values
indexed by nonnegative overlap scales $t$. The Parisi theorem in
Section 3 identifies their minimum with the limiting spin optimum;
that connection is an external input, not a change of variables in
the finite maximisation.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

An admissible **order parameter** is a function
$\gamma:[0,1)\to[0,\infty)$ that is nondecreasing, right-continuous
and integrable. It assigns a cumulative weight to each overlap scale $t$;
these weights will enter the variational formula. They are not probabilities
of overlaps sampled from a finite system. The associated **Stieltjes
measure** $\mu_\gamma$ records where the weight increases:

$$
\mu_\gamma([0,t])=\gamma(t),\qquad
\mu_\gamma((a,b])=\gamma(b)-\gamma(a).
$$

The first equation allows mass $\gamma(0)$ at zero. Positive mass
concentrated at one point is called an **atom**. The measure is finite
on every $[0,T]$ with $T<1$, although its total mass may be infinite.
It is not required to be a probability measure. A unit of mass at $s$ contributes to $\gamma(t)$ at every $t\ge s$.
Integrating that contribution over $t$ gives

$$
\int_0^1\gamma(t)\,dt
=\int_{[0,1)}\left(\int_s^1dt\right)\mu_\gamma(ds)
=\int_{[0,1)}(1-s)\,\mu_\gamma(ds)<\infty.
$$

The **support** consists of points every neighbourhood of which has
positive measure. Neighbourhoods are taken within $[0,1)$: the endpoint
one is not part of the domain. Full support therefore means that every
nonempty relative open interval has positive mass. It is equivalent to
strict increase of $\gamma$. Indeed, full support gives
$\mu_\gamma((a,b])>0$ whenever $a<b$; conversely, strict increase
gives positive mass on a smaller interval inside every neighbourhood.

For example, the admissible candidate

$$
\gamma(t)=
\begin{cases}
t,&0\le t\le1/3,\\
1/3,&1/3\le t\le2/3,\\
t-1/3,&2/3\le t<1
\end{cases}
$$

has a gap on $(1/3,2/3)$. Its measure has density one outside that
interval and zero inside it: the measure of a set is the integral of
this density over the set. Both endpoints of the gap remain in the
support. The upper curve in Figure 1 stays positive across the gap;
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
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

### 3.1 An auxiliary optimisation

To assign a value to $\gamma$, we first solve a one-dimensional control
problem: bias a noisy path so that its final position is large in
absolute value, while paying a running cost for the bias. Varying $\gamma$ will then reveal where a
minimiser can have mass. Here the overlap scale $t$ plays the role of
time; the path is auxiliary, not a motion of the spins.

The auxiliary noise is Brownian motion $B$: a continuous random path starting at zero, with
independent centred Gaussian increments, where $B_s-B_t$ has variance $s-t$.
Choose a **control** $\alpha_s\in[-1,1]$: at each time $s$, this
rule chooses a response using only the Brownian increments observed
since the starting time $t$. The rule must be measurable and must not
use future noise; the formal requirement is progressive measurability.
For a starting position $x$, set

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

The function $\Phi_\gamma(t,x)$ gives the best expected reward,
less the running cost, when we start at time $t$ in state $x$.
Inside the absolute value, noise and control change that state before
the final reward is paid. The reward is a one-spin optimisation,
$|x|=\max_{\sigma\in\{-1,1\}}x\sigma$. Expectation here averages
over Brownian paths, with $\gamma$ fixed. The **Parisi functional**
assigns the candidate its value:

$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
-\frac12\int_0^1t\gamma(t)\,dt.
$$

The inner supremum chooses a response for fixed $\gamma$; the outer
problem minimises $\mathcal P$ over $\gamma$.
The ground-state Parisi formula and attainment give

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

Every candidate therefore supplies an upper bound; minimisation finds
the sharpest one. The variational equality and
attainment come from [Auffinger–Chen (2017), Theorem 1 and the proof of
Lemma 3][auffinger-chen]; Gaussian concentration also gives the
expected-value form used here. The no-gap theorem assumes a minimiser and
proves a property of it; it does not prove existence. For comparison,
$\gamma=0$ gives $\Phi_0(t,x)=\mathbb E|x+\sqrt{1-t}Z|$ and
$\mathcal P(0)=\sqrt{2/\pi}$ for a standard Gaussian $Z$.
Evaluating this candidate alone does not establish minimality.

### 3.2 The best response and the path it generates

At $t=1$ there is no noise or response left to accumulate, so the value
is $|x|$. At earlier times it includes the best remaining response.
Its partial differential equation (PDE) runs backward from that final value:

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

Write $u=\partial_x\Phi_\gamma$ for its spatial slope and
$a=\partial_{xx}\Phi_\gamma$ for its spatial curvature. The source
proves convexity and $|u|\le1$, hence $a\ge0$. The equation expresses
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

At slope $u$, completing a square shows which response to choose:

$$
\gamma vu-\tfrac12\gamma v^2
=\tfrac12\gamma u^2-\tfrac12\gamma(v-u)^2.
$$

Since $\gamma\ge0$ and $|u|\le1$, $v=u$ attains the supremum,
yielding the stated PDE. This calculation explains the equation;
justifying the recursion and the Taylor expansion requires the
control representation and regularity results. See
[Auffinger–Chen, Theorem 2][auffinger-chen] for the zero-temperature
control formula and [Jagannath–Tobasco, Lemma 18][jt-control] for the
control method with finite-temperature terminal data. The extension
to the coefficients used here is in
[OpenAI (2026a), Lemmas 2.1–2.2][support-regularity].

Under the slope response the position follows

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

This random path is the **associated diffusion**. The response is a
**feedback control**: at each time it uses the slope at the current
state $X_t$. An atom of mass $c$ at scale $s$ gives $\gamma(t)=c\mathbf1_{[s,1)}(t)$: it switches on
both the drift and the running cost from that scale onward. It does
not make $X$ jump, because the accumulated drift is a time integral.
The path's average squared slope response defines the deterministic curve

$$
q(t):=\mathbb E[u(t,X_t)^2].
$$

The first variation will show that $\tfrac12(q(t)-t)$ is the
first-order cost density for changes in $\gamma$. This makes $q$
useful: optimality first forces $q(t)=t$ where the minimiser has mass;
excluding gaps then extends that equality everywhere.

### 3.3 How the squared response grows

For any admissible candidate, the facts needed below are

$$
q\in C^1([0,1)),\qquad q(0)=0,\qquad 0\le q(t)\le1,
\qquad q'(t)=\mathbb E[a(t,X_t)^2].
$$

Thus spatial curvature controls growth of the squared response.
Derivatives at zero are from the right, and $q'$ is continuous even
across jumps of $\gamma$. These facts do not assert $q=t$ for a general
candidate. They follow from [OpenAI (2026a), Lemmas 2.1–2.2][support-regularity];
readers who use them as inputs can continue to Section 4.
The following calculation explains the moment identity.

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

The cumulative function determines its measure uniquely; for a fixed
Brownian motion the associated diffusion is unique by the cited
regularity results. The theorem requires a minimiser,
not merely an admissible candidate. Zero field supplies $q(0)=0$;
$\xi''=1$ enters the curvature estimate. The statement does not cover
nonzero field or general mixed-spin covariance functions.
<!-- /passage:full-support-statement -->

<!-- passage:first-variation -->
## 5. Why a flat interval cannot minimise

### 5.1 Allowed changes and their first-order cost

The **first variation** in a direction $\eta$ is the derivative at
zero of $\varepsilon\mapsto\mathcal P(\gamma+\varepsilon\eta)$.
At a minimum its right derivative is nonnegative whenever small
$\varepsilon\ge0$ leave the candidate admissible. It need not vanish:
the opposite change may violate nonnegativity or monotonicity.
Precisely, let $\eta\in L^1(0,1)$ and suppose
$\gamma+\varepsilon\eta$ stays admissible for every
$0\le\varepsilon\le\varepsilon_0$, for some $\varepsilon_0>0$.
[OpenAI (2026a), Lemma 6.1][support-variation] proves

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

Here $q$ belongs to the unperturbed candidate $\gamma$.
The term $-t/2$ comes from the explicit penalty in $\mathcal P$;
$q(t)/2$ is the sensitivity of the reoptimised control value. The latter
is the analytic content of the formula, not differentiation with a fixed
control. The proof compares control values and bounds the terminal
remainder by the $L^1$ tail of $\eta$; related zero-temperature
variation formulas are in [Chen–Handschy–Lerman (2018),
Propositions 2–4][chl-optimality].
<!-- /passage:first-variation -->

<!-- passage:zero-candidate -->
**A candidate that fails the test.** Return to $\gamma=0$. Every control
then gives the same value, since both its drift and its cost vanish.
The slope response is still well defined. With $F_{\mathrm G}$ the
standard normal distribution function, the heat formula gives

$$
X_t=B_t,\qquad
u_0(t,x)=2F_{\mathrm G}\!\left(\frac{x}{\sqrt{1-t}}\right)-1,
\qquad
a_0(t,x)=\sqrt{\frac2{\pi(1-t)}}e^{-x^2/(2(1-t))}.
$$

The formula for $u_0$ is the expected sign of $x+\sqrt{1-t}Z$:
it subtracts the probability of a negative final state from that of
a positive one. Here $u_0$, not an arbitrarily chosen optimal control,
defines $q_0$. Using $\mathbb E e^{-B_t^2/(1-t)}=\sqrt{(1-t)/(1+t)}$ in the
moment identity and then integrating from zero yields

$$
q_0'(t)=\frac2{\pi\sqrt{1-t^2}},\qquad
q_0(t)=\frac2\pi\arcsin t.
$$

At the fixed state zero, symmetry gives $u_0(1/2,0)=0$.
But $q_0$ averages the square at the random state $B_{1/2}$, and
$q_0(1/2)=1/3$. Equality $q=t$ is not a definition.
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

<!-- passage:contact-and-gap -->

Adding a small atom at scale $s$ raises the cumulative function at
*every* later scale. It is always allowed: the total mass is not
fixed, so no compensating removal is required. Its direction is
$\eta(t)=\mathbf1_{[s,1)}(t)$. Thus

$$
D\mathcal P(\gamma)[\mathbf1_{[s,1)}]
=\frac12\int_s^1(q(t)-t)\,dt=:\frac12G(s).
$$

For the candidate in Figure 1, adding $\varepsilon$ mass at $s=1/2$
creates a jump of height $\varepsilon$ there and raises the entire
remaining curve by $\varepsilon$. This explains the tail integral:
$G(s)/2$ is the marginal cost of placing mass at $s$. At a minimiser,
$G(s)\ge0$ for every $s<1$.

We can also remove a fraction of existing mass on $K=[0,T]$, $T<1$.
The perturbed measure $(1-\varepsilon\mathbf1_K)\mu_\gamma$
is nonnegative for $0\le\varepsilon\le1$; its cumulative function is
$\gamma(t)-\varepsilon\mu_\gamma(K\cap[0,t])$. Thus the direction
$\eta_K(t)=-\mu_\gamma(K\cap[0,t])$ is admissible.
For Figure 1, take $K=[0,1/3]$. Then $\eta_K(t)=-\min(t,1/3)$:
the perturbed curve has slopes $1-\varepsilon$, $0$, $1$ on its
three pieces, and plateau height $(1-\varepsilon)/3$. It remains
nonnegative and nondecreasing for $0\le\varepsilon\le1$.
This example verifies admissibility; it does not assume that the
pictured candidate minimises the functional.

Return now to a minimiser. Local finiteness makes $\eta_K$ bounded.
As in the weighted-mass calculation in Section 2, interchanging the
integrals converts a cumulative change into a cost per unit of mass;
$|q(t)-t|\le1$ justifies the interchange. We obtain

$$
0\le D\mathcal P(\gamma)[\eta_K]
=-\frac12\int_KG(s)\,\mu_\gamma(ds).
$$

Since $G\ge0$, this integral must be zero. If $G$ were positive at a
support point, continuity would make it positive throughout a
neighbourhood of positive measure, contradicting this equality for a
large enough $T<1$. Therefore $G=0$ on the support. This equality is
called **contact**: the nonnegative function touches zero there.
Removing a fraction of existing mass makes the argument valid for
continuous measures too: subtracting an atom where none exists would
not be an admissible change.

### 5.2 Contact gives endpoint conditions

We need information about $q$ at the ends of a possible gap. An interior
support point $s$ is a minimum of $G$. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$, ordinary calculus gives

$$
q(s)=s,\qquad q'(s)\le1.
$$

At zero, if it belongs to the support, contact and symmetry give
$G(0)=q(0)=0$. The expansion
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$ and nonnegativity imply
$q'(0)\le1$. This one-sided argument includes an atom at zero.

### 5.3 Strict curvature creates an impossible integral

The support is relatively closed in $[0,1)$. Every missing point lies
in a maximal interval of its complement. Such an interval has two
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

The first two conditions require the average of $q'$ across the gap
to be one. The next input will force it below one throughout.

**Strict-curvature input ([OpenAI (2026a), Proposition 5.1][support-curvature]).**
For any admissible coefficient equal to $c>0$ on an open interval,
its moment curve satisfies, strictly inside that interval,

$$
q'''(t)\ge\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(r<t<s).
$$

Section 7 explains how this sign is obtained after expectation.
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

**Initial gap with zero outside the support.** If $[0,s)$ is missing
and $s<1$ is the first support point, then $\gamma=0$ on this interval.
The positive-curvature bound vanishes. Instead the heat equation gives
$q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$ for $0<t<s$, so $q'$ is
strictly increasing. The strict inequality is only at positive times:
at zero, symmetry gives $\Phi_{xxx}(0,0)=0$.
Here $X_t=B_t$, but the heat equation evolves backward from
$\Phi_\gamma(s,\cdot)$, which still depends on the later coefficient.
The explicit arcsine formula for the globally zero candidate therefore
does not apply. For $0<t<s$, $B_t$ has a positive density, and
$\Phi_{xxx}(t,\cdot)$ cannot vanish identically: then the even
function $\Phi(t,\cdot)$ would be quadratic. Bounded slopes would
make it constant. But the zero control and Jensen's inequality give
$\Phi_\gamma(t,x)\ge\mathbb E|x+B_1-B_t|\ge|x|$, excluding constancy.
Thus $q'(t)<q'(s)\le1$. Symmetry supplies $q(0)=0$ without contact at
zero, while right contact gives $q(s)=s$. Integration again gives too
little area. The case with zero in the support was already included
in Section 5.3, using its atom and the one-sided slope bound.

**Terminal gaps.** Figure 2 requires contact at both ends. It cannot
handle a gap reaching one, which lies outside the domain. Even the
zero candidate has $q_0(t)\to1$ while $q_0'(t)\to\infty$; convergence
of the value supplies no endpoint slope bound. Instead
[OpenAI (2026a), Lemma 6.3][support-variation] proves the following
terminal estimate: if $\gamma=c$ on $(r,1)$ for a finite $c\ge0$, then
for some $C>0$ and all sufficiently late $t$,

$$
1-q(t)\ge C\sqrt{1-t}.
$$

The two bounds behind this estimate have different jobs. Fix an earlier
time inside the assumed plateau and a bounded interval containing
positive probability mass of the diffusion then. The source's explicit
transition kernel carries some of that mass to a neighbourhood of zero
with a density bounded below uniformly for late $t$. The elapsed time
from the fixed earlier time stays positive; this is not an estimate
obtained by extending compact-strip derivative bounds to one.

The second source bound is $1-u(t,x)^2\ge\kappa>0$ throughout
$|x|\le\sqrt h$, where $h=1-t$ and $t$ is sufficiently late.
On a constant terminal interval, the heat formula writes $u$ as a
positively weighted average of the final signs $+1$ and $-1$.
The source bounds both weights away from zero in this window, whose
width matches the remaining noise scale $\sqrt h$. If $m>0$ is
the density lower bound there, these two estimates give

$$
1-q(t)\ge\int_{-\sqrt h}^{\sqrt h}\kappa m\,dx
=2m\kappa\sqrt h.
$$

Both uniform bounds are source inputs under the terminal-plateau
hypothesis. The elementary integration explains the square root,
which dominates the smaller quantity $h$ near zero.

It follows that $q(t)-t\le(1-t)-C\sqrt{1-t}<0$ near one, and

$$
G(s)\le\frac{(1-s)^2}{2}-\frac{2C}{3}(1-s)^{3/2}<0
$$

for $s$ sufficiently close to one. This contradicts the nonnegativity
forced by adding mass. It also excludes the empty-support candidate
$\gamma=0$. The explicit late-step variation against that candidate
appears in [Chen–Handschy–Lerman, proof of Theorem 6][chl-optimality].
[Auffinger–Chen–Zeng, Remark 7][acz] had also observed that a minimiser
cannot have a terminal plateau; the estimate used here is OpenAI's
Lemma 6.3.

These cases exhaust the complement of the support. Contact now gives
$q(t)=t$ for every interior time, and symmetry includes zero.
Differentiating gives $\mathbb E[a(t,X_t)^2]=1$, completing the theorem.
<!-- /passage:endpoints -->

<!-- passage:overlap-payoff -->
## 6. Return to the spins

We can now return to the arrangement of nearly optimal spin choices.
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

At target overlap $1/2$, two nearly optimal choices can differ on
approximately one quarter of the sites; at target zero, on half.
The pair may depend on the chosen target and the couplings. This is
existence for each fixed target, not a statement about
typically sampled pairs or a procedure for finding them. The companion
*Long Reasoning Record*,
<span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="near-ground-overlaps">[§9.3, “Near-ground configurations at a prescribed overlap”](../long/reasoning-record.md#near-ground-overlaps)</span>,
gives the probability bound and the covariance adjustment.
<!-- /passage:overlap-payoff -->

<!-- passage:changed-cases -->
### A check on the area argument

**Question.** Suppose a differentiable function $f$ on $[2,5]$ has
$f(2)=2$, $f(5)=5$, $f'(2)=1/2$ and $f'(5)=3/2$. If $f'$ is
strictly convex, can these data hold? What changes if strict convexity
is weakened to convexity? The endpoint chord is now tilted, so a
pointwise comparison with the constant one is unavailable.

Try the comparison before reading the answer below.
<!-- /passage:changed-cases -->

<!-- passage:changed-case-answer -->
**Answer.** A strictly convex $f'$ lies below its endpoint chord.
That chord has mean height $(1/2+3/2)/2=1$, hence integral three.
Therefore $f(5)-f(2)=\int_2^5f'(t)\,dt<3$, contradicting the
prescribed values. With non-strict convexity the data are possible:
$f(t)=2+(t-2)/2+(t-2)^2/6$ has affine derivative and satisfies all
four endpoint values. The argument needs a strict loss of area; the
common endpoint upper bound of one in Figure 2 is convenient, not essential. This is a
calculus example, not a candidate SK moment function.
<!-- /passage:changed-case-answer -->

<!-- passage:curvature-mechanism -->
## 7. Where the strict-curvature input comes from

The proof in Section 5 used strict curvature on a positive constant
interval. This section explains how that expectation acquires a sign;
the full analytic proof remains in the cited sources. For this section, take any admissible
coefficient with $\gamma=c>0$ on an open interval, without assuming
minimality. Set $b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$ there.
Differentiating the PDE and applying Itô's rule gives

$$
q''=\mathbb E[b^2-2ca^3],\qquad
q'''=\mathbb E[d^2-12cab^2+6c^2a^4].
$$

The negative middle term prevents a pointwise positivity argument.
The source instead uses the spatial probability density $f_t(x)$ of
$X_t$. Its probability law $f_t(x)\,dx$ is a measure in $x$, distinct from the Stieltjes measure
$\mu_\gamma(ds)$ on overlap scales. For step coefficients
and smoothed terminal data, this density factors into positive functions
propagated from the two ends of the time interval. Bounds on their
logarithmic derivatives supply the signs needed in integration by parts.

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

At the step-coefficient, smooth-terminal stage, write
$R_c=d^2-12cab^2+6c^2a^4$. The source constructs a correction
$C$ from the spatial derivatives and the density factors, with

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

### Further reading

<!-- passage:density-and-approximation -->
Full support alone does not give a density. Additional differentiation
of the identities $q=t$ and $\mathbb E[a^2]=1$, followed by
another use of the integrated curvature estimate on locally constant
comparison coefficients, proves that $\gamma$
is smooth, $\gamma(0)=0$, and
$\mu_\gamma=\gamma'(t)\,dt$ with $\gamma'(t)>0$ for $0<t<1$
([OpenAI (2026a), Corollary 6.4][support-density]). The *Long Reasoning
Record*, <span class="pdf-companion" data-pdf-target="../long/reasoning-record.pdf" data-pdf-anchor="positive-density">[§§9.1–9.2](../long/reasoning-record.md#positive-density)</span>, supplies this additional argument; Chen's earlier
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
The Lean [implementation][support-proof],
[challenge statement][support-interface] and [Comparator configuration][support-config]
concern a minimiser's support and moment identities. They assume a
minimiser; they do not prove the external Parisi formula or attainment.
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
- **Antonio Auffinger and Wei-Kuo Chen (2017).** *Parisi formula for
  the ground state energy in the mixed p-spin model*, Annals of
  Probability 45(6B), 4617–4631. [Version 2][auffinger-chen].
  The variational formula and attainment used in Section 3.1.
- **Aukosh Jagannath and Ian Tobasco (2016).** *A dynamic programming
  approach to the Parisi functional*, Proceedings of the American
  Mathematical Society 144, 3135–3150. [Version 4][jt-control].
  The control method, with finite-temperature terminal data; it is not
  by itself the zero-temperature regularity theorem used here.
- **Wei-Kuo Chen, Madeline Handschy and Gilad Lerman (2018).** *On the
  energy landscape of the mixed even p-spin model*, Probability Theory
  and Related Fields 171, 53–95. [Version 4][chl-optimality].
  Zero-temperature analytic and variational results and the explicit
  zero-candidate descent.
- **Antonio Auffinger, Wei-Kuo Chen and Qiang Zeng (2020).** *The SK model
  is infinite step replica symmetry breaking at zero temperature*.
  [Version 2][acz], Proposition 1 and Remark 7. Near-ground overlap pairs
  and the earlier terminal-plateau observation.
- **Hong-Bin Chen (2026).** *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][chen-support],
  Theorem 1.3. Full support and smooth nonnegative density; the strict
  positivity cited in the further-reading note comes from the separate OpenAI corollary.
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
