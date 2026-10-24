---
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
---

# Why the SK order parameter has no gaps

## A variational argument from contact to strict curvature

Expository draft, 24 October 2026

<!-- passage:opening -->
The Sherrington–Kirkpatrick problem asks us to choose signs so that a
random quadratic expression is as large as possible. Its limiting value
has a variational description: minimise a functional over nonnegative,
nondecreasing functions $\gamma$ on $[0,1)$. The theorem explained here
says that a minimising function cannot be constant on any nontrivial interval.
Equivalently, the measure recording its increments gives positive mass
to every nonempty open interval.

The proof turns this assertion into a calculus contradiction. Minimality
imposes values and slope bounds at the ends of a hypothetical flat
interval. A strict curvature estimate then forces too little area under
the slope to connect those values. The final integration is elementary;
the estimate that makes it strict is the substantial analytic input.
We explain what that input says and why it is needed, then treat the
initial and terminal intervals, where the same picture cannot simply be
reused.

The reader needs differentiation, integration, probability measures and
expectation. Brownian motion, the auxiliary optimisation and the
stochastic differentiation used below are introduced when they become
necessary. The aim is to reconstruct the no-gap argument, not the
separate algorithmic constructions to which it contributes.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. The finite optimisation problem

There are $n$ indexed positions. At position $i$ we choose a sign
$\sigma_i\in\{-1,1\}$, called a **spin**; the position is also called
a **site**. A configuration is the vector $\sigma=(\sigma_1,\ldots,\sigma_n)$.
For each unordered pair choose an independent standard Gaussian
$J_{ij}$, a normal random variable with mean zero and variance one.
These coefficients, or **couplings**, are drawn once and then held
fixed while we maximise

$$
H_n(\sigma)=\frac1{\sqrt n}\sum_{1\le i<j\le n}J_{ij}\sigma_i\sigma_j.
$$

A positive coupling rewards equal signs; a negative one rewards opposite
signs. These preferences can conflict when many pairs share positions.
The factor $n^{-1/2}$ is part of the model and must be retained when
comparing limiting values.

For two spins, $H_2(\sigma)=J_{12}\sigma_1\sigma_2/\sqrt2$.
The two configurations with equal signs have value $J_{12}/\sqrt2$,
and the two with opposite signs have value $-J_{12}/\sqrt2$.
Thus $\max_\sigma H_2(\sigma)=|J_{12}|/\sqrt2$ and
$\frac12\mathbb E\max_\sigma H_2(\sigma)=1/(2\sqrt\pi)$.
This finite calculation is not the limiting value. The quantity of
interest is

$$
P_*:=\lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma),
$$

where expectation averages over the couplings after taking the maximum.
We use the maximisation convention throughout. **Zero temperature**,
or **ground-state value**, refers here to this extremal problem,
rather than an average that gives positive weight to nonmaximising
configurations. The model is **pure** because every term contains
exactly two spins, and has **zero external field** because there is
no additional term $h\sum_i\sigma_i$.

For two configurations define their overlap
$R(\sigma,\tau)=n^{-1}\sum_i\sigma_i\tau_i$, their average agreement
with a disagreement counted as $-1$. Independence gives

$$
\mathbb E[H_n(\sigma)H_n(\tau)]
=\frac n2 R(\sigma,\tau)^2-\frac12.
$$

Accordingly the covariance function used in the limiting variational
problem is $\xi(t)=t^2/2$. This specifies the normalisation of every
formula below. The existence and variational description of $P_*$ are
external theorems; the two-spin example does not supply them.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

An admissible **order parameter** is a function
$\gamma:[0,1)\to[0,\infty)$ that is nondecreasing, right-continuous
and integrable. Its argument $t$ is a scale in the variational problem,
not the number of spins or a temperature. The associated **Stieltjes
measure** $\mu_\gamma$ records cumulative increments:

$$
\mu_\gamma([0,t])=\gamma(t),\qquad
\mu_\gamma((a,b])=\gamma(b)-\gamma(a).
$$

The first equation includes an atom of mass $\gamma(0)$ at zero; an
atom is positive mass concentrated at one point. The measure is finite
on every $[0,T]$ with $T<1$, although its total mass may be infinite.
It is not required to be a probability measure. Integrability means

$$
\int_0^1\gamma(t)\,dt
=\int_{[0,1)}(1-s)\,\mu_\gamma(ds)<\infty.
$$

The **support** consists of points every neighbourhood of which has
positive measure. Neighbourhoods are taken within $[0,1)$: the endpoint
one is not part of the domain. Full support therefore means that no
interval of scales is missing from the increments. This is equivalent
to strict increase of $\gamma$.

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
it is its *increments* that vanish.

```{=latex}
% Modified 2026-10-24. Derived from OpenAI/math Figure 1 (Apache-2.0).
% Axial composition, paired reference heights, dotted guides and open region
% are adapted from upstream/gap-convexity.original.tex; see SOURCE_PROVENANCE.json.
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,font=\small,line cap=round]
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
  \begin{scope}[yshift=-4.05cm]
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
The endpoint $1$ is excluded, as the open circles indicate. Values of the
density at individual points do not affect the measure. These are exact
candidate plots, not a computed minimiser. The paired-axis composition
adapts Figure 1 of OpenAI (2026a), credited in Section 5.3.}
\label{fig:support-increments}
\end{figure}
```

A constant candidate $\gamma(t)=c>0$ makes the distinction sharper:
its measure is $c\delta_0$, supported only at zero. Positivity of the
function is not the conclusion we seek. Nor does full support alone
assert a density: a measure with positive masses at a dense countable
set has full support. We will prove the support claim before mentioning
the source's stronger density conclusion.
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

### 3.1 An auxiliary optimisation

A functional assigns a number to a function. To assign a value to
$\gamma$, first solve a one-dimensional optimisation driven by
Brownian motion $B$: a continuous random path starting at zero, with
independent centred Gaussian increments, where $B_s-B_t$ has variance $s-t$.
Choose a response $\alpha_s\in[-1,1]$ using only increments observed
between the starting time $t$ and the present time $s$. Such a response
is called an **adapted control**; it cannot anticipate future noise.
For a starting position $x$, set

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

The first term rewards final absolute position and the second charges
for responding. The terminal reward is itself a one-spin optimisation,
$|x|=\max_{\sigma\in\{-1,1\}}x\sigma$. Here expectation is over
Brownian paths with $\gamma$ fixed, not over the finite couplings.
The paths are auxiliary real-valued variables, not motions of spins.
The candidate's value is

$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
-\frac12\int_0^1t\gamma(t)\,dt.
$$

The inner supremum chooses a response for a fixed coefficient; the
outer problem chooses the coefficient to minimise $\mathcal P$.
The ground-state Parisi formula and attainment give

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

Thus every candidate supplies an upper bound on the limiting maximum,
and minimisation searches for the sharpest bound. Both equality and
attainment come from [Auffinger–Chen (2017), Theorem 1 and the proof of
Lemma 3][auffinger-chen]. The no-gap theorem assumes a minimiser and
proves a property of it; it does not prove existence. For comparison,
$\gamma=0$ gives $\Phi_0(t,x)=\mathbb E|x+\sqrt{1-t}Z|$ and
$\mathcal P(0)=\sqrt{2/\pi}$ for a standard Gaussian $Z$.
Evaluating this candidate alone does not establish minimality.

### 3.2 Slope, curvature and a random path

The control value satisfies the backward partial differential equation

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

Write $u=\partial_x\Phi_\gamma$ for its spatial slope and
$a=\partial_{xx}\Phi_\gamma$ for its spatial curvature. The source
proves convexity and $|u|\le1$, hence $a\ge0$. The reason to use the
slope as a response is visible by completing a square. At slope $u$,
the local benefit minus cost of response $\alpha$ is

$$
\gamma\alpha u-\frac12\gamma\alpha^2
=\frac12\gamma u^2-\frac12\gamma(\alpha-u)^2.
$$

The allowed response $\alpha=u$ maximises this expression because
$\gamma\ge0$. Applying that choice over a short interval and then
continuing optimally gives the PDE; Brownian variance supplies its
second-derivative term. This control viewpoint follows the method of
[Jagannath–Tobasco (2016)][jt-control]. The zero-temperature terminal
data and estimates used here require the additional results in
[OpenAI (2026a), §2][support-regularity].

Under the slope response the position follows

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

This is the **associated diffusion**: noise plus the accumulated
response. We need it to define the deterministic function

$$
q(t):=\mathbb E[u(t,X_t)^2].
$$

The difference $q(t)-t$ will measure the first-order cost of changing
$\gamma$. The notation does not identify $q(t)$ with a finite overlap,
nor assume $q(t)=t$; that equality will follow from optimality.

The analytic foundation matters here. For every fixed $T<1$, the
source bounds spatial derivatives of positive order uniformly on
$[0,T]\times\mathbb R$, proves existence and uniqueness of the
associated path, and justifies the PDE and stochastic identities by
approximation. It begins with step coefficients and smoothed terminal
data, then passes to admissible integrable coefficients. Time
derivatives at jumps of $\gamma$ are not assumed classical. The
restriction $T<1$ avoids the corner of $|x|$ at the terminal time.
These are inputs, not consequences of the square completion.

### 3.3 Why the curvature differentiates the moment

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
value. This does not make its realised path constant. Zero external
field gives symmetry and $M_0=u(0,0)=0$. Applying Itô's rule once more
to $M_t^2$ gives

$$
q(0)=0,\qquad
q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds,\qquad
q'(t)=\mathbb E[a(t,X_t)^2].
$$

The stochastic integral has expectation zero because each coefficient
uses only the past, while the next Brownian increment has conditional
mean zero. The quadratic term contributes its variance, producing
$a^2\,dt$. The source's approximation and regularity justify these
identities for admissible $\gamma$. At zero, derivatives are from the
right. We now have the objects required for the proof: $q(0)=0$,
$0\le q\le1$ and $q'=\mathbb E[a^2]$.
<!-- /passage:value-and-diffusion -->

<!-- passage:full-support-statement -->
## 4. The full-support theorem

**Source theorem ([OpenAI (2026a), Theorem 1.1][support-manuscript]).**
In the pure, zero-field model with $\xi(t)=t^2/2$, let $\gamma$ be an
admissible integrable minimiser of the functional above, on a probability
space carrying standard Brownian motion. Then a Stieltjes measure and
an associated diffusion exist. Every measure satisfying
$\mu([0,t])=\gamma(t)$ has full relative support on $[0,1)$, and
$\gamma$ is strictly increasing. For every associated diffusion and
all $0\le t<1$,

$$
\mathbb E[u(t,X_t)^2]=t,\qquad
\mathbb E[a(t,X_t)^2]=1.
$$

[Hong-Bin Chen (2026), Theorem 1.3][chen-support] had already proved
full relative support and representation by a smooth nonnegative
density. Here we explain OpenAI's quantitative no-gap argument. The
stated theorem does not itself assert a density and does not cover
nonzero field or mixed-spin covariance functions.

The proof has two distinct inputs. A variational formula determines
where $q$ must meet the line $t$. An analytic curvature estimate on a
constant interval prevents $q$ from joining two such contact points
with the required endpoint slopes. Neither input alone excludes a gap.
<!-- /passage:full-support-statement -->

<!-- passage:contact-and-gap -->
## 5. Why a flat interval cannot minimise

### 5.1 Allowed changes and their first-order cost

The **first variation** in a direction $\eta$ is the derivative at
zero of $\varepsilon\mapsto\mathcal P(\gamma+\varepsilon\eta)$.
At a minimum its right derivative is nonnegative whenever small
$\varepsilon\ge0$ leave the candidate admissible. It need not vanish:
the opposite change may violate nonnegativity or monotonicity.
The source proves, for admissible integrable directions,

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

This is a theorem about the candidate's own PDE and diffusion, not a
formula for an arbitrary test curve $q$. Its derivation compares
control values and passes through the terminal limit; see
[OpenAI (2026a), §6][support-variation] and the zero-temperature
variational results of [Chen–Handschy–Lerman (2018),
Propositions 2–4][chl-optimality].

Adding a small atom at scale $s$ raises the cumulative function at
*every* later scale. It is always allowed, and its direction is
$\eta(t)=\mathbf1_{[s,1)}(t)$. Consequently define

$$
G(s):=\int_s^1(q(t)-t)\,dt.
$$

Then $G(s)/2$ is the first-order cost of adding unit mass at $s$.
The tail integral, rather than the residual at a single time, records
the whole change. Minimality gives $G(s)\ge0$ for every $s<1$.

We can also remove a fraction of existing mass on $K=[0,T]$, $T<1$.
The direction is $\eta_K(t)=-\mu_\gamma(K\cap[0,t])$.
For $0\le\varepsilon\le1$, this multiplies the measure on $K$ by
$1-\varepsilon$ and preserves admissibility. Local finiteness and
$|q(t)-t|\le1$ allow us to interchange the integrals, giving

$$
0\le D\mathcal P(\gamma)[\eta_K]
=-\frac12\int_KG(s)\,\mu_\gamma(ds).
$$

Since $G\ge0$, this integral must be zero. If $G$ were positive at a
support point, continuity would make it positive throughout a
neighbourhood of positive measure, contradicting this equality for a
large enough $T<1$. Therefore $G=0$ on the support. This equality is
called **contact**: the nonnegative function touches zero there.
Removing a fraction of mass on an interval, rather than just removing
atoms, makes the argument valid for measures whose mass is spread
continuously as well.

### 5.2 Contact gives endpoint conditions

An interior support point $s$ is a minimum of $G$. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$, ordinary calculus gives

$$
q(s)=s,\qquad q'(s)\le1.
$$

At zero, if it belongs to the support, contact and symmetry give
$G(0)=q(0)=0$. The expansion
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$ and nonnegativity imply
$q'(0)\le1$. This is a one-sided argument, and includes an atom at
zero. We have obtained precisely the endpoint data needed below.

### 5.3 Strict curvature creates an impossible integral

Suppose $(r,s)$ is a gap between support points, with
$0\le r<s<1$. The coefficient is constant there, say $\gamma=c$,
and contact imposes

$$
q(r)=r,\quad q(s)=s,\quad q'(r)\le1,\quad q'(s)\le1.
$$

For $c>0$, the analytic core of the source proves

$$
q'''(t)\ge\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(r<t<s).
$$

Because $q'''=(q')''$, the function $q'$ is strictly convex: between
two points its graph lies strictly below their joining chord. Hence

$$
q'(t)<\frac{s-t}{s-r}q'(r)+\frac{t-r}{s-r}q'(s)\le1
\qquad(r<t<s).
$$

\begin{figure}[H]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,font=\small,line cap=round]
  \fill[black!8] (0,3.1) -- (8,3.1) -- (8,2.2)
     .. controls (5.3333,.25) and (2.6667,.10) .. (0,1.8) -- cycle;
  \draw[->] (-1.9,0) -- (8.7,0) node[right] {$t$};
  \draw[->] (-1.9,0) -- (-1.9,3.5) node[above] {$q'(t)$};
  \draw[gray!70] (-1.9,3.1) -- (8.25,3.1);
  \node[left] at (-1.9,3.1) {$1$};
  \draw[densely dashed,gray!75] (0,1.8) -- (8,2.2)
    node[midway,above=3pt,text=black,fill=white,inner sep=1pt]
       {endpoint chord};
  \draw[very thick,black] (0,1.8)
    .. controls (2.6667,.10) and (5.3333,.25) .. (8,2.2);
  \draw[dotted,gray!80] (0,0) -- (0,1.8);
  \draw[dotted,gray!80] (8,0) -- (8,2.2);
  \fill (0,1.8) circle (1.6pt);
  \fill (8,2.2) circle (1.6pt);
  \node[below] at (0,0) {$r$};
  \node[below] at (8,0) {$s$};
  \node[above left=3pt] at (0,1.8) {$q'(r)\le1$};
  \node[above right=3pt] at (8,2.2) {$q'(s)\le1$};
  \node[below] at (4,.58) {strictly convex $q'$};
  \node at (4.4,2.7) {missing area};
\end{tikzpicture}
\caption{On a hypothetical positive constant interval $(r,s)$, contact
requires $q(s)-q(r)=s-r$. Strict convexity places $q'$ below its
endpoint chord, whose endpoint values are at most one. The shaded
area makes the integral of $q'$ strictly less than $s-r$. The curve
is schematic, not sampled SK diffusion data. Adapted from
\href{https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex}{Figure 1 of OpenAI (2026a)}, OpenAI/math (Apache 2.0).}
\end{figure}

Integration now gives $q(s)-q(r)<s-r$, whereas contact requires
$q(s)-q(r)=s-r$. The gap is impossible. For the candidate in Section 2,
a minimising plateau on $(1/3,2/3)$ would require the same increment
to be both equal to and strictly less than $1/3$.

The strict sign is the difficult part of the proof. It is not a
consequence of convexity of $\Phi_\gamma$ alone. Set
$b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$ on a constant interval.
Differentiating the PDE and applying Itô's rule gives

$$
q''=\mathbb E[b^2-2ca^3],\qquad
q'''=\mathbb E[d^2-12cab^2+6c^2a^4].
$$

The negative middle term prevents a direct positivity argument. The
source uses the law of $X_t$: for step coefficients and smoothed
terminal data, its density factors into two positive functions,
propagated from opposite ends of the time interval. Inequalities for
their logarithmic derivatives permit integration by parts. This adds
terms with expectation zero and exposes a positive remainder.
For comparison, for a sufficiently decaying differentiable $F$ and
standard Gaussian $Z$, integration by parts gives
$\mathbb E[F'(Z)-ZF(Z)]=0$; adding such an expression changes an
integrand without changing its mean. Here the diffusion density is
different, and its sign and boundary estimates must be proved.

The source's exact rational identity organises this calculation, but
the identity alone does not justify the integrations or their signs.
The resulting inequality is one *after expectation*, not pointwise
positivity of the displayed polynomial. Approximation then transfers
it to admissible coefficients by convergence of expectations of
polynomials in the first four spatial derivatives. The needed bounds
are uniform in space on each fixed interval below time one.
The complete inputs are [OpenAI (2026a), §3][support-signs],
[Lemma 4.1][support-certificate] and [Proposition 5.1][support-curvature].
The companion *Long Reasoning Record*, §4, “Strict curvature on a
constant interval”, expands this analytic step.
<!-- /passage:contact-and-gap -->

<!-- passage:endpoints -->
### 5.4 Initial, zero and terminal gaps

If the constant coefficient on a gap is zero, the preceding positive
lower bound vanishes. Instead the heat equation gives
$q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$ there, so $q'$ is
strictly increasing. To see strictness, noise accumulated over an
earlier part of the gap gives $X_t$ a positive density. Also
$\Phi_{xxx}(t,\cdot)$ cannot vanish identically: then the even
function $\Phi(t,\cdot)$ would be quadratic, incompatible with its
bounded slopes and bounded difference from $|x|$. Thus
$q'(t)<q'(s)\le1$, again giving too little area.

An initial gap $[0,s)$ has coefficient zero. Its left endpoint need
not be in the support, but symmetry still gives $q(0)=0$, which is all
the integral argument requires. If instead zero belongs to the support
and $(0,s)$ is missing, there must be positive mass at zero. The
positive-coefficient argument applies with the one-sided slope bound
from Section 5.2.

A terminal gap is different: we cannot use contact at one, because one
is outside the domain. On a putative terminal constant interval the
source proves, for some $C>0$ and all sufficiently late $t$,

$$
1-q(t)\ge C\sqrt{1-t}.
$$

Here is why the square root enters. The remaining Brownian noise has
standard deviation $\sqrt{1-t}$. For $|x|\le\sqrt{1-t}$ the
terminal Gaussian smoothing keeps both signs possible with probabilities
bounded away from zero, so $1-u(t,x)^2$ is bounded below by a positive
constant. The source's transition-density formula on the assumed
plateau bounds the density of $X_t$ below on this window, uniformly
for late $t$. Integrating across its width proves the estimate. This
uses the constant-interval formula, not an unproved general endpoint
regularity assumption.

It follows that $q(t)-t\le(1-t)-C\sqrt{1-t}<0$ near one, and

$$
G(s)\le\frac{(1-s)^2}{2}-\frac{2C}{3}(1-s)^{3/2}<0
$$

for $s$ sufficiently close to one. This contradicts the nonnegativity
forced by adding mass. It also excludes the empty-support candidate
$\gamma=0$. The explicit late-step variation against that candidate
already appears in [Chen–Handschy–Lerman, proof of Theorem 6][chl-optimality];
the terminal-plateau argument here follows
[OpenAI (2026a), §6][support-variation].

These cases exhaust the components of the complement of a relatively
closed support. Every scale below one is therefore a support point.
Contact gives $q(t)=t$ for interior times, and symmetry includes zero.
Differentiating gives $\mathbb E[a(t,X_t)^2]=1$, completing the
stated conclusions. The proof has used the whole sequence: admissible
mass changes, contact, strict interior curvature, and a separate
terminal estimate.
<!-- /passage:endpoints -->

<!-- passage:changed-cases -->
## 6. A changed-case check

**Question.** Suppose a differentiable function $f$ on $[2,5]$ has
$f(2)=2$, $f(5)=5$, $f'(2)=1/2$ and $f'(5)=3/2$. If $f'$ is
strictly convex, can these data hold? What changes if strict convexity
is weakened to convexity? The endpoint chord is now tilted, so a
pointwise comparison with the constant one is unavailable.

**Answer.** A strictly convex $f'$ lies below its endpoint chord.
That chord has mean height $(1/2+3/2)/2=1$, hence integral three.
Therefore $f(5)-f(2)=\int_2^5f'(t)\,dt<3$, contradicting the
prescribed values. With non-strict convexity the data are possible:
$f(t)=2+(t-2)/2+(t-2)^2/6$ has affine derivative and satisfies all
four endpoint values. The argument needs a strict loss of area; the
common endpoint upper bound of one in Figure 2 is convenient, not essential. This is a
calculus example, not a candidate SK moment function.
<!-- /passage:changed-cases -->

<!-- passage:density-and-approximation -->
## 7. Consequences beyond the no-gap argument

Full support alone says neither that a density exists nor that it is
positive at every point. Under the same pure, zero-field minimiser
hypotheses, [OpenAI (2026a), Corollary 6.4][support-density] further
proves that $\gamma$ is smooth on $[0,1)$, $\gamma(0)=0$, and
$\mu_\gamma=\gamma'(t)\,dt$ with $\gamma'(t)>0$ for $0<t<1$.
This needs additional differentiation and quantitative estimates.
Its proof belongs to the companion *Long Reasoning Record*, §§5.1–5.2,
“A further manuscript consequence: smooth density” and “Why the density
is strictly positive away from zero”; it is not an inference from the
support definition.
<!-- /passage:density-and-approximation -->

<!-- passage:scalar-identities -->
The moment identities also recover the optimal value. The source proves
that $u(t,X_t)$ has an almost-sure limit $U\in\{-1,1\}$ as $t\uparrow1$,
and that

$$
P_*=\int_0^1\mathbb E[a(t,X_t)]\,dt=\mathbb E[UB_1].
$$

The first moment $\mathbb E[a]$ here differs from the second moment
$\mathbb E[a^2]=1$ in the theorem. Terminal convergence and the Parisi
value identity are additional steps, given in
[OpenAI (2026a), Corollary 7.1][support-consequences] and the companion
*Long Reasoning Record*, §6, “Recovering the value from a martingale”.
Its §7, “A finite Gaussian spin and its adjacent correlations”, then
constructs finite approximations. Neither proof is supplied by this outlook.
<!-- /passage:scalar-identities -->

<!-- passage:qaoa-boundary -->
A separate construction uses this scalar value to obtain circuits for
the Quantum Approximate Optimization Algorithm (QAOA).
[OpenAI (2026b)][qaoa-manuscript] proves that for every
$\varepsilon>0$ there is a finite-depth QAOA circuit, with deterministic
angles chosen independently of $n$ and the couplings, whose limiting
expected reward per spin as $n\to\infty$ is at least
$P_*-\varepsilon$. The order matters: choose the circuit first, then
take the size limit. This is the eventual-optimality assertion
conjectured by [Basso–Farhi–Marwaha–Villalonga–Zhou, §7,
equation (7.2)][bfmvz]. The construction is a further theorem, not a
consequence of support alone. The companion *Long Reasoning Record*,
§9, “From the scalar formula to one ordinary QAOA word”, gives the
circuit synthesis, removal of auxiliary randomness and limit choices.
No circuit proof is needed for the no-gap argument above.
<!-- /passage:qaoa-boundary -->

<!-- passage:source-record -->
## Sources and scope of verification

The analytic proof reconstructed here is from the pinned OpenAI
full-support manuscript. Its Lean [implementation][support-proof],
[separately stated challenge][support-interface] and
[Comparator configuration][support-config] provide formal points of
comparison. The selected formal statement assumes a minimiser; it does
not establish the external Parisi formula or attainment. The scalar
[implementation][value-proof] and [challenge][value-interface] concern
the scalar identity cited in the outlook, not the complete circuit
theorem. Lean 4 and mathlib supply the proof-assistant infrastructure
([de Moura–Ullrich, 2021](https://doi.org/10.1007/978-3-030-79876-5_37);
[The mathlib Community, 2020](https://doi.org/10.1145/3372885.3373824)).

Source presence, compilation, declaration extraction and Comparator
acceptance are different observations. Earlier retained Comparator
attempts either could not start or stopped during solution builds after
exporting the challenges; they did not export or accept the solutions.
No accepted corrected research verdict is recorded at this draft.
The companion *Long Reasoning Record*, §11, “Source checks and finite
calculation”, records the verification evidence. These observations are
not a mathematical rejection or an
independent check of the entire analytic argument. No human reader
study is claimed for this exposition.

The following sources are used in the text; links select the editions
read for the stated results.

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
- **Hong-Bin Chen (2026).** *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][chen-support],
  Theorem 1.3. Full support and smooth nonnegative density; the strict
  positivity cited in Section 7 comes from the separate OpenAI corollary.
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
