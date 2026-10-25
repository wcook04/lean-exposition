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

The proof ends with calculus. Minimality fixes the values and bounds
the slopes of an auxiliary curve at the ends of a hypothetical gap.
Strict curvature then leaves too little area under its derivative to
connect those values. Endpoint cases need separate arguments.

We follow the quantitative proof in [OpenAI (2026a)][support-manuscript];
[Hong-Bin Chen (2026), Theorem 1.3][chen-support] had already proved
full support by a different method. Starting from calculus, probability
measures and expectation, we explain the stochastic identities' roles
and state the analytic inputs. Their proofs remain in the source;
the contact and area arguments are developed here.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. The finite optimisation problem

At each of $n$ positions we choose a sign $\sigma_i\in\{-1,1\}$,
called a **spin**. A configuration is the vector
$\sigma=(\sigma_1,\ldots,\sigma_n)$.
For each unordered pair choose an independent standard Gaussian
$J_{ij}$, a normal random variable with mean zero and variance one.
These coefficients, or **couplings**, are drawn once and then held
fixed while we maximise

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
overlap $1/2$; two disagreements would give zero. The overlap also
determines how their random scores are correlated: for fixed
$\sigma,\tau$, independence of the couplings gives

$$
\mathbb E[H_n(\sigma)H_n(\tau)]
=\frac n2 R(\sigma,\tau)^2-\frac12.
$$

Dividing by $n$ gives the limiting covariance
$\xi(t)=t^2/2$. For exact covariance
$n\xi(R)$, add the same independent centred Gaussian of variance $1/2$
to every energy; this leaves the expected maximum unchanged. Reversing
one configuration's signs preserves its energy and reverses its
overlap with another. The variational theorem uses nonnegative overlap
scales $t$; it is an external input, stated in Section 3.
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

The first equation includes an atom of mass $\gamma(0)$ at zero; an
atom is positive mass concentrated at one point. The measure is finite
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
one is not part of the domain. Full support therefore means that no
interval of scales is missing from the increments. This is equivalent
to strict increase of $\gamma$: every subinterval must contain positive
increments, not merely mass at one of its endpoints.

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
set has full support. Section 7 returns to the stronger density conclusion.
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

### 3.1 An auxiliary optimisation

To assign a value to $\gamma$, we first solve a one-dimensional control
problem: bias a noisy path to earn a large final reward, paying for the
response along the way. Varying $\gamma$ will then reveal where a
minimiser can have mass. Here the overlap scale $t$ plays the role of
time; the path is auxiliary, not a motion of the spins.

The auxiliary noise is Brownian motion $B$: a continuous random path starting at zero, with
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

Inside the absolute value, $x$ is the starting position, $B_1-B_t$ the
accumulated noise, and the integral the accumulated response. The second
term charges for that response. The final reward is a one-spin optimisation,
$|x|=\max_{\sigma\in\{-1,1\}}x\sigma$. Here expectation is over
Brownian paths with $\gamma$ fixed.
The candidate's value is

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

This random path is the **associated diffusion**. Its average squared
response defines the deterministic curve

$$
q(t):=\mathbb E[u(t,X_t)^2].
$$

The first variation will show that $\tfrac12(q(t)-t)$ is the
first-order cost density for changes in $\gamma$. This makes $q$
useful: optimality first forces $q(t)=t$ where the minimiser has mass;
excluding gaps then extends that equality everywhere.

### 3.3 How the squared response grows

The needed identity is $q'(t)=\mathbb E[a(t,X_t)^2]$: spatial curvature
controls growth of the squared response. The following calculation
explains it; the no-gap proof can also be read using the cited identity.

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
q(0)=0,\qquad
q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds,\qquad
q'(t)=\mathbb E[a(t,X_t)^2].
$$

The noise term has mean zero because its coefficient uses only past
observations; its squared increment contributes $a^2\,dt$.
Derivatives at zero are from the right. Also $0\le q\le1$.

These calculations use [OpenAI (2026a), Lemmas 2.1–2.2][support-regularity].
For each fixed $T<1$, the required spatial derivatives are bounded on
$[0,T]\times\mathbb R$, and step-coefficient and smooth-terminal
approximations justify the identities. The bounds depend on the coefficient
and strip. The PDE holds almost everywhere in time; $q$ and $q'$ are
continuous even across jumps. These are not bounds up to time one.
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

The measure and diffusion exist uniquely by the preceding construction
and the cited regularity results. The theorem requires a minimiser,
not merely an admissible candidate. Zero field supplies $q(0)=0$;
$\xi''=1$ enters the curvature estimate. The statement does not cover
nonzero field or general mixed-spin covariance functions.
<!-- /passage:full-support-statement -->

<!-- passage:contact-and-gap -->
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

The term $-t/2$ comes from the explicit penalty in $\mathcal P$;
$q(t)/2$ is the sensitivity of the reoptimised control value. The latter
is the analytic content of the formula, not differentiation with a fixed
control. The proof compares control values and bounds the terminal
remainder by the $L^1$ tail of $\eta$; related zero-temperature
variation formulas are in [Chen–Handschy–Lerman (2018),
Propositions 2–4][chl-optimality].

Adding a small atom at scale $s$ raises the cumulative function at
*every* later scale. It is always allowed, and its direction is
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
$\eta_K(t)=-\mu_\gamma(K\cap[0,t])$ is admissible. Local finiteness and
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

Suppose $(r,s)$ is a gap between support points, with
$0\le r<s<1$. The coefficient is constant there, say $\gamma=c$,
and contact imposes

$$
q(r)=r,\quad q(s)=s,\quad q'(r)\le1,\quad q'(s)\le1.
$$

The first two conditions require the average of $q'$ across the gap
to be one. For $c>0$, the next input will force it below one throughout.

**Strict-curvature input ([OpenAI (2026a), Proposition 5.1][support-curvature]).**
For any admissible coefficient equal to $c>0$ on an open interval,
its moment curve satisfies, strictly inside that interval,

$$
q'''(t)\ge\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\qquad(r<t<s).
$$

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
area is $\int_r^s(1-q'(t))\,dt$: strict convexity makes it positive,
whereas contact requires zero. The two comparisons are
$q'<\text{endpoint chord}\le1$. The curve is schematic. Adapted from
\href{https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex}{Figure 1 of OpenAI (2026a)}, OpenAI/math (Apache 2.0).}
\end{figure}

Integration gives $q(s)-q(r)<s-r$, contradicting contact. For the candidate in Section 2,
a minimising plateau on $(1/3,2/3)$ would require the same increment
to be both equal to and strictly less than $1/3$.

The strict sign is the difficult part of the proof. Set
$b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$ on a constant interval.
Differentiating the PDE and applying Itô's rule gives

$$
q''=\mathbb E[b^2-2ca^3],\qquad
q'''=\mathbb E[d^2-12cab^2+6c^2a^4].
$$

The negative middle term prevents a pointwise positivity argument.
The source instead uses the density of $X_t$. For step coefficients
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

The source chooses corrections of this form from the spatial derivatives
and density factors. Its rational identity rewrites the corrected
expression as nonnegative terms with a remainder at least
$c^2a^4/1000$ after rescaling. The sign bounds and vanishing boundary
products justify that use of the identity. The positivity is therefore
*after expectation*; the raw displayed polynomial can be negative.

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
and the companion *Long Reasoning Record*, §§4.4–4.5, “How the signs
make a correction with zero expectation useful” and “Passing the
integrated inequality to an integrable coefficient”.
<!-- /passage:contact-and-gap -->

<!-- passage:endpoints -->
### 5.4 Initial, zero and terminal gaps

**Zero coefficient.** If $c=0$, the positive lower bound vanishes. Instead the heat equation gives
$q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$ there, so $q'$ is
strictly increasing. To see strictness, noise accumulated over an
earlier part of the gap gives $X_t$ a positive density. Also
$\Phi_{xxx}(t,\cdot)$ cannot vanish identically: then the even
function $\Phi(t,\cdot)$ would be quadratic. Bounded slopes would
make it constant, contradicting its bounded difference from $|x|$. Thus
$q'(t)<q'(s)\le1$, again giving too little area.

**Initial gaps.** If zero is outside the support, an initial gap
$[0,s)$ has coefficient zero. Its left endpoint need
not be in the support, but symmetry still gives $q(0)=0$, which is all
the integral argument requires. If instead zero belongs to the support
and $(0,s)$ is missing, there must be positive mass at zero. The
positive-coefficient argument applies with the one-sided slope bound
from Section 5.2.

**Terminal gaps.** Figure 2 requires contact at both ends. It cannot
handle a gap reaching one, which lies outside the domain. Instead
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

Now put $h=1-t$. On this constant terminal interval, $u(t,x)$ is a
weighted average of the final signs $+1$ and $-1$. The remaining
Brownian noise has standard deviation $\sqrt h$, so in the window
$|x|\le\sqrt h$ both signs retain uniformly positive probabilities.
Their weighted average stays away from $-1$ and $1$, giving
$1-u(t,x)^2\ge\kappa>0$. If $m>0$ is the density lower bound there,
then

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

## 7. What full support says beyond the proof

<!-- passage:overlap-payoff -->
We can now return to the arrangement of nearly optimal spin choices.
A separate theorem
of [Auffinger–Chen–Zeng, Proposition 1, equation (5)][acz] applies at
each point in the minimiser's support. Combining it with full support:
for every fixed overlap $r\in[0,1)$ and tolerances $\varepsilon,\eta>0$,
with probability tending to one exponentially fast as $n\to\infty$,
there exist configurations $\sigma,\tau$ with

$$
|R(\sigma,\tau)-r|<\varepsilon,
\qquad H_n(\sigma)/n,\ H_n(\tau)/n\ge P_*-\eta.
$$

Thus near-optimal configurations occur at every prescribed overlap
scale. This is existence for each fixed target, not a statement about
typically sampled pairs or a procedure for finding them. The companion
*Long Reasoning Record*, §5.3, “Near-ground configurations at a prescribed
overlap”, gives the probability bound and the covariance adjustment.
<!-- /passage:overlap-payoff -->

<!-- passage:density-and-approximation -->
Full support alone does not give a density. Additional differentiation
of the saturated identities $q=t$ and $\mathbb E[a^2]=1$, followed by a
second use of its underlying integrated estimate on locally constant
comparison coefficients, proves that $\gamma$
is smooth, $\gamma(0)=0$, and
$\mu_\gamma=\gamma'(t)\,dt$ with $\gamma'(t)>0$ for $0<t<1$
([OpenAI (2026a), Corollary 6.4][support-density]). The *Long Reasoning
Record*, §§5.1–5.2, supplies this additional argument; Chen's earlier
theorem had already given smooth nonnegative density and full support.
<!-- /passage:density-and-approximation -->

<!-- passage:scalar-identities -->
Further martingale arguments show that $u(t,X_t)$ has an almost-sure
limit $U\in\{-1,1\}$ as $t\uparrow1$ and recover the optimal value as

$$
P_*=\int_0^1\mathbb E[a(t,X_t)]\,dt=\mathbb E[UB_1].
$$

The first moment $\mathbb E[a]$ differs from the second moment
$\mathbb E[a^2]=1$ used above. See [OpenAI (2026a), Corollary 7.1][support-consequences]
and the *Long Reasoning Record*, §6, “Recovering the value from a martingale”.
<!-- /passage:scalar-identities -->

<!-- passage:qaoa-boundary -->
A separate construction in [OpenAI (2026b)][qaoa-manuscript] uses that
value to prove the eventual-optimality conjecture of
[Basso–Farhi–Marwaha–Villalonga–Zhou, §7, equation (7.2)][bfmvz]:
for every $\varepsilon>0$, one finite-depth circuit of the Quantum
Approximate Optimization Algorithm (QAOA), with deterministic angles
independent of the size and couplings, has limiting expected reward per
spin at least $P_*-\varepsilon$ as $n\to\infty$.
The circuit is fixed before taking the size limit. The *Long Reasoning
Record*, §9, gives the additional synthesis and limiting arguments;
the no-gap proof alone does not supply them.
<!-- /passage:qaoa-boundary -->

<!-- passage:source-record -->
## Sources and scope of verification

The argument here reconstructs selected parts of the pinned OpenAI
analytic manuscript. The corresponding Lean [implementation][support-proof],
[challenge statement][support-interface] and [Comparator configuration][support-config]
concern a minimiser's support and moment identities. They assume a
minimiser; they do not prove the external Parisi formula or attainment.
The separate scalar [implementation][value-proof] and [statement][value-interface]
concern the value identity, not the whole QAOA circuit theorem.
The implementations use [Lean 4 (de Moura–Ullrich, 2021)](https://doi.org/10.1007/978-3-030-79876-5_37)
and [mathlib (The mathlib Community, 2020)](https://doi.org/10.1145/3372885.3373824).

The retained checks establish no Comparator acceptance of the research
targets; the corrected replay has no recovered terminal verdict. Source availability,
kernel checking and such acceptance are distinct observations. A kernel
check proves a declared statement under its definitions and axioms;
its correspondence with the analytic theorem needs a separate check. The *Long
Reasoning Record*, §11, records the checks and their outcomes. This
exposition claims neither an independent audit of the entire analytic
proof nor a human reader study.

Links below select the editions used.

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

[acz]: https://arxiv.org/abs/1703.06872v2
