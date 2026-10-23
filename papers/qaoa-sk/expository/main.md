---
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
---

# Why the SK order parameter has no gaps

## From a two-spin calculation to the scalar ingredients of QAOA

**Expository draft · 23 October 2026**

<!-- passage:opening -->
Assign a sign, either $+1$ or $-1$, to each of many sites. Every pair has
a random preference for whether its signs agree. The Sherrington–Kirkpatrick
(SK) optimisation problem asks for the largest total reward. Pair preferences
can conflict, so choosing the best sign for one pair need not help the others.

A theorem called the **Parisi formula** expresses the limiting reward per
site as the minimum of a quantity assigned to a nondecreasing function.
This function is the **order parameter**. Its increments describe which
scales are present in the variational description. The question studied
here is whether an exact minimiser can remain flat throughout an interval
of scales. The full-support result rules this out in the pure, zero-field
SK model, under the admissibility and minimiser hypotheses stated below.

The consequence is useful: optimality first gives identities only at scales
where the increments have support. Excluding every gap makes those
identities valid at every scale below one. They then yield a scalar
representation of the optimal energy. A separate manuscript uses scalar
ingredients in its argument about QAOA, the quantum approximate
optimisation algorithm; constructing its circuits requires further work.

This article reconstructs the argument in OpenAI's full-support manuscript
of 27 September 2026 and explains its scalar consequence. The exact conditional theorem is in Section 4. The decisive
calculus argument is in Section 5: contact fixes a change between two
endpoints, while strict curvature makes the same change too small.

The argument through Section 5 uses calculus and elementary probability;
Brownian motion enters when we calculate the effect of changing the order
parameter. We state the analytic regularity and strict-curvature results
at the points where the proof needs them. Section 6 derives the scalar
value identity, Section 7 explains its finite Gaussian approximation,
and Section 8 separates those facts from the further circuit construction.
The questions in Section 9 test the distinctions on changed examples.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. Two spins, and the normalisation we will keep

A spin configuration is a list $\sigma=(\sigma_1,\ldots,\sigma_n)$ with
each $\sigma_i\in\{-1,1\}$. Independent standard Gaussian numbers (mean zero and variance one)
$J_{ij}$ assign random preferences to pairs of spins. In the convention
used in this article and the two retained OpenAI manuscripts, the energy is

$$
H_n(\sigma)=\frac{1}{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j.
$$

Here **pure** means that the random interaction contains only pair products;
**zero field** means that no one-spin term $h\sum_i\sigma_i$ is present.

We maximise this energy. This fixes the sign convention: the positive
ground-state value below is a limiting maximum per spin.

For two spins there is only one coupling, say $J$. The calculation is
small enough to see every configuration:

| Configuration | Energy |
| --- | --- |
| $(+1,+1)$ | $J/\sqrt2$ |
| $(+1,-1)$ | $-J/\sqrt2$ |
| $(-1,+1)$ | $-J/\sqrt2$ |
| $(-1,-1)$ | $J/\sqrt2$ |

Thus $\max_\sigma H_2(\sigma)=|J|/\sqrt2$. Since
$\mathbb E|J|=\sqrt{2/\pi}$, the expected maximum **per spin** is
$1/(2\sqrt\pi)$. The calculation illustrates the normalisation and
the symmetry under reversing every spin. It does not approximate the
large-system optimum by itself.


With three spins, preferences can already conflict. As a deterministic
illustration, take all three couplings equal to $-1$. Satisfying each pair
separately would require all three products $\sigma_1\sigma_2$,
$\sigma_1\sigma_3$ and $\sigma_2\sigma_3$ to be $-1$. Their product
is always $1$, so this is impossible. If two spins agree and the third
differs, two terms contribute $+1$ and one contributes $-1$; if all
agree, their sum is $-3$. Hence the maximum energy is $1/\sqrt3$,
rather than the $\sqrt3$ suggested by satisfying every pair separately.
The three pair preferences conflict. The exact deterministic couplings
are an illustration, not an event of positive probability for continuous
Gaussian couplings, an SK average, or a large-system estimate.

To compare two configurations, define their overlap

$$
R(\sigma,\tau)=\frac1n\sum_{i=1}^n\sigma_i\tau_i.
$$

An overlap of $1$ means agreement everywhere; $-1$ means complete
reversal. If $a_i=\sigma_i\tau_i$, independence of the couplings gives

$$
\begin{aligned}
\mathbb E[H_n(\sigma)H_n(\tau)]
&=\frac1n\sum_{i<j}a_i a_j\\
&=\frac{(\sum_i a_i)^2-n}{2n}
=\frac n2 R(\sigma,\tau)^2-\frac12.
\end{aligned}
$$

This is why the scalar covariance function is $\xi(t)=t^2/2$.
The finite-size correction $-1/2$ is real: for two configurations with
zero overlap their energies can be negatively correlated. Adding the
same independent centred Gaussian of variance $1/2$ to every energy
removes this correction and leaves the expected maximum unchanged.
The sources account for that normalisation when using the Parisi formula.

The large-system question concerns

$$
P_* = \lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma).
$$

Here $\mathbb E$ averages over the random couplings $J_{ij}$.
Existence and evaluation of this limit follow from the ground-state
Parisi theorem discussed below.


### Why this is called a zero-temperature problem

For a finite list of rewards $h_1,\ldots,h_M$ and a parameter
$\lambda>0$, let $h_{\max}=\max_i h_i$. The inequalities

$$
e^{\lambda h_{\max}}\le\sum_{i=1}^M e^{\lambda h_i}
\le M e^{\lambda h_{\max}}
$$

give

$$
h_{\max}\le\lambda^{-1}\log\sum_i e^{\lambda h_i}
\le h_{\max}+\lambda^{-1}\log M.
$$

The logarithmic expression is a smooth way of approximating a maximum.
For the $2^n$ spin configurations, its error **per spin** is at most
$\log2/\lambda$. Statistical mechanics calls $\lambda$ the inverse
temperature; zero temperature means $\lambda\to\infty$, so that this
soft maximum becomes the maximum. This finite inequality explains the
name; see also [Auffinger and Chen (2017), §1][auffinger-chen].
The existence of the large-system limit and its Parisi representation
are further theorems. The scale $t$ used next is neither
temperature nor the number of spins.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

The Parisi formula represents the limiting optimum by minimising over
a function $\gamma$ of a scale $t\in[0,1)$. This is a new variational
description, not a relabelling of individual spin configurations.
The range $[0,1)$ is part of the zero-field representation used here.
Although the finite overlap $R$ can be negative, we must not infer this
whole representation just by taking its absolute value. Later the same
scale will serve as time for an auxiliary random process.
The admissible functions are nonnegative, nondecreasing, right-continuous,
and satisfy $\int_0^1\gamma(t)\,dt<\infty$. The value of a candidate
function will be defined in the next section; first consider its shape.

For example, the function

$$
\gamma(t)=
\begin{cases}
t,&0\le t\le 1/3,\\
1/3,&1/3<t\le 2/3,\\
t-1/3,&2/3<t<1
\end{cases}
$$

is admissible. It increases before and after its middle plateau, is
continuous at the two joins, and is bounded. No claim is being made
that it minimises the Parisi functional. The full-support theorem will
in fact rule that out.

Associate to any admissible $\gamma$ its Stieltjes measure, defined by

$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\le t<1.
$$

The measure records increments of $\gamma$: for $a<b$,
$\mu_\gamma((a,b])=\gamma(b)-\gamma(a)$. Thus a gap means **no
increase**, even if $\gamma$ is positive there. We study the support of
the increments, rather than the set where the function itself is nonzero.
For the displayed example it
has density one on $(0,1/3)$ and $(2/3,1)$ and density zero on
$(1/3,2/3)$. Its support is
$[0,1/3]\cup[2/3,1)$, with endpoints understood relative to $[0,1)$.
It has infinitely many support points and no final interval on which
$\gamma$ is constant, but it still has an interior gap.

A point belongs to the support when every relative neighbourhood of it
has positive measure. **Full relative support** means that every point
of $[0,1)$ has this property. In particular, every nonempty open interval
below one receives mass, so $\gamma(b)>\gamma(a)$ for every
$0\le a<b<1$. The word *relative* matters: the endpoint $1$ is outside
the underlying space.

For example, a neighbourhood of zero is relative to that space and
contains an interval $[0,\delta)$. It can have positive mass even if
the single point $0$ has none. A support point need not be an atom:
for the displayed continuous example every singleton has mass zero.

Conversely, the admissible constant function $\gamma(t)=c>0$
represents the measure $c\delta_0$, meaning mass $c$ concentrated at
zero. Its support is only $\{0\}$. Positivity of a cumulative function
and full support of its increments are different properties.

This measure need not be a probability measure. Its mass at zero is
$\gamma(0)$; its total mass can be infinite even though $\gamma$ is
integrable. For instance, $(1-t)^{-1/2}$ is an admissible candidate with
integral two and unbounded cumulative mass near one. The variational
problem therefore allows adding a small atom without removing mass
elsewhere. That freedom will determine the sign in the proof.

It is locally finite: every $[0,T]$ with $T<1$ has finite mass
$\gamma(T)$. Local finiteness will let us remove a small fraction of
the mass on such an interval even if the total mass is infinite.
Full support concerns where every neighbourhood receives mass; by itself
it does not assert a density, smoothness, or a quantitative cost for an
approximately optimal candidate with a plateau.
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

### 3.1 A function goes in; a number comes out

A **functional** assigns a number to an entire candidate function.
Here the candidate is $\gamma$. To define its number, we first define
a value function $\Phi_\gamma(t,x)$: the best expected reward from
starting at position $x$ at scale $t$.

Standard Brownian motion $B$ is a random continuous path starting at
zero. Its increments over disjoint time intervals are independent
Gaussians; $B_s-B_t$ has mean zero and variance $s-t$ for $s>t$.
This is the only noise law needed to read the formula. A control
$\alpha_s\in[-1,1]$ can respond to the increments already observed
after $t$ but cannot use future increments. For a fixed $\gamma$, set

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

The first term rewards the final absolute position. The second charges
for the control. The supremum varies the response $\alpha$, with the
whole candidate $\gamma$ held fixed. We then assign that candidate the number

$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
-\frac12\int_0^1t\gamma(t)\,dt.
$$

The outer variational problem minimises this number over admissible
$\gamma$. These two optimisations have different variables: the inner
one chooses a response for a fixed coefficient, and the outer one chooses
the coefficient. A **minimiser** is an admissible $\gamma$ whose value
is no larger than the value of every other admissible candidate.

For an immediate candidate evaluation, take $\gamma=0$. Both control
terms disappear, and a standard Gaussian $Z$ gives

$$
\Phi_0(t,x)=\mathbb E|x+\sqrt{1-t}\,Z|,
\qquad \mathcal P(0)=\mathbb E|Z|=\sqrt{2/\pi}.
$$

This evaluates one candidate; it has not solved the minimisation.
Once the Parisi formula below is supplied, it gives the upper bound
$P_*\le\sqrt{2/\pi}$. The full-support theorem will also tell us that
this particular candidate is not a minimiser, since its measure has empty support.

### 3.2 The theorem connecting the two optimisation problems

The ground-state Parisi formula and attainment identify

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

This is the substantial link between a maximum over spin configurations
and a minimum over functions. We use the result attributed to
[Auffinger and Chen (2017), Theorem 1 and proof of Lemma 3][auffinger-chen].
The infimum formula and the existence of a candidate attaining it are
separate parts of that input: an infimum is a greatest lower bound,
whereas a minimum must be achieved by a candidate. The support theorem
studied here assumes
an admissible minimiser and proves a property of it; neither selected
formal statement concludes minimiser existence.

### 3.3 Slope, curvature and an auxiliary path

For a fixed $\gamma$, write
$u(t,x)=\partial_x\Phi_\gamma(t,x)$ for its spatial slope and
$a(t,x)=\partial_{xx}\Phi_\gamma(t,x)$ for its spatial curvature.
The source proves that $\Phi_\gamma$ is convex in $x$ and has slopes
between $-1$ and $1$, so $a\ge0$ and $|u|\le1$ before the terminal time.
The optimal response can be taken as the current slope $u$.

The source's backward differential equation is

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

Here a partial derivative varies the indicated coordinate while keeping
the other fixed. The equation describes how the remaining value changes
with the starting scale. It is a cited analytic description of the control
value, rather than an extra definition the reader must solve to follow
the no-gap argument. For a general admissible coefficient it holds for
almost every time. The source also proves local absolute continuity in
time, so changes on a fixed strip are recovered by integrating the time
derivative. The needed spatial regularity and approximation hold on
each fixed strip $0\le t\le T<1$. Such a strip stops short of the
corner of the terminal function $|x|$; smoothness at time one is not assumed.

Using the slope as a response gives the diffusion

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

The Brownian term is accumulated noise and the integral is accumulated
drift. The existence and regularity of this process are source results;
the formal full-support conclusion also supplies an associated diffusion.
This is an auxiliary scalar process for the variational problem, not
the physical evolution of a spin configuration or a quantum circuit.

### 3.4 The stochastic identity used in the calculus proof

Set $M_t=u(t,X_t)$. A **conditional expectation** averages over future
randomness while retaining the information observed so far. The source
proves that $M_t$ is a bounded **martingale**: for $0\le t<s<1$,

$$
\mathbb E[M_s\mid\mathcal F_t]=M_t,
$$

where $\mathcal F_t$ denotes the observations available by time $t$.
This does not say that the realised path is constant. It says that its
present value is its conditional forecast of any later value.

The deterministic function needed below is its second moment,

$$
q(t):=\mathbb E[M_t^2],\qquad q'(t)=\mathbb E[a(t,X_t)^2].
$$

This $q(t)$ is not the overlap $R(\sigma,\tau)$ of two finite spin
configurations. The equality $q(t)=t$ will be a conclusion of optimality
and full support, not a definition of $q$ or of the scale.

The source proves the stochastic-integral representation
$M_t=\int_0^t a(s,X_s)\,dB_s$. Its moment calculation can be seen
first in a finite sum. Write $a_j=a(t_j,X_{t_j})$ and
$\Delta B_j=B_{t_{j+1}}-B_{t_j}$ on a uniform mesh of width
$\Delta t$. The coefficient $a_j$ uses only past observations.
Conditioning before each new increment makes cross terms vanish and gives

$$
\mathbb E\left[\left(\sum_j a_j\Delta B_j\right)^2\right]
=\sum_j\mathbb E[a_j^2]\Delta t.
$$

The stochastic integral is the mean-square limit of such sums: the
expectation of the squared difference tends to zero. Passing to that
limit gives
$q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds$; the source's regularity
then gives the derivative above. Zero external field gives symmetry,
$u(0,0)=0$, and hence $q(0)=0$. At zero a displayed time derivative
is understood from the right.

We start with the deterministic candidate $\gamma$ and its Stieltjes
measure $\mu_\gamma$. The value $\Phi_\gamma$ determines the slope
$u=\partial_x\Phi_\gamma$ and curvature $a=\partial_{xx}\Phi_\gamma$.
Along the diffusion $X_t$ driven by that slope, $M_t=u(t,X_t)$ is a
bounded martingale. Its second moment is the deterministic function
$q(t)=\mathbb E M_t^2$ used in the variation argument.

For the central proof, carry forward $q(0)=0$, $0\le q(t)\le1$ and
$q'=\mathbb E[a^2]$. The first-variation and strict-curvature theorems
will supply the other inputs. The full analytic foundation is in [OpenAI (2026a), §2][support-regularity],
which proves the regularity, diffusion and constant-interval transfer lemmas.
<!-- /passage:value-and-diffusion -->

<!-- passage:full-support-statement -->
## 4. The full-support result

**Source theorem ([OpenAI (2026a), Theorem 1.1][support-manuscript]).**
In the pure, zero-field model with
$\xi(t)=t^2/2$, let $\gamma$ be an admissible integrable minimizer of
the functional just defined, on a probability space carrying standard
Brownian motion. Then a Stieltjes measure and an associated diffusion
exist. Every measure satisfying $\mu([0,t])=\gamma(t)$ has full
relative support on $[0,1)$, and $\gamma$ is strictly increasing.
For every associated diffusion and every $0\le t<1$,

$$
\mathbb E[u(t,X_t)^2]=t,
\qquad
\mathbb E[a(t,X_t)^2]=1.
$$

The [fixed-revision Lean implementation][support-proof] and
[separately stated formal challenge][support-interface] give direct
formal points of comparison for this claim; their
[Comparator configuration][support-config] specifies the intended check.
Section 5 explains the no-gap mechanism using the manuscript's
regularity and curvature estimates. The statement concerns an admissible
minimiser in the pure, zero-field model. It does not assert a density
for the Stieltjes measure or cover nonzero field or mixed-spin covariances.
<!-- /passage:full-support-statement -->

<!-- passage:zero-candidate-example -->
### 4.1 An exact candidate which does not minimise

The minimiser hypothesis matters. Take $\gamma_0(t)=0$. It is
admissible, but its Stieltjes measure is zero, and its diffusion is
$X_t=B_t$. The calculation below shows that its moment misses the
contact identity and that a small added atom lowers the objective.
It tests the hypothesis without locating a minimiser.

Let $F_{\mathrm G}$ be the standard Gaussian distribution function and
$Z$ a standard Gaussian. The zero-coefficient heat formula gives

$$
\Phi_0(t,x)=\mathbb E|x+\sqrt{1-t}Z|,
\qquad
u_0(t,x)=2F_{\mathrm G}\!\left(\frac{x}{\sqrt{1-t}}\right)-1.
$$

Differentiating once more, for $0\le t<1$,

$$
a_0(t,x)=\sqrt{\frac2\pi}\frac1{\sqrt{1-t}}
          \exp\!\left(-\frac{x^2}{2(1-t)}\right).
$$

Since $B_t$ has variance $t$, a Gaussian integral gives
$\mathbb E e^{-B_t^2/(1-t)}=\sqrt{(1-t)/(1+t)}$. Thus the
moment identity from the preceding section becomes

$$
q_0'(t)=\mathbb E[a_0(t,B_t)^2]
       =\frac2{\pi\sqrt{1-t^2}},
\qquad
q_0(t)=\frac2\pi\arcsin t,
$$

where the last equality uses $q_0(0)=0$. In particular,
$q_0(1/2)=1/3$, rather than $1/2$. Admissibility alone has not
produced the identity that the minimiser will satisfy.

We can also improve the objective directly. Add an atom of mass $c\ge0$
at zero. Its cumulative function is the admissible constant
$\gamma_c(t)=c$, since $\mu_{\gamma_c}=c\delta_0$; no mass needs to
be removed elsewhere. For $c>0$, the constant-coefficient heat formula in
[OpenAI (2026a), §2][support-heat] gives

$$
\begin{aligned}
\mathcal P(\gamma_c)
&=\frac1c\log\mathbb E e^{c|Z|}-\frac c4\\
&=\frac c4+\frac1c\log\bigl(2F_{\mathrm G}(c)\bigr).
\end{aligned}
$$

The second line follows by completing the square:
$\mathbb E e^{c|Z|}=2e^{c^2/2}F_{\mathrm G}(c)$. Put
$A=\sqrt{2/\pi}$. Because
$2F_{\mathrm G}(c)=1+Ac+O(c^3)$ and
$\log(1+y)=y-y^2/2+O(y^3)$, the apparent division by zero has the
continuous extension

$$
\mathcal P(\gamma_c)
=\sqrt{\frac2\pi}
 +\left(\frac14-\frac1\pi\right)c+O(c^2).
$$

Its right derivative at zero is negative. Therefore sufficiently small
positive atoms lower the value, proving directly that $\gamma_0$ does
not minimise. For scale, $\mathcal P(\gamma_0)\approx0.797884561$
and $\mathcal P(\gamma_{0.1})\approx0.791421704$; these decimals
illustrate the exact calculation, and are not estimates of the optimum.

This example computes a feasible descent direction. It does not find a
minimiser or establish full support. Section 5 will recover the same
negative derivative from the general first-variation formula.
<!-- /passage:zero-candidate-example -->



<!-- passage:contact-and-gap -->
## 5. Why a flat interval cannot minimise

### 5.1 Allowed changes and their first-order cost

The proof needs a way to detect whether placing more Stieltjes mass at
a scale would improve the objective. A first variation is the slope of
$\varepsilon\mapsto\mathcal P(\gamma+\varepsilon\eta)$ at zero.
At a minimum its **right** derivative is nonnegative whenever small
positive values of $\varepsilon$ remain admissible. It need not vanish:
constraints may forbid the opposite change.

The source proves the following first-variation formula. If $\eta$ is
an integrable direction for which
$\gamma+\varepsilon\eta$ stays admissible for sufficiently small
$\varepsilon\ge0$, the right derivative is

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

Adding an atom at a scale $s$ increases $\gamma(t)$ by the same amount
for every $t\ge s$, because $\gamma$ is cumulative. This is the direction
$\eta(t)=\mathbf1_{[s,1)}(t)$. It motivates the contact potential

$$
G(s)=\int_s^1(q(t)-t)\,dt.
$$


Thus $G(s)/2$ is the first-order cost of adding a unit atom at $s$.
The tail integral appears because this one mass change affects all later
scales. The residual $q(s)-s$ at a single scale would not measure that cost.

At a minimiser the derivative in this direction cannot be negative,
so $G(s)\ge0$ everywhere. Removing a fraction of the existing measure
on a compact interval $K=[0,T]$, with $T<1$, is also admissible.
The direction is $\eta_K(t)=-\mu_\gamma(K\cap[0,t])$: every atom
or infinitesimal mass removed at $s$ lowers the cumulative function at
all later times. Scaling the mass on $K$ by $1-\varepsilon$ preserves
nonnegativity and therefore preserves an admissible cumulative function.
The mass $\mu_\gamma(K)=\gamma(T)$ is finite, and $|q(t)-t|\le1$.
Consequently the double integral is absolutely integrable; changing its
order by Fubini's theorem gives

$$
0\le -\frac12\int_KG(s)\,\mu_\gamma(ds).
$$

Since $G\ge0$, the integral must vanish. If $G$ were positive at a
support point, continuity would make it positive on a neighbourhood
having positive measure, contradicting that integral for a sufficiently
large $T<1$. Thus $G=0$ on the support. Removing a portion of all
the measure in $K$ is essential: a measure need not consist of atoms.

### 5.2 Contact gives endpoint conditions

An interior support point is therefore a minimum of $G$. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$, calculus gives

$$
q(s)=s,\qquad q'(s)\le1.
$$

If zero belongs to the support, $G(0)=0$ and $q(0)=0$ give
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$ as $h\downarrow0$.
Nonnegativity therefore implies $q'(0)\le1$, with a right derivative.
This includes the case where the measure has an atom at zero.

### 5.3 Strict curvature creates an impossible integral

Now suppose a gap $(r,s)$ lies between two support points, with
$0\le r<s<1$. The cumulative function is constant on that gap, say
$\gamma=c$. Contact at the endpoints forces

$$
q(r)=r,\quad q(s)=s,\quad q'(r)\le1,\quad q'(s)\le1.
$$

For $c>0$, the analytic core of the source proof establishes
$q'''(t)>0$ throughout the gap. Since $q'''=(q')''$, this says that $q'$ is strictly convex. A strictly
convex function lies below the line segment, or chord, joining two points
on its graph. Here that gives

$$
q'(t)<\frac{s-t}{s-r}q'(r)+\frac{t-r}{s-r}q'(s)\le1
\quad(r<t<s).
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

Integrating gives
$q(s)-q(r)<s-r$, whereas the endpoint equations require
$q(s)-q(r)=s-r$. This contradiction excludes the gap. Applied to the
candidate of Section 2, the argument says that a minimising plateau
on $(1/3,2/3)$ would have to produce both a change exactly $1/3$ and a
change strictly less than $1/3$.

The difficult ingredient is the strict sign of $q'''$, not the final
integration. Direct differentiation produces both positive and negative
terms; convexity of $\Phi_\gamma$ alone does not settle their sum.
The source proof combines inequalities for spatial derivatives and a
transformed diffusion density, then integrates by parts using an exact
rational identity. On a constant interval with $c>0$ it obtains

$$
q'''(t)\ge\frac{c^2}{1000}
\mathbb E[a(t,X_t)^4]>0.
$$

This is an inequality after expectation, not a claim that every term
before integration is positive. Approximation transfers that integrated
bound to an integrable order parameter. The complete analytic argument
combines the shape inequalities of [OpenAI (2026a), §4][support-signs]
with its [rational identity, Lemma 4.1][support-certificate], then
applies [Proposition 5.1][support-curvature].
<!-- /passage:contact-and-gap -->

<!-- passage:gap-area-example -->
### 5.4 Computing the missing area

The shaded deficit above can be measured in a polynomial model. It
illustrates the calculus step only; the model slope is
not asserted to come from an SK diffusion.

Use the same interval $[1/3,2/3]$ as the plateau in Section 2. Set
$x=3t-1$, so $0\le x\le1$, and for $0\le\lambda\le1$ define

$$
h_\lambda(t)=1-\lambda x(1-x).
$$

Think of $h_\lambda$ as a proposed derivative $q_\lambda'$.
It has endpoint values one, stays between $3/4$ and one, and has
$h_\lambda''(t)=18\lambda$. For $\lambda>0$ it is strictly convex.
Since $dt=dx/3$,

$$
\int_{1/3}^{2/3}h_\lambda(t)\,dt
=\frac13\int_0^1[1-\lambda x(1-x)]\,dx
=\frac13-\frac\lambda{18}.
$$

If the left contact condition is $q_\lambda(1/3)=1/3$, integration
therefore forces

$$
q_\lambda(2/3)=\frac23-\frac\lambda{18}.
$$

For $\lambda=1$, the required right endpoint value $2/3=12/18$
is missed by $1/18$: the model reaches only $11/18$. This is the
incompatibility in the no-gap proof. When $\lambda=0$, the slope is
constantly one, the deficit vanishes, and both endpoint contacts can
hold. Ordinary convexity alone would allow that equality case.

The source proof allows endpoint derivatives less than one as well;
choosing both equal to one gives this model the largest permitted
endpoint values. The parameter $\lambda$ is a teaching parameter,
with no claimed relation to the plateau height $c$. The model does
not prove the strict-curvature estimate, or address initial and
terminal gaps. Those require the separate source arguments below.
<!-- /passage:gap-area-example -->

<!-- passage:endpoints -->
### The intervals the interior argument does not cover

Three remaining cases explain why the endpoint conditions were stated
carefully. If a gap has coefficient zero, the heat equation gives strict
increase of $q'$ instead of the positive-coefficient convexity argument.
Then $q'(t)<q'(s)\le1$ and integration gives the same contradiction.
An initial gap $[0,s)$ also has coefficient zero. Here the left
endpoint identity comes from $q(0)=0$, even though zero is not a
support point.

A terminal plateau is different: one cannot use a support point at
$1$, because $1$ is outside the domain. The source instead proves that
on a putative terminal constant interval,

$$
1-q(t)\ge C\sqrt{1-t}
$$

for some $C>0$ and all sufficiently late $t$. Hence
$q(t)-t\le(1-t)-C\sqrt{1-t}<0$ near one, making $G(s)<0$ there.
This contradicts the nonnegativity supplied by optimality. The estimate
also excludes the empty-support case $\gamma=0$.

These cases exhaust the components of the complement of a relatively
closed support. Once all gaps are excluded, every interior time is a
contact point, so $q(t)=t$ everywhere below one, including zero by
symmetry. Differentiating yields $\mathbb E[a(t,X_t)^2]=1$.
The mass-removal and endpoint arguments are given in
[OpenAI (2026a), §6][support-variation].
<!-- /passage:endpoints -->

<!-- passage:scalar-identities -->
## 6. Recovering the optimal value from one terminal spin

Full support has turned a condition at support points into an identity
at every time. This supplies a useful normalization for the martingale
$u(t,X_t)$. It converges almost surely and in mean square to a random
variable $U$ with $|U|\le1$. Since its second moment tends to one,
$\mathbb E[U^2]=1$. A nonnegative random variable with expectation
zero vanishes almost surely; apply this to $1-U^2$ to obtain

$$
U\in\{-1,1\}\quad\text{almost surely}.
$$

Thus the continuous scalar process ends in a spin. Combining the
Parisi value equality with the source's martingale identities gives

$$
\begin{aligned}
P_*&=\mathcal P(\gamma)\\
&=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt\\
&=\mathbb E[UB_1]
=\int_0^1\mathbb E[a(t,X_t)]\,dt.
\end{aligned}
$$

The last integral involves the **first** moment of $a$. The support
identity involves its **second** moment. Replacing the former integrand
by one would be an error.

The coefficient of the penalty has changed from $1/2$ in
$\mathcal P$ to $1$ in the formula for $P_*$. The source's evolution
identity explains why:

$$
\mathbb E\Phi_\gamma(t,X_t)
=\Phi_\gamma(0,0)+\frac12\int_0^t\gamma(s)q(s)\,ds.
$$

Let $t\uparrow1$ and substitute $q(s)=s$. The left side tends to
$\mathbb E|X_1|$, so $\Phi_\gamma(0,0)$ is that expectation minus
half the integral. Subtracting the other half in $\mathcal P$ gives
the whole integral in the value formula.

Here is the cancellation behind the middle equality. Uniform convergence
of $\Phi_\gamma(t,\cdot)$ to $|\cdot|$, convexity, and $X_t\to X_1$
imply $UX_1=|X_1|$ almost surely, including when $X_1=0$.
For a nonzero limit $X_1$, convexity bounds the derivative between
nearby difference quotients, whose limits both give the sign of $X_1$.
If $X_1=0$, both sides of the claimed product identity vanish.
Multiply the diffusion equation at time one by $U$ and take expectations.
Martingality gives
$\mathbb E[Uu(t,X_t)]=\mathbb E[u(t,X_t)^2]=t$, so

$$
\mathbb E|X_1|=\mathbb E[UB_1]+\int_0^1t\gamma(t)\,dt.
$$

The deterministic penalty cancels. Pairing
$U=\int_0^1a(t,X_t)\,dB_t$ with $B_1$ yields the last integral.
The finite-sum reason is
$\mathbb E[(\sum_j a_j\Delta B_j)(\sum_j\Delta B_j)]
=\sum_j\mathbb E[a_j]\Delta t$: different increments again have
zero cross terms, while a matching pair contributes its variance.
Mean-square convergence gives the integral identity.
It is finite because
$\mathbb E|a(t,X_t)|\le(\mathbb E[a(t,X_t)^2])^{1/2}=1$.

The [fixed-revision Lean scalar statement][value-proof] and
[separate formal challenge][value-interface] record these identities
for every admissible minimiser and associated diffusion. Their
[Comparator configuration][value-config] specifies the intended
comparison. The finite Gaussian construction next approximates this
scalar value; it does not yet produce circuit angles.
<!-- /passage:scalar-identities -->

<!-- passage:finite-gaussian -->
## 7. From the diffusion to finitely many Gaussian inputs

The scalar process uses an entire Brownian path. To approximate its value
using finitely many inputs, we sample the diffusion up to a fixed
$T<1$, normalise the directions produced by its increments, and use
one independent Gaussian to round the terminal response to a sign
without changing earlier correlations. The value will emerge from
an adjacent-index sum, not from the output sign alone.

With $N$ time
steps, $\Delta=T/N$ and $t_j=j\Delta$, define

$$
Y_0=0,\qquad
Y_j=Y_{j-1}+\sqrt\Delta Z_j
+\Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),
\quad 1\le j\le N,
$$

where the $Z_j$ are independent standard Gaussians. Here $N$ counts
time steps; it is not the number $n$ of spins. This Euler scheme
replaces each Brownian increment by $\sqrt\Delta Z_j$.

The exact diffusion satisfies $\mathbb E[a(t,X_t)^2]=1$, but the
discrete scheme need not satisfy this exactly. Normalize its directions:

$$
c_j=\bigl(\mathbb E[a(t_{j-1},Y_{j-1})^2]\bigr)^{-1/2},
\qquad g_j=c_j a(t_{j-1},Y_{j-1})Z_j.
$$

The finite-Gaussian conclusion guarantees positivity of the normalizers
for all sufficiently large $N$, for every step $1\le j\le N$.
$Y_{j-1}$ depends only on preceding Gaussian inputs, so its curvature
coefficient is independent of $Z_j$. Each $g_j$ consequently has mean
zero and second moment one. The same conditional-mean argument makes
different $g_j$ orthogonal in mean square.
One extra independent Gaussian rounds the terminal response to a spin:

$$
F_N=\operatorname{sgn}\bigl(u(T,Y_N)+2F_{\mathrm G}(Z_{N+1})-1\bigr),
$$

where $F_{\mathrm G}$ is the standard Gaussian distribution function.
The random variable $2F_{\mathrm G}(Z_{N+1})-1$ is uniform on $[-1,1]$.
For any fixed $m\in[-1,1]$, the sign of $m$ plus this uniform variable
is positive with probability $(1+m)/2$ and negative with probability
$(1-m)/2$. Its mean is therefore $m$. Conditional on all of
$Z_1,\ldots,Z_N$, the mean of $F_N$ is exactly $u(T,Y_N)$.
The rounding therefore preserves every correlation with a function
of those first $N$ inputs. The extra rounding input $Z_{N+1}$ is
excluded from this conditioning.

Set $A_j=\mathbb E[F_Ng_j]$ for $1\le j\le N$, $A_0=0$, and
$D_i=\mathbb E[F_NZ_i]$ for $1\le i\le N+1$. We write $D_i$ for
the source's coefficient $B_i$ to distinguish it from Brownian motion.
The source theorem
states

$$
\lim_{N\to\infty}\sum_{j=0}^N A_jD_{j+1}
=\int_0^T\mathbb E[a(t,X_t)]\,dt.
$$

For $N=2$, the sum before taking a limit is
$A_0D_1+A_1D_2+A_2D_3=A_1D_2+A_2D_3$.
Here $A_0=0$ and $D_3$ uses the extra rounding Gaussian.
The final term is the boundary contribution shown below to vanish as
$N\to\infty$. This finite case checks the index shift; it makes no
asymptotic claim at $N=2$.

The shift by one has a reason. The proof shows that the coefficient
vectors are approximated by

$$
A_j\approx\frac{\sqrt\Delta}{c_j},\qquad
D_i\approx\sqrt\Delta\,\mathbb E[a(t_{i-1},Y_{i-1})]
\quad(1\le j,i\le N).
$$

Here approximation means that the Euclidean norm of each whole error
vector tends to zero. The approximating vectors have bounded norms,
so Cauchy–Schwarz controls the accumulated error in their scalar
product; small errors at each fixed index alone would not do this.
Pairing $A_j$ with $D_{j+1}$ for $1\le j<N$ selects the mesh point
$t_j$, and $c_j\to1$ uniformly. The final term vanishes because
$A_N\to0$ and $|D_{N+1}|\le1$. What remains is the Riemann sum
$\Delta\sum_{j=1}^{N-1}\mathbb E[a(t_j,Y_j)]/c_j$, which converges
to the displayed integral by the source's Euler and regularity estimates.

Only after refining this fixed-$T$ approximation does the right-hand
side tend to $P_*$ as $T\uparrow1$. The adjacent indices in
$A_jD_{j+1}$ are part of the statement. A different coefficient
pairing cannot be substituted without proof. These are scalar Gaussian
correlations, not the output of a finite-instance spin optimizer or a
QAOA circuit. Their full construction and proof are in the
[OpenAI (2026a), §7][support-consequences].
<!-- /passage:finite-gaussian -->

<!-- passage:qaoa-boundary -->
## 8. What the QAOA statement adds

QAOA uses a different object: a quantum state on $n$ spins, represented
here by a normalised complex vector whose coordinates are indexed by
the $2^n$ spin configurations. Its cost
operator $C_{n,J}$ is diagonal with entries $H_n(\sigma)$. Its mixer
$B_n=\sum_i X_i$ flips individual spins, where $X_i$ is the Pauli
$X$ matrix on spin $i$: it sends the basis vector $|\sigma\rangle$
to the vector with spin $i$ reversed. The equal superposition
$|+\rangle^{\otimes n}$ has every coordinate equal to $2^{-n/2}$.
For a state with coordinates $\psi_\sigma$, the notation
$\langle\psi|C_{n,J}|\psi\rangle$ means

$$
\sum_\sigma |\psi_\sigma|^2 H_n(\sigma),
\qquad \sum_\sigma |\psi_\sigma|^2=1.
$$

It is the classical energy averaged with the measurement probabilities
$|\psi_\sigma|^2$. The matrix exponentials below are norm-preserving
operations, so they produce another normalised state. A cost rotation
multiplies the amplitude of configuration $\sigma$ by the phase
$e^{-i\theta H_n(\sigma)}$. A mixer rotation is generated by
single-spin flips and redistributes amplitudes among configurations.
The angles choose how these operations alternate; the resulting
squared amplitudes determine the measurement probabilities above.
Starting from the equal superposition, a depth-$p$ circuit alternates
cost and mixer rotations:

$$
|\psi_{n,p,J}(\boldsymbol\theta,\boldsymbol\beta)\rangle
=e^{-i\beta_pB_n}e^{-i\theta_pC_{n,J}}\cdots
e^{-i\beta_1B_n}e^{-i\theta_1C_{n,J}}|+\rangle^{\otimes n}.
$$

The cost angles are written $\boldsymbol\theta$ here to distinguish
them from the function $\gamma(t)$ in the Parisi problem; the QAOA
manuscript writes these angles as $\boldsymbol\gamma$.

For each fixed depth and deterministic choice of real angles, first take
the large-system limit of the expected energy per spin, where the
expectation is over the Gaussian couplings $J$:

$$
v_p(\boldsymbol\theta,\boldsymbol\beta)
=\lim_{n\to\infty}\frac1n\mathbb E
\langle\psi_{n,p,J}|C_{n,J}|\psi_{n,p,J}\rangle,
\qquad Q_p=\sup_{\boldsymbol\theta,\boldsymbol\beta}v_p.
$$

The separate theorem of [OpenAI (2026b), Theorem 1.1][qaoa-theorem] claims
$\lim_{p\to\infty}Q_p=P_*$. Its quantifiers are worth spelling out:
for each desired error $\varepsilon>0$, choose a finite depth and one
deterministic angle vector, independent of both $n$ and the couplings
$J$, whose limiting expected energy is at least $P_*-\varepsilon$.
The chosen depth and angles may depend on $\varepsilon$.

Two elementary observations explain what remains to be constructed.
Measurement of any state gives a probability distribution on classical
configurations, so its energy expectation is at most
$\max_\sigma H_n(\sigma)$. Thus $Q_p\le P_*$. Appending a layer with
zero angles changes no state, so $Q_{p+1}\ge Q_p$. These upper-bound
and monotonicity facts do not supply the required lower bound near
$P_*$.

The scalar results identify a target value and finite Gaussian data
approaching it. The QAOA manuscript supplies additional arguments to
turn such data into quantum operations and a finite word in cost and
mixer gates. That transfer is a separate mathematical task: an
approximation by scalar random variables does not already exhibit
circuit angles. Neither of the two formal scalar and support statements
mentions the state $|\psi_{n,p,J}\rangle$ or asserts convergence of its energy.

The claim is consequently about the order $n\to\infty$ at fixed
parameters, followed by increasing $p$. It does not interchange those
limits or give a joint schedule $p=p(n)$. The manuscript states no
quantitative finite-size estimate, depth bound, or efficient method of
choosing the angles. Its complete circuit-construction argument is
outside the proof reconstructed in this article.
<!-- /passage:qaoa-boundary -->

<!-- passage:limit-order-example -->
### 8.1 A depth that works at each size need not survive the size limit

To see the distinction without quantum notation, consider the artificial
score

$$
b_{n,p}=\frac{p}{n+p},\qquad n,p\in\{1,2,\ldots\}.
$$

It lies strictly between zero and one. Increasing the depth improves it,
since

$$
b_{n,p+1}-b_{n,p}
=\frac{n}{(n+p)(n+p+1)}>0.
$$

At every fixed size $n$, increasing $p$ makes the score tend to one.
But at every fixed depth $p$, increasing $n$ makes it tend to zero.
Consequently the iterated limits disagree:

$$
\lim_{n\to\infty}\lim_{p\to\infty}b_{n,p}=1,
\qquad
\lim_{p\to\infty}\lim_{n\to\infty}b_{n,p}=0.
$$

For a requested error $0<\varepsilon<1$, solve the finite inequality:

$$
b_{n,p}\ge1-\varepsilon
\quad\Longleftrightarrow\quad
p\ge\frac{1-\varepsilon}{\varepsilon}n.
$$

Thus the smallest integer depth is the ceiling of the right side.
For $\varepsilon=1/10$, it is $9n$:

| Size $n$ | Smallest depth for score at least $9/10$ | Score at the fixed depth $p=9$ |
| --- | --- | --- |
| $1$ | $9$ | $9/10$ |
| $10$ | $90$ | $9/19$ |
| $100$ | $900$ | $9/109$ |

Each size admits a successful depth, but no finite depth succeeds after
the size limit. Boundedness, improvement with depth and fixed-size
convergence therefore do not supply the thermodynamic-first conclusion.

This is a toy array, not an SK energy or a prediction for QAOA. It
explains why the QAOA manuscript must construct one finite circuit word
for each accuracy before taking $n\to\infty$. It also does not show
that joint schedules are impossible: here $p=n$ gives $1/2$, while
$p=n^2$ gives $n/(n+1)\to1$. The manuscript's lack of a quantitative
specified schedule must be distinguished from nonexistence of every
possible schedule.
<!-- /passage:limit-order-example -->

<!-- passage:changed-cases -->
## 9. Checks that change one condition

### Questions

1. In the zero-candidate calculation, place the added atom at a fixed
   $s\in[0,1)$ instead of zero. What happens to the cumulative function,
   and does the first variation still lower the objective?
2. In the area model, replace $\lambda=1$ by $\lambda=1/2$, and then
   by $\lambda=0$. What is the deficit in each case? Which change
   removes the contradiction?
3. In the toy array, choose $p=n$. Does the resulting limit equal either
   iterated limit? What changes if $p=n^2$?
4. Does infinite support, together with absence of a final plateau,
   suffice for full support? Does a positive initial cumulative value?
5. Does ending in a terminal spin $U\in\{-1,1\}$ establish that the
   coefficient minimises the Parisi functional?
6. May the finite-Gaussian construction set $T=1$ before refining its
   time mesh? Would near-optimal circuit angles chosen separately for
   each disorder instance establish the stated QAOA claim?

### Answers and boundaries

**1. Moving the atom.** Its direction is
$\eta_s(t)=\mathbf1_{[s,1)}(t)$. For the zero candidate,
$q_0(t)=2\arcsin(t)/\pi<t$ for $0<t<1$: the strictly convex
arcsine function lies below its chord between zero and one. Hence
$G_0(s)=\int_s^1(q_0(t)-t)\,dt<0$ for every fixed $s<1$, and
$D^+\mathcal P(\gamma_0)[\eta_s]=G_0(s)/2<0$. A sufficiently
small positive atom gives descent. The allowable step size may depend
on $s$; no uniform improvement near the excluded endpoint is claimed.

**2. Weakening strictness.** The deficits are $1/36$ and zero.
At $\lambda=0$, $q_\lambda'=1$ and both endpoint contacts are
compatible. The inference from strict convexity fails when only
ordinary convexity is available. This equality case is a calculus
model, without a claim that it comes from a constant-coefficient
SK diffusion.

**3. Choosing a joint schedule.** With $p=n$, the score is exactly
$1/2$ for every $n$, different from both iterated limits. With
$p=n^2$, it equals $n/(n+1)$ and tends to one. Joint limits require
control of the chosen schedule.

**4. Distinguishing support properties.** The piecewise-linear
candidate in Section 2 has infinitely many support points and no
final plateau, yet $(1/3,2/3)$ receives no mass. The positive constant
candidate $\gamma=c>0$ represents $c\delta_0$ and has support only
$\{0\}$. Positivity of the cumulative function describes a different
property from support of its increments.

**5. A terminal spin does not suffice.** For $\gamma_0=0$,
$u_0(t,B_t)\to\operatorname{sgn}(B_1)$ almost surely: $B_t\to B_1$
and $B_1\ne0$ almost surely, so the argument of $F_{\mathrm G}$ tends
to positive or negative infinity. Nevertheless, this coefficient has
the negative first variation computed above. The terminal-spin
conclusion alone does not imply $q(t)=t$ or optimality.

**6. Keeping the stated choices.** The finite-Gaussian theorem fixes
$0<T<1$; its estimates give no substitution of $T=1$ before mesh
refinement. The separate limit $T\uparrow1$ recovers $P_*$. The QAOA
claim asks for one deterministic angle vector, independent of both
the couplings and system size, for each requested accuracy. Choosing
angles after seeing each instance changes those quantifiers.

<!-- /passage:changed-cases -->

<!-- passage:source-record -->
## Sources and verification

OpenAI's [full-support paper (2026a)][support-manuscript] is the source
of the no-gap theorem, the strict curvature estimate and the scalar
consequences explained here. It credits earlier Parisi theory and notes
that [Chen (2026)][chen-support] proved the same full-relative-support
conclusion. OpenAI's [QAOA paper (2026b)][qaoa-manuscript] states the
separate circuit theorem and its thermodynamic-first order of limits.
The exact manuscript editions and source locations are recorded in the
companion correspondence.

The [formal support statement][support-interface] and the
[formal scalar-value statement][value-interface] have separate
implementations. Both state the diffusion identities for every
associated diffusion under the admissible-minimiser hypothesis. The
scalar statement's final equality between the ground-state and Parisi
values needs only that minimiser premise; it explicitly includes
convergence of the finite-SK ground-state sequence. The developments
represent Brownian motion, the order parameter and the diffusion
differently, so this article does not claim they have been formally
composed.

The retained evidence includes verified source bytes and a historical
full-support Comparator startup that stopped before the checker ran
because its executable was unavailable. It does not establish a
completed research-target Lean or Comparator replay, independent review
of the full analytic proofs, or human reader review. The linked
configurations state what was selected for comparison, not its result.
<!-- /passage:source-record -->

[support-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean
[support-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35
[support-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.json
[value-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean
[value-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16
[value-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.json
[support-manuscript]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
[support-regularity]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex
[support-signs]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/signs.tex
[support-certificate]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex
[support-curvature]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/curvature.tex
[support-variation]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/variation.tex
[support-consequences]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/consequences.tex
[qaoa-manuscript]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf
[qaoa-theorem]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/01-introduction.tex
[auffinger-chen]: https://arxiv.org/abs/1606.05335v2
[chen-support]: https://arxiv.org/abs/2607.18032v1

[source-collection]: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
[writing-guide]: https://github.com/wcook04/plectis-erdos/blob/a0878310af794d7a0f76cc11f4de3a20c795dc60/paper/exposition/writing-a-good-mathematical-paper.tex

[support-heat]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/regularity.tex#L46-L56
[support-area-figure]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/gap-convexity.tex
