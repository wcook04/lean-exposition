---
header-includes:
  - |
    \usepackage{tikz}
    \usepackage{float}
---

# Why the SK order parameter has no gaps

## From finite spin rewards to a variational proof and its algorithmic consequences

**Expository draft · 24 October 2026**

<!-- passage:opening -->
Start with a list of $n$ signs, each either $+1$ or $-1$. The sign at
position $i$ is called a **spin**, and the indexed position is called a
**site**. Attach a real number to each pair of positions. This number,
called a **coupling**, contributes to a score when the signs agree and
its negative contributes when they disagree. A coupling of $3$ favours
agreement; one of $-3$ favours disagreement. With the couplings fixed,
choose the signs to maximise the sum. The choices interact: three signs
cannot all disagree with one another.

In the **Sherrington–Kirkpatrick (SK) model**, these couplings are independent
standard Gaussians. The score divided by $\sqrt n$ is the **energy**;
Section 1 gives its formula. We first ask for the limiting maximum energy
per spin, averaged over the couplings, as $n$ grows.

The **Parisi formula** expresses this limit through a different optimisation.
It assigns a number to each function in a class of nondecreasing functions
and minimises that number. The candidate functions are called **order
parameters**; Sections 2 and 3 define their class and values. Every
candidate gives an upper bound on the limiting spin optimum, and the
smallest bound equals it. Thus the maximum over signs becomes a minimum
over functions without changing the energy's sign convention.

We study the function attaining that minimum: **it cannot be constant on
any interval of positive length in $[0,1)$.** Section 4 states the exact
hypotheses for the pure, zero-field model defined in Section 1. An allowed
change to a minimising function cannot lower its value. This gives two
endpoint conditions on any proposed flat interval. A separate curvature
estimate makes them incompatible. Section 2.1 shows the calculus
contradiction before we construct the random process that supplies it.

Excluding flat intervals also expresses the optimum using one real random
process. This starts a second question: **can a quantum algorithm approach
the same optimum?** The quantum approximate optimisation algorithm,
**QAOA**, alternates an operation determined by the couplings with a
fixed mixing operation. The number of repetitions and their settings may
depend on the requested accuracy, but must be chosen
independently of $n$ and of the drawn couplings. Section 8 defines the
operations and the averaged measurement outcome in this question.

This article reconstructs OpenAI's no-gap argument of 27 September 2026
and its scalar consequence, then explains the separate circuit construction.
A reader interested in the support theorem can finish at Section 6. The
continuation in Sections 7–8 first retains the scalar value in finitely
many correlation products, then realises those products by quantum
operations and removes the temporary random controls used to construct them.
These steps explain why the variational argument precedes the circuit.

The first route assumes calculus, Gaussian expectations and conditional
expectation. The circuit continuation also uses complex inner products and
tensor products; its quantum notation is introduced in Section 8.
Existence, regularity, the first-variation formula and the strict-curvature
estimate are identified source results, as are the later operator and
gate-construction theorems. The exposition explains how they combine;
it does not replace their analytic proofs. Source credit and hypotheses
accompany each result. Section 9 gives changed-case questions with answers;
Section 10 retains supporting calculations.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. Two spins, and the normalisation we will keep

A **configuration** is the complete list $\sigma=(\sigma_1,\ldots,\sigma_n)$,
where $\sigma_i\in\{-1,1\}$ is the spin at position $i$. For each
pair $i<j$, draw a coupling $J_{ij}$ independently from a Gaussian of
mean zero and variance one. In the convention used here and in the two
OpenAI manuscripts, the energy of that configuration is

$$
H_n(\sigma)=\frac{1}{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j.
$$

Here **pure** means that the random interaction contains only pair products;
**zero field** means that no one-spin term $h\sum_i\sigma_i$ is present.

We maximise this energy. The term **ground-state value** below means
this limiting maximum per spin, in the stated sign convention.

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
agree, their sum is $-3$. Hence the maximum total energy is $1/\sqrt3$, or $1/(3\sqrt3)$ per spin,
rather than the $\sqrt3$ suggested by satisfying every pair separately.
These deterministic couplings illustrate conflicting preferences. Their
exact values have probability zero under the Gaussian law; this calculation
is neither an SK average nor a large-system estimate.

The large-system question concerns

$$
P_* = \lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma).
$$

Here $\mathbb E$ averages over the random couplings $J_{ij}$. The
maximisation occurs after those couplings have been drawn. Existence and
evaluation of this limit follow from the ground-state Parisi theorem in
Section 3.2; the two-spin calculation alone does not establish either.

To understand why the random energies cannot be treated as independent,
compare two configurations through their **overlap**

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

Thus the covariance has the form $n\xi(R(\sigma,\tau))-1/2$, where
$\xi(t)=t^2/2$. The function $\xi$ records how similarity between two
configurations determines the covariance of their energies. This is the
covariance function used in the variational formula below.
The finite-size correction $-1/2$ is real: for two configurations with
zero overlap their energies can be negatively correlated. Adding the
same independent centred Gaussian of variance $1/2$ to every energy
removes this correction and leaves the expected maximum unchanged.
The sources account for that normalisation when using the Parisi formula.

The common Gaussian can be exhibited explicitly. If $G_{ij}$ are
independent standard Gaussians for all ordered pairs, set
$J_{ij}=(G_{ij}+G_{ji})/\sqrt2$ for $i<j$. Then

$$
\frac1{\sqrt{2n}}\sum_{i,j}G_{ij}\sigma_i\sigma_j
=H_n(\sigma)+\frac1{\sqrt{2n}}\sum_iG_{ii}.
$$

The last term has variance $1/2$ and is the same for every configuration.
It changes neither the maximising configurations nor any difference between
their rewards. Its mean is zero, so it also preserves the expected maximum.
This is the ordered-pair convention with coefficient $1/\sqrt2$ that
matches the cited Parisi formula.

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

To favour large rewards without yet taking a maximum, assign probability
$e^{\lambda h_i}/\sum_j e^{\lambda h_j}$ to outcome $i$. This is the
**Gibbs distribution**. The parameter $\lambda$ is called inverse
temperature: increasing it concentrates probability on the best outcomes.
In the two-spin example, writing $h=J/\sqrt2$, the sum is
$4\cosh(\lambda h)$: two configurations have reward $h$ and two have
reward $-h$. Each aligned configuration has Gibbs probability
$e^{\lambda h}/(4\cosh(\lambda h))$, and each antialigned one has
probability $e^{-\lambda h}/(4\cosh(\lambda h))$. Their mean total
reward is $h\tanh(\lambda h)$, which tends to $|h|$ as the
inverse temperature grows. This optimisation is performed for each
realisation before averaging over $J$. Maximising the averaged rewards
would instead give zero, since every fixed configuration has mean zero.

The logarithmic expression is a smooth way of approximating a maximum.
For the $2^n$ spin configurations, its error **per spin** is at most
$\log2/\lambda$. Zero temperature means $\lambda\to\infty$, when this
**soft maximum** becomes the maximum. This finite inequality explains the
name; see also [Auffinger and Chen (2017), §1][auffinger-chen].
The existence of the large-system limit and its Parisi representation
are further theorems. In fact this finite bound gives a useful joint-limit statement. If
$f_n(\lambda)=\mathbb E\log\sum_\sigma e^{\lambda H_n(\sigma)}/(n\lambda)$
and $e_n=\mathbb E\max H_n/n$, then
$0\le f_n(\lambda)-e_n\le\log2/\lambda$. Since $e_n\to P_*$,
every sequence $\lambda_n\to\infty$ satisfies
$f_n(\lambda_n)\to P_*$. This scalar conclusion uses an error bound
uniform in $n$. No corresponding uniform circuit bound has been obtained
from it. The scale $t$ used next is neither temperature nor system size.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

The Parisi formula minimises over functions $\gamma(t)$ on $[0,1)$.
The variable $t$ indexes the successive increments of the Gaussian noise
in Section 3: it is the variance accumulated so far. Thus
noise already revealed has variance $t$, and the remaining noise has
variance $1-t$. This is a new variational description supplied by a theorem,
not an identification of $t$ with a finite overlap $R$ or $|R|$.
The allowed, or **admissible**, functions are nonnegative, nondecreasing, right-continuous,
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

To record where $\gamma$ increases, assign a measure $\mu_\gamma$ by

$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\le t<1.
$$

This is the **Stieltjes measure** of $\gamma$. For $a<b$,
$\mu_\gamma((a,b])=\gamma(b)-\gamma(a)$. Thus a gap means **no
increase**, even if $\gamma$ is positive there. We study the support of
the increments, rather than the set where the function itself is nonzero.

A point belongs to the **support** when every neighbourhood of it,
intersected with $[0,1)$, has positive measure. **Full relative support** means that every point
of $[0,1)$ has this property. In particular, every nonempty open interval
below one receives mass, so $\gamma(b)>\gamma(a)$ for every
$0\le a<b<1$. The word *relative* matters: the endpoint $1$ is outside
the underlying space.

For the displayed example, interval masses are obtained by integrating
a function equal to one on $(0,1/3)$ and $(2/3,1)$ and zero on
$(1/3,2/3)$. This function is the measure's **density**. Its support is
$[0,1/3]\cup[2/3,1)$, with endpoints understood relative to $[0,1)$.
It has infinitely many support points and no final interval on which
$\gamma$ is constant, but it still has an interior gap.

For example, a neighbourhood of zero is relative to that space and
contains an interval $[0,\delta)$. It can have positive mass even if
the single point $0$ has none. A support point need not carry any mass by itself. A point that does
carry positive mass is called an **atom**; the displayed continuous
example has none.

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
adapts the source figure credited in Section 2.1.}
\label{fig:support-increments}
\end{figure}
```

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

The integrability condition can also be written in terms of the measure.
Integrating the cumulative mass and interchanging two nonnegative integrals gives

$$
\int_0^1\gamma(t)\,dt
=\int_{[0,1)}(1-s)\,\mu_\gamma(ds)<\infty.
$$

Thus mass near one is weighted less heavily, explaining how infinite total
mass can be admissible. The convention at zero is necessary: increments
$\gamma(b)-\gamma(a)$ alone would not specify its initial atom.

Full support does not force a density. Enumerate distinct rationals
$r_k$ in $(0,1)$ and take $\mu=\sum_{k\ge1}2^{-k}\delta_{r_k}$.
Every nonempty interval contains some $r_k$ and has positive mass, although
all the mass is atomic. Its cumulative function is bounded and admissible.
Conversely, even a smooth density can vanish at an interior point without
losing full support: the measure $(t-1/2)^2\,dt$ has positive mass in
every interval. The support conclusion alone cannot distinguish these
examples from a strictly positive density.

Every $\mu_\gamma$ is **locally finite**: each $[0,T]$ with $T<1$ has finite mass
$\gamma(T)$. Local finiteness will let us remove a small fraction of
the mass on such an interval even if the total mass is infinite.
Full support concerns where every neighbourhood receives mass; by itself
it does not assert a density, smoothness, or a quantitative cost for an
approximately optimal candidate with a plateau.
<!-- /passage:order-parameter-example -->

<!-- passage:gap-area-example -->
### 2.1 The calculus contradiction in a small model

The proof will associate a differentiable function $q$ with a minimising
order parameter. If that order parameter had a flat interval $(r,s)$,
optimality would force $q(r)=r$ and $q(s)=s$. Thus $q$ would have to
increase by exactly $s-r$ across the interval. A separate estimate would
force its derivative to be strictly less than one there, making that
increase impossible. For now, we can understand this contradiction without
knowing how the proof constructs $q$. The following polynomial model
isolates the calculus; Sections 3 and 5 will supply the actual function
and justify the two requirements.

Use the same interval $[1/3,2/3]$ as the plateau in Section 2. Set
$x=3t-1$, so $0\le x\le1$, and for $0\le\kappa\le1$ define

$$
f_\kappa(t)=1-\kappa x(1-x).
$$

Think of $f_\kappa$ as a proposed derivative $q_\kappa'$.
It has endpoint values one, stays between $3/4$ and one, and has
$f_\kappa''(t)=18\kappa$. For $\kappa>0$ it is strictly convex.
Since $dt=dx/3$,

$$
\int_{1/3}^{2/3}f_\kappa(t)\,dt
=\frac13\int_0^1[1-\kappa x(1-x)]\,dx
=\frac13-\frac\kappa{18}.
$$

Require the left endpoint value $q_\kappa(1/3)=1/3$. Integration
therefore forces

$$
q_\kappa(2/3)=\frac23-\frac\kappa{18}.
$$

If we also require the right endpoint value $q_\kappa(2/3)=2/3$,
these requirements conflict whenever $\kappa>0$. For $\kappa=1$,
the required value $2/3=12/18$
is missed by $1/18$: the model reaches only $11/18$. This is the
incompatibility in the no-gap proof. When $\kappa=0$, the slope is
constantly one, the deficit vanishes, and both endpoint requirements can
hold. Ordinary convexity alone would allow that equality case.

The source proof allows endpoint derivatives less than one as well;
choosing both equal to one gives this model the largest permitted
endpoint values. The parameter $\kappa$ is a teaching parameter,
with no claimed relation to the plateau height $c$. The model does
not prove the strict-curvature estimate, or address initial and
terminal gaps. Sections 5.3 and 5.4 supply those source arguments.
<!-- /passage:gap-area-example -->

<!-- passage:value-and-diffusion -->
## 3. How a candidate receives its value

### 3.1 A function goes in; a number comes out

A **functional** assigns a number to an entire candidate function.
Here the candidate is $\gamma$. Its value will be defined through an
auxiliary one-dimensional optimisation with a random input and a cost for
responding to that input. The coefficient $\gamma$ determines both how
strongly the response changes the position and how much it costs. This
is the variational description supplied by the Parisi theorem; we are
not identifying its paths with configurations of the original spins.

Write $\Phi_\gamma(t,x)$ for the best expected terminal reward minus
that cost when starting at position $x$ at time $t$. At the final time
$1$, the reward is absolute position. This reward $|x|$ itself
is a one-spin optimisation: $|x|=\max_{\sigma\in\{-1,1\}}x\sigma$.

Standard Brownian motion $B$ is a random continuous path starting at
zero. Its increments over disjoint time intervals are independent
Gaussians; $B_s-B_t$ has mean zero and variance $s-t$ for $s>t$.
This is the only noise law needed to read the formula. Choose a response $\alpha_s\in[-1,1]$ at each time $s$. This
response, called a **control**, may use increments observed after $t$
and up to $s$, but not future increments. Expectations in this control
problem average over Brownian paths, with the deterministic coefficient
$\gamma$ fixed; they do not average over the finite couplings $J_{ij}$. For a fixed $\gamma$, set

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

At a starting time $t$, the available information at $s\ge t$ is generated
by $B_r-B_t$ for $t\le r\le s$; the response must be measurable using
this past information. This restriction is part of the optimisation.

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

Finite-step candidates can also be evaluated by a backward recursion of
Gaussian integrals, derived in Section 10.1 using the partial differential
equation introduced in Section 3.3.

This evaluates one candidate; it has not solved the minimisation.
Once the Parisi formula below is supplied, it gives the upper bound
$P_*\le\sqrt{2/\pi}$. The full-support theorem will also tell us that
this particular candidate is not a minimiser, since its measure has empty support.

### 3.2 The theorem connecting the two optimisation problems

The ground-state Parisi formula and attainment identify

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

Each admissible candidate therefore gives an asymptotic upper bound on
the maximum energy per spin. The outer minimisation searches for the sharpest bound. The equality
and its attainment are the results of
[Auffinger and Chen (2017), Theorem 1 and proof of Lemma 3][auffinger-chen].
The infimum formula and the existence of a candidate attaining it are
separate parts of that input: an infimum is a greatest lower bound,
whereas a minimum must be achieved by a candidate. Their construction
produces an admissible $\widehat\gamma$ for which
$P_*\ge\mathcal P(\widehat\gamma)\ge\inf_\gamma\mathcal P(\gamma)=P_*$.
Equality throughout gives attainment; evaluating a convenient candidate
alone would not give the first inequality. The support theorem
studied here assumes
an admissible minimiser and proves a property of it; neither selected
formal statement concludes minimiser existence.

The passage from positive temperature to this terminal absolute value,
including the $\log2/\lambda$ term and the rescaling of $x$, is recorded in
Section 10.2.

### 3.3 Slope, curvature and an auxiliary path

For a fixed $\gamma$, differentiate the value with respect to the
starting position $x$. Write $u(t,x)=\partial_x\Phi_\gamma(t,x)$
for its slope and $a(t,x)=\partial_{xx}\Phi_\gamma(t,x)$ for its
curvature. These are the spatial derivatives used below.
The source proves that $\Phi_\gamma$ is convex in $x$ and has slopes
between $-1$ and $1$, so $a\ge0$ and $|u|\le1$ before the terminal time.
The optimal response can be taken as the current slope $u$. We now
check why the slope is the right choice.

The source describes this value by a partial differential equation (PDE).
It is solved backwards from the prescribed reward at time one:

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

The quadratic term records the local choice of control. For a proposed
response $\alpha\in[-1,1]$, the control displaces the position by
$\gamma\alpha\,dt$ over a short time $dt$. At spatial slope $u$,
its first-order benefit is therefore $\gamma\alpha u\,dt$.
Subtracting the control cost gives the rate

$$
\gamma\alpha u-\frac12\gamma\alpha^2
=\frac12\gamma u^2-\frac12\gamma(\alpha-u)^2.
$$

Since $|u|\le1$, the choice $\alpha=u$ is allowed and attains the
maximum. Nonnegativity of $\gamma$ fixes the inequality. If $\gamma=0$,
every response has the same local value; the slope remains a valid choice.
Choosing the response over a short first step and then using the optimal
continuation is the principle of **dynamic programming**. Brownian variance
adds the second-derivative term $\Phi_{xx}/2$ to that short-step calculation;
balancing it with the optimised control benefit gives the displayed equation.

Using this response, position follows the random path

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

This path is the **associated diffusion**. Its Brownian term is
accumulated noise; the integral is its **drift**, the displacement chosen
through the response. It is an auxiliary real-valued process, not the
physical motion of spins or the evolution of a quantum state.
The deterministic quantity that will test optimality is
$$
q(t):=\mathbb E[u(t,X_t)^2].
$$
It measures the mean square of the slope response along that path. Its
difference from the scale, $q(t)-t$, determines the first-order change
in the objective when we vary $\gamma$, as Section 5 shows. The next subsection explains why
$q$ can be differentiated using the curvature $a$.

To check this calculation along a random path, we use Itô's rule: if
$dY_t=b_t\,dt+dB_t$, then the drift of a smooth $f(t,Y_t)$ is
$f_t+b_tf_x+f_{xx}/2$, and its noise term is $f_x\,dB_t$.
The extra second derivative reflects the variance of Brownian increments.
For the controlled path $b_t=\gamma(t)\alpha_t$, the drift of
$\Phi(t,Y_t)-\tfrac12\int\gamma\alpha^2$ is exactly
$-\gamma(\alpha-u)^2/2$. Its expected accumulated value is therefore
no larger than its starting value, with equality under the slope response.
For a path starting at $(r,x)$ and $r<T<1$, the precise loss is
$$
\mathbb E\left[\Phi_\gamma(T,Y_T)-\frac12\int_r^T\gamma\alpha^2\,dt\right]
=\Phi_\gamma(r,x)-\frac12\mathbb E\int_r^T
\gamma(t)\bigl(\alpha_t-u(t,Y_t)\bigr)^2\,dt.
$$
The omitted noise term is a stochastic integral, the limit of sums of
past-dependent coefficients multiplied by Brownian increments. Its
expectation is zero here because the coefficient is bounded and
**adapted**, meaning that it uses only noise already observed. Section 3.4
shows the finite-sum calculation behind this assertion. The remaining
integral is nonnegative and finite:
$|\alpha-u|\le2$ and $\gamma$ is integrable. The formula identifies
exactly what is lost by departing from the slope response.
The calculation is first justified for step coefficients and smoothed
terminal data; the source proves the passage to admissible coefficients.

For a general admissible coefficient, these calculations use the source's
regularity and existence results. For every $T<1$, derivatives of positive order in $x$ are bounded
uniformly for $0\le t\le T$ and $x\in\mathbb R$; this region is
called a fixed strip. The slope-driven path exists and is unique for
its Brownian motion. Section 10.4 gives the approximation and uniqueness
arguments. The restriction $T<1$ avoids the corner of the final reward $|x|$.

### 3.4 The stochastic identity used in the calculus proof

Set $M_t=u(t,X_t)$. A **conditional expectation** averages over future
randomness while retaining the information observed so far. The source
proves that $M_t$ is a bounded **martingale**: for $0\le t<s<1$,

$$
\mathbb E[M_s\mid\mathcal F_t]=M_t,
$$

where $\mathcal F_t$ denotes the observations available by time $t$.
The martingale has a specific algebraic cause. Differentiate the PDE in
$x$ to obtain $u_t=-u_{xx}/2-\gamma u u_x$. Along the optimal path,
whose drift is $\gamma u$, Itô's rule gives

$$
du(t,X_t)=
\underbrace{(u_t+\gamma u u_x+u_{xx}/2)}_{0}\,dt
+u_x(t,X_t)\,dB_t
=a(t,X_t)\,dB_t.
$$

The slope response cancels the predictable drift of the slope itself.
This calculation supplies the martingale mechanism. Its justification
uses the fixed-strip approximation in Section 10.4, rather than assuming
classical time derivatives at jumps of $\gamma$.

This does not say that the realised path is constant. It says that its
present value is its conditional forecast of any later value.

The function introduced above is the second moment of this martingale,

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
For $i<j$, the product $a_i\Delta B_i a_j$ is known before
$\Delta B_j$, so
$\mathbb E[a_i\Delta B_i a_j\Delta B_j]
=\mathbb E[a_i\Delta B_i a_j\mathbb E(\Delta B_j\mid\mathcal F_{t_j})]=0$.
Thus conditioning before the later increment makes cross terms vanish and gives

$$
\mathbb E\left[\left(\sum_j a_j\Delta B_j\right)^2\right]
=\sum_j\mathbb E[a_j^2]\Delta t.
$$

For a concrete adapted sum, let $Z_1,Z_2$ be independent standard
Gaussians. The coefficients $1$ and $Z_1$ produce
$S=Z_1+Z_1Z_2$. Conditioning on $Z_1$ gives
$\mathbb E[Z_1Z_2\mid Z_1]=0$; hence $\mathbb ES^2=1+1=2$.
The terms $Z_1$ and $Z_1Z_2$ have zero expected product, so they
are orthogonal as random variables. They are nevertheless dependent:
$\mathbb E[Z_1^2(Z_1Z_2)^2]=3\ne1$.
If the coefficient of $Z_1$ were allowed to be $Z_1$ itself, the term
would instead be $Z_1^2$, with mean one. The rule that a coefficient
uses only earlier increments is doing real work.

The stochastic integral is the mean-square limit of such sums: the
expectation of the squared difference tends to zero. Passing to that
limit gives
$q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds$; the source's regularity
then gives the derivative above. Zero external field gives symmetry,
$u(0,0)=0$, and hence $q(0)=0$. At zero a displayed time derivative
is understood from the right.

Thus one candidate $\gamma$ determines a random slope response $M_t$
and its deterministic second moment $q(t)$. The variation argument will
use the latter.

For the central proof, carry forward $q(0)=0$, $0\le q(t)\le1$ and
$q'=\mathbb E[a^2]$. The first-variation and strict-curvature theorems
will supply the other inputs. The full analytic foundation is in [OpenAI (2026a), §2][support-regularity],
which proves the regularity, diffusion and constant-interval transfer lemmas.
<!-- /passage:value-and-diffusion -->

<!-- passage:full-support-statement -->
## 4. The full-support result

[Chen (2026), Theorem 1.3][chen-support] had already proved full relative
support and that the measure is represented by a smooth density. The statement and quantitative
no-gap argument below follow [OpenAI (2026a), Theorem 1.1][support-manuscript];
its further conclusion that the density is strictly positive on $(0,1)$
appears in Section 5.5.

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
regularity and curvature estimates. This statement does not assert a density
for the Stieltjes measure or cover nonzero field or mixed-spin covariances.
Section 5.5 explains the source's additional density corollary separately.
<!-- /passage:full-support-statement -->

<!-- passage:zero-candidate-example -->
### 4.1 An exact candidate which does not minimise

The minimiser hypothesis matters. The Gaussian formula for $\gamma=0$ and a decrease obtained by adding
a small amount to the coefficient on a final interval already appear in
[Chen–Handschy–Lerman, proof of Theorem 6, pp. 14–16, equation (24)][chl-optimality].
We evaluate that setup explicitly here. Take $\gamma_0(t)=0$. It is
admissible, but its Stieltjes measure is zero, and its diffusion is
$X_t=B_t$. The calculation below shows that its moment fails $q(t)=t$ and that a small added atom lowers the objective.
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

This allowed change lowers the value. It proves non-minimality,
without finding a minimiser or establishing full support. Section 5 will recover the same
negative derivative from the general first-variation formula.

### 4.2 Even full support and positive density do not certify a minimum

Take $\gamma(t)=12t$. Its Stieltjes density is the smooth positive
constant twelve, so it has full support and no initial atom. Yet the
allowed constant response $\alpha=1$ yields
$\Phi_\gamma(0,0)\ge\mathbb E|B_1+6|-3\ge3$ by Jensen's
inequality. Subtracting $\tfrac12\int_0^1 12t^2\,dt=2$ gives
$\mathcal P(\gamma)\ge1$. The zero candidate has value
$\sqrt{2/\pi}<1$, so $12t$ cannot minimise.
This checked example distinguishes a necessary property of minimisers
from a sufficient test for optimality.
<!-- /passage:zero-candidate-example -->



<!-- passage:contact-and-gap -->
## 5. Why a flat interval cannot minimise

### 5.1 Allowed changes and their first-order cost

The proof needs a way to detect whether placing more Stieltjes mass at
a scale would improve the objective. For a proposed change $\eta(t)$, the **first variation** is the slope of
$\varepsilon\mapsto\mathcal P(\gamma+\varepsilon\eta)$ at zero.
At a minimum its **right** derivative is nonnegative whenever small
positive values of $\varepsilon$ remain admissible. It need not vanish:
constraints may forbid the opposite change.

Adding a small atom at a scale $s$ is always an allowed change:
it raises every later cumulative value by the same amount. Removing an
atom is allowed only when that mass already exists. This is why we use the right derivative along an allowed change.

The source proves the following first-variation formula. If $\eta$ is
an integrable direction for which
$\gamma+\varepsilon\eta$ stays admissible for sufficiently small
$\varepsilon\ge0$, the right derivative is

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

Section 10.3 derives this formula by comparing the two PDEs, including
the order of the endpoint and perturbation limits. We first use it to
understand a concrete mass operation.

Adding an atom at a scale $s$ increases $\gamma(t)$ by the same amount
for every $t\ge s$, because $\gamma$ is cumulative. This is the direction
$\eta(t)=\mathbf1_{[s,1)}(t)$. Its cost is therefore recorded by the function

$$
G(s)=\int_s^1(q(t)-t)\,dt.
$$


Thus $G(s)/2$ is the first-order cost of adding a unit atom at $s$.
The tail integral appears because this one mass change affects all later
scales. The residual $q(s)-s$ at a single scale would not measure that cost.

For the zero candidate, this recovers the promised numerical slope exactly:

$$
\frac12G_0(0)
=\frac12\left[\frac2\pi
 \int_0^1\arcsin t\,dt-\frac12\right]
=\frac14-\frac1\pi,
$$

since $\int_0^1\arcsin t\,dt=\pi/2-1$. This agrees with the
constant-candidate expansion in Section 4.1.

At a minimiser the derivative in this direction cannot be negative,
so $G(s)\ge0$ everywhere. Removing a fraction of the existing measure
on a compact interval $K=[0,T]$, with $T<1$, is also admissible.
The direction is $\eta_K(t)=-\mu_\gamma(K\cap[0,t])$: every atom
or infinitesimal mass removed at $s$ lowers the cumulative function at
all later times. For $0\le\varepsilon\le1$, scaling the mass on $K$ by
$1-\varepsilon$ preserves nonnegativity and therefore an admissible
cumulative function. Moreover,
$\|\eta_K\|_1=\int_K(1-s)\,\mu_\gamma(ds)<\infty$, where
$\|f\|_1=\int_0^1|f(t)|\,dt$ measures the total absolute size of a
function on the time interval.
For instance, removing a fraction of mass spread with constant density
one on $[a,b]$ changes
$\gamma(t)$ by $-\varepsilon\max(0,\min(t,b)-a)$: zero before $a$,
a linear decrease of its increment on $[a,b]$, and a constant decrease
after $b$. No atom at either endpoint is needed.
The mass $\mu_\gamma(K)=\gamma(T)$ is finite, and $|q(t)-t|\le1$.
Consequently the double integral is absolutely integrable; changing its
order by Fubini's theorem gives

$$
0\le -\frac12\int_KG(s)\,\mu_\gamma(ds).
$$

Since $G\ge0$, the integral must vanish. If $G$ were positive at a
support point, continuity would make it positive on a neighbourhood
having positive measure, contradicting that integral for a sufficiently
large $T<1$. Thus $G=0$ on the support. This equality is called **contact**: the
nonnegative function $G$ touches zero there. Removing a fraction of
all the mass in $K$ is essential because that mass need not be atomic.

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


These conditions also give an exact optimality criterion: an admissible
$\gamma$ minimises $\mathcal P$ if and only if its own potential
$G$ is nonnegative and vanishes on $\operatorname{supp}\mu_\gamma$.
The converse uses weighted Fubini and convexity of the control value;
Section 10.5 gives the derivation, following
[Chen–Handschy–Lerman, Proposition 4][chl-optimality]. The words “its own”
are essential: $q$ must come from this candidate's PDE and diffusion.
An arbitrary curve satisfying contact is not a test of optimality.
For the full-support proof we need the forward implication already
established, and now use its endpoint conditions to rule out a gap.

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

The area calculation in Section 2.1 now has its intended objects: its
model slope represents $q'$, its contact values represent $q(r)=r$
and $q(s)=s$, and the missing area contradicts that prescribed change.

The difficult ingredient is the strict sign of $q'''$, not the final
integration. Direct differentiation produces both positive and negative
terms; convexity of $\Phi_\gamma$ alone does not settle their sum.
For example, set $b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$ on an interval
where $\gamma=c>0$. Differentiated PDEs and Itô's rule give

$$
q''=\mathbb E[b^2-2ca^3],\qquad
q'''=\mathbb E[d^2-12cab^2+6c^2a^4].
$$

The middle term in the second expression is negative. Merely knowing
$a\ge0$ does not make the integrand positive. The law of $X_t$ matters.
For step coefficients and smoothed terminal data, the source writes the
density as a product of two positive functions, one determined backwards
from the terminal data and the other forwards from the initial data.
It proves inequalities for the derivatives of their logarithms. Integration by parts can then add
expressions of mean zero to the displayed polynomial and reveal a
positive remainder.

A simple Gaussian analogy explains the operation. For a sufficiently
decaying differentiable function $F$ and standard Gaussian $Z$,
$\mathbb E[F'(Z)-ZF(Z)]=0$. Adding a multiple of this expression
changes an integrand without changing its expectation. The source uses
the actual transformed diffusion density in place of the Gaussian density,
with separately proved sign and boundary conditions, and an exact rational
identity chooses the correction. The algebra alone would not justify the
integration by parts or those sign conditions. On a constant interval with $c>0$ it obtains

$$
q'''(t)\ge\frac{c^2}{1000}
\mathbb E[a(t,X_t)^4]>0.
$$

This is an inequality after expectation, not a claim that every term
before integration is positive. Approximation transfers that integrated
bound to an integrable order parameter: only expectations of polynomials
in the first four spatial derivatives must converge. No convergence of
the auxiliary logarithmic density derivatives is needed. The complete analytic argument
combines the shape inequalities of [OpenAI (2026a), §3][support-signs]
with its [rational identity, Lemma 4.1][support-certificate], then
applies [Proposition 5.1][support-curvature].
<!-- /passage:contact-and-gap -->



<!-- passage:endpoints -->
### 5.4 Initial, zero and terminal gaps

Three remaining cases explain why the endpoint conditions were stated
carefully. If a gap has coefficient zero, the heat equation gives strict
increase of $q'$ instead of the positive-coefficient convexity argument.
Indeed $q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$ inside such
a gap. Noise accumulated over an earlier part of the gap gives $X_t$ a
density formed from positive Gaussian densities. The derivative $\Phi_{xxx}(t,\cdot)$ cannot vanish identically:
then the even function $\Phi(t,\cdot)$ would be quadratic, inconsistent
with having slopes in $[-1,1]$ and differing from $|x|$ by a bounded amount.
Thus $q'(t)<q'(s)\le1$, and integration gives the same contradiction.
An initial gap $[0,s)$ also has coefficient zero. Here the left
endpoint identity comes from $q(0)=0$, even though zero is not a
support point. If instead zero belongs to the support and $(0,s)$
is missing, the mass at zero makes this a positive plateau. The preceding
convexity argument applies with the one-sided contact condition at zero;
symmetry again supplies $q(0)=0$.

A terminal plateau is different: one cannot use a support point at
$1$, because $1$ is outside the domain. The source instead proves that
on a putative terminal constant interval,

$$
1-q(t)\ge C\sqrt{1-t}
$$

for some $C>0$ and all sufficiently late $t$. The remaining Brownian noise has standard deviation $\sqrt{1-t}$.
Within that distance of zero, the final sign is still uncertain.
On $|x|\le\sqrt{1-t}$, the terminal Gaussian smoothing gives both
signs a probability bounded away from zero, so $1-u(t,x)^2$ is
bounded below by a positive constant. The source's transition-density formula
for the hypothetical constant interval gives a density for $X_t$ that
is bounded below on this window, uniformly for late $t$. Integrating
$1-u(t,x)^2$ across a window of width $2\sqrt{1-t}$ proves the
bound. This density estimate follows from the assumed plateau; it is
not a general endpoint density assumption. Hence
$q(t)-t\le(1-t)-C\sqrt{1-t}<0$ near one, making $G(s)<0$ there.
More explicitly,
$$
G(s)\le\frac{(1-s)^2}{2}-\frac{2C}{3}(1-s)^{3/2}<0
$$
for $s$ sufficiently close to one. This contradicts the nonnegativity
supplied by optimality. The estimate also excludes the empty-support case $\gamma=0$.

These cases exhaust the components of the complement of a relatively
closed support. Once all gaps are excluded, every interior time is a
contact point, so $q(t)=t$ everywhere below one, including zero by
symmetry. Differentiating yields $\mathbb E[a(t,X_t)^2]=1$.
The mass-removal and endpoint arguments are given in
[OpenAI (2026a), §6][support-variation].

<!-- /passage:endpoints -->

<!-- passage:density-and-approximation -->
### 5.5 Exact minimisers, densities and approximate minimisers

The no-gap proof is complete. This subsection explains a further density
consequence and the distinction between exact and approximate minimisers;
the scalar-energy argument can be read directly in Section 6.

Full support is a statement about every interval, not a regularity theorem
by itself. The source proves more in a separate corollary. For the same
admissible minimiser, $\gamma(0)=0$ and $\gamma$ is smooth on $[0,1)$,
with derivatives at zero understood from the right. Its Stieltjes measure
is $\gamma'(t)\,dt$, with $\gamma'(t)>0$ for $0<t<1$.
This is [OpenAI (2026a), Corollary 6.4][support-density], an additional
ordinary mathematical conclusion, not an added clause of the selected
formal support statement.

One can see the start of the regularity argument. Itô's rule for
$a=\Phi_{xx}$ gives
$\frac{d}{dt}\mathbb Ea^2=\mathbb E\Phi_{xxx}^2-2\gamma\mathbb Ea^3$
for almost every time. Since $\mathbb Ea^2=1$ at a minimiser,

$$
\gamma(t)=\frac{\mathbb E[\Phi_{xxx}(t,X_t)^2]}
                 {2\mathbb E[a(t,X_t)^3]}.
$$

The denominator is at least two by $a\ge0$ and $\mathbb Ea^2=1$.
The moments are continuous, so right continuity extends the initially
almost-everywhere identity to every time. Repeated differentiation of the equations for all polynomial
moments together gives derivatives of every order; symmetry gives
$\Phi_{xxx}(0,0)=0$ and hence $\gamma(0)=0$. Strict positivity of the
density uses the quantitative lower bound in Section 5.3, applied to shrinking
constant-interval approximations. Smoothness and nonnegative derivative
alone would not exclude an isolated zero, as Section 2's density example
shows. The limiting step transfers expectations of polynomials in spatial
derivatives at one fixed time. It does not assert convergence of third
time derivatives of the approximating moment functions. The source credits Chen's independent full-support and smoothness
results [Chen (2026), Theorem 1.3][chen-support].

An exact minimiser has no gaps, but can a function with finitely many
flat steps have value close to the minimum? Yes. Comparing the control formula for two coefficients
using the same response gives

$$
\|\Phi_\gamma-\Phi_{\widetilde\gamma}\|_\infty
 \le\tfrac32\|\gamma-\widetilde\gamma\|_1,
\qquad
|\mathcal P(\gamma)-\mathcal P(\widetilde\gamma)|
 \le2\|\gamma-\widetilde\gamma\|_1.
$$

Here the infinity norm is the supremum over all starting times and
positions, and the $L^1$ norm is the integral of the absolute coefficient
difference on $[0,1)$. The first bound uses $||x|-|y||\le|x-y|$ and $|\alpha|\le1$;
the penalty adds at most half the $L^1$ difference. Truncation near one
followed by monotone step approximation gives admissible finite staircases
converging in $L^1$ to any admissible coefficient. For example,
$\gamma(t)=t$ and $\gamma_m(t)=\lfloor mt\rfloor/m$ have
$\|\gamma-\gamma_m\|_1=1/(2m)$. Applied to a minimiser, the general
approximation makes objective values converge to the minimum even though
every finite staircase has gaps. For an explicit construction even when $\gamma$ is unbounded near one,
cap it at $M$ and round its values down in steps of $1/m$:
$$
\gamma_{M,m}(t)=\frac{\lfloor m\min(\gamma(t),M)\rfloor}{m}.
$$
This is a nonnegative, nondecreasing, right-continuous function with
finitely many values, and
$$
\|\gamma-\gamma_{M,m}\|_1
\le\int_0^1(\gamma(t)-M)_+\,dt+\frac1m.
$$
Here $(x)_+=\max(x,0)$. Choose $M$ first to control the integrable tail, then $m$ for the rounding
error. The functional bound above makes its value arbitrarily close to
that of $\gamma$. Finite staircases have flat intervals, so there is no
uniform positive loss for every approximate minimiser with a plateau.
The no-gap theorem concerns exact minimisers.
<!-- /passage:density-and-approximation -->

<!-- passage:scalar-identities -->
## 6. Recovering the optimal value from one terminal spin

Full support gives $\mathbb E[u(t,X_t)^2]=t$ at every time.
As $t$ approaches one, this second moment will force the limiting slope
to be a sign. It converges almost surely and in mean square to a random
variable $U$ with $|U|\le1$. Since its second moment tends to one,
$\mathbb E[U^2]=1$. A nonnegative random variable with expectation
zero vanishes almost surely; apply this to $1-U^2$ to obtain

$$
U\in\{-1,1\}\quad\text{almost surely}.
$$

The process has a useful prediction interpretation. Bounded martingale
convergence gives $M_t=\mathbb E[U\mid\mathcal F_t]$, so
$\mathbb E[UM_t]=\mathbb E[M_t^2]=t$ and

$$
\mathbb E|U-M_t|^2=1-2t+t=1-t.
$$

Thus $M_t$ is the conditional mean of the terminal spin and $1-t$ is
its mean-square prediction error. Since $\mathbb EM_t=0$, the two
terminal signs have equal probability. The second moment $q(t)=t$
does not say that $M_t$ is Brownian motion. At each positive time Brownian
motion has positive probability of lying outside $[-1,1]$, whereas $M_t$
always stays in that interval. A matching second moment does not determine
a process's distribution.

We also need the endpoint of the path $X_t$. Since $|u|\le1$ and
$\gamma$ is integrable, its accumulated drift has a finite limit. Define
$$
X_1=B_1+\int_0^1\gamma(s)u(s,X_s)\,ds=\lim_{t\uparrow1}X_t.
$$
The spin $U$ and position $X_1$ are different quantities. The calculation
below will show that $U X_1=|X_1|$, so $U$ chooses an optimal sign for
this terminal position.

Combining the
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

The endpoint passage has quantitative bounds. Write
$\|V\|_2=(\mathbb E|V|^2)^{1/2}$ for the root-mean-square size of
a random variable. Since $|u|\le1$,

$$
\|X_1-X_t\|_2\le\sqrt{1-t}+\int_t^1\gamma(s)\,ds\longrightarrow0.
$$

The control formula also gives
$$
0\le\Phi_\gamma(t,x)-|x|\le\delta_t,
\qquad
\delta_t=\sqrt{2(1-t)/\pi}+\frac12\int_t^1\gamma(s)\,ds\longrightarrow0.
$$
For the lower bound use the zero response and convexity of absolute value.
For the upper bound use the triangle inequality and
$|\alpha|-\alpha^2/2\le1/2$ for $|\alpha|\le1$.
Together these estimates give
$\mathbb E|\Phi_\gamma(t,X_t)-|X_1||\to0$, the asserted $L^1$
convergence. We may therefore let
$t\uparrow1$ and substitute $q(s)=s$. The left side tends to
$\mathbb E|X_1|$, so $\Phi_\gamma(0,0)$ is that expectation minus
half the integral. Subtracting the other half in $\mathcal P$ gives
the whole integral in the value formula.

It remains to show that the limiting slope chooses an optimal terminal
sign. We cannot simply differentiate $|x|$ at zero. Instead, the
tangent inequality for a convex function gives
$xu(t,x)\ge\Phi_\gamma(t,x)-\Phi_\gamma(t,0)$.
Together with $|u|\le1$, $\Phi_\gamma(t,x)\ge|x|$ and
$\Phi_\gamma(t,0)\le\delta_t$, this yields
$$
0\le |x|-xu(t,x)\le\delta_t.
$$
Apply it at $x=X_t$ and use the almost-sure limits of $X_t$ and $M_t$.
Since $\delta_t\to0$, we get $UX_1=|X_1|$, including on
$\{X_1=0\}$. We need neither a derivative of $|x|$ at zero nor the assumption
$\Pr(X_1=0)=0$.
Multiply the diffusion equation at time one by $U$ and take expectations.
Martingality gives
$\mathbb E[Uu(t,X_t)]=\mathbb E[u(t,X_t)^2]=t$, so

$$
\mathbb E|X_1|=\mathbb E[UB_1]+\int_0^1t\gamma(t)\,dt.
$$

Fubini is legitimate here because $|Uu|\le1$ and $\gamma$ is
integrable. The deterministic penalty cancels. Pairing
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
comparison.

This completes the scalar argument: variational optimality gave contact,
curvature extended contact to every time, and the terminal martingale
cancelled the penalty. We have recovered the optimal energy from one
scalar process. A new question now begins: can a finite construction
retain the correlations carrying that value, and can quantum gates
realise it? Section 7 handles the finite scalar object; Section 8 needs
additional operator theorems before it reaches a circuit.
<!-- /passage:scalar-identities -->

<!-- passage:finite-gaussian -->
## 7. From the diffusion to finitely many Gaussian inputs

The value formula uses an entire Brownian path. We now stop at a fixed
time $T<1$ and replace that path by finitely many Gaussian increments.
We scale the resulting random variables to have second moment one, then
use one further independent Gaussian to choose a final sign without
changing its expected products with earlier inputs. Products of these
correlation coefficients will approximate the optimum. Section 8 will
use this finite calculation to construct a circuit whose depth and angles
are chosen before the system-size limit.

We regard square-integrable random variables as vectors with inner product
$\langle g,h\rangle=\mathbb E[gh]$. A direction is normalised when
$\mathbb E g^2=1$; two directions are orthogonal when $\mathbb E[gh]=0$.
This lets us control all their correlations together using inner-product
estimates.

A one-step model shows what the correlations will measure. Take independent
standard Gaussians $Z_1,Z_2$, a cutoff $0<T<1$, the direction $g_1=Z_1$,
and the sign
$$
F_1=\operatorname{sgn}(\sqrt T Z_1+\sqrt{1-T}Z_2).
$$
Write $A_1=\mathbb E[F_1g_1]$ for its correlation with the direction,
and $D_j=\mathbb E[F_1Z_j]$ for its correlation with the $j$th input.
To calculate these, put $V=\sqrt T Z_1+\sqrt{1-T}Z_2$, a standard
Gaussian. The residual $Z_1-\sqrt T V$ is centred and independent of
$V$: the two are jointly Gaussian with zero covariance. Thus
$\mathbb E[Z_1\mid V]=\sqrt T V$ and
$A_1=D_1=\mathbb E[\operatorname{sgn}(V)Z_1]
=\sqrt T\,\mathbb E|V|=\sqrt{2T/\pi}$.
The same calculation gives $D_2=\sqrt{2(1-T)/\pi}$.
The adjacent product $A_1D_2$ pairs the
first direction with the next input, which performs the rounding.
At $T=4/5$ it is $4/(5\pi)$; pairing the same indices would instead
give $8/(5\pi)$. Section 7.1 derives this model from the coefficient
$\gamma=0$ and explains why it illustrates the indexing without
satisfying the minimiser hypothesis. We now construct the corresponding
directions and correlations for a minimiser and show why the sum of
adjacent correlation products approaches the optimum.

First fix the accuracy of the terminal cutoff. Since $a\ge0$ and
$\mathbb Ea^2=1$, Cauchy–Schwarz gives

$$
0\le P_*-\int_0^T\mathbb E[a(t,X_t)]\,dt\le1-T.
$$

For $0<\varepsilon<1$, choosing $T=1-\varepsilon/2$ leaves a
cutoff error at most $\varepsilon/2$. The remaining task is to choose
a sufficiently fine mesh for this fixed $T$.

With $N$ time
steps, $\Delta=T/N$ and $t_j=j\Delta$, define

$$
Y_0=0,\qquad
Y_j=Y_{j-1}+\sqrt\Delta Z_j
+\Delta\gamma(t_{j-1})u(t_{j-1},Y_{j-1}),
\quad 1\le j\le N,
$$

where the $Z_j$ are independent standard Gaussians. Here $N$ counts
time steps; it is not the number $n$ of spins. This discrete approximation, called an **Euler scheme**, uses a Gaussian
increment $\sqrt\Delta Z_j$ and freezes the drift at the beginning
of each step.

The exact diffusion satisfies $\mathbb E[a(t,X_t)^2]=1$, but
the discrete scheme need not satisfy this exactly. Normalize its directions:

$$
c_j=\bigl(\mathbb E[a(t_{j-1},Y_{j-1})^2]\bigr)^{-1/2},
\qquad g_j=c_j a(t_{j-1},Y_{j-1})Z_j.
$$

The source proves that these second moments are positive for all
sufficiently large $N$, at every step $1\le j\le N$, so each $c_j$
is defined.
$Y_{j-1}$ depends only on preceding Gaussian inputs, so its curvature
coefficient is independent of $Z_j$. Each $c_j$ is computed from the joint distribution of the inputs,
not by dividing by the curvature observed on one random path. Each $g_j$ consequently has mean
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
For every integrable function $V$ of those first $N$ inputs,
$\mathbb E[F_NV]=\mathbb E[u(T,Y_N)V]$. Thus rounding preserves
exactly the past correlations needed below. The tie event has probability
zero because the independent uniform variable has a continuous law. The extra rounding input $Z_{N+1}$ is
excluded from this conditioning.

Preserving conditional means does not remove the randomness of the spin.
Writing $m_N=u(T,Y_N)$, one has
$$
\mathbb E[(F_N-m_N)^2\mid Z_1,\ldots,Z_N]=1-m_N^2,
\qquad \|F_N-m_N\|_2^2\longrightarrow1-T.
$$
The last limit uses Euler convergence and $\mathbb E M_T^2=T$.
At fixed $T<1$ this error stays positive. The vanishing residual below
compares $m_N$ with an adapted sum, not $F_N$ with $m_N$.

Set $A_j=\mathbb E[F_Ng_j]$ for $1\le j\le N$, $A_0=0$, and
$D_i=\mathbb E[F_NZ_i]$ for $1\le i\le N+1$. We write $D_i$ for
the source's coefficient $B_i$ to distinguish it from Brownian motion.
The $A_j$ record the spin's correlations with normalized response
directions; the $D_i$ record its correlations with the original Gaussian
inputs. Section 8 will arrange these successive steps on a tree; neighbouring
outputs there will explain the pairing of adjacent indices. The source
theorem states

$$
\lim_{N\to\infty}\sum_{j=0}^N A_jD_{j+1}
=\int_0^T\mathbb E[a(t,X_t)]\,dt.
$$

For $N=2$, the sum before taking a limit is
$A_0D_1+A_1D_2+A_2D_3=A_1D_2+A_2D_3$.
Here $A_0=0$ and $D_3$ uses the extra rounding Gaussian.
The final term is the boundary contribution shown below to vanish as
$N\to\infty$. This finite case displays the index shift.

The vector estimates come from one mean-square approximation. Constructing the
Euler variables from the same Brownian increments as the continuous path,
the source proves

$$
S_N:=\sum_{j=1}^N\sqrt\Delta\,a(t_{j-1},Y_{j-1})Z_j,
\qquad \|u(T,Y_N)-S_N\|_2\longrightarrow0.
$$

Write this difference as $R_N$. The $g_j$ are an orthonormal family
and $S_N=\sum_j\sqrt\Delta\,g_j/c_j$. Rounding preserves their
correlations, so
$A_j-\sqrt\Delta/c_j=\mathbb E[R_Ng_j]$. Bessel's inequality gives
$\sum_j|\mathbb E[R_Ng_j]|^2\le\mathbb E R_N^2$.
The independent coordinates $Z_i$ form a second orthonormal family.
In $\mathbb E[S_NZ_i]$, earlier terms are independent of $Z_i$
and later terms have zero conditional mean; the matching term contributes
$\sqrt\Delta\,\mathbb E a(t_{i-1},Y_{i-1})$.
Applying Bessel again gives the second vector estimate. To see why
Bessel controls the whole error, subtract the component of $R_N$
in the span of the $g_j$:
$$
0\le\left\|R_N-\sum_j\mathbb E[R_Ng_j]g_j\right\|_2^2
=\|R_N\|_2^2-\sum_j|\mathbb E[R_Ng_j]|^2.
$$
The bound has no factor growing with the number of coordinates.
In particular,



$$
A_j\approx\frac{\sqrt\Delta}{c_j},\qquad
D_i\approx\sqrt\Delta\,\mathbb E[a(t_{i-1},Y_{i-1})]
\quad(1\le j,i\le N).
$$

Here approximation means that the Euclidean norm of each whole error
vector tends to zero. The approximating vectors have bounded norms,
so Cauchy–Schwarz controls the accumulated error in their scalar
product; small errors at each fixed index alone would not do this. For example,
a vector with $N$ entries all equal to $N^{-1/2}$ has entries tending
to zero but norm one, whereas entries $N^{-1}$ give norm $N^{-1/2}$.
Pairing $A_j$ with $D_{j+1}$ for $1\le j<N$ selects the mesh point
$t_j$, and $c_j\to1$ uniformly. For an explicit error bound, put $r_N=\|R_N\|_2$ and
$\alpha_j=\sqrt\Delta/c_j$. Bessel gives $\|A\|_2,\|D\|_2\le1$
and $\|\alpha\|_2\le1+r_N$. The interior pairing error is at most
$2r_N+r_N^2$, and the last term is bounded by
$|A_ND_{N+1}|\le r_N+\sqrt\Delta/c_N$. Consequently
$$
\left|\sum_{j=0}^NA_jD_{j+1}
-\Delta\sum_{j=1}^{N-1}\frac{\mathbb E a(t_j,Y_j)}{c_j}\right|
\le3r_N+r_N^2+\frac{\sqrt\Delta}{c_N}\longrightarrow0.
$$
What remains is the Riemann sum
$\Delta\sum_{j=1}^{N-1}\mathbb E[a(t_j,Y_j)]/c_j$, which converges
to the displayed integral by the source's Euler and regularity estimates.

For the chosen cutoff, take $N$ large enough that the finite sum
is within $\varepsilon/2$ of the integral. Its distance from $P_*$
is then at most $\varepsilon$. This proves an existence statement
with $T$ chosen before $N$; the cited convergence supplies no uniform
mesh rule at $T=1$. Equivalently, refine the fixed-$T$ approximation
and only then let $T\uparrow1$. These are scalar Gaussian
correlations, not the output of a finite-instance spin optimizer or a
QAOA circuit. Their full construction and proof are in the
[OpenAI (2026a), §7][support-consequences].

<!-- /passage:finite-gaussian -->

<!-- passage:gaussian-one-step-example -->
### 7.1 A one-step calculation, including the rounding coordinate

The rounding and index shift can be computed exactly for the non-minimising
candidate $\gamma=0$ with $N=1$. In that case $Y_1=\sqrt T Z_1$
and $g_1=Z_1$. Using the zero-candidate slope from Section 4.1, the
rounding formula is equivalent to

$$
F_1=\operatorname{sgn}\bigl(\sqrt T Z_1+\sqrt{1-T}Z_2\bigr).
$$

Indeed $F_{\mathrm G}(x)+F_{\mathrm G}(z)>1$ exactly when $x+z>0$.
The Gaussian expression inside the sign has variance one. Conditioning
on it, as in the calculation at the start of Section 7, gives

$$
A_1=D_1=\sqrt{\frac{2T}\pi},\qquad
D_2=\sqrt{\frac{2(1-T)}\pi},\qquad
A_1D_2=\frac2\pi\sqrt{T(1-T)}.
$$

At $T=1/2$ the adjacent product is $1/\pi$, but the same-index
product accidentally has the same value. To detect the index difference,
take $T=4/5$ instead:
$$
A_1D_2=\frac4{5\pi},\qquad A_1D_1=\frac8{5\pi}.
$$
Replacing the adjacent product $A_1D_2$ by the same-index product
$A_1D_1$ doubles the answer. Deleting the sole rounding boundary term
instead leaves zero.
The rounding coordinate is essential even at one step. This calculation
illustrates the construction outside the theorem's minimiser hypothesis;
it does not assert that its mesh limit is $P_*$. In fact at this
candidate the normalisers do not approach one, because $q_0'(t)\ne1$.
The normalisation hypothesis is what the general proof uses to recover
the first-moment integral.

The use of the slope martingale and a normalised Euler discretisation
follows [Montanari, §3.1, Lemmas 3.2–3.4][montanari] and
[El Alaoui–Montanari–Sellke, §§6.1–6.2][eams-meanfield]; the precise adjacent
coefficient identity here is the conclusion of
[OpenAI (2026a), Proposition 7.2][support-consequences].
<!-- /passage:gaussian-one-step-example -->

<!-- passage:qaoa-boundary -->
## 8. From scalar correlations to a quantum circuit

A state of this circuit is a complex vector with one coordinate $\psi_\sigma$
for each of the $2^n$ sign configurations and
$\sum_\sigma|\psi_\sigma|^2=1$. Its coordinates are called **amplitudes**.
Measuring the state returns configuration $\sigma$ with probability
$|\psi_\sigma|^2$. A quantum gate is a norm-preserving linear operation
on these vectors, and a circuit is a finite ordered sequence of gates.

The notation $|\psi\rangle$ means the column vector $\psi$, while
$\langle\psi|$ is its conjugate transpose. For one spin the basis vectors
are $|+1\rangle=(1,0)$ and $|-1\rangle=(0,1)$. In that basis the
three **Pauli matrices** are
$$
X^{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y^{\rm P}=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z^{\rm P}=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$
Thus $X^{\rm P}$ exchanges the two basis vectors; $Z^{\rm P}$
multiplies each by its sign; and $Y^{\rm P}$ exchanges them with factors
$i$ and $-i$. On $n$ spins, a subscript $i$ means action on the $i$th
spin and identity on the others.
We omit the superscript where no confusion is possible and restore it
when Gaussian coordinates $Z_j$ or the diffusion $X_t$ also appear.

The energy is represented by the diagonal matrix $C_{n,J}$ with entries
$H_n(\sigma)$, conventionally called the **cost operator** even though
we maximise its expectation. The matrix $B_n=\sum_iX_i$ generates the
mixing operations: each $X_i$ sends a basis vector $|\sigma\rangle$
to the configuration with only spin $i$ reversed.

The initial vector is $|+\rangle^{\otimes n}$, where
$|+\rangle=(1,1)/\sqrt2$. This is distinct from the basis vector
$|+1\rangle$. The tensor product multiplies the one-spin amplitudes,
so every configuration initially has amplitude $2^{-n/2}$ and probability
$2^{-n}$. The expected energy is the quadratic form
$\langle\psi|C_{n,J}|\psi\rangle$:

$$
\sum_\sigma |\psi_\sigma|^2 H_n(\sigma),
\qquad \sum_\sigma |\psi_\sigma|^2=1.
$$

The circuit uses two matrix exponentials, both norm-preserving. A **cost
rotation** $e^{-i\theta C_{n,J}}$ multiplies each amplitude by
$e^{-i\theta H_n(\sigma)}$, a complex factor of modulus one, or **phase**.
It therefore leaves measurement probabilities unchanged. A **mixer
rotation** $e^{-i\beta B_n}$ combines amplitudes. For one spin,
$X^2=I$ gives $e^{-i\beta X}=\cos\beta\,I-i\sin\beta\,X$;
combined amplitudes can reinforce or cancel and change probabilities.

A depth-$p$ QAOA circuit consists of $p$ cost–mixer pairs. Its real
parameters $\theta_j,\beta_j$, called angles, set the operations in each
pair. The rightmost operation is performed first:

$$
|\psi_{n,p,J}(\boldsymbol\theta,\boldsymbol\beta)\rangle
=e^{-i\beta_pB_n}e^{-i\theta_pC_{n,J}}\cdots
e^{-i\beta_1B_n}e^{-i\theta_1C_{n,J}}|+\rangle^{\otimes n}.
$$

The cost angles are written $\boldsymbol\theta$ here to distinguish
them from the function $\gamma(t)$ in the Parisi problem; the QAOA
manuscript writes these angles as $\boldsymbol\gamma$.

### 8.1 Two spins: converting phase into probability

Return to the two-spin reward and put $h=J/\sqrt2$. A single cost
rotation gives amplitudes $e^{-i\theta h}/2$ to aligned configurations
and $e^{i\theta h}/2$ to antialigned ones. All four probabilities
are still $1/4$. After applying the two commuting one-spin mixers,
where each mixer is $e^{-i\beta X}$, the amplitude of either aligned
configuration becomes

$$
\frac12\left(\cos(2\beta)e^{-i\theta h}
             -i\sin(2\beta)e^{i\theta h}\right).
$$

Each aligned probability is consequently
$[1+\sin(4\beta)\sin(2\theta h)]/4$, and each antialigned one is
$[1-\sin(4\beta)\sin(2\theta h)]/4$. The mean reward per spin is

$$
\frac12\langle C\rangle
=\frac h2\sin(4\beta)\sin(2\theta h).
$$

Both gates are needed. Cost alone preserves the probabilities; mixer
alone acts on the initial plus state only by a common phase. Reversing
the two gates therefore also leaves the probabilities uniform.
For nonzero $h$, the instance-dependent choices $\beta=\pi/8$ and
$\theta=\pi/(4|h|)$ put all probability on the optimal sign of the
pair. But a deterministic angle must be chosen before $J$ is observed.
Since $\mathbb E\cos(2\theta h)=e^{-\theta^2}$, differentiating gives
$\mathbb E[h\sin(2\theta h)]=\theta e^{-\theta^2}$, and hence

$$
\frac12\mathbb E_J\langle C\rangle
=\frac\theta2e^{-\theta^2}\sin(4\beta)
\le\frac1{2\sqrt{2e}}.
$$

Equality is achieved at $\theta=1/\sqrt2$, $\beta=\pi/8$.
This best deterministic one-layer value is smaller than the expected
instance optimum $1/(2\sqrt\pi)$. The distinction is between choosing angles before and after seeing $J$.
This two-spin calculation gives no large-system convergence estimate.

### 8.2 Choosing one circuit before taking the size limit

For each fixed depth and deterministic choice of real angles, first take
the large-system limit of the expected energy per spin, where the
expectation is over the Gaussian couplings $J$:

$$
v_p(\boldsymbol\theta,\boldsymbol\beta)
=\lim_{n\to\infty}\frac1n\mathbb E
\langle\psi_{n,p,J}|C_{n,J}|\psi_{n,p,J}\rangle,
\qquad Q_p=\sup_{\boldsymbol\theta,\boldsymbol\beta}v_p.
$$

The fixed-depth, fixed-angle limit is an earlier result of
[Farhi, Goldstone, Gutmann and Zhou, §4][fggz]. Their first- and
second-moment limits also give concentration of the measured energy per
spin. This identifies a performance function for fixed parameters, not its
limit as depth grows. [Basso, Farhi, Marwaha, Villalonga and Zhou,
full preprint §7, equation (7.2)][bfmvz] conjectured that increasing depth
would reach the optimum in this order of limits. The separate theorem of
[OpenAI (2026b), Theorem 1.1][qaoa-theorem] states
$\lim_{p\to\infty}Q_p=P_*$. Its quantifiers are worth spelling out:
for each desired error $\varepsilon>0$, choose a finite depth and one
deterministic angle vector, independent of both $n$ and the couplings
$J$, whose limiting expected energy is at least $P_*-\varepsilon$.
The chosen depth and angles may depend on $\varepsilon$.

The order matters even for the elementary array $f_p(n)=p/(p+n)$:
for each fixed $n$ it tends to one as $p$ grows, but for each fixed $p$
it tends to zero as $n$ grows. Section 8.8 works out the required depth
for this example. Thus a circuit chosen separately for each finite size
would not answer the stated question.

Two elementary observations explain what remains to be constructed.
Measurement of any state gives a probability distribution on classical
configurations, so its energy expectation is at most
$\max_\sigma H_n(\sigma)$. Thus $Q_p\le P_*$. Appending a layer with
zero angles changes no state, so $Q_{p+1}\ge Q_p$. These upper-bound
and monotonicity facts do not supply the required lower bound near
$P_*$.

The proof next uses an auxiliary tree: a graph with no cycles, with
$D+1$ neighbours at every vertex. Calculations use only finitely many
levels around a chosen vertex. Summing independent branch outputs with
a $D^{-1/2}$ factor produces Gaussian variables as $D$ grows. The manuscript constructs a common space for
these coordinates and the limiting quantum operations. Its operator
estimates are additional source results, not consequences of the two
selected formal support and scalar statements.

<!-- /passage:qaoa-boundary -->

<!-- passage:rooted-energy -->
### 8.3 Why the adjacent coefficient sum is an energy

Section 7 gave a sum of scalar correlation products. On the auxiliary
tree, the energy is a scaled expected product of the outputs at the
ends of an edge. The source arranges the scalar calculations on this
tree and proves that the two expressions agree. Matching the separate distributions at individual sites would
not establish this relation: the neighbouring outputs must be constructed
together. This is the purpose of the common space and the operation that
moves a calculation from a child to its parent below.

A **root** is the vertex where we read an output. In a calculation sent
towards a parent along one edge, the other $D$ neighbours are its
**children**. Each vertex has an independent auxiliary random input,
called its **seed**. An output depends on this seed and on sums of
outputs computed farther down the tree. If $f$ is the rule at a child,
the parent receives the normalised sum
$D^{-1/2}\sum_{k=1}^D f_k$, where the $f_k$ use independent
child subtrees. The limiting construction starts with centred,
square-integrable $f$: $\mathbb E f=0$ and $\mathbb E f^2<\infty$.
It associates to each such child calculation a Gaussian coordinate
$\mathsf G(f)$, with the joint covariance rule

$$
\mathbb E[\mathsf G(f)\mathsf G(g)]=\langle f,g\rangle
=\mathbb E[fg].
$$

The receiving parent's own seed is independent of all these coordinates.
Orthonormal child calculations therefore give independent standard
Gaussian coordinates. Independence follows from their joint Gaussian
law; it would not follow from orthogonality of arbitrary random variables.

The number of descendant levels read by a calculation is its **height**.
Adding unused levels lets the source compare calculations of different
heights in one Hilbert space, a complete inner-product space. Write
$\Omega$ for its initial vector. Real random functions are represented
there by $f\Omega$, with inner product $\mathbb E[fg]$, while every
quantum spin remains in $|+\rangle$. This is the **classical subspace**.
The larger complex space also allows quantum gates to change the spins. Constructing that space and
proving the finite-degree limits are additional source results. This
representation is related to [Boulebnane and coauthors' fixed-depth
spin–boson mapping, Theorem 2 and Supplement VI.B][spin-boson]. The
additional bounds needed to preserve energy while gates are composed
are proved in the QAOA source.

A vector is **centred** when it is orthogonal to $\Omega$; for a
classical function this means $\mathbb Ef=0$. The source defines a
linear map $\mathsf L$ on these vectors by adding a new root in its
initial state and placing the old vector one level below it. The child
component is symmetric under permutation of children and has one factor
orthogonal to its initial state. The map preserves norm,
$\|\mathsf Lf\|=\|f\|$, so it is an **isometry**.

In the classical subspace, $\mathsf G(f)\Omega=\mathsf Lf$.
This identifies the Gaussian construction and the root shift in the same
space, including their dependence on one another. The energy functional is

$$
\mathcal E(v)=\operatorname{Re}\langle v,\mathsf Lv\rangle.
$$

For real classical vectors the real part is unnecessary. The source's
root-shift proposition identifies this expression with a scaled edge
correlation for convergent finite-tree calculations. Its hypotheses
include invariance under permutations of entire child subtrees, convergence
in norm at fixed height, and a uniform bound on expected **occupation**.
To define the last quantity, decompose a vector according to which child
factors are orthogonal to their initial states. The occupation operator
weights each component by the number of these factors. An expectation
bounded by $C$ makes the finite-edge remainder at most $C/(D+1)$.
After multiplication by $\sqrt D/2$, it still vanishes. Norm convergence
alone gives no such bound on the scaled error. The later gate estimates supply this additional control for the
circuits used below. [OpenAI (2026b), §§2.1–2.3][qaoa-foundations]

To use the adjoint on the whole space, extend $\mathsf L$ by sending
the initial vector to zero. The adjoint is defined by
$\langle f,\mathsf Lg\rangle=\langle\mathsf L^*f,g\rangle$.
For an orthonormal family $e_1,\ldots,e_k$ of real centred child vectors,
and a function $F$ of their Gaussian coordinates alone, it has the
concrete formula

$$
\mathsf L^*F
=\sum_{j=1}^k\mathbb E[F\mathsf G(e_j)]e_j.
$$

Indeed, $\mathsf L^*$ retains the component linear in these Gaussian
coordinates, with no dependence on the receiving root's seed. Constants
and components orthogonal to the linear coordinates disappear. It first projects onto the span of those Gaussian coordinates, then
moves the retained child vector back up one level.

For a concrete instance, reuse Section 7's one-step sign for the
non-minimising candidate $\gamma=0$. Let $g_0$ be the function that reads
a site's own standard Gaussian seed. The same rule can be evaluated at
any site: $g_0$ at the receiving root reads its own seed, whereas
$\mathsf G(g_0)$ aggregates the seeds read at its children. Those children
use independent seeds, so the aggregate is independent of the receiving
root's seed. Use the compatible height embeddings to put successive
child calculations in the same recursive space. Let
$Z_1=\mathsf G(g_0)$ and $g_1=Z_1$,
and let $Z_2=\mathsf G(g_1)$. The directions $g_0,g_1$ are orthonormal,
so $Z_1,Z_2$ are independent standard Gaussians. For
$F_1=\operatorname{sgn}(\sqrt T Z_1+\sqrt{1-T}Z_2)$ the adjoint gives
$$
\mathsf L^*F_1=D_1g_0+D_2g_1,\qquad
\mathcal E(F_1)=D_1\langle F_1,g_0\rangle
                 +D_2\langle F_1,g_1\rangle=A_1D_2.
$$
The first inner product vanishes because $F_1$ is independent of the
receiving root's seed. The second is exactly $A_1$. At $T=4/5$ the
energy is therefore $4/(5\pi)$: moving up one level creates the adjacent
index already seen in the finite Gaussian calculation.

Now take the local Gaussian seed as $g_0$ and recursively set
$Z_{j+1}=\mathsf G(g_j)$, using the normalised directions $g_j$ from
Section 7. At each stage the new direction is centred, has norm one,
and is orthogonal to the earlier directions: its new Gaussian factor
is independent of its coefficient and has mean zero. The compatible
height embeddings preserve the previously constructed coordinates.
Consequently this recursive realization has the independent Gaussian
law used in Section 7. Its output $F_N$ is centred by sign symmetry and
is a function of $Z_1,\ldots,Z_{N+1}$ alone. Hence

$$
\mathsf L^*F_N=\sum_{j=0}^N D_{j+1}g_j,
\qquad
\mathcal E(F_N)=\sum_{j=0}^N A_jD_{j+1},
$$

where $A_0:=\langle F_N,g_0\rangle=0$ because the receiving root's
seed is independent of $F_N$. For $j\ge1$ the inner products are exactly
the $A_j$ of Section 7. Taking the inner product with $F_N$ proves the
second identity. The adjacent index now records a parent–child
relation. The scalar calculation therefore supplies a bounded output
in the limiting classical space with energy arbitrarily close to
$P_*$. This conclusion precedes the further approximation and gate
construction. [OpenAI (2026b), §3.2][qaoa-classical]

<!-- /passage:rooted-energy -->

<!-- passage:circuit-synthesis -->
### 8.4 Making the classical calculation available to gates

The next task is to turn a bounded real output $m$ into gates with the
same energy. After a circuit $U$, the root sign is represented by the
operator $U^*Z_{\mathrm{root}}^{\mathrm P}U$, where $U^*$ is the
adjoint. Applied to the initial vector $\Omega$, it gives the vector
$v=U^*Z_{\mathrm{root}}^{\mathrm P}U\Omega$, called an **insertion**.
The gate $e^{i\theta Y^{\mathrm P}}$ will encode $m=\sin(2\theta)$.
We first approximate the classical output by one this gate can represent,
then check that the resulting insertion has the same energy.

The raw calculation uses a discontinuous sign. The intermediate values passed from children
to parents can also be unbounded.
Write $H_N=u(T,Y_N)+2F_{\mathrm G}(Z_{N+1})-1$ for the argument
of the sign defining $F_N$ in Section 7. At fixed $T$ and $N$, replacing $\operatorname{sgn}(H_N)$ by
$\tanh(kH_N)$ gives convergence in mean square, since
$\Pr(H_N=0)=0$. The isometry property of $\mathsf L$ gives

$$
|\mathcal E(v)-\mathcal E(w)|
\le(\|v\|+\|w\|)\|v-w\|,
$$

so this approximation preserves energy. Smooth truncations and finite
expressions built from finitely many sines and cosines then make every
transmitted value bounded
and put the output in the form $m=\sin(2\theta)$ with bounded smooth $\theta$ that changes sign when all its inputs
change sign. Such a function is called **odd**. The Gaussian aggregate inputs themselves need not be bounded.
Work backwards through the formula: first bound how much an outer
function can amplify an input error, then approximate its inputs to the
required accuracy.

A further modification makes each descendant calculation usable by
operations defined without a chosen root. The source assigns random
labels, called **types**, using the local seeds while preserving the
independent Gaussian inputs and their sign symmetry. Some labels reserve
vertices for temporary control operations; these are the **helper types**. An aggregate
excludes the current site's type, every ancestor type on its active
branch, and all reserved helper types. For example, when a value is passed along an edge from type $c$ to
type $d$, the calculation at the second endpoint excludes type $c$. Its sum over all neighbours therefore omits the first
endpoint, exactly as a descendant sum should. This prevents the calculation from feeding its own input back along
the same edge. The reserved types also separate vertices used to control
a gate from vertices on which it acts.
It does not assert that formulas sharing descendants are independent.
For a fixed bounded formula, the squared norm error is at most
$C(\alpha+p_H)$, where $\alpha$ is the largest nonhelper type probability
and $p_H$ is the total helper probability. These probabilities can be
chosen small. [OpenAI (2026b), §§3.3–3.5][qaoa-classical]

More precisely, take $\Omega$ to be the initial plus state, together
with the seed variables when present. The root observable has insertion
vector

$$
v=U^*Z_{\mathrm{root}}^{\mathrm P}U\Omega.
$$

The inner product of the insertions at two endpoints gives that edge's
$Z^{\mathrm P}Z^{\mathrm P}$ expectation: the intervening $UU^*=I$
cancels. The vectors used here
are centred by the joint spin and seed sign symmetry and have norm one.
The root-shift theorem therefore connects their limiting edge energy to
the same $\mathcal E(v)$ used for classical calculations, once the gate
convergence and occupation bounds have been proved.

Evaluate the angle function at each vertex to obtain $\theta_i$.
The desired gates, which still depend on the auxiliary seeds, are
$U_{\mathrm{cl}}=\prod_i e^{i\theta_iY_i^{\mathrm P}}$.
Writing $| -\rangle=(1,-1)/\sqrt2$ for the other eigenvector of
$X^{\mathrm P}$, the root insertion is

$$
v_{\mathrm{cl}}
=|+\rangle\sin(2\theta)+|-\rangle\cos(2\theta).
$$

The second term contributes zero to $\mathcal E(v_{\mathrm{cl}})$:
$\mathsf L$ puts the new root in $|+\rangle$, and shifting a
$|-\rangle$ spin to a child is orthogonal to the classical sector.
Thus $\mathcal E(v_{\mathrm{cl}})=\mathcal E(m)$. This calculation
explains why the classical output is the correct synthesis target.
[OpenAI (2026b), §2.2][qaoa-foundations]

To isolate an interaction, the gate-construction proof combines spin
flips applied only to selected types. The resulting sign changes cancel
unwanted interactions and retain the required ones. This is the selective refocusing method
of [Jones and Knill (1999), §II][jones-knill]; the QAOA source adapts it
to its type masks and controls the approximation inside a surrounding circuit.

The **synthesis theorem** constructs this approximation using cost and mixer gates
plus temporary controls
$\exp(-i\rho\sum_i s_iZ_i^{\mathrm P})$ with a real parameter
$\rho$. The $s_i$ are independent standard Gaussians, and the same seed family
is reused at every seed gate. For a finite bounded odd formula with the
type exclusions above, and disjoint unused helper types of positive probability reserved for each level of the formula that sums child values, and any requested error $\eta>0$, it produces a finite seeded circuit with
root insertion $v$ satisfying

$$
\|\mathbf1_{H^c}(v-v_{\mathrm{cl}})\|<\eta,
\qquad
|\mathcal E(v)-\mathcal E(m)|\le2\eta+2\sqrt{p_H}.
$$

Here $H$ is the event that the root's type belongs to one of the classes
reserved for temporary controls. The desired classical output is set to
zero on those sites, and $p_H=\Pr(H)$. The two terms have separate meanings: $2\eta$ bounds the
error away from helpers, while omitting the helper part of a unit-norm
insertion costs at most $2\sqrt{p_H}$. The theorem supplies convergence
even when the approximating operation is placed among other fixed gates.
It also supplies the occupation bounds required for the energy limit.
Thus the claim controls composition and energy, as well as the output
vector itself.
[OpenAI (2026b), §4, Classical synthesis theorem][qaoa-synthesis]

Reusing the same seed is necessary even for one spin. The gates
$e^{i\rho sZ}$ and $e^{-i\rho sZ}$ cancel exactly. If the second
uses an independent standard Gaussian $s'$, their product has phase
$\rho(s-s')$. On the plus state its expected $X$ measurement is
$\mathbb E\cos(2\rho(s-s'))=e^{-4\rho^2}$ instead of one.
Equal one-gate distributions therefore do not preserve a sequence of
correlated gates.

<!-- /passage:circuit-synthesis -->

<!-- passage:seed-removal -->
### 8.4.1 Removing the temporary random controls

The circuit still uses operations depending on extra random seeds; QAOA
allows only the original cost and mixer operations. The next source theorem
replaces an entire fixed sequence of seed-dependent operations while
preserving the correlations created by reusing the same seeds. Replacing
each operation independently would fail even the one-spin cancellation
test above.

The construction uses a small parameter $r>0$. It prepares a part of
the state with amplitude proportional to $r$ and selectively changes it.
A sequence containing cost evolution and its reverse, with durations of
order $1/r$, amplifies that small change into the required finite phase
rotation. The errors therefore have to vanish faster than $r$, not merely
tend to zero. The selective-control method builds on
[Li and Khaneja (2005), §II, Examples 1–2][li-khaneja]; the finite gate
construction and cancellation estimates are proved in the QAOA source.

More precisely, if $v_r$ and $v'_r$ are the insertion vectors before and
after the selective change, the source constructs a bounded vector $w_r$
such that $v'_r-v_r=-2rw_r+o(r)$. The notation $o(r)$ means an error
whose norm divided by $r$ tends to zero. For example, errors $r^2$, $r$ and
$\sqrt r$ all tend to zero, but division by $r$ sends them respectively
to zero, one and infinity. The estimate must compare the actual selected
direction $w_r$ on both sides; replacing it by a limiting direction with
only $o(1)$ accuracy could destroy the cancellation. The proof keeps the same Gaussian input
through successive simulated seed gates and separately controls the root
energy. It fixes the target gate sequence, an initialisation parameter,
a small angle perturbation and finite lists of operations before taking
$r$ sufficiently small. Every final angle is finite, though some may be large.
[OpenAI (2026b), §5, Removal of seed controls theorem][qaoa-seeds]

<!-- /passage:seed-removal -->

<!-- passage:fixed-word-transfer -->
### 8.5 The final transfer and error choices

Let $W$ be the fixed finite sequence of cost and mixer gates just
constructed, with all its angles fixed. Such a sequence is also called a
word. Write $v_W$ for its limiting SK energy $v_p$ from Section 8.2.
To compare it with the auxiliary tree, apply the same sequence and angles
using the tree's cost operator and mixer; call the resulting operation
$W_D$ on a tree of degree $D+1$. For adjacent vertices $i,j$, the source's
transfer identity is

$$
v_W=\lim_{D\to\infty}\frac{\sqrt D}{2}
\langle W_D\Omega,Z_iZ_jW_D\Omega\rangle,
$$

where $\Omega$ is the all-plus input, the tree mixer is $\sum_iX_i$,
and the positive tree cost is
$D^{-1/2}\sum_{\{i,j\}}Z_iZ_j$, counting each edge once. These are
Pauli operators on tree sites. A finite sequence around the chosen edge
uses only finitely many neighbouring generations.
The source derives its convention from
[Basso and coauthors, full preprint Theorem 1][bfmvz], with the opposite
cost sign by flipping spins at every even-distance level of the tree. This reverses each
edge product, preserves the plus input and commutes with the mixer.
The identity concerns a word whose depth and angles are already fixed;
it asserts no joint limit in size, degree and depth.
[OpenAI (2026b), §2.1, Fixed-word transfer proposition][qaoa-foundations]

For a requested error $\varepsilon$, the classical near-optimality
proposition chooses the formula and its helper probabilities together:
the classical energy is within $\varepsilon/4$ of $P_*$ and
$0<p_H<(\varepsilon/8)^2$. In that construction the formula without
types is fixed first; then small positive helper probabilities and the
approximation excluding those types are chosen. One cannot silently
change the helper law of an already fixed formula. Now set synthesis
accuracy $\eta=\varepsilon/8$ and require seed-removal error below
$\varepsilon/4$. Since $2\sqrt{p_H}<\varepsilon/4$,
adding the four losses gives one ordinary word with value above
$P_*-\varepsilon$. Consecutive gates of the same kind can be merged,
and zero-angle gates put it in alternating QAOA form. This lower bound,
together with $Q_p\le P_*$ and monotonicity, proves the source's
stated conclusion with system size tending to infinity before depth. [OpenAI (2026b), §6][qaoa-assembly]

The order is $n\to\infty$ at fixed parameters, followed by increasing
$p$. No interchange or specified joint schedule $p=p(n)$ has been used.
The 25 September manuscript supplies no quantitative finite-size estimate
for its constructed words, depth bound, or efficient angle-selection
procedure. Here depth counts cost–mixer pairs; implementing one cost operation
for all pairs of spins may require many elementary gates. Neither selected formal scalar
statement mentions the circuit state or asserts convergence of its energy.

<!-- /passage:fixed-word-transfer -->

<!-- passage:measured-energy -->
### 8.5.1 From expected energy to a measured spin configuration

A large expected energy alone is not a guarantee about a sampled output.
Let $Y_n=H_n(\sigma)/n$, where $J$ is sampled first and $\sigma$ is
then measured from the fixed QAOA state. For each fixed depth and angle
vector, [Farhi–Goldstone–Gutmann–Zhou, §4, equations (13)–(14)][fggz]
prove
$$
\mathbb E Y_n\longrightarrow v,\qquad
\mathbb E Y_n^2\longrightarrow v^2.
$$
The second quantity is the expectation of the squared measured energy,
$\mathbb E_J\langle\psi|(C_{n,J}/n)^2|\psi\rangle$.
It is not merely the square of the conditional mean for each instance:
a fair random sign has conditional mean zero but second moment one.

Choose the word above with limiting value $v\ge P_*-\varepsilon/2$.
The two moment limits give $\mathbb E(Y_n-v)^2\to0$, and hence
$$
\Pr\{Y_n<P_*-\varepsilon\}
\le\frac4{\varepsilon^2}\mathbb E(Y_n-v)^2\longrightarrow0.
$$
This probability averages over both the random couplings and the
configuration sampled from the quantum state.
It also has a typical-instance interpretation. If $b_n(J)$ is the
conditional probability of failure on instance $J$, then
$\mathbb E_Jb_n(J)\to0$. For every fixed $\tau>0$,
$\Pr_J\{b_n(J)>\tau\}\le\mathbb E_Jb_n(J)/\tau\to0$.
Thus most sufficiently large instances have small measurement-failure
probability. Neither argument supplies a finite-size rate, an
every-instance guarantee, or a result for arbitrary growing depth.

<!-- /passage:measured-energy -->

<!-- passage:classical-algorithm -->
### 8.6 A distinct classical optimisation consequence

The same scalar construction also informs a classical algorithm acting
directly on a finite spin instance. To state its cost, extend the quadratic
formula for $H_n$ from sign vectors to real vectors. Its gradient, the vector of first partial derivatives, is obtained by
multiplying by the coupling matrix scaled by $1/\sqrt n$: computing every coordinate costs $O(n^2)$
arithmetic operations, and computing one coordinate costs $O(n)$.

Full support makes the admissible minimiser strictly increasing, verifying
[El Alaoui, Montanari and Sellke's Assumption 2][eams-meanfield]. Their
Corollary 2.2 then gives near-optimality. The operation count comes from
the displayed Theorem 3 on page 7 of that preprint, which the corollary
calls Theorem 3.2: $C(\varepsilon)(\chi+n)+n\chi_1$, where $\chi$
is the cost of a full gradient and $\chi_1$ that of one gradient coordinate.
With the two costs just described, in the source's real-arithmetic model,
for every fixed $\varepsilon>0$ there is
a randomised algorithm using at most $C(\varepsilon)n^2$ operations
and returning $\sigma^{\rm alg}$ with

$$
\Pr\{H_n(\sigma^{\rm alg})\ge\max_\sigma H_n(\sigma)-\varepsilon n\}
\longrightarrow1.
$$

The probability includes the couplings and the algorithm's randomness.
Real sums and products have unit cost, and the scalar functions and
normalisations prescribed for the chosen accuracy are available. This
instance-size bound does not supply a preprocessing or finite-precision
complexity bound. This algorithm returns signs for a supplied finite list of couplings.
Section 7 instead constructs Gaussian functions, and Section 8 builds gates.
[OpenAI (2026a), Corollary 7.3 and its EAMS attribution][support-algorithm]

<!-- /passage:classical-algorithm -->

<!-- passage:positive-temperature-route -->
### 8.7 An alternative finite-temperature starting point

The previous construction began with an exact zero-temperature minimiser.
The QAOA manuscript also reaches a near-optimal classical energy by starting
with the smooth approximation to a maximum from Section 1. This is its
independent positive-temperature route. It fixes a large finite inverse
temperature $\beta_0>1$, then a cutoff
$0<T<q_{\beta_0}$, the largest support point of the finite-temperature
Parisi probability measure, and then finitely many steps in which each vertex updates values sent to
its neighbours.
Its terminal function is $\beta_0^{-1}\log(2\cosh(\beta_0x))$.
[Talagrand (2006), Theorem 1.1][talagrand] supplies the positive-temperature
Parisi formula for the soft-maximum value per spin, called the **free
energy**, in these rescaled coordinates. The **partition function** is
the unnormalised exponential sum over all $2^n$ configurations;
its soft-maximum error contributes the $\log2/\beta_0$ term below.
Using the finite-temperature support theorem and separate tree estimates,
the source obtains a classical energy integral with loss bounded by

$$
\frac{1/4+\log2}{\beta_0}+(q_{\beta_0}-T).
$$

The finite-temperature support input is [Lopatto, version 3][lopatto-support].
The message-passing construction uses [Montanari, §3.1, Lemmas 3.2–3.3][montanari]
and the [El Alaoui–Montanari–Sellke framework, Assumption 1 and Theorem 2][eams-meanfield].
Their [separate regular-graph paper, version 2][eams-graphs] supplies the
finite-tree antecedent. The QAOA source reconstructs the indexed calculation;
the long record §9.7 distinguishes that argument from an incorrect weighted
finite-degree formula printed in the graph paper.
After this alternative classical construction, bounded approximation,
synthesis, seed removal and fixed-word transfer proceed as above.
This argument does not obtain zero-temperature full support by taking a
limit of supports. It has different initial hypotheses and approximation
parameters and meets the first route only at a bounded classical formula.
[OpenAI (2026b), Appendix A][qaoa-positive]
<!-- /passage:positive-temperature-route -->

<!-- passage:limit-order-example -->
### 8.8 A depth that works at each size need not survive the size limit

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
2. In the area model, replace $\kappa=1$ by $\kappa=1/2$, and then
   by $\kappa=0$. What is the deficit in each case? Which change
   removes the contradiction?
3. In the toy array, choose $p=n$. Does the resulting limit equal either
   iterated limit? What changes if $p=n^2$?
4. Does infinite support, together with absence of a final plateau,
   suffice for full support? Does a positive initial cumulative value?
5. Does ending in a terminal spin $U\in\{-1,1\}$ establish that the
   coefficient minimises the Parisi functional?
6. May the finite-Gaussian construction set $T=1$ before refining its
   time mesh? Would near-optimal circuit angles chosen separately for
   each draw of the couplings establish the stated QAOA claim?

7. Can a sequence of finite staircases approach the Parisi minimum despite
   every staircase having a gap? Does full support with smooth positive
   density suffice to prove minimisation?
8. In the adapted-sum example, replace the coefficient of $Z_2$ by
   $Z_2$ itself. What fails? Does $\mathbb E M_t^2=t$ imply that
   the martingale $M$ is Brownian motion?
9. In the two-spin circuit, reverse cost and mixer. What is the expected
   reward? Does an angle depending on $|J|$ meet the deterministic-angle
   quantifier of the large-system theorem?
10. If $\lambda_n=\log(n+1)$, does the finite-temperature free energy
    per spin approach $P_*$? Can the same reasoning justify $p(n)=\log(n+1)$
    for the circuit depth?


11. In a calculus model on $[2,5]$, suppose $f(2)=2$, $f(5)=5$,
    $f'(2)=1/2$ and $f'(5)=3/2$. Can $f'$ be strictly convex?
    Does your argument require $f'<1$ everywhere?
12. Modify the admissible class by requiring total Stieltjes mass one.
    If an atom at $r$ can donate mass to $s$, what variation replaces
    atom addition, and what inequality does minimality give?
13. At fixed $T<1$, can the rounded spin converge in mean square to
    its conditional mean? Which residual actually vanishes in Section 7?
14. A circuit has nearly constant conditional expected energy across draws
    of the couplings.
    Does this alone control a measurement? Which additional moment does
    Section 8.5.1 use?

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
At $\kappa=0$, $q_\kappa'=1$ and both endpoint contacts are
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


**7. Approximation and optimality.** Admissible staircase approximations
converge in $L^1$ to a minimiser, and the stability bound in Section 5.5
makes their objective values converge to its value. None need be an exact
minimiser. Conversely $\gamma(t)=12t$ has smooth positive density and
full support but value at least one, exceeding the zero candidate's value.
Neither support nor smoothness supplies a sufficient optimality test.

**8. Predictability and second moments.** The new term is $Z_2^2$ and
has mean one, so conditional centring and the martingale calculation
fail. In the actual construction, $M$ is bounded by one; Brownian motion at any positive time has positive probability outside
$[-1,1]$. Equal second moments therefore do not
identify these processes.

**9. Gate order and the instance.** A mixer acts on the initial plus
state by a common phase, and the subsequent cost gate preserves all
probabilities. The mean reward is zero for each two-spin instance.
The angle $\pi/(4|J|/\sqrt2)$ works at that instance but depends on
its coupling, so it is not the deterministic angle required in Section 8.2.

**10. A uniform bound is the difference.** Since $\log(n+1)\to\infty$,
the soft-maximum error per spin is at most
$\log2/\log(n+1)\to0$. The ground-state convergence therefore gives
the scalar limit. The circuit theorem has no analogous uniform estimate
for that schedule, so this argument makes no conclusion about it.


**11. A nonhorizontal chord.** The chord joining $1/2$ and $3/2$ has
average height one and integral three. Strict convexity puts $f'$ below
it in the interior, so $f(5)-f(2)=\int_2^5f'<3$, a contradiction.
The pointwise bound $f'<1$ is unnecessary. Without strictness,
$f(t)=2+(t-2)/2+(t-2)^2/6$ satisfies all endpoint data and has affine
derivative. This is a calculus model, not an asserted SK moment function.

**12. A different feasible set.** Move mass by
$\varepsilon(\delta_s-\delta_r)$ with
$0<\varepsilon\le\mu(\{r\})$. Its cumulative direction is
$\mathbf1_{[s,1)}-\mathbf1_{[r,1)}$, with derivative
$[G(s)-G(r)]/2\ge0$. Adding a lone atom violates the new constraint,
so this argument does not infer $G(s)\ge0$. The original SK admissible
class has no mass-one constraint; its earlier proof is unchanged.

**13. Rounding keeps noise.** The exact error is
$\|F_N-m_N\|_2^2=1-\mathbb E m_N^2\to1-T>0$.
The source proves $\|m_N-S_N\|_2\to0$. Conditioning removes the
rounding noise from the correlations with earlier inputs, allowing Bessel's
inequality to use the latter residual. The remaining rounding variance
vanishes only when the cutoff later tends to one.

**14. A second moment of the output.** An independent fair sign has
conditional mean zero on every instance but never concentrates at zero.
One needs the source's limit of
$\mathbb E_J\langle\psi|(C_{n,J}/n)^2|\psi\rangle$, not just
concentration of $\langle\psi|C_{n,J}/n|\psi\rangle$. Together with
the first moment it controls the actual measured energy by the displayed
mean-square bound.

<!-- /passage:changed-cases -->

<!-- passage:analytic-notes -->
## 10. Supporting calculations

The preceding argument identifies the operations before their full
derivations. These notes supply the computations used at those points.

### 10.1 Evaluating a finite staircase

One can evaluate a finite step candidate backwards, one interval at a time.
Suppose $\gamma=c$ on $[t,b)$ and the continuation value at $b$ is
$h(x)=\Phi_\gamma(b,x)$. Then

$$
\Phi_\gamma(t,x)=
\begin{cases}
 c^{-1}\log\mathbb E e^{c h(x+\sqrt{b-t}Z)},&c>0,\\
 \mathbb E h(x+\sqrt{b-t}Z),&c=0.
\end{cases}
$$

Starting with $h(x)=|x|$ at one gives a finite recursion of Gaussian
integrals. If the successive heights are $c_j$ on $[t_{j-1},t_j)$,
the penalty is $\sum_j c_j(t_j^2-t_{j-1}^2)/4$. This describes an
actual candidate calculation, not an optimisation over all candidates.
To derive the recursion from Section 3.3, set $H=e^{c\Phi}$ when
$c>0$. Then $H_t=cH\Phi_t$ and
$H_{xx}=cH\Phi_{xx}+c^2H\Phi_x^2$, so the PDE gives
$H_t=-H_{xx}/2$. The Gaussian formula for this equation, followed by a logarithm, gives
the positive-height recursion. When $c=0$, the same equation holds for
$\Phi$ itself and gives the second case.

### 10.2 The positive-temperature convention

At positive inverse temperature $\lambda$, the variational order parameter
is a cumulative probability function $m$. In energy units its coefficient
is $\lambda m$, and its terminal value is
$\lambda^{-1}\log(2\cosh(\lambda x))$. The inequality

$$
0\le\lambda^{-1}\log(2\cosh(\lambda x))-|x|
\le\frac{\log2}{\lambda}
$$

explains the terminal absolute value in the zero-temperature problem.
The scaled cumulative function need no longer have total mass one in the
limit. Controlling this limit and possible mass near one is part of the
Parisi theorem, not a consequence of the terminal inequality alone.

When comparing conventions, rescale the spatial coordinate as well.
If $\psi(t,y)$ has terminal value $\log\cosh y$ and covariance
$\lambda^2\xi$, then
$\varphi(t,x)=[\psi(t,\lambda x)+\log2]/\lambda$ satisfies
$\varphi_x=\psi_y$ and $\varphi_{xx}=\lambda\psi_{yy}$ at the
rescaled point. Thus the equation
$\psi_t=-\lambda^2(\psi_{yy}+m\psi_y^2)/2$ becomes
$\varphi_t=-(\varphi_{xx}+\lambda m\varphi_x^2)/2$, and its
penalty is $\frac12\int t\lambda m(t)\,dt$.
Putting $\log2/\lambda$ outside the functional instead gives the same
number. Both the entropy constant and spatial rescaling matter.
[Auffinger and Chen (2017), §1, equations (1)–(2)][auffinger-chen]


### 10.3 Comparing coefficients before taking a derivative

We now justify the first variation used in Section 5.1. Write $\beta=\gamma+\varepsilon\eta$,
$\widetilde u=\Phi_{\beta,x}$ and $D=\Phi_\beta-\Phi_\gamma$.
Subtracting the two PDEs, before taking any limit, gives

$$
D_t=-\tfrac12D_{xx}
-\tfrac12\beta(\widetilde u+u)D_x
-\tfrac12\varepsilon\eta u^2.
$$

Use an auxiliary path $Y^\varepsilon$ starting at zero with drift
$\beta(\widetilde u+u)/2$ and the same Brownian motion. Itô's rule
cancels the first two terms and yields, on $[0,T]$,

$$
D(0,0)=\mathbb E D(T,Y_T^\varepsilon)
+\frac\varepsilon2\int_0^T\eta(t)
               \mathbb E[u(t,Y_t^\varepsilon)^2]\,dt.
$$

The control formula bounds the terminal remainder by
$\|D(T,\cdot)\|_\infty\le(3\varepsilon/2)\int_T^1|\eta|$.
First let $T\uparrow1$ at fixed positive $\varepsilon$. Next let
$\varepsilon\downarrow0$: fixed-strip stability couples
$Y^\varepsilon$ to $X$, while $|u|\le1$ bounds the integrand by
$|\eta|$. Dominated convergence gives the derivative of $\Phi(0,0)$
as $\tfrac12\int\eta q$. Differentiating the explicit linear penalty
contributes $-\tfrac12\int\eta t$, proving the formula. Thus the
changing optimiser is handled by an exact difference identity, not by
assuming that its response stays fixed.


The path comparison can be quantified. On $[0,T]$, let $L_T$ be a
common spatial Lipschitz bound for the two slopes. Coupling with the same
Brownian motion and using $|u|,|\widetilde u|\le1$ gives
$$
\sup_{t\le T}|Y_t^\varepsilon-X_t|
\le\left(\varepsilon\|\eta\|_{L^1(0,T)}
+\tfrac12\|\gamma\|_{L^1(0,T)}
 \|\widetilde u-u\|_{\infty,[0,T]\times\mathbb R}\right)
 e^{L_T\|\gamma\|_{L^1(0,T)}}.
$$
For example, split the drift difference into $(\beta-\gamma)
(\widetilde u+u)/2$ and $\gamma[(\widetilde u+u)/2-u]$,
then separate the change in position from the change in slope.
The displayed bound tends to zero. For coefficients with jumps, apply
the identity first to paired step approximations with the same smoothed final reward, then take the limit on $[0,T]$. This justifies Itô's rule
without assuming classical time differentiability at a jump.

There is a second short route to contact after $G\ge0$ is known.
The feasible direction $\eta=-\gamma$ scales all existing mass down.
Absolute Fubini follows from
$$
\int_{[0,1)}\int_s^1|q(t)-t|\,dt\,\mu_\gamma(ds)
\le\int_{[0,1)}(1-s)\,\mu_\gamma(ds)=\|\gamma\|_1.
$$
Minimality gives $0\le-\frac12\int G\,d\mu_\gamma$; nonnegativity
then gives contact. This works even when the total mass is infinite.
The compact-removal proof in Section 5.1 additionally shows the local
operation and applies equally to diffuse and atomic mass.

### 10.4 Regularity and uniqueness of the auxiliary path

A partial derivative varies the indicated coordinate while keeping
the other fixed. The PDE in Section 3.3 describes how the control value changes with
the starting time and position. The source proves that the value defined
by the optimisation satisfies this equation. For a general admissible coefficient it holds for
almost every time. The source also proves local absolute continuity in
time, so changes on a fixed strip are recovered by integrating the time
derivative. Every positive-order spatial derivative is bounded on
each fixed strip $0\le t\le T<1$. Such a strip stops short of the
corner of the terminal function $|x|$; smoothness at time one is not assumed.
The value itself grows like $|x|$. If coefficients converge in $L^1$,
their positive-order spatial derivatives converge uniformly over all
$x\in\mathbb R$ on each such strip. This is the precise regularity
input used when the calculations pass from finite steps to general
coefficients. It is different from the uniform terminal-value bound

$$
0\le\Phi_\gamma(t,x)-|x|
\le\sqrt{\frac{2(1-t)}\pi}+\frac12\int_t^1\gamma(s)\,ds,
$$

which tends to zero as $t\uparrow1$. Terminal values can converge even
when derivatives become unbounded: for $\gamma=0$, the curvature at
$x=0$ is $\sqrt{2/\pi}/\sqrt{1-t}$. Jagannath–Tobasco supplies the dynamic-programming and verification method;
Chen–Handschy–Lerman supplies zero-temperature control and regularity results.
The all-space convergence just used is the stronger statement proved in
[OpenAI (2026a), Lemmas 2.1–2.2][support-regularity]; convergence on bounded
spatial intervals alone would not cover an unbounded Gaussian path.
Finite-step approximation in $L^1$ and smoothing the terminal absolute
value are separate limiting operations. The proof controls both while
keeping $T<1$ fixed.

For uniqueness, fix $T<1$. The bounded curvature gives
$|u(t,x)-u(t,y)|\le L_T|x-y|$ for $t\le T$; this is a spatial
Lipschitz bound. Two solutions driven by the same Brownian path therefore obey
$$
|X_t-\widetilde X_t|
\le L_T\int_0^t\gamma(s)|X_s-\widetilde X_s|\,ds.
$$
Gronwall's inequality forces the difference to vanish. Existence still
uses the source's regularity theorem; the comparison proves that any two
adapted solutions with the same Brownian motion agree. This is why the
identities hold for every associated diffusion. The path equation holds
almost surely simultaneously in time. The formal full-support conclusion
also supplies an associated diffusion.

### 10.5 Why the potential conditions suffice for optimality

The converse criterion in Section 5.2 uses the actual $q$ and $G$
of the same candidate $\gamma$.
Suppose $G\ge0$ and $G=0$ on $\operatorname{supp}\mu_\gamma$.
For any other admissible $\beta$, with measure $\mu_\beta$, weighted
Fubini gives
$$
2D\mathcal P(\gamma)[\beta-\gamma]
=\int_{[0,1)}G\,d\mu_\beta-\int_{[0,1)}G\,d\mu_\gamma\ge0.
$$
Each integral is absolutely finite: $|G(s)|\le1-s$ and Section 2's
weighted-mass identity applies. The second integral vanishes by contact.
The control formula makes $\mathcal P$ convex in its coefficient:
for each fixed response the terminal absolute value is convex and both
penalties are linear, and taking the supremum over the same response
class preserves convexity. Hence
$$
\mathcal P(\beta)-\mathcal P(\gamma)
\ge D\mathcal P(\gamma)[\beta-\gamma]\ge0.
$$
So the two potential conditions characterize minimisation. This is an
ordinary variational consequence, consistent with
[Chen–Handschy–Lerman, Proposition 4][chl-optimality]. It is stronger than
checking that $\gamma$ increases or has positive density. An arbitrary
curve drawn to satisfy contact is not enough: it must be generated by
that candidate's PDE and diffusion. Sections 5.3–5.4 use the forward implication to prove full support.

<!-- /passage:analytic-notes -->

<!-- passage:source-record -->
## Sources and verification

OpenAI's [full-support paper (2026a)][support-manuscript] is the source
of the no-gap theorem, the strict curvature estimate and the scalar
consequences explained here. It credits earlier Parisi theory and notes
that [Chen (2026)][chen-support] proved the same full-relative-support
conclusion. OpenAI's [QAOA paper (2026b)][qaoa-manuscript] states the
separate circuit theorem and its thermodynamic-first order of limits.
The main mathematical sources and their roles are listed below. Links
select the editions used for the stated results.

- **OpenAI (2026a).** *Full support of the zero-temperature
  Sherrington–Kirkpatrick order parameter*, 27 September 2026.
  [Pinned manuscript][support-manuscript]: Lemmas 2.1–2.2 supply the
  fixed-strip regularity, Proposition 5.1 the plateau curvature estimate,
  §6 the variational proof, and Corollary 6.4 the additional density result.
- **OpenAI (2026b).** *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*, 25 September 2026.
  [Pinned manuscript][qaoa-manuscript]: §§2–6 provide rooted energy,
  finite classical formulas, synthesis, seed removal and assembly.
- **Antonio Auffinger and Wei-Kuo Chen (2017).** *Parisi formula for the
  ground state energy in the mixed p-spin model*, Annals of Probability
  45(6B), 4617–4631. [Version 2][auffinger-chen] supplies the external
  variational formula and its zero-temperature convention.
- **Aukosh Jagannath and Ian Tobasco (2016).** *A dynamic programming
  approach to the Parisi functional*, Proceedings of the American
  Mathematical Society 144, 3135–3150. [Version 4][jt-control] develops
  the control method with a finite-temperature terminal datum; that
  result alone is not the zero-temperature regularity theorem used here.
- **Wei-Kuo Chen, Madeline Handschy and Gilad Lerman (2018).** *On the
  energy landscape of the mixed even p-spin model*, Probability Theory
  and Related Fields 171, 53–95. [Version 4][chl-optimality]: Propositions
  2–4 and Theorems 4–6 give zero-temperature analytic and variational
  results; the proof of Theorem 6 supplies the explicit zero-candidate
  descent used in Section 4.1.
- **Hong-Bin Chen (2026).** *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][chen-support],
  Theorem 1.3, proves full support and a smooth nonnegative density.
  Strict positivity at positive times in Section 5.5 uses the additional
  OpenAI corollary; it is not attributed to that theorem.
- **Edward Farhi, Jeffrey Goldstone, Sam Gutmann and Leo Zhou (2022).**
  *The Quantum Approximate Optimization Algorithm and the
  Sherrington-Kirkpatrick Model at Infinite Size*, Quantum 6, 759.
  [Version 4][fggz], §§III–IV, gives the fixed-parameter first and second
  moments and their concentration consequence used in Section 8.5.1.
- **Joao Basso, Edward Farhi, Kunal Marwaha, Benjamin Villalonga and
  Leo Zhou (2022).** *The Quantum Approximate Optimization Algorithm
  at High Depth for MaxCut on Large-Girth Regular Graphs and the
  Sherrington-Kirkpatrick Model*. [Full preprint, version 3][bfmvz],
  §7, equation (7.2), states the eventual-optimality conjecture. Its
  full-preprint numbering is used here.

- **Sami Boulebnane and coauthors (2026).** *Spin–Boson Mapping of the
  Quantum Approximate Optimization Algorithm*, Physical Review Letters
  136, 240601. [Version 2][spin-boson], Theorem 2 and Supplement VI.B,
  supplies the related fixed-depth representation; its empirical depth
  fit is not a convergence theorem.
- **Jonathan A. Jones and Emanuel Knill (1999).** *Efficient Refocussing
  of One Spin and Two Spin Interactions for NMR Quantum Computation*,
  Journal of Magnetic Resonance 141, 322–325. [Version 1][jones-knill],
  §II, gives orthogonal sign patterns for selective interaction refocusing.
- **Jr-Shin Li and Navin Khaneja (2005).** *Noncommuting vector fields,
  polynomial approximations and control of inhomogeneous quantum ensembles*.
  [Version 1][li-khaneja], §II, Examples 1–2, supplies the approximate
  bracket-and-polynomial method, rather than the QAOA source's exact
  finite-family cancellation lemma.
- **Michel Talagrand (2006).** *The Parisi formula*, Annals of Mathematics
  163, 221–263. [Theorem 1.1][talagrand] gives the positive-temperature
  free energy; equations (1.3)–(1.5) specify covariance hypotheses and
  (1.14) uses an unnormalised partition sum.
- **Andrea Montanari (2025).** *Optimization of the Sherrington–Kirkpatrick
  Hamiltonian*, SIAM Journal on Computing 54(4), FOCS19-1–FOCS19-38.
  The [2019 preprint, version 2][montanari], supplies the message-passing
  construction and states its support assumption and computational model.
- **Ahmed El Alaoui, Andrea Montanari and Mark Sellke (2021).**
  *Optimization of mean-field spin glasses*, Annals of Probability 49,
  2922–2960. The [preprint, version 1][eams-meanfield], Assumption 1,
  Theorem 2 and Remark 2.1, gives the general algorithmic framework.
  Assumption 2 and Corollary 2.2 supply the no-gap application in §8.6,
  with the complexity of displayed Theorem 3 on page 7.
- **Ahmed El Alaoui, Andrea Montanari and Mark Sellke (2023).**
  *Local algorithms for Maximum Cut and Minimum Bisection on locally
  treelike regular graphs of large degree*, Random Structures and
  Algorithms 63, 689–715. [Version 2][eams-graphs] supplies the distinct
  finite-tree construction, with the formula limitation noted in §8.7.
- **Patrick Lopatto (2026).** *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [Version 3][lopatto-support] supplies
  the positive-temperature support input used by the QAOA appendix;
  its use here is not an automatic zero-temperature transfer.

The companion source record supplies the fuller bibliography and exact
source locations.

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

The formal proofs are written in Lean and use mathlib. The tools are
described by de Moura and Ullrich in [*The Lean 4 Theorem Prover and
Programming Language* (2021)](https://doi.org/10.1007/978-3-030-79876-5_37)
and by The mathlib Community in [*The Lean Mathematical Library*
(2020)](https://doi.org/10.1145/3372885.3373824). The companion source
record gives the precise versions used here.

The retained evidence distinguishes source presence, successful compilation,
declaration extraction and Comparator acceptance. An early Comparator
invocation could not start. Later invocations built and exported the
full-support and scalar-value challenges, then stopped during their solution
builds because imported compiled modules were missing. Neither exported
or accepted its solution. No completed corrected research replay is recorded. This is a
build obstruction, not a mathematical rejection. The linked configurations
state what is selected for comparison, not an acceptance result. Nor do
these observations establish independent review of the complete analytic
proofs or human reader comprehension.
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

[support-density]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/order-parameter-regularity.tex

[qaoa-classical]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/03-classical-optimization.tex

[qaoa-foundations]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/02-foundations.tex

[qaoa-synthesis]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/04-classical-synthesis.tex

[qaoa-seeds]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/05-seed-simulation.tex

[qaoa-assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/06-assembly.tex

[qaoa-positive]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/build/sections/07-positive-temperature.tex

[support-algorithm]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/algorithm-application.tex

[fggz]: https://arxiv.org/abs/1910.08187v4
[bfmvz]: https://arxiv.org/abs/2110.14206v3

[chl-optimality]: https://arxiv.org/abs/1609.04368v4

[jt-control]: https://arxiv.org/abs/1502.04398v4

[jones-knill]: https://arxiv.org/abs/quant-ph/9905008v1
[li-khaneja]: https://arxiv.org/abs/quant-ph/0510012v1
[talagrand]: https://annals.math.princeton.edu/2006/163-1/p04
[montanari]: https://arxiv.org/abs/1812.10897v2
[eams-meanfield]: https://arxiv.org/abs/2001.00904v1
[eams-graphs]: https://arxiv.org/abs/2111.06813v2
[lopatto-support]: https://arxiv.org/abs/2607.11756v3

[spin-boson]: https://arxiv.org/abs/2505.07929v2
