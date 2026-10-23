# Why the SK order parameter has no gaps

## From a two-spin calculation to the scalar ingredients of QAOA

**Expository draft · 23 October 2026**

<!-- passage:opening -->
In the pure Sherrington–Kirkpatrick model with no external field, every
admissible minimizer of the zero-temperature Parisi functional increases
strictly between any two scales below one. Its associated measure gives
positive mass to every nonempty relatively open interval in $[0,1)$.
The decisive argument rules out a flat interval: optimality fixes the
values at its endpoints, while a strict curvature inequality makes the
change between those endpoints too small. The resulting identities also
express the limiting optimal energy through a one-dimensional diffusion.

This article explains those results from OpenAI's full-support manuscript
and the two accompanying Lean interfaces. It then identifies their role
in the separate manuscript claim about QAOA, the quantum approximate
optimization algorithm. The scalar results do not themselves assert
convergence of QAOA circuit energies. The supplied source collection has
not been replayed in Lean or Comparator here.

The intended reader knows calculus, expectations and elementary linear
algebra. Brownian motion and martingales are introduced by their roles;
the analytic estimates underlying the strict curvature inequality are
identified but not reproved. By the end, the reader should be able to
reconstruct the no-gap contradiction, explain the terminal-spin value
identity, and state which limits the QAOA claim takes in which order.
<!-- /passage:opening -->

<!-- passage:spins-and-overlap -->
## 1. Two spins, and the normalization we will keep

A spin configuration is a list $\sigma=(\sigma_1,\ldots,\sigma_n)$ with
each $\sigma_i\in\{-1,1\}$. Independent standard Gaussian numbers
$J_{ij}$ assign random preferences to pairs of spins. In the convention
used throughout the sources, the energy is

$$
H_n(\sigma)=\frac{1}{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j.
$$

We maximize this energy. This fixes the sign convention: the positive
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
$1/(2\sqrt\pi)$. The calculation illustrates the normalization and
the symmetry under reversing every spin. It does not approximate the
large-system optimum by itself.

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
same independent centered Gaussian of variance $1/2$ to every energy
removes this correction and leaves the expected maximum unchanged.
The sources account for that normalization when using the Parisi formula.

The large-system question concerns

$$
P_* = \lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma).
$$

Existence and evaluation of this limit require a theorem. Writing a
limit symbol is not a proof of convergence.
<!-- /passage:spins-and-overlap -->

<!-- passage:order-parameter-example -->
## 2. What a gap means

The Parisi variational problem replaces the exponentially many spin
configurations by a function $\gamma$ of a scale $t\in[0,1)$.
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
that it minimizes the Parisi functional. The full-support theorem will
in fact rule that out.

Associate to any admissible $\gamma$ its Stieltjes measure, defined by

$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\le t<1.
$$

The measure records increments of $\gamma$: for $a<b$,
$\mu_\gamma((a,b])=\gamma(b)-\gamma(a)$. For the displayed example it
has density one on $(0,1/3)$ and $(2/3,1)$ and density zero on
$(1/3,2/3)$. Its support is
$[0,1/3]\cup[2/3,1)$, with endpoints understood relative to $[0,1)$.
It has infinitely many support points and no final interval on which
$\gamma$ is constant, but it still has an interior gap.

A point belongs to the support when every relative neighborhood of it
has positive measure. **Full relative support** means that every point
of $[0,1)$ has this property. In particular, every nonempty open interval
below one receives mass, so $\gamma(b)>\gamma(a)$ for every
$0\le a<b<1$. The word *relative* matters: the endpoint $1$ is outside
the underlying space.

This measure need not be a probability measure. Its mass at zero is
$\gamma(0)$; its total mass can be infinite even though $\gamma$ is
integrable. For instance, $(1-t)^{-1/2}$ is an admissible candidate with
integral two and unbounded cumulative mass near one. The variational
problem therefore allows adding a small atom without removing mass
elsewhere. That freedom will determine the sign in the proof.
<!-- /passage:order-parameter-example -->

<!-- passage:value-and-diffusion -->
## 3. The value assigned to a candidate function

To evaluate $\gamma$, start at position $x$ at time $t$, add Brownian
noise until time one, and allow a bounded response to that noise.
Standard Brownian motion $B$ has independent Gaussian increments with
variance equal to elapsed time. A control $\alpha_s\in[-1,1]$ can use
the increments already observed after time $t$, but cannot anticipate
future increments. The value function is

$$
\Phi_\gamma(t,x)=\sup_\alpha\mathbb E\left[
\left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
-\frac12\int_t^1\gamma(s)\alpha_s^2\,ds
\right].
$$

The first term rewards the final absolute position; the second charges
for the control. The functional being minimized is

$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
-\frac12\int_0^1t\gamma(t)\,dt.
$$

Thus minimizing $\mathcal P$ is a specific global condition on
$\gamma$, not a synonym for admissibility or monotonicity. The
full-support theorem assumes this minimum has been attained. The
manuscript attributes the ground-state Parisi formula and attainment to
[Auffinger and Chen][auffinger-chen], Theorem 1 and the proof of Lemma 3:

$$
P_*=\min_{\gamma\text{ admissible}}\mathcal P(\gamma).
$$

This theorem connects the maximum over spin configurations with the
minimum over functions. It is a substantial input, not a change of
notation. Neither selected formal interface states minimizer existence
as its own conclusion.

The value function is locally absolutely continuous in time on compact
strips and satisfies the backward equation for almost every time:

$$
\partial_t\Phi_\gamma
=-\frac12\left(\partial_{xx}\Phi_\gamma
+\gamma(t)(\partial_x\Phi_\gamma)^2\right),
\qquad \Phi_\gamma(1,x)=|x|.
$$

The terminal function has a corner at zero. The sources establish the
needed spatial regularity and approximation on strips $0\le t\le T<1$;
one cannot silently use smooth terminal data at $t=1$.

Write $u(t,x)=\partial_x\Phi_\gamma(t,x)$ and
$a(t,x)=\partial_{xx}\Phi_\gamma(t,x)$. The derivative $u$ gives the
optimal bounded response. Follow the diffusion

$$
X_t=B_t+\int_0^t\gamma(s)u(s,X_s)\,ds,\qquad X_0=0.
$$

This equation uses the same Brownian motion as the value function.
The integral is the accumulated drift from the response, and $B_t$ is
the accumulated noise. The formal full-support conclusion includes
existence of such a diffusion.

This is an auxiliary process used to evaluate the variational problem.
It is not the time evolution of a spin configuration or a quantum circuit.

Along it, $u(t,X_t)$ is a bounded martingale: conditional on the
information at an earlier time, its expected future value equals its
current value. Its second moment and derivative satisfy

$$
q(t):=\mathbb E[u(t,X_t)^2],\qquad
q'(t)=\mathbb E[a(t,X_t)^2].
$$

The second identity follows from the stochastic-integral representation
$u(t,X_t)=\int_0^t a(s,X_s)\,dB_s$. To see its moment calculation,
approximate this integral by a sum of past-dependent coefficients
$a_j=a(t_j,X_{t_j})$ times Brownian increments $\Delta B_j$.
Each next increment has conditional mean zero and variance $\Delta t$,
so different increments give zero cross terms and

$$
\mathbb E\left[\left(\sum_j a_j\Delta B_j\right)^2\right]
=\sum_j\mathbb E[a_j^2]\Delta t.
$$

The stochastic integral is the mean-square limit of such sums. Passing
to that limit gives $q(t)=\int_0^t\mathbb E[a(s,X_s)^2]\,ds$,
and the source's regularity gives the displayed derivative. In zero
external field symmetry gives $u(0,0)=0$, hence $q(0)=0$.
These identities link the variational problem to the calculus argument.
<!-- /passage:value-and-diffusion -->

<!-- passage:full-support-statement -->
## 4. The full-support result

**Source theorem.** In the pure, zero-field model with
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

This is the scope of `OAI.ZeroTemperatureSK.full_support`, with its
definitions in the [full-support interface][support-interface] and its
implementing declaration in [SKSupport/Main.lean][support-proof]. The
proof below reconstructs the manuscript's no-gap mechanism; it is not a
new proof of its analytic inputs. The assumptions exclude a nonzero
external field and general mixed-spin covariance functions. The selected
conclusion does not assert smoothness or a positive density of the
Stieltjes measure, even though the manuscript develops further results.
<!-- /passage:full-support-statement -->

<!-- passage:contact-and-gap -->
## 5. Why a flat interval cannot minimize

The proof needs a way to detect whether placing more Stieltjes mass at
a scale would improve the objective. The first-variation formula supplies
it. If $\eta$ is a direction for which
$\gamma+\varepsilon\eta$ stays admissible for sufficiently small
$\varepsilon\ge0$, the right derivative is

$$
D\mathcal P(\gamma)[\eta]
=\frac12\int_0^1\eta(t)(q(t)-t)\,dt.
$$

Adding an atom at a scale $s$ increases $\gamma(t)$ by the same amount
for every $t\ge s$. This is the direction
$\eta(t)=\mathbf1_{[s,1)}(t)$. It motivates the contact potential

$$
G(s)=\int_s^1(q(t)-t)\,dt.
$$

At a minimizer the derivative in this direction cannot be negative,
so $G(s)\ge0$ everywhere. Removing a fraction of the existing measure
on a compact interval $K=[0,T]$, with $T<1$, is also admissible.
The direction is $\eta_K(t)=-\mu_\gamma(K\cap[0,t])$: every atom
or infinitesimal mass removed at $s$ lowers the cumulative function at
all later times. Changing the order of integration in the variation
formula then gives

$$
0\le -\frac12\int_KG(s)\,\mu_\gamma(ds).
$$

Since $G\ge0$, the integral must vanish. If $G$ were positive at a
support point, continuity would make it positive on a neighborhood
having positive measure, contradicting that integral for a sufficiently
large $T<1$. Thus $G=0$ on the support. Removing a portion of all
the measure in $K$ is essential: a measure need not consist of atoms.

An interior support point is therefore a minimum of $G$. Since
$G'(s)=s-q(s)$ and $G''(s)=1-q'(s)$, calculus gives

$$
q(s)=s,\qquad q'(s)\le1.
$$

If zero belongs to the support, $G(0)=0$ and $q(0)=0$ give
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$ as $h\downarrow0$.
Nonnegativity therefore implies $q'(0)\le1$, with a right derivative.
This includes the case where the measure has an atom at zero.

Now suppose a gap $(r,s)$ lies between two support points, with
$0\le r<s<1$. The cumulative function is constant on that gap, say
$\gamma=c$. Contact at the endpoints forces

$$
q(r)=r,\quad q(s)=s,\quad q'(r)\le1,\quad q'(s)\le1.
$$

For $c>0$, the analytic core of the source proof establishes
$q'''(t)>0$ throughout the gap. Thus $q'$ is strictly convex. Its
graph lies strictly below the chord joining its endpoint values:

$$
q'(t)<\frac{s-t}{s-r}q'(r)+\frac{t-r}{s-r}q'(s)\le1
\quad(r<t<s).
$$

Integrating gives
$q(s)-q(r)<s-r$, whereas the endpoint equations require
$q(s)-q(r)=s-r$. This contradiction excludes the gap. Applied to the
candidate of Section 2, the argument says that a minimizing plateau
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
is in the source's [shape inequalities][support-signs],
[rational identity][support-certificate] and
[constant-interval curvature proposition][support-curvature].
<!-- /passage:contact-and-gap -->

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
The [variation section][support-variation] gives the mass-removal and
endpoint arguments in full.
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

The [scalar-value interface][value-interface] packages these conclusions
in `ScalarValueConclusion` and asserts them for every admissible
minimizer and associated diffusion. Its final Parisi equality needs
only the minimizer premise. The full-support and scalar-value trees
use different Lean representations of the Brownian space, order
parameter and diffusion; the mathematical presentation above is not a
claim that their declarations have been directly composed in Lean.
<!-- /passage:scalar-identities -->

<!-- passage:finite-gaussian -->
## 7. From the diffusion to finitely many Gaussian inputs

The scalar process uses an entire Brownian path. To approximate its value
using finitely many inputs, first fix a time $0<T<1$. With $N$ time
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
[scalar consequences section][support-consequences].
<!-- /passage:finite-gaussian -->

<!-- passage:qaoa-boundary -->
## 8. What the QAOA statement adds

QAOA uses a different object: a quantum state on $n$ spins, represented
here by a normalized complex vector whose coordinates are indexed by
the $2^n$ spin configurations. Its cost
operator $C_{n,J}$ is diagonal with entries $H_n(\sigma)$. Its mixer
$B_n=\sum_i X_i$ flips individual spins, where $X_i$ is the Pauli
$X$ matrix on spin $i$: it sends the basis vector $|\sigma\rangle$
to the vector with spin $i$ reversed. The equal superposition
$|+\rangle^{\otimes n}$ has every coordinate equal to $2^{-n/2}$.
Starting from this vector, a depth-$p$ circuit alternates cost and mixer
rotations:

$$
|\psi_{n,p,J}(\boldsymbol\theta,\boldsymbol\beta)\rangle
=e^{-i\beta_pB_n}e^{-i\theta_pC_{n,J}}\cdots
e^{-i\beta_1B_n}e^{-i\theta_1C_{n,J}}|+\rangle^{\otimes n}.
$$

The cost angles are written $\boldsymbol\theta$ here to distinguish
them from the function $\gamma(t)$ in the Parisi problem; the QAOA
manuscript writes these angles as $\boldsymbol\gamma$.

For each fixed depth and deterministic choice of angles, first take the
large-system limit of the expected energy per spin:

$$
v_p(\boldsymbol\theta,\boldsymbol\beta)
=\lim_{n\to\infty}\frac1n\mathbb E
\langle\psi_{n,p,J}|C_{n,J}|\psi_{n,p,J}\rangle,
\qquad Q_p=\sup_{\boldsymbol\theta,\boldsymbol\beta}v_p.
$$

The separate [QAOA manuscript theorem][qaoa-theorem] claims
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
circuit angles. Neither `full_support` nor `value_consequences` mentions
the state $|\psi_{n,p,J}\rangle$ or asserts convergence of its energy.

The claim is consequently about the order $n\to\infty$ at fixed
parameters, followed by increasing $p$. It does not interchange those
limits or give a joint schedule $p=p(n)$. The manuscript states no
quantitative finite-size estimate, depth bound, or efficient method of
choosing the angles. Its complete circuit-construction argument is
outside the proof reconstructed in this article.
<!-- /passage:qaoa-boundary -->

<!-- passage:changed-cases -->
## 9. Checks that change one condition

**Does infinite support suffice?** No. The piecewise-linear candidate
in Section 2 has an interval's worth of support points on either side
of its middle plateau, and increases arbitrarily close to one. Yet
$(1/3,2/3)$ receives no mass. Infinite support and absence of a terminal
plateau do not prove full support.

**What if strict convexity is weakened to convexity?** The area
contradiction may disappear. The function $q(t)=t$ on $[r,s]$ has
endpoint contact and $q'(t)=1$ everywhere. Its derivative is convex,
but integrating produces equality, not a contradiction. The strict
analytic inequality is load-bearing.
This tests the inference from convexity and endpoint contact; the
illustrative function is not asserted to arise from an SK diffusion
with a constant coefficient.

**Does a positive initial value imply full support?** No. The
admissible constant candidate $\gamma(t)=c>0$ represents $c\delta_0$.
Its support is only $\{0\}$. Positivity of the function and support of
its increments are different properties.

**May we set $T=1$ before refining the Gaussian approximation?** The
stated finite-Gaussian theorem has $0<T<1$ and its estimates use this
fixed strip. It gives no such endpoint substitution. The separate
limit $T\uparrow1$ is what recovers $P_*$.

**Does near-optimality with angles depending on $J$ establish the
stated QAOA theorem?** No. That changes the order of quantifiers.
The theorem asks for one deterministic angle vector, fixed independently
of the instance and system size, for each requested accuracy.

These questions are author-provided checks with justified answers.
They have not been administered as a human reader study. A useful
reader test is to reconstruct the chain
$G\ge0\to$ endpoint contact $\to$ strict area deficit, then explain
why the last step still leaves a separate circuit-construction problem.
<!-- /passage:changed-cases -->

<!-- passage:source-record -->
## Sources and verification

The mathematical sources are the public OpenAI corpus at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, retained with its original
attribution in [the public source collection][source-collection]. OpenAI is the author of
both manuscripts. This article is an explanatory reconstruction, not a
new support theorem, a priority claim, or an independent complete review
of either manuscript.

- **Full support:** [*Full support of the zero-temperature
  Sherrington–Kirkpatrick order parameter*][support-manuscript],
  27 September 2026. The introduction defines the model and states the
  result; `variation.tex` contains the contact and gap argument;
  `curvature.tex` states the strict inequality; `consequences.tex`
  derives the scalar representations. The manuscript credits earlier
  Parisi theory and states that [Chen][chen-support] proves the same full-relative-support
  conclusion. This article makes no independent novelty assessment.
- **Formal interfaces and implementations:**
  [SKFullSupport.lean][support-interface] and
  [SKSupport/Main.lean][support-proof];
  [SKValue.lean][value-interface] and
  [SKValue/Main.lean][value-proof]. The challenge files contain admitted
  interfaces; the separate `OAI` trees contain the implementing proofs.
- **QAOA:** [*QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*][qaoa-manuscript], 25 September 2026,
  especially [the model and main theorem][qaoa-theorem]. It supplies
  the circuit claim and its limit order.

The scalar Lean interface names the ground-state value through
`limUnder`; its separate `Tendsto` clause asserts convergence of the
actual finite-SK sequence. Source bytes, Lean compilation, Comparator
checking, mathematical correspondence and reader understanding are
distinct forms of evidence. This article records source comparison and
explanatory calculations; no fresh Lean or Comparator replay or human
reader-comprehension study accompanies it.

The public [mathematical-writing guide][writing-guide] informs the
use of worked examples, local proof warrants and exact source
correspondence. It is an exposition method, not a mathematical premise.
<!-- /passage:source-record -->

[support-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean
[support-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean
[value-interface]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean
[value-proof]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean
[support-manuscript]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
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
