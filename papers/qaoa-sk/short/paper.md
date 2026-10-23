# Why zero-temperature SK minimisers have no support gaps

*A short reconstruction of OpenAI's full-support argument · 23 October 2026*

<!-- passage:abstract -->
**Abstract.** For the pure Sherrington–Kirkpatrick model at zero external
field, every admissible integrable minimiser of the zero-temperature Parisi
functional has full relative Stieltjes support on $[0,1)$. We reconstruct
OpenAI's proof of this known support conclusion. Minimality gives contact
conditions at the endpoints of a hypothetical gap. An integrated coercive
estimate makes the derivative of a diffusion moment strictly convex
throughout each positive constant interval of the order parameter.
The resulting deficit between two contact points excludes an interior
gap; separate endpoint arguments complete the proof. We explain the
curvature estimate, compare it with Chen's crossing argument, and derive
the scalar value identity. The subsequent QAOA construction lies beyond
the support theorem.
<!-- /passage:abstract -->

<a id="model-and-result"></a>

## 1. The variational problem and the result

<!-- passage:model -->
Let $J_{ij}$ be independent standard Gaussian variables. The zero-field SK
Hamiltonian is
$$
H_n(\sigma)=\frac1{\sqrt n}\sum_{i<j}J_{ij}\sigma_i\sigma_j,
\qquad \sigma\in\{-1,1\}^n.
$$
We use the covariance convention $\xi(t)=t^2/2$. For configurations
$\sigma,\tau$ with overlap $R=n^{-1}\sum_i\sigma_i\tau_i$, the covariance
of this unordered-pair Hamiltonian is
$nR^2/2-1/2$. Adding a single independent centered Gaussian of variance
$1/2$, common to all configurations, gives covariance $n\xi(R)$ and
does not change the expected maximum.

Let $\mathcal U$ consist of the nonnegative, nondecreasing,
right-continuous functions $\gamma:[0,1)\to[0,\infty)$ with
$\int_0^1\gamma(t)\,dt<\infty$. Its Stieltjes measure is determined by
$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\leq t<1.
$$
Thus $\mu_\gamma(\{0\})=\gamma(0)$. This measure is locally finite;
its total mass need not be finite and it is not normalized to be a
probability measure. Support always means support in the relative topology
of $[0,1)$.

For $\gamma\in\mathcal U$, let $\Phi_\gamma$ be the solution of
$$
\partial_t\Phi_\gamma
 =-\frac12\bigl(\partial_{xx}\Phi_\gamma
              +\gamma(t)(\partial_x\Phi_\gamma)^2\bigr),
\qquad \Phi_\gamma(1,x)=|x|.
$$
On compact time strips, the value function and its spatial derivatives
are locally absolutely continuous in time, and the PDE holds almost
everywhere in time. For nonsmooth coefficients the value function is
defined by the stochastic-control
formula, equivalently the monotone-coefficient approximation, in
[OpenAI (2026a, equation (1.1) and §2)][FS]. Define
$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
                 -\frac12\int_0^1t\gamma(t)\,dt.
$$
By [Auffinger and Chen (2017), Theorem 1 and the proof of Lemma 3][AC],
the zero-temperature Parisi formula and attainment give
$$
P_*:=\lim_{n\to\infty}n^{-1}\mathbb E\max_\sigma H_n(\sigma)
=\min_{\gamma\in\mathcal U}\mathcal P(\gamma).
$$
The support theorem below is conditional on a minimizer; it does
not itself prove existence.
<!-- /passage:model -->

<!-- passage:main-result -->
**Theorem 1 ([OpenAI (2026a), Theorem 1.1][FS]: full support).** In the pure zero-field SK
normalisation $\xi(t)=t^2/2$, let $\gamma\in\mathcal U$ minimise
$\mathcal P$. Then
$$
\operatorname{supp}\mu_\gamma=[0,1),
\qquad \gamma(b)>\gamma(a)\quad(0\leq a<b<1).
$$
Writing $u=\partial_x\Phi_\gamma$, the associated diffusion
$$
dX_t=\gamma(t)u(t,X_t)\,dt+dB_t,\qquad X_0=0,
$$
exists, with $B$ standard Brownian motion, and satisfies
$$
\mathbb E[u(t,X_t)^2]=t,
\qquad
\mathbb E[(\partial_{xx}\Phi_\gamma(t,X_t))^2]=1
\quad(0\leq t<1).
$$

The [fixed-revision Lean implementation][support-lean] and its
[separately stated formal challenge][support-challenge] give the exact
formal scope of Theorem 1. The [Comparator configuration][support-config]
selects their intended comparison; it is not a successful replay receipt.

Integrability allows $\gamma$ to grow near one; the theorem does not assume
a bounded or finitely stepped order parameter. Zero field supplies the
symmetry $u(0,0)=0$, and the constant value $\xi''=1$ enters the curvature
calculation. Extensions to nonzero field or mixed-spin covariance are not
asserted here.

Infinitely many support points would not suffice. For example,
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$ has infinitely many support
points accumulating at one and still leaves open intervals without mass.
Theorem 1 excludes every such interval. [Auffinger, Chen and Zeng
(2020)][ACZ] proved infinite support. [Chen (2026), Theorem 1.3][Chen]
gives the same full-relative-support conclusion, together with smooth
absolute continuity.
We retain the support-and-moment statement above; density regularity
requires a further argument. The reason to study OpenAI's route is its
constant-interval curvature estimate, compared with Chen's argument in §3.
This note claims neither a new support theorem nor priority for that conclusion.
<!-- /passage:main-result -->

<a id="contact"></a>

## 2. Minimality creates contact points

<!-- passage:contact -->
Fix a minimizer and set
$$
q(t)=\mathbb E[u(t,X_t)^2],\qquad
G(s)=\int_s^1(q(t)-t)\,dt.
$$
The analytic regularity and diffusion results of [OpenAI (2026a)][FS] give, on each compact
time interval below one,
$$
du(t,X_t)=\partial_{xx}\Phi_\gamma(t,X_t)\,dB_t,
\qquad
q'(t)=\mathbb E[(\partial_{xx}\Phi_\gamma(t,X_t))^2].
$$
In particular $q(0)=0$. The same source proves the one-sided variation
formula
$$
D\mathcal P(\gamma)[\eta]
 =\frac12\int_0^1\eta(t)(q(t)-t)\,dt
$$
for each integrable direction $\eta$ for which
$\gamma+\varepsilon\eta\in\mathcal U$ for all sufficiently small
$\varepsilon\geq0$. We now extract its consequence without assuming
that the Stieltjes measure has atoms or a density.

Adding an atom at $s$ corresponds to $\eta(t)=\mathbf1_{[s,1)}(t)$.
Minimality therefore gives $G(s)\geq0$. For a compact
$K\subset[0,1)$, restrict $\mu_\gamma$ to $K$ and write this finite
measure as $\nu$. Removing a fraction of this mass gives the admissible
direction $\eta(t)=-\nu([0,t])$. Fubini's theorem yields
$$
0\leq D\mathcal P(\gamma)[\eta]
  =-\frac12\int_KG(s)\,d\mu_\gamma(s).
$$
Since $G\geq0$, it vanishes $\mu_\gamma$-almost everywhere on every
such $K$. Continuity then gives $G=0$ on
$S=\operatorname{supp}\mu_\gamma$.

At an interior support point $s$, the function $G$ has a minimum. As
$G'=s-q(s)$ and $G''=1-q'$, we obtain
$$
q(s)=s,\qquad q'(s)\leq1.                       \tag{1}
$$
If $0\in S$, then $G(0)=q(0)=0$ and
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$, so $q'(0)\leq1$ as well.
These are contact conditions, not yet the identity $q(t)=t$ everywhere.
Their proof uses the freedom to add and remove Stieltjes mass without a
probability normalization constraint.
<!-- /passage:contact -->

<a id="curvature"></a>

## 3. The estimate that excludes a gap

<!-- passage:curvature -->
A gap in the support is a constant interval of the order parameter.
The analytic input is [OpenAI (2026a, Proposition 5.1)][FS]. Its conclusion holds
throughout every positive constant interval, without assuming minimality.

**Lemma 2 (constant-interval curvature).** Let $\gamma\in\mathcal U$,
let $X$ be its controlled diffusion, and set
$q(t)=\mathbb E[\Phi_{\gamma,x}(t,X_t)^2]$. Suppose that $\gamma=c$
on an open interval $I\subset(0,1)$. If $c>0$, then
$$
q'''(t)\geq\frac{1}{1000c^2}
  \mathbb E[(c\Phi_{\gamma,xx}(t,X_t))^4]>0,
\qquad t\in I.                                      \tag{2}
$$
Thus $q'$ is strictly convex on $I$. If $c=0$, then $q'$ is
strictly increasing on $I$.

For comparison, on a putative positive gap of the minimiser, Chen's
Proposition 4.2 gives $q''(t)=0\Rightarrow q'''(t)>0$, with this
moment denoted by $\Gamma$ there [Chen (2026)][Chen]. Estimate (2) gives
positivity at every interior time. It therefore supplies the strict
convexity used in the endpoint-chord contradiction of §4.

On a positive constant interval put
$$
r=c\Phi_x,\qquad v=r_x,\qquad w=r_{xx},\qquad z=r_{xxx}.
$$
Along $X$, the drift and diffusion coefficients of $r,v,w$ are,
respectively, $(0,v)$, $(-v^2,w)$ and $(-3vw,z)$. Starting from
$c^2q'=\mathbb E v^2$, Itô's formula gives
$$
c^2q''=\mathbb E[w^2-2v^3],\qquad
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].                 \tag{3}
$$
Indeed, the drift of $w^2$ is $z^2-6vw^2$, and that of $v^3$ is
$3vw^2-3v^4$. The negative term in (3) explains why convexity of
$\Phi$ alone does not give the required sign.

For positive nondecreasing finite-step coefficients, smooth the terminal
cusp using
$$
\Phi(1,x)=M^{-1}\log(2\cosh(Mx)),\qquad
M\geq\|\gamma_{\rm step}\|_\infty.
$$
On a step with coefficient $c$,
the diffusion density factors as $f=e^{c\Phi}g$, where $g$ solves the
forward heat equation.

The source propagates backward inequalities for
$r$ and forward inequalities for the score $s=-\partial_x\log g$.
On $x>0$, $r$ and $s$ are increasing and concave. With $\tau$
denoting backward heat time, $r_\tau/r\leq0$ is nondecreasing
in $x$, and so is $s/r$.
The ratios extend smoothly through zero. These signs and extensions are
analytic inputs. The polynomial calculation does not prove them.

The rational certificate [OpenAI (2026a, Lemma 4.1)][FS] writes the integrand in
(3) as a derivative correction and a nonnegative remainder. For a chosen
polynomial $F$, its differential expression $\mathcal W(F)$ satisfies
$$
f\mathcal W(F)=\partial_x(rfF).
$$
The propagated signs make the remaining weighted squares and polynomial
terms nonnegative, with at least $10^{-3}v^4$ left over. The source's
integrability and tail bounds remove the derivative after integration,
giving
$$
\mathbb E_f[z^2-12vw^2+6v^4]
  \geq\frac1{1000}\mathbb E_f[v^4].                 \tag{4}
$$
This is an integrated inequality for the specified profiles and density.
It is not a pointwise inequality for arbitrary $v,w,z$.

To reach an integrable coefficient, choose positive nondecreasing
finite-step approximants that remain equal to $c$ near a fixed time
in $I$. Spatial derivatives of $\Phi$ through order four converge
uniformly on compact time strips, and the coupled diffusions converge.
Only $v,w,z$ remain in (4), so no convergence of the auxiliary scores
or their ratios is required. Strict positivity of $\Phi_{xx}$ then
gives (2). For $c=0$, the heat equation instead gives
$q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$; this case is not obtained
by dividing by $c$.

The sign propagation, exact certificate and approximation proofs are in
[OpenAI (2026a, §§4–5)][FS].
The long reasoning record, §4, “Strict curvature on a constant interval”,
also explains strictness in the zero-coefficient case and the polynomial
correction, with a link to the complete source expression.
<!-- /passage:curvature -->

<a id="gap-elimination"></a>

## 4. Eliminating all support gaps

<!-- passage:gap-proof -->
We can now complete the variational argument. Suppose first that
$(a,b)$ is a gap with $0\leq a<b<1$ and both endpoints in $S$.
The contact conditions give $q(a)=a$, $q(b)=b$ and
$q'(a),q'(b)\leq1$, with the right derivative at zero when needed.
If the constant value of $\gamma$ is positive, strict convexity and
continuity at the endpoints imply
$$
q'(t)<\frac{b-t}{b-a}q'(a)+\frac{t-a}{b-a}q'(b)
      \leq1\qquad(a<t<b).
$$
Integrating gives $q(b)-q(a)<b-a$, contradicting contact at the two
endpoints. If the constant is zero, strict increase gives
$q'(t)<q'(b)\leq1$ and yields the same contradiction.

An initial gap $[0,b)$ with $0\notin S$ has $\gamma=0$ throughout:
there is neither an atom at zero nor any later mass before $b$.
Again $q'(t)<q'(b)\leq1$, whereas $q(0)=0$ and $q(b)=b$.
Integration excludes this gap.

A terminal gap requires another argument because its endpoint $1$ is
outside the support domain. On a hypothetical constant interval
$(a,1)$, [OpenAI (2026a, Lemma 6.3)][FS] proves
$$
1-q(t)\geq C\sqrt{1-t}
$$
for some $C>0$ and all $t$ sufficiently close to one. The estimate comes
from the terminal cusp $|x|$: in a window $|x|\leq\sqrt{1-t}$ the
smoothed gradient stays uniformly away from both $-1$ and $1$, while
the diffusion density has a uniform positive lower bound. Integrating
over that window gives
the displayed square-root deficit. It follows that
$q(t)-t\leq(1-t)-C\sqrt{1-t}<0$ near one, contradicting $G(s)\geq0$
for $s$ sufficiently close to one. This also excludes empty support,
when $\gamma=0$ everywhere. The terminal-plateau conclusion was
already recorded in [Auffinger, Chen and Zeng (2020, Remark 7)][ACZ].

The relatively closed set $S$ has no component in its complement, so
$S=[0,1)$. Equation (1) now holds at every positive time, and symmetry
supplies $q(0)=0$. Differentiating $q(t)=t$ gives the second moment
identity in Theorem 1, including its one-sided value at zero. Finally,
every nonempty open interval has positive $\mu_\gamma$-mass, whence
$\gamma(b)-\gamma(a)=\mu_\gamma((a,b])>0$. This proves Theorem 1
using the analytic input stated above. The long reasoning record, §5,
"Excluding terminal, interior and initial gaps", retains the case
separation and source destinations.
<!-- /passage:gap-proof -->

<a id="value-and-qaoa"></a>

## 5. A scalar consequence and the QAOA question

<!-- passage:scalar-value -->
The moment identities explain why full support matters to the value
problem. Let $M_t=u(t,X_t)$ and $a(t,x)=\Phi_{xx}(t,x)$.
Then $M_t=\int_0^t a(s,X_s)\,dB_s$ is a bounded martingale with
$\mathbb E M_t^2=t$. Its terminal limit $U_1$ satisfies
$|U_1|\leq1$ and $\mathbb E U_1^2=1$, hence $U_1^2=1$ almost surely.
The terminal convergence in [OpenAI (2026a)][FS] gives $U_1X_1=|X_1|$ without
requiring that $X_1\ne0$ almost surely.

Itô's formula and $q(t)=t$ give
$$
\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt.
$$
Multiplying
$X_1=B_1+\int_0^1\gamma(t)M_t\,dt$ by $U_1$, taking expectations,
and using $\mathbb E[U_1M_t]=\mathbb E M_t^2=t$ then yields
$$
P_* = \mathbb E[U_1B_1]
    = \int_0^1\mathbb E[a(t,X_t)]\,dt.              \tag{5}
$$
The scalar identity belongs to a [separate Lean implementation][value-lean]
and [formal challenge][value-challenge], with its own
[Comparator configuration][value-config]. Its formal premises and the
finite-Gaussian clause are set out in §6.
The use of $P_*$ here invokes the Parisi formula [Auffinger and Chen (2017)][AC]; the preceding
identity is already an identity for $\mathcal P(\gamma)$.
The integral is finite since
$\mathbb E|a(t,X_t)|\leq(\mathbb E a(t,X_t)^2)^{1/2}=1$.
This is [OpenAI (2026a, Corollary 7.1)][FS]; the
long reasoning record, §6, "Recovering the value from a martingale",
provides the terminal and stochastic-integral justification.

The companion finite Gaussian construction approximates the right side
of (5) first on $[0,T]$, with fixed $0<T<1$, and then as $T\uparrow1$.
Its mesh count tends to infinity before $T$ approaches one. Those
coefficients are scalar Gaussian correlations, not circuit energies.
The approximation is treated in
[OpenAI (2026a, Proposition 7.2)][FS] and the
long reasoning record, §7, "A finite Gaussian spin and its adjacent
correlations".
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
[OpenAI (2026b)][Q] proves a further QAOA statement.
For a $p$-layer circuit with deterministic cost and mixer angles
$\boldsymbol\theta,\boldsymbol\beta$, let
$v_p(\boldsymbol\theta,\boldsymbol\beta)$ be its limiting expected
energy per spin as $n\to\infty$, holding those angles fixed. Define
$$
Q_p=\sup_{\boldsymbol\theta,\boldsymbol\beta\in\mathbb R^p}
       v_p(\boldsymbol\theta,\boldsymbol\beta).
$$
The manuscript's main theorem asserts $\lim_{p\to\infty}Q_p=P_*$:
for every $\varepsilon>0$, a finite depth and deterministic angles,
independent of both $n$ and the disorder, attain at least
$P_*-\varepsilon$ in that limiting expectation. The angles and depth
may depend on $\varepsilon$. No quantitative depth bound, finite-size
estimate or efficient angle-selection procedure is supplied by that
statement.

The zero-temperature route still requires a rooted realisation of the
scalar Gaussian formula, classical synthesis, removal of temporary
longitudinal seed controls and fixed-word transfer to SK. The independent
positive-temperature route supplies a different classical input to the
circuit construction. See [OpenAI (2026b, §§3–6 and Appendix A)][Q] and the
long reasoning record, §9, "From the scalar formula to one ordinary QAOA word".
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## 6. Source and verification scope

<!-- passage:evidence-scope -->
This is an AI-assisted draft reconstruction of the cited arguments.
OpenAI is the credited author of both cited 2026 manuscripts. The exact
editions, claim correspondences and verification records are identified
in the companion source review.

The selected full-support interface assumes an admissible minimiser and
includes Stieltjes-measure and diffusion existence, full relative support,
strict increase and both moment identities for every associated diffusion.
The scalar-value interface assumes a minimiser and an associated diffusion
for its scalar and finite-Gaussian clauses; its final ground-state/Parisi
equality assumes only the minimiser. Neither declaration asserts QAOA
circuit convergence.

The retained source-integrity checks passed, but the attempted full-support
Comparator invocation could not start because the executable was unavailable;
the scalar-value invocation remained unrun. Separate tool-fixture checks
replay neither target. These records establish no research-target build,
transitive axiom audit, successful Comparator replay, complete manuscript
correspondence review or independent human review. The admitted challenge
statements remain distinct from their implementing sources.
<!-- /passage:evidence-scope -->

## References

- OpenAI (2026a). *Full support of the zero-temperature Sherrington–Kirkpatrick
  order parameter*. 27 September 2026. [Manuscript][FS]. Theorem 1.1;
  Lemmas 6.2 and 6.3; Proposition 5.1; Corollary 7.1.
- OpenAI (2026b). *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*. 25 September 2026. [Manuscript][Q].
  Theorem 1.1; construction in sections 3–6.
- Auffinger and Chen (2017). “Parisi formula for the
  ground state energy in the mixed p-spin model.” *Annals of Probability*
  **45** (2017), 4617–4631. [Preprint][AC]. External formula and attainment
  input used in [OpenAI (2026a)][FS].
- Auffinger, Chen and Zeng (2020). “The SK model
  is infinite step replica symmetry breaking at zero temperature.”
  *Communications on Pure and Applied Mathematics* **73** (2020),
  921–943. [Preprint][ACZ]. Infinite support and the terminal-plateau
  antecedent; these do not by themselves exclude an interior gap.
- Chen (2026). *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. 20 July 2026, version 1.
  [Preprint][Chen]. Theorem 1.3 is credited by [OpenAI (2026a)][FS] with the same full-support
  conclusion and smooth absolute continuity.

[FS]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
[FS-source]: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build
[Q]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf
[AC]: https://arxiv.org/abs/1606.05335v2
[ACZ]: https://arxiv.org/abs/1703.06872v2
[Chen]: https://arxiv.org/abs/2607.18032v1
[support-lean]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Main.lean#L35
[support-challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.lean#L81-L92
[support-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKFullSupport.json
[value-lean]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/Main.lean#L16
[value-challenge]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean#L163
[value-config]: https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.json
