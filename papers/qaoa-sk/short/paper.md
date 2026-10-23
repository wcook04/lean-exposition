# Why zero-temperature SK minimizers have no support gaps

*A short reconstruction of OpenAI's full-support argument · 23 October 2026*

<!-- passage:abstract -->
**Abstract.** For the pure Sherrington–Kirkpatrick model at zero external
field, every admissible integrable minimizer of the zero-temperature Parisi
functional has full relative Stieltjes support on $[0,1)$. This draft
reconstructs the argument in OpenAI's September 2026 manuscript. Minimality
gives a nonnegative contact potential. An integrated coercive estimate makes
the derivative of a diffusion moment strictly convex on every positive
constant interval of the order parameter. The resulting deficit between two
contact points excludes an interior support gap; separate endpoint arguments
complete the proof. We state the analytic input explicitly, derive the
variational contradiction, and explain the resulting scalar value identity.
The connection to the quantum approximate optimization algorithm (QAOA) requires further constructions beyond this support
theorem.
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
[[FS, equation (1.1) and the regularity section]][FS]. Define
$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
                 -\frac12\int_0^1t\gamma(t)\,dt.
$$
The zero-temperature Parisi formula and attainment identify
$P_*:=\lim_{n\to\infty}n^{-1}\mathbb E\max_\sigma H_n(\sigma)$
with $\min_{\gamma\in\mathcal U}\mathcal P(\gamma)$
[[AC, Theorem 1 and the proof of Lemma 3]][AC]. The support theorem below is conditional on a minimizer; it does
not itself prove existence.
<!-- /passage:model -->

<!-- passage:main-result -->
**Theorem 1 (full support; OpenAI [[FS]][FS]).** In the pure zero-field SK
normalization $\xi(t)=t^2/2$, let $\gamma\in\mathcal U$ minimize
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

Integrability allows $\gamma$ to grow near one; the theorem does not assume
a bounded or finitely stepped order parameter. Zero field supplies the
symmetry $u(0,0)=0$, and the constant value $\xi''=1$ enters the curvature
calculation. Extensions to nonzero field or mixed-spin covariance are not
asserted here.

Infinitely many support points would not suffice. For example,
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$ has infinitely many support
points accumulating at one and still leaves open intervals without mass.
Theorem 1 excludes every such interval. Auffinger, Chen and Zeng proved
infinite support [[ACZ]][ACZ]. Chen's Theorem 1.3 gives the same full-relative-support
conclusion, together with smooth absolute continuity [[Chen]][Chen]. The argument
reconstructed here is OpenAI's explicit coercive-identity route to excluding
gaps. This note claims neither a new support theorem nor priority for that
conclusion.
<!-- /passage:main-result -->

<a id="contact"></a>

## 2. Minimality creates contact points

<!-- passage:contact -->
Fix a minimizer and set
$$
q(t)=\mathbb E[u(t,X_t)^2],\qquad
G(s)=\int_s^1(q(t)-t)\,dt.
$$
The analytic regularity and diffusion results of [[FS]][FS] give, on each compact
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
A gap in $S$ is a constant interval of $\gamma$. The following analytic
input is the hard step of [[FS, Proposition 5.1]][FS].

**Lemma 2 (constant-interval curvature).** Let $\gamma\in\mathcal U$,
without assuming minimality, and suppose that $\gamma=c$ on an open
interval $I\subset(0,1)$. If $c>0$, then for every $t\in I$,
$$
q'''(t)\geq\frac{1}{1000c^2}
     \mathbb E[(c\partial_{xx}\Phi_\gamma(t,X_t))^4]>0. \tag{2}
$$
Consequently $q'$ is strictly convex on $I$. If $c=0$, then $q'$ is
strictly increasing on $I$.

Here is the mechanism behind (2), with the analytic sign-propagation
lemmas retained as cited inputs. On a positive constant interval, put
$$
r=c\Phi_x,\qquad v=r_x,\qquad w=r_{xx},\qquad z=r_{xxx}.
$$
Differentiation along the diffusion gives
$$
c^2q'''(t)=\mathbb E[z^2-12vw^2+6v^4](t,X_t).        \tag{3}
$$
The negative middle term prevents a pointwise positivity argument. Even
convexity of $\Phi$ does not settle the sign of this expression.

For a positive nondecreasing finite-step approximation $\widetilde\gamma$
and terminal data $M^{-1}\log(2\cosh(Mx))$ with
$M\geq\|\widetilde\gamma\|_\infty$,
the diffusion density factors as $f=e^{c\Phi}g$, where $g$ obeys a
forward heat equation between coefficient jumps. The source propagates
backward inequalities for $r$ and forward inequalities for the score
$s=-\partial_x\log g$. On $x>0$, $r$ is increasing and concave;
its backward heat-time derivative obeys $r_\tau/r\leq0$, with this
ratio nondecreasing in $x$. The score $s$ is increasing and concave, and
$s/r$ is nondecreasing in $x$. The ratios extend smoothly through zero.
These are substantive analytic inputs to the certificate. The source
then defines a polynomial differential
expression $\mathcal W(F)$ satisfying
$$
f\mathcal W(F)=\partial_x(rfF).
$$
The exact rational identity in [[FS, Lemma 4.1]][FS]
rewrites the integrand of (3) as this derivative correction, weighted
squares, and terms nonnegative under those propagated inequalities.
The remainder contains a $v^4$ term with coefficient
$$
\frac{1661507}{1521000000}>\frac1{1000}.
$$
The proved tail and integrability bounds make the derivative integrate
to zero. Therefore the identity gives
$$
\mathbb E_f[z^2-12vw^2+6v^4]
 \geq\frac1{1000}\mathbb E_f[v^4].                 \tag{4}
$$
This is an **integrated** inequality under specific profile and density
conditions, not a pointwise inequality in arbitrary $v,w,z$.

The source next approximates an integrable coefficient by positive
nondecreasing finite-step coefficients that remain equal to $c$ near
the chosen time. Spatial derivatives of $\Phi$ through order four
converge uniformly there, and the coupled diffusions converge. Thus
(4) passes to the limit using only the derivative moments appearing
in it. No limit of the auxiliary density scores or their ratios is
required. Strict positivity of $\Phi_{xx}$ makes the right side
positive. The case $c=0$ follows separately from the heat equation;
division by $c$ does not address it.

The full sign propagation, polynomial identity and approximation proofs
are in [FS, `signs.tex`, `certificate.tex`, `curvature.tex`][FS-source].
The long reasoning record, §4, "Strict curvature on a constant interval",
expands the mechanism and records the exact source destinations.
This section explains that input rather than reproducing its coefficient
table or claiming an independent verification of it.
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
$(a,1)$, [[FS, Lemma 6.3]][FS] proves
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
already recorded in [[ACZ, Remark 7]][ACZ].

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
The terminal convergence in [[FS]][FS] gives $U_1X_1=|X_1|$ without
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
The use of $P_*$ here invokes the Parisi formula [[AC]][AC]; the preceding
identity is already an identity for $\mathcal P(\gamma)$.
The integral is finite since
$\mathbb E|a(t,X_t)|\leq(\mathbb E a(t,X_t)^2)^{1/2}=1$.
This is [[FS, Corollary 7.1]][FS]; the
long reasoning record, §6, "Recovering the value from a martingale",
provides the terminal and stochastic-integral justification.

The companion finite Gaussian construction approximates the right side
of (5) first on $[0,T]$, with fixed $0<T<1$, and then as $T\uparrow1$.
Its mesh count tends to infinity before $T$ approaches one. Those
coefficients are scalar Gaussian correlations, not circuit energies.
The approximation is treated in
[[FS, Proposition 7.2]][FS] and the
long reasoning record, §7, "A finite Gaussian spin and its adjacent
correlations".
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
OpenAI's separate QAOA manuscript [[Q]][Q] targets a further statement.
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

The zero-temperature route uses scalar value approximation, a classical
synthesis construction, temporary longitudinal seed controls and their
removal, and a final error
assembly. The support theorem supplies only an earlier ingredient in
that route. The manuscript also gives an independent positive-temperature
route. Its full QAOA argument is outside this note; see [[Q, sections 3–6
and Appendix A]][Q] and the long reasoning record, §9,
"From the scalar formula to one ordinary QAOA word".
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## 6. Source and verification scope

<!-- passage:evidence-scope -->
This is an AI-assisted draft reconstruction of the cited public arguments,
not a new result or an independent verification claim. OpenAI is the credited
author of [[FS]][FS] and [[Q]][Q]. The exact source edition is
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The accompanying evidence graph records source pins and check status;
the passage correspondence record binds this text to that graph and
the source locators.

The selected full-support interface takes an admissible minimizer
as input and includes Stieltjes-measure and diffusion existence, full
relative support, strict increase and the two moment identities. In the
companion scalar-value interface, scalar and finite-Gaussian conclusions
require a minimizer
and an associated diffusion; its final ground-state/Parisi equality
requires the minimizer premise alone. The source example records no
fresh Lean build, axiom audit or Comparator replay of these targets.
The admitted challenge statements and the implementing source files
are different objects. Neither selected declaration asserts QAOA
circuit convergence. Source inspection and the exposition checks for
this draft do not constitute independent human review or peer review.
<!-- /passage:evidence-scope -->

## References

- **[[FS]][FS]** OpenAI. *Full support of the zero-temperature Sherrington–Kirkpatrick
  order parameter*. 27 September 2026. [Exact manuscript][FS] and
  [TeX source directory][FS-source]. Principal locators: Theorem 1.1;
  Lemmas 6.2 and 6.3; Proposition 5.1; Corollary 7.1.
- **[[Q]][Q]** OpenAI. *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*. 25 September 2026. [Exact manuscript][Q].
  Theorem 1.1; construction in sections 3–6.
- **[[AC]][AC]** Antonio Auffinger and Wei-Kuo Chen. “Parisi formula for the
  ground state energy in the mixed p-spin model.” *Annals of Probability*
  **45** (2017), 4617–4631. [Preprint][AC]. External formula and attainment
  input used in [[FS]][FS].
- **[[ACZ]][ACZ]** Antonio Auffinger, Wei-Kuo Chen and Qiang Zeng. “The SK model
  is infinite step replica symmetry breaking at zero temperature.”
  *Communications on Pure and Applied Mathematics* **73** (2020),
  921–943. [Preprint][ACZ]. Infinite support and the terminal-plateau
  antecedent; these do not by themselves exclude an interior gap.
- **[[Chen]][Chen]** Hong-Bin Chen. *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. 20 July 2026, version 1.
  [Preprint][Chen]. Theorem 1.3 is credited by [[FS]][FS] with the same full-support
  conclusion and smooth absolute continuity.

[FS]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/main.pdf
[FS-source]: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build
[Q]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf
[AC]: https://arxiv.org/abs/1606.05335v2
[ACZ]: https://arxiv.org/abs/1703.06872v2
[Chen]: https://arxiv.org/abs/2607.18032v1
