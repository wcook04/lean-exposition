# Full support and positive density in the zero-temperature SK model

*A reconstruction of OpenAI's coercive-curvature argument · Revised 24 October 2026*

<!-- passage:abstract -->
**Abstract.** Every admissible integrable minimiser of the zero-temperature
Parisi functional for the pure, zero-field Sherrington–Kirkpatrick model has
full relative Stieltjes support on $[0,1)$ and a smooth density that is
strictly positive on $(0,1)$. We reconstruct OpenAI's proof of these
conclusions. Minimality gives contact conditions at the endpoints of a
proposed support gap. An integrated coercive estimate makes the derivative of a
diffusion moment strictly convex on each positive constant interval of the
order parameter. The resulting area deficit contradicts contact; separate
arguments handle zero coefficients and the two endpoints. A fixed-time
approximation by shrinking constant intervals reuses the same estimate to
prove strict positivity of the density. A martingale calculation recovers
the scalar ground-state value. Chen already proved full support and smooth
absolute continuity. Our contribution is a compact account of the two uses
of the quantitative estimate and their distinct analytic requirements.
<!-- /passage:abstract -->

<a id="model-and-result"></a>

## 1. The order parameter and the result

<!-- passage:model -->
We study how a minimising order parameter distributes mass across overlap
scales. We use the pure SK covariance
$\xi(t)=t^2/2$ and zero external field. Let $\mathcal U$ be the nonnegative,
nondecreasing, right-continuous functions $\gamma:[0,1)\to[0,\infty)$ with
$\int_0^1\gamma(t)\,dt<\infty$. Define their Stieltjes measures by
$$
\mu_\gamma([0,t])=\gamma(t),\qquad 0\leq t<1.
$$
In particular, an atom of mass $\gamma(0)$ is initially allowed at zero.
The measure is locally finite, need not have finite total mass, and is not
normalised as a probability measure. Support is relative to $[0,1)$.

Let $\Phi=\Phi_\gamma$ solve the backward Parisi equation
$$
\partial_t\Phi=-\frac12\bigl(\Phi_{xx}+\gamma(t)\Phi_x^2\bigr),
\qquad \Phi(1,x)=|x|,
$$
and set
$$
\mathcal P(\gamma)=\Phi_\gamma(0,0)
                    -\frac12\int_0^1t\gamma(t)\,dt.
$$
Write $u=\Phi_x$ and $a=\Phi_{xx}$. The associated diffusion is
$$
dX_t=\gamma(t)u(t,X_t)\,dt+dB_t,\qquad X_0=0,
$$
where $B$ is standard Brownian motion. For an integrable coefficient,
the value function is defined by
$$
\Phi_\gamma(t,x)=\sup_{|\alpha|\leq1}\mathbb E\left[
 \left|x+B_1-B_t+\int_t^1\gamma(s)\alpha_s\,ds\right|
 -\frac12\int_t^1\gamma(s)\alpha_s^2\,ds\right],
$$
where the controls are progressively measurable for the Brownian increments
after $t$. It is equivalently obtained by monotone-coefficient approximation.
The control and heat-equation methods have antecedents in
[Jagannath and Tobasco (2016)][JT] at positive temperature and
[Chen, Handschy and Lerman (2018), Proposition 2 and Theorem 5][CHL]
at zero temperature. We use the estimates of
[OpenAI (2026a), Lemmas 2.1–2.2][FS]: $\Phi$ is even, convex and
one-Lipschitz in space, all its spatial derivatives are bounded and
continuous on $[0,T]\times\mathbb R$ for $T<1$, and the PDE holds
almost everywhere in time. In particular $|u|\leq1$, and
$$
0\leq\Phi_\gamma(t,x)-|x|
\leq\sqrt{2(1-t)/\pi}+\frac12\int_t^1\gamma(s)\,ds.       \tag{T}
$$
Existence and uniqueness of the diffusion, these regularity estimates,
and the variation formula below are analytic inputs from that source.

For independent standard Gaussian $J_{ij}$ and $\sigma\in\{-1,1\}^n$, put
$H_n(\sigma)=n^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j$, the
model introduced by [Sherrington and Kirkpatrick (1975)][SK].
The Parisi formula and attainment give
$$
P_*:=\lim_{n\to\infty}\frac1n\mathbb E\max_\sigma H_n(\sigma)
     =\min_{\gamma\in\mathcal U}\mathcal P(\gamma)
$$
[Auffinger and Chen (2017), Theorem 1 and proof of Lemma 3][AC].
Here $\operatorname{Cov}(H_n(\sigma),H_n(\tau))=nR^2/2-1/2$ for
overlap $R=n^{-1}\sum_i\sigma_i\tau_i$; a common centred Gaussian of
variance $1/2$ restores $n\xi(R)$ without changing the expected maximum.
<!-- /passage:model -->

<!-- passage:main-result -->
**Theorem 1 (full support; [OpenAI (2026a), Theorem 1.1][FS]).**
If $\gamma\in\mathcal U$ minimises $\mathcal P$, then
$$
\operatorname{supp}\mu_\gamma=[0,1),\qquad
\gamma(t_2)>\gamma(t_1)\quad(0\leq t_1<t_2<1).
$$
For every associated diffusion,
$$
\mathbb E[u(t,X_t)^2]=t,
\qquad \mathbb E[a(t,X_t)^2]=1
\quad(0\leq t<1).
$$

The theorem assumes a minimiser; its existence comes from the separate
attainment result. Integrability permits growth of $\gamma$ near one.
Zero field supplies the symmetry $u(0,0)=0$, and the pure-SK value
$\xi''=1$ enters the curvature calculation. No extension to nonzero field
or a general mixed-spin covariance is asserted.

Infinite support alone leaves room for gaps: the measure
$\sum_{k\geq1}2^{-k}\delta_{1-2^{-k}}$ is an example.
[Auffinger, Chen and Zeng (2020), Theorem 1][ACZ] proved infinite support;
[Chen (2026), Theorem 1.3][Chen] proved full relative support and smooth
absolute continuity. Our route is OpenAI's quantitative curvature argument.
Its second use will prove the separate positive-density Corollary 3 in §4.
The [fixed-revision Lean implementation][support-lean] and
[formal challenge][support-challenge] specify the narrower support-and-moment
interface; their [Comparator configuration][support-config] selects an
intended comparison, with the actual evidence described in §6.
<!-- /passage:main-result -->

<a id="contact"></a>

## 2. Contact and the contradiction inside a gap

<!-- passage:contact -->
Fix a minimiser and define
$$
q(t)=\mathbb E[u(t,X_t)^2],\qquad
G(s)=\int_s^1(q(t)-t)\,dt.
$$
Itô's formula gives $du(t,X_t)=a(t,X_t)\,dB_t$, hence $q(0)=0$ and
$q'(t)=\mathbb E[a(t,X_t)^2]$. The compact-time regularity makes $q'$
continuous, including across jumps of $\gamma$. The one-sided first variation is
$$
D_+\mathcal P(\gamma)[\eta]
 =\frac12\int_0^1\eta(t)(q(t)-t)\,dt
$$
for every integrable direction $\eta$ such that
$\gamma+\varepsilon\eta\in\mathcal U$ for sufficiently small
$\varepsilon\geq0$ [OpenAI (2026a), Lemma 6.1][FS]. The earlier
zero-temperature variation and support-point identities are in
[Chen, Handschy and Lerman (2018), Propositions 3–4][CHL].

Adding an atom at $s$ means taking $\eta=\mathbf1_{[s,1)}$, so
minimality gives $G(s)\geq0$. To obtain equality on the support, take a
compact $K\subset[0,1)$ and let $\nu$ be the finite restriction of
$\mu_\gamma$ to $K$. Removing a fraction of this mass is feasible and gives
$$
0\leq D_+\mathcal P(\gamma)[-\nu([0,\cdot])]
   =-\frac12\int_KG(s)\,d\mu_\gamma(s).
$$
Thus $G=0$ almost everywhere for $\mu_\gamma$, and by continuity on
$S=\operatorname{supp}\mu_\gamma$. This argument removes diffuse mass as
well as atoms; no density assumption or probability constraint is used.

At a support point $s>0$, $G$ has a minimum. Since $G'=s-q(s)$ and
$G''=1-q'$, we obtain
$$
q(s)=s,\qquad q'(s)\leq1.                         \tag{1}
$$
If $0\in S$, then $G(0)=q(0)=0$ and
$G(h)=\tfrac12(1-q'(0))h^2+o(h^2)$, so the right derivative also
satisfies $q'(0)\leq1$. These are the contact conditions of
[OpenAI (2026a), Lemma 6.2][FS].
<!-- /passage:contact -->

<a id="gap-elimination"></a>

<!-- passage:gap-proof -->
A support gap forces $\gamma$ to be constant there. The analytic estimate
that rules it out does not require minimality.

**Lemma 2 (constant-interval curvature; [OpenAI (2026a), Proposition 5.1][FS]).**
For any $\gamma\in\mathcal U$, define $q$ using its associated diffusion
as above. If $\gamma=c$ on an open interval $I\subset(0,1)$, then
$$
q'''(t)\geq\frac{c^2}{1000}\mathbb E[a(t,X_t)^4]>0
\quad(t\in I,\ c>0).                              \tag{2}
$$
Thus $q'$ is strictly convex on a positive constant interval. If $c=0$,
then $q''(t)=\mathbb E[\Phi_{xxx}(t,X_t)^2]>0$, so $q'$ is strictly
increasing there.

We first use this estimate, then explain its proof. Suppose $(\ell,r)$ is
a gap with both endpoints in $S$ and $r<1$. On a positive plateau,
strict convexity and (1) give
$$
q'(t)<\frac{r-t}{r-\ell}q'(\ell)
        +\frac{t-\ell}{r-\ell}q'(r)\leq1
\quad(\ell<t<r).
$$
Consequently $q(r)-q(\ell)<r-\ell$, contradicting contact at both
endpoints. The geometric obstruction is an area deficit under $q'$.
On a zero plateau, strict increase instead gives $q'(t)<q'(r)\leq1$
and the same contradiction. An initial gap $[0,r)$ with $r\in S$, $r<1$
and $0\notin S$
has $\gamma=0$, including no atom at zero; use $q(0)=0$ and contact at
$r$ to reach that contradiction without assuming contact at zero.

The point $1$ lies outside the support domain, so a terminal gap needs
a different argument. On a constant interval ending at one,
[OpenAI (2026a), Lemma 6.3][FS] proves
$$
1-q(t)\geq C\sqrt{1-t}
$$
for some $C>0$ and all sufficiently late $t$. In a window of width
$\sqrt{1-t}$ around the terminal cusp, $u$ stays uniformly away from
$\pm1$ and the diffusion density has a uniform positive lower bound.
Integrating $1-u^2$ over that window gives the estimate. Hence
$q(t)-t\leq(1-t)-C\sqrt{1-t}<0$ near one, contradicting $G\geq0$.
This also excludes empty support. Terminal-plateau exclusion was already
recorded by [Auffinger, Chen and Zeng (2020), Remark 7][ACZ].

These cases exhaust the components of the complement of the relatively
closed set $S$. Thus $S=[0,1)$, (1) gives $q(t)=t$ everywhere, and
differentiation gives $\mathbb E a^2=1$, including the right-hand value at
zero. Positive mass on every open interval gives
$\gamma(t_2)-\gamma(t_1)=\mu_\gamma((t_1,t_2])>0$.
This proves Theorem 1 conditional on Lemma 2 and the cited analytic inputs.
<!-- /passage:gap-proof -->

<a id="curvature"></a>

## 3. What makes the curvature positive

<!-- passage:curvature -->
On a positive plateau put $r=c\Phi_x$, $v=r_x$, $w=r_{xx}$ and
$z=r_{xxx}$. Along $X$, their drift and diffusion pairs are
$(0,v)$, $(-v^2,w)$ and $(-3vw,z)$ for $r,v,w$, respectively.
Starting from $c^2q'=\mathbb E v^2$, Itô's formula yields
$$
c^2q''=\mathbb E[w^2-2v^3],\qquad
c^2q'''=\mathbb E[z^2-12vw^2+6v^4].                \tag{3}
$$
The drift of $w^2$ is $z^2-6vw^2$; that of $v^3$ is
$3vw^2-3v^4$. The negative mixed term is the difficulty: convexity of
$\Phi$ does not give a sign for this expression.

First take a positive nondecreasing finite-step coefficient and smooth
the terminal value to $M^{-1}\log(2\cosh Mx)$, with
$M\geq\|\gamma_{\rm step}\|_\infty$; along approximation sequences
we also take $M\to\infty$. On a step of height $c$, the
diffusion density factors as $f=e^{c\Phi}g$, where $g$ solves the
forward heat equation. For the score $s=-\partial_x\log g$, the source
propagates inequalities jointly with those for $r$: on $x>0$, $r$ and
$s$ are increasing and concave, while $w/(2r)+v\leq0$ is nondecreasing
and $s/r$ is nondecreasing. The relevant ratios extend through zero.
These are analytic shape inequalities, proved in §3 of [OpenAI (2026a)][FS].
The Cole–Hopf and transformed-density methods have close antecedents in
[Lopatto (2026), Propositions 3.6, 7.1 and 9.1][Lopatto] and
[Chen (2026), §§3–4 and Appendix C][Chen];
Chen's appendix distinguishes the earlier shared estimates from the
parallel crossing proofs.

The rational certificate of [OpenAI (2026a), Lemma 4.1 and Proposition 4.2][FS]
adds a polynomial derivative correction. For its polynomial $F$, the
associated expression $\mathcal W(F)$ satisfies
$$
f\mathcal W(F)=\partial_x(rfF).
$$
After this correction the shape inequalities make the remaining weighted
squares and polynomial terms nonnegative, leaving at least $10^{-3}v^4$.
The source's tail bounds remove the derivative upon integration. Therefore
$$
\mathbb E_f[z^2-12vw^2+6v^4]
       \geq\frac1{1000}\mathbb E_f[v^4].           \tag{4}
$$
This is an integrated inequality for the specified profiles and density;
the polynomial on the left has no such sign for arbitrary $v,w,z$.

For a general integrable coefficient, positive monotone finite-step
approximants retain the plateau height $c$ near a fixed interior time.
Spatial derivatives through order four converge uniformly on compact time
strips, and the coupled diffusions converge. Only $v,w,z$ remain in (4),
so convergence of the auxiliary scores is unnecessary. Strict positivity
of $\Phi_{xx}$ gives (2). On a zero plateau, heat evolution gives the
separate formula for $q''$ in Lemma 2. It is strict at positive times
because the diffusion has a positive density and $\Phi_{xxx}$ cannot
vanish identically: a quadratic spatial profile would contradict the
one-Lipschitz bound and $|x|+O(1)$ growth.

Chen's Proposition 4.2 gives the crossing implication
$q''(t)=0\Rightarrow q'''(t)>0$ on a hypothetical positive gap of the
minimiser [Chen (2026)][Chen]. Estimate (2) is quantitative and holds
throughout each positive plateau for any admissible coefficient. The
complete sign, certificate and approximation proofs are in
[OpenAI (2026a), §§2–5][FS]; the long reasoning record, §4,
“Strict curvature on a constant interval”, explains their assembly.
<!-- /passage:curvature -->

<a id="positive-density"></a>

## 4. The same estimate makes the density positive

<!-- passage:density-consequence -->
Full support does not by itself imply a positive density at every point.
For example, the smooth increasing function
$\gamma(t)=\int_0^t(s-\tfrac12)^2\,ds$ has full Stieltjes support but
$\gamma'(\tfrac12)=0$. The source's coercive estimate rules out this
behaviour for a minimiser.

**Corollary 3 (smooth positive density; [OpenAI (2026a), Corollary 6.4][FS]).**
Under the hypotheses of Theorem 1, $\gamma(0)=0$ and
$\gamma\in C^\infty([0,1))$, with derivatives at zero understood from
the right. Moreover, $\mu_\gamma(dt)=\gamma'(t)\,dt$, and
$$
2\gamma'(t)\mathbb E[a(t,X_t)^3]
 \geq\frac{\gamma(t)^2}{1000}\mathbb E[a(t,X_t)^4]>0
\quad(0<t<1).                                    \tag{5}
$$
In particular the density is strictly positive on $(0,1)$; only
nonnegativity at zero is asserted. This is a separate manuscript result,
not a conclusion of the selected full-support formal interface.

For the proof, write $b=\Phi_{xxx}$ and $d=\Phi_{xxxx}$, evaluating
spatial factors along $X$ below. Since
$da=-\gamma a^2\,dt+b\,dB$ and $\mathbb E a^2=1$, Itô's formula gives
$$
\gamma(t)=\frac{\mathbb E b(t,X_t)^2}
                    {2\mathbb E a(t,X_t)^3}.       \tag{6}
$$
Initially the identity holds almost everywhere. Convexity gives $a\geq0$
and $\mathbb E a^3\geq(\mathbb E a^2)^{3/2}=1$. Compact-strip
continuity of the moments and right continuity of $\gamma$ extend (6)
to every time, proving continuity of $\gamma$. Evenness gives $b(0,0)=0$,
so $\gamma(0)=0$.

To bootstrap, consider all polynomial moments of finitely many spatial
derivatives at once. Itô's formula writes the derivative of each as
another polynomial moment plus $\gamma$ times a polynomial moment.
Their continuity makes them $C^1$; (6) then makes $\gamma$ $C^1$.
Repeating gives smoothness without assuming derivatives of $\gamma$
in advance. This smoothness argument is in
[Chen (2026), Proposition 4.6 and Appendix B.6][Chen]; the polynomial-moment
method is developed in [Auffinger and Chen (2015), Lemma 2 and the proof
of Theorem 2(ii)][AC-properties].

Differentiating $\mathbb E b^2=2\gamma\mathbb E a^3$ now gives
$$
2\gamma'\mathbb E a^3
  =\mathbb E[d^2-12\gamma ab^2+6\gamma^2a^4].       \tag{7}
$$
Fix $0<t<1$ and put $c=\gamma(t)>0$. Flatten $\gamma$ to $c$ on a
shrinking interval about $t$, preserving monotonicity, and approximate
by positive finite-step coefficients with that plateau. These coefficients
converge in $L^1$. With the terminal smoothings of §3, apply (4) at the fixed time, with
$(v,w,z)=(ca,cb,cd)$. The derivative and diffusion convergence on a
fixed compact strip does not depend on the shrinking plateau widths,
so the inequality passes to the original coefficient. Equations (4)
and (7) yield (5), with strictness from $\mathbb E a^4\geq1$.
The long record, §§5.1–5.2, retains the moment bootstrap and the
fixed-time approximation proving strict positivity of the density.
<!-- /passage:density-consequence -->

<a id="value-and-qaoa"></a>

## 5. The scalar value and the further circuit problem

<!-- passage:scalar-value -->
There is also a direct value consequence, which needs full support but
not the density corollary. The gradient-martingale and normalised Euler
methods occur in [Montanari (2025), §§2–3 of the cited preprint][Montanari]
and [El Alaoui, Montanari and Sellke (2021), §§5–6 of the cited preprint][EAMS].
For a minimiser and its associated diffusion, the bounded martingale
$M_t=u(t,X_t)=\int_0^t a(s,X_s)\,dB_s$ satisfies $\mathbb E M_t^2=t$.
It therefore converges almost surely and in $L^2$ to a variable $U$ with
$|U|\leq1$ and $\mathbb E U^2=1$, so $U^2=1$ almost surely.
The integrable drift bound $|\gamma u|\leq\gamma$ gives
$X_t\to X_1$ almost surely and in $L^2$.

The terminal estimate (T) and convexity imply
$u(t,x_t)\to\operatorname{sgn}(x)$ whenever $x_t\to x\ne0$:
trap the derivative between difference quotients on a small interval
that stays on one side of zero. Thus $UX_1=|X_1|$, including when
$X_1=0$. Itô's formula gives
$$
\mathbb E\Phi_\gamma(t,X_t)
=\Phi_\gamma(0,0)+\frac12\int_0^t\gamma(s)s\,ds.
$$
Using (T) to let $t\uparrow1$ and subtracting the Parisi penalty yields
$\mathcal P(\gamma)=\mathbb E|X_1|-\int_0^1t\gamma(t)\,dt$.
Multiply $X_1=B_1+\int_0^1\gamma(t)M_t\,dt$ by $U$ and use
$\mathbb E[UM_t]=\mathbb E M_t^2=t$. Boundedness and $\gamma\in L^1$
justify Fubini, so the drift cancels the penalty. Finally
$\mathbb E\int_0^1a(t,X_t)^2\,dt=1$ extends the stochastic integral
in $L^2$ to time one; its cross-isometry with $B_1$ gives
$$
P_*=\mathbb E[UB_1]
    =\int_0^1\mathbb E[a(t,X_t)]\,dt.              \tag{8}
$$
This is the first curvature moment, distinct from $\mathbb E a^2=1$;
its integrability follows by Cauchy–Schwarz. The equality with $P_*$
uses the external Parisi formula. This proves the scalar identity of
[OpenAI (2026a), Corollary 7.1][FS]; the long record, §6,
“Recovering the value from a martingale”, retains the full argument.
The [scalar-value implementation][value-lean],
[formal challenge][value-challenge] and [comparison configuration][value-config]
are separate from those for full support.

The companion finite-Gaussian approximation first refines a mesh on
$[0,T]$ at fixed $0<T<1$, then sends $T\uparrow1$. Its scalar Gaussian
correlations are not themselves circuit energies
[OpenAI (2026a), Proposition 7.2][FS]; see the long record, §7,
“A finite Gaussian spin and its adjacent correlations”.
The order also gives a finite accuracy choice: since $a\geq0$ and
$\mathbb E a^2=1$,
$$
0\leq P_*-\int_0^T\mathbb E[a(t,X_t)]\,dt\leq1-T.
$$
For $0<\varepsilon<1$, choose $T=1-\varepsilon/2$, then a finite mesh
whose coefficient sum differs from the fixed-$T$ integral by less than
$\varepsilon/2$. This provides a finite scalar approximation within
$\varepsilon$, without specifying a mesh rate or a coupled cutoff schedule.
<!-- /passage:scalar-value -->

<!-- passage:qaoa-boundary -->
The quantum approximate optimisation algorithm of
[Farhi, Goldstone and Gutmann (2014)][FGG] alternates cost-Hamiltonian
evolution and transverse-field mixing from the uniform superposition.
At depth $p$, let $v_p(\boldsymbol\theta,\boldsymbol\beta)$ be its
limiting disorder-averaged energy per spin, with deterministic cost and
mixer angles held fixed as $n\to\infty$. This limit and fixed-parameter
concentration are due to [Farhi, Goldstone, Gutmann and Zhou (2022)][FGGZ].
Their minimum-energy convention becomes the maximum-energy convention
here by symmetry of the disorder and reversal of the cost angles.
Put
$$
Q_p=\sup_{\boldsymbol\theta,\boldsymbol\beta\in\mathbb R^p}
v_p(\boldsymbol\theta,\boldsymbol\beta).
$$
The further theorem of [OpenAI (2026b), Theorem 1.1][Q] asserts
$\lim_{p\to\infty}Q_p=P_*$, the eventual-optimality conclusion
conjectured by [Basso et al. (2022), §7, equation (7.2) of the full
preprint][BFMVZ]. Equivalently, for every $\varepsilon>0$ there are a
finite depth and deterministic angles, independent of both $n$ and the
disorder, whose limiting expected energy is at least $P_*-\varepsilon$.
The depth and angles may depend on $\varepsilon$. The system-size limit
is taken at that fixed circuit before improving the accuracy; the theorem
provides no quantitative depth bound, finite-size rate or efficient
angle-selection procedure.

The concentration result also turns the expected-energy conclusion into
a sampling statement. Choose the word to attain $P_*-\varepsilon/2$.
Its first and second energy moments converge to $v_p$ and $v_p^2$,
so a measured energy per spin is at least $P_*-\varepsilon$ with
probability tending to one jointly over disorder and quantum measurement.
The long record, §9.8, gives the mean-square and Markov argument; this
consequence still supplies no convergence rate or every-instance guarantee.

The scalar Gaussian correlations above do not yet provide such a circuit.
OpenAI constructs a rooted representation of the Gaussian calculation,
synthesises it with quantum controls, removes temporary longitudinal seed
controls, and transfers one fixed finite circuit to SK. It also gives a
positive-temperature construction with different classical input. The
long record, §9, “From the scalar formula to one ordinary QAOA word”,
reconstructs these additional arguments and their antecedents; the originals
are [OpenAI (2026b), §§2–6 and Appendix A][Q].
<!-- /passage:qaoa-boundary -->

<a id="evidence-scope"></a>

## 6. Source and verification scope

<!-- passage:evidence-scope -->
This AI-assisted draft reconstructs existing results credited to
OpenAI and the cited authors. The main mathematical work is the integrated
coercivity estimate: variation turns it into full support, and saturated
moments turn it into positive density. Neither this reconstruction nor
its finite algebra check establishes a new theorem.

The selected formal support statement includes measure and diffusion
existence, support, strict increase and both moment identities for every
associated diffusion, conditional on a minimiser. The separate scalar
statement assumes a minimiser and an associated diffusion for its scalar
and finite-Gaussian clauses; its ground-state/Parisi equality assumes only
the minimiser. Neither statement includes Corollary 3 or QAOA convergence.

Source-integrity checks passed. After an earlier unavailable Comparator
startup, a later recorded attempt built and exported the admitted
full-support challenge, then failed to build the implementing solution
because an imported compiled object was missing. No successful corrected
replay or completed scalar-target replay is recorded. Challenge export,
tool-fixture success and the exact polynomial calculation establish no
research-target acceptance, transitive axiom audit or independent human
review. Exact versions, the partial attempt and remaining obligations are
retained in the companion source review.
<!-- /passage:evidence-scope -->

## References

- OpenAI (2026a). *Full support of the zero-temperature Sherrington–Kirkpatrick
  order parameter*. 27 September 2026. [Manuscript][FS], fixed revision.
  Theorem 1.1; §§2–6; Corollaries 6.4 and 7.1; Proposition 7.2.
- OpenAI (2026b). *QAOA attains the SK ground-state energy in the
  thermodynamic-first limit*. 25 September 2026. [Manuscript][Q], fixed
  revision. Theorem 1.1; §§2–6 and Appendix A.
- Auffinger, A. and Chen, W.-K. (2017). “Parisi formula for the ground
  state energy in the mixed $p$-spin model.” *Annals of Probability*
  **45**, 4617–4631. [Preprint v2][AC]: Theorem 1 and proof of Lemma 3.
- Auffinger, A., Chen, W.-K. and Zeng, Q. (2020). “The SK model is
  infinite step replica symmetry breaking at zero temperature.”
  *Communications on Pure and Applied Mathematics* **73**, 921–943.
  [Preprint v2][ACZ]: Theorem 1 and Remark 7.
- Chen, H.-B. (2026). *FRSB in the SK spin glass: convergence to
  full-interval support at zero temperature*. [Version 1][Chen],
  20 July 2026. Theorem 1.3; Propositions 4.2 and 4.6; Appendices B.6 and C.
- Lopatto, P. (2026). *Full replica symmetry breaking in the
  Sherrington–Kirkpatrick model*. [arXiv version 3][Lopatto], submitted
  16 July 2026. Propositions 3.6, 7.1 and 9.1; related Cole–Hopf, density
  and crossing arguments.

- Sherrington, D. and Kirkpatrick, S. (1975). “Solvable Model of a Spin-Glass.”
  *Physical Review Letters* **35**, 1792–1796. [Original model][SK].
- Jagannath, A. and Tobasco, I. (2016). “A dynamic programming approach
  to the Parisi functional.” *Proceedings of the AMS* **144**, 3135–3150.
  [Preprint v4][JT]. Positive-temperature control methods.
- Chen, W.-K., Handschy, M. and Lerman, G. (2018). “On the energy
  landscape of the mixed even $p$-spin model.” *Probability Theory and
  Related Fields* **171**, 53–95. [Preprint v4][CHL]: Proposition 2,
  Theorem 5, Lemma 3 and Propositions 3–4.
- Auffinger, A. and Chen, W.-K. (2015). “On properties of Parisi
  measures.” *Probability Theory and Related Fields* **161**, 817–850.
  [Preprint v1][AC-properties]: Lemma 2 and proof of Theorem 2(ii).
- Montanari, A. (2025). “Optimization of the Sherrington–Kirkpatrick
  Hamiltonian.” *SIAM Journal on Computing* **54**, FOCS19-1–FOCS19-38.
  [Preprint v2, 2019][Montanari]: §§2–3.
- El Alaoui, A., Montanari, A. and Sellke, M. (2021). “Optimization of
  mean-field spin glasses.” *Annals of Probability* **49**, 2922–2960.
  [Preprint v1][EAMS]: §§5–6.
- Farhi, E., Goldstone, J. and Gutmann, S. (2014). *A Quantum Approximate
  Optimization Algorithm*. [Preprint v1][FGG]. Algorithm definition;
  §VI concerns the fixed-instance depth limit.
- Farhi, E., Goldstone, J., Gutmann, S. and Zhou, L. (2022). “The Quantum
  Approximate Optimization Algorithm and the Sherrington–Kirkpatrick
  Model at Infinite Size.” *Quantum* **6**, 759. [Preprint v4][FGGZ].
- Basso, J., Farhi, E., Marwaha, K., Villalonga, B. and Zhou, L. (2022).
  “The Quantum Approximate Optimization Algorithm at High Depth for
  MaxCut on Large-Girth Regular Graphs and the Sherrington–Kirkpatrick
  Model.” *TQC 2022*, 7:1–7:21. [Full preprint v3][BFMVZ]: transfer
  theorem and §7, equation (7.2); the full preprint has separate numbering.


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
