
<!-- passage:front -->
# From a recurrent profile to unforced Navier–Stokes blow-up

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · **specialist digest** · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](cell-layer-fidelity.md) · [certificate checker](certificate-checker.md)

**A specialist digest of the paper by Levent Alpöge and Tristan Buckmaster**  
20 November 2026 · Lean at commit [`ad53419`](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546)
<!-- /passage:front -->

## One-page summary

<!-- passage:sec-one-page-summary -->

**The result and its premise.** The paper's Theorem 1.1 starts with a smooth, nonzero solution of the backward similarity equation, periodic in logarithmic time up to an orthogonal transformation, with $|W|\lesssim(1+|y|)^{-1}$ and $|\nabla W|\lesssim(1+|y|)^{-2}$. Write $u_1^*$ for this profile in physical variables with terminal time one. The theorem constructs smooth compactly supported solenoidal data on $\mathbb R^3$ whose unforced Navier–Stokes solution has bounded kinetic energy and blows up at time one, with

$$
\|\nabla u(t)\|_2\asymp(1-t)^{-1/4},\qquad
\|\nabla(u-u_1^*)(t)\|_2\lesssim(1-t)^{\kappa-1/4},\quad 0<\kappa<\tfrac14.
$$

It also constructs smooth data on $\mathbb T^3$ with the analogous $H^1$ rate and local profile convergence. Positive viscosity is arbitrary by scaling. Theorem 7.1 supplies the required profile from a certificate; Corollary 7.2 composes the two implications. The central steps are the use of time dependence beyond the stationary-profile setting, the passage from a potentially infinite-energy profile to compact initial data, and the removal of every localization force on the torus. [Paper, Theorems 1.1 and 7.1, pp. 3, 35.]

**The strategy in six sentences.** Work in $X=\dot H^1_{\mathrm{div}}$, where the heat evolution after restoring similarity scale contracts by $e^{-S/4}$. The linearized evolution over a period is a compact perturbation of this contraction, leaving only finitely many directions that obstruct a chosen decay rate. A Lyapunov–Perron construction removes those directions by changing the datum in a finite-dimensional space of compactly supported fields, and a contraction solves the nonlinear perturbation problem. Cutting off a vector potential supplies finite-energy initial data, while a transferred right inverse and a second correction give an exact unforced solution on a large torus. Separately, a bordered linear problem, quantitative error bounds and a parameter fixed point turn an approximate profile into an exact one with zero auxiliary force. Regularization supplies the smooth decaying profile, and Appendix B reduces the required universal operator bounds to cell, mode, tail and matrix conditions on finitely represented data.

**What the evidence establishes.** The paper proves the two conditional analytic implications. Named Lean declarations below support corresponding conditional results; internal statements retain substantial quantitative content, although the public exports omit parts of the paper's full conclusions. The package builds, and the authors' axiom script reports only the three standard axioms for its 27 names; Lean's Comparator, with four further checkers, accepts all 15 selected theorems and rejects a control ([§5 of the statement comparison](paper.md#5-checking-workflow-and-status)). The authors report a separate 128-bit Arb/FLINT verification of the concrete certificate. **The pinned release supplies neither that certificate nor its checking program.** Its published SHA-256 identifies intended bytes; it does not discharge the numerical premise. [Paper, pp. 4, 9–10, 70; authors' README.]
<!-- /passage:sec-one-page-summary -->

# The argument

<!-- passage:sec-the-argument -->

**Reading conventions.** Sections 1–6 explain profile $\Rightarrow$ blow-up; §§7–12 explain certificate $\Rightarrow$ profile and its finite reduction; §13 identifies the remaining computational premise. Paper numbers refer to the 79-page version in the authors' repository. Lean anchors refer to source at `ad53419de079eb8f95f60313473374624a348546`; abbreviated paths beginning `Profile/`, `Transfer/`, `Torus/`, `Cert/` and similar lie under `lean/Breakdown/`. “Formal anchor” identifies a definition or proved result used at the indicated step; the accompanying comparisons specify which mathematical claims it supports. Each Lean path links to the cited lines.

The symbol $\lesssim$ allows constants fixed by the profile and chosen analytic parameters; such constants are independent of time and, in the torus comparison, of a sufficiently large period $L$. Numerical certificate constants are displayed explicitly. We write $\mathcal M$ for the monodromy operator, reserving $M$ for the certificate's correction bound.
<!-- /passage:sec-the-argument -->

<a id="1"></a>

## 1. The input orbit and the actual conclusion

<!-- passage:sec-1 -->

The analytic half of the argument starts with a profile; it does not construct one. Let $S>0$, $R\in O(3)$ and let $(W,q)$ be a smooth, nonzero solution on $\mathbb R\times\mathbb R^3$ of

$$
\partial_sW+\tfrac12W+\tfrac12(y\cdot\nabla)W-\Delta W+(W\cdot\nabla)W+\nabla q=0,
\qquad \nabla\cdot W=0,
$$

with $W(s+S,y)=RW(s,R^{-1}y)$ and uniform bounds $|W|\lesssim(1+|y|)^{-1}$, $|\nabla W|\lesssim(1+|y|)^{-2}$. For a chosen terminal time $T$, define

$$
s=\log\frac{T}{T-t},\qquad y=\frac{x}{\sqrt{T-t}},\qquad
u_T^*(t,x)=(T-t)^{-1/2}W(s,y).
$$

The transformed pressure is $(T-t)^{-1}q(s,y)$. Substitution gives the unforced viscosity-one Navier–Stokes equations. With $\lambda=e^{-S}$, one similarity period corresponds to $t\mapsto T-\lambda(T-t)$ and spatial contraction by $\sqrt\lambda$.

The profile is recurrent in logarithmic time, rather than stationary. This distinction is necessary: a stationary profile in the stated $L^6$ class is excluded by the classical nonexistence theory recalled in the paper. The $1/|y|$ upper bound permits an infinite-energy tail and does not supply strong $L^3$ control; it does not, by itself, prove that either norm diverges. What is supplied is membership in the space used below.

Theorem 1.1 asserts considerably more than existence of this possibly infinite-energy solution. It constructs $u_0\in C^\infty_{c,\mathrm{div}}(\mathbb R^3)$ and a smooth, uniformly finite-energy solution on $[0,1)$ for which, for some $0<\kappa<1/4$,

$$
c(1-t)^{-1/4}\le\|\nabla u(t)\|_2\le C(1-t)^{-1/4},
\qquad
\|\nabla(u-u_1^*)(t)\|_2\le C(1-t)^{\kappa-1/4}.
$$

It also constructs smooth data on the unit torus and a solution blowing up at some $T\in(0,1]$, with the same two-sided $H^1$ rate and the local estimate

$$
\|u_{\mathrm{per}}(t)-u_T^*(t)\|_{H^1(B_{1/16})}
\le C(T-t)^{\kappa-1/4}.
$$

These error bounds allow the physical error to grow. Multiplication by $(T-t)^{1/4}$ shows that its size relative to the profile tends to zero. In similarity variables the convergence is exponential, at rate $e^{-\kappa s}$. The torus comparison is local in physical space; that fixed physical ball expands to exhaust $\mathbb R^3$ in similarity coordinates.

**Paper:** §1.1, (1.2)–(1.7), pp. 2–3. **Formal anchor:** `Breakdown.profileOrbit_holds`, [`Profile/Orbit.lean:39–41`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Orbit.lean#L39-L41), constructs the abstract recurrent orbit from the formal smooth-profile premise. The public conclusions `Breakdown.breakdown_on_space` and `Breakdown.breakdown_on_torus` in [`Solution.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean) exclude global smooth solutions in specified classes: uniformly finite-energy solutions on the whole space, and solutions with periodic velocity on the torus. They do not themselves state the displayed quantitative bundle. The formal profile premise writes additional second-derivative and pressure-gradient decay assumptions. Remark 1.2 supplies the higher spatial derivative bound. A pressure-normalization argument gives the gradient bound: the difference from the Riesz-transform pressure is harmonic, and testing in time makes it decay at infinity without assuming a bound on the time derivative. This is an analytic bridge, not yet a Lean declaration.
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. Why the space is homogeneous $H^1$

<!-- passage:sec-2 -->

Set

$$
X=\dot H^1_{\mathrm{div}}(\mathbb R^3)
=\{f\in L^6(\mathbb R^3;\mathbb R^3):\nabla f\in L^2,
\ \nabla\cdot f=0\},\qquad \|f\|_X=\|\nabla f\|_2.
$$

The $L^6$ representative is part of the definition; it removes the constant-field ambiguity of the homogeneous seminorm. The Lean represents $X$ as a closed Fourier-space submodule and recovers its $L^6$ velocity through a continuous linear map. The profile bounds give $W(s)\in X$ uniformly in $s$. Smooth compactly supported solenoidal fields are dense in $X$, an assertion used twice: to approximate the initial profile, and to represent its finite-dimensional correction directions by compact fields.

Write $D_\mu f(x)=\sqrt\mu f(\sqrt\mu x)$ and $\rho_Rf(x)=Rf(R^{-1}x)$. A change of variables gives

$$
\|D_\mu f\|_X=\mu^{1/4}\|f\|_X,
\qquad \|\rho_Rf\|_X=\|f\|_X.
$$

That quarter-power is the structural reason for choosing $X$. It yields a strict contraction for the free flow after each backward similarity period, while allowing the profile's slow spatial decay.

Eliminate pressure using the Leray projection $\mathbb P$ and put

$$
K(\tau)(u,v)=-\tfrac12e^{\tau\Delta}\mathbb P
\big[(u\cdot\nabla)v+(v\cdot\nabla)u\big].
$$

The key analytic estimate is

$$
\|K(\tau)(u,v)\|_X
\le C\tau^{-3/4}\|u\|_X\|v\|_X.
$$

Indeed $(u\cdot\nabla)v\in L^{3/2}$, with norm bounded by $\|u\|_6\|\nabla v\|_2$, and heat–Leray smoothing maps $L^{3/2}$ to $\dot H^1$ with factor $\tau^{-3/4}$. The exponent is integrable at zero, so the Duhamel term defines a continuous $X$-valued function:

$$
u(t)=e^{(t-a)\Delta}u(a)
+\int_a^tK(t-t')(u(t'),u(t'))\,dt'.
$$

This supplies local mild existence, uniqueness and bounded linearized evolution on compact time intervals. The smooth physical profile satisfies the divergence-free weak identity; the weak-to-mild result then places it in this same framework. Pressure has not been ignored: it is incorporated through $\mathbb P$.

**Hard point:** the proof needs the exact homogeneous space, not an informal homogeneous norm on arbitrary fields. On a bounded ball its $L^6$ control gives an $L^2$ bound; this is what permits local Rellich compactness in the next step.

**Paper:** §§2.1, 3.1–3.5, pp. 10–15; Lemmas 3.1 and 3.3–3.6; Appendix A.1, pp. 47–48. **Formal anchors:** `Breakdown.Freq.bilin_holds`, [`FreqTr/Realization.lean:95–96`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L95-L96); `Breakdown.Freq.testDense_holds`, lines 68–71; `Breakdown.physicalMild_unconditional`, [`Profile/Orbit.lean:22–30`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Orbit.lean#L22-L30). [`Base/Framework.lean:9–29`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L9-L29) records the abstract heat, dilation, bilinear and compactness properties, subsequently instantiated by the Fourier realization.
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. A spectral split without a numerical spectrum

<!-- passage:sec-3 -->

Normalize $T=1$, set $t_1=1-\lambda$, and let $h_\chi$ solve the linearized equation about $u^*=u_1^*$ on the first physical period:

$$
h_\chi(t)=e^{t\Delta}\chi
+2\int_0^tK(t-t')(u^*(t'),h_\chi(t'))\,dt'.
$$

The monodromy operator compares perturbations after restoring scale and orientation:

$$
\mathcal M\chi=\rho_R^{-1}D_\lambda h_\chi(t_1),\qquad
\mathcal M_0=\rho_R^{-1}D_\lambda e^{t_1\Delta},
\qquad \|\mathcal M_0\|\le\lambda^{1/4}=e^{-S/4}<1.
$$

The decisive assertion is that $\mathcal M-\mathcal M_0$ is compact. For fixed $\tau>0$ and $u\in X$, the map $v\mapsto K(\tau)(u,v)$ is compact. To see the mechanism, approximate $u$ in $X$ by a compactly supported smooth coefficient $\phi$. A weakly null bounded sequence in $X$ tends strongly to zero in $L^2$ on the support of $\phi$, by Rellich. Positive-time smoothing of $\operatorname{div}(\phi\otimes v+v\otimes\phi)$ then gives strong convergence in $X$. The bilinear bound controls the coefficient-approximation error uniformly in $v$. This is the paper's physical-space argument. The Lean first proves compactness for coefficients in the dense test space through frequency truncation and total boundedness.

There is a second compactness issue: the monodromy contains an integral up to a singular time endpoint. If $\chi_k\rightharpoonup0$ in $X$, then $h_{\chi_k}(t')\rightharpoonup0$ at each fixed time, since the linear evolution is bounded. For $t'<t_1$, the compact coefficient operator sends this sequence strongly to zero. Its norm is bounded by

$$
C(t_1-t')^{-3/4}\sup_k\|\chi_k\|_X,
$$

which is integrable. Dominated convergence proves compactness of the integrated perturbation. Merely calling it an integral of compact operators would leave this endpoint unaccounted for. The Lean cuts off a terminal interval, bounds its contribution by $O(\varepsilon^{1/4})$, and extends compactness from simple coefficient paths by density.

Compact perturbation theory now gives $r_{\mathrm{ess}}(\mathcal M)\le e^{-S/4}$. Choose a circle $|z|=\Theta$, with $e^{-S/4}<\Theta<1$, missing the spectrum. The spectrum outside it consists of finitely many eigenvalues of finite algebraic multiplicity. Its Riesz projection $P_u$ is real, finite rank and commutes with $\mathcal M$. On its range $\mathcal M_u$ is invertible, and

$$
\sum_{n\ge0}\Theta^{-n}\|\mathcal M^n(I-P_u)\|
+\sum_{n\ge0}\Theta^n\|\mathcal M_u^{-n}P_u\|<\infty.
$$

No eigenvalues have been calculated. The finite exceptional space includes every direction that obstructs the selected decay rate, including neutral and slowly decaying directions; calling it simply the growing eigenspace would be misleading. Jordan blocks cause no additional hypothesis because the spectral gaps give the displayed summability. The exported Lean dichotomy gives power bounds at two separated radii and surjectivity on the exceptional range; the weighted sums follow from those bounds.

**Paper:** Lemma 3.2, p. 14; §§4.3–4.4, Lemmas 4.4–4.5, pp. 18–20. **Formal anchors:** `Breakdown.Freq.bilinCompact_holds`, [`FreqTr/Realization.lean:116–119`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L116-L119); `Breakdown.monodromy`, [`Transfer/Exports.lean:47`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L47), whose type `MonodromyStatement` records compact perturbation and the free bound in [`StatementsFrame.lean:71–88`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/StatementsFrame.lean#L71-L88); `Breakdown.dichotomyHolds`, [`Spectral/RealDichotomy.lean:151`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/RealDichotomy.lean#L151). The source uses subdivided time periods and an abstract dichotomy; these are supporting formal declarations, not a claim that the revised paper follows their proof line for line.
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. Compact corrections and the infinite-time boundary condition

<!-- passage:sec-4 -->

Let $\Theta=e^{-\kappa S}$, so $0<\kappa<1/4$, and define

$$
\|v\|_\kappa=\sup_{0\le t<1}(1-t)^{1/4-\kappa}\|v(t)\|_X.
$$

The linear problem asks for both a perturbation $v$ and an initial-data correction $\gamma$:

$$
v-2B(u^*,v)-e^{t\Delta}\gamma=g,
\qquad
B(f,h)(t)=\int_0^tK(t-t')(f(t'),h(t'))\,dt'.
$$

After scaling the successive intervals $[1-\lambda^n,1-\lambda^{n+1}]$ back to the first, let $v_n,g_n$ denote the rescaled fields and set $\chi_n=v_n(0)-g_n(0)$. Thus $\chi_0=\gamma$, and the equation becomes a forced recurrence

$$
\chi_{n+1}=\mathcal M\chi_n+f_n,\qquad
\|f_n\|_X\le C\Theta^n\|g\|_\kappa.
$$

This is a boundary-value problem at infinity on the exceptional components. Their unique decaying choice is

$$
P_u\gamma=-\sum_{m\ge0}\mathcal M_u^{-(m+1)}P_uf_m.
$$

The crucial choice is where $\gamma$ lives. Density and finite-dimensionality let one select a space $E\subset C^\infty_{c,\mathrm{div}}$ such that $P_u|_E:E\to\operatorname{ran}P_u$ is an isomorphism. Thus $E$ is a compactly supported transversal. It need not be invariant, and its elements need not be eigenfunctions. This bypasses every question about eigenfunction decay at spatial infinity.

The resulting recurrence is explicitly

$$
P_u\chi_n=-\sum_{m\ge n}\mathcal M_u^{-(m-n+1)}P_uf_m,
$$

$$
(I-P_u)\chi_n=\mathcal M^n(I-P_u)\gamma
+\sum_{m<n}\mathcal M^{n-1-m}(I-P_u)f_m.
$$

The stable initial term must be retained because $E$ is a transversal, not the spectral range. The spectral sums bound both expressions by $C\Theta^n\|g\|_\kappa$. Returning to continuous time yields a bounded right inverse $\mathcal R:g\mapsto(\gamma,v)$, with

$$
\max\{\|\gamma\|_X,\|v\|_\kappa\}\le C_{\mathcal R}\|g\|_\kappa.
$$

The nonlinear argument now has a standard shape, but depends on the weighted estimate. The relevant convolution is bounded because

$$
\int_0^t(t-t')^{-3/4}(1-t')^{\kappa-1/2}\,dt'
\le C(1-t)^{\kappa-1/4};
$$

after $t-t'=(1-t)\theta$, the remaining integral is controlled by $\int_0^\infty\theta^{-3/4}(1+\theta)^{\kappa-1/2}\,d\theta<\infty$. Here one of the two factors $(1-t')^\kappa$ has been bounded by $1$. Hence $\|B(v,v')\|_\kappa\le C\|v\|_\kappa\|v'\|_\kappa$. For a small prescribed datum displacement $\chi$, applying $\mathcal R$ to $e^{t\Delta}\chi+B(v,v)$ is a contraction on a small ball. The fixed point gives $u=u^*+v$ with initial datum $u^*(0)+\chi+\gamma$.

The exceptional directions are removed by choosing data. The proof neither assumes spectral stability nor claims that every nearby datum blows up. Proposition 2.1 states that every sufficiently close datum can be corrected in the one fixed space $E$; the time, centre and phase are held fixed.

**Our inference: a translation check.** Spatial translations already force at least three exceptional directions. Differentiating the recurrence for $h_a=(a\cdot\nabla)u^*$ gives $\mathcal M h_a(0)=e^{S/2}h_{R^{-1}a}(0)$. If $h_a(0)=0$ for a nonzero $a$, the slice is constant on every line parallel to $a$. A nonzero field with that property cannot belong to $L^6(\mathbb R^3)$, so $a\mapsto h_a(0)$ is injective. These three multipliers have modulus $e^{S/2}>1$, hence $\dim E\ge3$. This short deduction does not compute the remaining codimension or add a hypothesis to the proof. [Paper (4.2), (4.10).]

**Paper:** Proposition 4.3 and its proof, pp. 18, 20–21; Lemmas 4.6–4.8, pp. 19–22; Proposition 2.1, p. 11. **Formal anchors:** `Breakdown.exists_section`, [`Transfer/Section.lean:31`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Section.lean#L31); `Breakdown.periodicInverse`, [`Transfer/Exports.lean:49`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L49); `Breakdown.stepData`, lines 51–52; `Breakdown.contraction`, [`Transfer/Contraction.lean:45`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Contraction.lean#L45); `Breakdown.transferHolds_of_dichotomy`, [`Transfer/Exports.lean:54–55`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L54-L55). Its conclusion `TransferHolds`, [`Base/Framework.lean:66–73`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Base/Framework.lean#L66-L73), retains a compact-data orbit and quantitative rescaled convergence. The paper's full corrected-data family has not been identified as one fully matching exported theorem.
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. Finite energy and the lower blow-up bound

<!-- passage:sec-5 -->

To produce compact data explicitly, cut off a vector potential, rather than multiplying the velocity by a scalar cutoff. With $\eta=1$ on $B_{1/2}$ and supported in $B_1$, put

$$
A(t,x)=\int_0^1\sigma\,u^*(t,\sigma x)\times x\,d\sigma,
\qquad \bar u(t)=\operatorname{curl}\big(\eta(x/r)A(t,x)\big).
$$

The identity $\operatorname{curl}A=u^*$ follows by integrating the derivative of $\sigma^2u^*(t,\sigma x)$. Thus $\bar u$ is solenoidal, agrees with $u^*$ on $B_{r/2}$, and vanishes outside $B_r$. The far-field bounds give $|A|\lesssim1$, $|\nabla A|\lesssim|x|^{-1}$. Consequently

$$
\|\bar u(t)-u^*(t)\|_X\lesssim r^{-1/2},
\qquad \|\bar u(t)\|_2\lesssim r^{1/2},
$$

uniformly before time one. The square of the first estimate comes from $r^{-4}$ times the cutoff shell's volume and $\int_r^\infty\rho^{-4}\rho^2\,d\rho$. Choose $r$ large enough that $w_0=\bar u(0)$ satisfies $\|w_0-u^*(0)\|_X$ within the perturbative tolerance. The datum is close to the profile; it need not have small norm itself. The correction $\gamma\in E$ preserves smooth compact support.

Only the initial datum is truncated in this whole-space construction. The exact background still has its original tail. Smallness in $X$ does not imply smallness in $L^2$; finite energy of the corrected solution comes instead from smooth compact initial data, local classical $H^1$ theory, uniqueness with the constructed mild trajectory, continuation on every $[0,b]$, $b<1$, and the energy identity. In particular $\|u(t)\|_2\le\|u_0\|_2$ throughout the interval.

For the lower rate, nonzero recurrence supplies a positive lower bound for the orbit norm, not just an upper bound. If one slice vanished, mild uniqueness would force all later slices to vanish, and recurrence would force the entire orbit to vanish. Continuity on one compact period therefore gives $\inf_s\|W(s)\|_X>0$. Dilation gives $\|u^*(t)\|_X\asymp(1-t)^{-1/4}$; choosing the perturbation smaller than half its lower coefficient gives the same two-sided rate for $u$. Squared, that rate is $(1-t)^{-1/2}$, which is integrable in time, so there is no conflict with finite total energy dissipation.

**Paper:** Lemma 4.2, p. 17; Lemma 5.1 and §5.2, pp. 23–24; Lemma 2.3, pp. 11–12, and Appendix A.2, pp. 48–49. **Formal anchors:** `Breakdown.orbitBound` and `Breakdown.orbitNorm`, [`Transfer/OrbitNorm.lean:60`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/OrbitNorm.lean#L60) and [`Transfer/Exports.lean:41`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Transfer/Exports.lean#L41); `Breakdown.mildRegular_realization`, [`Uniqueness/Space.lean:19–22`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Space.lean#L19-L22); `Breakdown.breakdownOnSpace_of_profile`, lines 24–26. The abstract transfer and regularity library contain substantial construction data. Our [Theorem 1.1 wrapper](https://github.com/wcook04/proof-reader/tree/claude/navier-stokes-20261120/lean-wrappers/navier-stokes/theorem11) states the whole printed result in physical terms and proves, with only the standard axioms, the two-sided rate and the rescaled convergence for one fixed compact datum on every compact time interval before blow-up; one solution on all of $[0,1)$ with one energy bound is still to be proved.
<!-- /passage:sec-5 -->

<a id="6"></a>

## 6. The torus: make the localization error disappear

<!-- passage:sec-6 -->

A large torus is convenient because the blow-up core can be kept far from its periodic copies. Let $L\gg1$, truncate the evolving profile at $r=L/8$ by the vector-potential construction, and periodize:

$$
u^a(t)=\Pi_L\bar u(t),\qquad
\Pi_Lf=\sum_{j\in\mathbb Z^3}f(\cdot-Lj).
$$

It agrees with $u^*$ on $B_{L/16}$. A compactly supported solenoidal field has zero integral, since $f=\operatorname{div}(x\otimes f)$, so its periodization lies in the mean-zero periodic homogeneous $H^1$ space. This removes the constant mode and gives Sobolev estimates independent of $L$ in the paper's argument. Lean instead works on the unit torus in an inhomogeneous Fourier $H^1$ space with weight $1+4\pi^2|k|^2$; its ambient space does not impose zero mean.

Write $Q_L=[-L/2,L/2]^3$, and let $\Delta_T$, $\mathbb P_T$ and $B_T$ be the periodic Laplacian, Leray projection and Duhamel bilinear map on this torus. Periodization does not commute exactly with the whole-space nonlinear flow. The required estimate uses the Oseen kernel, incorporating the Leray projection and hence nonlocal pressure. Its derivatives satisfy $|\nabla O_t(x)|\lesssim|x|^{-4}$, $|\nabla^2O_t(x)|\lesssim|x|^{-5}$ uniformly in positive time. Summing over nonzero lattice images and integrating over one period cell gives, for a compact tensor $F$ supported in $B_{L/8}$,

$$
\|\nabla g\|_{L^2(Q_L)}+\|g\|_{L^6(Q_L)}
\lesssim L^{-7/2}\|F\|_1,
\quad
g=e^{t\Delta_T}\mathbb P_T\operatorname{div}\Pi_LF
-e^{t\Delta}\mathbb P\operatorname{div}F.
$$

Writing a compact solenoidal velocity as a divergence similarly gives a heat-flow discrepancy $O(L^{-5/2}\|f\|_1)$. Here $\|\bar u\|_2^2\lesssim L$ and $\|\bar u(0)\|_1\lesssim L^2$, so the nonlinear and initial-data discrepancies are $O(L^{-5/2})$ and $O(L^{-1/2})$. Together with the cutoff error, the Duhamel residual of $u^a$ satisfies $\|F^a\|_\kappa\lesssim L^{-1/2}$.

The harder issue is an inverse for the equation linearized about $u^a$. There is no exact periodic recurrent background and no new torus monodromy to calculate. Instead use the fact that the background coefficient is supported inside $B=B_{L/8}$. Its interaction with a perturbation depends only on that perturbation's restriction to $B$. Measure restrictions by

$$
\|\zeta\|_B=\|\nabla\zeta\|_{L^2(B)}+\|\zeta\|_{L^6(B)},
$$

so constants remain independent of $L$. Let $\mathcal A$ and $\mathcal A_T$ be the time-integrated linear interactions with $\bar u$ and its periodization. The kernel comparison yields $\| (\mathcal A_T\zeta-\mathcal A\zeta)|_B\|_\kappa\lesssim L^{-2}\|\zeta\|_\kappa$.

Given a periodic source $g$, solve on the whole space using the already constructed right inverse:

$$
(\gamma,v)=\mathcal R\big(\mathcal A(g|_B)\big),\qquad
\zeta=g|_B+v|_B,\qquad
z=g+\mathcal A_T\zeta+e^{t\Delta_T}\Pi_L\gamma.
$$

For $\mathcal L_T(\gamma,z)=z-2B_T(u^a,z)-e^{t\Delta_T}\Pi_L\gamma$, its defect is exactly $\mathcal A_T(\zeta-z|_B)$. The difference inside this expression has three sources: periodic kernel mismatch, the mismatch of the compact correction's free evolution, and replacing $u^*$ by $\bar u$. Their bounds are respectively $O(L^{-2})$, $O(L^{-5/2})$ and $O(L^{-1/2})$. Thus the resulting approximate inverse $\mathcal R^a$ satisfies

$$
\|\mathcal L_T\mathcal R^a-I\|\lesssim L^{-1/2},
\qquad \|\mathcal R^a\|\lesssim1.
$$

For large $L$ the Neumann series

$$
\mathcal R_T=\mathcal R^a\sum_{n\ge0}(I-\mathcal L_T\mathcal R^a)^n
$$

is an exact bounded right inverse. The same nonlinear contraction now removes $F^a$, producing an exact unforced periodic solution. Separate smallness choices keep the inverse bounded, make the nonlinear contraction valid, and preserve the positive lower blow-up rate. A truncated profile with its residual retained as a force would not establish this conclusion; the exact correction is the substantive step.

Finally, $u_{\mathrm{per}}(t,x)=L u(L^2t,Lx)$ scales the period to one and gives $T=L^{-2}$. The gradient norm gains $L^{1/2}$, exactly cancelling the time-scale factor: $L^{1/2}(1-L^2t)^{-1/4}=(T-t)^{-1/4}$. The comparison region becomes $B_{1/16}$. Smoothness and periodic pressure follow from the periodic local theory.

**Paper:** §6, pp. 24–29; Lemmas 6.1–6.3; (6.12)–(6.18). **Formal anchors:** `Breakdown.Periodic.heatDivFreeComparison` and `freeHeatComparison`, [`Torus/HeatComparison.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean):[18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean#L18), [24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/HeatComparison.lean#L24); `Breakdown.Periodic.rightInversePerturb`, [`Torus/InverseAlgebra.lean:41`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/InverseAlgebra.lean#L41); the full assembly `Breakdown.Periodic.breakdownOnTorus_of_profile`, [`Torus/Main.lean:69–112`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Torus/Main.lean#L69-L112). The printed transfer proof is a revised analytic argument; the formal route uses its own discrete inverse, comparison and gluing machinery. Its heat comparisons prove convergence below a sufficiently small scale, using Fourier integrals and lattice sums; they do not state the displayed powers of $L$ as their conclusion. The exported periodic endpoint permits arbitrary smooth pressure with periodic velocity, using an additional moving-frame reduction. It should not be confused with the narrower periodic-pressure class in which the constructed solution first appears.
<!-- /passage:sec-6 -->

<a id="7"></a>

## 7. What the certificate has to construct

<!-- passage:sec-7 -->

The second implication starts afresh: its approximate profiles are input data, not the singular finite-energy trajectories constructed above. Theorem 7.1 is an a posteriori existence theorem. Its input is a family of approximate profiles, together with estimates strong enough to correct one member to a genuine, nonzero periodic solution. Normalize time by $\theta=s/S$ and set

$$
T_S=\frac1S\partial_\theta+\frac12+\frac12y\cdot\nabla-\Delta,
\qquad
H=L^2((0,1)\times\mathbb R^3).
$$

The spatial space remains $X=\dot H^1_{\mathrm{div}}(\mathbb R^3)$, realized by $L^6$ vector fields. The correction space $D_S$ consists of periodic $L^2_\theta X$ fields satisfying $\Delta v,T_Sv\in H$. This is a graph domain: it does **not** require $\partial_\theta v$ and $y\cdot\nabla v$ separately to belong to $H$ on all of space.

For parameters $\alpha$ in the certificate's nonempty compact convex set $K$, formed from coordinate intervals and a weighted ball, the data provide a period $S(\alpha)$, an approximate field $W^a_\alpha$, fixed forcing fields $b_i$, approximate force coefficients $\beta^a(\alpha)$ and a residual:

$$
T_{S(\alpha)}W^a_\alpha+(W^a_\alpha\cdot\nabla)W^a_\alpha
+\sum_i\beta_i^a(\alpha)b_i\simeq F^a_\alpha.
$$

Here $\simeq$ means equality modulo gradients. A correction and new multipliers solve

$$
T_{S(\alpha)}v+C_\alpha v+(v\cdot\nabla)v
+\sum_i\beta_i b_i\simeq-F^a_\alpha,
\quad
\ell(v)=\bar\ell(\alpha),
\quad
C_\alpha v=(W^a_\alpha\cdot\nabla)v+(v\cdot\nabla)W^a_\alpha.
$$

The force is a device for making the linearized problem invertible; it must disappear at the end. There are as many pinning conditions $\ell_i(v)=\langle\nabla v,\Xi_i\rangle_H$ as force coefficients. They deal with the phase direction and other badly conditioned directions. The construction is not restricted to a single phase parameter.

Let $\Gamma$ be the prescribed set of space-time symmetry pairs $(R,\theta_0)$, requiring $F(\theta+\theta_0,y)=RF(\theta,R^{-1}y)$. The superscript $\Gamma$ denotes the invariant subspace; all correction and linear-solve spaces below carry this restriction. The set may be empty. Write $P$ for the Leray projection acting at each time. The certificate supplies a bounded measurable weight $w\ge w_*>0$, a multiplier weight $\omega>0$, radii $\varepsilon\ge0$ and $M>0$, and $b_*\ge0$ with $\sum_i\|b_i\|_H^2\le b_*^2$. Measure the correction by

$$
\|v\|_w^2=\|\Delta v\|_H^2+\int_0^1\!\!\int w|\nabla v|^2,
\qquad
\|(v,\beta)\|_{w,\omega}^2=\|v\|_w^2+\omega^2|\beta|^2.
$$

The target is a solution with $\|(v,\beta)\|_{w,\omega}\le2\varepsilon$, $\sup_\theta\|\nabla v(\theta)\|_2\le M$, and $\beta^a(\alpha)+\beta=0$. Theorem 7.1 then returns the **same** $\alpha$, period and corrected field, with the pinning identities, both bounds and all prescribed space-time symmetries. After force cancellation, its first quantitative bound contains $|\beta^a(\alpha)|$, because $\beta=-\beta^a(\alpha)$.

**Paper:** §§7.1–7.4, pp.30–35; (7.4), (7.10)–(7.18), (7.38)–(7.39). **Lean:** `Breakdown.IsExtendedCertificate` in [`Breakdown/Cert/ExtendedStatement.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean); the assembled conditional result is `Breakdown.extended_certificate_orbit_proved` in [`Breakdown/Cert/ExtendedMain.lean:56`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedMain.lean#L56). The public result is existential weak-profile existence; it does not expose the paper's complete same-witness quantitative bundle.
<!-- /passage:sec-7 -->

<a id="8"></a>

## 8. Why the bordered linear problem is solvable

<!-- passage:sec-8 -->

The free equation is controlled by an enstrophy identity, not a finite-kinetic-energy estimate:

$$
\frac1{2S}\frac d{d\theta}\|\nabla v(\theta)\|_2^2
+\|\Delta v(\theta)\|_2^2+\frac14\|\nabla v(\theta)\|_2^2
=-\langle T_Sv(\theta),\Delta v(\theta)\rangle.
$$

Integrating over a period removes the derivative and bounds the graph norm by the forcing. The identity also supplies a continuous $X$ representative. The free inverse is constructed from the heat evolution in physical variables; density then gives surjectivity. Local compactness of this inverse, combined with the uniform $|y|^{-1}$ and $|y|^{-2}$ decay of $W^a_\alpha$ and its gradient, makes $PC_\alpha T_S^{-1}$ compact.

The certificate's difficult input is the uniform estimate for a reference linearization $C^r_\alpha$:

$$
\|(v,\beta)\|_{w,\omega}\le c_1\|F\|_H+[F]+c_2|\ell(v)|,
\quad
F\simeq T_Sv+C^r_\alpha v+\sum_i\beta_i b_i,
$$

where $[F]$ measures finitely many difficult forcing directions and $[F]\le c_0\|F\|_H$. Appendix B constructs this estimate. The reference and approximate fields differ by an operator of norm at most $c_r$ from the weighted correction space into $H$. Thus, with $\vartheta=(c_1+c_0)c_r<1$, the error can be absorbed:

$$
(1-\vartheta)\|(v,\beta)\|_{w,\omega}
\le c_1\|F\|_H+[F]+c_2|\ell(v)|.
$$

For differences of solutions with the same pin, $\ell(v)=0$, so the inverse constant is at most $c_L$ provided $c_1+c_0\le(1-\vartheta)c_L$.

This estimate proves injectivity; surjectivity still needs an argument. After composing the velocity coordinate with $T_S^{-1}$, the bordered operator on $H^\Gamma_{\mathrm{div}}\times\mathbb R^n$ is identity plus a compact operator: convection is compact, and the pin/force blocks are finite rank. The finite-dimensional identity block may be added and subtracted inside that compact perturbation, so its Fredholm index is zero. Injectivity therefore supplies the unique linear solve used by the nonlinear construction.

**Paper:** Lemmas 7.4 and 7.7; Propositions 7.5 and 7.8; (7.42)–(7.54), pp.36–40. **Lean:** `Breakdown.Cert.exists_gradInvSpec`, `freeInvHolds_of`, `extendedConvectionCompactHolds_of` and `extendedBorderedInvertibleHolds_of`, in the correspondingly named modules; the last is at [`Breakdown/Cert/ExtendedBorderedInvertible.lean:101`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedBorderedInvertible.lean#L101). Coercivity is a certificate premise at this stage; the Fredholm step is proved.
<!-- /passage:sec-8 -->

<a id="9"></a>

## 9. Closing the nonlinear bounds: two routes

<!-- passage:sec-9 -->

The weighted norm controls an average in time, whereas the quadratic term needs a time supremum. The key product estimate is

$$
\|(v\cdot\nabla)v\|_H
\le c_w\|v\|_w\sup_\theta\|\nabla v(\theta)\|_2,
\qquad
c_w=(4\pi\sqrt{w_*})^{-1/2}.
$$

For a linearized solution, the certificate's quadratic lower bound (7.22), integrated from a minimum of periodic enstrophy, yields

$$
\sup_\theta\|\nabla v(\theta)\|_2^2
\le\left(\frac1{w_*}+\frac{2S c_3}{m}\right)\|v\|_w^2
+\frac{2S}{m}(\|F\|_H+b_*|\beta|)\|v\|_w.
$$

The symmetry condition permits $m=1$, and also permits $m=2$ when a half-period time shift is an orthogonal spatial symmetry. The estimates involving $m$ must be checked for the chosen value. It is the **scalar enstrophy** that has the shorter period. No pointwise-in-time forcing bound is silently inserted.

The paper solves the nonlinear problem and selects the parameter simultaneously. Let $Z\subset H^\Gamma$ be the closed ball of radius $2c_w\varepsilon M$. For $(\alpha,g)\in K\times Z$, solve the bordered linear problem with $-F^a_\alpha-g$ as its right side. The residual/pin budget (7.24), $2c_Lc_wM<1$, and (7.27) place its answer in the two desired correction bounds; the product estimate returns $(v\cdot\nabla)v$ to $Z$. Equip $Z$ with its weak Hilbert-space topology. The product is compact and convex. Strong local convergence of velocities, weak convergence of gradients and the uniform $H$ bound identify the weak limit of the nonlinear term. Uniqueness of the limiting **linear** solve identifies its multipliers. This makes the joint map continuous and permits Schauder–Tychonoff.

Lean takes a different route. For fixed $\alpha$, after absorbing the reference-field error and normalizing $\omega=1$, put $\rho=2\varepsilon$ and use

$$
d((v,\beta),(u,\gamma))
=\max\left\{
\sqrt{\|v-u\|_w^2+|\beta-\gamma|^2},
\frac{\rho}{M}\operatorname*{ess\,sup}_\theta\|\nabla(v-u)\|_2
\right\}.
$$

The expansion

$$
N(v)-N(u)=((v-u)\cdot\nabla)v+(u\cdot\nabla)(v-u)
$$

has $H$ norm at most $2c_wM\,d$. Equation (7.26) makes the supremum component of the inverse obey the same constant $c_L$ as the weighted component. Consequently the nonlinear solve contracts by $2c_Lc_wM<1$. It has a unique solution in this held class for each $\alpha$, and compactness plus that uniqueness proves continuity of the multiplier map. The remaining topological argument is finite dimensional.

Two continuity points matter. The certificate does not assume that the chosen residual representative is continuous as an $H$-valued function of $\alpha$: pressure gradients can change that representative. Its pairings against compactly supported solenoidal tests are continuous by the defining residual equation, which suffices to pass to the limit. Nor must the approximate adjoints depend continuously on $\alpha$. They occur in estimates for the update, not in the map to which the fixed-point theorem is applied.

Equation (7.26) is explicitly unused in the paper's proof. Its role in Lean is therefore substantive, not an unexplained extra test and not evidence of a gap. The two proofs should be read as different constructions with overlapping analytic ingredients. The ordinary and extended formal certificate predicates also differ; the anchors here follow the extended route, without asserting that either written predicate is equivalent to the paper definition.

**Paper:** Lemma 7.6, Proposition 7.9 and Proposition 7.10, pp.38–44; (7.24)–(7.27). **Lean:** `Breakdown.Cert.extendedHeldMapsToHolds_of`, `extendedHeldContractsHolds_of` and `extendedHeldExistsUniqueHolds_of` in [`ExtendedHeldMapsTo.lean:179`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldMapsTo.lean#L179), [`ExtendedHeldContracts.lean:185`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldContracts.lean#L185) and [`ExtendedHeldExistsUnique.lean:135`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedHeldExistsUnique.lean#L135), under `Breakdown/Cert/`. The contraction uses `IsExtendedCertificate.small_second`, the counterpart of (7.26).
<!-- /passage:sec-9 -->

<a id="10"></a>

## 10. The parameter argument removes the force exactly

<!-- passage:sec-10 -->

The parameter domain is a product of a box and a weighted ball:

$$
K=\left\{\alpha:|\alpha_j|\le\rho_j\ (j\in J),\
\sum_{j\notin J}d_j^2\alpha_j^2\le\rho_*^2\right\}.
$$

With $V_j$ the columns of an invertible matrix and each $d_j\ne0$, define

$$
\Phi=\beta^a(\alpha)+\beta,\qquad
\alpha'_j=\alpha_j-d_j^{-1}V_j\cdot\Phi.
$$

The decisive assertion is that the raw update satisfies $\alpha'\in K$. An outward update at a boundary point can be fixed by nearest-point projection while $\Phi\ne0$.

For $j\in J$, pair the equation with an approximate adjoint $\psi_{\alpha,j}$. The adjoint-defect condition at $v=0$ forces this field to annihilate gradients, which makes pairing an equation modulo gradients legitimate. The adjoint-defect, nonlinear and affine-offset estimates give

$$
|V_j\cdot\Phi-d_j\alpha_j|
\le\widetilde a_j(2\varepsilon)^2
+2\varepsilon\sqrt{a_j^2+
\frac{|\langle b,\psi_{\alpha,j}\rangle_H-V_j|^2}{\omega^2}}
+o_j
\le |d_j|\rho_j.
$$

The middle square root combines the velocity and multiplier errors using their **joint** weighted norm. For the remaining coordinates the bound is $2\varepsilon a_*/\omega+o_*\le\rho_*$. These are precisely the two membership conditions for the raw update. In the paper, the Schauder map used its projection; membership now removes the projection. In Lean, the continuous raw update is already a self-map of $K$, so a compact-convex fixed-point theorem applies. At a fixed point, $V^\mathsf T\Phi=0$, hence $\Phi=0$. Non-strict inclusions suffice: the fixed point may lie on the boundary, and $K$ may have empty interior.

The resulting profile $\mathcal W=W^a_\alpha+v$ is nonzero because (7.28) requires

$$
4\varepsilon^2<w_*\|\nabla W^a_\alpha\|_H^2.
$$

If $\mathcal W=0$, the correction bound would give the reverse inequality. Thus neither residual smallness nor a Newton heuristic substitutes for the force-zero and nonzero-profile steps.

**Paper:** (7.29)–(7.37), Proposition 7.10 and §7.9, pp.33–35 and 42–45. **Lean:** `Breakdown.Cert.extendedAdjointEnclosureHolds_of`, `extendedStiffEnclosureHolds`, `extendedExistsZeroHeldHolds_of`, `extendedHeldWeakEquationHolds_of` and `extendedHeldNonzeroHolds_of`; `Breakdown.Held.testSetZero_of` is at [`Breakdown/Held/TestSetZero.lean:92`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L92). Its compact-convex input is supplied by `convexCompactFixedPoint` and the proved `Breakdown.exists_fixedPoint_box`.
<!-- /passage:sec-10 -->

<a id="11"></a>

## 11. Regularity is recovered from the constructed solution

<!-- passage:sec-11 -->

The corrected field is continuous into $X$, periodic, and solves the similarity equation modulo gradients. The next estimates describe the paper's proof of Proposition 7.11; the formal proof uses a different smoothing and decay argument, identified below. The proposition assumes the constructed profile and, after returning to physical variables, already has

$$
u\in C((-\infty,1);L^6),
\qquad
\sup_{t<1}(1-t)^{1/4}\|u(t)\|_6<\infty.
$$

Lemma 3.6 identifies this weak solution with its mild evolution. Two heat/Oseen estimates then give

$$
\|u(t)\|_{12}\lesssim(1-t)^{-3/8},
\qquad
\|u(t)\|_\infty\lesssim(1-t)^{-1/2}.
$$

The nonlinear kernels have time singularities $(t-\tau)^{-7/8}$ and $(t-\tau)^{-3/4}$, respectively, both integrable. The solution is consequently bounded on every compact interval before time 1. Bounded-mild regularity gives a smooth velocity; the smooth residual is curl-free, so a smooth pressure can be recovered. Ordinary discrete self-similarity with factor $e^{S/2}$ then permits the Chae–Wolf decay theorem at $p=6$:

$$
|u(t,x)|\lesssim\frac1{\sqrt{1-t}+|x|}.
$$

Scaling back gives the required profile decay, and interior estimates give derivative decay. This route never requires finite kinetic energy of the profile. Recovering the full same-witness conclusion also requires identifying the smooth representative with the originally selected correction at every time. Equality in $X$ then preserves the correction norms and pins; continuity upgrades each almost-everywhere symmetry to pointwise symmetry.

With its analytic inputs supplied, the formal weak-profile bridge gives a continuous mild orbit. For each chosen mild orbit, the formal smoothing statement returns smooth velocity and pressure together with equality to that orbit's velocity almost everywhere in space at every time. For a smooth orbit satisfying the profile integral equation, the formal decay theorem bounds the velocity and its first two spatial derivatives by $C(1+|y|)^{-1-j}$, and the pressure gradient by $C(1+|y|)^{-3}$.

**Paper:** Proposition 7.11, pp.45–47; Lemma 3.6 and Appendix A; Remark 1.2. The paper uses Koch–Nadirashvili–Seregin–Šverák, Proposition 4.1 (2009), and Chae–Wolf, Theorem 1.1 (2017); their hypotheses are met here, as [the statement comparison](paper.md) explains. **Lean:** With the weak-to-mild analytic prerequisites supplied by the assembled proof, `Breakdown.WeakProfile.weakOrbitOfParts_holds`, `Breakdown.FarField.smoothFieldOfOrbit_holds` and `farFieldDecay_holds` supply the weak-to-mild, smoothing and decay steps through a different proof organization. `Breakdown.FarField.periodicLerayProfileExists_of_weak` at [`Breakdown/CertTorus/Main.lean:8`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Main.lean#L8) closes weak-to-smooth existence. The authors' existential interfaces hide the correspondence to the originally selected correction; our [Theorem 7.1 wrapper](https://github.com/wcook04/proof-reader/tree/claude/navier-stokes-20261120/lean-wrappers/navier-stokes-theorem71) exposes it, and `Breakdown.theorem71_extended` and `theorem71_cell` prove the full same-witness conclusion with only the standard axioms.
<!-- /passage:sec-11 -->

<a id="12"></a>

## 12. Appendix B: why finite data can control every perturbation

<!-- passage:sec-12 -->

The certificate is more than a finely resolved approximate solution. It must certify an inverse estimate **for every admissible perturbation**, including modes and spatial regions omitted from the numerical representation.

The data use finitely many time/azimuthal harmonics

$$
E_\iota(\theta,\varphi)
=\exp i\!\left(2\pi(2\iota_2-\iota_1)\theta+k_{\mathrm{sym}}\iota_1\varphi\right),
\qquad
\sigma=\frac{|y|}{|y|+L},\quad \eta=\frac{y_3}{|y|}.
$$

Piecewise polynomials in $(\sigma,\eta)$, explicit factors at the axis, origin and infinity, and a radial phase describe the fields. Divergence is built into the representation. Joins make distributional derivatives agree with the piecewise formulas. Write $k_{\mathrm{sym}}$ for Appendix B's symmetry integer, to distinguish it from the decay exponent $\kappa$. The paper reports $k_{\mathrm{sym}}=19$ for its intended instance; this is a finite rotational symmetry. The scalar $m=2$ used above comes from its half-period rotational symmetry and is a different integer.

The central construction is the a priori estimate (7.18). Proposition B.1 builds a multiplier consisting of $-\Delta v$ and mode-dependent skew terms. In rotating frames those skew terms recover positive contributions proportional to the absolute frequency; profile stretching and commutator errors remain as explicit quadratic forms. Proposition B.4 reduces those forms to cell coefficients, trace variables, model-error bounds and the remaining harmonics. The paper describes these two proofs but relies on the formalization for their complete proofs.

Three reductions prevent a finite calculation from silently truncating the PDE.

**Resolved cells.** Polynomial coefficients represent low-order mode components. Orthogonal remainders are controlled by explicit Legendre/Jacobi spectral gaps such as (B.27). Global cell maps enforce shared traces, symmetry and divergence identities. Local quadratic inequalities must hold on their stated range, including pressure/gauge and free coordinates, not merely on the sampled profile.

**Unresolved modes and the exterior.** For a single mode $u=\widehat v_\iota$, let $r=(y_1^2+y_2^2)^{1/2}$ be the cylindrical radius, $k=k_{\mathrm{sym}}\iota_1$ its azimuthal frequency, and $a_+=\max\{a,0\}$. Angular derivative inequalities give, almost everywhere for the weak Fourier modes,

$$
(|k|-1)_+|u|\le r|\nabla u|,
\qquad
(|k|-2)_+|\nabla u|\le r|\nabla^2u|.
$$

With an auxiliary function $t$ satisfying $0\le t\le f_1^*$, as in (B.29), these inequalities reduce a remaining form to
$(f_1^*-t)|\nabla u|^2+f_0^*|u|^2-f_{01}|\nabla u||u|$.
Here $t$ is unrelated to physical time. Nonnegativity follows from nonnegative square coefficients and
$f_{01}^2\le4(f_1^*-t)f_0^*$. At infinity, the replacement is an integrated Hardy inequality with an explicit constant $\Lambda_0$, requiring
$f_0^\infty/\Lambda_0+f_{01}^\infty/\sqrt{\Lambda_0}\le f_1^\infty$.
Thus the exterior is included analytically; it is not assigned zero error.

**The matrix tree and its free directions.** Local bounds telescope along a finite rooted tree. Each node contributes positive pivots and finitely many negative column squares; internal matrix fronts cancel. The formal tree bound retains the root front. Dropping its nonnegative contribution under the pivot-count conditions gives the following form of Lemma B.7:

$$
\langle Nx,x\rangle
\ge\sum_\xi\sum_{j\in U_\xi}p_{\xi,j}x_j^2
-\sum_\xi|Y_\xi^\mathsf Tx|^2.
$$

Under the pivot-count conditions, every coordinate is covered by a positive pivot and the root front is nonnegative. The root form is then positive on the complement of the bad columns; the tree lower bound transfers this positivity to the total leaf form. The negative columns remain explicit in the global bound. The actual vector has physical coordinates $x_p$ and freely selectable auxiliary coordinates $x_f$. Proposition B.8 shows that the pure-free subspace is nonpositive, hence intersects the positive complement only at zero. The number of bad columns is at most the dimension of that free subspace. A dimension count therefore lets every $x_p$ be completed to $(x_p,x_f)$ in the positive complement. Let $Y$ concatenate the columns of all $Y_\xi$. Writing $\mathscr L=Y^\perp$ and $\mathscr F=\{0\}\times\mathbb R^{n_f}$, the argument has proved $\mathscr L\cap\mathscr F=\{0\}$ and $\operatorname{codim}\mathscr L\le n_f=\dim\mathscr F$. Hence $\mathscr L\oplus\mathscr F$ is the whole coordinate space. The direction of this dimension inequality matters: it proves the availability of the auxiliary completion, not a numerical count of unstable PDE modes. This converts the finite matrix certificate into the universal perturbation inequality (B.21).

Adding (B.21) to the multiplier inequality cancels the problematic integral and force pairings. With

$$
P^2=\frac3{50}\|(v,\beta)\|_{w,\omega}^2+c_\mu\|v\|_\mu^2,
\qquad
Q^2=\frac3{50}[F]^2+1000|\ell(v)|^2,
$$

one gets $P^2\le c_M\|F\|_H P+Q^2$, hence $P\le c_M\|F\|_H+Q$. Lemma B.2 obtains (7.18). Lemmas B.9–B.13 similarly turn a finite family of field norms, pairings and enclosure estimates into the reference-error, growth and adjoint bounds. Proposition B.14 assembles the certificate of §7.

The published choice $w_*=39/50$ and the stated scalar inequalities imply $c_1\ge50/3$, $c_0>81.64$, $c_2>129$, $c_L>98.3$, $M<0.01695$ and $\varepsilon<0.0075$. These numerical bounds are deductions from the paper's constants. These are necessary constraints on any satisfying data, not measured margins of the absent instance. The small number is the correction after the stabilized inverse has been applied, not the size of $W^a_\alpha$ itself. A profile with large gradient can therefore coexist with a small correction radius. Whether the required residual and coercive margins actually coexist in one data set remains a numerical question; compatibility of the scalar inequalities alone cannot settle it.

**Paper:** Appendix B.1–B.4, pp.49–70; especially Propositions B.1, B.4, B.8 and B.14, Lemmas B.2 and B.7. **Lean:** `Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_proof`; `Breakdown.CertCell.cellLayerParts_closed` and `rowRestClause_closed` in [`Breakdown/CertCell/CellLayerClosed.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean); `Breakdown.CertCell.Certificate.signedTreeLowerBound` in [`CertTreeLowerBound.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean); `Breakdown.CellLayerSystem.isExtendedCertificate_of_parts` in [`Breakdown/CellReduction/CellLayerBreakdownCompose.lean:171`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CellReduction/CellLayerBreakdownCompose.lean#L171).
<!-- /passage:sec-12 -->

<a id="13"></a>

## 13. What remains to be supplied by computation

<!-- passage:sec-13 -->

“Finite certificate” means finitely represented data plus a sound reduction of all universal conditions. Appendix B still requires uniform bounds over $K$, every point of specified regions, all relevant harmonics and the unbounded exterior. The exact checker must connect bytes to these mathematical objects and discharge those quantifiers. A small numerical residual at selected points is insufficient. The final paragraph of Appendix B explicitly leaves several coefficient expressions and side conditions unwritten. For those clauses the readable Lean definitions and the complete decoding rules must supply the specification; the appendix alone is not a standalone executable checker.

At the pinned release, the paper reports a 128-bit Arb verification; the supplied release contains neither the data nor the checking program. The published SHA-256 is `3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5`. It identifies the intended file; it does not prove any inequality. The unproved checker-to-condition obligation is

$$
\operatorname{Accept}(\text{bytes})
\Longrightarrow
\operatorname{CellSystemCondition}(\operatorname{decode}(\text{bytes})).
$$

The decoded instance then enters proved conditional space and torus results, including `Breakdown.CellLayerSystem.spaceAndTorusBreakdown_of_cell_system_condition`. The obligation map on the [certificate-checker page](certificate-checker.md) matters here: its entries include identities, side conditions and shared witnesses, not just scalar tests. Correct evaluation must preserve their meanings and scopes. That is the precise boundary between the mathematical argument reconstructed above and the still-unreproduced numerical assertion.

**Paper:** p.4; the paragraph following Proposition B.14, p.70. **Source:** [the certificate-checker page](certificate-checker.md). **Lean:** [`Breakdown/CertTorus/CertificateCorollary.lean:28`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/CertificateCorollary.lean#L28) and public wrappers at [`Solution.lean:338–350`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L338-L350).

For a released instance, three tasks remain distinct: establish that the decoded objects satisfy every field of the formal premise; check the conditional theorem against those definitions; and relate its output to the desired physical statement. The public whole-space endpoint excludes a global smooth solution with uniformly bounded energy, and the torus endpoint excludes a global smooth solution with periodic velocity even when pressure is not assumed periodic. These are substantive nonexistence conclusions, but their signatures do not retain all the displayed rates, trajectory identities or family quantifiers. The internal transfer and smoothing results deserve their full credit without silently strengthening those signatures.
<!-- /passage:sec-13 -->

# Where the weight sits

<!-- passage:sec-where-the-weight-sits -->

These are the six points on which a referee's close reading has the greatest effect. They identify dependencies, not newly alleged defects. The first row includes the unreproduced numerical premise; the other rows explain what the analytic implications must carry. 

| Step and location | What deserves the time | What a failure would cost |
|---|---|---|
| **W1. Universal coercivity and the actual certificate.** Appendix B, especially B.1, B.4, B.7–B.8; §§12–13 here. | All perturbations, free/gauge coordinates, tails and unresolved modes must be controlled. The tree needs the auxiliary-completion argument. Released bytes must imply the exact formal premise. | The inverse bound, or its concrete instantiation, would remain unproved. This alone would not refute either abstract analytic implication. |
| **W2. Compact monodromy.** Lemmas 3.2, 4.4–4.5; §3. | Compactness in the homogeneous space and the integrable time endpoint must give the essential-radius bound and finite exceptional space. | The finite-dimensional correction mechanism could fail. |
| **W3. Compact correction and finite energy.** Proposition 4.3, Lemma 5.1, Lemma 2.3; §§4–5. | The transversal must have compact support; both recurrence directions must close; classical continuation must carry compact data into bounded-energy evolution. | A recurrent or abstract solution would not yet give the stated compact-data singular trajectory. |
| **W4. Unforced torus transfer.** Lemmas 6.1–6.3; §6. | The nonlocal comparison and the $O(L^{-1/2})$ inverse defect must be uniform. Both the inverse defect and nonlinear residual must be removed. | The torus statement could stop at a forced construction; the whole-space argument is separate. |
| **W5. Solve and cancel the force.** Propositions 7.8–7.10; §§8–10. | Fredholm surjectivity, the two correction norms, the correct nonlinear route, and membership of the raw parameter update in $K$. | One could retain only a forced profile, or lose the parameter existence argument. |
| **W6. A nonzero smooth profile with the right identity.** Proposition 7.11, (7.28), (7.38)–(7.39); §§10–11. | Strong input norms must justify smoothing and decay; equality of representatives must preserve period, parameter, bounds and symmetries. | Classical admissibility or the full same-witness conclusion would be missing; this must be separated from a coarser formal endpoint. |

For an afternoon reading, start with §§1, 3–6 and 8–12, using the six groups of equations that carry the logic: the free contraction and compact perturbation; the two-sided recurrence; the inverse-defect estimate; the absorbed bordered bound; the raw-update enclosure; and the tree/free-variable coercivity argument. The full paper is still needed to check the detailed analytic estimates and the coefficient-level conditions omitted from its Appendix B.
<!-- /passage:sec-where-the-weight-sits -->

# Lineage: mechanisms, discovery and validation

<!-- passage:sec-lineage-mechanisms-discovery-and-validation -->

The relevant history has three strands: mechanisms that can concentrate a fluid, numerical methods that find candidate profiles, and estimates that turn a candidate into an exact solution. Each precedent contributes something different to the construction under review.

**Leray, 1934.** In *Sur le mouvement d’un liquide visqueux emplissant l’espace*, Leray placed the global weak-solution theory beside the unresolved question of whether a smooth motion can cease to be regular. His backward self-similar ansatz, recalled in the present paper at p. 1, sought a singular motion by fixing its shape under rescaling. The present paper returns to this separation. Its candidate recurring profile need not have finite energy, and its localization argument must produce finite-energy initial data without destroying the singular core. Its backward discretely self-similar orbit is periodic in logarithmic time. This is a precise additional structure beyond merely saying that smaller scales repeat. [L1; present paper, p. 1 and Theorem 1.1; comparison is our reading.]

**Tao, preprint 3 February 2014; journal July 2016.** Tao constructs finite-time blow-up for an averaged Navier–Stokes equation. The altered bilinear term retains the cancellation behind the energy identity and the relevant function-space estimates. The result therefore isolates a limitation of arguments using only those estimates: such an argument cannot distinguish the genuine nonlinearity from one permitting blow-up. This supplies conceptual motivation for seeking a singularity compatible with energy dissipation. It does not supply a Navier–Stokes profile for the original nonlinearity. Alpöge–Buckmaster’s profile equation and certificate have to retain that exact nonlinearity. The journal paper appeared electronically on 30 June 2015 and in *JAMS* 29(3), 601–674 (2016). [L2–L3.]

**Chen–Hou, analysis preprint 13 October 2022; numerical sequel 9 May 2023.** Their construction proves nearly self-similar blow-up for the 2D Boussinesq and 3D axisymmetric Euler equations with smooth finite-energy data and a boundary. The analysis establishes stability near an approximate profile through weighted sup and Hölder estimates; the numerical component verifies the quantitative inequalities needed by that argument. The numerical sequel was published online on 6 January 2025 and in the March 2025 issue of *Multiscale Modeling & Simulation*. Both preprints were revised on 16 August 2026. For the present paper the methodological link is the division between an analytic implication and concrete verified bounds. The equations, boundary geometry and stability mechanism remain distinct: this paper studies an unforced viscous problem on $\mathbb R^3$ and transfers the construction to a boundaryless torus. [L4–L6.]

**Wang–Lai–Gómez-Serrano–Buckmaster, preprint 18 January 2022; journal 16 June 2023.** Their physics-informed neural-network method numerically finds smooth self-similar profiles for axisymmetric Euler and Boussinesq, and an unstable profile for the Córdoba–Córdoba–Fontelos model. The paper presents these candidates as possible inputs to subsequent computer-assisted proofs. Its relevance is to discovery: an approximation can guide a proof even when its construction offers no error certificate. The present Appendix C serves a related discovery role, while §7 and Appendix B bear the validation burden. A small sampled residual and a rigorous inverse bound are separate mathematical achievements. [L7–L8; the comparison with Appendix C is our inference.]

**Alpöge–Buckmaster–Coiculescu, announced 20 November 2026.** The accompanying Euler paper constructs unforced flow on $\mathbb T^3$ with smooth data, bounded velocity and a finite-time vorticity singularity. Its mechanism uses localized Craik–Criminale waves: one scale amplifies a new wave whose velocity gradient prepares the next amplification. Successive growth intervals have finite total length. This differs from the viscous paper’s strategy of validating one periodic orbit in similarity variables. The Euler release records `TorusEuler.theorem11` as a hypothesis-free proof of its torus existence statement; that claim is part of the release record, not a new compilation or semantic audit performed for this digest. Its notes distinguish a manuscript frozen on 18 November from the revised arXiv manuscript, so theorem numbering must follow the chosen version. [L9–L11.]

**What Tao’s 20 November assessment contributes.** Tao separates the Euler paper’s readable proof from the Navier–Stokes paper’s broadly intelligible strategy and unfinished exposition. This is a useful description of the digestion task, not a replacement for checking the arguments. The present digest makes the two analytic implications navigable and identifies the finite numerical premises that remain to be discharged by the released certificate. That final computation cannot yet be replayed independently. [L11.]
<!-- /passage:sec-lineage-mechanisms-discovery-and-validation -->

## Dated primary sources for the lineage

<!-- passage:sec-dated-primary-sources-for-the-lineage -->

- **L1, 1934.** Jean Leray, [Sur le mouvement d’un liquide visqueux emplissant l’espace](https://www.i2m.univ-amu.fr/perso/thierry.gallouet/artbase.d/leray-ns.pdf).
- **L2, 2014-02-03.** Terence Tao, [Finite time blowup for an averaged three-dimensional Navier–Stokes equation](https://arxiv.org/abs/1402.0290).
- **L3, 2016-07; online 2015-06-30.** Terence Tao, [Finite time blowup for an averaged three-dimensional Navier–Stokes equation](https://doi.org/10.1090/jams/838).
- **L4, 2022-10-13.** Jiajie Chen and Thomas Y. Hou, [Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler equations with smooth data I: Analysis](https://arxiv.org/abs/2210.07191).
- **L5, 2023-05-09.** Jiajie Chen and Thomas Y. Hou, [Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler equations with smooth data II: Rigorous Numerics](https://arxiv.org/abs/2305.05660).
- **L6, 2025-03; online 2025-01-06.** Jiajie Chen and Thomas Y. Hou, [Stable Nearly Self-Similar Blowup ... II: Rigorous Numerics](https://authors.library.caltech.edu/records/n8p3w-pkt03).
- **L7, 2022-01-18.** Yongji Wang, Ching-Yao Lai, Javier Gómez-Serrano and Tristan Buckmaster, [Asymptotic self-similar blow-up profile for three-dimensional axisymmetric Euler equations using neural networks](https://arxiv.org/abs/2201.06780).
- **L8, 2023-06-16.** Yongji Wang, Ching-Yao Lai, Javier Gómez-Serrano and Tristan Buckmaster, [Asymptotic Self-Similar Blow-Up Profile for Three-Dimensional Axisymmetric Euler Equations Using Neural Networks](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.130.244002).
- **L9, 2026-11-20.** Levent Alpöge, Tristan Buckmaster and Matei P. Coiculescu, [Finite-Time Singularity Formation for the Three-Dimensional Euler Equations](https://cims.nyu.edu/~tristanb/cc.pdf).
- **L10, 2026-11-20.** Levent Alpöge, Tristan Buckmaster and Matei P. Coiculescu, [EulerBlowupPublic repository](https://github.com/mcoiculescu/EulerBlowupPublic).
- **L11, 2026-11-20.** Terence Tao, [Unforced Euler singularity, unforced Navier-Stokes singularity, and the Generalized Riemann Hypothesis](https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/).
<!-- /passage:sec-dated-primary-sources-for-the-lineage -->

