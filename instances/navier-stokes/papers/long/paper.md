
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

## 1. The input orbit and the actual conclusion

<!-- passage:sec-1-the-input-orbit-and-the-actual-conclusion -->

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
<!-- /passage:sec-1-the-input-orbit-and-the-actual-conclusion -->

## 2. Why the space is homogeneous $H^1$

<!-- passage:sec-2-why-the-space-is-homogeneous-h-1 -->

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
<!-- /passage:sec-2-why-the-space-is-homogeneous-h-1 -->

## 3. A spectral split without a numerical spectrum

<!-- passage:sec-3-a-spectral-split-without-a-numerical-spectrum -->

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
<!-- /passage:sec-3-a-spectral-split-without-a-numerical-spectrum -->

## 4. Compact corrections and the infinite-time boundary condition

<!-- passage:sec-4-compact-corrections-and-the-infinite-time-boundary-condition -->

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
<!-- /passage:sec-4-compact-corrections-and-the-infinite-time-boundary-condition -->

## 5. Finite energy and the lower blow-up bound

<!-- passage:sec-5-finite-energy-and-the-lower-blow-up-bound -->

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
<!-- /passage:sec-5-finite-energy-and-the-lower-blow-up-bound -->

## 6. The torus: make the localization error disappear

<!-- passage:sec-6-the-torus-make-the-localization-error-disappear -->

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
<!-- /passage:sec-6-the-torus-make-the-localization-error-disappear -->

## 7. What the certificate has to construct

<!-- passage:sec-7-what-the-certificate-has-to-construct -->

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
<!-- /passage:sec-7-what-the-certificate-has-to-construct -->

## 8. Why the bordered linear problem is solvable

<!-- passage:sec-8-why-the-bordered-linear-problem-is-solvable -->

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
<!-- /passage:sec-8-why-the-bordered-linear-problem-is-solvable -->

## 9. Closing the nonlinear bounds: two routes

<!-- passage:sec-9-closing-the-nonlinear-bounds-two-routes -->

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
<!-- /passage:sec-9-closing-the-nonlinear-bounds-two-routes -->

## 10. The parameter argument removes the force exactly

<!-- passage:sec-10-the-parameter-argument-removes-the-force-exactly -->

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
<!-- /passage:sec-10-the-parameter-argument-removes-the-force-exactly -->

## 11. Regularity is recovered from the constructed solution

<!-- passage:sec-11-regularity-is-recovered-from-the-constructed-solution -->

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
<!-- /passage:sec-11-regularity-is-recovered-from-the-constructed-solution -->

## 12. Appendix B: why finite data can control every perturbation

<!-- passage:sec-12-appendix-b-why-finite-data-can-control-every-perturbation -->

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
<!-- /passage:sec-12-appendix-b-why-finite-data-can-control-every-perturbation -->

## 13. What remains to be supplied by computation

<!-- passage:sec-13-what-remains-to-be-supplied-by-computation -->

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
<!-- /passage:sec-13-what-remains-to-be-supplied-by-computation -->

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

# From a recurrent profile to compact-data Navier–Stokes blow-up

<!-- passage:sec-from-a-recurrent-profile-to-compact-data-navier-stokes-blow-up -->

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · **full account, part I** · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

*An expanded account of §§1–6 and Appendix A of Alpöge and Buckmaster, with correspondences to the Lean source at `ad53419de079eb8f95f60313473374624a348546`.*

The input to this argument is one nonzero smooth solution of the similarity equations which returns after a positive time, possibly after an orthogonal change of coordinates. Its spatial decay is just strong enough to put it in the homogeneous Sobolev space with norm $\|\nabla u\|_2$. In that space, heat evolution followed by rescaling contracts. The linearised return map differs from this contraction by a compact operator. Only finitely many directions can therefore obstruct a chosen decay rate. Choosing the initial datum along a finite-dimensional space of compactly supported fields removes those obstructions. A nonlinear correction then produces the whole-space solution. A second construction transfers the correction to a large torus and removes its localisation error exactly.

The profile is assumed throughout. Constructing it from certificate data is the separate argument of Theorem 7.1. The numerical certificate and its external checker are outside the formal proofs of the released source. Nothing below changes that boundary.
<!-- /passage:sec-from-a-recurrent-profile-to-compact-data-navier-stokes-blow-up -->

## Notation

<!-- passage:sec-notation -->

The table names the objects used in this account. A parent declaration followed by a field or parameter description means that Lean packages the object there. A mathematical construction with no separately identified declaration is labelled as such. In particular, the periodic space $X_L$ used in the analytic proof and the formal Fourier space $V$ have different norms.

### Geometry, variables and common conventions

| Symbols | Meaning | Lean correspondence |
|---|---|---|
| $\mathbb R^3,\mathbb T^3,x,y,t,s$ | Euclidean space, the unit torus, physical and similarity position, and physical and similarity time. | `Breakdown.Space`; `Breakdown.physicalTime`; `Breakdown.physicalScale` Space is Euclidean three-space; periodic fields are represented on it. See (1.6) for the time and position changes. |
| $W,q,S,R,\rho=\rho_R$ | Smooth similarity velocity, its pressure, positive recurrence period, orthogonal recurrence map, and its action on vector fields. | `Breakdown.PeriodicSimilarityProfileExists`; `Breakdown.IsSimilarityProfile`; `Breakdown.pushForward` The internal orbit interface calls its period P and its isometry rho. The formal profile premise includes the derivative bounds discussed in Appendix A. |
| $u,p,\nu,T,u_0,w_0,\chi$ | Physical velocity and pressure, positive viscosity, terminal time, constructed datum, prescribed nearby datum, and its difference from the initial profile. | `Breakdown.IsSmoothSolution`; `Breakdown.TransferHolds` The nearby-datum family is proved in Proposition 6.5; TransferHolds retains a dense-data existence statement. |
| $\nabla,\Delta,\operatorname{div},\operatorname{curl},\partial_s,\partial_t$ | Spatial gradient, Laplacian, divergence and curl; similarity and physical time derivatives. | `Breakdown.SimilarityResidual`; `Breakdown.IsSmoothSolution` These are ordinary differential operations. The declarations package the equations; they are not aliases for each displayed operator. |
| $\Vert \cdot\Vert _p,L^p,H^1,\dot H^1,B_r,\langle\cdot,\cdot\rangle$ | Lebesgue norm and space; inhomogeneous and homogeneous Sobolev spaces; the Euclidean ball of radius r; the relevant real inner product. | `Breakdown.Freq.X`; `Breakdown.Periodic.V` The declared spaces give the Fourier realisations used here; ordinary function-space notation is analytic notation. |
| $\widehat f,\xi,\mathbb P,\mathcal D,\mathcal S$ | Fourier transform with phase exp(-2 pi i x dot xi), Fourier variable, Leray projection, compact smooth solenoidal test space, and Schwartz class. | `Breakdown.Freq.X`; `Breakdown.Freq.testDense_holds`; `Breakdown.Freq.testSpan_holds` The multiplier of the Leray projection is I minus xi tensor xi divided by squared xi norm. |
| $\lambda,t_n,\sigma,n,m,j,\ell$ | One-period scale exp(-S), geometric piece endpoints 1-lambda^n, a local time, and integer indices or derivative order. | `Breakdown.MildFramework.IsOrbit`; `Breakdown.Periodic.stepStart` Lemma 9.5 in Section 9.4 reuses lambda for a subdivided scale; that local convention is stated there. |
| $G(t)=H_t,\ B=B_0,\ C_\kappa=\mathcal Y_\kappa(X)$ | Two names for the heat semigroup, the zero-origin Duhamel bilinear map, and the weighted continuous path space. | `Breakdown.Freq.heatX`; `Breakdown.HeatBilinear.pieceBil` G_t in Lemma 8.2 is the scalar Gaussian kernel, whereas G(t) is the heat operator. Abstract letters inside Lemma 8.10 are local to that lemma. |
| $m=c_*,\ M=C_*,\varepsilon,\varepsilon_0,\delta,C,C_i$ | Positive lower and upper orbit bounds, smallness parameters and finite estimate constants. | `Breakdown.orbitNorm`; `Breakdown.orbitBound` These are chosen analytic constants. No numerical values are supplied for the unknown profile. |

### Whole-space analytic objects

| Symbols | Meaning | Lean correspondence |
|---|---|---|
| $X$ | Solenoidal homogeneous H1 space with its L6 representative | `Breakdown.Freq.X` The formal representation is a closed Fourier L2 subspace. |
| $H_t=e^{tΔ}$ | Heat semigroup | `Breakdown.Freq.heatX` |
| $D_μ$ | Navier–Stokes dilation, sqrt(mu) u(sqrt(mu) x) | `Breakdown.dilateField`; `Breakdown.Freq.dilX` |
| $ρ_R$ | Orthogonal push-forward, R u(R^{-1}x) | `Breakdown.pushForward`; `Breakdown.Freq.rotX` |
| $K(τ)$ | Symmetric heat-Leray bilinear interaction | `Breakdown.Freq.bilinX` |
| $B_a(f,g)$ | Time integral of K(t-r)(f(r),g(r)) starting at a | `Breakdown.HeatBilinear.pieceBil` Formal pieceBil uses a time piece starting at zero; this is not the literal B_a notation. |
| $C_K$ | Positive constant in the bilinear bound | `Breakdown.HeatBilinear` CK is a field of the structure; the physical proof may enlarge it to be at least one. |
| $u_T^*,p_T^*$ | Physical velocity and pressure associated with the profile and terminal time T | `Breakdown.physicalField`; `Breakdown.physicalPressure` The formal definitions normalise T=1 and permit a phase s0. |
| $s,y$ | Similarity time log(T/(T-t)) and similarity position x/sqrt(T-t) | `Breakdown.physicalTime`; `Breakdown.physicalScale` |
| $K_L,H_t on the torus$ | Periodic bilinear map and periodic heat semigroup | `Breakdown.Periodic.kernel`; `Breakdown.Periodic.heat` |
| $q_0,ℛ_i,H_ψ$ | Normalised pressure, Riesz transforms, and the time-tested harmonic pressure remainder in Lemma A.6 | Local analytic notation; no separately identified declaration. Local proof notation; no exact pinned declaration is claimed for this analytic bridge. |
| $E_2$ | Closure of Schwartz fields in the uniformly local L2 norm | Local analytic notation; no separately identified declaration. Only used to apply Dubois in the analytic argument; the formal route uses Fourier test density. |
| $Ψ$ | The periodic dual field -Delta H_tau z in Lemma A.4 | Local analytic notation; no separately identified declaration. Local notation in the analytic duality proof; no one-to-one exported declaration was identified. |

### Spectral correction and short intervals

| Symbols | Meaning | Lean correspondence |
|---|---|---|
| $\mathcal M$ | Linearized evolution through one similarity period, followed by inverse twist | `Breakdown.MonodromyStatement`; `Breakdown.monodromy` In the source it is a local expression built from rho inverse and iterProd of stepMap; no global declaration named M. |
| $\mathcal M_0$ | Free period map rho inverse composed with D_lambda and heat evolution | `Breakdown.MonodromyStatement` The source writes the product of free short-interval maps. |
| $k,\delta,\mu,\tau$ | Subdivision count; S/k; exp(-S/k); short physical interval length 1-mu | `Breakdown.MildFramework.stepLength`; `Breakdown.StepDataInternal.exists_step_count` The formal period parameter is P. |
| $Y,a_n,A_n,\Gamma,\operatorname{Ev}$ | Continuous functions on one short interval; profile piece; linearized operator; free solution; rescaled endpoint | `Breakdown.Piece`; `Breakdown.MildFramework.profilePiece`; `Breakdown.MildFramework.stepOp`; `Breakdown.MildFramework.stepFree`; `Breakdown.MildFramework.stepEnd` All are described in (4.5)–(4.6). |
| $S_n$ | Linearized short-interval step map | `Breakdown.stepMap` Not the period S. |
| $P_u,V,Q$ | Exceptional projection, its finite-dimensional range, and I minus P_u | `Breakdown.DichotomyHolds`; `Breakdown.Spectral.exists_dichotomy` P_u is not required to be orthogonal. |
| $r_1,\Theta,r_2,\kappa,\theta$ | Stable radius, chosen period decay factor, exceptional inverse radius, logarithmic decay exponent, short-interval decay factor | `Breakdown.DichotomyHolds`; `Breakdown.stepData` Theta=lambda^kappa and theta=Theta^(1/k); these are local proof variables. |
| $C_\kappa,\Vert \cdot\Vert _\kappa$ | Continuous functions on [0,1) weighted by (1-t)^(1/4-kappa) | Local analytic notation; no separately identified declaration. Paper notation reconstructed in the rewrite; the Lean transfer route uses lp infinity of short-interval functions. |
| $E,J_V,J,\gamma,e$ | Compact transversal; inverse section onto it; ambient section; compact initial correction; exceptional-coordinate correction | `Breakdown.SectionStatement`; `Breakdown.exists_section`; `Breakdown.StepDataStatement` The formal section maps an abstract dense submodule; its exceptional coordinate is lifted to physical data. |
| $\chi_n,f_n,g_n$ | Rescaled endpoint of v-g, recurrence forcing, and rescaled continuous source | `Breakdown.orbitSeq`; `Breakdown.PeriodicInverseStatement` The continuous-source construction is distinct from the formal normalized sequence interface. |
| $\mathcal R,\mathcal R_d$ | Continuous weighted right inverse and normalized sequence right inverse | `Breakdown.periodicInverse`; `Breakdown.PeriodicInverseStatement` Only the sequence interface is the literal source statement. |
| $u^a,F^a,\mathcal L$ | Approximate background, Duhamel residual, and linearized equation with datum correction | `Breakdown.ContractionStatement` Paper continuous formulation; the source theorem uses its short-interval sequence analogue. |
| $N,z_n,v_n$ | Interval bilinear map, normalized perturbation, and theta^n times that perturbation | `Breakdown.HeatBilinear.pieceBil`; `Breakdown.contraction` z belongs to lp infinity in the source. |
| $A,\eta,\bar u_r$ | Radial homotopy vector potential, scalar cutoff, and its curl | `Breakdown.Periodic.homotopyPotential`; `Breakdown.Periodic.cutoffField` The source quantitative torus route fixes a centre and cutoff radius. |
| $C_B,C_{\mathcal R},B_d,K_d,C_d,\rho_0$ | Bilinear and inverse bounds, sequence growth constants, correction bound and admissible datum size | `Breakdown.ContractionInternal.exists_small_fixed`; `Breakdown.contraction` Local proof constants, not separately named global Lean objects. |

### Torus transfer and its local notation

| Symbols | Meaning | Lean correspondence |
|---|---|---|
| $L,\ Q_L,\ \mathbb T_L^3$ | Large spatial period, centred period cell, and torus of that period. | Local analytic notation; no separately identified declaration. The main formal construction uses a unit torus and small terminal time T instead of a varying period L. |
| $X_L$ | Mean-zero divergence-free H1 fields on the L-periodic torus, with gradient norm. | `Breakdown.Periodic.V`; `Breakdown.Periodic.weight` These are comparison anchors. V uses the full inhomogeneous unit-torus H1 norm and permits the constant mode. |
| $V,\ \operatorname{toV}$ | Formal periodic Fourier Hilbert space and the Fourier map for smooth periodic solenoidal physical fields. This use of V in Sections 8–9 is distinct from the finite-dimensional spectral range V in Sections 4–6. | `Breakdown.Periodic.V`; `Breakdown.Periodic.toV` The weighted coefficients use 1+4*pi^2*|k|^2. |
| $\Pi_L$ | Periodization of a compact field supported within one cell. | `Breakdown.Periodic.transplantField` The formal analogue includes a dilation and a shift to the centre of the unit cell. |
| $G_t,\ O_t$ | Scalar Gaussian heat kernel and matrix Oseen kernel of the whole-space heat flow followed by the Leray projection. | Local analytic notation; no separately identified declaration. The explicit Oseen representation is derived in Lemma 8.2; no matching named kernel declaration is asserted. |
| $G_L(t),\ \mathbb P_L,\ B_L$ | Periodic heat flow, Leray projection and symmetric time-integrated Navier–Stokes bilinear map. | `Breakdown.Periodic.torusFactor`; `Breakdown.Periodic.seqPerturbation` These are formal interaction and correction anchors, not aliases for the entire continuous large-torus formula. |
| $\bar u,\ u^a,\ d$ | Solenoidal cutoff of u*, its periodization, and the cutoff difference bar-u minus u*. | `Breakdown.Periodic.approxFieldProperties_holds` The formal cutoff is centred on the unit cell and has its own pressure cutoff. |
| $F^a,\ \bar F$ | Periodic and whole-space Duhamel residuals of the cutoff field. | `Breakdown.Periodic.approxResidualSmall` The formal residual bound is on geometric time pieces. |
| $\mathcal Y_\kappa(Y),\ \Vert \cdot\Vert _\kappa$ | Continuous time paths with supremum norm weighted by (1-t)^(1/4-kappa). | `Breakdown.Periodic.seqPerturbation` The formal torus correction uses a weighted sequence of bounded pieces instead of this continuous weighted path space. |
| $B,\ \Vert \cdot\Vert _B$ | Local ball B_(L/8), with gradient-L2 plus velocity-L6 norm. | `Breakdown.Periodic.r3Factor`; `Breakdown.Periodic.torusFactor` The corresponding formal interface is shell data; the same letter B is locally reused for an abstract operator only in Lemma 8.10. |
| $f_\zeta,\ F_\zeta$ | Local linearized advection source and its divergence-form tensor. | `Breakdown.Periodic.r3Factor`; `Breakdown.Periodic.torusFactor` The tensor is extended by zero using the flat compact cutoff coefficient. |
| $\mathcal A,\ \mathcal A_L$ | Time-integrated whole-space and periodic linear interactions determined by local restriction. | `Breakdown.Periodic.r3Factor`; `Breakdown.Periodic.torusFactor`; `Breakdown.Periodic.operatorNormBounds_holds` The formal statements use instantaneous factors and induced bounded sequence operators. |
| $r_E,\ C_E$ | Common support radius and L1-to-X norm bound for the fixed finite-dimensional correction space E. | Local analytic notation; no separately identified declaration. Existence follows by choosing a basis and finite-dimensional norm equivalence; no numerical value is fixed. |
| $\mathcal L_L,\ \mathcal R_L^a,\ \mathcal R_L$ | Periodic linearized equation, its approximate right inverse, and its corrected exact right inverse. | `Breakdown.Periodic.shellInverseTransfer`; `Breakdown.Periodic.rightInversePerturb` The exact continuous formula differs from the formal sequence presentation. |
| $C_1,\ C_2,\ C_B,\ D,\ a,\ r,\ \Phi$ | Residual, inverse and bilinear constants; D=2C2, a=‖Fa‖, fixed-point radius r=2Da, and its contraction map. | `Breakdown.Periodic.seqPerturbation` Locally chosen constants of Proposition 8.8, not externally computed certificate constants. |
| $E,Y,Y_L,Z,\ S,G,B,D,\ S_L,G_L^\circ,B_L^\circ,D_L^\circ$ | Banach spaces and free propagation, data injection, interaction and restriction maps in Lemma 8.10. | `Breakdown.Periodic.shellInverseTransfer` This notation is local to the abstract lemma; it renames the theorem arguments. |
| $\mathsf Q,\ \mathsf Q_L,\ \mathcal C,\ \mathcal C_L,\ \mathcal H,\ \mathcal H_L$ | Free resolvents, full chain operators, and reduced operators on the common restriction space. | `Breakdown.Periodic.shellInverseTransfer` The prose derives the full elimination/reconstruction identity. |
| $R_f,\ R_H,\ R_{H,L},\ q,\ K_f,\ \delta,\ C_\circ$ | Right inverses and quantitative bounds in the shell-transfer lemma. | `Breakdown.Periodic.shellInverseTransfer` The norm and smallness conditions match the formal statement. |
| $T,\ u_L,\ u_{\mathrm{per}}$ | Terminal time L^(-2), large-torus solution, and its period-one rescaling. | `Breakdown.Periodic.torusBlowup_of_parts`; `Breakdown.Periodic.transplantNorm` The formal assembly chooses a small T directly. |
| $h,\ U_{\mathrm{per}},\ s,\ y$ | Remaining time T-t, rescaled periodic field, similarity time and similarity position in Proposition 9.1. | `Breakdown.Periodic.approxFieldProperties_holds` The local similarity convergence is derived from physical gradient and L6 error bounds. |
| $v,p,a,p_0,g,b,\widetilde v,\widetilde p$ | Competitor solution, affine pressure coefficient, periodic pressure part, integrated frame velocity, translation and transformed solution. | `Breakdown.Periodic.movingFrameReduction` These symbols are local to the pressure reduction; b here is a time-dependent translation. |
| $\nu,\ \widehat v,\ \widehat p$ | Viscosity and the viscosity-one rescaling of a hypothetical global competitor. | `Breakdown.Periodic.breakdownOnTorus_of_torusBlowup` The initial datum is scaled by nu. |
| $\lambda,\theta,\mu_n,t_n,u_n,u_n^a,z_n$ | Geometric scale, correction decay, remaining piece scale, piece start, exact piece, approximate piece and bounded correction. | `Breakdown.Periodic.stepScale`; `Breakdown.Periodic.stepStart`; `Breakdown.Periodic.gluePieces`; `Breakdown.Periodic.seqPerturbation` The formal implementation may subdivide the profile period before choosing lambda. |
| $c_0,\ Z,\ M,\ N$ | Positive piece lower bound, correction bound, optional upper bound, and an index beyond which the correction is small. | `Breakdown.Periodic.approxSizes`; `Breakdown.Periodic.glueUnbounded` Used only in Lemma 9.5 and its explicitly identified late-time estimate. |

The symbols $C$, $C_1$, $C_2$ and their variants denote positive constants whose dependence is stated at use; their value may increase after an inequality. Constants in large-torus comparisons are independent of $L$ until $L$ is chosen. The notation $a\lesssim b$ abbreviates $a\le Cb$ with those dependencies. Vector, matrix and multilinear norms are Euclidean or the corresponding operator norms; changing between fixed-dimensional equivalent norms changes only $C$. All whole-space integrals use Lebesgue measure, and all vector-valued time integrals are Bochner integrals. Test fields are real, smooth, compactly supported and divergence-free unless another test class is specified.
<!-- /passage:sec-notation -->

## 1. The conditional theorem and its proof

<!-- passage:sec-1-the-conditional-theorem-and-its-proof -->

<a id="1.1"></a>

### 1.1 The profile hypothesis

We work first with viscosity one:

$$
\partial_tu-\Delta u+(u\cdot\nabla)u+\nabla p=0,
\qquad \operatorname{div}u=0.
\tag{1.1}
$$

**Definition 1.1 (recurrent similarity profile; paper (1.2)–(1.3), p. 2).** A profile consists of smooth fields $W:\mathbb R\times\mathbb R^3\to\mathbb R^3$ and $q:\mathbb R\times\mathbb R^3\to\mathbb R$, a number $S>0$, and an orthogonal map $R:\mathbb R^3\to\mathbb R^3$, satisfying

$$
\partial_sW+\frac12W+\frac12(y\cdot\nabla)W-\Delta W
 +(W\cdot\nabla)W+\nabla q=0,
\qquad \operatorname{div}W=0,
\tag{1.2}
$$

$$
W(s+S,y)=R\,W(s,R^{-1}y),\qquad W\not\equiv0,
\tag{1.3}
$$

and, for one finite constant independent of $s$ and $y$,

$$
|W(s,y)|\le C_W(1+|y|)^{-1},\qquad
|\nabla W(s,y)|\le C_W(1+|y|)^{-2}.
\tag{1.4}
$$

An orthogonal map here may reverse orientation. Define its action on fields by $\rho_Rf(y)=R f(R^{-1}y)$. The gradient norm and the Navier–Stokes equation are invariant under this action.

The formal profile predicate records the same equation and recurrence, together with bounds for second spatial derivatives of the velocity and the first spatial derivative of the pressure.

The extra bounds are

$$
|\nabla^2W(s,y)|\le C(1+|y|)^{-3},\qquad
|\nabla q(s,y)|\le C(1+|y|)^{-3}.
\tag{1.5}
$$

The spatial regularity argument and the pressure reconstruction in Appendix A explain their derivation from the profile hypothesis. This is an analytic bridge supplied in the exposition. The linked formal predicate itself assumes those bounds. The proof of pressure decay also removes the harmonic ambiguity in reconstructing pressure; spatial derivative estimates for $W$ alone do not justify an unsupported estimate for $\partial_sW$.

For a prospective blow-up time $T>0$, put

$$
s=\log\frac{T}{T-t},\qquad y=\frac{x}{\sqrt{T-t}},\qquad
u_T^*(t,x)=(T-t)^{-1/2}W(s,y),
\quad p_T^*(t,x)=(T-t)^{-1}q(s,y).
\tag{1.6}
$$

Section 3 verifies the equation, the recurrence and the norm identities in these variables. The time variable $s$ is normalised so that $s=0$ at $t=0$. This normalisation matters when comparing the solution on the unit torus with the original profile.

<a id="1.2"></a>

### 1.2 Theorem A: the full construction

**Theorem A (conditional finite-time blow-up; paper Theorem 1.1, p. 3).** Assume Definition 1.1. There are a number $\kappa\in(0,1/4)$ and positive constants $c,C$ with the following properties.

There is a smooth compactly supported divergence-free datum $u_0$ on $\mathbb R^3$ whose viscosity-one solution has smooth velocity and pressure on $[0,1)\times\mathbb R^3$, satisfies $\|u(t)\|_2\le\|u_0\|_2$, and obeys

$$
c(1-t)^{-1/4}\le\|\nabla u(t)\|_2\le C(1-t)^{-1/4},
\qquad
\|\nabla(u(t)-u_1^*(t))\|_2\le C(1-t)^{\kappa-1/4}.
\tag{A-space}
$$

There are a time $T\in(0,1]$, a smooth divergence-free datum on the unit torus, and a solution $u_{\mathrm{per}}$ with smooth periodic velocity and pressure on $[0,T)\times\mathbb T^3$ such that

$$
c(T-t)^{-1/4}\le\|u_{\mathrm{per}}(t)\|_{H^1(\mathbb T^3)}
 \le C(T-t)^{-1/4},
\tag{A-torus-rate}
$$

$$
\|u_{\mathrm{per}}(t)-u_T^*(t)\|_{H^1(B_{1/16})}
 \le C(T-t)^{\kappa-1/4}.
\tag{A-torus-profile}
$$

The constants can be enlarged, and $\kappa$ decreased, to use common values in these assertions. On whole space there are also a fixed finite-dimensional subspace $E\subset C^\infty_{c,\mathrm{div}}$ and a fixed $\varepsilon_0>0$ such that every $w_0\in X$ with $\|w_0-W(0)\|_X\le\varepsilon_0$ admits some $\gamma\in E$ for which a mild solution with datum $w_0+\gamma$ satisfies the estimates in (A-space). If $w_0$ is smooth and compactly supported, the resulting solution has the stated smoothness and finite-energy bound. At least one such compactly supported $w_0$ exists.

The fixed space $E$ is chosen before the nearby datum $w_0$; only the correction $\gamma$ depends on that datum. This quantifier order is the content of the finite-codimension assertion. It does not assert an open set of blowing-up data, and it does not identify a smooth manifold of such data.

**Proof, organised by dependency.** Section 2 establishes the space, heat estimates, the mild equation and the compactness of the positive-time linearised interaction. Section 3 places $u_1^*$ in that framework and proves a strictly positive lower bound for its rescaled norm. Section 4 turns those facts into a finite-dimensional spectral obstruction. Section 5 selects compactly supported corrections which satisfy the boundary condition at infinite rescaled time. Section 6 solves the nonlinear correction equation, proves the fixed-$E$ assertion and constructs the compact initial approximation. Section 7 identifies the resulting mild solution with the classical solution on every compact time interval, proves its uniform energy bound and derives the two-sided rate. Sections 8 and 9 construct the exact unforced periodic solution and rescale it to the unit torus. These steps prove all clauses of Theorem A. The auxiliary analytic results used at those steps are stated and proved or supplied with exact external hypotheses in Appendix A. $\square$

The norm estimates have different roles. The upper bounds control the perturbation space. The positive lower bounds prove growth of the solution itself. The convergence bounds say that the error is smaller than the background by a factor tending to zero. In whole-space similarity variables $u(t,x)=(1-t)^{-1/2}U(s,y)$ they imply

$$
\|\nabla(U(s)-W(s))\|_2\le C e^{-\kappa s}.
\tag{1.7}
$$

For the periodic solution the comparison is local in physical coordinates. Its comparison domain in similarity coordinates is $B_{(16\sqrt{T-t})^{-1}}$. Every fixed similarity ball eventually lies in that domain. The estimate does not assert convergence in a whole-space norm of a periodically repeated field.

<a id="1.3"></a>

### 1.3 What the linked formal endpoints state

The library proves that its smooth-profile premise implies the two formal breakdown predicates.

On whole space the formal conclusion says: for every viscosity $\nu>0$, some smooth compactly supported divergence-free datum has no global smooth solution whose kinetic energy stays bounded. On the torus it says: for every $\nu>0$, some smooth periodic divergence-free datum has no global smooth solution with periodic velocity, with no periodicity hypothesis imposed on its pressure. These are the predicates `Breakdown.BreakdownOnSpace` and `Breakdown.BreakdownOnTorus`.

Those endpoints do not display all the rates, profile comparisons and simultaneous choices in Theorem A. Intermediate declarations carry additional construction information, and Sections 4–9 describe it where it is used. The correspondence records therefore distinguish a matching local statement from an abstract result used in its proof, or an endpoint with a different conclusion. The paper's continuous weighted right inverse and the formal proof's bounded sequences of short pieces also receive separate descriptions.

The whole-space endpoint follows from the constructed solution and finite-energy uniqueness; the periodic endpoint also uses a moving change of frame to handle a pressure with an affine part. The change

$$
u^{(\nu)}(t,x)=\nu u(\nu t,x),\qquad
p^{(\nu)}(t,x)=\nu^2p(\nu t,x)
\tag{1.8}
$$

carries a viscosity-one solution to viscosity $\nu$. Sections 7 and 9 give the precise exclusions and the pressure normalisation needed for them.
<!-- /passage:sec-1-the-conditional-theorem-and-its-proof -->

## 2. The analytic space and the mild equation

<!-- passage:sec-2-the-analytic-space-and-the-mild-equation -->

The construction needs a norm in which the profile is finite, smooth compact data are dense, and the free evolution contracts after a similarity period. All three requirements are met by

$$
X=\{u\in L^6(\mathbb R^3;\mathbb R^3):\nabla u\in L^2,\ \operatorname{div}u=0\},
\qquad \|u\|_X=\|\nabla u\|_2.
$$

Derivatives and divergence in this definition are distributional. The gradient norm uses the Euclidean norm on the full matrix of first derivatives. An element has its specified $L^6$ representative; this removes the ambiguity of adding a constant to a homogeneous Sobolev class.

### Lemma 2.1. The space and its compactly supported dense subspace

*Paper correspondence: §3.1, p. 12, especially (3.1) and (3.2).*

The space $X$ is a real Hilbert space, the inequality $\|u\|_6\le C_S\|u\|_X$ holds on it, and $C^\infty_{c,\mathrm{div}}(\mathbb R^3)$ is dense in it.

**Proof.** First consider a scalar compactly supported smooth function $f$. The elementary three-dimensional inequality

$$
\|g\|_{3/2}\le C\sum_{j=1}^3\|\partial_jg\|_1
$$

follows from the fundamental theorem of calculus on each coordinate line: bound $|g(x)|$ by the line integral of $|\partial_jg|$ in direction $j$, multiply the three bounds, take their square root, and integrate. Repeated Cauchy–Schwarz gives

$$
\int |g|^{3/2}
\le\prod_{j=1}^3\|\partial_jg\|_1^{1/2}.
$$

Apply this to $g=|f|^4$. Since $|\nabla |f|^4|\le4|f|^3|\nabla f|$, Hölder gives $\|f\|_6^4\le C\|f\|_6^3\|\nabla f\|_2$. Division gives the desired Sobolev bound; the same argument applies to a vector field by using its Euclidean magnitude.

For a general field with $u\in L^6$ and $\nabla u\in L^2$, choose a smooth cutoff $\chi_R$ equal to one on $B_R$ and zero outside $B_{2R}$. Then

$$
\|\nabla(\chi_Ru-u)\|_2
\le\|(1-\chi_R)\nabla u\|_2
+CR^{-1}\|u\|_{L^2(B_{2R}\setminus B_R)}
\le o(1)+C\|u\|_{L^6(B_{2R}\setminus B_R)}\longrightarrow0.
$$

Mollification of each cutoff proves the scalar completion assertion and extends the Sobolev bound. Consequently a sequence that is Cauchy in the gradient norm converges in $L^6$ to a field $u$ whose distributional gradient is the $L^2$ limit of the gradients. Divergence passes to the limit. The inner product $\int\nabla u:\nabla v$ is positive definite, since a field with zero distributional gradient is constant and a constant in $L^6(\mathbb R^3)$ is zero. These facts prove completeness and the Hilbert-space assertion.

The cutoff just used need not preserve divergence. To obtain solenoidal density, first work in Fourier variables with convention $\widehat f(\xi)=\int e^{-2\pi i x\cdot\xi}f(x)\,dx$. The transformed gradient identifies $u$ with $2\pi|\xi|\widehat u\in L^2$, subject to $\xi\cdot\widehat u=0$ and the reality symmetry $\widehat u(-\xi)=\overline{\widehat u(\xi)}$. The weighted transform determines $\widehat u$ as a locally integrable function: Cauchy–Schwarz applies near zero because $|\xi|^{-1}\in L^2(B_1)$ in dimension three. Approximate the weighted transform in $L^2$ by smooth functions supported on compact annuli, apply the orthogonal projection

$$
P_\xi=I-\frac{\xi\otimes\xi}{|\xi|^2}\quad(\xi\ne0),
$$

and impose the reality symmetry by averaging. Projection is bounded and smooth on each annulus, so these operations preserve convergence. Divide each approximant by $2\pi|\xi|$ before taking its inverse transform. The resulting $f_n$ are solenoidal Schwartz fields with Fourier support away from zero and converge to $u$ in $X$. The vector potential $A_n=(-\Delta)^{-1}\operatorname{curl}f_n$ is Schwartz too, and $\operatorname{curl}A_n=f_n$. Therefore $\operatorname{curl}(\chi_RA_n)$ is smooth, compactly supported and solenoidal; the Schwartz bounds show that its gradient converges in $L^2$ to $\nabla f_n$ as $R\to\infty$. Choosing $R$ successively for each $n$ completes the approximation. This also proves that no extra spatial decay has been imposed on an arbitrary member of $X$. $\square$

The formal space stores a solenoidal Fourier representative in a closed subspace of $L^2$.

Its velocity map recovers the corresponding $L^6$ field, and its embedding records the physical gradient norm on smooth decaying fields.

The formal density theorem also approximates a field and its Laplacian together when the latter belongs to the same space.

### Lemma 2.2. Heat, dilation and orthogonal changes of coordinates

*Paper correspondence: §3.1, p. 12, equations (3.3)–(3.5).*

For $t\ge0$, let $H_t=e^{t\Delta}$. For $\mu>0$ and $R\in O(3)$, define

$$
D_\mu u(x)=\sqrt\mu\,u(\sqrt\mu x),
\qquad \rho_Ru(x)=R\,u(R^{-1}x).
$$

Heat flow is a strongly continuous contraction semigroup on $X$, dilation has norm factor $\mu^{1/4}$, and $\rho_R$ is an isometry commuting with both operations.

More precisely,

$$
H_{t+t'}=H_tH_{t'},\quad H_0=I,\quad
\|H_tu\|_X\le\|u\|_X,
$$

$$
D_\mu D_{\mu'}=D_{\mu\mu'},\quad
D_\mu H_{\mu t}=H_tD_\mu,\quad
\|D_\mu u\|_X=\mu^{1/4}\|u\|_X.
$$

**Proof.** In Fourier variables, $H_t$ multiplies by $e^{-4\pi^2t|\xi|^2}$. Products give the semigroup identity; its magnitude is at most one. Dominated convergence in the weighted $L^2$ norm gives strong continuity including $t=0$. Direct differentiation gives $\nabla D_\mu u(x)=\mu\nabla u(\sqrt\mu x)$, so changing variables in its squared norm gives the factor $\mu^{1/2}$, and hence the stated norm factor. The algebra and heat covariance follow by substituting the definitions. Orthogonality preserves lengths, measure and the trace defining divergence, and gives all statements about $\rho_R$. Continuity of $\mu\mapsto D_\mu u$ follows first for a compactly supported smooth approximation and then for $u$ by the norm law, uniformly when $\mu$ stays in a compact subinterval of $(0,\infty)$. $\square$

### Lemma 2.3. The bilinear heat estimate

*Paper correspondence: Lemma 3.1 and (3.8), p. 13.*

Set

$$
K(\tau)(u,v)=-\frac12H_\tau\mathbb P\big((u\cdot\nabla)v+(v\cdot\nabla)u\big),\qquad \tau>0,
$$

where $\mathbb P$ has Fourier symbol $P_\xi$. Choose $C_K\ge1$ large enough that

$$
\|H_\tau\mathbb P f\|_X\le C\tau^{-3/4}\|f\|_{3/2},
\qquad
\|K(\tau)(u,v)\|_X\le C_K\tau^{-3/4}\|u\|_X\|v\|_X.
$$

The map $K$ is symmetric and bilinear, is strongly continuous for positive $\tau$, and obeys

$$
H_tK(\tau)(u,v)=K(t+\tau)(u,v),
$$

$$
\mu D_\mu K(\mu\tau)(u,v)=K(\tau)(D_\mu u,D_\mu v),
\qquad
\rho_RK(\tau)(u,v)=K(\tau)(\rho_Ru,\rho_Rv).
$$

**Proof.** The Fourier transform has norm at most one from $L^1$ to $L^\infty$, and its $L^2$ extension is an isometry by Plancherel; interpolation between these two bounds gives the precise Hausdorff–Young inequality $\|\widehat f\|_3\le C\|f\|_{3/2}$ used here. Together with $\|P_\xi\|\le1$, these facts give

$$
\|H_\tau\mathbb P f\|_X
\le2\pi\big\||\xi|e^{-4\pi^2\tau|\xi|^2}\widehat f\big\|_2
\le2\pi\big\||\xi|e^{-4\pi^2\tau|\xi|^2}\big\|_6\|\widehat f\|_3
\le C\tau^{-3/4}\|f\|_{3/2}.
$$

The Gaussian multiplier's $L^6$ norm has the factor $\tau^{-1/2}\tau^{-1/4}$. Approximation by Schwartz inputs and Lemma 2.1 identify the inverse transform with its $L^6$ representative. Since $\|(u\cdot\nabla)v\|_{3/2}\le\|u\|_6\|\nabla v\|_2$, the second estimate follows. The multiplier kills the longitudinal part, so the output is solenoidal. Symmetry and bilinearity follow from the definition. The semigroup identity follows in frequency space. Near any $\tau_0>0$, factor off heat time $\tau_0/2$ and use strong continuity of $H_t$ to prove continuity in $\tau$. Finally, the multiplier $P_\xi$ is homogeneous of degree zero and satisfies $P_{R\xi}R=RP_\xi$; substitution proves the two covariance identities. $\square$

The formal bilinear map is defined by duality against a smoothed test field, and its realized bound has the same time exponent $-3/4$.

This definition avoids assigning a pointwise Fourier transform to every nonlinear product. Its proven covariance and time-shift identities supply exactly the operations used to rescale mild equations.

### Lemma 2.4. Compactness for a fixed coefficient

*Paper correspondence: Lemma 3.2, p. 14.*

For each $u\in X$ and each $\tau>0$, the linear operator $v\mapsto K(\tau)(u,v)$ is compact on $X$.

**Proof.** First take $u=\phi\in C^\infty_{c,\mathrm{div}}$, supported in a ball $B$. For $v\in X$, put $F_v=\phi\otimes v+v\otimes\phi$. Its divergence is $(\phi\cdot\nabla)v+(v\cdot\nabla)\phi$. The Fourier multiplier for $\nabla H_\tau\mathbb P\operatorname{div}$ has norm bounded by $C\tau^{-1}$, since $|\xi|^2e^{-4\pi^2\tau|\xi|^2}\le C\tau^{-1}$. Hence

$$
\|K(\tau)(\phi,v)\|_X\le C\tau^{-1}\|F_v\|_2
\le C\tau^{-1}\|\phi\|_\infty\|v\|_{L^2(B)}.
$$

If $v_n\rightharpoonup0$ in $X$, restriction to $B$ is bounded into $H^1(B)$ because $\|v\|_{L^2(B)}\le|B|^{1/3}\|v\|_6$. The compact embedding $H^1(B)\hookrightarrow L^2(B)$ therefore gives $v_n\to0$ in $L^2(B)$. This is the form of Rellich compactness used here; one proof extends functions boundedly from a ball to a larger ball, then uses uniform translation bounds $\|f(\cdot+h)-f\|_2\le|h|\|\nabla f\|_2$ and finite step-function approximations on a bounded region. Thus the displayed estimate sends weakly null sequences to strongly null sequences, proving compactness in the Hilbert space $X$.

For arbitrary $u$, choose $\phi_n\to u$ in $X$ as in Lemma 2.1. Lemma 2.3 gives

$$
\|K(\tau)(u,\cdot)-K(\tau)(\phi_n,\cdot)\|_{X\to X}
\le C_K\tau^{-3/4}\|u-\phi_n\|_X\longrightarrow0.
$$

An operator-norm limit of compact operators is compact: for a bounded sequence, successively take subsequences on which the approximating operators converge, choose the diagonal subsequence, and use the norm error to make its images under the limit operator Cauchy. $\square$

The formal compactness theorem is first stated for coefficients in the dense test-field subspace.

Its abstract framework retains that dense-subspace formulation; closure in operator norm gives the all-coefficient statement used above.

### Lemma 2.5. Duhamel integrals and the mild equation

*Paper correspondence: §2.1, pp. 10–11; Lemma 3.3, p. 14; Appendix A.1, p. 47.*

For continuous $f,g:[a,b]\to X$, the Bochner integral

$$
B_a(f,g)(t)=\int_a^tK(t-r)(f(r),g(r))\,dr
$$

is defined for every $t\in[a,b]$, is continuous in $t$, and satisfies

$$
\|B_a(f,g)(t)\|_X\le4C_K(t-a)^{1/4}\|f\|_{C([a,b];X)}\|g\|_{C([a,b];X)}.
$$

The Bochner integral is continuous even at the moving endpoint where its kernel has the integrable singularity $(t-r)^{-3/4}$.

A mild solution on $[a,b]$ is a continuous $X$-valued map satisfying

$$
u(t)=H_{t-a}u(a)+B_a(u,u)(t).
$$

On $[a,b)$, impose this identity on every compact subinterval. The value assigned to $K(0)$ at the single integration endpoint does not affect the integral. A proof of the integral assertion, including endpoint continuity, is given in Lemma A.1.

### Lemma 2.6. Finite-interval linearized evolution

*Paper correspondence: Lemma 3.4, p. 14; Appendix A.1, p. 47.*

For continuous $f,g:[a,b]\to X$, the equation $h=2B_a(f,h)+g$ has exactly one continuous solution, and the map $g\mapsto h$ is bounded and linear in the supremum norm.

The bound may depend on $b-a$ and $\sup\|f\|_X$. No smallness of the background on the whole interval is required. Lemma A.2 proves the assertion and explains the formal library's construction by short time pieces.

### Lemma 2.7. Restarting and uniqueness

*Paper correspondence: Lemma 3.5, p. 15; Appendix A.1, p. 47.*

If $u(t)=H_{t-a}u(a)+B_a(f,h)(t)$ and $a\le m\le t\le b$, then

$$
u(t)=H_{t-m}u(m)+\int_m^tK(t-r)(f(r),h(r))\,dr.
$$

Two continuous mild solutions with the same value at the initial time agree throughout their common interval.

Lemma A.2 proves both assertions. The uniqueness class here is the continuous $X$-valued mild class. Comparisons with a more broadly defined smooth solution require the additional physical regularity bridge discussed in §7 and the endpoint section.

### Lemma 2.8. From solenoidal tests to the mild equation

*Paper correspondence: Lemma 3.6, p. 15; Appendix A.1, pp. 47–48.*

Suppose $u\in C([a,b];X)$ and, for each $\psi\in C^\infty_{c,\mathrm{div}}$, the pairing $\langle u(t),\psi\rangle$ is continuously differentiable with

$$
\frac{d}{dt}\int u\cdot\psi
=\int u\cdot\Delta\psi+\sum_{i,j}u_i u_j\partial_i\psi_j.
$$

Then $u$ is mild on $[a,b]$. Lemma A.3 gives the exact distributional-to-integral theorem used and checks its hypotheses. Solenoidal tests remove the pressure term by integration by parts; they do not assume that pressure vanishes.

The formal weak-to-mild theorem additionally assumes smooth decaying slices and $L^2$ continuity of their time differences.

Those hypotheses are available for the physical profile after the spatial-derivative and pressure estimates in Lemmas A.5 and A.6. They are not part of the mathematical statement of Lemma 2.8.

### Lemma 2.9. The periodic estimate has a uniform constant

*Paper correspondence: §3.6 and Lemma 3.7, pp. 15–16; Appendix A.1, p. 48.*

For $L>0$ set $Q_L=[-L/2,L/2)^3$ and

$$
X_L=\{u\in H^1(\mathbb T_L^3;\mathbb R^3):\operatorname{div}u=0,\ \int_{Q_L}u=0\},
\qquad \|u\|_{X_L}=\|\nabla u\|_{L^2(Q_L)}.
$$

The zero mean removes the constant Fourier mode. With Fourier coefficients indexed by $k\in L^{-1}\mathbb Z^3$, heat flow multiplies by $e^{-4\pi^2t|k|^2}$. Its contraction and continuity follow term by term. There are constants independent of $L$ such that

$$
\|u\|_{L^6(Q_L)}\le C\|u\|_{X_L},\qquad
\|H_\tau\mathbb P_Lf\|_{X_L}\le C\tau^{-3/4}\|f\|_{L^{3/2}(Q_L)}
$$

whenever $f$ has mean zero. Consequently the periodic bilinear map $K_L$ satisfies the bound of Lemma 2.3 with a constant independent of the period.

The periodic Fourier construction provides the heat and bilinear operations used by the torus proof.

Lemma A.4 proves the uniform bound. On the unit torus, $\|u\|_{X_1}\le\|u\|_{H^1}\le C\|u\|_{X_1}$. For other periods the first-order homogeneous norm is the scale-compatible one. Under $D_\mu$, the period becomes $L/\sqrt\mu$ and the gradient norm retains the factor $\mu^{1/4}$.
<!-- /passage:sec-2-the-analytic-space-and-the-mild-equation -->

## 3. The profile in physical variables

<!-- passage:sec-3-the-profile-in-physical-variables -->

### Proposition 3.1. A profile supplies a recurrent mild solution

*Paper correspondence: equations (1.2)–(1.5), p. 2; Proposition 4.1, pp. 16–17.*

Assume the profile of Theorem A. For any $T>0$, put

$$
s=\log\frac{T}{T-t},\qquad y=\frac{x}{\sqrt{T-t}},\qquad
u_T^*(t,x)=(T-t)^{-1/2}W(s,y),\qquad
p_T^*(t,x)=(T-t)^{-1}q(s,y).
$$

The physical field obtained from the profile is a smooth Navier–Stokes solution and a continuous $X$-valued mild solution before its terminal time.

**Proof.** Write $a=T-t$. Then $s_t=a^{-1}$ and $y_t=y/(2a)$, so

$$
\partial_tu_T^*=a^{-3/2}\left(\partial_sW+\tfrac12W+\tfrac12(y\cdot\nabla)W\right),
$$

$$
\Delta_xu_T^*=a^{-3/2}\Delta_yW,\quad
(u_T^*\cdot\nabla_x)u_T^*=a^{-3/2}(W\cdot\nabla_y)W,\quad
\nabla_xp_T^*=a^{-3/2}\nabla_yq.
$$

The similarity equation therefore gives the physical momentum equation, and $\operatorname{div}_xu_T^*=a^{-1}\operatorname{div}_yW=0$. Smoothness follows from the smooth change of variables. The profile bounds become

$$
|u_T^*(t,x)|\le\frac{C_W}{\sqrt{T-t}+|x|},\qquad
|\nabla u_T^*(t,x)|\le\frac{C_W}{(\sqrt{T-t}+|x|)^2}.
$$

Their sixth and second powers, respectively, are integrable in space, so every slice belongs to $X$. On any compact time interval below $T$, the second bound supplies one $L^2$ majorant for the gradients. Dominated convergence makes the trajectory continuous in $X$. Multiply the momentum equation by a compact solenoidal test, integrate by parts, and use Lemma 2.8. This gives the mild equation on every compact interval. $\square$

For $T=1$, set $u^*=u_1^*$, $\lambda=e^{-S}$ and $t_n=1-\lambda^n$. The recurrence of the profile gives

$$
u^*(1-\lambda(1-t))=\rho_RD_{1/\lambda}u^*(t),
\qquad
u^*(t_n+\lambda^n\sigma)=\rho_R^nD_{\lambda^{-n}}u^*(\sigma).
$$

The first identity follows because the new similarity time is $s+S$ and the new spatial variable is $\lambda^{-1/2}y$; the second follows by induction. Nontriviality persists: if the physical field vanished for $0\le t<1$, then $W$ would vanish for $s\ge0$ and recurrence would make it vanish at every similarity time.

The formal orbit theorem embeds this same profile into the abstract heat and dilation framework and retains its twisted recurrence.

The formal profile premise writes the second-derivative and pressure-gradient bounds explicitly. Lemmas A.5 and A.6 supply the analytic implications from the paper's profile assumptions; this account does not claim that those implications have been compiled as a new Lean bridge.

### Lemma 3.2. The orbit norm stays away from zero

*Paper correspondence: Lemma 4.2, p. 17; a proof following the formal small-data route.*

There are constants $0<m\le M$ with $m\le\|W(s)\|_X\le M$ for every $s\in\mathbb R$.

**Proof.** Continuity in $X$ and the isometric recurrence make $s\mapsto\|W(s)\|_X$ continuous and $S$-periodic, so it has a finite upper bound. To obtain a positive lower bound by the formal route, use the small-data statement proved in Lemma A.2: there is $\varepsilon>0$ such that every $x\in X$ with $\|x\|_X\le\varepsilon$ generates a mild solution $v$ on $[0,1]$ with $\sup_t\|v(t)\|_X\le2\|x\|_X$.

Fix a similarity phase $s_0$ for which $\|W(s_0)\|_X\le\varepsilon$. Its physical profile starting at this phase has initial value $W(s_0)$, so mild uniqueness identifies it with $v$ on $[0,1)$. Undoing the dilation at $t=1-e^{-\sigma}$ gives

$$
\|W(s_0+\sigma)\|_X\le2e^{-\sigma/4}\|W(s_0)\|_X,\qquad \sigma\ge0.
$$

For $\sigma=nS$, the left-hand norm equals $\|W(s_0)\|_X$. Taking $n$ large enough that $2e^{-nS/4}<1$ forces $W(s_0)=0$. The same estimate then makes every later slice zero; recurrence transports any earlier slice into that future region. This contradicts nontriviality. Thus every slice has norm greater than $\varepsilon$, and one may take $m=\varepsilon$. $\square$

The formal lower-bound proof uses small-data existence, mild uniqueness and recurrence to exclude an arbitrarily small slice.

The paper instead proves that a zero slice is impossible and takes the minimum over one period. Both arguments give the positive lower coefficient required for blow-up. Neither is a numerical lower bound for the unknown profile.

### Corollary 3.3. The background has the required rate

*Paper correspondence: Lemma 4.2 and (4.4), p. 17.*

For $0\le t<1$,

$$
m(1-t)^{-1/4}\le\|u^*(t)\|_X\le M(1-t)^{-1/4}.
$$

**Proof.** The identity $u^*(t)=D_{(1-t)^{-1}}W(-\log(1-t))$ and the dilation norm law give this directly from Lemma 3.2. $\square$

The factor $(1-t)^{-1/4}$ comes from the dilation norm, while positivity of its lower coefficient comes from the recurrent orbit.

The pointwise profile bound alone only supplies upper estimates. The lower estimate uses the equation through uniqueness, as the preceding proof makes explicit.
<!-- /passage:sec-3-the-profile-in-physical-variables -->

## 4. The monodromy and the exceptional directions

<!-- passage:sec-4-the-monodromy-and-the-exceptional-directions -->

Fix the profile from Section 1, put $\lambda=e^{-S}$ and $t_1=1-\lambda$, and write $\rho=\rho_R$ for its action on vector fields. We use $G(t)=e^{t\Delta}$ and the bilinear map $K$ from Section 2. All operator norms in this section are taken on the indicated Banach spaces. The norm on $X$ is $\|\nabla u\|_2$.

The linear equation about $u^*=u^*_1$ has a bounded solution operator on $[0,t_1]$. Denote it by $U$:

$$
Ug=g+2B(u^*,Ug),\qquad
B(f,h)(t)=\int_0^tK(t-s)(f(s),h(s))\,ds.
$$

Thus $h_\chi=U(G(\cdot)\chi)$ is the linearized solution with initial value $\chi$. Its value at the end of the period must be returned to the original scale and orientation. This defines

$$
\mathcal M\chi=\rho^{-1}D_\lambda h_\chi(t_1).
\tag{4.1}
$$

The next two lemmas construct this operator through short intervals. This follows the organisation of the Lean transfer proof and makes the compactness statement precise before any spectrum is considered.

### Lemma 4.1. Compactness of the endpoint interaction

*Paper correspondence: Lemma 3.2 and the compactness argument in Lemma 4.4, pp. 14 and 18–19.*

Let $0<T\leq1$ and let $a\in C([0,T];X)$. The operator

$$
\mathcal C_a f=\int_0^TK(T-s)(a(s),f(s))\,ds,
\qquad C([0,T];X)\longrightarrow X,
\tag{4.2}
$$

is compact.

**Proof.** Lemma 2.4 gives compactness of $K(r)(v,\cdot)$ for every $r>0$ and every $v\in X$. To use it inside an integral, we also need control of the time endpoint. Set $M_a=\sup_s\|a(s)\|_X$. For $0<\varepsilon<T$, the contribution from $[T-\varepsilon,T]$ has operator norm at most

$$
C_KM_a\int_{T-\varepsilon}^T(T-s)^{-3/4}\,ds
=4C_KM_a\varepsilon^{1/4}.
\tag{4.3}
$$

It remains to prove compactness of the integral over $[0,T-\varepsilon]$.

For a fixed $v\in X$, the map $r\mapsto K(r)(v,\cdot)$ is continuous in operator norm on each compact subinterval of $(0,\infty)$. Here is why the strong continuity of the heat semigroup suffices. Choose $r_0>0$ smaller than all times under consideration. The heat-shift identity gives

$$
K(r)(v,\cdot)=G(r-r_0)K(r_0)(v,\cdot).
$$

The second factor is compact. Strong convergence of a uniformly bounded family of operators is uniform on a compact subset: cover the compact set by finitely many small balls, use convergence at their centres, and use the uniform operator bound on each ball. Apply this to the closure of the image of the unit ball under $K(r_0)(v,\cdot)$. This proves the asserted operator-norm continuity. The bilinear estimate also gives, for $r\geq\varepsilon$,

$$
\|K(r)(v,\cdot)-K(r)(w,\cdot)\|
\leq C_K\varepsilon^{-3/4}\|v-w\|_X.
$$

Consequently $s\mapsto K(T-s)(a(s),\cdot)$ is an operator-norm continuous map from $[0,T-\varepsilon]$ into the compact operators on $X$.

Choose a finite partition so that replacing this map on each partition interval $I_j$ by its value $C_j$ at one point changes it uniformly by at most $\delta$. The resulting approximation to the integral operator is

$$
f\longmapsto\sum_jC_j\int_{I_j}f(s)\,ds.
$$

Each summand is compact: the integral is a bounded operator into $X$, followed by the compact operator $C_j$. The approximation error is at most $T\delta$ in operator norm. The truncated integral is therefore compact. Letting $\varepsilon\downarrow0$ in (4.3) proves the lemma, since compact operators are closed under operator-norm limits. $\square$

The formal endpoint compactness result applies to an arbitrary continuous coefficient on a short time interval. Its proof first treats coefficients of the form $\phi(s)v$ and then uses density; the norm-limit argument above records the same two requirements, spatial compactness and an integrable time singularity. The declarations are `Breakdown.compactSimple` and `Breakdown.compactPiece`. The latter assumes the abstract compact-kernel property, which the Fourier realization supplies through the dense test-field subspace.

### Lemma 4.2. The monodromy is a compact perturbation of a contraction

*Paper correspondence: (4.9)–(4.10) and Lemma 4.4, pp. 18–19.*

The operator $\mathcal M$ is bounded, and

$$
\mathcal M-\mathcal M_0\text{ is compact},\qquad
\mathcal M_0=\rho^{-1}D_\lambda G(1-\lambda),\qquad
\|\mathcal M_0\|\leq e^{-S/4}<1.
\tag{4.4}
$$

**Proof.** Let $M_W=\sup_s\|W(s)\|_X$, which is finite by Section 3. Choose a positive integer $k$ and put

$$
\delta=S/k,\qquad \mu=e^{-\delta},\qquad \tau=1-\mu,
\qquad Y=C([0,\tau];X).
$$

For each integer $n\geq0$, define the profile on the $n$th short interval, after restoring its spatial scale, by

$$
a_n(s)=D_{(1-s)^{-1}}W(n\delta-\log(1-s)),
\qquad 0\leq s\leq\tau.
\tag{4.5}
$$

The dilation law gives $\|a_n\|_Y\leq e^{\delta/4}M_W$. Define the bounded operators

$$
A_nf=2B(a_n,f),\qquad
(\Gamma x)(s)=G(s)x,\qquad
\operatorname{Ev}f=D_\mu f(\tau).
\tag{4.6}
$$

Integration of $(s-r)^{-3/4}$ yields

$$
\|A_n\|\leq8C_K\tau^{1/4}e^{\delta/4}M_W.
$$

The right side tends to zero as $k\to\infty$. We fix $k$ so large that it is at most $1/4$, uniformly in $n$. Hence

$$
(I-A_n)^{-1}=\sum_{j=0}^{\infty}A_n^j,
\qquad \|(I-A_n)^{-1}\|\leq4/3.
\tag{4.7}
$$

The short-interval evolution followed by the spatial rescaling is

$$
S_n=\operatorname{Ev}(I-A_n)^{-1}\Gamma.
\tag{4.8}
$$

This is exactly the composition used by `Breakdown.stepMap`. The definitions `Breakdown.MildFramework.profilePiece`, `Breakdown.MildFramework.stepOp`, `Breakdown.MildFramework.stepFree` and `Breakdown.MildFramework.stepEnd` give its four ingredients. In the source, the period is called $P$ and the number of subdivisions is $k$.

Let $T_0=D_\mu G(\tau)$. Since $\operatorname{Ev}\Gamma=T_0$, the resolvent identity gives

$$
S_n-T_0
=\operatorname{Ev}A_n(I-A_n)^{-1}\Gamma.
\tag{4.9}
$$

Lemma 4.1 shows that $\operatorname{Ev}A_n$ is compact. Thus every $S_n-T_0$ is compact. For each $m$, the difference

$$
S_{m-1}\cdots S_0-T_0^m
$$

is compact. This follows by induction: the next difference is

$$
(S_m-T_0)S_{m-1}\cdots S_0
+T_0(S_{m-1}\cdots S_0-T_0^m),
$$

and compositions of bounded and compact operators are compact.

The twisted recurrence of $W$ gives $a_{n+k}=\rho a_n$. The covariance of $G,K,D$ then implies $S_{n+k}=\rho S_n\rho^{-1}$. After $k$ short intervals the linearized evolution has traversed one similarity period, so

$$
\mathcal M=\rho^{-1}S_{k-1}\cdots S_0.
\tag{4.10}
$$

To verify that this is the operator in (4.1), solve the linearized equation successively on the short intervals, undo each dilation, and join the solutions at their common endpoints. The dilation identities for $G$ and $K$ turn every local integral equation into the linearized equation about $u^*$. The endpoint definition in (4.6) makes the values agree. Uniqueness of the linear Volterra equation on $[0,t_1]$ identifies the joined solution with $h_\chi$. The final inverse twist is $\rho^{-1}$ in both definitions.

The heat and dilation identities also give

$$
(D_\mu G(1-\mu))^k=D_{\mu^k}G(1-\mu^k)
=D_\lambda G(1-\lambda).
\tag{4.11}
$$

For example, the induction step uses $G(t)D_\mu=D_\mu G(\mu t)$ and the geometric sum $(1-\mu)(1+\mu+\cdots+\mu^{k-1})=1-\mu^k$. Equations (4.10)–(4.11) prove compactness in (4.4). Finally $\rho^{-1}$ is an isometry, $\|D_\lambda x\|_X=\lambda^{1/4}\|x\|_X$, and $G(t)$ is a contraction. These facts prove the norm bound. $\square$

The formal monodromy theorem records compactness of the product over the short intervals and the bound $e^{-S/4}$ for its free part. It is `Breakdown.monodromy`, whose precise proposition is `Breakdown.MonodromyStatement`. The equality between that product and the full-period formula is explained above using uniqueness; the two source presentations do not use an identical definition of the period map.

There is also a direct check of the compactness argument in the paper. If $\chi_j\rightharpoonup0$ in $X$, boundedness of the linear evolution implies $h_{\chi_j}(s)\rightharpoonup0$ for each $s$. For $s<t_1$, Lemma 2.4 makes $K(t_1-s)(u^*(s),h_{\chi_j}(s))$ converge strongly to zero. Its norm is bounded uniformly in $j$ by a constant times $(t_1-s)^{-3/4}$. Dominated convergence proves that the integral defining $(\mathcal M-\mathcal M_0)\chi_j$ tends to zero. The weak-sequence criterion applies here because the domain $X$ is a Hilbert space.

### Lemma 4.3. A finite-dimensional exceptional space

*Paper correspondence: Lemma 4.5 and (4.11), p. 19.*

There are numbers $r_1,\Theta,r_2$ and a bounded real projection $P_u$ such that

$$
e^{-S/4}<r_1<\Theta<r_2<1,\qquad
P_u\mathcal M=\mathcal MP_u,
$$

the range $V=\operatorname{ran}P_u$ is finite dimensional, the restriction $\mathcal M_u=\mathcal M|_V$ is invertible, and, for suitable finite constants $C_s,C_u$,

$$
\|\mathcal M^n(I-P_u)\|\leq C_s r_1^n,
\qquad
\|\mathcal M_u^{-n}P_u\|\leq C_u r_2^{-n}
\quad(n\geq0).
\tag{4.12}
$$

In particular,

$$
\sum_{n\geq0}\Theta^{-n}\|\mathcal M^n(I-P_u)\|
+\sum_{n\geq0}\Theta^n\|\mathcal M_u^{-n}P_u\|<\infty.
\tag{4.13}
$$

**Spectral input.** We use the following bounded-operator facts, in the precise form of Engel and Nagel, Chapter IV, §1, especially (1.6)–(1.8), §1.17 and §1.20. Compact perturbations preserve the essential spectral radius. Outside that radius, spectral points in the unbounded Fredholm component are isolated resolvent poles of finite algebraic multiplicity. A contour in the resolvent set separates the corresponding invariant subspaces through its Riesz projection. On each subspace, the restricted spectrum is the enclosed part of the spectrum. The spectral radius formula gives $\lim_n\|T^n\|^{1/n}=r(T)$. These are statements for bounded operators; no spectral-mapping assertion about an unbounded generator is used.

**Proof.** Complexify the real Hilbert space $X$ and extend $\mathcal M$ and $\mathcal M_0$ complex linearly. Their norms are unchanged. In the Calkin algebra the two extensions have the same image, so the essential spectral radius of $\mathcal M$ is at most $a=e^{-S/4}$. Every point with modulus larger than $a$ lies in the unbounded component of the Fredholm domain: it can be connected to infinity while remaining outside the disk containing the essential spectrum. Thus the spectral input applies throughout $\{|z|>a\}$.

For each $r>a$, only finitely many spectral points satisfy $|z|\geq r$. Otherwise the bounded spectrum would contain an accumulation point in that region, contrary to the isolation of its points there. Choose $\Theta\in(a,1)$ whose circle misses the spectrum. Let $P_u$ first denote the complex Riesz projection for the part with $|z|>\Theta$. It has finite rank and commutes with $\mathcal M$. Equivalently, $I-P_u$ is the resolvent integral around $|z|=\Theta$.

The spectrum is invariant under conjugation because $\mathcal M$ is real. The contour formula therefore commutes with conjugation. It follows that $P_u$ preserves the real copy of $X$; restrict it to that copy. Its range remains finite dimensional. The restricted spectrum on $V$ is contained in $\{|z|>\Theta\}$, so $0$ is excluded and $\mathcal M_u$ is invertible.

The stable restricted spectrum is compact and contained in $\{|z|<\Theta\}$, so its radius is strictly less than $\Theta$. Choose $r_1$ between that radius and $\Theta$, also requiring $r_1>a$. On $V$, the inverse has spectral radius strictly less than $\Theta^{-1}$. Choose $r_2\in(\Theta,1)$ whose inverse exceeds this radius. If $V=\{0\}$, any such $r_2$ works and the inverse bound is vacuous. The spectral radius formula supplies constants that bound all powers by $r_1^n$ and $r_2^{-n}$, respectively; enlarging them covers the finitely many powers preceding the eventual bound. Composing with the bounded projections gives (4.12). The two geometric ratios $r_1/\Theta$ and $\Theta/r_2$ are less than one, proving (4.13). $\square$

The formal real dichotomy provides two radii and a finite-rank projection with geometric bounds. In `Breakdown.Spectral.exists_dichotomy` the inverse estimate is written as a lower bound for forward powers on the projection's range, together with surjectivity there. Injectivity follows by taking one forward power; applying the lower bound to the inverse gives (4.12). The exported declaration is `Breakdown.dichotomyHolds`.

The exceptional space contains every mode outside the chosen circle. This includes any neutral modes and any decaying modes whose decay is slower than the chosen rate. The argument computes neither the dimension of this space nor its eigenvalues. Repeated eigenvalues and Jordan blocks are allowed, since the estimates use a strict gap between the chosen radii.
<!-- /passage:sec-4-the-monodromy-and-the-exceptional-directions -->

## 5. A right inverse with compact initial corrections

<!-- passage:sec-5-a-right-inverse-with-compact-initial-corrections -->

Set

$$
\kappa=\frac{\log\Theta}{\log\lambda},\qquad
0<\kappa<\frac14,
\qquad
\|v\|_\kappa=\sup_{0\leq t<1}(1-t)^{1/4-\kappa}\|v(t)\|_X.
\tag{5.1}
$$

Write $C_\kappa$ for the continuous functions $[0,1)\to X$ with finite norm (5.1). Multiplication by the positive weight identifies this space with bounded continuous $X$-valued functions, so it is a Banach space. A field in $C_\kappa$ has an error of order $e^{-\kappa s}$ after returning to similarity variables.

The aim is to solve

$$
v-2B(u^*,v)-G(\cdot)\gamma=g
\tag{5.2}
$$

for an arbitrary $g\in C_\kappa$, with $v\in C_\kappa$ and $\gamma$ in one fixed finite-dimensional space of compactly supported smooth fields. The choice of $\gamma$ enforces the decay condition at large similarity time.

### Lemma 5.1. The exact forcing recurrence

*Paper correspondence: Lemma 4.6 and (4.12)–(4.15), pp. 19–20.*

Let $g\in C_\kappa$ and $\chi\in X$. Let $v$ be the continuous solution on $[0,1)$ of

$$
v=G(\cdot)\chi+2B(u^*,v)+g.
$$

Put $t_n=1-\lambda^n$ and, for $0\leq\sigma\leq t_1$, define

$$
v_n(\sigma)=\rho^{-n}D_{\lambda^n}v(t_n+\lambda^n\sigma),
\qquad
g_n(\sigma)=\rho^{-n}D_{\lambda^n}g(t_n+\lambda^n\sigma),
$$

$$
\chi_n=v_n(0)-g_n(0),\qquad
f_n=\rho^{-1}D_\lambda\big((Ug_n-g_n)(t_1)\big).
\tag{5.3}
$$

Then

$$
v_n=h_{\chi_n}+Ug_n,\qquad
\chi_{n+1}=\mathcal M\chi_n+f_n,\qquad \chi_0=\chi,
\tag{5.4}
$$

and there is a constant $C_g$ such that

$$
\|g_n\|_{C([0,t_1];X)}+\|f_n\|_X
\leq C_g\Theta^n\|g\|_\kappa.
\tag{5.5}
$$

The sequence $f_n$ is linear in $g$ and independent of $\chi$.

**Proof.** The linear Volterra result applies on every $[0,b]$ with $b<1$. Its uniqueness makes these solutions agree on overlaps, producing $v$ on $[0,1)$. Restart its equation at $t_n$ after subtracting $g$:

$$
(v-g)(t)=G(t-t_n)(v-g)(t_n)
+2\int_{t_n}^tK(t-r)(u^*(r),v(r))\,dr.
\tag{5.6}
$$

No time derivative of $g$ is required for this identity. It follows by splitting the original Duhamel integral at $t_n$ and using the heat-shift identity on the earlier portion.

Apply $\rho^{-n}D_{\lambda^n}$ at $t=t_n+\lambda^n\sigma$, and substitute $r=t_n+\lambda^n\sigma'$ in the integral. The heat covariance transforms the first term into $G(\sigma)\chi_n$. The bilinear covariance transforms the integral into $2B(u^*,v_n)(\sigma)$, because the rescaled background is $u^*(\sigma)$. Thus

$$
v_n=G(\cdot)\chi_n+2B(u^*,v_n)+g_n.
$$

Apply the definition and linearity of $U$ to obtain the first identity of (5.4). At adjacent endpoints,

$$
v_{n+1}(0)=\rho^{-1}D_\lambda v_n(t_1),\qquad
g_{n+1}(0)=\rho^{-1}D_\lambda g_n(t_1).
$$

Subtracting these equations gives the recurrence, including exactly the source term in (5.3). At time zero the original equation gives $v(0)-g(0)=\chi$.

For $t=t_n+\lambda^n\sigma$ one has $1-t\geq\lambda^{n+1}$. Since $\kappa-1/4<0$,

$$
\|g_n(\sigma)\|_X
\leq\lambda^{n/4}(1-t)^{\kappa-1/4}\|g\|_\kappa
\leq\lambda^{\kappa-1/4}\Theta^n\|g\|_\kappa.
$$

The definition of $f_n$ bounds its norm by $\lambda^{1/4}(\|U\|+1)\|g_n\|_\infty$. This proves (5.5), and the definition proves the last assertion. $\square$

The formal proof uses a recurrence for rescaled values on short intervals. Its definition `Breakdown.orbitSeq` divides each update by the chosen decay factor. In the one-period notation above, normalising $\chi_n$ by $\Theta^n$ gives exactly that form, with bounded forcing $\Theta^{-n}f_n$. The subtraction of $g_n(0)$ is essential in the continuous-source derivation.

### Lemma 5.2. A compactly supported transversal

*Paper correspondence: the first paragraph of the proof of Proposition 4.3, p. 20.*

There is a finite-dimensional subspace $E\subset C^\infty_{c,\mathrm{div}}(\mathbb R^3)$ such that $P_u|_E:E\to V$ is an isomorphism. Its inverse $J_V:V\to E$ is bounded.

**Proof.** Let $\mathcal D=C^\infty_{c,\mathrm{div}}(\mathbb R^3)$. Its density in $X$ implies density of $P_u\mathcal D$ in $V$: approximate any preimage in $X$ by elements of $\mathcal D$ and apply the continuous map $P_u$. The image $P_u\mathcal D$ is a linear subspace of the finite-dimensional space $V$. Every such subspace is closed, hence $P_u\mathcal D=V$.

Choose a basis $b_1,\ldots,b_d$ of $V$ and choose $e_j\in\mathcal D$ with $P_ue_j=b_j$. Set $E=\operatorname{span}\{e_1,\ldots,e_d\}$. A relation among the $e_j$ projects to the same relation among the basis vectors, so the $e_j$ are independent. Thus $P_u|_E$ is an isomorphism. Its inverse is bounded because its domain is finite dimensional. If $V=\{0\}$, take $E=\{0\}$. $\square$

The compact correction is a lift of the exceptional component through a dense subspace. This is `Breakdown.exists_section`, which constructs a bounded $J:X\to X$ with $P_uJ=P_u$ and image in a given dense linear subspace. Taking $E=J(V)$ gives the formulation above. The range $E$ need not be invariant under $\mathcal M$; its elements need not be eigenfunctions. In particular $(I-P_u)\gamma$ must be kept when evolving a correction $\gamma\in E$.

### Proposition 5.3. A weighted right inverse

*Paper correspondence: Proposition 4.3, pp. 18 and 20–21.*

There is a bounded linear map

$$
\mathcal R:C_\kappa\longrightarrow E\times C_\kappa,
\qquad g\longmapsto(\gamma,v),
$$

such that (5.2) holds and

$$
\max\{\|\gamma\|_X,\|v\|_\kappa\}\leq C_{\mathcal R}\|g\|_\kappa.
\tag{5.7}
$$

**Proof.** Use the forcing sequence of Lemma 5.1. The inverse estimate (4.12) and (5.5) imply absolute convergence of

$$
e_g=-\sum_{m=0}^{\infty}\mathcal M_u^{-(m+1)}P_uf_m.
\tag{5.8}
$$

Indeed the $m$th norm is at most $C_uC_g r_2^{-1}(\Theta/r_2)^m\|g\|_\kappa$. Set $\gamma=J_Ve_g$. Then $\gamma\in E$ and $\|\gamma\|_X\leq C\|g\|_\kappa$. Solve the continuous linearized equation with $\chi=\gamma$. Its endpoint sequence satisfies (5.4).

Let $Q=I-P_u$. Induction in the recurrence gives

$$
P_u\chi_n=-\sum_{m=n}^{\infty}\mathcal M_u^{-(m-n+1)}P_uf_m,
\tag{5.9}
$$

$$
Q\chi_n=\mathcal M^nQ\gamma
+\sum_{m=0}^{n-1}\mathcal M^{n-1-m}Qf_m.
\tag{5.10}
$$

For the first formula, apply $\mathcal M$ to the absolutely convergent tail, then add $P_uf_n$; the first tail term cancels. For the second, iterate the forward recurrence. These computations also show why the stable term $\mathcal M^nQ\gamma$ occurs: the compactly supported lift generally has a nonzero $Q$ component.

The unstable tail is bounded by

$$
\|P_u\chi_n\|_X
\leq\frac{C_uC_g}{r_2-\Theta}\Theta^n\|g\|_\kappa.
\tag{5.11}
$$

For $n\geq1$, the sum in (5.10) is bounded by

$$
C_sC_g\Theta^{n-1}\|g\|_\kappa
\sum_{j=0}^{n-1}(r_1/\Theta)^j.
$$

The geometric sum is uniformly bounded. The initial term is at most $C_s r_1^n\|\gamma\|_X$, hence also at most a constant times $\Theta^n\|g\|_\kappa$. The $n=0$ case follows from the bound for $\gamma$. Therefore

$$
\|\chi_n\|_X\leq C\Theta^n\|g\|_\kappa.
$$

Using $v_n=h_{\chi_n}+Ug_n$ and the heat contraction now yields

$$
\|v_n\|_{C([0,t_1];X)}\leq C\Theta^n\|g\|_\kappa.
\tag{5.12}
$$

If $t=t_n+\lambda^n\sigma$, multiply this inequality by the inverse dilation factor and the weight in (5.1). Since $1-t=\lambda^n(1-\sigma)$ and $\Theta=\lambda^\kappa$, one obtains

$$
(1-t)^{1/4-\kappa}\|v(t)\|_X
\leq C(1-\sigma)^{1/4-\kappa}\|g\|_\kappa
\leq C\|g\|_\kappa.
$$

Thus $v\in C_\kappa$, and (5.7) follows after enlarging the constant. Every operation used to choose $\gamma$ is linear in $g$, and the linear Volterra solution is unique, so $\mathcal R$ is linear.

For completeness, (5.8) is also forced by the decay requirement. If a solution of the recurrence obeys $\|\chi_n\|\leq C\Theta^n$, solve its exceptional recurrence backwards from $N$ to zero. The remaining terminal term is $\mathcal M_u^{-N}P_u\chi_N$, whose norm tends to zero because $\Theta/r_2<1$. Letting $N\to\infty$ recovers (5.8). This explains the condition at infinite similarity time. $\square$

The formal discrete inverse uses a convergent tail sum for the exceptional component and a forward sum for the stable component. The relevant declarations are `Breakdown.DiscreteDichotomyInternal.tailSum`, `Breakdown.DiscreteDichotomyInternal.norm_tailSum_le`, `Breakdown.DiscreteDichotomyInternal.rec_formula` and `Breakdown.discreteDichotomy`. They use normalized bounded sequences. The continuous operator $\mathcal R$ in Proposition 5.3 is reconstructed here from that mechanism and the continuous forcing recurrence; it is not the literal type of `Breakdown.periodicInverse`.

### Lemma 5.4. The inverse used for the short-interval sequence

*Paper correspondence: the linear construction of Proposition 4.3, pp. 20–21; alternative organisation used in the Lean proof.*

Retain the operators $A_n,\Gamma,\operatorname{Ev},S_n$ of Section 4 and set $\theta=\Theta^{1/k}$. Let $J:X\to X$ be a bounded linear section with $P_uJ=P_u$. There is a bounded linear map

$$
\mathcal R_d:\ell^\infty(\mathbb N;Y)\longrightarrow
V\times\ell^\infty(\mathbb N;Y),\qquad
g\longmapsto(e,z),
$$

such that, for every $n\geq0$,

$$
z_n-A_nz_n-
\begin{cases}
\Gamma Je,&n=0,\\
\theta^{-1}\Gamma\operatorname{Ev}z_{n-1},&n\geq1,
\end{cases}
=g_n.
\tag{5.13}
$$

**Proof.** Set $H_n=(I-A_n)^{-1}$ and $c_n=\operatorname{Ev}H_ng_n$. Given $x_0=Je$, define

$$
x_{n+1}=\theta^{-1}(S_nx_n+c_n),\qquad
z_n=H_n(\Gamma x_n+g_n).
\tag{5.14}
$$

The second formula immediately gives (5.13), provided these sequences are bounded. The uniform bound $\|H_n\|\leq4/3$ ensures that $c$ is bounded. The conjugacy $S_{n+k}=\rho S_n\rho^{-1}$ makes all the $S_n$ uniformly bounded as well.

Group $k$ updates at a time and put $y_m=\rho^{-m}x_{mk}$. Expanding the finite recurrence gives

$$
y_{m+1}=\Theta^{-1}(\mathcal My_m+d_m),
$$

where

$$
d_m=\sum_{j=0}^{k-1}\theta^j\rho^{-(m+1)}
S_{mk+k-1}\cdots S_{mk+j+1}c_{mk+j}.
\tag{5.15}
$$

The product is the identity when $j=k-1$. This formula follows by multiplying the $k$-step recurrence by $\theta^k=\Theta$ before untwisting it. There are only $k$ terms, and their operator norms are uniformly bounded by the conjugacy, so $\|d\|_\infty\leq C\|g\|_\infty$.

Choose $e\in V$ by the normalized version of the tail sum (5.8):

$$
e=-\sum_{m\geq0}\Theta^m\mathcal M_u^{-(m+1)}P_ud_m.
$$

Since $P_uy_0=P_uJe=e$, the same forward and backward estimates used in Proposition 5.3 show that $y$ is bounded, with a bound linear in $\|g\|_\infty$. The remaining $k-1$ values inside each block are controlled by the finite recurrence (5.14). This proves boundedness of $x$, and then of $z$. All the formulas are linear in $g$ and all the displayed estimates are uniform, giving a bounded linear operator $\mathcal R_d$. $\square$

The formal periodic inverse solves precisely the normalized sequence system (5.13), allowing general Banach spaces for both the endpoint and the interval variables. This is `Breakdown.periodicInverse`, with proposition `Breakdown.PeriodicInverseStatement`. The theorem `Breakdown.stepData` chooses the subdivision, the projection, the compact section and this right inverse from the profile and the dichotomy.
<!-- /passage:sec-5-a-right-inverse-with-compact-initial-corrections -->

## 6. The nonlinear correction on whole space

<!-- passage:sec-6-the-nonlinear-correction-on-whole-space -->

The linear inverse is now fixed. The nonlinear step has two useful forms. The continuous form controls an approximate solution and will be used on the torus. The bounded-sequence form is the one assembled by the whole-space Lean proof.

### Lemma 6.1. Weighted estimates for the nonlinear term

*Paper correspondence: (4.18) and Lemma 4.7, pp. 21–22.*

For $0<\kappa<1/4$ there is a constant $C_B$, depending only on $\kappa$ and $C_K$, such that

$$
\|B(v,w)\|_\kappa\leq C_B\|v\|_\kappa\|w\|_\kappa,
\qquad
\|G(\cdot)\chi\|_\kappa\leq\|\chi\|_X.
\tag{6.1}
$$

If $f$ is bounded and continuous in $X$ and $g\in C_0$, then

$$
\|B(f,g)\|_\kappa
\leq C_B\sup_{0\leq t<1}\|f(t)\|_X\,\|g\|_0.
\tag{6.2}
$$

All these Duhamel terms are continuous on $[0,1)$.

**Proof.** On each compact time interval continuity follows from the bilinear integral result in Section 2. The estimate reducing the infinite-time weight to a finite constant is

$$
\int_0^t(t-s)^{-3/4}(1-s)^{\kappa-1/2}\,ds
\leq C_\kappa(1-t)^{\kappa-1/4},
\tag{6.3}
$$

where

$$
C_\kappa=\int_0^{\infty}r^{-3/4}(1+r)^{\kappa-1/2}\,dr<\infty.
$$

To obtain (6.3), substitute $t-s=(1-t)r$. Near zero, the integrand defining $C_\kappa$ has exponent $-3/4>-1$. Near infinity its exponent is $\kappa-5/4<-1$. These two inequalities establish integrability without an unspecified endpoint argument.

For $v,w\in C_\kappa$, their pointwise norm product is bounded by

$$
\|v\|_\kappa\|w\|_\kappa(1-s)^{2\kappa-1/2}
\leq\|v\|_\kappa\|w\|_\kappa(1-s)^{\kappa-1/2}.
$$

Apply the kernel bound and (6.3), then multiply by the weight. This proves the first inequality in (6.1). The heat contraction and $(1-t)^{1/4-\kappa}\leq1$ prove the second. Finally $\|g(s)\|\leq(1-s)^{-1/4}\|g\|_0$, and

$$
(1-s)^{-1/4}\leq(1-s)^{\kappa-1/2}
$$

because $\kappa<1/4$. The same integral proves (6.2). $\square$

For $0<T\leq1$, the interval bilinear operator has norm at most $4C_KT^{1/4}$. This is the estimate packaged in `Breakdown.pieceOperator`; the weighted continuous estimate above is the paper's resummation over times approaching one. The sequence proof below instead puts the decay factors directly into the forcing.

### Lemma 6.2. Correcting an approximate solution

*Paper correspondence: (4.16)–(4.17) and Lemma 4.8, pp. 21–22.*

This lemma is valid in any Banach space with the heat and bilinear properties used in Lemma 6.1. Let $u^a:[0,1)\to X$ be continuous, let $J:E\to X$ be linear, and define

$$
F^a=u^a-G(\cdot)u^a(0)-B(u^a,u^a),
$$

$$
\mathcal L(\gamma,v)=v-2B(u^a,v)-G(\cdot)J\gamma.
\tag{6.4}
$$

Suppose $F^a\in C_\kappa$ and a linear right inverse $\mathcal R$ of $\mathcal L$ exists, with its second component satisfying $\|\mathcal R_vg\|_\kappa\leq C_{\mathcal R}\|g\|_\kappa$. Enlarge $C_{\mathcal R}$ to be positive if necessary. For a prescribed datum change $\chi\in X$, set $g_0=G(\cdot)\chi-F^a$. If

$$
C_{\mathcal R}^2\|g_0\|_\kappa\leq(8C_B)^{-1},
\tag{6.5}
$$

then there are $\gamma\in E$ and $v\in C_\kappa$ such that $u=u^a+v$ is a mild solution with initial value $u^a(0)+\chi+J\gamma$, and

$$
\|v\|_\kappa\leq2C_{\mathcal R}\|g_0\|_\kappa.
\tag{6.6}
$$

**Proof.** Bilinearity and symmetry give the exact identity

$$
u-G(\cdot)(u^a(0)+\chi+J\gamma)-B(u,u)
=F^a+\mathcal L(\gamma,v)-G(\cdot)\chi-B(v,v).
$$

Thus it suffices to solve $\mathcal L(\gamma,v)=g_0+B(v,v)$. Put $b=C_{\mathcal R}\|g_0\|_\kappa$, and on the closed ball $\|v\|_\kappa\leq2b$ define

$$
\Phi(v)=\mathcal R_v(g_0+B(v,v)).
$$

Its norm is at most $b+4C_{\mathcal R}C_Bb^2$. Condition (6.5) gives $8C_{\mathcal R}C_Bb\leq1$, so this is at most $3b/2\leq2b$. Furthermore

$$
B(v,v)-B(w,w)=B(v-w,v)+B(w,v-w),
$$

and hence on the ball

$$
\|\Phi(v)-\Phi(w)\|_\kappa
\leq4C_{\mathcal R}C_Bb\|v-w\|_\kappa
\leq\tfrac12\|v-w\|_\kappa.
$$

The closed ball is complete. Iterating $\Phi$ therefore produces a Cauchy sequence: successive differences are bounded by a geometric sequence of ratio $1/2$. Its limit is fixed by continuity, proving existence and (6.6). If $b=0$, the ball consists of zero and the conclusion follows directly. Let $\gamma$ be the first component of $\mathcal R(g_0+B(v,v))$. The right-inverse identity gives the required equation, and evaluating it at zero gives the specified datum. $\square$

The formal small-fixed-point lemma uses the same two estimates, a quadratic growth bound and a Lipschitz bound proportional to the sum of the two norms. It is `Breakdown.ContractionInternal.exists_small_fixed`. The full declaration `Breakdown.contraction` applies this lemma to a bounded sequence of interval variables. It does not itself state the continuous residual theorem (6.4)–(6.6).

### Lemma 6.3. Nonlinear gluing in the formal sequence variables

*Paper correspondence: the nonlinear correction in §4.5 and §5.2, pp. 21–24; the formal short-interval route.*

Let $N:Y\times Y\to Y$ be the continuous bilinear Duhamel operator on one short interval. Use $\mathcal R_d$ from Lemma 5.4 and $0<\theta<1$. Every sufficiently small $\xi\in X$ admits a correction $e\in V$ and a bounded sequence $z$ satisfying

$$
z_n-A_nz_n-
\begin{cases}
\Gamma(Je+\xi),&n=0,\\
\theta^{-1}\Gamma\operatorname{Ev}z_{n-1},&n\geq1
\end{cases}
=\theta^nN(z_n,z_n).
\tag{6.7}
$$

The corrected pieces $a_n+\theta^nz_n$ join to a mild solution on $[0,1)$ with datum $W(0)+\xi+Je$, and its rescaled distance from $W$ decays like $(1-t)^\kappa$.

**Proof.** On $Z=\ell^\infty(\mathbb N;Y)$, define

$$
G_\xi(z)_n=\mathbf1_{n=0}\Gamma\xi+\theta^nN(z_n,z_n),
\qquad
\Phi_\xi(z)=(\mathcal R_dG_\xi(z))_2.
$$

Because $\theta^n\leq1$, bilinearity gives

$$
\|G_\xi(z)\|_Z\leq\|\Gamma\|\|\xi\|+\|N\|\|z\|_Z^2,
$$

$$
\|G_\xi(z)-G_\xi(w)\|_Z
\leq\|N\|(\|z\|_Z+\|w\|_Z)\|z-w\|_Z.
$$

Put $B_d=\|\mathcal R_d\|\|\Gamma\|$ and $K_d=\|\mathcal R_d\|\|N\|$. The argument in Lemma 6.2 applies whenever $8K_dB_d\|\xi\|\leq1$, yielding a fixed point with $\|z\|_Z\leq2B_d\|\xi\|$. One uniform choice is

$$
\|\xi\|\leq\rho_0=
\frac1{8(K_d+1)(B_d+1)}.
\tag{6.8}
$$

This also ensures $\|z\|_Z\leq1$. Define $e=(\mathcal R_dG_\xi(z))_1$. The right-inverse identity is (6.7), and

$$
\|e\|\leq C_d\|\xi\|,\qquad
C_d=\|\mathcal R_d\|(\|\Gamma\|+2\|N\|B_d),
\tag{6.9}
$$

since $\|z\|_Z^2\leq\|z\|_Z\leq2B_d\|\xi\|$. The range property of $\mathcal R_d$ also gives $e\in V$.

Set $v_n=\theta^nz_n$. Multiplication of (6.7) by $\theta^n$ and bilinearity of $N$ turn its right side into $N(v_n,v_n)$. For $n\geq1$, the preceding endpoint becomes $\Gamma\operatorname{Ev}v_{n-1}$. For $n=0$, it is $\Gamma(Je+\xi)$. Thus every $a_n+v_n$ solves the mild equation on its short interval, and the initial value of the next piece is the rescaled endpoint of the preceding piece.

For $t=1-\mu^n+\mu^n\sigma$, $0\leq\sigma<1-\mu$, define the global field by

$$
u(t)=D_{\mu^{-n}}(a_n(\sigma)+v_n(\sigma)).
\tag{6.10}
$$

The endpoint identities give continuity. The covariance identities transform each local equation to the physical equation. Splitting and concatenating Duhamel integrals verifies the global mild equation on each compact time interval; only finitely many pieces are needed before any $b<1$. Hence it holds throughout $[0,1)$.

Finally $1-t=\mu^n(1-\sigma)$ and $\theta=\mu^\kappa$, with $0<\kappa<1/4$ because $\mu^{1/4}<\theta<1$. The background part of (6.10), after application of $D_{1-t}$, is $W(-\log(1-t))$. The remaining part obeys

$$
\|D_{1-t}u(t)-W(-\log(1-t))\|_X
\leq\theta^n\|z\|_Z
\leq\theta^{-1}\|z\|_Z(1-t)^\kappa.
\tag{6.11}
$$

The last inequality uses $1-\sigma\geq\mu$. $\square$

The formal contraction constructs the normalized pieces, and the formal gluing theorem joins the resulting exact local solutions. These steps are `Breakdown.contraction`, `Breakdown.piecePerturbation` and `Breakdown.glue`. The final assembly retains the quantitative rescaled estimate in `Breakdown.TransferHolds`.

### Lemma 6.4. A divergence-free cutoff with uniform bounds

*Paper correspondence: (5.1) and Lemma 5.1, p. 23.*

Choose a smooth scalar function $\eta$ with $0\leq\eta\leq1$, equal to one on $B_{1/2}$ and zero outside $B_1$. For $r>0$ set

$$
A(t,x)=\int_0^1\sigma\,u^*(t,\sigma x)\times x\,d\sigma,
\qquad
\bar u_r(t,x)=\operatorname{curl}_x(\eta(x/r)A(t,x)).
\tag{6.12}
$$

The field $\bar u_r$ is smooth before time one, divergence free, equal to $u^*$ on $B_{r/2}$ and supported in $\overline B_r$. Uniformly for $0\leq t<1$,

$$
\|\bar u_r(t)-u^*(t)\|_X\leq C r^{-1/2},
\qquad
\|\bar u_r(t)\|_2\leq C r^{1/2}.
\tag{6.13}
$$

**Proof.** For each compact set in $(t,x)$ with $t<1$, the integrand and all its derivatives are bounded on its product with $[0,1]$. Differentiation under the integral is therefore legitimate to every order, proving smoothness. Write $u=u^*(t,\cdot)$ temporarily. The vector identity

$$
\operatorname{curl}_x\big(\sigma u(\sigma x)\times x\big)
=2\sigma u(\sigma x)+\sigma^2(x\cdot\nabla)u(\sigma x)
=\frac{d}{d\sigma}\big(\sigma^2u(\sigma x)\big)
$$

uses $\operatorname{div}u=0$. Integrating from zero to one gives $\operatorname{curl}A=u$. Thus

$$
\bar u_r=\eta(x/r)u^*
+r^{-1}(\nabla\eta)(x/r)\times A.
\tag{6.14}
$$

This identity proves equality on the inner ball and vanishing outside the outer ball. Divergence vanishes because $\bar u_r$ is a curl.

The uniform far-field inequalities from Section 3 imply, for every $x\ne0$,

$$
|u^*(t,x)|\leq C_W|x|^{-1},\qquad
|\nabla u^*(t,x)|\leq C_W|x|^{-2}.
$$

They may be used even at small nonzero $x$; the right sides there are simply coarse bounds. Applied at $\sigma x$, they give $|A(t,x)|\leq C_W$. Differentiating the integrand gives terms bounded by

$$
\sigma^2|\nabla u^*(t,\sigma x)||x|
+\sigma|u^*(t,\sigma x)|\leq C|x|^{-1},
$$

for $\sigma>0$. Hence $|\nabla A(t,x)|\leq C|x|^{-1}$. The endpoint $\sigma=0$ causes no singularity in the actual integrand, which is smooth.

On the shell $r/2\leq|x|\leq r$, the product rule applied to (6.14) bounds $|\nabla(\bar u_r-u^*)|$ by $Cr^{-2}$. The terms are, explicitly, the cutoff times $\nabla u^*$, a first cutoff derivative times $u^*$, a second cutoff derivative times $A$, and a first cutoff derivative times $\nabla A$. Each has this bound. Inside $B_{r/2}$ the difference vanishes, and outside $B_r$ its gradient is $-\nabla u^*$. Therefore

$$
\|\bar u_r-u^*\|_X^2
\leq C r^{-4}|B_r|+C\int_{|x|\geq r}|x|^{-4}\,dx
\leq C r^{-1}.
$$

Similarly (6.14) gives $|\bar u_r(t,x)|\leq C|x|^{-1}$ on $B_r$ and zero outside it. The integral of $|x|^{-2}$ over $B_r$ is $4\pi r$, proving the second bound in (6.13). The field and its gradient are square integrable for each fixed $r,t$, and the divergence and smoothness statements already proved show $\bar u_r(t)\in C^\infty_{c,\mathrm{div}}$. $\square$

The formal homotopy potential has curl equal to the original smooth divergence-free field. This is `Breakdown.Periodic.homotopyCurl`. The definition `Breakdown.Periodic.cutoffField` expands the curl as in (6.14), and `Breakdown.Periodic.cutoffDivergenceFree` proves its solenoidal property. These declarations allow an arbitrary centre. The quantitative declarations `Breakdown.Periodic.cutoffGradientClose` and `Breakdown.Periodic.cutoffMassBound` use a fixed physical cutoff and a small blow-up scale; their parameters differ from the expanding-radius estimates (6.13).

### Proposition 6.5. The family of corrected whole-space data

*Paper correspondence: Proposition 2.1, p. 11, and its proof in §5.2, pp. 23–24.*

There are $\varepsilon_0>0$, the fixed space $E\subset C^\infty_{c,\mathrm{div}}$, and constants $0<c<C<\infty$ such that every $w_0\in X$ with $\|w_0-W(0)\|_X\leq\varepsilon_0$ admits a $\gamma\in E$ and a mild solution $u$ on $[0,1)$ with $u(0)=w_0+\gamma$ and

$$
\|u(t)-u^*(t)\|_X\leq C(1-t)^{\kappa-1/4},
\qquad
c(1-t)^{-1/4}\leq\|u(t)\|_X\leq C(1-t)^{-1/4}.
\tag{6.15}
$$

Such a $w_0$ can be chosen smooth, compactly supported and divergence free. The corrected datum then has those properties as well.

**Proof.** Section 3 gives constants $c_*>0$ and $C_*<\infty$ with

$$
c_*(1-t)^{-1/4}\leq\|u^*(t)\|_X\leq C_*(1-t)^{-1/4}.
$$

Fix $\varepsilon_0$ small enough that

$$
C_{\mathcal R}^2\varepsilon_0\leq(8C_B)^{-1},
\qquad 4C_{\mathcal R}\varepsilon_0\leq c_*.
\tag{6.16}
$$

Let $\chi=w_0-u^*(0)$. Apply Lemma 6.2 with $u^a=u^*$, with $J$ the inclusion $E\hookrightarrow X$, and with the right inverse of Proposition 5.3. The residual is zero because $u^*$ is an exact mild solution. The heat estimate gives $\|g_0\|_\kappa\leq\|\chi\|_X\leq\varepsilon_0$. Hence the lemma produces $u=u^*+v$ with the desired datum and

$$
\|v(t)\|_X\leq2C_{\mathcal R}\varepsilon_0(1-t)^{\kappa-1/4}
\leq\tfrac12c_*(1-t)^{-1/4}.
$$

The last inequality uses both (6.16) and $(1-t)^\kappa\leq1$. The reverse triangle inequality now gives the lower rate in (6.15) with $c=c_*/2$, while the triangle inequality gives its upper rate. The error estimate has already been proved, with constants independent of the particular $w_0$ in this neighbourhood.

Finally choose $r$ so large that the first bound in (6.13), at $t=0$, is at most $\varepsilon_0$. Then $w_0=\bar u_r(0)$ is admissible. Since $\gamma\in E$ and $E$ consists of compactly supported smooth divergence-free fields, the sum $w_0+\gamma$ remains in this class. $\square$

The whole-space construction truncates the initial field and then solves the exact equation about the original background. Its perturbative smallness is measured in $X$. The uniform $L^2$ bound for the resulting solution is proved separately from its compact initial datum in Section 7; it does not follow from the $X$ error estimate.

The paper's proposition quantifies over every nearby datum and corrects it in one fixed finite-dimensional space. The public abstract transfer theorem instead exports the existence of arbitrarily close data in any prescribed dense submodule, together with rescaled convergence. The internal section, inverse and contraction constructions explain the corrected-data mechanism; the exported statement alone does not record the complete family in Proposition 6.5.

### Theorem 6.6. The dense-data transfer retained by the formal theorem

*Paper correspondence: the construction behind Proposition 2.1 and Theorem 1.1, pp. 11 and 18–24; the abstract formulation used in Lean.*

Let a real Hilbert space carry the heat, dilation, bilinear and compactness properties stated in Section 2, let a surjective linear isometry $\rho$ commute with these operations, and let $w$ be a nonzero continuous twisted-periodic mild orbit. For every dense linear subspace $\mathcal D\subset X$ and every $\varepsilon>0$, there is a mild solution $u$ on $[0,1)$ with $u(0)\in\mathcal D$, $\|u(0)-w(0)\|_X<\varepsilon$, and constants $C,\kappa>0$ such that

$$
\|D_{1-t}u(t)-w(-\log(1-t))\|_X
\leq C(1-t)^\kappa\qquad(0\leq t<1).
\tag{6.17}
$$

**Proof.** Apply the compact-section construction with $\mathcal D$ in place of smooth compactly supported fields. The inverse in Lemma 5.4 has a section $J$ taking values in $\mathcal D$. Choose $f_0\in\mathcal D$ so close to $w(0)$ that

$$
\|f_0-w(0)\|_X
<\min\left\{\rho_0,\frac{\varepsilon}{1+\|J\|C_d}\right\},
$$

where $\rho_0$ and $C_d$ are from Lemma 6.3. Set $\xi=f_0-w(0)$ and carry out that construction. The datum is $f_0+Je\in\mathcal D$, and (6.9) gives

$$
\|f_0+Je-w(0)\|_X
\leq(1+\|J\|C_d)\|\xi\|_X<\varepsilon.
$$

The rescaled estimate is (6.11), and the mild equation follows from the gluing argument there. All uses of the physical space in the construction were through the stated framework properties, so the proof applies to the abstract Hilbert space as claimed. $\square$

The formal transfer statement retains the dense-data quantifier and the rescaled error estimate. It is `Breakdown.TransferHolds`; `Breakdown.transferHolds_of_dichotomy` proves it from the dichotomy, and `Breakdown.dichotomyHolds` discharges that input. This theorem still requires a recurrent nonzero orbit. It supplies no concrete profile or numerical certificate.
<!-- /passage:sec-6-the-nonlinear-correction-on-whole-space -->

## 7. Smoothness, energy and the whole-space conclusion

<!-- passage:sec-7-smoothness-energy-and-the-whole-space-conclusion -->

### Proposition 7.1. A compact-data mild solution is a smooth finite-energy solution

*Paper correspondence: Lemma 2.3, p. 11; Appendix A.2, pp. 48–49.*

Let $0<T<\infty$, let $u\in C([0,T);X)$ be mild, and suppose $u(0)=u_0\in C^\infty_{c,\mathrm{div}}$. Then a smooth pressure can be chosen so that $(u,p)$ solves Navier–Stokes smoothly up to time zero on $[0,T)\times\mathbb R^3$, and

$$
\|u(t)\|_2^2+2\int_0^t\|\nabla u(r)\|_2^2\,dr=\|u_0\|_2^2,
\qquad 0\le t<T.
$$

**Proof.** The local $H^1$ theorem used here has the following precise content. A solenoidal $H^1$ datum has a unique local solution in $C_tH^1\cap L^2_tH^2$ satisfying the projected integral equation; it can be continued while its $H^1$ norm stays bounded. Smooth data with all Sobolev norms finite give smooth velocity and pressure, including at the initial time. These are the zero-force specialisations of Tao's Theorem 5.4(i), (ii), (iv) and Corollary 5.8. The statement is also realised by the Fourier-flow construction in the supplied formal library. The only global conclusion used below is the continuation alternative, not an assumption of global regularity.

Fix $b<T$. The $X$ trajectory is bounded on $[0,b]$; let $M_b=\sup_{[0,b]}\|u(t)\|_X$. Start the local $H^1$ solution $\widetilde u$ from $u_0$. It is continuous into $X$ because $H^1\hookrightarrow L^6$ and $\nabla\widetilde u\in L^2$. Its projected equation is the mild equation in $X$: the two integrands agree as distributions and the latter is a Bochner integral by Lemma 2.5. Both sides are continuous into $X$, so an initially almost-everywhere identity holds at every time. Lemma 2.7 gives $\widetilde u=u$ on each common compact interval.

The datum is compactly supported and smooth, hence Schwartz. Local regularity supplies the spatial and time Sobolev bounds needed for integration by parts. Take the $L^2$ inner product of the equation with $\widetilde u$. Solenoidality gives

$$
\int\widetilde u\cdot(\widetilde u\cdot\nabla)\widetilde u
=\frac12\int\operatorname{div}(|\widetilde u|^2\widetilde u)=0,
\qquad
\int\widetilde u\cdot\nabla\widetilde p=0,
$$

and the Laplacian contributes $-\|\nabla\widetilde u\|_2^2$. These equalities follow first with a spatial cutoff; the local Sobolev bounds and finite $L^2$ norm send the cutoff error to zero. Integration in time yields the displayed energy identity on every interval where the $H^1$ solution exists. In particular,

$$
\|\widetilde u(t)\|_{H^1}\le\|u_0\|_2+M_b,\qquad t\le b.
$$

If its maximal lifetime were at most $b$, this bound would contradict the $H^1$ continuation alternative. Thus it reaches $b$ and coincides there with $u$. Since $b<T$ was arbitrary, the construction covers all of $[0,T)$. The pressure can be chosen by the common normalisation $p=\sum_{i,j}\mathcal R_i\mathcal R_j(u_i u_j)$, so pressures chosen on overlapping intervals agree after addition of time functions. This gives one smooth pressure on the whole interval, and the energy bound has the same constant $\|u_0\|_2$ for every $b$. $\square$

The formal regularity theorem identifies a compact-data mild path with a smooth physical velocity and pressure on each closed interval before blow-up.

Its public type records a finite energy bound on that interval; the uniform non-increasing energy identity above is an additional analytic deduction. In particular, one cannot infer a single bound up to $T$ merely by writing “bounded on every compact interval”. The energy identity supplies that uniformity.

### Corollary 7.2. Completion of the whole-space construction

*Paper correspondence: Proposition 2.1, p. 11; Theorem 1.1(i), p. 3; proof in §2.3, pp. 11–12.*

Apply the correction construction to a compact solenoidal datum $w_0$ sufficiently close to $W(0)$ in $X$. Its correction $\gamma$ lies in the fixed finite-dimensional subspace $E\subset C^\infty_{c,\mathrm{div}}$, so $u_0=w_0+\gamma$ is smooth, compactly supported and solenoidal. The resulting mild solution $u=u^*+v$ is smooth and has energy at most that of $u_0$.

Choose the contraction ball so that $\|v\|_\kappa\le m/2$, where $m$ is the lower coefficient of Corollary 3.3. Then

$$
\|v(t)\|_X\le\frac m2(1-t)^{\kappa-1/4}
\le\frac m2(1-t)^{-1/4},
$$

and the triangle inequality gives

$$
\frac m2(1-t)^{-1/4}\le\|\nabla u(t)\|_2
\le\left(M+\frac m2\right)(1-t)^{-1/4}.
$$

Thus the enstrophy norm diverges at time one, with the stated two-sided rate. The correction estimate is precisely the profile comparison in Theorem A. It can increase in physical variables because $\kappa<1/4$. In similarity variables $U(s)=D_{e^{-s}}u(1-e^{-s})$, it becomes

$$
\|U(s)-W(s)\|_X
=e^{-s/4}\|u(1-e^{-s})-u^*(1-e^{-s})\|_X
\le C e^{-\kappa s}.
$$

The abstract transfer theorem retains a compact datum and decay of the rescaled error toward the given recurrent orbit.

It is an existence statement; by itself it does not state the paper's family of corrections for every sufficiently close $w_0$. The finite-codimension family follows here from the explicit right inverse and contraction in §§5–6. The exact printed family and the full rate-and-energy bundle are therefore treated separately in the correspondence table.

Finally, the rate is consistent with finite energy dissipation: its squared gradient norm is of order $(1-t)^{-1/2}$, whose integral is finite at $t=1$. This observation checks the exponents; it supplies no independent existence argument.

### Proposition 7.3. Smoothness of the periodic solution

*Paper correspondence: second part of Lemma 2.3, p. 11; Appendix A.2, p. 49.*

A continuous mean-zero $X_1$-valued mild solution on $[0,T)$ with smooth periodic datum has a smooth periodic velocity and pressure on every closed interval $[0,b]$ with $b<T$.

**Proof.** The periodic local $H^1$ theory is the zero-force, mean-zero form of Tao's Theorem 5.1(i), (ii), (iv), with its continuation alternative in Corollary 5.2. Identify the local $H^1$ solution with the given mild trajectory by Lemmas 2.5, 2.7 and 2.9. On $[0,b]$, the trajectory has bounded $X_1$ norm, and the zero-mode-free Poincaré inequality gives a bound for its full $H^1$ norm. This excludes premature termination of the local solution. Smoothness persists from the smooth datum, and pressure is recovered as the periodic zero-mean solution of its Poisson equation. Since $b$ was arbitrary, the representatives agree throughout $[0,T)$. $\square$

The formal periodic uniqueness route explicitly converts smooth periodic solutions into mild ones before comparing them.

That comparison direction suffices for its global nonexistence endpoint. The converse regularity assertion just proved for the constructed path uses the stated periodic local theory. In particular, a declaration proving smooth-to-mild conversion is not a declaration of this converse.

### Proposition 7.4. Excluding global smooth competitors at every positive viscosity

*Paper correspondence: Theorem 1.1(i), p. 3; §1.5, pp. 9–10; the formal endpoint explained in `lean/README.md`.*

For each $\nu>0$ there is a smooth compactly supported solenoidal datum for which no global smooth viscosity-$\nu$ solution has uniformly bounded energy.

**Proof.** First take viscosity one and the datum $u_0$ constructed in Corollary 7.2. Suppose a competing velocity-pressure pair $(v,p)$ is smooth on $[0,\infty)\times\mathbb R^3$, has datum $u_0$, solves the same unforced equation, and has uniformly bounded $L^2$ energy. Its restriction to the closed interval $[0,1]$ is a smooth finite-energy competitor with $H^1$ datum. The exact auxiliary implication used here is Tao's Corollary 11.1: a smooth finite-energy solution on a closed finite interval, with $H^1$ initial datum, has bounded $H^1$ norm on that interval. The closed interval includes the candidate terminal time. Applying a result only on each $[0,b]$, $b<1$, would not supply the required uniform bound.

Tao's Corollary 4.3 supplies the pressure normalisation and integral formulation for this smooth finite-energy class. It therefore places $v$ in the $H^1$ mild class on $[0,1]$, and hence in the continuous $X$ mild class on each $[0,b]$, $b<1$. The datum is the same as that of $u$, so Lemma 2.7 gives $v=u$ on all those intervals. This contradicts the lower estimate $\|\nabla u(t)\|_2\ge c(1-t)^{-1/4}$ as $t\uparrow1$, since $\sup_{[0,1]}\|v(t)\|_{H^1}$ is finite. Thus no such global competitor exists at viscosity one.

For arbitrary $\nu>0$, the transform

$$
u_\nu(t,x)=\nu u(\nu t,x),\qquad
p_\nu(t,x)=\nu^2p(\nu t,x),\qquad
u_{0,\nu}=\nu u_0
$$

carries a unit-viscosity solution to a viscosity-$\nu$ solution. Indeed all terms except the viscous term acquire the factor $\nu^2$, and $\nu\Delta u_\nu=\nu^2\Delta u$. If a global smooth bounded-energy competitor $(v,q)$ existed for the scaled datum $\nu u_0$, then

$$
\widetilde v(s,x)=\nu^{-1}v(s/\nu,x),\qquad
\widetilde q(s,x)=\nu^{-2}q(s/\nu,x)
$$

would be a global unit-viscosity competitor for $u_0$ with bounded energy. This is impossible by the preceding argument. Scalar multiplication preserves smoothness, compact support and divergence zero of the datum. $\square$

The formal whole-space endpoint excludes global smooth bounded-energy solutions at every positive viscosity, conditional on a profile.

Its statement is an implication. The existence of the concrete profile still belongs to the separate certificate part of the project. In this rewrite the extra written bounds in its premise are supplied analytically by Lemmas A.5 and A.6, with no claim of a new compiled wrapper.
<!-- /passage:sec-7-smoothness-energy-and-the-whole-space-conclusion -->

## 8. The construction on a large torus

<!-- passage:sec-8-the-construction-on-a-large-torus -->

We keep the whole-space objects already constructed: the profile field $u^*=u_1^*$, its positive lower norm constant $c_*$, the exponent $0<\kappa<1/4$, the finite-dimensional space $E$ of smooth compactly supported solenoidal corrections, and the bounded right inverse $\mathcal R$ of Section 5. The parameter $L\ge1$ will be the spatial period. Every implicit constant in this section is independent of $L$ and of $0\le t<1$; it may depend on the fixed profile, $\kappa$, $E$ and the cutoff.

The plan is to put a compact part of $u^*$ into one periodic cell, measure its failure to solve the equation, and remove that failure. The inverse is transferred through a ball on which the coefficient is supported. This avoids requiring any recurrence of the periodic approximate field.

### 8.1. Periodic fields and the norm used by Lean

Write $Q_L=[-L/2,L/2]^3$, $\mathbb T_L^3=\mathbb R^3/(L\mathbb Z^3)$, and

$$
X_L=\left\{v\in H^1(\mathbb T_L^3;\mathbb R^3):
\operatorname{div}v=0,\quad \int_{Q_L}v=0\right\},
\qquad
\|v\|_{X_L}=\|\nabla v\|_{L^2(Q_L)}.
$$

The mean-zero condition makes this a norm. The Fourier modes $k\in L^{-1}\mathbb Z^3\setminus\{0\}$ give

$$
\|v\|_2\le \frac{L}{2\pi}\|\nabla v\|_2.
$$

Scaling the mean-zero Sobolev inequality on the unit torus gives

$$
\|v\|_{L^6(Q_L)}\le C_{\mathrm{S}}\|v\|_{X_L},
$$

with $C_{\mathrm{S}}$ independent of $L$: both sides scale by $L^{-1/2}$ under $v(x)\mapsto v(Lx)$, when the norms are moved to the unit cell.

Denote the periodic heat flow by $G_L(t)=e^{t\Delta_L}$ and the periodic Leray projection by $\mathbb P_L$. The heat and bilinear bounds established in Section 2 apply to $X_L$, with constants independent of $L$. In particular, if $B_L$ denotes the time-integrated symmetric bilinear operator,

$$
B_L(f,h)(t)
=-\frac12\int_0^t
e^{(t-s)\Delta_L}\mathbb P_L
\big((f(s)\cdot\nabla)h(s)+(h(s)\cdot\nabla)f(s)\big)\,ds,
$$

then the same weighted estimates used on $\mathbb R^3$ apply here.

**Lemma 8.1 (periodizing compact solenoidal fields).** If $f$ is smooth, divergence-free and supported in $\overline B_{L/8}$, then

$$
\Pi_L f(x)=\sum_{j\in\mathbb Z^3}f(x-Lj)
$$

is a smooth mean-zero field in $X_L$ and

$$
\|\Pi_L f\|_{X_L}=\|f\|_X.
$$

For any compactly supported $L^p$ field with the same support condition, periodization also preserves its $L^p$ norm over one cell. This is the paper's equation (6.1), p. 24.

**Proof.** The translated supports lie in disjoint balls. On the interior of $Q_L$, all terms except $j=0$ vanish, so the assertions about norms follow by integration. Smoothness and divergence freedom hold term by term, since the sum is locally finite. For the mean, work componentwise. If $f_j$ is the $j$th component, then

$$
f_j=\sum_{m=1}^3\partial_m(x_jf_m),
$$

because $\operatorname{div}f=0$. Integrating this identity over $\mathbb R^3$ gives $\int f_j=0$. The integral of the periodization over its cell is the same integral. This proves mean zero and the lemma.

There is a material difference in the formal norm. Lean's periodic space $V$ uses the Fourier weight $1+4\pi^2|k|^2$ and includes the constant Fourier mode. Its norm represents the full $H^1$ norm on a unit torus. The formal transplant is also centred at $(1/2,1/2,1/2)$. Translation carries that centre to the origin used here. For a smooth compactly supported solenoidal field $f$ supported in $\overline B_b$, where $b>0$, and $0<\mu\le1$ with $\sqrt\mu\,b\le1/8$, the formal transplant lemma gives

$$
\left\|\mu^{1/4}\operatorname{toV}
   \big(\operatorname{transplantField}(\mu,f)\big)\right\|_V^2
= \|\nabla f\|_2^2+\mu\|f\|_2^2.
$$

The extra $L^2$ term tends to zero as $\mu\downarrow0$. This formula explains how the formal unit-torus construction approaches the homogeneous whole-space norm.

### 8.2. Comparing heat flows with pressure included

The comparison must include the Leray projection. Its nonlocal part records the pressure contribution. We first give the kernel calculation behind the required decay.

**Lemma 8.2 (the Oseen kernel and its derivatives).** Let

$$
G_t(x)=(4\pi t)^{-3/2}e^{-|x|^2/(4t)}
$$

be the scalar heat kernel. The matrix kernel of $e^{t\Delta}\mathbb P$ can be written

$$
(O_t)_{ij}(x)=\delta_{ij}G_t(x)
+\partial_i\partial_j\int_t^\infty G_s(x)\,ds.
$$

For every integer $\ell\ge0$,

$$
|\nabla^\ell O_t(x)|\le C_\ell(|x|+\sqrt t)^{-3-\ell}.
$$

Consequently, for a sufficiently integrable matrix field $F$,

$$
e^{t\Delta}\mathbb P\operatorname{div}F=\nabla O_t*F
$$

with the tensor indices contracted in the divergence convention. These are the kernel facts used in the paper's (3.9) and (3.10), p. 13.

**Proof.** The Fourier multiplier of the displayed kernel is

$$
e^{-4\pi^2t|\xi|^2}
\left(\delta_{ij}-\frac{\xi_i\xi_j}{|\xi|^2}\right)
$$

This uses the Fourier convention of Section 2 and is the heat multiplier followed by the orthogonal projection onto $\xi^\perp$. The value at $\xi=0$ is irrelevant for whole-space integrals.

Differentiation of the Gaussian gives, for every $m$,

$$
|\nabla^mG_s(x)|
\le C_m s^{-(3+m)/2}e^{-|x|^2/(8s)}.
$$

Indeed each derivative is a polynomial in $x/\sqrt s$ times the original Gaussian, and that polynomial is absorbed by replacing $4s$ in the exponential denominator with $8s$. For the second term of $O_t$ it remains to bound

$$
\int_t^\infty s^{-(5+\ell)/2}e^{-|x|^2/(8s)}\,ds.
$$

If $|x|\le\sqrt t$, discard the exponential and integrate the power, obtaining $C_\ell t^{-(3+\ell)/2}$. If $|x|>\sqrt t$, set $r=|x|^2/s$. The integral is bounded by

$$
|x|^{-3-\ell}\int_0^\infty r^{(1+\ell)/2}e^{-r/8}\,dr.
$$

This integral is finite. The derivative of the first Gaussian term satisfies the same two-region bound. Combining the regions proves the estimate. The convolution identity follows from the multiplier identity, first for smooth compactly supported $F$ and then by approximation in the norms used below. In particular $\nabla O_t$ and $\nabla^2O_t$ are bounded and integrable for fixed $t>0$, which is sufficient for the periodization argument.

This proof expands the cited kernel input. The representation and its first derivative bound agree with Koch, Nadirashvili, Seregin and Šverák, §3, equations (3.3)–(3.7); the calculation above supplies the additional derivative required here.

The pinned formal comparison used below is `Breakdown.Periodic.heatDivFreeComparison`, which states a unit-torus limit. The Oseen representation above is an analytic derivation; no literal exported declaration of that complete kernel statement has been identified in this return.

**Lemma 8.3 (uniform comparison on a cell).** Let $L\ge1$, $t>0$, and let $F\in W^{1,1}(\mathbb R^3;\mathbb R^{3\times3})$ vanish outside $\overline B_{L/8}$. Set

$$
g=e^{t\Delta_L}\mathbb P_L\operatorname{div}\Pi_LF
   -e^{t\Delta}\mathbb P\operatorname{div}F.
$$

Then

$$
\|\nabla g\|_{L^2(Q_L)}+\|g\|_{L^6(Q_L)}
\le C L^{-7/2}\|F\|_{L^1(\mathbb R^3)}.
$$

This is Lemma 6.1 of the paper, pp. 24–25.

**Proof.** Put $h=\nabla O_t*F$. For $x$ in the interior of $Q_L$, $x'\in\overline B_{L/8}$ and $j\ne0$,

$$
|x-x'-Lj|
\ge L|j|_\infty-\frac58L
\ge\frac38L|j|_\infty.
$$

Lemma 8.2 therefore gives

$$
|h(x-Lj)|\le C(L|j|_\infty)^{-4}\|F\|_1,
\qquad
|\nabla h(x-Lj)|\le C(L|j|_\infty)^{-5}\|F\|_1.
$$

The number of lattice points with $|j|_\infty=n$ is at most $Cn^2$. Both resulting series converge. Thus the sum

$$
g_0(x)=\sum_{j\ne0}h(x-Lj)
$$

and its first derivatives converge uniformly on the cell interior, and

$$
|g_0(x)|\le CL^{-4}\|F\|_1,
\qquad
|\nabla g_0(x)|\le CL^{-5}\|F\|_1.
$$

To identify the sum with the periodic heat flow, use Fourier coefficients. Since $h\in L^1$, the coefficient of $\sum_jh(x-Lj)$ at $k\in L^{-1}\mathbb Z^3$ is $L^{-3}\widehat h(k)$. The multiplier identity gives

$$
\widehat h(k)=e^{-4\pi^2t|k|^2}P_k\,\widehat{\operatorname{div}F}(k).
$$

These are exactly the coefficients of the periodic heat evolution of $\operatorname{div}\Pi_LF$. Its zero coefficient is zero, because the integral of a compactly supported divergence is zero. Uniqueness of Fourier coefficients identifies the two periodic fields almost everywhere. Hence $g=g_0$ on $Q_L$. The boundary of the cube has measure zero and does not affect the norms.

Finally, the $L^6$ norm of a bounded function on $Q_L$ gains the factor $L^{1/2}$, and its gradient's $L^2$ norm gains $L^{3/2}$. Both bounds become $CL^{-7/2}\|F\|_1$. This proves the result for the stated $W^{1,1}$ class as well as for smooth tensors.

The formal comparison target for this estimate is `Breakdown.Periodic.heatDivFreeComparison`. Its small-$\mu$ conclusion and separated time window are recorded after Corollary 8.4; the quantitative cell estimate just proved is an analytic part of this exposition.

**Corollary 8.4 (comparison for compact initial velocities).** Under the hypotheses of Lemma 8.1,

$$
\left\|\nabla\big(G_L(t)\Pi_Lf-G(t)f\big)\right\|_{L^2(Q_L)}
+
\left\|G_L(t)\Pi_Lf-G(t)f\right\|_{L^6(Q_L)}
\le CL^{-5/2}\|f\|_1.
$$

This is the paper's (6.3), p. 25.

**Proof.** Apply Lemma 8.3 to the tensor with components $F_{jm}=x_jf_m$. Its divergence is $f$, its $L^1$ norm is at most $(L/8)\|f\|_1$, and the Leray projection fixes both $f$ and $\Pi_Lf$. At time zero the two fields agree on the cell, so their difference there is zero.

The formal heat-comparison declarations express a related limit in the unit-torus scaling parameter $\mu$. Their statements allow an arbitrarily small error after choosing $\mu$ sufficiently small; the source comparison keeps time away from zero. They do not state the explicit powers $L^{-7/2}$ and $L^{-5/2}$ just proved. The formal sequence argument deals separately with its short-time part.

### 8.3. The periodic approximate solution and its residual

Let $\bar u(t)$ be the solenoidal cutoff from Section 6 with radius $L/8$, and set

$$
u^a(t)=\Pi_L\bar u(t).
$$

It agrees with $u^*(t)$ on $B_{L/16}$ and belongs to $X_L$. The cutoff estimates give, uniformly for $t<1$,

$$
\|\bar u(t)-u^*(t)\|_X\le C L^{-1/2},
\qquad
\|\bar u(t)\|_2\le C L^{1/2}.
$$

The maps involved are continuous on each compact time interval because the cutoff is smooth and has fixed compact support.

For any Banach space $Y$, use

$$
\mathcal Y_\kappa(Y)=
\left\{f\in C([0,1);Y):
\|f\|_{\kappa,Y}:=
\sup_{0\le t<1}(1-t)^{1/4-\kappa}\|f(t)\|_Y<\infty\right\}.
$$

We suppress the second subscript when its meaning is clear. Define the Duhamel residual by

$$
F^a(t)=u^a(t)-G_L(t)u^a(0)-B_L(u^a,u^a)(t).
$$

**Proposition 8.5 (small residual after periodization).** There is $C_1$ independent of $L\ge1$ such that

$$
(c_*-C_1L^{-1/2})(1-t)^{-1/4}
\le\|u^a(t)\|_{X_L}
\le C_1(1-t)^{-1/4},
$$

and

$$
F^a\in\mathcal Y_\kappa(X_L),
\qquad
\|F^a\|_\kappa\le C_1L^{-1/2}.
$$

This restates Lemma 6.2 of the paper, pp. 25–26.

**Proof.** Lemma 8.1 identifies the gradient norm of $u^a$ with that of $\bar u$. The upper and lower bounds follow by comparing $\bar u$ to $u^*$ and using $1\le(1-t)^{-1/4}$.

For the residual, first work on the whole space. Write $d=\bar u-u^*$ and

$$
\bar F=\bar u-G(t)\bar u(0)-B(\bar u,\bar u).
$$

The exact mild equation for $u^*$ gives

$$
\bar F=d-G(t)d(0)-B(d,\bar u)-B(u^*,d).
$$

The first two terms have weighted norm at most $CL^{-1/2}$. For the last two, use the mixed weighted estimate from Section 6: a uniformly bounded first factor of size $a$ and a second factor with bounded $\mathcal Y_0(X)$ norm give a $\mathcal Y_\kappa(X)$ norm at most $C_\kappa a\|h\|_0$. This follows from the same integrable convolution used for the nonlinear correction. Since $\|d\|_{L^\infty_tX}\le CL^{-1/2}$ and both $\bar u$ and $u^*$ have uniformly bounded $\mathcal Y_0(X)$ norms,

$$
\|\bar F\|_\kappa\le CL^{-1/2}.
$$

On $Q_L$, the undifferentiated field terms in $F^a-\bar F$ cancel. The initial heat terms differ by Corollary 8.4. The nonlinear terms are the heat evolutions of $\operatorname{div}(\bar u\otimes\bar u)$ and its periodization, so Lemma 8.3 applies under the time integral. Consequently

$$
\|\nabla(F^a(t)-\bar F(t))\|_{L^2(Q_L)}
\le CL^{-5/2}\|\bar u(0)\|_1
 +CL^{-7/2}\int_0^t\|\bar u(s)\|_2^2\,ds.
$$

The support volume is at most $CL^3$. Cauchy–Schwarz and the cutoff $L^2$ estimate yield $\|\bar u(0)\|_1\le CL^2$, while $\|\bar u(s)\|_2^2\le CL$. The two errors are therefore bounded by $CL^{-1/2}$ and $CL^{-5/2}$, respectively. Since the weight $(1-t)^{1/4-\kappa}$ is at most one, the asserted weighted bound follows. Continuity and membership in $X_L$ follow from the periodic heat and bilinear estimates. At $t=0$ the residual vanishes.

The formal residual estimate is written on rescaled time pieces: its size is bounded by $K T^{1/4}\theta^n$. The relation $T=L^{-2}$ explains the same small parameter, $T^{1/4}=L^{-1/2}$, while the formal construction also carries a pressure cutoff and a piecewise forcing identity.

### 8.4. Restricting the interaction to one ball

Put $B=B_{L/8}$. On $H^1(B)$ use

$$
\|\zeta\|_B=\|\nabla\zeta\|_{L^2(B)}+\|\zeta\|_{L^6(B)}.
$$

For a fixed ball this is equivalent to the usual $H^1$ norm. Its advantage here is the uniform restriction bound

$$
\|v|_B\|_B\le C\|v\|_X,\qquad
\|z|_B\|_B\le C\|z\|_{X_L}.
$$

The two inequalities follow from the whole-space and mean-zero periodic Sobolev bounds. The radius-dependent estimate $\|\zeta\|_2\le |B|^{1/3}\|\zeta\|_6$ will be used only where its factor $O(L)$ is included explicitly.

For a continuous divergence-free $\zeta(t)\in H^1(B)$, define $f_\zeta$ on $B$ by

$$
f_\zeta=(\bar u\cdot\nabla)\zeta+(\zeta\cdot\nabla)\bar u
$$

and extend it by zero outside $B$. Also extend the tensor

$$
F_\zeta=\zeta\otimes\bar u+\bar u\otimes\zeta
$$

by zero. Then $F_\zeta\in W^{1,1}(\mathbb R^3)$ and $\operatorname{div}F_\zeta=f_\zeta$ in distributions.

Here is why the extension introduces no boundary distribution. A field in $H^1(B_r)$ has an $H^1$ extension to a slightly larger ball: one may reflect radially across $|x|=r$ in the annulus $r<|x|<3r/2$, multiply the reflected part by a smooth cutoff, and use the original field inside. The reflection and its inverse have bounded first derivatives on that annulus. The inner and outer traces coincide. Multiplication by the globally smooth $\bar u$, which vanishes outside $\overline B_r$, produces the indicated zero-extended tensor. Its weak derivative is the product-rule derivative. The possible boundary term is zero because $\bar u$ has zero trace there. All these products are integrable on their compact support, by Hölder. The divergence identities within $B$ then give $\operatorname{div}F_\zeta=f_\zeta$, and $\int f_\zeta=0$.

Define

$$
\mathcal A\zeta(t)=-\int_0^tG(t-s)\mathbb P f_\zeta(s)\,ds,
\qquad
\mathcal A_L\zeta(t)=-\int_0^tG_L(t-s)\mathbb P_L\Pi_Lf_\zeta(s)\,ds.
$$

**Lemma 8.6 (local interaction and comparison).** The maps $\mathcal A$ and $\mathcal A_L$ are bounded from $\mathcal Y_\kappa(H^1(B))$, restricted to divergence-free fields, into $\mathcal Y_\kappa(X)$ and $\mathcal Y_\kappa(X_L)$, with uniform bounds. Moreover,

$$
2B(\bar u,v)=\mathcal A(v|_B),\qquad
2B_L(u^a,z)=\mathcal A_L(z|_B),
$$

and

$$
\|(\mathcal A_L\zeta-\mathcal A\zeta)|_B\|_\kappa
\le CL^{-2}\|\zeta\|_\kappa.
$$

These assertions are the paper's (6.7)–(6.11), pp. 26–27.

**Proof.** Hölder and Sobolev give

$$
\|f_\zeta(t)\|_{3/2}
\le \|\bar u(t)\|_6\|\nabla\zeta(t)\|_2
+\|\zeta(t)\|_6\|\nabla\bar u(t)\|_2
\le C(1-t)^{-1/4}\|\zeta(t)\|_B.
$$

The heat–Leray smoothing estimate therefore bounds either integrand's target norm by

$$
C(t-s)^{-3/4}(1-s)^{\kappa-1/2}\|\zeta\|_\kappa.
$$

Its integral is at most $C_\kappa(1-t)^{\kappa-1/4}\|\zeta\|_\kappa$, by the weighted convolution calculation from Section 6. This proves existence and the uniform operator bounds. The usual split of the integral into $[0,t-\varepsilon]$ and its short final interval proves continuity: continuity controls the first part, and the integrable power $(t-s)^{-3/4}$ makes the second uniformly small. The two identities with $B$ follow by substituting $f_\zeta$ and using the support of $\bar u$.

For the comparison, retain the full tensor. The cutoff estimate and the local $L^6$ norm give

$$
\|F_\zeta(t)\|_1
\le2\|\bar u(t)\|_2\|\zeta(t)\|_{L^2(B)}
\le CL^{3/2}\|\zeta(t)\|_B.
$$

Applying Lemma 8.3 under the integral,

$$
\|(\mathcal A_L\zeta-\mathcal A\zeta)(t)|_B\|_B
\le CL^{-2}\|\zeta\|_\kappa
   \int_0^t(1-s)^{\kappa-1/4}\,ds
\le \frac{CL^{-2}}{\kappa+3/4}\|\zeta\|_\kappa.
$$

The time weight is at most one, so this proves the weighted comparison.

In the formal proof, restriction to this local region is represented by shell data. The interaction factors through restriction, and the whole-space and periodic factors have separate bounds. This is the role of the factorization and operator-norm declarations, rather than an assertion that the two ambient function spaces coincide.

### 8.5. Building an exact right inverse on the torus

Every field in $E$ is supported in one fixed ball $\overline B_{r_E}$. To see this, choose a basis and take the union of its finitely many supports. The map $E\to L^1$ is continuous because every linear map from a finite-dimensional normed space is continuous. Thus

$$
\|\gamma\|_1\le C_E\|\gamma\|_X,\qquad \gamma\in E.
$$

From now on choose $L\ge\max\{1,8r_E\}$, so that every correction can be periodized by Lemma 8.1.

Define the periodic linearized operator

$$
\mathcal L_L(\gamma,z)=
z-2B_L(u^a,z)-G_L(t)\Pi_L\gamma.
$$

**Proposition 8.7 (an approximate right inverse).** There is a linear map

$$
\mathcal R_L^a:\mathcal Y_\kappa(X_L)
\longrightarrow E\times\mathcal Y_\kappa(X_L)
$$

and a constant $C_2$ independent of $L$ such that

$$
\|\mathcal R_L^a g\|\le C_2\|g\|_\kappa,
\qquad
\|\mathcal L_L\mathcal R_L^a g-g\|_\kappa
\le C_2L^{-1/2}\|g\|_\kappa.
$$

The product norm is the maximum of the two component norms. This is Lemma 6.3 of the paper, pp. 27–28.

**Proof.** Apply the whole-space right inverse to the localized interaction of $g$:

$$
(\gamma,v)=\mathcal R\big(\mathcal A(g|_B)\big),\qquad
\zeta=g|_B+v|_B,\qquad
z=g+\mathcal A_L\zeta+G_L(t)\Pi_L\gamma.
$$

Define $\mathcal R_L^ag=(\gamma,z)$. Restriction, the two interaction operators, and $\mathcal R$ are bounded, so

$$
\max\{\|\gamma\|_X,\|v\|_\kappa,\|\zeta\|_\kappa,\|z\|_\kappa\}
\le C\|g\|_\kappa.
$$

For the free correction term use $\|G_L(t)\Pi_L\gamma\|_\kappa\le\|\gamma\|_X$, which follows from heat contraction and Lemma 8.1.

The operator defect has the exact identity

$$
\mathcal L_L(\gamma,z)-g
=\mathcal A_L(\zeta-z|_B).
$$

The defining equation for $(\gamma,v)$ reads

$$
v=\mathcal A(g|_B)+2B(u^*,v)+G(t)\gamma.
$$

Since $\mathcal A(v|_B)=2B(\bar u,v)$, this becomes

$$
v=\mathcal A\zeta+G(t)\gamma-2B(\bar u-u^*,v).
$$

Substitution into $\zeta-z|_B$ now gives the complete decomposition

$$
\zeta-z|_B
= (\mathcal A-\mathcal A_L)\zeta|_B
+\big(G(t)\gamma-G_L(t)\Pi_L\gamma\big)|_B
-2B(\bar u-u^*,v)|_B.
$$

The three terms have weighted norms bounded by

$$
CL^{-2}\|\zeta\|_\kappa,\qquad
CL^{-5/2}\|\gamma\|_1,\qquad
CL^{-1/2}\|v\|_\kappa,
$$

respectively. The first bound is Lemma 8.6. The second is Corollary 8.4 and the fact that the difference vanishes at $t=0$. For the third use uniform restriction, the cutoff bound and the mixed weighted bilinear estimate. Replace $\|\gamma\|_1$ by $C_E\|\gamma\|_X$ and use the already established bounds. Since $L\ge1$, the total is at most $CL^{-1/2}\|g\|_\kappa$. Applying the bounded operator $\mathcal A_L$ proves the asserted defect estimate.

**Proposition 8.8 (the unforced periodic correction).** For all sufficiently large $L$ there are $\gamma\in E$ and $z\in\mathcal Y_\kappa(X_L)$ such that

$$
u_L=u^a+z
$$

is an exact unforced mild solution on $[0,1)$, with smooth mean-zero datum

$$
u_L(0)=\Pi_L(\bar u(0)+\gamma),
$$

and

$$
\|z\|_\kappa\le4C_1C_2L^{-1/2},\qquad
\frac{c_*}{2}(1-t)^{-1/4}
\le\|u_L(t)\|_{X_L}\le C(1-t)^{-1/4}.
$$

This is the construction in §6.4 of the paper, pp. 28–29.

**Proof.** Take $L$ so large that $C_2L^{-1/2}\le1/2$. The operator $Q=I-\mathcal L_L\mathcal R_L^a$ then has norm at most $1/2$, and the norm-convergent geometric series defines

$$
\mathcal R_L=
\mathcal R_L^a\sum_{n=0}^\infty Q^n.
$$

Multiplication by $I-Q=\mathcal L_L\mathcal R_L^a$ telescopes. Hence $\mathcal L_L\mathcal R_L=I$ and $\|\mathcal R_L\|\le2C_2$. Both the correction and the trajectory are controlled in this product norm.

For completeness, perform the nonlinear step explicitly. Write $D=2C_2$, $a=\|F^a\|_\kappa$, and let $C_B$ be a common constant in

$$
\|B_L(z,z')\|_\kappa\le C_B\|z\|_\kappa\|z'\|_\kappa.
$$

Consider

$$
\Phi(z)=\big[\mathcal R_L(-F^a+B_L(z,z))\big]_2.
$$

On the closed ball of radius $r=2Da$,

$$
\|\Phi(z)\|_\kappa\le D(a+C_Br^2),
\qquad
\|\Phi(z)-\Phi(z')\|_\kappa
\le2DC_Br\|z-z'\|_\kappa.
$$

The condition $8C_BD^2a\le1$ makes the first bound at most $r$ and the second at most $\frac12\|z-z'\|_\kappa$. It holds after enlarging $L$, because $a\le C_1L^{-1/2}$. If $a=0$, the zero correction is already a fixed point. Otherwise the contraction theorem gives $z$ in the indicated ball. Let $\gamma$ be the first component of the same right-inverse output. Then

$$
\mathcal L_L(\gamma,z)=-F^a+B_L(z,z).
$$

Expanding this equality proves the exact mild equation

$$
u_L=G_L(t)(u^a(0)+\Pi_L\gamma)+B_L(u_L,u_L).
$$

Every residual term has cancelled. At $t=0$, both Duhamel integrals and $F^a$ vanish, so $z(0)=\Pi_L\gamma$. The initial datum is therefore the stated smooth periodization.

The correction bound is $r\le4C_1C_2L^{-1/2}$. Finally require

$$
C_1(1+4C_2)L^{-1/2}\le \frac{c_*}{2}.
$$

Using $\|z(t)\|\le(1-t)^{\kappa-1/4}\|z\|_\kappa
\le(1-t)^{-1/4}\|z\|_\kappa$ and Proposition 8.5 proves the lower bound. The upper bound follows from the same triangle inequality. These three smallness choices serve separate purposes: inverse convergence, nonlinear contraction, and preservation of the positive lower norm.

### 8.6. The inverse argument in the formal sequence spaces

The continuous proof above displays the powers of $L$ used by the revised paper. The formal proof organizes time into geometric pieces on a fixed unit torus. The following two operator statements make its inverse transfer explicit.

**Lemma 8.9 (perturbing a bounded right inverse).** Let $A,A':U\to Y$ and $R:Y\to U$ be bounded linear maps between Banach spaces, with $AR=I$, $\|R\|\le K$ and

$$
\|A'-A\|K\le\frac12.
$$

Then $A'$ has a bounded right inverse of norm at most $2K$.

**Proof.** Set $Q=(A'-A)R$. The series $\sum_{n\ge0}(-Q)^n$ converges in operator norm and has norm at most two. Since $A'R=I+Q$,

$$
R'=R\sum_{n\ge0}(-Q)^n
$$

satisfies $A'R'=I$ and $\|R'\|\le2K$. This is the precise general statement carried by the formal right-inverse perturbation theorem.

**Lemma 8.10 (transferring an inverse through a restriction space).** Let $E,Y,Y_L,Z$ be Banach spaces. Consider bounded maps

$$
S:Y\to Y,\quad G:E\to Y,\quad B:Z\to Y,\quad D:Y\to Z,
$$

and periodic counterparts $S_L,G_L^\circ,B_L^\circ,D_L^\circ$ with $Y_L$ in place of $Y$. Here the superscript distinguishes these abstract maps from the heat and bilinear operators above. Suppose $\|S\|,\|S_L\|\le q<1$ with $q\ge0$. Put

$$
\mathsf Q=(I-S)^{-1},\qquad \mathsf Q_L=(I-S_L)^{-1}.
$$

Suppose

$$
\mathcal C(e,y)=(I-S)y-Ge-BDy
$$

has a right inverse $R_f:Y\to E\times Y$ with $\|R_f\|\le K_f$. Define

$$
C_\circ=1+K_f\|B\|(1+\|D\|).
$$

Assume the two restricted propagators satisfy

$$
\|D_L^\circ \mathsf Q_L B_L^\circ-D\mathsf Q B\|\le\delta,\qquad
\|D_L^\circ \mathsf Q_L G_L^\circ-D\mathsf Q G\|\le\delta,
$$

and $4\delta C_\circ\le1$. Then

$$
\mathcal C_L(e,y_L)
=(I-S_L)y_L-G_L^\circ e-B_L^\circ D_L^\circ y_L
$$

has a bounded right inverse. One possible norm bound is

$$
\frac1{1-q}
\left[
1+
(\|B_L^\circ\|+\|G_L^\circ\|+1)
\,2C_\circ\|D_L^\circ\|\frac1{1-q}
\right].
$$

This is the formal shell inverse transfer statement, an algebraic version of the local restriction argument.

**Proof.** Eliminate $y$ and work first on $E\times Z$. Define

$$
\mathcal H(e,\zeta)=\zeta-D\mathsf Q B\zeta-D\mathsf Q Ge.
$$

For given $\eta\in Z$, choose $(e,y)=R_f(B\eta)$ and set $\zeta=\eta+Dy$. The identity $\mathcal C(e,y)=B\eta$ implies

$$
y=\mathsf Q Ge+\mathsf Q B(\eta+Dy),
$$

so $\mathcal H(e,\zeta)=\eta$. This constructs a right inverse $R_H$ for $\mathcal H$. Its norm is at most $C_\circ$, since

$$
\|e\|\le K_f\|B\|\|\eta\|,
\qquad
\|\eta+Dy\|\le(1+\|D\|K_f\|B\|)\|\eta\|.
$$

The periodic reduced map is

$$
\mathcal H_L(e,\zeta)
=\zeta-D_L^\circ \mathsf Q_L B_L^\circ\zeta
      -D_L^\circ \mathsf Q_L G_L^\circ e.
$$

In the maximum norm on $E\times Z$, the two comparison assumptions give
$\|\mathcal H_L-\mathcal H\|\le2\delta$. Thus
$\|\mathcal H_L-\mathcal H\|\|R_H\|\le1/2$.
Lemma 8.9 supplies a right inverse $R_{H,L}$ of norm at most $2C_\circ$.

Now let $h\in Y_L$, put

$$
(e,\zeta)=R_{H,L}D_L^\circ \mathsf Q_L h,
\qquad
y_L=\mathsf Q_L(h+B_L^\circ\zeta+G_L^\circ e).
$$

The reduced equation says precisely that $\zeta=D_L^\circ y_L$. Substitution proves $\mathcal C_L(e,y_L)=h$.

For the norm, set $c=(1-q)^{-1}$ and $a=2C_\circ\|D_L^\circ\|c$. The geometric series gives $\|\mathsf Q_L\|\le c$, so

$$
\max\{\|e\|,\|\zeta\|\}\le a\|h\|,
\qquad
\|y_L\|\le c\big(1+(\|B_L^\circ\|+\|G_L^\circ\|)a\big)\|h\|.
$$

Because $c\ge1$, both components are bounded by
$c[1+(\|B_L^\circ\|+\|G_L^\circ\|+1)a]\|h\|$.
This is the stated bound.

In the formal application, $Y$ and $Y_L$ are bounded sequences of short time pieces, while $Z$ holds their restrictions. The operators $S,S_L$ pass the previous piece's endpoint to the next piece by free evolution. Their norms are bounded by $\lambda^{1/4}/\theta<1$. The whole-space inverse supplies $R_f$, heat comparison supplies the two $\delta$ bounds, and the shell lemma supplies the periodic inverse. Approximating the profile pieces by compact fields and then replacing those approximants by the periodic cutoff field requires two uses of Lemma 8.9. The formal assembly discharges both smallness conditions.

The sequence contraction then produces exact mild pieces of the form

$$
u_n=u_n^a+\theta^n z_n,\qquad \sup_n\|z_n\|<\infty.
$$

Their endpoint conditions are part of the contraction conclusion. The gluing theorem uses those equalities to join the pieces into one mild solution; no jump in time is left at a junction. This is the formal route corresponding to the continuous correction in Proposition 8.8.
<!-- /passage:sec-8-the-construction-on-a-large-torus -->

## 9. The unit torus and the theorem

<!-- passage:sec-9-the-unit-torus-and-the-theorem -->

### 9.1. Scaling the constructed solution

**Proposition 9.1 (period one and the local profile estimate).** Let $u_L$ be the solution of Proposition 8.8 and set

$$
T=L^{-2},\qquad
u_{\mathrm{per}}(t,x)=L\,u_L(L^2t,Lx),\qquad 0\le t<T.
$$

Then $u_{\mathrm{per}}$ is a mean-zero periodic mild solution of viscosity one on the unit torus, with smooth divergence-free datum. There are positive constants $c,C$ such that

$$
c(T-t)^{-1/4}
\le \|u_{\mathrm{per}}(t)\|_{H^1(\mathbb T^3)}
\le C(T-t)^{-1/4},
$$

and

$$
\|u_{\mathrm{per}}(t)-u_T^*(t)\|_{H^1(B_{1/16})}
\le C(T-t)^{\kappa-1/4}.
$$

This is Proposition 2.2 of the paper, p. 11, with its proof on p. 29.

**Proof.** The transformed field has period one. Its divergence is zero, and its mean remains zero by change of variables. The initial field is the periodization of

$$
x\longmapsto L\big(\bar u(0,Lx)+\gamma(Lx)\big).
$$

It is smooth and supported, before periodization, in $\overline B_{1/8}$.

The Navier–Stokes scaling preserves viscosity one. Directly, every term in the velocity equation gains the factor $L^3$, while the pressure transforms by $p(t,x)\mapsto L^2p(L^2t,Lx)$. The same identity follows in the mild formulation by the heat scaling and the change of integration variable $s=L^2t'$.

The gradient norm transforms according to

$$
\|\nabla u_{\mathrm{per}}(t)\|_{L^2(\mathbb T^3)}
=L^{1/2}\|\nabla u_L(L^2t)\|_{L^2(\mathbb T_L^3)}.
$$

Since $1-L^2t=L^2(T-t)$,

$$
L^{1/2}(1-L^2t)^{-1/4}=(T-t)^{-1/4}.
$$

The bounds from Proposition 8.8 therefore give the asserted gradient rate. On the unit mean-zero torus, the full $H^1$ norm is bounded above by a fixed multiple of the gradient norm and below by the gradient norm itself. This proves the displayed two-sided $H^1$ rate.

For the local estimate, $u^a=u^*$ on $B_{L/16}$. Hence $u_L-u^*=z$ there. The rescaled profile identity is exact:

$$
L\,u_1^*(L^2t,Lx)
= (T-t)^{-1/2}
W\!\left(\log\frac{T}{T-t},\frac{x}{\sqrt{T-t}}\right)
=u_T^*(t,x).
$$

In particular no change of profile phase is needed. On $B_{1/16}$,

$$
u_{\mathrm{per}}(t)-u_T^*(t)=Lz(L^2t,L\,\cdot).
$$

The right side is the restriction of a mean-zero periodic field. By the unit-torus norm inequality,

$$
\begin{aligned}
\|u_{\mathrm{per}}(t)-u_T^*(t)\|_{H^1(B_{1/16})}
&\le C L^{1/2}\|z(L^2t)\|_{X_L}\\
&\le C L^{1/2}(1-L^2t)^{\kappa-1/4}\|z\|_\kappa\\
&=C T^{-\kappa}(T-t)^{\kappa-1/4}\|z\|_\kappa.
\end{aligned}
$$

The choice of $L$, and therefore of $T$, is fixed. Its factor $T^{-\kappa}$ is absorbed in the theorem's constant.

The comparison is local in physical space. A nonzero periodic field has no finite global $H^1(\mathbb R^3)$ norm, so the norm in this statement must retain its ball.

Here is the corresponding convergence statement in similarity variables. Put $h=T-t=Te^{-s}$ and

$$
U_{\mathrm{per}}(s,y)=\sqrt h\,u_{\mathrm{per}}(t,\sqrt h\,y).
$$

The comparison region becomes $|y|<(16\sqrt h)^{-1}$. On that region the gradient norm of $U_{\mathrm{per}}-W$ is $h^{1/4}$ times the physical gradient error. The $L^6$ norm transforms by the same factor. Since the physical error is the restriction of the rescaled $z$, periodic Sobolev also controls its $L^6$ norm by $CT^{-\kappa}h^{\kappa-1/4}$. Thus

$$
\|\nabla_y(U_{\mathrm{per}}-W)\|_{L^2(B_{1/(16\sqrt h)})}
+\|U_{\mathrm{per}}-W\|_{L^6(B_{1/(16\sqrt h)})}
\le Ce^{-\kappa s}.
$$

Every fixed ball eventually lies in this expanding region. Hölder then gives convergence in $H^1$ on each fixed ball, with a ball-dependent constant. This is an explicit consequence of the estimates just proved.

### 9.2. Smooth velocity and periodic pressure before blow-up

**Lemma 9.2 (upgrading the periodic mild solution).** The solution in Proposition 9.1 has a smooth periodic velocity and a smooth periodic pressure on $[0,T)\times\mathbb T^3$. It obeys the energy identity on every compact time interval before $T$. This is the periodic part of Lemma 2.3 and Appendix A.2, pp. 11 and 49.

**Proof.** Apply the periodic part of Proposition 7.3. The datum is smooth, divergence-free and mean-zero. On every $[0,b]$ with $b<T$, continuity into $X_1$ and Poincaré give the $H^1$ bound required there. Thus the constructed mild path has smooth periodic velocity and pressure on that interval. Choose the pressure with zero spatial mean; this makes the representatives agree on overlaps and gives one smooth pressure on $[0,T)$.

Multiply the smooth equation by the velocity and integrate over one cell. Periodicity cancels the boundary terms. Divergence freedom cancels the advective contribution and the pressure contribution. We obtain

$$
\frac12\|u_{\mathrm{per}}(t)\|_2^2
+\int_0^t\|\nabla u_{\mathrm{per}}(s)\|_2^2\,ds
=\frac12\|u_{\mathrm{per}}(0)\|_2^2
\qquad(t<T).
$$

The two-sided $H^1$ rate then rules out smooth continuation through $T$: smoothness on a compact time interval containing $T$ and a compact spatial torus would give a bounded $H^1$ norm.

The formal endpoint uses a periodic Fourier mild trajectory whose norm is unbounded. The present lemma supplies the paper's smooth physical representative through the stated local theory; the top-level formal endpoint itself does not include that entire physical conclusion.

### 9.3. Arbitrary periodic-velocity competitors and their pressure

The solution constructed above has periodic pressure. The exported formal nonexistence statement quantifies over smooth solutions whose velocity is periodic, while imposing no periodicity on their pressure. The next calculation explains that additional step.

**Lemma 9.3 (removing the affine part of the pressure).** Suppose $(v,p)$ is a smooth unforced solution of viscosity one on $[0,\infty)\times\mathbb R^3$, with velocity periodic of period one and with datum $v_0$. There is a smooth unforced solution $(\widetilde v,\widetilde p)$ with the same datum, whose velocity and pressure are both periodic.

**Proof.** The momentum equation expresses $\nabla p$ in terms of $v$ and its derivatives, all of which are periodic. Therefore, for each coordinate vector $e_j$, the gradient of

$$
p(t,x+e_j)-p(t,x)
$$

vanishes. This difference is constant in $x$. Put $a_j(t)=p(t,e_j)-p(t,0)$ and $a(t)=(a_1(t),a_2(t),a_3(t))$. Then

$$
p_0(t,x)=p(t,x)-a(t)\cdot x
$$

is periodic. The functions $a_j$ are smooth. The identity at $t=0$ follows by continuity from positive times if the differential equation is initially stated only for $t>0$.

Define

$$
g(t)=\int_0^t a(s)\,ds,\qquad
b(t)=-\int_0^t g(s)\,ds
$$

and

$$
\widetilde v(t,x)=v(t,x+b(t))+g(t),\qquad
\widetilde p(t,x)=p(t,x+b(t))-a(t)\cdot(x+b(t)).
$$

The pressure is a spatial translate of $p_0$, so it is periodic; the velocity is periodic as well. Both are smooth, and $g(0)=b(0)=0$ preserves the datum.

To check the equation, differentiate. The time derivative of the translated velocity contributes $(b'\cdot\nabla)v+g'$. Its new advection term contributes $(g\cdot\nabla)v$ in addition to the old one. Since $b'=-g$, these two transport terms cancel. The remaining added term is $g'=a$, exactly the change from $-\nabla p$ to $-\nabla\widetilde p$. The Laplacian and divergence commute with translation, and a spatially constant velocity addition has zero divergence. This proves the assertion.

This calculation is the moving-frame reduction carried by the formal proof. It also gives a direct proof of the pressure adjustment described by Tao's Lemma 4.1(ii) and Galilean transformation (33). When $v_0$ has mean zero, integrating the transformed equation over a cell shows that $\widetilde v$ keeps mean zero.

**Proposition 9.4 (the formal periodic nonexistence conclusion).** The periodic datum produced above implies, for each viscosity $\nu>0$, the existence of smooth divergence-free period-one data admitting no global smooth unforced solution with periodic velocity.

**Proof.** First take $\nu=1$. Suppose a global smooth periodic-velocity solution had the constructed datum. Lemma 9.3 changes its pressure to a periodic one while preserving that datum. Its periodic Fourier representation satisfies the mild equation. Uniqueness therefore identifies it with the constructed solution before $T$. Smoothness on $[0,T]\times\mathbb T^3$ bounds its $H^1$ norm, contradicting Proposition 9.1.

For $\nu>0$, use the datum $\nu u_0$. A hypothetical global solution $(v,p)$ with viscosity $\nu$ and this datum yields a viscosity-one solution

$$
\widehat v(t,x)=\nu^{-1}v(t/\nu,x),
\qquad
\widehat p(t,x)=\nu^{-2}p(t/\nu,x)
$$

with datum $u_0$. Substitution into the equation verifies the scaling term by term. Its velocity remains periodic. The viscosity-one contradiction applies.

This is a conditional conclusion: the initial profile remains an assumption. The formal theorem obtains it from the formal profile premise and the complete torus construction.

### 9.4. The final norm contradiction in the formal pieces

The final norm argument can be read without the representation details.

**Lemma 9.5 (unboundedness after gluing).** Let $0<\lambda,\theta<1$, $T>0$, and set

$$
\mu_n=T\lambda^n,\qquad t_n=T-\mu_n.
$$

Suppose continuous $V$-valued pieces on $0\le s\le1-\lambda$ have the form

$$
u_n(s)=u_n^a(s)+\theta^n z_n(s),
\qquad
\|u_n^a(s)\|\ge c_0>0,\qquad
\sup_n\|z_n\|_\infty\le Z,
$$

and are glued with

$$
u(t_n+\mu_ns)=\mu_n^{-1/4}u_n(s).
$$

Then $\|u(t)\|$ is unbounded on $[0,T)$. This is the formal gluing-to-unboundedness statement used in the construction.

**Proof.** Since $\theta^nZ\to0$, choose $N$ so that $\theta^nZ\le c_0/2$ for $n\ge N$. The reverse triangle inequality gives $\|u_n(0)\|\ge c_0/2$. At the junction times,

$$
\|u(t_n)\|\ge \frac{c_0}{2}(T\lambda^n)^{-1/4}\longrightarrow\infty.
$$

All $t_n$ lie in $[0,T)$, which proves unboundedness.

The same identity gives a quantitative late-time bound if one also retains the uniform upper bound $\|u_n^a\|_\infty\le M$. For $n\ge N$ and $0\le s\le1-\lambda$, $T-t=\mu_n(1-s)$ with $\lambda\le1-s\le1$. Therefore

$$
\frac{c_0\lambda^{1/4}}2(T-t)^{-1/4}
\le\|u(t)\|
\le(M+Z)(T-t)^{-1/4}.
$$

This is an elementary deduction from the retained piece bounds and the gluing identity. The intermediate periodic mild-solution statement records unboundedness, and the final theorem records nonexistence of global smooth periodic-velocity solutions; neither states this two-sided formula or the local physical profile estimate of Proposition 9.1.

Together with the whole-space construction in Section 7, Proposition 9.1 and Lemma 9.2 complete the analytic proof of Theorem A. Proposition 9.4 explains the broader periodic nonexistence formulation exported by Lean. The additional work needed for an unconditional blow-up result is the separate construction of a profile.
<!-- /passage:sec-9-the-unit-torus-and-the-theorem -->

## Appendix A. The analytic results used above

<!-- passage:sec-appendix-a-the-analytic-results-used-above -->

This appendix supplies the proofs deferred from §2 and makes explicit the two bounds added by the formal profile premise. Its numbered lemmas are ours. The paper's Appendix A has two subsections, A.1 and A.2; all paper correspondences below use that numbering.

### Lemma A.1. Integrability at the moving time endpoint

*Paper correspondence: Lemma 3.3 and Appendix A.1, pp. 14 and 47.*

Assume a strongly continuous contraction semigroup $H_t$ and a continuous symmetric bilinear family $K(\tau)$ on a Banach space, with $\|K(\tau)(x,y)\|\le C_K\tau^{-3/4}\|x\|\|y\|$. Then the integral and estimate in Lemma 2.5 hold.

**Proof.** Bilinearity, the bound, and continuity in $\tau>0$ imply joint continuity of $(\tau,x,y)\mapsto K(\tau)(x,y)$ away from zero. For fixed $t$, the integrand is strongly measurable on $[a,t)$ and bounded in norm by $C_KM_fM_g(t-r)^{-3/4}$. Its norm integral is at most $4C_KM_fM_g(t-a)^{1/4}$, proving Bochner integrability and the estimate.

For continuity, fix $t_0\in[a,b]$ and a small $\delta>0$. Split the integral into the part where $t-r\ge\delta$ and a terminal piece of length at most $\delta$. On the first part, the integrand and its parameter dependence are continuous on a compact set; extend the integrand by zero outside its integration range and use dominated convergence. The change of the integration range contributes only a bounded integrand times an interval whose length tends to zero. Each terminal piece has norm at most $4C_KM_fM_g\delta^{1/4}$, uniformly in $t$. First let $t\to t_0$, then $\delta\to0$. At $t_0=a$, the displayed integral estimate alone gives continuity. $\square$

The formal variation-of-constants integral theorem includes existence, continuity and the explicit factor $4(t-a)^{1/4}$ on intervals of length at most one.

The formal abstract assumptions bound the kernel near time zero; larger intervals are handled by the heat shift law or by subdivision. Our physical estimate is available for every positive $\tau$.

### Lemma A.2. Linear evolution, small data and restarting

*Paper correspondence: Lemmas 3.4–3.5 and Appendix A.1, pp. 14–15 and 47; the small-data statement is used by the formal proof of Lemma 4.2.*

**Proof of finite-interval linear solvability.** In $C([a,b];X)$ use the equivalent norm

$$
\|h\|_\beta=\sup_{a\le t\le b}e^{-\beta(t-a)}\|h(t)\|_X.
$$

Writing $F=\sup\|f(t)\|_X$, the linear map $Lh=2B_a(f,h)$ satisfies

$$
\|Lh\|_\beta
\le 2C_KF\|h\|_\beta\int_0^\infty r^{-3/4}e^{-\beta r}\,dr
=2C_KF\Gamma(1/4)\beta^{-1/4}\|h\|_\beta.
$$

Choose $\beta$ so that the last coefficient $q$ is below one. Then $h=\sum_{n\ge0}L^ng$ converges in this norm and solves $h=Lh+g$. The estimate $\|h\|_\beta\le(1-q)^{-1}\|g\|_\beta$ gives boundedness, and uniqueness follows from $\|h_1-h_2\|_\beta\le q\|h_1-h_2\|_\beta$. Each term of the sum is linear in $g$, so the solution map is linear. This proves Lemma 2.6.

The formal linear construction subdivides time so that each piece operator is inverted by a norm-convergent geometric series.

On an interval of length $\delta$, Lemma A.1 bounds the linear operator by $8C_KF\delta^{1/4}$. Choose this below one, solve on the first interval, restart at its endpoint, and repeat finitely many times. This produces the same unique solution as the exponentially weighted argument and explains how the formal piece construction covers a large background on a long interval.

**Proof of small-data existence.** For $\delta\le1$, consider $\Phi(u)(t)=H_t x+B_0(u,u)(t)$ on $C([0,\delta];X)$ with the ball $\|u\|_\infty\le2\|x\|_X$. Lemma A.1 gives

$$
\|B_0(u,u)\|_\infty\le16C_K\delta^{1/4}\|x\|_X^2,
$$

and, by bilinearity and symmetry,

$$
\|B_0(u,u)-B_0(v,v)\|_\infty
\le16C_K\delta^{1/4}\|x\|_X\|u-v\|_\infty.
$$

For $\|x\|_X\le(32C_K)^{-1}$ and $\delta=1$, this map preserves the ball and has Lipschitz constant at most $1/2$. Its iterates form a Cauchy sequence, since consecutive differences shrink geometrically; their limit is the desired mild solution and has norm at most $2\|x\|_X$. For arbitrary $x$, choosing a sufficiently small $\delta$ proves local existence. The case $x=0$ gives the zero solution directly.

**Proof of restarting.** Apply $H_{t-m}$ to the integral equation at $m$. The bounded operator passes through the Bochner integral. The semigroup law and $H_{t-m}K(m-r)=K(t-r)$ give

$$
H_{t-m}u(m)=H_{t-a}u(a)+\int_a^mK(t-r)(f(r),h(r))\,dr.
$$

Subtract this from the equation at $t$ to obtain Lemma 2.7's restarted equation. Conversely, adding the restarted pieces proves concatenation.

**Proof of uniqueness.** If $u$ and $v$ have the same datum, their difference satisfies

$$
u-v=B_a(u,u)-B_a(v,v)=2B_a\left(\frac{u+v}{2},u-v\right).
$$

Apply the proved linear uniqueness with zero source. This works on closed intervals and, by restriction, on any half-open interval. $\square$

The formal mild uniqueness theorem covers both closed and half-open time intervals.

### Lemma A.3. The weak identity fixes the integral solution and its initial trace

*Paper correspondence: Lemma 3.6 and Appendix A.1, pp. 15 and 47–48.*

**Proof of Lemma 2.8.** Translate the initial time to zero. Let $E_2$ be the closure of Schwartz functions in the uniformly local norm $\|f\|_{L^2_{\mathrm{uloc}}}=\sup_x\|f\|_{L^2(x+B_1)}$. Hölder gives $\|f\|_{L^2_{\mathrm{uloc}}}\le |B_1|^{1/3}\|f\|_6$, and compact smooth approximation in $L^6$ gives $L^6\subset E_2$. Consequently $u\in C([0,b];E_2)$, in particular $u\in L^2((0,c);E_2)$ for every $c<b$.

The precise external result used is Dubois's Theorem 1: in this latter time-space class, the Navier–Stokes formulation tested against compact solenoidal space-time fields is equivalent to the projected integral formulation, with a unique tempered-distribution initial trace and a trajectory continuous in tempered distributions. This is the only implication needed here.

To verify the test formulation, let $\phi(t,x)$ be a smooth compactly supported solenoidal field. The product rule and the assumed identity for fixed spatial tests give

$$
\frac d{dt}\int u(t)\cdot\phi(t)
=\int u\cdot(\partial_t\phi+\Delta\phi)
+\sum_{i,j}u_i u_j\partial_i\phi_j.
$$

One may justify the product rule by difference quotients: compact support and $L^6$ continuity handle the moving test, while the fixed-test hypothesis handles the velocity difference. Integration in time is exactly the required space-time identity, including the datum $u(0)$. Dubois's theorem therefore gives

$$
u(t)=H_tv_0-\int_0^tH_{t-r}\mathbb P\operatorname{div}(u(r)\otimes u(r))\,dr
$$

in tempered distributions. The nonlinear integrand is $K(t-r)(u(r),u(r))$. Lemma 2.5 shows that this distributional integral is the same as its $X$-valued Bochner integral, since testing against a Schwartz function is a continuous functional on $X$ by Hölder and the Sobolev inequality. That integral tends to zero in $X$ as $t\downarrow0$, and $H_tu(0)\to u(0)$ in $X$. Uniqueness of the distributional trace forces $v_0=u(0)$. The two sides are continuous in $X$, so the equality extends to $t=b$. This proves the lemma. $\square$

The supplied formal weak-to-mild proof uses the Fourier test-field density argument instead of invoking Dubois's theorem.

Its hypothesis packages the extra decay and time-difference properties already mentioned after Lemma 2.8. These are verified for the profile by its physical evolution: once Lemmas A.5 and A.6 hold, the momentum equation yields $|\partial_tu_T^*(t,x)|\le C_b(1+|x|)^{-3}$ on a compact interval $[0,b]$ below $T$. Hence

$$
|u_T^*(t,x)-u_T^*(t',x)|\le C_b|t-t'|(1+|x|)^{-3}.
$$

The square of the spatial majorant is integrable. This proves both existence of the $L^2$ time differences and their continuity in $L^2$, without asserting that an individual profile slice lies in $L^2$.

### Lemma A.4. Periodic Sobolev and heat estimates

*Paper correspondence: Lemma 3.7 and Appendix A.1, pp. 16 and 48.*

**Proof of Lemma 2.9.** On the unit torus, Fourier expansion gives $\|u\|_2\le(2\pi)^{-1}\|\nabla u\|_2$ for a mean-zero field. Cover the torus by finitely many coordinate cubes and a smooth partition of unity. Apply the Euclidean Sobolev inequality from Lemma 2.1 to the compactly supported local pieces. Summing gives $\|u\|_6\le C(\|\nabla u\|_2+\|u\|_2)$, and the Poincaré bound removes the last term. For period $L$, write $v(z)=u(Lz)$. Both $\|v\|_6$ and $\|\nabla v\|_2$ are $L^{-1/2}$ times their corresponding norms on $Q_L$, proving independence of $L$.

For $f\in L^{3/2}(Q_L)$ of zero mean, set $z=H_\tau\mathbb P_Lf$. Its Fourier coefficients decay rapidly because $f\in L^1(Q_L)$ and the heat multiplier is Gaussian; hence $z$ is smooth, solenoidal and mean zero. Put $\Psi=-\Delta H_\tau z$. Parseval and the self-adjointness of the projection give

$$
\int_{Q_L}\Psi\cdot f=\|\nabla z\|_2^2.
$$

To see this directly, the coefficient of $\Psi$ at $k$ is $4\pi^2|k|^2e^{-4\pi^2\tau|k|^2}\widehat z(k)$, while $\widehat z(k)=e^{-4\pi^2\tau|k|^2}P_k\widehat f(k)$. Their pairing is $4\pi^2|k|^2|\widehat z(k)|^2$ after using $P_k\widehat z(k)=\widehat z(k)$.

The scalar bounds $r^{1/2}e^{-r}\le C$ and $re^{-r}\le C$ show

$$
\|\Psi\|_2\le C\tau^{-1/2}\|z\|_{X_L},\qquad
\|\nabla\Psi\|_2\le C\tau^{-1}\|z\|_{X_L}.
$$

Interpolate $L^3$ between $L^2$ and $L^6$, and apply the uniform Sobolev inequality:

$$
\|z\|_{X_L}^2
\le\|f\|_{3/2}\|\Psi\|_3
\le\|f\|_{3/2}\|\Psi\|_2^{1/2}\|\Psi\|_6^{1/2}
\le C\tau^{-3/4}\|f\|_{3/2}\|z\|_{X_L}.
$$

Divide if $z\ne0$; if $z=0$ the bound is immediate. The semigroup identity is coefficientwise. For continuity in positive $\tau$, factor off half of a fixed positive time and use strong heat continuity. Finally, $(u\cdot\nabla)v=\operatorname{div}(v\otimes u)$ has zero mean on a periodic cell. Hölder and the uniform Sobolev inequality control its $L^{3/2}$ norm, giving the bilinear estimate. $\square$

The formal periodic kernel estimate is formulated on a unit-period Fourier space and is used on short time steps.

The large-period estimate above follows from the displayed scaling. The named formal bound is stated for $0<\tau\le1$ on the unit-period space; the comparison table therefore does not equate it with the whole all-period statement of Lemma 2.9.

### Lemma A.5. Recovering the extra spatial derivative bound

*Paper correspondence: Remark 1.2, p. 3; the second-derivative clause of the formal profile definition.*

Suppose a smooth ancient Navier–Stokes field satisfies $|u(t,x)|\le C/(|x|+\sqrt{T-t})$ for every $t<T$. Then for each fixed integer $j\ge1$,

$$
|\nabla_x^j u(t,x)|\le C_j(|x|+\sqrt{T-t})^{-1-j}.
$$

**Proof.** The local input is the spatial interior estimate of Pineau–Vicol, Lemma 9.1: a smooth solution bounded by $A/r$ on a backward parabolic cylinder of radius $r$ has its $j$th spatial derivative bounded by $C(j,\varepsilon,A)r^{-j-1}$ on a fixed smaller cylinder. No pressure bound or time-derivative estimate is part of this input.

Fix $(t,x)$ and put $d=|x|+\sqrt{T-t}$ and $r=d/8$. On the backward cylinder with spatial radius $2r$ and top time $t$, the quantity $|z|+\sqrt{T-\tau}$ is bounded below by a fixed multiple of $d$. Indeed, if $|x|\ge d/2$, then $|z|\ge|x|-2r\ge d/4$; otherwise $\sqrt{T-\tau}\ge\sqrt{T-t}\ge d/2$. The assumed velocity bound is therefore at most $4C/d=C/(2r)$ there. The solution exists on this entire cylinder because it is ancient and its top time is below $T$. Apply the interior estimate with a fixed shrinking factor and evaluate at the top centre, obtaining $C_jd^{-j-1}$.

Returning to $W(s,y)=(T-t)^{1/2}u(t,(T-t)^{1/2}y)$ multiplies the $j$th spatial derivative by $(T-t)^{(j+1)/2}$. The asserted profile estimate is therefore

$$
|\nabla_y^jW(s,y)|\le C_j(1+|y|)^{-1-j}.
$$

In particular it supplies $j=2$, with a constant uniform in similarity time. $\square$

The formal profile definition assumes the second spatial derivative bound as an explicit field of its premise.

This lemma proves its analytic availability from the paper's assumptions. It does not attach a new compiled theorem to that implication.

### Lemma A.6. Recovering the pressure-gradient bound

*Paper correspondence: the profile equation (1.2), p. 2, and the explanatory paragraph in `lean/README.md`; the derivation is expanded here from the prior audit.*

If the smooth profile satisfies the bounds $|\nabla_y^jW(s,y)|\le C_j(1+|y|)^{-1-j}$ for $j=0,1,2$, then $|\nabla_yq(s,y)|\le C(1+|y|)^{-3}$ uniformly in $s$.

**Proof.** Write $F_{ij}=W_iW_j$. It and its first two spatial derivatives satisfy

$$
|\nabla^jF_{ij}(s,y)|\le C(1+|y|)^{-2-j},\qquad 0\le j\le2.
$$

Let $N(y)=(4\pi|y|)^{-1}$ and define the normalised pressure $q_0=\sum_{i,j}\partial_i\partial_jN*F_{ij}$. Convolution here uses the principal-value kernel

$$
K_{ij}(z)=\frac{3z_i z_j-\delta_{ij}|z|^2}{4\pi|z|^5}
$$

together with its local term $-\delta_{ij}F_{ij}/3$. This is well-defined: the kernel has zero spherical mean, so near the singularity subtract $F_{ij}(s,y)$; the remainder is locally integrable by smoothness. At infinity the product of the $|z|^{-3}$ kernel and the $|z|^{-2}$ input is absolutely integrable. This construction agrees with $\sum\mathcal R_i\mathcal R_jF_{ij}$ and satisfies $-\Delta q_0=\partial_i\partial_jF_{ij}$ in distributions, by $-\Delta N=\delta_0$.

We first estimate $\nabla q_0$. Fix $y$ with $r=|y|\ge2$. Choose a smooth cutoff $\chi$ supported in $B(y,r/2)$ and equal to one in $B(y,r/4)$, with $j$th derivatives bounded by $C_jr^{-j}$. Hold this cutoff fixed while differentiating the output at the point $y$. For the near input $\chi F$, commute a first derivative through the convolution and write $h=\partial_k(\chi F)$. Throughout its support,

$$
|h|\le Cr^{-3},\qquad |\nabla h|\le Cr^{-4}.
$$

The local term is $O(r^{-3})$. In the principal value, spherical cancellation permits subtraction of $h(y)$ throughout $B(y,r/2)$, so the remaining magnitude is at most

$$
Cr^{-4}\int_0^{r/2}\rho^{-3}\rho\rho^2\,d\rho\le Cr^{-3}.
$$

For the far input $(1-\chi)F$, the derivative may instead fall on the kernel because its support stays at least $r/4$ from $y$. Its contribution is bounded by

$$
C\int_{|z-y|\ge r/4}|y-z|^{-4}(1+|z|)^{-2}\,dz.
$$

On $|z|\le r/2$, this is at most $Cr^{-4}\int_0^{r/2}(1+\rho)^{-2}\rho^2\,d\rho\le Cr^{-3}$. On $r/2<|z|\le2r$, use $(1+|z|)^{-2}\le Cr^{-2}$ and integrate $|y-z|^{-4}$ outside $B(y,r/4)$, obtaining $Cr^{-3}$. On $|z|>2r$, integrate $C|z|^{-6}$ to obtain the same bound. A fixed-radius cutoff gives a uniform bound for $|y|\le2$. Thus

$$
|\nabla q_0(s,y)|\le C(1+|y|)^{-3}.
$$

All constants are uniform in $s$. The same cancellation formulas and integrable majorants show that $\nabla q_0$ is continuous in $(s,y)$, without differentiating the profile in similarity time.

It remains to identify the actual pressure gradient. Taking divergence of the profile equation yields $-\Delta q=\partial_i\partial_jF_{ij}$. Thus $H=\nabla q-\nabla q_0$ is harmonic in $y$, component by component. The momentum equation expresses it as

$$
H=-\partial_sW+G,\qquad
G=-\tfrac12W-\tfrac12(y\cdot\nabla)W+\Delta W-(W\cdot\nabla)W-\nabla q_0.
$$

Every term in $G$ is bounded by $C(1+|y|)^{-1}$ uniformly in $s$. A bound for $\partial_sW$ has not been assumed. To avoid that missing premise, take any $\psi\in C^\infty_c(\mathbb R)$ and integrate in similarity time:

$$
H_\psi(y)=\int\psi(s)H(s,y)\,ds
=\int\psi'(s)W(s,y)\,ds+\int\psi(s)G(s,y)\,ds.
$$

This is an entire harmonic vector field with $|H_\psi(y)|\le C_\psi(1+|y|)^{-1}$. An entire harmonic scalar function tending to zero at spatial infinity is zero: its value at any point is its average on every sphere about that point, and those averages tend to zero. Apply this componentwise to conclude $H_\psi=0$. Since this holds for every time test $\psi$, $H$ vanishes as a time distribution; its continuity makes the equality pointwise. Therefore $\nabla q=\nabla q_0$, which proves the estimate. $\square$

The formal profile premise contains the pressure-gradient bound, while the preceding harmonic-remainder argument supplies its analytic justification.

The elimination of the harmonic remainder is essential. Solving the pressure Poisson equation alone leaves a harmonic summand and does not justify identifying the prescribed $q$ with the normalised pressure.
<!-- /passage:sec-appendix-a-the-analytic-results-used-above -->

## References

<!-- passage:sec-references -->

The paper references throughout are to the supplied 79-page version of Alpöge and Buckmaster, *Finite-time blow-up for the Navier–Stokes equations*, at [commit ad53419](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546). Paper page numbers refer to the numbered PDF pages.

The external inputs used above are:

1. Sandrine Dubois, [*What is a solution to the Navier–Stokes equations?*](https://www.numdam.org/item/CRMATH_2002__335_1_27_0.pdf), C. R. Acad. Sci. Paris, Ser. I 335 (2002), 27–32. Theorem 1 supplies the implication stated in Lemma A.3.
2. Terence Tao, [*Localisation and compactness properties of the Navier–Stokes global regularity problem*](https://msp.org/apde/2013/6-1/apde-v6-n1-p02-s.pdf), Analysis & PDE 6 (2013), 25–107. Theorems 5.1 and 5.4, Corollaries 5.2 and 5.8, and Corollaries 4.3 and 11.1 are used with the hypotheses stated in Section 7.
3. Ben Pineau and Vlad Vicol, [*On rotated backwards self-similar solutions of the incompressible 3D Navier–Stokes equations*, arXiv:2607.09619v2](https://arxiv.org/pdf/2607.09619v2), 6 August 2026. Lemma 9.1 supplies the spatial interior estimate stated in Lemma A.5.
4. Gabriel Koch, Nikolai Nadirashvili, Gregory Seregin and Vladimír Šverák, [*Liouville theorems for the Navier–Stokes equations and applications*](https://arxiv.org/pdf/0709.3599), §3, formulas (3.3)–(3.7). Lemma 8.2 gives the kernel calculation used here.
5. Klaus-Jochen Engel and Rainer Nagel, [*One-Parameter Semigroups for Linear Evolution Equations*](https://link.springer.com/book/10.1007/b97696), GTM 194 (2000), Chapter IV, §1. Lemma 4.3 states the bounded-operator spectral facts used.

The comparison values describe the linked formal statement relative to the local mathematical statement: `same` after the stated identifications, `stronger` if it carries additional conclusion or generality, `weaker` if a named declaration retains only part of the claim, and `different` when the interfaces or premises require the explanation supplied with the comparison. A declaration can support distinct passages, so its single reader card sometimes uses `different` and explains those contexts separately.
<!-- /passage:sec-references -->

# Part II. A certificate produces a nonzero periodic profile

<!-- passage:sec-part-ii-a-certificate-produces-a-nonzero-periodic-profile -->

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · **part II** · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

This is an original account of §7 of Alpöge and Buckmaster, *Finite-time blow-up for the Navier–Stokes equations*, version of 20 November 2026. The reference version of the accompanying Lean source is `ad53419de079eb8f95f60313473374624a348546`. Paper references below use its printed numbering and pages. The notation agrees with the [specialist digest](../navier-stokes/digest.md). Our results and equations carry the prefix II; references to the authors' Appendix B keep the prefix B and the source key [P].

The input to this part is a certificate: approximate periodic fields, a finite-dimensional parameter set, and inequalities that control every admissible perturbation. The output is one nonzero smooth profile, together with the parameter, period, bounds and symmetries used to construct it. The existence of the concrete numerical certificate remains a separate premise.

We first solve the nonlinear equation for each fixed parameter by contraction. We then choose the parameter by a finite-dimensional fixed-point theorem. This follows the extended-certificate route in Lean and explains the purpose of (7.26). Section 9.4 also gives the paper's simultaneous Schauder–Tychonoff construction. For regularity we write out the paper's argument with the precise external results it uses, then explain the different formal route. The comparisons distinguish a proof of an analytic step from a theorem whose conclusion retains every requested witness.
<!-- /passage:sec-part-ii-a-certificate-produces-a-nonzero-periodic-profile -->

## 1. The result and its notation

<!-- passage:sec-1-the-result-and-its-notation -->

### 1.1 Theorem II.1: the full conclusion of Theorem 7.1

**Theorem II.1.** Suppose a certificate satisfies the conditions set out in §2 below. There exist a single parameter $\alpha_*\in K$, a smooth velocity $W:\mathbb R\times\mathbb R^3\to\mathbb R^3$, and a smooth pressure $q:\mathbb R\times\mathbb R^3\to\mathbb R$, with $S=S(\alpha_*)>0$, such that

$$
\partial_sW+\frac12W+\frac12(y\cdot\nabla)W-\Delta W
 +(W\cdot\nabla)W+\nabla q=0,
\qquad \nabla\cdot W=0,
\qquad W(s+S,y)=W(s,y).
$$

The velocity is nonzero and, for one finite constant $C$, satisfies

$$
|W(s,y)|\le \frac{C}{1+|y|},
\qquad |\nabla W(s,y)|\le \frac{C}{(1+|y|)^2}.
$$

Define the correction using that same parameter and that same velocity:

$$
v_*(\theta,y)=W(S\theta,y)-W^a_{\alpha_*}(\theta,y).
$$

Then $v_*\in D_S^\Gamma$, and all of the following hold together:

$$
\|v_*\|_w^2+\omega^2|\beta^a(\alpha_*)|^2\le4\varepsilon^2,
\qquad
\|\nabla v_*(\theta)\|_2\le M\quad\text{for every }\theta\in\mathbb R,
\qquad
\ell(v_*)=\bar\ell(\alpha_*).
\tag{II.1}
$$

For every $(R,\theta_0)\in\Gamma$, the same velocity satisfies

$$
W(s+S\theta_0,y)=R W(s,R^{-1}y)
\quad\text{for every }(s,y)\in\mathbb R\times\mathbb R^3.
\tag{II.2}
$$

These are the complete velocity, correction and symmetry conclusions of the paper's Theorem 7.1, including the multiplier term in (7.38). Spatial second derivatives of the correction are weak derivatives. The approximate field is only required to have the regularity stated in the certificate, so subtracting it from a smooth field does not make its Hessian classical. The norm in (II.1) is finite, and its gradient integrand uses the Frobenius matrix norm.

The period is the specified $S(\alpha_*)$; it need not be the least period. The theorem prescribes velocity symmetries. No choice of pressure gauge is part of its quantitative conclusion. The proof is completed in §12. [P, Theorem 7.1 and (7.38)–(7.39), p.35.]

### 1.2 Dictionary

In the table, $d$ has type `Breakdown.ExtendedCertificateData`. Its field names are qualified by that type. This convention makes the distinction between stored data and proved properties visible. The formal representations of $X$, $H$ and the graph domains are related by physical-reading lemmas; they are not literal synonyms for the paper's spaces.

| Symbol | Meaning in this account | Lean representation or interface |
|---|---|---|
| $s,\theta=s/S$ | Similarity time and period-one time | Real time; `Breakdown.Cert.TimeCircle` represents $\mathbb R/\mathbb Z$ |
| $y$ | Spatial similarity variable in $\mathbb R^3$ | `Breakdown.Space` |
| $X$ | Solenoidal homogeneous $H^1$, realised by $L^6$ fields | `Breakdown.Freq.X` encodes the homogeneous derivative symbol; physical readings recover the velocity |
| $H$ | $L^2((0,1)\times\mathbb R^3)$ of periodic vector fields | `Breakdown.periodNorm`; `Breakdown.Cert.HH` represents the projected Fourier forcing |
| $P$ | Leray projection, at each time | `Breakdown.Cert.solProj`, `Breakdown.Cert.physToHH` |
| $T_S$ | $S^{-1}\partial_\theta+\frac12+\frac12y\cdot\nabla-\Delta$ | Free inverse: `Breakdown.Cert.freeInv`; physical equation: `Breakdown.IsPerturbation` and `Breakdown.IsRightSide` |
| $D_S^\Gamma$ | Periodic invariant graph domain of $T_S$ with $\Delta v\in H$ | `Breakdown.IsPerturbation`; its stored transport field is $T_Sv+\Delta v$ |
| $\Gamma$ | Prescribed orthogonal spatial actions with time shifts | `d.symmetries`, using `Breakdown.Symmetry` |
| $m\in\{1,2\}$ | Period reduction of scalar enstrophy | `d.twist` |
| $\alpha\in K\subset\mathbb R^n$ | Parameter and its box-times-ball domain | `Breakdown.ExtendedCertificateData.params`; the Lean dimension is named $k$ |
| $S(\alpha),S_{\max}$ | Period and upper bound | `d.period`, `d.periodMax` |
| $W^a_\alpha,W^r_\alpha$ | Approximate field and reference field | `d.profile`, `d.model` |
| $F^a_\alpha$ | Chosen residual representative modulo gradients | `Breakdown.ExtendedCertificateData.defect` |
| $\beta^a(\alpha),b_i,b_*$ | Approximate force coefficients, directions and their bound | `d.multiplier`, `d.actuator`, `d.actuatorBound` |
| $\beta$ | Correction force coefficients | The finite vector in the held solution; normalised internally by $\omega$ |
| $\Xi_i,\ell_i(v)$ | Pin field and its gradient pairing | `d.pin`, `Breakdown.pinValue` |
| $\bar\ell(\alpha)$ | Required pin values for the correction | `Breakdown.ExtendedCertificateData.targetGap`; `d.target` stores full-profile pins |
| $w,w_*,w^{\max},\omega$ | Spatial weight, lower and upper bounds, multiplier weight | `d.weightFn`, `d.weight`, `d.weightMax`, `d.multiplierWeight` |
| $\lVert v\rVert_w^2, \lvert u\rvert_w^2$ | Period-integrated and single-slice derivative energies | `Breakdown.weightedEnergy`, `Breakdown.stationaryEnergy` |
| $\lvert\nabla v\rvert_{\rm F}^2$ | Sum of squares of all gradient entries | `Breakdown.matSq`; not the squared operator norm |
| $[F],c_0$ | Finite-row seminorm and its $H$ bound | `Breakdown.ExtendedCertificateData.rows`, `d.rowBound` |
| $c_1,c_2,c_L$ | Reference forcing constant, pin constant, zero-pin inverse constant | `d.coerciveL2`, `d.coercivePin`, `d.coerciveTotal` |
| $c_r,\vartheta$ | Reference error and absorbable loss | `d.gapSize`, `Breakdown.ExtendedCertificateData.transferLoss` |
| $c_3$ | Lower-bound constant for the frozen quadratic form | `d.formBound`; obtained from `d.modelFormBound` and `d.formShift` |
| $\delta(\alpha),\delta_0(\alpha),\delta_{\max}$ | Residual norm, row and uniform bounds | `d.defectBound`, `d.defectRowBound`, `d.defectMax` |
| $\varepsilon,M,\rho=2\varepsilon$ | Half the joint radius, gradient supremum radius, joint radius | `d.sizeBound`, `d.supBound`; the factor two is explicit |
| $c_w$ | $(4\pi\sqrt{w_*})^{-1/2}$ | `Breakdown.supBoundFactor` |
| $J,\rho_j,\rho_*,d_j$ | Box coordinates, their radii, ball radius and nonzero scales | `d.adjointSet`, `d.radius`, `d.stiffRadius`, `d.scale` |
| $V_j$ | Column $j$ of an invertible matrix $V$ | `d.frame`; the update uses its transpose |
| $\psi_{\alpha,j},Y(\alpha)$ | Approximate adjoints and pin coupling | `d.adjoint`, `d.coupling` |
| $a_j,\widetilde a_j,o_j$ | Adjoint linear, quadratic and affine errors | `d.adjointDefect`, `d.adjointQuad`, `d.adjointOffset` |
| $a_*,o_*$ | Joint bound and affine offset on the remaining coordinates | `d.stiffNorm`, `d.stiffOffset` |
| $\mathcal E$ | Complete spatial derivative space used before solving the time equation | `Breakdown.Cert.XX`, built from `Breakdown.Cert.XBar` |
| $A(v,\beta),B(v)$ | Joint weighted norm and essential gradient supremum | `Breakdown.Cert.sizeZ` after normalisation; `Breakdown.Cert.supGrad` |

The pin translation is $\bar\ell_i(\alpha)=d.\mathrm{target}(\alpha)_i-\ell_i(W^a_\alpha)$. Thus a statement about the correction's pin and a statement about the full field's pin express the same constraint only after this subtraction. Likewise, the stored transport field in `IsPerturbation` includes the dilation and time derivative before subtracting the Laplacian. These two translations will be used explicitly.

### 1.3 What the formal endpoints retain

The authors' declaration `Breakdown.extended_certificate_orbit_proved` proves that an extended certificate yields an existential weak periodic profile. Its conclusion does not retain the chosen parameter, the correction, or the full inequality (II.1). The argument inside the library supplies much of that information before the final existential packaging.

Our [Theorem 7.1 wrapper](https://github.com/wcook04/proof-reader/tree/main/lean-wrappers/navier-stokes-theorem71) keeps those witnesses through regularity and states (II.1) for the actual smooth-profile difference. It compiles against the authors' package, with a small patch that adds keeping variants of three existential lemmas, and `Breakdown.theorem71_extended` and `Breakdown.theorem71_cell` use only the standard axioms ([run 44844164476](https://github.com/wcook04/proof-reader/actions/runs/44844164476)). Its declarations are not shown beside this account, which links only the authors' Lean. The mathematical transport proof in §12 is written out independently.
<!-- /passage:sec-1-the-result-and-its-notation -->

## 2. The complete analytic certificate

<!-- passage:sec-2-the-complete-analytic-certificate -->

<a id="2.1"></a>

### 2.1 Equations modulo gradients and symmetry

Let $H$ be the real Hilbert space of period-one vector fields square integrable on one time period and all of space. Write $F\simeq G$ if

$$
\int_{\mathbb R\times\mathbb R^3}(F-G)\cdot\varphi=0
$$

for every compactly supported smooth space-time test field $\varphi$ that is divergence-free in space. This definition also applies to locally integrable fields whose individual terms have no global $H$ norm. It is the appropriate formulation of an equation whose pressure has been removed. [P, (7.1)–(7.4), p.30.]

Here $X$ consists of divergence-free $L^6(\mathbb R^3;\mathbb R^3)$ fields with weak gradient in $L^2$, equipped with the gradient norm. For $S>0$, the correction domain is

$$
D_S=\{v\in L^2_{\rm loc}(\mathbb R;X):v\text{ has period one},\ \Delta v\in H,\ T_Sv\in H\}.
$$

All derivatives in this definition are distributional, and $D_S^\Gamma$ is its invariant subspace. It is the combined expression $S^{-1}\partial_\theta v+\frac12v+\frac12y\cdot\nabla v$ that is square integrable globally. Neither $\partial_\theta v$ nor $y\cdot\nabla v$ is separately assumed to belong to $H$. Lemma II.3 will supply the continuous $X$ representative used throughout the conclusions.

**Lemma II.2.** For $F,G\in H$, equality modulo gradients is equivalent to $PF=PG$.

To prove this, periodicise a compact test field in time. Its pairing with a period-one field over all time becomes a pairing in $H$ over one period. Finite sums of products $a(\theta)\psi(y)$, with $a$ smooth and periodic and $\psi$ smooth, compactly supported and solenoidal, are dense in $H_{\rm div}$. A partition of unity in time realises these products as periodicised compact tests. Hence annihilation of all tests says that $F-G$ is orthogonal to $H_{\rm div}$, which is exactly $P(F-G)=0$. Conversely, $P(F-G)=0$ annihilates every such test because $P$ fixes it. The density input is the solenoidal test-field density used in [P, (7.3), p.30]; its formal counterpart is `Breakdown.Cert.testDenseHolds_proof`.

For an orthogonal map $R$ and a shift $\theta_0$, define the action by

$$
(\rho_{R,\theta_0}F)(\theta,y)=R F(\theta-\theta_0,R^{-1}y).
$$

An invariant field is fixed by every action listed in $\Gamma$. Orthogonal change of variables preserves the $H$ and $X$ norms. The chain rule shows that the action commutes with $T_S$ and with $P$, and that it carries $(u\cdot\nabla)v$ to $(\rho u\cdot\nabla)\rho v$. Its fixed space is closed, being the kernel of the continuous map $\rho-I$; the intersection over any set $\Gamma$ is closed. The set of prescribed symmetries can be empty. Define $m=2$ if some $(R,1/2)$ belongs to $\Gamma$, and $m=1$ otherwise. Only the norm of an invariant slice is then asserted to have period $1/m$.

<a id="2.2"></a>

### 2.2 Approximate fields, residuals and pins

The parameter set $K$ is the compact convex set specified in §2.5. On it, $S$ is continuous and $0<S(\alpha)\le S_{\max}$. The approximate fields are period-one and solenoidal; $W^a$, $\partial_\theta W^a$ and $\nabla W^a$ depend continuously on $(\alpha,\theta,y)\in K\times\mathbb R\times\mathbb R^3$. Their weak second spatial derivatives are locally integrable. For a constant $C_a$ independent of the parameter,

$$
|W^a_\alpha(\theta,y)|\le C_a(1+|y|)^{-1},
\qquad
|\nabla W^a_\alpha(\theta,y)|\le C_a(1+|y|)^{-2}.
\tag{II.3}
$$

They have every prescribed symmetry pointwise. The forcing directions $b_1,\ldots,b_n\in H$ are invariant, with $\sum_i\|b_i\|_H^2\le b_*^2$, where $b_*\ge0$. A continuous coefficient map $\beta^a:K\to\mathbb R^n$ and chosen residuals $F^a_\alpha\in H$ satisfy

$$
T_{S(\alpha)}W^a_\alpha+N(W^a_\alpha)+\sum_i\beta_i^a(\alpha)b_i\simeq F^a_\alpha,
\qquad N(u)=(u\cdot\nabla)u.
\tag{II.4}
$$

No continuity of the chosen residual in the $H$ norm is assumed. Nor need that representative be invariant. Its projection and its solenoidal test pairings will have precisely the properties needed in §8. [P, (7.7)–(7.10), p.31.]

Choose matrix fields $\Xi_i\in H$ and a continuous map $\bar\ell:K\to\mathbb R^n$. Set

$$
\ell_i(v)=\langle\nabla v,\Xi_i\rangle_H,
\qquad
C_\alpha v=(W^a_\alpha\cdot\nabla)v+(v\cdot\nabla)W^a_\alpha.
$$

The correction problem at a fixed parameter is

$$
T_{S(\alpha)}v+C_\alpha v+N(v)+\sum_i\beta_i b_i\simeq-F^a_\alpha,
\qquad \ell(v)=\bar\ell(\alpha).
\tag{II.5}
$$

Adding (II.4) and (II.5) gives the exact nonlinear equation for $W^a_\alpha+v$, with force coefficients $\beta^a(\alpha)+\beta$. There are as many scalar pins as force coefficients. This equality of dimensions is used in the bordered Fredholm argument, and the coefficients will be cancelled exactly in §9. [P, (7.11)–(7.13), pp.31–32.]

<a id="2.3"></a>

### 2.3 Norms and the finite-row measurement

Let $w$ be measurable and bounded, with $0<w_*\le w(y)\le w^{\max}$, and let $\omega>0$. Define

$$
|u|_w^2=\|\Delta u\|_2^2+\int_{\mathbb R^3}w|\nabla u|_{\rm F}^2,
\quad
\|v\|_w^2=\int_0^1|v(\theta)|_w^2\,d\theta,
\quad
A(v,\beta)^2=\|v\|_w^2+\omega^2|\beta|^2.
\tag{II.6}
$$

Take pairwise orthogonal fields $e_1,\ldots,e_N\in H$ with $\|e_a\|_H\le c_0$, where $c_0\ge0$, and put

$$
[F]=\left(\sum_{a=1}^N\langle F,e_a\rangle_H^2\right)^{1/2}.
$$

The row measurement is a seminorm and satisfies $[F]\le c_0\|F\|_H$. Indeed, discard zero rows, divide each remaining row by its norm, apply Bessel's inequality to this orthonormal family, and restore each norm using its upper bound $c_0$. In Lean the normalised row fields and their nonnegative squared weights are stored separately. This is a change of representation of the same finite sum. Both $n=0$ and $N=0$ are permitted. [P, (7.14)–(7.17), p.32.]

<a id="2.4"></a>

### 2.4 Analytic inequalities required of a certificate

The following estimates hold uniformly for every $\alpha\in K$. The reference field $W^r_\alpha$ is $C^1$ and periodic, and $C^r_\alpha v=(W^r_\alpha\cdot\nabla)v+(v\cdot\nabla)W^r_\alpha$. The reference coercivity estimate is

$$
A(v,\beta)\le c_1\|F\|_H+[F]+c_2|\ell(v)|
\quad\text{whenever}\quad
F\simeq T_{S(\alpha)}v+C^r_\alpha v+\sum_i\beta_i b_i,
\tag{II.7}
$$

for every $v\in D_{S(\alpha)}^\Gamma$, every $\beta\in\mathbb R^n$, and every $F\in H$ with the displayed relation. Here $c_1\ge0$ and the paper allows $c_2\in\mathbb R$. The extended formal predicate additionally requires $c_2\ge0$. The norm and row measurement belong to the actual representative $F$. In particular, the quantifier in (II.7) cannot be replaced by a statement solely about a projected right side. [P, (7.18), p.32.]

The reference error obeys $\|(C_\alpha-C^r_\alpha)v\|_H\le c_r\|v\|_w$, with $c_r\ge0$. Define

$$
\vartheta=(c_1+c_0)c_r,
\qquad \vartheta<1,
\qquad c_1+c_0\le(1-\vartheta)c_L,
\qquad c_L>0.
\tag{II.8}
$$

For $c_3\ge0$, the frozen-form inequality is

$$
\mathcal Q_\alpha(\theta;u):=
\|\Delta u\|_2^2+\frac14\|\nabla u\|_2^2
-\langle C_\alpha(\theta)u,\Delta u\rangle
\ge-c_3|u|_w^2.
\tag{II.9}
$$

It is required at every time for each $u\in X$ with $\Delta u\in L^2$ and with every spatial symmetry $(R,0)\in\Gamma$. The formal route first bounds the reference form, then transfers it by a form error; `d.formBound` bounds their sum. [P, (7.19)–(7.22), pp.32–33.]

The residual bounds and the pin budget are

$$
\|F^a_\alpha\|_H\le\delta(\alpha)\le\delta_{\max},
\qquad [F^a_\alpha]\le\delta_0(\alpha),
\qquad
c_1\delta(\alpha)+\delta_0(\alpha)+c_2|\bar\ell(\alpha)|
\le(1-\vartheta)\varepsilon,
\tag{II.10}
$$

with $\varepsilon\ge0$. Choose $M>0$ and set $c_w=(4\pi\sqrt{w_*})^{-1/2}$. The three smallness conditions are

$$
2c_Lc_wM<1,
\tag{II.11 / 7.25}
$$

$$
4\varepsilon^2\left[\frac1{w_*}
+\frac{2S_{\max}}m\left(c_3+\frac{b_*}{\omega}+\frac1{c_L}\right)\right]\le M^2,
\tag{II.12 / 7.26}
$$

$$
4\varepsilon^2\left(\frac1{w_*}+\frac{2S_{\max}c_3}{m}\right)
+\frac{4S_{\max}}m\varepsilon
\left(\delta_{\max}+2c_w\varepsilon M+\frac{2b_*\varepsilon}{\omega}\right)
\le M^2.
\tag{II.13 / 7.27}
$$

Finally, the approximate profile must be separated from zero:

$$
4\varepsilon^2<w_*\|\nabla W^a_\alpha\|_H^2.
\tag{II.14 / 7.28}
$$

The roles of these conditions are different. The residual budget starts the correction inside the joint ball. Condition (II.13) keeps the linear output inside the gradient-supremum ball. Condition (II.12) controls differences in that supremum norm, and (II.11) makes the resulting nonlinear map contract. Condition (II.14) excludes the zero profile after force cancellation.

For Appendix B's prescribed weight, $w_*=39/50$. Its restrictions $c_1\ge50/3$ and $c_0>81.64$, together with (II.8), force $c_L>98.3$. Thus (II.11) requires $M<0.01695$. The first term of (II.13) then gives $\varepsilon\le M\sqrt{w_*}/2<0.0075$. These restrictions are visible at the exact estimates that use them. They do not supply the unreleased certificate or establish that its residual achieves the required accuracy. Section 13.1 gives the arithmetic in detail. [P, (B.22), p.56; concluding paragraph of Appendix B, p.70.]

<a id="2.5"></a>

### 2.5 The parameter enclosure

Let $J\subseteq\{1,\ldots,n\}$, let $\rho_j\ge0$ for $j\in J$, let $\rho_*\ge0$, and require $d_j\ne0$ for every coordinate. Define

$$
K=\left\{\alpha\in\mathbb R^n:
|\alpha_j|\le\rho_j\ (j\in J),
\quad\sum_{j\notin J}d_j^2\alpha_j^2\le\rho_*^2\right\}.
\tag{II.15}
$$

Take an invertible matrix $V$ with columns $V_j$. For $j\in J$ and $\alpha\in K$, choose $\psi_{\alpha,j}\in H$. Also choose a real matrix $Y(\alpha)$. These auxiliary choices need no continuity in the parameter. Write $\langle b,\psi\rangle_H$ for the vector with components $\langle b_i,\psi\rangle_H$. For $a_j,\widetilde a_j\ge0$ require

$$
|\langle N(v),\psi_{\alpha,j}\rangle_H|
\le\widetilde a_j\|v\|_w^2,
\tag{II.16}
$$

and, for every $F\in H$ equivalent modulo gradients to $T_{S(\alpha)}v+C_\alpha v$,

$$
|\langle F,\psi_{\alpha,j}\rangle_H-(Y(\alpha)\ell(v))_j|
\le a_j\|v\|_w.
\tag{II.17}
$$

Both statements are quantified over $v\in D_{S(\alpha)}^\Gamma$. The affine offset and inclusion conditions are

$$
|V_j\cdot\beta^a(\alpha)-\langle F^a_\alpha,\psi_{\alpha,j}\rangle_H
 -(Y(\alpha)\bar\ell(\alpha))_j-d_j\alpha_j|\le o_j,
\tag{II.18}
$$

$$
\widetilde a_j(2\varepsilon)^2
+2\varepsilon\sqrt{a_j^2+
\frac{|\langle b,\psi_{\alpha,j}\rangle_H-V_j|^2}{\omega^2}}
+o_j\le |d_j|\rho_j.
\tag{II.19}
$$

For the complementary coordinates, choose $a_*\ge0$ and $o_*\in\mathbb R$ such that

$$
\sum_{j\notin J}(V_j\cdot\beta)^2\le a_*^2|\beta|^2
\quad(\beta\in\mathbb R^n),
\qquad
\left(\sum_{j\notin J}(V_j\cdot\beta^a(\alpha)-d_j\alpha_j)^2\right)^{1/2}\le o_*,
\tag{II.20}
$$

$$
\frac{2\varepsilon a_*}{\omega}+o_*\le\rho_*.
\tag{II.21}
$$

The offsets may initially be declared real; their absolute-value bounds and the nonemptiness of $K$ force them to be nonnegative whenever the hypotheses are satisfied. Zero radii and an empty-interior parameter set are allowed. These are the paper's conditions (7.29)–(7.37), pp.33–34.

<a id="2.6"></a>

### 2.6 The two normalisations used in Lean

The multiplier weight can be normalised to one without changing the physical force or the parameter update. Make the replacements

$$
\widetilde b_i=b_i/\omega,
\quad \widetilde\beta=\omega\beta,
\quad \widetilde\beta^a=\omega\beta^a,
\quad \widetilde b_*=b_*/\omega,
\quad \widetilde V=V/\omega,
\quad \widetilde a_*=a_*/\omega.
$$

Then $\sum_i\widetilde\beta_i\widetilde b_i=\sum_i\beta_i b_i$ and $|\widetilde\beta|^2=\omega^2|\beta|^2$. Moreover $\widetilde V^{\mathsf T}(\widetilde\beta^a+\widetilde\beta)=V^{\mathsf T}(\beta^a+\beta)$, so the raw parameter map is identical. The actuator-pairing error scales by $1/\omega$; the adjoint fields, their linear and quadratic defect constants, and the affine offsets stay unchanged. `Breakdown.Cert.extendedUnitWeightHolds` proves this transformation. We retain $\omega$ in the mathematics so the final multiplier term remains visible.

The second normalisation replaces the reference field by the approximate field after absorbing $\vartheta$. Divide $c_1$, $c_2$ and $c_0$ by $1-\vartheta$, divide the row weights by $(1-\vartheta)^2$, set the reference gap to zero, and use the transferred frozen-form bound. This is `Breakdown.Cert.extendedAtProfileHolds`. Section 5 proves the absorption directly. Neither normalisation selects a different approximate field, parameter, period or pin target.
<!-- /passage:sec-2-the-complete-analytic-certificate -->

## 3. The free time-periodic equation

<!-- passage:sec-3-the-free-time-periodic-equation -->

<a id="3.1"></a>

### 3.1 Lemma II.3: the energy identity at graph-domain regularity

**Lemma II.3.** If $v\in D_S$, then $T_Sv\in H_{\rm div}$, and $v$ has a continuous, period-one representative with values in $X$. Its squared gradient norm $E(\theta)=\|\nabla v(\theta)\|_2^2$ is locally absolutely continuous and satisfies

$$
\frac{E'(\theta)}{2S}+\|\Delta v(\theta)\|_2^2+\frac14E(\theta)
=-\langle T_Sv(\theta),\Delta v(\theta)\rangle
\quad\text{for almost every }\theta.
\tag{II.22}
$$

Consequently,

$$
\|\Delta v\|_H^2+\frac14\|\nabla v\|_H^2
=-\langle T_Sv,\Delta v\rangle_H
\le\|T_Sv\|_H^2.
\tag{II.23}
$$

This is Lemma 7.4, including the representative needed later to interpret a bound at every time. We prove it without assuming global square integrability of the time derivative or of the dilation derivative separately. [P, pp.36–37.]

Put $f=T_Sv$. The distributional identity

$$
\operatorname{div}((y\cdot\nabla)v)
=(y\cdot\nabla)\operatorname{div}v+\operatorname{div}v
$$

shows that $f$ is solenoidal. To obtain the time regularity, change to physical variables:

$$
t=1-e^{-S\theta},\qquad x=e^{-S\theta/2}y,
\qquad u(t,x)=e^{S\theta/2}v(\theta,y).
\tag{II.24}
$$

The distributional chain rule gives

$$
\partial_tu-\Delta u=e^{3S\theta/2}f(\theta,y),
\qquad \Delta u=e^{3S\theta/2}\Delta v(\theta,y).
$$

On each compact interval below $t=1$, the change of variables and its factors are bounded. Hence $u\in L^2_tX$ and $\partial_tu,\Delta u\in L^2_{t,x}$ on that interval. Plancherel gives $\|\nabla^2u\|_2=\|\Delta u\|_2$. Thus $g=\nabla u$ belongs to $L^2_tH^1_x$ and its time derivative to $L^2_tH^{-1}_x$.

The Hilbert-triple energy lemma says that such a $g$ has a continuous $L^2_x$ representative and

$$
\|g(b)\|_2^2-\|g(a)\|_2^2
=2\int_a^b\langle\partial_tg,g\rangle_{H^{-1},H^1}\,dt.
$$

For completeness, regularise $g$ in time on an interior subinterval and differentiate its squared norm there. The two $L^2$ assumptions allow the dual pairings to pass to the limit by Cauchy–Schwarz. Pairings with a dense subset of $H^1$ first provide a weakly continuous $L^2$ representative. The integrated identity makes its norm continuous; weak convergence together with convergence of norms in a Hilbert space gives strong continuity. Exhausting the time interval gives the assertion, including its endpoints whenever they are interior to a larger interval. In the present application the dual pairing is $-\langle\partial_tu,\Delta u\rangle$, so

$$
\|\nabla u(b)\|_2^2-\|\nabla u(a)\|_2^2
=-2\int_a^b\langle\partial_tu,\Delta u\rangle\,dt.
$$

The gradients of fields in $X$ form a closed subspace of $L^2$, so this continuous representative is the gradient of a continuous $X$ curve. Undo the scaling in (II.24). The gradient norm scales by

$$
\|\nabla u(t)\|_2^2=e^{S\theta/2}\|\nabla v(\theta)\|_2^2.
$$

Differentiation of this identity and substitution of the physical energy identity yield (II.22). In particular, the coefficient $1/4$ comes from the dilation of the gradient norm. Periodicity holds for every time because the translated continuous curves agree almost everywhere. Integrating over a period eliminates $E'$. Cauchy–Schwarz first gives $\|\Delta v\|_H\le\|f\|_H$ by discarding the nonnegative gradient term, then gives (II.23) on substitution. It also gives $\|\nabla v\|_H\le2\|f\|_H$.

The formal construction proves the graph equation, a continuous scalar energy representative, and its physical interpretation in separate declarations. The relevant steps are `Breakdown.Cert.freeInvHolds_of`, `Breakdown.Cert.freeEnergyLocalHolds_of`, `Breakdown.Cert.freePerturbationHolds_of` and `Breakdown.Cert.readingEnergyHolds_of`. The hypotheses of these modular results are supplied in `Breakdown.extended_certificate_orbit_proved`.

<a id="3.2"></a>

### 3.2 Proposition II.4: construction of the free inverse

**Proposition II.4.** The map $T_S:D_S\to H_{\rm div}$ is a bijection. It restricts to a bijection $D_S^\Gamma\to H_{\rm div}^\Gamma$.

Injectivity follows at once from (II.23): if $T_Sv=0$, then $\nabla v=0$. The $L^6$ realisation of $X$ excludes a nonzero constant field, hence $v=0$. For surjectivity, begin with a dense collection of right sides $f(\theta,y)=a(\theta)\psi(y)$, where $a$ is smooth and period-one and $\psi$ is smooth, compactly supported and solenoidal. [P, Proposition 7.5, pp.37–38.]

For $r\ge0$ define the heat-dilation evolution

$$
U_r(y)=e^{-r/2}\bigl(e^{(1-e^{-r})\Delta}\psi\bigr)(e^{-r/2}y).
$$

Differentiating the heat flow and the scaling gives

$$
\partial_rU_r+\frac12U_r+\frac12(y\cdot\nabla)U_r-\Delta U_r=0,
\qquad U_0=\psi.
$$

Heat flow contracts the gradient and Laplacian $L^2$ norms, and dilation yields

$$
\|\nabla U_r\|_2\le e^{-r/4}\|\nabla\psi\|_2,
\qquad
\|\Delta U_r\|_2\le e^{-3r/4}\|\Delta\psi\|_2.
$$

Consequently the integral

$$
v(\theta)=\int_0^\infty a(\theta-r/S)U_r\,dr
\tag{II.25}
$$

converges in both derivative norms. The smooth input also permits differentiation under the integral. Since $S^{-1}\partial_\theta a(\theta-r/S)=-\partial_r a(\theta-r/S)$, integration by parts gives a boundary contribution $a(\theta)\psi$ at $r=0$. The exponential estimates remove the boundary at infinity. The remaining integral is $-\frac12v-\frac12y\cdot\nabla v+\Delta v$. Thus $T_Sv=f$.

Now approximate an arbitrary $f\in H_{\rm div}$ by finite sums of these products. For their inverse images $v_j$, (II.23) applied to differences makes $\nabla v_j$ and $\Delta v_j$ Cauchy in $H$. Their limits give a period-one $v\in L^2_\theta X$ with $\Delta v\in H$. Distributional differentiation commutes with this convergence, so $T_Sv=f$. Hence $v\in D_S$, proving surjectivity. If $f$ is invariant, applying any prescribed symmetry to $v$ gives a second solution of the same equation. Injectivity makes it equal to $v$, proving the invariant assertion.

The Fourier implementation constructs the gradient inverse before assembling the graph-domain inverse. `Breakdown.Cert.exists_gradInvSpec` supplies the integral operator, `Breakdown.Cert.freeInvHolds_of` supplies the graph inverse, and `Breakdown.Cert.freeEquivariantHolds_of` proves preservation of symmetry. The proof above and the formal proof use the same contracting heat-dilation evolution, with different representations of its domain.

<a id="3.3"></a>

### 3.3 Proposition II.5: weak forcing gives strong local compactness

**Proposition II.5.** Suppose $S_j\to S>0$ and $f_j\rightharpoonup f$ weakly in $H_{\rm div}$. Set $v_j=T_{S_j}^{-1}f_j$ and $v=T_S^{-1}f$. Then $\nabla v_j\rightharpoonup\nabla v$ and $\Delta v_j\rightharpoonup\Delta v$ in $H$, while $v_j\to v$ strongly in $L^2((0,1)\times B_R)$ for every finite $R$.

The sequence $(f_j)$ is bounded. The free energy estimate therefore bounds both derivative norms of $v_j$; the Sobolev inequality bounds $v_j$ in $L^2_\theta L^6_y$. On a fixed ball,

$$
\partial_\theta v_j
=S_j\left(f_j+\Delta v_j-\frac12v_j-\frac12y\cdot\nabla v_j\right)
$$

is bounded in local space-time $L^2$. The factor $y$ is bounded there. Thus $v_j$ is bounded in $H^1$ on each fixed space-time cylinder. The Rellich compactness theorem used here is the compact inclusion $H^1(\Omega)\hookrightarrow L^2(\Omega)$ on bounded Lipschitz domains $\Omega\subset\mathbb R^4$. Apply it on an exhaustion and take a diagonal subsequence. This gives strong local $L^2$ convergence and weak convergence of the two spatial derivative arrays.

The limiting distributional equation is $T_S\widetilde v=f$. The limit lies in $D_S$, and injectivity from Proposition II.4 identifies it with $v$. Every subsequence has a further subsequence with this same limit, so the stated convergence holds for the entire sequence. This proves the last assertion of Proposition 7.5. The formal route separates period continuity from local compactness in `Breakdown.Cert.periodContinuityHolds_of` and `Breakdown.Cert.localCompactnessHolds_of`.
<!-- /passage:sec-3-the-free-time-periodic-equation -->

## 4. The two convection estimates

<!-- passage:sec-4-the-two-convection-estimates -->

<a id="4.1"></a>

### 4.1 Lemma II.6: the exact product constant

**Lemma II.6.** If $u\in X$ and $\Delta u\in L^2$, then

$$
\|u\|_\infty^2\le
\frac{\|\Delta u\|_2^2+w_*\|\nabla u\|_2^2}{4\pi\sqrt{w_*}}
\le c_w^2|u|_w^2.
\tag{II.26}
$$

This is Lemma 7.6's slice estimate. The following Fourier proof computes its constant directly. Use the unitary Fourier convention with phase $e^{-iy\cdot\xi}$. For a smooth frequency cutoff away from zero and infinity, Fourier inversion and Cauchy–Schwarz give

$$
|u(y)|^2\le(2\pi)^{-3}
\left(\int(|\xi|^4+w_*|\xi|^2)|\widehat u(\xi)|^2\,d\xi\right)
\left(\int\frac{d\xi}{|\xi|^4+w_*|\xi|^2}\right).
$$

For vector fields, apply the scalar estimate to the inner product with an arbitrary unit vector and take the supremum over that vector. The second integral is

$$
4\pi\int_0^\infty\frac{dr}{r^2+w_*}
=\frac{2\pi^2}{\sqrt{w_*}}.
$$

Plancherel now gives (II.26). The extension to the homogeneous space deserves attention: $u$ need not belong to $L^2$. Its homogeneous Fourier symbol $g=|\xi|\widehat u$ lies in $L^2$, and the Laplacian hypothesis gives $|\xi|g\in L^2$. Cauchy–Schwarz with the same integrable weight shows that $g/|\xi|\in L^1$. Smooth spectral cutoffs converge in the derivative graph norm and, by the displayed estimate, uniformly after inverse transform. Sobolev also makes their velocities converge in $L^6$. The uniform limit is therefore the canonical $L^6$ representative of $u$. No constant-field ambiguity survives in that realisation.

At almost every time apply (II.26) and use $|(a\cdot\nabla)b|\le |a|\,|\nabla b|_{\rm F}$. Integrating gives the bilinear estimate

$$
\|(a\cdot\nabla)b\|_H
\le c_w\|a\|_w\operatorname*{ess\,sup}_\theta\|\nabla b(\theta)\|_2.
\tag{II.27}
$$

For $a=b=v\in D_S$, the essential supremum is the ordinary supremum of its continuous $X$ representative. In particular $N(v)\in H$ and $\|N(v)\|_H\le c_w\|v\|_w\sup_\theta\|\nabla v(\theta)\|_2$. The same estimate applies to the larger spatial derivative space used in §7 whenever its essential supremum is finite.

The paper obtains this constant from Xie's inequality. The formal proof uses its Fourier graph, through `Breakdown.Cert.sliceSupBoundHolds_of` and `Breakdown.Cert.productBoundHolds_of`. The proof just given is our derivation of the same analytic inequality; it is not an additional Lean proof. At $w_*=39/50$, the constant is approximately $0.300172856$. [P, (7.48)–(7.49), pp.38–39.]

<a id="4.2"></a>

### 4.2 Lemma II.7: bounded and compact convection

**Lemma II.7.** The linearised convection map satisfies $\|C_\alpha v\|_H\le C\|\nabla v\|_H$, with $C$ uniform in $\alpha$. It preserves the prescribed invariance, and $C_\alpha T_{S(\alpha)}^{-1}:H_{\rm div}\to H$ is compact.

The coefficient bounds (II.3) imply

$$
|C_\alpha v|\le C_a\left((1+|y|)^{-1}|\nabla v|
+(1+|y|)^{-2}|v|\right).
$$

Hölder and the homogeneous Sobolev inequality give the tail estimate

$$
\|C_\alpha v(\theta)\|_{L^2(B_R^c)}
\le C_a\left((1+R)^{-1}
+C_S\|(1+|y|)^{-2}\|_{L^3(B_R^c)}\right)\|\nabla v(\theta)\|_2.
\tag{II.28}
$$

The coefficient in parentheses is finite at $R=0$ and tends to zero as $R\to\infty$. Integrating its square in time proves boundedness and uniform control of tails. The covariance of the bilinear expression proves invariance.

For compactness, take $f_j\rightharpoonup0$ and set $v_j=T_S^{-1}f_j$. Proposition II.5 gives strong local convergence of $v_j$ to zero, while (II.23) bounds its derivatives. Choose a smooth spatial cutoff $\chi$ supported in $B_{2R}$ and equal to one on $B_R$. Integration by parts gives

$$
\int_0^1\!\int\chi^2|\nabla v_j|^2
=-\int_0^1\!\int\chi^2v_j\cdot\Delta v_j
-2\int_0^1\!\int\chi\,v_j\cdot((\nabla\chi\cdot\nabla)v_j).
$$

Both right-hand terms tend to zero: the local $L^2$ norm of $v_j$ tends to zero, and the relevant derivative norms remain bounded. Thus gradients also converge strongly on bounded cylinders. The bounded local coefficients imply $C_\alpha v_j\to0$ locally in $L^2$. First make the tail uniformly small by choosing $R$ in (II.28), then make the bounded-cylinder norm small by choosing $j$. This proves convergence in $H$, and hence compactness. This is Lemma 7.7, pp.39–40. The corresponding formal steps are `Breakdown.Cert.extendedConvectionHolds_of` and `Breakdown.Cert.extendedConvectionCompactHolds_of`.
<!-- /passage:sec-4-the-two-convection-estimates -->

## 5. Why the bordered inverse exists

<!-- passage:sec-5-why-the-bordered-inverse-exists -->

<a id="5.1"></a>

### 5.1 Lemma II.8: transfer the reference estimate

**Lemma II.8.** If $F\simeq T_Sv+C_\alpha v+\sum_i\beta_i b_i$, then

$$
(1-\vartheta)A(v,\beta)
\le c_1\|F\|_H+[F]+c_2|\ell(v)|.
\tag{II.29}
$$

Let $G=(C_\alpha-C^r_\alpha)v$. The reference equation has right side $F-G$, so (II.7), the two triangle inequalities and $[G]\le c_0\|G\|_H$ give

$$
A(v,\beta)\le c_1\|F\|_H+[F]+c_2|\ell(v)|
+(c_1+c_0)c_r\|v\|_w.
$$

Since $\|v\|_w\le A(v,\beta)$, subtract $\vartheta A(v,\beta)$ and use $\vartheta<1$. This proves (II.29), which is (7.52) on p.39. When the pins vanish, (II.8) gives

$$
A(v,\beta)\le c_L\|F\|_H.
\tag{II.30}
$$

This proof allows the paper's real $c_2$: the pin term is kept unchanged, and it is zero in (II.30). `Breakdown.Cert.extendedAtProfileHolds` implements the normalised transfer, while `Breakdown.Cert.extendedCoerciveBorderedHolds_of` applies the estimate to the physically interpreted graph solution under the formal certificate's hypotheses.

<a id="5.2"></a>

### 5.2 Proposition II.9: bijectivity of the bordered map

**Proposition II.9.** For fixed $\alpha$ and $S=S(\alpha)$, the map

$$
\mathcal L_\alpha(v,\beta)=
\left(T_Sv+PC_\alpha v+\sum_i\beta_iPb_i,\ \ell(v)\right)
\tag{II.31}
$$

is a bijection from $D_S^\Gamma\times\mathbb R^n$ to $H_{\rm div}^\Gamma\times\mathbb R^n$. Equivalently, every $F\in H$ with $PF\in H_{\rm div}^\Gamma$, and every prescribed pin vector, determine exactly one pair solving the linear equation modulo gradients with those pins.

The map takes values in the indicated invariant space by Propositions II.4 and Lemma II.7. If its output is zero, (II.29) with zero forcing and zero pins implies $A(v,\beta)=0$. Positivity of $w_*$ and $\omega$ gives $\beta=0$ and $\nabla v=0$, hence $v=0$. This proves injectivity.

Existence requires another argument. Use $f=T_Sv$ as the velocity coordinate. On the Hilbert space $\mathcal H_0=H_{\rm div}^\Gamma\times\mathbb R^n$, the transformed map is $I+Q$, where

$$
Q(f,\beta)=
\left(PC_\alpha T_S^{-1}f+\sum_i\beta_iPb_i,
\quad\ell(T_S^{-1}f)-\beta\right).
\tag{II.32}
$$

The convection block is compact by Lemma II.7. The remaining blocks are bounded and finite rank; for instance

$$
|\ell_i(T_S^{-1}f)|\le\|\Xi_i\|_H\|\nabla T_S^{-1}f\|_H
\le2\|\Xi_i\|_H\|f\|_H.
$$

Therefore $Q$ is compact. The finite-dimensional negative identity in its second component is legitimate because the pin space and multiplier space have the same dimension. The resulting identity plus compact operator is generally not self-adjoint.

Here is the precise Fredholm argument. Let $A_0=I+Q$ be injective on a Hilbert space. It is bounded below: otherwise there are unit vectors $x_j$ with $A_0x_j\to0$. Compactness gives a subsequence for which $Qx_j$ converges; then $x_j=A_0x_j-Qx_j$ converges to a unit vector in the kernel, a contradiction. Every power $A_0^r$ therefore has closed range. If $A_0$ were not onto, these ranges would descend strictly: equality of consecutive ranges, cancelled through the injective $A_0^r$, would imply surjectivity. Choose a unit vector $e_r\in A_0^{r-1}\mathcal H_0\cap(A_0^r\mathcal H_0)^\perp$. For $j>r$, the vectors $e_j$, $A_0e_j$ and $A_0e_r$ belong to $A_0^r\mathcal H_0$, so $Qe_j-Qe_r=A_0e_j-e_j-A_0e_r+e_r$ has component one along $e_r$. Thus $\|Qe_j-Qe_r\|\ge1$, contradicting compactness. Hence $A_0$ is onto.

Applying this argument to (II.32) proves Proposition II.9, the paper's Proposition 7.8. The formal compact-operator step is `Breakdown.Cert.Internal.BorderedInvertible.exists_inverse_of_compact_bordered`; `Breakdown.Cert.extendedBorderedInvertibleHolds_of` supplies its hypotheses for this problem. [P, (7.53)–(7.54), p.40.]
<!-- /passage:sec-5-why-the-bordered-inverse-exists -->

## 6. The frozen form controls the worst time

<!-- passage:sec-6-the-frozen-form-controls-the-worst-time -->

<a id="6.1"></a>

### 6.1 Proposition II.10: the supremum estimate

**Proposition II.10.** Suppose $v\in D_{S(\alpha)}^\Gamma$ and $F\simeq T_{S(\alpha)}v+C_\alpha v+\sum_i\beta_i b_i$. Then

$$
\sup_\theta\|\nabla v(\theta)\|_2^2
\le\left(\frac1{w_*}+\frac{2S(\alpha)c_3}{m}\right)\|v\|_w^2
+\frac{2S(\alpha)}m(\|F\|_H+b_*|\beta|)\|v\|_w.
\tag{II.33}
$$

This is the paper's Proposition 7.9. Its input is a global $L^2$ right-side bound. The proof does not require a pointwise-in-time bound on that forcing. [P, (7.55)–(7.56), pp.40–41.]

Let $E(\theta)=\|\nabla v(\theta)\|_2^2$. The Leray projection drops out when paired with the solenoidal field $\Delta v(\theta)$. Substitution into (II.22) gives

$$
\frac{E'}{2S}
=-\langle F,\Delta v\rangle
+\left\langle\sum_i\beta_i b_i,\Delta v\right\rangle
-\mathcal Q_\alpha(\theta;v).
$$

For almost every time the slice is admissible in (II.9); its pure spatial symmetries extend to every time in $X$ by continuity. Therefore

$$
\frac{E'}{2S}\le\Lambda(\theta):=
\left(\|F(\theta)\|_2+\left\|\sum_i\beta_i b_i(\theta)\right\|_2\right)
\|\Delta v(\theta)\|_2+c_3|v(\theta)|_w^2.
$$

This is a nonnegative, period-one integrable function. Cauchy–Schwarz in the finite coefficient vector and then in time gives

$$
\int_0^1\Lambda\le(\|F\|_H+b_*|\beta|)\|v\|_w+c_3\|v\|_w^2.
\tag{II.34}
$$

Choose a minimum point $\theta_*$ of the continuous periodic function $E$. Its minimum is at most its mean, so $E(\theta_*)\le\|v\|_w^2/w_*$. The scalar function $E$ has period $1/m$: a half-period spatial isometry preserves the $X$ norm. For $\theta\in[\theta_*,\theta_*+1/m]$, integrate $E'\le2S\Lambda$ on each of the intervals

$$
[\theta_*+j/m,\ \theta+j/m],\qquad j=0,\ldots,m-1.
$$

Their interiors are disjoint and their union lies inside one full period. Every increment on the left equals $E(\theta)-E(\theta_*)$. Nonnegativity of $\Lambda$ consequently gives

$$
m(E(\theta)-E(\theta_*))\le2S\int_0^1\Lambda.
$$

Every value of $E$ is attained in this shorter interval. Combining this estimate with (II.34) proves (II.33). Only the scalar energy was given a shorter period; the chosen forcing representative and $\Lambda$ may have period one alone. This distinction explains the factor $1/m$ without adding a symmetry assumption.

The formal bridge from the reference frozen form is `Breakdown.Cert.extendedFrozenBridgeHolds_of`. The resulting supremum estimate is `Breakdown.Cert.extendedSupBoundHolds_of`. Its `twist` is one or two; the nineteenfold spatial rotation in the proposed certificate is not the value of $m$.
<!-- /passage:sec-6-the-frozen-form-controls-the-worst-time -->

## 7. Solve the nonlinear equation at a fixed parameter

<!-- passage:sec-7-solve-the-nonlinear-equation-at-a-fixed-parameter -->

<a id="7.1"></a>

### 7.1 Lemma II.11: a complete space for the iteration

**Lemma II.11.** The iteration can be carried out on a complete held set in the spatial derivative space

$$
\mathcal E=\{v\in L^2(\mathbb R/\mathbb Z;X):\Delta v\in H\},
\qquad
\|v\|_{\mathcal E}^2=\|\nabla v\|_H^2+\|\Delta v\|_H^2.
$$

This space imposes no time-domain condition. It is complete: a Cauchy sequence gives a limit in $L^2_\theta X$ and a separate $H$ limit of its Laplacians; passage against compact tests identifies the latter with the distributional Laplacian of the former. The bounds on $w$ make $\|\cdot\|_w$ an equivalent Hilbert norm. Symmetry is a closed constraint, since each action is bounded in the unweighted norm and hence in the equivalent weighted norm.

Put $\rho=2\varepsilon$ and

$$
B(v)=\operatorname*{ess\,sup}_\theta\|\nabla v(\theta)\|_2,
\qquad
\mathcal B=\{(v,\beta)\in\mathcal E^\Gamma\times\mathbb R^n:
A(v,\beta)\le\rho,\ B(v)\le M\}.
\tag{II.35}
$$

The set contains zero and is closed in the ambient Hilbert space. The weighted norm is continuous. For the supremum constraint, convergence in $\mathcal E$ implies convergence of velocities in $L^2_\theta X$. A subsequence converges in $X$ at almost every time, so the slice bound passes to the limit. This proves closedness of every sublevel set of $B$, and hence its lower semicontinuity in the ambient topology.

For $z=(v,\beta)$ and $z'=(u,\gamma)$ in $\mathcal B$, define

$$
d(z,z')=\max\left\{A(v-u,\beta-\gamma),
\frac{\rho}{M}B(v-u)\right\}.
\tag{II.36}
$$

The difference supremum is finite, at most $2M$. Both terms satisfy the triangle inequality, and the first controls the ambient norm by the positive constant $\min\{1,\sqrt{w_*},\omega\}$. Thus $d$ separates points. If a sequence is $d$-Cauchy, it has an ambient limit in the closed set $\mathcal B$. Fixing one sufficiently late term and passing the other index to the limit, continuity of $A$ and lower semicontinuity of $B$ show convergence in $d$ as well. This proves completeness.

This argument remains valid when $\rho=0$. The held set is then the singleton zero pair; no division by $\rho$ has occurred. The pins and the condition $T_Sv\in H$ are imposed by each linear solve, and will therefore hold at its fixed point. Completeness of $D_S$ in the weighted norm would not justify this iteration, because that norm omits $T_Sv$.

The formal ambient space `Breakdown.Cert.XX` is $L^2$ in period-one time over a closed spatial Fourier graph. In its Fourier convention the graph relation is $h(\xi)=2\pi|\xi|g(\xi)$, where $g$ represents the homogeneous first derivative and $h$ the negative Laplacian. `Breakdown.Cert.mem_halfOrderGraph_iff` proves that taking the graph closure introduced no additional pairs. `Breakdown.Cert.extendedHeldMetricHolds_of` provides the closed-set, ambient-norm and limit properties used in the contraction theorem. This is the formal counterpart of the completeness argument above.

<a id="7.2"></a>

### 7.2 Proposition II.12: the nonlinear step preserves both bounds

**Proposition II.12.** Fix $\alpha\in K$. Given $z=(u,\gamma)\in\mathcal B$, let $\mathcal F_\alpha(z)=(v,\beta)$ be the unique bordered solution

$$
T_{S(\alpha)}v+C_\alpha v+\sum_i\beta_i b_i
\simeq-F^a_\alpha-N(u),
\qquad\ell(v)=\bar\ell(\alpha).
\tag{II.37}
$$

Then $\mathcal F_\alpha$ maps $\mathcal B$ into itself. The input coefficient $\gamma$ is not used by the map; including it in the state keeps the output multiplier inside the same joint norm as the velocity.

The residual relation implies $PF^a_\alpha\in H_{\rm div}^\Gamma$: applying a symmetry to (II.4) leaves its left side unchanged modulo gradients, so the projected residual is fixed by that symmetry. Also $N(u)$ is invariant. Hence Proposition II.9 gives the required solve. Its output already belongs to $D_{S(\alpha)}^\Gamma$.

The bilinear estimate gives $\|N(u)\|_H\le c_w\rho M$. Apply (II.29) to (II.37), use the residual and pin budget (II.10), and bound the extra row contribution by $c_0\|N(u)\|_H$. The result is

$$
A(v,\beta)\le\varepsilon+c_L\|N(u)\|_H
\le\varepsilon+c_Lc_w\rho M
=\varepsilon(1+2c_Lc_wM)\le\rho.
\tag{II.38}
$$

For the second bound, insert $\|v\|_w\le\rho$, $|\beta|\le\rho/\omega$, $S(\alpha)\le S_{\max}$ and $\|F^a_\alpha+N(u)\|_H\le\delta_{\max}+c_w\rho M$ into (II.33). This gives

$$
\sup_\theta\|\nabla v(\theta)\|_2^2
\le\left(\frac1{w_*}+\frac{2S_{\max}c_3}{m}\right)\rho^2
+\frac{2S_{\max}}m\left(\delta_{\max}+c_w\rho M+\frac{b_*\rho}{\omega}\right)\rho
\le M^2.
\tag{II.39}
$$

The last inequality is exactly (7.27), after substituting $\rho=2\varepsilon$. The continuous $X$ representative supplied by the free solve makes this a bound at every time. This proves the self-map property. Its formal counterpart is `Breakdown.Cert.extendedHeldMapsToHolds_of`.

<a id="7.3"></a>

### 7.3 Proposition II.13: contraction and a unique held solution

**Proposition II.13.** For each $\alpha\in K$, the map $\mathcal F_\alpha$ has a unique fixed point in $\mathcal B$. Its contraction constant is

$$
\kappa_{\rm ctr}=2c_Lc_wM<1.
\tag{II.40}
$$

Let $z=(u,\gamma)$ and $z'=(u',\gamma')$ be held inputs. The exact quadratic difference is

$$
N(u)-N(u')=((u-u')\cdot\nabla)u
+(u'\cdot\nabla)(u-u').
$$

Using (II.27) on each term gives

$$
\|N(u)-N(u')\|_H
\le c_w\bigl(M\|u-u'\|_w+\rho B(u-u')\bigr)
\le2c_wM\,d(z,z').
\tag{II.41}
$$

The last step multiplies $(\rho/M)B(u-u')\le d(z,z')$ by $M>0$. It never divides by $\rho$, so it remains valid at zero radius.

Write $(h,\eta)=\mathcal F_\alpha z-\mathcal F_\alpha z'$ and $f=\|N(u)-N(u')\|_H$. The output difference has zero pins. By (II.30), $A(h,\eta)\le c_Lf$. Apply (II.33) to that difference, and use $\|h\|_w\le c_Lf$ and $|\eta|\le c_Lf/\omega$. We obtain

$$
B(h)^2\le c_L^2f^2
\left[\frac1{w_*}+\frac{2S_{\max}}m
\left(c_3+\frac{b_*}{\omega}+\frac1{c_L}\right)\right].
\tag{II.42}
$$

The term $1/c_L$ comes from the factor $f\|h\|_w$ in the forcing contribution; it must be retained. Condition (7.26) says that the bracket in (II.42), multiplied by $\rho^2$, is at most $M^2$. Taking nonnegative square roots yields

$$
\frac{\rho}{M}B(h)\le c_Lf.
$$

The two components of the output metric therefore obey the same inverse estimate. Combining them with (II.41) proves

$$
d(\mathcal F_\alpha z,\mathcal F_\alpha z')
\le c_Lf\le\kappa_{\rm ctr}d(z,z').
\tag{II.43}
$$

This calculation explains the use of (7.26) in Lean's proof. The paper's Schauder proof does not need it. At the Appendix B value $w_*=39/50$ and its forced $c_L>98.3$, the same calculation imposes the small upper bound on $M$ stated in §2.4.

To finish the existence proof, set $z_0=0$ and $z_{r+1}=\mathcal F_\alpha z_r$. Proposition II.12 keeps every iterate in $\mathcal B$. If $D_0=d(z_0,z_1)$, induction and summation give

$$
d(z_r,z_j)\le D_0\sum_{i=r}^{j-1}\kappa_{\rm ctr}^i
\le\frac{D_0\kappa_{\rm ctr}^r}{1-\kappa_{\rm ctr}}
\qquad(j>r).
$$

Completeness from Lemma II.11 supplies a limit $z_*$. The contraction estimate makes $\mathcal F_\alpha z_r$ converge to $\mathcal F_\alpha z_*$; the shifted sequence also converges to $z_*$, proving the fixed-point identity. If $z_*'$ were another fixed point, (II.43) would give $d(z_*,z_*')\le\kappa_{\rm ctr}d(z_*,z_*')$, forcing equality of the points. For $\varepsilon=0$, the self-map property directly forces the singleton zero pair to solve the equation. It does not force the arbitrary raw residual representative to vanish; a gradient representative can remain.

The fixed point solves (II.5), belongs to $D_{S(\alpha)}^\Gamma$, has the prescribed pins, and satisfies both bounds. Uniqueness is within this held class at a fixed parameter. No assertion of uniqueness of all periodic solutions, or of the parameter eventually selected, is made. The formal steps are `Breakdown.Cert.extendedHeldContractsHolds_of`, `Breakdown.Cert.contractionFixedPointHolds_proof` and `Breakdown.Cert.extendedHeldExistsUniqueHolds_of`.
<!-- /passage:sec-7-solve-the-nonlinear-equation-at-a-fixed-parameter -->

## 8. Continuity of the remaining finite-dimensional problem

<!-- passage:sec-8-continuity-of-the-remaining-finite-dimensional-problem -->

<a id="8.1"></a>

### 8.1 Proposition II.14: continuity of the multiplier

**Proposition II.14.** Let $(v_\alpha,\beta_\alpha)$ be the unique held solution at $\alpha$. The map $\alpha\mapsto\beta_\alpha$ is continuous on $K$.

A parameter-dependent contraction theorem requiring norm continuity of the raw residual would add a hypothesis absent from the certificate. Instead, we use compactness and uniqueness. First, for every compactly supported smooth solenoidal test $\varphi$, the residual relation gives continuity of

$$
\alpha\longmapsto\int_{\mathbb R\times\mathbb R^3}F^a_\alpha\cdot\varphi.
\tag{II.44}
$$

Replace the residual by the left side of (II.4) in this pairing and integrate the Laplacian term by parts once. Only $W^a_\alpha$, $\partial_\theta W^a_\alpha$, $\nabla W^a_\alpha$, $1/S(\alpha)$ and $\beta^a(\alpha)$ remain, together with fixed test and actuator integrals. Their dependence is continuous on the compact support, and $S>0$, so the pairing is continuous. This is the continuity statement in (7.58), p.41.

Take $\alpha_j\to\alpha$ and abbreviate the held solutions by $(v_j,\beta_j)$. Their joint and supremum bounds control $v_j$ in $\mathcal E$, the multipliers in $\mathbb R^n$, and $N(v_j)$ in $H$. The residual bound and the uniform convection bound then control

$$
f_j=T_{S(\alpha_j)}v_j
=-P\left(F^a_{\alpha_j}+N(v_j)+C_{\alpha_j}v_j+\sum_i\beta_{j,i}b_i\right)
$$

in $H$. From any subsequence extract a further subsequence on which $f_j\rightharpoonup f$ and $\beta_j\to\widetilde\beta$. Since $S(\alpha_j)\to S(\alpha)>0$, Proposition II.5 gives weak convergence of gradients and Laplacians and strong local $L^2$ convergence to $\widetilde v=T_{S(\alpha)}^{-1}f$.

We pass the nonlinear equation to the limit against compact solenoidal tests. The free term passes by weak convergence. The coefficients of convection converge uniformly on compact sets; its two terms pass using weak gradient convergence and strong local velocity convergence. The multiplier term passes in finite dimension. The residual term passes by (II.44). Finally, because $v_j$ is solenoidal, $N(v_j)=\operatorname{div}(v_j\otimes v_j)$ in distributions. Strong local $L^2$ convergence makes $v_j\otimes v_j$ converge in local $L^1$, so the nonlinear term passes against every compact smooth vector test, whether solenoidal or not. Its uniform global $H$ bound identifies the limit with $N(\widetilde v)$ and permits the same identification against all $H$ tests by density.

The pin pairings pass by weak convergence of gradients and continuity of $\bar\ell$. The bound $A\le\rho$ passes by weak lower semicontinuity. The set of gradients with essential slice norm at most $M$ is convex and norm-closed in $L^2_{\theta,y}$, hence weakly closed; therefore $B(\widetilde v)\le M$. The symmetry subspace is weakly closed as well. Thus $(\widetilde v,\widetilde\beta)$ is a held solution at $\alpha$. Proposition II.13 identifies it with $(v_\alpha,\beta_\alpha)$.

Every subsequence has a further subsequence with this same multiplier limit. Since the multipliers lie in a bounded finite-dimensional set, this proves convergence of the full sequence and hence continuity. In particular,

$$
\Phi(\alpha)=\beta^a(\alpha)+\beta_\alpha
\tag{II.45}
$$

is continuous. The approximate adjoints and their coupling matrices enter no definition of this map; their possible discontinuity is harmless. The formal counterparts are `Breakdown.Cert.extendedDataContinuityHolds_of`, `Breakdown.Cert.extendedHeldLimitHolds_of` and `Breakdown.Cert.extendedMultiplierContinuityHolds_of`.
<!-- /passage:sec-8-continuity-of-the-remaining-finite-dimensional-problem -->

## 9. Choose the parameter and cancel the force

<!-- passage:sec-9-choose-the-parameter-and-cancel-the-force -->

<a id="9.1"></a>

### 9.1 Proposition II.15: the raw update stays in the parameter set

**Proposition II.15.** The continuous map

$$
\mathcal T(\alpha)=\alpha-D^{-1}V^{\mathsf T}\Phi(\alpha),
\qquad D=\operatorname{diag}(d_1,\ldots,d_n),
\tag{II.46}
$$

sends $K$ into itself. Its fixed points satisfy $\Phi(\alpha)=0$.

The transpose in this formula records that $V_j$ is column $j$. We prove the box and weighted-ball inclusions separately, using the same held solution at the current parameter.

<a id="9.2"></a>

### 9.2 The adjoint coordinates

Fix $j\in J$ and write $\psi=\psi_{\alpha,j}$. Applying (II.17) with $v=0$ shows that $\psi$ annihilates every $H$ field equivalent to zero modulo gradients. Equivalently, $\psi\in H_{\rm div}$. Thus the forthcoming pairing is justified even though $\psi$ was specified as an $H$ field rather than as a compact solenoidal test.

The field $F'=-F^a_\alpha-N(v_\alpha)-\sum_i\beta_{\alpha,i}b_i$ belongs to $H$ and represents $T_Sv_\alpha+C_\alpha v_\alpha$. Insert it into (II.17), use the pin identity and (II.16), and set $e_j=\langle b,\psi\rangle_H-V_j$. This gives

$$
\left|V_j\cdot\beta_\alpha+\langle F^a_\alpha,\psi\rangle_H
+(Y(\alpha)\bar\ell(\alpha))_j\right|
\le a_j\|v_\alpha\|_w+|e_j|\,|\beta_\alpha|
+\widetilde a_j\|v_\alpha\|_w^2.
$$

Combine the first two errors with the joint norm rather than estimating its two components independently:

$$
a_j\|v_\alpha\|_w+|e_j|\,|\beta_\alpha|
\le\sqrt{a_j^2+|e_j|^2/\omega^2}\,
\sqrt{\|v_\alpha\|_w^2+\omega^2|\beta_\alpha|^2}.
$$

Adding the affine offset bound (II.18), and using $A\le2\varepsilon$ and (II.19), yields

$$
|V_j\cdot\Phi(\alpha)-d_j\alpha_j|
\le o_j+2\varepsilon\sqrt{a_j^2+|e_j|^2/\omega^2}
+\widetilde a_j(2\varepsilon)^2
\le |d_j|\rho_j.
\tag{II.47}
$$

Since $d_j\mathcal T_j(\alpha)=d_j\alpha_j-V_j\cdot\Phi(\alpha)$ and $d_j\ne0$, this is the required coordinate inclusion $|\mathcal T_j(\alpha)|\le\rho_j$. The formal estimate is `Breakdown.Cert.extendedAdjointEnclosureHolds_of`, supported by `Breakdown.Cert.extendedAdjointPairingHolds_of` and the representative-independent pairing condition.

<a id="9.3"></a>

### 9.3 The remaining coordinates and the fixed point

For coordinates outside $J$, the Euclidean triangle inequality, (II.20), and $|\beta_\alpha|\le2\varepsilon/\omega$ give

$$
\left(\sum_{j\notin J}d_j^2\mathcal T_j(\alpha)^2\right)^{1/2}
\le\left(\sum_{j\notin J}(V_j\cdot\beta_\alpha)^2\right)^{1/2}
+\left(\sum_{j\notin J}(V_j\cdot\beta^a(\alpha)-d_j\alpha_j)^2\right)^{1/2}
\le\frac{2\varepsilon a_*}{\omega}+o_*\le\rho_*.
\tag{II.48}
$$

This proves the weighted-ball inclusion and completes $\mathcal T(K)\subseteq K$. Its formal counterpart is `Breakdown.Cert.extendedStiffEnclosureHolds`.

The set $K$ contains zero, is closed, and is bounded: outside $J$, each nonzero $d_j$ gives $|\alpha_j|\le\rho_*/|d_j|$. It is convex as an intersection of slabs and the inverse image of a Euclidean ball under a linear map. In finite dimension it is compact. We use the finite-dimensional fixed-point theorem in this exact form: every continuous self-map of a nonempty compact convex subset of a real finite-dimensional space has a fixed point. Empty interior causes no difficulty. Enclose $K$ in a box and compose $\mathcal T$ with the nearest-point projection onto $K$; the box fixed-point theorem gives a point whose image lies in $K$, so the point itself lies in $K$ and is a fixed point of $\mathcal T$.

Choose such an $\alpha_*$. Equation (II.46) gives $V^{\mathsf T}\Phi(\alpha_*)=0$. Invertibility of $V$ implies

$$
\beta_{\alpha_*}=-\beta^a(\alpha_*).
\tag{II.49}
$$

The force has vanished exactly. This argument also covers $n=0$, empty $J$, zero radii and boundary fixed points. The formal composition is `Breakdown.Cert.extendedExistsZeroHeldHolds_of`; its topological input is supplied through `Breakdown.Held.testSetZero_of`, `Breakdown.Held.convexCompactFixedPoint` and `Breakdown.exists_fixedPoint_box`.

A fixed point of a projected update alone would not suffice. For example, on $[-1,1]$, the raw update $x\mapsto x-1$ has no fixed point, while its nearest-point projection fixes $-1$. The displacement there remains one. The raw inclusions (II.47)–(II.48) are what remove this ambiguity in both the paper's route and the formal route.

<a id="9.4"></a>

### 9.4 The paper's simultaneous fixed point

The paper proves Proposition 7.10 by applying Schauder–Tychonoff to the pair consisting of a parameter and a proposed quadratic forcing. It establishes existence with the held bounds and exact cancellation stated in (7.59)–(7.60). The two constructions need not choose identical parameters or profiles. [P, pp.41–44.]

Let $Z$ be the closed ball of invariant fields $g\in H$ with $\|g\|_H\le2c_w\varepsilon M$. For each $(\alpha,g)$, use Proposition II.9 to solve the linear equation with right side $-F^a_\alpha-g$ and the required pins. The calculations in Proposition II.12 place its answer $(v,\beta)$ inside both correction bounds and return $N(v)$ to $Z$. If $\Pi_K$ is nearest-point projection onto $K$, define

$$
\mathcal G(\alpha,g)=
\left(\Pi_K\bigl(\alpha-D^{-1}V^{\mathsf T}(\beta^a(\alpha)+\beta)\bigr),\ N(v)\right).
$$

Give $Z$ the weak Hilbert-space topology. Closed bounded balls in a Hilbert space are weakly compact; $Z$ is convex. Since $H$ is separable, the weak topology on this ball is metrizable. Thus $K\times Z$ is a compact convex subset of a locally convex space.

To prove continuity, take $\alpha_j\to\alpha$ and $g_j\rightharpoonup g$. The linear solutions satisfy the uniform bounds already proved. Their free right sides are bounded in $H$, so Proposition II.5 supplies subsequential strong local velocity convergence and weak derivative convergence. Pass the linear equation, residual pairings and pins to the limit as in §8. Uniqueness of the bordered linear solve identifies the limiting pair with the solve at $(\alpha,g)$. Strong local convergence and the uniform $H$ bound identify the weak limit of $N(v_j)$ with $N(v)$. The multipliers converge as well, proving continuity of $\mathcal G$.

The Schauder–Tychonoff theorem used here states that a continuous self-map of a nonempty compact convex subset of a Hausdorff locally convex topological vector space has a fixed point. At a fixed point, $g=N(v)$, so the nonlinear equation holds. The raw membership proof (II.47)–(II.48) then shows that the projection in the first component is inactive. Hence $\alpha$ is a fixed point of the raw update, and (II.49) follows.

This proof needs the self-map estimates and compactness, while the main proof also establishes fixed-parameter uniqueness using (7.26). The main exposition follows the latter route because it is the route actually assembled by the extended-certificate Lean proof. The simultaneous route explains the paper's explicit statement that (7.26) is unused there. Neither comparison establishes equivalence of the complete paper and formal certificate predicates.
<!-- /passage:sec-9-choose-the-parameter-and-cancel-the-force -->

## 10. The selected weak profile

<!-- passage:sec-10-the-selected-weak-profile -->

<a id="10.1"></a>

### 10.1 Proposition II.16: cancellation and nontriviality

**Proposition II.16.** For the selected $\alpha_*$, put $S=S(\alpha_*)$, $v=v_{\alpha_*}$ and $\mathcal W=W^a_{\alpha_*}+v$. Then $\mathcal W$ is a nonzero continuous period-one curve in $X$, and

$$
T_S\mathcal W+N(\mathcal W)\simeq0.
\tag{II.50}
$$

Every term in this distributional equation is represented by a locally integrable function.

To prove the equation, add the approximate relation (II.4) to the correction equation (II.5). The quadratic expansion contributes the two cross terms whose sum is $C_\alpha v$, together with the pure correction term $N(v)$. The residuals cancel, and the total force coefficients cancel by (II.49). This gives (II.50).

The correction is continuous in $X$ by Lemma II.3. For the approximate profile, continuity of the gradient and (II.3) permit dominated convergence in $L^2_y$: the square is bounded by a constant times $(1+|y|)^{-4}$, integrable in dimension three. Its velocities are likewise continuous in $L^6$, using $(1+|y|)^{-6}$. Thus the sum is a continuous periodic $X$ curve.

For local integrability of the correction's time derivative, solve the graph identity for it:

$$
S^{-1}\partial_\theta v
=T_Sv+\Delta v-\frac12v-\frac12y\cdot\nabla v.
$$

The first two fields are in $H$. On bounded spatial sets the last two are locally square integrable, by $v\in L^2_\theta L^6_y$ and the gradient bound. Thus the time derivative is locally square integrable. The approximate field has the required local derivatives by hypothesis, and the quadratic and cross terms have the bounds from §4. This verifies all local-integrability requirements without separating the time and dilation terms globally.

If $\mathcal W$ vanished, then $\nabla v=-\nabla W^a_{\alpha_*}$, so

$$
w_*\|\nabla W^a_{\alpha_*}\|_H^2
=w_*\|\nabla v\|_H^2
\le\|v\|_w^2\le A(v,\beta)^2\le4\varepsilon^2.
$$

This contradicts (II.14). The strict profile-separation inequality, rather than residual smallness alone, supplies nontriviality. The formal steps are `Breakdown.Cert.extendedHeldWeakEquationHolds_of` and `Breakdown.Cert.extendedHeldNonzeroHolds_of`. [P, proof of Theorem 7.1, pp.44–45.]
<!-- /passage:sec-10-the-selected-weak-profile -->

## 11. Regularity of the selected orbit

<!-- passage:sec-11-regularity-of-the-selected-orbit -->

<a id="11.1"></a>

### 11.1 Proposition II.17: the precise regularity statement

**Proposition II.17.** Let $S>0$ and let $\mathcal W\in C(\mathbb R;X)$ be nonzero and period-one. Suppose every term of $T_S\mathcal W+N(\mathcal W)$ is locally integrable and this expression is zero modulo gradients. Then there are smooth $W,q$ satisfying the similarity equation, with period $S$, identity isometry and the profile decay in Theorem II.1, such that

$$
W(s,\cdot)=\mathcal W(s/S,\cdot)\quad\text{in }X
\quad\text{for every }s\in\mathbb R.
\tag{II.51}
$$

This is Proposition 7.11, stated on p.44 and proved on pp.45–47. Its hypotheses are much more specific than unrestricted weak Navier–Stokes solvability. The hypotheses of Proposition II.17 already provide a continuous periodic homogeneous $H^1$ orbit. The linked formal weak-profile hypothesis instead gives measurable recurrent fields with global derivative bounds; its construction derives a continuous orbit before smoothing. We verify below how that input reaches each regularity theorem used.

<a id="11.2"></a>

### 11.2 From the similarity equation to a physical mild solution

Define, for $t<1$,

$$
s=-\log(1-t),\quad \theta=s/S,\quad y=x/\sqrt{1-t},
\qquad
u(t,x)=(1-t)^{-1/2}\mathcal W(\theta,y).
\tag{II.52}
$$

Continuity of dilation on $X$ gives $u\in C((-\infty,1);X)$, and the Sobolev embedding gives continuity in $L^6$. Periodicity of $\mathcal W$ implies the uniform scaling bound

$$
B_6:=\sup_{t<1}(1-t)^{1/4}\|u(t)\|_6
=\sup_\theta\|\mathcal W(\theta)\|_6<\infty.
\tag{II.53}
$$

Changing variables in the weak similarity equation gives the physical weak Navier–Stokes equation against solenoidal tests. In particular, for a compactly supported smooth solenoidal spatial field $\psi$,

$$
\frac{d}{dt}\int u(t)\cdot\psi
=\int u(t)\cdot\Delta\psi+u(t)\otimes u(t):\nabla\psi.
\tag{II.54}
$$

Initially this is an identity in time distributions. Both integrals on the right depend continuously on $t$, by $u\in C_tL^6_x$ and the compact support of $\psi$. The left pairing is therefore continuously differentiable and (II.54) holds at every time.

We use the weak-to-mild statement proved in Part I, corresponding to the paper's Lemma 3.6: an $X$-continuous solenoidal curve on a compact interval that satisfies (II.54) for every such spatial test is its mild Navier–Stokes evolution from its value at the left endpoint. Consequently, for every $a<t<1$,

$$
u(t)=e^{(t-a)\Delta}u(a)
-\int_a^t\nabla O_{t-\tau}*(u(\tau)\otimes u(\tau))\,d\tau,
\tag{II.55}
$$

where $O_r$ is the kernel of $e^{r\Delta}P$, with the tensor indices contracted as in the convection term. The integral is an $X$ integral and hence also an $L^6$ integral. The mathematical argument applies to the particular selected orbit, preserving its identity. The linked formal weak-to-mild result returns an existential orbit, so retaining that identity in a theorem statement requires the separate same-witness construction. The formal construction `Breakdown.WeakProfile.weakOrbitOfParts_holds` proves the corresponding weak-to-mild orbit step through its own representative interfaces.

<a id="11.3"></a>

### 11.3 Two explicit integrable bootstraps

Fix $t<1$, put $h=1-t$, and start (II.55) at $a=t-h$. On $[a,t]$, one has $h\le1-\tau\le2h$, so $\|u(\tau)\|_6\le B_6h^{-1/4}$. The heat kernel maps $L^6$ to $L^{12}$ with bound $Ch^{-1/8}$; the Oseen derivative has $L^{4/3}$ norm at most $Cr^{-7/8}$. These exponents follow from the three-dimensional heat-kernel scaling and one spatial derivative. Since $u\otimes u\in L^3$, Young's and Minkowski's inequalities give

$$
\begin{aligned}
\|u(t)\|_{12}
&\le C h^{-1/8}\|u(a)\|_6
+C\int_a^t(t-\tau)^{-7/8}\|u(\tau)\|_6^2\,d\tau\\
&\le C B_6h^{-3/8}+C B_6^2h^{-1/2}\int_0^h r^{-7/8}\,dr
\le C_{B_6}h^{-3/8}.
\end{aligned}
\tag{II.56}
$$

This holds at every $t<1$. Repeat the argument using $L^{12}$ in place of $L^6$. The heat map $L^{12}\to L^\infty$ costs $Ch^{-1/8}$, and $\|\nabla O_r\|_{6/5}\le Cr^{-3/4}$. Since the tensor product is now in $L^6$,

$$
\begin{aligned}
\|u(t)\|_\infty
&\le Ch^{-1/8}\|u(a)\|_{12}
+C\int_a^t(t-\tau)^{-3/4}\|u(\tau)\|_{12}^2\,d\tau\\
&\le C_{B_6}h^{-1/2}+C_{B_6}h^{-3/4}\int_0^h r^{-3/4}\,dr
\le C'_{B_6}h^{-1/2}.
\end{aligned}
\tag{II.57}
$$

The integrals are $8h^{1/8}$ and $4h^{1/4}$ respectively. Both singularities are integrable; no endpoint convolution estimate is being assumed. Hence $u$ is bounded on every strip $(-\infty,b]\times\mathbb R^3$ with $b<1$. These are the calculations behind (7.63)–(7.65), pp.45–46, using the heat and Oseen estimates established in Part I.

<a id="11.4"></a>

### 11.4 Smoothness, every-time identity and pressure

On a compact interval $[a,b]\subset(-\infty,1)$ the solution and its initial datum $u(a)$ are bounded. Since $\|\nabla O_r\|_1\le Cr^{-1/2}$, the nonlinear integral in (II.55) also converges absolutely pointwise on this interval and agrees almost everywhere with the mild expression already obtained. The shifted solution therefore meets the bounded-mild hypotheses of Koch–Nadirashvili–Seregin–Šverák, Proposition 4.1 [K, PDF p.11]: a bounded mild solution with bounded initial datum has bounded distributional derivatives $(t-a)^{j/2+l}\nabla_x^j\partial_t^l u$ for every pair of nonnegative integers $j,l$. It consequently has a smooth representative away from $a$. Since $a$ and $b$ are arbitrary, there is a smooth representative $U$ on the entire interval $(-\infty,1)$.

The representative still denotes the original $X$ element at every time. To see this without assuming global gradient continuity for $U$ in advance, fix any compact smooth spatial test $\psi$. The functions $t\mapsto\int u(t)\cdot\psi$ and $t\mapsto\int U(t)\cdot\psi$ are continuous, the first by $C_tL^6$ continuity and the second by local smoothness. Their space-time almost-everywhere equality makes the two continuous pairings equal almost everywhere in time, and therefore everywhere. This holds for all tests, so $U(t)=u(t)$ as spatial distributions at each time. Spatial almost-everywhere equality and uniqueness of weak derivatives transfer the original $L^6$ field and its $L^2$ gradient to $U(t)$. Hence they are equal in $X$ for every time. We henceforth call the smooth representative $u$.

Let $G=\partial_tu-\Delta u+(u\cdot\nabla)u$. Equation (II.54) says that this smooth field annihilates every compact solenoidal spatial test at each time. Testing against curls gives $\operatorname{curl}G=0$. On $\mathbb R^3$ the radial primitive

$$
p(t,x)=-\int_0^1G(t,\sigma x)\cdot x\,d\sigma
\tag{II.58}
$$

is smooth and satisfies $\nabla p=-G$. Indeed, differentiating the radial primitive of a curl-free field converts the integrand to the derivative of $\sigma G(t,\sigma x)$; evaluating at $0$ and $1$ gives the required gradient. Thus $(u,p)$ solves the classical physical Navier–Stokes equations. This pressure construction leaves only the usual freedom to add a function of time.

<a id="11.5"></a>

### 11.5 Spatial decay and return to similarity time

Periodicity of the original orbit and (II.52) imply, with $\lambda=e^{S/2}>1$,

$$
u(1+t,x)=\lambda u(1+\lambda^2t,\lambda x)
\qquad(t<0).
\tag{II.59}
$$

The shifted field is smooth, solves Navier–Stokes and belongs to $C(( -\infty,0);L^6)$, and (II.59) gives ordinary backward discrete self-similarity. These are exactly the hypotheses of Chae–Wolf, Theorem 1.1 [C, PDF p.2], with exponent $p=6$: a smooth backward discretely self-similar solution continuous in $L^p$, for $3\le p<\infty$, obeys a bound by a constant times $(\sqrt{-t}+|x|)^{-1}$. Therefore

$$
|u(t,x)|\le\frac{C}{\sqrt{1-t}+|x|},\qquad t<1.
\tag{II.60}
$$

Now set

$$
W(s,y)=e^{-s/2}u(1-e^{-s},e^{-s/2}y),
\qquad
q(s,y)=e^{-s}p(1-e^{-s},e^{-s/2}y).
\tag{II.61}
$$

The chain rule gives the similarity equation and solenoidality. The every-time identity already proved gives (II.51), so periodicity and nontriviality are retained. Substitution in (II.60) gives $|W(s,y)|\le C(1+|y|)^{-1}$.

Here is the derivative-decay step invoked in the paper's Remark 1.2. At a physical point $(t,x)$ choose $r=\frac12\max\{|x|,\sqrt{1-t}\}$. On its backward parabolic cylinder $(t-r^2,t)\times B_r(x)$, either $|x|$ is dominant and $|z|\ge r$, or the time scale is dominant and $\sqrt{1-\tau}\ge2r$. Thus (II.60) bounds $|u|$ by $C/r$ on the cylinder. The pressure-independent interior estimate [V, Lemma 9.1, PDF p.30] states that a smooth Navier–Stokes solution bounded by $A/r$ on a backward cylinder has spatial derivatives of order $j$ bounded by $C_j(A)r^{-j-1}$ on each fixed smaller concentric cylinder. Apply it at the top centre by continuity from earlier times. Since $x=\sqrt{1-t}\,y$ and

$$
\nabla_y^jW=(1-t)^{(j+1)/2}\nabla_x^ju,
$$

we obtain $|\nabla_y^jW(s,y)|\le C_j(1+|y|)^{-j-1}$, in particular the required first-derivative bound. This finishes Proposition II.17. Its proof uses the exact external regularity statements above, after their hypotheses have been derived. It does not assume finite kinetic energy of the profile.

<a id="11.6"></a>

### 11.6 How the formal regularity proof is organised

The formal regularity route proves the necessary analytic results inside the library instead of invoking the two named external profile regularity theorems. The following is a correspondence of proof mechanisms; the complete mathematical proof of Proposition II.17 above follows the published argument. It is not a line-by-line expansion of the much larger far-field library.

`Breakdown.WeakProfile.weakOrbitOfParts_holds` produces a continuous mild orbit from the weak profile data. `Breakdown.FarField.smoothFieldOfOrbit_holds` uses Fourier Sobolev bootstrapping and Picard estimates to obtain a smooth velocity and pressure representing that orbit. Its velocity relation preserves spatial almost-everywhere equality at each time. These are the facts needed to keep the selected orbit through smoothing.

`Breakdown.FarField.integralEquationOfOrbit_holds` derives an Oseen integral equation extending into the past. `Breakdown.FarField.farFieldDecay_holds` then proves spatial decay by weighted integral estimates and a small-tail inverse argument. It also supplies stronger derivative and pressure-gradient decay than the two velocity bounds required in the paper's profile definition. Those extra conclusions do not, by themselves, retain a certificate parameter or its correction.

The public theorem `Breakdown.FarField.periodicLerayProfileExists_of_weak` packages this route as weak-to-smooth profile existence. That existential interface is insufficient as a direct statement of (II.1). The proof in the next section retains the relation to the originally constructed orbit throughout.
<!-- /passage:sec-11-regularity-of-the-selected-orbit -->

## 12. Keep the same witness through regularity

<!-- passage:sec-12-keep-the-same-witness-through-regularity -->

<a id="12.1"></a>

### 12.1 Completion of Theorem II.1

Apply Proposition II.17 to the particular $\mathcal W=W^a_{\alpha_*}+v$ from Proposition II.16. It gives a smooth profile with the selected period and

$$
W(S\theta,\cdot)=W^a_{\alpha_*}(\theta,\cdot)+v(\theta,\cdot)
\quad\text{in }X\quad\text{for every }\theta.
\tag{II.62}
$$

Consequently the actual difference $v_*(\theta,y)=W(S\theta,y)-W^a_{\alpha_*}(\theta,y)$ is the original correction as an $X$ element at every time. Equality in $X$ here includes equality of the canonical $L^6$ representatives. It preserves weak gradients and weak second derivatives, as well as their distributional transport equation. Therefore $v_*\in D_S^\Gamma$ and

$$
\|v_*\|_w^2=\|v\|_w^2,
\qquad \ell(v_*)=\ell(v),
\qquad
\|\nabla v_*(\theta)\|_2=\|\nabla v(\theta)\|_2
\quad\text{for every }\theta.
\tag{II.63}
$$

The weak Hessian can simply be the already constructed weak Hessian of $v$. There is no need to demand a classical Hessian of the $C^1$ approximate profile. All energy integrals remain finite because the derivative classes have been retained and $w$ is bounded. Substituting $\beta=-\beta^a(\alpha_*)$ in the original joint estimate gives

$$
\|v_*\|_w^2+\omega^2|\beta^a(\alpha_*)|^2
=\|v\|_w^2+\omega^2|\beta|^2\le4\varepsilon^2.
$$

Together with the pins and the last identity of (II.63), this proves all of (II.1). A bound on the velocity correction alone would not imply this joint estimate; the multiplier component has been carried through every step.

For symmetry, fix any one pair $(R,\theta_0)\in\Gamma$. The invariant-class identity for the correction holds almost everywhere in time, and both sides are continuous $X$ curves. It therefore holds at every time. The approximate field satisfies the corresponding identity pointwise, so the sum satisfies it in $X$ at every time. By (II.62), this is an identity between smooth spatial functions for each fixed time; spatial almost-everywhere equality then becomes pointwise equality. Substituting $s=S\theta$ gives (II.2). The argument is made separately for each pair and uses no common exceptional set over a possibly uncountable $\Gamma$. This completes Theorem II.1. [P, (7.62) and proof of Theorem 7.1, pp.44–45.]

<a id="12.2"></a>

### 12.2 The every-time bridge in the proposed wrapper

The proposed wrapper follows a more explicit representative route. Some intermediate readings give equalities almost everywhere in time and space, while the smooth-orbit interface gives spatial almost-everywhere equality for every time. The wrapper keeps both relations and uses the derivative tails to recover the final time quantifier for the correction's gradient norm.

Let $V(\theta,y)=W(S\theta,y)-W^a_{\alpha_*}(\theta,y)$. The exact and approximate fields have uniform derivative tails, so for a constant $A_0$,

$$
|\nabla V(\theta,y)|_{\rm op}\le A_0(1+|y|)^{-2},
\qquad
|\nabla V(\theta,y)|_{\rm F}^2\le3A_0^2(1+|y|)^{-4}.
$$

The second right side is integrable on $\mathbb R^3$. Joint $C^1$ regularity and dominated convergence make $E_V(\theta)=\int|\nabla V(\theta,y)|_{\rm F}^2\,dy$ continuous. The reading of the held solution gives $E_V\le M^2$ almost everywhere. If it failed at one time, continuity would make it fail on an interval of positive measure. Thus it holds at every time. Pointwise smoothness alone would not establish continuity of an integral over all of space; the integrable tail bound supplies the needed domination.

The intended wrapper also proves finiteness before interpreting a nonnegative integral as a real number. In Lean, the total conversion from extended nonnegative reals sends infinity to zero. A real-valued inequality obtained through that conversion would be insufficient without the separate finite-integral fact. Here the existing gradient and Laplacian integrability, together with bounded $w$, gives precisely that fact.

Under multiplier normalisation the retained coefficient is $\kappa_i=-\omega\beta_i^a(\alpha_*)$, so its squared Euclidean norm is exactly $\omega^2|\beta^a(\alpha_*)|^2$. The same parameter set, period and pin data survive the two normalisations from §2.6. These are the bridges in our Theorem 7.1 wrapper, which compiles against the authors' package; its declarations are not linked from this account.

<a id="12.3"></a>

### 12.3 Corollary II.18: apply Part I to this profile

**Corollary II.18.** If a certificate exists, the conclusions of Theorem 1.1 hold on $\mathbb R^3$ and $\mathbb T^3$ with the smooth profile, selected period and identity isometry supplied by Theorem II.1.

Here is the quantitative content of that application, with unit viscosity as in the paper. Define

$$
u_T^*(t,x)=(T-t)^{-1/2}W\left(\log\frac{T}{T-t},\frac{x}{\sqrt{T-t}}\right).
$$

On $\mathbb R^3$ there is a smooth compactly supported solenoidal initial datum and a smooth finite-energy unforced solution on $[0,1)$, with constants $0<c\le C$ and $\kappa\in(0,1/4)$, such that

$$
c(1-t)^{-1/4}\le\|\nabla u(t)\|_2\le C(1-t)^{-1/4},
\qquad
\|\nabla(u(t)-u_1^*(t))\|_2\le C(1-t)^{\kappa-1/4}.
\tag{II.64}
$$

On $\mathbb T^3$ there are a time $T\in(0,1]$, a smooth solenoidal initial datum and a smooth unforced solution on $[0,T)$ such that

$$
c(T-t)^{-1/4}\le\|u_{\rm per}(t)\|_{H^1(\mathbb T^3)}\le C(T-t)^{-1/4},
\qquad
\|u_{\rm per}(t)-u_T^*(t)\|_{H^1(B_{1/16})}
\le C(T-t)^{\kappa-1/4}.
\tag{II.65}
$$

The local comparison on the torus uses its coordinate ball about the singularity. The proof is direct substitution into Part I's Theorem 1.1: Theorem II.1 supplies its smooth nonzero profile, solenoidality, periodicity and two decay bounds, with $S=S(\alpha_*)$ and $R=I$. That theorem supplies the solutions and rates, so the profile in (II.64)–(II.65) is the one just constructed. This is the paper's Corollary 7.2. [P, Theorem 1.1, p.3; Corollary 7.2, p.35.]

The public declaration `Breakdown.extended_certificate_breakdown_on_space` gives the whole-space breakdown endpoint directly from an extended certificate hypothesis. For the torus, compose `Breakdown.extended_certificate_orbit_proved` with `Breakdown.FarField.breakdownOnTorus_of_weak`. Their theorem types expose less than the full quantitative same-profile corollary above. A reader link to those endpoints therefore carries a weaker comparison, with that loss of displayed information stated explicitly.

<a id="12.4"></a>

### 12.4 Remark II.19: a prescribed shorter recurrence

If $(R,\theta_0)\in\Gamma$ with $\theta_0>0$, equation (II.2) makes the same velocity a profile with recurrence time $S\theta_0$ and isometry $R$. The differential equation and decay bounds do not depend on the choice of recurrence. In particular, a half-period symmetry gives recurrence time $S/2$. This is Remark 7.3, p.35. It supplies an additional recurrence description of the same velocity; it makes no claim about a least period.
<!-- /passage:sec-12-keep-the-same-witness-through-regularity -->

## 13. Constants, comparisons and the conditional boundary

<!-- passage:sec-13-constants-comparisons-and-the-conditional-boundary -->

<a id="13.1"></a>

### 13.1 Where the numerical restrictions enter

The Appendix B weight is $w_*=39/50$. It sets the exact coefficient in Lemma II.6, the mean-to-supremum conversion in Proposition II.10, and the nonzero comparison in Proposition II.16. Appendix B's restrictions also give $c_1\ge50/3$, $c_0>81.64$ and $c_2>129$. Because $\vartheta\ge0$, (II.8) forces

$$
c_L\ge\frac{c_1+c_0}{1-\vartheta}\ge c_1+c_0
>\frac{50}{3}+81.64=\frac{7373}{75}>98.3.
$$

At this weight $c_w\approx0.3001728559793$, and therefore (II.11) implies

$$
M<\frac{1}{2c_Lc_w}
<\frac{1}{2(7373/75)c_w}
\approx0.016943987271<0.01695.
$$

Every remaining term on the left of (II.13) is nonnegative. In particular $\delta_{\max}\ge0$ follows by choosing $\alpha\in K$ and using $0\le\|F^a_\alpha\|_H\le\delta(\alpha)\le\delta_{\max}$. Hence

$$
\varepsilon\le\frac{M\sqrt{39/50}}2
<\frac{(39/50)^{3/4}\sqrt\pi}{2(7373/75)}
\approx0.007482262185<0.0075.
$$

The displayed decimals are explanatory evaluations of symbolic consequences. The validation script additionally checks the rounded bounds with rational inequalities and an explicit rational upper bound for $\pi$. It performs no interval evaluation of an approximate profile, a coercive form, or a cell matrix. The source of the restrictions is [P, (B.22), p.56; concluding paragraph of Appendix B, p.70].

| Quantity | Exact point where it is used |
|---|---|
| $w_*=39/50$ | Fourier product constant, weighted norm coercivity, enstrophy mean, profile separation |
| $c_L>98.3$ | Zero-pin inverse estimate and the contraction factor |
| $M<0.01695$ | Necessary upper limit for the held gradient-supremum radius |
| $\varepsilon<0.0075$ | Necessary upper limit for half the joint correction radius |
| $(7.24)$ | Residual and pins fit inside the first correction budget |
| $(7.25)$ | The nonlinear difference factor is strictly below one |
| $(7.26)$ | The inverse controls the second component of the contraction metric |
| $(7.27)$ | Each nonlinear step preserves the gradient-supremum bound |
| $(7.28)$ | The resulting exact profile cannot be zero |
| $(7.35),(7.37)$ | The raw parameter update stays inside the box and weighted ball |

<a id="13.2"></a>

### 13.2 What is represented differently in the formal certificate

The mathematical proof above uses the analytic certificate stated in the paper. The linked formal construction starts from `Breakdown.IsExtendedCertificate`. Some differences are choices of representation: the finite rows are normalised, full-profile pin targets are converted to correction targets by subtracting the approximate pins, and the weak Hessian and pressure contribution are supplied separately. The pressure contribution is required to annihilate compact solenoidal tests; these data do not specify a scalar pressure whose gradient it is. Other differences strengthen the stated input: the formal approximate profile is globally jointly $C^1$ in the ambient parameter, time and space; it has a specified weak Hessian with cubic decay; the weight is invariant under the symmetries; the pin coefficient is nonnegative; and the adjoints carry a uniform spatial $L^2$ bound at each time. The paper's §§7.2–7.3 do not state all these requirements in that form.

The formal `twist` may be one even when a half-period symmetry is available, which gives a conservative version of the same inequalities. The paper defines $m$ to be two whenever that symmetry is present. None of these observations asserts that the concrete Appendix B data violate a formal hypothesis. They show why a comparison must name the actual input predicate and why a collection of local correspondences does not prove equivalence of the complete certificate definitions.

Intermediate results establish one analytic step from previously proved estimates or representation identities. The linked top-level theorem assembles these steps from an extended certificate hypothesis. They are linked here for the particular step they establish. The top-level `Breakdown.extended_certificate_orbit_proved` assembles these nodes from the extended certificate hypothesis. Its conclusion is still conditional and existential. The same-witness wrapper attempts an additional conclusion-preserving assembly; its supplied source and build state remain separately identified.

<a id="13.3"></a>

### 13.3 What this argument does and what remains external

The implications proved here are: the analytic certificate gives a nonzero smooth periodic profile with (II.1)–(II.2); that profile gives the two breakdown constructions through Part I. The authors' repository explicitly separates these implications from the existence and verification of their concrete certificate. The supplied repository contains neither that numerical data set nor its 128-bit Arb computation. A hash or a stated numerical precision does not establish the missing inequalities.
<!-- /passage:sec-13-constants-comparisons-and-the-conditional-boundary -->

## Source keys

<!-- passage:sec-source-keys -->

**[P]** Alpöge and Buckmaster, *Finite-time blow-up for the Navier–Stokes equations*, supplied 79-page version of 20 November 2026. [Pinned paper](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/paper/finite-time-blow-up-navier-stokes.pdf).

**[L]** Authors' [pinned Lean README](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/README.md) and the Lean source at the same commit.

**[K]** Koch, Nadirashvili, Seregin and Šverák, *Liouville theorems for the Navier–Stokes equations and applications*, Proposition 4.1, [author preprint, PDF p.11](https://arxiv.org/pdf/0709.3599). Used only after establishing bounded mild solvability.

**[C]** Chae and Wolf, *Removing discretely self-similar singularities for the 3D Navier–Stokes equations*, Theorem 1.1, [author preprint, PDF p.2](https://arxiv.org/pdf/1610.09464). Used with $p=6$ and backward scaling factor $e^{S/2}>1$.

**[V]** Pineau and Vicol, *On rotated backwards self-similar solutions of the incompressible 3D Navier–Stokes equations*, Lemma 9.1, [version 2, PDF p.30](https://arxiv.org/pdf/2607.09619v2). Used for pressure-independent interior spatial derivative bounds as in [P, Remark 1.2].

A formal theorem's input and output types, its successful checking receipt, and the mathematical interpretation of its definitions are distinct pieces of evidence.
<!-- /passage:sec-source-keys -->

