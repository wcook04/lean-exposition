
<!-- passage:front -->
# Part II. A certificate produces a nonzero periodic profile

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · **part II** · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

This is an original account of §7 of Alpöge and Buckmaster, *Finite-time blow-up for the Navier–Stokes equations*, version of 20 November 2026. The reference version of the accompanying Lean source is `ad53419de079eb8f95f60313473374624a348546`. Paper references below use its printed numbering and pages. The notation agrees with the [specialist digest](../navier-stokes/digest.md). Our results and equations carry the prefix II; references to the authors' Appendix B keep the prefix B and the source key [P].

The input to this part is a certificate: approximate periodic fields, a finite-dimensional parameter set, and inequalities that control every admissible perturbation. The output is one nonzero smooth profile, together with the parameter, period, bounds and symmetries used to construct it. The existence of the concrete numerical certificate remains a separate premise.

We first solve the nonlinear equation for each fixed parameter by contraction. We then choose the parameter by a finite-dimensional fixed-point theorem. This follows the extended-certificate route in Lean and explains the purpose of (7.26). Section 9.4 also gives the paper's simultaneous Schauder–Tychonoff construction. For regularity we write out the paper's argument with the precise external results it uses, then explain the different formal route. The comparisons distinguish a proof of an analytic step from a theorem whose conclusion retains every requested witness.
<!-- /passage:front -->

## 1. The result and its notation

<!-- passage:sec-1-the-result-and-its-notation -->

<a id="1.1"></a>

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

<a id="1.2"></a>

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

<a id="1.3"></a>

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

