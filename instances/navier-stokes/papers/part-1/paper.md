
<!-- passage:front -->
# From a recurrent profile to compact-data Navier–Stokes blow-up

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · **full account, part I** · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

*An expanded account of §§1–6 and Appendix A of Alpöge and Buckmaster, with correspondences to the Lean source at `ad53419de079eb8f95f60313473374624a348546`.*

The input to this argument is one nonzero smooth solution of the similarity equations which returns after a positive time, possibly after an orthogonal change of coordinates. Its spatial decay is just strong enough to put it in the homogeneous Sobolev space with norm $\|\nabla u\|_2$. In that space, heat evolution followed by rescaling contracts. The linearised return map differs from this contraction by a compact operator. Only finitely many directions can therefore obstruct a chosen decay rate. Choosing the initial datum along a finite-dimensional space of compactly supported fields removes those obstructions. A nonlinear correction then produces the whole-space solution. A second construction transfers the correction to a large torus and removes its localisation error exactly.

The profile is assumed throughout. Constructing it from certificate data is the separate argument of Theorem 7.1. The numerical certificate and its external checker are outside the formal proofs of the released source. Nothing below changes that boundary.
<!-- /passage:front -->

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

<a id="1"></a>

## 1. The conditional theorem and its proof

<!-- passage:sec-1 -->

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
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. The analytic space and the mild equation

<!-- passage:sec-2 -->

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
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. The profile in physical variables

<!-- passage:sec-3 -->

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
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. The monodromy and the exceptional directions

<!-- passage:sec-4 -->

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
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. A right inverse with compact initial corrections

<!-- passage:sec-5 -->

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
<!-- /passage:sec-5 -->

<a id="6"></a>

## 6. The nonlinear correction on whole space

<!-- passage:sec-6 -->

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
<!-- /passage:sec-6 -->

<a id="7"></a>

## 7. Smoothness, energy and the whole-space conclusion

<!-- passage:sec-7 -->

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
<!-- /passage:sec-7 -->

<a id="8"></a>

## 8. The construction on a large torus

<!-- passage:sec-8 -->

We keep the whole-space objects already constructed: the profile field $u^*=u_1^*$, its positive lower norm constant $c_*$, the exponent $0<\kappa<1/4$, the finite-dimensional space $E$ of smooth compactly supported solenoidal corrections, and the bounded right inverse $\mathcal R$ of Section 5. The parameter $L\ge1$ will be the spatial period. Every implicit constant in this section is independent of $L$ and of $0\le t<1$; it may depend on the fixed profile, $\kappa$, $E$ and the cutoff.

The plan is to put a compact part of $u^*$ into one periodic cell, measure its failure to solve the equation, and remove that failure. The inverse is transferred through a ball on which the coefficient is supported. This avoids requiring any recurrence of the periodic approximate field.

<a id="8.1"></a>

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

<a id="8.2"></a>

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

<a id="8.3"></a>

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

<a id="8.4"></a>

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

<a id="8.5"></a>

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

<a id="8.6"></a>

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
<!-- /passage:sec-8 -->

<a id="9"></a>

## 9. The unit torus and the theorem

<!-- passage:sec-9 -->

<a id="9.1"></a>

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

<a id="9.2"></a>

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

<a id="9.3"></a>

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

<a id="9.4"></a>

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
<!-- /passage:sec-9 -->

<a id="appendix-a"></a>

## Appendix A. The analytic results used above

<!-- passage:sec-appendix-a -->

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
<!-- /passage:sec-appendix-a -->

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

