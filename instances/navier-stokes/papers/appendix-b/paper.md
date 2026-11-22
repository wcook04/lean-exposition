
<!-- passage:front -->
# From cell data to a Navier–Stokes certificate

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · **part III** · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

An original account of Appendix B of Alpöge and Buckmaster, *Finite-time blow-up for the Navier–Stokes equations*, with a short account of Appendix C.

**Source edition:** 20 November 2026, commit `ad53419de079eb8f95f60313473374624a348546`. Mathematical statements are restated in our own words.
<!-- /passage:front -->

## What Appendix B establishes

<!-- passage:sec-what-appendix-b-establishes -->

Appendix B explains how represented fields, cell calculations and matrix inequalities supply the estimates required of a certificate in Section 7. Its principal conclusion is conditional: data satisfying all the specified conditions produce a certificate, from which the profile and breakdown results follow. The public source contains the proof of this implication. It does not contain a particular numerical certificate satisfying the conditions, or the program reported to have checked one.

A useful reading order separates two tasks. The first establishes a coercive estimate for every admissible perturbation. The second establishes the approximation, parameter and adjoint estimates that let Theorem 7.1 construct a profile. The two tasks meet at B.14.

| Stage | Results | What has been established at the end |
|---|---|---|
| Construct a multiplier | B.1 | A bounded solenoidal multiplier and a lower estimate for its pairing with the linearised equation. |
| Control the spatial and harmonic pieces | B.3–B.6 | A cell form, with all unresolved harmonics, coupling remainders and the unbounded exterior accounted for. |
| Certify the assembled form | B.7–B.8 | A lower bound modulo the specified constraints, obtained through the elimination tree. |
| Close the a priori estimate | B.2, using B.1 and B.8 | A bound on the perturbation in terms of the residual and constraint values. |
| Control the candidate and the adjoints | B.9–B.13 | The remaining profile, linear, dual and quadratic estimates used in Section 7. |
| Assemble the certificate | B.14 | One certificate for the same linked data, with a sufficiently large common decay bound. |

The proof of B.2 appears immediately after B.1 in the paper because it explains the lower bound the remaining cell argument must deliver. Read it once as a target, then return to it after B.8.
<!-- /passage:sec-what-appendix-b-establishes -->

## Finitely represented data and universal conditions

<!-- passage:sec-finitely-represented-data-and-universal-conditions -->

Three notions of finiteness need to be distinguished. Each stored object can have a finite description, such as a polynomial coefficient table or a matrix. The analytic reductions can leave finitely many *families* of inequalities. An inequality in one such family can still quantify over every point of a cell, every parameter in a box times an ellipsoid, or every vector in a specified linear space. The reduction also needs arguments covering all omitted harmonics and the entire unbounded exterior.

Accordingly, `CellSystemCondition` is a mathematical predicate on seven linked inputs. Its fifteen fields are not fifteen floating-point comparisons. Some fields assert exact representation identities, some assert regularity or coverage, and others give bounds uniformly over continuous domains. The account below explains which obligations come from finite algebra, which come from analytic theorems in the library, and which still have to be supplied by a concrete decoder and checker.

Use $\theta$ for period-one time, $y\in\mathbb R^3$ for space, $r=\sqrt{y_1^2+y_2^2}$, $z=y_3$, and $\varphi$ for the cylindrical angle. The paper's compactified radial variable is $\sigma=|y|/(L+|y|)$. When the representation section calls this variable $s$, it means the same compactified radius. In Lean source, a variable named `σ` often denotes time instead. The mathematical role, rather than that identifier, determines which coordinate is meant.

The symbols $\mathcal H$, $X$, the perturbation domain, the weighted norm and the constraints are those used by the paper's Section 7. Each result below recalls the hypotheses needed at that step. A coefficient equality uses the precise fields constructed from the supplied data; changing a basis, a phase, a matrix orientation or a continuation outside a finite table changes the object to which the theorem applies.
<!-- /passage:sec-finitely-represented-data-and-universal-conditions -->

## How to read the source links

<!-- passage:sec-how-to-read-the-source-links -->

A **formal source** is a named declaration in the pinned Lean development. A **paper result** is identified by its Appendix B number and printed page. A **reconstruction** is the mathematical explanation given here of how the source proof works. A **checker requirement** describes an obligation for a future numerical implementation. None of those labels claims that the unreleased bytes have been checked in this account.

The actual proof declarations under `lean/Breakdown/` are used where available. Readable challenge files also contain theorem placeholders and are useful interfaces; those placeholders are not proof evidence.
<!-- /passage:sec-how-to-read-the-source-links -->

## Reading the encoded data

<!-- passage:sec-reading-the-encoded-data -->

Appendix B specifies mathematical objects and conditions on them. Its Lean interface fixes their meaning, including how they behave between sample points, at interfaces and at infinity. The certificate bytes and the program that interprets them are absent from this snapshot. The account below therefore specifies a semantic decoder: it tells an implementer which objects must be reconstructed and which identities must be preserved. It does not prescribe an undocumented byte order or file layout.

### The seven inputs must describe one instance

The root condition takes seven mutually dependent inputs. A decoder first fixes the number of parameter directions $k$, the finite class type $C$, and the numbers $n_E,n_M$ of multiplier pieces. It then constructs the following tuple.

| Input | Mathematical role | Principal declaration |
|---|---|---|
| $D$ | The extended certificate, reference field, multiplier weights, bounds, physical cells, local models, rows and pinning fields | `Breakdown.CertCell.CellLayerData` |
| $X$ | Representations of row fields, weights and compact forcing fields, with their common indexing | `Breakdown.CertCell.Instance.InstanceData` |
| $R$ | Cell layouts, analytic leaf forms, local polynomial decompositions and error budgets | `Breakdown.CertCell.CellCalculus.CellCalculusEntry` |
| $T$ | The finite matrix tree and the maps tying its coordinates to the cell problem | `Breakdown.CertCell.TreeEntry` |
| $Y$ | Assembly, coupling, row, omitted-mode and exterior data | `Breakdown.CertCell.CellLayerEntries` |
| $N$ | The multiplier bounds $\varepsilon_\infty,\varepsilon'_{\infty}$, the ratio bound and the accumulated global error | `Breakdown.CellLayerSystem.CoerciveNumbers` |
| $B$ | Approximate profile, pressure, adjoints, offset expansion, comparison bounds and potentials | `Breakdown.CellLayerSystem.ReductionEntries` |

The seven arguments of `CellSystemCondition` must be interpreted together, because the cell layouts, tree and assembly records are typed over the preceding data. In particular, a matrix check and a residual check must refer to the same parameter box, harmonic convention, coefficients and field functions. Acceptance must imply that decoding succeeded and that this one tuple satisfies all fifteen fields. Choosing a new existential witness independently for each descendant condition changes the proposition.

Some records already contain proofs. For example, a tree carries a family of admissible base points, and a nonnegative numerical quantity may have a proof in its type. A sound decoder may construct canonical values and establish their properties once, but reading the associated numbers alone does not supply those proofs.

### Coordinates, harmonics and normalisation

We use $\theta$ for period-one time, $\rho=|y|$ for spherical radius, $r=(y_1^2+y_2^2)^{1/2}$ for cylindrical radius, and

$$
s=\frac{\rho}{\rho+L},\qquad \eta=\frac{y_3}{\rho},\qquad
\rho=\frac{Ls}{1-s}.
$$

Here $s$ is the paper's compactified coordinate $\sigma$. Lean often uses the identifier `σ` for time instead. The distinction matters: radial spline knots lie in $[0,1]$, while the time variable ranges over a period. The formula for $\eta$ is interpreted through the source's total definition at the origin; regularity follows from amplitude conditions rather than from assigning an arbitrary direction there.

A lattice label $\iota=(\iota_1,\iota_2)$ denotes temporal frequency $2\iota_2-\iota_1$ and azimuthal frequency $\kappa\iota_1$. Thus

$$
E_\iota(\theta,\varphi)
 =\exp\!\left(i\{2\pi(2\iota_2-\iota_1)\theta+\kappa\iota_1\varphi\}\right).
$$

The general cell condition requires $\kappa\geq3$; the numerical experiment discussed in Appendix C uses $\kappa=19$. The maps `labelHarmonic`, `labelFlip` and `flipLabel` distinguish the two kinds of frequency pair. Reflection sends the lattice label to $(-\iota_1,\iota_2-\iota_1)$, whereas the corresponding physical pair $(j,n)$ goes to $(j,-n)$. These operations must not be interchanged merely because both pairs have the same Lean type.

A field key includes a further integer $\ell$ for radial phase. Its complete oscillatory factor is $E_\iota e^{i\ell f(\rho^2)}$. Negation of a key changes both $\iota$ and $\ell$; reflection changes $\iota$ and retains $\ell$. The source takes a finite sum and then its real part. A decoder that stores one representative from each conjugate pair must restore exactly that sum, including fixed points of the symmetry operations.

The mode projector averages over $\theta\in[0,1]$ and $\varphi\in[0,2\pi]$ with factor $1/(2\pi)$. Cylindrical spatial measure is $r\,dr\,dz\,d\varphi$. Reflection and conjugacy introduce additional factors in particular formulas, so there is no universal extra factor of two to attach to every stored mode.

### The divergence-free profile representation

The vector carried by one key is assembled in the radial direction $y/\rho$ and the two scaled tangent directions

$$
p=\left(\frac{\eta y_1}{\rho},\frac{\eta y_2}{\rho},-(1-\eta^2)\right),
\qquad a=\left(-\frac{y_2}{\rho},\frac{y_1}{\rho},0\right).
$$

These two tangent vectors have length $\sqrt{1-\eta^2}$, so replacing them by unit polar vectors changes the amplitudes. Introduce

$$
\mathcal V_\ell=s(1-s)\partial_s+2i\ell\rho^2f'(\rho^2).
$$

For a nonzero azimuthal label, two spline functions $A,B$ and integer orders $h_0\geq2$, $h\geq1$ determine

$$
u_0=s^{h_0}(1-s)^h(1-\eta^2)^2A,\qquad
u_1=s^{h_0}(1-s)^h(1-\eta^2)^2B,
$$

$$
u_2=\frac{i}{\kappa\iota_1}
 \left((\mathcal V_\ell+2)u_0
       -\partial_\eta\big((1-\eta^2)u_1\big)\right).
$$

For zero azimuthal label, put $p_h(s)=s(1-s)^h$ and $\Psi=\gamma g(s)\eta+S(s,\eta)$. The stream and swirl splines $S,T$ give

$$
u_0=-p_h\partial_\eta\big((1-\eta^2)\Psi\big),\qquad
u_1=-(\mathcal V_\ell+2)(p_h\Psi),\qquad
u_2=p_hT.
$$

The field is the real part of the sum of $E_\iota e^{i\ell f(\rho^2)}(u_0y/\rho+u_1p+u_2a)$. The constructor `reducedComps` enforces divergence freedom algebraically in each harmonic. In the first case, substitution cancels the bracket against $i\kappa\iota_1u_2$. In the second, the radial and polar differentiations commute and their two contributions cancel. The required joins and axis conditions then give a globally meaningful weakly divergence-free field.

The factors have separate jobs. Powers of $s$ control the origin, powers of $1-\eta^2$ control the polar axis, and powers of $1-s=L/(\rho+L)$ control spatial decay. The exceptional axis coefficient $\gamma$ records the allowed linear behaviour at the origin. It cannot be discarded as a coordinate singularity.

### Splines and jets

Each profile spline has its own product mesh in $[0,1]\times[-1,1]$. The knots are strictly increasing and include the four boundary values. A spline piece is a polynomial in the chart variables $s,\eta$, unless a separate constructor explicitly changes basis. The joins are polynomial identities along an entire edge. Spline evaluation assigns an internal knot to the interval on its right, while the final endpoint remains in the last interval; `cellIndex` implements this by counting internal knots below or equal to the coordinate.

| Amplitude | Joined orders in $s,\eta$ | Additional condition |
|---|---:|---|
| $A$ | $(2,1)$ | Used for nonzero azimuthal label |
| $B$ | $(1,2)$ | Used for nonzero azimuthal label |
| $S$ | $(2,2)$ | Vanishes at $s=0$; odd in $\eta$ |
| $T$ | $(1,1)$ | Vanishes at $s=0$; odd in $\eta$ |

These asymmetric orders reflect the derivatives used to reconstruct $u_2$ or the stream field. Integer temporal harmonics provide period-one dependence; the radial and polar spline endpoints are not identified periodically. `IsTimeFieldData` also requires the exact conjugation and reflection identities, the order restrictions and the origin cancellations.

The origin function $g$ is a polynomial up to a positive edge and constant thereafter, with $g(0)=1$. If the edge is below 1, its value and first two derivatives join the constant branch there. A radial phase is $C^3$ on a neighbourhood of the nonnegative axis, with bounded $x f'(x)$, $x^2f''(x)$ and $x^3f'''(x)$. The logarithmic phase has a separate analytic proof; it still needs its positive scale and the equality identifying the decoded phase with that constructor.

The Hermite representation uses two types of degrees of freedom: `node(k,p)` is a derivative of order $p$ at knot $k$, and `bubble(i,j)` is an interior coefficient on interval $i$. At depth $D$, the nodal orders are $0\leq p<D$. On the unit interval the left cardinal polynomial is

$$
h_{D,p}(t)=\frac{t^p(1-t)^D}{p!}
 \sum_{j=0}^{D-p-1}\binom{D-1+j}{j}t^j.
$$

On $[a,b]$, the left polynomial is $(b-a)^p h_{D,p}((x-a)/(b-a))$ and the right polynomial is $(a-b)^p h_{D,p}((b-x)/(b-a))$. The sign in the right scale converts derivatives back to the physical coordinate. Interior polynomials are

$$
((x-a)(b-x))^D\left(x-\frac{a+b}{2}\right)^j.
$$

Tensor products of the two one-dimensional bases reconstruct each spline piece. The constructor `JetSpline.toSpline` sums over the finite active degree-of-freedom sets, while its coefficient function is total on all pairs of degrees of freedom. A finite file therefore needs an explicit continuation, commonly exact zero outside the active table. The source's reflection maps reverse node and interval indices and attach $(-1)^p$ to derivative nodes and $(-1)^j$ to bubbles. Some support predicates quantify over all natural indices, so the continuation must also prove their out-of-range cases. In `VanishesBeyond`, a missing knot defaults to the support radius, which makes the relevant guard true and forces the associated coefficient to be exactly zero.

Scaled jets require another exact basis change before that reconstruction. At a node, derivative order $p$ is multiplied by the inverse $p$th power of the stored node scale. Bubble coefficients are converted through the coefficients of the symmetric Jacobi polynomial of degree $j$ and parameter $2D$, with the interval factors $(4/(b-a)^2)^D(2/(b-a))^s$ and the stored bubble normalisation. If $A_s,A_\eta$ are these two conversion matrices, the ordinary coefficient table is

$$
c(d,e)=\sum_{d',e'}A_s(d,d')A_\eta(e,e')\widehat c(d',e').
$$

`ScaledJetAxis.convert` fixes the orientation, signs, defaults and powers in this transformation. The scale list is required to have the right length and symmetry where used; that condition alone does not make each scale nonzero. Lean's inverse of zero is zero. A numerical implementation must reproduce the total operation or prove the extra nonzero premise before cancelling. Positive mesh widths are supplied by the validated knot order.

For integrals involving second derivatives, the reference-field route uses the specified `knotZeroHess` representative at spline seams. Its analytic relation to weak derivatives is a theorem about the joined representation. A decoder may use an almost-everywhere equal representative where the target proposition permits it; a pointwise identification needs the actual stated representative.

### Parameter dependence, pressure and compact support

The approximate profile uses a centre field, $k$ tangent fields and a common moving radial phase. Let $\chi$ be a $C^2$ piecewise polynomial on $[0,1]$, zero below an interior knot $s_*$ and identically one near 1. Set

$$
f_*(\rho^2)=\int_0^\rho\frac{\chi(t/(t+L))}{t}\,dt,
\qquad f_q=f+(a\cdot q)f_*.
$$

The field is affine in its stored amplitudes, evaluated using $f_q$. On $\rho\leq Ls_* /(1-s_*)$, the moving phase vanishes and the actual field is affine in $q$. Outside that ball, the phase makes the field nonlinear in $q$. This is why the offset proof expands the residual on the interior ball and treats the exterior separately.

`IsStepProfile` specifies the joins, exact zero pieces and final constant branch of this phase. With a validated mesh, its requirement of being one near 1 is equivalent to the last polynomial being identically one. This finite equivalence is an elementary decoder argument recorded in the earlier obligations return; it is not claimed here as a newly compiled Lean lemma. The existing `stepPhase_holds` theorem proves the analytic conclusion from the full `IsStepProfile` premise.

Pressure terms have the form $E_\iota e^{i\ell f_q(\rho^2)}s^{h_0}(1-s)^h(1-\eta^2)^aP$. The pressure spline is continuous, $h\geq2$, and nonzero azimuthal modes require $a\geq1$ together with either a radial factor or exact first-row vanishing. Zero azimuthal modes use $a=0$; if $h_0=0$, their first radial row is constant in $\eta$. These are the source's alternatives, which an implementation must preserve. The residual receives the gradient of this pressure minus $|W_q^a|^2/2$.

The reference profile is fixed across the parameter set. Forcing fields use the same divergence-free form, with zero axis coefficient on zero azimuthal modes and amplitudes vanishing beyond a chart edge below 1. Their physical support radius is $L s_b/(1-s_b)$. Adjoint fields are also fixed across the parameter set, with decay order at least 3. Neither compact support nor faster adjoint decay follows from a small coefficient on the final stored cell: the relevant vanishing and order statements are exact.

### Physical cells, row fields and matrices

A computational cell is a rectangle $[r_1,r_2]\times[z_1,z_2]$ in cylindrical coordinates, with $0\leq r_1<r_2$ and $0\leq z_1<z_2$. Its spatial solid includes the reflected points with $(r,|y_3|)$ in that rectangle. This mesh differs from each profile's compactified $(s,\eta)$ mesh. The cell polynomial constructor uses reference coordinates

$$
\widehat r=\frac{2r-r_1-r_2}{r_2-r_1},\qquad
\widehat z=\frac{2z-z_1-z_2}{z_2-z_1},
$$

and coefficients of $\widehat r^{\,i}\widehat z^{\,j}$. A derivative or a moment integral must include the resulting physical scale factors.

Each cell stores resolved, tested and band harmonic sets. Tested modes form a subset of resolved modes; band and resolved modes are disjoint. These sets are closed under negation. Axis cells resolve only zero azimuthal labels. The mesh stores a signed skeleton degree. The complete layout requires it to be at least 1 on resolved modes and at least 2 on tested modes, and the volume degree is at least the skeleton degree plus 2. A decoder must check this complete path rather than stopping after the weaker preliminary mesh guard.

`CellVecField.field` and `CellMatField.field` sum indicators of the closed cell solids. Cells are allowed to meet on sets of measure zero, so a seam may contribute from more than one cell to a pointwise value. Selecting an arbitrary owner at a seam yields the same integrals only after an almost-everywhere equality argument. It does not give literal equality of the defined functions.

The pinning matrices and local model polynomials carry harmonic labels and cylindrical component indices. For $z<0$, the label is flipped and a vector component receives the sign $(1,-1,-1)$; a matrix entry receives the product of its two component signs. Lean's matrix of a derivative has output index first. The paper's written gradient convention is its transpose. Complex matrices use conjugate transpose in Hermitian forms.

Row fields start from divergence-free polynomial triples in a cell. Their Gram blocks must be positive definite. The orthogonalisation uses the actual Gram matrix and row weights, so an arbitrary orthonormal basis with the same span is insufficient unless every transformed row and matrix is transported consistently. The generic cell construction also uses infinite orthogonal polynomial families. Their continuation is the source's proved orthogonal-family continuation; extending the finite prefix by zero would destroy orthogonality and positive leading coefficients.

The local leaf form acts on nine gradient entries and three velocity entries. Thus the analytic leaf matrix is $12\times12$ complex. Larger assembly matrices include resolved cell data, ports and two actuator blocks. Their index types and real/complex distinctions are part of the representation, not an implementation choice that can be forgotten after flattening.

### Weights and potential fields

The multiplier data divide the physical harmonics into finitely many classes. Class weights $D,Z$ are joined scalar fields; the skew weights $\lambda$ and $\mu$ have one and two powers of $1-s$, respectively. Auxiliary positive fields may be piecewise constant after their prescribed decay factor. Upper and lower half-charts are distinct, and the scalar constructors specify the value at the equator and at the origin. In particular, one lower-bound constructor takes a minimum of the two chart values on the equator.

The cell root fixes the constant energy weight $w=39/50$, coercivity $c=3/50$, pin weight $1000$, and the row bound $400(1+2^{-18})$. The physical mode sets for skew weights may be infinite sectors. A list of resolved cell modes is not an encoding of those sets. One needs a finite description and a proof of the stated frequency and coverage bounds on the entire set.

Potential fields use a separate helical component encoding. For base azimuthal order $n=\kappa\iota_1$, the plus, minus and axial components have orders $n+1,n-1,n$. The first two include $\sqrt{1-\eta^2}$. If their values are $g_+,g_-,g_z$, Cartesian components are $(g_++g_-)/2$, $(g_+-g_-)/(2i)$ and $g_z$.

A potential scalar multiplies its jet spline by powers of $s$, $1-s$ and $1-\eta^2$, as well as its oscillatory factor. Required origin and infinity orders may be supplied by these explicit powers or by exact vanishing of the appropriate jet rows. The alternatives are recorded in `IsPotentialSeries`; they should not be replaced by a single informal assertion of smoothness.

| Lean potential component | Paper object | Conditions supplied by the representation |
|---|---|---|
| `theta` | $G_j$ | $C^1$; effective origin order at least 2 and decay order at least 2 |
| `phi` | $U_j$ | $C^1$; effective origin order at least 2 and decay order at least 1 |
| `flux` | $F_j^{\mathsf T}$ under the paper's convention | Decay order at least 2 and the normal-flux joins needed for a weak divergence |
| `pressure` | $q_j$ | Continuous piecewise representation, origin/axis conditions and decay order at least 2 |

The radial flux has a joined radial axis; the polar flux has a joined polar axis. Those are the joins in the direction normal to each interface. Tangential jumps can be allowed because the integration-by-parts identity uses divergence. The analytic source theorems prove the weak derivative and decay properties from this representation. Numerical norm bounds for the particular coefficients are additional obligations.

### A decoder and checker that meet this interface

A sufficient implementation can proceed in the following order. These are design choices for a future checker, with source requirements stated separately from proposed finite reductions.

1. Decode exact integers and rationals, finite index types, knot lists, coefficients and dependency identifiers. Specify whether each interval encloses an exact value or a function range. A midpoint is an exact value only if the format defines it that way.
2. Construct total coefficient functions, including the correct continuation of every sparse or infinite family. Build harmonic symmetry closures, jets, profiles, pressure, weights, cells, bases and potentials through the named constructors.
3. Check structural identities exactly: knot order, polynomial joins, zero coefficients, support and mode membership, conjugation, reflection, assembly maps and matrix symmetry. Establish the analytic format lemmas whose hypotheses those checks supply.
4. Enclose numerical quantities on their full domains: every parameter in the box times ellipsoid, every point of each cell, all omitted harmonics and the unbounded exterior. Include interval endpoint cases, strict margins, tail integrability and the particular norms in the source.
5. Check matrix inequalities on the complete required spaces, then follow the fifteen-field dependency map. Record which expression, domain, threshold and strictness each numerical receipt establishes.

Affine parameter dependence permits a useful exact reduction. If $|q_i|\leq r_i$ for $i\in J$ and $\sum_{i\notin J}(s_iq_i)^2\leq R^2$ with nonzero $s_i$, then the extreme value of $\sum_i a_iq_i$ is

$$
\sum_{i\in J}|a_i|r_i+R\sqrt{\sum_{i\notin J}(a_i/s_i)^2}.
$$

The box endpoints and Cauchy-Schwarz give this formula. It applies to an affine reciprocal period, for example. The moving radial phase and most matrix expressions require other enclosures. Sampling the centre and coordinate extremes does not validate a general expression on the box times ellipsoid.

`InRowRange` includes more than the coordinates obtained by plugging in a cell solution. Gauge and pressure-head coefficients are complex, unused coordinates and ports remain free, and actuator coordinates are real. A matrix positivity test must account for all those directions, for example through the complete real generator matrix described in the earlier checker account.

Active model harmonics can be covered conservatively by taking the union of the four declared model supports. Omitting a mode requires exact vanishing of the relevant velocity, vorticity, strain and vorticity-gradient polynomials on that cell. An interval containing zero does not establish this identity. Likewise, an inconclusive interval sign test cannot become an acceptance branch.

The [certificate-checker page](../navier-stokes/certificate-checker.md), with its obligation map, decoder contract and finite reductions, provides the record-level expansion. They are useful alongside this account because they retain quantified domains, shared existential witnesses and the distinction between an implication's premises and its conclusion.
<!-- /passage:sec-reading-the-encoded-data -->

<a id="appendix-b.1"></a>

## B.1 The multiplier and its lower bound

<!-- passage:sec-appendix-b.1 -->

### Notation and the weak domain

Time has period one. Let $H=L^2((0,1)\times\mathbb R^3;\mathbb R^3)$, with the time-periodic interpretation, and let $H_{\rm div}$ be its closed solenoidal subspace. Spatial matrix fields use the Frobenius inner product. The space $X=\dot H^1_{\rm div}(\mathbb R^3)$ consists of divergence-free $L^6$ fields with gradient in $L^2$, with norm $\|\nabla u\|_2$. A perturbation belongs to $D_S$ when it is periodic, lies in $L^2_{\rm loc}(\mathbb R;X)$, and has $\Delta v,T_Sv\in H$, where

$$
T_Sv=S^{-1}\partial_\theta v+\tfrac12v+\tfrac12(y\cdot\nabla)v-\Delta v,
\qquad C^r_\alpha v=(W^r_\alpha\cdot\nabla)v+(v\cdot\nabla)W^r_\alpha.
$$

The superscript $\Gamma$ imposes the prescribed space-time symmetries. The source represents this domain by measurable periodic fields $v,G,H_2,g$, with $G$ and $H_2$ their weak first and second spatial derivatives and $g=S^{-1}\partial_\theta v+(v+y\cdot\nabla v)/2$. It assumes finite gradient, Laplacian and $g$ energies, the spatial $L^6$ condition almost everywhere in time, solenoidality and symmetry; the full Hessian energy follows from the weak div-curl identities.

For bounded $w\ge w_*>0$ and $\omega>0$, define

$$
\|v\|_w^2=\int_0^1\!\int\bigl(|\Delta v|^2+w|\nabla v|^2\bigr),\qquad
\|(v,\beta)\|_{w,\omega}^2=\|v\|_w^2+\omega^2|\beta|^2.
$$

The row seminorm is $[F]^2=\sum_j\langle F,e_j\rangle_H^2$, for the supplied orthogonal row fields. The pin functionals are $\ell_i(v)=\langle\nabla v,\Xi_i\rangle_H$. These quantities use the given $F$, which need not itself be divergence-free.

**Proposition B.1, rewritten from printed pages 55–56.** Put $c=3/50$. Fix a parameter $\alpha$, an admissible family of weights, and a perturbation $v\in D_{S(\alpha)}^\Gamma$ satisfying

$$
F\simeq T_{S(\alpha)}v+C^r_\alpha v+\sum_i\beta_i b_i.
$$

Here $\simeq$ means equality against divergence-free test fields. The multiplier of (B.14) exists in $H_{\mathrm{div}}$, its auxiliary seminorm is finite, and its norm satisfies the following bound.

$$
\|Mv\|_H\le c_M\bigl(c\|v\|_w^2+c_\mu\|v\|_\mu^2\bigr)^{1/2},
\qquad
c_M^2=\frac{(1+n_\lambda+n_{\nabla\lambda}/\sqrt{w_*})^2}{c}
       +\frac{n_\mu}{c_\mu}.
$$

If $I^-<\infty$, then $I^+<\infty$ and the following multiplier lower bound holds.

$$
\int_0^1\!\int_{\mathbb R^3}\left(\sum_\iota I_\iota+J\right)
\le \langle F,Mv\rangle_H-c\|v\|_w^2-c_\mu\|v\|_\mu^2
       -\sum_i\beta_i\langle b_i,Mv\rangle_H.
\tag{B.20}
$$

The integrals defining $I^+$ and $I^-$ take the positive and negative parts of each **whole mode density** $I_\iota$, together with those of $J$, before summing. This distinction matters when individual coefficients have opposite signs.

For clarity, write $u_\iota=\widehat v_\iota$ for the rotating-frame mode, and $\widehat\psi_\iota$ for that of a test field. The defining multiplier pairing and seminorm are given by the following formulas.

$$
\begin{aligned}
\langle Mv,\psi\rangle_H={}&\langle-\Delta v,\psi\rangle_H+
\sum_\iota\int_0^1\!\int\operatorname{Re}\left[
i\sum_{p\in P_\lambda}\operatorname{sgn}_p(\iota)\lambda_p\,
\operatorname{curl}u_\iota\cdot\overline{\operatorname{curl}\widehat\psi_\iota}
+i\sum_{p\in P_\mu}\operatorname{sgn}_p(\iota)\mu_p\,
u_\iota\cdot\overline{\widehat\psi_\iota}\right],\\
\|v\|_\mu^2={}&\sum_{p\in P_\mu,\iota}\int_0^1\!\int
|\operatorname{sgn}_p(\iota)|\,|\Omega_p(\iota)|\,\mu_p|u_\iota|^2.
\end{aligned}
$$

Here the sign is $1$ on $N_p$, $-1$ on $-N_p$ and zero elsewhere. The density is $I_\iota=I_{2,\iota}|\nabla^2u_\iota|^2+I'_{2,\iota}|\nabla\operatorname{curl}u_\iota|^2+I'_{1,\iota}|\operatorname{curl}u_\iota|^2+I_{1,\iota}|\nabla u_\iota|^2+I_{0,\iota}|u_\iota|^2$. With $S_W=(\nabla W^r+(\nabla W^r)^T)/2$ and $\omega_W=\operatorname{curl}W^r$, the remaining real density is

$$
J=-\operatorname{curl}v\cdot S_W\operatorname{curl}v
+((v\cdot\nabla)\omega_W)\cdot\operatorname{curl}v
+\tfrac12\sum_j\nabla(\omega_W)_j\cdot(v\times\partial_jv).
$$

Admissibility requires $0<c_\mu<1$, nonnegative piece weights, disjointness $N_p\cap(-N_p)=\varnothing$, and a positive lower bound for $\Omega_p$ on each $N_p$. The profile and transport bounds, the regularity and decay of the weights, and the nonnegativity of $I'_{2,\iota}$ must also hold. At every spatial point and for every mode, the multiplier-size bounds are the following three inequalities.

$$
\sum_{p\in P_\lambda}\lambda_p\le n_\lambda,
\qquad \sum_{p\in P_\lambda}|\nabla\lambda_p|\le n_{\nabla\lambda},
\qquad
\left(\sum_{p\in P_\mu}|\operatorname{sgn}_p(\iota)|\mu_p\right)^2
\le n_\mu\sum_{p\in P_\mu}|\operatorname{sgn}_p(\iota)|\,|\Omega_p(\iota)|\mu_p.
\tag{B.19}
$$

The same constants work for every $\alpha$. The signed sets exclude all forcing harmonics: in the paper's labels, no $N_p$ meets the box $|\iota_2|\le j_*$, $|\iota_2-\iota_1|\le j_*$ containing their supports.

### The five coefficients, including the omitted terms

The following formulas spell out the definitions used by the source. They also fix the allocation of every Young-inequality error. In these formulas the generic frequencies and rotating-frame frequency are related to the paper's labels by the following equations.

$$
\xi=(n,k)=(2\iota_2-\iota_1,\kappa\iota_1),
\qquad \Omega_p(\xi)=2\pi n/S+\nu_p k.
$$

Thus $\iota$ is a paper label and $\xi$ is the integer frequency pair used by the multiplier library. All mode sets and coefficient classes in the formulas below are read in the latter coordinates.

Let $\mathcal H$ be the finite reference frequency set. Write $W_b,G_b,O_b,V_b$ for the nonnegative bounds on its modes of $W^r,\nabla W^r,\operatorname{curl}W^r,\nabla\operatorname{curl}W^r$. Let $O,V$ bound the full vorticity norm and its gradient operator norm, and put $G_\Sigma=\sum_{b\in\mathcal H}G_b$. All these quantities depend on position. For a set $T$ disjoint from $-T$, define

$$
\begin{aligned}
\chi_T(\xi)&=\mathbf1_{T\cup(-T)}(\xi),\\
\operatorname{back}_T[A](\xi)&=\sum_{b\in\mathcal H:\,\xi-b\notin T}A_b,
&\operatorname{forward}_T[A](\xi)&=\sum_{b\in\mathcal H:\,\xi+b\in T}A_b,\\
\operatorname{in}_T[A](\xi)&=
\begin{cases}\operatorname{back}_T[A](\xi),&\xi\in T,\\
\operatorname{back}_T[A](-\xi),&-\xi\in T,\\0,&\text{otherwise},\end{cases}\\
\operatorname{out}_T[A](\xi)&=
\mathbf1_{\xi\notin T}\operatorname{forward}_T[A](\xi)
+\mathbf1_{-\xi\notin T}\operatorname{forward}_T[A](-\xi).
\end{aligned}
$$

These sums record the two ends of a reference-profile coupling which crosses the boundary of a multiplier set. They are finite even when $T$ is infinite. For a particular piece $p$, abbreviate them to $\operatorname{in}_p$ and $\operatorname{out}_p$, and write $\chi_p=\chi_{T_p}$.

For a curl piece, use the names $\lambda_p,s_p,a_p,b_p,d_p,\ell_p,t_{0p},t_{1p},t_{2p},t_{3p}$ for its weight, transport bound, two shares, scale, length and four positive Young parameters. For a velocity piece use $\mu_p,s_p,a_p,t_{4p},\eta_p$, with $\eta_p>0$. The source calls curl pieces `epsP` and velocity pieces `muP`. Set

$$
\widehat s_\xi=
\sum_{p\in P_\lambda}\left[
 a_p\chi_p\mathbf1_{\lambda_p+|\nabla\lambda_p|>0}
 +\frac{b_p}{d_p}\mathbf1_{\lambda_p>0}\operatorname{out}_p[W](\xi)
\right].
$$

Then the five coefficients are

$$
I_{2,\xi}=D_\xi-c,\qquad
I'_{2,\xi}=1-D_\xi-\widehat s_\xi,\qquad
I'_{1,\xi}=A_\xi-Z_\xi,\qquad
I_{1,\xi}=A^{\mathrm g}_\xi,\qquad I_{0,\xi}=B_\xi,
$$

where

$$
\begin{aligned}
A_\xi={}&\frac14+
\sum_{p\in P_\lambda}\chi_p\Bigg[
\lambda_p|\Omega_p|
-\frac{(\lambda_ps_p+|\nabla\lambda_p|)^2}{4a_p}
-\frac{\lambda_p^2d_p\operatorname{in}_p[W]}{4b_p}\\
&\hspace{20mm}-\lambda_p\left(
|\nu_p|+\frac{1+t_{0p}}2O+\frac{\ell_p}2V
+\frac{t_{1p}}2\operatorname{in}_p[G]
+\frac{t_{2p}}2\operatorname{in}_p[V]
+\frac{t_{3p}}2\operatorname{in}_p[O]\right)\Bigg]
-\sum_{p\in P_\lambda}\frac{\lambda_p\operatorname{out}_p[G]}{2t_{1p}},\\[1mm]
A^{\mathrm g}_\xi={}&Z_\xi-\|\nabla^2D_\xi\|_{\mathrm{op}}-cw
-\sum_{p\in P_\lambda}\lambda_p
 \left(\frac{\chi_p O}{2t_{0p}}+\frac{\operatorname{out}_p[O]}{2t_{3p}}\right)\\
&-\sum_{p\in P_\mu}\left[
\chi_p\mathbf1_{\mu_p+|\nabla\mu_p|>0}a_p
+\frac{\mu_p\operatorname{out}_p[W]}{2t_{4p}}\right],\\[1mm]
B_\xi={}&-\|\nabla^2Z_\xi\|_{\mathrm{op}}
-\sum_{p\in P_\lambda}\lambda_p
 \left(\frac{\chi_p V}{2\ell_p}+\frac{\operatorname{out}_p[V]}{2t_{2p}}\right)\\
&+\sum_{p\in P_\mu}\chi_p\Bigg[
(1-c_\mu)\mu_p|\Omega_p|
-\frac{(\mu_ps_p+|\nabla\mu_p|)^2}{4a_p}
-\mu_p|\nu_p|-\frac{t_{4p}\mu_p}2\operatorname{in}_p[W]
-\frac{\eta_p\mu_p^2}2\\
&\hspace{34mm}-\frac{G_\Sigma(G_\Sigma-\operatorname{in}_p[G])}{2\eta_p}
\Bigg]
-\sum_{p\in P_\mu}\frac{G_\Sigma\operatorname{out}_p[G]}{2\eta_p}.
\end{aligned}
$$

Every inward and outward quantity in this display is evaluated at $\xi$, and every function at the same spatial point. The support indicators in $\widehat s_\xi$ and $A^{\mathrm g}_\xi$ prevent a positive share from being charged where its weight and derivative both vanish. Admissibility includes $D_\xi\le1-\widehat s_\xi$, which is exactly the nonnegativity of $I'_{2,\xi}$. The above formulas are a mathematical transcription of the five coefficient definitions.

### Proof: finiteness and existence of the multiplier

Write $g=S^{-1}\partial_\theta v+\tfrac12v+\tfrac12(y\cdot\nabla)v$ in the weak sense. The perturbation space controls $g$, $\nabla v$, $\nabla^2v$ and $v/(1+|y|^2)^{1/2}$ in $L^2$. If a continuous nonnegative weight $q$ satisfies $q\le B$ and $|y|^2q\le B$, the differentiated mode identities and Parseval give

$$
\sum_{(n,k)\in\mathbb Z^2}(n^2+k^2)
 \int_0^1\!\int q|u_{n,k}|^2
\le B\left(2\left(\frac S{2\pi}\right)^2+4\right)
\int_0^1\!\int\left(|g|^2+|\nabla v|^2+
\frac{|v|^2}{1+|y|^2}\right)<\infty.
$$

For example, the time identity gives

$$
(2\pi n/S)^2|u_{n,k}|^2
\le2|\widehat g_{n,k}|^2+\tfrac12|y|^2|\widehat{\nabla v}_{n,k}|^2;
$$

the angular identity bounds the other frequency by the gradient and the damped velocity. Since $|n|\le n^2$ and $|k|\le k^2$ for integer frequencies,

$$
|\Omega_p(n,k)|\le(2\pi/S+|\nu_p|)(|n|+|k|)
$$

proves the finiteness of every velocity-piece seminorm. Summing the finitely many pieces proves $\|v\|_\mu<\infty$. This argument needs no unweighted $L^2$ bound on $\partial_\theta v$ separately.

For a smooth solenoidal test field $\psi$, integrate one curl by parts in the $\lambda$ part of (B.14). The resulting terms involve $\lambda_p\Delta u$ and $\nabla\lambda_p\times\operatorname{curl}u$. The three bounds in (B.19), Cauchy–Schwarz and Parseval give

$$
|\mathcal M_v(\psi)|
\le\bigl((1+n_\lambda)\|\Delta v\|_H
+n_{\nabla\lambda}\|\nabla v\|_H
+\sqrt{n_\mu}\|v\|_\mu\bigr)\|\psi\|_H.
$$

Density of these tests in $H_{\mathrm{div}}$ and the Riesz representation theorem give a unique representing field $Mv$. Since $w\ge w_*>0$, the expression in parentheses is at most

$$
(1+n_\lambda+n_{\nabla\lambda}/\sqrt{w_*})\|v\|_w
+\sqrt{n_\mu}\|v\|_\mu.
$$

Applying Cauchy–Schwarz to these two summands with weights $c,c_\mu$ gives the stated value of $c_M$.

### Proof: the lower bound and passage to weak fields

First use a smooth solenoidal perturbation of compact spatial support. Pairing the equation with $-\Delta v$ gives the following energy identity.

$$
\langle T_Sv+C^r_\alpha v,-\Delta v\rangle_H
=\int_0^1\!\int\left(|\nabla\operatorname{curl}v|^2
+\tfrac14|\operatorname{curl}v|^2+J\right).
$$

The time derivative integrates to zero by periodicity. The dilation and zeroth-order terms give the coefficient $1/4$; integration by parts in the profile terms gives precisely the three summands defining $J$. For a complex solenoidal field $u$ and a real smooth weight $Z$, two integrations by parts give

$$
\int Z\bigl(|\nabla u|^2-|\operatorname{curl}u|^2\bigr)
=\int\sum_{a,b}(\partial_a\partial_bZ)u_a\overline{u_b}.
$$

Taking real parts and using the Hessian operator norm bounds this last integral below by $-\int\|\nabla^2Z\|_{\mathrm{op}}|u|^2$. Applying the same identity to each derivative of $u$, with weight $D$, converts part of the curl-gradient energy into Hessian energy at a cost $\|\nabla^2D\|_{\mathrm{op}}|\nabla u|^2$. After subtracting $c\|v\|_w^2$, this yields the five displayed coefficients with their piece terms removed.

For each curl piece, curl the equation before pairing. The pressure disappears. In the rotating frame, the mode derivative contributes $\lambda_p\operatorname{sgn}_p(\xi)\Omega_p(\xi)|\operatorname{curl}u_\xi|^2$. Positive frequency on $T_p$ and oddness under $\xi\mapsto-\xi$ turn this into $\chi_p\lambda_p|\Omega_p||\operatorname{curl}u_\xi|^2$. For a velocity piece, use the projected equation and obtain the corresponding $\chi_p\mu_p|\Omega_p||u_\xi|^2$. Retain the fraction $c_\mu$ of the latter sum on the left of (B.20).

Here is the allocation of the remaining products. Put $X_c=|\nabla\operatorname{curl}u|$, $X_o=|\operatorname{curl}u|$, $X_g=|\nabla u|$, $X_v=|u|$. The transport and weight-derivative error of a curl piece is bounded by $(\lambda_ps_p+|\nabla\lambda_p|)X_cX_o$, and

$$
(\lambda_ps_p+|\nabla\lambda_p|)X_cX_o
\le a_pX_c^2+
\frac{(\lambda_ps_p+|\nabla\lambda_p|)^2}{4a_p}X_o^2.
$$

The analogous velocity-piece estimate replaces $(\lambda_p,X_c,X_o)$ by $(\mu_p,X_g,X_v)$. The within-piece products $\lambda_pOX_gX_o$ and $\lambda_pVX_vX_o$ are divided by

$$
XY\le\tfrac12(tX^2+t^{-1}Y^2)
$$

with $t=t_{0p}$ and $t=\ell_p$. The remaining diagonal costs are $\lambda_p(O/2+|\nu_p|)X_o^2$ and $\mu_p|\nu_p|X_v^2$.

For a crossing edge $\xi\in T_p$, $\xi-b\notin T_p$, the transport product is allocated by

$$
\lambda_pW_bX_{o,\xi}X_{c,\xi-b}
\le\frac{\lambda_p^2d_pW_b}{4b_p}X_{o,\xi}^2
+\frac{b_pW_b}{d_p}X_{c,\xi-b}^2.
$$

The three other curl-edge products use the same two-term inequality with the bounds $G_b,V_b,O_b$ and the parameters $t_{1p},t_{2p},t_{3p}$. The velocity-edge transport product uses $t_{4p}$. Reindexing each edge at its two endpoints produces exactly the inward and outward sums above. Finally, the projected velocity interaction is bounded with the parameter $\eta_p$ and

$$
\left|\sum_bG_b z_b\right|^2
\le G_\Sigma\sum_bG_b|z_b|^2.
$$

The retained endpoints contribute $G_\Sigma(G_\Sigma-\operatorname{in}_p[G])/(2\eta_p)$, the outside endpoints contribute $G_\Sigma\operatorname{out}_p[G]/(2\eta_p)$, and its other square contributes $\eta_p\mu_p^2/2$. This accounts for every term of $B_\xi$. All denominators are positive auxiliary parameters, and weights which vanish incur no share. Adding the allocations proves the smooth inequality.

The weak extension uses smooth solenoidal approximants converging in the gradient, Hessian, damped-velocity and transport norms. These are the norms needed by the integrations and by every product estimate above. The controlled error terms pass by strong $L^2$ convergence and Cauchy–Schwarz; the nonnegative frequency contributions pass by Fatou's lemma. The source keeps the positive and negative density integrals separate throughout this step. If $G_M$ denotes the real multiplier gap on the right of (B.20), the resulting statement is

$$
I^++(-G_M)_+\le(G_M)_++I^-.
$$

Thus $I^-<\infty$ forces $I^+<\infty$, and subtracting the two finite negative-part quantities gives $I^+-I^-\le G_M$. This proves (B.20), including its finiteness assertion. The forcing modes are excluded from all signed multiplier sets, so their skew pairings vanish and $\langle b_i,Mv\rangle_H=\langle\nabla b_i,\nabla v\rangle_H$.

The formal closure allows general symmetry sets and explicitly supplied weak Hessians, and states the density comparison in extended nonnegative reals. Its specialization and the finite-negative-part conversion above give the proposition in the paper's notation. No certificate values are supplied by this theorem.
<!-- /passage:sec-appendix-b.1 -->

<a id="appendix-b.2"></a>

## B.2 From the multiplier to the a priori estimate

<!-- passage:sec-appendix-b.2 -->

**Lemma B.2, rewritten from printed page 56.** Assume Proposition B.1 and the lower bound (B.21), with $t=1000$. Then the following a priori estimate holds.

$$
\|(v,\beta)\|_{w,\omega}
\le \frac{c_M}{\sqrt c}\|F\|_H+[F]+\sqrt{t/c}\,|\ell(v)|.
$$

Consequently the constants $c_1,c_2$ allowed by (B.22) give (7.18), uniformly in $\alpha$.

**Proof.** The finiteness supplied by B.1 permits ordinary addition of (B.20) and (B.21). Both the density integral and the actuator pairings cancel. Define

$$
P^2=c\bigl(\|v\|_w^2+\omega^2|\beta|^2\bigr)+c_\mu\|v\|_\mu^2,
\qquad Q^2=c[F]^2+t|\ell(v)|^2,
\qquad a=c_M\|F\|_H,
$$

Choose $P,Q\ge0$. Cauchy–Schwarz and $\|Mv\|_H\le c_MP$ imply $P^2\le aP+Q^2$. Completing the square gives the displayed bound.

$$
(P-a/2)^2\le Q^2+a^2/4\le(Q+a/2)^2,
\quad P\le a+Q\le a+\sqrt c[F]+\sqrt t|\ell(v)|.
$$

Since $\sqrt c\|(v,\beta)\|_{w,\omega}\le P$, division by $\sqrt c$ proves the claim. The independent requirement $c_0^2\ge(50/3)400(1+2^{-18})$ controls the norms of the orthogonal row fields; it is not used in this scalar completion of the square.
<!-- /passage:sec-appendix-b.2 -->

<a id="appendix-b.3"></a>

## B.3 Reduction to the quarter plane

<!-- passage:sec-appendix-b.3 -->

**Lemma B.3, rewritten from printed pages 56–57.** Under the flip symmetry of the coefficients and $I^-<\infty$, the full density integral equals the following quarter-plane expression.

$$
\int_0^1\!\int_{\mathbb R^3}\left(\sum_\iota I_\iota+J\right)
=4\pi\int_{r>0,z>0}\left(\sum_\iota I_\iota(r,z)+\overline J(r,z)\right)r\,dr\,dz.
\tag{B.23}
$$

The equality is interpreted through the separate positive and negative integrals if its positive side is infinite.

**Proof.** Equivariance of each mode makes the norms of its velocity, curl and derivatives independent of time and angle. Cylindrical integration therefore supplies a factor $2\pi$. Let $R_*={\rm diag}(1,-1,-1)$ and let

$$
\iota^\flat=(-\iota_1,\iota_2-\iota_1).
$$

This involution leaves $2\iota_2-\iota_1$ unchanged and reverses $\kappa\iota_1$. Mode covariance under $R_*$ and the coefficient symmetry give $I_\iota(r,-z)=I_{\iota^\flat}(r,z)$ almost everywhere. Relabelling the countable sum shows that its upper and lower half-space integrals agree. The rotation $R_*$ has determinant one, so gradients, curl and cross products transform covariantly; hence the full stretching expression is invariant, and its time-angle mean is even in $z$. This gives the second factor two.

Apply this argument to positive and negative parts before subtraction. Tonelli's theorem permits the nonnegative mode sums. Finiteness of the negative integral then makes the displayed extended difference meaningful. In the source, `labelFlip` acts on paper labels, whereas `flipLabel` acts on generic frequencies by $(n,k)\mapsto(n,-k)$; the bridge also proves that modes outside the symmetry lattice vanish.
<!-- /passage:sec-appendix-b.3 -->

<a id="appendix-b.4"></a>

## B.4 Cells, traces, tails and the exterior estimate

<!-- passage:sec-appendix-b.4 -->

**Proposition B.4, rewritten from printed pages 59–60.** Assume all cell, weight, charge, trace, row and assembly conditions of the appendix. Then $I^-<\infty$. On the complement of the cells,

$$
\overline J\ge-\sum_\iota L(\nabla u_\iota,u_\iota)\quad\hbox{almost everywhere},
\tag{B.32}
$$

where

$$
L(G,u)=s_1|\operatorname{curl}G|^2+
\sqrt{7/2}\,s_2|G||u|+
\frac{\sqrt{7/2}}2s_3\left(h|G|^2+\frac{|u|^2}{h}\right).
$$

If $I^+<\infty$, there is a physical vector $x_p$, containing $\beta$ and equal to zero for the zero perturbation and right-hand side, such that every free vector $x_f$ gives $x_g=(x_p,x_f)$ and real correction terms with

$$
\begin{aligned}
\langle A_QX_Qx_g,X_Qx_g\rangle+r_{Q,0}
+\sum_{\iota\text{ unresolved in }Q}\int_Q I_\iota^\circ r
\le\int_Q\left(\sum_\iota I_\iota+\overline J\right)r
+r_{Q,1}+r_{Q,2}+r_{Q,3}|\beta|^2.
\end{aligned}
\tag{B.33}
$$

The unresolved series here is absolutely convergent, and

$$
\begin{aligned}
\sum_Q(r_{Q,1}+r_{Q,2}+r_{Q,3}|\beta|^2-r_{Q,0})
+2\sum_\Pi\langle C_\Pi X_\Pi x_g,X_\Pi x_g\rangle\\
\le\frac{c[F]^2+\sum_i\beta_i\langle b_i,Mv\rangle_H
+2\zeta\cdot\ell(v)}{4\pi}+n_b|\beta|^2.
\end{aligned}
\tag{B.34}
$$

For a zero-azimuth mode, the square exterior $\{r>a\text{ or }z>a\}$ also satisfies (B.31) with constant $2$.

### Proof: integrability and the sharp stretching bound

The coefficient conditions give a mode-independent integrable majorant for negative density. More explicitly, for a fixed finite constant $C$ the negative part is bounded by

$$
(I_\iota)_-\le C\left(|\nabla^2u_\iota|^2+|\nabla u_\iota|^2+
\frac{|u_\iota|^2}{|y|^2}\right)
$$

almost everywhere away from $y=0$. Parseval and Hardy's inequality make its summed integral finite. The reference derivative bounds likewise bound the negative stretching by a constant times $|\nabla v|^2+|v|^2/|y|^2$: use $|\operatorname{curl}v|^2\le2|\nabla v|^2$ and Young's inequality on the velocity-gradient products. This proves $I^-<\infty$ before imposing any finite-positive-part hypothesis.

For the numerical constant in $L$, let $V=\nabla\operatorname{curl}W^r$. Its trace is zero. The two mixed stretching terms form a bilinear expression $\mathcal B_V(u,G)$ which can be written as the Frobenius product of $G$ with a matrix $K(V,u)$. The following kernel identity follows by expanding the alternating symbols.

$$
\|K(V,u)\|_F^2
=2|Vu|^2+u\cdot V^2u+\frac14\sum_{j=1}^3|V(e_j\times u)|^2.
$$

Because $\sum_j|e_j\times u|^2=2|u|^2$, this is at most

$$
\left(2+1+\tfrac12\right)\|V\|_{\mathrm{op}}^2|u|^2
=\tfrac72\|V\|_{\mathrm{op}}^2|u|^2.
$$

Cauchy–Schwarz now gives $|\mathcal B_V(u,G)|\le\sqrt{7/2}\|V\|_{\mathrm{op}}|u||G|$. For complex modes, split real and imaginary parts and apply Cauchy–Schwarz to their two norms; this retains the same constant. The required factor is $\sqrt{7/2}$.

The polynomial model of $V$ used inside a cell may have nonzero trace. Its mixed stretching estimate therefore uses the general constant $\sqrt{9/2}=3/\sqrt2$. Indeed, the first mixed term is bounded by $\sqrt2\|V\|_{\mathrm{op}}|u||G|$ using the curl inequality, and the cross-product term by $\|V\|_{\mathrm{op}}|u||G|/\sqrt2$ using $\sum_j|e_j\times u|^2=2|u|^2$. Their sum gives $\sqrt{9/2}$. For a symmetrized interaction between two different pairs $(u,G),(u',G')$, the corresponding bound is

$$
\sigma|\operatorname{curl}G||\operatorname{curl}G'|
+\frac{3\gamma}{2\sqrt2}\bigl(|u||G'|+|u'||G|\bigr),
$$

Here $\sigma$ and $\gamma$ bound the model strain and vorticity-gradient operators. Young's inequality gives the following diagonal charge.

$$
\sigma|\operatorname{curl}G|^2+
\frac{3\gamma}{2\sqrt2}\left(\ell|G|^2+\frac{|u|^2}{\ell}\right),
\qquad \frac{3}{2\sqrt2}=\frac12\sqrt{9/2}.
$$

These are the constants in the source's model and model-error charges. A grouped wave may use the smaller value $\sqrt{7/2}$ only when its complete vorticity-gradient wave has zero trace at every point and angle. The potential conditions explicitly require that trace identity whenever the smaller group constant is selected; they otherwise allow $\sqrt{9/2}$. This is the coefficient distinction made in the paper's discussion after B.14 on printed page 70.

Split $V$ in the cylindrical frame into its time-angle mean and its oscillatory part. For the mean, Parseval makes the pairing diagonal in the modes and gives the $s_2|G||u|$ term. For the oscillatory part, apply the pointwise bound followed by $|G||u|\le(h|G|^2+h^{-1}|u|^2)/2$, then average and use Parseval. The strain term is bounded below by $-s_1|\operatorname{curl}v|^2$. These three estimates prove (B.32).

### Proof: constructing a common vector of unknowns

The weak equation determines a pressure gradient: its residual annihilates all compactly supported solenoidal tests, hence is a distributional gradient. In the implementation the pressure object is this vector field, with a local scalar potential used to define pressure moments. Average the right-hand side under the flip symmetry when necessary. This preserves the tested row and multiplier pairings and supplies the pressure symmetry needed at $z=0$.

The weak Hessian regularity gives the local Sobolev modes, side traces and corner data required by the cell layouts. On axis cells only zero-azimuth harmonics are resolved; the cylindrical components and their weighted regularity supply the corresponding axis traces. Conjugation, reflection, shared-side continuity and the divergence identity yield the declared linear relations between these data. They express the physical moments through one real vector $x_p$, with the prescribed entries $\beta$.

Changing a pressure potential adds constant-pressure directions. The chosen global data and the local moment vectors can therefore differ by gauge and pressure-head shifts. The conditions require the relevant cell forms to annihilate these directions, so their quadratic values agree. This establishes the cell-state relation for every choice of free port and $\zeta$ coordinates. The construction at the zero tuple has $x_p=0$; this separate assertion is needed later in B.8.

### Proof: the resolved modes and the full tail budget

For a resolved mode, let $P_du$ denote the polynomial data retained by the layout, with degree $d$ for its gradient and degree $d-1$ for its velocity. Write the actual fields as these polynomials plus their orthogonal remainders. Orthogonality is with the prescribed tensor product cell bases and their measures; away from the axis some tail norms use the unweighted rectangular measure, while the physical integrals use $r\,dr\,dz$.

The local Hermitian $12\times12$ bound compares the lower-order density to a quadratic form on $(G,u)$. Together with the Hessian and curl-gradient floors, its integrated polynomial part is the energy leaf $E_Q$. Thus the true resolved energy is at least the value of $E_Q$ plus the still available derivative-tail energy. Expanding $\overline J$ separates polynomial couplings, interactions with tails, and unresolved or eliminated modes. The finite profile harmonics identify all coupled pairs. The polynomial models give $P_Q$; their certified errors and the remaining interactions are bounded by the allocated curl, gradient and velocity charges.

Here is the scalar inequality which absorbs those remainder charges. It is useful because it states all terms suppressed by the paper's summary of (B.27). Let $H_T,C_T,G_T,O_T,U_T$ be the nonnegative squared Hessian, curl-gradient, gradient, curl and velocity tail quantities in the source normalization. Let $L_T$ be the retained top-degree velocity allowance. The polynomial spectral estimates give

$$
H_T\ge g_HG_T,\qquad C_T\ge g_CO_T,\qquad O_T\le2G_T,
\qquad U_T\le L_T+G_T/g_U.
$$

For the box $Q=[r_1,r_2]\times[z_1,z_2]$, put $r_*=r_1$ when $r_1>0$ and $r_*=1$ on an axis box. In this normalization,

$$
\begin{aligned}
g_H&=r_*\min(\Lambda^r_{d+1},\Lambda^z_{d+1})+
       \frac{(|k|-2)_+^2}{r_2},\\
g_C&=r_*\min(\Lambda^r_{d+1},\Lambda^z_{d+1})+
       \frac{(|k|-1)_+^2}{r_2},\qquad
g_U=\min(\Lambda^r_d,\Lambda^z_d),
\end{aligned}
$$

where $\Lambda^r_j=j(j+1)(2/(r_2-r_1))^2$ off the axis, $\Lambda^r_j=j(j+2)(2/r_2)^2$ on it, and $\Lambda^z_j=j(j+1)(2/(z_2-z_1))^2$. These follow by expanding the polynomial tail in the corresponding Legendre or Jacobi basis and retaining its first allowed eigenvalue; the angular contribution is the tensor version of B.5. The top allowance appears because velocity and gradient are truncated at different degrees.

Write the Hessian and curl-gradient floors as $h_0,c_0\ge0$. Let $a_o,a_g,a_u$ be the absorption charges; let $p_g,p_u$ be potential charges, $l_g,l_u$ local leakage charges, and $l_*$ the global leakage charge. Define

$$
E_u=\max(a_u+p_u+l_u,0),\qquad
E_o=\max(a_o-c_0g_C,0).
$$

The complete tail condition is the following scalar inequality.

$$
a_g+p_g+l_g+l_*+2E_o+E_u/g_U\le h_0g_H.
$$

The four tail estimates and this condition imply the following absorption bound.

$$
\begin{aligned}
&h_0H_T+c_0C_T-a_oO_T
-(a_g+p_g+l_g+l_*)G_T-(a_u+p_u+l_u)U_T\\
&\hspace{20mm}\ge
\bigl(h_0g_H-a_g-p_g-l_g-l_*-2E_o-E_u/g_U\bigr)G_T-E_uL_T
\ge-E_uL_T.
\end{aligned}
$$

The top-block condition pays for $E_uL_T$ through $T_Q$. This proves absorption including the cases where one combined velocity or curl charge is negative.

Eliminated modes have nonzero azimuth. Their angular identity expresses the required velocity variables through angular derivatives, and the elimination condition completes squares pointwise. Its basic two-stage estimate uses a weight $w>0$ and $0\le\vartheta<1$: one square has weight $w\vartheta$ and the other has weight $w(1-\vartheta)$. The former divides a model residual $s-w\mu$ by $w\vartheta$. At $\vartheta=0$, the condition explicitly requires $s=w\mu$, so the residual square vanishes and no division is needed. Integrating this estimate produces $b_Q$ and the prescribed leakage charges. This is why a nonzero-azimuth condition and the zero-parameter residual condition both belong to the finite data.

For the row fields, integration by parts in the equation against their divergence-free polynomial triples expresses $\langle F,\varphi\rangle$ in terms of the retained moments, pressure-side terms and controlled remainders. The model-error bounds, row removal and row moment expansion give $e_Q$ and their tail charges. Combine these bounds with

$$
\langle(A_Q-E_Q)x,x\rangle
\le\langle(P_Q+B_Q-T_Q)x,x\rangle+b_Q(x)+e_Q(x)
$$

on the permitted cell-state range. Every remainder is now either absorbed in the tail inequality or included in the explicit correction terms below. This proves the local density comparison.

### Proof: choosing the four corrections and summing them

The four corrections have a concrete choice. Let $F^\sharp$ be the flip-symmetric right-hand side used to recover pressure. Write $\widetilde B_{i,\iota}$ for the supplied gradient profile paired with $\beta_i$ and $\widetilde\Xi_{i,\iota}$ for that paired with $2\zeta_i$. Put

$$
\begin{aligned}
S_Q&=\sum_{\iota\in\mathcal S_Q}w_{Q,\iota}
          \int_Q|\nabla u_\iota|^2r,\\
P_Q^{\rm pair}&=\sum_{i,\iota}\int_Q
\operatorname{Re}\left(\nabla u_\iota:
\overline{\beta_i\widetilde B_{i,\iota}+2\zeta_i\widetilde\Xi_{i,\iota}}\right)r,\\
R_Q^{\rm row}&=\sum_{\iota\text{ tested}}\gamma_{Q,\iota}\,
          m_{Q,\iota}(F^\sharp)^*G_{Q,\iota}^{-1}m_{Q,\iota}(F^\sharp),\\
C_Q^{\rm credit}&=\sum_\Pi\int_{\Pi\cap Q}a_\Pi
 \bigl(|u_{\iota_\Pi^\flat}|^2+|u_{-\iota_\Pi^\flat}|^2\bigr)r.
\end{aligned}
$$

Here $G_{Q,\iota}$ is the tested-block Gram matrix, $m$ its moment vector, and the coefficient in $R_Q^{\rm row}$ is the stored `testWeight`, with the normalization built into the row construction. The index sets and slack weights in $S_Q$ are supplied by the pairing conditions. Choose the four correction terms as follows.

$$
r_{Q,0}=S_Q+C_Q^{\rm credit},\qquad
r_{Q,1}=R_Q^{\rm row},\qquad
r_{Q,2}=P_Q^{\rm pair},\qquad
r_{Q,3}=\text{the stored cell actuator cost}.
$$

The local comparison just proved is exactly (B.33) with these choices. The separate positive and negative integral bounds in the source imply its real form when $I^+<\infty$; the coefficient and charge integrability also give absolute convergence of the unresolved series.

The global sum has three checks. First, Gram normalization of the row fields gives the following exact sum.

$$
\sum_QR_Q^{\rm row}=\frac{c[F]^2}{4\pi}.
$$

Flip averaging leaves their moments unchanged. Second, if the supplied actuator gradient is a surrogate, its error $d_i$ satisfies the pointwise estimate

$$
\sum_i\beta_i\operatorname{Re}(G:\overline{d_i})
\le w|G|^2+\frac{|\beta|^2}{4w}\sum_i|d_i|^2.
$$

The first term is precisely pairing slack. Integration, the exact pin pairing, and the actuator integration-by-parts identity yield the following global pairing bound.

$$
\sum_Q(P_Q^{\rm pair}-S_Q)
\le\frac{\sum_i\beta_i\langle b_i,Mv\rangle_H+2\zeta\cdot\ell(v)}{4\pi}
+e_{\rm pair}|\beta|^2.
$$

Third, consider a credit rectangle and its scalar test functions $\phi_l$, which vanish on the other three sides. For azimuth $k$, their full modal gradient has components $(\partial_r\phi_l,ik\phi_l/r,\partial_z\phi_l)$, with the conjugate sign in the dual pairing. Divergence-free integration by parts represents the selected normal-trace moments by the pairing with this full gradient. In particular the Dirichlet bound includes $k^2|\phi_l|^2/r^2$. If the matrix $H_\Pi$ bounds the Gram form with weight $a_\Pi^{-1}r$, then for every vector $a$,

$$
|a^*m|^2\le(a^*H_\Pi a)\int_\Pi a_\Pi|u|^2r,
\qquad m^*H_\Pi^{-1}m\le\int_\Pi a_\Pi|u|^2r.
$$

The inverse comparison for $C_\Pi$ gives the credit bound. On $z=0$, the normal component of $u_{\iota^\flat}$ is the negative of that of $u_\iota$, and conjugation gives equal energies for opposite modes. Thus the following total credit bound holds.

$$
2\sum_\Pi\langle C_\Pi X_\Pi x_g,X_\Pi x_g\rangle
\le\sum_Q C_Q^{\rm credit}.
$$

These credits are charged to modes excluded from both the resolved and eliminated sets, and the same debit is present in their $a_0$ term. Thus the allocation consumes the stated energy once. Adding the three checks and the input bound $\sum_Qr_{Q,3}+e_{\rm pair}\le n_b$ proves (B.34).

### Proof: constant two on a square exterior

Let $\rho^2=r^2+z^2$ and $Z=\{r>a\text{ or }z>a\}$ in the quarter plane. For a zero-azimuth vector mode the radial and angular components vanish on the axis, and its axial component vanishes on $z=0$. Use the positive comparison functions

$$
h_r=r/\rho^2,\qquad h_z=z/\rho^2.
$$

They satisfy

$$
\left(-\partial_{rr}-r^{-1}\partial_r-\partial_{zz}+r^{-2}\right)h_r
=2h_r/\rho^2,
\qquad
\left(-\partial_{rr}-r^{-1}\partial_r-\partial_{zz}\right)h_z
=2h_z/\rho^2.
$$

For either component $f$, with $q=r^{-2}$ or $q=0$ as appropriate, completing the square and integrating gives

$$
\int_Zr\left(|\nabla f|^2+q|f|^2-2|f|^2/\rho^2\right)
=\int_Zrh^2|\nabla(f/h)|^2
+\int_{\partial Z}r|f|^2\frac{\partial_nh}{h}.
$$

On the two inner square edges the normal points into the removed square, and direct differentiation gives $\partial_nh\ge0$ for both $h_r$ and $h_z$. The axis and plane terms vanish by the indicated component boundary conditions. For compactly supported smooth modes there is no boundary term at infinity. Summing the two transverse components and the axial component yields

$$
2\int_Z|u|^2\rho^{-2}r\le\int_Z|\nabla u|^2r;
$$

the transverse $r^{-2}$ terms are exactly the cylindrical contributions to the Cartesian gradient norm. Symmetry-preserving approximation and the finite gradient and inverse-square energies extend the result to the perturbation modes. This proves the last assertion.

The implementation establishes these components through the cell assembly, pressure, gauge, row, credit and exterior closures. The closed component package has additional structured entry hypotheses and no single declaration with the paper's literal B.4 statement. The proof above specializes those components and supplies the explicit corrections; it does not produce the unreleased numerical entries that must satisfy their conditions.
<!-- /passage:sec-appendix-b.4 -->

<a id="appendix-b.5"></a>

## B.5 Angular inequalities and the pointwise test

<!-- passage:sec-appendix-b.5 -->

**Lemma B.5, rewritten from printed pages 60–61.** For $u=u_\iota$ and $k=\kappa\iota_1$, the following four inequalities hold almost everywhere in the quarter plane.

$$
\begin{gathered}
|\operatorname{curl}u|^2\le2|\nabla u|^2,\qquad
(|k|-1)_+|u|\le r|\nabla u|,\\
(|k|-2)_+|\nabla u|\le r|\nabla^2u|,\qquad
(|k|-1)_+|\operatorname{curl}u|\le r|\nabla\operatorname{curl}u|.
\end{gathered}
\tag{B.35}
$$

Let a region have a common lower azimuth bound $k_0\le|k|$ and coefficient lower bounds. After subtracting its stretching and other charges, call the resulting bounds $f_2,f'_2,f'_1,f_1,f_0$, and call the velocity-gradient cross bound $f_{01}$. Explicitly,

$$
f_2=\underline I_2,\quad f'_2=\underline I'_2,\quad
f'_1=\underline I'_1-s_1-a_{01},\quad
f_1=\underline I_1-\tfrac12c_*s_3h-a_1,\quad
f_0=\underline I_0-\tfrac{c_*s_3}{2h}-a_0,\quad f_{01}=c_*s_2,
$$

where $c_*\ge\sqrt{7/2}$. Put

$$
q_1=(k_0-1)_+^2/r^2,\qquad q_2=(k_0-2)_+^2/r^2,
\qquad f_1^*=f_1+2\min(f'_1+f'_2q_1,0)+f_2q_2.
$$

If $f_2\ge0$, the charged density satisfies the following lower bound.

$$
I_\iota^\circ\ge f_1^*|\nabla u|^2+f_0|u|^2-f_{01}|\nabla u||u|.
\tag{B.36}
$$

If some $t\ge0$ satisfies $t\le f_1^*$, $f_0^*=f_0+tq_1\ge0$ and $f_{01}^2\le4(f_1^*-t)f_0^*$, this is nonnegative.

**Proof.** The curl inequality follows by applying $(a-b)^2\le2(a^2+b^2)$ to its three components. Differentiate the rotational covariance of $u$. With $Ju=e_z\times u$ this gives $r\partial_{e_\varphi}u=iku+Ju$. Since $\|J\|_{\mathrm{op}}=1$, the reverse triangle inequality proves the velocity bound. For $G=\nabla u$, differentiating its two-index covariance gives the commutator $JG-GJ$; its Frobenius norm is at most $2|G|$. This proves the Hessian bound. Curl transforms as a vector, so the velocity argument also applies to $\operatorname{curl}u$. Smooth approximation gives all four statements for the weak derivatives.

The Hessian term contributes at least $f_2q_2|\nabla u|^2$. If $f'_2\ge0$, the curl-gradient term contributes at least $f'_2q_1|\operatorname{curl}u|^2$. If $f'_2<0$, its **actual** coefficient remains nonnegative by admissibility, so the same lower estimate follows from $0\ge f'_2q_1|\operatorname{curl}u|^2$. This branch is needed when a valid interval lower bound is negative. Add the curl coefficient and use $|\operatorname{curl}u|^2\le2|\nabla u|^2$ only for its negative part. The result is (B.36).

Move $t|\nabla u|^2$ to the velocity term using $|\nabla u|^2\ge q_1|u|^2$. It remains to prove nonnegativity of

$$
A X^2+B Y^2-CXY,
\quad A=f_1^*-t,\ B=f_0^*,\ C=f_{01},\ X=|\nabla u|,\ Y=|u|.
$$

If $A=0$, the condition $C^2\le4AB$ gives $C=0$. If $A>0$, multiply by $4A$ to obtain $(2AX-CY)^2+(4AB-C^2)Y^2\ge0$. This proves the pointwise test without excluding zero boundary cases.
<!-- /passage:sec-appendix-b.5 -->

<a id="appendix-b.6"></a>

## B.6 Ray exteriors and the integrated test

<!-- passage:sec-appendix-b.6 -->

**Lemma B.6, rewritten from printed page 61.** Let $Z$ be a radial exterior in the quarter plane. In the formal conditions its directional radius is measurable, constant on positive rays, and bounded between positive finite constants. Every mode of azimuth $k$ satisfies the following inverse-square estimate.

$$
\left(\tfrac14+(|k|-1)_+^2\right)
\int_Z\frac{|u|^2}{\rho^2}r\,dr\,dz
\le\int_Z|\nabla u|^2r\,dr\,dz.
$$

For a common lower azimuth bound $k_0$, one may therefore use any $0<\Lambda_0\le\tfrac14+(k_0-1)_+^2$. For the integrated test, impose the following coefficient bounds.

$$
f_2\ge0,\quad f_1^*\ge f_1^\infty,\quad
\rho^2\max(-f_0,0)\le f_0^\infty,\quad
\rho f_{01}\le f_{01}^\infty,
\qquad
\frac{f_0^\infty}{\Lambda_0}+
\frac{f_{01}^\infty}{\sqrt{\Lambda_0}}\le f_1^\infty,
\tag{B.30}
$$

Assume the displayed bounds with nonnegative constants $f_0^\infty,f_{01}^\infty$. Then the negative part of $I_\iota^\circ$ is integrable on $Z$, and the integral of $I_\iota^\circ$ is nonnegative, allowing the value $+\infty$.

**Proof.** On one ray starting at radius $a>0$, integration by parts and Cauchy–Schwarz give the following inequality for a smooth compactly supported scalar function.

$$
\int_a^\infty|U|^2\,d\rho
=-a|U(a)|^2-2\operatorname{Re}\int_a^\infty\rho\overline U U'\,d\rho
\le2\left(\int_a^\infty|U|^2\right)^{1/2}
       \left(\int_a^\infty\rho^2|U'|^2\right)^{1/2}.
$$

If the first integral is nonzero, division and squaring give the constant four; if it is zero, the assertion holds directly. In polar coordinates on the quarter plane, $r\,dr\,dz=\rho^2\sin\vartheta\,d\rho\,d\vartheta$. Integrating this one-dimensional estimate over directions therefore gives the inverse-square constant $1/4$ for the radial derivative. The angular direction is orthogonal to the radial direction, and B.5 gives $|\partial_{e_\varphi}u|^2\ge(|k|-1)_+^2|u|^2/r^2\ge(|k|-1)_+^2|u|^2/\rho^2$. Adding the two estimates proves the first claim. Density and Fatou extend it to the Sobolev modes.

By B.5 and the exterior bounds,

$$
I_\iota^\circ\ge f_1^\infty|\nabla u|^2
-f_0^\infty|u|^2/\rho^2-f_{01}^\infty|\nabla u||u|/\rho.
$$

Young's inequality with $\sqrt{\Lambda_0}$ rewrites this lower bound as

$$
\left(f_1^\infty-\frac{f_{01}^\infty}{2\sqrt{\Lambda_0}}\right)|\nabla u|^2
-\left(f_0^\infty+\frac{\sqrt{\Lambda_0}f_{01}^\infty}{2}\right)|u|^2/\rho^2.
$$

Its two terms are integrable. In particular its negative part dominates the negative part of $I_\iota^\circ$. Integrating and applying the inverse-square inequality gives a lower bound

$$
\left(f_1^\infty-\frac{f_{01}^\infty}{\sqrt{\Lambda_0}}
-\frac{f_0^\infty}{\Lambda_0}\right)\int_Z|\nabla u|^2r\ge0.
$$

The coefficient condition also makes the preceding gradient coefficient nonnegative, so all comparisons retain their direction. The same integrated argument applies to a zero-azimuth square exterior with the value $\Lambda_0=2$ proved in B.4.
<!-- /passage:sec-appendix-b.6 -->

<a id="appendix-b.7"></a>

## B.7 The matrix tree lower bound

<!-- passage:sec-appendix-b.7 -->

**Lemma B.7, rewritten from printed pages 62–63.** Suppose the real or complex node enclosure conditions, positive pivot coverage and nonnegative root-front condition hold. If $N$ is the sum of the attached leaf matrices, including cancelling signed pairs, then the following lower bound holds for every real global vector $x$.

$$
\langle Nx,x\rangle\ge
\sum_\xi\left(\sum_{j\in U_\xi}p_{\xi,j}x_j^2-|Y_\xi^Tx|^2\right).
\tag{B.41}
$$

It is strictly positive on every nonzero vector orthogonal to all columns of the $Y_\xi$.

**Proof for a real node.** Suppress its index. Define the symmetric remainder

$$
B=H-\operatorname{diag}_{U}(p)-Y'Y'^T+YY^T-K,
\qquad E=H^0+K^0.
$$

The entrywise error matrices have nonnegative entries, and the node condition is

$$
w_i\sum_j\frac{|B_{ij}|+E_{ij}}{w_j}\le m_i,\qquad w_i>0.
$$

Apply the following weighted Young inequality to each pair of coordinates.

$$
2|x_ix_j|\le(w_i/w_j)x_i^2+(w_j/w_i)x_j^2.
$$

Symmetry permits exchange of $i,j$ in one of the double sums, giving

$$
-\langle Bx,x\rangle+\langle E|x|,|x|\rangle
\le\sum_{i,j}(|B_{ij}|+E_{ij})(w_i/w_j)x_i^2
\le\sum_i m_ix_i^2.
$$

Insert the definition of $B$, discard the nonnegative term $|Y'^Tx|^2$, and combine the input and output enclosure comparisons. The nonpivot $m_i x_i^2$ terms cancel against the corresponding output-front allowance. The pivot terms leave $(p_i-m_i)x_i^2\ge p_{\xi,i}x_i^2$. Thus, with $V_\xi$ the outgoing front,

$$
\langle N_\xi x,x\rangle+\sum_{\xi'\text{ child of }\xi}\langle V_{\xi'}x,x\rangle
\ge\langle V_\xi x,x\rangle+
\sum_{j\in U_\xi}p_{\xi,j}x_j^2-|Y_\xi^Tx|^2.
\tag{B.42}
$$

**Complex coordinates.** Repeat the same calculation with Hermitian forms, moduli and adjoints at $z=X_\xi x$, then multiply by $t_\xi\ge0$. A pivot coordinate is $x_j\pm ix_{j'}$, with distinct indices when both occur, so $|z_l|^2$ is the sum of the corresponding real squares. The coordinate-slack condition therefore yields the prescribed real pivot gain. Each complex loss column $y$ splits into two real squares as follows.

$$
t_\xi|y^*X_\xi x|^2
=\bigl(x\cdot\operatorname{Re}(\sqrt{t_\xi}X_\xi^*y)\bigr)^2
+\bigl(x\cdot\operatorname{Im}(\sqrt{t_\xi}X_\xi^*y)\bigr)^2.
$$

The two real columns on the right are included as separate indexed columns of $Y_\xi$. They need not be linearly independent. This distinction preserves the column count used later. The complex node therefore also satisfies (B.42).

Finally sum (B.42) over the finite nodes. Each nonroot front occurs once as an output and once as a child input; these contributions cancel exactly. The root front remains on the right and is nonnegative. The signed auxiliary leaves cancel in the total attached matrix, leaving the matrix $N$ of (B.38). This proves (B.41). If all loss-column pairings vanish and $x\ne0$, choose a nonzero coordinate $x_j$. Some node pivots that coordinate with $p_{\xi,j}>0$, so the remaining sum of pivot squares is strictly positive. The bound on the total number of loss columns is used in B.8. The last positivity argument uses pivot coverage.
<!-- /passage:sec-appendix-b.7 -->

<a id="appendix-b.8"></a>

## B.8 From all cells to the global inequality

<!-- passage:sec-appendix-b.8 -->

**Result and scope.** Assume the shape, cell, exterior, coupling, error, global-matrix and tree conditions of Appendix B. For every admissible parameter $\alpha$, perturbation $v$, multiplier vector $\beta$ and forcing representative $F$ in (7.18), the negative part $I^-$ is finite, and

$$
\int_0^1\!\int_{\mathbb R^3}
 \left(\sum_\iota I_\iota+J\right)
\geq \frac3{50}\omega^2|\beta|^2
 -\sum_i\beta_i\langle b_i,Mv\rangle_H
 -\frac3{50}[F]^2-1000|\ell(v)|^2.
\tag{B.8-R}
$$

Under these hypotheses, the global inequality (B.8-R) holds and $I^-$ is finite. Here $[F]$, $M$, $I_\iota$, $J$ and the physical coordinates $x_p$ are those already defined in B.2–B.4. The result concerns the assembled data for a fixed perturbation, while the free global coordinates remain available for the final linear-algebra argument. The closed source route from a cell hypothesis to the required row estimate is `Breakdown.CertCell.rowRestClause_closed`; combining it with the coefficient comparison gives `Breakdown.CertCell.extendedCoerciveClause_closed`.

**First, make every summation legitimate.** Proposition B.4 supplies $I^-<\infty$. If $I^+=\infty$, the left side of (B.8-R) is $+\infty$, so the inequality holds. Otherwise B.3 gives absolute convergence of the signed integrals used below. This is the point at which one may split the domain into cells and exterior regions, sum the harmonic contributions, and cancel finite error budgets.

**Next, account for every spatial region and harmonic.** On a cell, each unresolved harmonic has $I_\iota^\circ\geq0$ almost everywhere. This follows from B.5 on the supplied regions for that cell and harmonic, together with their covering property. The resolved terms are handled by the local matrix inequality and its explicit error allowances. Outside the cells, write $L_\iota=L(\nabla\widehat v_\iota,\widehat v_\iota)$ for the stretching allowance. Its nonnegativity and the nonnegative exterior weights imply

$$
I_\iota-L_\iota\geq I_\iota^\circ.
$$

The coefficient requirement $c^*\geq\sqrt{7/2}$ is used here. B.5 and B.6 give nonnegative integrals on the ordinary exterior regions; the zero harmonic on a square exterior uses the final assertion of B.4. The region partition has disjoint pieces, up to null boundaries, and covers the full complement. Since $\sum_\iota\int|I_\iota|<\infty$, the nonnegative stretching allowances are summable as well. Consequently the exterior contribution to the assembled inequality is nonnegative. In the source, the junction hypotheses carry both the region coverage and the compatibility between local expressions and the same global perturbation.

**Add the local bounds, including their errors.** Let $x_g=(x_p,x_f)$, with $x_f$ arbitrary for now. Summing the cell inequalities, the actuator-pairing inequality, the exterior inequality and the global block bound gives

$$
\begin{aligned}
4\pi\langle Nx_g,x_g\rangle
\leq{}&\int_0^1\!\int_{\mathbb R^3}
 \left(\sum_\iota I_\iota+J\right)
 -\frac3{50}\omega^2|\beta|^2
 +\sum_i\beta_i\langle b_i,Mv\rangle_H
 +\frac3{50}[F]^2\\
&+2\zeta\cdot\ell(v)-\frac{|\zeta|^2}{1000}.
\end{aligned}
\tag{B.8-A}
$$

Every cell allowance $r_{Q,0},\ldots,r_{Q,3}$ occurs with opposite signs in the two places where it was budgeted. The surrogate-actuator error $n_b$ cancels against the same quantity in the global block bound. These cancellations require equality of the data references, including the restriction maps used to form the local vectors. Merely verifying separate inequalities for unrelated matrices would not give (B.8-A). The source's assembly and junction declarations preserve those references.

Complete the square in the pin multiplier:

$$
2\zeta\cdot\ell(v)-\frac{|\zeta|^2}{1000}
=1000|\ell(v)|^2-\frac{|\zeta-1000\ell(v)|^2}{1000}
\leq1000|\ell(v)|^2.
$$

It remains to choose free coordinates for which the global quadratic form is nonnegative.

**Finally, choose those free coordinates.** Let $P$ be the common orthogonal complement of all columns of all negative-column matrices $Y_\xi$. B.7 says that $\langle Nx,x\rangle>0$ for every nonzero $x\in P$. Let $F_0=\{(0,x_f)\}$ be the free-coordinate subspace. Apply (B.8-A) to $v=0$, $\beta=0$, $F=0$. Its right side becomes $-|\zeta|^2/1000$, so $N$ is nonpositive on $F_0$. Hence $P\cap F_0=\{0\}$.

The number of negative columns bounds $\operatorname{codim}P$ and is at most $\dim F_0$. Thus

$$
\dim P+\dim F_0\geq\dim(x_g).
$$

Together with the trivial intersection this proves $P+F_0$ is the whole global-coordinate space. For the prescribed physical vector, decompose $(x_p,0)=p+(0,-x_f)$. Then $(x_p,x_f)=p\in P$, and its quadratic form is nonnegative. Inserting this choice in (B.8-A) and using the completed square proves (B.8-R).

The source terminal argument also permits slaved coordinates that change by a fixed linear map of the free variables and pressure coordinates that the quadratic form ignores. Its state therefore has the form $(z_0(v)+Lu,u)$, considered after dropping the ignored coordinates. The map from a positive-subspace vector and a free vector to their difference in this quotient is injective: equality would put a positive vector at the value of the nonpositive free graph. The same dimension count makes this map surjective and produces the required $u$. This explains why the declaration `stateTerminalTest` has a more elaborate interface than the notation $(x_p,x_f)$ in the paper. The conclusion still concerns the same state data and the same perturbation.

**Declaration route.** `cellJunctions_of_parts` assembles the cell interfaces; `halfPlaneFormBound_of_hypothesis` and `rowRestClause_of_halfPlane` pass from the meridional form to the global row estimate. `signedTreeLowerBound`, `pivotCountPositive` and `stateTerminalTest` give the finite-dimensional conclusion, assembled by `signedCertificateTerminal` and `stateEnclosureCertificateNonneg_holds`. These are proof declarations, rather than the placeholder assertions in the challenge file. The full finite hypothesis is the source's explicit replacement for the paper's partly unwritten conditions; literal equivalence of two fully written condition lists cannot be asserted when one list is absent from the paper. [Authors' numbering: Proposition B.8, pp.63–64.]
<!-- /passage:sec-appendix-b.8 -->

<a id="appendix-b.9"></a>

## B.9 Bounds for changing the profile

<!-- passage:sec-appendix-b.9 -->

Write $w_*=39/50$, let $w\geq w_*$, and put

$$
|u|_w^2=\|\Delta u\|_2^2+\int w(y)|\nabla u(y)|^2\,dy,
\qquad
c_w=\frac1{\sqrt{4\pi\sqrt{w_*}}}.
$$

For the cell certificate the weight is the constant $w_*$. We use four elementary consequences of this energy, together with the stated Sobolev bound:

$$
\begin{gathered}
\sqrt{w_*}\|\nabla u\|_2\leq|u|_w,
\quad \|\Delta u\|_2\leq|u|_w,
\quad 2\sqrt{w_*}\|\nabla u\|_2\|\Delta u\|_2\leq|u|_w^2,\\
\|u\|_\infty\leq c_w|u|_w,
\qquad \|u\|_6\leq\frac2{\sqrt3}\|\nabla u\|_2.
\end{gathered}
\tag{B.9-E}
$$

The third inequality follows from $2ab\leq a^2+b^2$; the uniform bound uses the Sobolev estimate of Section 7. The notation $c_w$ retains the paper's name, although this displayed upper bound uses the fixed lower weight $w_*$.

**Data and conclusion.** Define

$$
Z_0=W_0^a-W^r,\qquad Z_1=W_\alpha^a-W_0^a.
$$

The supplied nonnegative bounds are uniform in time and, where relevant, in $\alpha\in K$:

$$
\begin{array}{lll}
\|Z_0\|_\infty\leq n_0^\infty,&
\|\,|\nabla Z_0|_{\mathrm{op}}\,\|_2\leq n_0^{(2)},&
\|Z_1\|_\infty\leq n_1^\infty,\\
\|\,|\nabla Z_1|_{\mathrm{op}}\,\|_3\leq n_1^{(3)},&
\|\,|\nabla W^r|_{\mathrm{op}}\,\|_3\leq n_r^{(3)},&
\operatorname{sym}\nabla W^r\geq-s_-I.
\end{array}
$$

Set

$$
\begin{aligned}
A&=c_wn_0^{(2)}+
 \frac{n_0^\infty+n_1^\infty}{\sqrt{w_*}}
 +\frac{2n_1^{(3)}}{\sqrt3\sqrt{w_*}},\\
B&=\frac{s_-}{w_*}+\frac{n_r^{(3)}}{\sqrt3\sqrt{w_*}},\\
C&=c_wn_0^{(2)}+
 \frac{n_0^\infty+n_1^\infty}{2\sqrt{w_*}}
 +\frac{n_1^{(3)}}{\sqrt3\sqrt{w_*}}.
\end{aligned}
$$

If $A\leq c_r$, $B\leq c'_3$ and $C\leq c''_3$, the change in linearised convection has norm at most $c_r\|v\|_w$, as required in (7.19), and the frozen quadratic form is bounded below by $-(c'_3+c''_3)|u|_w^2$, as required in (7.22). Any larger final value of $c_3$ is admissible.

**Proof of the norm estimate.** For a fixed time, the difference of convection operators is

$$
((Z_0+Z_1)\cdot\nabla)u+(u\cdot\nabla)Z_0+(u\cdot\nabla)Z_1.
$$

Hölder's inequality gives

$$
\begin{aligned}
\|((Z_0+Z_1)\cdot\nabla)u\|_2
 &\leq(n_0^\infty+n_1^\infty)\|\nabla u\|_2,\\
\|(u\cdot\nabla)Z_0\|_2
 &\leq n_0^{(2)}\|u\|_\infty
 \leq c_wn_0^{(2)}|u|_w,\\
\|(u\cdot\nabla)Z_1\|_2
 &\leq n_1^{(3)}\|u\|_6
 \leq\frac2{\sqrt3}n_1^{(3)}\|\nabla u\|_2.
\end{aligned}
$$

Their sum is at most $A|u|_w$. Apply this to almost every time slice of $v$, square the bound and integrate in time. It proves both membership of the difference field in $H$ and (7.19). The source distinguishes the two gradient exponents explicitly: the centre discrepancy uses an $L^2$ gradient and the parameter discrepancy uses an $L^3$ gradient.

**Proof of the frozen-form estimate.** First use $W=W^r$. The field $W$ is bounded, divergence-free and continuously differentiable with bounded gradient. The weak Hessian of $u$ is square integrable because $\Delta u\in L^2$, by the Fourier identity for second derivatives. For each component set $g=\nabla u_i$. Integration by parts, using $\partial_k g_j=\partial_j g_k$, gives

$$
-\int(W\cdot\nabla)u_i\,\Delta u_i
=\int g^T(\operatorname{sym}\nabla W)g
 +\frac12\int W\cdot\nabla|g|^2.
$$

The last integral vanishes. One can first insert a spatial cutoff; the boundary error tends to zero since $W$ is bounded and $|g|^2\in W^{1,1}$, while $\operatorname{div}W=0$. Summing over $i$ therefore gives a lower bound $-s_-\|\nabla u\|_2^2$. The other convection term satisfies

$$
\left|\int(u\cdot\nabla)W\cdot\Delta u\right|
\leq \frac2{\sqrt3}n_r^{(3)}
 \|\nabla u\|_2\|\Delta u\|_2.
$$

The positive terms $\|\Delta u\|_2^2+\frac14\|\nabla u\|_2^2$ can be discarded for this lower bound. Applying (B.9-E) leaves $-B|u|_w^2$.

To replace $W^r$ by $W_\alpha^a$, pair the three discrepancy terms above with $-\Delta u$. The transport and $L^3$-gradient terms involve $\|\nabla u\|_2\|\Delta u\|_2$, so their coefficients receive the factor $1/(2\sqrt{w_*})$. The $L^2$-gradient term is bounded by $c_wn_0^{(2)}|u|_w\|\Delta u\|_2$, which costs $c_wn_0^{(2)}|u|_w^2$. Their sum is $C|u|_w^2$. Combining the reference lower bound and this absolute error gives the asserted $c_3$.

The proof declarations `gapTransferBridge_of`, `frozenFormBridge_of` and `formShiftBridge_of` implement these three estimates. `convectionIdentity_holds` supplies the integration-by-parts identity at the weak regularity needed here. The cell assembly instantiates the abstract finite list of discrepancy pieces with exactly $Z_0,Z_1$, with their two different gradient exponents. [Authors' numbering: Lemma B.9, pp.64–65.]
<!-- /passage:sec-appendix-b.9 -->

<a id="appendix-b.10"></a>

## B.10 Bounding the quadratic adjoint pairing

<!-- passage:sec-appendix-b.10 -->

**Result.** Fix $j\in J$. Either of the following sufficient conditions yields (7.32):

$$
\sup_\theta\|\psi_j(\theta)\|_3\leq n_\psi,
\qquad \frac{2n_\psi}{\sqrt3\,w_*}\leq\widetilde a_j,
$$

or

$$
\sup_\theta\|\psi_j(\theta)\|_2\leq n_\psi,
\qquad \frac{c_wn_\psi}{\sqrt{w_*}}\leq\widetilde a_j.
$$

In either case the quadratic adjoint pairing is absolutely integrable and has absolute value at most $\widetilde a_j\|v\|_w^2$.

**Proof.** At almost every time, apply Hölder to the absolute integrand. With an $L^3$ adjoint norm,

$$
\int|(v\cdot\nabla)v\cdot\psi_j|
\leq\|v\|_6\|\nabla v\|_2n_\psi
\leq\frac{2n_\psi}{\sqrt3}\|\nabla v\|_2^2
\leq\frac{2n_\psi}{\sqrt3\,w_*}|v|_w^2.
$$

With an $L^2$ adjoint norm,

$$
\int|(v\cdot\nabla)v\cdot\psi_j|
\leq\|v\|_\infty\|\nabla v\|_2n_\psi
\leq\frac{c_wn_\psi}{\sqrt{w_*}}|v|_w^2.
$$

Integrate the chosen bound over one period. Finiteness of the energy proves absolute integrability before the signed pairing is used. `adjointQuadTerm_of` proves the slice estimate with the relevant Sobolev and matrix facts; `adjointQuadraticBridge_of` integrates it and supplies the certificate clause. Its abstract interface allows the adjoint to depend on the parameter; the shape data in Appendix B select the fixed field $\psi_j$. [Authors' numbering: Lemma B.10, p.65.]
<!-- /passage:sec-appendix-b.10 -->

<a id="appendix-b.11"></a>

## B.11 A dual norm that uses azimuthal order

<!-- passage:sec-appendix-b.11 -->

**What the finite data assert.** A periodic measurable real vector field $R$ has dual bound $n$ if it splits into $R_{\mathrm{plain}}+R_{\mathrm{modes}}$, with nonnegative budgets $n_{\mathrm{plain}}+n_{\mathrm{modes}}\leq n$, such that

$$
2\|\,|y|R_{\mathrm{plain}}\|_H\leq n_{\mathrm{plain}}.
$$

For the mode part, form the complex components $R_1+iR_2$, $R_1-iR_2$, $R_3$. Each has a finite expansion

$$
\sum_p e^{2\pi i\nu_p\theta}g_p(y),
\qquad
g_p(R_\varphi y)=e^{im_p\varphi}g_p(y),
\qquad \nu_p,m_p\in\mathbb Z.
$$

The triples consisting of component, time frequency and azimuthal order must be distinct. Assign component weights $a_+=a_-=1/2$, $a_3=1$. The numerical condition is

$$
\sum_p\frac{a_{c_p}}{(|m_p|+1/2)^2}
 \int_{\mathbb R^3}|y|^2|g_p(y)|^2\,dy
\leq n_{\mathrm{modes}}^2.
\tag{B.11-D}
$$

`AzimuthalBounded` includes measurability, reconstruction of the field almost everywhere, rotation covariance, injectivity of the triple labels and this weighted square-sum condition. A decoder must combine amplitudes with an identical triple before applying (B.11-D), because the squared norm of their sum includes cross terms. The time-frequency label and the azimuthal label have separate roles; only the latter appears in the denominator.

**Result.** For a one-periodic $v\in L^2_{\mathrm{loc}}(\mathbb R;X)$, the product $v\cdot R$ is absolutely integrable over a period and satisfies the dual estimate (B.11-R).

$$
\left|\int_0^1\!\int_{\mathbb R^3}v\cdot R\right|
\leq n\|\nabla v\|_H.
\tag{B.11-R}
$$

The source expresses the perturbation class by its measurable field, weak gradient, spatial $L^6$ slices and finite period gradient energy. Periodicity of the test field is unnecessary for its integral over a single period, so that analytic interface also covers nonperiodic tests restricted to that interval.

**The improved Hardy inequality.** Let $U$ be a complex function of azimuthal order $m$, initially smooth with compact support. Radial Hardy gives

$$
\frac14\int\frac{|U|^2}{|y|^2}\leq\int|\partial_\rho U|^2.
$$

Here $\rho=|y|$ is the spherical radius. For $m\ne0$, use $\rho$, $\eta=y_3/|y|$ and the azimuthal angle. The angular derivative in that angle is $imU$. Smoothness and the nonzero order force $U$ to vanish on the axis. Integrating by parts in $\eta$ gives

$$
\begin{aligned}
&\int_{-1}^1\left((1-\eta^2)|\partial_\eta U|^2
 +\frac{m^2}{1-\eta^2}|U|^2\right)d\eta
 -(m^2+|m|)\int_{-1}^1|U|^2d\eta\\
&\hspace{1cm}=
\int_{-1}^1(1-\eta^2)
 \left|\partial_\eta U+\frac{|m|\eta}{1-\eta^2}U\right|^2d\eta
\geq0.
\end{aligned}
$$

There are no endpoint terms because of the axis behaviour. Integrate over $\rho$ and the angle, and add the radial estimate. Since $m^2+|m|+1/4=(|m|+1/2)^2$,

$$
(|m|+1/2)^2\int\frac{|U|^2}{|y|^2}
\leq\int|\nabla U|^2.
\tag{B.11-H}
$$

For $m=0$, radial Hardy already gives (B.11-H). For a general $L^6$ function with weak gradient in $L^2$, approximate in gradient norm by smooth compactly supported functions and average each approximation against $e^{-im\varphi}$ over rotations. The averaging projects onto order $m$, does not increase the gradient norm, and commutes with the limiting procedure. Ordinary Hardy controls the weighted $L^2$ norm, so the improved inequality passes to the limit. The declarations `smoothModeInverseSquare` and `modeInverseSquareWeak_of` carry these two stages.

**Use orthogonality before summing errors.** For a complex component $u$ of $v$, project onto the joint time and rotation modes:

$$
u_{\nu,m}(y)=\frac1{2\pi}\int_0^1\!\int_0^{2\pi}
 e^{-2\pi i\nu\theta-im\varphi}u(\theta,R_\varphi y)
 \,d\varphi\,d\theta.
$$

The integer time exponentials are orthogonal on $[0,1]$, and spatial rotation preserves gradient energy. The joint projections therefore have orthogonal ranges, and Bessel's inequality gives

$$
\sum_{\nu,m}\|\nabla u_{\nu,m}\|_2^2
\leq\int_0^1\|\nabla u(\theta)\|_2^2d\theta.
$$

The pairing with $e^{2\pi i\nu\theta}g$ selects exactly $u_{\nu,m}$. Weighted Cauchy–Schwarz and (B.11-H) bound it by

$$
\frac{\|\nabla u_{\nu,m}\|_2\,\|\,|y|g\|_2}{|m|+1/2}.
$$

Apply Cauchy–Schwarz to the finite collection of distinct modes, and then to the three complex components with weights $(1/2,1/2,1)$. Those weights reproduce the real dot product, by taking its real part, and reproduce $|\nabla v|^2$ exactly. The result is $n_{\mathrm{modes}}\|\nabla v\|_H$. The source's `modePairing`, `timeModeSum` and `remainderAzimuthalHolds_proof` implement this argument, grouping the azimuthal and time projections explicitly.

For the plain part, ordinary Hardy and Cauchy–Schwarz give

$$
\int|v\cdot R_{\mathrm{plain}}|
\leq\|v/|y|\|_H\|\,|y|R_{\mathrm{plain}}\|_H
\leq n_{\mathrm{plain}}\|\nabla v\|_H.
$$

The finite mode representation also has finite $\|\,|y|R_{\mathrm{modes}}\|_H$, so ordinary Hardy proves absolute integrability of that pairing. Indeed, every coefficient in (B.11-D) is positive, so every weighted amplitude norm is finite, and the squared norm of a sum of $N$ amplitudes is at most $N$ times their squared-norm sum. Its sharper signed bound is the orthogonality estimate just established. Add the two bounds and use the budget inequality. `dualBoundedBound_of_parts` supplies the final dual-pairing theorem from the plain and azimuthal estimates. Its endpoint predicate `RemainderDualBound` records spatial integrability at almost every time and integrability of the resulting scalar time integrand. The stronger packaging as joint absolute integrability follows from the weighted-norm argument above, with `weightedPairingIntegrable_proof` providing the corresponding source lemma. [Authors' numbering: Lemma B.11, p.66.]
<!-- /passage:sec-appendix-b.11 -->

<a id="appendix-b.12"></a>

## B.12 The linear adjoint error, including potentials and pins

<!-- passage:sec-appendix-b.12 -->

This lemma turns the error in an approximate adjoint equation into the number $a_j$ in (7.33). Fix $j\in J$ and abbreviate $\psi_j$ to $\psi$. The shape condition $h\geq3$ gives a divergence-free periodic field with $\psi,\partial_\theta\psi=O((1+|y|)^{-3})$, first spatial derivative $O((1+|y|)^{-4})$ and second spatial derivative $O((1+|y|)^{-5})$, with the latter understood almost everywhere across spline interfaces.

**The additional data.** For the pin fields take compactly supported potentials $\Phi_l$ and $C^1$ divergence-free generators $\widetilde\Phi_l$ with bounded weak second derivatives, with

$$
\left\|\sum_lY_{jl}(\Phi_l-\widetilde\Phi_l)\right\|_H\leq n_\Phi,
\qquad
\left(\sum_lY_{jl}^2\right)^{1/2}\leq n_Y.
$$

The rounding bound from B.1 must hold for every coefficient vector $c$:

$$
\left\|\sum_lc_l(\Xi_l-\nabla\Phi_l)\right\|_H
\leq c_\Xi|c|.
\tag{B.12-P}
$$

Supply vector fields $G_j,U_j$, a matrix field $F_j$ and a scalar field $q_j$, with the weak derivatives and decay needed for the integrations by parts below. The paper describes their coefficient representation only briefly. The source's precise analytic interface is `IsPotentialData`, which requires the following bounds for one common $C$, writing $\rho=|y|$:

| Object | Source requirement |
|---|---|
| $G_j$ | Joint $C^1$; $|G_j|\leq C(1+\rho)^{-2}$, $|\nabla G_j|\leq C(1+\rho)^{-3}$, $|\Delta G_j|\leq C(1+\rho)^{-4}$ almost everywhere |
| $U_j$ | Joint $C^1$; $|U_j|\leq C(1+\rho)^{-1}$, $|\nabla U_j|\leq C(1+\rho)^{-2}$, $|\Delta U_j|\leq C(1+\rho)^{-3}$ almost everywhere |
| $F_j$ | Measurable; $|F_j|\leq C(1+\rho)^{-2}$, $\rho|\operatorname{div}F_j^T|\leq C(1+\rho)^{-2}$ almost everywhere |
| $q_j$ | Measurable; $|q_j|\leq C(1+\rho)^{-2}$, $\rho|\nabla q_j|\leq C$ and $\rho^3|\nabla q_j|\leq C$ almost everywhere |
| Derivative identities | The supplied second derivatives, matrix divergence and scalar gradient represent the corresponding distributions |

These hypotheses are more detailed than (B.51), and the decay requirements on the two Laplacians are stronger than its common upper bound. The potential-shape constructors establish this interface from the source's finite spline conditions. At the level of arbitrary potential functions, a theorem using this interface has additional hypotheses relative to the printed lemma. The analytic decay interface uses operator norms for linear maps, while the quantitative budgets for $\nabla U_j$ and $F_j$ use the Frobenius norm encoded by `matSq`. An existential decay constant can absorb the equivalence of these finite-dimensional norms; a certified numerical budget must use its prescribed norm.

With $W_\alpha^a=W_\alpha^0+\sum_i\alpha_iW_\alpha^i$, define

$$
\begin{aligned}
R_{j,\alpha}={}&-S(0)^{-1}\partial_\theta\psi-\psi
 -\tfrac12(y\cdot\nabla)\psi-\Delta\psi
 -(W_\alpha^0\cdot\nabla)\psi
 +\sum_k\psi_k\nabla W_{\alpha,k}^0\\
&+\sum_lY_{jl}\Delta\widetilde\Phi_l
 +\nabla q_j+\Delta G_j+w_*\Delta U_j
 -\operatorname{div}F_j^T.
\end{aligned}
\tag{B.12-D}
$$

Assume this residual has dual bound $n_R$, uniformly in $\alpha$. Choose $n_G\geq\|G_j\|_H$, $n_U\geq\|\nabla U_j\|_H$, $n_F\geq\|F_j\|_H$. Choose coordinate bounds $|\alpha_i|\leq\bar\rho_i$ and positive weights $\varpi_i$. The remaining bounds are

$$
\begin{gathered}
\left\|\left(\sum_i\varpi_i|W_\alpha^i|^2\right)^{1/2}\psi\right\|_H\leq n_v,\\
\sum_k\psi_k\nabla W_{\alpha,k}^i
 \text{ has dual bound }n_i,
\qquad \sum_i\varpi_i n_i^2\leq n_d^2,\\
\partial_\theta\psi\text{ has dual bound }n_\theta,
\qquad S(\alpha)^{-1}=S(0)^{-1}+\sum_i\varsigma_i\alpha_i.
\end{gathered}
$$

Every norm budget used here is nonnegative. Define

$$
\begin{aligned}
A_j={}&\left(n_G^2+
 \frac{(w_*n_U+n_F+n_R)^2}{w_*}\right)^{1/2}\\
&+\frac1{\sqrt{w_*}}
 \left[\left(\sum_i\frac{\bar\rho_i^2}{\varpi_i}\right)^{1/2}
       (n_v+n_d)
       +\left(\sum_i|\varsigma_i|\bar\rho_i\right)n_\theta\right]
 +n_\Phi+\frac{n_Yc_\Xi}{\sqrt{w_*}}.
\end{aligned}
\tag{B.12-A}
$$

**Result.** If $a_j\geq A_j$, every admissible $v$ and every $F\in H$ representing $T_{S(\alpha)}v+C_\alpha v$ modulo pressure satisfy the linear adjoint estimate (B.12-R).

$$
\big|\langle F,\psi_j\rangle_H-(Y\ell(v))_j\big|
\leq a_j\|v\|_w.
\tag{B.12-R}
$$

**Justify the adjoint operation first.** The pressure ambiguity vanishes against the divergence-free $\psi$. The adjoint of $\frac12+\frac12y\cdot\nabla$ in dimension three is $-1-\frac12y\cdot\nabla$: the divergence of $y$ contributes three, while the original zeroth-order coefficient contributes one half. Thus

$$
\langle T_Sv,\psi\rangle_H
=\iint v\cdot\left(-S^{-1}\partial_\theta\psi
 -\psi-\tfrac12y\cdot\nabla\psi\right)
 +\langle\nabla v,\nabla\psi\rangle_H.
\tag{B.12-T}
$$

This use of a noncompact test field needs a density argument. The source constructs a decaying curl potential $A$ with $\operatorname{curl}A=\psi$, cuts off $A$, takes its curl and then smooths in space and time. The approximating tests remain divergence-free. A direct multiplication of $\psi$ by a spatial cutoff would introduce divergence. The bounds on the field, its time derivative, its gradient and the curl potential control all errors involving time differentiation and the unbounded coefficient $y$. They converge in the norms paired with $v$, $\nabla v$ and $F$. The source implements this construction in `testFieldDensityHolds_proof` and uses it in `representationHolds_of_density`.

For a matrix field $A\in L^2$ with $\operatorname{div}A^T\in L^{6/5}$, spatial density and Sobolev give

$$
\int v\cdot\operatorname{div}A^T
=-\int\nabla v:A.
\tag{B.12-I}
$$

The weak-derivative hypotheses in the table guarantee this identity across every spline interface. They exclude unrecorded surface contributions to the derivatives. Apply (B.12-I) to the gradients of $\psi,\widetilde\Phi_l,G_j,U_j$, to $F_j$, to the convection matrix, and to $q_jI$. The last pairing is zero because $\operatorname{div}v=0$. Also, for the compactly supported pin differences and for $G_j$, use

$$
\langle\nabla v,\nabla G\rangle_H
=-\langle\Delta v,G\rangle_H.
$$

**Write the complete error identity.** Expand the profile and reciprocal period, substitute (B.12-D), and subtract $\sum_lY_{jl}\langle\nabla v,\Xi_l\rangle_H$. The result is

$$
\begin{aligned}
\langle F,\psi\rangle_H-(Y\ell(v))_j
={}&\iint v\cdot R_{j,\alpha}
 -\langle\Delta v,G_j\rangle_H
 +\langle\nabla v,w_*\nabla U_j-F_j\rangle_H\\
&+\sum_i\alpha_i\left[
 \langle(W_\alpha^i\cdot\nabla)v,\psi\rangle_H
 +\iint v\cdot\sum_k\psi_k\nabla W_{\alpha,k}^i\right]
 -(\varsigma\cdot\alpha)\iint v\cdot\partial_\theta\psi\\
&+\left\langle\Delta v,\sum_lY_{jl}(\Phi_l-\widetilde\Phi_l)\right\rangle_H
 -\left\langle\nabla v,\sum_lY_{jl}(\Xi_l-\nabla\Phi_l)\right\rangle_H.
\end{aligned}
\tag{B.12-F}
$$

The signs of both pin terms follow from first inserting $\nabla\Phi_l$, and then integrating the difference $\Phi_l-\widetilde\Phi_l$ by parts. This is an identity between absolutely defined pairings.

**Bound its three lines.** Put $a=\|\Delta v\|_H$, $b=\|\nabla v\|_H$. B.11 and Cauchy–Schwarz bound the first line by

$$
n_Ga+(w_*n_U+n_F+n_R)b
\leq\sqrt{n_G^2+(w_*n_U+n_F+n_R)^2/w_*}
       \sqrt{a^2+w_*b^2}.
$$

The square root containing $a,b$ is at most $\|v\|_w$. This two-dimensional Cauchy–Schwarz step is the reason for the square root in the first term of (B.12-A).

For the parameter terms, weighted Cauchy–Schwarz gives the pointwise bound

$$
\left|\sum_i\alpha_iW_\alpha^i\right|
\leq\left(\sum_i\frac{\bar\rho_i^2}{\varpi_i}\right)^{1/2}
 \left(\sum_i\varpi_i|W_\alpha^i|^2\right)^{1/2}.
$$

It bounds the first sum of pairings by $(\sum_i\bar\rho_i^2/\varpi_i)^{1/2}n_vb$. B.11 and finite-dimensional Cauchy–Schwarz bound the second sum by the same expression with $n_d$. Finally $|\varsigma\cdot\alpha|\leq\sum_i|\varsigma_i|\bar\rho_i$, so the time-shift term costs at most $(\sum_i|\varsigma_i|\bar\rho_i)n_\theta b$. Divide their combined coefficient by $\sqrt{w_*}$ to bound this line by a multiple of $\|v\|_w$.

The last line is at most $n_\Phi a+n_Yc_\Xi b$. The second term follows by applying (B.12-P) to the entire row $(Y_{jl})_l$. Thus it costs $(n_\Phi+n_Yc_\Xi/\sqrt{w_*})\|v\|_w$. Adding the three bounds proves (B.12-R). The declarations `potentialBoundHolds_proof`, `freeShiftBoundHolds_proof` and `pinChargeHolds_proof` give these respective bounds, assembled by `adjointDefectBridge_of_pieces`.

**How to read the source data.** The source fields `PotentialData.theta`, `phi`, `flux` and `pressure` represent $G_j,U_j,F_j^T,q_j$ in coordinate matrices, respectively; `theta` here names a potential field, rather than a time variable. Its derivative is a linear map with output-component rows and differentiation-direction columns. The paper's derivative matrix convention is transposed, which explains `matrixDivergence flux` in the source where the paper writes $\operatorname{div}F_j^T$. The source defines its pin flux as $D\psi-\sum_lY_{jl}(D\widetilde\Phi_l-(D\widetilde\Phi_l)^*)$. Taking the divergence gives the same pin Laplacians when the generators are divergence-free; the additional term in the general interface is a gradient and pairs to zero against $v$. The general adjoint entry also has a set of fitted parameter directions, while `AdjointEntryLinks.fitted_empty` requires that set to be empty for these cell data. Consequently its `defectSum` plus `pinCharge` reduces exactly to (B.12-A). [Authors' numbering: Lemma B.12, pp.67–68.]
<!-- /passage:sec-appendix-b.12 -->

<a id="appendix-b.13"></a>

## B.13 Enclosing the constant, linear and quadratic offset

<!-- passage:sec-appendix-b.13 -->

The approximate profile has parameter-dependent radial phase outside the matching ball. Inside $B_{r_\chi}$, the phase perturbation and all derivatives needed below vanish. Hence the profile pieces agree there with the pieces at the central phase. Write these fixed fields as $W_i=W_0^i$, including $W_0=W_0^0$, and write $q_i$ for the pressure-potential pieces at that phase. Put $f_0=S(0)^{-1}$ and $f_i=\varsigma_i$.

**Define the coefficients before enclosing them.** The constant coefficient is

$$
\begin{aligned}
F^{(0)}={}&f_0\partial_\theta W_0+\tfrac12W_0
 +\tfrac12(y\cdot\nabla)W_0-\Delta W_0
 +(W_0\cdot\nabla)W_0\\
&+\sum_l\beta_l^0b_l+\nabla(q_0-|W_0|^2/2).
\end{aligned}
$$

For each parameter direction,

$$
\begin{aligned}
F^{(i)}={}&f_0\partial_\theta W_i+f_i\partial_\theta W_0
 +\tfrac12W_i+\tfrac12(y\cdot\nabla)W_i-\Delta W_i\\
&+(W_0\cdot\nabla)W_i+(W_i\cdot\nabla)W_0
 +\sum_l\beta_l^ib_l+\nabla(q_i-W_0\cdot W_i).
\end{aligned}
$$

Define the ordered quadratic expression

$$
Q_{il}=f_i\partial_\theta W_l+(W_i\cdot\nabla)W_l
 -\tfrac12\nabla(W_i\cdot W_l).
$$

The stored coefficient is $F^{(ii)}=Q_{ii}$ on the diagonal, and $F^{(il)}=Q_{il}+Q_{li}$ for $i<l$. Thus the diagonal appears once, while an off-diagonal coefficient already contains both ordered terms. The source records these two stages as `orderedQuadratic` and `quadraticCoefficient`; the sum uses only $i\leq l$.

Inside the matching ball, substitution of

$$
W_\alpha^a=W_0+\sum_i\alpha_iW_i,\qquad
q_\alpha^{\mathrm{potential}}=q_0+\sum_i\alpha_iq_i,
\qquad S(\alpha)^{-1}=f_0+\sum_if_i\alpha_i,
\qquad \beta^a(\alpha)=\beta^0+\sum_i\alpha_i\beta^i
$$

in the residual formula gives, almost everywhere,

$$
F_\alpha^a=F^{(0)}+\sum_i\alpha_iF^{(i)}
 +\sum_{i\leq l}\alpha_i\alpha_lF^{(il)}.
\tag{B.13-E}
$$

The quadratic pressure correction $-\nabla|W_\alpha^a|^2/2$ supplies the half in $Q_{il}$, and its two ordered cross terms supply the full gradient in an off-diagonal coefficient. No quadratic coefficient is lost or counted twice. The result holds almost everywhere because the shape data provide weak second derivatives and an almost-everywhere pressure gradient at the spline interfaces. `ballAgreement_holds` proves the local field agreement and `offsetBallIdentity_holds` proves the expansion.

**Finite enclosures.** Let $\langle\ ,\ \rangle_\chi$ mean the space-time pairing restricted to this ball. For each $j\in J$, supply centres $C_{0j},C_{1ji},C_{2jil}$ and nonnegative error bounds satisfying

$$
\begin{aligned}
|C_{0j}-V_j\cdot\beta^0+\langle F^{(0)},\psi_j\rangle_\chi|
 &\leq\widetilde C_{0j},\\
|C_{1ji}-V_j\cdot\beta^i+\langle F^{(i)},\psi_j\rangle_\chi|
 &\leq\widetilde C_{1ji},\\
|C_{2jil}+\langle F^{(il)},\psi_j\rangle_\chi|
 &\leq\widetilde C_{2jil}\qquad(i\leq l).
\end{aligned}
\tag{B.13-C}
$$

The absolute values apply to the entire discrepancy in each line. Also supply uniform tail bounds

$$
\|F_\alpha^a1_{|y|>r_\chi}\|_H\leq n_F^{\mathrm{out}},
\qquad \|\psi_j1_{|y|>r_\chi}\|_H\leq n_j^{\mathrm{out}}.
$$

Define the coordinate bounds

$$
\widehat\rho_i=
\begin{cases}
\rho_i,&i\in J,\\
\rho_*/|d_i|,&i\notin J.
\end{cases}
$$

The second case uses the nonzero scale $d_i$ and the nonnegative stiff radius $\rho_*$. Every $\alpha\in K$ satisfies $|\alpha_i|\leq\widehat\rho_i$; for a stiff direction, this follows from $d_i^2\alpha_i^2\leq\rho_*^2$. Set

$$
\begin{aligned}
o_j={}&|C_{0j}|+\widetilde C_{0j}\\
&+\sum_i\bigl(|C_{1ji}-d_j\delta_{ij}|+\widetilde C_{1ji}\bigr)\widehat\rho_i\\
&+\sum_{i\leq l}\bigl(|C_{2jil}|+\widetilde C_{2jil}\bigr)
     \widehat\rho_i\widehat\rho_l
 +n_F^{\mathrm{out}}n_j^{\mathrm{out}}.
\end{aligned}
\tag{B.13-O}
$$

In particular, the factor $\widehat\rho_j$ multiplies both terms of $|C_{1jj}-d_j|+\widetilde C_{1jj}$.

**Result and proof.** These data give the offset estimate (B.13-R) for every $\alpha\in K$.

$$
\big|V_j\cdot\beta^a(\alpha)
 -\langle F_\alpha^a,\psi_j\rangle_H-d_j\alpha_j\big|
\leq o_j.
\tag{B.13-R}
$$

Split the pairing into the ball and its exterior. In the ball insert (B.13-E), and expand the affine multiplier. The constant discrepancy is within $\widetilde C_{0j}$ of $C_{0j}$. Each linear discrepancy is within $\widetilde C_{1ji}$ of $C_{1ji}$, with the additional subtraction $d_j$ when $i=j$. Each quadratic coefficient is within $\widetilde C_{2jil}$ of $C_{2jil}$, with its sign already incorporated in (B.13-C). Apply the triangle inequality and the coordinate bounds. Cauchy–Schwarz bounds the remaining exterior pairing by $n_F^{\mathrm{out}}n_j^{\mathrm{out}}$. This gives exactly (B.13-O).

The source uses a closed ball, whereas the paper uses an open ball. Their integrals agree because the sphere is a null set; the tail in both formulations is $|y|>r_\chi$. The source's `offsetClause_holds_of` combines the expansion, coefficient enclosures, coordinate bound and tail estimate. Its frame product is written $\sum_l\mathrm{frame}_{lj}\beta_l$, corresponding to the paper's $V_j\cdot\beta$; a decoder must respect this index order. To identify its conclusion with (7.34), use the cell shape condition equating the certificate target with the profile's pin values, which makes the target gap $\bar\ell$ zero. The general certificate framework does not require that gap to vanish. [Authors' numbering: Lemma B.13, pp.68–69.]
<!-- /passage:sec-appendix-b.13 -->

<a id="appendix-b.14"></a>

## B.14 The same finite data give a certificate

<!-- passage:sec-appendix-b.14 -->

**Result.** Suppose data in the representation of B.1 satisfy the full cell, tree, bound and compatibility conditions. The sets $\Gamma,K$, periods, profile family, reference field, actuators, residuals, pins, row fields, adjoints, multiplier map, weight, matrices and numerical budgets then satisfy the certificate conditions of Section 7. This is a conditional construction from the given data. It supplies no concrete tuple satisfying those conditions.

The source's precise construction is `Breakdown.CellLayerSystem.isExtendedCertificate_of_parts`. Given all fifteen fields of `CellSystemCondition` and the analytic bridge results, it produces a number $b$ and proves that the supplied extended-certificate record, with its decay bound replaced by $b$, is an extended certificate. All other fields of the record are preserved. The quantified witness is the decay bound; the theorem does not replace the numerical profile or choose a different parameter family.

**Proof.** The shape and joining conditions first give the analytic properties required of the data: periodicity, symmetry, divergence freedom, spatial regularity, the stated weak Hessians, pressure orthogonality and decay. Measurability and finite norms are supplied for the pins, residual and row fields. The residual is the prescribed defect of the same profile, pressure and multiplier. The Gram and row bounds in the cell data give the orthonormal row family and $\|e_k\|_H\leq c_0$.

For an arbitrary $\alpha\in K$, B.8 gives the global form inequality and finiteness of its negative part. The weight admissibility and coefficient comparison of B.2 turn this into the coercive estimate (7.18), with the allowed $c_1,c_2$. The closed source declaration `extendedCoerciveClause_closed` is the corresponding cell-to-coercivity step. Its physical coordinates, restriction maps and global state are those already used in B.8.

B.9 supplies the convection-change bound and the frozen-form lower bound. B.10 supplies the quadratic adjoint estimate, B.12 supplies the linear adjoint estimate and B.13 supplies the offset estimate. The cell assembly proves the hypotheses connecting each generic bridge to the supplied shape data. In particular, the two-piece shift decomposition, the potential-field regularity, the fixed adjoint identity, the reciprocal-period identity and the empty fitted-direction set are verified at this interface. These estimates apply to the full perturbation class used by the lemmas and therefore also to its symmetry-invariant subclass.

Several certificate conditions are carried as numerical hypotheses rather than derived by these analytic lemmas. They include the sign and nonzero requirements; the positive-period bound $S(\alpha)\leq S_{\max}$; the frame and inverse relations; actuator and defect norm bounds, including the defect's row pairings; the transfer-constant bound; the size, smallness and parameter-inclusion inequalities; and the nontriviality condition. These are the remaining clauses listed after B.13. A checker must certify them using the actual numerical data. The source does not infer them from a small sampled residual or an approximate Newton solution.

Continuity is also part of the construction. The multiplier is affine in the parameter, and the reciprocal period is affine with nonvanishing denominator on the parameter set. The profile-to-pin pairing gives the continuous target map and the zero target gap for this cell representation. The shape-decay proof supplies the common bound $b$. Combining these facts with the universal estimates and the directly assumed numerical clauses fills every field of the extended-certificate structure.

The theorem `spaceBreakdown_of_cell_system_condition` supplies the bridge proofs from their closed source declarations and applies the certificate implication. `Solution.lean` exposes the conditional consequences on $\mathbb R^3$, on $\mathbb T^3$, and jointly. Their hypothesis remains a proof of `CellSystemCondition` for the selected data. The inspected declarations establish this implication; this rewrite neither constructs the unpublished certificate nor reruns its external numerical checker. [Authors' numbering: Proposition B.14, pp.69–70.]
<!-- /passage:sec-appendix-b.14 -->

## The fifteen fields of CellSystemCondition

<!-- passage:sec-the-fifteen-fields-of-cellsystemcondition -->

The following is a reading of the canonical definition in `Breakdown/CertCell/StatementDefs.lean`. Each field is a premise of the conditional theorem. A named analytic producer explains what that premise yields; it does not assert that the unpublished data satisfy the premise.

<a id="1"></a>

### 1. cell: the cell problem and its common constants

The `cell` field supplies the geometric, analytic and finite-dimensional structure on which the multiplier and cell arguments operate. It is the 17-field `CellHypothesis`, containing the following groups.

| Fields within `CellHypothesis` | What they require |
|---|---|
| `instance_entry` | The row, weight, forcing and pinning instances interpret the objects of $D$ correctly |
| `cell_conditions` | Valid layouts, bases, leaf bounds and polynomial/error decompositions on every cell |
| `tree_conditions` | The finite tree, its signed matrices, coordinate maps and pivot conditions |
| `pair_surrogate`, `kappaCost_nonneg` | One family of pairing-error witnesses, with the sum of those errors and cell costs bounded by $N.\mathrm{globalError}$ |
| `credit_evaluations` | Valid rectangle-credit evaluations and their geometric data |
| `continuum_conditions_given` | The coefficient and enclosure conditions that control the continuum and omitted modes |
| `bound_valueSets` | A shape representation for the coefficient bounds and transport-speed bounds |
| `given_shape` | A scaled-jet representation of the reference field and compatible compact forcing/support facts |
| `mesh_valid`, `azimuth_ge`, `mode_class` | Valid physical cells, azimuthal order at least 3, and the stated symmetry class |
| `box_uniform` | Reference field and weight data fixed across the parameter set, allowing the specified rotation-rate variation |
| `rowWeightMax_eq`, `weightFn_eq`, `coercivity_eq`, `pinWeight_eq` | The four exact constants just stated |

This field serves Propositions B.1 and B.4, the tree lemma B.7, and their assembly in B.8. A checker establishes it by building the representations and proving their format properties, then checking the actual inequalities and matrices. It must retain the same pairing-error witness through the sum bound. The support-cover subcondition by itself does not forbid an empty mesh, so it cannot be used as a standalone nonvacuity argument.

**Lean anchors:** `Breakdown.CertCell.CellHypothesis`; `Breakdown.CertCell.IsBoxUniform`; `Breakdown.CertCell.CoefficientConditions`; `Breakdown.CertCell.CellCalculus.IsLeafValues`.

<a id="2"></a>

### 2. shape_valueSets: the values needed by the shape-to-analysis bridge

The `shape_valueSets` field requires a positive period and constant positive weight, together with harmonic sets closed under the stated symmetries. Its seven clauses also require the zero harmonic and every reference-field harmonic to be present in the bound support. These facts let the finite shape representation feed the harmonic multiplier estimates without losing a required mode.

The paper counterpart is the representation and harmonic symmetry of B.1 and the weights in B.2, pp.50-54. Exact finite-set closure checks suffice when those bound supports have been decoded as finite sets. The positive-period condition is uniform on the whole parameter set. An affine formula for its reciprocal can be checked with the support-function formula above, after proving the formula and its nonzero denominator conditions. The field does not follow just from choosing a positive period at the central parameter.

**Lean anchor:** `Breakdown.CertCell.GivenShape.ShapeValuesFacts`.

<a id="3"></a>

### 3. entry_conditions: the meaning of the assembled matrices

The `entry_conditions` field ties the finite assembly matrices to the analytic cell forms, omitted modes and exterior estimates. Its twenty clauses are the omitted coefficient and bookkeeping conditions behind Proposition B.4, equations (B.26)-(B.34), and the global estimate (B.43).

They require regular charges and bounded measurable leaf entries; the potential and pairing inequalities; row and row-functional identities; tail conditions; the exact top-block form; elimination bounds; blindness to gauge, pressure-head and pressure-coordinate directions; omitted-mode and exterior coverage; far-field bounds; tree-row inequalities; and real, gauge and transport keys. The exterior stretch constant must be at least $\sqrt{7/2}$.

A checker must verify the displayed local inequalities for every vector allowed by `InRowRange`, not just an image under one convenient cell embedding. It must prove that each stored matrix is the matrix of the required form, then use Hermitian or real symmetric positivity tests on that matrix. The zero band-slack branch requires the corresponding residual to vanish; division by slack cannot erase this branch. Exterior checks must include measurable ray-dependent radii with the stated positive lower and finite upper bounds.

This is a detailed formal specification where the printed paper gives only part of the coefficient format. A reader can follow the Lean obligations, but full identity with an unpublished numerical implementation remains to be checked.

**Lean anchors:** `Breakdown.CertCell.CellLayerEntryConditions`; `Breakdown.CertCell.Assembly.InRowRange`; `Breakdown.CertCell.Assembly.IsExteriorCover`.

<a id="4"></a>

### 4. enclosure_numbers: bind the multiplier bounds to this instance

The `enclosure_numbers` field requires the same three numerical multiplier bounds to hold for every parameter in the certificate set. For each parameter it instantiates `EnclosureAdmissibleClauses` using the actual period, weights, bound fields, reference field and reference Hessian.

The clauses enclose each reference harmonic's velocity, gradient, vorticity and vorticity gradient; the full vorticity and its gradient; and the transport velocity in every rotating frame. They require a positive one-sided frequency margin on each skew-weight mode set, the $\mu$ ratio inequality, nonnegativity of its bound, bounds on the sums of $\lambda$ and $|\nabla\lambda|$, and the admissible convolution share. These are the conditions around (B.19) used in Proposition B.1 and Lemma B.2.

The `cell` premise already contains an existential enclosure route. This fourth field binds the particular numbers in $N$ that will be inserted into the final coercive constant. A checker must therefore transport a common witness or compare the chosen bounds in the direction that the formula needs. All mode-set frequency margins and spatial enclosures remain uniform assertions.

**Lean anchor:** `Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses`.

<a id="5"></a>

### 5. coerciveL2_ge: the coefficient of the forcing norm

The `coerciveL2_ge` field requires the certificate's forcing coefficient to dominate the constant derived by the multiplier estimate. With $w=39/50$, $c=3/50$, $c_\mu$ the common $\mu$ coefficient, and $\varepsilon,\varepsilon',b$ the three values from $N$, it asks for

$$
\frac{1}{\sqrt c}
 \sqrt{\frac{(1+\varepsilon+\varepsilon'/\sqrt w)^2}{c}+\frac{b}{c_\mu}}
 \leq c_1.
$$

This is the first bound in (B.22). Lemma B.2 supplies its use after the global lower bound has been proved. An outward-rounded upper bound on the left and a lower bound on the stored $c_1$ are sufficient. Positive $w,c,c_\mu$ must come from the other fields before a checker squares, divides or simplifies this expression. This is one scalar check with dependencies, rather than a free replacement of the derived constant by a preferred value.

**Lean anchor:** `Breakdown.CellLayerSystem.CellSystemCondition.coerciveL2_ge`.

<a id="6"></a>

### 6. coercivePin_ge: the coefficient of the pinning error

The `coercivePin_ge` field requires the certificate's pinning coefficient to be at least $\sqrt{1000/(3/50)}$. This is the second inequality in (B.22), arising from the pinning penalty in the global lower bound. The checker needs a rigorous one-sided comparison and the same exact pin weight and coercivity as in `cell`.

The coefficient survives in the generic extended-certificate interface. In the present specialised construction the prescribed target equals the pins of the approximate profile, so `instantiation` makes the target gap zero. Retaining the coefficient is consistent with that specialisation and does not permit a different target.

**Lean anchor:** `Breakdown.CellLayerSystem.CellSystemCondition.coercivePin_ge`.

<a id="7"></a>

### 7. certificate: the numerical hypotheses used after coercivity

The `certificate` field contains the remaining numerical and parameter-inclusion conditions consumed by Theorem 7.1. Its 41 clauses include sign guards, nonzero parameter scales, a positive multiplier weight, the period bound, the symmetry-compatible time factor, actuator and residual norms, the three smallness bounds, an invertible finite frame, adjoint and stiff-coordinate inclusion estimates, and strict nontriviality of the approximate profile.

The transfer and total coercivity requirements have the form

$$
\tau<1,\qquad c_1+M_{\rm row}\leq(1-\tau)C,\qquad C>0.
$$

The residual budget is

$$
c_1\,\varepsilon(q)+\varepsilon_{\rm row}(q)
 +c_2|\mathrm{targetGap}(q)|\leq(1-\tau)r.
$$

Here the labels denote the corresponding fields of the same extended certificate; their definitions, including transfer loss, are fixed by that interface. The three smallness inequalities are the actual inequalities (7.26)-(7.28), with the source's weight, period, actuator and form constants. The parameter inclusions are (7.35)-(7.37). Nontriviality is strict:

$$
\frac{4r^2}{w}<\int_0^1\int_{\mathbb R^3}|\nabla W_q^a|_{\rm F}^2\,dy\,d\theta
\quad(q\in K).
$$

The norm here is the sum of squares of the derivative entries. The right side is not an arbitrarily chosen operator-norm estimate. `IsUnit frame` means invertibility, not orthogonality; the stiff bound uses the specified columns. A sound numerical check encloses the continuum norms and verifies all parameter-uniform inequalities, then evaluates the finite scalar budgets with their strictness preserved.

**Lean anchor:** `Breakdown.CellLayerSystem.CertificateClauses`.

<a id="8"></a>

### 8. instantiation: identify the actual profile, pressure and adjoints

The `instantiation` field identifies the certificate's profile, second derivatives, pressure gradient and adjoints with the specified shape constructions. It validates the centre, tangent and origin data, moving step phase and azimuthal order; fixes the target to the pin values of the approximate profile; gives the pressure gradient its Bernoulli correction; and identifies each active adjoint with a fixed shape field of decay order at least 3.

These are the formal versions of (B.6)-(B.9) and the pressure and adjoint data on p.52. Several constructor equalities, including the profile, pressure correction and target equality, hold for every real parameter vector, even though the quantitative estimates are used on $K$. Their analytic consequences are obtained by the profile, pressure, step-phase and adjoint theorems. A decoder should construct the fields through those definitions or prove equality to them. Independently computing a plausible Hessian or pressure gradient is insufficient when it differs at a branch or seam in a way relevant to a pointwise condition.

The target equality makes `targetGap` identically zero for this cell route. This is stronger information than reading the generic extended-certificate record in isolation.

**Lean anchors:** `Breakdown.CellReduction.Instantiation.InstantiationBounded`; `Breakdown.CellReduction.Instantiation.IsProfileShapeEntry`; `Breakdown.CellReduction.Instantiation.IsPressureShapeEntry`; `Breakdown.CellReduction.Instantiation.IsAdjointShapeEntry`.

<a id="9"></a>

### 9. offset_expansion: certify the parameter polynomial and its tail

The `offset_expansion` field checks the interior residual coefficients, their enclosure errors and the exterior Cauchy-Schwarz remainder used by Lemma B.13. It identifies the reciprocal period and multiplier coefficients as affine functions of the parameter, encloses the constant and linear adjoint pairings on the matching ball, and encloses the quadratic pairings for indices $i\leq l$.

The coefficient constructor retains a diagonal ordered term once and adds the two ordered terms when $i<l$. Accordingly the final bound uses a triangular sum over $i\leq l$. A decoder that both symmetrises the stored coefficient and counts both ordered pairs would double the off-diagonal contribution; a decoder that does neither would omit one contribution.

Separate exterior $L^2$ bounds on the residual and adjoint supply their product. The certificate's offset number is fixed to the resulting coefficient-and-tail expression, using radius $r_i$ on adjoint coordinates and $|R|/|s_i|$ on stiff coordinates. The uniform phase dependence outside the matching ball is handled by those tail bounds, not by extending the interior quadratic identity to all space.

**Lean anchors:** `Breakdown.CellReduction.Instantiation.IsOffsetExpansionEntry`; `Breakdown.CellReduction.Instantiation.OffsetExpansionEntry.quadraticCoefficient`; `Breakdown.CellReduction.Instantiation.offsetSum`.

<a id="10"></a>

### 10. shift_numbers: move estimates from the reference field

The `shift_numbers` field bounds the change from the frozen reference profile to the central approximate profile and then across the parameter set. It supplies four nonnegative numbers: a uniform central difference, a central $L^2$ gradient difference, a uniform parameter displacement and a parameter-displacement $L^3$ gradient bound. Two explicit weighted sums must fit within the certificate's gap and form-shift budgets.

These are the two stages of Lemma B.9 and (B.47)-(B.48). The checker must use the $L^2$ norm for the central gradient term and the $L^3$ norm for the parameter gradient term, and preserve the exact coefficients assigned to those different estimates. Every spatial bound is global and every parameter displacement is uniform on $K$. A central collocation residual does not establish these comparison norms.

**Lean anchor:** `Breakdown.CellLayerSystem.ShiftNumbersBounded`.

<a id="11"></a>

### 11. frozen_form: control the frozen quadratic form

The `frozen_form` field supplies a lower strain bound and an $L^3$ gradient bound for the frozen model. If $s_-$ and $g_3$ are its two nonnegative bounds, it requires the strain inequality for every vector at every point, the gradient bound uniformly in time and parameter, and

$$
\frac{s_-}{w}+\frac{g_3}{\sqrt{3w}}\leq M_{\rm model}.
$$

This is the frozen-model ingredient used together with Lemma B.9 to obtain the form bound in (7.22). A matrix eigenvalue enclosure can establish the strain inequality; rigorous global integration can establish the cubic gradient bound. The final scalar inequality then connects those values to the certificate's model-form budget. Sampling eigenvalues is sufficient only after a range enclosure has proved the bound between samples and in the exterior.

**Lean anchor:** `Breakdown.CertReduction.FrozenFormBounded`.

<a id="12"></a>

### 12. adjoint_quadratic: bound the nonlinear adjoint pairing

The `adjoint_quadratic` field turns an adjoint size bound into the coefficient of the quadratic perturbation term. For each active adjoint, the representation chooses either an $L^3$ or an $L^2$ spatial norm, proves that bound at every time and parameter, and multiplies it by the corresponding weight-dependent coefficient before comparing with the stored adjoint quadratic constant.

Lemma B.10 gives the two estimates. This disjunction belongs to the data: the chosen Boolean and its associated numerical bound must stay together. For the cubic branch the coefficient is $2/(\sqrt3\,w)$; for the $L^2$ branch it is $S(w)/\sqrt w$, where $S(w)=[2\pi(2\sqrt w)]^{-1/2}$. A stronger bound in another norm can be used only after proving the required embedding with its constants.

**Lean anchors:** `Breakdown.CertReduction.AdjointQuadraticBounded`; `Breakdown.CertReduction.AdjointSizeBound`; `Breakdown.CertReduction.adjointQuadCoeff`.

<a id="13"></a>

### 13. adjoint_links: use the same fields in the defect calculation

The `adjoint_links` field identifies the adjoint-defect calculation with the profile, adjoints, coupling matrix and reciprocal-period expansion already chosen. It fixes the adjoint field, pin coefficients, central profile, tangent family, central reciprocal period and its parameter derivative. It also makes the generic fitted tangent set empty.

These identities are the binding assumptions for Lemma B.12. The free-family identity is stated for all parameter vectors; the coupling identity is restricted to $K$. The empty fitted set makes its fitted-potential subconditions vacuous on this route; all parameter tangents are handled by the free-family estimates. A checker must still verify the free-family bounds and their shared weights. It cannot infer them from the absence of fitted data or choose different tangent fields for different checks.

**Lean anchor:** `Breakdown.CellReduction.Instantiation.AdjointEntryLinks`.

<a id="14"></a>

### 14. potential_entries: construct admissible integration-by-parts fields

The `potential_entries` field supplies the shape-valid potentials and compact pin fields used in the adjoint defect identity. It validates each active potential's shape parameters and potential series, validates the pin entry, and identifies the defect record's centre potential and pin data with those constructions. It also identifies their pinning matrix with $D$'s pin field.

This is the formal coefficient-level implementation of the fields preceding Lemma B.12 and the regularity needed for (B.51). The checker validates knot order, effective endpoint orders, exact row vanishing, normal-flux joins, compact support and constructor equalities. The source theorem `potentialData_of_series`, supplied with `potentialParts_holds`, converts the series conditions to analytic properties. The separate `PotentialNorms` checks in the next field certify sizes of the resulting objects.

The source's pressure, flux and spline predicates are more explicit than the printed coefficient specification. These facts permit a precise Lean-side account, but they do not identify the authors' unreleased serialisation or prove that its program implements the same fields.

**Lean anchors:** `Breakdown.CellLayerSystem.PotentialEntriesBounded`; `Breakdown.PotentialShape.IsPotentialSeries`; `Breakdown.PotentialShape.IsPinShapeEntry`; `Breakdown.PotentialShape.potentialData_of_series`.

<a id="15"></a>

### 15. adjoint_defect: close the adjoint error budget

The `adjoint_defect` field bounds the weak adjoint error after the potential decomposition, uniformly over the parameter set. Its 18 clauses bound parameter coordinates, the centre potential norms and remainder, any fitted terms, the weighted free-family value and dual errors, the time derivative's dual norm, pin approximation and rounding errors, the pin coefficient norm and the final sum charged to the certificate.

A dual-bound witness splits the remainder into two pieces. One uses a distinct family of helical component/frequency/order triples with the patched denominator $(|n|+1/2)^2$; the other uses the ordinary remainder bound. Duplicated triples must be merged before squaring, or rejected, because cross terms otherwise disappear. The first two helical components carry factor $1/2$ and the axial component factor 1.

The pin-rounding clause is an operator bound for every real coefficient vector, so it becomes a Gram-matrix inequality when the fields are represented finitely. The free dual clause chooses one family of bounds and requires its weighted square sum to fit the common budget. These witnesses must be reused consistently. Lemmas B.11 and B.12 then turn the estimates into the adjoint inequality required by Theorem 7.1.

**Lean anchors:** `Breakdown.AdjointDefect.AdjointDefectBounded`; `Breakdown.AdjointDefect.PotentialNorms`; `Breakdown.AdjointDefect.DualBounded`; `Breakdown.AdjointDefect.AzimuthalBounded`.
<!-- /passage:sec-the-fifteen-fields-of-cellsystemcondition -->

<a id="appendix-c"></a>

## Appendix C. How the approximate data were found

<!-- passage:sec-appendix-c -->

Appendix C describes the authors' numerical discovery and preparation of inputs. The following is context from that account, rather than a replay of its computation or a proof that its proposed certificate satisfies the finite conditions.

The authors report a profile with azimuthal symmetry order $\kappa=19$ and period about $0.36$ in self-similar time. Its harmonic decomposition contains two patterns rotating in opposite directions, exchanged by the half-turn symmetry. They use the same divergence-free harmonic and spline representation as Appendix B. The radial phase is

$$
f(x)=\frac{2\pi}{\bar S}\log(1+x/r_c^2),
\qquad x=|y|^2.
$$

Write $s_{\rm sim}=\bar S\theta$ for the unnormalised self-similar time. For the selected harmonic phase index, the large-radius phase involves $2\log|y|-s_{\rm sim}$. Under the self-similar change of variables, this becomes a function of the original spatial point and the chosen blow-up time. Incorporating that phase into the basis removes a logarithmic radial oscillation that the spline coefficients would otherwise need to resolve arbitrarily far out. This is the numerical motivation for the radial phase and the compactified exterior cells.

The computed equation is tested against divergence-free fields, which remove the pressure term from the weak equations. Trial fields use radial decay exponent $h=1$, while test fields use $h=3$. Products of harmonics are evaluated through angular grids, and cell integrals use Gauss quadrature. A phase condition fixes the free time translation, while the period is an additional unknown. The authors describe a Newton iteration with a flexible GMRES linear solver, matrix-free application of the linearisation and a block preconditioner arranged using nested dissection. These procedures generate approximate coefficients and directions; their convergence is separate from verification of the final inequalities.

The computation follows a continuation path through modified scaling, viscosity and forcing parameters, then returns to the desired unforced equation and refines the discretisation. Sensitive directions are extracted using a Lanczos calculation. They guide the actuator choices, the pin constraints and the parameter directions. Cutoffs and smoothing produce fields with the required support and divergence properties, and finite coefficients are rounded to the representation used by the proposed checker. Approximate adjoints and parameter directions help reduce the defect and the bounds required in B.10–B.13. The pin-rounding error $c_\Xi$ and the other finite error allowances are where the later certificate accounts for these representation changes.

Appendix C therefore explains why one might expect the finite conditions to be attainable and how candidate data are generated. The Lean route in B.14 starts after those candidates have been decoded into the specified objects and every required bound has been supplied with a proof. No cited declaration proves that the reported Newton, Krylov, quadrature or Lanczos computations produced a valid concrete certificate. [Authors' account: Appendix C, pp.70–75.]
<!-- /passage:sec-appendix-c -->

## What a numerical check must establish

<!-- passage:sec-what-a-numerical-check-must-establish -->

The interface between the numerical calculation and the formal implication is

$$
\operatorname{Accept}(b)
\Longrightarrow
\exists(D,X,R,T,Y,N,B),\quad
\operatorname{decode}(b)=(D,X,R,T,Y,N,B)
\quad\text{and}\quad
\operatorname{CellSystemCondition}(D,X,R,T,Y,N,B).
$$

Here decoding includes the representation identities that tie every bound and matrix to the same fields. A digest can identify a byte string, but it supplies neither those identities nor the inequalities. The conditions described above provide the mathematical specification against which a released implementation can be compared.

Rigorous ball arithmetic addresses the error in arithmetic on the values actually represented. The enclosing intervals must cover every point of the intended spatial and parameter domain. Merely containing zero does not establish that an exactly required coefficient is zero; an exact enclosure $[0,0]$ does. A failed sign test can also mean that the enclosure is too wide. These are the documented [Arb inclusion and comparison semantics](https://arblib.org/using.html) and [FLINT comparison conventions](https://flintlib.org/doc/guide/types/ball-arithmetic.html), applied here to the specified coefficient conditions.

For matrix checks, first identify the precise real or Hermitian form and the space on which it must be nonnegative. Constructing the full generator of `InRowRange` and restricting the form to its image is one sound route explained in the earlier obligations account. Preserve real actuator directions and the independent real and imaginary parts of the permitted complex directions. A matrix factorisation then checks that restricted form. FLINT's [Cholesky contract](https://flintlib.org/doc/arb_mat/_arb_mat_cholesky_banachiewicz.html) certifies the symmetric matrix represented by the supplied lower triangle; symmetry and correct assembly therefore need their own justification. Exact gauge directions also prevent replacing every semidefinite obligation by a strict positive-definiteness test.

A useful returned numerical record would identify the byte digest and decoder, the exact seven reconstructed inputs or a reproducible representation of them, the fifteen branches discharged, and the bounds or exact identities that discharged them. It would distinguish an affirmative enclosure from an undecided comparison. That record would make the reported computation assessable against the Lean condition. No such execution record is created by this prose reconstruction.
<!-- /passage:sec-what-a-numerical-check-must-establish -->

