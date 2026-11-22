
<!-- passage:front -->
# Checking the Navier–Stokes certificate

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](cell-layer-fidelity.md) · **certificate checker**

**Commit [`ad53419`](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546), 20 November 2026.**
Companion to [the statement comparison](paper.md).

The Lean package proves that data satisfying `CellSystemCondition` give
blow-up on $\mathbb R^3$ and on $\mathbb T^3$. The authors report that a
certificate, checked outside Lean with 128-bit Arb interval arithmetic,
satisfies the conditions written in Appendix B. Neither the certificate nor
the checking program is public yet; the paper gives the certificate's
SHA-256. What closes the argument is one implication:

$$
\text{Accept}(\text{bytes})\;\Longrightarrow\;
\text{CellSystemCondition}(\text{decode}(\text{bytes})).
$$

It has two halves. The decoder has to build the actual objects the Lean
predicate quantifies over (functions, parameters, cells, matrices,
constraints) from the bytes. The checker then has to establish every
condition for those objects, over the whole parameter set, every cell, the
omitted modes and the unbounded exterior. Correct interval arithmetic
applied to the wrong expression, or to a region that misses a corner,
establishes nothing about the predicate. This page records what that
implication requires, read from the Lean source, so that the program can be
judged against it when it appears.
<!-- /passage:front -->

## 1. The size of the predicate

<!-- passage:sec-1-the-size-of-the-predicate -->

`CellSystemCondition` has fifteen fields over seven data arguments. Tracing
them through the definitions they use reaches 176 local predicate
declarations, all of which resolve in the source. Expanded into terminal
comparisons, structural identities, analytic side conditions and existential
witnesses, they give about 1,630 schema records. These are not 1,630
numerical tests: some are alternative branches, some share one witness, and
one predicate can be instantiated with many arguments. A flat checklist that
loses those distinctions checks a different proposition.

Two counts from the Lean structures help with planning a parser: the five
statement files declare 228 structures with 2,172 direct fields. Many fields
are functions, sets or proofs, so this is an inventory of the interface, not
of the numbers in the file.
<!-- /passage:sec-1-the-size-of-the-predicate -->

## 2. Where a natural implementation checks too little

<!-- passage:sec-2-where-a-natural-implementation-checks-too-little -->

Each item below follows from a definition in the source. None is a claim
that the authors' program makes the mistake; they are the tests to run on it.

**Quadratic forms are required on a larger space than the cell's
coordinates.** `InRowRange` ([`CellLayerChallenge.lean:6547`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L6547)) constrains only
the coordinates whose row reason is not `.unused`, and only up to gauge and
pressure-head terms with complex coefficients; unused coordinates and port
coordinates are free complex numbers; the two actuator blocks are free real
numbers. The local estimates in `PotentialConditions.kept_le`,
`PairingConditions.kept_le` and `EliminationConditions.residual_value_le`
must hold for every such vector. A finite real matrix generates the whole
space: mask the row, gauge and pressure-head columns to the used
coordinates, then take the real slaved columns, each gauge and resolved
pressure-head column together with $i$ times it, the unit vectors of the
unused and port coordinates with $i$ times them, and real unit vectors for
the actuators. Writing $E_K$ for this matrix,

$$
\operatorname{InRowRange}(K,x)\iff\exists a\in\mathbb R^{m_K},\;x=E_Ka,
\qquad m_K=s+2g+2r_K+2u_K+2p_K+2k,
$$

and a Hermitian form $H$ becomes the real form $a^{\mathsf T}\operatorname{Re}(E_K^*HE_K)a$.
The columns need not be independent. Checking the form only on the image of
the cell embedding misses directions the predicate includes; the matrix
$\operatorname{diag}(0,-1)$ is nonnegative on the first coordinate and
negative on the second.

**Missing table entries need the right continuation, which is not always
zero.** For sparse spline and jet coefficients, `VanishesBeyond`
([`CellLayerChallenge.lean:6853`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L6853)) reads an out-of-range breakpoint as the
support radius, which makes its guard true, so every coefficient past the
stored list must be exactly zero. For the infinite orthonormal cell bases,
zero is wrong: the bases need positive leading coefficients at every degree.
The library already proves the right continuation
(`FracCell.extendBases_of` with `orthoFamily_spec`), and a decoder must use
it or prove that its own agrees. `actuator_model_regular`
([`CellLayerChallenge.lean:6050`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L6050)) quantifies over every natural index, not
only those below the number of actuators.

**Scales may be zero.** `ScaledJetAxis.convert`
([`CellLayerChallenge.lean:4140`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L4140)) inverts `scale.getD k 1`, and
`HasSymmetricScale` requires only the right length and symmetry. At a zero
scale Lean's inverse is zero and the positive-order entries vanish; the
bubble terms likewise divide by breakpoint gaps. A decoder must reproduce
this behaviour or establish that scales and gaps are nonzero.

**Active harmonics can be over-approximated instead of decided.**
`modelLabels` ([`CellLayerChallenge.lean:5753`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L5753)) keeps a label when some model
coefficient is nonzero somewhere on the cell, and its three users
(`group_link`, `groups_cover`, `rows_groups_cover`) demand coverage for every
kept label. Checking coverage for every label in the four declared support
sets therefore implies the condition, and removes the need to decide whether
a tiny coefficient is zero. Dropping a label requires exact vanishing of all
24 scalar polynomials involved (3 velocity, 3 vorticity, 9 strain and 9
vorticity-gradient components); a small value, or an interval containing
zero, is not exact vanishing.

**Mode triples must be distinct.** `AzimuthalBounded`
([`CellLayerChallenge.lean:3576`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L3576)) asks for an injective family of
(component, frequency, order) triples. Two equal amplitudes $g$ in one channel
contribute $\|2g\|^2=4\|g\|^2$, not $2\|g\|^2$, so duplicates must be merged
before the norm is formed. The weight is $1/(|m|+\tfrac12)^2$, which differs
from $1/(m^2+\tfrac14)$, with component weights $\tfrac12,\tfrac12,1$ and the
factor $2\pi$ in time.

**A matrix routine must see the matrix the predicate means.** A Cholesky or
LDL routine that reads the lower triangle certifies the symmetric matrix that
triangle determines: $\begin{pmatrix}1&100\\0&1\end{pmatrix}$ has the
identity's lower triangle, yet $(1,-1)A(1,-1)^{\mathsf T}=-98$. The stiff-frame
estimate uses columns of `frame`; reading rows instead can accept a bound of 1
where the true squared value is 4. And an interval comparison that returns false may
mean "undecided": $[-0.1,0.2]$ proves neither positivity nor nonnegativity.

**The parameter set is a box times an ellipsoid, and affine quantities have
exact extremes on it.** For
$K=\{q:|q_j|\le r_j\ (j\in J),\ \sum_{j\notin J}(s_jq_j)^2\le R^2\}$ and
$F(q)=a_0+\sum_ja_jq_j$,

$$
\min_KF=a_0-H_K(a),\quad \max_KF=a_0+H_K(a),\quad
H_K(a)=\sum_{j\in J}|a_j|r_j+R\Big(\sum_{j\notin J}(a_j/s_j)^2\Big)^{1/2},
$$

by choosing endpoints in the box and Cauchy–Schwarz in the ellipsoid. The
source gives the reciprocal period as an affine function of the parameter, so
$f_0-H_K(f)>0$ proves a positive period on all of $K$, and
$f_0-H_K(f)\ge1/P_{\max}$ gives the upper bound too. Sampling cannot replace
this: on the unit disk $F=\tfrac{11}{10}-q_1-q_2$ is positive at the centre and
at the four axis points, and equals $-\tfrac3{10}$ at $(\tfrac35,\tfrac45)$. Most
quantities, including anything that depends on the radial phase, are not
affine and need their own enclosures.

**Several conditions share work.** The enclosure constants checked at the
root are the ones the continuum branch needs. `IsBoxUniform.bounds_eq`
transports the support object across the parameter set. On this path
`AdjointEntryLinks.fitted_empty` ([`CellLayerChallenge.lean:4022`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean#L4022)) makes the
fitted adjoint set empty, so the fitted bounds hold vacuously. The step
profile's tail condition reduces to the last cell polynomial being identically
one.
<!-- /passage:sec-2-where-a-natural-implementation-checks-too-little -->

## 3. What the library already proves, and what it takes as input

<!-- passage:sec-3-what-the-library-already-proves-and-what-it-takes-as-input -->

Much of the infinite and analytic content is proved in Lean, with finite data
as input: the extension of checked finite bases to infinite orthonormal ones,
spline joins and scaled-jet facts, the logarithmic radial phase, step-phase
regularity, pressure continuity and periodicity, the moved profile and adjoint
constructions, potential-series derivatives and decay, and the azimuthal dual
estimate (`AdjointDefect.remainderAzimuthalHolds_proof`).

Some routes take implications as arguments. `ScalarShape.isWeightValues_of_conditions`
([`Breakdown/CertCell/ShapeScalarStatements.lean:369`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L369)) assumes six:
`MeshOfRational`, `JoinsOfCoefficients`, `NonnegOfCoefficients`,
`CoreOfCoefficients`, `FlatOfCoefficients` and `StepPositiveOfEntries`. We
found no closed proofs of them under those names, so the bridge from a
rational representation to these properties is a decoder obligation unless
it is proved. `ExtendSegmentStatement` is declared in
[`ReductionPointwiseDefs.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean) and neither proved nor used.
<!-- /passage:sec-3-what-the-library-already-proves-and-what-it-takes-as-input -->

## 4. A schema before the release

<!-- passage:sec-4-a-schema-before-the-release -->

Appendix B.1 gives mathematical representations, not a file format. The
missing choices are concrete: coefficient encodings, tensor order, sparse
defaults, pressure conventions, local-to-global assembly, and the encodings of
objects Lean states abstractly. A provisional schema can still fix what is
known. A harmonic label $(\iota_1,\iota_2)$ stands for temporal frequency
$2\iota_2-\iota_1$ and azimuthal frequency $19\iota_1$; normalized time has
period one; cylindrical integrals carry a radial factor; and exact zero, a
non-strict inequality and a strict margin are different checks. Constants
tied by $\pi$ should be stored as exact expressions, because rounding two
quantities separately can break an identity the tail needs.

That last point gives a cheap early test. If a leading tail mode decays like
$R^{-1}$ with radial phase $l\,c_\alpha\log R$, and the phase coefficient and
reciprocal period depend affinely on the parameter,
$c_\alpha=c_0+k\cdot\alpha$ and $1/S(\alpha)=f_0+\varsigma\cdot\alpha$, then
with $c_0=4\pi f_0$ a mode with $l\ne0$ leaves an $R^{-1}$ residual unless
$(k-4\pi\varsigma)\cdot\alpha=0$. Its square integral grows linearly in the
cutoff radius, so a mismatch invisible on a bounded domain makes the full
residual infinite. The Lean hypotheses already exclude this; the test catches
an incompatible file before any expensive bound.

The size of the file is unknown. Raw coefficients of one complex polynomial
field cost about $4bHC(d_r+1)(d_\eta+1)$ bytes for $H$ harmonics, $C$
rectangles, bidegree $(d_r,d_\eta)$ and $b$ bytes per real number; 128
harmonics, 256 rectangles, bidegree 12 and 16 bytes give 338 MiB before
pressure, auxiliary fields and matrices. That is a scenario, not an estimate.
<!-- /passage:sec-4-a-schema-before-the-release -->

## 5. Three ways to check it

<!-- passage:sec-5-three-ways-to-check-it -->

| Route | What it adds | Rough effort | What it leaves open |
|---|---|---|---|
| Rerun and read the authors' Arb/FLINT program | Reproducibility; a reading of the decoder against §2 | days to rerun, weeks to audit | errors shared by one implementation; the decoder's meaning |
| A second checker with a different interval library (MPFI, or Julia `IntervalArithmetic` with BigFloat) and separately derived formulas | Independent evaluation of the same obligations | 1–3 weeks for a prototype; a few months in full | errors in the shared specification |
| Check the numerical witnesses inside Lean | The numerical premise becomes a Lean proof about the actual instance | a pilot in weeks; the whole in many expert-months | the formal reading of the bytes; the trusted kernel |

The efforts are planning guesses that depend on the real format and margins.
A second checker gives the most independence per unit of work if it differs
in more than its arithmetic library. Matrix positivity in particular can be
split into finding and checking: an untrusted routine proposes a rational
matrix $C$, the checker encloses $N=C^{\mathsf T}HC$, and strict diagonal
dominance $\underline{N_{ii}}-\sum_{j\ne i}\overline{|N_{ij}|}>0$ in every row
proves $N$, hence $H$, positive definite once $C$ is square and invertible.
Weighted row norms built from a Gram matrix need no inverse square root when
the generators split into orthogonal blocks of constant weight:
$p^{\mathsf T}G^{-1/2}TG^{-1/2}p=\sum_bt_b\,p_b^{\mathsf T}G_b^{-1}p_b$, which an
exact LDL factorization evaluates. A standard-library prototype of these
witness checks in exact rational arithmetic passes its sixteen synthetic test
cases, including the inconclusive and invalid ones it is meant to refuse.

A residual diagnostic independent of the collocation equations also exists.
For a smooth divergence-free period-one field solving the similarity equation
with residual $R$, set $\Omega=\operatorname{curl}W$, $E=\int|\Omega|^2$,
$D=\int|\nabla\Omega|^2$ and $T=\int\Omega\cdot(\Omega\cdot\nabla)W$ over a
period and all of space. Then $D+\tfrac14E-T=-\langle R,\Delta W\rangle$, so

$$
\|R\|\ge\frac{|D+E/4-T|}{\sqrt D}.
$$

On the test field $W=(-y,x,0)e^{-|x|^2}$ the residual norm is about 6.145 and
the bound gives 6.079. Applied to the certificate it must account for the
finite-dimensional force and for the interfaces between spline pieces.
<!-- /passage:sec-5-three-ways-to-check-it -->

## 6. Order of work

<!-- passage:sec-6-order-of-work -->

Before the release: the conventions of §4, sparse indexing, polynomial
identities and joins, the witness checks of §5, and receipts that name for
every obligation its expression, domain, enclosure, threshold and strictness,
built from a list of obligations made independently of what the checker
reports doing.

At the release: keep the exact bytes and program versions, rerun the authors'
program, and record the distribution of margins. Then take one cell from its
coefficients to its final matrix inequality, choosing one near the axis, a
seam or the exterior early, since an interior cell exercises the least.

After that: extend to every cell, the weakest margins and the largest blocks,
and move the well-specified primitives into Lean.

Appendix C (period about 0.36, 19-fold symmetry, adaptive Newton continuation)
is context, not a starting point: without the seed, partitions, continuation
values and tolerances, recomputing the profile is a research project, and a
failure to find it would say little. One coarse profile in the stated
representation, with its residual recipe, would make independent residual
checks possible before the full certificate.
<!-- /passage:sec-6-order-of-work -->

## Precedents

<!-- passage:sec-precedents -->

| Work | Date | What it shows |
|---|---|---|
| [Chen–Hou](https://arxiv.org/abs/2305.05660) | preprints 2022–23 | Analytic estimates with INTLAB computations can carry a blow-up proof; public code allows reruns, which is not reimplementation. |
| [Wang–Lai–Gómez-Serrano–Buckmaster](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.130.244002) | PRL, June 2023 | Finding a profile numerically and certifying it are separate results. |
| [van den Berg–Breden–Lessard–van Veen](https://arxiv.org/abs/1902.00384) | preprint 2019 | A posteriori validation of forced Navier–Stokes periodic orbits, at 6 to 95 CPU-days per orbit. |
| [Shavit–Wang–Buckmaster](https://arxiv.org/abs/2611.07395), the paper's [82] | November 2026 | A Lean argument that keeps its numerical inputs as explicit hypotheses. |

Sources: [`CellLayerChallenge.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/CellLayerChallenge.lean) at the lines given; `Breakdown/FracCell/`,
[`Breakdown/CertCell/ShapeScalarStatements.lean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean); paper Appendix B.1, (B.16),
the paragraph after Proposition B.14, Appendix C. The derivations in §§2, 4
and 5 are hand mathematics checked with exact arithmetic or symbolic
computation; none of them is a Lean proof.
<!-- /passage:sec-precedents -->

