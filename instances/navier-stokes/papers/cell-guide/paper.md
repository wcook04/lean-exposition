
<!-- passage:front -->
# Reading the cell certificate

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · **cell layer guide** · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

Annotations for `CellLayerChallenge.lean` at `ad53419de079eb8f95f60313473374624a348546`.

This file describes the mathematical objects and conditions to which a numerical certificate must be connected. Start with the fifteen fields of `CellSystemCondition`, then follow the objects that those fields constrain. The earlier parts of the file supply representations, local inequalities and assembly interfaces. A value of one of the data structures is not evidence that its associated conditions hold.

The accompanying catalogue covers all 787 non-theorem declarations and the three final theorem statements. It gives a gloss for every one of the 1,672 directly declared structure fields. These counts concern source commands and direct fields. They exclude automatically generated constructors, recursors, inherited projections and imported declarations. `FracCellData` also inherits the 46 fields of `FracCertData`; the catalogue records that inheritance separately.

[The cell declaration reference](../navier-stokes-cell-reference/paper.md) contains the same annotations as a reading document.
<!-- /passage:front -->

<a id="1"></a>

## 1. What the final condition says

<!-- passage:sec-1 -->

`CellSystemCondition` requires all fifteen fields for the same seven arguments: the certificate data, their concrete field instances, the cell-calculus data, the tree, the assembly entries, the coercivity numbers and the reduction entries. Existential witnesses inside one field retain their original scope. Rechecking an inequality with a fresh witness does not establish a conjunction that requires one shared witness.

The three closing statements are conditional: data satisfying that complete condition give breakdown on space, on the torus, and on both. The readable challenge contains `sorry` stubs at those statements. The corresponding wrappers with proof bodies are at `Solution.lean:338–355`. The source comparison in this return checks their signatures and records both locations. It does not run Lean or Comparator. The input packet's build report and pending replay status remain separate evidence. [Source: final condition and statements, lines 7027–7080; implementation bindings in source_bindings.json.]

The numerical step still has a precise target:

\[
\operatorname{Accept}(b)\Longrightarrow
\operatorname{CellSystemCondition}(\operatorname{decode}(b)).
\]

Here `decode` must produce the actual functions, finite sets, matrices, parameters and auxiliary witnesses used by the predicate. Correct arithmetic on a nearby expression cannot supply this implication. The released source does not contain the certificate bytes or the authors' checker. Appendix B describes a mathematical representation and leaves some of its coefficient and matrix conditions to the formalisation. [Sources: [the certificate-checker page](../navier-stokes/certificate-checker.md); Appendix B, printed pp.49–50 and 69.]

### The fifteen required fields

| Field | What must be supplied or established | Paper location |
|---|---|---|
| `cell` | The instantiated fields, cell calculations, tree, pairing errors, enclosure witnesses, geometry and fixed constants fit together. | B.1–B.3; (B.19), (B.21)–(B.43) |
| `shape_valueSets` | Positive period and weight, constant weight, and the required harmonic-set relations for the reference fields and bounds. | B.1–B.2, pp.50–54 |
| `entry_conditions` | The local forms, row representation, eliminated modes, exterior cover and tree entries satisfy their joint obligations. | B.3, especially (B.26) and (B.43); some formats are omitted |
| `enclosure_numbers` | The particular coercivity numbers chosen at the top level satisfy the parameter-uniform enclosure conditions. | (B.19) |
| `coerciveL2_ge` | The chosen linear coercivity constant is large enough for the multiplier-weight bounds. | First bound in (B.22) |
| `coercivePin_ge` | The pinning constant is large enough for the pin weight and coercivity. | Second bound in (B.22) |
| `certificate` | The numerical and analytic certificate clauses include the residual bounds, smallness inequalities, frame condition, inclusion bounds and strict nontriviality. | Conditions listed in B.4 and §7 |
| `instantiation` | The profile, pressure and adjoints are the functions built from the specified shapes. | (B.6)–(B.9); pressure data on p.52 |
| `offset_expansion` | The polynomial expansion and tail control establish the required adjoint offsets. | Lemma B.13; (B.57)–(B.59) |
| `shift_numbers` | Central and parameter-dependent errors imply the shift bounds. | Lemma B.9; (B.47)–(B.48) |
| `frozen_form` | The reference profile and shift estimates bound the frozen linearised form. | (B.47)–(B.49) |
| `adjoint_quadratic` | The L² or L³ estimate controls the nonlinear pairing with each selected adjoint. | Lemma B.10 |
| `adjoint_links` | The adjoints, offset data and pinning fields agree with the objects used by the reduction. | Setup of Lemma B.12 |
| `potential_entries` | The potential series and pin fields satisfy the explicit representation conditions and identify the required fields. | The format is omitted on p.67; its analytic purpose is (B.51) |
| `adjoint_defect` | The potential, remainder and pin errors give the adjoint defect bound for every selected index. | Lemmas B.11–B.12; (B.50)–(B.53) |

This table describes roles. Each exact field, its local source span and its interpretation appears under `Breakdown.CellLayerSystem.CellSystemCondition` in the catalogue. The complete condition is finer than this table. [Source: lines 7030–7046; prior cell-layer fidelity table.]
<!-- /passage:sec-1 -->

<a id="2"></a>

## 2. The notation to keep separate

<!-- passage:sec-2 -->

| In the paper | In the cell source | Reading rule |
|---|---|---|
| Parameter dimension \(n\) | Usually `k` and `Fin k` | Do not confuse it with an azimuthal wave number. |
| Symmetry order \(\kappa\) | `D.azimuthOrder` | The final cell hypothesis requires at least 3. The value 19 belongs to the reported numerical construction, not to this generic declaration. |
| Harmonic label \(\iota=(\iota_1,\iota_2)\) | An integer pair | Its temporal frequency is \(2\iota_2-\iota_1\); its azimuthal frequency is \(\kappa\iota_1\). |
| Normalised time \(\theta\) | Often the argument `σ` | Time has period one at this layer. |
| Compactified radius \(\sigma=|y|/(|y|+L)\) | A coordinate of a shape or spline chart | It is a spatial coordinate; it is not the time argument above. |
| Physical cylindrical radius \(r\) | `cylRadius` or the first component of a cell point | It differs from spherical radius \(|y|\). |
| Cell \(Q=[r_1,r_2]\times[z_1,z_2]\) | `CellBox` | Its spatial solid uses \(|y_3|\), so the reflected half is included. |
| Gradient and velocity pair \((G,v)\) | A vector indexed by `Fin 12` | Nine gradient entries precede three velocity entries. The gradient block is not automatically symmetric. |
| Global real unknowns \(x_g\) | Slaved and free coordinates of the tree | Cell rows are complex, with separate reality constraints on the two actuator blocks. |

The label conventions implement (B.2), while the cell and chart conventions implement (B.3), (B.10) and the discussion preceding (B.26). [Source: lines 214–255, 331–337, 1700–1759 and 5589–5622; exact declarations are linked in the catalogue.]
<!-- /passage:sec-2 -->

<a id="3"></a>

## 3. The groups

<!-- passage:sec-3 -->

### Analytic interfaces

The file begins with abstract certificate and cell data, including profiles, derivatives, rows, pinning fields, model forms and error budgets. These interfaces explain what the later representations must provide. They are not a byte format. A function-valued field still needs a mathematical interpretation and the relevant regularity and identity conditions. The reader should distinguish this general interface from the specialised `CellLayerData` used by the final condition. [Sources: `FracCertData`, `FracCellData`; Appendix B's opening and B.1.]

### Data representation

Finite coordinate types, polynomial coefficient containers, complex quadratic forms and coordinate injections determine what a stored number means. A coefficient must be attached to the correct basis, component and normalisation. A matrix merely being square does not make it positive, Hermitian or invertible; those are separate conditions. Labels such as `inverseWeightedSq` describe an expression whose useful interpretation depends on its hypotheses. [Sources: `Coupling.quadForm`, `Coupling.inverseWeightedSq`, `CellPoly`, and the coordinate declarations.]

### Mesh and cells

The mesh specifies rectangles, resolved harmonics, tested row harmonics and eliminated bands. Validity requires genuine cell widths, negligible overlaps and the stated set relations. Cells touching the axis have a special weight and only zero first label coordinate among their resolved harmonics. The exterior is the complement of the mesh in the closed quarter plane. A finite mesh therefore does not remove the exterior obligations. [Sources: `CellBox`, `IsCellBox`, `CellMesh`, `IsCellMesh`; B.1 and B.3.]

### Splines and jets

Spline values are built from polynomial pieces and partitions. Joined data control derivatives at seams; Hermite data instead encode endpoint jets and interior bubble terms. The scaled-jet conversion is another coordinate map and must be applied before interpreting its coefficients as those of the unscaled spline. Some helpers are total on invalid or degenerate inputs. Their callers supply the active geometry and regularity conditions, while node-scale positivity is not a general requirement of `HasSymmetricScale`. [Sources: `SplineJoins`, `IsJoinedSpline`, `JetAxis`, `ScaledJetAxis`, `IsScaledJetEntry`; B.1, pp.51–52.]

### Harmonics and symmetry

Integer labels describe temporal and azimuthal frequencies, with separate operations for conjugation and reflection. Both a lattice label and its physical frequency pair have Lean type `ℤ × ℤ`, so the type alone cannot distinguish those meanings: `labelFlip` acts on the lattice label and `flipLabel` acts on the physical pair. Compressed data choose representatives of symmetry orbits, then reconstruct the remaining coefficients with prescribed signs and conjugations. A decoder must handle representatives fixed by a symmetry consistently. The reference model's active labels require exact nonvanishing information only if a checker tries to discard declared labels. [Sources: `labelTime`, `labelAzimuth`, `labelFlip`, `flipLabel`, the compressed-field declarations, and `Assembly.modelLabels`; (B.1)–(B.2), B.1.]

### Shape bounds

Compactified-radius charts turn decay and derivative estimates into bounds on functions of bounded coordinates. The corresponding conditions include the endpoints, origins, symmetry constraints, uniform parameter dependence and the supplied Hessian convention. Bounds on a sample of chart points do not establish a bound throughout a chart. In particular, Hessian values replaced on knot sets are interpreted through weak-derivative and almost-everywhere arguments already present in the library. [Sources: `ScalarShape`, `GivenShape.ShapeValuesFacts`, `GivenShape.IsScaledJetEntry`; B.1–B.2 and the prior trust audit.]

### Rows and pins

Polynomial row generators become real field rows through a harmonic convention and Gram normalisation. The pairing matrix, row weights and positivity assumptions jointly implement the construction surrounding (B.11). Pin fields encode the constraints from (B.10), with their own reflection signs and support. A reader should follow which object is a raw generator, which is an orthogonalised row and which constant includes the coercivity factor. [Sources: `RowValues`, the row-normalisation declarations, `Instance.IsInstanceEntry`, `PotentialShape.PinShapeEntry`; (B.10)–(B.11).]

### Potentials

The adjoint reduction replaces difficult pairings by norms of potentials and controlled remainders. The paper gives the analytic consequences in (B.51) but does not specify the full potential coefficient format. `PotentialSeries` and its validity predicate supply one explicit sufficient representation. The meanings of the flux indices, the pressure correction and weak derivatives matter when reading (B.52). A sign or transpose should be compared after reconstructing the operator it represents. [Sources: `AdjointDefect.PotentialData`, `PotentialShape.PotentialSeries`, `IsPotentialSeries`, `PotentialEntriesBounded`; p.67, (B.51)–(B.53).]

### Local forms

For each resolved cell mode, the source builds finite coordinate forms and measurable matrix fields acting on \((G,v)\). Lower bounds, absorption costs and polynomial approximation estimates express the local content used in (B.25)–(B.27). The quantifier over vectors is essential: a form checked on selected basis vectors or just on the physically realised cell embedding can miss the mixed directions demanded by the predicate. [Sources: `CellCalculus.IsLeafValues`, `CellCalculus.CellCalculusConditions`, `Assembly.EliminationConditions`; B.3, pp.57–60.]

### The tree

The tree carries local matrices to global coordinates and assembles a lower bound from node inequalities. It has an actual root, finite coordinate sets, pivot information, error enclosures and negative columns. The complex version must be translated into the prescribed real columns with the stated scaling and signs. Column counts are part of the dimension argument, so replacing repeated columns by a rank count needs a justification. [Sources: the tree enclosure predicates, `TreeEntry`, `TreeConditionsGiven`, `TreeRowConditions`; (B.38)–(B.42), Lemma B.7.]

### Assembly

Assembly relates potential, pairing, eliminated-mode, row, credit and global forms. It also describes the subspace on which the local comparisons are required. `InRowRange` leaves unused and port coordinates free over the complex numbers, adds gauge and pressure-head directions on used rows, and constrains the two actuator blocks to be real. The field `bandProjection` is a supplied matrix: its name alone grants no orthogonality or idempotence. [Sources: `Assembly.PotentialData`, `PotentialConditions`, `PairingConditions`, `InRowRange`, `CellLayerEntryConditions`; (B.26), (B.33)–(B.34), (B.43).]

### Exterior and omitted modes

Finite lists of regions can represent conditions on infinitely many harmonics and an unbounded domain. A region carries both geometry and a mode set; validity, membership, coverage and charge inequalities have to agree. Exterior regions also have measurability and overlap conditions, with the ray estimates implementing the Hardy-type argument around (B.30)–(B.31). Checking finitely many harmonics or a large ball does not establish those quantified conditions. [Sources: `TailBand`, `IsOffModeCover`, `IsExteriorCover`, `FarFieldConditions`; (B.28)–(B.37).]

### The fifteen fields

The final group collects the certificate clauses, the numerical constants, the profile and potential reductions, and their joint hypothesis. It is the entry point for assessing a candidate certificate. The generic extended-certificate interface permits some options that disappear after specialisation. For example, the cell instantiation fixes the pin target in a way that makes the specialised target gap zero; that cannot be inferred from `CertificateClauses` alone. [Sources: `CertificateClauses`, `ReductionEntries`, `CellSystemCondition`, `InstantiationBounded`; the existing cell-layer fidelity finding.]
<!-- /passage:sec-3 -->

<a id="4"></a>

## 4. Five decoder decisions to make explicit

<!-- passage:sec-4 -->

**Defaults are part of the definition.** The file contains eight declarations with literal `getD` calls. Their defaults include 0, 1 and a support radius. In `VanishesBeyond`, an out-of-range breakpoint is the support radius, so the support guard becomes true and forces the corresponding tail coefficients to vanish. In the scaled-jet conversion, the default scale is 1 and the default bubble normaliser is 0. A universal zero-fill rule changes these objects. [Source: default inventory in decoder_index.json; Lean's documented `List.getD` semantics, sources.md.]

**A zero scale has defined semantics.** A positive-order node coefficient is multiplied by a power of the inverse scale. At scale zero that factor is zero in Lean; the order-zero factor remains one. A checker can reproduce the totalised map, or justify stronger nonzero-scale assumptions before using an invertible change of basis. These are different implementation choices. Rejecting zero scales is not a newly discovered theorem hypothesis. [Source: `ScaledJetAxis.convert`, lines 4140–4147; `HasSymmetricScale`, line 4151; round-three guard G7.]

**The domain of a quadratic form must survive realification.** With used row coordinates, gauge directions, pressure heads, unused coordinates, ports and two real actuator blocks, the relevant space is a real-linear subspace of a complex coordinate space. Form the generator matrix for that complete space before checking a real quadratic form. A diagonal form with entries 0 and −1 passes on the first coordinate and fails on the omitted second coordinate. This elementary example explains the scope error; it does not exhibit a failure of the full certificate. [Source: `InRowRange`, lines 6547–6553; prior checker page and finite-reduction audit.]

**Coverage can be conservative.** Every active model label lies in the union of the four declared support sets. Satisfying the three coverage obligations for that whole union therefore suffices for the active-label obligations. This follows from set inclusion and the direction of those universal quantifiers. Dropping a label is harder: it needs exact vanishing of all relevant model components on the cell. An interval that contains zero supplies no such equality. [Source: `modelLabels`, lines 5753–5760, and its three consumers at lines 5814–5816, 5890–5891 and 6042–6043; prior trust finding I05; Arb predicate documentation in sources.md.]

**Merge repeated channels before using orthogonality.** `AzimuthalBounded` requires injective triples of component, temporal frequency and azimuthal order. Two identical amplitudes in one channel combine before squaring. For angular order \(n_p\), the bound uses \((|n_p|+1/2)^{-2}\); the circular components \(R_1+iR_2,R_1-iR_2,R_3\) have weights \(1/2,1/2,1\), and time has period one. Keeping duplicate rows in a sum of squares can undercount the norm. [Source: lines 3576–3585; p.66 and (B.50).]

The declaration-specific cautions also cover strict versus non-strict inequalities, zero-slack branches, actual versus weak Hessians, inherited data, all-natural-index conditions, frame invertibility, offset conventions and the full exterior. These cautions identify what a checker must preserve. They are not accusations about an unavailable implementation and are not replacements for the complete predicate.
<!-- /passage:sec-4 -->

<a id="5"></a>

## 5. How the annotations were checked

<!-- passage:sec-5 -->

A namespace-and-section scanner independently recovered the 790 explicit commands and their direct field spans. Each non-theorem command was then compared with its implementation occurrence using the locations established in the earlier trust audit: all 787 command texts agree, including local `open ... in` prefixes. The three theorem signatures also agree with their proof-bearing wrappers in `Solution.lean`. This comparison does not establish imported-environment or elaborated-expression equivalence.

The final validation checks exact name coverage, source positions, field coverage, line-tie containment, title lengths, group membership, pinned links, unique passage quotations, note references and statement comparisons. Paper-reference presence is checked separately from the judgement that a reference is mathematically appropriate. Printed pp.52, 58, 62 and 67 were also inspected visually to resolve prime marks, gradient blocks, complex-to-real tree conventions and potential formulas.
<!-- /passage:sec-5 -->

