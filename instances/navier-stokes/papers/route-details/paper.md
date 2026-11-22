
<!-- passage:front -->
# The proof routes in detail

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · [proof routes](../navier-stokes-routes/paper.md) · **proof routes in detail** · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

*How the assemblies behind Alpöge and Buckmaster's fifteen Comparator theorems reach their analytic statements, with links to their Lean at `ad53419de079eb8f95f60313473374624a348546`. Prepared with AI assistance. The authors have not reviewed it.*

This page continues [the route map](../navier-stokes-routes/paper.md). It follows each public theorem down through the assemblies that prove it to the analytic statements those assemblies take as inputs. A capitalised name ending in `Holds` or `Statement` is a proposition the library defines; the theorem named beside it proves that proposition under the hypotheses its Lean shows. The last part adds passages for items the other pages could not link.
<!-- /passage:front -->

## The assembly steps behind the public theorems

<!-- passage:sec-the-assembly-steps-behind-the-public-theorems -->

### Physical reading of the abstract flow

The abstract argument evolves a vector in a Hilbert space. To read its conclusion as a fluid velocity, follow the physical realization, the Fourier multiplier contracts, and the representative recovered from each vector. The same realization must be used when comparing the constructed trajectory with a smooth competitor.

Compact support and zero divergence are bundled so pressure disappears from the tested equation. The statement is `Breakdown.IsTestField`.

The bridge includes gradient-norm identities, covariance, dense test fields and a weak-to-mild implication. The definition is `Breakdown.Realization`.

The existential output hides the equality between the orbit and the embedded input profile. The statement is `Breakdown.ProfileOrbitHolds`.

The operator is chosen when a bounded realization exists, so its formula is established by a separate contract. The definition is `Breakdown.Freq.fieldOp`.

The definition has a zero fallback; embedding lemmas establish membership for the fields used in the proof. The definition is `Breakdown.Freq.embedX`.

The proof closes the encoding bridge used when reading rescaled convergence physically. The supplying theorem is `Breakdown.Freq.embedDilate`, with the hypotheses displayed in the source.

This export closes the basic Fourier-operator contract used by heat, dilation and physical recovery. The supplying theorem is `Breakdown.Freq.fieldOpRealized_holds`, with the hypotheses displayed in the source.

The theorem also returns a bound on all three derivative norms; the recovery edge uses its first component. The supplying theorem is `Breakdown.Freq.partial_holds`, with the hypotheses displayed in the source.

The proof connects the later regularity construction to the same Fourier realization. The supplying theorem is `Breakdown.Freq.h1Consistency_holds`, with the hypotheses displayed in the source.

Measurability and a uniform multiplier bound discharge the choice hidden in fieldOp. The statement is `Breakdown.Freq.FieldOpRealized`.

The contract includes contraction, strong continuity, self-adjointness and agreement with the ambient Fourier multiplier. The statement is `Breakdown.Freq.HeatSemigroup`.

The norm factor is the fourth root of the scale parameter used in the abstract framework. The statement is `Breakdown.Freq.DilationAlgebra`.

The physical parabolic dilation and the Fourier dilation agree after embedding a decay field. The statement is `Breakdown.Freq.EmbedDilate`.

The dense set is the span of embedded smooth compactly supported divergence-free fields. The statement is `Breakdown.Freq.TestDense`.

The statement puts every decay field in L6 with a uniform bound by its physical gradient L2 norm. The statement is `Breakdown.Freq.GradSixDecay`.

Physical recovery is an almost-everywhere equality, matching the L6 representation. The statement is `Breakdown.Freq.VelocityDecay`.

Each Fourier derivative agrees almost everywhere with its physical component derivative. The statement is `Breakdown.Freq.PartialDecay`.

The first component of bilin_holds supplies a representing bilinear operator for each positive time. The statement is `Breakdown.Freq.BilinExists`.

The time singularity has exponent minus three quarters and is integrable near zero. The statement is `Breakdown.Freq.BilinBound`.

Compactness is required first when one input lies in the dense test span. The statement is `Breakdown.Freq.BilinCompact`.

This contract includes decay and L2 time-difference assumptions specific to the smooth-profile realization. The statement is `Breakdown.Freq.MildOfWeak`.

Almost-everywhere vanishing of the recovered L6 velocity forces the abstract Hilbert vector to vanish. The statement is `Breakdown.Freq.VelocityInjective`.

This interface identifies both recovered velocity and recovered derivatives for smooth finite-energy H1 fields. The statement is `Breakdown.Freq.H1Consistency`.

### A recurrent profile and the transferred trajectory

A recurrent profile supplies the orbit from which the construction starts. The transfer theorem perturbs its initial value into a dense space of admissible data, solves on a geometric sequence of time pieces, and keeps a quantitative convergence estimate before the public breakdown statement hides the trajectory.

The proof combines kernel covariance with exponential change of variables. The supplying theorem is `Breakdown.flowOfMild_unconditional`, with the hypotheses displayed in the source.

The proof carries out componentwise integration by parts before summing the divergence. The supplying theorem is `Breakdown.gradientPairingZero_holds`, with the hypotheses displayed in the source.

Dominated convergence gives the physical estimate consumed by the abstract embedding. The supplying theorem is `Breakdown.sliceGradientContinuous_holds`, with the hypotheses displayed in the source.

This version keeps the literal orbit s mapped to the embedding of W(s), which the existential export hides. The statement is `Breakdown.EmbeddedProfileOrbit`.

The test field has compact support and zero divergence, so no pressure boundary term remains. The statement is `Breakdown.GradientPairingZero`.

The contract converts a physical mild solution back to the similarity-time flow identity. The statement is `Breakdown.FlowOfMild`.

This statement controls differences of profile slices and does not assert that a profile slice itself has finite energy. The statement is `Breakdown.PhysicalL2`.

Solenoidal tests remove the pressure term from the differentiated pairing. The statement is `Breakdown.PhysicalWeak`.

The implication still assumes a smooth similarity profile and continuity of its embedding. The statement is `Breakdown.PhysicalMild`.

Continuity is expressed through the integral of squared gradient differences. The statement is `Breakdown.SliceGradientContinuous`.

The proof uses the pairing derivative and two integration-by-parts contracts. The supplying theorem is `Breakdown.physicalWeak_holds`, with the hypotheses displayed in the source.

Finite-dimensionality is obtained after compactness and the projection identity have both been proved. The supplying theorem is `Breakdown.Spectral.finiteDimensional_range_of_isCompactOperator`, with the hypotheses displayed in the source.

The output carries a stable projection and backward operators before the real exceptional projection is formed. The supplying theorem is `Breakdown.Spectral.exists_dichotomy_complex`, with the hypotheses displayed in the source.

Compact perturbation leaves only finitely many spectral points beyond each larger radius. The supplying theorem is `Breakdown.Spectral.finite_spectrum_outside`, with the hypotheses displayed in the source.

This is the stable-side contour projection; the finite-dimensional exceptional part is its complement. The definition is `Breakdown.Spectral.specProj`.

The proof converts the physical orbit into matching pieces suitable for the discrete construction. The supplying theorem is `Breakdown.profilePiece`, with the hypotheses displayed in the source.

An exceptional initial component is chosen so the forced discrete orbit remains bounded. The statement is `Breakdown.DiscreteDichotomyStatement`.

The abstract inverse dilation uses the same logarithmic clock as the physical profile formula. The definition is `Breakdown.MildFramework.selfSimilar`.

A global upper bound follows from continuity and twisted periodicity of the abstract orbit. The statement is `Breakdown.OrbitBoundStatement`.

This positive lower bound uses mild uniqueness as well as recurrence. The statement is `Breakdown.OrbitNormStatement`.

Each rescaled piece retains its mild equation, twisted recurrence and uniform bound. The statement is `Breakdown.ProfilePieceStatement`.

The resulting half-open mild flow keeps a formula relating physical time to the geometric piece number. The statement is `Breakdown.GlueStatement`.

The contract asserts integrability, continuity and a norm bound for the heat-bilinear integral. The statement is `Breakdown.VarConstIntegralStatement`.

The contract identifies the bilinear Duhamel operator and free heat evolution on a closed time piece. The statement is `Breakdown.PieceOperatorStatement`.

Uniqueness is asserted in the abstract continuous mild class on the same closed time interval. The statement is `Breakdown.UniqueStatement`.

The short-time construction returns a quantitative bound on the mild solution. The statement is `Breakdown.SmallDataStatement`.

The contract treats a continuous scalar time factor multiplied by one fixed interaction vector. The statement is `Breakdown.CompactSimpleStatement`.

The endpoint value of the bilinear piece operator is compact when one input piece is fixed. The statement is `Breakdown.CompactPieceStatement`.

The perturbation equation makes the corrected background mild with the prescribed initial change. The statement is `Breakdown.PiecePerturbationStatement`.

### Why a global smooth competitor is excluded

The final whole-space contradiction has two distinct inputs: the constructed mild trajectory has recurrent concentration, and any proposed global smooth competitor must agree with it locally. These are separate statements in the source, so the reading links keep both available.

The compact-interval contract is separate from the global smooth-solution predicate. The statement is `Breakdown.IsSolutionOn`.

This quantifier pattern is imposed on the global competitor in the whole-space endpoint. The statement is `Breakdown.HasBoundedEnergy`.

The comparison uses compact-interval physical regularity and the global competitor energy bound. The supplying theorem is `Breakdown.agree_of_mildRegular`, with the hypotheses displayed in the source.

The proof combines a quantitative transferred orbit with local agreement of any smooth finite-energy competitor. The supplying theorem is `Breakdown.noBoundedSmoothSolution_of_exports`, with the hypotheses displayed in the source.

The contradiction uses a positive local L6 profile norm along repeated phases, together with physical continuity at time one. The supplying theorem is `Breakdown.false_of_orbit_rate`, with the hypotheses displayed in the source.

The abstract transfer, profile orbit and physical regularity inputs remain visible at this assembly boundary. The supplying theorem is `Breakdown.breakdownOnSpace_of_exports`, with the hypotheses displayed in the source.

The physical smooth-solution proof is built from this pointwise Fourier integral equation. The statement is `Breakdown.SmoothFlow.IsVarConstSymbol`.

The regularity argument controls weighted Fourier norms and their time continuity. The statement is `Breakdown.SmoothFlow.IsHsCurve`.

The Fourier regularity route returns both velocity and pressure while retaining almost-everywhere equality to the mild flow. The supplying theorem is `Breakdown.SmoothFlow.mildRegular_of_freq`, with the hypotheses displayed in the source.

This step reconstructs pressure as well as velocity from an all-orders Sobolev symbol flow. The supplying theorem is `Breakdown.SmoothFlow.isSolutionOn_physField`, with the hypotheses displayed in the source.

Amplitude and time rescaling turn the unit-viscosity contradiction into the universal viscosity endpoint. The supplying theorem is `Breakdown.breakdownOnSpace_of_unit_viscosity`, with the hypotheses displayed in the source.

### Turning a weak profile into a recurrent orbit

The weak route starts with space-time identities and almost-everywhere representatives. It first synchronizes good times, then reconstructs a continuous Hilbert-space curve. The continuity step is what allows later recurrence and mild-evolution statements to hold at the times required by the transfer argument.

The slice interface retains an L6 velocity, an L2 weak gradient and zero divergence. The statement is `Breakdown.WeakProfile.IsSlice`.

The proof uses the primitive of a weak time derivative to construct the common good-time set. The supplying theorem is `Breakdown.WeakProfile.goodTimes_holds`, with the hypotheses displayed in the source.

The proof extends the good-time equality to a continuous mild representative. The supplying theorem is `Breakdown.WeakProfile.mildFromGood_holds`, with the hypotheses displayed in the source.

The weak route rejoins whole-space transfer after it has obtained a continuous recurrent orbit. The supplying theorem is `Breakdown.WeakProfile.breakdownOnSpace_of_orbit`, with the hypotheses displayed in the source.

This assembly still takes pairing and weak-gradient identities before discharging the physical-time conversion. The supplying theorem is `Breakdown.WeakProfile.physicalIdentity_of_parts`, with the hypotheses displayed in the source.

The proof ensures the recurrent orbit can be stated pointwise in time. The supplying theorem is `Breakdown.WeakProfile.globalRepresentative_holds`, with the hypotheses displayed in the source.

The proof uses scaled solenoidal tests and the slice integrand identity. The supplying theorem is `Breakdown.WeakProfile.similarityIdentity_holds`, with the hypotheses displayed in the source.

The proof uses uniqueness of an L6 field with the given weak gradient to identify the Fourier representative. The supplying theorem is `Breakdown.WeakProfile.sliceEmbedding_holds`, with the hypotheses displayed in the source.

Locally continuous representatives agreeing almost everywhere are glued into one curve on all similarity times. The statement is `Breakdown.WeakProfile.GlobalRepresentative`.

The L6 requirement rules out a nonzero constant field on the whole space. The statement is `Breakdown.WeakProfile.ZeroGradientSix`.

Velocity and weak-gradient recovery are retained almost everywhere with a quantitative X norm bound. The statement is `Breakdown.WeakProfile.SliceEmbedding`.

The space-time test equation is converted into scalar pairings of the Hilbert curve. The statement is `Breakdown.WeakProfile.SimilarityIdentity`.

Changing variables introduces the tensor weak formulation on a physical-time interval. The statement is `Breakdown.WeakProfile.PhysicalIdentity`.

The weak scalar identities are synchronised so the Hilbert evolution can be compared at the same times. The statement is `Breakdown.WeakProfile.GoodTimes`.

The Duhamel representative is identified with the original curve almost everywhere before continuity closes the interval. The statement is `Breakdown.WeakProfile.MildFromGood`.

The proof removes the constant ambiguity when identifying a weak slice with its Fourier recovery. The supplying theorem is `Breakdown.WeakProfile.zeroGradientSix_holds`, with the hypotheses displayed in the source.

### Localizing and correcting on the torus

The periodic construction localizes the physical profile, compares the whole-space and periodic sequence operators, and corrects the resulting residual. It needs lower bounds on the localized profile as well as small upper bounds on the correction, because those inequalities perform different jobs at the final gluing step.

The proof uses density and compactness of one time interval to choose a finite approximation. The supplying theorem is `Breakdown.Periodic.approximantExists`, with the hypotheses displayed in the source.

The proof recasts StepDataStatement as the sequence-operator input for the torus comparison. The supplying theorem is `Breakdown.Periodic.baseInverse`, with the hypotheses displayed in the source.

The proof assembles entry formulas, operator bounds and the window and tail contracts. The supplying theorem is `Breakdown.Periodic.lambdaComparison`, with the hypotheses displayed in the source.

The proof combines free-heat comparison with dilation and norm bounds for the chosen test-field lifts. The supplying theorem is `Breakdown.Periodic.seedComparison`, with the hypotheses displayed in the source.

The shell-restricted inverse series is controlled by separating a finite window from its tail. The statement is `Breakdown.Periodic.LambdaComparison`.

The finite-dimensional correction is transported through the two inverse series. The statement is `Breakdown.Periodic.SeedComparison`.

The periodic heat interaction has the short-time bound needed to reuse the local abstract machinery. The statement is `Breakdown.Periodic.KernelSharpBound`.

A curl cutoff of a homotopy potential preserves the divergence constraint while localising the physical profile. The definition is `Breakdown.Periodic.approxField`.

The approximation is solenoidal, agrees with the central profile and vanishes away from the chosen ball. The statement is `Breakdown.Periodic.ApproxFieldProperties`.

The residual is controlled in the rescaled piece equation used for the nonlinear correction. The statement is `Breakdown.Periodic.ApproxResidualSmall`.

The comparison is in the periodic Hilbert norm after transplanting a whole-space test approximation. The statement is `Breakdown.Periodic.ApproxClose`.

The lower bound keeps the nonzero profile visible after localisation and periodic transplantation. The statement is `Breakdown.Periodic.ApproxSizes`.

Each recurring profile piece is approximated by finitely many compactly supported solenoidal fields. The statement is `Breakdown.Periodic.ApproximantExists`.

The starting inverse comes from the same finite-dimensional correction used for whole-space transfer. The statement is `Breakdown.Periodic.BaseInverse`.

The contract controls both the interaction and initial-data comparison as the torus scale shrinks. The statement is `Breakdown.Periodic.ComparisonSmall`.

A norm-small operator change preserves a bounded right inverse with a quantitative bound. The statement is `Breakdown.Periodic.RightInversePerturb`.

This abstract contract separates the common shell contribution from the two ambient sequence spaces. The statement is `Breakdown.Periodic.ShellInverseTransfer`.

The squared rescaled periodic norm equals the whole-space gradient energy plus the scale parameter times its L2 energy. The statement is `Breakdown.Periodic.TransplantNorm`.

The contract compares the restricted periodic response with the whole-space response after rescaling. The statement is `Breakdown.Periodic.HeatDivFreeComparison`.

The initial-data response is compared separately from the nonlinear source response. The statement is `Breakdown.Periodic.FreeHeatComparison`.

The interface links physical Fourier coefficients to the periodic Hilbert mild equation. The statement is `Breakdown.Periodic.SmoothPeriodicIsMild`.

The time scales shrink geometrically and the endpoint links yield one half-open mild trajectory. The statement is `Breakdown.Periodic.GlueMild`.

The contraction returns corrections whose geometric decay can be carried through the final gluing. The statement is `Breakdown.Periodic.SeqPerturbation`.

A positive lower bound on the approximate profile outlasts the geometrically decaying correction. The statement is `Breakdown.Periodic.GlueUnbounded`.

### From the certificate to a weak profile

The certificate argument solves a nonlinear held problem at each admissible parameter and then chooses a parameter with zero total multiplier. A proposition ending in Holds records an interface in this construction. Its supplying theorem has its own hypotheses, which remain visible in the linked source.

The explicit node arguments show which analytic facts must be supplied before the certificate implication closes. The supplying theorem is `Breakdown.Cert.certificate_orbit_of_nodes`, with the hypotheses displayed in the source.

The custom distance needs closedness and lower semicontinuity clauses beyond the usual norm contraction interface. The statement is `Breakdown.Cert.ContractionFixedPointHolds`. The supplying theorem is `Breakdown.Cert.contractionFixedPointHolds_proof`, with the hypotheses displayed in the source.

Quadratic error, adjoint defect and actuator-frame discrepancy bound the adjoint multiplier coordinates. The statement is `Breakdown.Cert.ExtendedAdjointEnclosureHolds`. The supplying theorem is `Breakdown.Cert.extendedAdjointEnclosureHolds_of`, with the hypotheses displayed in the source.

The normalised route solves at each parameter, finds a zero multiplier and then exports weak-profile existence. The supplying theorem is `Breakdown.Cert.extended_normal_orbit_of_nodes`, with the hypotheses displayed in the source.

The model becomes the approximate profile; transfer and form-shift losses are absorbed into the bounds. The statement is `Breakdown.Cert.ExtendedAtProfileHolds`. The supplying theorem is `Breakdown.Cert.extendedAtProfileHolds`, with the hypotheses displayed in the source.

Coercivity supplies injectivity and the compact perturbation argument supplies surjectivity. The statement is `Breakdown.Cert.ExtendedBorderedInvertibleHolds`. The supplying theorem is `Breakdown.Cert.extendedBorderedInvertibleHolds_of`, with the hypotheses displayed in the source.

The certificate coercivity clause is transferred to readings of the bordered inverse problem. The statement is `Breakdown.Cert.ExtendedCoerciveBorderedHolds`. The supplying theorem is `Breakdown.Cert.extendedCoerciveBorderedHolds_of`, with the hypotheses displayed in the source.

The abstract convection operator is identified through its physical test pairings. The statement is `Breakdown.Cert.ExtendedConvectionHolds`. The supplying theorem is `Breakdown.Cert.extendedConvectionHolds_of`, with the hypotheses displayed in the source.

Local compactness and decay tails turn convection composed with the free inverse into a compact operator. The statement is `Breakdown.Cert.ExtendedConvectionCompactHolds`. The supplying theorem is `Breakdown.Cert.extendedConvectionCompactHolds_of`, with the hypotheses displayed in the source.

The needed continuity is tested after projection and does not require separate continuity assumptions on raw pressure gradients. The statement is `Breakdown.Cert.ExtendedDataContinuityHolds`. The supplying theorem is `Breakdown.Cert.extendedDataContinuityHolds_of`, with the hypotheses displayed in the source.

The finite-dimensional zero argument selects a parameter only after the fixed-parameter nonlinear solves. The statement is `Breakdown.Cert.ExtendedExistsZeroHeldHolds`. The supplying theorem is `Breakdown.Cert.extendedExistsZeroHeldHolds_of`, with the hypotheses displayed in the source.

This Lean proof uses the second smallness inequality (7.26), which the paper's proof leaves unused. The statement is `Breakdown.Cert.ExtendedHeldContractsHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldContractsHolds_of`, with the hypotheses displayed in the source.

Uniqueness concerns corrections within the held set at each fixed parameter, with that restricted class kept explicit. The statement is `Breakdown.Cert.ExtendedHeldExistsUniqueHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldExistsUniqueHolds_of`, with the hypotheses displayed in the source.

The limit theorem follows actual nonlinear held solutions and retains a convergent subsequence of their multipliers. The statement is `Breakdown.Cert.ExtendedHeldLimitHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldLimitHolds_of`, with the hypotheses displayed in the source.

The two held bounds are preserved at each fixed parameter, before a parameter is selected. The statement is `Breakdown.Cert.ExtendedHeldMapsToHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldMapsToHolds_of`, with the hypotheses displayed in the source.

The strict lower bound on the approximate gradient rules out cancellation by the bounded correction. The statement is `Breakdown.Cert.ExtendedHeldNonzeroHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldNonzeroHolds_of`, with the hypotheses displayed in the source.

The total multiplier equality removes the entire actuator sum from the weak similarity equation. The statement is `Breakdown.Cert.ExtendedHeldWeakEquationHolds`. The supplying theorem is `Breakdown.Cert.extendedHeldWeakEquationHolds_of`, with the hypotheses displayed in the source.

Uniqueness identifies subsequential multiplier limits, making the selected total multiplier continuous on the parameter set. The statement is `Breakdown.Cert.ExtendedMultiplierContinuityHolds`. The supplying theorem is `Breakdown.Cert.extendedMultiplierContinuityHolds_of`, with the hypotheses displayed in the source.

Choice selects a held multiplier when one exists and defaults to zero elsewhere; continuity is proved on the valid parameter set. The definition is `Breakdown.ExtendedCertificateData.multiplierOf`.

Inverse rescaling of actuator and multiplier leaves the force unchanged while making the multiplier weight one. The statement is `Breakdown.Cert.ExtendedUnitWeightHolds`. The supplying theorem is `Breakdown.Cert.extendedUnitWeightHolds`, with the hypotheses displayed in the source.

The complement of the adjoint index set is controlled by the multiplier-size and frame bounds. The statement is `Breakdown.Cert.ExtendedStiffEnclosureHolds`. The supplying theorem is `Breakdown.Cert.extendedStiffEnclosureHolds`, with the hypotheses displayed in the source.

The inverse lands in the graph space and carries a second-derivative plus gradient estimate. The statement is `Breakdown.Cert.FreeInvHolds`. The supplying theorem is `Breakdown.Cert.freeInvHolds_of`, with the hypotheses displayed in the source.

This converts the inverse reading into IsPerturbation with the intended projected right side. The statement is `Breakdown.Cert.FreePerturbationHolds`. The supplying theorem is `Breakdown.Cert.freePerturbationHolds_of`, with the hypotheses displayed in the source.

Space and time translation bounds give a subsequence Cauchy on every bounded spatial region. The statement is `Breakdown.Cert.LocalCompactnessHolds`. The supplying theorem is `Breakdown.Cert.localCompactnessHolds_of`, with the hypotheses displayed in the source.

Main supplies the analytic node proofs to Assembly, while the certificate remains an input hypothesis. The supplying theorem is `Breakdown.certificate_orbit_proved`, with the hypotheses displayed in the source.

This interface identifies projected Hilbert pairings with physical integrals against solenoidal test fields. The statement is `Breakdown.Cert.TestPairingHolds`. The supplying theorem is `Breakdown.Cert.testPairingHolds_proof`, with the hypotheses displayed in the source.

The closed Fourier graph is read as measurable velocity, gradient and second-derivative fields. The statement is `Breakdown.Cert.ReadingExistsHolds`. The supplying theorem is `Breakdown.Cert.readingExistsHolds_proof`, with the hypotheses displayed in the source.

Exceptional-time values are repaired so each slice has weak gradient and uniform spatial bounds. The statement is `Breakdown.Cert.SliceReadingHolds`. The supplying theorem is `Breakdown.Cert.sliceReadingHolds_of`, with the hypotheses displayed in the source.

Weighted graph energy and the other factor's gradient supremum control the nonlinear forcing. The statement is `Breakdown.Cert.ProductBoundHolds`. The supplying theorem is `Breakdown.Cert.productBoundHolds_of`, with the hypotheses displayed in the source.

Vanishing against all space-time tests forces the projected Hilbert element to be zero. The statement is `Breakdown.Cert.TestDenseHolds`. The supplying theorem is `Breakdown.Cert.testDenseHolds_proof`, with the hypotheses displayed in the source.

The selected period is used inside the proof, then hidden by WeakPeriodicSimilarityProfileExists. The supplying theorem is `Breakdown.weakPeriodicSimilarityProfileExists_of_sigma`, with the hypotheses displayed in the source.

The abstract enclosure lemma combines the adjoint error terms before the certificate-specific application. The statement is `Breakdown.Held.AdjointEnclosureStatement`. The supplying theorem is `Breakdown.Held.adjointEnclosure`, with the hypotheses displayed in the source.

Compactness and convexity of the encoded test set support the finite-dimensional parameter selection. The statement is `Breakdown.Held.TestSetZeroStatement`. The supplying theorem is `Breakdown.Held.testSetZero`, with the hypotheses displayed in the source.

### The multiplier and coercivity estimates

The mode and piecewise multiplier routes share the weak perturbation class but use different decompositions of the density. The public Solution declarations forward to library proofs. The numerical rest inequalities and scalar conditions remain premises of the reductions to coercivity.

The Solution wrapper delegates the density estimate to this library theorem. The supplying theorem is `Breakdown.ModeWeights.multiplier_density_proved`, with the hypotheses displayed in the source.

The library provider discharges the two angular-frequency lower bounds in the public statement. The supplying theorem is `Breakdown.ModeWeights.mode_azimuthal_gain_proved`, with the hypotheses displayed in the source.

This provider closes the Fourier-mode estimate used by the public stretch wrapper. The supplying theorem is `Breakdown.ModeWeights.stretch_mean_bound_proved`, with the hypotheses displayed in the source.

This is the library proof behind the public reduction from density bounds to MultiplierInequality. The supplying theorem is `Breakdown.ModeWeights.multiplierInequality_of_density_proved`, with the hypotheses displayed in the source.

The provider uses the piecewise density construction before the Solution alias exposes it. The supplying theorem is `Breakdown.PieceWeights.piece_multiplier_density_proved`, with the hypotheses displayed in the source.

This reduction retains the cell-independent rest inequality and scalar bounds as inputs. The supplying theorem is `Breakdown.PieceWeights.multiplierInequality_of_pieceDensity_proved`, with the hypotheses displayed in the source.

The closed weak-density theorem feeds the extended coercivity estimate, while the numerical inequalities remain premises. The supplying theorem is `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceData_proved`, with the hypotheses displayed in the source.

### Cells, rows and the analytic residual

Finite rows become bounds for physical fields only after the harmonic, trace and gauge correspondences have been supplied. The cell-layer proof bundle establishes these general implications. Applying them to a particular cell system still requires that system to satisfy the stated conditions.

The physical cell state is restricted to the row range where the finite residual bound is valid. The statement is `Breakdown.CertCell.Assembly.CellStateInRowRangeHolds`. The supplying theorem is `Breakdown.CertCell.Assembly.cellStateInRowRange_holds`, with the hypotheses displayed in the source.

The matrix inequalities and band estimates supply the elimination-stage quadratic bound. The statement is `Breakdown.CertCell.Assembly.EliminationStageHolds`. The supplying theorem is `Breakdown.CertCell.Assembly.eliminationStage_holds`, with the hypotheses displayed in the source.

The supplied potential conditions are interpreted on physical cell states in the assembly. The statement is `Breakdown.CertCell.Assembly.PotentialStageHolds`. The supplying theorem is `Breakdown.CertCell.potentialStage_closed`, with the hypotheses displayed in the source.

The supplied pairing conditions become the physical pairing stage after the cell-state correspondence. The statement is `Breakdown.CertCell.Assembly.PairingStageHolds`. The supplying theorem is `Breakdown.CertCell.pairingStage_closed`, with the hypotheses displayed in the source.

Harmonic lifts, plane flips and trace independence connect finite row coefficients to field traces. The statement is `Breakdown.CertCell.Assembly.RowsMatchFieldsHolds`. The supplying theorem is `Breakdown.CertCell.Assembly.rowsMatchFieldsHolds_of_lift`, with the hypotheses displayed in the source.

Matched rows and gauge conditions place the physical data in the certificate tree state. The statement is `Breakdown.CertCell.Assembly.TreeStateHolds`. The supplying theorem is `Breakdown.CertCell.Assembly.treeState_holds`, with the hypotheses displayed in the source.

The finite relation rows vanish on harmonic data obtained from a valid periodic physical field. The statement is `Breakdown.CertCell.CellCalculus.HarmonicRelationsStatement`. The supplying theorem is `Breakdown.CertCell.CellCalculus.harmonicRelations_holds`, with the hypotheses displayed in the source.

The energy-leaf estimate and residual bound together bound the full cell quadratic form. The statement is `Breakdown.CertCell.CellCalculus.CellFormAssemblyStatement`. The supplying theorem is `Breakdown.CertCell.cellFormAssembly_closed`, with the hypotheses displayed in the source.

Gauge conditions on the finite tree give the corresponding physical field gauge. The statement is `Breakdown.CertCell.FieldGaugeParts`. The supplying theorem is `Breakdown.CertCell.fieldGauge_closed`, with the hypotheses displayed in the source.

This proof bundle closes the analytic cell machinery; it supplies no concrete satisfying numerical cell data. The statement is `Breakdown.CertCell.CellLayerParts`. The supplying theorem is `Breakdown.CertCell.cellLayerParts_closed`, with the hypotheses displayed in the source.

The theorem consumes the signed state-enclosure condition; it is the analytic implication a numerical certificate must feed. The statement is `Breakdown.CertCell.Certificate.StateEnclosureCertificateNonneg`. The supplying theorem is `Breakdown.CertCell.stateEnclosureCertificateNonneg_holds`, with the hypotheses displayed in the source.

Potential, pairing, row, tail and elimination stages combine into the cell residual estimate. The statement is `Breakdown.CertCell.CellResidualFromConditions`. The supplying theorem is `Breakdown.CertCell.cellResidualFromConditions_of`, with the hypotheses displayed in the source.

### From cell conditions to the two breakdown conclusions

The last assembly connects the cell analysis to the extended certificate. It supplies the profile structure, offset, transfer and adjoint bridges, then uses the weak-profile and breakdown routes. The decay parameter chosen in this assembly is part of the formal conclusion and must be retained by any wrapper.

Representation, potential and pin estimates connect the finite adjoint data to the weak right-side inequality. The statement is `Breakdown.AdjointDefect.AdjointDefectBridgeHolds`. The supplying theorem is `Breakdown.AdjointDefect.adjointDefectBridge_of_pieces`, with the hypotheses displayed in the source.

A slice estimate and period integration turn the supplied adjoint numbers into the quadratic pairing clause. The statement is `Breakdown.CertReduction.AdjointQuadraticBridgeHolds`. The supplying theorem is `Breakdown.CertReduction.adjointQuadraticBridge_of`, with the hypotheses displayed in the source.

Shape values and scaled-jet facts connect the finite cell records to the physical fields. The supplying theorem is `Breakdown.CellLayerSystem.layerJunctionFacts_of_parts`, with the hypotheses displayed in the source.

The model equality and enclosure clauses supply weak piece admissibility for each parameter. The supplying theorem is `Breakdown.CellLayerSystem.admissible_of_parts`, with the hypotheses displayed in the source.

The closed cell-layer theorem supplies the row-rest bound used in extended coercivity. The supplying theorem is `Breakdown.CellLayerSystem.coerciveClause_of_parts`, with the hypotheses displayed in the source.

Analytic bridge hypotheses are explicit here and are supplied in CellLayerBreakdownClosed. The supplying theorem is `Breakdown.CellLayerSystem.breakdownOnSpace_of_cell_system_condition_of_parts`, with the hypotheses displayed in the source.

Analytic shape lemmas yield the structural certificate clauses with a sufficiently large decay constant. The statement is `Breakdown.CellReduction.Instantiation.InstantiationHolds`. The supplying theorem is `Breakdown.CellReduction.Instantiation.instantiation_holds_of_open`, with the hypotheses displayed in the source.

The affine residual expansion and period pairings give the adjusted-multiplier error bound. The statement is `Breakdown.CellReduction.Instantiation.OffsetClauseHolds`. The supplying theorem is `Breakdown.CellReduction.Instantiation.offsetClause_holds_of`, with the hypotheses displayed in the source.

Bounds on the supplied shift pieces produce the certificate gap-transfer clause. The statement is `Breakdown.CertReduction.GapTransferBridgeHolds`. The supplying theorem is `Breakdown.CertReduction.gapTransferBridgeHolds_proof`, with the hypotheses displayed in the source.

The shift-piece bounds control the change of the frozen form between model and approximate profile. The statement is `Breakdown.CertReduction.FormShiftBridgeHolds`. The supplying theorem is `Breakdown.CertReduction.formShiftBridgeHolds_proof`, with the hypotheses displayed in the source.

The bridge converts bounded model-form data using the analytic convection identity. The statement is `Breakdown.CertReduction.FrozenFormBridgeHolds`. The supplying theorem is `Breakdown.CertReduction.frozenFormBridgeHolds_of_convection`, with the hypotheses displayed in the source.

The extended certificate first gives a weak profile, which is smoothed before the torus argument. The supplying theorem is `Breakdown.CellLayerSystem.torusBreakdown_of_cell_system_condition`, with the hypotheses displayed in the source.

### Smoothing the weak profile for the periodic route

The certificate-to-torus path first turns the weak recurrent object into a smooth decaying profile. Local smoothing, a uniform spatial tail, and the infinite-past integral formula are different stages of that reconstruction. Keeping their interfaces separate explains why a weak-profile export can feed the smooth-profile torus theorem.

The proof first gains weight three quarters, then weight one, then derivative and pressure bounds. The supplying theorem is `Breakdown.FarField.farFieldDecay_of_parts`, with the hypotheses displayed in the source.

The infinite-past representation is established for the supplied smooth representative. The statement is `Breakdown.FarField.IntegralEquationOfOrbit`. The supplying theorem is `Breakdown.FarField.integralEquationOfOrbit_holds`, with the hypotheses displayed in the source.

The formal route derives velocity derivatives through order two and cubic pressure-gradient decay. The statement is `Breakdown.FarField.FarFieldDecay`. The supplying theorem is `Breakdown.FarField.farFieldDecay_holds`, with the hypotheses displayed in the source.

Closed derivative graphs and the Picard bounds supply the local smoothing step. The statement is `Breakdown.FarField.LocalGainOfPicard`. The supplying theorem is `Breakdown.FarField.localGainOfPicard_holds`, with the hypotheses displayed in the source.

The interface iterates the derivative gain to arbitrary Sobolev regularity. The statement is `Breakdown.FarField.MildSmoothingOfLocalGain`. The supplying theorem is `Breakdown.FarField.mildSmoothingOfLocalGain_holds`, with the hypotheses displayed in the source.

The formal proof reconstructs smoothness from local windows and Fourier evolution. The statement is `Breakdown.FarField.OrbitSmoothOfWindows`. The supplying theorem is `Breakdown.FarField.orbitSmoothOfWindows_holds`, with the hypotheses displayed in the source.

One-period compactness upgrades pointwise Fourier decay to a tail bound uniform over the orbit. The statement is `Breakdown.FarField.OrbitTailOfSymbolCurve`. The supplying theorem is `Breakdown.FarField.orbitTailOfSymbolCurve_holds`, with the hypotheses displayed in the source.

RegularStatements names the analytic inputs and SmoothFieldClosed supplies their proofs. The supplying theorem is `Breakdown.FarField.smoothFieldOfOrbit_of_symbolCalculus`, with the hypotheses displayed in the source.
<!-- /passage:sec-the-assembly-steps-behind-the-public-theorems -->

## Following the closed assembly into its analytic statements

<!-- passage:sec-following-the-closed-assembly-into-its-analytic-statements -->

### The transfer and adjoint bridges

The cell-to-certificate passage needs analytic statements about fields and pairings. These paragraphs keep the small component estimates separate from the final transfer clauses, so a reader can see where a regularity assumption or a numerical coefficient enters.

The sum of the azimuthal gradient-mode energies is bounded by the integral of the squared matrix norm of the original measurable gradient field. The provider is `Breakdown.AdjointDefect.AzimuthalParts.gradientModeTotal`. The named statement is `Breakdown.AdjointDefect.AzimuthalParts.GradientModeTotalHolds`.

The standing bridge record retains a positive constant weight, a weak second-derivative state for the model, first-order regularity and decay of the profile, and measurability of the selected adjoint fields. The provider is `Breakdown.CellLayerSystem.bridgeStanding_of_parts`. The named statement is `Breakdown.CertReduction.BridgeStanding`.

The two assemblies establish the same integration-by-parts identity: pairing the transported weak gradient with the negative second-derivative trace equals a quadratic expression involving the derivative of the divergence-free background field. The providers are `Breakdown.CertReduction.convectionIdentityHolds_of`, `Breakdown.CertReduction.convectionIdentityHolds_of_approx`. The named statement is `Breakdown.CertReduction.ConvectionIdentityHolds`.

The energy bundle combines the slice supremum estimate, the profile-energy supremum estimate, and the period integral of the gradient energy. The provider is `Breakdown.CertReduction.energyBounds_of`. The named statement is `Breakdown.CertReduction.EnergyBoundsHolds`.

Spatial decay of the background and its derivative makes both frozen convection pairings integrable: the gradient applied to the background, and the background derivative applied to the weak profile, are each paired with the negative second-derivative trace. The providers are `Breakdown.CertReduction.frozenIntegrand`, `Breakdown.CertReduction.frozenIntegrandHolds_proof`. The named statement is `Breakdown.CertReduction.FrozenIntegrandHolds`.

A valid adjoint-shape entry supplies the adjoint-field facts required by the extended certificate. The provider is `Breakdown.CellReduction.Instantiation.adjointField_holds_of`. The named statement is `Breakdown.CellReduction.Instantiation.AdjointFieldHolds`.

Nonzero scales, bounded instantiation, the affine frequency formula, and the links between adjoint entries provide the adjoint-defect structure for every selected adjoint index. The provider is `Breakdown.CellReduction.Instantiation.adjointStructure_holds_of`. The named statement is `Breakdown.CellReduction.Instantiation.AdjointStructureHolds`.

When each active shape amplitude has high order at least three, the shape field is the curl of a time-periodic continuously differentiable potential; the potential and its time derivative decay quadratically, and its spatial derivative decays cubically. The provider is `Breakdown.CellReduction.Instantiation.fieldPotential_holds`. The named statement is `Breakdown.CellReduction.Instantiation.FieldPotentialHolds`.

The matrix bundle packages the operator-square estimate together with the reduction of strain to the symmetric part; its closed alias returns that same pair of facts. The providers are `Breakdown.CertReduction.matrixFacts`, `Breakdown.CertReduction.matrixFactsHolds_proof`. The named statement is `Breakdown.CertReduction.MatrixFactsHolds`.

The period-gluing bundle combines the period sum bound, the period pairing bound, the stationary pairing bound, and the slice-integration statement. The providers are `Breakdown.CertReduction.periodGlue`, `Breakdown.CertReduction.periodGlueHolds_proof`. The named statement is `Breakdown.CertReduction.PeriodGlueHolds`.

For a weakly twice differentiable $L^6$ field, the squared pointwise magnitude is bounded almost everywhere by $(2\pi)^{-1}$ times the product of the square roots of the gradient energy and the squared second-derivative-trace integral. The provider is `Breakdown.CertReduction.sliceSupNormHolds_proof`. The named statement is `Breakdown.CertReduction.SliceSupNormHolds`.

A perturbation has, for almost every time, the first and second weak-gradient identities together with finite sixth-power velocity, gradient-square, and second-derivative-trace integrals. The provider is `Breakdown.CertReduction.perturbationSliceHolds_proof`. The named statement is `Breakdown.CertReduction.PerturbationSliceHolds`.

The weighted square integral of $Aw$ is at most $4/3$ times the two-thirds power of the cubic integral of $|A|$ times the gradient energy of $w$, under the displayed weak-gradient and integrability hypotheses. The provider is `Breakdown.CertReduction.cubicWeightProductHolds_proof`. The named statement is `Breakdown.CertReduction.CubicWeightProductHolds`.

A uniform bound $s$ on the shift controls the squared period norm of the gradient applied to that shift by $(s/\sqrt{w_0})^2$ times the weighted perturbation energy. The provider is `Breakdown.CertReduction.gapSupTermHolds_proof`. The named statement is `Breakdown.CertReduction.GapSupTermHolds`.

The selected cubic or uniform piece-gradient bound controls the squared period norm of the shift derivative applied to the velocity, with the corresponding gap-gradient coefficient retained. The provider is `Breakdown.CertReduction.gapGradTermHolds_proof`. The named statement is `Breakdown.CertReduction.GapGradTermHolds`.

A uniform shift bound controls its stationary pairing with the second-derivative trace by $s/(2\sqrt{w_0})$ times the stationary energy. The provider is `Breakdown.CertReduction.shiftSupTermHolds_proof`. The named statement is `Breakdown.CertReduction.ShiftSupTermHolds`.

A piece-gradient bound on the shift derivative controls the stationary pairing with the second-derivative trace, using the coefficient selected by the cubic flag. The provider is `Breakdown.CertReduction.shiftGradTermHolds_proof`. The named statement is `Breakdown.CertReduction.ShiftGradTermHolds`.

A lower quadratic-form bound $-S$ on the background derivative yields the lower bound $-(S/w_0)$ times the stationary energy for the convection pairing. The provider is `Breakdown.CertReduction.strainTermHolds_of_convection`. The named statement is `Breakdown.CertReduction.StrainTermHolds`.

### Mode decomposition and coercivity

The closed density proofs supply their analytic nodes in the library. Their conclusions retain the original admissibility, integrability and numerical premises. The selected aliases in Solution expose the resulting inequalities.

The mode-density contract produces a multiplier field with finite frequency seminorm, bounds its period norm by the weighted energy and mode energy, and compares the positive and negative density integrals with the signed multiplier gap. One assembly accepts the analytic nodes; the closed proof supplies them. The providers are `Breakdown.Coercive.multiplierDensityHolds_of_nodes`, `Breakdown.Coercive.multiplierDensityHolds_proof`. The named statement is `Breakdown.Coercive.MultiplierDensityHolds`.

The piecewise-density contract returns the analogous multiplier and integral inequality for piece weights and harmonic bounds, with its own seminorm and coefficient. Its conditional assembly and closed proof remain separately selectable. The providers are `Breakdown.Coercive.pieceMultiplierDensityHolds_of_nodes`, `Breakdown.Coercive.pieceMultiplierDensityHolds_proof`. The named statement is `Breakdown.Coercive.PieceMultiplierDensityHolds`.

The weak-background density assembly uses an explicit weak second-derivative state and Hessian field in its admissibility and density terms, and keeps the same finite-energy multiplier conclusion. The provider is `Breakdown.CoerciveWeak.pieceMultiplierDensityWeakHolds_of_nodes`. The named statement is `Breakdown.CoerciveWeak.PieceMultiplierDensityWeakHolds`.

The mode-square-sum statement identifies the period energies of velocity, gradient, and second derivative with their sums over time and azimuthal modes, and also gives the corresponding summed pairing identity. The providers are `Breakdown.Coercive.modeSquareSumHolds_proved`, `Breakdown.CoerciveWeak.modeSquareSumHolds_closed`. The named statement is `Breakdown.Coercive.ModeSquareSumHolds`.

For an azimuthal index of magnitude at least two, the mode estimates compare velocity to gradient and gradient to second derivative with the factors $(|k|-1)^2/r^2$ and $(|k|-2)^2/r^2$, respectively, almost everywhere. The provider is `Breakdown.Coercive.modeAzimuthalGainHolds_proof`. The named statement is `Breakdown.Coercive.ModeAzimuthalGainHolds`.

The negative angular and time integral of stretching is bounded by the sum of the mode stretch charges, with the angular factor of two pi carried explicitly. The provider is `Breakdown.Coercive.stretchMeanBoundHolds_proof`. The named statement is `Breakdown.Coercive.StretchMeanBoundHolds`.

The mode-derivative statement supplies the weak-gradient identities for the real and imaginary parts of velocity and gradient modes, and the zero trace of the mode gradient. The provider is `Breakdown.CoerciveWeak.modeDerivativeHolds_closed`. The named statement is `Breakdown.Coercive.ModeDerivativeHolds`.

Axial rotation of a velocity or gradient mode introduces its complex azimuthal phase together with the corresponding vector or matrix rotation. The provider is `Breakdown.CoerciveWeak.modeRotationHolds_closed`. The named statement is `Breakdown.Coercive.ModeRotationHolds`.

The solenoidal-part statement supplies a unique projected field, its norm bound, the reflection-norm identity, and covariance under time shifts and axial rotations. The provider is `Breakdown.CoerciveWeak.solenoidalModeHolds_closed`. The named statement is `Breakdown.Coercive.SolenoidalModeHolds`.

### The cell potential and row stages

The finite-cell route alternates between identities and bounds. The low-tail and row-matching steps identify the physical quantities represented by finite data; the potential and credit stages then estimate those quantities. Positive-radius and axis-aware trace statements carry different hypotheses.

For a valid cell mesh, each physical cell tuple gives square-integrable band profiles. The provider is `Breakdown.CertCell.Assembly.bandProfileIntegrable_holds`. The named statement is `Breakdown.CertCell.Assembly.BandProfileIntegrableHolds`.

The resolved epsilon and long-partner charges are bounded by the box-pair amount of the remaining profile restricted to the resolved labels. The provider is `Breakdown.CertCell.Assembly.epsResolvedStage_holds`. The named statement is `Breakdown.CertCell.Assembly.EpsResolvedStageHolds`.

The negative sum of the group-own and group-partner amounts is bounded by twice the model pairing of the upper profile with the deactivated partners. The provider is `Breakdown.CertCell.Assembly.groupStageHolds`. The named statement is `Breakdown.CertCell.Assembly.GroupStageHolds`.

On each resolved label and almost everywhere in the cell rectangle, the true profile equals the low reconstruction from the cell state plus the tail profile. The provider is `Breakdown.CertCell.Assembly.lowTailSplit_holds`. The named statement is `Breakdown.CertCell.Assembly.LowTailSplitHolds`.

The model stage combines upper, band and tail pairings with the epsilon, long and high-charge terms under the common cell-state, regularity, potential-condition and low-tail-splitting assumptions. The provider is `Breakdown.CertCell.Assembly.modelStageHolds`. The named statement is `Breakdown.CertCell.Assembly.ModelStageHolds`.

The three potential assemblies expose alternative intermediate inputs while returning the same potential-stage contract; finiteness of cell pieces, membership of physical cell states and the potential conditions remain visible in that contract. The providers are `Breakdown.CertCell.Assembly.potentialStageHolds_of`, `Breakdown.CertCell.Assembly.potentialStageHolds_of_epsGroupCharge`, `Breakdown.CertCell.Assembly.potentialStageHolds_of_epsResolved`. The named statement is `Breakdown.CertCell.Assembly.PotentialStageHolds`.

The sharp stage bounds the box-pair amount after subtracting the band and tail absorption amounts by the remaining leaf pairing, true stretching and stretch-charge amount. The provider is `Breakdown.CertCell.Assembly.sharpStageHolds`. The named statement is `Breakdown.CertCell.Assembly.SharpStageHolds`.

The splitting contract records three equalities: the off-charge separates into stretch charge and surplus, the leaf-pair difference separates into cross and remaining-profile terms, and tail absorption equals the sum of its labelled curl, strain and velocity contributions. The provider is `Breakdown.CertCell.Assembly.splitIdentities_holds`. The named statement is `Breakdown.CertCell.Assembly.SplitIdentitiesHolds`.

The inverse-weighted square of the error piece is bounded by the three error allowances for resolved, band and deactivated-source labels. The provider is `Breakdown.CertCell.Assembly.errorPieceBound_holds`. The named statement is `Breakdown.CertCell.Assembly.ErrorPieceBoundHolds`.

For every band label and almost every point in the cell rectangle, the radius times the specified gradient slots equals the turn-matrix combination of the velocity slots. The provider is `Breakdown.CertCell.bandProfileTurned_closed`. The named statement is `Breakdown.CertCell.Assembly.BandProfileTurnedHolds`.

The perturbation hypotheses imply that the period integral of the spatial sixth-power integral raised to the one-sixth power is finite. The provider is `Breakdown.CertCell.velocitySixthIntegral_closed`. The named statement is `Breakdown.CertCell.Bridge.VelocitySixthIntegralHolds`.

For almost every positive radius, the planar velocity and its first height derivative have the stated weak height derivatives on every symmetric finite height interval; the mixed gradient derivative is retained as well. The providers are `Breakdown.CertCell.modeHeightDeriv_closed`, `Breakdown.CertCell.Bridge.modeHeightDeriv`. The named statement is `Breakdown.CertCell.Bridge.ModeHeightDerivHolds`.

Away from the axis, flipping the azimuthal label preserves the strip velocity moment up to the component sign and reverses the corresponding height-derivative sign. The provider is `Breakdown.CertCell.stripDataFlip_closed`. The named statement is `Breakdown.CertCell.Bridge.StripDataFlipHolds`.

The axis strip version permits the lower radial endpoint to be zero; its height-derivative identity additionally retains the axis-admissible-test condition. The provider is `Breakdown.CertCell.planeFlipStrip_closed`. The named statement is `Breakdown.CertCell.PlaneFlipFacts.StripDataFlipAxisHolds`.

The positive-radius and axis-aware corner statements give the same component-sign relation for the corner moment, while the axis-aware version permits the other radius to be zero and still requires distinct radii. The providers are `Breakdown.CertCell.cornerDataFlip_closed`, `Breakdown.CertCell.planeFlipCorner_closed`. The named statements are `Breakdown.CertCell.Bridge.CornerDataFlipHolds`, `Breakdown.CertCell.PlaneFlipFacts.CornerDataFlipAxisHolds`.

For almost every positive radius, the upper velocity trace transforms by the component sign, and the upper height-derivative trace transforms by its negative. The provider is `Breakdown.CertCell.planeDataFlip_closed`. The named statement is `Breakdown.CertCell.Bridge.PlaneDataFlipHolds`.

An even scalar field with the stated periodicity, weak gradient and local square-integrability assumptions has the same upper scalar trace after the azimuthal-label flip. The provider is `Breakdown.CertCell.scalarPlaneFlip_closed`. The named statement is `Breakdown.CertCell.Bridge.ScalarPlaneFlipHolds`.

The cell assembly bounds the square root of weighted perturbation energy plus multiplier energy by the forcing norm, row functional and pin term for every admissible parameter. The provider is `Breakdown.CertCell.extendedCoerciveClause_of_parts`. The named statement is `Breakdown.CoerciveWeak.ExtendedCoerciveClause`.

Under the credit-evaluation conditions, every credit-data vector formed from the physical fields equals the data vector of its recorded credit patch. The provider is `Breakdown.CertCell.creditEvalMatches_closed`. The named statement is `Breakdown.CertCell.CreditEval.CreditEvalMatchesHolds`.

Twice the sum of the credit-patch quadratic forms is bounded by the sum of the cell credit shares, with mesh validity, the mode class and credit-evaluation conditions retained. The provider is `Breakdown.CertCell.creditLeavesBound`. The named statement is `Breakdown.CertCell.CreditEval.CreditLeavesBoundHolds`.

Velocity and gradient components of a mode are integrable on each bounded plane rectangle whose radial interval starts at zero. The provider is `Breakdown.CertCell.SideTrace.modeAxisPlainIntegrable`. The named statement is `Breakdown.CertCell.SideTrace.ModeAxisPlainIntegrableHolds`.

If the phase associated with a time-shift and axial-rotation symmetry differs from one, that mode of velocity, gradient and second derivative vanishes almost everywhere. The provider is `Breakdown.CertCell.Bridge.modeOffLattice`. The named statement is `Breakdown.CertCell.Bridge.ModeOffLatticeHolds`.

On positive-radius plane rectangles, the mode velocity has the specified radial, height and mixed weak derivatives, and the gradient and second-derivative components are integrable. The provider is `Breakdown.CertCell.SideTrace.modePlaneDerivs`. The named statement is `Breakdown.CertCell.SideTrace.ModePlaneDerivsHolds`.

A time shift and axial rotation act on a velocity mode by the joint complex phase and the rotated component matrix, under the displayed orbit-integrability condition. The provider is `Breakdown.CertCell.Bridge.modeShiftRotate`. The named statement is `Breakdown.CertCell.Bridge.ModeShiftRotateHolds`.

The harmonic value of a side-velocity datum in the local layout equals the harmonic value of its corresponding skeleton key in the shared layout. The provider is `Breakdown.CertCell.Assembly.sideVelocityKeyMatch_holds`.

A nonprivate plane key in the indicated half-plane transforms by its key-flip sign when its mode is negated, with the field and key-mode hypotheses retained. The provider is `Breakdown.CertCell.Assembly.keyPlaneFlip_holds`. The named statement is `Breakdown.CertCell.Assembly.KeyPlaneFlip`.

For a flux row, agreement of every relevant lower-rank row implies agreement of the current row with its shifted physical field data. The provider is `Breakdown.CertCell.Assembly.fluxRowsMatchHolds_of`. The named statement is `Breakdown.CertCell.Assembly.FluxRowsMatchHolds`.

For a split row, the corresponding lower-rank agreement hypothesis yields agreement of that row with the shifted physical field data. The provider is `Breakdown.CertCell.Assembly.splitRowsMatchHolds_of`. The named statement is `Breakdown.CertCell.Assembly.SplitRowsMatchHolds`.

The full row-matching assembly retains the harmonic, strip, corner, flip, pressure and gauge inputs before deriving agreement of the finite rows with the physical fields. The provider is `Breakdown.CertCell.Assembly.rowsMatchFieldsHolds_of_parts`. The named statement is `Breakdown.CertCell.Assembly.RowsMatchFieldsHolds`.

### Smoothing kernels and physical windows

The weak-to-smooth route uses explicit kernel estimates, short physical-time windows and a return to similarity time. A module name mentioning fractional analysis can contain a reusable scalar inequality used here by the classical route; the statement determines its scope.

The bilinear-symbol bridge combines the homogeneous Wiener statement with recovery of velocity from its symbol to obtain the bilinear-symbol formula. The provider is `Breakdown.FarField.bilinSymbolOfVelocity_holds`. The named statement is `Breakdown.FarField.BilinSymbolOfVelocity`.

For positive time, every Leray-kernel component is bounded by a common constant times $(\lVert x\rVert+\sqrt{\tau})^{-4}$. The provider is `Breakdown.FarField.lerayKernelBound_holds`. The named statement is `Breakdown.FarField.LerayKernelBound`.

Each Leray-kernel component is measurable jointly in time and space. The provider is `Breakdown.FarField.lerayKernelMeasurable_holds`. The named statement is `Breakdown.FarField.LerayKernelMeasurable`.

At every positive time, each Leray-kernel component is continuously differentiable in space. The provider is `Breakdown.FarField.lerayKernelC1_holds`. The named statement is `Breakdown.FarField.LerayKernelC1`.

At positive time, summing the spatial derivatives of the Leray kernel over its velocity index gives zero. The provider is `Breakdown.FarField.lerayKernelDivFree_holds`. The named statement is `Breakdown.FarField.LerayKernelDivFree`.

Every positive-time kernel component is integrable and has absolute integral at most a common constant times $\tau^{-1/2}$. The provider is `Breakdown.FarField.kernelL1Bound_holds`. The named statement is `Breakdown.FarField.KernelL1Bound`.

Convolution of the kernel with a measurable tensor field bounded by $A$ has pointwise norm at most a common constant times $\tau^{-1/2}A$. The provider is `Breakdown.FarField.kernelConvSup_holds`. The named statement is `Breakdown.FarField.KernelConvSup`.

For a solenoidal test field, the negative kernel convolution with its tensor square satisfies the decay-field predicate at positive time. The provider is `Breakdown.FarField.kernelConvTestDecay_holds`. The named statement is `Breakdown.FarField.KernelConvTestDecay`.

A mild flow on a closed time interval remains mild after its left endpoint is moved to any later point of that interval. The provider is `Breakdown.FarField.mildRestrict_holds`. The named statement is `Breakdown.FarField.MildRestrict`.

Each similarity-time origin of the recurrent orbit produces a rescaled physical mild flow on every closed interval from zero to a time strictly below one. The provider is `Breakdown.FarField.orbitWindows_holds`. The named statement is `Breakdown.FarField.OrbitWindows`.

A uniform bound on a mild flow supplies a positive window length on which the fixed-point iterates from its initial value converge pointwise in time to that flow. The provider is `Breakdown.FarField.picardConverges_holds`. The named statement is `Breakdown.FarField.PicardConverges`.

The Picard derivative-bound assembly takes derivative algebra, the heat and integral derivative rules, difference quotients and the bilinear Leibniz rule as separate inputs. The provider is `Breakdown.FarField.picardDerivBoundOfCalculus_holds`. The named statement is `Breakdown.FarField.PicardDerivBoundOfCalculus`.

The first conditional assembly concludes existence of a smooth periodic similarity profile from the weak-profile hypothesis; the following assembly feeds that conclusion into periodic breakdown. Their analytic inputs remain arguments of the respective theorems. The providers are `Breakdown.FarField.periodicLerayProfileExists_of_weak_of_parts`, `Breakdown.FarField.breakdownOnTorus_of_weak_of_parts`. The named statement is `Breakdown.WeakPeriodicSimilarityProfileExists`.

A smooth physical-time solution and pressure on a window strictly below time one give smooth similarity fields with zero similarity residual and zero divergence on the corresponding open logarithmic-time window. The provider is `Breakdown.FarField.windowResidual_holds`. The named statement is `Breakdown.FarField.WindowResidual`.

The half-plane estimate bounds the inverse-square weighted scalar energy by the radial, vertical and angular derivative energies; it uses $s=|k|+1/2$, or $s=|k|+3/2$ when the scalar amplitude is odd in height. The provider is `Breakdown.FracInternal.FrameInverseSquareParts.halfPlaneBound'`. The named statement is `Breakdown.FracInternal.FrameInverseSquareParts.HalfPlaneBoundStatement`.

### Physical interpretation and weak time evolution

The physical reading must remain compatible with the Fourier realization, dilation and the weak evolution equation. The good-time statements first give tested identities and then identify a continuous mild representative.

For a solenoidal test field, embedding its negative second-derivative sum gives the abstract second-derivative relation of the embedded test field. The provider is `Breakdown.Freq.embedNegSsp_holds`. The named statement is `Breakdown.Freq.EmbedNegSsp`.

When two Hilbert vectors satisfy the half-order relation, the recovered velocity of the second equals the physical reading of the first almost everywhere. The provider is `Breakdown.Freq.velocityInverts_holds`. The named statement is `Breakdown.Freq.VelocityInvertsHalfSsp`.

The velocity-covariance proof returns both the rotation and dilation identities for recovered fields as almost-everywhere equalities. The provider is `Breakdown.Freq.velocityCov_holds`. The named statements are `Breakdown.Freq.VelocityRotate`, `Breakdown.Freq.VelocityDilate`.

For a smooth H1 field whose value and derivative are bounded, the self-interaction of its embedding equals negative divergence-free heat evolution of its advection field. The provider is `Breakdown.Freq.bilinH1Formula_holds`. The named statement is `Breakdown.Freq.BilinH1Formula`.

The orbit assembly keeps decay-field subtraction, slice decay, slice-gradient continuity, the physical mild equation and conversion back to similarity time as its five inputs. The provider is `Breakdown.orbitOfParts_holds`. The named statement is `Breakdown.OrbitOfParts`.

The whole-space shell interaction is bounded by a common constant times $\tau^{-3/4}$, the norm of the embedded test field and the shell-data norm. The provider is `Breakdown.Periodic.r3LambdaBound_holds`. The named statement is `Breakdown.Periodic.R3LambdaBound`.

The periodic shell estimate has the same $\tau^{-3/4}$ factor and additionally retains the shell-scale condition and the short-time restriction $\mu\tau\leq1$. The provider is `Breakdown.Periodic.torusLambdaBound_holds`. The named statement is `Breakdown.Periodic.TorusLambdaBound`.

Positive dilation and the corresponding time rescaling carry a mild solution on the interval ending at the scaled time to a mild solution on the original time interval. The provider is `Breakdown.scale`. The named statement is `Breakdown.ScaleStatement`.

A continuous similarity-time curve satisfying the similarity Duhamel identity becomes a physical mild flow on the half-open interval from zero to one, for every similarity-time origin. The provider is `Breakdown.orbitPhysical`. The named statement is `Breakdown.OrbitPhysicalStatement`.

The integral of the tensor advection pairing with a solenoidal test field equals the negative abstract trilinear form. The provider is `Breakdown.WeakProfile.advectionByParts_holds`. The named statement is `Breakdown.WeakProfile.AdvectionByParts`.

A bounded almost-everywhere strongly measurable Hilbert curve has an interval-integrable bilinear Duhamel term, including zero heat regularization. The provider is `Breakdown.WeakProfile.bilinIntegrable_holds`. The named statement is `Breakdown.WeakProfile.BilinIntegrable`.

The bilinear integrability interface makes the variation-of-constants representative continuous from its chosen starting time up to the open right endpoint. The provider is `Breakdown.WeakProfile.continuousVarConst_holds`. The named statement is `Breakdown.WeakProfile.ContinuousVarConst`.

The dilation identity moves positive Hilbert-space dilation from the curve to the inverse square-root spatial scaling of the test field inside the pairing. The provider is `Breakdown.WeakProfile.pairingDilate_holds`. The named statement is `Breakdown.WeakProfile.PairingDilate`.

Pairing a Hilbert vector with an embedded solenoidal test field equals the physical velocity paired with the negative second-derivative sum of that test field. The provider is `Breakdown.WeakProfile.pairingVelocity_holds`. The named statement is `Breakdown.WeakProfile.PairingVelocity`.

An almost-everywhere strongly measurable similarity-time curve gives an almost-everywhere strongly measurable physical curve on times below one. The provider is `Breakdown.WeakProfile.physicalCurveMeasurable_holds`. The named statement is `Breakdown.WeakProfile.PhysicalCurveMeasurable`.

Using the velocity weak-gradient identity, dilation of both repeated Hilbert inputs transfers to the inverse square-root spatial scaling of the test field in the trilinear form. The provider is `Breakdown.WeakProfile.trilinearDilate_holds`. The named statement is `Breakdown.WeakProfile.TrilinearDilate`.

At ordered times in the common good set, the variation-of-constants representative equals the original Hilbert curve; the integrability and tested-integral interfaces are explicit premises. The provider is `Breakdown.WeakProfile.varConstGood_holds`. The named statement is `Breakdown.WeakProfile.VarConstGood`.

At two ordered good times, testing against a positive-time heat smoothing gives the initial heat pairing plus the time integral of the bilinear pairing. The provider is `Breakdown.WeakProfile.varConstInner_holds`. The named statement is `Breakdown.WeakProfile.VarConstInner`.

Against a compactly supported smooth scalar test function, each recovered Fourier derivative satisfies the physical weak-gradient integration-by-parts identity. The provider is `Breakdown.WeakProfile.velocityWeakGradient_holds`. The named statement is `Breakdown.WeakProfile.VelocityWeakGradient`.
<!-- /passage:sec-following-the-closed-assembly-into-its-analytic-statements -->

## Analytic implementations behind the endpoint assemblies

<!-- passage:sec-analytic-implementations-behind-the-endpoint-assemblies -->

### Direct implementations of the preceding contracts

The preceding assembly guides describe the contracts used along the endpoint routes. These paragraphs connect additional direct implementations to the same source-read mathematical statements. The theorem hypotheses remain visible when the linked source is opened.

The weighted square integral of $Aw$ is at most $4/3$ times the two-thirds power of the cubic integral of $|A|$ times the gradient energy of $w$, under the displayed weak-gradient and integrability hypotheses. The provider is `Breakdown.CertReduction.cubicWeightProductHolds`. The contract is `Breakdown.CertReduction.CubicWeightProductHolds`.

The selected cubic or uniform piece-gradient bound controls the squared period norm of the shift derivative applied to the velocity, with the corresponding gap-gradient coefficient retained. The provider is `Breakdown.CertReduction.gapGradTerm_of`. The contract is `Breakdown.CertReduction.GapGradTermHolds`.

A uniform bound $s$ on the shift controls the squared period norm of the gradient applied to that shift by $(s/\sqrt{w_0})^2$ times the weighted perturbation energy. The provider is `Breakdown.CertReduction.gapSupTerm_of`. The contract is `Breakdown.CertReduction.GapSupTermHolds`.

The shape instantiation supplies a decay constant for which the structural certificate clauses hold, under the generated-symmetry, nonzero-scale and bounded-instantiation assumptions. Each pin field must be measurable and have finite period square integral. The theorem assembles the moved-field, affine-field, pressure and pin-continuity interfaces. The provider is `Breakdown.CellReduction.Instantiation.instantiation_holds_of`. The contract is `Breakdown.CellReduction.Instantiation.InstantiationHolds`.

When each active shape amplitude has high order at least three, the shape field is the curl of a time-periodic continuously differentiable potential; the potential and its time derivative decay quadratically, and its spatial derivative decays cubically. The provider is `Breakdown.CellReduction.Instantiation.fieldPotential_holds_of`. The contract is `Breakdown.CellReduction.Instantiation.FieldPotentialHolds`.

A perturbation has, for almost every time, the first and second weak-gradient identities together with finite sixth-power velocity, gradient-square, and second-derivative-trace integrals. The provider is `Breakdown.CertReduction.perturbationSliceHolds`. The contract is `Breakdown.CertReduction.PerturbationSliceHolds`.

A piece-gradient bound on the shift derivative controls the stationary pairing with the second-derivative trace, using the coefficient selected by the cubic flag. The provider is `Breakdown.CertReduction.shiftGradTerm_of`. The contract is `Breakdown.CertReduction.ShiftGradTermHolds`.

A uniform shift bound controls its stationary pairing with the second-derivative trace by $s/(2\sqrt{w_0})$ times the stationary energy. The provider is `Breakdown.CertReduction.shiftSupTerm_of`. The contract is `Breakdown.CertReduction.ShiftSupTermHolds`.

For a weakly twice differentiable $L^6$ field, the squared pointwise magnitude is bounded almost everywhere by $(2\pi)^{-1}$ times the product of the square roots of the gradient energy and the squared second-derivative-trace integral. The provider is `Breakdown.CertReduction.sliceSupNorm_of`. The contract is `Breakdown.CertReduction.SliceSupNormHolds`.

A lower quadratic-form bound $-S$ on the background derivative yields the lower bound $-(S/w_0)$ times the stationary energy for the convection pairing. The provider is `Breakdown.CertReduction.strainTerm_of`. The contract is `Breakdown.CertReduction.StrainTermHolds`.

The mode-density statement produces a multiplier field with finite frequency seminorm, bounds its period norm by weighted and mode energy, and compares the positive and negative density integrals with the signed multiplier gap. This direct provider consumes the multiplier-field existence, field-density and absorption interfaces. The provider is `Breakdown.Coercive.multiplierDensity_of_field`. The contract is `Breakdown.Coercive.MultiplierDensityHolds`.

The piecewise-density statement produces a multiplier field with finite seminorm, bounds its period norm by weighted and piecewise mode energy, and gives the positive-versus-negative density integral comparison. Its direct provider uses the piece-field, field-density and absorption interfaces. The provider is `Breakdown.Coercive.pieceMultiplierDensity_of_field`. The contract is `Breakdown.Coercive.PieceMultiplierDensityHolds`.

For an azimuthal index of magnitude at least two, the mode estimates compare velocity to gradient and gradient to second derivative with the factors $(|k|-1)^2/r^2$ and $(|k|-2)^2/r^2$, respectively, almost everywhere. The providers are `Breakdown.Coercive.modeAzimuthalGainHolds_of_nodes`, `Breakdown.Coercive.modeAzimuthalGainHolds_proof_of`. The contract is `Breakdown.Coercive.ModeAzimuthalGainHolds`.

The negative angular and time integral of stretching is bounded by the sum of the mode stretch charges, with the angular factor of two pi carried explicitly. The providers are `Breakdown.Coercive.stretchMeanBoundHolds_of_nodes`, `Breakdown.Coercive.stretchMeanBoundHolds_proof_of`. The contract is `Breakdown.Coercive.StretchMeanBoundHolds`.

The mode-derivative statement supplies the weak-gradient identities for the real and imaginary parts of velocity and gradient modes, and the zero trace of the mode gradient. The provider is `Breakdown.Coercive.modeDerivativeHolds_of`. The contract is `Breakdown.Coercive.ModeDerivativeHolds`.

Axial rotation of a velocity or gradient mode introduces its complex azimuthal phase together with the corresponding vector or matrix rotation. The provider is `Breakdown.Coercive.modeRotationHolds_of`. The contract is `Breakdown.Coercive.ModeRotationHolds`.

The solenoidal-part statement supplies a unique projected field, its norm bound, the reflection-norm identity, and covariance under time shifts and axial rotations. The provider is `Breakdown.Coercive.solenoidalModeHolds_of`. The contract is `Breakdown.Coercive.SolenoidalModeHolds`.

The mode-square-sum statement identifies the period energies of velocity, gradient, and second derivative with their sums over time and azimuthal modes, and also gives the corresponding summed pairing identity. The provider is `Breakdown.Coercive.modeSquareSumHolds_of`. The contract is `Breakdown.Coercive.ModeSquareSumHolds`.

The extended coercivity clause bounds the square root of weighted perturbation energy plus multiplier energy by forcing, row-functional and pin terms at every admissible parameter. The piece-data provider obtains this clause from the weak-background piece-density estimate and the displayed finite-data remainder inequality. The provider is `Breakdown.CoerciveWeak.extendedCoerciveClause_of_pieceDataHolds`. The contract is `Breakdown.CoerciveWeak.ExtendedCoerciveClause`.

For every band label and almost every point in the cell rectangle, the radius times the specified gradient slots equals the turn-matrix combination of the velocity slots. The provider is `Breakdown.CertCell.Assembly.bandProfileTurned_holds`. The contract is `Breakdown.CertCell.Assembly.BandProfileTurnedHolds`.

Assembly regularity, true-field regularity, membership of the physical cell states and the finite pairing conditions imply the physical pairing stage. The provider uses the low-tail splitting and projected-residual orthogonality statements to pass from those finite conditions to the physical pairing conclusion. The provider is `Breakdown.CertCell.Assembly.pairingStageHolds_of_lowTailSplit`. The contract is `Breakdown.CertCell.Assembly.PairingStageHolds`.

The resolved epsilon and long-partner charges are bounded by the box-pair amount of the remaining profile restricted to the resolved labels. The provider is `Breakdown.CertCell.Assembly.epsResolvedStage_holds_of`. The contract is `Breakdown.CertCell.Assembly.EpsResolvedStageHolds`.

The negative sum of the group-own and group-partner amounts is bounded by twice the model pairing of the upper profile with the deactivated partners. The provider is `Breakdown.CertCell.Assembly.Internal.groupStageHolds_of`. The contract is `Breakdown.CertCell.Assembly.GroupStageHolds`.

The model stage combines upper, band and tail pairings with the epsilon, long and high-charge terms under the common cell-state, regularity, potential-condition and low-tail-splitting assumptions. The provider is `Breakdown.CertCell.Assembly.Internal.ModelPart.modelStage_of_point`. The contract is `Breakdown.CertCell.Assembly.ModelStageHolds`.

The potential-stage statement gives the physical potential estimate under finiteness of cell pieces, physical cell-state membership and the potential conditions. Its parts provider assembles the model, sharp and grouped-charge estimates with the exact potential-splitting identities. The provider is `Breakdown.CertCell.Assembly.potentialStage_of_parts`. The contract is `Breakdown.CertCell.Assembly.PotentialStageHolds`.

The sharp stage bounds the box-pair amount after subtracting the band and tail absorption amounts by the remaining leaf pairing, true stretching and stretch-charge amount. The provider is `Breakdown.CertCell.Assembly.Internal.Sharp.sharpStageHolds_of`. The contract is `Breakdown.CertCell.Assembly.SharpStageHolds`.

The splitting contract records three equalities: the off-charge separates into stretch charge and surplus, the leaf-pair difference separates into cross and remaining-profile terms, and tail absorption equals the sum of its labelled curl, strain and velocity contributions. The provider is `Breakdown.CertCell.Assembly.splitIdentities_of_tail`. The contract is `Breakdown.CertCell.Assembly.SplitIdentitiesHolds`.

The inverse-weighted square of the error piece is bounded by the three error allowances for resolved, band and deactivated-source labels. The provider is `Breakdown.CertCell.Assembly.errorPieceBound_of`. The contract is `Breakdown.CertCell.Assembly.ErrorPieceBoundHolds`.

For the positive-radius corner data, flipping the azimuthal label multiplies each corner-moment component by its specified sign. This provider uses the corner trace, corner matching and trace-flip interfaces; the separate axis-aware result permits a zero radius and remains a distinct statement. The provider is `Breakdown.CertCell.Bridge.cornerDataFlip`. The contract is `Breakdown.CertCell.Bridge.CornerDataFlipHolds`.

Under the credit-evaluation conditions, every credit-data vector formed from the physical fields equals the data vector of its recorded credit patch. The provider is `Breakdown.CertCell.CreditEval.creditEvalMatches`. The contract is `Breakdown.CertCell.CreditEval.CreditEvalMatchesHolds`.

For almost every positive radius, the upper velocity trace transforms by the component sign, and the upper height-derivative trace transforms by its negative. The provider is `Breakdown.CertCell.Bridge.planeDataFlip`. The contract is `Breakdown.CertCell.Bridge.PlaneDataFlipHolds`.

The full row-matching assembly retains the harmonic, strip, corner, flip, pressure and gauge inputs before deriving agreement of the finite rows with the physical fields. The provider is `Breakdown.CertCell.Assembly.rowsMatchFieldsHolds_of_kinds`. The contract is `Breakdown.CertCell.Assembly.RowsMatchFieldsHolds`.

An even scalar field with the stated periodicity, weak gradient and local square-integrability assumptions has the same upper scalar trace after the azimuthal-label flip. The provider is `Breakdown.CertCell.Bridge.scalarPlaneFlip`. The contract is `Breakdown.CertCell.Bridge.ScalarPlaneFlipHolds`.

Away from the axis, flipping the azimuthal label preserves the strip velocity moment up to the component sign and reverses the corresponding height-derivative sign. The provider is `Breakdown.CertCell.Bridge.stripDataFlip`. The contract is `Breakdown.CertCell.Bridge.StripDataFlipHolds`.

The perturbation hypotheses imply that the period integral of the spatial sixth-power integral raised to the one-sixth power is finite. The provider is `Breakdown.CertCell.Bridge.velocitySixthIntegral`. The contract is `Breakdown.CertCell.Bridge.VelocitySixthIntegralHolds`.

The half-plane estimate bounds the inverse-square weighted scalar energy by the radial, vertical and angular derivative energies; it uses $s=|k|+1/2$, or $s=|k|+3/2$ when the scalar amplitude is odd in height. The provider is `Breakdown.FracInternal.FrameInverseSquareHalfPlane.halfPlaneBound_of_axis`. The contract is `Breakdown.FracInternal.FrameInverseSquareParts.HalfPlaneBoundStatement`.

A physical mild solution related to the similarity curve by the displayed dilation and logarithmic change of time gives the similarity Duhamel identity between any two ordered similarity times. The conclusion includes interval integrability of its bilinear term. The provider is `Breakdown.flowOfMild_holds`. The contract is `Breakdown.FlowOfMild`.

For a smooth similarity profile whose embedding is continuous in similarity time, the embedded physical field is mild on every closed interval from zero to T with zero less than T less than one. The time origin is arbitrary, and the provider retains its dilation, decay, physical L2, weak-equation and joint-continuity inputs. The provider is `Breakdown.physicalMild_holds`. The contract is `Breakdown.PhysicalMild`.

As the positive torus scale tends to zero, both the restricted interaction operator and the restricted initial-data operator become uniformly close in operator norm to their whole-space counterparts. The statement retains the finite-dimensional test lift, approximant, step-size and contraction-factor hypotheses and supplies a scale threshold for every positive tolerance. The provider is `Breakdown.Periodic.comparisonSmall_of_parts`. The contract is `Breakdown.Periodic.ComparisonSmall`.

Compatible mild pieces with a common scale ratio between zero and one glue to a mild solution on the half-open interval from zero to one. Every time belongs to a geometric piece with $1-t=\mu^n(1-s)$, and the formula identifies the corresponding dilated piece value with the glued field. The provider is `Breakdown.glue_of`. The contract is `Breakdown.GlueStatement`.

A continuous similarity-time curve satisfying the similarity Duhamel identity becomes a physical mild flow on the half-open interval from zero to one, for every similarity-time origin. The provider is `Breakdown.orbitPhysical_of`. The contract is `Breakdown.OrbitPhysicalStatement`.

The bilinear operator on a time piece evaluates to the Duhamel integral and has norm at most $4C_K T^{1/4}$ for positive T at most one. The free piece evaluates to the heat evolution and has operator norm at most one. The provider is `Breakdown.pieceOperator_of`. The contract is `Breakdown.PieceOperatorStatement`.

On a positive time interval of length at most one, a piece solving the displayed quadratic perturbation equation has the prescribed initial change and turns the mild background plus that piece into another mild solution. The provider is `Breakdown.piecePerturbation_of`. The contract is `Breakdown.PiecePerturbationStatement`.

Each positive subdivision count turns a recurrent orbit into mild pieces with the prescribed dilation matching at successive endpoints and the original twist after one full period. A uniform orbit bound M becomes the piece bound $\exp(P/(4k))M$. The provider is `Breakdown.profilePiece_of`. The contract is `Breakdown.ProfilePieceStatement`.

Positive dilation and the corresponding time rescaling carry a mild solution on the interval ending at the scaled time to a mild solution on the original time interval. The provider is `Breakdown.scale_of`. The contract is `Breakdown.ScaleStatement`.

There is a positive small-data threshold for which every initial vector below the threshold has a mild solution on the entire unit interval, starts at that vector and has norm at most twice the initial norm throughout the interval. The provider is `Breakdown.smallData_of`. The contract is `Breakdown.SmallDataStatement`.

Two abstract mild solutions with the same initial value agree throughout the common half-open interval. The companion clause gives the same uniqueness conclusion on a common closed interval when both solutions satisfy the closed-interval mild definition. The provider is `Breakdown.unique_of`. The contract is `Breakdown.UniqueStatement`.

### Density identities and analytic passage

The multiplier route uses concrete energy identities, Fourier-mode estimates and limit passages. The following statements identify what is established before the final density and certificate inequalities are assembled.

A split lower bound for the multiplier gap yields the comparison between the positive and negative density integrals, retaining the two extended-real terms for the positive and negative parts of the scalar lower bound. The piecewise version also retains its block term; its proof requires the Hessian energy bound and local square integrability in addition to the mode Parseval statement. The providers are `Breakdown.Coercive.modeAbsorbStepHolds_of`, `Breakdown.Coercive.pieceAbsorbStepHolds_of`. The contracts are `Breakdown.Coercive.ModeAbsorbStepHolds`, `Breakdown.Coercive.PieceAbsorbStepHolds`.

Given a smooth approximation of a perturbation, the density-passage theorems preserve the split lower bound for the multiplier gap in the limit. The field versions obtain such an approximation from the approximation interface, so it no longer appears as a caller-supplied sequence. Mode weights and piece weights have separate statements because the latter carry a nonzero block contribution. The providers are `Breakdown.Coercive.modeDensityPassageHolds_of`, `Breakdown.Coercive.pieceDensityPassageHolds_of`, `Breakdown.Coercive.modeDensityOfField_of_passage`, `Breakdown.Coercive.pieceDensityOfField_of_passage`. The contracts are `Breakdown.Coercive.ModeDensityPassageHolds`, `Breakdown.Coercive.PieceDensityPassageHolds`, `Breakdown.Coercive.ModeDensityOfFieldHolds`, `Breakdown.Coercive.PieceDensityOfFieldHolds`.

The mode and piecewise density bounds give the same certificate multiplier interface once the negative density is integrable and the displayed remainder inequality holds uniformly on the parameter box. The resulting coefficient is $a=\sqrt{(1+\varepsilon_{\mathrm{sup}}+\varepsilon_{\mathrm{grad}}/\sqrt{w_0})^2/c+\mathrm{ratio}/c_\mu}$; the conclusion includes an admissible multiplier, its norm bound, and the energy inequality with forcing, ball and pin terms. The providers are `Breakdown.Coercive.multiplierInequality_of_densityHolds`, `Breakdown.Coercive.multiplierInequality_of_pieceDensityHolds`. The contract is `Breakdown.MultiplierInequality`.

Admissible mode weights and an upper bound for the spatial weight imply a finite frequency seminorm and the existence of a multiplier field whose period norm is bounded by the prescribed multiplier constant times the square root of weighted energy plus mode energy. The proof consumes the mode Parseval, derivative, rotation and local square-integrability interfaces. The provider is `Breakdown.Coercive.modeFieldExistsHolds_of`. The contract is `Breakdown.Coercive.ModeFieldExistsHolds`.

The physical solenoidal projection exists, contracts the norm, has the stated adjoint pairing against embedded Hilbert-space vectors, and returns an embedded vector unchanged. These four properties let later estimates move between the physical field and its Hilbert-space representative. The provider is `Breakdown.Coercive.projectionHolds_of_spec`. The contract is `Breakdown.Cert.ProjectionHolds`.

A perturbation has full second-derivative square integral bounded by the square integral of its second-derivative trace. Its velocity is square integrable on every spatial ball over one time period, and its velocity, gradient and second derivative are locally integrable in space-time. The three providers expose these distinct consequences of the perturbation definition. The providers are `Breakdown.Coercive.perturbationSecondDerivBoundHolds_proof`, `Breakdown.Coercive.perturbationLocalSquareIntegrabilityHolds_proof`, `Breakdown.Coercive.perturbationLocalIntegrabilityHolds_proof`. The contracts are `Breakdown.Coercive.PerturbationSecondDerivBoundHolds`, `Breakdown.Coercive.PerturbationLocalSquareIntegrabilityHolds`, `Breakdown.Coercive.PerturbationLocalIntegrabilityHolds`.

Axial rotation is realized by a linear isometry, composes by addition of angles, is the identity at zero and is periodic with period two pi. It preserves the cylindrical radius and the vertical coordinate, which is the geometry used by azimuthal Fourier modes. The provider is `Breakdown.Coercive.axialRotationHolds_proof`. The contract is `Breakdown.Coercive.AxialRotationHolds`.

For a twice differentiable divergence-free field with the stated finite-energy and weighted-decay assumptions, the weighted curl-square integral equals the weighted gradient-matrix-square integral minus the contraction of the weight Hessian with the field twice. The derivative bounds on the weight and the integrability hypotheses are retained in this integration-by-parts identity. The provider is `Breakdown.Coercive.curlWeightIdentityDecayHolds_proof`. The contract is `Breakdown.Coercive.CurlWeightIdentityDecayHolds`.

For smooth perturbations, the energy identity, multiplier-pairing split and epsilon and mu estimates combine into a split lower bound for the multiplier gap, including actuator forcing. Mode weights, piece weights and weak-background piece weights have separate providers; the last uses the supplied weak second-derivative state and its Hessian field in the rest, block and stretching terms. The providers are `Breakdown.Coercive.modeDensitySmoothHolds_of`, `Breakdown.Coercive.pieceDensitySmoothHolds_of`, `Breakdown.CoerciveWeak.pieceDensitySmoothWeakHolds_of`. The contracts are `Breakdown.Coercive.ModeDensitySmoothHolds`, `Breakdown.Coercive.PieceDensitySmoothHolds`, `Breakdown.CoerciveWeak.PieceDensitySmoothWeakHolds`.

The period pairing of the smooth right side with the negative second-derivative trace equals the integral of the squared curl gradient, one quarter of the curl square, and the background stretching form. The background remains periodic, divergence-free, twice differentiable and subject to the displayed derivative-decay bounds. The provider is `Breakdown.Coercive.energyIdentitySmoothHolds_proof`. The contract is `Breakdown.Coercive.EnergyIdentitySmoothHolds`.

The epsilon estimate gives a split lower bound for the epsilon-weighted pairing with the smooth right side. The mu estimate applies to its solenoidal part and subtracts the frequency-seminorm contribution before forming the lower bound. Their hypotheses retain admissibility and the smooth periodic background assumptions. The providers are `Breakdown.Coercive.modeEpsEstimateSmoothHolds_of`, `Breakdown.Coercive.modeMuEstimateSmoothHolds_of`. The contracts are `Breakdown.Coercive.ModeEpsEstimateSmoothHolds`, `Breakdown.Coercive.ModeMuEstimateSmoothHolds`.

Each epsilon or mu piece contributes its own signed-weight pairing and its own mode remainder and block term. The mu piece also subtracts its share of the seminorm. These estimates are indexed by the actual finite piece families, so summing them is a later assembly step. The providers are `Breakdown.Coercive.pieceEpsEstimateSmoothHolds_of`, `Breakdown.Coercive.pieceMuEstimateSmoothHolds_of`. The contracts are `Breakdown.Coercive.PieceEpsEstimateSmoothHolds`, `Breakdown.Coercive.PieceMuEstimateSmoothHolds`.

The smooth right-side pairing with a multiplier splits exactly into the negative second-derivative-trace pairing, an epsilon pairing, and a mu pairing against the solenoidal part. Piece weights replace the last two terms by finite sums over their pieces. The weak-background version retains that exact splitting while taking its second derivative from an explicit weak-state witness. The providers are `Breakdown.Coercive.modePairingSplitSmoothHolds_of`, `Breakdown.Coercive.piecePairingSplitSmoothHolds_of`, `Breakdown.CoerciveWeak.piecePairingSplitSmoothWeakHolds_of`. The contracts are `Breakdown.Coercive.ModePairingSplitSmoothHolds`, `Breakdown.Coercive.PiecePairingSplitSmoothHolds`, `Breakdown.CoerciveWeak.PiecePairingSplitSmoothWeakHolds`.

A smooth perturbation supplies an ordinary perturbation with its classical gradient, second derivative and transport term, and with the empty symmetry set. This provider makes the smooth estimates available to interfaces phrased for weak perturbations. The provider is `Breakdown.Coercive.smoothPerturbationIsPerturbationHolds_proof`. The contract is `Breakdown.Coercive.SmoothPerturbationIsPerturbationHolds`.

For a Lipschitz weight and twice differentiable fields, the weighted difference of the two Laplacian pairings equals the negative integral of the weight gradient contracted with the corresponding first-derivative pairings. The three displayed integrability hypotheses justify the identity on the whole space. The provider is `Breakdown.Coercive.weightedSumSecondPartialsPairingHolds_proof`. The contract is `Breakdown.Coercive.WeightedSumSecondPartialsPairingHolds`.

A measurable periodic square-integrable field that pairs to zero with every periodic gradient test and every periodic solenoidal test field vanishes almost everywhere. This is the uniqueness statement needed when both testing classes have identified a field. The provider is `Breakdown.Coercive.gradSolenoidalDensityHolds_proof`. The contract is `Breakdown.Coercive.GradSolenoidalDensityHolds`.

The sum over integer time and angular frequencies of the squared mode averages is $(2\pi)^{-1}$ times the square integral over the unit time interval and the full angular interval. The statement requires measurability and finite square integral on that product domain. The provider is `Breakdown.Coercive.torusSquareSumHolds_proof`. The contract is `Breakdown.Coercive.TorusSquareSumHolds`.

Weak-background admissibility implies admissibility of the corresponding zero-flow weights. That reduction and the ordinary piece-field existence theorem supply a finite seminorm and a multiplier with the stated energy norm bound for the weak-background data. The providers are `Breakdown.CoerciveWeak.zeroFlowAdmissibleHolds_proof`, `Breakdown.CoerciveWeak.pieceFieldExistsWeak_of_zeroFlow`. The contracts are `Breakdown.CoerciveWeak.ZeroFlowAdmissibleHolds`, `Breakdown.CoerciveWeak.PieceFieldExistsWeakHolds`.

At every time, the Hessian supplied by a weak second-derivative state is symmetric in its two spatial arguments almost everywhere. The exceptional spatial set may depend on time; the statement does not replace the weak Hessian by a pointwise classical second derivative. The provider is `Breakdown.CoerciveWeak.weakSecondDerivSymmetricHolds_proof`. The contract is `Breakdown.CoerciveWeak.WeakSecondDerivSymmetricHolds`.

With a constant positive weight and the structural, potential and boundedness facts for every selected adjoint entry, the forcing pairing with that adjoint differs from the coupling-weighted pin sum by at most the adjoint-defect coefficient times the square root of weighted perturbation energy. The forcing is measurable, periodic and square integrable, and represents the perturbation equation with zero finite actuator coefficient. The bound holds at every selected adjoint index and every parameter in the recorded set. The provider is `Breakdown.AdjointDefect.adjointDefectBridge_of_parts`. The contract is `Breakdown.AdjointDefect.AdjointDefectBridgeHolds`.

### Compactness and the held solution

The certificate argument joins physical pairings and compactness to a finite-dimensional multiplier correction. These providers expose the metric, continuity and weak-equation facts used by that construction.

For certificate data and a parameter in its box, a bordered inverse satisfying the recorded specification exists. The bordered operator is injective on pairs whose Hilbert component lies in the symmetry-invariant subspace. This provider consumes the compact-convection, coercivity, invariance, equivariance, data and free-inverse interfaces. The provider is `Breakdown.Cert.borderedInvertibleHolds_of`. The contract is `Breakdown.Cert.BorderedInvertibleHolds`.

A periodic physical forcing that represents the first component of the bordered equation bounds the combined solution-and-multiplier size by its period norm, its localized ball norm and the pin norm. Each of the three terms carries the corresponding certificate coercivity coefficient. The provider is `Breakdown.Cert.coerciveBorderedHolds_of`. The contract is `Breakdown.Cert.CoerciveBorderedHolds`.

The convection operator has a continuous-linear specification and is bounded by a constant times the gradient norm. Testing its Hilbert representative gives the physical sum of the perturbation gradient applied to the background and the background derivative applied to the perturbation. The provider is `Breakdown.Cert.convectionHolds_of`. The contract is `Breakdown.Cert.ConvectionHolds`.

For a certificate parameter, convection composed with the free inverse is a compact operator. The theorem obtains this conclusion from local compactness, the physical convection representation and the free-inverse interface. The provider is `Breakdown.Cert.convectionCompactHolds_of`. The contract is `Breakdown.Cert.ConvectionCompactHolds`.

The convection operator varies continuously over the certificate parameter box. The extended-data version states the corresponding continuity over its parameter set, using the extended convection interface. The providers are `Breakdown.Cert.convectionContinuityHolds_of`, `Breakdown.Cert.extendedConvectionContinuityHolds_of`. The contracts are `Breakdown.Cert.ConvectionContinuityHolds`, `Breakdown.Cert.ExtendedConvectionContinuityHolds`.

The certificate defect and finite actuator combination have the required physical test pairings and Hilbert norm bounds, and the pin map agrees with pinning the physical gradient. The extended-data provider additionally records that its supplied defect is a periodic field. Both packages retain the certificate parameter restrictions. The providers are `Breakdown.Cert.dataHolds_of`, `Breakdown.Cert.extendedDataHolds_of`. The contracts are `Breakdown.Cert.DataHolds`, `Breakdown.Cert.ExtendedDataHolds`.

The target gap is continuous on the certificate box, and the defect pairing with each fixed space-time test field is continuous there. These are the parameter-continuity statements used when passing held solutions to a limiting parameter. The provider is `Breakdown.Cert.dataContinuityHolds_of`. The contract is `Breakdown.Cert.DataContinuityHolds`.

For an invariant right side, almost every time slice of its free inverse satisfies the frozen quadratic-form lower bound. The controlled expression contains the second-derivative square, one quarter of the gradient square and the projected convection pairing; the lower bound is the negative form coefficient times the weighted slice energy. The provider is `Breakdown.Cert.frozenBridgeHolds_of`. The contract is `Breakdown.Cert.FrozenBridgeHolds`.

The held set is closed, and its held distance dominates a positive multiple of the ambient norm and satisfies the triangle inequality. A limit of points obeying a common distance bound still obeys that bound. These are the specific metric facts supplied to the contraction argument. The provider is `Breakdown.Cert.heldMetricHolds_of`. The contract is `Breakdown.Cert.HeldMetricHolds`.

For each certificate parameter, the held step maps the held set into itself and decreases its held distance by a factor strictly below one. The fixed-point assembly combines these two facts with the metric and bordered-inverse interfaces to produce a unique held solution, including uniqueness of both its Hilbert component and its finite multiplier correction. The providers are `Breakdown.Cert.heldMapsToHolds_of`, `Breakdown.Cert.heldContractsHolds_of`, `Breakdown.Cert.heldExistsUniqueHolds_of`. The contracts are `Breakdown.Cert.HeldMapsToHolds`, `Breakdown.Cert.HeldContractsHolds`, `Breakdown.Cert.HeldExistsUniqueHolds`.

Along parameters in the box converging to another box point, a sequence of held solutions has a strictly increasing subsequence whose finite multiplier corrections converge to those of a held solution at the limiting parameter. The statement records this subsequential multiplier convergence; it does not assert convergence of the original sequence of Hilbert components. The provider is `Breakdown.Cert.heldLimitHolds_of`. The contract is `Breakdown.Cert.HeldLimitHolds`.

Uniqueness and the held-limit theorem make the corrected multiplier continuous on the box. The zero-held theorem then supplies a parameter and held solution for which the original multiplier plus the correction is zero. The providers are `Breakdown.Cert.multiplierContinuityHolds_of`, `Breakdown.Cert.existsZeroHeldHolds_of`. The contracts are `Breakdown.Cert.MultiplierContinuityHolds`, `Breakdown.Cert.ExistsZeroHeldHolds`.

A held solution read as a physical perturbation cannot cancel the background profile almost everywhere. When its corrected multiplier is zero, the held weak-equation theorem supplies an integrable similarity-equation test integrand with zero integral; the profile assembly combines these conclusions with the slice reading to obtain a sigma profile. The providers are `Breakdown.Cert.heldNonzeroHolds_of`, `Breakdown.Cert.heldWeakEquationHolds_of`, `Breakdown.Cert.sigmaProfileOfHeldHolds_of`. The contracts are `Breakdown.Cert.HeldNonzeroHolds`, `Breakdown.Cert.HeldWeakEquationHolds`, `Breakdown.Cert.SigmaProfileOfHeldHolds`.

For invariant perturbations, convection and the quadratic product lie in the invariant Hilbert subspace. Every actuator combination and the certificate defect lie there as well, keeping the held equation inside the symmetry class. The provider is `Breakdown.Cert.invarianceHolds_of`. The contract is `Breakdown.Cert.InvarianceHolds`.

When the second argument has finite supremum gradient size, pairing the Hilbert quadratic product with a test field equals the integral of its physical product field against that test. This identity connects the fixed-point nonlinearity to the tested equation. The provider is `Breakdown.Cert.productPairingHolds_of`. The contract is `Breakdown.Cert.ProductPairingHolds`.

Translating the physical velocity by a spatial vector changes its local period norm by at most the vector norm times the Hilbert gradient norm. The same statement for every gradient column uses the second-derivative norm. These bounds give the spatial translation control required for local compactness. The provider is `Breakdown.Cert.spaceModulusHolds_of`. The contract is `Breakdown.Cert.SpaceModulusHolds`.

On a bounded positive range of periods, one common rate tends to zero with the time increment and bounds the local period-norm changes of velocity and every gradient column of a free inverse, multiplied by the right-side norm. The rate is uniform over those periods and right sides. The provider is `Breakdown.Cert.timeModulusHolds_of`. The contract is `Breakdown.Cert.TimeModulusHolds`.

A measurable periodic sequence with a uniform local square bound and common vanishing moduli for spatial and time translations has a strictly increasing subsequence that is Cauchy in the local period norm. The square bound is assumed on the larger ball of radius R plus one, while the conclusion and translation moduli use radius R. The provider is `Breakdown.Cert.translationCriterionHolds_proof`. The contract is `Breakdown.Cert.TranslationCriterionHolds`.

The free inverse of an invariant right side has finite supremum gradient size. Its square is bounded by the weighted energy term with the period, twist and frozen-form coefficients, plus the bordered forcing and actuator size multiplied by the square root of that energy. The provider is `Breakdown.Cert.supBoundHolds_of`. The contract is `Breakdown.Cert.SupBoundHolds`.

### Fourier derivatives and smoothing

Spatial derivatives are first controlled in the Hilbert and Fourier descriptions, then recovered as derivatives of physical velocity and pressure. The distinctions between almost-everywhere representatives, weighted norm derivatives and pointwise smooth fields are retained below.

The Hilbert derivative relation is unique, includes the derivative of order zero, respects linear combinations, is unchanged by permuting coordinate derivatives, and composes by concatenating their coordinate lists. Its bounded-closedness theorem passes derivatives to a convergent sequence when the derivative norms have one common bound. The providers are `Breakdown.FarField.derivAlgebra_holds`, `Breakdown.FarField.derivClosed_holds`. The contracts are `Breakdown.FarField.DerivAlgebra`, `Breakdown.FarField.DerivClosed`.

A first coordinate derivative is equivalent to convergence of the corresponding translated difference quotients in the Hilbert norm. Together with translation covariance of the bilinear operator, this supplies the bilinear Leibniz rule, whose derivative is the sum of the two terms obtained by differentiating either argument. The providers are `Breakdown.FarField.diffQuotient_holds`, `Breakdown.FarField.shiftCovariance_holds`, `Breakdown.FarField.bilinLeibnizOfShift_holds`. The contracts are `Breakdown.FarField.DiffQuotient`, `Breakdown.FarField.ShiftCovariance`, `Breakdown.FarField.BilinLeibnizOfShift`.

The heat operator commutes with every recorded spatial derivative. For positive time, it also supplies derivatives of any prescribed order n with norm bounded by a constant times $t^{-n/2}$ times the input norm. The provider is `Breakdown.FarField.derivHeat_holds`. The contract is `Breakdown.FarField.DerivHeat`.

If two Hilbert-valued curves are interval integrable and are related by a fixed spatial derivative at every interior time, their interval integrals satisfy the same derivative relation. The endpoint inequality and both integrability assumptions are explicit. The provider is `Breakdown.FarField.derivIntegral_holds`. The contract is `Breakdown.FarField.DerivIntegral`.

Finite homogeneous Sobolev size of order n supplies all coordinate derivatives of that order. Conversely, a common norm bound for those derivatives bounds the homogeneous Sobolev square by a constant times the bound squared. The provider is `Breakdown.FarField.derivSobolev_holds`. The contract is `Breakdown.FarField.DerivSobolev`.

The weighted L1 integral of the velocity symbol with weight power k is bounded by a constant times the square root of the sum of the order-zero and order-(k+1) homogeneous Sobolev sizes. This is the Fourier integrability estimate used to recover differentiable physical fields. The provider is `Breakdown.FarField.homWiener_holds`. The contract is `Breakdown.FarField.HomWiener`.

A velocity symbol in the weighted L1 space of order j has its jth physical derivative uniformly bounded by a constant times that weighted L1 norm. The coefficient may depend on the derivative order, and the bound holds at every spatial point. The provider is `Breakdown.FarField.physFieldDerivBound_holds`. The contract is `Breakdown.FarField.PhysFieldDerivBound`.

Rotations preserve all homogeneous Sobolev sizes and weighted L1 symbol norms, and rotate the recovered physical velocity in the expected way. Positive dilation gives the stated homogeneous-size power law, continuity when that size is finite, square-root spatial scaling of smooth velocity and linear scaling of smooth pressure. The providers are `Breakdown.FarField.rotateSymbol_holds`, `Breakdown.FarField.dilateSymbol_holds`. The contracts are `Breakdown.FarField.RotateSymbol`, `Breakdown.FarField.DilateSymbol`.

The bilinear-symbol identity and weighted Fourier integrability imply the almost-everywhere Fourier Duhamel formula for a mild curve with the required Sobolev regularity. The physical Duhamel provider gives the corresponding almost-everywhere velocity identity between any two ordered times for a smooth orbit field representing the orbit. The providers are `Breakdown.FarField.duhamelSymbolOfBilinSymbol_holds`, `Breakdown.FarField.duhamelVelocityAE_holds`. The contracts are `Breakdown.FarField.DuhamelSymbolOfBilinSymbol`, `Breakdown.FarField.DuhamelVelocityAE`.

For an interval-integrable L6-valued curve and a jointly measurable pointwise representative agreeing almost everywhere at each interior time, the L6 integral agrees almost everywhere with the pointwise time integral. This is the representative-level passage used by the physical Duhamel formula. The provider is `Breakdown.FarField.intervalIntegralL6_holds`. The contract is `Breakdown.FarField.IntervalIntegralL6`.

Physical-time orbit windows, mild smoothing and the dilation identities give homogeneous Sobolev continuity of the orbit at every order. With weighted Fourier integrability, rotation covariance and physical derivative estimates, this gives a uniform bound through order three for the recovered orbit field. The providers are `Breakdown.FarField.orbitHomSobolevOfWindows_holds`, `Breakdown.FarField.orbitDerivBoundOfSymbolCurve_holds`. The contracts are `Breakdown.FarField.OrbitHomSobolevOfWindows`, `Breakdown.FarField.OrbitDerivBoundOfSymbolCurve`.

For a mild curve with homogeneous Sobolev continuity at every order, the Fourier Duhamel identity and weighted Fourier integrability give the prescribed time derivative of its velocity symbol in every weighted L1 space. For a smooth Hilbert vector, the same integrability interface identifies its velocity almost everywhere with the recovered physical symbol and makes its pressure gradient square integrable. The providers are `Breakdown.FarField.symbolCurveOfDuhamel_holds`, `Breakdown.FarField.velocityOfSymbolOfWiener_holds`, `Breakdown.FarField.pressureGradL2OfWiener_holds`. The contracts are `Breakdown.FarField.SymbolCurveOfDuhamel`, `Breakdown.FarField.VelocityOfSymbolOfWiener`, `Breakdown.FarField.PressureGradL2OfWiener`.

A solenoidal symbol curve with all weighted L1 moments and the stated time derivative in each weighted space reconstructs smooth velocity and pressure on the closed time slab. On interior times the velocity satisfies the Navier–Stokes evolution equation, and its divergence vanishes throughout the slab. The provider is `Breakdown.FarField.wienerSolution_holds`. The contract is `Breakdown.FarField.WienerSolution`.

### Kernel decay and pressure

The physical decay argument uses explicit kernel powers, parabolic scaling and near/far Newton estimates. Conditions on exponents and derivative orders are part of the statements, including the excluded borderline exponents.

At positive time, the heat kernel has the explicit Gaussian first derivative, and differentiation of the displayed second-derivative expression gives the named third derivative. The accompanying bounds control the kernel, first derivative and third derivative by powers three, four and six of the spatial norm plus the square root of time. The providers are `Breakdown.FarField.heatKernelPartials_holds`, `Breakdown.FarField.heatKernelBounds_holds`. The contracts are `Breakdown.FarField.HeatKernelPartials`, `Breakdown.FarField.HeatKernelBounds`.

Under positive parabolic scaling, the heat kernel scales by the inverse three-halves power and the Leray kernel by the inverse square power of the scale. The Leray kernel is odd in its spatial argument, which records the cancellation used by the convolution estimates. The providers are `Breakdown.FarField.kernelScaling_holds`, `Breakdown.FarField.lerayKernelOdd_holds`. The contracts are `Breakdown.FarField.KernelScaling`, `Breakdown.FarField.LerayKernelOdd`.

For positive time, the translated radial majorant $(|y-z|+\sqrt{\tau})^{-4}$ is integrable and its spatial integral is at most $5/\sqrt{\tau}$. The bound is independent of the translation y. The provider is `Breakdown.FarField.kernelMassBound_holds`. The contract is `Breakdown.FarField.KernelMassBound`.

For every natural derivative order n, the function $(1+\tau)^{-(1+n/2)}\tau^{-1/2}$ is integrable over positive time. This handles the integrable singularity near zero together with decay at infinity in the profile operator. The provider is `Breakdown.FarField.smallTimeIntegrable_holds`. The contract is `Breakdown.FarField.SmallTimeIntegrable`.

For a jointly continuously differentiable tensor field with uniformly bounded value and spatial derivative, differentiating the profile operator in a direction gives the same operator on the directional tensor with its exponent increased by one half. The conclusion retains the lower bound of one on the starting exponent and the Leray-kernel bound hypothesis. The provider is `Breakdown.FarField.profileOpDeriv_holds`. The contract is `Breakdown.FarField.ProfileOpDeriv`.

For derivative order at most two and a nonnegative decay exponent, the near and far time majorants are integrable and bounded by a constant times the radius to the negative minimum of the decay exponent and one plus the derivative order. The far estimate excludes equality of those two exponents; the near estimate has no such exclusion. The providers are `Breakdown.FarField.outerNearBound_holds`, `Breakdown.FarField.outerFarBound_holds`. The contracts are `Breakdown.FarField.OuterNearBound`, `Breakdown.FarField.OuterFarBound`.

For a nonnegative weight exponent different from three, the radial weight integral over a ball is bounded by a constant times the ball volume scale and the minimum of one and the scale-to-radius ratio raised to the smaller of the exponent and three. Both the scale and radius are required to be positive. The provider is `Breakdown.FarField.radialWeightBound_holds`. The contract is `Breakdown.FarField.RadialWeightBound`.

The tensor product of two weighted fields has decay exponent equal to the sum of their exponents and bound equal to the product of their bounds. When a smooth velocity and its first two derivatives decay with powers one, two and three, its self-tensor has derivatives through order two decaying with powers two plus the derivative order. The providers are `Breakdown.FarField.tensorWeight_holds`, `Breakdown.FarField.tensorDerivDecay_holds`. The contracts are `Breakdown.FarField.TensorWeight`, `Breakdown.FarField.TensorDerivDecay`.

For a smooth orbit field, the pressure source equals the double divergence of the velocity self-tensor, and the pressure Laplacian is the negative of that source. A weighted first-derivative bound of order two gives a smooth pressure source decaying with power four. The providers are `Breakdown.FarField.pressureSourceDivDiv_holds`, `Breakdown.FarField.pressureLaplacian_holds`, `Breakdown.FarField.pressureSourceBound_holds`. The contracts are `Breakdown.FarField.PressureSourceDivDiv`, `Breakdown.FarField.PressureSumSecondPartials`, `Breakdown.FarField.PressureSourceBound`.

A continuous scalar source decaying with power four gives an integrable near-cutoff Newton gradient term with cubic decay. For a twice differentiable tensor with the specified derivative decay, the far term can be integrated by parts twice onto the far weight; the resulting tensor integral has the same cubic decay bound. The providers are `Breakdown.FarField.newtonNear_holds`, `Breakdown.FarField.newtonFarIdentity_holds`, `Breakdown.FarField.newtonFarEstimate_holds`. The contracts are `Breakdown.FarField.NewtonNear`, `Breakdown.FarField.NewtonFarIdentity`, `Breakdown.FarField.NewtonFarEstimate`.

For a smooth scalar source with fourth-power decay, the gradients of its cut-off Newton potentials have a common quadratic decay bound once the cutoff radius is at least one. Each gradient component converges, as that radius tends to infinity, to the corresponding full Newton-gradient component. The provider is `Breakdown.FarField.truncatedNewton_holds`. The contract is `Breakdown.FarField.TruncatedNewton`.

A smooth function harmonic on a positive-radius ball equals its convolution with the specified mollifier at the center for every smaller positive mollifier radius. This identifies the locally harmonic remainder without changing its value at the center. The provider is `Breakdown.FarField.harmonicMeanValue_holds`. The contract is `Breakdown.FarField.HarmonicMeanValue`.

Weighted bounds of orders one, two and three on velocity and its first two derivatives, together with cubic coordinate bounds on the pressure gradient, supply one constant for the stated physical decay class. The provider is `Breakdown.FarField.classFormOfWeights_holds`. The contract is `Breakdown.FarField.ClassFormOfWeights`.
<!-- /passage:sec-analytic-implementations-behind-the-endpoint-assemblies -->

## Analytic foundations of the profile and cell reduction

<!-- passage:sec-analytic-foundations-of-the-profile-and-cell-reduction -->

The cylindrical estimates live in shared FracCell files that are reached by the classical endpoint route. Their inclusion here does not add the separate fractional Comparator configurations to the fifteen requested roots.

### Adjoint remainders and energy

`Breakdown.AdjointDefect.CentreResidualFieldHolds` says that transporting a valid adjoint field by a valid flow piece, with valid pin data, produces a residual field with the specified pin flux and the same decay exponent γ, for some constant C″. `Breakdown.AdjointDefect.centreResidualField_proof` proves the existence of that residual bound.

`Breakdown.AdjointDefect.RemainderAzimuthalHolds` turns AzimuthalBounded R ρ into RemainderDualBound R ρ. `Breakdown.AdjointDefect.AzimuthalParts.remainderAzimuthalHolds_of` supplies this implication from the weak mode inverse-square estimate, mode pairing and time-mode summation contracts; the numerical bound ρ is preserved.

`Breakdown.AdjointDefect.AzimuthalParts.WeakClassApproxHolds` supplies smooth compactly supported approximants to a measurable field V with measurable weak gradient D, finite sixth-power velocity integral and finite squared-gradient integral. Their gradients converge to D globally in squared integral, while the fields converge to V in squared integral on every ball. `Breakdown.AdjointDefect.AzimuthalParts.weakClassApprox` proves the approximation statement.

`Breakdown.CertReduction.SliceEnergySupHolds` bounds ‖v(σ,y)‖² almost everywhere by supBoundFactor(w₀)² times the sum of the squared second-derivative-trace integral and w₀ times the squared-gradient integral. It assumes w₀ > 0 and IsPerturbation. `Breakdown.CertReduction.sliceEnergySup_of` derives this contract from SliceSupNormHolds and PerturbationSliceHolds.

`Breakdown.CertReduction.ProfileEnergySupHolds` gives the corresponding almost-everywhere pointwise bound for a valid stationary profile, using supBoundFactor(w₀)² times its stationary energy with constant weight w₀ > 0. `Breakdown.CertReduction.profileEnergySup_of` derives the result from SliceSupNormHolds.

`Breakdown.CertReduction.PeriodGradientEnergyHolds` bounds w₀ times the real value of the period-integrated squared gradient by weightedEnergy, provided w₀ > 0 and the combined second-derivative and gradient energy is finite. `Breakdown.CertReduction.periodGradientEnergy` proves the inequality while retaining the finiteness premise needed for the extended-real to real conversion.

### From encoded fields to analytic fields

`Breakdown.CellReduction.Instantiation.SecondDerivAgreeHolds` states that valid shape parameters and time-field data make the first derivative differentiable almost everywhere in space at each time, and identify the adjoint second derivative with shapeHess there. `Breakdown.CellReduction.Instantiation.secondDerivAgree_from_keys` proves these two claims from the encoded keys; no pointwise identity at every spline knot is asserted.

`Breakdown.CellReduction.Instantiation.AffineFieldInvariantHolds` gives the exact space-time symmetry identity for affineField when the certificate symmetries are generated by the prescribed class symmetries, the azimuthal orders agree and all shape, origin-profile and time-field data are valid. `Breakdown.CellReduction.Instantiation.affineFieldInvariant_holds` proves the identity for every certificate symmetry, time, point and coefficient vector.

`Breakdown.CellReduction.Instantiation.AffineFieldStructureHolds` asserts time periodicity and zero classical divergence of affineField, together with joint almost-everywhere strong measurability and time periodicity of affineSecondDeriv. It assumes valid shape parameters, origin profiles and centre and tangent time-field data. `Breakdown.CellReduction.Instantiation.affineFieldStructure_holds` proves this package of structural properties.

`Breakdown.CellReduction.Instantiation.AffineFieldWeakSecondDerivHolds` identifies each directional first derivative of the valid affine field as having the corresponding flipped affineSecondDeriv component as its weak gradient. `Breakdown.CellReduction.Instantiation.affineFieldWeakSecondDeriv_holds` proves the statement at every time and for every coordinate direction.

`Breakdown.CellReduction.Instantiation.FieldDecayOrderHolds` converts a lower bound e on every active key’s highOrder into uniform decay of the shape field and its time derivative of order e, its first spatial derivative of order e+1 and shapeHess of order e+2. The data must satisfy IsShapeParams and IsTimeFieldData. `Breakdown.CellReduction.Instantiation.fieldDecayOrder_holds` proves that one constant can bound all four quantities.

`Breakdown.CellReduction.Instantiation.MovedFieldUniformDecayHolds` provides one decay constant for every coefficient vector with |qᵢ| ≤ M: the moved affine field decays like (1+‖y‖)⁻¹, its first derivative like (1+‖y‖)⁻² and its encoded second derivative like (1+‖y‖)⁻³. It retains the validity of the radial phase, shape parameters and all profile and time-field data. `Breakdown.CellReduction.Instantiation.movedFieldUniformDecay_holds` proves this uniform statement.

`Breakdown.CellReduction.Instantiation.MovedParamsValidHolds` says that movedParams preserves IsShapeParams for any real shift amplitude when the original parameters and the radial phase are valid. `Breakdown.CellReduction.Instantiation.movedParamsValid_holds` proves the preservation claim.

`Breakdown.CellReduction.Instantiation.MovedFieldJointSmoothHolds` asserts joint C1 regularity in the coefficient vector, time and space of the affine field whose shape parameters use the coefficient-dependent radial phase rate. It assumes the indicated shape, phase, origin-profile and time-field validity conditions. `Breakdown.CellReduction.Instantiation.movedFieldJointSmooth_holds` proves exactly C1 regularity in this contract.

`Breakdown.CellReduction.Instantiation.OffsetBallIdentityHolds` expands the defect-adjoint pairing on the matching ball into a constant term, a linear sum and a quadratic upper-triangular sum in q, for parameters in the certificate set and adjoints in its selected set. Valid given-shape data, bounded instantiation and a valid offset expansion remain premises. `Breakdown.CellReduction.Instantiation.offsetBallIdentity_of` derives the identity from ball agreement, the phase-step identity and pressure regularity.

`Breakdown.CellReduction.Instantiation.ParamsBoundedHolds` states that nonzero certificate scales give a common bound M on every coordinate of every q in the certificate parameter set. `Breakdown.CellReduction.Instantiation.paramsBounded_holds` proves this boundedness statement; the nonzero-scale premise is explicit.

`Breakdown.CellReduction.Instantiation.PinValueContinuousHolds` makes the pin value continuous on a parameter set when the underlying field is jointly C1, its gradient has uniform inverse-square decay there, and the measurable pin field has finite squared period integral. `Breakdown.CellReduction.Instantiation.pinValueContinuous_holds` proves the continuity with precisely those analytic hypotheses.

`Breakdown.CellReduction.Instantiation.PressureFieldRegularHolds` gives joint continuity and unit time periodicity of shapePressure, and a spatial Lipschitz constant on each closed ball that is uniform in time. It assumes valid shape parameters and pressure-field data. `Breakdown.CellReduction.Instantiation.pressureFieldRegular_holds` proves these properties without asserting a globally smooth pressure.

`Breakdown.CellReduction.Instantiation.ProfilePiecesFlowHolds` puts the profile centre and every tangent into IsFlowPiece with a common bound for all coefficient vectors in a prescribed coordinate box, assuming a valid profile-shape entry. `Breakdown.CellReduction.Instantiation.profilePiecesFlow_of` derives the contract from StepPhaseHolds and MovedFieldUniformDecayHolds.

`Breakdown.CellReduction.Instantiation.ProfileSplitHolds` states the exact identity profile(q) = profileCentreAt(q) + Σᵢqᵢ profileTangentAt(q,i), at every time and point, for a valid profile-shape entry. `Breakdown.CellReduction.Instantiation.profileSplit_holds` proves the identity; the centre and tangent pieces themselves can depend on q through the moving parameters.

`Breakdown.CellReduction.Instantiation.ScalarGradientOrthogonalHolds` gives joint almost-everywhere strong measurability of the spatial gradient of a jointly continuous scalar pressure that is locally Lipschitz in space, and makes its integral pairing with every IsSpaceTimeTestField vanish. `Breakdown.CellReduction.Instantiation.scalarGradientOrthogonal_holds` proves both conclusions with the spatial Lipschitz condition allowed to depend on time and ball.

`Breakdown.CellReduction.Instantiation.ClassicalDivergenceWeakHolds` converts a C1 vector field with zero classical divergence into the weak identity ∫Dφ(y)[v(y)] = 0 for every scalar IsTestFunction. `Breakdown.CellReduction.Instantiation.classicalDivergenceWeak_holds` proves this bridge from the pointwise equation to test-function integration.

### Pairing estimates and period integration

`Breakdown.CertReduction.OperatorSquareBoundHolds` bounds the squared operator norm of a real spatial linear map by matSq of that map. `Breakdown.CertReduction.operatorSquareBound` proves this finite-dimensional comparison, allowing the entrywise squared energy to control operator estimates.

`Breakdown.CertReduction.StrainOfSymmetricPartHolds` turns an operator-norm bound S on (A+A*)/2 into the lower quadratic estimate -S‖u‖² ≤ ⟨Au,u⟩ for every u. `Breakdown.CertReduction.strainOfSymmetricPart` proves the estimate from the symmetric part of the map.

`Breakdown.CertReduction.PeriodSumBoundHolds` bounds the period integral of F² by (Σcₐ)²E when nonnegative F is bounded by a finite sum of measurable nonnegative fₐ and each fₐ has squared period integral at most cₐ²E. It assumes E and all cₐ are nonnegative. `Breakdown.CertReduction.periodSumBound` proves this finite-sum estimate in extended-real integrals.

`Breakdown.CertReduction.PeriodPairingBoundHolds` bounds the absolute period pairing of two vector fields by B when B ≥ 0 and the period integral of their norm product is at most B. `Breakdown.CertReduction.periodPairingBound` proves this passage from a nonnegative integral estimate to the signed pairing.

`Breakdown.CertReduction.StationaryPairingBoundHolds` bounds the absolute spatial inner-product integral by a nonnegative B when the lower integral of the norm product is at most B. `Breakdown.CertReduction.stationaryPairingBound` proves this stationary counterpart of the period pairing estimate.

`Breakdown.CertReduction.SliceIntegrateHolds` integrates an inequality that holds for almost every time between spatial lower integrals, preserving its nonnegative constant c in the period-integral bound. `Breakdown.CertReduction.sliceIntegrate` proves this step from slice estimates to a full-period estimate.

### Potentials and weak divergence

`Breakdown.PotentialShape.CellPotentialRegular` gives joint almost-everywhere strong measurability of a valid cylindrical field and its derivative, the weak-gradient identity at every time, finite squared-gradient period integral, and vanishing when ‖y‖ ≥ 2Rsupp. `Breakdown.PotentialShape.cellPotentialRegular_holds` proves the package for every mode number m under IsCylModeData.

`Breakdown.PotentialShape.CompactFieldSecondRegular` gives weak gradients for all coordinate first derivatives of a valid compact time field, almost-everywhere differentiability of its first derivative and a uniform almost-everywhere bound on its second derivative. `Breakdown.PotentialShape.compactFieldSecondRegular_holds` proves these conclusions from valid shape parameters and IsCompactTimeFieldData.

`Breakdown.PotentialShape.RadialFluxPartWeak` states that each active potential-series key and component, multiplied by the radial direction vector, has HasWeakPointDivergence at every time. It assumes valid shape parameters and potential-series data. `Breakdown.PotentialShape.radialFluxPartWeak_holds` proves the radial flux assertion.

`Breakdown.PotentialShape.PolarFluxPartWeak` supplies the corresponding HasWeakPointDivergence statement for each active potential-series component multiplied by polarVecQ. `Breakdown.PotentialShape.polarFluxPartWeak_holds` proves this polar flux assertion under the same shape and series validity predicates.

`Breakdown.CertReduction.SmoothShiftPiecesHolds` differentiates an exact finite splitting of profile minus model when every piece is jointly C1 and each recorded pieceGrad is its actual spatial derivative. It concludes the gradient splitting and strong measurability of all pieces and gradients on certificate parameters, under BridgeStanding. `Breakdown.CertReduction.smoothShiftPiecesHolds` proves this implication.

### Cylindrical modes and inverse-square bounds

`Breakdown.CellCert.Spectral.CylStatement` rewrites the integral of an integrable real spatial function as the half-plane integral of r times its angular integral over -π to π. `Breakdown.CellCert.Spectral.cylIntegral` proves the cylindrical change of variables on r > 0, retaining the radial Jacobian.

`Breakdown.FracInternal.FrameInverseSquareHalfPlane.AxisHalfPlaneBoundStatement` bounds s² times the inverse-distance-square integral of a C1 compactly supported complex mode by its radial and vertical derivative energy plus k²/r² angular energy, all with measure weight 2πr. Here s = |k|+1/2, or s = |k|+3/2 when the mode is odd in the vertical coordinate; nonzero modes must vanish on the axis. `Breakdown.FracInternal.FrameInverseSquareHalfPlane.axisHalfPlaneBound_of` derives this contract from the radial inverse-square and angular cosine-weighted bounds.

`Breakdown.FracInternal.FrameInverseSquareHalfPlane.RadialInverseSquareStatement` states that the integral of |f|² on the positive half-line is at most four times the integral of r²|f′|² for a C1 compactly supported complex function. `Breakdown.FracInternal.FrameInverseSquareHalfPlane.radialInverseSquare` proves this estimate.

`Breakdown.FracInternal.FrameInverseSquareHalfPlane.AngularCosBoundStatement` gives a cosine-weighted angular energy bound on (-π/2,π/2), with coefficient m(m+1), or the improved coefficient (m+1)(m+2) when the function vanishes at zero. Positive m requires vanishing at both endpoints, and the function is C1. `Breakdown.FracInternal.FrameInverseSquareHalfPlane.angularCosBound_of` proves this contract using AngularOddBoundStatement.

`Breakdown.FracInternal.FrameInverseSquareHalfPlane.AngularOddBoundStatement` states the cosine-weighted angular estimate with coefficient (m+1)(m+2) when the C1 function vanishes at zero, with endpoint vanishing required for m > 0. `Breakdown.FracInternal.FrameInverseSquareHalfPlane.angularOdd` proves this result. Despite the source name, the displayed contract assumes the zero value at the centre directly, rather than a full oddness hypothesis.

`Breakdown.FracInternal.FrameInverseSquareParts.FrameModeCalculusStatement` gives C1 regularity and compact support of the horizontal and vertical angular modes of a smooth compactly supported vector field. At positive radius it identifies the gradient-mode energy with the radial and vertical derivative energies plus the k²/r² terms of those two modes. `Breakdown.FracInternal.FrameInverseSquareParts.frameModeCalculus'` proves these identities.

`Breakdown.FracInternal.FrameInverseSquareParts.ModeGradientLimitStatement` makes modeGradientSide converge for each mode when measurable gradient fields converge in the global squared entry norm and the limiting entry norm is integrable. `Breakdown.FracInternal.FrameInverseSquareParts.modeGradientLimit` proves this continuity statement for the mode energy.

`Breakdown.FracInternal.FrameInverseSquareParts.ModeWeightedLowerStatement` bounds the weighted mode quantity of a measurable limiting field by the liminf of the quantities for continuous approximants, provided they converge in squared integral on every ball. `Breakdown.FracInternal.FrameInverseSquareParts.modeWeightedLower` proves this lower-semicontinuity statement for each integer mode.

`Breakdown.CellCert.Reduction.ModeMeasurableStatement` transfers almost-everywhere strong measurability of a complex spatial field to each of its angular-mode functions on the positive-radius half-plane. `Breakdown.CellCert.Reduction.modeMeasurable` proves the statement with the half-plane restricted volume measure.

### Fourier realization

`Breakdown.Freq.EmbedMem` states that ofGrad f belongs to the Fourier constraint space Sig whenever f satisfies IsDecayField. `Breakdown.Freq.embedMem_holds` proves this membership, which is needed before the physical decay field can be packaged as a Fourier-space element.

### Profile scaling and physical equations

`Breakdown.ExpChangeOfVariables` states the Banach-valued substitution from r = 1 - exp(-(σ-s₀)) to similarity time: an integrable g on the physical interval gives an integrable transformed function, and the two interval integrals agree after multiplying by the exponential Jacobian. The endpoints satisfy s₀ < s. `Breakdown.expChangeOfVariables_holds` proves this proposition.

`Breakdown.DecayFieldSub` asserts that the difference of two fields satisfying IsDecayField again satisfies IsDecayField. `Breakdown.decayFieldSub_holds` proves this closure property, which allows the decay hypotheses to survive subtraction of profile slices.

`Breakdown.DilateCalculus` records the derivative rules for a smooth dilateField: the first derivative gains sqrt(μ)², while the second-partial trace and advection gain sqrt(μ)³, evaluated at sqrt(μ) times the point. `Breakdown.dilateCalculus_holds` proves these three identities. The proposition itself quantifies over every real μ and uses Lean’s real square root.

`Breakdown.GradientScale` states that the gradient of the smooth scalar function y ↦ g(cy) is c times the gradient of g at cy. `Breakdown.gradientScale_holds` proves the identity for every real c.

`Breakdown.DilateJointContinuous` asks for joint continuity of the framework dilation D(μ)x on positive μ and arbitrary x in the complete real Hilbert space. `Breakdown.dilateJointContinuous_holds` obtains this property from the MildFramework assumptions.

`Breakdown.KernelDilate` gives a two-scale identity for the diagonal bilinear kernel when a, b and τ are positive: D(a) applied to K(bτ) on two copies of D(b⁻¹)x equals b⁻¹ times D(ab⁻¹) applied to K(τ)(x,x). `Breakdown.kernelDilate_holds` proves the identity within every MildFramework.

`Breakdown.EmbeddedOrbitOfParts` is an implication from decay under subtraction, slice decay, slice-gradient continuity, the physical mild equation and the mild-to-flow bridge to EmbeddedProfileOrbit. `Breakdown.embeddedOrbitOfParts_holds` proves this implication. Each of its five analytic inputs remains a premise of the contract being assembled.

`Breakdown.PhysicalPairingDeriv` identifies the time derivative of the physical velocity paired with a test field at t < 1 as the integral of the second-partial trace minus advection minus the pressure gradient against that field. The velocity and pressure come from an IsSimilarityProfile. `Breakdown.physicalPairingDeriv_holds` supplies this conclusion from PhysicalTimeDeriv, PhysicalMomentum and SimilarityDerivBound.

`Breakdown.SumSecondPartialsPairing` states that pairing the second-partial trace of a smooth field with an IsTestField equals minus their gradient pairing. `Breakdown.sumSecondPartialsPairing_holds` proves the integration-by-parts identity; the compact-support requirements are carried by the test-field predicate.

`Breakdown.SimilarityDerivBound` bounds the combination ∂sW + W/2 + (DW)y/2 by K/(1+‖y‖)³, uniformly in similarity time and position, for a valid similarity profile. `Breakdown.similarityDerivBound_holds` proves the existence of such a constant K.

### Transfer through one period

`Breakdown.MonodromyStatement` starts with a MildFramework commuting with ρ and an orbit satisfying F.IsOrbit ρ w P, including its recurrence w(s+P) = ρ(w(s)). For a positive step count it combines five assertions: all I-stepOp are invertible with inverse norm at most 4/3; the step maps obey rotation covariance; the full-period map differs compactly from its free part; and the free part has norm at most exp(-P/4). Its premise bounds every stepOp norm by 1/4. `Breakdown.monodromy_of` derives the contract from PieceOperatorStatement, CompactPieceStatement and ProfilePieceStatement.

`Breakdown.PeriodicInverseStatement` constructs a bounded linear solution operator for the weighted piece recurrence, with its initial component in the range of the unstable projection. Its assumptions include uniform step inverses, rotation covariance, a commuting idempotent projection, the strict gap r₁ < θᵏ < r₂, stable and unstable estimates, surjectivity on the unstable range and compatibility with J. `Breakdown.periodicInverse_of` derives this contract from DiscreteDichotomyStatement.

`Breakdown.ShiftStatement` states the equivalence between a variation-of-constants identity for u from a to t and the same identity for s ↦ u(s+c) from a-c to t-c. `Breakdown.shift` proves the equivalence for every HeatBilinear structure.

`Breakdown.StepDataStatement` assumes a MildFramework commuting with ρ and an orbit satisfying F.IsOrbit ρ w P, with recurrence w(s+P) = ρ(w(s)). It chooses a positive step count, a weight θ strictly between the free decay factor and one, a finite-dimensional initial subspace, a map J into a prescribed dense submodule, and a bounded solution operator for the piece recurrence. The steps fit any supplied positive time bound and their operator norms are at most 1/4. `Breakdown.stepData_of` assembles this contract from monodromy, profile pieces, orbit bounds, piece operators, the periodic inverse, the finite-section statement and DichotomyHolds.

### Weak slices and changes of time

`Breakdown.WeakProfile.ConstOfWeakDeriv` turns the identity ∫θ′a = ∫θb for every smooth compactly supported test function inside an interval into an almost-everywhere representation a(t) = c - ∫ₗᵗb. Both a and b must be integrable on that open interval. `Breakdown.WeakProfile.constOfWeakDeriv_holds` proves the existence of the constant c, preserving the minus sign dictated by the tested identity.

`Breakdown.WeakProfile.GradientFreqTr` asserts that a valid physical slice f with weak gradient g has some x in the Fourier Hilbert space whose partialX components equal the components of g almost everywhere. `Breakdown.WeakProfile.gradientFreqTr_holds` proves this existence statement. The displayed conclusion concerns the gradient components; identification of the recovered velocity with f is a separate bridge.

`Breakdown.WeakProfile.TimeChangeNull` states that a property holds for almost every similarity time exactly when it holds after σ = s₀ - log(1-t) for almost every physical time t < 1. `Breakdown.WeakProfile.timeChangeNull_holds` proves this equivalence with the physical-time measure restricted to that interval.

`Breakdown.WeakProfile.ScaledTestField` requires that scaledTest formed from a smooth compactly supported time function, a phase s₀ and an IsTestField is an IsSpaceTimeTestField. `Breakdown.WeakProfile.scaledTestField_holds` verifies this construction, allowing the weak physical equation to be tested after rescaling.

`Breakdown.WeakProfile.SliceIntegrand` equates the spatial integral of the weak-similarity integrand against a scaled test with similarityRate for the Fourier slice. It assumes IsSlice f g C, a smooth compactly supported time function α, an IsTestField φ, and almost-everywhere agreement of the physical velocity and all Fourier partials with the supplied slice and gradient. It also takes PairingVelocity and AdvectionByParts as inputs. `Breakdown.WeakProfile.sliceIntegrand_holds` proves this conditional identity.

`Breakdown.WeakProfile.SliceMeasurable` transfers joint almost-everywhere strong measurability of the physical field W to the Fourier-valued curve x when IsSliceCurve relates x, W and G. The transfer assumes PairingVelocity. `Breakdown.WeakProfile.sliceMeasurable_holds` proves this implication, supplying the measurability needed for later time integrals.
<!-- /passage:sec-analytic-foundations-of-the-profile-and-cell-reduction -->

## CertCell foundations: from weak fields to finite budgets

<!-- passage:sec-certcell-foundations-from-weak-fields-to-finite-budgets -->

<a id="1"></a>

### 1. From real fields to harmonic data

The admissible harmonic lattice is an arithmetic restriction on the entire perturbation. For azimuthal order $m\geq1$, the label map is injective, respects reflection and negation, and has image exactly the integer pairs $(\nu,k)$ with $m\mid k$ and $\nu+k/m$ even. Combining that arithmetic with the mode exclusion interface makes every off-lattice velocity, gradient, and second derivative coefficient vanish almost everywhere in space-time. The support conclusion therefore applies to the derivative data used by the cell calculus, as well as to the velocity.

Real tensor fields have conjugate coefficients at opposite harmonic labels. A separate transformation law describes what happens under a time shift $s$ and axial rotation $\phi$: each coefficient acquires the phase $e^{i(2\pi\nu s+k\phi)}$, while the gradient has two rotated indices and the second derivative has three. The conjugacy identity is stated for arbitrary real input fields. The shift and rotation identities require time periodicity and integrability of the relevant orbit functions; these hypotheses justify moving the transformations through the mode averages.

Rotation averaging preserves the spatial integral of any almost everywhere measurable nonnegative extended-valued function. The normalization is $1/(2\pi)$, with the angular integral over $[0,2\pi]$. The source uses preservation of volume by axial rotations and interchange of nonnegative integrals. Since the statement is an equality of extended integrals, it remains meaningful before finiteness has been established; it does not supply finiteness of an energy by itself.

Temporal cosine and sine components retain the local second order field structure. When the parity condition $n+\nu$ even holds, their spatial modes combine into the complex velocity, gradient, and second derivative profiles used by the cell machinery. These identities hold for almost every meridian point with positive radius. The pressure companion establishes the corresponding velocity-style profile identity for a periodic pressure field. It supplies the pressure component of the representation without asserting the full perturbation equations or replacing the periodic pressure assumption.

Integrability near the axis comes in two different forms. A local second order field gives ordinary integrability of its velocity and gradient modes on meridian strips that include radius zero. For a periodic perturbation, the axis interface gives integrability of radius times each velocity, gradient, and second derivative component. The radial factor matters: the latter statement alone does not remove the cylindrical weight from a Hessian component. The source proves these facts through bounded mode kernels and local integrability, with a cutoff argument for the unweighted gradient modes.

The second derivative energy identity equates the period integral of the squared Frobenius norm of the Hessian with that of the squared norm of its trace. The perturbation supplies weak first and second derivatives and finite gradient energy. The source first obtains the spatial identity for almost every time slice and then integrates those equalities over the period. This is an identity of nonnegative extended integrals, so any later claim that both sides are finite needs its own finiteness hypothesis.

The scalar mode interface transports a weak spatial gradient into a weak derivative in height. Under joint measurability, local period-integrated square bounds, periodicity, and the stated reflection hypothesis, the scalar plane mode has the advertised height derivative on every interval $(-h,h)$ for almost every positive radius. The source uses a countable dense collection of one-dimensional test functions to choose one exceptional radial null set. Consequently, the same good radii work for all positive heights, rather than a separately chosen set for each interval.

Compact support of the given shape is controlled by the compactified chart. Valid shape parameters, compact time-field data, and the edge-break condition force the assembled physical field to vanish whenever the spatial radius exceeds $\text{chartLength}\,t_b/(1-t_b)$. The proof shows that every finite key contribution is zero beyond that edge and then sums the contributions. The radius bound concerns this explicitly assembled field; it is not a general support theorem for arbitrary perturbations.

<a id="2"></a>

### 2. Traces without pointwise representatives

The upper and lower plane traces are integral functionals of a function and its weak height derivative. Reflection exchanges them, with the derivative changing sign. If the pair satisfies the weak derivative relation on a larger interval, the upper and lower traces agree, and the upper trace is independent of the positive height used in its integral formula. The source proves matching with smooth approximations to a tent test and dominated convergence; height independence is proved through a weak primitive representative. These results justify a common plane trace without assuming an arbitrary representative has a prescribed point value.

A side trace at a fixed coordinate is independent of the auxiliary coordinate used to define its averaging interval. Both auxiliary coordinates and the trace coordinate must lie strictly inside a common interval on which the weak derivative relation holds, and neither auxiliary coordinate may equal the trace coordinate. The source compares the resulting tent identities in all relative-order cases. This is the compatibility fact that permits adjacent constructions to use different strip widths while referring to the same weak trace.

Height strip moments can be evaluated as radial integrals of one-dimensional trace functionals. The general formula allows distinct height coordinates and continuous radial weights, assuming weighted integrability of both the field and its height derivative. The specialization with endpoints zero and a positive height identifies the cell formula's strip moment with the upper plane trace. The orientation signs and affine height weights are part of these identities; they are not discarded by interpreting the strip as an informal boundary integral.

Corner data are also integrated trace functionals. The reflection identity reverses the height coordinate, changes the signs of the vertical and mixed derivatives, and carries along any complex scalar factor. The matching theorem identifies the positive-height and negative-height corner moments under weak plane derivative assumptions on a larger rectangle. The trace formula then expresses a corner moment as a radial integral of upper traces of the field and radial derivative, with explicit orientation and affine radial weights. None of these declarations introduces point evaluation at an arbitrary corner representative.

At the reflection plane, velocity strip and corner data inherit the component sign of the reflected mode, while the vertical-gradient strip data gain an additional minus sign. Their integration heights may be different on the two sides. The velocity strip identity permits radial intervals reaching the axis; the gradient identity additionally requires an axis-admissible test, which supplies the needed radial factor when the interval starts at zero. The corner identity permits an auxiliary radial endpoint at zero while keeping the corner radius positive and the two radii distinct. These statements combine weak traces, mode reflection, and axis integrability under an actual reflection symmetry of the perturbation.

Harmonic side data agree exactly with the segment moment formulas used by the cell layout. Velocity data use the velocity profile together with its radial and height derivatives. Gradient data select the radial or height derivative according to the segment orientation and use the corresponding second derivative profiles. The harmonic layout, periodic field structure, pressure interface, and parity condition are explicit inputs. This correspondence is what lets finite side-data coordinates represent weak field moments without requiring pointwise boundary samples.

<a id="3"></a>

### 3. Turning plane traces into quantitative credit

A patch trace obeys a weighted energy estimate on an annular meridian rectangle away from the axis. The squared trace norm is bounded by the product of the reflected velocity energy weighted by a positive charge $b$ and a test-gradient energy weighted by $1/b$, both with cylindrical radial measure. The test is Lipschitz, vanishes on the two radial sides and top, and the charge has positive lower and finite upper bounds. Its gradient energy includes the azimuthal frequency term. Reflection and weak-height-trace interfaces supply the integration identity before the Cauchy-type bound is applied.

The inverse-Gram step converts all scalar testing inequalities into one vector credit. If a positive definite real matrix $G$ bounds $|c^*t|^2$ by $A\,c^*Gc$ for every complex coefficient vector, with $A\geq0$, then the inverse quadratic form of $t$ is at most $A$. Applied to finite combinations of patch tests, this turns the trace energy estimate into an inverse-Gram bound on their collected traces. The matrix is required to dominate the test-gradient energy for every complex combination, not merely for each test separately.

A valid credit patch packages those tests, their trace-data map, a positive definite test matrix, and a credit matrix dominated by its inverse form. The bridge proves that the credit quadratic form evaluated on the actual field data is bounded by the charge-weighted reflected velocity energy on the patch region. The proof first identifies the matrix trace-data vector with the analytical patch traces, then applies the inverse-Gram estimate. Validity of the supplied patch data and the perturbation's reflection symmetry remain hypotheses.

<a id="4"></a>

### 4. Shared keys and finite row compatibility

For a skeleton key whose spatial mode is zero, reversing the temporal frequency conjugates its field harmonic. At temporal frequency zero the same key harmonic has zero imaginary part. These statements apply to the key-layout functionals of the field, derivative, and pressure data. Their scope is deliberately restricted by the key-mode condition: they do not assert reality of arbitrary nonzero spatial-mode keys or impose a gauge condition on the field.

A nonprivate local datum can be transported to a shared skeleton key in two stages. First, harmonic trace independence and valid cell layouts identify the local head functional with the corresponding key harmonic. Second, an admissible key evaluation transfers that harmonic to its canonical label and mode, including the specified conjugation and reflection operations. The transfer requires a key in the designated half-plane, the stated key-mode or stream-key condition, and the plane-flip interface. These hypotheses prevent an arbitrary coordinate identification from being mistaken for an analytic equality.

Odd temporal stream keys vanish on the reflection plane at every nonnegative radial endpoint. The source combines cosine and sine strip moments, applies the reflected vertical-component sign, and obtains an equality with its own negative; the zero-length case is handled separately. The theorem assumes the plane-trace facts, the field hypotheses, and agreement between the key layout's order and the layer's azimuthal order. It is a specific stream-key identity on the plane, not a statement that the whole odd-frequency field vanishes.

The zero-spatial-mode velocity keys satisfy flux identities in terms of stream-key differences. On a radial side with positive level, the velocity moment is a scaled difference of endpoint stream values. On a height side, the zeroth velocity moment is reconstructed from the first moment and the endpoint stream difference, with a nonzero test coefficient required for division. The provider derives both identities for each real cosine or sine tuple using the local second order field obtained from harmonic lifting.

The normal-segment identity expresses a normal gradient moment using velocity moments and corner data. On radial segments it includes the reciprocal radius and the azimuthal coupling; on height segments the corner terms carry radial endpoint weights. The polynomial derivative of the chosen test must be representable in the supplied test basis, and the segment endpoints must match the declared corners. Harmonic lifting proves the real cosine and sine identities and then combines them into the complex data identity. This is the analytic content used by normal rows.

Row matching is proved by row kind with an explicit induction premise. A row may use already matched, nonunused rows of strictly smaller rank. Key rows use the local-to-shared identification and canonical evaluation; derived rows use the cell relations and the lower-rank data; normal rows use the normal-segment identity. The common row-kind contract concludes equality of the finite row value with the corresponding shifted field datum. Its rank condition makes the dependency direction visible and does not grant circular row identities.

Once every relevant row agrees with the actual periodic field data, the row identity transfers to the true state of an admissible tuple. The provider substitutes the chosen recovered pressure into the field-level statement, using its periodicity and reflection properties. The conclusion is equality for every row whose reason is not unused. Pressure recovery and chosen-pressure symmetry are therefore part of the bridge from field equations to matrix state coordinates, rather than consequences of an arbitrary row matrix.

<a id="5"></a>

### 5. Finiteness and allocation before inequalities

Weak admissibility is assembled from two explicit collections of clauses. The weight collection supplies positivity, regularity, decay, axisymmetry, and the auxiliary convolution and share conditions. The remaining collection supplies period and weight bounds, harmonic expansion and amplitude bounds, one-sided frame-frequency controls, global share bounds, and the comparison with the convolution allowance. The provider fills the corresponding weak-admissibility record field by field. It combines established obligations; it does not infer those bounds from the existence of numerical arrays.

The regularity of the true field used by assembly consists of cell-profile regularity and measurability of cell densities, stretching integrands, given modes, and exterior densities. The provider obtains this package from the field-regularity record, which already contains a valid mesh, a positive azimuthal order, a weak model state, harmonic and symmetry information, admissibility, measurable bound data, and actuator shape facts. This is the bridge that makes later integrals legitimate for the actual perturbation data.

The cell allocation identity is preceded by a precise finiteness result: the negative cell part and both positive and negative off-cell parts are finite for every admissible cell tuple. Its assumptions include finite negative form, coefficient lower bounds, the shared coercivity coefficient, valid cell calculus, and regular charges. The allocation split then rewrites the real-valued cell contribution minus its off-cell contribution as the sum of resolved energy, off-charge contribution, and stretching. The finiteness contract does not itself assert finiteness of the positive cell part, so that stronger assertion should not be read into the conversion to real-valued expressions.

The stretching contribution first becomes a quadratic harmonic pairing of the true velocity and gradient profiles. A second identity splits that pairing into the upper-profile self-term, three cross interactions with the resolved remainder, the band, and the deactivated modes, and the other-profile self-term. Each cross term has its factor of two. The expansion uses the mode-class and regularity data; the finer split also assumes the low-tail decomposition. This exact bookkeeping identifies which later bounds must pay for each interaction.

The leaf comparison bounds the true leaf pairing plus the box contribution, after subtracting the retained low-profile leaf pairing, by resolved energy minus the energy budget and tail credit. It is an inequality for every allowed choice of cell pins and ports. The provider needs finite cell pieces and valid cell calculus in addition to field regularity. This is where the finite leaf representation is compared with the field energy while retaining the unresolved contribution as an explicit budget.

Absorption loss has two exact decompositions. The other-profile absorption equals the absorption of the low-band state plus that of the actual tail profiles. The latter is a finite sum over resolved labels of curl, strain, and velocity tail squares multiplied by the corresponding leaf absorption coefficients. The first equality uses the low-tail split; the second uses the valid mesh and cell calculus. Together they identify the coefficients that must appear in the later tail budget, rather than merely bounding an unspecified remainder.

The sharp-bound regularity package justifies the infinite harmonic operations locally. It gives almost everywhere summability of the squared other-profile norms and of the charge and stretching terms; the summed charge and stretching terms are integrable. It identifies the integrals of those two sums with the named charge amount and true stretching pairing, and supplies integrability of the resolved leaf, box, and absorption cores. These conclusions are conditional on the regularity, potential, and low-tail interfaces and are localized to each cell rectangle.

<a id="6"></a>

### 6. Paying for the potential interactions

The long harmonic model estimate separates frequency bands on the time-angle torus. It assumes integrable matrix coefficients, operator bounds on the symmetric stretching matrix and the gradient matrix, and vanishing low Fourier coefficients of the model matrix through the specified cutoff. The conclusion bounds the resolved self-pairing plus twice the resolved-tail pairing from below by the negative of the summed quadratic charges. The charge weights distinguish the low band from its complement through the chosen positive splitting parameter. This is a finite harmonic matrix estimate with torus facts as inputs, not the entire cell coercivity statement.

The two tail estimates pay for different interactions. The resolved-tail cross estimate puts the negative port quadratic form minus the strain and velocity balance costs below twice the model and leaf cross pairings. The high-partner estimate bounds the high-frequency partner charge of the actual tails by explicit strain and velocity tail costs, including the radius bound and the positive Young parameters. The cross estimate uses the low-tail split; the high-partner estimate has its own structural hypotheses. Their separate conclusions explain why both kinds of tail charges remain visible in the potential budget.

The charge stage compares the available charge surplus with a specific sum of demands: band energy, row and pairing leakage, group and partner charges, band allowances, credits, and pairing slack on the band and designated deactivated labels. Its conclusion is that this entire sum is at most the surplus. The provider depends on the actual potential conditions and regular field data. It is the accounting inequality that allows many individually estimated interactions to draw on one charge allocation without dropping a cost.

Potential assembly combines the previously separated expansion, leaf, sharp, model, cross-tail, group, charge, high-tail, resolved-error, and split identities. The resulting inequality controls the retained potential quadratic form, the band quadratic and linear terms, leakage, allowances, credits, and slack, while subtracting the explicit resolved tail costs. Its right-hand side is resolved energy plus off-charge contribution plus stretching, minus the energy budget and tail credit. The assembly theorem is conditional on those component stages; its value is a correctly signed aggregate inequality, not a replacement for checking the component hypotheses.

The final tail stage uses a top-block estimate that bounds each velocity tail square by a finite quadratic form plus a strain tail square divided by the velocity-tail gain. Combined with the tail-absorption and gain interfaces, it bounds the negative top quadratic form by tail credit minus the total strain, velocity, and curl costs. Positivity and admissibility of the gains belong to the tail conditions. This is the precise point at which the remaining tail costs can be absorbed into the assembled cell inequality.

<a id="7"></a>

### 7. The forcing row budget

A conjugate-closed finite cell vector field is recovered from its harmonic labels in the rotating frame. For almost every meridian point in a valid cell rectangle, every time, angle, and component satisfies the finite Fourier reconstruction formula. The source derives the identity from the cylindrical representation and uses conjugacy to identify the real physical field with the complex reconstruction. The exceptional meridian null set remains in the statement, so the formula is not a claim of pointwise equality on every geometric seam.

The exact row decomposition starts with the actual forcing moment and subtracts the retained row vector and tail row. The remainder is the sum of frequency, model error, long interaction, deactivated-mode, and actuator pieces. The provider uses finite actuator harmonic support, cell-state membership, and the regularity and row-functional conditions. This identity identifies the quantities that must be estimated before a finite row norm can be charged to physical forcing and error allowances.

The frequency and long-interaction pieces are estimated in their designated inverse weighted row norms. The frequency norm is controlled by the frequency allowance. The long-interaction norm is controlled by the sum of long allowances over the resolved labels, band labels, and deactivated source labels. The scaling matrices and costs are those specified by the row conditions. Keeping the three long-interaction label sets explicit matters because they are assigned to different budget terms in the allowance split.

The deactivated row remainder is first written exactly as the sum of its group pieces. A separate estimate bounds the deactivation cost times the sum of the groups' inverse row-Gram norms by the deactivation allowance. The group identity uses the potential and row-functional conditions; the norm estimate uses the row and potential conditions governing the costs and groups. These are distinct steps: the identity organizes the unresolved modes, and the inequality pays for the organized sum.

The actuator contribution is bounded in the inverse norm associated with its scaled row Gram matrix. The right-hand side is the product of the actuator cost, the certified actuator error coefficient, and the sum of squares of the actuator coordinates. The provider requires the cell-state, field-regularity, row, and row-functional interfaces. Thus the coordinate error appears as an explicit quadratic cost, rather than being silently identified with an exact actuator expansion.

The allowance split directs the row errors to their available resources. Frequency, resolved model error, resolved long interaction, and resolved pairing slack fit inside the box amount. Band model error and band long interaction fit inside the band allowance. The corresponding deactivated-source terms, together with the deactivation allowance, fit inside row leakage. These three inequalities are the bridge from local error estimates to the specific budget terms that are available in the potential assembly.

Combining the exact row decomposition with the frequency, model-error, long-interaction, deactivation, actuator, and allowance bounds yields the row moment inequality. It controls the inverse leak-Gram norm of the forcing moment minus the retained and tail rows, together with resolved pairing slack, by leakage, box and band allowances, and the actuator-coordinate cost. The companion provider packages these component interfaces into a reusable row-moment statement. The model-error estimate is an explicit input alongside the providers discussed here; no missing estimate is supplied merely by naming the assembled statement.

The forcing share agrees with the inverse base-row-weight norm of the stacked forcing moments. Row removal then compares the retained-row norm with that norm of forcing moments, the resolved strain and velocity tail costs, and the inverse leak-Gram norm of the remaining row mismatch. This is the quantitative step that permits retained coefficients to be removed from the final right-hand side. It preserves the mismatch term until the row moment estimate has paid for it.

The row stage combines stacked forcing-share equality, row removal, and the row moment inequality. Its conclusion bounds the retained-row norm plus resolved pairing slack by the actual forcing share, resolved strain and velocity tail costs, row leakage, the box and band allowances, and the actuator-coordinate cost. The provider assumes the row values, row conditions, field regularity, and band-profile integrability needed to use those pieces. It gives the forcing contribution in the form required by the cell assembly while keeping every remaining tail and error charge explicit.

### Reading the scope of this completion
<!-- /passage:sec-certcell-foundations-from-weak-fields-to-finite-budgets -->

## Closing the reading gaps

<!-- passage:sec-closing-the-reading-gaps -->

### Six scoped counterparts recovered from the library

For paper item (3.9): Lean defines the Leray-divergence kernel and supplies a proof of its power-four parabolic decay; the paper states bounds for every derivative order of the Oseen tensor. The scoped source counterparts are `Breakdown.FarField.lerayKernel`, `Breakdown.FarField.LerayKernelBound`, `Breakdown.FarField.lerayKernelBound_holds`.

For paper item (3.10): Lean supplies an almost-everywhere physical convolution formula for K(tau)(u,u), with a compact test-field version; the display also quantifies over arbitrary tensor divergences and distinct inputs u and v. The scoped source counterparts are `Breakdown.FarField.BilinTestKernel`, `Breakdown.FarField.BilinKernel`, `Breakdown.FarField.bilinKernel_of_test_decay`.

For paper item (3.19): Lean supplies the tau^(-3/4) L^(3/2) forcing bound for compactly supported L2 data transplanted to its inhomogeneous unit-torus space, with mu*tau <= 1; the paper allows every period and all positive times in the mean-zero homogeneous space. The scoped source counterparts are `Breakdown.Periodic.ShellTorus.Internal.sourceOp_threeHalves`, `Breakdown.Periodic.sourceOp`, `Breakdown.Periodic.trigHs`.

For paper item (7.45): Lean constructs a continuous periodic representative satisfying an integrated energy identity for freeInv in similarity time; the printed line is the physical-time identity obtained from a general Lions-Magenes argument. The scoped source counterparts are `Breakdown.Cert.Internal.FreeEnergyLocal.IsEnergyCurve`, `Breakdown.Cert.Internal.FreeEnergyLocal.exists_energyCurve`, `Breakdown.Cert.freeEnergyLocalHolds_of`.

For paper item (C.1): centreDefect encodes a continuum residual in derivative and pressure-adjusted advection form with extra period and actuator parameters; source proofs supply curl algebra, while the printed curl-cross PDE and the surrounding numerical computation are not one verified package. The scoped source counterparts are `Breakdown.CellReduction.Instantiation.centreDefect`, `Breakdown.CertCell.Assembly.Internal.RemainderAnnihilates.cross_identity`, `Breakdown.Coercive.Internal.TestDensityProof.negSsp_curl_curl`.

For paper item (C.2): Lean defines the two curl-cross linear coupling terms and proves their weak-testing bridge with explicit derivative, pressure and actuator data; these continuum results do not verify the matrix-free Newton or flexible-GMRES procedure described around the displayed operator. The scoped source counterparts are `Breakdown.CertCell.CellCalculus.couplingField`, `Breakdown.CertCell.CellCalculus.IsStrongRightSide`, `Breakdown.CertCell.Assembly.remainderAnnihilates_holds`, `Breakdown.CellReduction.Instantiation.linearDefect`.

Appendix C requires particular care: its displayed continuum residual and linearised coupling can have formal counterparts even though the surrounding Newton iteration, quadrature and GMRES procedure have no verified implementation in the supplied source. The corrected index keeps that computation outside the source correspondence.

### Read the condition with its witnesses

The fifteen fields of `Breakdown.CellLayerSystem.CellSystemCondition` all refer to one certificate data record, one instance record, one cell-calculus record, one tree, one assembly record, one set of coercivity numbers and one set of reduction entries.

The nested witnesses in `Breakdown.CertCell.CellHypothesis` retain their scope: the pairing-error family must satisfy its surrogate condition and its total-error bound together, while the chosen shape data must satisfy the shape and actuator-support conditions together.

The constants in `Breakdown.CertCell.CellHypothesis` include an azimuthal order of at least three, weight function equal to 39/50, coercivity equal to 3/50 and pin weight equal to 1000.

The data types and predicates have different jobs. Constructing a `CellLayerData` record chooses fields, arrays and constants; proving `CellSystemCondition` establishes the required relationships between those choices. A source declaration of the predicate supplies no particular certificate.

### Keep the local domain and the zero branches

The domain `Breakdown.CertCell.Assembly.InRowRange` constrains coordinates whose row reason is used, permits complex gauge and head contributions, and separately requires the final two actuator blocks to be real.

The local comparisons in `Breakdown.CertCell.Assembly.EliminationConditions` are required for every vector in their supplied domain predicate, so a comparison checked only on an arbitrarily smaller reconstruction image would leave a different obligation.

The slack condition in `Breakdown.CertCell.Assembly.EliminationConditions` allows zero and requires an exact field identity in that branch; its `slack_zero` clause quantifies over every spatial point, without a cell-membership premise.

The kept and port comparisons in `Breakdown.CertCell.Assembly.PotentialConditions` use the same supplied local-domain predicate as the rest of the assembly interface.

### Read a label together with its meaning

The functions `Breakdown.CertCell.labelTime` and `Breakdown.CertCell.labelAzimuth` send a lattice label to the temporal frequency 2ι₂−ι₁ and the azimuthal frequency κι₁.

The definition `Breakdown.CertCell.Assembly.modelLabels` filters the union of four finite support sets by the existence of a cell point where a velocity, vorticity, gradient or vorticity-gradient coefficient is nonzero.

A label is excluded by `modelLabels` only when the required coefficient functions vanish throughout the relevant cell, so an interval enclosure containing zero does not by itself establish exclusion.

The record `Breakdown.CertCell.RowValues` keeps the cell, label, real-or-imaginary selector and test number of each row separately, along with the test weights and polynomial test fields.

### Cautions for a certificate checker

### Shared cautions: Analytic interfaces

For `Breakdown.CertCell.Bridge.patchGradSq`, `Breakdown.CertCell.Bridge.PlaneSegment`, `Breakdown.CertCell.Bridge.IsPlaneSegment`: The angular Dirichlet term divides by r². Preserve the positive inner-radius condition and the patch's actual width and height when binding finite trace data.

For `Breakdown.CellReduction.Instantiation.IsAdjointShapeEntry`: Treat the representation links as exact identities of the decoded functions. Preserve each quantifier: pieces_eq and the bound links are on K, but frame-reflection, profile/target and pressure-gradient identities include unrestricted α where written.

For `Breakdown.CellReduction.Instantiation.ProfileShapeEntry.secondDeriv`: The profile is affine in coefficients only inside rχ, where χ and f_* vanish. Outside that ball f+(k·α)f_* changes with α, so affine vertex tests do not generally bound the field or its derivatives on all of K.

For `Breakdown.CertReduction.AdjointQuadNumbers`, `Breakdown.CertReduction.AdjointQuadraticBounded`: Keep the Boolean choice of L³ or L² norm aligned with its numerical coefficient. The cubed operator/field norm integral and the squared norm integral cannot be interchanged or estimated using a differently normalised matrix norm without a proved bound.

For `Breakdown.CertReduction.gapGradCoeff`, `Breakdown.CertReduction.shiftGradCoeff`, `Breakdown.CertReduction.adjointQuadCoeff`: These formulas divide by w_* or √w_*. The cell route obtains strict positivity from ShapeValuesFacts.weight_pos; preserve that separate premise rather than treating the generic arithmetic formulas as intrinsically guarded. Keep the Boolean choice of L³ or L² norm aligned with its numerical coefficient. The cubed operator/field norm integral and the squared norm integral cannot be interchanged or estimated using a differently normalised matrix norm without a proved bound.

For `Breakdown.CertCell.CellLayerData.stretchPosMean`, `Breakdown.CertCell.CellLayerData.formPos`: Keep the positive-part operation inside the time/angle average and retain the extended-real finiteness distinction. Replacing mean(max(J,0)) by max(mean(J),0), or treating infinity as a finite numeric accumulator, changes the hypothesis.

For `Breakdown.CertCell.Bridge.IsModeClass`: Distinguish lattice labels (ι₁,ι₂) from frequency pairs (2ι₂−ι₁,κι₁). Their flip operations differ, and κ>0 is needed for injectivity of the frequency map.

For `Breakdown.CertCell.Bridge.HasMeasurableBoundData`, `Breakdown.CertCell.Bridge.IsHarmonicExpansion`, `Breakdown.CertCell.Bridge.IsCrossWaveEntry`: These fields quantify over functions, points, angles or all complex test vectors. A finite checker needs a proved representation-level reduction; checking finitely many evaluations does not directly establish them.

For `Breakdown.CertCell.GivenShape.keyHess`, `Breakdown.CertCell.GivenShape.shapeHess`: The reference route requires exactly knotZeroHess, including zero values on its specified exceptional set. Do not identify this with an arbitrary pointwise second derivative at knots; the existing source route proves the weak-Hessian and null-set transfer under its shape conditions.

### Shared cautions: Data representation

For `Breakdown.CertCell.RowValues`: Represent one member of each nonzero ± label pair, with both real and imaginary rows for every test, and only the real row for the zero label. The imaginary generator uses −i before taking a real part; use the same convention in its Gram matrix.

For `Breakdown.CertCell.CellCalculus.CellVar`, `Breakdown.CertCell.CellCalculus.CellIndex`, `Breakdown.CertCell.CellCalculus.CellCalculusEntry`: Reconstruct the dependent layout dimensions and tagged sums before reading matrices: gradient degrees run through Q, velocity degrees stop below Q, ports are complex, and the two final k-blocks have distinct meanings. Preserve each resolved label rather than flattening labels and local coordinates ambiguously.

For `Breakdown.CertCell.Instance.InstanceData`: These records contain functions or possibly infinite sets, not merely stored numeric arrays. Supply a finite representation with exact evaluation and membership semantics and prove its interpretation over the full quantified domain.

For `Breakdown.CertCell.ModelErrors`: Interpret each base model error as the remainder after both high and long pieces are subtracted. The high-piece bounds are separate, and curl-gradient remainder control is almost everywhere; replacing this decomposition by a single uniform model error changes the obligations.

For `Breakdown.CertCell.CellVecField`, `Breakdown.CertCell.CellMatField`, `Breakdown.CertCell.CellLayerData`: The labels select the field sum while coefficient functions exist at all labels. Preserve the separate off-label and active-model conditions; omitting an active model label cannot be justified by merely shrinking a finite list.

For `Breakdown.CertCell.ModeCharges`: The loss contains a velocity-square term divided by the splitting length. Decode the length with its later strict positivity condition; zero length is a defined Lean expression but not the intended Young-inequality split.

For `Breakdown.CertCell.GivenShape.ShapeParams`: A sampled phase and derivatives do not establish C³ regularity or global scaled bounds on [0,∞). Use a concrete phase constructor with its proved conditions, or supply the corresponding analytic argument for the decoded function.

For `Breakdown.CertCell.CellPoly`, `Breakdown.CertCell.CellPoly.eval`: The coefficient array is evaluated in refR and refZ, each centred and scaled by the cell endpoints. Raw (r,z) coefficients require an exact basis conversion before they can denote the same polynomial.

For `Breakdown.CellCert.CellCoordinates.SkeletonKey`, `Breakdown.CellCert.CellCoordinates.keyOf`, `Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal.keySegment`: Use geometric keys to identify the intended skeleton coordinates only. All non-skeleton data map to private_, and the reconstructed key segment uses an auxiliary opposite face; neither fact authorises merging arbitrary interior coordinates.

For `Breakdown.CertCell.GivenShape.TimeFieldData`: Before completing symmetry orbits, check one representative per orbit and the fixed-orbit real/parity constraints. closureAmp has an explicit precedence order; silently merging conflicting representatives changes the decoded field.

### Shared cautions: Mesh and cells

For `Breakdown.CellCert.CellAnalysis.CellBox.refR`, `Breakdown.CellCert.CellAnalysis.CellBox.refZ`: Bind each formula to a valid cell before using its inverse width or height. Lean division is total and returns a value for a zero denominator; a numerical exception is a different semantics.

For `Breakdown.CellCert.CellAnalysis.CellBox.IsAxis`, `Breakdown.CellCert.CellAnalysis.CellBox.lineWeight`, `Breakdown.CellCert.CellAnalysis.CellBox.innerRadius`: Preserve the exact test r₁=0. Replacing it with a floating tolerance can switch the measure, polynomial family or boundary identities used by the proposition.

For `Breakdown.CertCell.CellMesh`, `Breakdown.CertCell.CellMesh.region`, `Breakdown.CertCell.CellMesh.maxVolumeDeg`, `Breakdown.CertCell.IsCellMesh`: Base mesh validity permits an empty mesh and skeleton degree −1; the full certificate adds support, layout and nontrivial-profile obligations. Apply the later skeleton-positive and band-frequency guards, and do not infer an accepted empty certificate from this record alone.

For `Breakdown.CertCell.CellCalculus.ownSolid`: The split bounds use uniquely owned cell portions with r>0; exterior faces can remain when they are not shared. IsSplitPartAE requires one planar null set outside which the residual bound holds for all times and angles, which is stronger than independently choosing a null set for each time/angle.

For `Breakdown.CertCell.CellCalculus.IsPlaneMatched`: IsPlaneMatched is a directional existence condition with exact equality of endpoints and test-coefficient functions. Use the parent quantifiers over reflected resolved labels, or check the desired direction explicitly; do not replace it by approximate geometric overlap.

For `Breakdown.CertCell.CellCalculus.IsPressureSegmentation`: Keep pressure segmentation as an independently required conjunct and check every covered side, disjointness clause, opposite-side value and trace orthogonality rule. The later radial-level condition does not make the entire segmentation optional on non-radial sides.

### Shared cautions: Splines and jets

For `Breakdown.CertCell.GivenShape.IsFullMesh`, `Breakdown.CertCell.GivenShape.IsJoinedSpline`, `Breakdown.CertCell.GivenShape.IsJetAxis`: Verify exact endpoints and strict ordering before using positive interval widths. The active index bounds make the getD defaults in joining tests unreachable, but the generic interpolation constructors do not enforce these guards themselves.

For `Breakdown.CellReduction.Instantiation.StepProfile.eval`: Use the exact cellIndex rule: count internal knots b with b≤u. An internal knot belongs to the cell to its right, while the endpoint 1 selects the final active cell; do not substitute an extrapolation or half-open convention without proving agreement.

For `Breakdown.CellCert.GivenFields.ChartParams`, `Breakdown.CellCert.GivenFields.IsChartParams`, `Breakdown.CellCert.GivenFields.chartT`: Require the chart's strictly positive length before using σ=|y|/(|y|+L). Zero or negative scales produce different total functions and do not satisfy the chart-validity interface.

For `Breakdown.CertCell.GivenShape.chartCoord`, `Breakdown.CertCell.GivenShape.chartRadius`, `Breakdown.CertCell.GivenShape.phaseSlope`, `Breakdown.CertCell.GivenShape.sphereKnots`: The inverse radius Lσ/(1−σ) is intended on σ<1; Lean defines it at σ=1 by total division. In sphereKnots the breakpoint 1 therefore contributes the origin equation, not an infinite sphere. Keep computational endpoint handling consistent with that literal set.

For `Breakdown.CertCell.GivenShape.jetUnit`, `Breakdown.CertCell.GivenShape.nodalLeft`, `Breakdown.CertCell.GivenShape.nodalRight`, `Breakdown.CertCell.GivenShape.bubblePoly`: Preserve the factorial normalization, endpoint orientation and powers of the interval gap. On active valid axes gaps are positive; at arbitrary indices Lean division and power conventions remain total rather than raising an error.

For `Breakdown.CertCell.GivenShape.reflectSpline`, `Breakdown.CertCell.GivenShape.JetDof`, `Breakdown.CertCell.GivenShape.JetAxis.dofs`, `Breakdown.CertCell.GivenShape.JetAxis.reflectDof`: JetDof constructors accept arbitrary natural indices and natural subtraction is truncated at zero. Use the active dofs sets for basis conversion, preserve the zero branches and getD defaults, and prove reflection identities on their stated domains instead of treating every raw index as valid.

For `Breakdown.CertCell.GivenShape.JetAxis.dofSign`: JetDof constructors accept arbitrary natural indices and natural subtraction is truncated at zero. Use the active dofs sets for basis conversion, preserve the zero branches and getD defaults, and prove reflection identities on their stated domains instead of treating every raw index as valid.

For `Breakdown.CellReduction.Instantiation.stepPhase`, `Breakdown.CellReduction.Instantiation.ProfileShapeEntry.moving`, `Breakdown.CellReduction.Instantiation.ProfileShapeEntry.matchRadius`, `Breakdown.CellReduction.Instantiation.ProfileShapeEntry.paramsAt`: The profile is affine in coefficients only inside rχ, where χ and f_* vanish. Outside that ball f+(k·α)f_* changes with α, so affine vertex tests do not generally bound the field or its derivatives on all of K.

For `Breakdown.CellReduction.Instantiation.ProfileShapeEntry.field`, `Breakdown.CellReduction.Instantiation.profileCentreAt`, `Breakdown.CellReduction.Instantiation.profileTangentAt`: The profile is affine in coefficients only inside rχ, where χ and f_* vanish. Outside that ball f+(k·α)f_* changes with α, so affine vertex tests do not generally bound the field or its derivatives on all of K.

For `Breakdown.CellCert.GivenFields.heightRatio`, `Breakdown.CellCert.GivenFields.qOf`, `Breakdown.CellCert.GivenFields.radialVec`, `Breakdown.CellCert.GivenFields.polarVecQ`: The chart formulas have total values at y=0, including divisions by |y|. Recovering continuity or derivatives there requires the prescribed origin factors and jet conditions, not evaluation of these formulas alone.

For `Breakdown.CellCert.GivenFields.azimVecQ`: The chart formulas have total values at y=0, including divisions by |y|. Recovering continuity or derivatives there requires the prescribed origin factors and jet conditions, not evaluation of these formulas alone.

For `Breakdown.CellReduction.Instantiation.PressureKeyAmp`, `Breakdown.CellReduction.Instantiation.pressureKeyValue`, `Breakdown.CellReduction.Instantiation.IsPressureFieldData`: Keep radial-origin exponent h₀, spatial decay h and axis exponent h′₀ separate. The source allows a nonzero-azimuthal term with radial h₀=0 only when its spline vanishes exactly at σ=0; axis h′₀ must still be positive.

For `Breakdown.CellReduction.Instantiation.shapePressure`, `Breakdown.CellReduction.Instantiation.PressureShapeEntry.pressure`: The decoded q is a pressure correction. The residual uses ∇(q−|W|²/2), and its expansion uses the matching linear and quadratic kinetic terms; substituting ∇q alone changes the certified PDE residual.

For `Breakdown.CertCell.GivenShape.symmetricJacobi`, `Breakdown.CertCell.GivenShape.HasSymmetricScale`, `Breakdown.CertCell.GivenShape.ScaledJetSpline`, `Breakdown.CertCell.GivenShape.ScaledKeyData`: A zero node scale is allowed by HasSymmetricScale: Lean has 0⁻¹=0, so positive-order node jets can vanish in conversion while order zero remains unchanged. Decode this literally, or prove an additional nonzero-scale invariant before using an invertible-basis interpretation; this local degeneracy is not a witness to the full cell condition.

For `Breakdown.CertCell.GivenShape.ScaledKeyData.toJets`, `Breakdown.CertCell.GivenShape.ScaledJetData`, `Breakdown.CertCell.GivenShape.ScaledJetData.toJets`: A zero node scale is allowed by HasSymmetricScale: Lean has 0⁻¹=0, so positive-order node jets can vanish in conversion while order zero remains unchanged. Decode this literally, or prove an additional nonzero-scale invariant before using an invertible-basis interpretation; this local degeneracy is not a witness to the full cell condition.

For `Breakdown.CertCell.GivenShape.ScaledJetSpline.coefValues`, `Breakdown.CertCell.GivenShape.ScaledKeyData.coefValueSets`, `Breakdown.CertCell.GivenShape.ScaledJetData.coefValueSets`, `Breakdown.CertCell.GivenShape.IsScaledJetData`: A zero node scale is allowed by HasSymmetricScale: Lean has 0⁻¹=0, so positive-order node jets can vanish in conversion while order zero remains unchanged. Decode this literally, or prove an additional nonzero-scale invariant before using an invertible-basis interpretation; this local degeneracy is not a witness to the full cell condition. coefValues/coefValueSets only expose the unconverted stored coefficients. The model is built from toJet/toJets and then symmetry closure; a checker must evaluate that converted model, not the coefficient-view field.

For `Breakdown.CertCell.GivenShape.ScaledJetAxis`, `Breakdown.CertCell.GivenShape.ScaledJetAxis.convert`, `Breakdown.CertCell.GivenShape.ScaledJetSpline.toJet`: A zero node scale is allowed by HasSymmetricScale: Lean has 0⁻¹=0, so positive-order node jets can vanish in conversion while order zero remains unchanged. Decode this literally, or prove an additional nonzero-scale invariant before using an invertible-basis interpretation; this local degeneracy is not a witness to the full cell condition. Use scale.getD k 1, bubbleConst.getD j 0 and breakpoint defaults 0 exactly. Missing bubble constants therefore remove those basis contributions, while missing node scales default to one; a uniform zero-fill rule changes the decoded field.

For `Breakdown.CellCert.GivenFields.TensorMesh`, `Breakdown.CellCert.GivenFields.IsTensorMesh`, `Breakdown.CellCert.GivenFields.cellIndex`, `Breakdown.CellCert.GivenFields.cellCount`: Use exact ordered knots with endpoints 0 and 1. cellIndex selects the right-hand piece at an interior knot and clamps by counting internal knots; polynomial joining, rather than approximate sampling, proves agreement at the knot.

For `Breakdown.CellCert.GivenFields.Spline`, `Breakdown.CellCert.GivenFields.Spline.evalHalf`: Use exact ordered knots with endpoints 0 and 1. cellIndex selects the right-hand piece at an interior knot and clamps by counting internal knots; polynomial joining, rather than approximate sampling, proves agreement at the knot.

For `Breakdown.CertCell.GivenShape.IsTimeFieldData`, `Breakdown.CertCell.GivenShape.GivenJetData`, `Breakdown.CertCell.GivenShape.GivenJetData.model`: Before completing symmetry orbits, check one representative per orbit and the fixed-orbit real/parity constraints. closureAmp has an explicit precedence order; silently merging conflicting representatives changes the decoded field.

For `Breakdown.CertCell.GivenShape.JetSpline`, `Breakdown.CertCell.GivenShape.JetSpline.IsReflectFixed`, `Breakdown.CertCell.GivenShape.JetSpline.IsConjReflectFixed`, `Breakdown.CertCell.GivenShape.JetSpline.VanishesAtStart`: The evaluated spline uses finite active coordinates, but several symmetry/origin predicates quantify over all radial JetDof coordinates or all pairs. Define the omitted coefficient continuation and prove those identities there; checking only stored coefficients is insufficient without that argument.

For `Breakdown.CertCell.GivenShape.JetSpline.HasRealCoef`: The evaluated spline uses finite active coordinates, but several symmetry/origin predicates quantify over all radial JetDof coordinates or all pairs. Define the omitted coefficient continuation and prove those identities there; checking only stored coefficients is insufficient without that argument.

For `Breakdown.CertCell.KnotZero.zeroOn`, `Breakdown.CertCell.GivenShape.splineKnots`, `Breakdown.CertCell.GivenShape.keyKnots`, `Breakdown.CertCell.GivenShape.shapeKnots`: The reference route requires exactly knotZeroHess, including zero values on its specified exceptional set. Do not identify this with an arbitrary pointwise second derivative at knots; the existing source route proves the weak-Hessian and null-set transfer under its shape conditions.

For `Breakdown.CertCell.GivenShape.mirrorKnots`, `Breakdown.CertCell.GivenShape.knotZeroHess`: The reference route requires exactly knotZeroHess, including zero values on its specified exceptional set. Do not identify this with an arbitrary pointwise second derivative at knots; the existing source route proves the weak-Hessian and null-set transfer under its shape conditions.

### Shared cautions: Harmonics and symmetry

For `Breakdown.CertCell.CellVecField.IsConjugateClosed`, `Breakdown.CertCell.CellMatField.IsConjugateClosed`: The conjugacy equality ranges over every integer label and every meridian point, including labels outside the finite support set. Specify the off-support coefficient continuation and distinguish label negation from reflection.

For `Breakdown.AdjointDefect.complexComponent`, `Breakdown.AdjointDefect.componentWeight`: Check injectivity of the full (component,frequency,order) triple. If a raw expansion contains repeats, sum their complex amplitudes before computing the bound; do not add their squared norms separately. Use weights 1/2,1/2,1, the factor 2π in time and denominator (|order|+1/2)² exactly.

For `Breakdown.CertCell.rowPartFactor`: Represent one member of each nonzero ± label pair, with both real and imaginary rows for every test, and only the real row for the zero label. The imaginary generator uses −i before taking a real part; use the same convention in its Gram matrix.

For `Breakdown.CertCell.CellMatField.frameMap`: Keep output-component index first and derivative/component index second. The 12 coordinates are nine ordered gradient entries 3a+b followed by three velocity entries; a transpose or packing permutation changes the form.

For `Breakdown.CertCell.CellCalculus.CellModelLong.IsLowLabel`: Polynomial moment cancellation uses ordinary dr dz, covers every temporal/angular label, and reaches bidegree 2·deg+1 in the active split. Long-mode cancellation excludes |ι₁|≤2·cut with no bound on ι₂; neither condition follows from a few discrete samples.

For `Breakdown.CertCell.GivenShape.FieldKey`, `Breakdown.CertCell.GivenShape.FieldKey.flipKey`, `Breakdown.CertCell.GivenShape.harmonicsOf`, `Breakdown.CertCell.GivenShape.labelsOf`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces.

For `Breakdown.CertCell.CellCalculus.gradAt`, `Breakdown.CertCell.CellCalculus.velAt`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces.

For `Breakdown.CertCell.CellVecField.field`, `Breakdown.CertCell.CellMatField.field`: Field construction sums closed-cell indicators, so a boundary point can receive contributions from neighbouring cells. The mesh requires measure-zero overlaps rather than pairwise-disjoint closed boxes; preserve the distinction between pointwise identities and almost-everywhere integral statements.

For `Breakdown.CertCell.GivenShape.orbitClosure`, `Breakdown.CertCell.GivenShape.closureAmp`, `Breakdown.CertCell.GivenShape.closureData`: Before completing symmetry orbits, check one representative per orbit and the fixed-orbit real/parity constraints. closureAmp has an explicit precedence order; silently merging conflicting representatives changes the decoded field.

For `Breakdown.CertCell.labelTime`, `Breakdown.CertCell.labelAzimuth`, `Breakdown.CertCell.labelHarmonic`, `Breakdown.CertCell.labelFlip`: Distinguish lattice labels (ι₁,ι₂) from frequency pairs (2ι₂−ι₁,κι₁). Their flip operations differ, and κ>0 is needed for injectivity of the frequency map.

For `Breakdown.CertCell.flipLabel`, `Breakdown.CertCell.IsLatticeHarmonic`, `Breakdown.CertCell.labelPhase`: Distinguish lattice labels (ι₁,ι₂) from frequency pairs (2ι₂−ι₁,κι₁). Their flip operations differ, and κ>0 is needed for injectivity of the frequency map.

### Shared cautions: Shape bounds

For `Breakdown.CertCell.Instance.StepDatum.upperValue`, `Breakdown.CertCell.Instance.StepDatum.lowerValue`: Use the exact cellIndex rule: count internal knots b with b≤u. An internal knot belongs to the cell to its right, while the endpoint 1 selects the final active cell; do not substitute an extrapolation or half-open convention without proving agreement.

For `Breakdown.CertCell.Instance.IsWeightInstance`: Treat the representation links as exact identities of the decoded functions. Preserve each quantifier: pieces_eq and the bound links are on K, but frame-reflection, profile/target and pressure-gradient identities include unrestricted α where written.

For `Breakdown.CertCell.Instance.EpsGiven.mirror`, `Breakdown.CertCell.Instance.MuGiven.mirror`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces.

For `Breakdown.CertCell.Instance.EpsGiven`, `Breakdown.CertCell.Instance.MuGiven`, `Breakdown.CertCell.Instance.WeightValues`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces. These records contain functions or possibly infinite sets, not merely stored numeric arrays. Supply a finite representation with exact evaluation and membership semantics and prove its interpretation over the full quantified domain.

For `Breakdown.CertCell.InstanceSplit.ValuesFlipClauses`, `Breakdown.CertCell.GivenShape.ShapeValuesFacts`, `Breakdown.CertCell.ScalarShape.BoundValues`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces. Verify the full stated domains: all times, spatial points and rotations for amplitudes/transport, all relevant harmonics for support, and all α∈K when the parent condition supplies it. A finite sample of points or parameters is not the enclosure proposition.

For `Breakdown.CertCell.Instance.IsPositiveStep`: Mesh validity is an independent conjunct, even when no table entry is tested. Prove positivity of both half-space values on every active cell; an empty or malformed mesh does not remove the mesh obligation.

For `Breakdown.CertCell.GivenShape.IsRadialPhase`, `Breakdown.CertCell.GivenShape.IsShapeParams`: A sampled phase and derivatives do not establish C³ regularity or global scaled bounds on [0,∞). Use a concrete phase constructor with its proved conditions, or supply the corresponding analytic argument for the decoded function.

For `Breakdown.CertCell.ScalarShape.planeMinEval`, `Breakdown.CertCell.ScalarShape.ChartBound`, `Breakdown.CertCell.ScalarShape.ChartBound.eval`: Keep all three scalar conventions distinct: StepDatum.eval uses the upper half on y₃=0; planeMinEval uses the minimum of the two sides there; ChartBound.eval handles y=0 with originValue before the integer power of σ. Negative powers and exact boundary values cannot be replaced by nearby samples.

For `Breakdown.CertCell.InstanceSplit.EnclosureAdmissibleClauses`, `Breakdown.CertCell.GivenShape.BoundValuesEntry`: Verify the full stated domains: all times, spatial points and rotations for amplitudes/transport, all relevant harmonics for support, and all α∈K when the parent condition supplies it. A finite sample of points or parameters is not the enclosure proposition.

### Shared cautions: Rows and pins

For `Breakdown.CertCell.RowValues.generator`, `Breakdown.CertCell.RowValues.generatorField`, `Breakdown.CertCell.RowValues.testValue`, `Breakdown.CertCell.RowValues.testBlockMatrix`: Represent one member of each nonzero ± label pair, with both real and imaginary rows for every test, and only the real row for the zero label. The imaginary generator uses −i before taking a real part; use the same convention in its Gram matrix.

For `Breakdown.CertCell.Instance.IsRowValues`: Represent one member of each nonzero ± label pair, with both real and imaginary rows for every test, and only the real row for the zero label. The imaginary generator uses −i before taking a real part; use the same convention in its Gram matrix.

For `Breakdown.CertCell.RowValues.fieldPairingMatrix`, `Breakdown.CertCell.RowValues.mix`: The row mixing uses a Hermitian functional-calculus inverse square root and has a zero fallback otherwise. Bind it to the positive-definite block-Gram construction and the exact global real generator matrix.

For `Breakdown.CertCell.RowValues.rowWeightOf`, `Breakdown.CertCell.Instance.IsRowInstance`: Keep the orthonormal row fields separate from testWeight/coercivity. Prove coercivity>0 and the squared row-bound inequality; copying the paper's weighted rows into both places would apply the weight twice.

### Shared cautions: Potentials

For `Breakdown.AdjointDefect.matrixDivergence`, `Breakdown.AdjointDefect.transposeApply`, `Breakdown.AdjointDefect.advectionShift`, `Breakdown.AdjointDefect.adjointTransport`: Match matrix action, transpose and divergence conventions before comparing (B.52). In pinFlux the antisymmetric generator derivative is intentional; replacing it by a bare Laplacian without the divergence-free identity can introduce a wrong sign or transpose.

For `Breakdown.AdjointDefect.remainderField`, `Breakdown.AdjointDefect.AdjointDefectEntry.pinFlux`: Match matrix action, transpose and divergence conventions before comparing (B.52). In pinFlux the antisymmetric generator derivative is intentional; replacing it by a bare Laplacian without the divergence-free identity can introduce a wrong sign or transpose.

For `Breakdown.CellReduction.Instantiation.ballPairing`: Use the same rχ and period-one measure in the core pairings and exterior errors. The source core ball is closed and the outside cutoff is strict; equivalence with an open-ball calculation needs the sphere-null/integrability argument.

For `Breakdown.CellReduction.Instantiation.coordRadius`: The radius formula for an ellipsoid coordinate divides by |scaleᵢ|. Preserve the nonzero-scale conditions on the active certificate route and the distinction between box coordinates in J and complementary ellipsoid coordinates.

For `Breakdown.AdjointDefect.AdjointDefectEntry`, `Breakdown.CellReduction.Instantiation.AdjointEntryLinks`: On the specialised cell route AdjointEntryLinks requires fittedSet=∅ for each active adjoint. The fitted norms then contribute nothing, but all complementary weighted free-direction and period-rate obligations remain.

For `Breakdown.AdjointDefect.PotentialNorms`, `Breakdown.AdjointDefect.RemainderBounded`: The squared/cubed norm comparisons use ENNReal.ofReal. Preserve the accompanying nonnegativity and finite-real upper bounds from the relevant condition; a negative proposed bound or an uncontrolled infinite norm is not an accepted norm certificate.

For `Breakdown.AdjointDefect.potentialDefect`, `Breakdown.AdjointDefect.AdjointDefectEntry.pinCharge`: These formulas divide by w_* or √w_*. The cell route obtains strict positivity from ShapeValuesFacts.weight_pos; preserve that separate premise rather than treating the generic arithmetic formulas as intrinsically guarded.

For `Breakdown.CellReduction.Instantiation.centreDefect`, `Breakdown.CellReduction.Instantiation.linearDefect`: The decoded q is a pressure correction. The residual uses ∇(q−|W|²/2), and its expansion uses the matching linear and quadratic kinetic terms; substituting ∇q alone changes the certified PDE residual.

For `Breakdown.CellReduction.Instantiation.OffsetExpansionEntry`, `Breakdown.CellReduction.Instantiation.OffsetExpansionEntry.orderedQuadratic`, `Breakdown.CellReduction.Instantiation.OffsetExpansionEntry.quadraticCoefficient`: Count off-diagonal αᵢαₗ terms once for i≤l after summing both ordered residual contributions; diagonal terms use only one order. A symmetric full-matrix convention otherwise introduces a factor-of-two error.

For `Breakdown.AdjointDefect.DualBounded`: Use one decomposition R=R₁+R₂ with its two bounds for DualBounded, and one family δᵢ in free_dual that works for every α∈K. Choosing unrelated witnesses for separate descendant inequalities checks a different proposition.

### Shared cautions: Local forms

For `Breakdown.CellCert.CellAnalysis.radialEigen`, `Breakdown.CellCert.CellAnalysis.heightEigen`: Bind each formula to a valid cell before using its inverse width or height. Lean division is total and returns a value for a zero denominator; a numerical exception is a different semantics.

For `Breakdown.CellCert.CellAnalysis.CellBox.proj`, `Breakdown.CellCert.CellAnalysis.CellBox.tailNormSq`: The projection chooses a witness only after an existence test and otherwise returns zero. A numerical least-squares implementation needs a proof of its agreement with the valid weighted projection, not an assumption that this fallback never matters.

For `Breakdown.CertCell.Bridge.CreditPatch.testCombination`, `Breakdown.CertCell.Bridge.CreditPatch.traceData`: Preserve conjugation in the test combination and use the same real trace map in the complex form. Establish positive definiteness of the test matrix before using its inverse; the displayed credit comparison is a real-valued form bound on every complex trace vector.

For `Breakdown.CertCell.CellCalculus.turnVector`, `Breakdown.CertCell.CellCalculus.testGrad`, `Breakdown.CertCell.CellCalculus.IsTestSolenoidal`, `Breakdown.CertCell.CellCalculus.IsAxisRegularTest`: Use the moving-frame angular derivative ikx+e_z×x and its division by r, including the component mixing. The solenoidal and axis-regularity conditions must hold on the whole rectangle; the generic formula alone does not certify smoothness at r=0.

For `Breakdown.CertCell.CellCalculus.lowStrainOf`, `Breakdown.CertCell.CellCalculus.lowVelocityOf`, `Breakdown.CertCell.CellCalculus.energyLeafForm`: Reconstruct the dependent layout dimensions and tagged sums before reading matrices: gradient degrees run through Q, velocity degrees stop below Q, ports are complex, and the two final k-blocks have distinct meanings. Preserve each resolved label rather than flattening labels and local coordinates ambiguously.

For `Breakdown.CertCell.CellCalculus.CellModeLayouts`, `Breakdown.CertCell.CellCalculus.IsCellModeLayouts`, `Breakdown.CertCell.CellCalculus.IsTestOfShape`: Combine the base mesh conditions with skeleton_positive≥1 on every resolved label and the stronger tested-mode degree rules. A generic formula with q−1 uses truncated natural subtraction; do not infer active degree validity from it.

For `Breakdown.CellCert.CellFormula.CellLayout.radialBeta`: Preserve the exact test r₁=0. Replacing it with a floating tolerance can switch the measure, polynomial family or boundary identities used by the proposition.

For `Breakdown.CellCert.CellFormula.CellLayout.sideRadius`, `Breakdown.CellCert.CellFormula.CellLayout.sideHeightIndex`, `Breakdown.CellCert.CellFormula.CellLayout.sideRadialIndex`, `Breakdown.CellCert.CellFormula.CellLayout.faceBaseRow`: Sides 0 and 1 are radial, sides 2 and 3 are height faces. Several selector helpers have total fallback branches, so call them with the same side guards as the assembled formula.

For `Breakdown.CellCert.CellFormula.CellLayout.strainFaceRow`: Sides 0 and 1 are radial, sides 2 and 3 are height faces. Several selector helpers have total fallback branches, so call them with the same side guards as the assembled formula.

For `Breakdown.CellCert.CellAnalysis.curlComp`, `Breakdown.CellCert.CellAnalysis.pairVec`, `Breakdown.CellCert.CellEnergy.matrixSesq`: Keep output-component index first and derivative/component index second. The 12 coordinates are nine ordered gradient entries 3a+b followed by three velocity entries; a transpose or packing permutation changes the form.

For `Breakdown.CertCell.CellCalculus.IsVecOrthogonal`, `Breakdown.CertCell.CellCalculus.IsMatOrthogonal`: Polynomial moment cancellation uses ordinary dr dz, covers every temporal/angular label, and reaches bidegree 2·deg+1 in the active split. Long-mode cancellation excludes |ι₁|≤2·cut with no bound on ι₂; neither condition follows from a few discrete samples.

For `Breakdown.CellCert.CellAnalysis.CellBases`, `Breakdown.CellCert.CellAnalysis.CellBases.radialPoly`, `Breakdown.CellCert.CellAnalysis.CellBases.heightPoly`, `Breakdown.CellCert.CellAnalysis.IsCellBases`: Supply the complete basis family, with the proved continuation beyond stored degrees. Uniform zero extension violates positive leading coefficients and orthonormality at every natural degree.

For `Breakdown.CellCert.CellFormula.FaceSegment`, `Breakdown.CellCert.CellFormula.FaceSegment.test`, `Breakdown.CellCert.CellFormula.IsFaceSegment`: The test family exists at every natural degree, and validity requires every leading coefficient nonzero. A finite table's unspecified entries cannot all be set to zero.

For `Breakdown.CellCert.CellEnergy.testSupForm`, `Breakdown.CellCert.CellEnergy.testInnerMatrix`, `Breakdown.CellCert.CellEnergy.heightInnerForm`, `Breakdown.CellCert.CellEnergy.radialOuterForm`: Retain the exact test Gram matrix and its positive-definiteness or invertibility proof. Lean matrix inversion is total; evaluating an inverse expression does not certify that the numerical factorisation solved the intended system.

For `Breakdown.CellCert.CellEnergy.heightOuterForm`, `Breakdown.CellCert.CellEnergy.angularAxisForm`, `Breakdown.CertCell.Coupling.inverseWeightedSq`: Retain the exact test Gram matrix and its positive-definiteness or invertibility proof. Lean matrix inversion is total; evaluating an inverse expression does not certify that the numerical factorisation solved the intended system.

For `Breakdown.CertCell.CellCalculus.LeafValues`, `Breakdown.CertCell.CellCalculus.lowSlotForm`, `Breakdown.CertCell.CellCalculus.modeBlockForm`: Pack the local vector as the nine gradient entries 3a+b followed by the three velocity entries. Check Hermiticity of the actual full complex matrix before factorization, and prove the inequalities on every complex gradient/vector pair, not just physically sampled values.

For `Breakdown.CellCert.CellEnergy.topForm`: Q−1 is subtraction in the natural numbers and saturates at zero. Enforce the active layout's degree guards before translating these ranges into signed integer loops.

For `Breakdown.CellCert.CellEnergy.angularOffWeight`, `Breakdown.CellCert.CellEnergy.componentForm`: Keep the axis/off-axis distinction and the radial denominator conditions together. The off-axis angular remainder uses 1/(r r₂), whereas the axis formula has its own test family.

For `Breakdown.CertCell.TailBand.PointCoef.curlWithGain`, `Breakdown.CertCell.TailBand.PointCoef.gradFloor`, `Breakdown.CertCell.TailBand.PointCoef.velWithShift`, `Breakdown.CertCell.TailBand.PointCoef.PassesTest`: The scalar formulas divide by r, the stretching length and auxiliary weights. Establish r>0 from the open quarter-plane, the length/step positivity from the associated conditions, and Λ₀>0 on the exterior branch before interval evaluation.

For `Breakdown.CertCell.TailBand.EntryCharges.Covers`: The scalar formulas divide by r, the stretching length and auxiliary weights. Establish r>0 from the open quarter-plane, the length/step positivity from the associated conditions, and Λ₀>0 on the exterior branch before interval evaluation.

For `Breakdown.CertCell.CellCalculus.opBound`, `Breakdown.CertCell.CellCalculus.IsChargeBound`, `Breakdown.CertCell.CellCalculus.IsLeafBoxLink`: opBound compares squared complex operator norms, so its bare predicate is insensitive to the sign of c. Preserve the separate nonnegative charge conditions and the operator-norm convention when translating it to a numerical matrix bound.

For `Breakdown.CellCert.CellFormula.CellLayout`, `Breakdown.CellCert.CellFormula.CellLayout.streamAt`, `Breakdown.CellCert.CellFormula.CellLayout.zeroMode`, `Breakdown.CellCert.CellFormula.IsCellLayout`: Preserve optional corner and zero-mode values. The axis-specific absence rules belong to IsCellLayout; treating every missing reference as an unrestricted zero loses those requirements.

For `Breakdown.CellCert.CellFormula.CellLayout.cornerAt`: Preserve optional corner and zero-mode values. The axis-specific absence rules belong to IsCellLayout; treating every missing reference as an unrestricted zero loses those requirements.

For `Breakdown.CellCert.CellFormula.CellLayout.strainAt`, `Breakdown.CellCert.CellFormula.CellLayout.velocityAt`, `Breakdown.CellCert.CellFormula.CellLayout.extraAt`: These helpers return zero rows outside their stated degree range. Check stored indices and dimensions before evaluation so malformed coordinates are not silently accepted as zeros.

For `Breakdown.CertCell.CellCalculus.IsSplitPart`, `Breakdown.CertCell.CellCalculus.IsSplitPartAE`: The split bounds use uniquely owned cell portions with r>0; exterior faces can remain when they are not shared. IsSplitPartAE requires one planar null set outside which the residual bound holds for all times and angles, which is stronger than independently choosing a null set for each time/angle.

For `Breakdown.CellCert.CellAnalysis.supremumLoss`: The loss contains a velocity-square term divided by the splitting length. Decode the length with its later strict positivity condition; zero length is a defined Lean expression but not the intended Young-inequality split.

For `Breakdown.CertCell.CellCalculus.ownStrainRow`, `Breakdown.CertCell.CellCalculus.ownVelocityRow`, `Breakdown.CertCell.CellCalculus.sideGradRow`, `Breakdown.CertCell.CellCalculus.sidePresRow`: Preserve radial measure, complex conjugation and outward edge orientation in the row integrals. Own pressure rows and gradient rows have opposite orientation signs; the tagged zero blocks are also part of the matrix contract.

For `Breakdown.CertCell.CellCalculus.ownRowVector`, `Breakdown.CertCell.CellCalculus.couplingStrainRow`, `Breakdown.CertCell.CellCalculus.couplingVelocityRow`, `Breakdown.CertCell.CellCalculus.couplingRowVector`: Preserve radial measure, complex conjugation and outward edge orientation in the row integrals. Own pressure rows and gradient rows have opposite orientation signs; the tagged zero blocks are also part of the matrix contract.

For `Breakdown.CellCert.CellFormula.ParamData`, `Breakdown.CellCert.CellFormula.ParamData.solvedBlock`, `Breakdown.CellCert.CellFormula.IsParamData`: Keep the selected rows, solved-coordinate injection and retained skeleton together. Invertibility of a differently ordered or different submatrix does not establish this solved block.

For `Breakdown.CellCert.CellFormula.edgeSign`, `Breakdown.CellCert.CellFormula.radialStripMoment`, `Breakdown.CellCert.CellFormula.heightStripMoment`, `Breakdown.CellCert.CellFormula.FaceSegment.moment`: Certify nonzero opposite-face separation and keep its signed orientation. A width expressed as an absolute value without the compensating sign changes the trace formula.

For `Breakdown.CellCert.CellFormula.CellDatum`, `Breakdown.CellCert.CellFormula.CellLayout.Datum`, `Breakdown.CellCert.CellFormula.CellLayout.instFintypeDatum`, `Breakdown.CellCert.CellFormula.CellLayout.RelIndex`: Decode the tagged blocks with their distinct cutoffs. For h harmonics, Q volume degree, q skeleton degree, s segments, p pressure segments and c corners, card(Datum)=h[9(Q+1)^2+3Q^2+3s(q+2)+3s(q+1)+pq+3c+12(Q+1)]+c; the final corner-stream block is not multiplied by h.

For `Breakdown.CertCell.TailBand.velTailGain`, `Breakdown.CertCell.TailBand.TailBudget.velCharge`, `Breakdown.CertCell.TailBand.TailBudget.Holds`: The generic velocity gain is zero at Q=0 and the real quotient is total. On the active resolved-cell route use the effective degree conditions before dividing by it; do not infer positivity merely from the function name.

For `Breakdown.CertCell.CreditEval.IsPlaneSideDatum`: Check the exact selected vertical side-velocity coordinate, physical harmonic, segment orientation, endpoints and all test-function values. A matching numeric port identifier alone does not establish the credit trace identity.

### Shared cautions: The tree

For `Breakdown.CertCell.Certificate.CoordinateRealification`, `Breakdown.CertCell.Certificate.IsCoordinateOn`, `Breakdown.CertCell.Certificate.CoordinateRealification.matrix`, `Breakdown.CertCell.Certificate.CoordinateRealification.Owns`: Absent slots are allowed. Pivot coordinates require sign squared equal to one and distinct present real/imaginary slots, but distinct complex coordinates may share a real slot; the translated slack is the sum over all owners.

For `Breakdown.CertCell.Certificate.CoordinateRealification.pivotImage`, `Breakdown.CertCell.Certificate.CoordinateRealification.slackOn`: Absent slots are allowed. Pivot coordinates require sign squared equal to one and distinct present real/imaginary slots, but distinct complex coordinates may share a real slot; the translated slack is the sum over all owners.

For `Breakdown.CertCell.Certificate.SignedTree`, `Breakdown.CertCell.Certificate.SignedTree.nodeInput`: The data type contains an arbitrary finite parent map. Later conditions require a unique parentless root, but do not literally require acyclicity; the proof uses finite summed cancellation. An acyclic file format is a stronger representation choice, not a missing extracted field.

For `Breakdown.CertCell.Certificate.slackRemainder`, `Breakdown.CertCell.Certificate.complexSlackRemainder`, `Breakdown.CertCell.Certificate.realRestriction`, `Breakdown.CertCell.Certificate.PassesRealNodeEnclosure`: Use the exact signs of the positive and negative column products, the two error matrices and the nonpivot radius subtraction. Complex forms require conjugate transposes and complex moduli, not real transposes and entrywise real parts.

For `Breakdown.CertCell.Certificate.PassesPivotCount`, `Breakdown.CertCell.Certificate.realColumns`, `Breakdown.CertCell.Certificate.ComplexNodeData`: Each negative complex column produces two indexed real columns, with an injective map into the global column type. Count the indices even when some resulting vectors vanish or coincide, and preserve the square-root factor.

### Shared cautions: Exterior and omitted modes

For `Breakdown.CertCell.TailBand.SetPieceBounds.shareHatHigh`, `Breakdown.CertCell.TailBand.SetPieceBounds.curlLow`, `Breakdown.CertCell.TailBand.SetPieceBounds.gradLow`, `Breakdown.CertCell.TailBand.SetPieceBounds.velLow`: Piece membership and strict positivity indicators are exact predicates in these coefficient formulas. An interval that contains zero does not decide a strict inequality; retain an undecided outcome or prove a sufficient enclosure without guessing the branch. wtGrad uses the total Fréchet derivative of the decoded weight. At a nondifferentiable spline knot this must not be silently replaced by a chosen one-sided derivative; preserve the exact convention for pointwise tests and use the source regularity/almost-everywhere arguments where appropriate.

For `Breakdown.CertCell.TailBand.IsDirectionRadius`: Keep the single shared radial function R and its global bounds throughout the radial-graph branch. The square-exterior alternative additionally requires every tested angular frequency to be zero; check the selected branch with its own Λ₀ bound.

For `Breakdown.CertCell.TailBand.OffModeCondition`, `Breakdown.CertCell.TailBand.ExteriorCondition`: These records contain functions or possibly infinite sets, not merely stored numeric arrays. Supply a finite representation with exact evaluation and membership semantics and prove its interpretation over the full quantified domain.

For `Breakdown.CertCell.TailBand.SetPieceBounds`: Distinguish lattice labels (ι₁,ι₂) from physical harmonic pairs (2ι₂−ι₁,κι₁), although both use ℤ×ℤ. Their reflection maps are labelFlip and flipLabel respectively; apply the correct map and conversion at support-set interfaces. These records contain functions or possibly infinite sets, not merely stored numeric arrays. Supply a finite representation with exact evaluation and membership semantics and prove its interpretation over the full quantified domain.

For `Breakdown.CertCell.TailBand.IsOffModeCondition`: The scalar formulas divide by r, the stretching length and auxiliary weights. Establish r>0 from the open quarter-plane, the length/step positivity from the associated conditions, and Λ₀>0 on the exterior branch before interval evaluation.

### Shared cautions: The fifteen fields

For `Breakdown.CellLayerSystem.breakdownOnSpace_of_cell_system_condition`, `Breakdown.CellLayerSystem.breakdownOnTorus_of_cell_system_condition`, `Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition`: Do not present this file’s sorry theorem as a compiled proof. Resolve the matching implementation and its verification receipt separately.
<!-- /passage:sec-closing-the-reading-gaps -->

