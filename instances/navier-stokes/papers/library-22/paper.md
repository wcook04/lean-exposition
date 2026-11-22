
<!-- passage:front -->
# Library guide 22: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) **22** [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.SharpYModeExpansion` to `Breakdown.FracCell.VelocityTailSt` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.SharpYModeExpansion

Expands the original mode energy and coupling into polynomial low modes, residual waves, cross terms and actuator or pin pairings, then integrates the decomposition.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYModeExpansion.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.ModeExpansionParts`.

**The residual-to-residual wave pair.** Definition `sharpPair`: The residual wave pair uses the residual gradient and velocity in both wave-form slots.

**The low-to-residual wave pair.** Definition `lowSharpPair`: The low-to-residual wave pair places the low gradient and velocity in the first slot and the residuals in the second.

**The residual-to-low wave pair.** Definition `sharpLowPair`: The residual-to-low wave pair places residuals in the first slot and low gradient and velocity modes in the second.

**The low-to-low wave pair.** Definition `lowLowPair`: The low wave pair uses polynomial gradient and velocity modes in both slots.

**Both orders of the low-residual crossing.** Definition `crossPair`: The cross pair adds the low-to-residual wave interaction and the reversed residual-to-low interaction.

**A matrix field paired with the residual.** Definition `fieldSharp`: The residual field pairing pairs the residual gradient with the same-frequency angular mode of the supplied matrix field.

**A matrix field paired with the low mode.** Definition `fieldLow`: The low field pairing pairs the low gradient with the same-frequency angular mode of the supplied matrix field.

**Derivative energy at one angular mode.** Definition `energyAt`: The mode energy density combines second-derivative and curl-gradient squares with their viscosity and coercivity coefficients.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Regularity of every expansion term.** Proposition `ModeExpansionRegularStatement`: This proposition requires the pointwise summability, modewise integrability and absolute integral summability needed for all energy, wave and field terms in the low-residual expansion.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYModeExpansion.Internal`.

**Curl components preserve addition.** Proved result `curl_add`: The curl component of a matrix sum equals the sum of its curl components.

**The coupling map preserves addition.** Proved result `coupling_add`: The coupling map is additive in its vector input.

**Matrix pairing adds in its left slot.** Proved result `pairing_add_left`: Pairing a matrix sum with a fixed matrix equals the sum of the pairings.

**Matrix pairing adds in its right slot.** Proved result `pairing_add_right`: Pairing a fixed matrix with a matrix sum equals the sum of the pairings.

**The wave form adds in its left slot.** Proved result `wave_add_left`: The wave form is additive in the paired gradient and velocity inputs of its left slot.

**The wave form adds in its right slot.** Proved result `wave_add_right`: The wave form is additive in the paired gradient and velocity inputs of its right slot.

**A zero left input gives zero.** Proved result `wave_zero_left`: The wave form is zero when both left inputs are zero.

**A zero right input gives zero.** Proved result `wave_zero_right`: The wave form is zero when both right inputs are zero.

**Split gradient into low and residual.** Proved result `grad_split`: The original angular gradient mode equals its low polynomial mode plus its residual.

**Split velocity into low and residual.** Proved result `vel_split`: The original angular velocity mode equals its low polynomial mode plus its residual.

**Low inputs vanish outside resolved modes.** Proved result `low_zero`: Low gradient and velocity modes are both zero outside the resolved mode set.

**Low wave pairs have finite support.** Proved result `lowLow_zero`: The low-to-low wave pair vanishes if either mode is outside the resolved set.

**The low-to-residual pair has low support.** Proved result `lowSharp_zero`: The low-to-residual wave pair vanishes when its low mode is outside the resolved set.

**The residual-to-low pair has low support.** Proved result `sharpLow_zero`: The residual-to-low wave pair vanishes when its low mode is outside the resolved set.

**Split a wave pair into four pieces.** Proved result `wave_split`: The original wave pair is the sum of the low-to-low, low-to-residual, residual-to-low and residual-to-residual wave pairs.

**Split the full mode coupling.** Proved result `coupling_split`: Given the required residual and cross summability, the mode coupling equals the real sum of the finite low wave sum, the low-residual crossings and the residual double wave sum.

**The radial factors multiply to radius.** Proved result `weight_rhat`: The line weight times the modified radius equals radius.

**Real parts commute with integration.** Proved result `re_integral`: For an integrable radial-weighted complex function, the real part of its integral equals the integral of its radial-weighted real part.

**Real parts preserve integrability.** Proved result `re_integrable`: Integrability of a radial-weighted complex function implies integrability of its radial-weighted real part.

**Split the full field pairing.** Proved result `field_split`: When the residual field series is summable, the mode field pairing is the real sum of its finite resolved low pairings and residual pairing series.

**Integrate the local density series.** Proved result `density_part`: Modewise integrability and the stated absolute and signed summability identify mode energy plus density sum with the integral of the full local density series.

**Exchange a real series and cell integral.** Proved result `series_part`: Almost-everywhere complex summability and absolute integral summability allow integration to commute with the radial-weighted real series.

**Partition the wave-cross integral.** Proved result `cross_part`: Under cross-series regularity, crossings into any mode set and its complement add to the full integrated cross sum.

**Integrate the three coupling pieces.** Proved result `coupling_part`: Pointwise residual summability and integrability of the low, cross and residual pieces give integrability of the full coupling and its three-part integral identity.

**Remove the low matrix contribution.** Proved result `localPair_part`: When the relevant low terms are integrable, the local pair form minus the low matrix sum equals the finite integrated low-to-low wave sum.

**Integrate the low-residual field split.** Proved result `field_part`: Pointwise summability and the stated integral regularity identify the full field integral with the finite low-mode integrals plus the residual integral series.

**Split actuator and pin linear terms.** Proved result `linear_part`: Under modewise integrability and absolute residual integral summability, the combined low and residual linear contribution equals the actuator-weighted and twice-pin-weighted full pairing sums.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The regular mode expansion holds.** Proved result `modeExpansion`: The expansion regularity interface proves the integrated low-residual mode expansion.

### Breakdown.FracCell.SharpYSharpCross

Identifies the Y coefficient linear terms with residual target pairings and uses symmetric model strain and Hermitian local matrices to express the wave and matrix crossings.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYSharpCross.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpParts`.

**One Y strain coefficient pairing.** Definition `yStrainCoefPart`: The Y strain coefficient term pairs a retained residual strain coefficient with the corresponding folded Y target coefficient and vanishes on excluded low indices.

**One Y velocity coefficient pairing.** Definition `yVelocityCoefPart`: The Y velocity coefficient term pairs the velocity coefficient with its Y target coefficient at or above the high-degree threshold and is zero below it.

**The integrated folded Y strain pairing.** Definition `yStrainPairing`: The Y strain pairing is twice the real line-weighted integral of residual gradient against the folded Y target.

**The integrated Y velocity pairing.** Definition `yVelocityPairing`: The Y velocity pairing is twice the real line-weighted integral of residual velocity against the Y velocity target.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The model strain is self-adjoint.** Definition `ModelStrainSymmetric`: This predicate requires the real model-strain linear map to be self-adjoint at every spatial point.

**The residual-cross bound with symmetry.** Proposition `SharpCrossSymmStatement`: This proposition gives the Y residual-form bound by coefficient energy and wave, linear and matrix crossings under an explicit model-strain symmetry hypothesis.

**The folded Y targets have finite energy.** Proposition `YTargetSquareStatement`: This proposition requires weighted square integrability of the folded strain target on the Y modes and of the velocity target on resolved modes.

**The Y pairings fit the crossing budget.** Proposition `YPairingStatement`: This proposition bounds the finite Y strain and resolved velocity pairing sums by resolved-and-band wave crossings, linear residual pairings and matrix crossings for symmetric model strain.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYSharpCross.Internal`.

**Y strain coefficients sum to the pairing.** Proved result `strain_hasSum`: The basis pairing and projection-coefficient interfaces identify the retained Y strain coefficient series with its integrated pairing when the field and target are weighted square integrable.

**Sum the Y velocity coefficient pairings.** Proved result `velocity_hasSum`: For a resolved mode and positive degree cutoff, the basis and projection interfaces identify the retained Y velocity coefficient series with its integrated pairing under weighted regularity.

**Split the Y strain coefficient term.** Proved result `strain_term_split`: With zero row multipliers, the residual strain term splits into its symmetric and antisymmetric weighted square terms plus the Y strain coefficient pairing.

**Split the Y velocity coefficient term.** Proved result `velocity_term_split`: With zero row multipliers, the residual velocity term splits into its weighted square term plus the Y velocity coefficient pairing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Derive the residual-cross bound.** Proved result `sharpCross_of`: Basis and projection identities, field and target regularity, residual coefficient energy and the Y pairing bound imply the residual-cross interface for symmetric model strain.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpParts`.

**The unfolded Y strain pairing.** Definition `yStrainUnfolded`: The unfolded Y strain pairing is twice the real line-weighted integral against the unfolded strain target.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Separate Y targets have finite energy.** Proposition `YStrainSquareStatement`: This proposition requires weighted square integrability of both unfolded strain and velocity Y targets on all Y modes.

**The unfolded Y pairings fit the budget.** Proposition `YUnfoldedStatement`: This proposition bounds the sum of separate Y strain and velocity pairings by wave, linear and matrix crossings under model-strain symmetry.

**Fold the Y pairing inequality.** Proved result `yPairing_of`: Field-mode regularity, separate Y target regularity, the turn identity and the unfolded pairing bound imply the folded Y pairing interface.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYSharpCross.Internal`.

**Strain symmetry in the cylindrical frame.** Proved result `frameMat_strain_symm`: A self-adjoint model strain has symmetric matrix entries in every cylindrical frame.

**Negative strain modes are adjoints.** Proved result `strainMode_neg`: For symmetric model strain, the negative-frequency strain coefficient equals the conjugate transpose of the positive-frequency coefficient.

**Real matrix pairings are symmetric.** Proved result `entry_re_swap`: The real part of half the matrix entry pairing is unchanged when the two matrices are exchanged.

**Real wave pairings exchange their slots.** Proved result `pairWave_re_swap`: Conjugate-transpose symmetry of the strain symbols makes the real wave pairing invariant under exchanging the two mode-input slots.

**Strain symmetry gives wave reciprocity.** Proved result `pairWave_re_swap_of_symm`: Self-adjoint model strain makes the real wave pairing invariant under exchange of its two mode-input slots.

**The velocity coupling adjoint identity.** Proved result `coupling_adj`: Pairing velocity with the coupling adjoint equals the complex conjugate of pairing strain with the forward coupling map.

**The curl adjoint pairing identity.** Proved result `curl_adj`: Pairing a matrix with the curl adjoint of a vector equals the component pairing of its curl with that vector.

**Wave actions recover both cross terms.** Proved result `wave_pair`: For symmetric model strain, twice the real pairing with the strain and velocity wave actions equals the sum of both ordered wave pairings.

**Unpack a twelve-component pairing.** Proved result `split_pair`: The strain and velocity pairings with split components add to the packed twelve-component conjugate pairing.

**Hermitian matrix action gives crossings.** Proved result `matrix_pair`: For a Hermitian local matrix, twice the real pairing with its action equals the real sum of both ordered matrix cross terms.

**The radial factors multiply to radius.** Proved result `lw_rHat`: The line weight times the modified radial factor equals physical radius.

**Pair a scaled sum of three matrices.** Proved result `ep_scale3`: A matrix pairing with a real-scaled sum of three targets equals that scalar times the sum of the three pairings.

**Pair a scaled sum of two vectors.** Proved result `vp_scale2`: A vector pairing with a real-scaled sum of two targets equals that scalar times the sum of the two pairings.

**Matrix pairing commutes with finite sums.** Proved result `ep_finsum`: Pairing a matrix with a finite target sum equals the finite sum of its pairings.

**Vector pairing commutes with finite sums.** Proved result `vp_finsum`: Pairing a vector with a finite target sum equals the finite sum of its pairings.

**Recover actuator and pin coefficients.** Proved result `ep_lin`: Twice the real pairing with half-weighted actuator targets and pin-weighted targets equals the real actuator pairing plus twice the pin pairing.

**Sum the wave-action crossing identity.** Proved result `wave_sum`: For symmetric model strain, twice the real pairing with the summed resolved wave actions equals the sum of both ordered resolved-to-input wave crossings.

**Expand the Y target crossings.** Proved result `unfolded_pointwise`: For symmetric model strain and Hermitian local matrices, twice the line-weighted residual Y pairing equals radius times its selected wave crossings, matrix crossing and linear actuator-pin contribution.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble the symmetric residual bound.** Proved result `sharpCross_of_leaves`: The basis, projection, field, target, turn, coefficient-energy and unfolded-pairing interfaces imply the residual-cross bound with model-strain symmetry.

### Breakdown.FracCell.SharpYSharpEnergyTail

Defines and assembles the coefficient-energy interfaces that charge residual strain, vorticity and velocity tails against full second-derivative mode energy.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYSharpEnergyTail.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailParts`.

**A weighted residual strain coefficient.** Definition `yTerm`: The strain term is the symmetric and antisymmetric weighted coefficient energy on retained residual indices and zero on excluded low indices.

**A weighted residual velocity coefficient.** Definition `vTerm`: The velocity term is the weighted velocity coefficient energy at or above the high-degree threshold and zero below it.

**A finite square plus its outer series.** Definition `splitSum`: The split sum adds the finite two-degree sum through the cutoff to the series outside that degree square.

**One mode's resolved energy charge.** Definition `energyAt`: The resolved charge combines strain and vorticity energies with their weights and subtracts the tail-shift multiple of the highest-degree gradient contribution.

**One mode's absorption integral.** Definition `absorbAt`: The absorption term is the line-weighted integral of the mode's residual absorption density.

**One mode's full derivative energy.** Definition `modeEnergyAt`: The mode energy integrates the radial-weighted second-derivative and curl-gradient squares with their viscosity and coercivity coefficients.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The coefficient-tail bound at one mode.** Proposition `ModeEnergyTailStatement`: This proposition bounds each mode's applicable resolved charge, Y strain tail, resolved velocity tail and absorption integral by its full derivative energy.

**Summability of energy and absorption.** Proposition `EnergyTailRegularStatement`: This proposition requires summability over angular modes of both the full derivative-energy integrals and absorption integrals.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailInternal`.

**A nonnegative series inequality.** Proved result `tsum_add_le`: For two nonnegative families, the total of their pointwise sum is at most the sum of their real-valued totals.

**Move a finite sum outside a series.** Proved result `tsum_finset_le`: For a finite family of nonnegative two-degree terms, the total after finite summation is at most the finite sum of their real-valued totals.

**A finite sum as a supported series.** Proved result `finset_as_tsum`: A finite mode sum equals the infinite sum of the family extended by zero outside that finite set.

**Finite mode support gives summability.** Proved result `finset_summable`: A family restricted to a finite mode set and set to zero elsewhere is summable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Sum the modewise tail bounds.** Proved result `sharpEnergyTail_of`: The per-mode energy-tail estimate and energy-tail regularity imply the integrated residual energy-tail inequality.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailParts`.

**The retained strain coefficient indices.** Definition `strainIdx`: A strain coefficient is retained when its angular mode is unresolved or either polynomial degree exceeds the high cutoff.

**The symmetric strain coefficient square.** Definition `symCoefSq`: The symmetric coefficient energy is the symmetric matrix square of the selected full gradient coefficient.

**The skew strain coefficient square.** Definition `antiCoefSq`: The antisymmetric coefficient energy is the antisymmetric matrix square of the selected full gradient coefficient.

**The velocity coefficient square.** Definition `velCoefSq`: The velocity coefficient energy is the vector square of the selected velocity coefficient.

**The symmetric angular frequency shift.** Definition `symShift`: The symmetric shift is angular weight times the square of the positive part of mode magnitude minus two.

**The skew angular frequency shift.** Definition `antiShift`: The antisymmetric shift is angular weight times the square of the positive part of mode magnitude minus one.

**Choose the velocity tail eigenvalue.** Definition `velEigen`: The velocity eigenvalue is radial when the radial degree meets the high cutoff and is the height eigenvalue otherwise.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The complete coefficient-energy bound.** Proposition `ModeCoefEnergyStatement`: This proposition combines weighted residual integrability, exact coefficient energy sums, shifted strain and vorticity tail bounds and the high-degree velocity bound into one modewise interface.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailInternal`.

**A convergent split sum is the full sum.** Proved result `split_eq`: For a summable two-degree family, the finite-square-plus-tail split equals the full series total.

**A convergent bound for the split sum.** Proved result `split_le`: A nonnegative two-degree family dominated by a series with specified sum has its finite-square-plus-tail sum bounded by that sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Coefficients give modewise tail bounds.** Proved result `modeEnergyTail_of`: The complete coefficient-energy interface implies the per-mode residual energy-tail estimate.

**Assemble the coefficient-tail bound.** Proved result `sharpEnergyTail_of_coef`: The coefficient-energy interface and angular energy-tail regularity imply the total residual energy-tail bound.

**Exact residual coefficient energy sums.** Proposition `ModeEnergySumStatement`: This proposition requires weighted residual and derivative integrability and identifies residual gradient, curl and resolved velocity energies with their selected coefficient-square series.

**Shifted strain fits derivative energy.** Proposition `ModeStrainCoefStatement`: This proposition requires summability of the shifted symmetric and antisymmetric coefficient series and bounds their sum plus any resolved strain energy by the full second-derivative energy.

**Shifted vorticity fits the curl energy.** Proposition `ModeVorticityCoefStatement`: This proposition bounds twice the shifted antisymmetric coefficient series plus any resolved vorticity energy by the full curl-gradient energy.

**Velocity tails fit gradient coefficients.** Proposition `ModeVelocityCoefStatement`: This proposition requires summability of the eigenvalue-weighted high-degree velocity coefficients and bounds their total by the highest-degree gradient contribution plus the residual strain coefficient energy.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailInternal`.

**A radial integral is nonnegative.** Proved result `rect_nonneg_integral`: On a valid cell, the integral of radius times a pointwise nonnegative real function is nonnegative.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Combine the coefficient-energy bounds.** Proved result `modeCoefEnergy_of`: The residual energy-sum, strain, vorticity and velocity coefficient interfaces jointly imply the complete mode coefficient-energy interface.

**Assemble the four coefficient bounds.** Proved result `sharpEnergyTail_of_parts`: The four coefficient-energy interfaces together with energy-tail regularity imply the residual energy-tail estimate.

**Velocity tails through residual norms.** Proposition `ModeVelocityIdentityStatement`: This proposition requires summability and a velocity-tail norm bound for the high-degree velocity coefficients, together with a bound of the gradient residual norm by the residual strain coefficient sum.

**Convert the legacy velocity identity.** Proved result `modeVelocityCoef_of`: The velocity-tail inequality and the stronger velocity-identity interface imply the downstream velocity coefficient bound.

**Shifted strain tails through derivatives.** Proposition `ModeStrainIdentityStatement`: This proposition requires summability of shifted strain coefficient tails and bounds them by projection-residual derivative energies on resolved modes and full derivative energies on other modes.

**Vorticity through curl derivatives.** Proposition `ModeVorticityIdentityStatement`: This proposition bounds the shifted antisymmetric coefficient series by curl residual derivative energies on resolved modes and by full curl-gradient energy on other modes.

**Derive the strain coefficient bound.** Proved result `modeStrainCoef_of`: Resolved and unresolved energy bounds together with the strain-identity interface imply the strain coefficient estimate.

**Derive the vorticity coefficient bound.** Proved result `modeVorticityCoef_of`: The resolved-energy bound and vorticity-identity interface imply the shifted vorticity coefficient estimate.

**Assemble the derivative-tail route.** Proved result `sharpEnergyTail_of_leaves`: Resolved and unresolved energy, velocity tails, exact coefficient sums, the three identity interfaces and energy-tail regularity imply the residual energy-tail estimate.

### Breakdown.FracCell.SharpYSharpField

Shows that subtracting the polynomial low projection preserves trace freedom and supplies the almost-everywhere turn constraint on unresolved modes.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYSharpField.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The low strain projection is trace free.** Proved result `low_trace`: For a second-order field and a valid cell basis, the diagonal entries of every low strain projection sum to zero at every point.

**Radius is positive almost everywhere.** Proved result `pos_ae`: Radius is strictly positive almost everywhere on a valid cell rectangle.

**The residual field constraints hold.** Proved result `sharpField`: The trace-free low projection and almost-everywhere angular identity establish the residual trace and turn interface.

### Breakdown.FracCell.SharpYSharpSupremum

Turns the pointwise residual wave lower bound into the integrated supremum-loss estimate using square summability and absolute integral regularity.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYSharpSupremum.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpSupremumParts`.

**The residual double wave series.** Definition `waveSum`: The wave sum is the iterated series of residual-to-residual wave pairings over both angular modes.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Residual circle squares are summable.** Proposition `SharpCircleSquareStatement`: This proposition requires the residual gradient and velocity square series to be summable at almost every cell point.

**The circle wave has a loss lower bound.** Proposition `SharpCircleBoundStatement`: This proposition bounds the real residual wave series below by minus the summed supremum density almost everywhere, assuming the two residual square series are summable.

**Regularity of the supremum-loss estimate.** Proposition `SharpSupremumRegularStatement`: This proposition requires modewise integrability and absolute integral summability of supremum losses and integrability of the radial-weighted real residual wave sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpSupremumParts`.

**Absolute integral sums are integrable.** Proved result `integrable_tsum_of`: An integrable family whose norm integrals are summable has an integrable pointwise series sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Integrate the residual wave lower bound.** Proved result `sharpSupremum_of`: Residual square summability, the circle wave bound and supremum regularity imply the integrated residual supremum estimate.

### Breakdown.FracCell.ShiftedParam

Shows that pressure gauge shifts leave the finite cell relations unchanged and therefore admit the shifted parameter reconstruction.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ShiftedParam.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula.ShiftedParamInternal`.

**Free coordinates preserve addition.** Proved result `freePart_add`: Taking the free coordinates of a data vector is additive.

**The parameter map preserves addition.** Proved result `param_add`: The finite data parameter map sends a sum to the sum of its parameter vectors.

**The pressure slot in the datum union.** Definition `presPt`: The pressure-point constructor embeds a mode, pressure index and side degree into the pressure branch of the nested cell datum type.

**A different unit row misses pressure.** Proved result `unitAt_presPt`: A unit row at a datum different from the selected pressure slot evaluates to zero at that pressure slot.

**Velocity rows have no pressure entry.** Proved result `velocityAt_presPt`: Every velocity coefficient row evaluates to zero at every pressure datum.

**Strain rows have no pressure entry.** Proved result `strainAt_presPt`: Every strain coefficient row evaluates to zero at every pressure datum.

**Extra rows have no pressure entry.** Proved result `extraAt_presPt`: Every extra face row evaluates to zero at every pressure datum.

**Stream rows have no pressure entry.** Proved result `streamAt_presPt`: Every stream row evaluates to zero at every pressure datum.

**Side velocity rows miss pressure data.** Proved result `sideVelocity_presPt`: A unit row at a side-velocity datum evaluates to zero at a pressure datum.

**Turn rows have no pressure entry.** Proved result `turnRow_presPt`: Every turn relation row evaluates to zero at every pressure datum.

**Relation rows have no pressure entry.** Proved result `relationRow_presPt`: Every finite relation row evaluates to zero at every pressure datum.

**Pressure shifts satisfy all relations.** Proved result `relationRow_mul_pressureShift`: The finite pairing of any relation row with the pressure-shift vector is zero.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Reconstruct the shifted parameters.** Proved result `shiftedParam_of_recover`: The true-data parametrization and parameter-recovery interfaces show that the parameter map fixes the pressure-shifted admissible data.

### Breakdown.FracCell.ShiftedRealReduction

Checks conjugation, zero-mode support and deleted coordinates for a real pressure gauge shift before reducing shifted complex data to real coordinates.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ShiftedRealReduction.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula.ShiftedRealReduction.Internal`.

**Negating a stored mode negates its value.** Proved result `negMode_val`: If the stored mode set is closed under negation, the selected negative mode has the negated integer value.

**The zero mode is its own negative.** Proved result `negMode_of_zero`: A stored zero mode is fixed by the negative-mode operation.

**Conjugating a datum negates its mode.** Proved result `modeOf_conj`: For a mode set closed under negation, the conjugate datum has the negative angular mode.

**Zero-mode data are fixed by conjugation.** Proved result `conj_of_modeOf_zero`: A datum whose angular mode is zero is fixed by datum conjugation.

**Conjugation preserves plane deletion.** Proved result `plane_conj`: A conjugate datum is plane-deleted exactly when the original datum is plane-deleted.

**Gauge-deleted data have zero mode.** Proved result `modeOf_of_gauge`: Every gauge-deleted datum belongs to angular mode zero.

**The pressure shift is real.** Proved result `shift_im`: Every pressure-shift datum has imaginary part zero.

**Pressure shifts vanish at nonzero modes.** Proved result `shift_of_modeOf_ne`: The pressure-shift vector vanishes at every datum with nonzero angular mode.

**Pressure shifts vanish on deleted planes.** Proved result `shift_of_plane`: The pressure-shift vector vanishes at every plane-deleted datum.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Reconstruct the shifted real coordinates.** Proved result `shiftedRealReduction_of`: Conjugate-data consistency and plane deletion show that the real expansion map fixes pressure-shifted data when the gauge-deleted coordinates vanish.

### Breakdown.FracCell.SliceMeasurable

Transfers spatial almost-everywhere measurability to the cylindrical-frame angular slices used by Fourier estimates.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SliceMeasurable.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SliceMeasurable`.

**Measurable continuous slice observables.** Proved result `comp_aesm`: A continuous complex observable of angle and an almost-everywhere strongly measurable angular function remains almost-everywhere strongly measurable.

**Frame entries on almost every circle.** Proved result `slice_aesm`: A measurable spatial matrix field has measurable cylindrical-frame entries on almost every angular circle over a valid cell rectangle.

### Breakdown.FracCell.SmoothingLower

Proves the Fourier multiplier lower estimate for a smoothing form by comparing a field with any L2 weakly differentiable approximant.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SmoothingLower.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Internal.SmoothingLower`.

**The scalar smoothing comparison.** Proved result `scalar_bound`: For positive lambda and nonnegative x, the ratio-weighted square of a sum is bounded by the first square plus x over lambda times the second square.

**The vector smoothing comparison.** Proved result `vec_bound`: For positive lambda and nonnegative x, the ratio-weighted square norm of a vector is bounded by its squared distance to a comparison vector plus x over lambda times that vector's square norm.

**The square of an L2 complex vector.** Proved result `sq_integrable`: The squared norm of a complex vector field in L2 is integrable.

**An L2 real vector has integrable square.** Proved result `sq_integrable_real`: The squared norm of a real vector field in L2 is integrable.

**Fourier transform of a weak derivative.** Proved result `hat_grad`: For an L2 field with square-integrable weak gradient, the Fourier transform of a coordinate derivative equals two pi i times that frequency coordinate times the field transform almost everywhere.

**Frequency energy is derivative energy.** Proved result `freq_energy`: The squared-frequency multiplier times the field's Fourier norm square equals the sum of the Fourier norm squares of its coordinate derivatives almost everywhere.

**Fourier transforms preserve subtraction.** Proved result `hat_sub`: For two L2 real fields, the transform of their difference equals the difference of their transforms almost everywhere.

**Squared frequency is nonnegative.** Proved result `freqPow_two_nonneg`: The frequency weight at exponent two is nonnegative everywhere.

**A weak approximant bounds smoothing.** Proved result `bound_one`: For positive lambda, an L2 comparison field with square-integrable weak gradient bounds the target's Fourier smoothing energy by squared approximation error plus gradient energy divided by lambda.

**Source namespace:** `Breakdown.CellCert`.

**The smoothing lower interface holds.** Proved result `smoothingLower`: For a positive smoothing parameter and an L2 target field, the ratio-weighted Fourier energy is at most the smoothing form.

### Breakdown.FracCell.SpectralAssembly

Connects cell and tree certificates to fractional form nonnegativity and assembles block smoothing estimates with explicit inverse-square-root spectral tails.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralAssembly.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Assembly`.

**Cell matrices bound the fractional form.** Proved result `stateBound_of_cells`: For valid fractional form data with exponent between one and five quarters and a valid cell split, the assembled cell-plus-global state quadratic form is bounded above by the analytic form on admissible data.

**A tree certificate gives nonnegativity.** Proved result `formNonneg_of_tree`: A valid tree certificate whose cell, delay and global forms match a valid split proves nonnegativity of the fractional quadratic form for second-order fields, actuator coefficients and admissible gradient-class fields.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**The interval minimum interface holds.** Proved result `intervalMinimal_holds`: For a positive parameter, the smoothed-polynomial pairing is bounded by the squared error of any Lipschitz comparison function vanishing at both endpoints plus its derivative energy divided by that parameter.

**Interval smoothing decreases with scale.** Proved result `intervalMonotone_holds`: Increasing a positive smoothing parameter decreases the interval pairing of a polynomial with its smoothed value.

**The closed interval estimate holds.** Proved result `intervalClosed_holds`: For a polynomial of degree at most q and a positive parameter, the smoothed pairing is bounded by the explicit degree-q interval coefficient times the polynomial square integral.

**Assemble the local block bound.** Proved result `blockBound_of_parts`: The local block approximation and cylindrical integration interfaces imply the block spectral bound.

**Assemble the two geometric block cases.** Proved result `blockBound_of_cores`: The off-axis and on-axis core estimates imply the block spectral bound.

**A block bound gives spectral control.** Proved result `spectral_of_blocks_of_bound`: The block-bound interface and valid spectral data bound every row-combination smoothing form by its block coefficients and give the inverse-square-root tail above the cutoff.

**Local blocks give spectral control.** Proved result `spectral_of_blocks_of_parts`: Local block and cylindrical integration interfaces imply the row-combination smoothing bound and the cutoff-dependent inverse-square-root spectral tail.

**Axis cases give the spectral estimates.** Proved result `spectral_of_blocks_of_cores`: The off-axis and on-axis core interfaces imply both the row smoothing bound and the inverse-square-root tail estimate for valid spectral data.

**Shape and axis lift control the spectrum.** Proved result `spectral_of_blocks_of_leaves`: The shape-gradient and axis-lift interfaces imply the row smoothing bound and its explicit inverse-square-root tail for valid spectral data.

**Derivatives give spectral control.** Proved result `spectral_of_blocks_of_derivs`: The shape-slope, shape-derivative and lift-derivative interfaces imply both the block-diagonal smoothing bound and the spectral tail estimate.

**The block spectral estimates hold.** Proved result `spectral_of_blocks`: Valid spectral data yield the row-combination smoothing bound and the explicit inverse-square-root tail above the cutoff.

### Breakdown.FracCell.SpectralBlocks

Combines weakly differentiable block approximants using orthogonality of errors and gradients, then obtains the global block-diagonal smoothing bound.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocks.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocks`.

**An admissible smoothing approximant.** Definition `Adm`: This predicate requires an L2 vector field, a measurable derivative field with L2 coordinate columns and the weak-gradient identity.

**Entry-square energy gives L2 columns.** Proved result `comp_memLp`: A measurable derivative field with integrable entry square has every coordinate column in L2.

**L2 columns give finite gradient energy.** Proved result `entrySq_integrable`: If all coordinate columns of a derivative field lie in L2, its entry-square density is integrable.

**L2 vector pairings are integrable.** Proved result `inner_integrable`: The pointwise real inner product of two L2 vector fields is integrable.

**Weak gradients add.** Proved result `weak_add`: The sum of two L2 fields with L2 weak-gradient columns has weak gradient equal to the sum of their weak gradients.

**Zero is an admissible approximant.** Proved result `adm_zero`: The zero vector field and zero derivative field form an admissible smoothing approximant.

**Admissible approximants add.** Proved result `adm_add`: Adding two admissible vector-and-gradient pairs gives another admissible pair.

**Finite approximant sums are admissible.** Proved result `adm_sum`: A finite sum of admissible block approximants is admissible with derivative equal to the finite sum of their derivatives.

**Orthogonality removes cross integrals.** Proved result `diag_integral`: If all finite double-sum terms are integrable and off-diagonal integrals vanish, the double-sum integral reduces to the sum of diagonal integrals.

**Expand a finite vector norm square.** Proved result `normSq_sum`: The squared norm of a finite vector sum equals the double sum of all real inner products.

**Orthogonal L2 energies add.** Proved result `sq_sum`: A finite family of pairwise L2-orthogonal vector fields has total square integral equal to the sum of its separate square integrals.

**Expand the square of a gradient sum.** Proved result `entrySq_sum`: The entry square of a finite derivative-map sum equals the double sum of all entry inner products.

**Self entry pairing is gradient energy.** Proved result `entryInner_self`: The entry inner product of a linear map with itself equals its entry square.

**Orthogonal gradient energies add.** Proved result `grad_sum`: For derivative fields with L2 columns and zero off-diagonal entry inner integrals, the integrated energy of their finite sum equals the sum of their energies.

**Approximation cost bounds smoothing.** Proved result `form_le`: For positive lambda, the smoothing form is at most the squared approximation error plus the admissible approximant's gradient energy divided by lambda.

**Coordinate insertion is continuous.** Proved result `single_cont`: Inserting a real scalar into one coordinate of Euclidean three-space is continuous.

**Coordinate evaluation is continuous.** Proved result `coord_cont`: Every coordinate function on Euclidean three-space is continuous.

**The radial coordinate is continuous.** Proved result `radial_cont`: The cylindrical radial coordinate is continuous in the spatial point.

**The angular coordinate is measurable.** Proved result `angle_meas`: The cylindrical angle coordinate is measurable.

**Bivariate evaluation is continuous.** Proved result `twoVar_cont`: Evaluating a polynomial in radius and height is continuous in both variables.

**Each block solid is measurable.** Proved result `solid_meas`: Each of the two cylindrical solid pieces of a cell block is measurable.

**Spatial angular modes are measurable.** Proved result `trig_meas`: A sine or cosine mode evaluated at the scaled cylindrical angle is measurable.

**The cylindrical frame is measurable.** Proved result `frame_meas`: Each cylindrical frame-vector field is measurable.

**Block fields are measurable.** Proved result `blockField_meas`: Every field satisfying the block-field representation is almost-everywhere strongly measurable.

**Certificate row fields lie in L2.** Proved result `row_memLp`: Valid spectral data place every certificate row field in L2.

**Each block row combination lies in L2.** Proved result `part_memLp`: For valid spectral data, the linear combination of rows in any block lies in L2.

**Pair orthonormal row combinations.** Proved result `pairingMat`: For valid spectral data, the integral pairing of two finite row combinations equals their coefficient product sum with the Kronecker delta.

**Different blocks are orthogonal.** Proved result `part_orth`: Row combinations supported on distinct block indices are L2-orthogonal under valid spectral data.

**Block energy is a coefficient square sum.** Proved result `part_norm`: The square integral of a block row combination equals the sum of the squared coefficients of rows in that block.

**An approximation gives block pieces.** Proved result `piece_of_approx`: The block approximation interface implies the block-piece estimate.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Assemble the full block smoothing bound.** Proved result `blockBound_of`: The interval identity, minimum, monotonicity and closed estimates, the axis closed estimate and block approximation jointly imply the block spectral bound.

### Breakdown.FracCell.SpectralBlocksFamily

Defines angular-mode families for block errors and gradients and uses their orthogonality to assemble simultaneous block approximants.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksFamily.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**A measurable cylindrical mode field.** Definition `ModeField`: This predicate represents a field on the two block solids as cylindrical frame vectors with measurable radial-height coefficients multiplying the block's sine and cosine modes.

**A measurable cylindrical mode gradient.** Definition `ModeGradient`: This predicate represents a derivative map on the block solids by cylindrical frame tensor products with measurable radial-height coefficients and the block's sine and cosine modes.

**Separated mode families are orthogonal.** Proposition `ModeOrthStatement`: This proposition requires field and gradient orthogonality for L2 mode families whose supports are disjoint up to measure zero or whose cell geometry agrees but angular modes differ.

**A smoothing witness for one row block.** Proposition `BlockWitnessStatement`: This proposition supplies an L2 weakly differentiable approximation whose gradient and residual retain the block mode and whose error-plus-gradient cost is bounded by the block spectral coefficient times the row coefficient squares.

**Assemble orthogonal block witnesses.** Proved result `blockFamily_of_parts`: Mode-family orthogonality and the single-block witness interface imply the simultaneous block-family interface.

### Breakdown.FracCell.SpectralBlocksField

Lifts a local field approximation estimate to the spectral row-block witness, including the minimum with one and almost-everywhere representatives.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksField.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**The untruncated block spectral estimate.** Definition `blockInner`: The inner block estimate uses axis and height bounds on axis blocks, and the outer-to-inner radius ratio times radial, height and angular bounds on off-axis blocks.

**A local field approximation witness.** Proposition `FieldWitnessStatement`: This proposition supplies an L2 weakly differentiable approximation to any L2 block field, preserving mode structure of its gradient and error and bounding its cost by the untruncated block estimate times field energy.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocksField`.

**The block bound is capped at one.** Proved result `blockSpectral_eq`: The block spectral coefficient is the minimum of one and its untruncated inner estimate.

**Evaluate a polynomial combination.** Proved result `twoVar_comb`: Evaluating a finite real weighted combination of bivariate polynomials equals the same combination of their evaluations.

**The zero polynomial evaluates to zero.** Proved result `twoVar_zero`: The zero bivariate polynomial evaluates to zero at every radial-height point.

**Bivariate evaluation is continuous.** Proved result `twoVar_continuous`: Every bivariate real polynomial defines a continuous radial-height function.

**Linear combinations stay in one block.** Proved result `comb_blockField`: A finite weighted combination is a block field when every field with nonzero coefficient belongs to that same block.

**The radial coordinate is continuous.** Proved result `radial_continuous`: The cylindrical radial coordinate is continuous.

**The angular coordinate is measurable.** Proved result `angle_measurable`: The cylindrical angle coordinate is measurable.

**Coordinate insertion is continuous.** Proved result `single_continuous`: The map inserting a real value into one coordinate of Euclidean three-space is continuous.

**The cylindrical frame is measurable.** Proved result `frame_measurable`: Each cylindrical frame-vector field is measurable.

**Block solids are measurable.** Proved result `solid_measurable`: Each cylindrical solid piece of a cell block is measurable.

**Trigonometric modes are measurable.** Proved result `trig_measurable`: Each sine or cosine mode function is measurable.

**Block fields are measurable.** Proved result `blockField_measurable`: The block-field representation implies almost-everywhere strong measurability.

**L2 field pairings are integrable.** Proved result `pair_integrable`: The real inner product of two L2 vector fields is integrable.

**A normalized block field lies in L2.** Proved result `row_memLp`: A block field whose self L2 pairing is one belongs to L2.

**Parseval for orthonormal rows.** Proved result `comb_norm`: A finite combination of L2 orthonormal row fields has square integral equal to the sum of its real coefficient squares.

**Choose a pointwise mode representative.** Proved result `blockField_mode`: Every block field agrees almost everywhere with a field satisfying the pointwise cylindrical mode representation.

**A null correction has zero gradient.** Proved result `shift_witness`: Subtracting an almost-everywhere equal mode representative gives an L2 zero weak-gradient correction, whose residual recovers the mode representative with the original field's square energy.

**Zero satisfies every mode-gradient form.** Proved result `zero_modeGradient`: The zero derivative field satisfies the mode-gradient representation for every block.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Turn field witnesses into row witnesses.** Proved result `blockWitness_of_field`: The local field-witness interface implies the row-block witness interface, including the spectral minimum with one.

### Breakdown.FracCell.SpectralBlocksMode

Proves angular orthogonality of cylindrical block fields and combines the cylindrical change of variables with local spectral bounds.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksMode.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Cylindrical coordinates in three-space.** Definition `cylPoint`: The cylindrical point has Cartesian coordinates radius times cosine, radius times sine and height.

**The cylindrical integration formula.** Proposition `CylStatement`: This proposition rewrites the integral of an integrable spatial real function as the positive-radius radial-height integral of radius times its full-turn angular integral.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocksMode`.

**The cylindrical frame at one angle.** Definition `frameAt`: The frame consists of the radial unit vector, angular unit vector and fixed axial unit vector at the given angle.

**The spatial frame uses the polar angle.** Proved result `frame_eq`: The cylindrical frame vector at a spatial point is the angle-parametrized frame vector evaluated at that point's polar angle.

**The cylindrical frame is orthonormal.** Proved result `frame_inner`: At each angle, the inner product of two cylindrical frame vectors is one for equal indices and zero otherwise.

**Frame expansion preserves inner products.** Proved result `inner_frame_sum`: The inner product of two cylindrical-frame expansions equals the dot product of their real coefficient vectors.

**The first cylindrical coordinate.** Proved result `cyl0`: The first Cartesian coordinate of a cylindrical point is radius times cosine of angle.

**The second cylindrical coordinate.** Proved result `cyl1`: The second Cartesian coordinate of a cylindrical point is radius times sine of angle.

**The third cylindrical coordinate.** Proved result `cyl2`: The third Cartesian coordinate of a cylindrical point is its height.

**Recover positive cylindrical radius.** Proved result `radial_cyl`: At positive radius, the radial coordinate of a cylindrical point equals the supplied radius.

**Recover the principal cylindrical angle.** Proved result `angle_cyl`: At positive radius and an angle in the principal half-open interval from minus pi to pi, the polar angle of the cylindrical point is the supplied angle.

**Nonzero integer modes integrate to zero.** Proved result `trig_int`: A sine or cosine at nonzero integer frequency has integral zero over the full angular interval.

**Split a trigonometric product.** Proved result `trig_prod`: A product of two sine-or-cosine factors is a real linear combination of a trigonometric mode at the difference and at the sum of their arguments.

**Angular modes are continuous.** Proved result `trig_cont`: Sine and cosine modes with real angular frequency are continuous.

**Distinct angular modes are orthogonal.** Proved result `trig_orth`: Sine or cosine factors at distinct nonnegative integer frequencies have zero product integral over a full turn.

**Block membership is angle independent.** Proved result `solid_iff`: At positive radius, membership in either cylindrical block solid is independent of angle.

**A conditional vector as an indicator.** Proved result `ite_smul_one`: Selecting a vector or zero by a proposition equals multiplying that vector by the corresponding real zero-one indicator.

**The cylindrical shape-field formula.** Proved result `shape_cyl`: At positive radius and a principal angle, a shaped block field expands into radial-height solid indicators times its trigonometric cylindrical-frame coefficients.

**The radial-height pairing coefficient.** Definition `cylCoef`: The cylindrical coefficient sums products of the two block solid indicators and their frame-component amplitudes for fixed trigonometric indices.

**Separate the angular pairing factors.** Proved result `inner_cyl`: The inner product of two shaped fields at a cylindrical point is a finite sum of radial-height pairing coefficients times products of their angular modes.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Integrate the angular orthogonality.** Proved result `sameSolidOrth_of_cyl`: The cylindrical integration interface implies orthogonality of shaped fields on identical solids with different angular modes.

**Integrate the local block bound.** Proved result `blockBound_of_cyl`: The interval and axis estimates, local block approximation and cylindrical integration interface jointly imply the block spectral bound.

### Breakdown.FracCell.SpectralBlocksOrth

Combines angular-mode orthogonality on the same solid with support disjointness to obtain orthogonality of general separated block families.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksOrth.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Distinct modes on one solid.** Proposition `ModeOrthSameStatement`: This proposition requires L2 field and gradient orthogonality for block mode families with matching radial-height geometry and distinct angular modes.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocksOrth`.

**A mode field vanishes outside its solid.** Proved result `field_outside`: A field in the block mode family is zero at any point outside both block solid pieces.

**Mode gradients vanish off their solid.** Proved result `grad_outside`: A derivative field in the block mode family is zero at any point outside both block solid pieces.

**Disjoint solids separate almost surely.** Proved result `apart_ae`: If two block-solid unions intersect in measure zero, almost every point lies outside all pieces of at least one block.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Extend same-solid mode orthogonality.** Proved result `modeOrth_of_same`: The same-solid distinct-mode orthogonality interface implies the full mode-family orthogonality interface, including disjoint-support blocks.

### Breakdown.FracCell.SpectralBlocksParts

Specifies a family of mode-compatible weak approximants with mutually orthogonal errors and gradients and individual block cost bounds.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**An orthogonal family of block witnesses.** Proposition `BlockFamilyStatement`: This proposition supplies one L2 weakly differentiable approximant per row block, with pairwise orthogonal residuals and gradients and error-plus-gradient cost bounded by each block spectral coefficient times its coefficient-square sum.

### Breakdown.FracCell.SpectralBlocksPiece

Defines row-block pieces, their capped spectral coefficient and the local approximation conditions sufficient for simultaneous block estimates.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksPiece.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**The row combination in one block.** Definition `blockPart`: The block part sums the supplied row coefficients times the row fields whose block index equals the chosen block.

**Orthogonal approximants for block pieces.** Proposition `BlockPieceStatement`: This proposition supplies L2 weak approximants to every block part, with pairwise orthogonal errors and gradients and the capped block spectral error-plus-gradient bound.

**The block estimate before capping.** Definition `blockInnerValue`: The untruncated block value combines axis and height estimates on axis blocks and radius-scaled radial, height and angular estimates off axis.

**The spectral bound is capped at one.** Proved result `blockSpectral_eq_min_inner`: The block spectral coefficient equals the minimum of one and the untruncated block value.

**Approximation below the trivial bound.** Proposition `BlockApproxStatement`: This proposition supplies block approximants with cross-block field and gradient orthogonality and requires the untruncated approximation-cost bound only on active blocks where that bound is below one.

### Breakdown.FracCell.SpectralBlocksSplit

Uses shaped approximants and frame-column orthogonality to assemble block approximations, treating disjoint support and different angular modes separately.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralBlocksSplit.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**A field from cylindrical amplitudes.** Definition `shapeField`: The shaped field combines the two solid indicators with measurable radial-height amplitudes, block sine and cosine modes and cylindrical frame vectors.

**A block-shaped field representative.** Definition `IsBlockShaped`: This predicate requires a field to agree almost everywhere with a shaped block field whose radial-height amplitudes are measurable.

**Geometric or angular block separation.** Definition `BlocksApart`: Two blocks are separated when their solid unions intersect in measure zero or their radial-height geometry agrees and their angular modes differ.

**Separated shaped fields are orthogonal.** Proposition `ShapeOrthStatement`: This proposition requires L2 shaped fields from separated blocks to have zero integral inner product.

**A shaped local smoothing witness.** Proposition `BlockLocalStatement`: This proposition supplies a weak approximation on each active block whose untruncated bound is below one, retaining block shape for the approximant and its frame derivative columns and satisfying the local error-plus-gradient estimate.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocksSplit`.

**The radial frame in coordinates.** Proved result `frame_zero`: The radial frame vector is cosine times the first coordinate vector plus sine times the second.

**The angular frame in coordinates.** Proved result `frame_one`: The angular frame vector is minus sine times the first coordinate vector plus cosine times the second.

**The axial frame is the third coordinate.** Proved result `frame_two`: The axial frame vector equals the fixed third coordinate unit vector.

**Entry inner products in the frame.** Proved result `trace_frame`: The entry inner product of two linear maps equals the sum of inner products of their actions on the three cylindrical frame vectors.

**Bound frame derivatives by columns.** Proved result `frame_apply_le`: The norm of a linear map applied to any cylindrical frame vector is bounded by the sum of the norms of its three coordinate columns.

**Frame columns retain L2 regularity.** Proved result `frame_memLp`: A measurable derivative field with L2 coordinate columns has L2 columns in the cylindrical frame.

**Row blocks have shaped representations.** Proved result `part_shaped`: Under valid spectral data, every block row combination has the shaped-field representation for that block.

**An unused block has zero row part.** Proved result `part_zero`: If no row has the selected block index, the corresponding block part is identically zero.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Combine local shape and orthogonality.** Proved result `approx_of_split`: The local block witness and shaped-field orthogonality interfaces imply the simultaneous block approximation interface.

**Assemble the split-block estimate.** Proved result `blockBound_of_split`: The interval and axis estimates together with local approximation and shaped-field orthogonality imply the block spectral bound.

**Different modes on identical solids.** Proposition `SameSolidOrthStatement`: This proposition requires L2 shaped fields with identical radial-height geometry and distinct angular modes to be orthogonal.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.SpectralBlocksSplit`.

**Shaped fields vanish off block solids.** Proved result `shape_out`: A shaped field is zero outside the union of its block solid pieces.

**Disjoint blocks are orthogonal.** Proved result `disjoint_orth`: Shaped fields on block solids whose intersection has measure zero have zero integral inner product.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Combine support and mode orthogonality.** Proved result `shapeOrth_of_sameSolid`: The identical-solid angular orthogonality interface implies orthogonality for every separated pair of shaped blocks.

**Local witnesses close the block estimate.** Proved result `blockBound_of_local`: The interval and axis estimates, local block witnesses and identical-solid angular orthogonality jointly imply the block spectral bound.

### Breakdown.FracCell.SpectralDefs

Defines cylindrical polynomial row blocks and the certified spectral data: orthonormal rows, compatible geometry, interval and axis bounds and a positive cutoff.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralDefs.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**The principal cylindrical angle.** Definition `angleCoord`: The angular coordinate is the complex argument of the first two Cartesian coordinates.

**The spatial cylindrical frame.** Definition `frameVector`: The radial and angular vectors rotate the first two coordinate vectors by the point's polar angle, while the axial vector is the third coordinate vector.

**Evaluate the radial-height polynomial.** Definition `twoVarEval`: Bivariate evaluation first evaluates each coefficient polynomial at height and then evaluates the resulting polynomial at radius.

**Select cosine or sine.** Definition `trigMode`: Trigonometric index zero selects cosine and the other index selects sine.

**A polynomial cylindrical block field.** Definition `IsBlockField`: This predicate gives an almost-everywhere cylindrical representation with radial and height degrees bounded by the block degree and, on axis blocks, a radial factor in each transverse component.

**The certified spectral-data conditions.** Structure `IsSpectralData`: This structure requires orthonormal block-supported rows, valid separated block geometry, certified interval and axis estimates, an axis-gradient bound and a positive spectral cutoff.

### Breakdown.FracCell.SpectralTail

Extracts explicit inverse-square-root decay of block spectral coefficients above the cutoff from the closed interval and axis estimates.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SpectralTail.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**A negative half power is reciprocal root.** Proved result `rpow_neg_half_eq`: For a nonnegative real number, exponent minus one half equals the reciprocal of its square root.

**Scale a reciprocal square-root power.** Proved result `rpow_scaled`: For positive lambda and width, the negative half power of lambda times width squared equals reciprocal width times lambda to the negative half.

**Scale a quarter-width spectral argument.** Proved result `rpow_quarter`: For positive lambda and width, the negative half power of lambda times width squared divided by four equals two over width times lambda to the negative half.

**Trade inverse decay for a cutoff bound.** Proved result `inv_le_cross`: Above a positive cutoff, reciprocal lambda is at most the product of the cutoff and lambda negative-half powers.

**Expand the scaled interval tail formula.** Proved result `intervalClosed_quarter`: For positive parameter and width, the closed interval bound at the quarter-width-scaled argument splits into the explicit inverse-square-root and reciprocal-parameter terms.

**Expand the scaled axis tail formula.** Proved result `axisClosed_scaled`: For positive parameter and width, the closed axis bound at the width-scaled argument splits into its explicit inverse-square-root and gradient-bound reciprocal terms.

**An axis-gradient bound is nonnegative.** Proved result `gradient_nonneg`: Any constant satisfying the axis-gradient bound is nonnegative.

**A frequency-over-scale ratio bound.** Proved result `ratio_le`: For positive lambda and nonnegative x, the smoothing ratio is at most x divided by lambda.

**The off-axis block has a spectral tail.** Proved result `off_axis_bound`: Above a positive cutoff and for a nondegenerate cell with positive inner radius, the off-axis block bound is at most the explicit geometry-dependent constant times lambda to the negative half.

**The axis block has a spectral tail.** Proved result `on_axis_bound`: Above a positive cutoff satisfying the radial width threshold and with a nonnegative axis-gradient constant, the axis block bound is at most the explicit constant times lambda to the negative half.

**The spectral tail interface holds.** Proved result `tail_holds`: The on-axis and off-axis closed estimates give the certified inverse-square-root tail for each block spectral coefficient.

### Breakdown.FracCell.SplitRows

Bounds the row coefficients of the fractional split field by its split energy using Fourier symbols, finite smoothing levels and an integrated spectral tail.

Fractional dissipation analysis for exponents between one and five quarters; it connects the cell spectral certificates to the fractional split-row estimate rather than asserting an ordinary-viscosity paper lemma.

Source: `lean/Breakdown/FracCell/SplitRows.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Internal.SplitRows`.

**A fractional power has a smoothing tail.** Proved result `tail_le`: For exponent between zero and one, positive cutoff and x above the cutoff, the power increment is bounded by the lower integral of the exponent-weighted smoothing ratio over scales above the cutoff.

**Control the increment of a rational term.** Proved result `ratio_step`: If both numerator scale and positive denominator offset increase, the new quadratic-over-linear ratio is at most the old ratio plus the numerator-scale increment.

**The ratio increases with frequency.** Proved result `ratioFn_mono`: For positive lambda, the smoothing ratio is monotone in its nonnegative frequency argument.

**The smoothing ratio is nonnegative.** Proved result `ratioFn_nonneg`: For positive lambda and nonnegative frequency, the smoothing ratio is nonnegative.

**The smoothing ratio is at most one.** Proved result `ratioFn_le_one`: For positive lambda and nonnegative frequency, the smoothing ratio is bounded above by one.

**The split viscosity is positive.** Proved result `splitVisc_pos`: Valid fractional cell data have strictly positive split viscosity.

**The spectral cutoff is positive.** Proved result `cutoff_pos`: Valid fractional cell data have a strictly positive spectral cutoff.

**The finite level sum is monotone.** Proved result `levelSum_mono`: For valid fractional cell data, the finite smoothing-level sum is monotone on nonnegative frequencies.

**The finite level sum is nonnegative.** Proved result `levelSum_nonneg`: For valid fractional cell data, the finite smoothing-level sum is nonnegative at nonnegative frequencies.

**A level-plus-tail symbol bound.** Proved result `symbol_le`: For fractional exponent between one and five quarters, the ratio symbol at positive frequency is bounded by the finite level sum plus the continuous high-scale smoothing tail.

**A weighted pairing-square estimate.** Proved result `amgm_pt`: An absolute pairing bound and positive energy weight and balancing parameter bound the weighted pairing by the balanced arithmetic mean of the two weighted square terms.

**Rewrite the fractional frequency power.** Proved result `freqPow_pow`: The frequency power at exponent twice alpha minus two equals the squared-frequency weight raised to alpha minus one.

**Squared frequency is nonnegative.** Proved result `freqPow_nonneg`: The frequency weight at exponent two is nonnegative everywhere.

**Squared frequency is positive off zero.** Proved result `freqPow_pos`: The frequency weight at exponent two is strictly positive away from the zero frequency.

**Squared frequency is measurable.** Proved result `measurable_freqPow`: The squared-frequency weight is measurable.

**The full fractional symbol is positive.** Proved result `full_pos`: For valid fractional cell data, the full symbol is strictly positive at every nonzero frequency.

**The fractional ratio is nonnegative.** Proved result `ratio_nonneg`: For valid fractional cell data, the ratio symbol is nonnegative at nonzero frequencies.

**Zero frequency is negligible.** Proved result `ae_ne_zero'`: Almost every spatial-frequency point is nonzero.

**The Fourier split-field pairing.** Proved result `pair_split`: The weak fractional-power symbol interface identifies an L2 test pairing with the split field as the integrable Fourier pairing weighted by frequency to alpha minus one minus split viscosity.

**L2 pairing respects row combinations.** Proved result `pair_sum`: Pairing an L2 field with a finite real linear combination of L2 row fields equals the corresponding linear combination of row pairings.

**A certificate row combination lies in L2.** Proved result `memLp_rows`: Every finite real row combination from valid fractional cell data belongs to L2.

**Row Fourier energy is a coefficient norm.** Proved result `norm_rows`: For valid fractional cell data, the Fourier square integral of a real row combination equals the sum of its coefficient squares.

**The smoothing form is nonnegative.** Proved result `smoothingForm_nonneg`: For positive lambda, the smoothing form of any field is nonnegative.

**The spectral bound controls one level.** Proved result `level_pt`: The smoothing lower-bound interface and valid fractional cell data give integrability and the block-diagonal coefficient bound for a row combination's ratio-weighted Fourier energy at each positive scale.

**Integrate the high-scale spectral tail.** Proved result `tail_lint`: The smoothing lower-bound interface and a nonnegative tail constant bound the row combination's continuous spectral tail by its coefficient-square sum times the explicit cutoff power and exponent factor.

**Integrate the finite smoothing levels.** Proved result `level_int`: The smoothing lower-bound interface makes the finite-level-weighted Fourier energy integrable and bounds it by the row coefficient squares weighted by the base and certified level coefficients.

**Bound the complete ratio-symbol energy.** Proved result `ratio_int`: For valid fractional cell data and nonnegative tail constant, the ratio-weighted row Fourier energy is integrable and bounded by the combined finite-level and explicit high-scale tail coefficient.

**Optimize a balanced square inequality.** Proved result `final_real`: If nonnegative E and B satisfy the stated balanced quadratic inequality for every positive parameter, then R is at most B times E.

**The split energy is a Fourier square.** Proved result `energy_eq`: The second-symbol energy and weak fractional-power symbol interfaces identify the nonnegative split energy squared with the integral of the full symbol times the second-derivative Fourier square.

**A row witness gives nonnegative tail.** Proved result `tailConst_nonneg`: For valid fractional cell data with a supplied row index, the tail constant is nonnegative.

**The split field satisfies the row bound.** Proved result `splitRows_main`: For exponent between one and five quarters, the smoothing and Fourier-symbol interfaces bound the weighted row size of the split field by the split constant times its split energy.

**Source namespace:** `Breakdown.CellCert`.

**Assemble the fractional row estimate.** Proved result `splitRows_of`: The smoothing lower-bound, second-symbol energy and weak fractional-power symbol interfaces imply the fractional split-row estimate.

### Breakdown.FracCell.SplitRowsTail

Proves the scalar fractional-power increment bound over a finite smoothing-scale interval used to control the continuous row spectral tail.

A scalar estimate in the fractional split-row route for exponent alpha minus one; its application is recorded separately from the ordinary Navier-Stokes proof route.

Source: `lean/Breakdown/FracCell/SplitRowsTail.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Internal.SplitRowsTail`.

**Bound a power increment by a finite tail.** Proved result `tail_real`: For exponent strictly between zero and one and x above a positive cutoff c, the increment x to that exponent minus c to that exponent is bounded by the exponent-weighted smoothing-ratio integral from c to x squared divided by c.

### Breakdown.FracCell.StAngularHeightMode

States the angular derivative relations for the height-gradient column, including the cylindrical frame-rotation corrections.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/StAngularHeightMode.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Angular identities for the height column.** Proposition `AngularHeightModeStatement`: This proposition requires radius times each angular derivative mode of the height-gradient column to equal imaginary frequency times that column, with the radial-angular rotation corrections, almost everywhere at positive radius for second-order fields.

### Breakdown.FracCell.StAngularMode

States weighted mode integrability and the cylindrical angular velocity-gradient relation used by the finite cell constraints.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/StAngularMode.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Weighted field modes are integrable.** Proposition `ModeIntegrableStatement`: This proposition requires line-weighted velocity and gradient modes of every second-order field to be integrable on every valid cell rectangle.

**The angular velocity-gradient identity.** Proposition `AngularModeStatement`: This proposition requires radius times the angular gradient column to equal imaginary frequency times velocity plus the radial-angular frame rotation almost everywhere at positive radius.

### Breakdown.FracCell.StAssembly

States the analytic decomposition into cell, exterior and global forms and the linear closure properties of admissible field tuples.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/StAssembly.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Assembly`.

**Cell and exterior pieces bound the form.** Proposition `QuadFormSplitStatement`: This proposition bounds the sum of all cell pieces, the exterior piece and the global matrix value by the fractional quadratic form for a valid cell split and admissible data.

**Real linearity of admissible tuples.** Proposition `AdmissibleLinearStatement`: This proposition requires the zero tuple to be admissible and admissibility to be preserved by addition and real scalar multiplication.

### Breakdown.FracCell.StCellBound

Defines the angular local density and wave coupling, plus the symmetry and mode-expansion interfaces that connect cell solids to the finite cell form.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/StCellBound.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The cell weight is angle independent.** Definition `IsAxisymmetricWeight`: This predicate requires the spatial weight on every circle over the cell rectangle to equal the sampled radial-height weight.

**The model has the required mirror parity.** Definition `IsModelMirror`: This predicate requires velocity, strain, actuator and pin fields to obey their even mirror transformations and curl and curl-gradient fields their odd transformations away from the mirror plane inside the cell solid.

**The full local density of one mode.** Definition `modeLocalDensity`: The mode local density combines weighted second-derivative and curl-gradient squares with the local density form of the gradient mode.

**The complete angular wave coupling.** Definition `modeCoupling`: The mode coupling is the real iterated wave-form series using original gradient and velocity modes at both angular indices.

**The angular matrix-field pairing.** Definition `modeFieldPair`: The field pairing is the real series of same-frequency entry pairings between a gradient field's modes and the supplied matrix field's modes.

**The density mode integral on a solid.** Proposition `CellDensityModesStatement`: This proposition expresses the cell-solid density and each pin-field integral as four pi times their radial-weighted mode integrals under cell geometry, axisymmetric weight, model mirror symmetry and admissibility hypotheses.

**The cell form bounds its split piece.** Proposition `CellFormBoundStatement`: This proposition bounds four pi times the finite cell form by the matching cell contribution when the solid agrees almost everywhere with the selected split cell and the row memberships agree.

### Breakdown.FracCell.StCentrePairing

States the integration identity that converts the centre-field interaction into strain and curl-gradient terms.

Appendix B cell coercivity; shared fractional formulation.

Source: `lean/Breakdown/FracCell/StCentrePairing.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert`.

**Centre-field pairing identity.** Proposition `CentreIdentityStatement`: The interface equates the centre interaction paired with the negative second trace to the integral of the strain and curl-gradient form for an admissible second-order field.

### Breakdown.FracCell.StCircleWeak

States angular integration by parts for weakly differentiable fields on almost every cylindrical coordinate circle.

Appendix B cylindrical Fourier analysis.

Source: `lean/Breakdown/FracCell/StCircleWeak.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellEnergy`.

**Weak differentiation around a circle.** Proposition `CircleWeakStatement`: The interface transfers a weak Cartesian gradient to angular integration by parts against smooth periodic weights on almost every positive-radius circle.

### Breakdown.FracCell.StClauses

States derivative agreement, fractional-energy identities, and model, row, pin, and smoothing bounds needed to convert cell data into a fractional certificate.

Appendix B reduction to analytic coercivity, with fractional hypotheses.

Source: `lean/Breakdown/FracCell/StClauses.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert`.

**Chosen derivatives agree almost surely.** Proposition `ChosenAgreeStatement`: The interface requires chosen first and second derivatives to agree almost everywhere with any supplied second-order-field witnesses.

**Average gradients without changing rows.** Proposition `ClassAverageRowsStatement`: The interface requires a symmetry-class gradient whose addition leaves every certificate row unchanged.

**Second-derivative energy identities.** Proposition `SecondIdentityStatement`: The interface identifies Hessian and curl-gradient energies with the Laplacian energy, and curl energy with gradient energy, for second-order fields.

**Cross-product decomposition.** Proposition `CrossIdentityStatement`: The interface expresses the symmetric transport term through curls, cross products and adjoint derivatives.

**Model-field local regularity.** Proposition `ModelRegularStatement`: For valid fractional cell data with exponent between one and five quarters, the interface requires the model field to be measurable and locally square-integrable.

**Model coercivity estimate.** Proposition `ModelLowerStatement`: For admissible fields and gradient perturbations, the interface bounds the squared certificate size by the model form, row norm and weighted pin squares.

**Model form versus local pairing.** Proposition `ModelFormStatement`: For a weak fractional-power field with square-integrable drift, the interface bounds the model form after the potential loss by the local-field pairing.

**Model rows versus local rows.** Proposition `ModelFieldStatement`: For a weak fractional-power field with square-integrable drift, the interface requires a gradient correction controlling the difference between local and model rows.

**Model pins versus exact pins.** Proposition `ModelPinStatement`: For a weak fractional-power field with square-integrable drift, the interface bounds the difference between model pins and derivative pins by the pin-loss allowance.

**Rows of the fractional remainder.** Proposition `SplitRowsStatement`: The interface bounds the split-field rows by the split constant times the fractional split energy.

**Smoothing dominates its Fourier form.** Proposition `SmoothingLowerStatement`: For positive smoothing scale and an L² field, the interface bounds the Fourier multiplier energy by the smoothing form.

### Breakdown.FracCell.StCoordsProof

States the coordinate relations and the comparison between the exact matrix formula and cell energy.

Appendix B coordinate elimination and exact cell matrices.

Source: `lean/Breakdown/FracCell/StCoordsProof.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Radial coefficient relations.** Proposition `RelRadialCoefStatement`: The interface requires every radial coefficient relation to annihilate the true data of an admissible field.

**Height coefficient relations.** Proposition `RelHeightCoefStatement`: The interface requires every height coefficient relation to annihilate the true data of an admissible field.

**Angular turning relations.** Proposition `RelTurnStatement`: The interface requires every angular turning relation to annihilate the true data of an admissible field.

**Trace relations.** Proposition `RelTraceStatement`: The interface requires every trace relation to annihilate the true data of an admissible field.

**Zero-mode relations.** Proposition `RelZeroModeStatement`: The interface requires every zero-mode relation to annihilate the true data of an admissible field.

**Radial-side relations.** Proposition `RelRadialSideStatement`: The interface requires every radial-side relation to annihilate the true data of an admissible field.

**Height-side relations.** Proposition `RelHeightSideStatement`: The interface requires every height-side relation to annihilate the true data of an admissible field.

**Axis relations.** Proposition `RelAxisStatement`: The interface requires every axis relation to annihilate the true data of an admissible field.

**Stream-function relations.** Proposition `RelStreamStatement`: The interface requires every stream-function relation to annihilate the true data of an admissible field.

**Side-splitting relations.** Proposition `RelSideSplitStatement`: The interface requires every side-splitting relation to annihilate the true data of an admissible field.

**Conjugation preserves chosen coordinates.** Definition `IsConjClosedParam`: The predicate requires both skeleton and solved coordinate sets to be closed under conjugation.

**Exact formula bounds the cell form.** Proposition `ExactFormulaBoundStatement`: With valid formula inputs, supported far-field data and positive split viscosity, the interface bounds the exact quadratic formula by the cell form divided by that viscosity.

### Breakdown.FracCell.StCornerModesOpen

States the weak radial and height derivative identities used to define corner traces.

Appendix B cell corner data.

Source: `lean/Breakdown/FracCell/StCornerModesOpen.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Height modes remain integrable at axis.** Proposition `ModeHeightAxisStatement`: The interface requires height-gradient modes of a second-order field to be integrable on bounded radial-height rectangles that meet the axis.

**Weak derivatives of cylindrical modes.** Proposition `ModeWeakIdentityStatement`: Away from the axis, the interface identifies weak radial, height and mixed derivatives of velocity and gradient modes.

### Breakdown.FracCell.StCylModeWeak

States the changes of variables that transport Cartesian weak derivatives into cylindrical Fourier modes.

Appendix B cylindrical coordinates and weak mode traces.

Source: `lean/Breakdown/FracCell/StCylModeWeak.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Cylindrical modes have weak derivatives.** Proposition `CylModeWeakStatement`: The interface transfers a locally integrable weak gradient to radial and height derivatives of angular Fourier coefficients against smooth tests supported away from the axis.

**Cylindrical change of variables.** Proposition `CylChangeStatement`: The interface expresses an integrable three-dimensional field integral as a radial-height integral of angular integrals with the radial Jacobian.

**Weak derivatives away from the axis.** Proposition `AxisWeakStatement`: The interface gives integrability and radial-height integration identities for weighted cylindrical test functions supported away from the axis.

### Breakdown.FracCell.StEnergyProof

States how finite coordinate forms reproduce the cell's component energies and bound its local quadratic form.

Appendix B finite-dimensional cell energy.

Source: `lean/Breakdown/FracCell/StEnergyProof.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellEnergy`.

**Data representing a second-order field.** Structure `EnergySetting`: The structure packages a valid cell, bases and scalars with a second-order field and coordinates representing its modes.

**Measurable bounded class errors.** Definition `IsClassRegular`: The predicate requires each class-error function to be measurable and uniformly bounded on the cell rectangle.

**Linear combination of strain modes.** Definition `strainField`: The definition contracts the gradient Fourier mode with a specified complex matrix.

**Radial derivative combination.** Definition `radialField`: The definition contracts the radial gradient mode with a specified complex matrix.

**Height derivative combination.** Definition `heightField`: The definition contracts the height gradient mode with a specified complex matrix.

**Angular derivative combination.** Definition `angularField`: The definition contracts the angular gradient mode with a specified complex matrix.

**Radial matrix equals radial energy.** Proposition `ComponentRadialStatement`: For represented second-order data, the interface identifies the radial projection and boundary quadratic forms with the radial energy.

**Height matrix equals height energy.** Proposition `ComponentHeightStatement`: For represented second-order data, the interface identifies the height projection and boundary quadratic forms with the height energy.

**Angular derivative in the moving frame.** Proposition `AngularFrameStatement`: For represented second-order data, the interface expresses angular derivative modes through the angular frame combination almost everywhere on the cell.

**Angular matrix equals angular energy.** Proposition `ComponentAngularStatement`: The interface identifies the axis or off-axis angular quadratic form with angular energy for represented second-order data.

**Top matrix equals top-mode energy.** Proposition `TopFormStatement`: The interface identifies the top quadratic form with the sum of component top-mode energies.

**Class matrix equals class-error term.** Proposition `ClassFormStatement`: For represented fields and regular class errors, the interface identifies the class quadratic form with the analytic class-error term.

**Pairing matrix equals local interaction.** Proposition `PairFormStatement`: The interface identifies the pairing quadratic form with the local interaction form for represented fields.

**Local matrix separates cross terms.** Proposition `CrossFormStatement`: The interface splits the local quadratic form into energy, class and pairing forms plus the linear multiplier and pin term.

**Energy matrix equals analytic energy.** Proposition `EnergyFormStatement`: The interface identifies the complete energy quadratic form with the cell's analytic energy term.

**Local matrix bounds local cell energy.** Proposition `LocalFormBoundStatement`: For valid cell data, regular class errors and represented second-order fields, the interface bounds the local matrix value by the local cell form.

### Breakdown.FracCell.StExterior

States Hardy-type bounds on exterior ray regions and the resulting nonnegative exterior contribution.

Appendix B exterior coercivity.

Source: `lean/Breakdown/FracCell/StExterior.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Exterior`.

**Exterior of a radial threshold.** Definition `rayRegion`: The definition selects points whose norm exceeds the specified direction-dependent radius.

**Hardy inequality on an exterior ray.** Proposition `RayLineStatement`: For a positive lower radius and a compactly supported C¹ function, the interface bounds its squared integral by four times its weighted derivative energy.

**Hardy bound for smooth exterior fields.** Proposition `RaySmoothStatement`: For a bounded positive radius constant along rays, the interface gives the inverse-square Hardy bound for smooth compactly supported vector fields.

**Hardy bound for weak exterior fields.** Proposition `RayWeakStatement`: For an L⁶ field with square-integrable weak gradient, the interface gives integrability and the inverse-square Hardy bound outside a bounded positive ray threshold.

**Pointwise exterior lower bound.** Proposition `ExteriorPointwiseStatement`: For valid exterior data and admissible fields, the interface bounds the local density below by gradient energy minus the wave and mean curl-gradient losses.

**Exterior energy is nonnegative.** Proposition `ExteriorNonnegStatement`: The interface requires the integrated local density outside the cell region to be nonnegative under the exterior certificate conditions.

**Exterior split is nonnegative.** Proposition `ExteriorPartNonnegStatement`: When the cell union equals the certificate region, the interface requires the split exterior contribution to be nonnegative.

### Breakdown.FracCell.StFormulaProof

States synthesis and polarization facts used to construct exact cell matrices.

Appendix B exact quadratic formula.

Source: `lean/Breakdown/FracCell/StFormulaProof.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Coordinates synthesize the low modes.** Proposition `SynthesisStatement`: For valid cell data and admissible fields, the interface reconstructs resolved low strain and velocity modes from the augmented vector.

**Response coefficients are linear.** Proposition `YCoefLinearStatement`: The interface writes each strain and velocity response coefficient as a linear combination of augmented coordinates.

**A function represented by a matrix.** Definition `IsRealQuadratic`: The predicate requires a real-valued function to equal a matrix quadratic form on every coordinate vector.

**Polarization matrix.** Definition `polarized`: The definition recovers matrix entries from the function's values on pairs of coordinate vectors and their sum.

**Polarization recovers the quadratic form.** Proposition `PolarizationStatement`: The interface requires the polarization matrix to reproduce any function represented by a real matrix quadratic form.

**The exact formula is quadratic.** Proposition `FormulaQuadraticStatement`: The interface requires the cell formula to be a real quadratic function whenever its coordinate-to-data map is linear.

### Breakdown.FracCell.StHeightModeIbp

States height integration by parts in the cell's weighted mode representation.

Appendix B height-side and coefficient relations.

Source: `lean/Breakdown/FracCell/StHeightModeIbp.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Height integration by parts.** Proposition `HeightModeIbpStatement`: For second-order fields and a valid cell, the interface transfers a height derivative from a vanishing-endpoint test to the gradient mode and supplies the needed integrability.

### Breakdown.FracCell.StMesh

States how local cell coordinates and pressure gauges assemble into one global moment vector.

Appendix B mesh gluing and pressure gauges.

Source: `lean/Breakdown/FracCell/StMesh.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellCoordinates`.

**Global moments recover local slots.** Proposition `MeshSkeletonSlotStatement`: The interface requires each cell's coordinate map applied to canonical global moments to recover its local values.

**Root pressure gauges vanish.** Proposition `MeshRootZeroStatement`: The interface requires every designated root pressure datum to vanish after the canonical gauge shift.

**Edge gauges have the prescribed jump.** Proposition `MeshEdgeJumpStatement`: The interface requires the canonical right gauge to equal the left gauge plus the specified edge jump.

**Canonical pressure gauges are linear.** Proposition `MeshGaugeLinearStatement`: The interface requires both canonical pressure gauges to respect real linear combinations of admissible fields.

**Canonical moments are linear.** Proposition `MeshMomentLinearStatement`: The interface requires canonical moments to preserve zero, addition and scalar multiplication and to recover each multiplier coordinate.

**Radial flux is a stream difference.** Proposition `FluxRadialStatement`: For an admissible field and a radial segment away from the axis, the interface expresses its zero-mode radial flux moment as a difference of stream values.

**Height flux is a stream difference.** Proposition `FluxHeightStatement`: For an admissible field and a height segment, the interface expresses the radial-weighted axial flux moments as a difference of stream values.

**Stream function vanishes on the plane.** Proposition `StreamPlaneStatement`: The interface requires the stream value of an admissible field to vanish on the symmetry plane for nonnegative radius.

### Breakdown.FracCell.StSpectral

States interval and axis estimates that bound row smoothing and its spectral tail.

Appendix B spectral bounds for row families.

Source: `lean/Breakdown/FracCell/StSpectral.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Interval resolvent remainder.** Definition `intervalResolvent`: The definition subtracts the interval-smoothed polynomial from the polynomial itself.

**Resolvent identity with zero endpoints.** Proposition `IntervalIdentityStatement`: For positive scale, the interface gives twice differentiability, zero boundary values and the interval resolvent energy identity.

**Resolvent minimizes the interval energy.** Proposition `IntervalMinimalStatement`: For positive scale, the interface bounds the smoothed polynomial pairing by the error-plus-derivative energy of every Lipschitz competitor with zero endpoints.

**Interval smoothing decreases with scale.** Proposition `IntervalMonotoneStatement`: The interface requires the smoothed polynomial pairing to decrease as a positive scale increases.

**Closed bound for interval polynomials.** Proposition `IntervalClosedStatement`: The interface bounds the interval-smoothed pairing by the closed constant times polynomial L² energy at the declared degree.

**Closed bound at the cylindrical axis.** Proposition `AxisClosedStatement`: Given the polynomial gradient bound and scale at least 24, the interface supplies a Lipschitz competitor attaining the stated axis-functional bound.

**Blockwise smoothing bound.** Proposition `BlockBoundStatement`: For valid spectral data and positive scale, the interface bounds smoothing of a row combination by the weighted sum of its squared coefficients.

**Spectral tail decays as inverse root.** Proposition `TailStatement`: Above the cutoff, the interface bounds each block's spectral value by its tail constant times the inverse square root of scale.

### Breakdown.FracCell.StWeightedInverseSquare

States weighted mode Hardy estimates used in the adjoint reduction.

Appendix B adjoint and angular-mode estimates.

Source: `lean/Breakdown/FracCell/StWeightedInverseSquare.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Weighted inverse-square mode energy.** Definition `modeEnergy`: The definition sums horizontal and vertical angular-mode energies with their shifted angular weights and inverse-square spatial weight.

**Absolute mode-pairing sum.** Definition `modePairing`: The definition sums the radial integrals of products of horizontal and vertical angular-mode magnitudes.

**Mode energy is bounded by the gradient.** Proposition `ModeInverseSquareStatement`: The interface bounds the weighted inverse-square mode energy of a second-order field by its gradient energy.

**Physical pairing is bounded modewise.** Proposition `ModePairingStatement`: For a second-order field and a measurable forcing with square-integrable radial weight, the interface bounds the absolute physical pairing by the mode-pairing sum.

**Angular modes are measurable.** Proposition `ModeMeasurableStatement`: The interface requires each angular mode of a measurable scalar field to be measurable on the positive-radius half-plane.

**Distance to the cylindrical axis.** Definition `ringRadius`: The definition takes the square root of the sum of squares of the first two coordinates.

**Cylindrical orthonormal frame.** Definition `ringFrame`: The definition gives radial, angular and axial frame vectors through the cylindrical radius.

**Squared gradient energy in one mode.** Definition `frameModeSq`: The definition sums horizontal and vertical angular-mode squares of the gradient applied to the three cylindrical frame vectors.

**Gradient modes obey a summed bound.** Proposition `GradientModeSumStatement`: The interface bounds the sum of cylindrical-frame gradient-mode energies by the physical gradient energy.

**Inverse-square bound in each mode.** Proposition `FrameInverseSquareStatement`: The interface bounds each weighted horizontal and vertical inverse-square mode energy by its cylindrical-frame gradient energy.

### Breakdown.FracCell.StateBound

Adds the cell matrix bounds and exterior nonnegativity to obtain the global state estimate.

Appendix B assembly of cell coercivity.

Source: `lean/Breakdown/FracCell/StateBound.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Assembly`.

**Quadratic forms add with their matrices.** Proved result `quadValue_add_matrix`: The quadratic value of a sum of matrices equals the sum of their quadratic values.

**Finite sums of quadratic forms.** Proved result `quadValue_sum_matrix`: The quadratic value of a finite matrix sum equals the finite sum of quadratic values.

**Cell bounds imply the state bound.** Proved result `stateBound_of_cells_of`: Given the quadratic splitting interface and a valid cell split, the sum of cell and global matrix values is bounded by the certificate quadratic form.

### Breakdown.FracCell.StatementDefs

Defines fractional cell geometry, Fourier modes, moment coordinates, spectral bounds, profile and adjoint encodings, and the matrix conditions used by the cell certificate.

Appendix B cell certificate definitions and shared fractional generalization.

Source: `lean/Breakdown/FracCell/StatementDefs.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert`.

**Matrix entry in the Cartesian basis.** Definition `entry`: The definition reads the chosen coordinate of a linear map applied to a Cartesian unit vector.

**Curl encoded by a derivative matrix.** Definition `curlOf`: The definition contracts derivative entries with permutation signs to form the curl vector.

**Vector cross product.** Definition `crossVec`: The definition gives the three coordinate components of the vector cross product.

**Symmetric part of a derivative.** Definition `symPart`: The definition averages a linear map and its adjoint.

**Curl gradient from second derivatives.** Definition `curlGradMatrix`: The definition contracts the second derivative tensor with permutation signs to form the curl-gradient matrix.

**Resolvent ratio.** Definition `ratioFn`: The definition is the scalar ratio x divided by the sum of the scale and x.

**Source namespace:** `Breakdown.CellCert.FracCellData`.

**Derivative of the centre field.** Definition `centreGrad`: The definition takes the Fréchet derivative of the centre velocity field.

**Curl of the centre field.** Definition `centreCurl`: The definition forms the curl from the centre field's derivative.

**Strain of the centre field.** Definition `centreStrain`: The definition takes the symmetric part of the centre field's derivative.

**Curl gradient of the centre field.** Definition `centreCurlGrad`: The definition forms the curl-gradient matrix from the centre's supplied second derivative.

**Error in the model strain.** Definition `strainError`: The definition subtracts the model strain from the centre strain.

**Error in the model curl gradient.** Definition `curlGradError`: The definition subtracts the model curl gradient from the centre curl gradient.

**Velocity error inside the cells.** Definition `velocityError`: The definition restricts the centre-minus-model velocity error to the cell region and sets it to zero outside.

**Curl error inside the cells.** Definition `curlError`: The definition restricts the centre-minus-model curl error to the cell region and sets it to zero outside.

**Fractional spectral gap symbol.** Definition `gapSymbol`: The definition subtracts the split viscosity from the fractional frequency power.

**Gap symbol with coercivity correction.** Definition `fullSymbol`: The definition adds the reduced-coercivity and inverse-frequency correction to the gap symbol.

**Squared gap divided by full symbol.** Definition `ratioSymbol`: The definition divides the square of the gap symbol by the full symbol.

**Finite resolvent-level combination.** Definition `levelSum`: The definition adds the base coefficient to the finite weighted sum of resolvent ratios.

**Source namespace:** `Breakdown.CellCert.Finite`.

**Positivity on a subspace.** Definition `IsPositiveOn`: The predicate requires the matrix quadratic value to be positive on every nonzero vector of the specified subspace.

**Tree of elimination matrices.** Structure `TreeCertificate`: The structure records cell matrices, parent nodes, ranks, eliminated coordinates, front matrices and the root global form.

**Source namespace:** `Breakdown.CellCert.Finite.TreeCertificate`.

**Input matrix at a tree node.** Definition `nodeInput`: The definition adds the matrices of cells assigned to a node and the front matrices of its children.

**A coordinate eliminated in the tree.** Definition `IsEliminatedSomewhere`: The predicate records that a coordinate belongs to the eliminated set of at least one node.

**Subspace left at the tree root.** Definition `rootSpace`: The definition takes the subspace whose coordinates eliminated anywhere in the tree are zero.

**Source namespace:** `Breakdown.CellCert.Finite`.

**Validity of an elimination tree.** Structure `IsTreeCertificate`: The structure requires symmetry, acyclic ranked parent relations, disjoint elimination, front lower bounds and sufficient positive dimension at the root.

**Source namespace:** `Breakdown.CellCert.Assembly`.

**Velocity and derivative field tuple.** Abbreviation `FieldTuple`: The abbreviation packages velocity, first and second derivatives, multipliers and a gradient field.

**Cell splitting and global coordinates.** Structure `CellSplit`: The structure records the cells, row assignments, global moments, multiplier slots, cell matrices and delayed forms.

**Source namespace:** `Breakdown.CellCert.Assembly.CellSplit`.

**Global multiplier and pin penalties.** Definition `globalMatrix`: The definition is the diagonal matrix subtracting multiplier-size and inverse pin-weight penalties from the global form.

**Source namespace:** `Breakdown.CellCert.Exterior`.

**Data for the exterior estimate.** Structure `ExteriorData`: The structure records the ray boundary and strain, curl-gradient and splitting bounds used outside the cells.

**Source namespace:** `Breakdown.CellCert.Exterior.ExteriorData`.

**Exterior gradient coefficient.** Definition `gradientCoef`: The definition combines the curl weight, coercive weight and exterior strain and wave losses into the gradient coefficient.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Vector in the cylindrical frame.** Definition `frameVec`: The definition takes a vector's radial, angular and axial inner products.

**Matrix in the cylindrical frame.** Definition `frameMat`: The definition expresses a linear map using cylindrical frame vectors in both its input and output slots.

**Cylindrical velocity Fourier mode.** Definition `modeVec`: The definition takes the normalized angular Fourier coefficient of a vector field in the cylindrical frame.

**Cylindrical derivative Fourier mode.** Definition `modeMat`: The definition takes the normalized angular Fourier coefficient of a matrix field in the cylindrical frame.

**Radial, angular and axial frame vectors.** Definition `frameUnit`: The definition lists the three cylindrical frame vectors.

**Second derivative in the moving frame.** Definition `frameThird`: The definition evaluates a second derivative tensor in three cylindrical frame directions.

**Fourier mode of the second derivative.** Definition `modeThird`: The definition takes the normalized angular Fourier coefficient of a second derivative component in the moving frame.

**Component of a gradient mode.** Definition `gradMode`: The definition selects one entry of the gradient's cylindrical Fourier mode.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellBox`.

**Angular weight for a cell.** Definition `angularWeight`: The definition uses a special zero-mode value on axis cells and the appropriate outer-radius weight otherwise.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellBases`.

**Weighted polynomial coefficient.** Definition `coef`: The definition integrates a field against the radial and height basis polynomials with the cell line weight.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Certificate weight on a radial slice.** Definition `sampleWeight`: The definition evaluates the certificate weight on the zero-angle cylindrical slice.

**Tail eigenvalue threshold.** Definition `tailLam`: The definition multiplies the sum of radial and height eigenvalues by the cell's inner-radius factor.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Absolute angular frequency.** Definition `modeNumber`: The definition is the absolute value of the mode's azimuthal frequency.

**Skew matrix associated to a vector.** Definition `bracketMat`: The definition contracts a complex vector with permutation signs to form its cross-product matrix.

**Strain and velocity coupling.** Definition `couplingMap`: The definition combines a curl-gradient matrix and a velocity into the matrix coupling used in the cell interaction.

**Complex matrix entry pairing.** Definition `entryPairing`: The definition sums the products of matrix entries with the conjugates of the second matrix's entries.

**Interaction between two angular modes.** Definition `waveForm`: The definition combines the strain-curl interaction and the two curl-gradient velocity couplings.

**Classes of angular-mode errors.** Structure `CellClasses`: The structure records mode classes, four deviation bounds, sharing weights, row weights and resolved portions.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Fourier mode of the model strain.** Definition `strainMode`: The definition takes the cylindrical matrix mode of the model strain.

**Fourier mode of the model curl gradient.** Definition `curlGradMode`: The definition takes the cylindrical matrix mode of the model curl gradient.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Adjoint of the curl contraction.** Definition `curlAdj`: The definition contracts a complex vector with permutation signs to produce the adjoint curl matrix.

**Adjoint of the velocity coupling.** Definition `couplingAdj`: The definition applies the conjugated curl-gradient coefficients to a strain matrix.

**Complex matrix-vector multiplication.** Definition `matVec`: The definition multiplies a three-by-three complex matrix by a complex vector.

**Strain part of the interaction action.** Definition `waveActionStrain`: The definition combines the negative adjoint curl action and half the velocity coupling.

**Velocity part of the interaction action.** Definition `waveActionVelocity`: The definition takes half the adjoint curl-gradient coupling applied to the strain matrix.

**Strain entries of a twelve-vector.** Definition `splitStrain`: The definition reads the first nine coordinates as a three-by-three strain matrix.

**Velocity entries of a twelve-vector.** Definition `splitVelocity`: The definition reads the final three coordinates as a velocity vector.

**Action of a twelve-by-twelve matrix.** Definition `matAct`: The definition multiplies the twelve-component field vector by its coefficient matrix.

**Inverse adjoint angular operator.** Definition `turnAdjInv`: The definition gives the explicit three-component inverse formula for the adjoint angular operator.

**Fold velocity into the angular column.** Definition `foldVelocity`: The definition adds the radius-scaled inverse-adjoint velocity contribution to the angular column of the strain array.

**Data for reduced and unresolved rows.** Structure `CellRows`: The structure records row mode support, reduction matrices, far-field kernels and row-class weights.

**Complex vector cross product.** Definition `crossC`: The definition gives the coordinate formula for the cross product of two complex vectors.

**Componentwise vector conjugation.** Definition `conjVec3`: The definition conjugates each coordinate of a complex vector.

**Cartesian vector from frame coordinates.** Definition `cartOfFrame`: The definition synthesizes a Cartesian vector from its three cylindrical frame coefficients.

**Cartesian map from frame entries.** Definition `cartOpOfFrame`: The definition synthesizes a Cartesian linear map from its cylindrical frame matrix.

**Angle of a Cartesian point.** Definition `cylAngle`: The definition takes the complex argument of the first two Cartesian coordinates.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Angular mode of a certificate row.** Definition `rowMode`: The definition takes the cylindrical Fourier mode of the selected row field.

**Strain coupling for a certificate row.** Definition `rowCouplingStrain`: The definition sums row modes against conjugate model-velocity modes through the adjoint curl, with radial weighting.

**Velocity coupling for a certificate row.** Definition `rowCouplingVelocity`: The definition sums row modes crossed with conjugate model-curl modes, with radial weighting.

**Row coupling with velocity folded in.** Definition `rowCouplingFolded`: The definition uses the strain coupling on resolved modes and folds in the velocity coupling on the other modes.

**Weighted symmetric and skew pairing.** Definition `sigmaWeightedPair`: The definition pairs symmetric and antisymmetric matrix parts with their separate reciprocal weights.

**Squared row coefficient bound.** Definition `rowSquare`: The definition sums selected unresolved strain and velocity coefficient squares divided by their weights.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Matrix reconstructed from a mode class.** Definition `classField`: The definition synthesizes a matrix field from the Fourier modes in a finite class.

**Vector reconstructed from a mode class.** Definition `classVec`: The definition synthesizes a vector field from the Fourier modes in a finite class.

**Bound on a complex matrix action.** Definition `OpBound`: The predicate requires the squared matrix-vector norm to be bounded by the squared stated constant times the input norm.

**Source namespace:** `Breakdown.CellCert.CellFormula.ParamData`.

**Coordinates solved by the relations.** Definition `solvedSet`: The definition is the image of the selected solved-coordinate map.

**Coordinates left free.** Definition `freeSet`: The definition selects coordinates outside the solved-coordinate set.

**Interior free coordinates.** Definition `interiorSet`: The definition removes skeleton coordinates from the free-coordinate set.

**Projection onto free coordinates.** Definition `freePart`: The definition keeps free coordinates and replaces solved coordinates with zero.

**Reconstruction from free coordinates.** Definition `param`: The definition corrects the free vector using the inverse solved block so that the relation matrix vanishes.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Corner trace as a volume moment.** Definition `cornerMoment`: The definition combines field, radial, height and mixed-derivative integrals over a rectangle to encode a corner value.

**Weak potential for a gradient field.** Definition `IsPotentialOf`: The predicate requires a measurable locally square-integrable scalar potential whose distributional gradient is the given field.

**Chosen weak potential.** Definition `potentialOf`: The definition selects a weak potential when one exists and uses the zero function otherwise.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellDatum`.

**Pressure moment coordinate.** Definition `sidePressure`: The definition embeds a mode, pressure segment and degree into the sum type of cell data.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellLayout`.

**Velocity mode of a field tuple.** Definition `velMode`: The definition extracts the selected velocity Fourier mode from a field tuple using the layout order.

**Gradient mode of a field tuple.** Definition `gradModeOf`: The definition extracts the selected gradient Fourier component from a field tuple.

**Second-derivative mode of a field tuple.** Definition `secondModeOf`: The definition extracts the selected second-derivative Fourier component from a field tuple.

**Pressure-gradient mode of a field tuple.** Definition `pressureGradMode`: The definition takes the selected Fourier component of the tuple's gradient field.

**Moment fixing the pressure gauge.** Definition `gaugeValue`: The definition evaluates the zero-mode potential and its gradient on the designated gauge segment.

**Gauge moment of the constant function.** Definition `gaugeUnit`: The definition evaluates the designated pressure gauge on the constant scalar function one.

**Pressure with its gauge removed.** Definition `pressureOf`: The definition subtracts the real gauge-normalizing constant from the selected weak potential.

**Fourier mode of normalized pressure.** Definition `pressMode`: The definition takes a pressure mode after applying the layout's gauge normalization.

**Extra velocity moments on four sides.** Definition `extraValue`: The definition assigns the appropriate radial or height strip moment to each of the cell's four sides.

**Cell data of an admissible field.** Definition `trueData`: The definition assembles low coefficients, side moments, pressure moments, corner traces, stream values and extra side data from a field tuple.

**Locate a low coefficient in cell data.** Definition `lowEntry`: The definition returns a low strain or velocity coordinate when its mode and degrees fit the layout, and returns no coordinate otherwise.

**Complex coordinates from real pairs.** Definition `realCoord`: The definition combines the two real components of each datum as its real and imaginary parts.

**Real and imaginary coordinate pairs.** Definition `realPart`: The definition splits each complex datum into its real and imaginary components.

**Negative mode when it is available.** Definition `negMode`: The definition chooses the negative mode when it belongs to the layout and otherwise retains the original mode.

**Conjugate cell coordinate.** Definition `conjDatum`: The definition reverses each mode index in the cell datum while preserving its other indices.

**Angular mode of a cell coordinate.** Definition `modeOf`: The definition reads the Fourier index of each datum and assigns zero to stream coordinates.

**Coordinates deleted by plane symmetry.** Definition `IsPlaneDeleted`: The predicate selects the side, corner and stream coordinates forced to vanish on the symmetry plane.

**Pressure coordinates deleted by gauge.** Definition `IsGaugeDeleted`: The predicate selects designated zero-mode pressure moments removed by the gauge choice.

**Independent real system coordinates.** Definition `IsSystemCoord`: The predicate keeps positive modes and real zero-mode parts while excluding plane and gauge deletions.

**Sign of a conjugated real component.** Definition `partSign`: The definition gives sign one to a real part and sign minus one to an imaginary part.

**Expand the independent real coordinates.** Definition `expandSystem`: The definition reconstructs negative modes by conjugation signs and fills deleted coordinates with zero.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Pressure-side layout conditions.** Structure `IsPressureLayout`: The structure requires a valid symmetric-mode layout whose pressure segments cover the non-axis sides, have disjoint interiors and carry orthonormal tests.

**Pressure gauge shifts across a cell.** Structure `GaugeShift`: The structure records left, right and pointwise real gauge shifts as functions of a field tuple.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellLayout`.

**Effect of a pressure gauge shift.** Definition `pressureShift`: The definition changes only zero-mode pressure data using radial-side constants and height-side endpoint contributions.

**True data after a gauge shift.** Definition `shiftedData`: The definition adds the pressure-shift vector to the true cell data.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Gauge edge and root choices.** Structure `GaugeSpec`: The structure chooses an optional pressure edge and a finite set of pressure roots.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellLayout`.

**Coefficient of the left gauge shift.** Definition `shiftCoefLeft`: The definition gives the pressure datum's response to the left gauge constant using segment integrals and radial primitives.

**Coefficient of the right gauge shift.** Definition `shiftCoefRight`: The definition gives the pressure datum's response to the right gauge constant using segment integrals and radial primitives.

**Real zero-mode pressure datum.** Definition `pressureDatumValue`: The definition reads the real pressure moment if a zero mode is present and returns zero otherwise.

**Pressure jump fixed by an edge.** Definition `gaugeJump`: The definition is zero without a gauge edge and otherwise divides the negative edge pressure value by the right-shift coefficient.

**Piecewise gauge from left and right.** Definition `gaugeShiftOf`: The definition uses the right gauge at the outer radius and the left gauge at all other radii.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Valid pressure gauge specification.** Structure `IsGaugeSpec`: The structure requires the gauge edge and roots to match deleted data, with balanced nonzero edge response and whole-side pressure segments.

**Source namespace:** `Breakdown.CellCert.CellEnergy`.

**Sesquilinear matrix pairing.** Definition `sumSesq`: The definition sums the products of conjugated first-matrix entries and second-matrix entries.

**Sesquilinear vector pairing.** Definition `vecSesq`: The definition sums the products of conjugated first-vector components and second-vector components.

**Sesquilinear curl pairing.** Definition `curlSesq`: The definition pairs the curls of two strain arrays using conjugation in the first argument.

**Cell-mode sesquilinear interaction.** Definition `pairSesq`: The definition combines the wave interaction between two modes and the local matrix contribution on equal modes.

**Matrix of the integrated interaction.** Definition `pairForm`: The definition integrates the weighted mode interaction of basis slots to construct the pairing matrix.

**Matrix of the class-error penalty.** Definition `classForm`: The definition integrates the shared strain and gradient deviation penalties on equal resolved modes.

**Row coupling an actuator to strain.** Definition `actuatorRow`: The definition integrates the strain basis against the model actuator gradient, with the prescribed half factor.

**Row coupling a pin field to strain.** Definition `pinRow`: The definition integrates the strain basis against the model pin field.

**Actuator and pin cross rows.** Definition `crossRow`: The definition places actuator rows and pin rows in the two parts of a sum index.

**Block matrix of the local cell form.** Definition `localForm`: The definition combines the energy, class-error and interaction matrices with the actuator and pin cross blocks.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Index of a low cell coefficient.** Abbreviation `LowIndex`: The abbreviation records the angular mode, field component, strain-or-velocity slot and two polynomial degrees.

**Finite support of low coefficients.** Definition `lowSupport`: The definition selects resolved modes and radial-height degrees up to the high-degree cutoff.

**Low coefficients within the support.** Abbreviation `LowSupp`: The abbreviation is the subtype of low indices belonging to the selected finite support.

**Low data with multipliers and pins.** Abbreviation `Aug`: The abbreviation joins low coefficient indices to multiplier and pin indices.

**Rank-one Hermitian matrix.** Definition `rankOne`: The definition is the matrix with entries given by a conjugated coordinate times an unconjugated coordinate.

**Linear form of coefficient vectors.** Definition `linForm`: The definition sums coordinatewise products of the coefficient row and the input vector.

**One strain basis component.** Definition `unitStrain`: The definition places a radial-height basis polynomial in its selected mode and strain component and uses zero elsewhere.

**One velocity basis component.** Definition `unitVelocity`: The definition places a radial-height basis polynomial in its selected mode and velocity component and uses zero elsewhere.

**Synthesis of low strain modes.** Definition `synthStrain`: The definition sums the low strain basis components with the augmented vector's coefficients.

**Synthesis of low velocity modes.** Definition `synthVelocity`: The definition sums the low velocity basis components with the augmented vector's coefficients.

**Multiplier part of an augmented vector.** Definition `kappaPart`: The definition reads a multiplier coordinate from the augmented vector.

**Pin part of an augmented vector.** Definition `pinPart`: The definition reads a pin coordinate from the augmented vector.

**Strain response to the low field.** Definition `yStrainOf`: The definition combines wave interactions, the local matrix, actuator gradients and pin fields into the weighted strain response.

**Velocity response to the low field.** Definition `yVelocityOf`: The definition combines the wave and local-matrix velocity contributions with radial weighting.

**Response with velocity folded in.** Definition `yFoldedOf`: The definition retains the strain response on resolved modes and folds velocity into strain on other modes.

**Polynomial coefficient of the response.** Definition `yCoef`: The definition takes a weighted basis coefficient of the folded response synthesized from augmented data.

**Coefficient of the velocity response.** Definition `yVelCoef`: The definition takes a weighted basis coefficient of the synthesized velocity response.

**Response row on unit coordinates.** Definition `yVec`: The definition evaluates a response coefficient on each unit augmented coordinate.

**Symmetric response coefficient row.** Definition `symVec`: The definition averages a response row with its transposed component row.

**Antisymmetric response coefficient row.** Definition `antiVec`: The definition halves the difference of a response row and its transposed component row.

**Velocity response on unit coordinates.** Definition `velVec`: The definition evaluates a velocity response coefficient on each unit augmented coordinate.

**Near-tail response matrix.** Definition `nearMatrix`: The definition sums weighted rank-one symmetric, antisymmetric and velocity response matrices over near unresolved coefficients.

**Coefficient of folded row coupling.** Definition `rowCouplingCoef`: The definition takes a polynomial coefficient of a certificate row's folded coupling.

**Coefficient of row velocity coupling.** Definition `rowCouplingVelCoef`: The definition takes a polynomial coefficient of a certificate row's velocity coupling.

**Weighted row-response pairing.** Definition `rowYVec`: The definition pairs response coefficient rows with the conjugated row couplings using their symmetric, antisymmetric and velocity weights.

**Embed augmented indices into far data.** Definition `augToFar`: The definition forgets the proof of low-support membership while preserving multiplier and pin indices.

**Far kernel restricted to supported data.** Definition `farMatrix`: The definition reads the far kernel on augmented indices and sets entries outside the declared far support to zero.

**Velocity mode of a row field.** Definition `rowModeVec`: The definition takes the cylindrical Fourier mode of the selected certificate row.

**Gradient mode of a row field.** Definition `rowModeGrad`: The definition takes the cylindrical Fourier mode of the derivative of the selected certificate row.

**Complex vector pairing.** Definition `pairC`: The definition sums component products with conjugation in the second vector.

**Position in the cylindrical frame.** Definition `frameY`: The definition gives the complex frame vector with radial and height components and zero angular component.

**Rotated position in the frame.** Definition `frameTurnY`: The definition gives the complex frame vector with the radius in its angular component.

**Planar rotation of a complex vector.** Definition `turnC`: The definition rotates the first two components through a quarter turn and sets the axial component to zero.

**Product of radial and height bases.** Definition `basisVal`: The definition multiplies the radial and height basis polynomials and regards the value as complex.

**Strain coefficient in a model row.** Definition `strainRowCoef`: The definition integrates the drift, rotation, viscosity and model-velocity contributions multiplying a strain basis coefficient.

**Velocity coefficient in a model row.** Definition `velocityRowCoef`: The definition integrates the scaling, rotation and model-curl contributions multiplying a velocity basis coefficient.

**Trace moment on a face segment.** Definition `segmentTrace`: The definition evaluates the segment moment using the field and its radial and height derivatives.

**Gradient boundary coefficient of a row.** Definition `gradSideRowCoef`: The definition multiplies the conjugated row trace by the signed viscosity and the radial boundary factor where needed.

**Pressure boundary coefficient of a row.** Definition `presSideRowCoef`: The definition multiplies the conjugated normal row trace by the signed boundary factor.

**Normal coordinate of a segment.** Definition `segmentNormal`: The definition chooses the radial coordinate on radial segments and the axial coordinate on height segments.

**Normal coordinate of a cell side.** Definition `sideNormal`: The definition chooses the radial normal for the first two sides and the axial normal for the last two.

**Position of a cell side.** Definition `faceLevel`: The definition returns the inner radius, outer radius, lower height or upper height according to the side index.

**Position of the opposite cell side.** Definition `faceOther`: The definition returns the opposite radial or height boundary of the cell.

**Normal row coefficient on a face.** Definition `faceRowCoef`: The definition integrates the normal row mode against the relevant height or radial basis polynomial on the face.

**Normal-strain boundary row.** Definition `normalFaceRowData`: The definition assembles signed viscous normal-strain face rows and omits the inner face when it is the axis.

**Complete row on layout data.** Definition `layoutRowData`: The definition assembles volume coefficients, tangential-gradient side coefficients, pressure coefficients and normal-strain face contributions.

**Multiplier coefficient of a row.** Definition `layoutRowKappa`: The definition divides the model actuator's pairing with the row field by four pi.

**Inputs for the exact cell formula.** Structure `CellFormulaInputs`: The structure records finite coordinates, their reconstruction, true data, low entries, row coefficients and the local quadratic matrix.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellFormulaInputs`.

**Skeleton, interior, multiplier and pin.** Abbreviation `Coord`: The abbreviation joins the four groups of real coordinates used by the exact cell formula.

**Complex data with real auxiliaries.** Definition `dataVec`: The definition appends real multiplier and pin coordinates to the complex cell-data vector.

**Augmented vector extracted from data.** Definition `augOfData`: The definition reads available low entries and appends multiplier and pin values, using zero when a low entry is absent.

**Real value of a model row.** Definition `rowValue`: The definition takes the real part of the data-row pairing and adds the multiplier contribution.

**Row residual after response subtraction.** Definition `residualValue`: The definition subtracts the real weighted response pairing from the model-row value.

**Exact cell quadratic expression.** Definition `formulaValue`: The definition combines local energy, near and far losses and reduced residual squares, with the prescribed viscosity scaling.

**Exact matrix obtained by polarization.** Definition `exactFormula`: The definition polarizes the exact cell quadratic expression on pairs of real unit coordinates.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Real skeleton coordinate set.** Definition `skeletonCoords`: The definition pairs every skeleton datum with its real and imaginary component indices.

**Real interior coordinate set.** Definition `interiorCoords`: The definition pairs every interior free datum with its real and imaginary component indices.

**Embed skeleton and interior vectors.** Definition `embedCoords`: The definition places the two finite coordinate vectors in their indexed positions and sets all other entries to zero.

**Canonical inputs from a cell layout.** Definition `canonicalInputs`: The definition reconstructs constrained data from real coordinates and equips it with gauge-shifted true data, row coefficients and the cell matrix.

**Source namespace:** `Breakdown.CellCert.CellCoordinates`.

**Independent skeleton coordinates.** Definition `systemSkeletonCoords`: The definition keeps the skeleton coordinates satisfying the real system-coordinate predicate.

**Independent interior coordinates.** Definition `systemInteriorCoords`: The definition keeps the interior coordinates satisfying the real system-coordinate predicate.

**Vector of independent cell coordinates.** Definition `systemVector`: The definition combines independent skeleton and interior values in a common coordinate array and fills other entries with zero.

**A pressure datum.** Definition `IsPressureDatum`: The predicate selects the pressure-moment branch of the cell-data sum type.

**Preset viscosity scale for pressure.** Definition `presetScale`: The definition assigns the viscosity scale to pressure data and scale one to other data.

**Expand and rescale system coordinates.** Definition `expandedCoords`: The definition applies conjugation reconstruction and pressure scaling to independent skeleton and interior coordinates.

**Coordinates attached to one cell.** Structure `CellCoords`: The structure records the layout, parametrization, chosen relations, global-to-local map, pressure gauges and proposed cell matrix.

**Source namespace:** `Breakdown.CellCert.CellCoordinates.CellCoords`.

**Restrict a global state to a cell.** Definition `restrictState`: The definition maps global moments to local skeleton data and divides multiplier and pin coordinates by the viscosity.

**Canonical formula for cell coordinates.** Definition `formula`: The definition constructs the cell's exact formula inputs from its layout, parametrization and two pressure gauges.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellBox`.

**Radial polynomial projection tail.** Definition `radialTail`: The definition subtracts the squared radial coefficients through the cutoff from the weighted radial L² norm.

**Height polynomial projection tail.** Definition `heightTail`: The definition subtracts the squared height coefficients through the cutoff from the height L² norm.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Family of polynomial tail estimates.** Structure `TailFamily`: The structure records multipliers, input and output modes, degree cutoffs, output weights and radial-height tail bounds.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.TailFamily`.

**Total radial tail allowance.** Definition `radialTotal`: The definition sums each input group's radial bounds through its input-degree cutoff.

**Total height tail allowance.** Definition `heightTotal`: The definition sums each input group's height bounds through its input-degree cutoff.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Radial and height bounds for a group.** Structure `FarGroupBounds`: The structure records the two families of degree-dependent far-tail bounds.

**Data bounding the far response.** Structure `FarMajorantData`: The structure gathers strain, velocity and band tail bounds with sharing factors, turning bounds and positive-weight floors.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Model strain in the cylindrical frame.** Definition `strainAt`: The definition evaluates the real model strain in the moving frame and regards its entries as complex.

**Model curl gradient in the frame.** Definition `curlGradAt`: The definition evaluates the real model curl gradient in the moving frame and regards its entries as complex.

**Complex coordinate unit vector.** Definition `unitVec3`: The definition places one in the selected vector component and zero in the others.

**Complex coordinate unit matrix.** Definition `unitMat`: The definition places one in the selected flattened matrix component and zero in the others.

**Tail family for the strain response.** Definition `strainGroupFamily`: The definition supplies the two strain-response multiplier groups with their mode supports, degree cutoffs and tail bounds.

**Tail family for resolved velocity.** Definition `velocityGroupFamily`: The definition supplies the velocity response on resolved output modes with its weight and tail bounds.

**Tail family for band velocity.** Definition `bandGroupFamily`: The definition supplies the radius-weighted velocity response on band output modes with its weight and tail bounds.

**Strain coefficients in far data.** Definition `lowStrainCoef`: The definition reads a three-by-three strain coefficient array from the low-index part of the far-data vector.

**Velocity coefficients in far data.** Definition `lowVelocityCoef`: The definition reads a three-component velocity coefficient vector from the low-index part of the far data.

**Combined radial and height group weight.** Definition `groupWeight`: Within the input degree range, the definition combines each radial-height bound with its total allowance and uses zero outside that range.

**Quadratic majorant for the far response.** Definition `farMajorantForm`: The definition sums strain, curl and velocity coefficient squares with the corresponding group weights.

**Unresolved row squares up to a cutoff.** Definition `rowSquareUpTo`: The definition sums weighted strain and velocity row-coupling squares above the near-degree cutoff and below a finite upper cutoff.

**Source namespace:** `Breakdown.CellCert.CellCoordinates`.

**Gauge positions of a pressure datum.** Definition `pressurePositions`: The definition lists the radial positions and left-or-right gauge choices that affect a pressure datum.

**Assemble a row from weighted entries.** Definition `rowEntries`: The definition sums the coefficients assigned to a selected slot in a list of weighted slots.

**Compatibility of a split segment.** Definition `SegmentSplit`: The predicate requires two subsegments to cover the original segment and their weighted polynomial tests to reproduce its test on each piece.

**Stream value with fixed zero boundaries.** Definition `streamEval`: The definition returns zero on the axis or symmetry plane and reads the stream key elsewhere.

**Compatibility of a flux split.** Definition `FluxSplit`: The predicate requires a zero-mode normal-velocity split to respect both polynomial tests and the corresponding stream-function flux identities.

**Data gluing cell coordinates on a mesh.** Structure `MeshData`: The structure records local coordinate systems, ownership, pressure classes and paths, and delayed-coordinate substitutions.

**Source namespace:** `Breakdown.CellCert.CellCoordinates.MeshData`.

**Cell datum belonging to a skeleton row.** Definition `rowDatum`: The definition converts a finite skeleton-row number back into its datum and real-part index.

**Gauge value fixed at a class root.** Definition `rootValue`: The definition chooses the gauge constant that cancels the root pressure datum using the selected side's shift coefficient.

**Gauge value transported along a path.** Definition `classValue`: The definition adds signed edge jumps along the class path to the root gauge value.

**Canonical left gauge of a cell.** Definition `canonicalLeft`: The definition reads the transported gauge value of the cell's left pressure class.

**Canonical right gauge of a cell.** Definition `canonicalRight`: The definition reads the transported gauge value of the cell's right pressure class.

**Rescaled local skeleton value.** Definition `localValue`: The definition reads the gauge-shifted real datum and divides by its prescribed pressure scale.

**Skeleton key owned by a global slot.** Definition `ownerKey`: The definition reads the geometric skeleton key of the slot's owner cell and owner row.

**Skeleton key of a local row.** Definition `rowKey`: The definition reads the geometric skeleton key attached to a cell's skeleton row.

**Pressure classes of an owned datum.** Definition `ownerNodes`: The definition attaches pressure-class nodes to the radial gauge positions of the slot's owned datum.

**Pressure classes of a local row.** Definition `rowNodes`: The definition attaches pressure-class nodes to the radial gauge positions of a cell's local row.

**Pressure nodes participating in a row.** Definition `participantNodes`: The definition collects the local row's pressure nodes and those of all owner slots in its expansion.

**Base moment of a global slot.** Definition `baseMoment`: The definition reads the multiplier when the slot is a multiplier slot and otherwise reads the owning cell's local value.

**A slot represented by a delay relation.** Definition `IsDelaySlot`: The predicate records that a slot is selected by one of the delayed-row indices.

**Canonical global moment.** Definition `canonicalMoment`: The definition uses the delayed expansion on delay slots and the base moment on all other slots.

**Vector encoding a delayed relation.** Definition `delayVector`: The definition subtracts the expanded delayed row from the unit vector at its delay slot.

**Skeleton keys of extra coordinates.** Definition `extraKeys`: The definition converts a list of extra cell data into weighted geometric skeleton keys.

**Pressure nodes of extra coordinates.** Definition `extraNodes`: The definition collects the pressure-class nodes participating in a list of extra cell data.

**A key removed by a compatible gauge.** Definition `DeletedKey`: The predicate requires a matching gauge-deleted datum whose pressure-class nodes agree with the local row at shared radial positions.

**Source namespace:** `Breakdown.CellCert.CellCoordinates`.

**Conditions for consistent mesh data.** Structure `IsMeshData`: The structure imposes compatible gauges, moment ownership, delayed expansions, segment and flux splitting, pressure paths and geometric side conditions.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Azimuthal angle of a point.** Definition `angleOf`: The definition is the complex argument of the point's first two Cartesian coordinates.

**Complementary compactified radius.** Definition `chartS`: The definition subtracts the compactified radial coordinate from one.

**Core ratio in compactified coordinates.** Definition `coreRatioT`: The definition expresses the squared-radius core ratio as a rational function of the compactified radius.

**Logarithmic radial phase.** Definition `logPhase`: The definition is half the logarithm of one plus the squared radius divided by the squared core radius.

**Radial decay factor.** Definition `decayFactor`: The definition raises the complementary compactified radius to twice the decay exponent.

**Vector from three real components.** Definition `ofComponents`: The definition assembles a Cartesian vector from three real coordinate values.

**Spline extended by even or odd parity.** Definition `eval`: The definition evaluates the half-spline at absolute height and applies the selected parity sign.

**Spline joins and parity conditions.** Structure `IsSplineClass`: The structure requires a tensor mesh, matching derivatives across radial and height joins, and parity-compatible vanishing derivatives on the symmetry plane.

**Spline with real coefficients.** Definition `IsReal`: The predicate requires every polynomial coefficient of every spline piece to have zero imaginary part.

**Four spline amplitudes for a mode.** Structure `ModeAmp`: The structure records radial, polar, stream and swirl amplitudes.

**Conjugate mode amplitudes.** Definition `conj`: The definition conjugates each of a mode's four spline amplitudes.

**Data synthesizing a finite-mode field.** Structure `FieldData`: The structure records the angular support, spline amplitudes, endpoint orders and stream and swirl guards.

**Radial scaling with phase and decay.** Definition `twistedScale`: The definition adds the logarithmic-phase and decay corrections to the radial scaling derivative.

**Reduced field of one angular mode.** Definition `reducedField`: The definition constructs the zero mode from stream and swirl amplitudes and nonzero modes from radial and polar amplitudes with a divergence constraint.

**Angular and logarithmic phase factor.** Definition `modePhase`: The definition exponentiates the combined angular phase and logarithmic radial phase for one mode.

**Real field synthesized from mode data.** Definition `fieldOf`: The definition sums decaying phase-weighted reduced modes in the spatial frame and takes their real components.

**Regularity conditions for field data.** Structure `IsFieldData`: The structure requires conjugate modes, spline regularity and parity, endpoint guards and sufficient radial and axis vanishing orders.

**Field data with compact support.** Structure `IsCompactFieldData`: The structure adds a compactified cutoff below one, vanishing amplitudes past it and matching mesh breaks to the field-data conditions.

**Parameterized profile data.** Structure `ProfileData`: The structure records chart parameters, the fractional power, affine rotation rate and a finite polynomial family of field and multiplier coefficients.

**Source namespace:** `Breakdown.CellCert.GivenFields.ProfileData`.

**Affine rotation rate.** Definition `rate`: The definition adds the base rotation rate to its linear parameter variation.

**Phase fixed by the rotation rate.** Definition `phase`: The definition scales the rotation rate by minus twice the fractional power and angular order.

**Parameter monomial.** Definition `monomialOf`: The definition multiplies the parameter coordinates raised to their specified multi-index powers.

**Polynomial family of profile fields.** Definition `profile`: The definition sums the field-data components weighted by their parameter monomials at the parameter-dependent phase.

**Polynomial family of multipliers.** Definition `multiplier`: The definition sums each multiplier's coefficients weighted by the parameter monomials.

**Second derivative of the profile.** Definition `second`: The definition takes the iterated Fréchet derivative of the parameterized profile.

**Chosen weak fractional-power field.** Definition `powerField`: The definition selects a weak fractional power of the profile when one exists and otherwise uses the zero field.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Consistency of parameterized profiles.** Structure `IsProfileData`: The structure requires a valid chart, the matching fractional exponent, nonnegative parameter radii and a downward-closed family of regular field data.

**Identify encoded and analytic profiles.** Structure `IsProfileInstance`: The structure equates certificate profiles, derivatives, fractional power, rotation, radius, order and multipliers with their explicit data constructions.

**Centre equals the zero-parameter profile.** Structure `IsCentreInstance`: The structure identifies the centre field and its second derivative with the profile at zero parameters.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Horizontal distance from the axis.** Definition `horizontalNorm`: The definition takes the Euclidean norm of the first two Cartesian coordinates.

**Kernel bound from mass and supremum.** Definition `kernelShell`: The definition combines mass, supremum and separation into a Newton-kernel shell estimate, using a separate expression at nonpositive separation.

**Gap between radial or height ranges.** Definition `gapDist`: The definition takes the nonnegative gap between two intervals, allowing an absent upper endpoint.

**Integrated sheet-area expression.** Definition `sheetArea`: The definition combines inverse hyperbolic sine and a square-root term in the explicit sheet-area bound.

**Data for summing cell kernel bounds.** Structure `CellSumData`: The structure records source pieces and target boxes with geometric bounds, masses, suprema and chosen pair-estimate rules.

**Source namespace:** `Breakdown.CellCert.Reduction.CellSumData`.

**Distance to a rotated sector.** Definition `sectorDist`: The definition combines radial separation, direct or reflected height separation and angular sector separation.

**Sum of paired angular-sector bounds.** Definition `sectorSum`: The definition sums twice the shell-kernel estimate over the specified range of paired sectors.

**Lower angular separation constant.** Definition `sectorConst`: The definition combines the lower source and target radii with the sine-over-angle sector factor.

**Near-sector integral estimate.** Definition `nearTerm`: The definition adds a separated mass contribution and a sheet-area contribution for the nearest sector.

**Chosen bound for a source-target pair.** Definition `pairTerm`: The definition chooses a sector sum, a single shell bound or a near-sector estimate plus the remaining sector sum.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Weak negative Laplacian relation.** Definition `IsWeakNegTraceOf`: The predicate identifies a field's negative Laplacian distribution through pairings with smooth test vector fields.

**Weak divergence of a matrix field.** Definition `IsWeakMatrixDivergenceOf`: The predicate identifies a matrix field's distributional divergence by integration against test-field derivatives.

**Normalization of a low fractional power.** Definition `lowPowerNormalizer`: The definition integrates the inverse-power kernel against one minus the cosine of a Cartesian coordinate.

**Symmetric fractional difference integral.** Definition `lowPowerAt`: The definition forms the normalized singular integral of the symmetric second difference of a vector field.

**Point on a cylindrical circle.** Definition `ringPoint`: The definition converts radius, angle and height into Cartesian coordinates.

**Horizontal vector encoded as complex.** Definition `horizontalPart`: The definition encodes the first two components of a vector field as a complex scalar.

**Axial vector component as complex.** Definition `verticalPart`: The definition regards the axial component of a vector field as a complex scalar.

**Angular Fourier mode on a circle.** Definition `angularMode`: The definition takes a normalized integer angular Fourier coefficient on the interval from minus pi to pi.

**Weighted norm on selected harmonics.** Definition `harmonicWeightSqOn`: The definition sums radius-weighted mode energies over a finite harmonic set with separate shifted horizontal and vertical divisors.

**Adjoint scaling and rotation drift.** Definition `driftAdjointField`: The definition combines the adjoint scaling coefficient, radial derivative and oppositely signed rotational derivative.

**Adjoint of the convection interaction.** Definition `convectionAdjointField`: The definition combines a curl cross-product term and twice the adjoint profile derivative acting on the test field.

**Data for the adjoint dual estimate.** Structure `AdjointDual`: The structure records adjoint derivatives, pin potentials, pressure, dual and flux decompositions, inverse-square terms and their bounds.

**Source namespace:** `Breakdown.CellCert.Reduction.AdjointDual`.

**Scaled pin dual field.** Definition `pinDual`: The definition divides the pin trace by its pin scale.

**Residual in the adjoint equation.** Definition `residualField`: The definition adds drift, sharp trace and convection terms, subtracts pin duals and adds the pressure gradient.

**Remainder of the adjoint decomposition.** Definition `remainderField`: The definition subtracts the dual trace, scaled potential trace and flux divergence from the adjoint residual.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Multi-index parameter power.** Definition `multiPow`: The definition is the product of parameter powers prescribed by a multi-index.

**Finite polynomial family of field data.** Structure `FieldFamily`: The structure records a finite multi-index support and field-data coefficient for each index.

**Evaluate a polynomial field family.** Definition `eval`: The definition sums the family fields with their parameter monomial weights and supplied phase.

**Downward-closed multi-index support.** Definition `IsDownClosed`: The predicate requires every coordinatewise smaller multi-index to remain in the finite support.

**Two-component pressure spline data.** Structure `PressureData`: The structure records angular modes, two spline amplitude families and their endpoint and axis orders.

**Weighted spline pressure shape.** Definition `pressureShape`: The definition multiplies a pressure spline by compactified radial, decay and axis factors.

**Real pressure from two decay orders.** Definition `pressureOf`: The definition sums phase-weighted pressure shapes with the first and second decay factors and takes the real part.

**Conditions on encoded pressure data.** Structure `IsPressureData`: The structure requires continuous spline classes, conjugate mode data and sufficient decay and axis orders.

**Spline amplitudes for an auxiliary atom.** Structure `AtomData`: The structure records harmonic support and the plus, minus and height amplitudes.

**Last radial cell of an atom spline.** Definition `atomLastT`: The definition subtracts one from the number of radial mesh cells.

**Last height cell of an atom spline.** Definition `atomLastX`: The definition subtracts one from the number of height mesh cells.

**Endpoint conditions for an atom spline.** Structure `IsAtomSpline`: The structure requires first-order spline joins, origin and infinity vanishing and the axis condition for nonzero harmonics.

**One phase-weighted atom term.** Definition `atomTerm`: The definition combines logarithmic and angular phase, an axis factor and the parity-extended spline amplitude.

**Horizontal part of an auxiliary atom.** Definition `atomPlane`: The definition combines the plus harmonics and conjugated nonzero minus harmonics with the decay factor.

**Height part of an auxiliary atom.** Definition `atomHeight`: The definition sums the height harmonics with weight one at zero and weight two elsewhere, then applies the decay factor.

**Real vector field of an auxiliary atom.** Definition `atomOf`: The definition reads the real and imaginary horizontal parts and the real height part as a Cartesian vector.

**Conditions on an auxiliary atom.** Structure `IsAtomData`: The structure imposes the plus, minus and height spline conditions and reality of the zero height harmonic.

**Continuity across radial spline joins.** Structure `IsRadialContinuous`: The structure requires a valid tensor mesh and matching spline values across radial joins.

**Conditions on a flux spline.** Structure `IsFluxSpline`: The structure requires radial continuity and vanishing value and first radial derivative at infinity.

**Flux amplitudes use atom data.** Definition `FluxData`: The definition identifies flux data with the auxiliary-atom amplitude structure.

**Radial flux matrix field.** Definition `fluxOf`: The definition forms the rank-one linear map sending a vector's radial component to the auxiliary atom field.

**Conditions on encoded flux data.** Structure `IsFluxData`: The structure requires valid flux splines for every supported harmonic and a real zero height harmonic.

**Finite polynomial family of atom data.** Structure `AtomFamily`: The structure records multi-index support and auxiliary-atom coefficients.

**Evaluate a polynomial atom family.** Definition `eval`: The definition sums auxiliary atoms weighted by parameter monomials and the supplied phase.

**Auxiliary fields for the certificate.** Structure `AuxData`: The structure records actuators, pins, adjoint families, sharp terms, pressures, duals, potentials and flux data.

**Source namespace:** `Breakdown.CellCert.GivenFields.AuxData`.

**Affine phase of auxiliary fields.** Definition `phase`: The definition adds the phase base to its linear parameter variation.

**Actuator reconstructed from field data.** Definition `actuatorField`: The definition evaluates the selected actuator data at the base phase.

**Pin potential reconstructed from data.** Definition `pinPotentialField`: The definition evaluates the selected pin-potential data at the base phase.

**Scaled derivative defining a smooth pin.** Definition `smoothPinField`: The definition divides the derivative of the pin potential by its pin scale.

**Parameterized adjoint field.** Definition `adjointField`: The definition evaluates the selected adjoint field family at the auxiliary phase.

**Sharp approximation to the adjoint.** Definition `sharpField`: The definition combines the leading adjoint term, subtracts the atom approximation and subtracts the viscosity-scaled adjoint.

**Parameterized dual field.** Definition `dualFieldOf`: The definition evaluates the selected dual atom family at the auxiliary phase.

**Parameterized potential field.** Definition `potentialFieldOf`: The definition evaluates the selected potential atom family at the auxiliary phase.

**Parameterized flux matrix.** Definition `fluxFieldOf`: The definition sums the flux matrices weighted by the adjoint family's parameter monomials.

**Parameterized adjoint pressure.** Definition `adjointPressureField`: The definition sums encoded pressure fields weighted by the adjoint family's parameter monomials.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Conditions on all auxiliary data.** Structure `IsAuxData`: The structure imposes compact actuator and pin support, positive pin scales, closed adjoint support and regularity and decay conditions on all auxiliary families.

**Identify encoded auxiliary fields.** Structure `IsAuxInstance`: The structure matches the explicit phase, actuator, pin, adjoint and sharp constructions to the analytic certificate fields.

**Profile amplitude in one parameter.** Definition `amplitudeFieldAt`: The definition evaluates the field-data coefficient of the selected unit parameter monomial at the current phase.

**Residual inverse-square contribution.** Definition `inverseSquarePartOf`: The definition subtracts the parameter-dependent convection corrections outside the exact index set from the adjoint remainder.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Finite even-derivative resolvent series.** Definition `evenSeries`: The definition sums even derivatives of a polynomial with inverse powers of the scale.

**Explicit interval smoothing formula.** Definition `intervalSmoothed`: The definition combines the polynomial resolvent series with hyperbolic boundary corrections.

**Certified interval smoothing bound.** Definition `IntervalCertificate`: The predicate requires positive scale and a uniform L² pairing bound for polynomials through the chosen degree.

**Weighted axis approximation energy.** Definition `axisFunctional`: The definition integrates approximation error and radial-angular derivative energy with the radial measure.

**Certified axis smoothing bound.** Definition `AxisCertificate`: The predicate requires positive scale and a zero-endpoint Lipschitz cutoff attaining the stated bound for the allowed polynomial degrees and angular orders.

**Polynomial gradient bound at the axis.** Definition `AxisGradientBound`: The predicate bounds radial and angular derivative energy by weighted polynomial L² energy for the two allowed angular orders.

**Best eligible spectral certificate.** Definition `certMin`: The definition takes the infimum of one and all certificate values whose scales do not exceed the requested scale.

**Explicit interval upper bound.** Definition `intervalClosed`: The definition combines inverse-square-root and inverse-scale terms with the polynomial degree factors.

**Explicit axis upper bound.** Definition `axisClosed`: The definition combines inverse-square-root and inverse-scale terms with the polynomial degree and axis-gradient constant.

**Geometric data for a spectral block.** Structure `CellBlock`: The structure records radial and height bounds, polynomial degree, angular mode and whether the block meets the axis.

**Spectral blocks and bound certificates.** Structure `SpectralData`: The structure records block geometry, interval and axis certificates, cutoffs and axis-gradient constants.

**Source namespace:** `Breakdown.CellCert.Spectral.SpectralData`.

**Best interval spectral upper bound.** Definition `intervalUpper`: The definition takes the smaller of the eligible certificate bound and the explicit interval bound.

**Best axis spectral upper bound.** Definition `axisUpper`: The definition combines eligible axis certificates with the explicit formula when the scale is at least 24 and with one below that threshold.

**Smoothing bound assigned to a block.** Definition `blockSpectral`: The definition combines scaled radial, height and angular bounds using separate formulas on and off the axis, capped at one.

**Constant for the inverse-root tail.** Definition `tailFormula`: The definition assembles the geometric and polynomial factors in the block's inverse-square-root spectral tail bound.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Radial coordinate of a point.** Definition `radialCoord`: The definition is the square root of the sum of the first two coordinate squares.

**Solid of a spectral block.** Definition `cellSolid`: The definition selects the radial-height cylinder of a block, with direct or reflected height according to the side index.

**Source namespace:** `Breakdown.CellCert.GivenModel`.

**Finite mesh of cylindrical cells.** Structure `CellMesh`: The structure records a finite family of cell boxes and their common outer size.

**Source namespace:** `Breakdown.CellCert.GivenModel.CellMesh`.

**Region covered by the cell mesh.** Definition `region`: The definition is the union of all cell solids.

**Disjoint piece assigned to a cell.** Definition `piece`: The definition removes all earlier cell solids from the selected solid.

**Field assembled piecewise on the mesh.** Definition `piecewise`: The definition sums cell fields restricted to their disjoint mesh pieces.

**Source namespace:** `Breakdown.CellCert.GivenModel`.

**Geometry of a valid cell mesh.** Structure `IsCellMesh`: The structure requires valid boxes with disjoint interiors that cover the nonnegative radial-height square up to a positive outer size.

**Bivariate coefficient array.** Definition `CellPoly`: The definition represents a polynomial with each variable's degree bounded by the given cutoff as a finite complex coefficient array.

**Evaluate a cell polynomial.** Definition `evalPoly`: The definition sums the coefficient array against radial and height monomials.

**Real finite harmonic polynomial field.** Definition `harmonicValue`: The definition combines the cell polynomials with angular phases, doubles the nonzero modes and takes the real part.

**Reflection sign of a vector component.** Definition `vectorSign`: The definition changes the axial vector component's sign below the symmetry plane.

**Reflection sign of a pseudovector.** Definition `pseudoSign`: The definition uses the pseudovector reflection sign below the symmetry plane.

**Vector field from harmonic polynomials.** Definition `vectorOf`: The definition synthesizes the cylindrical components with vector reflection parity and converts them to Cartesian coordinates.

**Pseudovector from harmonic polynomials.** Definition `pseudoOf`: The definition synthesizes the cylindrical components with pseudovector reflection parity and converts them to Cartesian coordinates.

**Tensor field from harmonic polynomials.** Definition `tensorOf`: The definition synthesizes matrix entries with vector parity in both slots and converts the moving-frame matrix to Cartesian form.

**Pseudotensor from harmonic polynomials.** Definition `pseudoTensorOf`: The definition synthesizes matrix entries with pseudovector output parity and vector input parity in the moving frame.

**Polynomial model data on a cell mesh.** Structure `ModelData`: The structure records harmonic polynomial arrays for velocity, curl, strain, curl gradient, actuators and pins.

**Algebraic conditions on the model data.** Structure `IsModelData`: The structure requires symmetric strain, trace-free curl gradient and vanishing coefficients above each cell's declared harmonic cutoff.

**Source namespace:** `Breakdown.CellCert.GivenModel.ModelData`.

**Piecewise model velocity.** Definition `velocityField`: The definition assembles model velocity polynomials on the disjoint mesh pieces.

**Piecewise model curl.** Definition `curlField`: The definition assembles model curl pseudovectors on the disjoint mesh pieces.

**Model strain with exact exterior strain.** Definition `strainField`: The definition uses polynomial strain inside the mesh and the symmetric centre derivative outside it.

**Model curl gradient with exact exterior.** Definition `curlGradField`: The definition uses polynomial curl-gradient data inside the mesh and the centre's curl gradient outside it.

**Piecewise model actuator.** Definition `actuatorField`: The definition assembles the selected actuator's polynomial vector field on the mesh.

**Piecewise model actuator gradient.** Definition `actuatorGradField`: The definition assembles the selected actuator-gradient polynomial tensor on the mesh.

**Piecewise model pin field.** Definition `pinFieldField`: The definition assembles the selected model pin-field polynomial tensor on the mesh.

**Piecewise pin-value field.** Definition `pinValueField`: The definition assembles the selected pin-value polynomial tensor on the mesh.

**Source namespace:** `Breakdown.CellCert.GivenModel`.

**Identify encoded and analytic models.** Structure `IsModelInstance`: The structure equates the mesh region and all reconstructed model fields with the analytic cell-certificate data.

**Radial derivative of a cell polynomial.** Definition `polyDr`: The definition differentiates the radial monomial factors in the coefficient array.

**Height derivative of a cell polynomial.** Definition `polyDz`: The definition differentiates the height monomial factors in the coefficient array.

**Divergence-free polynomial mode.** Definition `IsSolenoidalProfile`: The predicate requires the radial, angular and height polynomial components to satisfy the cylindrical divergence equation.

**Polynomial test-row data.** Structure `RowData`: The structure records each test row's cell, harmonic, polynomial profile, weight and real-imaginary partner.

**Source namespace:** `Breakdown.CellCert.GivenModel.RowData`.

**Cell-supported polynomial test field.** Definition `testField`: The definition synthesizes a real harmonic polynomial vector field and restricts it to its assigned cell solid.

**Pairing density of one harmonic.** Definition `modePairDensity`: The definition uses real-component products at zero frequency and half the real Hermitian pairing at nonzero frequency.

**Gram matrix of polynomial test fields.** Definition `testPairing`: The definition integrates test profiles on matching cells and harmonics and assigns zero to other pairs.

**Inverse-square-root Gram normalization.** Definition `mix`: The definition uses functional calculus to take the inverse-square-root Gram matrix when Hermitian and returns zero otherwise.

**Normalized row field.** Definition `rowField`: The definition mixes the polynomial test fields with the inverse-square-root Gram matrix.

**Weight of a normalized row.** Definition `rowWeightOf`: The definition assigns the weight of the row's supporting cell.

**Source namespace:** `Breakdown.CellCert.GivenModel`.

**Conditions on polynomial test rows.** Structure `IsRowData`: The structure requires a positive-definite Gram matrix, solenoidal profiles, positive bounded weights, axis regularity and compatible real-imaginary partners.

**Piecewise cell-weight function.** Definition `cellWeightField`: The definition assigns the chosen constant weight on each mesh piece.

**Identify normalized rows with data.** Structure `IsRowInstance`: The structure matches the region, normalized row fields and row and cell weights to the analytic certificate.

**Ray boundary of the outer cylinder.** Definition `boxRadius`: The definition gives the ray radius of the outer radial-height box, using the outer size at the origin.

**Rows belonging to one cell.** Structure `IsRowsInstance`: The structure identifies the local row set with one mesh cell and requires both signs of every row harmonic in its mode set.

**Spectral block attached to a row.** Definition `rowBlock`: The definition copies the row's cell geometry, polynomial degree, angular frequency and axis status into a spectral block.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Encoded profile, mesh, model and rows.** Structure `IsGivenData`: The structure packages valid explicit data and the equalities identifying it with the analytic fractional cell certificate.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Weighted polynomial inner product.** Definition `polyPair`: The definition integrates the product of two polynomials against the specified weight on a closed interval.

**Orthonormal polynomials by subtraction.** Definition `orthoFamily`: The recursive definition removes projections onto earlier polynomials from each monomial and normalizes the residual.

**Canonical radial and height bases.** Definition `canonicalBases`: The definition takes coefficients of the canonical weighted radial and unweighted height orthonormal polynomial families.

**Extend a supplied finite basis.** Definition `extendBases`: The definition preserves the supplied basis through its cutoff and uses canonical polynomials above it.

**Valid supplied orthonormal basis.** Structure `IsGivenBases`: The structure requires positive leading coefficients and radial and height orthonormality through the supplied degree cutoff.

**Angular weight at unit mode.** Definition `angularConst`: The definition evaluates the cell's angular weight at mode one.

**Scalar data generating mode weights.** Structure `WeightData`: The structure records mode cutoffs, energy and vorticity weights, absorption constants and geometric upper and lower bounds.

**Source namespace:** `Breakdown.CellCert.Reduction.WeightData`.

**Effective angular frequency for weights.** Definition `kEff`: The definition uses the actual frequency through the declared range and a fixed first-exterior frequency above it.

**Strain absorption at a frequency.** Definition `strainAt`: The definition combines the base, band-dependent penalties and inverse-frequency mean and wave terms.

**Symmetric coefficient weight.** Definition `symAt`: The definition subtracts the strain absorption from the radial-height and angular energy weight.

**Antisymmetric coefficient weight.** Definition `antiAt`: The definition combines energy and vorticity weights and subtracts curl and strain absorption.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Prescribed formulas for cell weights.** Structure `IsWeightForm`: The structure identifies the cell's resolved and band mode sets and all energy, absorption and coefficient weights with the explicit scalar formulas.

**Scalar tests ensuring positive weights.** Structure `IsWeightTests`: The structure collects positivity, geometric and model bounds and endpoint inequalities sufficient for the cell's coefficient-weight floors.

**Scalar matrix on strain coordinates.** Definition `strainScalarMatrix`: The definition places a scalar on the nine strain diagonal entries and zero on the three velocity entries.

**Tests for resolved-mode absorption.** Structure `IsResolvedTests`: The structure requires a scalar resolved matrix and bounds controlling resolved curl, strain and velocity absorption.

**Tests for far-tail weight floors.** Structure `IsFarFloorTests`: The structure requires radial, height, band and velocity endpoint inequalities for the chosen far-tail floors.

**Columnwise radial and height tail bounds.** Structure `IsTailColumnBound`: The structure requires measurable multiplier sections, nonnegative weights and uniform radial and height projection-tail bounds for each input column.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Numbers bounding row rotation.** Structure `IsRowTurnNumbers`: The structure requires angular order at least two and a nonnegative constant controlling each nonzero-harmonic row's weight times squared outer radius.

**Finite values for cell-sum estimates.** Structure `CellSumValues`: The structure records source and target geometric ranges, optional compactified charts, supremum and mass bounds and final box bounds.

**Solid with optional upper bounds.** Definition `pieceSolidOf`: The definition selects a nonnegative-height radial box whose radial and height upper endpoints may be absent.

**Solid in compactified coordinates.** Definition `chartSolid`: The definition imposes compactified radial bounds and homogeneous height-ratio bounds on spatial points.

**Source namespace:** `Breakdown.CellCert.CellSystem.CellSumValues`.

**Geometric solid of a source piece.** Definition `pieceSolid`: The definition uses a chart solid when chart data is present and the optional-endpoint radial box otherwise.

**Base cell-sum data.** Definition `baseData`: The definition copies geometric and numerical values into the analytic cell-sum format with the default sector rule and zero near length.

**Candidate near-sector fractions.** Definition `nearFactors`: The definition lists six fixed fractions used to choose a near-sector length.

**Near length from a sector fraction.** Definition `nearLength`: The definition scales the sector separation constant by the selected fraction of the angular sector width.

**Admissible near-sector length.** Definition `NearValid`: The predicate requires positive length and angular separation and finite upper radial and height bounds for the source piece.

**Value of a proposed near-sector bound.** Definition `nearValue`: The definition adds the proposed nearest-sector estimate to the remaining paired-sector sum.

**Choose the best valid near length.** Definition `bestNear`: The definition scans the fixed candidate fractions and retains the valid length with the smallest computed near-bound value.

**Choose the best kernel-sum rule.** Definition `ruleOf`: The definition chooses the least available sector, shell or near-sector estimate for a source-target pair.

**Chosen near-sector length.** Definition `lengthOf`: The definition reads the selected near length and uses zero when no valid candidate exists.

**Optimized analytic cell-sum data.** Definition `toData`: The definition equips the base cell-sum data with the selected pair rules and near lengths.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Geometry of valid cell-sum values.** Structure `IsCellSumValues`: The structure requires even angular order at least four, valid source geometry and chart enclosures, nonnegative suprema and source and target coverage.

**Numerical bounds for a cell-sum density.** Structure `IsCellSumBounded`: The structure requires source-piece supremum and mass bounds and the final sum bound on each target box.

**Numerical bounds for an adjoint dual.** Structure `IsAdjointDualNumbers`: The structure requires positive pin scales and bounds on the dual, potential, flux, inverse-square and parameter-shift terms.

**Derivative with respect to phase.** Definition `phaseDerivField`: The definition differentiates the encoded field with respect to its phase parameter.

**Second derivative with respect to phase.** Definition `phaseCurvField`: The definition differentiates the encoded field twice with respect to phase.

**Amplitude with its phase correction.** Definition `ampField`: The definition adds the parameter coefficient field to the phase derivative of the centre field multiplied by its phase step.

**Squared derivative norm.** Definition `gradSq`: The definition is the squared operator norm of the field's Fréchet derivative.

**Maximum phase variation on a box.** Definition `splitWidth`: The definition sums each parameter radius times the absolute phase step.

**Recorded constants for adjoint estimates.** Structure `AdjointNumbers`: The structure records the potential scale, dual and remainder bounds, shift bounds and exact parameter set.

**Chosen weak trace of the sharp term.** Definition `sharpTraceOf`: The definition selects a weak negative trace with square-integrable radial weight when one exists and otherwise uses zero.

**Chosen pin Hessian and negative trace.** Definition `pinSecondTraceOf`: The definition selects measurable bounded weak pin derivatives and negative trace when available and otherwise returns two zero fields.

**Chosen negative trace of the dual.** Definition `dualTraceOf`: The definition selects a weak negative trace of the dual field with square-integrable radial weight when one exists and otherwise uses zero.

**Chosen negative trace of the potential.** Definition `potentialTraceOf`: The definition selects a weak negative trace of the potential field with square-integrable radial weight when one exists and otherwise uses zero.

**Chosen weak divergence of the flux.** Definition `fluxDivOf`: The definition selects a weak matrix divergence with square-integrable radial weight when one exists and otherwise uses zero.

**Core adjoint-dual construction.** Definition `adjointDualCore`: The definition assembles encoded auxiliary fields, selected derivatives and recorded constants, initially using zero inverse-square data.

**Choose the inverse-square representative.** Definition `inverseSquareChoice`: The definition selects a measurable weighted-L² representative of the inverse-square remainder with finite harmonic support when available.

**Adjoint dual with its harmonic remainder.** Definition `adjointDualOf`: The definition inserts the selected inverse-square representative and its finite harmonic support into the core adjoint-dual data.

**All finite data attached to one cell.** Structure `CellEntry`: The structure records bases, mode classes, rows, weights, deviation bounds, far estimates and system multiplier and reducer matrices.

**Source namespace:** `Breakdown.CellCert.CellSystem.CellEntry`.

**Box of a cell entry.** Definition `box`: The definition reads the mesh box selected by the cell entry.

**Full bases of a cell entry.** Definition `bases`: The definition extends the entry's supplied finite bases with canonical higher-degree polynomials.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Complete finite cell-system data.** Structure `CellSystemData`: The structure combines the split, tree, spectral, exterior and mesh data with cell entries and global loss and adjoint bounds.

**Identify the specialized cell system.** Structure `IsSystemInstance`: The structure fixes fractional power 501/500 and matches the constant weight, exterior formulas, support, mesh moments and spectral blocks to the certificate.

**Base analytic certificate conditions.** Structure `IsBaseSystem`: The structure packages coercivity and loss bounds, contraction and defect estimates, parameter-box inclusions and nontriviality for the fractional certificate.

**Numerical cell error and spectral bounds.** Structure `IsCellNumbers`: The structure requires model-error allowances, nonnegative loss constants, spectral-level bounds and the scalar inequalities controlling the fractional split.

**Reduced loss bounds from explicit data.** Structure `IsReducedLosses`: The structure binds model, parameter and adjoint kernel estimates to the certificate's centre, row, potential and adjoint loss allowances.

**Exterior-system inequalities.** Structure `IsExteriorSystem`: The structure requires exterior strain and curl-gradient bounds and the scalar Hardy inequality ensuring exterior nonnegativity.

**Spectral-system geometry and tails.** Structure `IsSpectralSystem`: The structure requires valid separated spectral blocks, axis conditions, a positive cutoff and tail constants dominated by the certificate bound.

**Validity of supplied spectral bounds.** Structure `IsSpectralBounds`: The structure requires every supplied interval and axis certificate to satisfy its defining analytic bound.

**Multiplier slots in the split system.** Structure `IsSplitSystem`: The structure requires injective multiplier slots whose rows in the free-coordinate map vanish.

**Identify the elimination tree with cells.** Structure `IsTreeSystem`: The structure requires a valid tree, a bijection matching its cell matrices to cell and delayed forms, and the correct global matrix.

**Weight for real harmonic normalization.** Definition `systemWeight`: The definition gives weight one to zero-harmonic rows and weight two to the other rows.

**Scale converting system rows to tests.** Definition `systemScale`: The definition divides the square root of split viscosity by the real harmonic normalization weight.

**Test multiplier from the system matrix.** Definition `testMultiplierOf`: The definition conjugates the system multiplier by the diagonal row-scaling matrix.

**Test reducer from the system reducer.** Definition `testReducerOf`: The definition multiplies the system reducer by the inverse diagonal row scale.

**Combined multiplier-side row bound.** Definition `multiplierLHS`: The definition sums weighted row coefficients, class penalties and near and far unresolved row-square contributions.

**Cell data and matrix compatibility.** Structure `IsCellSystemFacts`: The structure packages cell weights, mode bounds, tail controls, row-matrix identities and coordinate and quadratic-form comparisons needed by the cell-system reduction.

### Breakdown.FracCell.StrainFace

Assembles side, corner and turning identities into the strain-face reconstruction formula.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFace.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Evaluate a row on true cell data.** Definition `ev`: The definition pairs a complex coordinate row with the field's true cell data. Source: `Breakdown.FracCell.StrainFace:15`.

**Row evaluation preserves addition.** Proved result `ev_add`: Evaluating a sum of coordinate rows gives the sum of their evaluations. Source: `Breakdown.FracCell.StrainFace:17`.

**Row evaluation preserves subtraction.** Proved result `ev_sub`: Evaluating a difference of coordinate rows gives the difference of their evaluations. Source: `Breakdown.FracCell.StrainFace:21`.

**Row evaluation preserves negation.** Proved result `ev_neg`: Evaluating the negative of a coordinate row negates its evaluation. Source: `Breakdown.FracCell.StrainFace:25`.

**Row evaluation preserves scalar factors.** Proved result `ev_smul`: Evaluating a scalar multiple of a coordinate row multiplies its evaluation by that scalar. Source: `Breakdown.FracCell.StrainFace:29`.

**A unit row reads its coordinate.** Proved result `ev_unit`: Evaluating a unit coordinate row returns the corresponding true datum. Source: `Breakdown.FracCell.StrainFace:33`.

**Finite polynomial sum has bounded degree.** Proved result `poly_sum`: A finite sum of monomials through degree D is a polynomial function of degree at most D. Source: `Breakdown.FracCell.StrainFace:43`.

**Increase a polynomial degree bound.** Proved result `poly_mono`: A polynomial function satisfying one degree bound also satisfies any larger bound. Source: `Breakdown.FracCell.StrainFace:52`.

**Differentiation lowers the degree bound.** Proved result `poly_deriv`: The derivative of a polynomial function of degree at most D has degree at most D minus one. Source: `Breakdown.FracCell.StrainFace:56`.

**The variable raises the degree bound.** Proved result `poly_mulX`: Multiplication by the variable raises the polynomial degree bound by one. Source: `Breakdown.FracCell.StrainFace:63`.

**Forget a polynomial's degree bound.** Proved result `poly_any`: A polynomial function with a specified degree bound is a polynomial function without that bound. Source: `Breakdown.FracCell.StrainFace:70`.

**Corner rows read corner values.** Proved result `corner_eval`: For a valid cell layout and a corner away from the axis, evaluating the corner row gives the encoded corner value. Source: `Breakdown.FracCell.StrainFace:74`.

**Strain faces from side identities.** Proved result `strainFace_of`: Assuming the side-evaluation, radial and height derivative, turning, and zero-trace identities, every allowed strain-face row evaluates to its physical face moment for valid cell data and admissible fields, excluding an inner axis face.

**Strain faces from strip integrability.** Proved result `strainFace_of_traces`: Strip integrability and the radial, height, turning, and zero-trace identities imply that every allowed strain-face row recovers its physical face moment, with the inner axis face excluded.

### Breakdown.FracCell.StrainFaceDefs

Defines side and corner values and separates the weak-trace obligations used by strain-face reconstruction.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceDefs.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Polynomial function with a degree bound.** Definition `IsPolyFn`: The predicate identifies a real function with a polynomial whose natural degree is at most the specified bound.

**A real polynomial function.** Definition `IsAnyPolyFn`: The predicate requires the function to equal some real polynomial everywhere.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellLayout`.

**Velocity moment on a cell side.** Definition `sideVelocityValue`: The definition uses the appropriate radial or height strip moment of a velocity mode and its derivative.

**Normal-gradient moment on a cell side.** Definition `sideGradientValue`: The definition takes the radial or height face moment of the normal gradient mode and its second derivative.

**Velocity trace at a cell corner.** Definition `cornerValue`: The definition evaluates the weak corner moment from velocity, first derivatives and the mixed second derivative.

**Turning contribution on a cell side.** Definition `turnValue`: The definition combines the angular frequency with the frame-rotation correction in each velocity component.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Side rows recover velocity moments.** Proposition `SideVelocityEvalStatement`: The interface requires side velocity rows to evaluate to the corresponding moments for polynomial tests of the allowed degree, excluding an inner axis face.

**Side rows recover gradient moments.** Proposition `SideGradientEvalStatement`: The interface requires side gradient rows to evaluate to the corresponding moments for polynomial tests of the allowed degree, excluding an inner axis face.

**Tangential derivative on a radial face.** Proposition `RadialTangentStatement`: For valid cell data and admissible fields, the interface expresses a polynomial height-gradient moment on a radial face away from the axis as endpoint corner terms minus the velocity moment of the test derivative.

**Angular derivative on a radial face.** Proposition `RadialTurnStatement`: For valid cell data and admissible fields, the interface identifies a polynomial angular-gradient moment on a radial face away from the axis with the turning contribution divided by the face radius.

**Radial derivative on a height face.** Proposition `HeightNormalStatement`: For valid cell data and admissible fields, the interface expresses a polynomial radial-gradient moment on a height face as radius-weighted corner terms minus the velocity moment of the derivative of radius times the test.

**Angular derivative on a height face.** Proposition `HeightTurnStatement`: For valid cell data and admissible fields, the interface identifies each polynomial angular-gradient moment on a height face with its turning contribution.

**Zero trace of gradient face moments.** Proposition `FaceTraceFreeStatement`: For valid cell data and admissible fields, the interface requires the sums of the three diagonal gradient moments to vanish on both radial and height faces for every polynomial test.

**Source namespace:** `Breakdown.CellCert.CellFormula.CellLayout`.

**Position of the chosen cell side.** Definition `sideLevel`: The definition selects the corresponding radial or height endpoint of the cell.

**Position of the opposite cell side.** Definition `sideOther`: The definition subtracts the chosen side level from the sum of the two matching endpoints.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Integrability of side strip formulas.** Proposition `SideStripIntegrableStatement`: The interface requires integrability of the velocity and normal-gradient strip integrands on radial and height sides, with the inner axis face excluded.

### Breakdown.FracCell.StrainFaceFaceTraceFree

Derives zero-trace identities for weak gradient modes and their face moments.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceFaceTraceFree.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.Internal.StrainFaceFaceTraceFree`.

**Cylindrical frame is orthonormal.** Proved result `frame_orth`: The sum of products of frame coordinates is one on equal Cartesian indices and zero on distinct indices.

**Trace is unchanged by the moving frame.** Proved result `mat_trace`: The trace of a linear map in the cylindrical frame equals its Cartesian trace.

**Second-derivative trace in the frame.** Proved result `third_trace`: The traced second derivative in one frame direction equals the Cartesian traced derivatives combined in that direction.

**Operator norm bounded by basis images.** Proved result `opnorm_le`: A linear map's operator norm is bounded by the sum of the norms of its Cartesian unit-vector images.

**Weak gradient is locally integrable.** Proved result `grad_loc`: The gradient witness of a second-order field is locally integrable.

**Weak Hessian is locally integrable.** Proved result `second_loc`: The second-derivative witness of a second-order field is locally integrable.

**Derivative of the divergence is zero.** Proved result `second_trace`: Each Cartesian derivative of the trace of a second-order field's gradient vanishes almost everywhere.

**Almost every circle is integrable.** Proved result `circ_int`: A locally integrable field is integrable along almost every positive-radius circle in a valid cell rectangle.

**Fourier kernel for second derivatives.** Definition `thirdKernel`: The definition multiplies a moving-frame second-derivative component by its angular Fourier phase.

**Second-derivative kernel is continuous.** Proved result `thirdKernel_cont`: The angular Fourier kernel depends continuously on the angle and second-derivative tensor.

**Second-derivative kernel norm bound.** Proved result `thirdKernel_bound`: The norm of a second-derivative Fourier kernel is at most the operator norm of the tensor.

**Second modes use the centred circle.** Proved result `third_eq`: The second-derivative Fourier mode equals its normalized integral on the interval from minus pi to pi.

**Gradient modes have zero trace.** Proved result `grad_sum`: For a second-order field, the diagonal gradient modes sum to zero almost everywhere on a valid cell.

**Second modes have zero traced sum.** Proved result `third_sum`: For a second-order field, the traced second-derivative modes sum to zero almost everywhere on a valid cell.

**Weighted second modes are integrable.** Proved result `third_int`: The second-derivative mode multiplied by the cell line weight is integrable on a valid cell rectangle.

**Continuous factors preserve weighted L¹.** Proved result `weighted`: A continuously weighted mode remains integrable after multiplication by the permitted radial factor.

**Radial trace integrands are integrable.** Proved result `radial_int`: Integrability of the field and its weighted radial derivative gives integrability of the radial strip expression with a continuous test.

**Height trace integrands are integrable.** Proved result `height_int`: Weighted integrability of a field and its height derivative gives integrability of the radius-weighted height strip expression.

**Zero sums commute with integration.** Proved result `sum3`: Three integrable functions summing to zero almost everywhere have integrals summing to zero.

**Zero trace passes to radial moments.** Proved result `radial_zero`: Integrable radial strip data with vanishing field and derivative traces have radial moments whose sum is zero.

**Zero trace passes to height moments.** Proved result `height_zero`: Integrable height strip data with vanishing field and derivative traces have weighted height moments whose sum is zero.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Gradient modes integrable at the axis.** Proposition `AxisGradModeIntegrableStatement`: The interface requires every gradient mode of a second-order field to be integrable on valid cell rectangles meeting the axis.

**Guarded zero-trace face identity.** Proved result `faceTraceFree_of`: Assuming axis-mode integrability, the three diagonal radial and height face moments sum to zero when the chosen radial face is away from the axis.

### Breakdown.FracCell.StrainFaceGuarded

Assembles strain faces while retaining the guard on the inner radial face.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceGuarded.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Evaluate a row on true cell data.** Definition `ev`: The definition pairs a complex coordinate row with the field's true cell data. Source: `Breakdown.FracCell.StrainFaceGuarded:24`.

**Row evaluation preserves addition.** Proved result `ev_add`: Evaluating a sum of coordinate rows gives the sum of their evaluations. Source: `Breakdown.FracCell.StrainFaceGuarded:26`.

**Row evaluation preserves subtraction.** Proved result `ev_sub`: Evaluating a difference of coordinate rows gives the difference of their evaluations. Source: `Breakdown.FracCell.StrainFaceGuarded:30`.

**Row evaluation preserves negation.** Proved result `ev_neg`: Evaluating the negative of a coordinate row negates its evaluation. Source: `Breakdown.FracCell.StrainFaceGuarded:34`.

**Row evaluation preserves scalar factors.** Proved result `ev_smul`: Evaluating a scalar multiple of a coordinate row multiplies its evaluation by that scalar. Source: `Breakdown.FracCell.StrainFaceGuarded:38`.

**A unit row reads its coordinate.** Proved result `ev_unit`: Evaluating a unit coordinate row returns the corresponding true datum. Source: `Breakdown.FracCell.StrainFaceGuarded:42`.

**Finite polynomial sum has bounded degree.** Proved result `poly_sum`: A finite sum of monomials through degree D is a polynomial function of degree at most D. Source: `Breakdown.FracCell.StrainFaceGuarded:52`.

**Increase a polynomial degree bound.** Proved result `poly_mono`: A polynomial function satisfying one degree bound also satisfies any larger bound. Source: `Breakdown.FracCell.StrainFaceGuarded:61`.

**Differentiation lowers the degree bound.** Proved result `poly_deriv`: The derivative of a polynomial function of degree at most D has degree at most D minus one. Source: `Breakdown.FracCell.StrainFaceGuarded:65`.

**The variable raises the degree bound.** Proved result `poly_mulX`: Multiplication by the variable raises the polynomial degree bound by one. Source: `Breakdown.FracCell.StrainFaceGuarded:72`.

**Forget a polynomial's degree bound.** Proved result `poly_any`: A polynomial function with a specified degree bound is a polynomial function without that bound. Source: `Breakdown.FracCell.StrainFaceGuarded:79`.

**Corner rows read corner values.** Proved result `corner_eval`: For a valid cell layout and a corner away from the axis, evaluating the corner row gives the encoded corner value. Source: `Breakdown.FracCell.StrainFaceGuarded:83`.

**Height-face trace vanishes.** Proved result `heightTrace`: The three diagonal height-face gradient moments of an admissible field sum to zero for every polynomial test.

**Strain-face assembly with the axis guard.** Proved result `strainFace_guarded`: Side evaluations, radial and height derivative identities, turning identities, and axis-gradient-mode integrability yield strain-face moment reconstruction for valid data and admissible fields whenever the chosen face avoids the inner axis.

**Strain faces from axis regularity.** Proved result `strainFace_of_axis`: Assuming integrability of gradient modes on rectangles meeting the axis, valid cell data and an admissible field have their allowed strain-face moments recovered by the finite coordinate rows, with the inner axis face excluded.

### Breakdown.FracCell.StrainFaceHeightNormal

Proves the radial derivative identity on height faces by weak integration by parts.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceHeightNormal.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Weak radial derivative of a height mode.** Proposition `RadialMixedWeakStatement`: The interface requires the weak radial derivative identity for height-gradient modes against tests vanishing at the radial endpoints.

**Cell rectangles are compact.** Proved result `rect_compact`: A cell's closed radial-height rectangle is compact. Source: `Breakdown.FracCell.StrainFaceHeightNormal:21`.

**Continuous factors preserve cell L¹.** Proved result `cmul`: Multiplying an integrable function on a cell rectangle by a continuous function preserves integrability.

**Real-to-complex inclusion is continuous.** Proved result `ofReal_cont`: A continuous real-valued function remains continuous when regarded as complex-valued.

**Allowed radial factors preserve L¹.** Proved result `wmul`: Weighted mode integrability implies integrability after multiplication by continuous separated factors that include a radius on axis cells.

**Height moments by radial integration.** Proved result `hbase`: Under the stated integrability and weak derivative identities, a normal-gradient height moment equals its corner contributions minus a differentiated-test velocity moment.

**Axial evaluation preserves measurability.** Proved result `ax_meas`: Evaluating a measurable second-derivative field on the axial vector gives a measurable linear-map field.

**Axial second derivatives have L² energy.** Proved result `ax_sq`: Finite second-derivative energy implies integrability of the squared entries after evaluation on the axial vector.

**Height-normal identity from weak modes.** Proved result `heightNormal_holds`: The weak radial-mode and mixed-mode identities imply that a polynomial radial-gradient moment on a height face equals radius-weighted corner terms minus the velocity moment of the derivative of radius times the test.

### Breakdown.FracCell.StrainFaceHeightTurn

Transfers angular-mode identities to height-face moments.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceHeightTurn.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.StrainFaceHeightTurn`.

**The axis has measure zero.** Proved result `axis_null`: Almost every point of the radial-height plane has nonzero radial coordinate. Source: `Breakdown.FracCell.StrainFaceHeightTurn:20`.

**Angular relations pass to strip moments.** Proved result `strip_turn`: An almost-everywhere radius-weighted linear relation and the stated integrability assumptions imply the matching linear relation between height strip moments.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Height turning from angular modes.** Proved result `heightTurn_of`: Side-strip integrability and the angular and angular-height mode identities imply that each polynomial angular-gradient moment on a height face equals its turning contribution.

**Height turning from circle integration.** Proved result `heightTurn_of_circle`: Side-strip integrability and weak circle integration by parts imply the height-turn identity.

### Breakdown.FracCell.StrainFaceRadialTangent

Builds cutoff-based weak integration by parts and proves the tangential derivative identity on radial faces.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceRadialTangent.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Mixed second-derivative modes agree.** Proposition `ModeThirdSwapStatement`: The interface requires radial-height and height-radial second modes to agree almost everywhere at positive radius.

**Height integration on a radial strip.** Proposition `RadialStripIbpStatement`: The interface requires radial-strip integrability and the weak height derivative identity against smooth tests vanishing at the height endpoints.

**Integration by parts on a closed strip.** Proposition `StripIbpStatement`: The interface transfers a weak height derivative to the weighted closed-rectangle identity for endpoint-vanishing tests.

**Source namespace:** `Breakdown.FracInternal.StripIbp`.

**Smooth cutoff inside an interval.** Definition `cut`: The definition multiplies two smooth transitions to vanish near each endpoint of the interval.

**Derivative formula for the cutoff.** Definition `cutD`: The definition is the product-rule derivative of the two endpoint transition factors.

**The smooth transition is differentiable.** Proved result `sm_diff`: The standard smooth transition is differentiable over the real numbers.

**The transition derivative is continuous.** Proved result `sd_cont`: The derivative of the standard smooth transition is continuous.

**The transition derivative vanishes away.** Proved result `sd_zero`: The transition derivative is zero below zero and above one.

**The transition derivative is bounded.** Proved result `sd_bound`: There is a nonnegative global bound on the absolute derivative of the smooth transition.

**The interval cutoff is smooth.** Proved result `cut_smooth`: The product cutoff is smooth for every choice of its scale and endpoints.

**The cutoff has its stated derivative.** Proved result `cut_hasDeriv`: The derivative of the interval cutoff equals its explicit product-rule formula.

**The cutoff vanishes near the endpoints.** Proved result `cut_zero`: For positive scale, the cutoff vanishes within that scale of either interval endpoint and outside the interval.

**The cutoff has magnitude at most one.** Proved result `cut_le`: The absolute value of the interval cutoff is at most one.

**Cutoffs eventually equal one inside.** Proved result `cut_lim`: At an interior point, sufficiently small reciprocal-scale cutoffs equal one and their derivatives equal zero.

**Derivative bounds control increments.** Proved result `h_slopeBound`: A bound on a smooth function's derivative over an interval bounds each increment by that bound times the distance.

**Uniform bound on the cutoff error.** Proved result `hcut_bound`: Endpoint linear bounds on a function give a scale-independent bound on its product with the cutoff derivative.

**The cutoff derivative is continuous.** Proved result `cutD_cont`: The explicit derivative formula for the interval cutoff is continuous.

**A vertical line has measure zero.** Proved result `line_null1`: Almost every point of the plane has first coordinate different from any fixed value.

**A horizontal line has measure zero.** Proved result `line_null2`: Almost every point of the plane has second coordinate different from any fixed value.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Closed-strip integration by parts holds.** Proved result `stripIbp_holds`: A weak height derivative with the stated weighted integrability on a nondegenerate closed rectangle satisfies integration by parts against smooth height tests that vanish at both height endpoints.

**Source namespace:** `Breakdown.CellCert.CellFormula.RadialTangentInternal`.

**A height polynomial is continuous.** Proved result `poly_cont2`: A polynomial evaluated at the height coordinate remains continuous after inclusion into the complex numbers.

**Tangential strip moment from corners.** Proved result `hbase`: With the stated integrability, mixed-derivative agreement and weak identity, the tangential strip moment equals corner terms minus the velocity moment of the test derivative.

**The axis has measure zero.** Proved result `axis_null`: Almost every point of the radial-height plane has nonzero radial coordinate. Source: `Breakdown.FracCell.StrainFaceRadialTangent:502`.

**Mode agreement restricts to a cell.** Proved result `swap_on`: An almost-everywhere identity at positive radius holds almost everywhere on any valid cell rectangle.

**Derivatives of tests are tests.** Proved result `dtest`: A fixed directional derivative of a smooth compactly supported scalar test is again a scalar test.

**Smooth mixed derivatives commute.** Proved result `mixed3`: The two directional Fréchet derivatives of a smooth scalar function agree after their directions are exchanged.

**Weak Hessian entries commute in tests.** Proved result `weak_swap`: The two orders of Cartesian weak second differentiation have the same integral against every scalar test.

**Each Hessian column belongs to L².** Proved result `col_memLp`: Measurability and finite full second-derivative energy imply L² membership of each Cartesian Hessian component vector.

**Weak Hessian symmetry almost everywhere.** Proved result `sym_ae`: The weak second derivative of a second-order field is symmetric in its two derivative inputs almost everywhere.

**Vectors expand in the Cartesian basis.** Proved result `vec_sum`: Every vector is the sum of its coordinates times the Cartesian unit vectors.

**Basis symmetry implies full symmetry.** Proved result `sym_all`: A bilinear map symmetric on Cartesian unit-vector pairs is symmetric on arbitrary vectors.

**Periodic Hessian frame components.** Proved result `frameThird_per`: A second-derivative component in the cylindrical frame has period two pi in the angle.

**Second modes on a centred interval.** Proved result `third_Ioo`: The second-derivative mode equals the normalized Fourier integral over the centred angular interval.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Mixed second modes agree.** Proved result `modeThirdSwap_holds`: The theorem proves the almost-everywhere interchange of radial and height second modes.

**Radial tangency from strip integration.** Proved result `radialTangent_of`: Assuming radial-strip integration by parts, every polynomial height-gradient moment on a radial face away from the axis equals the endpoint corner terms minus the velocity moment of the test derivative.

**Source namespace:** `Breakdown.CellCert.CellFormula.RadialTangentInternal`.

**Cell rectangles are compact.** Proved result `rect_cpt`: A cell's closed radial-height rectangle is compact.

**Cell rectangles are measurable.** Proved result `rect_ms`: A cell's radial-height rectangle is a measurable set.

**A cell lies in a bounded axis rectangle.** Proved result `rect_sub`: A valid cell rectangle lies within the rectangle from radius zero to its outer radius and the symmetric height interval.

**A continuous height factor preserves L¹.** Proved result `int_mix`: Multiplying a radially weighted integrable function by a continuous height factor preserves integrability on a cell.

**Radial cutoff times a mode is integrable.** Proved result `phi_mode`: For a square-integrable matrix field and an allowed radial side, the affine radial cutoff times its gradient mode is integrable on the cell.

**Mixed mode as an axial gradient mode.** Proved result `third_as_grad`: The radial-axial second mode equals the radial gradient mode of the Hessian evaluated on the axial vector.

**Axial Hessian entries have finite energy.** Proved result `axial_sq`: Finite full second-derivative energy implies finite entry energy after one Hessian slot is set to the axial vector.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Radial strips from the general identity.** Proved result `radialStripIbp_of`: The closed-strip integration-by-parts estimate gives integrable radial-strip representatives for a second-order field and their weak height derivative identity against smooth endpoint-vanishing tests.

**Radial tangency from the general strip.** Proved result `radialTangent_of_strip`: Assuming the closed-strip integration-by-parts estimate, every polynomial height-gradient moment on a radial face away from the axis equals its endpoint corner terms minus the velocity moment of the test derivative.

**The radial-tangent identity holds.** Proved result `radialTangent_holds`: For valid cell data and an admissible field, every polynomial height-gradient moment on a radial face away from the axis equals the endpoint corner terms minus the velocity moment of the test derivative.

### Breakdown.FracCell.StrainFaceRadialTurn

Proves angular turning identities for radial-face moments through weak radial differentiation.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceRadialTurn.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Angular-radial second-mode identities.** Proposition `TurnSecondStatement`: The interface expresses radius-weighted angular-radial second modes using angular frequency and the moving-frame gradient corrections.

**Weak radial derivative of angular modes.** Proposition `TurnRadialWeakStatement`: The interface requires integrable angular gradient modes and their weak radial derivative identity on a cell.

**The axis has measure zero.** Proved result `axis_null`: Almost every radial-height point has nonzero radius.

**Cell rectangles are measurable.** Proved result `rect_meas`: A cell's radial-height rectangle is measurable.

**Cell rectangles are compact.** Proved result `rect_compact`: A cell's closed radial-height rectangle is compact. Source: `Breakdown.FracCell.StrainFaceRadialTurn:54`.

**Algebraic correction for radial turning.** Proved result `point`: When the radius-weighted field and derivative satisfy the given relations, the strip integrand splits into its face-radius term and an exact weak-derivative correction.

**Radial factors preserve integrability.** Proved result `int_weighted`: A continuously weighted affine radial factor preserves the assumed weighted integrability, including the axis-compatible case.

**The radial strip integrand is integrable.** Proved result `int_strip`: An integrable field and weighted derivative give an integrable radial strip formula for a continuous test.

**Turning identity for the strip integral.** Proved result `hbase`: The stated angular relation, weak radial derivative and integrability assumptions give the face-radius-scaled linear identity for the strip integrals.

**Turning identity for radial moments.** Proved result `strip_turn`: Under the stated angular and weak derivative hypotheses, the radial strip moment is the corresponding velocity-moment combination divided by the face radius.

**Radial turning from four mode interfaces.** Proved result `radialTurn_of`: The angular-mode, angular-radial second-mode, radial-turning weak, and radial weak identities imply that the polynomial angular-gradient moment on a radial face away from the axis equals the turning contribution divided by the face radius.

**Kernel for the angular-radial Hessian.** Definition `tKer`: The definition multiplies the angular-radial second-derivative frame component by its Fourier phase.

**Angular-radial kernel is continuous.** Proved result `tKer_cont`: The angular-radial Fourier kernel is continuous in the angle and second-derivative tensor.

**Angular-radial kernel norm bound.** Proved result `tKer_bound`: The angular-radial Fourier kernel's norm is bounded by the tensor's operator norm.

**Angular-radial mode as a kernel integral.** Proved result `third_eq_ker`: The angular-radial second mode is its normalized kernel integral over the centred angular interval.

**Compact positive-radius sets fit a box.** Proved result `box_of`: A compact set lying at positive radius fits inside a bounded rectangle separated from the axis.

**Angular averages are integrable off axis.** Proved result `off_mode`: A bounded continuous angular kernel applied to a locally integrable field has an integrable averaged mode on every bounded rectangle away from the axis.

**Compact tests give integrable products.** Proved result `test_int`: A mode integrable on all bounded rectangles away from the axis has an integrable product with any continuous compact test supported there.

**Rectangle integrability gives local L¹.** Proved result `loc_on`: Integrability on every bounded positive-radius rectangle implies local integrability on the positive-radius half-plane.

**Cartesian basis expansion.** Proved result `vec_exp`: Every vector equals the sum of its coordinate-scaled Cartesian unit vectors.

**Operator norm is bounded by column norms.** Proved result `opNorm_cols`: The operator norm is at most the sum of the norms of the Cartesian columns.

**Evaluation preserves local L¹.** Proved result `loc_apply`: A locally integrable linear-map field remains locally integrable after evaluation at a fixed vector.

**Finite Hessian energy gives local L¹.** Proved result `loc_H`: A measurable second-derivative field with finite component energy is locally integrable.

**Polynomial extension of the frame.** Definition `uAt`: The definition extends the radial, angular and axial frame vectors to arbitrary two-dimensional coordinates.

**The extended frame matches on the circle.** Proved result `uAt_circle`: Evaluating the polynomial frame extension at cosine and sine returns the cylindrical frame.

**Frame coordinates are smooth.** Proved result `uAt_coord`: Every Cartesian component of the extended frame is smooth.

**The extended frame is smooth.** Proved result `uAt_smooth`: Each vector of the polynomial frame extension is smooth.

**Projection onto an extended frame vector.** Definition `prA`: The definition forms the continuous linear functional whose coefficients are an extended frame vector.

**Frame projection varies smoothly.** Proved result `prA_smooth`: The projection functional is smooth in the two frame parameters.

**Frame projection as an inner product.** Proved result `prA_apply`: On the unit circle, the extended projection evaluates to the inner product with the cylindrical frame vector.

**Angular column component functional.** Definition `colT`: The definition evaluates a matrix on the angular frame vector and then projects onto the selected output frame vector.

**The angular-column functional is smooth.** Proved result `colT_smooth`: The angular-column evaluation functional depends smoothly on the frame parameters.

**Angular-column evaluation in the frame.** Proved result `colT_apply`: On the unit circle, the functional returns the selected component of the matrix's angular column.

**Scale a weak integral identity.** Proved result `scaleC`: Multiplying both fields in a weak integral identity by the same complex scalar preserves the identity.

**Weak radial derivative of angular modes.** Proved result `turn_weak`: The radial weak derivative of the angular gradient mode is the corresponding angular-radial second mode for tests supported away from the axis.

**Differentiate the radial mode relation.** Proved result `combine`: The stated weak derivative identities differentiate the radius-weighted mode relation and yield its required extra minus-field term almost everywhere.

**Second modes from angular identities.** Proved result `turnSecond_of`: The angular-mode identity implies that, almost everywhere at positive radius, radius times each angular-radial second mode equals its frequency-weighted radial gradient mode with the stated moving-frame corrections.

**Radial turning from weak radial modes.** Proved result `radialTurn_of_weak`: The angular-mode and two radial weak-mode identities imply that a polynomial angular-gradient moment on a radial face away from the axis equals the turning contribution divided by the face radius.

**Gradient modes are integrable at axis.** Proposition `GradModeAxisStatement`: The interface requires every gradient mode to be integrable on bounded rectangles meeting the axis.

**Radial weak modes from axis regularity.** Proved result `turnRadialWeak_of`: Integrability of gradient modes on rectangles meeting the axis implies integrability and the weak radial derivative identity for angular gradient modes on every valid cell.

**Radial turning from axis integrability.** Proved result `radialTurn_of_axis`: Assuming gradient-mode integrability on rectangles meeting the axis, a polynomial angular-gradient moment on a radial face away from the axis equals the turning contribution divided by its radius.

**Gradient modes are integrable at axis.** Proved result `gradModeAxis`: The theorem proves gradient-mode integrability on bounded rectangles meeting the axis.

**The radial-turn identity holds.** Proved result `radialTurn_holds`: For valid cell data and an admissible field, each polynomial angular-gradient moment on a radial face away from the axis equals its turning contribution divided by the face radius.

### Breakdown.FracCell.StrainFaceSideStripIntegrable

Establishes the integrability needed for cell-side weak traces, including the axis.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceSideStripIntegrable.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.SideStripSixInternal`.

**Power bound for a mollification.** Proved result `normPow_conv_le_of_dom`: For an integer power at least one and an integrable dominating function, the norm power of a normalized mollification is bounded by the mollification of the norm power.

**Integrate a dominated nonnegative sum.** Proved result `sum_integral_le`: A finite nonnegative sum bounded by an integrable function has its summed integrals bounded by that function's integral.

**Convolution preserves a sum bound.** Proved result `conv_sum_le`: A sum of mollified squared component norms is bounded by the mollified common energy majorant.

**Mollified weak derivatives agree.** Proved result `mollify_fderiv_apply`: The Cartesian derivative of a normalized mollification equals the mollification of the corresponding weak derivative.

**L⁶ and the integral of the sixth power.** Proved result `memLp_six_iff`: For a measurable field, L⁶ membership is equivalent to integrability of the sixth power of its norm.

**Cutoff error bounded by an L⁶ tail.** Proved result `cross_tail_le`: A derivative bound for a radial cutoff controls the L² cutoff-error term by the exterior L⁶ norm.

**L⁶ tails tend to zero.** Proved result `tail_tendsto`: The L⁶ norm outside growing balls tends to zero for every L⁶ field.

**Sobolev bound for a smooth L⁶ field.** Proved result `smooth_six_of_six`: The L⁶ norm of a smooth L⁶ field is bounded by the Sobolev constant times its gradient L² norm.

**L⁶ bound for compact weak fields.** Proved result `six_bound_of_compact`: A compactly supported L² field with weak derivatives bounded by an integrable energy majorant satisfies the stated L⁶ estimate.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Weak derivative of a cutoff gradient.** Proved result `col_weak`: The weak derivative of a cutoff gradient column obeys the product rule with the cutoff derivative and Hessian column.

**Cutoff gradient columns lie in L⁶.** Proved result `col_six`: A bounded smooth compact cutoff times a gradient column of a second-order field belongs to L⁶.

**Radial kernel bounded by two columns.** Proved result `radial_kernel_le`: The radial-gradient Fourier kernel is bounded by the sum of the first two Cartesian column norms.

**A weighted sixth-power bound.** Proved result `pow_bnd`: A scalar dominated in norm admits the stated bound by an inverse radial fifth-power term plus the radial sixth-power contribution.

**Mode integrability from L⁶ domination.** Proved result `int_of_six`: An angular kernel dominated by an L⁶ field has an integrable angular average on bounded radial-height rectangles meeting the axis.

**A cylindrical box fits inside a ball.** Proved result `ball_of_box`: Every cylindrical point over the indicated bounded rectangle lies within the displayed radius bound.

**Radial gradient modes are integrable.** Proved result `radial_col_int`: Each radial gradient mode of a second-order field is integrable on a bounded rectangle meeting the axis.

**Velocity modes are integrable at axis.** Proved result `vel_col_int`: Each velocity mode of a second-order field is integrable on a bounded rectangle meeting the axis.

**Second-derivative Fourier kernel.** Definition `thirdKer`: The definition combines the second-derivative frame component with its angular phase.

**The second-mode kernel is continuous.** Proved result `thirdKer_cont`: The second-derivative Fourier kernel is continuous in the angle and tensor.

**Second-mode kernel is norm bounded.** Proved result `thirdKer_bound`: The norm of the second-derivative Fourier kernel is bounded by the tensor norm.

**Second modes as centred kernel integrals.** Proved result `third_eq`: A second-derivative mode equals its normalized kernel integral over the centred angular interval.

**Tensor norm bounded by basis components.** Proved result `bil_le`: A bilinear map's norm is bounded by the sum of the norms of all its Cartesian basis evaluations.

**Local integrability of the Hessian.** Proved result `second_loc`: The Hessian witness of a second-order field is locally integrable.

**Weighted second modes lie in L¹.** Proved result `third_weighted`: The second-derivative modes multiplied by radius are integrable on bounded radial-height rectangles.

**Continuous factors preserve L¹.** Proved result `coef_mul`: Multiplication by a continuous real function preserves integrability on a compact set.

**A valid cell fits an axis rectangle.** Proved result `rect_sub`: A valid cell rectangle is contained in its bounded symmetric-height axis rectangle.

**The opposite-endpoint interval agrees.** Proved result `icc_pair`: Either endpoint and its reflected opposite determine the original ordered closed interval.

**Radial strip pairs are integrable.** Proved result `radial_pair`: The stated velocity, gradient and weighted-Hessian integrability assumptions give integrability of both radial strip expressions.

**Height strip pairs are integrable.** Proved result `height_pair`: The stated velocity, gradient and radius-weighted Hessian assumptions give integrability of both height strip expressions.

**Side-strip integrability holds.** Proved result `sideStripIntegrable_holds`: For valid cell data and admissible fields, the velocity and normal-gradient strip integrands defining radial and height side moments are integrable, with the inner axis face excluded.

### Breakdown.FracCell.StrainFaceSides

Evaluates side coordinate rows using the analytic strip moments.

Shared cell-face machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StrainFaceSides.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Finite side rows evaluate term by term.** Proved result `row_sum`: A finite sum of weighted unit rows evaluates to the corresponding finite sum of weighted true data.

**Gradient side rows equal their moments.** Proved result `sideGradientEval_of`: Assuming side-strip integrability, every allowed side-gradient row evaluates on true cell data to the normal-gradient face moment for the corresponding polynomial test, with the inner axis face excluded.

**Velocity side rows equal their moments.** Proved result `sideVelocityEval_of`: Assuming side-strip integrability, every allowed side-velocity row evaluates on true cell data to the velocity face moment for the corresponding polynomial test, with the inner axis face excluded.

### Breakdown.FracCell.StripTrace

Constructs the zero-mode radial strip trace whose affine-weighted endpoint difference equals the integral of the radial product derivative.

Shared cell trace machinery; corresponding role in Appendix B.

Source: `lean/Breakdown/FracCell/StripTrace.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.Internal.StripTrace`.

**Rectangle integrals can be iterated.** Proved result `st_iterated`: An integrable function's rectangle integral equals the iterated radial-height integral.

**Integrated height slices are integrable.** Proved result `st_sliceInt`: Integrability on a rectangle implies integrability of the height integral as a function of radius.

**Integrable height slices almost surely.** Proved result `st_sliceAe`: An integrable rectangle function has integrable height slices for almost every radius.

**Integrate a primitive by changing order.** Proved result `st_primSwap`: The integral of an integral from the left endpoint equals the original function weighted by distance to the right endpoint.

**Affine formula for a primitive.** Proved result `st_affine`: The integral of the affine product-rule expression equals the weighted primitive values at the endpoints.

**Construct a trace from a weak derivative.** Proved result `st_core`: Local rectangle integrability and the weak radial derivative identity yield a trace whose endpoint differences represent every affine strip integral.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**The strip trace interface holds.** Proved result `stripTrace_holds`: For a second-order field and a nondegenerate height interval, the zero-frequency radial velocity has a strip-trace function whose endpoint values give the integral of every affine-weighted radial product derivative.

### Breakdown.FracCell.SystemBridgeAdjointDual

Verifies that the selected weak derivatives and encoded fields satisfy the adjoint-dual structural conditions.

Fractional cell-system reduction; analogous adjoint role in Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgeAdjointDual.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.Internal`.

**The selected sharp trace is valid.** Proved result `sharpTraceOf_spec`: Existence of a weighted-L² weak negative trace ensures the selected sharp trace has those properties.

**The selected pin derivatives are valid.** Proved result `pinSecondTraceOf_spec`: Existence of bounded measurable weak pin derivatives ensures the selected Hessian and negative trace satisfy the same conditions.

**The selected dual trace is valid.** Proved result `dualTraceOf_spec`: Existence of a weighted-L² weak negative trace ensures the selected dual trace has those properties.

**The selected potential trace is valid.** Proved result `potentialTraceOf_spec`: Existence of a weighted-L² weak negative trace ensures the selected potential trace has those properties.

**The selected flux divergence is valid.** Proved result `fluxDivOf_spec`: Existence of a weighted-L² weak matrix divergence ensures the selected flux divergence has those properties.

**The selected harmonic remainder is valid.** Proved result `inverseSquareChoice_spec`: Existence of a suitable representative ensures the selected inverse-square remainder agrees almost everywhere with the raw one and retains measurability, weighted L² membership and finite harmonic support.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Encoded data gives an adjoint dual.** Proved result `adjointDualStructure_of`: Valid explicit data at exponent 501/500, with every unit parameter index present, gives the adjoint-dual structural conditions.

### Breakdown.FracCell.SystemBridgeAdjointKernel

Turns cell-sum bounds for polynomial adjoint components into a bound for the full adjoint family.

Fractional cell-system reduction; analogous adjoint role in Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgeAdjointKernel.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.AdjointKernelInternal`.

**Integral Cauchy-Schwarz inequality.** Proved result `pair_bound`: Two nonnegative measurable L² scalar fields have integrable product bounded by the product of their L² norms.

**L² bound for a dominated finite sum.** Proved result `sum_bound`: A nonnegative measurable density dominated by a squared finite sum has its integral bounded by the squared sum of component L² bounds.

**Monomials are bounded by box radii.** Proved result `multiPow_abs_le`: Coordinatewise bounds on absolute parameter values bound the absolute monomial by the radius monomial.

**Radius monomials are nonnegative.** Proved result `multiPow_nonneg'`: A monomial of nonnegative radii is nonnegative.

**Phase stays within the box variation.** Proved result `phase_near`: The affine auxiliary phase varies by at most the sum of absolute slopes times parameter radii.

**Adjoint bound from component estimates.** Proved result `hbase`: The cell-system conditions and component weight and kernel interfaces imply the declared kernel bound for every active adjoint over the parameter box.

**Adjoint components define valid weights.** Proved result `part_weight`: Valid explicit adjoint data gives the required symmetry and integrability properties for its squared norm divided by a positive weight.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Adjoint bound from component weights.** Proved result `adjointKernel_of_weights`: The cell-system conditions and admissible component weights imply the adjoint kernel estimate on the parameter box.

**The adjoint kernel estimate follows.** Proved result `adjointKernel_of`: The cell-system condition implies the kernel bound for each active adjoint throughout the parameter box.

### Breakdown.FracCell.SystemBridgeCentreKernel

Bounds the kernel norm of profile variation by separating parameter amplitudes and a phase Taylor remainder.

Fractional certificate reduction; analogous centre-error role in Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgeCentreKernel.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.CentreKernel.Internal`.

**Derivative in the phase parameter.** Definition `partB`: The definition differentiates a function of phase and position in its real phase coordinate.

**Derivative in the spatial variable.** Definition `partY`: The definition takes the Fréchet derivative in the spatial coordinate while holding phase fixed.

**Phase slice of the full derivative.** Proved result `deriv_slice`: At a differentiable point, the phase derivative is the full derivative applied to the phase unit direction.

**Derivative of a spatial slice.** Proved result `slice_hasDeriv`: A differentiable function has the stated spatial-slice derivative obtained by composing with the spatial inclusion.

**Spatial slice of the full derivative.** Proved result `slice_deriv`: The derivative of a spatial slice applied to a vector equals the full derivative in the corresponding spatial direction.

**Smoothness gives differentiability.** Proved result `diff_of`: A function of class C^(n+1) on an open set is differentiable at each point of that set.

**Differentiation lowers smoothness by one.** Proved result `deriv_smooth`: The full derivative of a C^(n+1) function is C^n on the same open set.

**Phase partial in its coordinate.** Proved result `partB_eq`: On the open smoothness domain, the phase partial equals the full derivative in the phase direction.

**Spatial partial from the full derivative.** Proved result `partY_eq`: On the open smoothness domain, the spatial partial is the full derivative restricted to spatial inputs.

**Phase differentiation lowers smoothness.** Proved result `partB_smooth`: The phase partial of a C^(n+1) function is C^n on its open domain.

**Spatial partial lowers smoothness.** Proved result `partY_smooth`: The spatial partial of a C^(n+1) function is C^n on its open domain.

**Phase and spatial derivatives commute.** Proved result `partYB_comm`: For a C^(n+2) function on an open domain, phase and spatial differentiation commute.

**Domain of local C⁵ regularity.** Definition `goodSet`: The definition selects the points where the function is C⁵.

**The C⁵ domain is open.** Proved result `goodSet_open`: The set of points where the function is C⁵ is open.

**The function is C⁵ on its C⁵ domain.** Proved result `goodSet_smooth`: The function is C⁵ on its domain of local C⁵ regularity.

**Differentiability on the C⁵ domain.** Proved result `good_diff`: The function is differentiable at each point of its local C⁵ domain.

**Spatial slices are differentiable.** Proved result `slice_diff`: Differentiability of a function of phase and space implies differentiability of its spatial slice.

**Lower regularity on the C⁵ domain.** Proved result `good_smooth`: The function has every indicated smoothness order through five on its local C⁵ domain.

**Square-root Newton-kernel bound.** Definition `Kb`: Defines a nonnegative constant and a nonnegative almost everywhere measurable function whose squared value has an integrable Newton potential bounded everywhere by the square of that constant.

**The Newton denominator is measurable.** Proved result `den_meas`: The function four pi times distance from a fixed point is measurable.

**The Newton denominator is nonnegative.** Proved result `den_nonneg`: Four pi times the distance between two points is nonnegative.

**Measurable square-kernel integrand.** Proved result `integrand_aem`: A measurable scalar function gives an almost-everywhere measurable squared Newton-kernel integrand.

**Kernel bounds give square-root bounds.** Proved result `kb_of_kernelBound`: A kernel bound for a nonnegative density gives the corresponding square-root Newton-kernel bound.

**The zero field has zero kernel bound.** Proved result `kb_zero`: The zero function satisfies the square-root kernel bound with constant zero.

**Scale a square-root kernel bound.** Proved result `kb_smul`: Multiplication by a nonnegative scalar scales the square-root kernel bound by the same scalar.

**Decrease the field or enlarge the bound.** Proved result `kb_mono`: A nonnegative measurable function dominated almost everywhere by a kernel-bounded function inherits any larger bound.

**Split a squared sum with two weights.** Proved result `sq_split`: For positive weights, the square of a sum is bounded by the two stated weighted squares.

**Kernel bounds add.** Proved result `kb_add`: The sum of two nonnegative functions satisfies the sum of their square-root kernel bounds.

**Kernel bounds sum over a finite family.** Proved result `kb_sum`: A finite sum of functions satisfying square-root kernel bounds satisfies the sum of their constants.

**Square-root bounds give density bounds.** Proved result `kernelBound_of_kb`: A measurable function with a square-root kernel bound gives the corresponding kernel bound for its square.

**Root bound from the squared density.** Proved result `kb_of_sq`: A nonnegative measurable function inherits a square-root kernel bound from a kernel bound for its square.

**Compare real and nonnegative integrals.** Proved result `ofReal_setIntegral_le`: The nonnegative part of a nonnegative real set integral is bounded by the corresponding extended nonnegative integral.

**The integral of the unit-interval weight.** Proved result `lower_integral_id`: The nonnegative integral of the variable over the half-open unit interval is one half.

**Kernel bound for the phase remainder.** Proved result `kb_remainder`: Uniform phase-curvature kernel bounds and the stated remainder inequality give the squared-phase-step over two times the curvature bound.

**Weighted unit-interval Cauchy-Schwarz.** Proved result `weighted_sq`: The squared weighted integral of a continuous function is bounded by half its weighted square integral.

**Taylor remainder bounded by curvature.** Proved result `remainder_sq`: For a twice continuously differentiable curve, the squared backward linearization remainder is bounded by the displayed weighted second-derivative integral.

**Split constant, linear and higher terms.** Proved result `index_split`: A supported parameter polynomial separates into its constant term, unit-parameter terms and terms of total degree at least two.

**Higher monomials vanish at zero.** Proved result `monomial_zero_filter`: A monomial of total degree at least two vanishes at the zero parameter vector.

**Centre variation from component weights.** Proved result `hbase`: The cell-system conditions and component weight assumptions give the squared kernel bound for the profile-gradient difference from the centre.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**The centre-gradient kernel bound.** Proved result `centreKernelSplit_of`: The cell-system condition implies the declared kernel bound for the profile-gradient variation throughout the parameter box.

### Breakdown.FracCell.SystemBridgeRowTurn

Translates explicit row harmonics and geometric bounds into the analytic row-turning condition.

Fractional cell-system reduction; analogous rotation-loss role in Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgeRowTurn.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.RowTurnBridgeInternal`.

**Zero frequency and zero harmonic agree.** Proved result `turnMode_eq_zero_iff`: For positive angular order, a row's signed turning frequency is zero exactly when its harmonic is zero.

**Magnitude of the row turning frequency.** Proved result `abs_turnMode`: The absolute turning frequency equals the angular order times the row harmonic.

**Valid cell indexing recovers its solid.** Proved result `cellSet_pos`: The guarded cell-set lookup at a valid finite index returns the actual cell solid.

**Valid cell indexing recovers its radius.** Proved result `outer_pos`: The guarded outer-radius lookup at a valid finite index returns the actual outer radius.

**Cell solids are bounded.** Proved result `solid_bounded`: The solid associated to a cell box is bounded.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Row-turn data follows from scalar tests.** Proved result `rowTurnData_of`: Valid explicit data and the row-turn scalar conditions imply the analytic row-turn data condition.

### Breakdown.FracCell.SystemBridgeSumWeights

Verifies symmetry, decay and integrability of the weights used by cell-sum kernel estimates.

Fractional certificate reduction; shared symmetry tools analogous to Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgeSumWeights.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsInternal`.

**Discrete rotation as a linear isometry.** Definition `turnIso`: The definition packages the discrete rotation into a linear isometric equivalence.

**The rotation isometry is the turn step.** Proved result `turnIso_apply`: Applying the rotation isometry equals applying the discrete turn map.

**Reflection as a linear isometry.** Definition `mirrorIso`: The definition packages reflection into a linear isometric equivalence.

**The reflection isometry agrees.** Proved result `mirrorIso_apply`: Applying the reflection isometry equals the reflection map.

**One turn step is its angle rotation.** Proved result `turnBy_eq`: Rotation by two pi divided by the order equals the discrete turn step.

**Equivariance preserves derivative norms.** Proved result `norm_fderiv_equiv`: An isometry-equivariant field has equal derivative operator norms at points related by the isometry.

**Continuous symmetry holds everywhere.** Proved result `everywhere_of_ae`: An almost-everywhere isometry symmetry of a continuous field holds at every point.

**Derivatives commute with an isometry.** Proved result `deriv_equiv`: A curve transformed by a linear isometry has its derivative transformed by the same isometry.

**Squaring doubles the decay exponent.** Proved result `weight_sq`: The square of the radial decay weight equals the weight with twice the exponent.

**The spatial dimension is three.** Proved result `finrank_lt`: The real dimension of space is smaller than every real number greater than three.

**Symmetric field with gradient decay.** Structure `GradClass`: The structure requires C¹ regularity, discrete rotation and reflection symmetry and inverse-square derivative decay.

**Gradient decay gives a valid sum weight.** Proved result `sumWeight_gradSq`: A field in the gradient-decay class has a squared derivative norm satisfying the cell-sum weight conditions.

**Gradient classes are closed under sums.** Proved result `gradClass_add_smul`: The gradient-decay class is closed under adding a real scalar multiple of another member.

**Encoded fields respect discrete rotation.** Proved result `fieldOf_turn_all`: For positive angular order, every encoded field commutes with the discrete turn step.

**Valid encoded fields respect reflection.** Proved result `fieldOf_mirror_all`: Valid chart and field data give reflection equivariance of the reconstructed field.

**Valid encoded fields have gradient decay.** Proved result `gradClass_fieldOf`: A field reconstructed from valid chart and order-one field data belongs to the gradient-decay class.

**Phase derivatives respect rotation.** Proved result `phaseDeriv_turn`: The phase derivative of an encoded field commutes with the discrete rotation at positive angular order.

**Phase derivatives respect reflection.** Proved result `phaseDeriv_mirror`: The phase derivative of a valid encoded field commutes with reflection.

**Phase derivatives have gradient decay.** Proved result `gradClass_phaseDeriv`: The phase derivative of a valid order-one encoded field belongs to the gradient-decay class.

**Phase curvature respects rotation.** Proved result `phaseCurv_turn`: The second phase derivative of an encoded field commutes with the discrete rotation at positive angular order.

**Phase curvature respects reflection.** Proved result `phaseCurv_mirror`: The second phase derivative of a valid encoded field commutes with reflection.

**Decaying squares give sum weights.** Proved result `sumWeight_sqDiv`: A continuous symmetric field with inverse-cubic decay has a squared norm divided by a positive constant satisfying the sum-weight conditions.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsCellInternal`.

**Explicit data gives a regular centre.** Proved result `centreRegular_of`: Valid given data implies the analytic centre-field regularity condition.

**The curl contraction is continuous.** Proved result `curlOf_continuous`: The map from a derivative matrix to its curl vector is continuous.

**The cell weight is nonnegative.** Proved result `cellWeight_nonneg`: Valid explicit data gives a nonnegative cell-weight function.

**The cell weight is measurable.** Proved result `cellWeight_measurable`: The cell-weight function reconstructed from valid explicit data is measurable.

**The cell weight is bounded.** Proved result `cellWeight_bound`: The cell-weight function reconstructed from valid explicit data has a finite global upper bound.

**Cell weight depends on radius and height.** Proved result `cellWeight_congr`: Points with the same cylindrical radius and absolute height have the same cell weight.

**The cell weight respects rotation.** Proved result `cellWeight_turn`: The cell-weight function is invariant under the discrete turn step.

**The cell weight respects reflection.** Proved result `cellWeight_mirror`: The cell-weight function is invariant under reflection.

**The curl error is measurable.** Proved result `curlError_measurable`: The centre-minus-model curl error is measurable for valid explicit data.

**The curl error is bounded.** Proved result `curlError_bound`: The curl error has a finite nonnegative uniform norm bound for valid explicit data.

**Curl error vanishes outside the cells.** Proved result `curlError_zero`: The curl error is zero outside the cell region.

**The centre Hessian is measurable.** Proved result `centreSecond_measurable`: The centre's second-derivative field is measurable for valid explicit data.

**The curl-gradient error is measurable.** Proved result `curlGradError_measurable`: The curl-gradient error is measurable for valid explicit data.

**The curl-gradient error is bounded.** Proved result `curlGradError_bound`: The curl-gradient error has a finite nonnegative uniform norm bound for valid explicit data.

**Curl-gradient error vanishes outside.** Proved result `curlGradError_zero`: The curl-gradient error is zero outside the cell region for valid explicit data.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsMirrorInternal`.

**Derivatives retain equivariance.** Proved result `fderiv_equiv_apply`: The derivative of an equivariant field intertwines the same isometry on its input and output.

**Reflection sign of a coordinate.** Definition `zs`: The definition gives minus one to the axial coordinate and one to the other coordinates.

**Reflection acts by coordinate signs.** Proved result `mirror_apply`: Each coordinate of a reflected vector is its original coordinate times the corresponding reflection sign.

**Reflection of a Cartesian unit vector.** Proved result `mirror_unit`: Reflection multiplies each Cartesian unit vector by its coordinate sign.

**Reflection is an involution.** Proved result `mirror_mirror`: Reflecting a vector twice returns the original vector.

**Entries under reflection conjugation.** Proved result `entry_mirror`: Conjugating a linear map by reflection multiplies each matrix entry by its input and output reflection signs.

**Curl transforms as a pseudovector.** Proved result `curlOf_mirror`: The curl of a reflection-conjugated derivative is minus the reflection of the original curl.

**The centre field respects reflection.** Proved result `centre_mirror_all`: The centre reconstructed from valid data commutes with reflection at every point.

**Centre gradients respect reflection.** Proved result `centreGrad_mirror`: The centre derivative intertwines reflection in its point, input and output.

**Curl-error norms respect reflection.** Proved result `curlError_mirror`: The curl error has equal norm at reflected points.

**Reflection is its own inverse isometry.** Proved result `mirror_symm`: The inverse of the reflection isometry is the same reflection map.

**Conjugation of maps by reflection.** Definition `mirrorOp`: The definition conjugates a continuous linear map by the reflection equivalence.

**Reflection conjugation evaluated.** Proved result `mirrorOp_apply`: Applying the conjugated map means reflecting its input, applying the original map and reflecting its output.

**Reflection conjugation preserves norm.** Proved result `mirrorConj_norm`: A negative reflection-conjugate of a linear map has the same operator norm as that map.

**The centre Hessian is its derivative.** Proved result `centreSecond_eq_fderiv`: Valid data identifies the centre's supplied second derivative with the Fréchet derivative of its gradient.

**Centre Hessians respect reflection.** Proved result `centreSecond_mirror`: The centre Hessian transforms under reflection in the point and both derivative slots.

**Curl gradients have reflected parity.** Proved result `curlGradMatrix_mirror`: The curl-gradient matrix of a reflected Hessian is the negative reflection-conjugate of the original curl-gradient matrix.

**Curl-gradient norms reflect equally.** Proved result `curlGradError_mirror`: The curl-gradient error has equal operator norm at reflected points.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsTurnInternal`.

**Complex horizontal norm is the radius.** Proved result `plane_norm`: The norm of the first two coordinates regarded as complex equals the cylindrical radius.

**Rotation of the complex horizontal point.** Proved result `turn_plane`: The discrete turn has the stated cosine-sine action on the complex horizontal coordinate.

**Sine and cosine after rotation.** Proved result `angle_cos_sin`: Away from the axis, the angle after a turn has the sine and cosine of the original angle plus the turn angle.

**Supported harmonic phases are invariant.** Proved result `exp_turn`: For positive angular order and away from the axis, the encoded harmonic phase is invariant under one turn step.

**Harmonic polynomial values are invariant.** Proved result `harmonic_turn`: Away from the axis, the real harmonic polynomial value is invariant under the discrete turn step.

**The frame rotates with the point.** Proved result `frame_turn_angle`: Away from the axis, the frame at the rotated point is the rotated original frame.

**Frame synthesis commutes with rotation.** Proved result `cart_turn`: Away from the axis, converting frame coordinates to Cartesian vectors commutes with the discrete turn.

**Points on the axis are fixed by rotation.** Proved result `axis_fixed`: A point with zero cylindrical radius is fixed by every discrete turn.

**Model pseudovectors respect rotation.** Proved result `pseudoOf_turn`: Away from the axis, harmonic-polynomial pseudovectors commute with the discrete turn at positive angular order.

**The mesh region is rotation invariant.** Proved result `mem_region_turn`: Membership in the union of cell solids is unchanged by a discrete turn.

**The model curl respects rotation.** Proved result `modelCurl_turn`: For valid explicit data and away from the axis, the model curl commutes with the discrete turn.

**Inverse rotation on the Cartesian basis.** Proved result `turn_inv`: The displayed inverse-rotated basis vectors map back to the Cartesian basis under the discrete turn.

**Curl respects rotation conjugation.** Proved result `curlOf_turn`: When two derivative maps are related by rotation conjugation, their curls are related by the same rotation.

**The centre field respects rotation.** Proved result `centre_turn_all`: The centre reconstructed from valid data commutes with the discrete turn at every point.

**Curl-error norms respect rotation.** Proved result `curlError_turn`: The curl error has equal norm at points related by the discrete turn.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsSecondInternal`.

**Curl gradient evaluated in a direction.** Proved result `curlGradMatrix_apply`: Applying the curl-gradient matrix to a direction equals taking the curl after evaluating the Hessian in that direction.

**Isometric conjugation preserves norm.** Proved result `conj_norm`: Linear maps related by conjugation with a linear isometry have equal operator norm.

**Frame matrix synthesis respects rotation.** Proved result `cartOp_turn`: Away from the axis, a Cartesian map synthesized from frame entries transforms by rotation conjugation.

**Model pseudotensors respect rotation.** Proved result `pseudoTensorOf_turn`: Away from the axis, harmonic-polynomial pseudotensors transform by rotation conjugation.

**Centre gradients respect rotation.** Proved result `centreGrad_turn`: The centre derivative intertwines the discrete turn in its point, input and output.

**Conjugation of maps by the discrete turn.** Definition `turnOp`: The definition conjugates continuous linear maps by the discrete rotation equivalence.

**Rotation conjugation evaluated.** Proved result `turnOp_apply`: The conjugated map applied to a rotated vector equals the rotated value of the original map.

**Centre Hessians respect rotation.** Proved result `centreSecond_turn`: The centre Hessian intertwines the discrete turn in its point, both derivative inputs and output.

**Curl-gradient error norms rotate equally.** Proved result `curlGradError_turn`: The curl-gradient error has equal operator norm at points related by the discrete turn.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsCellInternal`.

**Bounded finite-support densities are L¹.** Proved result `integrable_of_region`: A bounded measurable density vanishing outside a measurable finite-volume set is integrable.

**The cell region has finite measure.** Proved result `region_facts`: The cell region reconstructed from valid explicit data is measurable and has finite volume.

**Curl-gradient error gives a sum weight.** Proved result `curlGradError_sumWeight`: The squared curl-gradient error satisfies the cell-sum weight conditions for valid data.

**Weighted curl error is a sum weight.** Proved result `curlError_sumWeight`: The squared curl error multiplied by the cell weight satisfies the cell-sum weight conditions for valid data.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**The reduction weights are valid.** Proved result `sumWeights_of`: Valid explicit data, positive normalization weight and the required unit indices give the complete set of sum-weight conditions for errors, profile amplitudes, phase curvature and adjoints.

### Breakdown.FracCell.SystemBridgeSumWeightsOpen

Proves spatial smoothness and global inverse-square derivative decay for the second phase derivative of a finite mode field.

Shared cell analysis supporting parameter-error weights; in this fractional directory it supplies the analogue of Appendix B field-enclosure estimates.

Source: `lean/Breakdown/FracCell/SystemBridgeSumWeightsOpen.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem.SumWeightsOpen`.

**Quadratic trigonometric amplitude.** Definition `quadTrig`: Defines a cosine-sine combination whose two amplitudes are quadratic polynomials in the argument.

**Derivative of a trigonometric amplitude.** Proved result `quadTrig_hasDerivAt`: Differentiating this quadratic trigonometric combination produces another combination with the displayed coefficient recurrence.

**Quadratic growth of the amplitude.** Proved result `quadTrig_bound`: The absolute value of the trigonometric combination is bounded by the sum of its six absolute coefficients times the square of one plus the absolute argument.

**Smooth trigonometric amplitude.** Proved result `quadTrig_contDiff`: Every quadratic trigonometric combination is continuously differentiable.

**Affine cosine amplitude.** Definition `cosPart`: Defines an affine amplitude multiplied by the cosine of a shifted phase.

**Affine sine amplitude.** Definition `sinPart`: Defines an affine amplitude multiplied by the sine of a shifted phase.

**Cosine-amplitude slope.** Definition `cosSlope`: Defines the product-rule expression for the first phase derivative of an affine cosine amplitude.

**Sine-amplitude slope.** Definition `sinSlope`: Defines the product-rule expression for the first phase derivative of an affine sine amplitude.

**Cosine-amplitude curvature.** Definition `cosCurv`: Defines the second phase derivative expression for an affine cosine amplitude.

**Sine-amplitude curvature.** Definition `sinCurv`: Defines the second phase derivative expression for an affine sine amplitude.

**Derivative of the phase angle.** Proved result `angle_hasDerivAt`: A shifted linear phase has derivative equal to its frequency.

**Derivative of the affine amplitude.** Proved result `lin_hasDerivAt`: An affine scalar amplitude has derivative equal to its slope.

**Derivative of the cosine amplitude.** Proved result `cosPart_hasDerivAt`: The derivative of the affine cosine amplitude equals the specified cosine-slope expression.

**Derivative of the sine amplitude.** Proved result `sinPart_hasDerivAt`: The derivative of the affine sine amplitude equals the specified sine-slope expression.

**Second cosine derivative.** Proved result `cosSlope_hasDerivAt`: The cosine-slope expression has derivative equal to the specified curvature expression.

**Second sine derivative.** Proved result `sinSlope_hasDerivAt`: The sine-slope expression has derivative equal to the specified curvature expression.

**Cosine curvature in polynomial form.** Proved result `cosCurv_eq`: When its frequency is a mode number times a variable, the cosine curvature is the displayed quadratic trigonometric combination in that variable.

**Sine curvature in polynomial form.** Proved result `sinCurv_eq`: When its frequency is a mode number times a variable, the sine curvature is the negative of the displayed quadratic trigonometric combination.

**Vectors commute with finite sums.** Proved result `ofComponents_sum`: Forming a vector from componentwise finite sums gives the finite sum of the corresponding vectors.

**Finite decomposition into modes.** Proved result `fieldOf_modeSum`: The reconstructed field is the finite sum of its individual mode fields.

**The zero mode is phase independent.** Proved result `mode_zero_const`: The mode with index zero agrees with its value at phase zero for every phase.

**Rotation formula for a nonzero mode.** Proved result `mode_rot`: A nonzero mode at an arbitrary phase is expressed through its values at phases zero and one, their quarter turns, and affine trigonometric coefficients.

**Mode slope vector.** Definition `slopeVec`: Defines the first phase derivative candidate of a mode by differentiating its trigonometric coefficients, with zero slope for the zero mode.

**Mode curvature vector.** Definition `curvVec`: Defines the second phase derivative candidate of a mode by differentiating its trigonometric coefficients twice, with zero curvature for the zero mode.

**Derivative of an individual mode.** Proved result `mode_hasDerivAt`: Each mode field has the declared slope vector as its phase derivative at every spatial point.

**Derivative of the mode slope.** Proved result `slope_hasDerivAt`: Each mode slope has the declared curvature vector as its phase derivative.

**Curvature is the sum of mode curvatures.** Proved result `phaseCurv_eq`: The second phase derivative field equals the finite sum of the individual mode-curvature vectors.

**Smooth fields with derivative decay.** Definition `Good`: Defines the property of being continuously differentiable with a derivative bounded by a constant times inverse radius squared outside some ball.

**Derivative decay survives addition.** Proved result `good_add`: The sum of two continuously differentiable fields with eventual inverse-square derivative bounds has the same property.

**The zero field has derivative decay.** Proved result `good_zero`: The zero field is continuously differentiable and satisfies an eventual inverse-square derivative bound.

**Derivative decay survives finite sums.** Proved result `good_sum`: A finite sum of continuously differentiable fields with eventual inverse-square derivative bounds has the same property.

**The logarithmic phase is smooth.** Proved result `logPhase_contDiff`: The logarithmic phase is continuously differentiable for every chart parameter choice.

**Derivative of the logarithmic phase.** Proved result `logPhase_hasFDerivAt`: For valid chart parameters, the phase derivative is inner product with the spatial point divided by the squared core radius plus squared radius.

**Inverse-radius phase derivative.** Proved result `logPhase_fderiv_le`: For valid chart parameters and a nonzero spatial point, the norm of the logarithmic-phase derivative is at most the reciprocal radius.

**The logarithmic phase is nonnegative.** Proved result `logPhase_nonneg`: The logarithmic phase is nonnegative at every spatial point.

**Logarithmic growth fits a power bound.** Proved result `logPhase_growth`: For valid chart parameters, the square of one plus the logarithmic phase is bounded outside the unit ball by a nonnegative constant times radius to the chart exponent.

**Decay absorbs logarithmic amplitudes.** Proved result `good_piece`: Multiplying a continuously differentiable field with the stated stronger field and derivative decay by a quadratic trigonometric function of logarithmic phase preserves inverse-square derivative decay.

**Smoothness of a nonzero mode.** Proved result `mode_contDiff_wave`: For valid chart and field data, every included nonzero mode is continuously differentiable in space at any fixed phase.

**Weighted modes retain derivative decay.** Proved result `good_mode`: For valid chart and field data, any included nonzero mode multiplied by a quadratic trigonometric function of logarithmic phase has eventual inverse-square derivative decay.

**Every mode curvature has decay.** Proved result `good_curvVec`: For valid chart and field data, each included mode-curvature field is continuously differentiable and has eventual inverse-square derivative decay.

**Global form of derivative decay.** Proved result `weighted_of_good`: A continuously differentiable field with eventual inverse-square derivative decay has a global derivative bound by a constant times one plus radius to power minus two.

**Regularity of the phase curvature.** Proved result `phaseCurv_regular`: For valid chart and field data, the second phase derivative field is continuously differentiable and its spatial derivative satisfies a global inverse-square weight bound.

### Breakdown.FracCell.SystemBridgesMatrix

Transfers a certified system quadratic inequality to the test multiplier and restricted row multiplier matrices.

Fractional cell-system assembly corresponding to the finite matrix bounds used in Appendix B.

Source: `lean/Breakdown/FracCell/SystemBridgesMatrix.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Transfer of the reducer inequality.** Proved result `testReducer_bound_of_system`: With positive split viscosity, the system-reducer quadratic bound implies the corresponding test-reducer bound by the Euclidean square norm.

**Restrict a supported quadratic form.** Proved result `quad_restrict`: If a vector vanishes outside a finite index set, its matrix quadratic form equals the double sum over that set.

**Restrict a supported matrix.** Proved result `quad_restrict'`: If a matrix vanishes whenever either index lies outside a finite set, its restricted double sum equals its full quadratic form.

**Quadratic forms under congruence.** Proved result `congr_quad`: Applying a matrix transpose to the argument of a quadratic form equals applying the congruence-transformed matrix to the original argument.

**Certified row multiplier.** Proved result `rowMultiplier_of_test`: Cell-system facts, an orthonormal test mixing identity, and block-preserving mixing imply symmetry, row support, domination of the multiplier expression, and the reducer square-norm bound for the row multiplier matrix.

### Breakdown.FracCell.SystemBridgesSplit

Bounds a parameter-dependent profile's displacement from its centre using first-order amplitudes, higher parameter monomials, and phase curvature.

Fractional parameter-box enclosure analogous to Appendix B error estimates.

Source: `lean/Breakdown/FracCell/SystemBridgesSplit.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.GivenFields`.

**Complex embedding preserves smoothness.** Proved result `ofReal_cd`: A twice continuously differentiable real function remains twice continuously differentiable when regarded as complex valued.

**Smooth real-to-complex embedding.** Proved result `ofReal_cd'`: The inclusion of the real line into the complex plane is twice continuously differentiable.

**Smooth phase dependence of a component.** Proved result `reduced_contDiff`: Every component of a reduced mode field is twice continuously differentiable in the phase parameter.

**Smooth phase dependence of the field.** Proved result `fieldOf_contDiff`: At each spatial point, the reconstructed field is twice continuously differentiable in phase.

**The curvature is the second derivative.** Proved result `phaseCurv_genuine`: The phase-curvature field is the derivative of the phase-derivative field at each spatial point.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Taylor bound from the endpoint slope.** Proved result `expansion_end`: For a twice continuously differentiable vector-valued function with second derivative bounded along the relevant interval, the remainder using the endpoint derivative is at most half the squared displacement times that bound.

**The phase is affine in parameters.** Proved result `phase_split`: If each declared phase step equals minus twice the profile power, symmetry order, and corresponding rate slope, the profile phase equals its central phase plus the linear parameter increment.

**A degree-one multi-index is a unit.** Proved result `sum_one`: A natural-number multi-index whose entries sum to one has exactly one unit entry and all remaining entries zero.

**Uniform displacement of the profile.** Proved result `centreSup`: Under the phase-step identity, phase-width bound, index inclusion, and the stated amplitude, higher-term, and curvature bounds, every parameter in the box has the displayed uniform displacement bound from the central profile.

**The cell system bounds centre error.** Proved result `centreSupSplit_of`: The cell-system condition guarantees that the profile's displacement from the centre is bounded pointwise by its declared central supremum estimate throughout the parameter box.

### Breakdown.FracCell.SystemBridgesSums

Converts finite piece and box data into valid integral-sum estimates, checking measurable solids and near-sector rules.

Shared enclosure machinery underlying Appendix B style spatial sums in the fractional cell construction.

Source: `lean/Breakdown/FracCell/SystemBridgesSums.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Rotations preserve height.** Proved result `turnBy_two`: Rotation about the axis leaves the third spatial coordinate unchanged.

**Rotations preserve horizontal radius.** Proved result `horizontalNorm_turnBy`: Rotation about the axis preserves horizontal radius.

**Rotations preserve spatial norm.** Proved result `norm_turnBy`: Rotation about the axis preserves the Euclidean norm.

**Reflection reverses height.** Proved result `mirror_two`: The mirror map negates the third spatial coordinate.

**Reflection preserves horizontal radius.** Proved result `horizontalNorm_mirror`: The mirror map preserves horizontal radius.

**Measurable horizontal radius.** Proved result `measurable_horizontalNorm`: Horizontal radius is a measurable real-valued function of the spatial point.

**Measurable height coordinate.** Proved result `measurable_coord_two`: The third spatial coordinate is measurable.

**Measurable cylindrical piece.** Proved result `pieceSolidOf_measurable`: A solid specified by lower and optional upper radial and height bounds is measurable.

**Measurable chart solid.** Proved result `chartSolid_measurable`: The solid represented by a rectangular chart box is measurable.

**Measurable stored piece solid.** Proved result `pieceSolid_measurable`: Every solid piece in the finite sum data is measurable.

**Piece solids are rotation invariant.** Proved result `pieceSolid_turn`: Membership in each stored piece solid is unchanged by arbitrary axial rotation.

**Stored piece bounds contain the solid.** Proved result `pieceSolid_box`: For valid finite sum data, every point of a stored piece satisfies its lower radial and height bounds and every specified upper bound.

**An optional fold preserves invariants.** Proved result `foldl_inv`: If each successful fold step preserves a predicate from any successful accumulator, every successful result of the list fold satisfies that predicate.

**The selected near estimate is valid.** Proved result `bestNear_valid`: Every successful near-sector estimate selected by the search satisfies the required near-validity predicate.

**The near rule has positive parameters.** Proved result `toData_near_valid`: Whenever conversion selects the near-sector rule, its sector length and sector constant are positive and both piece upper bounds are present.

**Construct valid integral-sum data.** Proved result `cellSumData_holds`: Valid finite sum values, the declared pointwise weight bounds, and a valid symmetric sum weight together construct valid integral-sum data.

**Finite values yield integral-sum data.** Proved result `cellSumData_of`: Valid finite sum values, boundedness, and the sum-weight condition imply that their converted representation satisfies every integral-sum-data requirement.

### Breakdown.FracCell.TreeFinal

Combines local matrix inequalities on a certificate tree with a state bound to prove nonnegativity of the original quadratic quantity.

Shared finite-dimensional certificate elimination corresponding to Appendix B and the final coercivity step.

Source: `lean/Breakdown/FracCell/TreeFinal.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Finite.TreeFinalInternal`.

**Quadratic evaluation is additive.** Proved result `quad_add`: Evaluating the quadratic form of a sum of two matrices equals the sum of their quadratic evaluations.

**The zero matrix has zero quadratic form.** Proved result `quad_zero`: The quadratic form of the zero matrix vanishes at every vector.

**Every quadratic form vanishes at zero.** Proved result `quad_at_zero`: Every matrix quadratic form evaluates to zero at the zero vector.

**Quadratic evaluation of a finite sum.** Proved result `quad_sum`: The quadratic form of a finite matrix sum equals the finite sum of the individual quadratic forms.

**The root front is bounded by cells.** Proved result `front_root_le`: For a valid tree certificate, the root-front quadratic form is at most the sum of all cell quadratic forms at every state vector.

**Source namespace:** `Breakdown.CellCert.Finite`.

**A tree certificate proves positivity.** Proved result `tree_final`: A valid tree certificate, nonpositive value at zero, and the stated state bound by the sum of cell and global forms imply that the original quadratic quantity is nonnegative for every input.

### Breakdown.FracCell.TrueParam

Shows that the true cell moments are fixed by the chosen relation-based parametrization.

Shared reconstruction of cell data from the finite relation system in Appendix B.

Source: `lean/Breakdown/FracCell/TrueParam.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**True moments survive parametrization.** Proved result `trueParam_of`: Assuming the relation and parameter-recovery statements, valid cell data and a valid selected parametrization send the true moments of every admissible field to those same moments.

### Breakdown.FracCell.UnresolvedChargeFinite

Bounds finite sums of unresolved modal charge by the total row charge and proves the needed integrability.

Fractional unresolved-mode estimates analogous to the tail charges in Appendix B.

Source: `lean/Breakdown/FracCell/UnresolvedChargeFinite.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.UnresolvedChargeFinite.Internal`.

**Measurable cell rectangle.** Proved result `rect_measurable`: Every cell rectangle is a measurable subset of the radial-height plane.

**Row-charge density is nonnegative.** Proved result `density_nonneg`: Positive class row weights make the modal row-charge density nonnegative at every radial-height point.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Finite modal charges fit the row charge.** Proved result `unresolvedChargeFinite_holds`: For valid fractional form and cell data, an axisymmetric weight, and an admissible field, each finite unresolved modal-charge sum times radius is integrable and its integral is bounded by the unresolved row charge.

### Breakdown.FracCell.UnresolvedEnergy

Controls the unresolved gradient-mode energy by the cylindrical integral of second-derivative mode energy.

Shared weighted mode estimates used in fractional cell coercivity, analogous to Appendix B tail estimates.

Source: `lean/Breakdown/FracCell/UnresolvedEnergy.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Inverse cylindrical coordinates.** Proved result `symm_apply`: The inverse cylindrical map sends radius, angle, and height to the usual Cartesian coordinates with cosine and sine.

**Measurable cylindrical inverse.** Proved result `symm_meas`: The inverse cylindrical coordinate map is measurable.

**Null sets survive cylindrical pullback.** Proved result `symm_qmp`: The inverse cylindrical map is quasi-measure-preserving from volume restricted to its cylindrical target to Cartesian volume.

**Measurable Hessian in cylindrical form.** Proved result `second_comp_meas`: For a second-order field, its second derivative composed with inverse cylindrical coordinates is almost everywhere strongly measurable on the coordinate target.

**Continuous coordinate embedding.** Proved result `single_cont`: Embedding a real scalar into one fixed Euclidean coordinate is continuous.

**Continuous moving frame.** Proved result `frameUnit_cont`: Each cylindrical frame vector depends continuously on the angle.

**Continuous frame evaluation.** Proved result `frameThird_cont`: Evaluating a bilinear vector map on cylindrical frame vectors and taking a frame component is continuous jointly in angle and the map.

**Second-derivative Fourier integrand.** Definition `kern`: Defines the third-order frame component of a second derivative multiplied by the negative-frequency angular exponential.

**The Fourier integrand is periodic.** Proved result `kern_periodic`: The second-derivative Fourier integrand has period two pi in its angular argument.

**A mode is an angular average.** Proved result `mode_eq`: A second-derivative mode coefficient is the angular integral of its Fourier integrand over minus pi to pi, divided by two pi.

**Measurable Fourier integrand.** Proved result `kern_meas`: For a second-order field, each second-derivative Fourier integrand is almost everywhere strongly measurable on positive radii, all heights, and the angular interval.

**Measurable second-derivative mode.** Proved result `mode_meas`: For a second-order field, every second-derivative mode coefficient is almost everywhere strongly measurable on the positive radial half-plane.

**Coordinate expansion of a vector.** Proved result `coord_expand`: Every spatial vector is the sum of its coordinate values times the coordinate unit vectors.

**Bilinear evaluation from entries.** Proved result `apply_bound`: If both argument vectors have coordinates of absolute value at most one, the norm of a bilinear map applied to them is at most the sum of the norms of its coordinate entries.

**Frame coordinates are bounded by one.** Proved result `frameUnit_coord`: Every coordinate of a cylindrical frame vector has absolute value at most one.

**Frame vectors have unit norm.** Proved result `frameUnit_norm`: Every cylindrical frame vector has Euclidean norm one.

**Frame component square from entries.** Proved result `frameThird_sq`: The square of a frame component of a bilinear vector map is bounded by nine times the sum of the squared norms of its coordinate entries.

**Fourier-integrand square bound.** Proved result `kern_sq`: The squared norm of the second-derivative Fourier integrand is at most nine times the sum of squared coordinate-entry norms of the second derivative.

**Square of an angular integral.** Proved result `sq_integral_le`: A measurable complex integrand whose squared norm is bounded by an integrable function has squared integral norm at most two pi times the integral of that bound.

**Sum of squared second-derivative entries.** Definition `entrySqSum`: Defines the sum of squared norms of all coordinate entries of the second derivative.

**Integrable mode energy on the half-plane.** Proved result `mode_integrable_half`: For a second-order field, radius times the squared norm of each second-derivative mode is integrable over positive radii and all heights.

**Integrable mode energy on a cell.** Proved result `mode_integrable`: For a valid cell and second-order field, radius times the squared norm of each second-derivative mode is integrable on the cell rectangle.

**Measurable cell rectangle.** Proved result `rect_meas`: Every cell rectangle is measurable in the radial-height plane. Source: `Breakdown.FracCell.UnresolvedEnergy:324`.

**Normalized radius has square at most one.** Proved result `refR_sq_le`: Within the radial interval of a valid cell, the squared reference radial coordinate is at most one.

**Normalized height has square at most one.** Proved result `refZ_sq_le`: Within the height interval of a valid cell, the squared reference height coordinate is at most one.

**The frame weight is bounded by radius.** Proved result `frame_weight`: For a valid cell, a radius above its inner boundary, and a factor between zero and one, inner radius times line weight times that factor lies between zero and the radius.

**The angular weight is bounded by radius.** Proved result `angular_weight`: On a valid cell's radial interval, angular weight times line weight times squared radius lies between zero and the radius.

**Comparison of weighted mode energies.** Proved result `weighted_le`: If a weight lies between zero and radius on the cell and the radius-weighted squared mode is integrable, its weighted integral is at most the radius-weighted integral.

**Radial frame energy bound.** Proved result `radial_term`: For a valid cell and an integrable radius-weighted squared mode, the inner-radius-scaled radial frame energy is at most its radius-weighted energy.

**Height frame energy bound.** Proved result `height_term`: For a valid cell and an integrable radius-weighted squared mode, the inner-radius-scaled height frame energy is at most its radius-weighted energy.

**Angular frame energy bound.** Proved result `angular_term`: For a valid cell and an integrable radius-weighted squared mode, the angularly weighted line norm of radius times that mode is at most its radius-weighted energy.

**Unresolved gradients fit Hessian energy.** Proved result `unresolvedEnergy`: For every valid cell and second-order field, the summed radial, height, and angular weighted gradient-mode energies are bounded by the radius-weighted integral of the corresponding second-derivative mode energy.

### Breakdown.FracCell.UnresolvedPairIntegrable

Develops weighted square-integrability rules and applies them to unresolved velocity and strain row pairings.

Fractional unresolved-mode analysis needed before integrating Appendix B style class bounds.

Source: `lean/Breakdown/FracCell/UnresolvedPairIntegrable.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.UnresolvedPairIntegrable`.

**Weighted square-integrability.** Definition `WeightedSq`: Defines a complex function on a cell to be almost everywhere strongly measurable with integrable line-weighted squared norm.

**Measurable boundedness on a cell.** Definition `BoundedOn`: Defines a complex function on a cell to be almost everywhere strongly measurable and uniformly bounded there by a real constant.

**The line weight is nonnegative.** Proved result `lw_nonneg`: The line weight is nonnegative at every point of a valid cell rectangle.

**Measurable line weight.** Proved result `lw_meas`: The cell line weight is almost everywhere strongly measurable on the cell rectangle.

**Weighted square-integrability of sums.** Proved result `ws_add`: On a valid cell, the sum of two weighted square-integrable complex functions remains weighted square-integrable.

**Weighted square-integrability of errors.** Proved result `ws_sub`: On a valid cell, the difference of two weighted square-integrable complex functions remains weighted square-integrable.

**The zero function has finite energy.** Proved result `ws_zero`: The zero function is weighted square-integrable on every cell.

**Finite sums preserve weighted energy.** Proved result `ws_sum`: On a valid cell, a finite sum of weighted square-integrable functions remains weighted square-integrable.

**Bounded left multiplication.** Proved result `ws_bdd_mul`: On a valid cell, multiplying a weighted square-integrable function on the left by a measurable bounded function preserves weighted square-integrability.

**Bounded right multiplication.** Proved result `ws_mul_bdd`: On a valid cell, multiplying a weighted square-integrable function on the right by a measurable bounded function preserves weighted square-integrability.

**Constant functions are bounded.** Proved result `bdd_const`: Every complex constant defines a measurable bounded function on a cell.

**Constant scaling preserves energy.** Proved result `ws_const_mul`: On a valid cell, multiplying a weighted square-integrable function by a complex constant preserves weighted square-integrability.

**Conjugation preserves boundedness.** Proved result `bdd_conj`: Complex conjugation preserves measurable boundedness on a cell.

**Conjugation preserves weighted energy.** Proved result `ws_conj`: Complex conjugation preserves weighted square-integrability on a cell.

**The weighted pairing is integrable.** Proved result `pair_int`: On a valid cell, the line weight times one weighted square-integrable function times the conjugate of another is integrable.

**Axial lift of a vector field.** Definition `lift`: Defines a vector field's operator-valued lift by multiplying its value by the axial coordinate of the operator argument.

**The axial column recovers the vector.** Proved result `frame_lift`: The axial column of a lifted vector's cylindrical frame matrix equals the vector's cylindrical frame components.

**A vector mode is a lifted matrix mode.** Proved result `modeVec_lift`: Every cylindrical vector-mode component equals the axial-column gradient-mode coefficient of its lifted operator field.

**Measurability of the axial lift.** Proved result `lift_meas`: The axial lift of an almost everywhere strongly measurable vector field is almost everywhere strongly measurable.

**Finite energy of the axial lift.** Proved result `lift_sq`: A square-integrable vector field has an integrable sum of squared entries after axial lifting.

**Vector modes have weighted finite energy.** Proved result `ws_mode`: On a valid cell, every component of every angular mode of a square-integrable vector field is weighted square-integrable.

**An angular mode inherits a uniform bound.** Proved result `mode_norm_le`: If a vector field is bounded by a constant around a cylindrical circle, each component of its angular mode has norm at most that constant.

**Bounded fields give bounded cell modes.** Proved result `bdd_mode`: On a valid cell, an almost everywhere strongly measurable vector field uniformly bounded over all cell circles has measurable bounded mode components.

**Cell circles lie in the solid.** Proved result `cyl_mem_solid`: Every cylindrical point obtained from a radial-height point in a valid cell rectangle lies in its cell solid.

**The radial conversion factor is bounded.** Proved result `bdd_rHat`: On a valid cell, the radial conversion factor is a measurable bounded complex-valued function.

**Finite energy of bounded cross products.** Proved result `ws_cross_bdd`: On a valid cell, each component of the cross product of a componentwise bounded vector with a componentwise weighted square-integrable vector is weighted square-integrable.

**Finite energy survives reversed crossing.** Proved result `ws_cross_ws`: On a valid cell, each component of the cross product in the reversed order is weighted square-integrable under the same boundedness and square-integrability hypotheses.

**The curl adjoint preserves finite energy.** Proved result `ws_curlAdj`: On a valid cell, every entry of the curl-adjoint matrix of a componentwise weighted square-integrable vector is weighted square-integrable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Integrable unresolved row pairings.** Proved result `unresolvedPairIntegrable_holds`: For valid fractional form and cell data, an axisymmetric weight, and an admissible field, every selected row pairing at an unresolved mode is integrable on the cell rectangle.

### Breakdown.FracCell.UnresolvedRowClass

Restricts unresolved row interactions to finite frequency support and integrates pointwise class bounds.

Fractional class-charge estimate corresponding to the unresolved-frequency part of Appendix B coercivity.

Source: `lean/Breakdown/FracCell/UnresolvedRowClass.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.UnresolvedRowClass`.

**All class frequencies.** Definition `allClassModes`: Defines the finite union of the frequency sets belonging to all classes.

**Possible unresolved pairing frequencies.** Definition `pairSupport`: Defines the finite set of selected-row frequencies and their negatives shifted by every class frequency.

**Measurable cell rectangle.** Proved result `rect_meas`: Every cell rectangle is measurable in the radial-height plane. Source: `Breakdown.FracCell.UnresolvedRowClass:21`.

**Almost every point avoids the axis.** Proved result `axis_null_ae`: The radial coordinate is nonzero at almost every point of the radial-height plane.

**Almost every cell point is interior.** Proved result `open_rect_ae`: Almost every point of a cell rectangle lies in its open interior and has nonzero radial coordinate.

**Couplings vanish outside finite support.** Proved result `coupling_zero`: For valid cell data and a selected row, an unresolved frequency outside the finite pairing support makes both velocity and curl cross couplings zero at every interior cell point away from the axis.

**Finite support of unresolved pairings.** Proved result `pairAt_zero`: Under valid cell data, a selected row's unresolved pairing integrand vanishes at interior points away from the axis whenever the frequency lies outside the finite pairing support.

**The row pairing is a real integral.** Proved result `rowPair_eq`: If the complex unresolved integrand is integrable whenever the mode is unresolved, the stored unresolved row pairing equals the integral of its real pointwise counterpart.

**The real pairing is integrable.** Proved result `point_integrable`: Integrability of the complex integrand at unresolved modes implies integrability of the real pointwise pairing, which is zero at resolved modes.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Integrated unresolved class bound.** Proved result `unresolvedRowClass_of`: Assuming the pointwise bound, pairing integrability, class square bound, and finite-charge bound, the negative twice unresolved row pairing is at most the class-weighted row coefficient squares plus the unresolved row charge.

### Breakdown.FracCell.UnresolvedRowClassSt

Defines unresolved row pairings and class charges and states the four analytic obligations needed to integrate their pointwise bound.

Fractional interface layer for the unresolved-frequency part of Appendix B style row coercivity.

Source: `lean/Breakdown/FracCell/UnresolvedRowClassSt.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Unresolved complex row integrand.** Definition `unresolvedPairAt`: Defines the line-weighted sum of the strain-mode pairing with its row coupling and the velocity-mode pairing with its row coupling.

**Unresolved real pairing density.** Definition `unresolvedPairPoint`: Defines the real part of the unresolved complex row integrand, with value zero for modes in the resolved set or band.

**Unresolved modal charge density.** Definition `unresolvedChargePoint`: Defines the unresolved charge as the sum over classes of twice the row weight times velocity-deviation and curl-deviation square penalties, with zero charge for resolved or band modes.

**Squared row combination in a class.** Definition `classRowSq`: Defines the sum over row frequencies of squared vector norms of the row combination whose selected rows belong to a given class.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Pointwise unresolved class inequality.** Proposition `UnresolvedRowPointStatement`: Specifies that valid fractional cell data, an axisymmetric weight, an admissible field, and supported row coefficients bound each finite unresolved pairing sum at interior points away from the axis by radius times modal charge plus reciprocal-weighted class row squares.

**Integrable unresolved pairings.** Proposition `UnresolvedPairIntegrableStatement`: Specifies that for valid fractional form and cell data, an axisymmetric weight, and an admissible field, each selected row's complex unresolved pairing integrand is integrable on the cell rectangle.

**Class row square interface.** Proposition `ClassRowSqStatement`: Specifies that under valid fractional cell data and an axisymmetric weight, radius times each class row square is integrable and its integral is at most the sum of the relevant coefficient squares divided by four pi.

**Finite unresolved charge interface.** Proposition `UnresolvedChargeFiniteStatement`: Specifies that under valid fractional cell data, an axisymmetric weight, and an admissible field, every finite modal-charge sum times radius is integrable and its integral is at most the unresolved row charge.

### Breakdown.FracCell.UnresolvedRowPoint

Proves finite Fourier convolution and classwise estimates for the pointwise unresolved row pairing.

Fractional local mode algebra supporting the unresolved class-charge bound analogous to Appendix B.

Source: `lean/Breakdown/FracCell/UnresolvedRowPoint.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.UnresolvedRowPoint`.

**Complex scalar triple product.** Definition `tri`: Defines the scalar triple product of three complex three-component vectors by its coordinate determinant formula.

**Scaling a triple product.** Proved result `tri_smul`: Scaling the three arguments scales the triple product by the product of the three scalars.

**A sum in the first triple-product slot.** Proved result `tri_sum_left`: The triple product distributes over a finite sum in its first vector argument.

**A sum in the middle triple-product slot.** Proved result `tri_sum_mid`: The triple product distributes over a finite sum in its second vector argument.

**A sum in the last triple-product slot.** Proved result `tri_sum_right`: The triple product distributes over a finite sum in its third vector argument.

**Three-dimensional Cauchy-Schwarz.** Proved result `dotSq3`: The square of a real three-component scalar product is at most the product of the two sums of squares.

**The cross-product square bound.** Proved result `cross_sq`: The squared norm sum of a complex cross product is at most the product of the two squared norm sums.

**Complex scalar-product square bound.** Proved result `dot_sq`: The squared norm of the bilinear scalar product of two complex three-component vectors is at most the product of their squared norm sums.

**A triple product is a scalar product.** Proved result `tri_eq_dot`: The scalar triple product equals the first vector's bilinear scalar product with the cross product of the second and third vectors.

**The triple-product square bound.** Proved result `tri_sq`: The squared norm of the complex triple product is at most the product of the three squared norm sums.

**Two-product weighted inequality.** Proved result `twoProductBound`: For positive weight, twice the sum of two real factors times a third is bounded by twice the weight times the first two squares plus the third square divided by the weight.

**Equally spaced Fourier phase.** Definition `ee`: Defines the complex exponential for an integer frequency at an equally spaced angular sample.

**Multiplication adds sampled frequencies.** Proved result `ee_mul`: The product of two sampled Fourier exponentials equals the exponential at the sum of their frequencies.

**Conjugation reverses sampled frequency.** Proved result `ee_conj`: Complex conjugation changes the sign of the sampled Fourier frequency.

**The sampled zero frequency is one.** Proved result `ee_zero`: The sampled exponential at frequency zero equals one.

**Samples are powers of one phase.** Proved result `ee_pow`: The exponential at sample index j is the j-th power of the first sampled phase.

**Discrete Fourier orthogonality.** Proved result `ee_sum`: For a positive sample count and an integer frequency strictly between its negative and positive values, the sum of sampled exponentials equals the sample count at zero frequency and zero otherwise.

**A norm square is a conjugate product.** Proved result `norm_sq_eq`: The real squared norm of a complex number, embedded into the complex plane, equals that number times its conjugate.

**Discrete Parseval for a finite spectrum.** Proved result `sampleSumSq`: With positive sample count and all frequency differences strictly smaller in magnitude than that count, the sum of sampled squared norms equals the sample count times the sum of coefficient squared norms.

**Vector discrete Parseval.** Proved result `sampleSumVecSq`: Under the same frequency-separation condition, the sampled squared vector-norm sum equals the sample count times the sum of the coefficient squared vector norms.

**Sampled products select convolution.** Proved result `expand`: If every relevant combined frequency lies strictly between the negative and positive sample count, summing the sampled triple product selects exactly the matching convolution frequencies and multiplies their sum by the sample count.

**Conjugation of a sampled Fourier sum.** Proved result `conj_sum_ee`: The sum of conjugated coefficients with reversed frequencies equals the componentwise conjugate of the original sampled Fourier sum.

**Conjugation preserves vector norm.** Proved result `vecSq_conj`: Componentwise complex conjugation leaves the squared vector-norm sum unchanged.

**Squared vector norm is nonnegative.** Proved result `vecSq_nonneg`: The sum of squared norms of a complex vector's components is nonnegative.

**A square bound implies an upper bound.** Proved result `le_of_sq_le`: If a real number's square is at most the square of a nonnegative bound, the number itself is at most that bound.

**Weighted bound for two triple products.** Proved result `point_bound`: Given nonnegative bounds for two vector norms and a positive weight, twice the norm of the difference of the two triple products is bounded by the stated weighted field squares plus the test-vector square divided by the weight.

**Finite convolution class estimate.** Proved result `classConvolutionBound`: Uniform bounds on the two finite Fourier class sums and a positive class weight bound the convolution triple-product difference by the weighted mode energies plus the row energy divided by that weight.

**The unresolved triple-product term.** Definition `qterm`: Defines the difference between the vorticity-velocity triple product and the velocity-curl triple product, both paired with the conjugated row vector.

**A zero row kills the coupling term.** Proved result `qterm_zero_right`: The unresolved triple-product term vanishes when its row-vector argument is zero.

**Zero model fields kill the coupling term.** Proved result `qterm_zero_mid`: The unresolved triple-product term vanishes when both model-vector arguments are zero.

**Scaling the third triple-product slot.** Proved result `tri_scal_right`: Scaling the third vector argument multiplies the triple product by that complex scalar.

**Real row combinations distribute.** Proved result `qterm_sum`: The unresolved triple-product term distributes over finite real linear combinations of its row-vector argument.

**Curl-adjoint pairing as a triple term.** Proved result `entry_curlAdj`: Pairing a matrix with the curl adjoint of a conjugated-vector cross product equals the triple product of the matrix curl, model vector, and conjugated row vector.

**Velocity cross pairing as a triple term.** Proved result `vecPair_cross`: Pairing velocity with a row crossed against a conjugated model curl equals the negative scalar triple product with the conjugated row.

**Matrix pairings distribute over sums.** Proved result `entry_scal_sum`: Pairing a matrix with a real scalar times a finite matrix sum equals that scalar times the sum of pairings.

**Vector pairings distribute over sums.** Proved result `vec_scal_sum`: Pairing a vector with a real scalar times a finite vector sum equals that scalar times the sum of pairings.

**The weighted row pairing is trilinear.** Proved result `pair_generic`: If the line weight times radial conversion factor equals radius, the weighted strain and velocity row pairings equal radius times the sum of unresolved triple-product terms.

**Classes select the allowed couplings.** Proved result `select`: For valid cell data, an interior point away from the axis, a selected row, and an unresolved mode, the coupling equals its sum over exactly those classes containing the model frequency and the row's resolved frequency.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The unresolved pointwise inequality.** Proved result `unresolvedRowPoint_holds`: For valid fractional cell data, axisymmetric weight, admissible fields, and supported row coefficients, the finite unresolved pairing at an interior point away from the axis is bounded by modal charges and reciprocal-weighted class row squares.

### Breakdown.FracCell.VelocityTail

Assembles one-dimensional and tensor projection estimates into the velocity-tail inequality.

Shared cell tail analysis supporting Appendix B style control of omitted polynomial modes.

Source: `lean/Breakdown/FracCell/VelocityTail.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**An equality point arbitrarily nearby.** Proved result `exists_eq_near_aux`: Two functions equal almost everywhere on a closed interval agree at a point arbitrarily close to the left of any interior point.

**Transfer a derivative through continuity.** Proved result `hasDerivAt_of_ae_aux`: If two functions agree almost everywhere on an interval and the second is continuous inside it, a derivative of the first at an interior point is also a derivative of the second there.

**Derivative norm under almost equality.** Proved result `norm_deriv_le_of_ae_aux`: If two complex functions agree almost everywhere on an interval and the second is continuous inside it, the derivative norm of the first at an interior point is at most that of the second.

**Projection respects almost equality.** Proved result `lineProj_congr_aux`: The weighted polynomial projection is unchanged when its input is replaced by an almost everywhere equal function on the interval.

**Polynomial projections are continuous.** Proved result `lineProj_continuous_aux`: Every function produced by the line projection is continuous.

**The interval shape factor is nonnegative.** Proved result `shape_nonneg_aux`: On a nondegenerate closed interval, one minus the squared normalized coordinate is nonnegative.

**Transfer the one-dimensional tail bound.** Proved result `oneVarTail_of`: The integrable one-dimensional tail estimate for a continuous representative implies the tail inequality for every function equal to that representative almost everywhere.

**The radial line weight is nonnegative.** Proved result `lineWeight_nonneg_aux`: The cell line weight is nonnegative throughout its closed radial interval.

**The two line-weight cases.** Proved result `lineWeight_cases_aux`: The cell line weight is either constant one or is the radius itself on a cell whose inner radius is zero.

**A tail squared norm is nonnegative.** Proved result `tailNormSq_nonneg_aux`: The squared norm of a cell projection tail is nonnegative for every input.

**Radial projection as line projection.** Proved result `projR_eq_lineProj_aux`: A cell's radial projection agrees at every point with the weighted line projection of the corresponding fixed-height slice.

**Assemble the radial velocity-tail bound.** Proved result `radialTailPart_of`: The one-variable tail estimate, radial mode representative, radial projection bound, and gradient-mode square-integrability together imply the radial part of the velocity-tail inequality.

**Assemble the height velocity-tail bound.** Proved result `heightTailPart_of`: The one-variable tail estimate, height mode representative, height projection bound, velocity and gradient square-integrability, and projection-composition identity imply the height part of the velocity-tail inequality.

**Combine radial and height tails.** Proved result `velocityTail_of`: The radial and height tail inequalities imply the full velocity-tail estimate for every valid second-order field, degree at least five, and nonnegative coefficient.

**Velocity tails from projection estimates.** Proved result `velocityTail_of_parts`: The eight stated line-representative, projection, and square-integrability interfaces imply the full velocity-tail bound by the top gradient part and gradient tails.

**Velocity tails from analytic leaves.** Proved result `velocityTail_of_leaves`: The integrable one-variable estimate and the seven stated mode and projection interfaces imply the full velocity-tail bound.

### Breakdown.FracCell.VelocityTailSt

Defines the weighted one-dimensional projection and the analytic interfaces for radial and height velocity-tail bounds.

Shared statement layer for the polynomial-tail estimates associated with Appendix B.

Source: `lean/Breakdown/FracCell/VelocityTailSt.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Weighted line projection.** Definition `lineProj`: Defines a polynomial of the specified maximal degree whose error is weighted-orthogonal to every polynomial test of that degree, choosing the zero function if no such coefficients exist.

**One-dimensional tail interface.** Proposition `OneVarTailStatement`: Specifies that for the allowed constant or radial weight, a continuous integral representative with square-integrable value and derivative, and degree at least two, the shape-weighted derivative tail of any almost everywhere equal input is bounded by the lower-degree derivative tail.

**Integrable line-tail interface.** Proposition `OneVarTailGoodStatement`: Specifies integrability and the derivative-tail inequality for the continuous integral representative under the allowed weight, square-integrability, and degree-at-least-two hypotheses.

**Radial representative of a mode.** Proposition `ModeRadialLineStatement`: Specifies that on almost every height slice of a valid second-order field, each velocity mode has a continuous integral representative whose radial derivative is the radial gradient mode and whose value and derivative have finite weighted square integrals.

**Radial projection-tail interface.** Proposition `RadialProjBoundStatement`: Specifies that for a measurable weighted square-integrable function and degree at least five, the radial projection remainder is integrable across heights and bounded by the difference of two rectangular projection energies plus the full tail energy.

**Finite square energy of gradient modes.** Proposition `ModeGradSquareStatement`: Specifies measurability and integrability of the line-weighted squared norm of every gradient-mode entry of a second-order field on a valid cell.

**Finite square energy of velocity modes.** Proposition `ModeVelSquareStatement`: Specifies measurability and integrability of the line-weighted squared norm of every velocity-mode component of a second-order field on a valid cell.

**Height representative after projection.** Proposition `ModeHeightLineStatement`: Specifies that each radial projection of a velocity mode has a continuous integral representative in height, with derivative given by the radial projection of the height gradient mode and finite square integrals for both.

**Composition of the two projections.** Proposition `ProjComposeStatement`: Specifies that for a measurable weighted square-integrable function, radial projection followed by height projection of the same degree equals the rectangular cell projection at every point.

**Height projection-tail interface.** Proposition `HeightProjBoundStatement`: Specifies that for degree at least five, the height projection remainder of a radially projected weighted square-integrable function is integrable and bounded by the corresponding projection-energy difference plus full tail energy.

**Radial velocity-tail interface.** Proposition `RadialTailPartStatement`: Specifies that for a valid second-order field and degree at least five, the radial shape-weighted derivative energy of the radial velocity projection error is bounded by a radial gradient projection-energy difference plus its tail energy.

**Height velocity-tail interface.** Proposition `HeightTailPartStatement`: Specifies that for a valid second-order field and degree at least five, the height shape-weighted derivative energy between radial and rectangular velocity projections is bounded by the corresponding height gradient projection-energy difference plus its tail energy.
<!-- /passage:front -->

