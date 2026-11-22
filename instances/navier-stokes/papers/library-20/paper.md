
<!-- passage:front -->
# Library guide 20: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) **20** [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.ModeRadialPartsF` to `Breakdown.FracCell.RelAxis` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.ModeRadialPartsF

Derives radial velocity-mode primitives and integration by parts from L⁶ velocity control and a square-integrable weak gradient. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Lemma · Integrate a C¹ derivative.** Integrating a real C¹ derivative over a half-open interval gives the function's endpoint difference. [`prim_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L16).

**Lemma · Integrate a weighted weak primitive.** A function agreeing almost everywhere with a terminal-point primitive satisfies radial integration by parts against real C¹ tests vanishing at both endpoints when the derivative is integrable with its distance from the left endpoint. [`line_ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L22).

**Lemma · Transfer a dominating integrable weight.** If an integrable weighted field uses a nonnegative measurable weight, multiplication by any measurable scalar bounded in absolute value by a constant times that weight preserves integrability. [`mul_weight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L131).

**Lemma · Translate a cylindrical point vertically.** Adding an axial coordinate vector to a cylindrical point adds the same amount to its height coordinate. [`cyl_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L156).

**Lemma · Translate a gradient mode vertically.** Translating a spatial gradient field in the axial direction translates its cylindrical mode by the same amount in height. [`gm_shift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L161).

**Lemma · Measurability of the planar line weight.** The cell line weight composed with the radial coordinate is measurable. [`lw_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L165).

**Lemma · Nonnegative line weight on the interval.** For a nonnegative lower radius, the line weight is nonnegative at every radius above that endpoint. [`lw_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L171).

**Lemma · Control radius by the line weight.** On a nonnegative radial interval, the radius is at most the larger of one and the upper radius times the cell line weight. [`lw_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L178).

**Lemma · Integrability of weighted gradient modes.** A measurable gradient field with integrable entry squares has line-weight-integrable modes on each nondegenerate rectangle with nonnegative lower radius. [`wgm_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L185).

**Lemma · Integrate modes with a radial factor.** A continuous factor bounded by a constant times radius makes a radial gradient mode integrable on the stated rectangle when the gradient entry squares are integrable. [`part_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L212).

**Lemma · Integrability of radial slices.** An integrable complex rectangular field has integrable radial slices at almost every height. [`slice_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L228).

**Lemma · Linear vanishing at a zero endpoint.** A real C¹ function vanishing at the left endpoint is bounded on the interval by a constant times distance from that endpoint. [`psi_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L233).

**Interface · Velocity rectangle proposition.** This proposition requires every mode component of a measurable L⁶ velocity field to be integrable on every closed radial-height rectangle with nonnegative lower radius. [`ModeVecRectIntegrableStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L254).

**Interface providers.** [`Breakdown.CellCert.CellFormula.modeVecRectIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L779) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:779](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L779); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellFormula.modeRadialParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267); named reference in type); [`Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF.dtest_mv_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L452) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:452](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L452); named reference in type); [`Breakdown.CellCert.CellFormula.Internal.ModeRadialPartsF.test_slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L471) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:471](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L471); named reference in type); [`Breakdown.CellCert.CellFormula.modeRadialFormula_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L614) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:614](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L614); named reference in type); [`Breakdown.CellCert.CellFormula.modeRadialParts_of_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L650) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:650](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L650); named reference in type).

**Interface · Radial velocity primitive proposition.** This proposition requires an L⁶ velocity field with square-integrable weak gradient to equal a constant minus its radial gradient-mode integral on almost every radial slice and almost every radius. [`ModeRadialFormulaStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L259).

**Interface providers.** [`Breakdown.CellCert.CellFormula.modeRadialFormula_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L614) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:614](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L614); named premises: `ModeVecRectIntegrableStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellFormula.modeRadialParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267); named reference in type).

**Theorem · Assemble velocity radial parts.** The rectangle-integrability and radial-primitive propositions imply integrability of radially weighted gradient pairings and the velocity-mode radial integration-by-parts formula. [`modeRadialParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267).

**Definition · Extend the cylindrical component map.** The auxiliary linear functional extracts a cylindrical vector component using two planar parameters and the fixed axial coordinate functional. [`frameForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L362).

**Lemma · Smooth cylindrical component functionals.** Each auxiliary cylindrical component functional depends smoothly on its planar parameters. [`frameForm_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L367).

**Lemma · Evaluate the component map on the circle.** The cylindrical vector component equals the auxiliary functional evaluated at cosine and sine. [`frameVec_eq_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L371).

**Lemma · Extract the radial matrix column.** A radial-column cylindrical matrix component equals the auxiliary functional applied to the linear map's radial-vector image. [`frameMat_eq_form`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L376).

**Lemma · Local integrability of gradient columns.** Every Cartesian column of a measurable gradient field with integrable entry squares is locally integrable. [`col_loc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L381).

**Lemma · Planar radial weak identity.** An L⁶ velocity field and its square-integrable weak gradient satisfy the radial mode weak identity for smooth compactly supported planar tests away from the axis. [`weak_plane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L394).

**Lemma · Smooth interval comparison tests.** Each localized interval comparison test is smooth. [`test_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L420).

**Lemma · Integrate a localized gradient pairing.** A radial comparison test vanishing below a positive radius, multiplied by a continuous height test, gives an integrable radial gradient-mode pairing on the rectangle. [`test_gm_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L429).

**Lemma · Integrate a differentiated velocity test.** Assuming rectangle-integrability of velocity modes, a differentiated radial comparison test times a continuous height test gives an integrable velocity-mode pairing. [`dtest_mv_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L452).

**Lemma · Product measure on a rectangle.** The measure restricted to the radial-height rectangle equals the product of its restricted interval measures. [`prod_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L466).

**Lemma · Weak radial tests on almost every slice.** Under velocity rectangle-integrability and weak-gradient assumptions, each localized radial test satisfies its weak identity at almost every height. [`test_slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L471).

**Theorem · Recover radial velocity primitives.** The velocity rectangle-integrability proposition implies the almost everywhere radial primitive formula for L⁶ fields with square-integrable weak gradients. [`modeRadialFormula_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L614).

**Theorem · Derive parts from rectangle control.** Velocity-mode rectangle-integrability alone supplies the remaining interface needed to derive the radial velocity integration-by-parts proposition. [`modeRadialParts_of_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L650).

**Lemma · Control linear growth by sixth powers.** For positive r and nonnegative x, $x≤rx^6+r^{-1/5}$. [`pow_six_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L659).

**Lemma · Split an extended norm near the axis.** For positive radius r, a vector's extended norm is at most r times its sixth power plus $r^{-1/5}$. [`enorm_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L674).

**Lemma · Integrate velocity modes on rectangles.** Every mode component of a measurable L⁶ velocity field is integrable on a closed radial-height rectangle with nonnegative lower radius. [`modeVec_rect_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L683).

**Theorem · Establish velocity rectangle control.** Measurable L⁶ velocity fields satisfy the proposition requiring integrability of all cylindrical mode components on rectangles with nonnegative radii. [`modeVecRectIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L779).

**Theorem · Integrate velocity modes radially.** For an L⁶ velocity field with square-integrable weak gradient, the weighted gradient pairings are integrable and radial integration by parts holds for separated tests vanishing at both radial endpoints. [`modeRadialParts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L782).

**Reader note.** This closes the CellFormula proposition from RelRadialCoef; the same local name in ModeRadialPartsA closes the different CellAnalysis proposition from ResolvedEnergySt.

### Breakdown.FracCell.ModeRadialWeak

States the cellwise weak radial identity and the integrability needed to recover radial velocity representatives. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Interface · Weak radial mode proposition.** This proposition requires unweighted velocity-mode integrability, line-weighted radial gradient-mode integrability, and the vanishing weak radial pairing against C¹ radial tests with zero endpoint values and continuous height tests. [`ModeRadialWeakStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeak.lean#L15).

**Interface providers.** [`Breakdown.CellCert.CellAnalysis.modeRadialWeak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L604) ([lean/Breakdown/FracCell/ModeRadialWeakProof.lean:604](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L604); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellAnalysis.velocityTail_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L180) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:180](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L180); named reference in type); [`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L190) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:190](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L190); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:413](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:420](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420); named reference in type); [`Breakdown.CellCert.CellAnalysis.velocityTail_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L457) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:457](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L457); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L467) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:467](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L467); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L473) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:473](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L473); named reference in type); [`Breakdown.CellCert.CellAnalysis.cellSharpBound_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L489) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:489](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L489); named reference in type); [`Breakdown.CellCert.CellAnalysis.cellFormBound_of_open`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L494) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:494](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L494); named reference in type); [`Breakdown.CellCert.CellCoordinates.cellBound_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L506) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:506](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L506); named reference in type); [`Breakdown.CellCert.CellAnalysis.modeRadialLine_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L487) ([lean/Breakdown/FracCell/ModeRadialLine.lean:487](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialLine.lean#L487); named reference in type); [`Breakdown.CellCert.CellCoordinates.RadialAxisCrossInternal.axisPrimitive_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L425) ([lean/Breakdown/FracCell/RadialAxisCross.lean:425](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L425); named reference in type); [`Breakdown.CellCert.CellCoordinates.radialAxisCross_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L460) ([lean/Breakdown/FracCell/RadialAxisCross.lean:460](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L460); named reference in type); [`Breakdown.CellCert.CellFormula.relRadialSide_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialSide.lean#L298) ([lean/Breakdown/FracCell/RelRadialSide.lean:298](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialSide.lean#L298); named reference in type); [`Breakdown.CellCert.CellAnalysis.SharpCoefTailInternal.vel_radial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L553) ([lean/Breakdown/FracCell/SharpCoefTail.lean:553](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L553); named reference in type); [`Breakdown.CellCert.CellAnalysis.SharpCoefTailInternal.vel_tail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L690) ([lean/Breakdown/FracCell/SharpCoefTail.lean:690](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L690); named reference in type); [`Breakdown.CellCert.CellAnalysis.sharpCoefTail_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L708) ([lean/Breakdown/FracCell/SharpCoefTail.lean:708](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SharpCoefTail.lean#L708); named reference in type); [`Breakdown.CellCert.CellFormula.heightNormal_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceHeightNormal.lean#L229) ([lean/Breakdown/FracCell/StrainFaceHeightNormal.lean:229](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceHeightNormal.lean#L229); named reference in type); [`Breakdown.CellCert.CellFormula.radialTurn_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceRadialTurn.lean#L228) ([lean/Breakdown/FracCell/StrainFaceRadialTurn.lean:228](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceRadialTurn.lean#L228); named reference in type); [`Breakdown.CellCert.CellFormula.radialTurn_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceRadialTurn.lean#L639) ([lean/Breakdown/FracCell/StrainFaceRadialTurn.lean:639](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StrainFaceRadialTurn.lean#L639); named reference in type).

### Breakdown.FracCell.ModeRadialWeakProof

Extends the planar weak radial identity to cell tests by localization, smoothing, dominated convergence, and endpoint cutoffs. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Integrate velocity modes up to the axis.** The cylindrical modes of an L⁶ velocity field are integrable on every finite rectangle from radius zero and symmetric in height. [`vel_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L15).

**Theorem · Operator L² control from entries.** A measurable gradient field with integrable entry squares belongs to L² in operator norm. [`grad_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L21).

**Theorem · Integrate radius-weighted gradient modes.** A locally integrable gradient field gives radially weighted gradient modes integrable on every finite axis-touching rectangle. [`grad_on`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L28).

**Theorem · Measurability of radial gradient modes.** A measurable gradient field gives measurable radial gradient modes on each finite axis-touching rectangle. [`grad_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L37).

**Theorem · Enclose a compact set symmetrically.** Every compact subset of the real line is contained in an interval symmetric about zero. [`bound_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L45).

**Theorem · A function vanishes off its support.** A real function is zero outside its topological support. [`zero_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L49).

**Theorem · A derivative vanishes off support.** The derivative of a real function is zero outside its topological support. [`deriv_zero_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L51).

**Theorem · Divide a positive-radius test by radius.** A continuous function supported strictly at positive radii remains continuous after division by the radial coordinate. [`ratio_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L54).

**Theorem · Recover a test after division by radius.** A function supported at positive radii equals its radius quotient multiplied by radius everywhere. [`ratio_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L68).

**Theorem · Integrability of localized weak pairings.** Local integrability of a field and radial-weighted integrability of its derivative candidate imply integrability of both weak-test terms on finite height strips when the radial test is compactly supported away from zero. [`part_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L79).

**Theorem · Make a strip-integrable field global.** Multiplication by a continuous compactly supported height factor makes a field globally integrable if it is integrable on every finite height strip. [`weight_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L107).

**Theorem · Radial derivative of a separated test.** The radial Fréchet derivative of a product of differentiable radial and height functions equals the radial derivative times the height factor. [`fderiv_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L119).

**Theorem · Weak identity on almost every slice.** The planar radial weak identity and local integrability imply the one-dimensional weak identity at almost every height for each smooth radial test supported away from the axis. [`slice_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L130).

**Theorem · Restrict smooth weak identities to cells.** A smooth radial test compactly supported inside the radial interval satisfies the zero weak pairing on any height rectangle against a continuous height test. [`rect_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L202).

**Theorem · Pass vanishing weak pairings to a limit.** Almost everywhere convergence of uniformly dominated test coefficients preserves the zero weak pairing under the stated field and weight integrability assumptions. [`limit_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L237).

**Definition · Shrinking bumps within a fixed margin.** The smoothing bump has outer radius $δ/(k+1)$ and inner radius half as large for positive δ. [`bumpSeq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L276).

**Theorem · Allow compact C¹ radial tests.** The smooth planar weak identity extends to C¹ radial tests compactly supported inside the cell interval under the given positive-weight and integrability hypotheses. [`rect_c1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L284).

**Theorem · Bound a shrinking-edge product.** If a factor is O(δ) where a bounded transition derivative is active, the stated product containing $1/δ$ is bounded by $2MD$. [`edge_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L391).

**Theorem · Transition derivative off [0,1].** The derivative of the smooth transition function is zero outside the closed unit interval. [`trans_deriv_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L404).

**Theorem · Allow C¹ tests with zero boundary values.** The planar weak radial identity extends to real C¹ radial tests vanishing at both endpoints when the nonnegative weight controls distance from the left boundary and the stated integrability holds. [`rect_psi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L418).

**Theorem · Establish the cell weak radial identity.** Second-order fields satisfy velocity-mode integrability, weighted radial gradient-mode integrability, and the zero weak radial pairing for the prescribed separated boundary-vanishing tests. [`modeRadialWeak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialWeakProof.lean#L604).

### Breakdown.FracCell.ModeRectIntegrable

Obtains unweighted rectangle integrability of admissible velocity and gradient modes through localized Sobolev estimates. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Convexity under mollification.** For integer power at least one and an integrable dominating function, the power of the mollified vector norm is bounded by the mollification of the norm power. [`normPow_conv_le_of_dom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L14).

**Theorem · Integrate a finite nonnegative bound.** A finite family of nonnegative functions whose pointwise sum is bounded by an integrable function has summed integrals bounded by that function's integral. [`sum_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L74).

**Theorem · Mollify a column-energy bound.** A pointwise integrable bound on the sum of three column norm squares remains a bound after convolution with a normalized bump. [`conv_sum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L89).

**Theorem · Differentiate a weakly smoothened field.** Convolution of a locally integrable vector field with a normalized bump has coordinate derivatives equal to the convolutions of its specified weak derivative columns. [`mollify_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L103).

**Theorem · Characterize vector L⁶ membership.** For a measurable vector field, membership in L⁶ is equivalent to integrability of the sixth power of its norm. [`memLp_six_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L135).

**Theorem · Control the cutoff derivative error.** A cutoff derivative bounded by K/R gives an L² product bound in terms of the field's exterior L⁶ norm, with the stated dimension-three ball-volume constant. [`cross_tail_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L141).

**Theorem · Vanishing exterior L⁶ tails.** The L⁶ norm of an L⁶ vector field restricted outside balls of radii n plus one tends to zero. [`tail_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L200).

**Theorem · Sobolev control for smooth L⁶ fields.** A smooth L⁶ vector field has L⁶ norm bounded by the stated Sobolev constant times the L² norm of its derivative. [`smooth_six_of_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L231).

**Theorem · Sobolev bound from weak columns.** A compactly supported L² vector field with weak derivative columns dominated in squared sum by an integrable energy has the stated L⁶ bound using three times the square root of that energy integral. [`six_bound_of_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L295).

**Theorem · Control scalar kernels near the axis.** For a norm-bounded scalar transform and positive r, the extended output norm is bounded by $r^{-1/5}$ plus r times the sixth power of the input norm. [`pt_bound_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L377).

**Theorem · Integrate angular averages of L⁶ fields.** An L⁶ field valued in a normed space gives integrable unweighted angular averages on finite axis-touching rectangles for continuous norm-bounded scalar transforms. [`six_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L386).

**Theorem · Weak product rule for a gradient column.** A test cutoff times a Cartesian gradient column has weak derivative equal to the cutoff derivative times that column plus the cutoff times its second derivative column. [`col_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L449).

**Theorem · Localized gradient columns lie in L⁶.** For a second-order field, each Cartesian gradient column multiplied by a scalar test cutoff of magnitude at most one belongs to L⁶. [`col_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L490).

**Theorem · The localized gradient lies in L⁶.** The operator-valued gradient of a second-order field belongs to L⁶ after multiplication by a scalar test cutoff of magnitude at most one. [`op_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L527).

**Theorem · Enclose a valid cell at the axis.** A valid cell rectangle is contained in the axis-touching rectangle with its upper radius and heights from minus to plus its upper height. [`rect_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L545).

**Theorem · Integrate admissible cell modes.** For a valid cell layout and admissible field tuple, every layout velocity-mode and gradient-mode component is integrable on the cell rectangle. [`modeRectIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRectIntegrable.lean#L559).

### Breakdown.FracCell.ModeSquareIntegrable

Controls finite gradient-mode combinations and second-derivative modes in weighted L² on cells. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Cauchy–Schwarz for matrix combinations.** The squared norm of a complex matrix-component combination is bounded by the squared coefficient sum times the squared component sum. [`combo_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L15).

**Theorem · Preserve weighted L² under combinations.** Finite complex combinations of measurable weighted-square-integrable components remain measurable and weighted-square-integrable for a nonnegative measurable weight. [`combo_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L28).

**Theorem · Apply an operator by Cartesian columns.** Applying a linear map to a vector equals the sum of its Cartesian columns scaled by the vector coordinates. [`clm_apply_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L52).

**Theorem · Bound an operator by Cartesian columns.** The operator norm of a map from three-dimensional space is at most the sum of its Cartesian column norms. [`clm_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L60).

**Theorem · Bound a bilinear operator by entries.** The squared operator norm of a spatial bilinear map is at most nine times the sum of its Cartesian two-index column norm squares. [`bil_norm_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L71).

**Definition · Angular second-derivative kernel.** The kernel multiplies a cylindrical-frame second-derivative component by the negative-frequency complex exponential. [`thirdKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L86).

**Theorem · Continuity of second-derivative entries.** Each cylindrical-frame second-derivative component depends continuously on the angle and bilinear map. [`frameThird_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L89).

**Theorem · Continuity of the angular kernel.** The second-derivative angular kernel is jointly continuous in angle and bilinear map. [`thirdKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L95).

**Theorem · Bound second-derivative frame entries.** The absolute value of a cylindrical-frame second-derivative component is at most the bilinear operator norm. [`frameThird_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L99).

**Theorem · Bound the second-derivative kernel.** The complex second-derivative angular kernel has norm at most the bilinear operator norm. [`thirdKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L113).

**Theorem · Periodic second-derivative entries.** A cylindrical-frame second-derivative component is unchanged by adding $2π$ to the angle. [`frameThird_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L118).

**Theorem · Use a centered angular period.** A second-derivative mode equals the normalized integral of its angular kernel over the centered interval from minus π to π. [`modeThird_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L122).

**Theorem · Measurability of second-derivative modes.** A measurable bilinear-map field has measurable cylindrical second-derivative modes on every valid cell. [`th_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L132).

**Theorem · Radial L² control of second derivatives.** Integrable Cartesian second-derivative norm squares imply radial-Jacobian-weighted square-integrability of each second-derivative mode on a valid cell. [`th_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L142).

**Theorem · Establish combined mode L² control.** For second-order fields, each complex gradient-mode combination is measurable and line-weight-square-integrable, and each corresponding second-derivative combination is measurable and radius-square-integrable. [`modeSquareIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeSquareIntegrable.lean#L204).

### Breakdown.FracCell.ModeStripIntegrable

Places arbitrary finite height strips inside symmetric rectangles to transfer velocity and gradient mode integrability. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Enclose a strip in a symmetric rectangle.** A radial-height strip lies in the rectangle with the same radial interval and symmetric height bound $|z₁|+|z₂|$. [`strip_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeStripIntegrable.lean#L12).

**Theorem · Integrate modes over arbitrary strips.** All velocity-mode and gradient-mode components of a second-order field are integrable on every finite axis-touching radial-height strip. [`modeStripIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeStripIntegrable.lean#L30).

### Breakdown.FracCell.ModeTurn

Identifies angular differentiation of velocity modes with the tangential gradient column almost everywhere on a cell. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Positive radius almost everywhere.** The radius is strictly positive almost everywhere in a valid cell rectangle. [`rect_radius_pos_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeTurn.lean#L13).

**Theorem · Identify the angular mode derivative.** For a second-order field, applying the mode-frequency turn operator to the velocity mode equals radius times the tangential gradient-mode column almost everywhere on each valid cell. [`modeTurn_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeTurn.lean#L26).

### Breakdown.FracCell.ModeVelSquare

Proves measurability and weighted square-integrability of velocity modes by cylindrical coordinates and an L⁶ majorant. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Inverse cylindrical coordinate formula.** The inverse cylindrical chart maps radius, angle, and height to radius times cosine, radius times sine, and the unchanged height. [`symm_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L14).

**Theorem · Measurability of the inverse chart.** The inverse cylindrical coordinate map is measurable. [`symm_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L18).

**Theorem · Transfer null sets through the chart.** The inverse cylindrical map is quasi-measure-preserving from its restricted target measure to spatial Lebesgue measure. [`symm_qmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L23).

**Theorem · Continuity of a coordinate embedding.** Inserting a real scalar in one Cartesian coordinate is a continuous map into space. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L50).

**Theorem · Continuity of cylindrical frame vectors.** Each cylindrical unit-frame vector depends continuously on the angle. [`frameUnit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L60).

**Theorem · Unit length of cylindrical frame vectors.** Every cylindrical frame vector has norm one. [`frameUnit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L69).

**Theorem · Cylindrical components as inner products.** A cylindrical-frame vector component is the inner product with the corresponding frame unit vector. [`frameVec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L73).

**Theorem · Continuity of cylindrical components.** Each cylindrical vector component depends jointly continuously on angle and vector. [`frameVec_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L77).

**Theorem · Bound a cylindrical component.** The absolute value of each cylindrical-frame vector component is at most the vector norm. [`frameVec_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L82).

**Definition · Velocity Fourier kernel.** The velocity kernel multiplies a cylindrical-frame velocity component at the cylindrical point by its negative-frequency complex exponential. [`kern`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L87).

**Theorem · Periodicity of the velocity kernel.** At a fixed radial-height point, the velocity Fourier kernel is periodic with period $2π$. [`kern_periodic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L91).

**Theorem · Center the velocity-mode integral.** A velocity-mode component equals the normalized integral of its Fourier kernel over the half-open centered angular period. [`mode_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L108).

**Theorem · Measurability in cylindrical coordinates.** The velocity of a second-order field remains almost everywhere strongly measurable after composition with the inverse cylindrical chart. [`vel_comp_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L116).

**Theorem · Measurability of the velocity kernel.** The velocity Fourier kernel of a second-order field is measurable on the product of the positive-radius half-plane and the centered angular period. [`kern_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L122).

**Theorem · Measurability of a velocity mode.** Each velocity-mode component of a second-order field is almost everywhere strongly measurable on the positive-radius half-plane. [`mode_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L147).

**Theorem · Bound angular averaging by an envelope.** If a measurable complex angular function has squared norm bounded by an integrable real envelope, its squared integral norm is at most $2π$ times the envelope integral. [`sq_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L159).

**Definition · Local L⁶ energy envelope.** The envelope equals one plus the sixth power of the velocity norm inside the closed ball of radius R and zero outside it. [`bump`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L199).

**Theorem · Integrability of the local envelope.** The closed-ball L⁶ energy envelope of a second-order field is integrable. [`bump_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L202).

**Theorem · Norm of a cylindrical point.** A cylindrical point has Euclidean norm equal to the square root of radius squared plus height squared. [`cylPoint_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L212).

**Theorem · Dominate the velocity kernel energy.** On a valid cell, the squared velocity-kernel norm is bounded by the local L⁶ envelope in the ball of radius equal to the upper radius plus upper height. [`kern_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L218).

**Theorem · Radial L² control of velocity modes.** Each velocity-mode component of a second-order field has integrable squared norm times radius on a valid cell. [`mode_integrable_p`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L238).

**Theorem · Positive radii almost everywhere.** The measure on a valid cell is dominated by the measure on the positive-radius half-plane. [`rect_ae_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L311).

**Theorem · Establish velocity-mode L² control.** Each velocity-mode component of a second-order field is measurable and has integrable squared norm with the cell line weight. [`modeVelSquare`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeVelSquare.lean#L322).

### Breakdown.FracCell.ModeWeakIdentity

Transfers cylindrical weak differentiation to velocity and gradient modes and derives the mixed-derivative identity. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Extend the cylindrical frame.** The auxiliary frame uses planar coordinates q to define radial and tangential vectors together with the fixed axial unit vector. [`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L13).

**Theorem · Recover the angular frame.** Evaluating the auxiliary frame at cosine and sine gives the cylindrical orthonormal frame. [`unitAt_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L17).

**Definition · Extend frame component extraction.** The auxiliary row map forms the real linear functional with coefficients given by the chosen auxiliary frame vector. [`angQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L19).

**Definition · Cylindrical component functional.** The angular functional evaluates the auxiliary frame row map at cosine and sine of the angle. [`angL`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L22).

**Theorem · Extract a cylindrical vector component.** The angular functional equals inner product with the selected cylindrical frame vector. [`angL_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L24).

**Theorem · Smooth auxiliary frame coordinates.** Every Cartesian coordinate of each auxiliary frame vector is smooth in the planar parameters. [`unitAt_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L27).

**Theorem · Smooth auxiliary frame vectors.** Each auxiliary frame vector is a smooth function of the planar parameters. [`unitAt_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L32).

**Theorem · Smooth frame component functionals.** The auxiliary row functional depends smoothly on the planar parameters. [`angQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L35).

**Definition · Auxiliary radial-column functional.** The auxiliary operator functional extracts a chosen frame component of the operator applied to the auxiliary radial vector. [`colQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L39).

**Definition · Cylindrical radial-column functional.** The angular radial-column functional evaluates its planar auxiliary functional at cosine and sine. [`colL`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L42).

**Theorem · Smooth radial-column functionals.** The auxiliary radial-column functional depends smoothly on its planar parameters. [`colQ_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L44).

**Theorem · Extract a radial gradient component.** The angular radial-column functional equals the inner product of the operator's radial image with the selected frame vector. [`colL_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L47).

**Theorem · Expand in Cartesian unit vectors.** Every spatial vector equals the sum of its Cartesian coordinates times the corresponding unit vectors. [`vec_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L52).

**Theorem · Bound an operator by its columns.** The operator norm of a linear map from three-dimensional space is at most the sum of the norms of its Cartesian columns. [`norm_le_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L55).

**Theorem · Local integrability of the norm.** The norm of a locally integrable field is locally integrable. [`loc_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L64).

**Theorem · Local integrability from columns.** A measurable operator field is locally integrable if each of its Cartesian columns is locally integrable. [`loc_of_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L68).

**Theorem · Square-integrability of gradient columns.** Each Cartesian column of a measurable gradient field with integrable entry squares lies in L². [`memLp_col'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L78).

**Theorem · Square-integrability of second columns.** Each Cartesian two-index column of a measurable second derivative field lies in L² when the summed column norm squares are integrable. [`memLp_col2'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L87).

**Predicate · Planar tests away from the axis.** A permitted planar test is smooth, compactly supported, and has strictly positive radial coordinate throughout its topological support. [`IsTest2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L101).

**Theorem · Directional derivatives as valid tests.** Every fixed directional derivative of a permitted planar test is again a permitted planar test. [`test_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L104).

**Theorem · Commute smooth directional derivatives.** For a smooth real planar function, the two successive derivatives in fixed directions commute. [`mixed`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L109).

**Theorem · Derive the remaining mixed weak identity.** Given radial and height weak derivatives of a common field and the height derivative of its radial derivative, the radial derivative of its height derivative satisfies the same weak identity. [`third_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L121).

**Theorem · Scale a weak complex identity.** Multiplying both fields in the given complex integral identity by the same complex constant preserves that identity. [`scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L136).

**Theorem · Cylindrical components as inner products.** A cylindrical-frame vector component is the inner product with the corresponding frame unit vector. [`frameVec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L142).

**Theorem · Assemble the four mode weak identities.** The cylindrical weak differentiation proposition implies the radial and height velocity-mode identities and both mixed gradient-mode identities for second-order fields. [`modeWeakIdentity_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L145).

**Theorem · Establish the four mode weak identities.** Second-order fields satisfy radial and height velocity-mode weak differentiation and the two matching mixed gradient-mode identities against smooth compactly supported tests away from the axis. [`modeWeakIdentity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeWeakIdentity.lean#L210).

### Breakdown.FracCell.ModelField

Constructs the gradient correction between analytic and model fields and bounds its measured row discrepancy. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Unit length of Cartesian basis vectors.** Every Cartesian unit vector has norm one. [`unit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L18).

**Theorem · Derivatives vanish outside support.** The Fréchet derivative of a real scalar function is zero outside its topological support. [`zero_off`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L20).

**Theorem · Values vanish outside support.** A real scalar function is zero outside its topological support. [`zero_off'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L24).

**Theorem · Identify two operator convolutions.** The convolution using scalar multiplication precomposed on the operator input equals the ordinary scalar-multiplication convolution of the operator-valued field. [`precomp_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L28).

**Theorem · Use C¹ compactly supported weak tests.** A locally integrable vector field with locally integrable weak-gradient columns satisfies the coordinate weak derivative identity for C¹ compactly supported scalar tests. [`weak_c1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L35).

**Theorem · Measurability of operator application.** Applying a measurable operator field to a measurable vector field gives a measurable vector field. [`aesm_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L206).

**Theorem · Measurability of adjoint application.** Applying the adjoint of a measurable operator field to a measurable vector field gives a measurable vector field. [`aesm_adj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L210).

**Theorem · Local integrability of coordinates.** Each Cartesian coordinate of a locally integrable vector field is locally integrable. [`comp_li`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L215).

**Theorem · Integrate a compactly supported product.** The product of a continuous compactly supported scalar function and a locally integrable scalar function is globally integrable. [`cint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L220).

**Theorem · Control operator norm by entry energy.** The squared operator norm of a spatial linear map is at most three times its entry-square energy. [`opNorm_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L224).

**Theorem · L² membership from gradient entries.** A measurable gradient field with integrable entry-square energy belongs to L² in operator norm. [`memLp_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L237).

**Theorem · Local integrability of gradient columns.** Each Cartesian column of a measurable gradient field with integrable entry energy is locally integrable. [`li_col`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L244).

**Theorem · L⁶ fields are locally integrable.** Every L⁶ spatial vector field is locally integrable. [`li_v`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L250).

**Theorem · Weak derivative of a scalar product.** Pairing a weakly differentiable vector field with a C¹ vector field obeys the stated weak product rule when both resulting terms are locally integrable. [`product_rule`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L253).

**Theorem · Continuity of coordinate insertion.** Inserting a real number in a fixed Cartesian coordinate is continuous. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L312).

**Theorem · Continuity of the cross product.** The spatial cross product depends jointly continuously on its two vectors. [`cross_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L321).

**Theorem · Continuity of the algebraic curl.** The curl extracted from a spatial linear map depends continuously on that map. [`curl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L325).

**Theorem · Bound the squared cross-product norm.** The squared norm of a cross product is at most the square of the product of the two vector norms. [`cross_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L329).

**Theorem · Bound the cross-product norm.** The norm of a cross product is at most the product of the two vector norms. [`cross_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L335).

**Theorem · Bound an operator entry.** The absolute value of each Cartesian entry is at most the operator norm. [`entry_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L342).

**Theorem · Bound the permutation sign.** The absolute value of the three-index permutation sign is at most one. [`sign_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L349).

**Theorem · Bound curl by operator norm.** The norm of the algebraic curl is at most twenty-seven times the operator norm. [`curl_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L353).

**Theorem · Bound an adjoint application.** Applying an adjoint to a vector has norm at most the original operator norm times the vector norm. [`adj_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L375).

**Theorem · Local L² energy of an L⁶ field.** A measurable L⁶ vector field has integrable squared norm on every set of finite volume. [`sqK`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L379).

**Theorem · Restrict an L⁶ field to finite volume.** Restricting an L⁶ vector field to a measurable set of finite volume gives an L² field after extension by zero. [`memLp_ind`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L385).

**Theorem · Local integrability by norm domination.** A measurable scalar function bounded in absolute value by a constant times a locally integrable vector norm is locally integrable. [`li_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L391).

**Theorem · Construct the scalar-product gradient.** For a second-order field and a bounded C¹ comparison field with bounded derivative, the negative sum of the two adjoint product terms is a gradient field. [`grad_field`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L397).

**Theorem · L² control of the symmetric product.** For L⁶ velocity and square-integrable gradient, twice the symmetric product lies in L² when its coefficient field is bounded and its derivative decays quadratically. [`memLp_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L469).

**Theorem · Measurability of a cross product.** The pointwise cross product of two measurable vector fields is measurable. [`aesm_cross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L510).

**Theorem · Measurability of the curl field.** Taking the algebraic curl of a measurable gradient field gives a measurable vector field. [`aesm_curl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L514).

**Theorem · Subtract in a cross-product argument.** A cross product with a difference in its second argument equals the difference of the two cross products. [`cross_sub_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L518).

**Theorem · Subtract in the first cross factor.** A cross product with a difference in its first argument equals the difference of the two cross products. [`cross_sub_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L522).

**Theorem · Cross product with a zero first factor.** The cross product of the zero vector with any vector is zero. [`cross_zero_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L526).

**Theorem · Row measurements depend only on pairings.** Two fields have the same aggregate row measurement if their pairings with every row field agree. [`rows_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L532).

**Theorem · Restrict a pairing to the row support.** When a row field vanishes outside a set, its pairing with a field equals its pairing with that field restricted to the set. [`pair_ind`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L537).

**Theorem · Triangle inequality for row measurements.** With nonnegative row weights and L² row fields, the aggregate row measurement of a sum of two L² fields is at most the sum of their measurements. [`rows_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L546).

**Theorem · Homogeneity of row measurements.** With nonnegative row weights, scaling a field by a real number scales its aggregate row measurement by the absolute value of that number. [`rows_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L559).

**Theorem · The zero field has zero row measurement.** The aggregate row measurement of the zero field is zero. [`rows_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L574).

**Theorem · Bound rows of a finite field sum.** With nonnegative row weights and L² rows and summands, the row measurement of a finite sum is at most the sum of the individual measurements. [`rows_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L578).

**Theorem · Nonnegative entry energy.** The sum of squared Cartesian operator entries is nonnegative. [`es_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L590).

**Theorem · Bound a scalar times a unit factor.** Multiplying a real constant by a number between zero and one gives a value at most the constant's absolute value. [`bound_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L594).

**Theorem · Replace a coefficient by its magnitude.** For a nonnegative factor, replacing a real coefficient by its absolute value can only increase the product. [`bound_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L599).

**Theorem · Continuity of the axial turn.** The axial-turn vector map is continuous. [`turn_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L601).

**Theorem · Finite Cauchy–Schwarz bound.** The finite sum of real products is bounded by the product of the square roots of their squared sums. [`sum_mul_le_sqrt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L606).

**Theorem · Bound the model-field discrepancy.** Chosen-derivative agreement, the cross-product identity, and second-derivative energy identities yield a gradient correction whose row-measured analytic/model field discrepancy is bounded by row loss times field size under the model hypotheses. [`modelField_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelField.lean#L616).

### Breakdown.FracCell.ModelForm

Combines center and actuator pairing identities with drift energy to compare the model form to the analytic local-field pairing. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Interface · Center pairing proposition.** This proposition identifies the center symmetric-product pairing with the negative second trace as the integral of jForm and identifies each actuator pairing with its gradient entry pairing for valid cell data and second-order fields. [`CentrePairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelForm.lean#L14).

**Interface providers.** [`Breakdown.CellCert.centrePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CentrePairing.lean#L12) ([lean/Breakdown/FracCell/CentrePairing.lean:12](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CentrePairing.lean#L12); named premises: `CentreIdentityStatement`); [`Breakdown.CellCert.centrePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CentrePairing.lean#L15) ([lean/Breakdown/FracCell/CentrePairing.lean:15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CentrePairing.lean#L15); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.modelForm_of_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CertificateOfCell.lean#L39) ([lean/Breakdown/FracCell/CertificateOfCell.lean:39](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CertificateOfCell.lean#L39); named reference in type); [`Breakdown.CellCert.isFracCert_of_cell_of_pairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CertificateOfCell.lean#L42) ([lean/Breakdown/FracCell/CertificateOfCell.lean:42](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CertificateOfCell.lean#L42); named reference in type); [`Breakdown.CellCert.modelForm_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelForm.lean#L24) ([lean/Breakdown/FracCell/ModelForm.lean:24](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelForm.lean#L24); named reference in type).

**Theorem · Compare model form with analytic energy.** Chosen-derivative agreement, second-derivative identities, drift energy, and center pairings imply that model form minus potential loss times squared field size is bounded by the local-field pairing with the negative second trace under the model hypotheses. [`modelForm_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelForm.lean#L24).

### Breakdown.FracCell.ModelFormParts

Estimates the strain and curl-gradient contributions to model-form error and proves their measurability and integrability. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Curl-gradient contribution to the form.** The scalar contribution contracts the gradient entries with the specified antisymmetric curl-gradient expression involving the velocity and curl-gradient matrix. [`curlGradPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L21).

**Theorem · Operator action in Cartesian entries.** A Cartesian coordinate of an operator applied to a vector is the sum of that matrix row times the vector coordinates. [`coord_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L26).

**Theorem · Expand a three-dimensional norm.** The squared Euclidean norm equals the sum of the three squared Cartesian coordinates. [`norm_sq_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L35).

**Theorem · Expand a three-dimensional inner product.** The Euclidean inner product equals the sum of the three Cartesian coordinate products. [`inner_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L39).

**Theorem · Exact curl-gradient coefficient energy.** The squared coefficient sum in the curl-gradient term equals the stated combination of operator images, cross-product images, second application, and trace contributions. [`sq_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L42).

**Theorem · Sum coordinate cross-product energies.** The sum of squared cross-product norms with the three Cartesian unit vectors equals twice the squared vector norm. [`cross_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L52).

**Theorem · Bound trace-free curl-gradient terms.** For a trace-free matrix, the squared coefficient sum in the curl-gradient term is at most $7/2$ times the squared product of its operator norm and the velocity norm. [`part_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L57).

**Theorem · Entry energy as a double sum.** The entry-square energy equals the double sum of squared Cartesian matrix entries. [`entrySq_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L77).

**Theorem · Bound the curl-gradient contribution.** For a trace-free curl-gradient matrix, the absolute contribution is at most the square root of 7/2 times its operator norm, velocity norm, and the square root of gradient entry energy. [`part_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L81).

**Theorem · Entrywise Cauchy–Schwarz inequality.** The absolute entry inner product is at most the product of the square roots of the two entry-square energies. [`entryInner_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L101).

**Theorem · Bound curl energy by gradient energy.** The squared norm of the algebraic curl is at most twice the entry-square energy. [`curl_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L108).

**Theorem · Integrate a product bound.** A scalar integrand dominated by a nonnegative constant times two nonnegative L² factors has integral magnitude bounded by that constant times their L² norms. [`pairIntegral_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L114).

**Theorem · Separate strain and curl-gradient errors.** The difference of two jForm values equals the negative curl quadratic form of the strain difference plus the curl-gradient contribution of the curl-gradient difference. [`jForm_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L133).

**Theorem · Integrability of an L² pairing.** The pointwise inner product of two L² vector fields is integrable. [`pair_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L140).

**Theorem · Bound the energy of a matrix difference.** The entry-square energy of a difference is at most twice the entry energy of each matrix added together. [`entrySq_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L146).

**Theorem · Integrated entrywise Cauchy–Schwarz.** Measurable operator fields with integrable entry energies have an integrable entry pairing whose integral magnitude is bounded by the product of their entry-energy square roots. [`entryInner_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L155).

**Theorem · Model form under a.e. equality.** Replacing the gradient and second derivative by almost everywhere equal fields leaves the model form unchanged. [`formOf_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L190).

**Theorem · Continuity of the algebraic curl.** The algebraic curl is continuous in its operator argument. [`continuous_curlOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L216).

**Theorem · Continuity of the curl-gradient map.** The matrix extracted as the gradient of the curl depends continuously on its second-derivative argument. [`continuous_curlGradMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L220).

**Theorem · Continuity of the symmetric part.** Taking the symmetric part of a spatial linear map is continuous. [`continuous_symPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L224).

**Theorem · Continuity of the curl-gradient term.** The curl-gradient form contribution depends jointly continuously on both matrices and the velocity vector. [`continuous_part`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L229).

**Theorem · Bound the symmetric part.** The operator norm of the symmetric part is at most the operator norm of the original map. [`norm_symPart_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L234).

**Theorem · Unit length of Cartesian basis vectors.** Every Cartesian unit vector has norm one. [`norm_unitVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L241).

**Theorem · Bound the permutation sign.** The absolute value of the three-index permutation sign is at most one. [`abs_permSign_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L244).

**Theorem · Bound the curl-gradient operator.** The operator norm of the curl-gradient matrix is at most eighty-one times the second-derivative operator norm. [`norm_curlGradMatrix_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L248).

**Theorem · The curl-gradient trace vanishes.** A second derivative symmetric in its Cartesian input indices produces a trace-free curl-gradient matrix. [`trace_curlGradMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L283).

**Theorem · Symmetry of the center second derivative.** For valid fractional cell data, the center second derivative is symmetric in its two Cartesian inputs almost everywhere. [`second_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L294).

**Theorem · The center curl gradient is trace-free.** The center curl-gradient matrix of valid fractional cell data has zero trace almost everywhere. [`trace_centre`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L348).

**Theorem · The curl-gradient error is trace-free.** The curl-gradient error matrix of valid fractional cell data has zero trace almost everywhere. [`trace_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L353).

**Theorem · Separate the two jForm contributions.** The jForm value equals the negative curl quadratic form of the strain matrix plus the curl-gradient contribution. [`jForm_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L363).

**Theorem · Measurability of the curl-gradient term.** Measurable matrix fields and a measurable velocity field give a measurable curl-gradient form contribution. [`part_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L366).

**Theorem · Integrability from two L² factors.** A measurable scalar function whose magnitude is bounded almost everywhere by a constant times two measurable square-integrable factors is integrable. [`int_of_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L372).

**Theorem · A center decay constant is nonnegative.** A constant satisfying the stated global center, gradient, and second-derivative decay bounds must be nonnegative. [`centre_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L380).

**Theorem · Negative radial powers are at most one.** For nonnegative s, the power $(1+‖y‖)^{-s}$ is at most one. [`rpow_neg_le_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L388).

**Theorem · Integrate a bounded curl quadratic.** A bounded measurable operator field paired quadratically with the curl of a second-order field gives an integrable scalar function. [`quad_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L391).

**Theorem · Continuity of the center strain.** The center strain field of valid fractional cell data is continuous. [`centreStrain_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L411).

**Theorem · Bound center strain and its derivatives.** Valid fractional cell data admit a nonnegative uniform center-strain bound that also controls the center second derivative with cubic spatial decay. [`centreStrain_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L415).

**Theorem · Integrate the strain-error pairing.** For valid cell data and a second-order field, the curl quadratic form of the strain-error matrix is integrable. [`strain_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L422).

**Theorem · Integrability of curl-gradient errors.** For valid cell data and a second-order field, curl-gradient-error norm times velocity norm is measurable and square-integrable, and its curl-gradient form contribution is integrable. [`curlGradError_data`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L438).

**Theorem · Integrability of the center form.** The center jForm evaluated on a second-order field is integrable for valid fractional cell data. [`centre_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelFormParts.lean#L492).

### Breakdown.FracCell.ModelLower

Transfers the certificate lower bound to the chosen analytic representatives and arbitrary gradient corrections. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Validity of chosen second-order data.** If a velocity has a second-order field witness, the chosen gradient and chosen second derivative also form a second-order field with that velocity. [`chosen_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelLower.lean#L16).

**Theorem · Weighted energy under a.e. equality.** Replacing gradient and second derivative fields by almost everywhere equal representatives leaves the weighted energy unchanged. [`weightedEnergy_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelLower.lean#L24).

**Theorem · Nonnegative weighted derivative energy.** A pointwise nonnegative weight gives nonnegative weighted energy for any gradient and second derivative fields. [`weightedEnergy_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelLower.lean#L32).

**Theorem · Transfer the model coercivity bound.** Chosen-derivative agreement, class-averaging of row measurements, and model regularity imply that coercivity times squared field size is bounded by model form, corrected squared row measurement, and weighted pin squares under the model hypotheses. [`modelLower_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelLower.lean#L43).

### Breakdown.FracCell.ModelPin

Bounds pinning errors by integrated entrywise Cauchy–Schwarz and transfers the result to chosen gradients. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Nonnegative entry energy.** The sum of squared Cartesian operator entries is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L15).

**Theorem · Continuity of entry energy.** The entry-square energy depends continuously on the linear map. [`entrySq_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L18).

**Theorem · Difference energy is symmetric.** The entry-square energy of A minus B equals that of B minus A. [`entrySq_sub_comm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L21).

**Theorem · Bound the energy of a matrix difference.** The entry-square energy of a difference is at most twice the sum of the two individual entry energies. [`entrySq_sub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L24).

**Theorem · Expand an affine matrix energy.** The entry energy of xA plus B equals $x^2$ times A's energy plus $2x$ times the entry pairing plus B's energy. [`entrySq_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L33).

**Theorem · Integrability of the entry pairing.** Two measurable operator fields with integrable entry energies have an integrable pointwise entry inner product. [`integrable_entryInner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L42).

**Theorem · Cauchy–Schwarz for integrated entries.** The square of the integrated entry pairing is bounded by the product of the two integrated entry energies under measurability and integrability assumptions. [`pair_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L61).

**Theorem · Control the pinning discrepancy.** Chosen-derivative agreement implies that the Euclidean norm of the difference between model pins and analytic gradient pins is at most pin loss times field size under the model hypotheses. [`modelPin_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelPin.lean#L87).

### Breakdown.FracCell.ModelRegular

Proves measurability and local square-integrability of the model field from bounded model coefficients and second-order field data. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Bound a vector coordinate.** The absolute value of any Cartesian coordinate is at most the Euclidean norm. [`coord_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L15).

**Theorem · Expand in Cartesian unit vectors.** Every spatial vector equals the sum of its coordinates times the Cartesian unit vectors. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L18).

**Theorem · Bound an operator image by its columns.** The norm of an operator applied to a vector is at most the vector norm times the sum of the Cartesian column norms. [`apply_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L22).

**Theorem · Norm of a coordinate vector.** A vector with one nonzero Cartesian coordinate has norm equal to the absolute value of that coordinate. [`single_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L30).

**Theorem · A coarse cross-product bound.** The norm of a cross product is at most six times the product of the vector norms. [`cross_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L33).

**Theorem · Bound the permutation sign.** The absolute value of the three-index permutation sign is at most one. [`sign_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L57).

**Theorem · Bound curl by column norms.** The algebraic curl norm is at most nine times the sum of the operator's Cartesian column norms. [`curl_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L61).

**Theorem · Bound the axial turn.** The axial-turn vector has norm at most twice the original vector norm. [`turn_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L88).

**Theorem · Bound the second-derivative trace.** The second-derivative trace norm is at most the sum of the norms of its diagonal Cartesian entries. [`trace_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L94).

**Theorem · Scale a Cartesian unit vector.** Inserting x in coordinate i equals x times the ith Cartesian unit vector. [`single_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L97).

**Theorem · Continuity of the cross product.** The cross product is jointly continuous in its two vector arguments. [`cross_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L101).

**Theorem · Continuity of the algebraic curl.** The algebraic curl depends continuously on the linear map. [`curl_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L105).

**Theorem · Continuity of the axial turn.** The axial-turn map is continuous. [`turn_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L109).

**Theorem · Continuity of the second trace.** The second-derivative trace depends continuously on the bilinear map. [`trace_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L117).

**Theorem · Measurability of pointwise application.** For any measure, applying a measurable operator field to a measurable spatial vector field gives a measurable result. [`apply_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L121).

**Theorem · Measurability of cross products.** For any measure, the cross product of two measurable spatial vector fields is measurable. [`cross_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L127).

**Theorem · Gradient columns belong to L².** Each Cartesian gradient column in a second-order field belongs to L². [`grad_col_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L132).

**Theorem · Diagonal second derivatives belong to L².** Each diagonal Cartesian second-derivative column in a second-order field belongs to L². [`second_col_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L144).

**Theorem · Local L² regularity of the model field.** A second-order field gives a measurable, locally square-integrable model field when the model velocity and curl are measurable and bounded and the model actuators lie in L². [`field_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L160).

**Theorem · Uniform bounds for model coefficients.** Valid fractional cell data admit a single global bound for both the model velocity and model curl. [`model_bounded_all`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L260).

**Theorem · Establish model-field regularity.** Chosen-derivative agreement implies measurability and local square-integrability of the certificate model field for valid fractional cells with $1<α<5/4$, admissible parameter values, and second-order field data. [`modelRegular_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModelRegular.lean#L270).

### Breakdown.FracCell.OffAxisCore

This module lifts rectangular smoothing estimates to three-dimensional cell fields whose inner radius is positive. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Subtracting cell shapes.** Subtracting two cell shape fields subtracts their coefficient functions. [`shape_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L19).

**Theorem · Continuity on a fixed radial slice.** A continuous function of radius and height remains continuous when the radius is fixed. [`cont_slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L30).

**Theorem · Continuity of the height integral.** Integrating a continuous function over a fixed height interval gives a continuous function of radius. [`cont_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L34).

**Theorem · Ordered rectangular integrals.** A pointwise inequality between continuous functions on an ordered rectangle gives the same inequality between their iterated integrals. [`rect_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L38).

**Theorem · Adding rectangular integrals.** The iterated integral of two continuous functions on a rectangle is the sum of their iterated integrals. [`rect_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L47).

**Theorem · Scaling a rectangular integral.** A constant factor can be moved outside the iterated integral over radius and height. [`rect_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L58).

**Theorem · Continuous radial derivative.** A continuously differentiable function of radius and height has a continuous radial partial derivative. [`partial_r`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L62).

**Theorem · Continuous height derivative.** A continuously differentiable function of radius and height has a continuous height partial derivative. [`partial_z`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L74).

**Theorem · Adding the cylindrical weight.** A rectangular smoothing bound acquires at most the outer-to-inner radius factor when the cylindrical radial weight is inserted. [`rect_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L86).

**Theorem · Smoothing respects equality a.e..** A block smoothing estimate transfers to a field equal to the original field almost everywhere. [`smoothing_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L160).

**Theorem · Choosing a polynomial representative.** A smoothing estimate for every exact polynomial representative gives the estimate for an almost-everywhere represented block field. [`smoothing_of_everywhere`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L180).

**Theorem · Off-axis smoothing from rectangles.** The rectangular estimate, shape norm identity and shape gradient estimate together imply the off-axis block smoothing statement. [`offAxisCore_of_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L196).

**Theorem · Off-axis smoothing from gradients.** The rectangular estimate and shape gradient estimate imply off-axis block smoothing after supplying the shape norm identity. [`offAxisCore_of_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L293).

### Breakdown.FracCell.OffAxisCoreGrad

This module controls the gradient of an off-axis cell shape by radial, height and angular coefficient energies. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Expansion in the cylindrical frame.** Every three-vector expands in the orthonormal cylindrical frame at a fixed angle. [`frame_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L21).

**Theorem · Energy in the cylindrical frame.** The squared norm of a vector is the sum of its squared cylindrical-frame components. [`frame_energySum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L29).

**Theorem · Energy in the coordinate frame.** The squared norm of a vector is the sum of its squared standard-coordinate components. [`std_energySum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L34).

**Theorem · Matrix energy in a rotated frame.** The sum of squared matrix entries equals the sum of squared images of the cylindrical-frame vectors. [`entrySq_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L39).

**Theorem · Reconstructing a linear map.** A linear map is the sum of rank-one maps formed from its images of the cylindrical-frame vectors. [`clm_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L57).

**Theorem · A gradient column is a shape field.** Applying the encoded shape gradient to a frame vector selects the corresponding coefficient column. [`column`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L63).

**Theorem · Continuous gradient coefficients.** For a positive inner radius, continuously differentiable shape coefficients give continuous encoded gradient coefficients. [`coef_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L78).

**Theorem · Nonnegative angular weights.** Every angular weight is nonnegative because it is an integral of a square. [`weight_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L99).

**Theorem · Equal weights for nonzero modes.** The sine and cosine weights agree when the angular mode is nonzero. [`weight_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L102).

**Theorem · The angular gradient bound.** With nonnegative compatible sine and cosine weights, the angular coefficient energy is bounded by the squared mode-plus-one factor. [`ang_ineq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L121).

**Theorem · Summing under rectangular integrals.** Finite weighted sums of continuous coefficient functions commute with rectangular integration. [`rect_ct`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L140).

**Definition · A rank-one frame operator.** The frame outer product sends a vector to its inner product with the first factor times the second factor. [`frameOuter`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L151).

**Theorem · Continuous rank-one operators.** The rank-one frame operator depends continuously on both vector factors. [`frameOuter_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L153).

**Theorem · Simplifying a radial inverse weight.** For nonzero radius, multiplying a squared inverse-radius factor by radius leaves one inverse-radius factor. [`inv_sq_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L157).

**Theorem · Gradient bound from a weak gradient.** The explicit weak-gradient identity supplies the integrability, symmetry and energy estimate required for shape gradients. [`shapeGrad_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L160).

**Theorem · Supplying the shape gradient bound.** The weak-gradient statement implies the full shape gradient statement. [`shapeGrad_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L274).

**Theorem · Off-axis smoothing via weak gradients.** The rectangle estimate and explicit weak-gradient statement imply the off-axis block smoothing estimate. [`offAxisCore_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L277).

### Breakdown.FracCell.OffAxisCoreNorm

This module computes the spatial squared norm of an off-axis shape by angular orthogonality and cylindrical integration. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Continuity on a fixed radial slice.** A continuous function of radius and height remains continuous when the radius is fixed. [`cont_slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L19).

**Theorem · Continuity of the height integral.** Integrating a continuous function over a fixed height interval gives a continuous function of radius. [`cont_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L23).

**Theorem · Summing rectangular integrals.** A finite sum of continuous functions can be integrated term by term over a rectangle. [`rect_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L27).

**Theorem · Sine and cosine are orthogonal.** The integral of the same-mode sine-cosine product over a full angular period is zero. [`trig_cross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L35).

**Theorem · Angular energy of two coefficients.** Integrating the square of a sine-cosine combination leaves the two squared coefficients with their angular weights. [`trig_sq_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L45).

**Theorem · The rectangular cell cross-section.** At positive radius, membership in a cell solid is equivalent to membership in its radial and reflected-height intervals. [`mem_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L64).

**Theorem · The shape norm in cylindrical form.** Away from the axis and the symmetry plane, the squared shape norm splits into the active cell's frame components. [`norm_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L79).

**Theorem · Integrating the angular shape norm.** Away from the symmetry plane, angular integration replaces sine-cosine squares by their angular weights. [`theta_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L99).

**Theorem · Measurable cell shapes.** Continuous coefficient functions produce a measurable cell shape field. [`shape_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L120).

**Theorem · Frame vectors have norm at most one.** Every encoded frame vector has norm at most one, including points where cylindrical coordinates degenerate. [`frame_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L131).

**Theorem · Trigonometric factors are bounded.** Each sine or cosine mode has norm at most one. [`trig_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L136).

**Theorem · Coordinate bounds inside a cell.** A point in a cell solid lies between its radial bounds and between the two extreme reflected heights. [`solid_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L142).

**Theorem · The cylindrical shape norm identity.** The shape field is square integrable and its spatial energy equals the weighted sum of its rectangular coefficient energies. [`shapeNorm_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L149).

**Theorem · Supplying the shape norm identity.** The complete shape norm statement is proved without an additional named interface premise. [`shapeNorm_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L282).

### Breakdown.FracCell.OffAxisCoreSlope

This module turns global Lipschitz control and almost-everywhere classical derivatives into the weak gradient needed for off-axis smoothing. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Coordinates commute with integration.** Taking a coordinate of an integrable vector field's integral equals integrating that coordinate. [`coord_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L18).

**Theorem · Lipschitz derivatives are weak gradients.** A globally Lipschitz field with the stated derivative almost everywhere has that field as its weak gradient. [`weak_of_slopeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L22).

**Theorem · Constructing the shape weak gradient.** The shape Lipschitz statement and almost-everywhere derivative statement imply its weak-gradient statement. [`shapeWeak_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73).

**Theorem · Assembling off-axis smoothing.** The rectangle estimate, shape Lipschitz control and almost-everywhere derivative identity imply off-axis block smoothing. [`offAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L78).

### Breakdown.FracCell.OffAxisCoreSlopeSt

This module states the Lipschitz and classical-derivative obligations for shapes with coefficients vanishing on the cell boundary. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · Lipschitz control of cell shapes.** This proposition requires a global Lipschitz constant for an off-axis shape with continuously differentiable coefficients vanishing on every cell face. [`ShapeSlopeStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlopeSt.lean#L15).

**Interface providers.** [`Breakdown.CellCert.Spectral.Internal.ShapeSlope.shapeSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L280) ([lean/Breakdown/FracCell/ShapeGrad.lean:280](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L280); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.Spectral.shapeSlope_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L704) ([lean/Breakdown/FracCell/ShapeGrad.lean:704](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L704); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.shapeWeak_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73) ([lean/Breakdown/FracCell/OffAxisCoreSlope.lean:73](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73); named reference in type); [`Breakdown.CellCert.Spectral.offAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L78) ([lean/Breakdown/FracCell/OffAxisCoreSlope.lean:78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L78); named reference in type); [`Breakdown.CellCert.Spectral.spectral_of_blocks_of_derivs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L105) ([lean/Breakdown/FracCell/SpectralAssembly.lean:105](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L105); named reference in type).

**Interface · The classical shape derivative.** This proposition requires the encoded gradient to be the classical derivative almost everywhere for those boundary-vanishing off-axis shapes. [`ShapeDerivStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlopeSt.lean#L23).

**Interface providers.** [`Breakdown.CellCert.Spectral.shapeDeriv_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L707) ([lean/Breakdown/FracCell/ShapeGrad.lean:707](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShapeGrad.lean#L707); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.shapeWeak_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73) ([lean/Breakdown/FracCell/OffAxisCoreSlope.lean:73](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73); named reference in type); [`Breakdown.CellCert.Spectral.offAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L78) ([lean/Breakdown/FracCell/OffAxisCoreSlope.lean:78](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L78); named reference in type); [`Breakdown.CellCert.Spectral.spectral_of_blocks_of_derivs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L105) ([lean/Breakdown/FracCell/SpectralAssembly.lean:105](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L105); named reference in type).

### Breakdown.FracCell.OffAxisCoreSt

This module names reflected height bounds, angular weights and the norm and gradient obligations used in off-axis smoothing. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The lower reflected height.** The lower height is the original lower endpoint on one side and the negative upper endpoint on the reflected side. [`solidLower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSt.lean#L16).

**Definition · The upper reflected height.** The upper height is the original upper endpoint on one side and the negative lower endpoint on the reflected side. [`solidUpper`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSt.lean#L18).

**Definition · The squared angular mode integral.** The angular weight is the integral of the squared sine or cosine mode over one full period. [`trigWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSt.lean#L20).

**Interface · The shape norm identity.** This proposition requires square integrability and the exact cylindrical energy formula for continuous off-axis shape coefficients. [`ShapeNormStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSt.lean#L22).

**Interface providers.** [`Breakdown.CellCert.Spectral.Internal.OffAxisCoreNorm.shapeNorm_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L149) ([lean/Breakdown/FracCell/OffAxisCoreNorm.lean:149](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L149); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.Spectral.shapeNorm_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L282) ([lean/Breakdown/FracCell/OffAxisCoreNorm.lean:282](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreNorm.lean#L282); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.offAxisCore_of_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L196) ([lean/Breakdown/FracCell/OffAxisCore.lean:196](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L196); named reference in type).

**Interface · The shape gradient energy bound.** This proposition requires a square-integrable weak gradient with the prescribed mode symmetry and the stated rectangular derivative-energy bound. [`ShapeGradStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSt.lean#L30).

**Interface providers.** [`Breakdown.CellCert.Spectral.Internal.OffAxisCoreGrad.shapeGrad_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L160) ([lean/Breakdown/FracCell/OffAxisCoreGrad.lean:160](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L160); named premises: `ShapeWeakStatement`); [`Breakdown.CellCert.Spectral.shapeGrad_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L274) ([lean/Breakdown/FracCell/OffAxisCoreGrad.lean:274](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L274); named premises: `ShapeWeakStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.offAxisCore_of_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L196) ([lean/Breakdown/FracCell/OffAxisCore.lean:196](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L196); named reference in type); [`Breakdown.CellCert.Spectral.offAxisCore_of_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L293) ([lean/Breakdown/FracCell/OffAxisCore.lean:293](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCore.lean#L293); named reference in type); [`Breakdown.CellCert.Spectral.spectral_of_blocks_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L97) ([lean/Breakdown/FracCell/SpectralAssembly.lean:97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L97); named reference in type).

### Breakdown.FracCell.OffAxisCoreWeakSt

This module encodes cylindrical derivatives of cell shapes and states that the resulting field is their weak gradient. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The encoded shape gradient.** The encoded gradient sums cell indicators and trigonometric coefficient matrices in the cylindrical frame. [`shapeGradField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreWeakSt.lean#L15).

**Definition · Angular differentiation of a shape.** The angular coefficient combines differentiation of the trigonometric mode with differentiation of the cylindrical frame. [`angularCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreWeakSt.lean#L21).

**Definition · Radial, angular and height derivatives.** The gradient coefficient selects the radial derivative, a capped inverse-radius angular derivative, or the height derivative according to its column. [`shapeGradCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreWeakSt.lean#L26).

**Reader note.** The angular coefficient uses max(r, innerRadius) in its denominator. On a positive-radius cell this agrees with the intended inverse-radius coefficient, while the definition stays total outside that cell.

**Interface · The explicit shape weak gradient.** This proposition requires the encoded gradient to be a weak gradient for boundary-vanishing continuously differentiable off-axis shapes. [`ShapeWeakStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreWeakSt.lean#L33).

**Interface providers.** [`Breakdown.CellCert.Spectral.shapeWeak_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73) ([lean/Breakdown/FracCell/OffAxisCoreSlope.lean:73](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreSlope.lean#L73); named premises: `ShapeDerivStatement`, `ShapeSlopeStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.Internal.OffAxisCoreGrad.shapeGrad_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L160) ([lean/Breakdown/FracCell/OffAxisCoreGrad.lean:160](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L160); named reference in type); [`Breakdown.CellCert.Spectral.shapeGrad_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L274) ([lean/Breakdown/FracCell/OffAxisCoreGrad.lean:274](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L274); named reference in type); [`Breakdown.CellCert.Spectral.offAxisCore_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L277) ([lean/Breakdown/FracCell/OffAxisCoreGrad.lean:277](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OffAxisCoreGrad.lean#L277); named reference in type).

### Breakdown.FracCell.OnAxisCore

This module combines axis-rectangle smoothing and an axis lift to construct three-dimensional smoothing on cells meeting the axis. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Continuous cutoff polynomial fields.** A continuous radial cutoff times a finite radial polynomial with continuous height coefficients is continuous. [`cut_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L17).

**Theorem · Continuous two-variable polynomials.** Evaluating a polynomial in two real variables defines a continuous function. [`poly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L23).

**Theorem · Smoothing respects equality a.e..** A block smoothing estimate transfers to a field equal to the original field almost everywhere. [`smoothing_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L33).

**Theorem · Choosing a polynomial representative.** A smoothing estimate for every exact polynomial representative gives the estimate for an almost-everywhere represented block field. [`smoothing_of_everywhere`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L53).

**Theorem · Axis smoothing from its components.** The axis rectangle estimate, norm identity and lift statement together imply axis block smoothing. [`onAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L68).

**Theorem · Axis smoothing from a rectangle lift.** The axis rectangle estimate and lift statement imply axis block smoothing after supplying the axis norm identity. [`onAxisCore_of_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L182).

### Breakdown.FracCell.OnAxisLiftSt

This module states the norm and lifting formulas for cells meeting the axis, including the vanishing condition on horizontal constant terms. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · The axis shape norm identity.** This proposition identifies the energy of a square-integrable axis shape with twice pi times its weighted rectangular coefficient energy. [`AxisNormStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisLiftSt.lean#L15).

**Interface providers.** [`Breakdown.CellCert.Spectral.axisNorm_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L132) ([lean/Breakdown/FracCell/OnAxisNorm.lean:132](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L132); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.onAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L68) ([lean/Breakdown/FracCell/OnAxisCore.lean:68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L68); named reference in type).

**Interface · Lifting an axis rectangle field.** This proposition requires a square-integrable weak-gradient lift of the cutoff polynomial field with the stated error-plus-gradient estimate. [`AxisLiftStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisLiftSt.lean#L26).

**Interface providers.** [`Breakdown.CellCert.Spectral.axisLift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLift.lean#L11) ([lean/Breakdown/FracCell/AxisLift.lean:11](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLift.lean#L11); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.Spectral.axisLift_of_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLiftEnergy.lean#L187) ([lean/Breakdown/FracCell/AxisLiftEnergy.lean:187](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLiftEnergy.lean#L187); named premises: `LiftGradStatement`); [`Breakdown.CellCert.Spectral.axisLift_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLiftEnergy.lean#L287) ([lean/Breakdown/FracCell/AxisLiftEnergy.lean:287](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisLiftEnergy.lean#L287); named premises: `LiftDerivStatement`, `LiftSlopeStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Spectral.onAxisCore_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L68) ([lean/Breakdown/FracCell/OnAxisCore.lean:68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L68); named reference in type); [`Breakdown.CellCert.Spectral.onAxisCore_of_rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L182) ([lean/Breakdown/FracCell/OnAxisCore.lean:182](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisCore.lean#L182); named reference in type); [`Breakdown.CellCert.Spectral.spectral_of_blocks_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L97) ([lean/Breakdown/FracCell/SpectralAssembly.lean:97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/SpectralAssembly.lean#L97); named reference in type).

### Breakdown.FracCell.OnAxisNorm

This module integrates the two reflected axis cells and proves the cylindrical norm identity for their fields. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The axis-cell indicator.** This scalar indicator is one when the cylindrical point lies in the selected cell solid and zero otherwise. [`cellInd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L19).

**Definition · The lower axis-cell height.** The selected cell's lower height is the original lower endpoint or the negative upper endpoint on reflection. [`zLow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L22).

**Definition · The upper axis-cell height.** The selected cell's upper height is the original upper endpoint or the negative lower endpoint on reflection. [`zHigh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L24).

**Theorem · Membership in an axis cell.** At positive radius in an axis cell, membership is determined by the outer radius and the selected height interval. [`mem_cell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L26).

**Theorem · The axis field in a fixed frame.** At a valid positive-radius cylindrical point, the axis field expands in the angular frame with the two cell indicators as coefficients. [`field_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L43).

**Theorem · The squared axis-field norm.** The squared axis-field norm is the sum of the squared indicator-weighted frame coefficients. [`norm_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L53).

**Theorem · Indicators take values zero or one.** The axis-cell scalar indicator always equals zero or one. [`ind_cases`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L61).

**Theorem · Reflected cells do not overlap a.e..** For positive radius and nonzero height, the two reflected cell indicators have zero product. [`ind_cross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L67).

**Theorem · Separating the two axis-cell energies.** Away from the symmetry plane, the radial-weighted square of the two-cell field separates into the two indicator-weighted energies. [`sq_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L78).

**Theorem · Integrating one axis-cell piece.** A continuous coefficient's indicator-weighted energy is integrable and equals its radial-weighted integral over the selected rectangle. [`piece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L88).

**Theorem · Supplying the axis norm identity.** The axis shape norm identity is proved from cylindrical integration and disjointness of the reflected cell interiors. [`axisNorm_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OnAxisNorm.lean#L132).

### Breakdown.FracCell.OneVarTail

This module proves the one-variable derivative-tail inequality using weighted polynomial projection and integration by parts. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · Absolute continuity under equality.** Equality throughout the unoriented interval transfers absolute continuity to the replacement function. [`ac_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L9).

**Lemma · Complexifying absolute continuity.** A real absolutely continuous function remains absolutely continuous after inclusion in the complex numbers. [`ac_ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L23).

**Lemma · An integral primitive is continuous.** The primitive of an interval-integrable function is absolutely continuous when based inside the interval. [`ac_primitive`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L31).

**Lemma · Integration by parts on a segment.** An integral representation of the first factor gives the endpoint terms and the derivative-transfer identity on an ordered segment. [`ibp_seg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L48).

**Lemma · Conjugating powers of real numbers.** Complex conjugation fixes every natural power of a real number viewed as complex. [`conj_pow_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L105).

**Lemma · Polynomial form of line projection.** The line projection is represented by a complex polynomial of degree at most the requested cutoff. [`lineProj_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L108).

**Lemma · Projection residual moments vanish.** When coefficients satisfying the moment equations exist, the chosen projection residual is orthogonal to every monomial through the cutoff. [`lineProj_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L121).

**Lemma · Orthogonality to all low polynomials.** Vanishing weighted monomial moments imply orthogonality to every polynomial of degree at most the cutoff. [`orth_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L135).

**Lemma · Coefficients of a finite power sum.** The selected coefficient of the finite monomial expansion equals the corresponding input coefficient. [`coeff_sum_fin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L155).

**Lemma · Solving weighted projection moments.** A continuous nonnegative weight positive inside a nondegenerate interval admits coefficients solving the weighted projection equations for integrable data. [`pairing_exists`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L167).

**Lemma · Continuous polynomial evaluation.** A complex polynomial evaluated on the real line is continuous. [`pc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L298).

**Lemma · Differentiating a complex polynomial.** The derivative of a complex polynomial along the real line is evaluation of its polynomial derivative. [`pd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L301).

**Lemma · Smoothness of polynomial evaluation.** A complex polynomial evaluated on the real line is continuously differentiable. [`cd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L305).

**Lemma · Weighted square bounds give integrals.** Weighted square integrability and measurability imply integrability of the weight times the function on the compact interval. [`wt_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L313).

**Lemma · Subtracting a continuous comparison.** Weighted square integrability is preserved after subtracting a continuous comparison function on the compact interval. [`sq_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L327).

**Lemma · A bounded extra weight is integrable.** An additional continuous weight between zero and one preserves weighted square integrability on the interval. [`w_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L345).

**Lemma · Integration by parts at an endpoint.** The derivative-transfer identity extends to the endpoint when the boundary product tends to zero and both products are integrable. [`ibp_lim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L359).

**Theorem · The weighted derivative-tail bound.** Under the weighted projection and dual-polynomial hypotheses, the derivative energy of the projection residual is bounded by the projected derivative's residual energy. [`hbase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L400).

**Lemma · Dual polynomials for constant weight.** For degree at least two, the constant weight admits the boundary-vanishing dual polynomials used in the tail estimate. [`dual_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L696).

**Lemma · Dual polynomials for radial weight.** On an interval starting at zero, the radial weight admits the dual-polynomial identity used in the tail estimate. [`dual_id`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L725).

**Theorem · The one-variable tail estimate.** The one-variable tail statement is proved for the two weights used by the cell argument. [`main_statement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L757).

**Theorem · Supplying the tail estimate.** The completed one-variable tail estimate is exported as its named proposition. [`oneVarTailGood`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/OneVarTail.lean#L769).

### Breakdown.FracCell.ParamDefs

This module states the recovery property of the finite parametrization used to eliminate cell relations. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Interface · Recovery from the relation kernel.** This proposition requires the parametrization to return the original vector whenever valid parameter data are applied to a vector in the relation kernel. [`ParamRecoverStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamDefs.lean#L16).

**Interface providers.** [`Breakdown.CellCert.CellFormula.paramRecover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamRecover.lean#L35) ([lean/Breakdown/FracCell/ParamRecover.lean:35](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamRecover.lean#L35); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CertCell.CellCalculus.harmonicParam_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L164) ([lean/Breakdown/CertCell/CellCalculusStatements.lean:164](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L164); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_recover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShiftedParam.lean#L111) ([lean/Breakdown/FracCell/ShiftedParam.lean:111](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ShiftedParam.lean#L111); named reference in type); [`Breakdown.CellCert.CellFormula.trueParam_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/TrueParam.lean#L9) ([lean/Breakdown/FracCell/TrueParam.lean:9](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/TrueParam.lean#L9); named reference in type).

### Breakdown.FracCell.ParamRecover

This module reconstructs a relation-kernel vector from its free coordinates and the solved block. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Separating free and solved entries.** An injective solved-coordinate selection decomposes a data vector into its free part and its selected single-coordinate entries. [`decomp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamRecover.lean#L9).

**Theorem · The relation on solved coordinates.** Applying the relation matrix to the solved-coordinate vector equals applying the solved block to its coefficients. [`mulVec_sum_single`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamRecover.lean#L26).

**Theorem · Proving parameter recovery.** Valid parameter data recover every vector annihilated by the relation matrix. [`paramRecover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ParamRecover.lean#L35).

### Breakdown.FracCell.PlaneDeleted

This module uses mirror symmetry to prove that the trace moments removed on the symmetry plane vanish. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · Coordinate signs under reflection.** Reflection leaves the first two coordinates unchanged and negates the third coordinate. [`sR`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L16).

**Theorem · Reflection signs square to one.** Each coordinate reflection sign has square one. [`sR_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L18).

**Theorem · The two mirror definitions agree.** The linear-solver mirror isometry agrees pointwise with the cell mirror map. [`mirror_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L21).

**Theorem · Reflection is an involution.** Reflecting a point twice returns the original point. [`mirror_mirror'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L23).

**Theorem · Reflecting a coordinate vector.** Reflection multiplies each coordinate unit vector by its coordinate sign. [`mirror_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L26).

**Theorem · Reflection of a weak derivative.** Mirror symmetry of a field gives the corresponding signed mirror symmetry of its square-integrable weak directional derivative almost everywhere. [`weak_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L29).

**Theorem · Square-integrable gradient columns.** A measurable matrix field with integrable entry-square sum has square-integrable coordinate columns. [`memLp_grad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L88).

**Theorem · Square-integrable second derivatives.** A measurable second-derivative field with integrable coordinate-square sum has each coordinate second derivative in L². [`memLp_second`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L99).

**Theorem · Mirror identities for field derivatives.** An admissible second-order field and its first two derivatives satisfy the stated signed mirror identities almost everywhere. [`field_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L113).

**Definition · Reflection as a linear map.** The mirror isometry is viewed as a continuous linear map. [`mirrorClm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L135).

**Theorem · The linear mirror acts by reflection.** Applying the continuous linear mirror map gives the cell mirror function. [`mirrorClm_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L137).

**Theorem · Reflection respects scalar factors.** Reflecting a scalar multiple equals the same multiple of the reflected vector. [`mirror_smul'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L139).

**Theorem · Linear maps agree on a basis.** Two linear maps out of three-dimensional space are equal when they agree on every coordinate unit vector. [`clm_ext`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L142).

**Theorem · The reflected gradient operator.** The coordinate reflection identities determine the full gradient operator by conjugation with the mirror map. [`grad_at`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L147).

**Theorem · The reflected second derivative.** The coordinate reflection identities determine the full second derivative by reflecting its two arguments and its value. [`second_at`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L156).

**Theorem · Almost-everywhere cylindrical slicing.** A spatial almost-everywhere property holds for almost every positive-radius height pair and almost every angle. [`cyl_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L172).

**Theorem · Periodicity of the Fourier phase.** The integer azimuthal Fourier phase is periodic with period twice pi. [`exp_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L227).

**Theorem · Periodicity of cylindrical points.** Adding a full turn to the angle leaves the cylindrical point unchanged. [`cyl_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L235).

**Theorem · Periodicity of the radial direction.** The radial unit vector repeats after a full angular turn. [`radial_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L238).

**Theorem · Periodicity of the angular direction.** The angular unit vector repeats after a full angular turn. [`angular_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L241).

**Theorem · Equal periodic integrals.** Periodic functions equal almost everywhere on the centered angular interval have equal integrals over a full period. [`circle_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L244).

**Theorem · Moving reflection in an inner product.** Reflection can be moved from either argument of the real inner product to the other. [`inner_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L256).

**Theorem · Height reflection in coordinates.** Negating cylindrical height applies the spatial mirror map. [`cyl_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L260).

**Theorem · Reflecting the cylindrical frame.** Reflection preserves the radial and angular frame vectors and negates the axial vector. [`frame_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L263).

**Theorem · Reflected vector components.** Each cylindrical component of a reflected vector is multiplied by its coordinate reflection sign. [`frameVec_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L267).

**Theorem · Reflected matrix components.** Conjugating a matrix by reflection multiplies each frame entry by the product of its two coordinate signs. [`frameMat_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L271).

**Theorem · Reflected Hessian frame components.** Reflecting both inputs and the output of the second derivative multiplies each frame component by three coordinate signs. [`frameThird_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L277).

**Theorem · The phase after one full turn.** The azimuthal complex exponential is unchanged when its angle is increased by twice pi. [`exp_per'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L288).

**Theorem · Equality of periodic mode integrals.** Almost-everywhere proportional periodic integrands give the same proportionality between their normalized mode integrals. [`mode_congr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L292).

**Theorem · Mirror symmetry of all field modes.** The velocity, gradient and second-derivative modes inherit the corresponding products of reflection signs almost everywhere. [`modes_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L308).

**Predicate · The mode reflection condition.** This proposition records the signed mirror identities for velocity modes and their first two derivative modes at positive radius. [`MirrorModes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L351).

**Definition · Reflection of the height coordinate.** The measurable equivalence keeps radius fixed and negates height. [`refl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L358).

**Theorem · The planar reflection formula.** The planar reflection sends a radius-height pair to the same radius and opposite height. [`refl_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L360).

**Theorem · Planar reflection preserves measure.** Reflection of the height coordinate preserves planar Lebesgue measure. [`refl_mp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L362).

**Theorem · Reflecting a height-interval integral.** Integrating over a reflected height interval equals integrating the height-reflected integrand over the original interval. [`reflect_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L365).

**Theorem · The zero-radius line has measure zero.** The first coordinate of a planar point is nonzero almost everywhere. [`ae_fst_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L374).

**Theorem · The edge sign changes on reflection.** Reflecting a nonzero height endpoint negates the orientation sign relative to height zero. [`edgeSign_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L382).

**Theorem · Reflecting a lower interval endpoint.** The lower endpoint formed from zero and a negated number is the negative of the corresponding upper endpoint. [`min_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L391).

**Theorem · Reflecting an upper interval endpoint.** The upper endpoint formed from zero and a negated number is the negative of the corresponding lower endpoint. [`max_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L394).

**Theorem · The reflected reciprocal coefficient.** Reflection negates the reciprocal height-width coefficient. [`coefA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L397).

**Theorem · The reflected affine coefficient.** Simultaneous reflection of height and endpoint preserves the normalized affine height coefficient. [`coefB`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L400).

**Theorem · Oddness of a height-strip moment.** Oddness of the field and evenness of its height derivative make the reflected height-strip moment its negative. [`height_reflect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L403).

**Theorem · Oddness of a corner moment.** The stated parities of a field and its derivatives make the reflected corner moment its negative. [`corner_reflect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L416).

**Theorem · A symmetric odd strip moment vanishes.** A height-strip moment vanishes when reflection both preserves and negates it under the stated field parity. [`height_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L430).

**Theorem · A symmetric odd corner moment vanishes.** A corner moment vanishes when reflection both preserves and negates it under the stated derivative parities. [`corner_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L437).

**Theorem · Reflection for layout modes.** When the layout order agrees with the cell order, the general mode reflection condition gives the layout's signed mode identities. [`modes_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L447).

**Theorem · Refactoring a strip-moment weight.** A height-strip moment is unchanged when its two scalar weights are replaced by weights with the same product. [`weight_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L463).

**Theorem · Vanishing traces on the symmetry plane.** Segment independence and mirror parity force the selected velocity and gradient trace moments on height zero to vanish. [`seg_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L468).

**Theorem · Deleting symmetry-plane coordinates.** Segment independence, corner independence and mirror-mode symmetry imply the plane-deletion statement. [`planeDeleted_of_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L500).

**Theorem · Supplying plane deletion from traces.** Segment and corner independence imply plane deletion after deriving mirror-mode symmetry from admissibility. [`planeDeleted_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PlaneDeleted.lean#L583).

### Breakdown.FracCell.ProjCoef

This module identifies the coefficients of the finite cell projection by orthogonality. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · Selecting one coefficient in a square.** The double Kronecker-delta sum returns the requested coefficient inside the degree square and zero outside it. [`sum_pick`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCoef.lean#L12).

**Theorem · Coefficients of the cell projection.** The cell projection has the asserted coefficient values through the chosen cutoff. [`projCoef_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCoef.lean#L35).

### Breakdown.FracCell.ProjCompose

This module solves weighted polynomial normal equations and proves that radial and height projections compose to the cell projection. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The weighted monomial Gram matrix.** This matrix pairs monomials by integrating their product against the interval weight. [`pairMat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L15).

**Definition · Weighted monomial moments.** This vector stores the weighted pairings of a function with all monomials through the degree cutoff. [`mom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L18).

**Theorem · Real monomials equal their conjugates.** Complex conjugation fixes a natural power of a real number viewed as complex. [`conj_pow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L21).

**Theorem · Symmetry of monomial pairings.** Interchanging the monomial indices leaves the weighted Gram matrix entry unchanged. [`pairMat_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L24).

**Theorem · The Gram matrix equals its transpose.** The weighted monomial Gram matrix is symmetric. [`pairMat_transpose`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L32).

**Theorem · Integrable weighted monomial products.** A continuous weight times two monomials is integrable over a compact interval. [`mono_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L36).

**Theorem · The projection normal equations.** The weighted residual moment equals the original moment minus the Gram matrix applied to the proposed coefficients. [`normal_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L45).

**Theorem · A polynomial vanishing infinitely often.** A finite polynomial expansion that vanishes on an infinite real set has all coefficients zero. [`poly_zero_of_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L72).

**Theorem · Zero integral forces interior vanishing.** A continuous nonnegative function with zero integral on a closed interval vanishes throughout its interior. [`vanish_of_integral_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L97).

**Theorem · The weighted Gram matrix is injective.** A continuous nonnegative weight positive in the interior of a nondegenerate interval gives an injective monomial Gram matrix. [`pairMat_inj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L112).

**Theorem · Projection from inverse Gram matrices.** With integrable moments and an injective Gram matrix, line projection is the polynomial obtained by applying the inverse matrix to the moments. [`lineProj_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L173).

**Theorem · Continuity of the radial line weight.** The cell's radial line weight is continuous. [`lw_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L198).

**Theorem · The line weight is nonnegative.** The radial line weight is nonnegative throughout the closed radial interval. [`lw_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L207).

**Theorem · The line weight is positive inside.** The radial line weight is positive in the open radial interval. [`lw_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L214).

**Theorem · The cell measure is a product.** Lebesgue measure restricted to the cell rectangle is the product of its restricted radial and height measures. [`rect_measure`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L221).

**Theorem · Continuous product monomials.** The product of a radial monomial and a height monomial is continuous. [`mono_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L226).

**Theorem · Continuous rectangular polynomials.** A finite polynomial with matrix coefficients in radius and height is continuous. [`poly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L229).

**Theorem · Integrability of weighted cross terms.** A measurable weighted-square-integrable function can be paired integrably with a continuous test function on the cell rectangle. [`cross_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L233).

**Theorem · Integrability after polynomial removal.** Subtracting a continuous comparison function preserves integrability of the weighted pairing with a continuous test function. [`sub_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L251).

**Theorem · Separating radial and height moments.** The weighted rectangular pairing of product monomials factors into its radial and height pairings. [`prod_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L264).

**Theorem · Normal equations on a rectangle.** A polynomial residual's rectangular moments equal the original moments minus the coefficient matrix multiplied by the two Gram matrices. [`pair_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L276).

**Theorem · Monomials lie in the degree space.** A product monomial whose two indices are within the cutoff belongs to the rectangular polynomial space. [`mono_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L326).

**Theorem · Monomial moments give orthogonality.** Vanishing moments against all allowed product monomials give orthogonality to the whole rectangular polynomial space. [`orth_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L331).

**Theorem · Cancelling invertible matrix factors.** Equal products with the same two invertible outer matrices have equal middle matrices. [`cancel_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L358).

**Theorem · Rearranging coefficient contractions.** The nested coefficient contraction equals the double sum formed using the transposed matrix product. [`coef_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L368).

**Theorem · Moving a matrix across a dot product.** A matrix can be moved from a matrix-vector product to the corresponding row-vector product inside the scalar sum. [`dot_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L375).

**Definition · Radial moments at fixed height.** This vector collects the weighted radial moments of a field with height held fixed. [`bvec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L380).

**Definition · The rectangular moment matrix.** This matrix integrates the radial moment vectors against the height monomials. [`bmat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L383).

**Definition · The rectangular projection coefficients.** The coefficient matrix applies the inverse radial and height Gram matrices to the rectangular moments. [`coefM`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L386).

**Theorem · Radial and height projections compose.** The successive one-variable projections equal the specified two-variable cell projection. [`projCompose`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ProjCompose.lean#L392).

### Breakdown.FracCell.PuncturedWeakScalar

This module removes the origin from the weak-gradient calculation by controlling the shrinking-ball error. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Gradient coordinates as derivatives.** Pairing the scalar gradient with a coordinate unit vector gives the directional Fréchet derivative. [`inner_gradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L15).

**Theorem · Integration by parts on an annulus.** A Lipschitz function on a closed annulus obeys integration by parts against a smooth test supported in its interior. [`annulus_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L20).

**Theorem · The inverse radius is locally integrable.** The reciprocal Euclidean norm is integrable on every ball in three-dimensional space. [`invNorm_ball`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L58).

**Theorem · Integrability from inverse-radius bounds.** A measurable scalar function bounded almost everywhere by a ball-supported reciprocal-radius majorant is integrable. [`inv_bound_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L68).

**Theorem · Cubic scaling of ball volume.** A closed ball of nonnegative radius has volume equal to the radius cubed times the unit-ball volume. [`ball_volume`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L75).

**Theorem · The shrinking-ball error bound.** A uniformly bounded function supported in a ball has integral bounded by its bound times the ball's cubic volume. [`small_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L80).

**Theorem · Removing the origin from a weak gradient.** A bounded measurable function locally Lipschitz on annuli, with the stated reciprocal-radius derivative bound, has its classical gradient as a weak gradient. [`weak_of_punctured`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/PuncturedWeakScalar.lean#L88).

### Breakdown.FracCell.QuadFormSplit

This module splits the global coercive quadratic form into cell integrals, row contributions, an exterior term and the global finite matrix. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The norm as three coordinate squares.** The squared norm of a three-vector is the sum of its three squared coordinates. [`norm_sq_coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L17).

**Theorem · A coordinate is bounded by the norm.** The absolute value of any coordinate is at most the Euclidean norm. [`coord_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L21).

**Theorem · Coordinate vectors have unit norm.** Each coordinate unit vector has norm one. [`unit_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L28).

**Theorem · Matrix entries obey the operator bound.** The absolute value of a matrix entry is bounded by the operator norm. [`entry_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L31).

**Theorem · Nonnegative matrix entry energy.** The sum of squared matrix entries is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L37).

**Theorem · Column energy is bounded by total energy.** The squared norm of any coordinate column is at most the sum of squared matrix entries. [`col_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L40).

**Theorem · Permutation signs are bounded.** The absolute value of a three-index permutation sign is at most one. [`sign_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L43).

**Theorem · A bound for one stretching row.** The specified curl-stretching row expression is bounded by eight times the product of the operator and vector norms. [`row_term_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L47).

**Theorem · A bound for the stretching contraction.** The full stretching contraction is bounded by thirty-six times the sum of the squared norm product and gradient entry energy. [`part_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L88).

**Theorem · Writing matrix energy by entries.** The matrix entry energy is the double sum of the squared coordinate entries. [`entrySq_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L114).

**Theorem · Curl energy versus gradient energy.** The squared curl norm is at most twice the sum of squared matrix entries. [`curl_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L118).

**Theorem · Bounding antisymmetric contractions.** The sum of squared permutation-sign contractions is at most twice the sum of squared input entries. [`sign_sum_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L124).

**Theorem · Curl-gradient and Hessian energies.** The curl-gradient square is at most twice the full second-derivative square. [`curlGradSq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L130).

**Theorem · Nonnegative curl-gradient energy.** The curl-gradient square is nonnegative. [`curlGradSq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L140).

**Theorem · Continuous extraction of curl.** Extracting curl from a linear map is continuous. [`continuous_curlOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L143).

**Theorem · Continuous curl-gradient energy.** The curl-gradient square depends continuously on the second-derivative tensor. [`continuous_curlGradSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L147).

**Theorem · Continuity of the stretching form.** The stretching form is jointly continuous in its three matrix arguments and vector argument. [`continuous_jForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L151).

**Theorem · Adding curl-gradient matrices.** The curl-gradient matrix of a sum is the sum of the curl-gradient matrices. [`curlGradMatrix_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L157).

**Theorem · Scaling the curl-gradient matrix.** Scaling the second-derivative tensor scales its curl-gradient matrix by the same scalar. [`curlGradMatrix_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L162).

**Theorem · A bounded curl-gradient operator.** A fixed nonnegative constant bounds the curl-gradient matrix norm by the second-derivative operator norm. [`curlGradMatrix_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L172).

**Theorem · The cell weight obeys its bound.** Valid form data bound the absolute cell weight by the specified maximum. [`weight_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L180).

**Theorem · A uniform model-strain bound.** Valid form data provide a nonnegative uniform bound on the model strain. [`strain_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L188).

**Theorem · Cubic decay of the model curl gradient.** Valid form data bound the model curl gradient by a constant times the inverse cube of one plus distance. [`decay_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L219).

**Theorem · A cubic product inequality.** For nonnegative inputs, the squared first input times the second is bounded by the sum of their cubes. [`cubic_mean_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L255).

**Theorem · Integrable decaying cross energy.** The model curl-gradient decay makes its squared norm product with an admissible second-order field integrable. [`decay_sq_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L262).

**Theorem · The integral of the local density.** For admissible data, the local density is integrable and its integral is the global form minus the coercive weighted energy. [`density_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L298).

**Theorem · Splitting a full integral into cells.** A valid cell split partitions an integrable function's full integral into its cell integrals and exterior integral. [`cell_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L387).

**Theorem · Summing a cell-supported integral.** For an integrable function vanishing outside the cell region, its full integral equals the sum of the cell integrals. [`cell_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L394).

**Theorem · Summing row energies by cell.** Grouping the weighted row pairings by their assigned cell gives the squared global row functional. [`rows_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L404).

**Theorem · The global finite-matrix correction.** The global matrix quadratic value is exactly the negative multiplier-coordinate penalty and the negative pin-coordinate penalty. [`global_value`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L412).

**Theorem · The global quadratic-form decomposition.** The stated cell, row, exterior and global-matrix decomposition of the coercive quadratic form is proved. [`quadFormSplit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/QuadFormSplit.lean#L453).

### Breakdown.FracCell.RadialAxisCross

This module extends radial trace formulas across the axis using the odd radial velocity mode and its even derivative. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Interface · A primitive starting on the axis.** This proposition requires the zero angular radial-velocity mode to equal the integral of its radial gradient mode from the axis almost everywhere. [`AxisPrimitiveStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L24).

**Interface providers.** [`Breakdown.CellCert.CellCoordinates.RadialAxisCrossInternal.axisPrimitive_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L425) ([lean/Breakdown/FracCell/RadialAxisCross.lean:425](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L425); named premises: `ModeRadialWeakStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellCoordinates.radialAxisCross_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L453) ([lean/Breakdown/FracCell/RadialAxisCross.lean:453](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L453); named reference in type).

**Theorem · A half-turn preserves a full integral.** Shifting a periodic angular integrand by half a turn leaves its full-period integral unchanged. [`half_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L33).

**Theorem · Negative radius as a half-turn.** Negating the radius is equivalent to adding pi to the cylindrical angle. [`cylPoint_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L40).

**Theorem · A full turn preserves the point.** Adding twice pi to the cylindrical angle leaves the spatial point unchanged. [`cylPoint_full`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L43).

**Theorem · A half-turn reverses radial direction.** The radial unit vector is negated by a half-turn. [`radialUnit_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L46).

**Theorem · A full turn preserves radial direction.** The radial unit vector is unchanged by a full turn. [`radialUnit_full`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L50).

**Theorem · The zero radial mode is odd.** The radial component of the zero angular velocity mode is odd in the signed radius. [`modeVec_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L53).

**Theorem · The radial derivative mode is even.** The radial-radial component of the zero angular gradient mode is even in the signed radius. [`gradMode_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L72).

**Theorem · Product measure on a rectangle.** Restricted planar Lebesgue measure on a rectangle equals the product of the two restricted interval measures. [`rect_measure`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L88).

**Theorem · Integrable radial slices.** A function integrable on a rectangle has an integrable radial slice for almost every height. [`slice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L92).

**Theorem · Integrability under radial reflection.** Reflecting the radial coordinate carries integrability on a positive radial strip to the corresponding negative strip. [`reflect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L97).

**Theorem · A linear weight as a nested integral.** Integrating a function times distance from the left endpoint equals integrating its upper-tail integrals. [`weight_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L117).

**Theorem · The axis-based line identity.** If the field agrees almost everywhere with the primitive based at zero, the displayed affine integral equals the integral of its derivative from zero to the outer endpoint. [`line_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L164).

**Theorem · The axis-based strip identity.** The axis-based line identity integrates over height to identify the corresponding rectangular strip expression. [`strip_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L205).

**Theorem · Crossing the axis preserves the trace.** An odd field with an even derivative and the stated primitive formula has the same radial-strip moment across the axis as on the positive side. [`cross_generic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L224).

**Theorem · The primitive has zero axis constant.** The integral representation and integrability of the angular quotient force the radial primitive's integration constant at the axis to vanish. [`axis_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L287).

**Theorem · The axis primitive above the plane.** The radial-line and angular-mode statements give the axis-based primitive formula on height intervals above the symmetry plane. [`axisPrimitive_upper`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L344).

**Theorem · Changing the order of a.e. slicing.** A planar almost-everywhere statement holds for almost every height and then almost every radius. [`swap_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L367).

**Theorem · Moving the mirror in an inner product.** The mirror map can be transferred between the two arguments of the real inner product. [`inner_mirror_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L373).

**Theorem · Reflecting cylindrical height.** Negating the height of a cylindrical point gives its spatial reflection. [`cylPoint_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L377).

**Theorem · Reflection fixes the radial unit vector.** The radial unit vector lies in the fixed plane of the mirror map. [`radialUnit_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L382).

**Theorem · Even radial modes in height.** For a second-order admissible field, the zero radial velocity mode and its radial derivative are even in height almost everywhere. [`mode_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L387).

**Theorem · The axis primitive from weak calculus.** The radial weak-mode statement implies the axis-based primitive statement. [`axisPrimitive_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L425).

**Theorem · Axis crossing from the primitive.** The axis primitive statement supplies the radial trace identity across the axis. [`radialAxisCross_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L453).

**Theorem · Axis crossing from a weak radial mode.** The radial weak-mode statement gives the radial axis-crossing statement through its primitive formula. [`radialAxisCross_of_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L460).

**Theorem · Supplying the axis-crossing identity.** The radial axis-crossing statement is proved with its weak-mode prerequisite supplied. [`radialAxisCross`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialAxisCross.lean#L463).

### Breakdown.FracCell.RadialMixedWeak

This module obtains the mixed radial-height weak derivative by applying radial calculus to the axial column of the second derivative. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · Measurable axial Hessian columns.** A measurable second-derivative field remains measurable after fixing its first argument to the axial unit vector. [`axis_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialMixedWeak.lean#L14).

**Theorem · Integrable axial Hessian energy.** The full second-derivative square bound implies integrability of the matrix energy of its axial column. [`axis_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialMixedWeak.lean#L18).

**Theorem · The mixed mode as a gradient mode.** The radial-height second-derivative mode equals the radial gradient mode of the axial Hessian column. [`third_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialMixedWeak.lean#L34).

**Theorem · The mixed radial weak derivative.** The mixed radial-height mode satisfies the stated weak-derivative identity. [`radialMixedWeak_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialMixedWeak.lean#L37).

### Breakdown.FracCell.RadialProjBound

This module solves the radial projection equations and proves weighted least-squares minimality on a cell interval. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · A polynomial from its coefficients.** The coefficient vector is evaluated as a finite complex polynomial in the real radius. [`pl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L20).

**Definition · The radial monomial Gram matrix.** This matrix contains the cell-weighted radial pairings of the monomials through the cutoff. [`pairingMat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L22).

**Definition · The radial moment vector.** This vector pairs the supplied function with each radial monomial against the cell line weight. [`rhs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L25).

**Definition · Solving the radial moment equations.** The proposed radial projection coefficients are the inverse Gram matrix applied to the radial moment vector. [`sol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L28).

**Theorem · Nonnegative radial projection weight.** The cell line weight is nonnegative on the closed radial interval. [`w_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L30).

**Theorem · Positive interior radial weight.** The cell line weight is positive on the open radial interval. [`w_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L36).

**Theorem · Continuous coefficient polynomials.** Every finite coefficient polynomial is continuous as a function of radius. [`pl_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L42).

**Theorem · Continuity of the complex weight.** The radial line weight remains continuous when viewed as complex-valued. [`wc_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L46).

**Theorem · Continuous complex monomials.** A real variable raised to a natural power and viewed as complex defines a continuous function. [`pow_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L49).

**Theorem · Continuous conjugate monomials.** The complex conjugate of a real-variable monomial is continuous. [`pow_conj_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L52).

**Theorem · Integrable weighted continuous squares.** A continuous function has integrable line-weighted squared norm on the compact radial interval. [`sq_int_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L55).

**Theorem · Integrable radial cross pairings.** A measurable function with finite weighted square energy pairs integrably with a continuous function on the radial interval. [`cross_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L59).

**Theorem · Integrable radial residual energy.** Subtracting a continuous function preserves finite weighted square energy on the radial interval. [`sub_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L72).

**Theorem · Polynomial moments as a matrix product.** Pairing a coefficient polynomial against a monomial gives the corresponding Gram-matrix product entry. [`pl_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L87).

**Theorem · The radial residual equation.** A residual moment equals the original function's moment minus the Gram matrix applied to the polynomial coefficients. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L103).

**Theorem · Conjugating a coefficient polynomial.** Conjugation distributes through the finite polynomial sum and conjugates both coefficients and monomials. [`conj_pl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L119).

**Theorem · Vanishing pairings with low polynomials.** Vanishing radial moments against the allowed monomials force the weighted pairing with every allowed coefficient polynomial to vanish. [`cross_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L124).

**Theorem · Subtracting coefficient polynomials.** Subtracting two coefficient polynomials is evaluation of their coefficient difference. [`pl_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L140).

**Theorem · The least-squares radial projection.** Any solution of the radial normal equations minimizes the weighted squared error among all polynomials of the same cutoff degree. [`min1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L145).

**Theorem · Zero polynomials have zero coefficients.** For a valid cell interval, vanishing throughout its interior forces every coefficient of the polynomial to be zero. [`pl_eq_zero_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L184).

**Theorem · The radial Gram kernel is zero.** For a valid cell box, a coefficient vector annihilated by the radial Gram matrix is zero. [`pairingMat_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L202).

**Theorem · Injectivity of the radial Gram matrix.** The radial Gram matrix of a valid cell box acts injectively on coefficient vectors. [`pairingMat_inj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L236).

**Theorem · The chosen coefficients solve the system.** For a valid cell box, the inverse-matrix coefficients satisfy the radial normal equations. [`pairingMat_sol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L241).

**Theorem · Identifying the chosen radial projection.** For a measurable finite-energy radial slice, the defined radial projection equals the polynomial from the inverse-matrix solution. [`projR_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L248).

**Theorem · The radial projection error bound.** The radial projection satisfies the stated weighted approximation bound. [`radialProjBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialProjBound.lean#L277).

### Breakdown.FracCell.RadialTrace

This module proves radial integration by parts for gradient modes, including weighted integrability near the axis. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Theorem · A compact-interval derivative bound.** A continuously differentiable scalar function has a uniformly bounded derivative on each closed interval. [`deriv_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L16).

**Theorem · Linear vanishing at an endpoint.** A continuously differentiable function vanishing at the left endpoint is bounded by a constant times distance from that endpoint. [`lin_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L22).

**Theorem · Integrating a tail primitive by parts.** A weighted-integrable derivative and a test function vanishing at the left endpoint give the stated tail-primitive integration identity. [`tail_ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L41).

**Theorem · The weak line derivative identity.** A line represented by its tail primitive satisfies integration by parts against a continuously differentiable test vanishing at both endpoints. [`line_ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L135).

**Predicate · Weak differentiation in radius.** This proposition requires the radial integration-by-parts identity against smooth compact tests supported at positive radius. [`IsRadialWeak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L177).

**Theorem · Smooth step approximations.** Each step approximation used to localize radial tests is smooth. [`step_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L181).

**Theorem · Smooth interval tests.** Each radial interval test constructed from the step approximations is smooth. [`test_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L187).

**Theorem · An interval test vanishes outside.** Outside the enlarged interval, the interval test and its derivative are both zero. [`test_out`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L192).

**Theorem · Differentiating a product test radially.** The radial derivative of a separated radial-height test differentiates only its radial factor. [`prod_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L210).

**Theorem · The radial identity on typical slices.** A weak radial derivative with the stated cell integrability satisfies the localized test identity for almost every height. [`slice_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L226).

**Theorem · A fixed-radius line has measure zero.** The first coordinate differs from any prescribed real number at almost every planar point. [`ae_fst_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L347).

**Theorem · Integrability with a distance weight.** Integrability with the cell line weight implies integrability after multiplication by distance from the inner radial endpoint. [`shifted_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L351).

**Theorem · Measurability from a weighted product.** Integrability after multiplication by distance from a fixed radial line implies almost-everywhere strong measurability of the unweighted function. [`meas_of_shifted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L366).

**Theorem · Radial integration by parts on a cell.** The weak radial identity extends to a boundary-vanishing radial test times a continuous height factor, with integrability of both terms. [`rect_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L378).

**Definition · The frame from planar coordinates.** This vector family encodes radial, angular and axial frame directions using two planar coordinates. [`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L474).

**Theorem · The planar frame on the unit circle.** Evaluating the planar frame at cosine and sine gives the cylindrical frame at that angle. [`unitAt_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L478).

**Definition · A frame coordinate as a linear form.** This linear form pairs a vector with the selected planar-frame vector. [`coordForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L480).

**Theorem · The coordinate form in the frame.** On the unit circle, the coordinate form is the inner product with the selected cylindrical-frame vector. [`coordForm_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L483).

**Theorem · Smooth planar frame coordinates.** Each coordinate of a planar-frame vector is smooth in the two planar inputs. [`unitAt_coord_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L487).

**Theorem · Smooth planar frame vectors.** Each planar-frame vector is smooth in the two planar inputs. [`unitAt_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L492).

**Theorem · Smooth frame coordinate forms.** The linear form extracting a planar-frame coordinate depends smoothly on the planar inputs. [`coordForm_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L495).

**Definition · A frame matrix-entry functional.** This continuous linear functional extracts a matrix entry using the selected input and output frame vectors. [`entryForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L499).

**Theorem · Smooth frame-entry functionals.** The frame matrix-entry functional depends smoothly on its planar inputs. [`entryForm_smooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L502).

**Theorem · Matrix entries in the circular frame.** On the unit circle, the entry functional is the inner product of the selected matrix column with the selected frame vector. [`entryForm_circle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L505).

**Theorem · Expansion in coordinate unit vectors.** Every three-vector is the sum of its coordinates times the corresponding unit vectors. [`vec_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L510).

**Theorem · Operator norm from column norms.** The norm of a linear map out of three-dimensional space is at most the sum of its coordinate-column norms. [`opNorm_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L513).

**Theorem · Locally integrable columns give a field.** A measurable linear-map field is locally integrable when all its coordinate columns are locally integrable. [`locInt_cols`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L522).

**Theorem · Radial differentiation of gradient modes.** For an admissible second-order field, each gradient mode has its corresponding second-derivative mode as a weak radial derivative. [`field_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L534).

**Theorem · Local integrability of the Hessian.** The second-derivative tensor of an admissible second-order field is locally integrable. [`second_loc`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L601).

**Definition · The phased second-derivative component.** This kernel multiplies the radial second-derivative frame component by its azimuthal Fourier phase. [`thirdKernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L608).

**Theorem · Continuous phase-component kernel.** The phased second-derivative component is jointly continuous in angle and tensor. [`thirdKernel_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L611).

**Theorem · The phase kernel obeys the tensor bound.** The norm of the phased second-derivative component is bounded by the tensor's operator norm. [`thirdKernel_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L618).

**Theorem · Periodicity of tensor frame components.** A tensor's cylindrical-frame component is unchanged by a full angular turn. [`frameThird_per`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L634).

**Theorem · The radial mode as an angular integral.** The radial gradient mode is the normalized integral of the phased tensor component over the centered angular interval. [`radialGradMode_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L638).

**Theorem · Weighted integrability of radial modes.** The radial second-derivative mode is integrable with the cell line weight for an admissible second-order field. [`third_lw_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L648).

**Theorem · Integrability of gradient modes.** Each gradient mode of an admissible second-order field is integrable on a valid cell rectangle. [`grad_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L658).

**Theorem · Supplying radial trace calculus.** The radial trace statement is proved from weak mode differentiation and the weighted cell integration-by-parts identity. [`radialTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RadialTrace.lean#L698).

### Breakdown.FracCell.RayLine

This module proves the one-dimensional exterior estimate underlying the ray-region Hardy inequality. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · A Hardy bound along an interval.** A continuously differentiable function vanishing at the outer endpoint has the integral of its square bounded by four times its radius-squared weighted derivative energy. [`rayLine_interval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayLine.lean#L13).

### Breakdown.FracCell.RaySmooth

This module integrates the one-dimensional ray estimate over directions to obtain an exterior bound for smooth compactly supported fields. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Lemma · Polar integration of nonnegative fields.** A measurable nonnegative spatial function integrates as a sphere integral of its radial integrals with the radius-squared Jacobian. [`polar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L20).

**Lemma · Directional energy versus total energy.** For a unit vector, the squared norm of its image is at most the matrix entry-square sum. [`apply_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L49).

**Lemma · Integrability on an exterior half-line.** A continuous function dominated in support by a compactly supported function is integrable on every exterior half-line. [`ion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L73).

**Lemma · Vector energy in coordinates.** The squared vector norm equals the sum of its squared coordinates. [`sq_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L79).

**Lemma · The vector estimate along a ray.** The line estimate bounds a smooth compactly supported vector field along a ray by four times its radius-weighted gradient energy. [`ray_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L83).

**Lemma · The nonnegative ray-region estimate.** The ray inequality holds for nonnegative integrals with the homogeneous exterior-region indicator included. [`ray_ennreal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L142).

**Lemma · The smooth ray-region Hardy bound.** A positive homogeneous exterior threshold gives the inverse-radius energy bound with constant four for smooth compactly supported vector fields. [`main_one`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L215).

**Theorem · Lifting the line estimate to space.** The one-dimensional line statement implies the smooth spatial ray-region statement. [`raySmooth_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RaySmooth.lean#L252).

### Breakdown.FracCell.RayWeak

This module extends the smooth ray-region inequality to weak fields by mollification and radial cutoffs. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Theorem · The cutoff derivative lies in an annulus.** A nonzero derivative of the radial cutoff can occur only between its radius and twice that radius. [`fderiv_radialCutoff_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L18).

**Theorem · Controlling a square by a sixth power.** For a positive parameter, the scalar square is bounded by the sixth power divided by the parameter squared plus the parameter. [`sq_le_six_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L40).

**Theorem · The cutoff-gradient error vanishes.** For a continuous L⁶ field, the integral of its squared norm times the squared cutoff gradient tends to zero as the radius grows. [`cutoffTail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L54).

**Theorem · A tunable bound for a squared sum.** A positive parameter bounds a squared sum by the two squares with coefficients one plus the parameter and one plus its reciprocal. [`sq_add_le_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L152).

**Theorem · Gradient energy after applying a cutoff.** The cutoff field's gradient energy is bounded by a weighted original-gradient energy and an explicit cutoff-error term. [`entrySq_cutoff_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L160).

**Theorem · Large cutoffs preserve gradient energy.** For a smooth L⁶ field with finite gradient energy, sufficiently large radial cutoffs increase that energy by less than any chosen positive tolerance. [`cutoffEnergy`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L200).

**Theorem · Mollification contracts convex powers.** For an integrable norm power of order at least one, the mollified field's norm power is bounded by the mollified norm power. [`normPow_convolution_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L244).

**Theorem · Mollifying a weak gradient.** Each coordinate derivative of the mollified L⁶ field equals the mollification of its corresponding weak-gradient column. [`mollify_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L300).

**Theorem · Smooth approximation with energy control.** An L⁶ field with square-integrable weak gradient has smooth approximants converging almost everywhere with no increase in gradient energy. [`smoothApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L331).

**Theorem · Compact approximation of weak fields.** An L⁶ field with square-integrable weak gradient has smooth compactly supported approximants whose values and gradient entry-square densities converge almost everywhere, with total gradient-energy excess at most 1/(n+1). [`approxSeq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L410).

**Theorem · Nonnegative gradient entry energy.** The sum of squared entries of a linear map is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L457).

**Theorem · The ray estimate for weak fields.** The smooth ray-region statement implies the corresponding weak-field statement by the approximation sequence. [`rayWeak_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RayWeak.lean#L470).

### Breakdown.FracCell.RectAxis

This module combines the radial axis certificate and the height interval certificate to smooth polynomial data on an axis rectangle. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The height-interval resolvent.** The height resolvent rescales the fixed-interval resolvent to the given height endpoints and spectral parameter. [`zres`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L17).

**Theorem · Twice differentiable height resolvents.** Positive spectral parameter and ordered height endpoints give a twice continuously differentiable height resolvent. [`zres_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L21).

**Theorem · The height resolvent vanishes at ends.** For positive spectral parameter on a nondegenerate height interval, the height resolvent is zero at both endpoints. [`zres_ends`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L28).

**Theorem · The resolvent of zero is zero.** The height resolvent applied to the zero polynomial vanishes identically. [`zres_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L40).

**Theorem · Linearity of the height resolvent.** The height resolvent distributes over finite scalar combinations of polynomials. [`zres_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L46).

**Theorem · The height resolvent energy identity.** The integral pairing of the height residual with its resolvent equals the inverse-parameter derivative energy. [`zres_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L61).

**Theorem · The certified height smoothing bound.** An interval certificate bounds the height residual energy plus resolvent derivative energy for polynomials through its degree cutoff. [`zres_cert`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L125).

**Theorem · Integrability with a bounded parameter.** A continuous function composed with a bounded measurable parameter is integrable on an ordered finite interval. [`int1`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L132).

**Theorem · Integrating a parameterized rectangle.** A continuous function composed with a bounded measurable radial parameter is integrable against the product of finite interval measures. [`int2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L142).

**Theorem · Integrability on a compact rectangle.** A continuous planar function is integrable against the product of the two restricted finite interval measures. [`int2c`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L155).

**Theorem · Reordering rectangular integration.** Product-measure integrability gives integrable iterated integrals and permits their order to be exchanged. [`prod_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L159).

**Theorem · Regularity of a Lipschitz radial cutoff.** A Lipschitz cutoff is continuous and its rescaled derivative is measurable, bounded and defined by differentiability almost everywhere. [`cut_facts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L169).

**Theorem · Removing the apparent axis denominator.** When the angular index is one and the field has a radial factor, the inverse-radius energy reduces to the square of the remaining factor. [`iterm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L182).

**Theorem · The rescaled axis certificate bound.** The axis certificate controls radial cutoff error and derivative energy after rescaling, with the required radial divisibility for horizontal components. [`axis_nice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L188).

**Theorem · The radial cutoff error alone.** The axis certificate bounds the radial cutoff error of a polynomial by its certified weighted energy factor. [`axis_first`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L284).

**Theorem · Expanding a two-variable polynomial.** A polynomial of the stated outer degree expands as radial powers with height-polynomial coefficients. [`tve`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L303).

**Theorem · Combining radial and height errors.** The radial and height smoothing hypotheses give the full cylindrical rectangle estimate with the sum of their two error bounds. [`hbase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L310).

**Theorem · The axis-rectangle smoothing estimate.** The axis rectangle statement is proved by combining the axis certificate with the height interval certificate. [`rectAxis_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectAxis.lean#L445).

### Breakdown.FracCell.RectOff

This module combines two interval resolvents by tensor-product quadratic forms to prove the off-axis rectangle estimate. **Reading context:** Appendix B: projections, smoothing, cell relations and tail control in the local-to-global cell estimate (B.4–B.6).

**Definition · The rescaled interval resolvent.** The fixed-interval resolvent is transported to arbitrary interval endpoints and the corresponding rescaled spectral parameter. [`scaledRes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L17).

**Definition · Pairings of two function families.** This matrix records interval integrals of products from two indexed function families. [`pairMat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L21).

**Definition · A finite bilinear coefficient form.** The bilinear form contracts two finite coefficient vectors with a matrix. [`bform`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L23).

**Definition · The tensor coefficient form.** The tensor form contracts a coefficient matrix against one radial and one height bilinear form. [`kform`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L26).

**Definition · A separated finite function sum.** The tensor sum forms a finite function expansion from radial and height families and a coefficient matrix. [`tensorSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L29).

**Definition · The real monomial family.** The monomial family sends its degree and argument to the corresponding real power. [`powF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L32).

**Definition · Resolvents of the monomial family.** Each member is the rescaled interval resolvent applied to a single monomial. [`resF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L34).

**Definition · Derivatives of monomial resolvents.** Each member is the derivative of the corresponding rescaled monomial resolvent. [`dresF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L36).

**Definition · The monomial resolvent residual.** The residual subtracts the rescaled resolvent from its input monomial. [`diffF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L38).

**Theorem · Regularity and zero endpoint values.** A rescaled resolvent with positive parameter on a nondegenerate interval is twice continuously differentiable and vanishes at both ends. [`scaledRes_props`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L40).

**Theorem · Linearity of the interval resolvent.** The interval resolvent preserves finite scalar combinations of polynomial inputs. [`res_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L55).

**Theorem · Linearity after interval rescaling.** The rescaled interval resolvent preserves finite scalar combinations of polynomials. [`scaledRes_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L66).

**Theorem · The rescaled resolvent pairing identity.** Pairing a resolvent with an input polynomial splits into the two-resolvent pairing and the inverse-parameter derivative pairing. [`scaledRes_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L71).

**Theorem · Transposing a family pairing.** Exchanging the two function families transposes their pairing matrix. [`pairMat_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L139).

**Theorem · Integrating two finite expansions.** The integral of two finite continuous expansions equals their coefficient bilinear form against the pairing matrix. [`integral_bform`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L146).

**Theorem · Nonnegative Gram forms.** A same-family pairing matrix has nonnegative quadratic form on an ordered interval. [`bform_pairMat_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L165).

**Theorem · Exchanging the tensor directions.** Exchanging the two tensor matrices and transposing the coefficient array leaves the tensor form unchanged. [`kform_symm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L170).

**Theorem · Expanding two three-term matrices.** The tensor form of two three-term matrix combinations expands into their nine weighted pairings. [`kform_lin3`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L185).

**Theorem · Linearity in a three-term matrix.** The finite quadratic coefficient form distributes over a three-term scalar matrix combination. [`bform_lin3`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L195).

**Theorem · Continuous tensor expansions.** Finite separated expansions of continuous radial and height families are jointly continuous. [`tensor_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L213).

**Theorem · The integral tensor-product identity.** The rectangular integral of two continuous tensor expansions is their tensor coefficient form against the two pairing matrices. [`iint_tensor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L219).

**Theorem · Nonnegative tensor forms.** A nonnegative coefficient form combined with a same-family interval Gram matrix gives a nonnegative tensor form. [`kform_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L252).

**Theorem · Integrating a finite weighted sum.** A finite weighted sum of continuous rectangular functions can be integrated term by term. [`iint_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L277).

**Theorem · Continuity of the monomial family.** Each real monomial is continuous. [`cont_pow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L294).

**Theorem · The interval certificate as a form bound.** An interval certificate gives the residual-plus-derivative quadratic-form bound for finite polynomial coefficient vectors. [`cert_bform`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L296).

**Theorem · Pairing monomials with resolvents.** The monomial-resolvent pairing is the resolvent Gram pairing plus the inverse-parameter derivative Gram pairing. [`pairMat_pow_res`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L352).

**Theorem · Splitting the monomial Gram matrix.** The monomial Gram matrix splits into residual, twice the inverse-parameter derivative, and resolvent Gram matrices. [`pairMat_pow_pow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L379).

**Theorem · The polynomial as a tensor expansion.** A polynomial within both degree cutoffs equals the tensor expansion of its coefficient matrix in monomial families. [`twoVar_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L411).

**Theorem · The off-axis rectangle estimate.** The off-axis rectangle smoothing statement follows from the two certified interval resolvents. [`rectOff_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RectOff.lean#L429).

### Breakdown.FracCell.ReductionAdjointAdjointExtension

This module extends integration by parts from compact smooth tests to the weighted weak fields used in the adjoint-error estimate. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Interface · The drift adjoint pairing.** This proposition requires integrability and transfer of the drift operator to its adjoint for second-order fields and regular adjoint fields. [`DriftPairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L21).

**Interface providers.** [`Breakdown.CellCert.Reduction.driftPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L707) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:707](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L707); named premises: `SecondOrderTestApproxStatement`); [`Breakdown.CellCert.Reduction.driftPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L864) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:864](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L864); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · The convection adjoint pairing.** This proposition requires transfer of the linearized convection term to its adjoint for a decaying divergence-free background and regular adjoint field. [`ConvectionPairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L29).

**Interface providers.** [`Breakdown.CellCert.Reduction.convectionPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L867) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:867](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L867); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · Moving the negative second trace.** This proposition transfers the negative second trace between fields under the stated weak-trace and weighted L² hypotheses. [`NegTracePairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L41).

**Interface providers.** [`Breakdown.CellCert.Reduction.negTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L927) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:927](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L927); named premises: `SecondOrderTestApproxStatement`); [`Breakdown.CellCert.Reduction.negTracePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L952) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:952](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L952); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · The gradient-trace pairing identity.** This proposition equates the negative-trace pairing with the entrywise pairing of two weak gradients under their L² bounds. [`GradientTracePairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L47).

**Interface providers.** [`Breakdown.CellCert.Reduction.gradientTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L955) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:955](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L955); named premises: `SecondOrderTestApproxStatement`); [`Breakdown.CellCert.Reduction.gradientTracePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L988) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:988](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L988); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · The matrix-divergence pairing.** This proposition transfers a matrix weak divergence to the vector field with a negative sign under the stated weighted bounds. [`MatrixDivergencePairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L54).

**Interface providers.** [`Breakdown.CellCert.Reduction.matrixDivergencePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L991) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:991](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L991); named premises: `SecondOrderTestApproxStatement`); [`Breakdown.CellCert.Reduction.matrixDivergencePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1006) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:1006](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1006); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · Solenoidal fields kill gradient pairings.** This proposition requires an admissible solenoidal field to pair to zero with a scalar weak gradient satisfying the weighted L² assumptions. [`ScalarGradientTracePairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L61).

**Interface providers.** [`Breakdown.CellCert.Reduction.scalarGradientPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1009) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:1009](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1009); named premises: `SecondOrderTestApproxStatement`); [`Breakdown.CellCert.Reduction.scalarGradientPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1059) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:1059](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1059); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · Weighted bounds for compact weak traces.** This proposition gives a radius-weighted L² bound for a bounded measurable weak negative trace of a compactly supported C¹ field. [`CompactTraceWeightStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L67).

**Interface providers.** [`Breakdown.CellCert.Reduction.compactTraceWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1062) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:1062](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1062); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · Classical gradients of compact fields.** This proposition identifies the classical derivative of a compactly supported C¹ field as its weak gradient. [`CompactWeakGradientStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L71).

**Interface providers.** [`Breakdown.CellCert.Reduction.compactWeakGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L640) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:640](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L640); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named reference in type).

**Interface · Approximating through second order.** This proposition requires compact smooth tests converging in gradient energy, second-derivative energy and inverse-radius velocity energy. [`SecondOrderTestApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L75).

**Interface providers.** [`Breakdown.CellCert.Reduction.secondOrderTestApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L657) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:657](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L657); named premises: `GradientSecondApproxStatement`); [`Breakdown.CellCert.Reduction.secondOrderTestApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L704) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:704](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L704); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.driftPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L707) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:707](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L707); named reference in type); [`Breakdown.CellCert.Reduction.negTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L927) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:927](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L927); named reference in type); [`Breakdown.CellCert.Reduction.gradientTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L955) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:955](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L955); named reference in type); [`Breakdown.CellCert.Reduction.matrixDivergencePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L991) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:991](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L991); named reference in type); [`Breakdown.CellCert.Reduction.scalarGradientPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1009) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:1009](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1009); named reference in type).

**Theorem · Integrable pairings of L² fields.** The pointwise inner product of two L² vector fields is integrable. [`inner_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L86).

**Theorem · The L² norm as a square integral.** The squared norm of the L² equivalence class equals the integral of the field's squared norm. [`sq_integral_toLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L92).

**Theorem · Cauchy-Schwarz for vector integrals.** The absolute integral pairing of two L² fields is bounded by the product of their square-integral roots. [`abs_pair_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L99).

**Theorem · Passing an L² pairing to a limit.** Convergence in squared L² distance gives convergence of pairings against a fixed L² field. [`pair_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L110).

**Theorem · Square integrability gives L² membership.** A measurable vector field with integrable squared norm belongs to L². [`memLp_of_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L134).

**Theorem · The second-trace square bound.** The squared norm of the second trace is at most three times the full second-derivative square. [`trace_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L138).

**Theorem · A column is bounded by matrix energy.** The squared norm of a coordinate column is at most the sum of squared matrix entries. [`column_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L155).

**Theorem · Continuity of the second trace.** Taking the second trace is a continuous operation on second-derivative tensors. [`trace_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L158).

**Theorem · The second trace belongs to L².** A measurable tensor field with integrable full second-derivative square has an L² second trace. [`trace_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L163).

**Theorem · Matrix columns belong to L².** A measurable matrix field with integrable entry-square sum has each coordinate column in L². [`column_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L172).

**Theorem · Cancelling opposite radial weights.** Inverse-radius and radius factors cancel in the pointwise inner product almost everywhere. [`weighted_inner_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L181).

**Theorem · The inverse-radius norm identity.** The squared norm after inverse-radius scaling is the vector's squared norm divided by the squared radius. [`weighted_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L188).

**Theorem · Inverse-radius velocity is in L².** The inverse-radius-weighted velocity of an admissible second-order field belongs to L². [`weighted_velocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L191).

**Theorem · Convergence of weighted pairings.** Convergence in inverse-radius velocity energy gives convergence of pairings against a radius-weighted L² field. [`weighted_pair_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L199).

**Theorem · Continuous test-field second derivatives.** A smooth compact test vector field has a continuous second derivative. [`test_second_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L223).

**Theorem · Continuous test-field gradients.** A smooth compact test vector field has a continuous first derivative. [`test_first_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L227).

**Theorem · Second partials equal the Hessian trace.** The sum of second coordinate partial derivatives equals the trace of the second Fréchet derivative. [`ssp_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L231).

**Theorem · Convergence of second-trace pairings.** Convergence in full second-derivative energy gives convergence of negative-trace pairings against an L² vector field. [`trace_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L237).

**Theorem · Convergence of matrix-entry pairings.** Convergence in matrix entry energy gives convergence of entrywise pairings against a fixed finite-energy matrix field. [`entry_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L267).

**Theorem · Compact test fields belong to L².** Every smooth compact test vector field belongs to L². [`test_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L300).

**Theorem · Differentiating test fields.** A fixed directional derivative of a smooth compact test vector field is again a test vector field. [`test_dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L303).

**Theorem · Differentiating a test-field derivative.** The derivative of a fixed directional derivative is the second derivative applied in the stated order. [`dir_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L307).

**Theorem · Coordinates of a vector test.** Every coordinate of a smooth compact vector test is a smooth compact scalar test. [`coord_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L314).

**Theorem · Coordinates commute with differentiation.** Differentiating a coordinate of a test field equals the corresponding coordinate of its derivative. [`coord_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L319).

**Theorem · The coordinate inner-product formula.** The real inner product is the sum of the three products of corresponding coordinates. [`inner_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L327).

**Theorem · Weak differentiation with vector tests.** The weak-gradient identity extends coordinatewise to the inner product with a compact smooth vector test. [`weak_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L330).

**Theorem · Integrability from opposite weights.** A measurable scalar function dominated by a product is integrable when the two factors satisfy opposite radial L² weights. [`weighted_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L364).

**Theorem · Weighted L² bounds for approximants.** A measurable approximation with finite inverse-radius distance from an admissible field is itself in inverse-radius-weighted L². [`weighted_approx_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L376).

**Theorem · A coordinate obeys the vector norm.** Every absolute coordinate of a vector is bounded by its norm. [`coord_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L389).

**Theorem · A coordinate as an inner product.** The inner product with a coordinate unit vector equals that coordinate. [`inner_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L393).

**Theorem · The coordinate expansion of a vector.** Every vector is the finite sum of its coordinates times the coordinate unit vectors. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L396).

**Theorem · Applying a map to a coordinate sum.** Applying a linear map to a vector equals the coordinate-weighted sum of its columns. [`apply_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L400).

**Theorem · Smooth coordinates of a linear map.** Each coordinate of a linear map is a smooth scalar function. [`coordL_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L405).

**Theorem · Differentiating a linear coordinate.** The derivative of a linear coordinate function applies that same coordinate map to the direction. [`coordL_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L408).

**Theorem · Linear coordinates preserve test fields.** Multiplying a test vector field by a coordinate of a linear map gives another test vector field. [`ibp_test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L415).

**Theorem · The linear-coordinate product rule.** The directional derivative of the linear-coordinate-weighted test field splits into the two product-rule terms. [`ibp_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L419).

**Theorem · Integration by parts for linear drift.** Moving a linear vector field's directional derivative across a pairing adds its trace term and the derivative of the other field. [`ibp_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L427).

**Definition · Axial turning as a linear map.** The axial-turn map sends the first coordinate into the second and the second coordinate into the negative first. [`turnL`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L474).

**Theorem · The linear turn equals axial turning.** The continuous linear turn map acts as the axial-turn function. [`turnL_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L478).

**Theorem · The axial turn has zero trace.** The sum of the diagonal entries of axial turning is zero. [`turn_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L482).

**Theorem · The identity trace is three.** The trace of the three-dimensional identity is three. [`unit_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L485).

**Theorem · Axial turning contracts the norm.** The norm of an axially turned vector is at most the original norm. [`turn_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L488).

**Theorem · Skew symmetry of axial turning.** Moving axial turning across a real inner product changes its sign. [`turn_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L494).

**Theorem · Matrix energy controls operator action.** The norm of a matrix applied to a vector is bounded by the square root of its entry energy times the vector norm. [`clm_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L498).

**Theorem · Measurable matrix-vector application.** Applying a measurable matrix field to a measurable vector field gives a measurable vector field. [`apply_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L504).

**Theorem · Continuous axial turning.** The axial-turn map is continuous. [`turn_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L509).

**Theorem · Bounding the square of a sum.** The square of a sum is at most twice the sum of the two squares. [`sq_add_le2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L514).

**Theorem · A pointwise bound for the drift.** The drift norm is bounded by explicit parameter-weighted velocity and radius-times-gradient terms. [`drift_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L517).

**Theorem · Inverse-radius drift energy.** The inverse-radius squared drift is bounded by explicit multiples of inverse-radius velocity energy and gradient energy. [`drift_weighted_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L537).

**Theorem · A pointwise bound for adjoint drift.** The adjoint drift norm is bounded by the stated parameter-weighted adjoint field and radius-times-gradient terms. [`adj_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L561).

**Theorem · Radius-weighted adjoint drift energy.** The radius-weighted adjoint drift square is bounded by the stated weighted adjoint and fourth-power-radius gradient energies. [`adj_weighted_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L582).

**Theorem · Integrating four linear terms.** An integrable four-term scalar combination integrates to the same combination of the four integrals. [`integral_lin4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L603).

**Theorem · Weighted L² bounds for derivatives.** A fourth-power-radius gradient-energy bound gives a radius-weighted L² bound after applying the gradient to a norm-contracting linear image. [`clm_apply_memLp_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L614).

**Interface · Weak gradients against C¹ tests.** This proposition extends the weak-gradient identity to compactly supported C¹ scalar tests under local integrability assumptions. [`WeakGradientFirstOrderTestStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L630).

**Interface providers.** [`Breakdown.CellCert.Reduction.weakGradientFirstOrderTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L636) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:636](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L636); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Theorem · Proving the C¹ test extension.** The weak-gradient identity is proved for compactly supported C¹ tests. [`weakGradientFirstOrderTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L636).

**Theorem · Proving the compact gradient identity.** A compactly supported C¹ vector field has its classical derivative as its weak gradient. [`compactWeakGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L640).

**Theorem · Adding weighted velocity convergence.** The gradient-and-Hessian approximation statement implies the second-order test approximation with inverse-radius velocity control. [`secondOrderTestApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L657).

**Theorem · Second-order test approximation.** The full second-order compact-test approximation is proved with its prerequisite supplied. [`secondOrderTestApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L704).

**Theorem · Drift pairing from approximation.** The second-order test approximation statement implies the drift-adjoint pairing identity. [`driftPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L707).

**Theorem · Supplying the drift adjoint identity.** The drift-adjoint pairing statement is proved with the approximation input supplied. [`driftPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L864).

**Theorem · The convection adjoint identity.** The convection-adjoint pairing statement is proved under its background-field and adjoint regularity assumptions. [`convectionPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L867).

**Theorem · Trace pairing from approximation.** Second-order compact-test approximation implies the weak negative-trace pairing identity. [`negTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L927).

**Theorem · Supplying the negative-trace pairing.** The negative-trace pairing statement is proved with its approximation input supplied. [`negTracePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L952).

**Theorem · Gradient pairing from approximation.** Second-order compact-test approximation implies the gradient-trace pairing identity. [`gradientTracePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L955).

**Theorem · Supplying the gradient-trace pairing.** The gradient-trace pairing statement is proved with its approximation input supplied. [`gradientTracePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L988).

**Theorem · Divergence pairing from approximation.** Second-order compact-test approximation implies the matrix-divergence pairing identity. [`matrixDivergencePairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L991).

**Theorem · Supplying matrix-divergence pairing.** The matrix-divergence pairing statement is proved with its approximation input supplied. [`matrixDivergencePairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1006).

**Theorem · Gradient cancellation from approximation.** Second-order compact-test approximation implies cancellation of the scalar-gradient pairing. [`scalarGradientPairing_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1009).

**Theorem · Supplying scalar-gradient cancellation.** The scalar-gradient cancellation statement is proved with its approximation input supplied. [`scalarGradientPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1059).

**Theorem · The compact weak-trace weighted bound.** The bounded measurable weak negative trace of a compact C¹ field has the required radius-weighted L² bound. [`compactTraceWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L1062).

### Breakdown.FracCell.ReductionAdjointAdjointLocal_of_dual

This module bounds the local adjoint defect by combining its dual representation with weighted inverse-square and Cauchy-Schwarz estimates. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · A product majorant gives an L² bound.** A measurable scalar function dominated by two nonnegative square-integrable factors is integrable with the corresponding Cauchy-Schwarz integral bound. [`abs_integral_le_sqrt_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L20).

**Theorem · Nonnegative matrix entry squares.** The matrix entry-square sum is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L43).

**Theorem · Continuous matrix entry energy.** The matrix entry-square sum is continuous in the matrix. [`entrySq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L46).

**Theorem · Continuous second trace.** The second trace is continuous in the second-derivative tensor. [`trace_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L49).

**Theorem · Cauchy-Schwarz for matrix entries.** The absolute entrywise inner product is bounded by the product of the square roots of the two entry energies. [`entryInner_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L52).

**Theorem · The trace is bounded by tensor energy.** The squared second-trace norm is at most three times the full sum of squared tensor coordinates. [`trace_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L59).

**Theorem · The spatial origin has measure zero.** A spatial point is nonzero almost everywhere with respect to volume. [`ae_ne_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L74).

**Theorem · The matrix-field pairing bound.** The absolute integral entrywise pairing is bounded by the product of the square roots of the two matrix-field energies. [`pair_entry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L79).

**Theorem · Weighted two-term Cauchy-Schwarz.** For a positive weight, a two-term product sum is bounded by the two complementary weighted Euclidean norms. [`mul_add_mul_le_sqrt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L95).

**Theorem · The local adjoint defect bound.** For the stated fractional exponent, valid dual data and quantitative budget, the local adjoint error is bounded by its prescribed constant times the square root of field energy. [`adjointLocal_of_dual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109).

### Breakdown.FracCell.ReductionAdjointAdjointRepresentation

This module assembles the drift, convection, trace, pressure and pin integration identities into the exact dual decomposition of the adjoint defect. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · The origin is negligible for integration.** Almost every spatial point is different from the origin. [`ae_ne_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L20).

**Theorem · Pairing two L² fields is integrable.** The pointwise inner product of two L² vector fields is integrable. [`pair_of_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L24).

**Theorem · Measurability from a radial L² weight.** Radius-weighted L² membership implies almost-everywhere strong measurability of the unweighted field. [`aesm_of_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L30).

**Theorem · Integrability of a weighted dual pairing.** Finite inverse-radius velocity energy and radius-weighted L² control of the other factor make the pairing integrable. [`weighted_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L38).

**Theorem · The negative second trace is in L².** The negative second trace of an admissible second-order field belongs to L². [`negTrace_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L56).

**Theorem · Integrating the eight defect terms.** The specified eight-term integrable combination integrates to the same signed and weighted combination of integrals. [`integral_eight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L72).

**Theorem · Assembling the adjoint representation.** The eight named integration-by-parts and compact-field interfaces imply the exact adjoint-defect representation. [`adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91).

**Theorem · Supplying the adjoint representation.** The exact adjoint-defect representation is proved with all eight named analytic inputs supplied. [`adjointRepresentation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L221).

### Breakdown.FracCell.ReductionAdjointAdjointSpread_of_power

This module bounds the fractional adjoint-spread error by transferring the fractional power to the adjoint field. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · Bounding the adjoint spread error.** For the stated fractional exponent and weighted regularity hypotheses, the power-pairing identity turns the L² adjoint residual bound into the prescribed field-energy error bound. [`adjointSpread_of_power`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointSpread_of_power.lean#L16).

### Breakdown.FracCell.ReductionAdjointCutoffSecondApprox

This module cuts off smooth fields at large radius while making both first- and second-derivative errors arbitrarily small. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · Matrix energy versus operator norm.** The sum of squared matrix entries is at most three times the squared operator norm. [`entrySq_le_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L21).

**Theorem · Tensor energy versus operator norm.** The full second-derivative square is at most nine times the squared tensor operator norm. [`fullSecondSq_le_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L30).

**Theorem · Operator norm versus matrix energy.** The squared matrix operator norm is bounded by the sum of squared entries. [`norm_sq_le_entrySq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L42).

**Theorem · Operator norm versus tensor energy.** The squared tensor operator norm is bounded by the full second-derivative square. [`norm_sq_le_fullSecondSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L50).

**Theorem · Classical derivatives are weak gradients.** A continuously differentiable vector field has its classical derivative as its weak gradient. [`smooth_weak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L67).

**Theorem · Scaling the radial cutoff.** The cutoff of positive radius is the unit-radius cutoff composed with inverse-radius dilation. [`scale_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L85).

**Theorem · Derivative bounds for scaled cutoffs.** Each derivative order of the scaled cutoff is bounded uniformly by a constant times the corresponding inverse-radius power. [`iter_cutoff_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L92).

**Theorem · Cutoff derivatives vanish far away.** Outside twice the positive cutoff radius, every iterated derivative of the cutoff is zero. [`iter_cutoff_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L106).

**Theorem · A reciprocal-radius cutoff bound.** For cutoff radius at least one, a positive-order cutoff derivative obeys the stated reciprocal-distance bound away from the origin. [`cut_term`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L114).

**Theorem · Continuity of matrix energy.** The matrix entry-square sum is continuous. [`entrySq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L133).

**Theorem · Continuity of tensor energy.** The full second-derivative square is continuous. [`fullSecondSq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L137).

**Theorem · Two forms of the second-derivative norm.** The second iterated derivative has the same norm as the iterated Fréchet derivative. [`iter_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L142).

**Theorem · The first derivative after cutoff.** The cutoff gradient is bounded by the original gradient plus the stated inverse-radius velocity term. [`first_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L146).

**Theorem · The second derivative after cutoff.** The cutoff Hessian is bounded by the original Hessian and the stated gradient and inverse-radius velocity terms. [`second_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L162).

**Interface · Compact approximation by radial cutoffs.** This proposition requires a smooth L⁶ field with finite first- and second-derivative energies to admit a compact test within any positive energy tolerance. [`CutoffSecondApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L193).

**Interface providers.** [`Breakdown.CellCert.Reduction.cutoffSecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L203) ([lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean:203](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L203); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.gradientSecondApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82) ([lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean:82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82); named reference in type).

**Theorem · Proving compact cutoff approximation.** Radial cutoffs supply the stated compact approximation in both gradient and second-derivative energies. [`cutoffSecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointCutoffSecondApprox.lean#L203).

### Breakdown.FracCell.ReductionAdjointDefs

This module defines the weighted adjoint regularity and dual decomposition, together with the inverse-square and fractional-power pairing interfaces. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Predicate · The scalar weak-gradient identity.** This proposition defines a scalar weak gradient by integration by parts against smooth compact scalar tests in each coordinate direction. [`IsWeakScalarGradientOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L18).

**Definition · The harmonic weighted dual square.** The dual square sums radial-weighted horizontal and vertical mode energies with denominator shifts one-half and three-halves respectively. [`harmonicWeightSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L22).

**Reader note.** The horizontal and vertical Fourier energies are divided by (|k|+1/2)² and (|k|+3/2)² respectively, and multiplied by the spatial radius squared. These shifted denominators are part of the definition.

**Predicate · Regularity for an adjoint field.** This proposition collects L² and L³ bounds, radial weighted bounds, and weak first- and second-derivative energy conditions for an adjoint field. [`IsAdjointRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L28).

**Predicate · Conditions on an adjoint dual witness.** This record requires the weak derivative, trace, potential, pressure, pin, remainder and finite-mode bounds that justify a proposed adjoint dual decomposition. [`IsAdjointDual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L41).

**Interface · An inverse-square constant.** This proposition requires a nonnegative constant whose square bounds inverse-radius velocity energy by gradient energy for the given symmetry order. [`InverseSquareConstStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L92).

**Interface providers.** [`Breakdown.CellCert.Reduction.inverseSquareConst_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointInverseSquareConst_two.lean#L16) ([lean/Breakdown/FracCell/ReductionAdjointInverseSquareConst_two.lean:16](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointInverseSquareConst_two.lean#L16); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointLocal_of_dual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109) ([lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean:109](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109); named reference in type).

**Interface · The harmonic weighted pairing bound.** This proposition bounds a field pairing by the finite harmonic weighted dual norm times the square root of gradient energy. [`WeightedInverseSquareStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L96).

**Interface providers.** [`Breakdown.CellCert.Reduction.weightedInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L213) ([lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean:213](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L213); named premises: `ModeInverseSquareStatement`, `ModePairingStatement`); [`Breakdown.CellCert.Reduction.weightedInverseSquare_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L278) ([lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean:278](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L278); named premises: `FrameInverseSquareStatement`, `GradientModeSumStatement`, `ModePairingStatement`); [`Breakdown.CellCert.Reduction.weightedInverseSquare_of_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L535) ([lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean:535](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L535); named premises: `FrameInverseSquareStatement`, `ModePairingStatement`); [`Breakdown.CellCert.Reduction.weightedInverseSquare_of_frameBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L833) ([lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean:833](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L833); named premises: `FrameInverseSquareStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointLocal_of_dual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109) ([lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean:109](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109); named reference in type).

**Interface · The exact adjoint-defect decomposition.** This proposition expresses the local adjoint defect as a dual trace pairing, a potential pairing, a flux pairing and a remainder pairing. [`AdjointRepresentationStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L102).

**Interface providers.** [`Breakdown.CellCert.Reduction.adjointRepresentation_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L91); named premises: `CompactTraceWeightStatement`, `CompactWeakGradientStatement`, `ConvectionPairingStatement`, `DriftPairingStatement`, `GradientTracePairingStatement`, `MatrixDivergencePairingStatement`, `NegTracePairingStatement`, `ScalarGradientTracePairingStatement`); [`Breakdown.CellCert.Reduction.adjointRepresentation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L221) ([lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean:221](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointRepresentation.lean#L221); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointLocal_of_dual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109) ([lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean:109](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointLocal_of_dual.lean#L109); named reference in type).

**Interface · Transferring the fractional power.** This proposition transfers the fractional power from a second-order field to a regular adjoint field and asserts the resulting low-power field is in L². [`PowerPairingStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L113).

**Interface providers.** [`Breakdown.CellCert.Reduction.powerPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L776) ([lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean:776](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L776); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointSpread_of_power`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointSpread_of_power.lean#L16) ([lean/Breakdown/FracCell/ReductionAdjointAdjointSpread_of_power.lean:16](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointSpread_of_power.lean#L16); named reference in type).

**Interface · The proposed two-thirds class constant.** This proposition asks for inverse-square constant two-thirds for every symmetry order at least two. [`ClassInverseSquareStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointDefs.lean#L120).

**Reader note.** No theorem with this exact interface as its named result and no theorem referring to its name were found in the library. Its universal requirement with constant 2/3 is distinct from inverseSquareConst_two, which supplies InverseSquareConstStatement with constant 2.

**Interface providers.** No theorem with this exact named interface as its result was found in the library.

**Theorems using this interface name.** None found in the library.

### Breakdown.FracCell.ReductionAdjointFrameInverseSquare

This module assembles smooth harmonic bounds and approximation limits into the frame inverse-square estimate. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · The frame inverse-square bound.** The smooth-mode bound, mirror approximation, weighted lower limit and gradient upper limit imply the frame inverse-square statement. [`frameInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17).

**Theorem · Supplying the frame inverse-square bound.** The frame inverse-square statement is proved with its four named analytic inputs supplied. [`frameInverseSquare`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L30).

### Breakdown.FracCell.ReductionAdjointFrameInverseSquareHalfPlane

This module proves the half-plane inverse-square estimate by separating a radial Hardy inequality from angular inequalities with different parity constants. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Definition · The meridional plane as a linear map.** The linear map sends radius and height to the spatial meridional plane at the specified angle. [`ringLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L16).

**Theorem · The meridional linear-map formula.** Applying the meridional linear map gives the cylindrical ring point. [`ringLin_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L21).

**Theorem · Continuous meridional planes.** The meridional linear map depends continuously on angle. [`ringLin_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L25).

**Theorem · Recovering a nonnegative ring radius.** For a nonnegative input radius, the ring radius of the constructed point is that input. [`ringRadius_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L42).

**Theorem · The squared norm of a ring point.** The ring point's squared norm is radius squared plus height squared. [`norm_pt_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L47).

**Theorem · The radial frame direction.** At positive radius, the meridional image of the radial unit input is the ring's radial frame vector. [`frame0_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L55).

**Theorem · The angular frame direction.** At positive radius, the angular frame vector has the sine-cosine coordinate formula. [`frame1_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L62).

**Theorem · The axial frame direction.** The meridional image of the height unit input is the axial frame vector. [`frame2_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L69).

**Theorem · Differentiating a ring in angle.** The derivative of a positive-radius ring point in angle is radius times the angular frame vector. [`pt_hasDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L74).

**Theorem · Matching Fourier phases at both ends.** An integer Fourier phase agrees at the angles pi and negative pi. [`exp_pi_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L94).

**Theorem · Regularity and derivatives of a mode.** A compact C¹ scalar field has compact C¹ angular modes with the stated radial, height and angular derivative formulas at positive radius. [`modeData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L102).

**Definition · A coordinate projection as a linear map.** This continuous linear map extracts the chosen spatial coordinate. [`coord`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L263).

**Theorem · Applying the coordinate projection.** The coordinate projection returns the selected coordinate of its input vector. [`coord_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L269).

**Theorem · The horizontal complex derivative.** The derivative of the horizontal complex encoding combines the first two derivative coordinates with the imaginary unit. [`hpart_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L271).

**Theorem · The vertical complex derivative.** The derivative of the vertical complex encoding is the third coordinate of the derivative viewed as complex. [`vpart_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L283).

**Theorem · The angular-derivative energy factor.** At positive radius, the squared angular derivative multiplier contributes the integer mode squared divided by radius squared. [`norm_mode_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L291).

**Theorem · The inverse-radius integral diverges.** A positive multiple of the reciprocal variable has infinite nonnegative integral on every interval starting at zero. [`inv_lintegral_top`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L297).

**Theorem · A nonzero axis value forces divergence.** A continuous nonzero angular mode with a nonzero axis value has infinite stated half-plane gradient energy. [`axis_top`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L316).

**Interface · The axis-compatible half-plane bound.** This proposition bounds the half-plane inverse-square energy of a compact C¹ mode whose axis values vanish for nonzero frequency, using shift |k|+1/2 generally and |k|+3/2 under odd height parity. [`AxisHalfPlaneBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L371).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.axisHalfPlaneBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:448](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448); named premises: `AngularCosBoundStatement`, `RadialInverseSquareStatement`).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.halfPlaneBound_of_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L378) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:378](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L378); named reference in type).

**Theorem · Removing the explicit axis condition.** The axis-compatible half-plane statement implies the general half-plane statement by treating a nonvanishing axis value through divergent energy. [`halfPlaneBound_of_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L378).

**Interface · The radial Hardy inequality.** This proposition bounds a compact C¹ function's positive-ray square integral by four times its radius-squared derivative integral. [`RadialInverseSquareStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L387).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.radialInverseSquare`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L670) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:670](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L670); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.axisHalfPlaneBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:448](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448); named reference in type).

**Theorem · Compact support along a planar ray.** Restricting a compactly supported planar function to a fixed radial ray gives a compactly supported function of signed radius. [`ray_support`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L393).

**Interface · The weighted angular spectral bound.** This proposition gives either angular spectral constant with cosine weight, requiring endpoint vanishing for positive mode and central vanishing for the larger constant. [`AngularCosBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L414).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.angularCosBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L855) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:855](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L855); named premises: `AngularOddBoundStatement`).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.axisHalfPlaneBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:448](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448); named reference in type).

**Theorem · Rotations preserve paired complex energy.** A real sine-cosine rotation of two complex numbers preserves the sum of their squared norms. [`rot_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L421).

**Theorem · A planar linear map from two columns.** A linear map on the real plane is determined by its values on the two coordinate directions. [`clm_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L429).

**Theorem · The positive-cosine angular interval.** Within the centered full-turn interval, cosine is positive exactly between negative and positive pi over two. [`cos_pos_iff_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L433).

**Theorem · Combining radial and angular estimates.** The radial Hardy statement and cosine-weighted angular statement imply the axis-compatible half-plane estimate. [`axisHalfPlaneBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L448).

**Theorem · Proving the radial Hardy inequality.** The stated radial inverse-square inequality with constant four is proved. [`radialInverseSquare`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L670).

**Interface · The larger angular spectral constant.** This proposition gives the larger angular constant for C¹ functions vanishing at the center and satisfying the required endpoint conditions. [`AngularOddBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L754).

**Reader note.** The proposition assumes the stated vanishing at the centre. Its name does not by itself assert oddness of the function on the whole interval.

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.angularOdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L901) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:901](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L901); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.angularCosBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L855) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:855](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L855); named reference in type).

**Theorem · The base angular square inequality.** The displayed completed-square inequality bounds the angular cross term when cosine is positive and sine and cosine have unit square sum. [`angular_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L761).

**Theorem · The base angular spectral bound.** A C¹ angular function with the required endpoint vanishing satisfies the cosine-weighted bound with constant m(m+1). [`angularEven`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L778).

**Theorem · Adding the central-vanishing bound.** The larger angular bound supplies the second branch of the full cosine-weighted angular statement. [`angularCosBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L855).

**Theorem · The central-vanishing square inequality.** The displayed pointwise inequality controls the stronger angular expression where cosine is positive and sine is nonzero. [`odd_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L863).

**Theorem · Signed and nonnegative integrals.** The nonnegative part of a continuous interval integral is bounded by the nonnegative integral of the pointwise nonnegative parts. [`ofReal_int_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L883).

**Theorem · Proving the larger angular bound.** The central-vanishing angular statement with constant (m+1)(m+2) is proved. [`angularOdd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L901).

**Theorem · Supplying frame-mode calculus.** The frame-mode differentiation and regularity statement is supplied for the half-plane argument. [`frameModeCalculus'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1101).

**Theorem · Supplying the half-plane bound.** The full half-plane inverse-square statement is proved with the radial and angular inputs supplied. [`halfPlaneBound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1129).

### Breakdown.FracCell.ReductionAdjointFrameInverseSquareLimit

This module proves continuity of each angular gradient energy under convergence in the full matrix-entry L² energy. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · Continuous matrix entry squares.** The sum of squared matrix entries is continuous in the operator. [`entrySq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L22).

**Theorem · Nonnegative matrix entry energy.** Every matrix entry-square sum is nonnegative. [`entrySq_nn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L27).

**Theorem · Nonnegative frame-mode energy.** The sum of squared frame-mode components is nonnegative. [`frameModeSq_nn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L31).

**Theorem · Measurable angular gradient density.** A measurable gradient field gives a measurable radial-weighted frame-mode density almost everywhere on the positive half-plane. [`side_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L35).

**Theorem · A mode is bounded by full energy.** Each mode's gradient energy is bounded by the full spatial matrix-entry energy. [`coefEnergy_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L53).

**Theorem · A frame component obeys total energy.** Away from the axis, each horizontal or vertical component of a matrix applied to a ring-frame vector is bounded in square by the matrix energy. [`term_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L145).

**Predicate · Square integrability on a ring.** This proposition requires every frame column's horizontal and vertical ring functions to belong to angular L². [`SliceL2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L155).

**Theorem · Almost every ring has finite energy.** A measurable matrix field with finite total entry energy has the required angular L² slices almost everywhere. [`slices`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L162).

**Theorem · A weighted complex-square split.** For a positive tolerance, the square of a complex sum is bounded by the two squares with complementary tolerance weights. [`sq_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L199).

**Theorem · Splitting horizontal derivative modes.** With the stated angular L² hypotheses, a horizontal mode splits into the comparison field's mode and the difference mode. [`mode_add_h`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L210).

**Theorem · Splitting vertical derivative modes.** With the stated angular L² hypotheses, a vertical mode splits into the comparison field's mode and the difference mode. [`mode_add_v`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L221).

**Theorem · Two-sided comparison of mode energies.** On an L² ring, either frame-mode energy is bounded by (1+ε) times the other plus (1+ε⁻¹) times the difference-mode energy, for every ε>0. [`point_both`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L232).

**Theorem · Two-sided integrated mode comparison.** Finite measurable gradient energies give both tolerance-weighted comparisons between their integrated angular mode energies. [`side_both`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L259).

**Theorem · A vanishing multiplicative tolerance.** Multiplying a finite nonnegative extended-real number by one plus a reciprocal index converges to that number. [`coeff_tend`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L299).

**Theorem · Adding a vanishing energy error.** Adding a fixed nonnegative multiple of an error tending to zero converges to the unchanged extended-real base value. [`tail_tend`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L308).

**Theorem · Convergence of gradient-mode energies.** The mode-gradient limit statement is proved from the two-sided energy comparison and the vanishing full-gradient error. [`modeGradientLimit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L317).

### Breakdown.FracCell.ReductionAdjointFrameInverseSquareLower

This module proves lower semicontinuity of the inverse-square angular energy by truncating away from the axis and infinity. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Definition · The inverse-square mode density.** This nonnegative density weights horizontal and vertical angular energies by their shifted mode squares and inverse spatial radius squared. [`wF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L21).

**Definition · The unweighted mode-error density.** This nonnegative density is the radial Jacobian times the sum of horizontal and vertical angular coefficient energies. [`bF`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L26).

**Definition · A bounded region away from the axis.** The truncation region keeps radius above a reciprocal index and spatial radius below the index plus one. [`tset`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L30).

**Theorem · Integrating the weighted mode density.** The inverse-square mode energy is the integral of the defined density over the positive radius-height half-plane. [`side_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L33).

**Theorem · Measurability of the truncated region.** Each bounded region separated from the axis is measurable. [`tset_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L35).

**Theorem · Measurable inverse-square mode density.** A measurable vector field gives an almost-everywhere measurable weighted angular density. [`wF_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L39).

**Theorem · Measurable unweighted mode density.** A measurable vector field gives an almost-everywhere measurable unweighted angular coefficient density. [`bF_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L47).

**Theorem · A truncated ring lies in a ball.** Every angle of a ring indexed by the truncation region lies in the corresponding spatial ball. [`ring_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L55).

**Theorem · Local coefficient energy is bounded.** The angular coefficient energy over the truncation region is bounded by the field's square energy in the corresponding ball. [`vcircleCoefBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L62).

**Theorem · Splitting a weighted error expression.** The stated nonnegative weight bounds turn two componentwise error inequalities into the combined weighted error inequality. [`real_split`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L113).

**Theorem · Continuous horizontal complex fields.** The horizontal complex encoding of a continuous vector field is continuous. [`hor_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L131).

**Theorem · Continuous vertical complex fields.** The vertical complex encoding of a continuous vector field is continuous. [`ver_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L137).

**Theorem · Continuity around a ring.** At fixed radius and height, the cylindrical ring point depends continuously on angle. [`ring_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L141).

**Theorem · Continuous angular functions are in L².** A continuous complex function belongs to L² on the bounded angular interval. [`cont_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L144).

**Theorem · Horizontal energy obeys vector energy.** The squared norm of the horizontal complex encoding is at most the squared full-vector norm. [`hor_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L149).

**Theorem · Vertical energy obeys vector energy.** The squared vertical component is at most the squared full-vector norm. [`ver_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L153).

**Theorem · Local L² fields have finite ring slices.** Finite spatial square energy in a ball gives horizontal and vertical L² ring functions almost everywhere in its truncation region. [`diff_slices`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L157).

**Theorem · Comparing truncated weighted densities.** On the truncated region, a field's weighted mode density is bounded by a comparison density plus an explicit multiple of the difference-mode density. [`point_low`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L191).

**Theorem · Bounding truncated inverse-square energy.** The truncated weighted mode energy is bounded by the comparison energy and an explicit local L² error term. [`trunc_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L250).

**Theorem · A lower limit on each truncated region.** Local L² convergence of continuous approximants bounds each truncated weighted energy by the lower limit of their full weighted energies. [`trunc_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L280).

**Theorem · Lower semicontinuity of mode energy.** The full weighted mode energy is lower semicontinuous under local L² convergence of continuous approximants. [`modeWeightedLower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L312).

### Breakdown.FracCell.ReductionAdjointFrameInverseSquareParts

This module states the smooth estimate and approximation steps for the harmonic inverse-square bound and supplies frame calculus and mirror symmetrization. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Definition · The weighted inverse-square mode energy.** This energy integrates the shifted horizontal and vertical mode squares with the cylindrical Jacobian and inverse-square spatial weight. [`modeWeightedSide`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L17).

**Definition · The gradient energy of one mode.** This energy integrates the frame-mode gradient square with the cylindrical radial Jacobian. [`modeGradientSide`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L23).

**Interface · The smooth mirror-symmetric mode bound.** This proposition requires each inverse-square mode energy of a smooth compact mirror-symmetric field to be bounded by its gradient-mode energy. [`SmoothModeBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L26).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareParts.smoothModeBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85); named premises: `FrameModeCalculusStatement`, `HalfPlaneBoundStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.frameInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean:17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17); named reference in type).

**Interface · Approximation preserving mirror symmetry.** This proposition requires compact smooth mirror-symmetric approximants converging in gradient energy and local velocity L² energy. [`MirrorApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L30).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareParts.mirrorApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530); named premises: `GradientMirrorStatement`, `TestGradientApproxStatement`); [`Breakdown.FracInternal.FrameInverseSquareParts.mirrorApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L616) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:616](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L616); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.frameInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean:17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17); named reference in type).

**Interface · Lower limits of weighted mode energy.** This proposition requires lower semicontinuity of weighted mode energy under local L² convergence of continuous fields. [`ModeWeightedLowerStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L38).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareParts.modeWeightedLower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L312) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean:312](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLower.lean#L312); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.frameInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean:17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17); named reference in type).

**Interface · Limits of gradient-mode energy.** This proposition requires convergence of each mode's gradient energy under full matrix-entry L² convergence. [`ModeGradientLimitStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L43).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareParts.modeGradientLimit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L317) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean:317](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareLimit.lean#L317); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.frameInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean:17](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquare.lean#L17); named reference in type).

**Interface · Differentiation of angular frame modes.** This proposition records compact C¹ angular modes and the exact decomposition of frame-mode gradient energy into radial, height and angular parts. [`FrameModeCalculusStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L51).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareParts.frameModeCalculus'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1101) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:1101](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1101); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.FracInternal.FrameInverseSquareParts.frameModeCalculus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L418) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:418](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L418); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareParts.smoothModeBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85); named reference in type).

**Interface · The half-plane inverse-square estimate.** This proposition gives the half-plane weighted inequality with a half-integer shift, using the larger shift for odd height dependence. [`HalfPlaneBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L66).

**Interface providers.** [`Breakdown.FracInternal.FrameInverseSquareHalfPlane.halfPlaneBound_of_axis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L378) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:378](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L378); named premises: `AxisHalfPlaneBoundStatement`); [`Breakdown.FracInternal.FrameInverseSquareParts.halfPlaneBound'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1129) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean:1129](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareHalfPlane.lean#L1129); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareParts.smoothModeBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:85](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85); named reference in type).

**Theorem · The vertical mode is odd in height.** Mirror symmetry of a vector field makes its vertical angular mode odd in height. [`verticalMode_odd`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L73).

**Theorem · The smooth bound from mode calculus.** Frame-mode calculus and the half-plane estimate imply the smooth mirror-symmetric mode bound. [`smoothModeBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L85).

**Definition · The first radial coordinate map.** This linear map places the planar radial input in the first spatial coordinate. [`axisA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L151).

**Definition · The second radial coordinate map.** This linear map places the planar radial input in the second spatial coordinate. [`axisB`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L154).

**Definition · The axial coordinate map.** This linear map places the planar height input in the third spatial coordinate. [`axisC`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L157).

**Definition · The meridional ring map.** The ring map combines two trigonometric radial coordinate maps with the axial coordinate map. [`ringLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L160).

**Theorem · The ring map gives cylindrical points.** Applying the meridional map yields the cylindrical ring point. [`ringLin_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L162).

**Theorem · Continuous dependence on ring angle.** The meridional ring map depends continuously on angle. [`ringLin_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L166).

**Theorem · A uniform meridional operator bound.** The ring-map operator norm is bounded by the sum of the norms of the three fixed coordinate maps. [`ringLin_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L170).

**Theorem · The meridional Euclidean norm formula.** The squared norm of the mapped point equals the sum of its squared radial and height inputs. [`ringLin_norm_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L178).

**Theorem · The ring map controls the product norm.** The norm of the planar input is bounded by the norm of its spatial meridional image. [`norm_le_ringLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L184).

**Definition · The complex angular Fourier phase.** The phase is the complex exponential of negative imaginary integer mode times angle. [`wave`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L190).

**Theorem · A continuous Fourier phase.** The angular Fourier phase is continuous in angle. [`wave_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L192).

**Theorem · The Fourier phase has unit norm.** The angular Fourier phase has complex norm one. [`wave_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L196).

**Definition · The unnormalized angular mode integral.** This integral pairs a field around the meridional ring with its Fourier phase over the centered full period. [`modeInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L201).

**Theorem · Normalizing the angular mode integral.** The angular mode is the unnormalized mode integral divided by twice pi. [`angularMode_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L204).

**Definition · The candidate derivative of a mode.** This operator integrates the phased spatial derivative composed with the meridional ring map. [`modeDer`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L208).

**Theorem · Continuity of the mode derivative.** For a C¹ field, the candidate derivative of its angular mode is continuous. [`modeDer_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L211).

**Theorem · Differentiating the mode integral.** For a compact C¹ field, the angular integral has the stated integrated derivative. [`modeInt_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L220).

**Theorem · The normalized mode as a planar function.** The radius-height angular-mode function equals the normalized meridional mode integral. [`mode_eq_fun`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L244).

**Theorem · Differentiating a normalized mode.** The derivative of a compact C¹ field's angular mode is its candidate derivative divided by twice pi. [`mode_hasFDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L248).

**Theorem · The angular mode is C¹.** Angular modes of a compact C¹ field are continuously differentiable in radius and height. [`mode_contDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L254).

**Theorem · Compact support of angular modes.** A compactly supported spatial field has compactly supported radius-height angular modes. [`mode_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L264).

**Theorem · The pointwise normalized mode formula.** At the selected radius and height, the angular mode equals the normalized meridional integral. [`angularMode_eq'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L282).

**Theorem · Differentiating a linear observation.** Applying a continuous linear scalar observation to a smooth vector field commutes with differentiation. [`fderiv_clm_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L286).

**Theorem · Recovering positive cylindrical radius.** The ring radius of a point constructed with positive radius equals that radius. [`ringRadius_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L290).

**Theorem · The meridional radial column.** At positive radius, the radial ring-frame vector is the meridional map applied to the radial unit input. [`frame0_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L295).

**Theorem · The meridional height column.** The axial ring-frame vector is the meridional map applied to the height unit input. [`frame2_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L301).

**Theorem · The angular derivative of a ring map.** Radius times the angular frame vector equals the angular derivative combination of the two radial coordinate maps. [`frame1_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L307).

**Theorem · Radial and height mode derivatives.** A mode's derivative in a meridional direction equals the mode of the spatial derivative in the matching frame direction. [`radial_height_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L313).

**Theorem · The derivative of the Fourier phase.** Differentiating the angular phase multiplies it by negative imaginary integer mode. [`wave_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L331).

**Theorem · The Fourier phase matches at endpoints.** The Fourier phase has equal values at pi and negative pi. [`wave_period`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L338).

**Theorem · The ring map matches at endpoints.** The meridional ring map has equal values at pi and negative pi. [`ringLin_period`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L345).

**Theorem · The angular multiplier of a mode.** At positive radius, the angular-frame derivative mode equals the original mode times imaginary integer mode divided by radius. [`turn_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L348).

**Definition · The horizontal complex observation.** This linear map combines the first coordinate with the imaginary unit times the second coordinate. [`horizLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L399).

**Definition · The vertical complex observation.** This linear map views the third coordinate as a complex number. [`vertLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L403).

**Theorem · The horizontal part as a linear image.** The horizontal complex part of a field is its composition with the horizontal observation map. [`horiz_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L405).

**Theorem · The vertical part as a linear image.** The vertical complex part of a field is its composition with the vertical observation map. [`vert_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L409).

**Theorem · The squared angular multiplier.** The angular derivative multiplier contributes the integer mode squared divided by positive radius squared to norm energy. [`turn_norm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L413).

**Theorem · Proving angular frame calculus.** The regularity and derivative-energy identities for angular frame modes are proved. [`frameModeCalculus`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L418).

**Theorem · The mirror is its own inverse.** Applying the mirror map twice gives the original vector. [`mirror_mirror'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L436).

**Theorem · Reflection preserves the norm.** The mirror map preserves the Euclidean norm. [`norm_mirror'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L440).

**Definition · Reflection as a real linear map.** This real linear map implements the spatial mirror reflection. [`mirrorLin'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L445).

**Definition · Reflection as a linear isometry.** The mirror map is bundled as an invertible norm-preserving real linear map. [`mirrorEquiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L454).

**Definition · The continuous linear reflection.** The mirror isometry is viewed as a continuous linear operator. [`mirrorCL`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L457).

**Theorem · Applying the linear reflection.** The continuous linear reflection agrees pointwise with the mirror function. [`mirrorCL_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L459).

**Theorem · Applying the reflection isometry.** The reflection isometry agrees pointwise with the mirror function. [`mirrorEquiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L461).

**Definition · Conjugating an operator by reflection.** The reflected operator applies the mirror before and after the original operator. [`conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L463).

**Theorem · The reflected operator formula.** The conjugated operator sends a vector to the mirror of the original operator applied to the mirrored vector. [`conj_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L465).

**Theorem · Reflection respects operator differences.** Conjugation by reflection preserves subtraction of operators. [`conj_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L467).

**Theorem · Reflection preserves matrix energy.** Conjugating an operator by reflection preserves its entry-square sum. [`entrySq_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L470).

**Theorem · Bounding an averaged vector.** The squared norm of the arithmetic mean of two vectors is bounded by the sum of their squared norms. [`half_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L482).

**Theorem · Bounding an averaged matrix.** The entry energy of the arithmetic mean of two matrices is bounded by the sum of their entry energies. [`entrySq_half_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L489).

**Theorem · Nonnegative matrix energy.** The matrix entry-square sum is nonnegative. [`entrySq_nonneg_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L495).

**Theorem · Continuous matrix energy.** The matrix entry-square sum is continuous. [`entrySq_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L498).

**Theorem · Reflection respects averaging.** The mirror of a vector average is the average of the mirrored vectors. [`mirror_half`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L502).

**Theorem · Reflection respects subtraction.** The mirror of a vector difference is the difference of the mirrored vectors. [`mirror_sub'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L507).

**Theorem · Nonnegative integrals under reflection.** Composing any nonnegative spatial integrand with reflection preserves its integral. [`lintegral_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L511).

**Theorem · Reflection preserves ball integrals.** Reflection preserves the nonnegative integral over every origin-centered ball. [`ball_lintegral_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L514).

**Theorem · Symmetrizing compact approximants.** Compact gradient approximation and the weak-gradient mirror identity imply mirror-symmetric compact approximation. [`mirrorApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530).

**Theorem · Supplying symmetric approximation.** The mirror-symmetric approximation statement is proved with its two named inputs supplied. [`mirrorApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L616).

### Breakdown.FracCell.ReductionAdjointFrameMirrorLeaves

This module supplies smooth approximation, cutoff convergence and the weak-gradient mirror identity used by symmetric approximation. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Interface · Compact approximation in gradient energy.** This proposition requires smooth compact approximants converging in global gradient energy and local velocity L² energy. [`TestGradientApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L19).

**Interface providers.** [`Breakdown.FracInternal.FrameMirrorLeaves.testGradientApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61); named premises: `CutoffGradientStatement`, `SmoothL2ApproxStatement`); [`Breakdown.FracInternal.FrameMirrorLeaves.testGradientApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L735) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:735](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L735); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareParts.mirrorApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530); named reference in type).

**Interface · Reflection of the weak gradient.** This proposition requires the weak gradient to intertwine reflection on its spatial point and its directional argument almost everywhere. [`GradientMirrorStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L26).

**Interface providers.** [`Breakdown.FracInternal.FrameMirrorLeaves.gradientMirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L787) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:787](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L787); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameInverseSquareParts.mirrorApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530) ([lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean:530](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameInverseSquareParts.lean#L530); named reference in type).

**Interface · Smooth L⁶ approximation with gradients.** This proposition requires smooth L⁶ approximants with finite gradient energy and convergence in global gradient and local velocity energy. [`SmoothL2ApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L31).

**Interface providers.** [`Breakdown.FracInternal.FrameMirrorLeaves.smoothL2Approx_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L241) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L241); named premises: `MollifierL2Statement`); [`Breakdown.FracInternal.FrameMirrorLeaves.smoothL2Approx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L510) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:510](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L510); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameMirrorLeaves.testGradientApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61); named reference in type).

**Interface · Convergence of cutoff gradients.** This proposition requires the gradient of large radial cutoffs of a smooth finite-energy L⁶ field to converge in matrix-entry energy. [`CutoffGradientStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L39).

**Interface providers.** [`Breakdown.FracInternal.FrameMirrorLeaves.cutoffGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L683) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:683](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L683); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameMirrorLeaves.testGradientApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61); named reference in type).

**Theorem · Nonnegative entry-square energy.** Every matrix entry-square sum is nonnegative. [`entrySq_nonneg_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L44).

**Theorem · Bounding the energy of a matrix sum.** The entry energy of a matrix sum is at most twice the sum of its two entry energies. [`entrySq_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L47).

**Theorem · Continuity of entry-square energy.** The matrix entry-square sum is continuous. [`entrySq_cont'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L57).

**Theorem · Combining smoothing and radial cutoffs.** Smooth L² approximation and cutoff-gradient convergence imply compact gradient approximation. [`testGradientApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L61).

**Theorem · Convex powers after mollification.** The norm power of a normalized mollification is bounded by the mollification of the norm power when that power is integrable. [`conv_pow_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L120).

**Theorem · The derivative of a mollified weak field.** Each coordinate derivative of a mollified L⁶ field is the mollification of its weak-gradient column. [`conv_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L176).

**Interface · L² convergence of shrinking mollifiers.** This proposition requires normalized mollifiers with shrinking outer radii to converge to each L² field in squared L² distance. [`MollifierL2Statement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L208).

**Interface providers.** [`Breakdown.FracInternal.FrameMirrorLeaves.mollifierL2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L422) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:422](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L422); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.FracInternal.FrameMirrorLeaves.smoothL2Approx_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L241) ([lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean:241](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L241); named reference in type).

**Definition · A sequence of shrinking smooth bumps.** The bump at index n has outer radius one divided by n plus one and inner radius half as large. [`bump`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L214).

**Theorem · Mollification uses a nearby ball.** Inside a ball, mollification by the chosen bump depends only on the field inside the ball enlarged by one. [`conv_local`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L220).

**Theorem · Smooth approximation from mollifiers.** The L² mollifier convergence statement implies smooth approximation of admissible fields and their weak gradients. [`smoothL2Approx_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L241).

**Theorem · Mollification decreases square energy.** Normalized mollification does not increase the nonnegative square integral of a square-integrable vector field. [`conv_l2_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L325).

**Theorem · Mollifying a compact continuous field.** Shrinking normalized mollifiers converge in squared L² distance to a continuous compactly supported field. [`conv_compact_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L345).

**Theorem · Proving L² mollifier convergence.** The L² mollifier convergence statement is proved for shrinking normalized bumps. [`mollifierL2`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L422).

**Theorem · Supplying smooth L² approximation.** Smooth approximation of admissible fields is proved with the mollifier convergence input supplied. [`smoothL2Approx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L510).

**Theorem · The cutoff gradient stays in its annulus.** A nonzero cutoff gradient occurs only between the positive cutoff radius and twice that radius. [`fderiv_cutoff_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L514).

**Theorem · An L⁶-to-square scalar bound.** For positive parameter, the square of a scalar is bounded by its sixth power divided by the parameter squared plus the parameter. [`sq_le_six`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L536).

**Theorem · Integrable continuous-field cutoff error.** The squared cutoff gradient times the squared norm of a continuous field is integrable for every positive cutoff radius. [`cutoff_term_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L550).

**Theorem · The cutoff error tends to zero.** For a continuous L⁶ field, its squared cutoff-gradient error integral tends to zero at large radius. [`cutoff_tail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L557).

**Theorem · A pointwise cutoff-gradient error bound.** The gradient difference after cutoff is bounded by twice the removed gradient energy plus six times the cutoff-derivative error. [`cutoff_pointwise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L651).

**Theorem · Proving cutoff-gradient convergence.** The cutoff-gradient convergence statement follows from the tail estimate and pointwise energy bound. [`cutoffGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L683).

**Theorem · Supplying compact gradient approximation.** The compact gradient approximation statement is proved by combining smooth approximation with radial cutoffs. [`testGradientApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L735).

**Theorem · Applying reflection twice.** The mirror map applied twice returns its input. [`mm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L739).

**Theorem · The norm is invariant under reflection.** The Euclidean norm of a mirrored vector equals its original norm. [`nm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L743).

**Definition · The linear mirror map.** This real linear map implements the mirror function. [`mLin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L748).

**Definition · The mirror isometry equivalence.** This invertible linear isometry bundles the norm-preserving mirror map. [`mIso`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L757).

**Definition · The mirror as a continuous operator.** The mirror isometry is viewed as a continuous linear operator. [`mCL`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L760).

**Theorem · The isometry acts by reflection.** The mirror isometry evaluates to the mirror function. [`mIso_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L762).

**Theorem · The continuous reflection operator.** The continuous mirror operator evaluates to the mirror function. [`mCL_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L764).

**Definition · The coordinate reflection sign.** The sign is negative on the axial coordinate and positive on the other two coordinates. [`sgn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L766).

**Theorem · Reflection of a coordinate unit vector.** Reflection multiplies each coordinate unit vector by its assigned sign. [`mirror_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L768).

**Theorem · Squared coordinate reflection signs.** Every coordinate reflection sign has square one. [`sgn_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L771).

**Theorem · Reflection of a scalar multiple.** The mirror map commutes with multiplication by a real scalar. [`mirror_smul'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L774).

**Theorem · The standard-coordinate vector expansion.** A vector is the sum of its three coordinate multiples of unit vectors. [`vec_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L776).

**Theorem · Changing variables by reflection.** Composition with the mirror isometry preserves the vector-valued integral. [`integral_mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L780).

**Theorem · Reflection commutes with integration.** Applying reflection to an integrand and then integrating equals reflecting its integral. [`integral_mIso`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L784).

**Theorem · Proving weak-gradient reflection.** The weak-gradient reflection statement is proved for admissible second-order fields. [`gradientMirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointFrameMirrorLeaves.lean#L787).

### Breakdown.FracCell.ReductionAdjointGradientSecondApprox

This module combines mollification and cutoff approximation to approximate both weak derivatives through order two. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Interface · Approximation of gradients and Hessians.** This proposition requires compact smooth tests converging to the weak gradient and Hessian in their respective square energies. [`GradientSecondApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L18).

**Interface providers.** [`Breakdown.CellCert.Reduction.gradientSecondApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82) ([lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean:82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82); named premises: `CutoffSecondApproxStatement`, `MollifySecondApproxStatement`); [`Breakdown.CellCert.Reduction.gradientSecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L122) ([lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean:122](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L122); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.secondOrderTestApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L657) ([lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean:657](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointAdjointExtension.lean#L657); named reference in type).

**Theorem · The square norm of a vector sum.** The squared norm of a vector sum is at most twice the sum of the two squared norms. [`sq_norm_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L29).

**Theorem · The entry energy of a matrix sum.** The entry energy of a sum is at most twice the sum of the two entry energies. [`entrySq_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L34).

**Theorem · The tensor energy of a sum.** The full second-derivative energy of a sum is at most twice the sum of the two tensor energies. [`fullSecondSq_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L41).

**Theorem · Nonnegative first-derivative energy.** The matrix entry-square sum is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L51).

**Theorem · Nonnegative second-derivative energy.** The full second-derivative square is nonnegative. [`fullSecondSq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L54).

**Theorem · Continuous first-derivative energy.** The matrix entry-square sum is continuous. [`entrySq_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L57).

**Theorem · Continuous second-derivative energy.** The full second-derivative square is continuous. [`fullSecondSq_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L61).

**Theorem · Combining two approximation errors.** A nonnegative measurable error bounded by twice each of two integrable errors has integral at most four times their common bound. [`split_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L66).

**Theorem · Mollification followed by cutoff.** Mollifier approximation and cutoff approximation together imply compact approximation of gradients and Hessians. [`gradientSecondApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82).

**Theorem · Approximation through order two.** The compact gradient-and-Hessian approximation statement is proved with its two inputs supplied. [`gradientSecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L122).

### Breakdown.FracCell.ReductionAdjointInverseSquareConst_two

This module supplies the universal inverse-square constant used by the dual adjoint estimate. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · The inverse-square norm constant is two.** Every symmetry order admits inverse-square norm constant two, so the corresponding squared-energy coefficient is four. [`inverseSquareConst_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointInverseSquareConst_two.lean#L16).

**Reader note.** The parameter is the norm constant H=2 in InverseSquareConstStatement; the squared-energy inequality therefore contains H²=4.

### Breakdown.FracCell.ReductionAdjointMollifySecondApprox

This module smooths admissible fields while controlling the square errors in their first and second weak derivatives. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Definition · The shrinking mollifier bump.** The bump at index n has outer radius one divided by n plus one and half that inner radius. [`kernelBump`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L19).

**Theorem · The mollifier radius tends to zero.** The outer radii of the chosen bumps converge to zero. [`kernelBump_rOut`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L25).

**Theorem · The mollifier radius is at most one.** Every chosen bump has outer radius at most one. [`kernelBump_rOut_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L28).

**Theorem · A norm-power bound for convolution.** Normalized mollification bounds the norm power by the convolution of the norm power when the exponent is at least one and the latter is integrable. [`normPow_conv_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L33).

**Theorem · Square-energy contraction by smoothing.** Mollifying a locally integrable square-integrable field gives an integrable square norm with no larger square integral. [`conv_sq_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L87).

**Theorem · Square convergence of mollification.** The chosen shrinking mollifiers converge to every measurable square-integrable field in squared L² distance. [`conv_sq_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L109).

**Theorem · Mollifying a locally integrable gradient.** For a locally integrable field with a weak gradient, each derivative column of its mollification is the mollified weak-gradient column. [`mollify_fderiv_apply'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L250).

**Theorem · Integrable mollification error.** The squared difference between a measurable square-integrable field and its normalized mollification is integrable. [`diff_sq_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L281).

**Interface · Smooth approximation through order two.** This proposition requires a smooth L⁶ approximant with finite derivative energies and arbitrarily small first- and second-derivative square errors. [`MollifySecondApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L295).

**Interface providers.** [`Breakdown.CellCert.Reduction.mollifySecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L306) ([lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean:306](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L306); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.gradientSecondApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82) ([lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean:82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointGradientSecondApprox.lean#L82); named reference in type).

**Theorem · Second-order mollifier approximation.** The shrinking mollifiers supply the stated smooth approximation through second derivative order. [`mollifySecondApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointMollifySecondApprox.lean#L306).

### Breakdown.FracCell.ReductionAdjointPowerPairing

This module identifies the singular-integral low fractional power with its Fourier multiplier and transfers that power across an L² pairing. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Definition · The symmetric second difference.** The symmetric second difference is the original value minus the average of the two opposite translated values. [`secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L23).

**Definition · The second-difference Fourier weight.** The Fourier weight is one minus the cosine of twice pi times the frequency-displacement inner product. [`cosWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L26).

**Definition · The low-power singular kernel.** The kernel is the norm of the displacement raised to negative three minus twice the fractional exponent. [`kern`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L28).

**Theorem · The low power as a kernel integral.** The low fractional power is the normalized integral of the singular kernel times the symmetric second difference. [`lowPowerAt_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L30).

**Theorem · The Fourier symbol of the negative trace.** For a regular adjoint field, the negative Hessian trace has Fourier symbol equal almost everywhere to the squared-frequency multiplier times the field symbol. [`hat_trace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L33).

**Theorem · The cosine weight preserves band symbols.** Multiplying a band symbol by the second-difference cosine weight gives another band symbol. [`band_cos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L79).

**Theorem · Integrability of phased band symbols.** A band symbol multiplied by the Fourier exponential is integrable. [`int_exp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L94).

**Theorem · Second differences of band fields.** The symmetric second difference of the field reconstructed from a band symbol corresponds to multiplying that symbol by the cosine weight. [`niceField_secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L103).

**Theorem · Second differences preserve L².** The symmetric second difference of an L² field belongs to L² for every displacement. [`memLp_secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L137).

**Theorem · Second differences are self-adjoint.** The symmetric second difference can be moved between the two fields in an L² integral pairing. [`pair_secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L145).

**Theorem · The second-difference Fourier symbol.** The Fourier symbol of an L² second difference equals its cosine weight times the original symbol almost everywhere. [`hat_secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L175).

**Theorem · Bounds on the cosine difference.** The cosine weight lies between zero and two and its square satisfies the stated fourth-order displacement bound. [`cosWeight_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L197).

**Theorem · Fourth-order small-displacement energy.** A regular adjoint field's second-difference square integral is bounded by a constant times the minimum of one and displacement norm to the fourth power. [`secondDiff_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L221).

**Theorem · Combining the kernel and quadratic power.** Multiplying the singular radial power by radius squared gives the stated exponent shifted by two. [`pow_near`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L263).

**Theorem · An integrable truncated kernel weight.** For fractional exponent between zero and one, the kernel times the minimum of one and radius squared is integrable. [`kern_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L273).

**Theorem · The complementary kernel weight.** For fractional exponent between zero and one, the kernel with the complementary truncated-square factor is integrable. [`kern_integrable_inv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L289).

**Theorem · The singular kernel is nonnegative.** The singular radial kernel is nonnegative at every displacement. [`kern_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L305).

**Theorem · Measurability of the singular kernel.** The singular radial kernel is measurable. [`measurable_kern`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L307).

**Theorem · Measurable second differences.** A strongly measurable field gives a jointly measurable symmetric second difference in the base point and displacement. [`measurable_secondDiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L309).

**Theorem · A weighted kernel Cauchy-Schwarz bound.** The square of the absolute kernel integral is bounded by the product of the two complementary weighted nonnegative integrals. [`square_point_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L315).

**Theorem · The kernel integral has finite L² norm.** The fourth-order second-difference bound implies finiteness of the squared absolute kernel integral for exponents between zero and one. [`core_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L366).

**Theorem · Second differences respect equality a.e..** Almost-everywhere equal fields have almost-everywhere equal second differences at every fixed displacement. [`secondDiff_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L402).

**Theorem · Changing representatives in the kernel.** When two almost-everywhere equal fields also agree at the base point, their kernel integrands agree almost everywhere in displacement. [`integrand_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L410).

**Theorem · The low fractional power belongs to L².** For exponent between zero and one, the low fractional power of a measurable regular adjoint field belongs to L². [`lowPower_memLp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L418).

**Theorem · Rotating an inner product to one axis.** Every nonzero vector admits a linear isometry expressing its inner product as its norm times the first transformed coordinate. [`coord_isometry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L459).

**Theorem · The Fourier multiplier integral.** The kernel-cosine integral equals the low-power normalization constant times the required fractional frequency power. [`kern_cos_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L473).

**Theorem · A positive low-power normalization.** The low-power normalization constant is positive for fractional exponents between zero and one. [`normalizer_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L502).

**Theorem · An integrable physical-space pairing.** The stated L² and second-difference bounds make the displacement-space kernel pairing integrable on the product space. [`prod_int_phys`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L550).

**Theorem · An integrable frequency-space pairing.** For a band test symbol and an L² frequency field, the kernel-cosine pairing is integrable on the product frequency-displacement space. [`prod_int_freq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L607).

**Theorem · Identifying the low-power symbol.** The stated measurability, second-difference and L² hypotheses identify the low power's symbol with multiplication by the fractional frequency power. [`symbol_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L662).

**Theorem · The adjoint low-power Fourier symbol.** A measurable regular adjoint field has the expected fractional Fourier multiplier as the symbol of its low power. [`lowPower_symbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L733).

**Theorem · Proving the fractional-power pairing.** The fractional-power pairing statement is proved from the low-power Fourier symbol and the negative-trace symbol. [`powerPairing`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointPowerPairing.lean#L776).

### Breakdown.FracCell.ReductionAdjointWeightedInverseSquare

This module combines cylindrical Fourier pairings and frame inverse-square estimates into the harmonic weighted dual bound. **Reading context:** Appendix B: the inverse-square, approximation and duality estimates supporting the adjoint reduction (B.11–B.12).

**Theorem · Inverting cylindrical coordinates.** The inverse cylindrical map multiplies radius by cosine and sine while preserving height. [`symm_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L20).

**Theorem · A measurable inverse cylindrical map.** The inverse cylindrical-coordinate map is measurable. [`symm_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L24).

**Theorem · Null sets in cylindrical coordinates.** A measurable spatial null set pulls back to a null set within the cylindrical chart target. [`target_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L30).

**Definition · The radius-height-angle map.** This map sends a radius-height pair and angle to the corresponding spatial ring point. [`ringMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L62).

**Theorem · The ring map as coordinate changes.** The ring map is the composition of the coordinate permutation, inverse cylindrical map and conversion to spatial vectors. [`ringMap_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L64).

**Theorem · Continuous coordinate insertion.** Inserting a real number into one fixed spatial coordinate is continuous. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L69).

**Theorem · The ring map is continuous.** The spatial ring point depends continuously on radius, height and angle. [`ringMap_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L79).

**Theorem · Null-set control for ring coordinates.** The ring map preserves null-set statements relative to the positive-radius and centered-angle product measure. [`ringMap_qmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L84).

**Theorem · Measurability of angular modes.** The angular-mode measurability statement is proved from the ring map's measure properties. [`modeMeasurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L104).

**Theorem · A weighted two-factor inequality.** Positive scaling parameters bound a product by the stated two complementary weighted squares. [`mean_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L128).

**Theorem · A two-component weighted inequality.** The radial Jacobian times two component products is bounded by the stated primal and dual weighted energy terms. [`point_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L137).

**Theorem · Optimizing the positive scale.** A family of complementary quadratic bounds for every positive scale implies the product-of-square-roots bound. [`le_sqrt_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L153).

**Theorem · Measurable horizontal complex parts.** The horizontal complex encoding of a measurable vector field is measurable almost everywhere. [`horizontal_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L193).

**Theorem · Measurable vertical complex parts.** The vertical complex encoding of a measurable vector field is measurable almost everywhere. [`vertical_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L203).

**Theorem · The dual bound from mode estimates.** The mode inverse-square estimate and mode-pairing estimate imply the harmonic weighted inverse-square statement. [`weightedInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L213).

**Theorem · Summing the frame mode inequalities.** The gradient-mode sum bound and frame inverse-square bound imply the full mode inverse-square statement. [`modeInverseSquare_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L274).

**Theorem · The weighted inverse-square bound.** Gradient-mode summation, frame inverse-square control and mode pairing together imply the harmonic weighted bound. [`weightedInverseSquare_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L278).

**Theorem · The angular Fourier coefficient.** The normalized centered-period angular integral equals the library's interval Fourier coefficient. [`coeff_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L287).

**Theorem · Bessel's bound on a circle.** Twice pi times the sum of squared normalized angular Fourier coefficients is bounded by the angular square integral. [`circle_coef_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L305).

**Theorem · A cylindrical nonnegative integral bound.** The radial-weighted cylindrical integral of a measurable nonnegative field is bounded by its spatial integral. [`cyl_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L335).

**Theorem · Horizontal and vertical energies add.** The squared horizontal complex norm plus the squared vertical norm equals the full vector's squared norm. [`parts_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L367).

**Theorem · A coordinate insertion as scalar scaling.** Inserting a scalar into one spatial coordinate equals scaling that coordinate unit vector. [`single_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L374).

**Theorem · Summing frame-column energies.** Away from the axis, the horizontal and vertical energies of all three frame columns sum to the matrix entry energy. [`frame_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L379).

**Theorem · Recovering the nonnegative ring radius.** A ring point constructed with nonnegative radius has that ring radius. [`ringRadius_ringPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L399).

**Theorem · Measurable ring-frame vectors.** Each ring-frame vector is a measurable function of the spatial point. [`ringFrame_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L404).

**Theorem · Proving the gradient-mode sum bound.** The gradient-mode sum statement follows from circle Bessel bounds and cylindrical integration. [`gradientModeSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L431).

**Theorem · The weighted bound from frame control.** The frame inverse-square and mode-pairing statements imply the weighted inverse-square bound with gradient summation supplied. [`weightedInverseSquare_of_frame`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L535).

**Definition · The normalized Fourier coefficient.** This coefficient integrates a complex angular function against the integer Fourier phase and divides by twice pi. [`coef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L545).

**Theorem · Identifying Fourier coefficients.** The defined angular coefficient equals the library's Fourier coefficient on the centered full period. [`coef_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L548).

**Theorem · Integrability of an L² Fourier integrand.** Multiplying an angular L² function by its integer Fourier phase gives an interval-integrable function. [`int_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L564).

**Theorem · Fourier coefficients preserve addition.** For angular L² functions, the coefficient of a sum is the sum of their coefficients. [`coef_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L573).

**Theorem · Subtracting Fourier coefficients.** For angular L² functions, the coefficient of a difference is the difference of their coefficients. [`coef_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L580).

**Theorem · Recovering a complex real pairing.** The difference of the squared norms of the sum and difference, divided by four, equals the real complex inner product. [`polar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L587).

**Theorem · A circle pairing bound by coefficients.** The absolute integral pairing of angular L² functions is bounded by twice pi times the sum of products of their normalized Fourier coefficient norms. [`circle_pair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L593).

**Theorem · Finite integrals on almost every ring.** A spatial integrable scalar function has finite nonnegative-part angular integral on almost every positive-radius ring. [`slice_fin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L658).

**Theorem · The spatial norm along a ring.** The squared norm of a ring point equals radius squared plus height squared. [`ring_norm_sq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L677).

**Theorem · The horizontal norm is controlled.** The horizontal complex norm is at most the full vector norm. [`hor_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L685).

**Theorem · The vertical norm is controlled.** The vertical complex norm is at most the full vector norm. [`ver_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L689).

**Theorem · Splitting a vector inner product.** The real vector inner product is the sum of its horizontal complex pairing and vertical complex pairing. [`inner_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L693).

**Theorem · A nonnegative triangle inequality.** The nonnegative extended-real absolute value of a sum is bounded by the sum of the two absolute values. [`ofReal_abs_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L700).

**Theorem · Ring coefficients equal angular modes.** The Fourier coefficient of a function restricted to a ring equals its angular mode at that radius and height. [`coef_ring`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L704).

**Theorem · Integrability of an angular L² pairing.** The real part of the complex pairing of two angular L² functions is interval integrable. [`pair_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L707).

**Theorem · Proving the mode-pairing estimate.** The mode-pairing statement is proved by circle Fourier pairing estimates and cylindrical integration. [`modePairingBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L728).

**Theorem · The weighted bound from one frame input.** The harmonic weighted inverse-square bound follows from the frame bound with its other mode estimates supplied. [`weightedInverseSquare_of_frameBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionAdjointWeightedInverseSquare.lean#L833).

### Breakdown.FracCell.ReductionFarDefs

This module states the scalar floor, angular inverse and column-tail estimates needed for unresolved high modes. **Reading context:** Appendix B: the unbounded exterior and angular-mode bounds in the cell and tail estimates (B.4–B.5).

**Interface · Floors for far-mode weights.** This proposition requires the finite far-floor tests to bound the strain and velocity weights beyond the near-degree cutoff. [`FarFloorStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarDefs.lean#L17).

**Interface providers.** [`Breakdown.CellCert.Reduction.farFloor_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L102) ([lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean:102](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L102); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Interface · A bound for the angular inverse.** This proposition bounds the angular inverse on the specified mode band by the proposed turn constant under the order and band assumptions. [`TurnBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarDefs.lean#L26).

**Interface providers.** [`Breakdown.CellCert.Reduction.turnBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean#L96) ([lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean:96](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean#L96); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Interface · From column tails to all inputs.** This proposition requires valid column-tail bounds for a regular family to imply tail bounds for all finite input combinations. [`TailColumnBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarDefs.lean#L34).

**Interface providers.** [`Breakdown.CellCert.Reduction.tailBounds_of_columns`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L285) ([lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean:285](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L285); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

### Breakdown.FracCell.ReductionFarFarFloor_of

This module extends the tested high-degree weight floors to all larger coefficient indices by spectral monotonicity. **Reading context:** Appendix B: the unbounded exterior and angular-mode bounds in the cell and tail estimates (B.4–B.5).

**Theorem · Radial eigenvalues increase with degree.** Increasing the radial index cannot decrease the radial eigenvalue. [`radialEigen_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L17).

**Theorem · Height eigenvalues increase with degree.** Increasing the height index cannot decrease the height eigenvalue. [`heightEigen_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L22).

**Theorem · The zero radial eigenvalue.** The radial eigenvalue at index zero is zero. [`radialEigen_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L27).

**Theorem · The zero height eigenvalue.** The height eigenvalue at index zero is zero. [`heightEigen_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L30).

**Theorem · The inner radius is nonnegative.** The inner radius extracted from a valid cell box is nonnegative. [`innerRadius_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L33).

**Theorem · A high mode exceeds one cutoff edge.** Beyond the square degree cutoff, the tail eigenvalue is at least one of the two first excluded edge eigenvalues. [`tailLam_ge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L39).

**Theorem · Extending two tested spectral floors.** Nonnegative scaling and increasing offsets extend the two edge floor bounds to every index beyond the degree cutoff. [`floor_gen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L57).

**Theorem · Nonnegative angular cell weight.** The angular weight of a valid cell is nonnegative. [`angularWeight_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L66).

**Theorem · The angular weight for nonzero modes.** Every nonzero angular mode has the cell's fixed nonzero-mode angular weight. [`angularWeight_ne_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L74).

**Theorem · The in-band strain bound decreases.** Under the stated nonnegative coefficient assumptions, increasing the mode number above one cannot increase the in-band strain bound. [`strainAt_anti`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L79).

**Theorem · Mode number from integer absolute value.** The mode number is the natural absolute value of the integer index multiplied by the symmetry order. [`modeNumber_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L94).

**Theorem · Proving the far-weight floors.** The far-floor statement is proved from radial, height and angular monotonicity. [`farFloor_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarFarFloor_of.lean#L102).

### Breakdown.FracCell.ReductionFarTailBounds_of_columns

This module rewrites tail energy as an orthogonal projection residual and bounds arbitrary input combinations by the sum of the column tails. **Reading context:** Appendix B: the unbounded exterior and angular-mode bounds in the cell and tail estimates (B.4–B.5).

**Predicate · Bounded measurable interval functions.** This proposition requires almost-everywhere strong measurability and a uniform norm bound on the closed interval. [`Good`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L9).

**Lemma · Integrating bounded measurable functions.** A function satisfying the bounded measurable interval condition is integrable on that interval. [`good_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L14).

**Lemma · Products preserve the interval condition.** The product of two bounded measurable interval functions is bounded and measurable. [`good_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L19).

**Lemma · Sums preserve the interval condition.** The sum of two bounded measurable interval functions is bounded and measurable. [`good_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L27).

**Lemma · The interval condition under subtraction.** The difference of two bounded measurable interval functions is bounded and measurable. [`good_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L33).

**Lemma · Constants satisfy the interval condition.** Every constant function is bounded and measurable on the closed interval. [`good_const`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L39).

**Lemma · Finite sums preserve interval regularity.** A finite sum of bounded measurable interval functions is bounded and measurable. [`good_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L42).

**Lemma · Complexification preserves regularity.** A bounded measurable real interval function remains bounded and measurable when viewed as complex. [`good_ofReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L49).

**Lemma · Interval regularity under conjugation.** Complex conjugation preserves the bounded measurable interval condition. [`good_conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L54).

**Lemma · Interval regularity of squared norms.** The squared norm of a bounded measurable complex interval function is bounded and measurable. [`good_normSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L59).

**Lemma · Continuity gives interval regularity.** A continuous function is bounded and measurable on each closed finite interval. [`good_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L65).

**Definition · The weighted sesquilinear pairing.** This interval pairing conjugates its first factor and weights the product of the two factors by the real weight before integration. [`pr`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L68).

**Definition · A weighted polynomial coefficient.** The coefficient pairs the supplied function with one real polynomial basis function against the interval weight. [`coefA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L71).

**Definition · Energy after removing low coefficients.** The tail quantity subtracts the squared low polynomial coefficients from the full weighted square energy. [`tailW`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L74).

**Lemma · Integrability of the weighted pairing.** Bounded measurable weight and factors make their weighted sesquilinear product integrable on the interval. [`pr_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L79).

**Lemma · Subtracting in the first pairing slot.** The weighted pairing distributes over subtraction in its first argument under the interval regularity conditions. [`pr_sub_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L83).

**Lemma · Subtracting in the second pairing slot.** The weighted pairing distributes over subtraction in its second argument under the interval regularity conditions. [`pr_sub_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L92).

**Lemma · Linearity in the second pairing slot.** Finite scalar combinations in the second argument pass outside the weighted pairing. [`pr_sum_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L100).

**Lemma · Conjugate symmetry of the pairing.** Exchanging the two arguments conjugates the weighted interval pairing. [`pr_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L112).

**Lemma · Conjugate linearity in the first slot.** A finite scalar combination in the first argument produces conjugated scalar coefficients outside the pairing. [`pr_sum_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L120).

**Lemma · The pairing of a function with itself.** The self-pairing is the real weighted square integral viewed as a complex number. [`pr_self`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L127).

**Lemma · A basis pairing is a coefficient.** Pairing a polynomial basis function with the supplied function gives its weighted coefficient. [`pr_poly_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L137).

**Lemma · Orthonormality in the complex pairing.** Real weighted orthonormal polynomials remain orthonormal for the complex weighted pairing. [`pr_poly_poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L145).

**Lemma · Tail energy equals residual energy.** For a regular orthonormal polynomial family, the tail quantity is exactly the squared weighted error after removing the low coefficients. [`resid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L158).

**Lemma · Bounding a combination by column tails.** The tail energy of a finite linear combination is at most its coefficient square sum times the sum of the individual column tails. [`col`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L193).

**Lemma · Combining weighted output bounds.** Nonnegative output weights combine the separate column-tail bounds into the stated total output bound. [`sumo`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L239).

**Lemma · The height tail in one-variable form.** The cell height-tail quantity is the generic tail energy with unit weight on the height interval. [`heightTail_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L256).

**Lemma · Continuity of a coefficient polynomial.** Every finite real polynomial assembled from the coefficient row is continuous. [`poly_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L260).

**Lemma · Continuity of the cell line weight.** The cell's radial line weight is continuous. [`lineWeight_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L264).

**Lemma · Nonnegativity of the cell line weight.** The cell line weight is nonnegative on its closed radial interval. [`lineWeight_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L277).

**Theorem · Proving full tail bounds from columns.** The full tail-bound statement follows from column residual estimates and the finite coefficient inequality. [`tailBounds_of_columns`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTailBounds_of_columns.lean#L285).

### Breakdown.FracCell.ReductionFarTurnBound_of

This module converts the explicit inverse angular operator into a uniform bound on the high mode band. **Reading context:** Appendix B: the unbounded exterior and angular-mode bounds in the cell and tail estimates (B.4–B.5).

**Theorem · A complex square norm in coordinates.** The squared complex norm is the sum of the squared real and imaginary parts. [`normSq_eq_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean#L15).

**Theorem · The angular-inverse energy estimate.** When the absolute angular frequency exceeds one, the inverse-turn energy times the squared frequency gap is bounded by the original energy. [`turnAdjInv_vecSq_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean#L19).

**Theorem · Proving the angular band bound.** The stated angular inverse bound holds throughout the specified mode band. [`turnBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionFarTurnBound_of.lean#L96).

### Breakdown.FracCell.ReductionLossAdjointQuad_of_potential

This module uses a positive kernel majorant for the adjoint field to control its quadratic nonlinear pairing. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Matrix energy bounds vector images.** The norm of a matrix applied to a vector is bounded by its entry-energy square root times the vector norm. [`apply_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L17).

**Theorem · Nonnegative matrix entry energy.** The matrix entry-square sum is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L36).

**Theorem · A scaled product-to-square inequality.** For a positive scale, a product is bounded by the two complementary weighted squares. [`amgm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L39).

**Theorem · A pointwise adjoint-pairing bound.** The stated field majorant and entry-energy bound give the two-term weighted estimate for the absolute adjoint pairing. [`pointwise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L46).

**Theorem · The quadratic adjoint loss bound.** The kernel-potential statement and a valid adjoint majorant imply the prescribed quadratic adjoint pairing bound by full field energy. [`adjointQuad_of_potential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L68).

### Breakdown.FracCell.ReductionLossCentreLoss_of_kernel

This module combines a uniform profile difference and a kernel bound for its gradient difference to control the change from the centre field. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · The matrix-energy action bound.** A matrix image is bounded in norm by the matrix entry-energy square root times the input norm. [`apply_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L19).

**Theorem · Nonnegative entry energy.** The matrix entry-square sum is nonnegative. [`entry_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L25).

**Theorem · The L² triangle inequality for majorants.** Two nonnegative square-integrable majorants have sum-square integral bounded by the square of the sum of their L² norms. [`sum_sq_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L27).

**Theorem · Bounding the change from the centre.** A valid centre kernel split and the stated numerical budget bound the linearized profile-centre difference by the centre loss times the energy square root. [`centreLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L63).

### Breakdown.FracCell.ReductionLossCurlGradLoss_of_kernel

This module turns a kernel majorant for the curl-gradient error into the corresponding perturbation loss bound. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Bounding the curl-gradient error.** The kernel-potential estimate bounds the curl-gradient error times an admissible velocity by the prescribed loss times the gradient-energy square root. [`curlGradLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlGradLoss_of_kernel.lean#L15).

### Breakdown.FracCell.ReductionLossCurlLoss_of_kernel

This module turns the cell-weighted curl-error kernel majorant into the curl perturbation loss bound. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Bounding the weighted curl error.** The kernel-potential estimate bounds the cell-weighted curl error times an admissible velocity by the prescribed loss times the gradient-energy square root. [`curlLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlLoss_of_kernel.lean#L15).

### Breakdown.FracCell.ReductionLossDefs

This module states the finite-energy, kernel, rotation and centre-splitting conditions used to bound perturbation losses. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Predicate · A finite-energy weak-gradient pair.** This proposition pairs a measurable L⁶ velocity with a measurable square-integrable weak gradient. [`IsGradientPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L18).

**Predicate · A finite-energy weak Hessian pair.** This proposition pairs a finite-energy gradient with a measurable square-integrable weak second derivative. [`IsSecondDerivPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L22).

**Interface · A proposed Sobolev norm constant.** This proposition requires a nonnegative constant whose sixth power bounds velocity L⁶ energy by the cube of gradient energy. [`SixthPowerConstStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L26).

**Reader note.** No theorem with this exact interface as its named result and no theorem referring to its name were found in the library. This records the status of the named interface; it does not assert that the mathematical estimate is false.

**Interface providers.** No theorem with this exact named interface as its result was found in the library.

**Theorems using this interface name.** None found in the library.

**Predicate · A uniform Newtonian potential bound.** This proposition requires a measurable nonnegative potential with integrable Newtonian kernel at every center and a uniform upper bound. [`KernelBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L29).

**Interface · A potential-weighted energy inequality.** This proposition bounds the potential-weighted velocity square integral by the Newtonian kernel bound times weak-gradient energy. [`KernelPotentialStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L33).

**Interface providers.** [`Breakdown.CellCert.Reduction.kernelPotential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L82) ([lean/Breakdown/FracCell/ReductionLossKernelPotential.lean:82](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L82); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.adjointQuad_of_potential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L68) ([lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean:68](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossAdjointQuad_of_potential.lean#L68); named reference in type); [`Breakdown.CellCert.Reduction.centreLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L63) ([lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean:63](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCentreLoss_of_kernel.lean#L63); named reference in type); [`Breakdown.CellCert.Reduction.curlGradLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlGradLoss_of_kernel.lean#L15) ([lean/Breakdown/FracCell/ReductionLossCurlGradLoss_of_kernel.lean:15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlGradLoss_of_kernel.lean#L15); named reference in type); [`Breakdown.CellCert.Reduction.curlLoss_of_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlLoss_of_kernel.lean#L15) ([lean/Breakdown/FracCell/ReductionLossCurlLoss_of_kernel.lean:15](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossCurlLoss_of_kernel.lean#L15); named reference in type).

**Definition · Rotation about the third coordinate.** This map rotates the first two coordinates through the specified angle and leaves the third coordinate fixed. [`turnBy`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L37).

**Predicate · Conditions for finite kernel cell sums.** This record binds a nonnegative symmetric potential to its geometric pieces, suprema, masses, near-region rules and finite box-sum bounds. [`IsCellSumData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L47).

**Structure · Rotation data for the row family.** This record stores row partners, integer modes, cell assignments, cell radii and the row-rate constant. [`RowTurnData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L71).

**Predicate · Conditions for rotating row estimates.** This record requires the row rotation law, compatible partners and cells, orthonormality, support and radius-weight conditions used in the row-mode estimate. [`IsRowTurnData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L79).

**Interface · Row angular and gradient energies.** This proposition bounds weighted row-pairing energy with the clipped angular-gap factor by the row-rate constant squared times gradient energy. [`RowModeGradientStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L100).

**Interface providers.** [`Breakdown.CellCert.FinalCellSystem.rowModeGradient_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/FinalChain.lean#L1147) ([lean/Breakdown/FracCell/FinalChain.lean:1147](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/FinalChain.lean#L1147); no additional named Statement/Holds premise in its displayed declaration); [`Breakdown.CellCert.Reduction.rowModeGradient_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L116) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:116](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L116); named premises: `CellAngularBoundStatement`); [`Breakdown.CellCert.Reduction.rowModeGradient_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:183](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183); named premises: `RotationDifferenceStatement`, `RowRotationCoefEnergyStatement`); [`Breakdown.CellCert.Reduction.rowModeGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L859) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:859](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L859); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.FinalCellSystem.cellRest_of_system`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/FinalChain.lean#L775) ([lean/Breakdown/FracCell/FinalChain.lean:775](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/FinalChain.lean#L775); named reference in type); [`Breakdown.CellCert.Reduction.rateLoss_of_rows`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L61) ([lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean:61](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L61); named reference in type).

**Interface · The pointwise field bound from energies.** This proposition bounds the velocity norm squared almost everywhere by one over twice pi times the product of gradient-energy and trace-energy square roots. [`SupNormStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L106).

**Interface providers.** [`Breakdown.CellCert.Reduction.supNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L599) ([lean/Breakdown/FracCell/ReductionLossSupNorm.lean:599](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L599); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.productConst_of_supNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L165) ([lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean:165](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L165); named reference in type).

**Structure · The two centre-error budgets.** This record stores a parameter-dependent uniform profile-error bound and a fixed gradient-kernel bound. [`CentreKernelSplit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L112).

**Predicate · Conditions on the centre-error split.** This record requires the profile difference to obey its uniform bound and its squared gradient difference to obey the stated nonnegative kernel bound. [`IsCentreKernelSplit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossDefs.lean#L116).

### Breakdown.FracCell.ReductionLossKernelBoundParts

This file partitions cell solids into equal-angle sectors and proves the geometric and radial-shell estimates used to bound the Newton kernel. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Definition · The angle of the planar coordinate.** The planar angle is the complex argument of the first two spatial coordinates. [`planeAngle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L19).

**Definition · One angular sector of a set.** A sector consists of the points of a set whose angle relative to the target falls in the specified half-open subdivision of a full turn. [`sectorPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L21).

**Theorem · The interval gap bounds separation.** The gap between the displayed intervals is nonnegative and no greater than the distance between any two points satisfying their endpoint bounds. [`gapDist_le_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L26).

**Theorem · Squaring a nonnegative gap bound.** A nonnegative lower bound for an absolute value gives the corresponding bound between squares. [`sq_le_of_gap_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L41).

**Theorem · Squared spatial norm by coordinates.** Squared spatial norm equals the sum of the three squared coordinates. [`norm_sq_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L45).

**Theorem · Reflection reverses height.** The mirror map keeps both planar coordinates and negates height. [`mirror_apply_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L49).

**Theorem · The planar angle is measurable.** The planar angle is a measurable function of the spatial point. [`planeAngle_measurable_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L52).

**Theorem · Angular sectors are measurable.** Each angular sector cut from a measurable set is measurable. [`sectorPart_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L61).

**Theorem · Positive sector counts cover the set.** For a positive number of sectors, every point of the set lies in a sector with index below that number. [`sectorPart_cover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L72).

**Theorem · Planar coordinates from radius and angle.** Horizontal norm times cosine and sine of the planar angle recover the first two coordinates. [`polar_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L98).

**Theorem · Planar distance by radial and angle gaps.** Squared planar distance splits into the squared difference of horizontal radii and the displayed sine-squared angular term. [`horizontal_polar_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L109).

**Theorem · An angular lower bound within a sector.** For an even sector count, the sector index gives the displayed lower bound for the squared sine of half the angle. [`sin_sector_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L136).

**Theorem · Rotation as complex multiplication.** Rotating the spatial point multiplies its complex planar coordinate by the corresponding unit phase. [`plane_turn_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L205).

**Theorem · The angle after a planar rotation.** Away from the axis, rotation adds its angle to the planar argument up to an integer multiple of two pi. [`angle_turn_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L210).

**Theorem · Reducing a bounded angle modulo two pi.** In the displayed angle range, reduction modulo two pi either leaves the angle unchanged or subtracts one full turn. [`toIcoMod_shift_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L219).

**Theorem · Reducing a rotated relative angle.** Away from the axis, the relative angle after rotation is obtained by adding the rotation to the reduced relative angle and reducing again. [`shifted_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L237).

**Theorem · Rotation moves to the next sector.** For a rotation-invariant set and a nonfinal sector, rotation through one sector width moves off-axis membership to the next sector. [`mem_shift_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L249).

**Theorem · Almost every point is off the axis.** The complex planar coordinate is nonzero almost everywhere in space. [`axis_null_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L296).

**Theorem · Finite endpoints bound a cell solid.** A piece solid with finite upper radial and height endpoints is bounded. [`solid_bounded_of_some`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L312).

**Theorem · Integrability on a cell solid.** The cell-sum hypotheses make the potential integrable on each piece solid. [`solid_integrable_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L341).

**Theorem · Distinct ordered sectors are disjoint.** For a positive sector count, sectors with strictly ordered indices are disjoint. [`sector_disjoint_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L344).

**Theorem · A sector receives at most equal mass.** The cell-sum symmetry hypotheses bound each sector's potential mass by the piece mass divided by the sector count. [`sectorPart_mass`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L356).

**Theorem · Sector geometry bounds kernel distance.** The certified sector distance is a lower bound for the distance from the target or its mirror to every point in that sector. [`sectorPart_dist`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L412).

**Definition · The truncated radial kernel excess.** The shell cutoff is the excess of the inverse-radius kernel over its value at the outer radius on the displayed radial interval, and zero elsewhere. [`shellCut`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L454).

**Theorem · The shell cutoff is nonnegative.** The truncated kernel excess is nonnegative for every displayed radius. [`shellCut_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L457).

**Theorem · The weighted cutoff as a polynomial.** On positive radii, multiplying the shell cutoff by the radial volume weight gives the displayed interval-restricted quadratic expression. [`shellCut_radial_eqOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L468).

**Theorem · The cutoff integral on its interval.** With ordered nonnegative endpoints, the positive-radius integral of the restricted quadratic expression equals its interval integral. [`shellCut_Ioi`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L481).

**Theorem · Evaluating the radial cutoff integral.** For positive outer radius, the radial cutoff integral equals the displayed difference of quadratic and cubic endpoint terms divided by four pi. [`shellCut_interval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L502).

**Theorem · The translated cutoff is integrable.** The shell cutoff applied to distance from any fixed target is integrable over space. [`shellCut_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L512).

**Theorem · The exact spatial cutoff integral.** For ordered nonnegative radii and positive outer radius, the spatial cutoff integral equals the displayed quadratic-minus-cubic expression. [`shellCut_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L522).

**Theorem · Splitting the inverse-radius kernel.** A nonnegative weight bounded by M is controlled by its constant outer-radius kernel plus M times the shell cutoff. [`shell_pointwise`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L534).

**Theorem · The shell bound for a weighted kernel.** A nonnegative integrable weight with mass, supremum and distance bounds has an integrable Newton kernel bounded by the displayed shell quantity. [`shellKernel_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L567).

**Theorem · A shell bound with an a.e. supremum.** The same Newton-kernel shell bound holds when the weight's supremum bound is imposed almost everywhere. [`shellKernel_le_ae`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L678).

**Definition · The signed relative planar angle.** The signed turn selects the relative angle greater than minus pi and at most pi by subtracting a full turn when necessary. [`signedTurn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L697).

**Definition · A thin angular neighbourhood.** The near sheet takes the two sectors adjacent to the target angle and restricts the scaled signed angle by the supplied length. [`nearSheet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L702).

**Theorem · The signed relative angle is measurable.** For a fixed target, the signed turn is measurable in the other point. [`signedTurn_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L705).

**Theorem · The signed angle in adjacent sectors.** With at least four sectors, the signed angle in the two adjacent sectors has size at most one sector width and gives the same squared half-angle sine as the reduced angle. [`signedTurn_props`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L715).

**Theorem · A chord bound for sine.** Between zero and an angle at most pi, the sine lies above the chord joining the endpoints. [`sin_chord_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L756).

**Theorem · Distance outside the near angular sheet.** Outside the near-sheet angular cutoff in the adjacent sectors, spatial distance is at least the square root of the base-distance square plus cutoff-length square. [`far_dist_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L769).

**Theorem · Sheet bounds for nearby sectors.** Under rule two, the stated unweighted near-sheet integral bound yields the certified bound for the weighted kernel on the two adjacent sectors. [`twoSector_near_of_sheet`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundParts.lean#L861).

### Breakdown.FracCell.ReductionLossKernelBoundPiece

This file combines the alternative geometric estimates into the rule-selected kernel bound for a single source piece and target box. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · The interval gap bounds separation.** The gap between the displayed intervals is nonnegative and no greater than the distance between any two points satisfying their endpoint bounds. [`gapDist_le_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L16).

**Theorem · Squaring a nonnegative gap bound.** A nonnegative lower bound for an absolute value gives the corresponding bound between squares. [`sq_le_of_gap_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L31).

**Theorem · Horizontal radius difference is bounded.** The squared difference of horizontal radii is at most the squared planar distance. [`horizontal_gap_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L35).

**Theorem · Squared spatial norm by coordinates.** Squared spatial norm equals the sum of the three squared coordinates. [`norm_sq_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L51).

**Theorem · Reflection preserves horizontal radius.** Mirroring a spatial point leaves its horizontal norm unchanged. [`horizontalNorm_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L55).

**Theorem · The first sector gives a distance bound.** The zero-index certified sector distance bounds the distance from the target or its mirror to every point in the piece solid. [`firstDist_le_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L59).

**Theorem · Integrability on a cell solid.** The cell-sum hypotheses make the potential integrable on each piece solid. [`solid_integrable_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L90).

**Theorem · An integral bounded by a finite cover.** A nonnegative integrable function on a measurable set has integral at most the sum of its integrals over a finite measurable cover. [`cover_integral_le_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L93).

**Theorem · Pairing reflected sector indices.** Summing a function of the reflected index over twice as many sectors equals twice the sum over the first half. [`reflect_sum_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L113).

**Theorem · Pairing the interior reflected indices.** Excluding the two outer indices, the reflected-index sum equals twice the corresponding interior half-sum. [`reflect_sum_inner_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L129).

**Theorem · Bounding a piece by sector sums.** The weighted Newton-kernel integral over a piece solid is bounded by its full certified sector sum. [`sectorKernel_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L155).

**Theorem · A near term plus the remaining sectors.** Under rule two, a piece's kernel integral is bounded by the near term plus the sector sum excluding the adjacent pair. [`nearKernel_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L197).

**Theorem · The certified bound for one piece.** Every piece kernel is integrable and its integral is bounded by the selected pair term for the target box and reflection choice. [`pieceKernel_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundPiece.lean#L271).

### Breakdown.FracCell.ReductionLossKernelBoundSheet

This file integrates the thin angular-sheet estimate, using a decreasing radial rearrangement and an explicit primitive to obtain the near-sector bound. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Integrating the angular kernel bound.** For positive separation, scale and length, the truncated angular inverse-distance integral is bounded by the displayed inverse-hyperbolic-sine expression. [`uIntegral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L17).

**Theorem · A decreasing radial rearrangement bound.** For a decreasing radial integrand, a finite-measure set outside an inner radius has integral at most the comparison shell when that shell has at least its measure. [`bathtub_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L76).

**Theorem · Polar integration of a radial function.** The planar integral of a measurable nonnegative radial function equals two pi times its radius-weighted positive radial integral. [`radial_lintegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L109).

**Theorem · Inverse hyperbolic sine is bounded.** The absolute inverse hyperbolic sine is at most the absolute value of its input. [`arsinh_abs_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L131).

**Definition · A primitive for the sheet bound.** The sheet primitive combines a squared-radius inverse-hyperbolic-sine term and a square-root term, divided by two. [`sheetPrim`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L144).

**Theorem · Derivative of the sheet primitive.** At positive radius, the sheet primitive has derivative radius times the inverse hyperbolic sine of length divided by radius. [`sheetPrim_deriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L146).

**Theorem · Continuity of the sheet primitive.** The sheet primitive is continuous on every displayed closed interval starting at zero. [`sheetPrim_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L167).

**Theorem · Integrating the radial sheet weight.** The nonnegative radial inverse-hyperbolic-sine integral over an ordered nonnegative interval is bounded by the difference of sheet primitives. [`radial_arsinh_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L194).

**Theorem · The sheet primitive is increasing.** For positive sheet length, the sheet primitive is nondecreasing between ordered nonnegative radii. [`sheetPrim_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L233).

**Theorem · Signed angular reduction is measurable.** Reduction modulo two pi into the signed angular interval is measurable. [`toIocMod_measurable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L245).

**Theorem · Rotating an angular integral.** Shifting and reducing the angular input modulo a full turn leaves its nonnegative integral over one period unchanged. [`periodic_lintegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L254).

**Theorem · Bounding the planar sheet integral.** A rectangle separated from the target by the stated radial gap has its inverse-hyperbolic-sine integral bounded by the comparison annulus expression. [`planar_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L274).

**Definition · Cartesian coordinates as spatial vectors.** The measurable equivalence reorders two planar coordinates and a height coordinate into the three-dimensional spatial vector. [`cylSp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L383).

**Theorem · Coordinates preserve volume.** The Cartesian-to-space measurable equivalence preserves volume. [`cylSp_mp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L389).

**Theorem · Coordinates of the spatial equivalence.** The coordinate equivalence returns its two planar inputs and height as the three spatial coordinates. [`cylSp_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L395).

**Theorem · Angle and radius of a cylindrical point.** At positive radius and angle strictly between minus pi and pi, the cylindrical point has the supplied planar angle and horizontal norm. [`planeAngle_cyl`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L398).

**Theorem · Signed turn as modular reduction.** The signed relative angle is precisely reduction of the angle difference into the signed two-pi interval. [`signedTurn_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L415).

**Theorem · Signed angles in adjacent sectors.** With at least four sectors, the two adjacent sectors have signed angle of size at most one sector width. [`signedTurn_small`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L438).

**Theorem · The sine lies above its endpoint chord.** For the displayed angles between zero and pi, sine is at least its linear endpoint chord. [`chord_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L468).

**Theorem · Recovering planar coordinates.** Horizontal norm and planar angle recover both planar coordinates by cosine and sine. [`plane_coords`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L481).

**Theorem · Squared gap bounds squared separation.** The squared interval gap is bounded by the squared difference of points satisfying the displayed endpoint conditions. [`gap_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L492).

**Theorem · Cylindrical control of the sheet kernel.** Near-sheet membership supplies the cylindrical coordinate bounds and bounds the kernel by the displayed radial-height-angular distance expression. [`geom_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L508).

**Theorem · Measurability of the planar angle.** The complex argument of the planar coordinate is measurable. [`planeAngle_meas`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L629).

**Theorem · The geometric near-sheet integral bound.** Under rule two, the unweighted Newton-kernel integral over the near sheet is bounded by the explicit sheet-area expression. [`nearSheet_kernel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L638).

**Theorem · The weighted adjacent-sector bound.** Under rule two, the weighted Newton-kernel integral over the two adjacent sectors is bounded by the certified near term. [`twoSector_near`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBoundSheet.lean#L831).

### Breakdown.FracCell.ReductionLossKernelBound_of_cellSums

This file sums the piece bounds over the upper half-space and uses mirror symmetry to obtain the global kernel estimate. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Reflection is an involution.** Mirroring a spatial point twice returns the original point. [`mirror_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L16).

**Theorem · Moving a reflection between endpoints.** Distance from a point to a mirrored point equals distance from the first point's mirror to the original second point. [`norm_sub_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L20).

**Theorem · Horizontal norm is nonnegative.** The horizontal norm of every spatial point is nonnegative. [`horizontalNorm_nonneg_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L26).

**Theorem · Reflecting a symmetric kernel weight.** For a mirror-invariant potential, reflecting the integration point transfers the reflection to the target in the weighted Newton kernel. [`kernel_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L28).

**Theorem · Measurability of the weighted kernel.** A measurable potential gives a measurable weighted Newton kernel for every fixed target. [`kernel_measurable_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L32).

**Theorem · Nonnegativity of the weighted kernel.** A nonnegative potential makes the weighted Newton kernel nonnegative. [`kernel_nonneg_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L36).

**Theorem · Reflection is a measurable embedding.** The mirror map is a measurable embedding of space. [`mirror_embedding_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L41).

**Theorem · Reflection preserves integrability.** A real spatial function is integrable exactly when its composition with reflection is integrable. [`comp_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L44).

**Theorem · Reflection preserves the integral.** Composing a real spatial function with reflection leaves its integral unchanged. [`integral_comp_mirror_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L48).

**Theorem · Cell sums bound the upper half-space.** A uniform upper bound for the certified box bounds gives an integrable weighted Newton kernel and that same bound at every target of nonnegative height. [`upper_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L52).

**Theorem · Cell sums supply the global kernel bound.** Valid cell-sum data and one upper bound for every box bound imply the global kernel-bound proposition. [`kernelBound_of_cellSums`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelBound_of_cellSums.lean#L129).

### Breakdown.FracCell.ReductionLossKernelPotential

This file passes the smooth test-field potential estimate through controlled approximations and proves the full weak-gradient kernel-potential statement. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Matrix energy is nonnegative.** The sum of the squared matrix entries is nonnegative. [`entrySq_nonneg_aux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L17).

**Theorem · The kernel constant is nonnegative.** Any constant satisfying the global kernel-bound proposition is nonnegative. [`kernelBound_const_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L20).

**Theorem · Passing the potential bound to a limit.** Smooth compactly supported approximations converging almost everywhere to a measurable vector field, with derivative energies at most the given energy plus a vanishing error, transfer the weighted potential estimate to that field. [`kernel_of_approx`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L26).

**Theorem · The full kernel-potential estimate.** The global kernel bound controls the potential-weighted squared norm of a field by the energy of its weak gradient, under the integrability and measurability hypotheses in the kernel-potential proposition. [`kernelPotential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotential.lean#L82).

### Breakdown.FracCell.ReductionLossKernelPotentialApprox

This file constructs smooth approximations from weak gradients, then uses radial cutoffs to obtain compact support while making the added derivative energy vanish. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Cutoff derivatives lie in an annulus.** For a positive radius, a nonzero derivative of the radial cutoff can occur only between that radius and twice that radius. [`fderiv_radialCutoff_ne`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L18).

**Theorem · A square controlled by a sixth power.** For a positive scale M, a real square is at most its sixth power divided by M squared, plus M. [`sq_le_six_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L40).

**Theorem · The cutoff derivative cost vanishes.** For a continuous field in L6, the integral of its squared norm times the squared cutoff derivative tends to zero as the cutoff radius tends to infinity. [`cutoffTail`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L54).

**Theorem · A weighted bound for a squared sum.** For a positive parameter, the square of a real sum is bounded by the two squares with reciprocal complementary weights. [`sq_add_le_weighted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L152).

**Theorem · Energy of a cutoff field.** Multiplying a smooth field by a radial cutoff bounds its derivative energy density by a weighted original energy density plus the cutoff derivative cost. [`entrySq_cutoff_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L160).

**Theorem · Cutoffs add vanishing energy.** A smooth L6 field with integrable derivative energy admits all sufficiently large radial cutoffs whose total derivative energy exceeds the original by at most any prescribed positive error. [`cutoffEnergy`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L200).

**Theorem · Convex powers pass through smoothing.** For an integrable norm power of exponent at least one, the same power of a normalized bump convolution is at most the convolution of that norm power. [`normPow_convolution_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L244).

**Theorem · Smoothing recovers the weak gradient.** For an L6 field with the stated weak gradient, each coordinate derivative of its normalized bump smoothing is the smoothing of the corresponding gradient column. [`mollify_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L300).

**Theorem · Smooth approximations preserve energy.** An L6 field with measurable finite-energy weak gradient has smooth L6 approximations converging almost everywhere, each with derivative energy at most the original gradient energy. [`smoothApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L331).

**Theorem · Radial cutoffs are scalar test functions.** The radial cutoff of radius n plus one is a smooth compactly supported scalar test function. [`testScalar_cutoff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L400).

**Theorem · Compact smooth energy approximations.** An L6 field with measurable finite-energy weak gradient has smooth compactly supported approximations converging almost everywhere with derivative energies at most the original plus 1/(n+1). [`smoothCompactApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialApprox.lean#L403).

### Breakdown.FracCell.ReductionLossKernelPotentialTest

This file proves the potential estimate for compactly supported smooth scalar and vector tests, using smoothing and the signed fundamental-solution potential. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Positive sources have negative potential.** The fundamental-solution potential of a nonnegative scalar source is nonpositive everywhere. [`potential_nonpos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L19).

**Theorem · A smooth potential controls test energy.** For a smooth compactly supported nonnegative weight whose negative potential is bounded by Λ, every smooth compactly supported scalar test function satisfies the weighted energy bound with constant Λ plus any positive error. [`smoothCase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L30).

**Theorem · Smoothing preserves the potential bound.** A nonnegative integrable weight below a kernel-bounded potential retains the same potential bound after normalized bump smoothing. [`mollPotential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L161).

**Theorem · The smoothed weight controls test energy.** A compactly supported nonnegative integrable weight below a kernel-bounded potential, after normalized bump smoothing, satisfies the scalar test-function energy estimate with the original kernel constant. [`mollCase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L258).

**Theorem · A kernel bound controls scalar tests.** The global kernel bound makes the potential-weighted square of a smooth compactly supported scalar test function integrable and bounds its integral by the kernel constant times its gradient energy. [`scalarCase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L283).

**Theorem · A scalar test has finite gradient energy.** The sum of the squared coordinate derivatives of a smooth compactly supported scalar function is integrable. [`gradSq_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L387).

**Theorem · A kernel bound controls vector tests.** The global kernel bound makes the potential-weighted squared norm of a smooth compactly supported vector field integrable and bounds its integral by the kernel constant times its matrix derivative energy. [`kernelPotentialTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossKernelPotentialTest.lean#L405).

### Breakdown.FracCell.ReductionLossProductConst_of_supNorm

This file combines supremum control with gradient energy and a weighted quartic inequality to derive the product-loss estimate and its explicit numerical constant. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · A product bounded by fourth powers.** For three real numbers, the product of the first two and the square of the third is bounded by their weighted fourth-power mean. [`four_mean`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L16).

**Theorem · Existence of positive fourth roots.** Every positive real number has a positive real fourth root. [`fourth_root`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L22).

**Theorem · A weighted fourth-power product bound.** When positive κ and w satisfy 256κ⁴w³ = 27, the mixed quartic sum abp² + pqa² is bounded by κ times the corresponding weighted fourth-power sum. [`sum_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L25).

**Theorem · A balanced two-factor product bound.** With the same sharp relation between positive κ and w and nonnegative a and p, the mixed quartic sum is at most twice κ times the square roots of the two weighted fourth-power sums. [`pair_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L56).

**Theorem · Matrix energy is nonnegative.** The sum of squared entries of a linear map is nonnegative. [`entry_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L84).

**Theorem · Matrix energy bounds its action.** The norm of a linear map applied to a vector is at most the square root of its entry-square energy times the vector norm. [`apply_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L87).

**Theorem · Supremum bounds control the product.** Almost-everywhere supremum bounds on two fields, together with finite gradient energies, bound the L2 norm of their symmetrized product by half the sum of each supremum bound times the other gradient-energy square root. [`product_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L92).

**Theorem · Supremum estimates supply product loss.** Assuming the supremum-norm statement, a positive measurable bounded weight and the displayed numerical lower bound on the product constant give the required symmetrized-product energy estimate for two second-order fields. [`productConst_of_supNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossProductConst_of_supNorm.lean#L165).

### Breakdown.FracCell.ReductionLossRateLoss_of_rows

This file turns angular row-mode estimates into the rate-loss bound, tracking the order correction and the lower bound on the reduction weight. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Modes control the shifted angular factor.** For order at least two and a nonzero mode whose magnitude is at least that order, the mode square is bounded by the shifted absolute-mode square with factor (m divided by m minus one) squared. [`mode_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L16).

**Theorem · Scaling an L2 pairing.** Scaling the first field in the L2 pairing scales the pairing by the same real factor. [`pair_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L30).

**Theorem · An involution preserves a finite sum.** Reindexing a finite sum by an involution leaves the sum unchanged. [`sum_partner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L37).

**Theorem · The weighted energy controls gradients.** A positive lower bound on the weight makes the reduction energy dominate that lower bound times the total gradient entry-square energy for a second-order field. [`energy_ge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L41).

**Theorem · Row estimates supply rotation-rate loss.** Assuming the row-mode gradient statement, valid turning rows and the stated per-box rate inequality give the reduction rate-loss estimate for every second-order field. [`rateLoss_of_rows`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRateLoss_of_rows.lean#L61).

### Breakdown.FracCell.ReductionLossRotationLeaves

This file proves rotation-difference estimates and constructs smooth approximations that preserve angular derivatives, including the mollifier and convolution-gradient interfaces. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Interface · Smooth rotation estimate interface.** This proposition requires the L2 change of a continuously differentiable field under any axial turn on a bounded measurable rotation-invariant set to be at most the turn angle magnitude times its angular-derivative L2 norm. [`RotationSmoothStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L19).

**Interface providers.** [`Breakdown.CellCert.Reduction.rotationSmooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L265) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L265); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.rotationDifference_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110); named reference in type).

**Interface · Angular approximation interface.** This proposition requires second-order fields to admit continuously differentiable approximations on every compact set whose values and angular derivatives converge in L2 to the field and its gradient applied to the axial direction. [`RotationApproxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L25).

**Interface providers.** [`Breakdown.CellCert.Reduction.rotationApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:293](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293); named premises: `ConvGradientStatement`, `MollifierStatement`); [`Breakdown.CellCert.Reduction.rotationApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L440) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:440](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L440); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.rotationDifference_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110); named reference in type).

**Interface · Spatial smoothing interface.** This proposition requires smooth compactly supported kernels supported in the unit ball whose convolutions converge in L2 to every L2 vector field. [`MollifierStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L33).

**Interface providers.** [`Breakdown.CellCert.Reduction.rotationMollifier`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L395) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:395](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L395); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.rotationApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:293](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293); named reference in type).

**Interface · Local convolution gradient interface.** This proposition identifies coordinate derivatives of a locally truncated convolution with convolutions of the weak-gradient columns whenever the truncating set contains the relevant closed unit ball. [`ConvGradientStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L39).

**Interface providers.** [`Breakdown.CellCert.Reduction.convGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L400) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:400](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L400); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.rotationApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293) ([lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean:293](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293); named reference in type).

**Theorem · The two axial rotation maps agree.** The axialRotation map and turnBy have the same value for every angle and spatial point. [`rot_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L49).

**Theorem · The rotation functions coincide.** For each angle, turnBy and axialRotation are equal as functions on space. [`turn_fun`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L53).

**Theorem · Axial turns preserve volume.** Every axial turn preserves spatial volume. [`turn_mp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L55).

**Theorem · An axial turn is a measurable embedding.** An axial turn is a measurable embedding of space. [`turn_embedding`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L59).

**Theorem · Restricted volume is rotation invariant.** An axial turn preserves volume restricted to a measurable set that is invariant under all axial turns. [`turn_mp_restrict`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L63).

**Theorem · An axial turn preserves the norm.** The norm of a spatial point is unchanged by an axial turn. [`norm_turn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L72).

**Theorem · A zero-angle turn is the identity.** Turning a spatial point through zero angle leaves it unchanged. [`turn_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L76).

**Theorem · The angle derivative is axial motion.** As a function of the turning angle, an axial rotation has derivative equal to axialTurn applied to the rotated point. [`turn_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L80).

**Theorem · A coordinate injection is continuous.** The map inserting a real number into one spatial coordinate and zero into the others is continuous. [`single_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L86).

**Theorem · Joint continuity of rotation.** The rotated point depends continuously on the point and on the turning angle together. [`turn_joint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L98).

**Theorem · An integral-square bound on finite mass.** For an integrable real function with integrable square on a finite measure space, its integral squared is at most the total mass times the integral of its square. [`sq_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L105).

**Theorem · The angular derivative is continuous.** For a continuously differentiable field, its derivative applied to the axial direction varies continuously in space. [`fd_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L132).

**Theorem · Continuity of a rotation orbit.** The axial-turn orbit of a fixed spatial point is continuous in the angle. [`orbit_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L136).

**Theorem · Integrating the angular derivative.** For a continuously differentiable field, integrating its angular derivative along the orbit from zero to an angle gives the field difference between the rotated and original point. [`ftc_orbit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L143).

**Theorem · The angular interval has finite measure.** The unordered half-open interval between zero and a real angle has finite volume. [`uIoc_finite`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L154).

**Theorem · The angular interval has absolute length.** The real volume of the unordered half-open interval between zero and an angle is the magnitude of that angle. [`uIoc_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L158).

**Theorem · A pointwise rotation-difference bound.** The squared change of a continuously differentiable field under a turn is at most the angle magnitude times the orbit integral of its squared angular derivative. [`point_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L162).

**Theorem · Squared norms as an L2 expression.** For a measurable vector field, the integral of its squared norm equals the real conversion of its extended L2 norm squared. [`sq_int_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L177).

**Reader note.** This uses the totalized integral and ENNReal.toReal conventions, so the identity alone does not assert a finite L2 norm.

**Theorem · Angular derivatives are bounded on balls.** The squared norm of the angular derivative of a continuously differentiable field is bounded on each closed ball. [`fd_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L188).

**Theorem · The smooth integral rotation estimate.** On a bounded measurable rotation-invariant set, the squared L2 change of a continuously differentiable field under a turn is at most the angle squared times the integral of its squared angular-derivative norm. [`smooth_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L196).

**Theorem · Axial motion is bounded by the radius.** The norm of axialTurn applied to a spatial point is at most the norm of that point. [`turn_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L237).

**Theorem · The kernel derivative vanishes far away.** A differentiable scalar kernel supported in the closed unit ball has zero derivative at points of norm greater than one. [`fderiv_zero_far`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L244).

**Theorem · Differentiating a reversed translate.** Differentiating a smooth scalar kernel at y minus z with respect to z gives the negative derivative of the kernel at that translated point. [`shift_fderiv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L253).

**Theorem · The smooth rotation estimate.** The smooth rotation-difference proposition holds for continuously differentiable fields on bounded measurable rotation-invariant sets. [`rotationSmooth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L265).

**Theorem · Smoothing yields angular approximations.** The mollifier proposition and the local convolution-gradient proposition together imply the angular approximation proposition. [`rotationApprox_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L293).

**Theorem · Construction of L2 smoothing kernels.** There exist smooth compactly supported kernels supported in the unit ball whose convolutions converge in L2 to every L2 vector field. [`rotationMollifier`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L395).

**Theorem · Local weak derivatives of convolution.** The local convolution-gradient proposition holds for smooth compactly supported kernels, locally integrable fields and their weak gradients. [`convGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L400).

**Theorem · Approximating angular derivatives.** The angular approximation proposition holds for second-order fields on every compact spatial set. [`rotationApprox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRotationLeaves.lean#L440).

### Breakdown.FracCell.ReductionLossRowModeGradient

This file separates the row-mode estimate into cell angular energy, rotation differences and coefficient control, then sums the cell energies using almost disjointness and radius bounds. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Interface · Cell angular-energy interface.** This proposition requires the sum of the cell's squared row coefficients, weighted by the squared positive part of absolute mode minus one, to be bounded by the field's angular-gradient energy on that cell. [`CellAngularBoundStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L15).

**Interface providers.** [`Breakdown.CellCert.Reduction.cellAngularBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:173](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173); named premises: `RotationDifferenceStatement`, `RowRotationCoefEnergyStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.rowModeGradient_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L116) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:116](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L116); named reference in type).

**Interface · Weak-field rotation estimate interface.** This proposition requires second-order fields to satisfy the integral rotation-difference estimate on bounded measurable rotation-invariant sets, with the angle squared multiplying the angular-gradient energy. [`RotationDifferenceStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L22).

**Interface providers.** [`Breakdown.CellCert.Reduction.rotationDifference_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:110](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110); named premises: `RotationApproxStatement`, `RotationSmoothStatement`); [`Breakdown.CellCert.Reduction.rotationDifference`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L234) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:234](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L234); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.cellAngularBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:173](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173); named reference in type); [`Breakdown.CellCert.Reduction.rowModeGradient_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:183](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183); named reference in type).

**Interface · Rotation-to-coefficient interface.** This proposition requires any quadratic bound on the rotation differences of an L2 field on a row cell to bound its sum of row-coefficient squares weighted by the squared positive part of absolute mode minus one. [`RowRotationCoefEnergyStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L28).

**Interface providers.** [`Breakdown.CellCert.Reduction.rowRotationCoefEnergy`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L633) ([lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean:633](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L633); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.cellAngularBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:173](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173); named reference in type); [`Breakdown.CellCert.Reduction.rowModeGradient_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183) ([lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean:183](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183); named reference in type).

**Theorem · Axial motion in coordinate vectors.** The axial direction at a point is minus its second coordinate times the first unit vector plus its first coordinate times the second unit vector. [`axialTurn_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L37).

**Theorem · Angular gradients controlled by radius.** Applying a linear map to the axial direction has squared norm at most the horizontal radius squared times the map's entry-square energy. [`turn_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L42).

**Theorem · Matrix energy is nonnegative.** The sum of the squared entries of a linear map is nonnegative. [`entrySq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L65).

**Theorem · A cell radius bounds angular energy.** On a measurable set with horizontal radius bounded by ρ, the integral of the squared angular gradient is at most ρ squared times the integral of the gradient entry-square energy. [`cell_turn_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L68).

**Theorem · Almost disjoint cells share one energy.** The sum of the integrals of a nonnegative integrable function over finitely many measurable pairwise almost disjoint cells is at most its full-space integral. [`sum_cells_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L84).

**Theorem · Cell angular bounds supply row estimates.** The cell angular-energy proposition implies the row-mode gradient proposition. [`rowModeGradient_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L116).

**Theorem · Rotation control supplies cell energy.** The rotation-difference proposition and the rotation-to-coefficient energy proposition together imply the cell angular-energy proposition. [`cellAngularBound_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L173).

**Theorem · Rotation control gives row gradients.** The rotation-difference proposition and the rotation-to-coefficient energy proposition together imply the row-mode gradient proposition. [`rowModeGradient_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradient.lean#L183).

### Breakdown.FracCell.ReductionLossRowModeGradientParts

This file proves the weak-field rotation estimate and the coefficient bound using paired angular modes, orthogonality and an explicit inverse for the angular generator. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · The two axial rotation maps agree.** The turnBy map agrees pointwise with axialRotation for every angle. [`turnBy_eq_rotation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L19).

**Theorem · Axial turns preserve volume.** Every axial turn preserves spatial volume. [`turnBy_measurePreserving`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L23).

**Theorem · Restricted volume is rotation invariant.** An axial turn preserves volume restricted to any measurable rotation-invariant set. [`turnBy_measurePreserving_restrict`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L28).

**Theorem · Horizontal radius bounded by full radius.** The horizontal norm of a point is at most its full spatial norm. [`horizontalNorm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L37).

**Theorem · Squared norms as an L2 expression.** For an almost-everywhere strongly measurable field, its squared-norm integral equals the real conversion of its extended L2 norm squared. [`integral_sq_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L43).

**Reader note.** The totalized integral and ENNReal.toReal conventions do not by themselves assert that the field has finite L2 norm.

**Theorem · Opposite rotations cancel.** Turning by an angle and then by its negative returns the original point. [`turn_neg_cancel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L54).

**Theorem · The L2 pairing obeys Cauchy-Schwarz.** The square of the integral inner product of two L2 fields is at most the product of their squared-norm integrals. [`pair_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L63).

**Theorem · Rotational control of a pairing.** A quadratic rotation-difference bound for an L2 field on a measurable invariant set bounds the change in its pairing with a counter-rotated L2 test field by the same angle factor times the test field's squared norm. [`rotation_pair_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L84).

**Theorem · Smooth estimates pass to weak fields.** The smooth rotation proposition and the angular approximation proposition together imply the rotation-difference proposition for second-order fields. [`rotationDifference_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L110).

**Theorem · A pairing derivative inherits the bound.** Under a quadratic rotation-difference bound, the derivative at zero of the field's pairing with a counter-rotated L2 test field has square at most the bound constant times the test field's squared norm. [`rotation_deriv_sq_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L213).

**Theorem · Rotation control for second-order fields.** The integral rotation-difference proposition holds for second-order fields on bounded measurable rotation-invariant sets. [`rotationDifference`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L234).

**Definition · Projection onto the vertical axis.** The map qv retains the third coordinate of a spatial vector and sets its two horizontal coordinates to zero. [`qv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L241).

**Theorem · Rotation preserves vector sums.** Turning a sum of spatial vectors gives the sum of their turns. [`turn_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L243).

**Theorem · Rotation preserves scalar multiples.** Turning a real scalar multiple gives that scalar multiple of the turned vector. [`turn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L246).

**Theorem · Rotation preserves inner products.** Turning two vectors through the same angle leaves their inner product unchanged. [`turn_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L249).

**Theorem · Rotation fixes the zero vector.** An axial turn sends the zero vector to zero. [`turn_zero_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L252).

**Theorem · Axial motion commutes with rotation.** Applying axialTurn before or after an axial rotation gives the same vector. [`axialTurn_comm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L255).

**Theorem · Rotation and vertical projection commute.** Vertical projection commutes with every axial rotation. [`qv_comm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L259).

**Theorem · Axial motion preserves sums.** The axialTurn map preserves vector addition. [`axialTurn_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L263).

**Theorem · Axial motion preserves scalar multiples.** The axialTurn map preserves real scalar multiplication. [`axialTurn_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L267).

**Theorem · Vertical projection preserves sums.** The vertical projection qv preserves vector addition. [`qv_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L271).

**Theorem · Vertical projection preserves scaling.** The vertical projection qv preserves real scalar multiplication. [`qv_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L275).

**Theorem · The negative-angle rotation formula.** A negative-angle rotation decomposes into the unchanged vertical projection, cosine times the horizontal part and minus sine times the axial direction. [`turn_neg_formula`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L279).

**Theorem · The vertical projection norm bound.** The norm of the vertical projection is at most the norm of the original vector. [`qv_norm_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L284).

**Theorem · Vertical projection is continuous.** The vertical projection qv is a continuous map. [`qv_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L290).

**Theorem · Axial motion is continuous.** The axialTurn map is continuous. [`axialTurn_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L294).

**Theorem · Norm-decreasing maps preserve L2.** Composing an L2 field with a continuous map that never increases norms gives another L2 field. [`memLp_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L296).

**Theorem · Two L2 fields have integrable pairing.** The pointwise inner product of two L2 fields is integrable. [`int_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L300).

**Theorem · The spatial axis has zero volume.** Almost every spatial point has nonzero horizontal radius. [`axis_null`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L306).

**Predicate · A rotating harmonic pair.** A TurnPair of frequency n consists of two fields whose values under any axial turn obey the paired sine-cosine transformation law almost everywhere. [`TurnPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L322).

**Theorem · Zero fields form every turning pair.** Two zero fields satisfy the turning-pair law at every real frequency. [`pair_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L327).

**Theorem · Turning pairs are closed under addition.** Adding two turning pairs with the same frequency gives another pair at that frequency. [`pair_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L330).

**Theorem · Turning pairs are closed under scaling.** Multiplying both fields of a turning pair by the same real scalar preserves its frequency law. [`pair_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L336).

**Theorem · Exchanging the two turning partners.** Exchanging a turning pair's first and second fields while negating the new second field preserves the frequency law. [`pair_swap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L342).

**Theorem · Changing the sign of the frequency.** Negating the second field converts a turning pair of frequency minus n into one of frequency n. [`pair_neg_mode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L352).

**Theorem · Equivariant linear maps preserve pairs.** A real-linear map that commutes with axial rotations sends both fields of a turning pair to another pair with the same frequency. [`pair_comp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L363).

**Theorem · Finite sums preserve a turning frequency.** A finite sum of turning pairs at one common frequency again satisfies that frequency's turning-pair law. [`pair_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L373).

**Theorem · Derivative of a mixed trigonometric form.** At zero angle, the derivative of the displayed four-term sine-cosine expression is m times its cosine-sine coefficient plus n times its sine-cosine coefficient. [`trig_hasDerivAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L383).

**Theorem · Integrating four weighted terms.** The integral of a linear combination of four integrable scalar functions is the same linear combination of their integrals. [`int_lin4`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L395).

**Theorem · Integrating six weighted terms.** The integral of a linear combination of six integrable scalar functions is the same linear combination of their integrals. [`int_lin6`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L407).

**Theorem · Integrals on rotation-invariant sets.** Composing a scalar function with an axial turn leaves its integral over a measurable rotation-invariant set unchanged. [`inv_integral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L423).

**Theorem · The invariant pairing transformation law.** The inner-product integral of two L2 turning pairs on a measurable invariant set equals its four-term sine-cosine expansion after any common rotation. [`pair_inner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L427).

**Theorem · Distinct squared modes have zero pairing.** On a measurable rotation-invariant set, L2 turning pairs with different squared frequencies have zero inner-product integral between the first field of one pair and the second field of the other. [`pair_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L451).

**Theorem · Orthogonality of distinct turning modes.** On a measurable rotation-invariant set, the first fields of two L2 turning pairs with different squared frequencies have zero inner-product integral. [`pair_orth'`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L484).

**Theorem · Differentiating a turning-pair test.** At zero angle, the derivative of pairing an L2 field with a counter-rotated turning-pair field is minus its pairing with the axial direction of that field, minus the frequency times its pairing with the partner. [`pair_dual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L493).

**Theorem · A quadratic block estimate.** For nonnegative α and β summing to t and γ squared at most αt, the displayed combination of a vector, an axial direction and a vertical projection has squared norm at most αt times the first squared norm plus βt times the second. [`block_pt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L548).

**Theorem · Inverting the angular pair combination.** For frequency at least two, the displayed rational combinations of two vectors, their axial directions and vertical projections reconstruct the second vector through the angular generator. [`gen_identity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L556).

**Theorem · The norm of an orthonormal combination.** For a finite L2 family with identity Gram matrix, the squared-norm integral of a real linear combination is the sum of the coefficient squares. [`norm_comb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L564).

**Theorem · Squared norms add for orthogonal fields.** For a finite pairwise L2-orthogonal family, the squared-norm integral of the sum is the sum of the squared-norm integrals. [`norm_sum_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L590).

**Theorem · Replacing a frequency by its magnitude.** A turning pair can be expressed at the absolute value of its frequency by changing the partner's sign when the original frequency is negative. [`pair_abs`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L611).

**Theorem · Angular block combinations remain in L2.** A real linear combination of an L2 field, the axial direction of another L2 field and the first field's vertical projection remains in L2. [`memLp_lin3`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L620).

**Theorem · Rotation controls row coefficient energy.** The rotation-to-coefficient energy proposition holds for valid turning rows and L2 fields on their cells. [`rowRotationCoefEnergy`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L633).

**Theorem · The row-mode gradient estimate.** The row-mode gradient proposition holds for valid turning rows and second-order fields. [`rowModeGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossRowModeGradientParts.lean#L859).

### Breakdown.FracCell.ReductionLossStrainLoss_of_opNorm

This file obtains the strain-loss quadratic estimate directly from a uniform bound on the strain-error operator norm. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · An operator bound supplies strain loss.** A uniform operator-norm bound on the strain error, no larger than the declared strain-loss constant, bounds its quadratic form by that constant times the vector norm squared. [`strainLoss_of_opNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossStrainLoss_of_opNorm.lean#L15).

### Breakdown.FracCell.ReductionLossSupNorm

This file proves the supremum-norm statement by smoothing weak derivatives and controlling cutoff errors with L6 tails, starting from a pointwise inequality for smooth fields. **Reading context:** Appendix B: the norm, rotation and product estimates used for the profile-change and quadratic adjoint bounds (B.9–B.10).

**Theorem · Convex powers pass through smoothing.** If the norm to an integer power at least one is dominated by an integrable function, its value after normalized bump smoothing is bounded by the smoothing of that norm power. [`normPow_conv_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L19).

**Theorem · A bound for nonnegative integral sums.** For finitely many nonnegative scalar functions whose pointwise sum is bounded by an integrable function, the sum of their integrals is at most that majorant's integral. [`sum_integral_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L79).

**Theorem · Smoothing a column-energy bound.** A pointwise bound on the sum of three squared column norms passes through normalized bump convolution. [`conv_sum_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L94).

**Theorem · Smoothing commutes with the column sum.** Normalized bump convolution commutes with the sum of three locally integrable vector fields. [`conv_sum_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L108).

**Theorem · Smoothing recovers each weak derivative.** For a locally integrable field satisfying the scalar-test weak-gradient identities, the coordinate derivatives of its normalized bump smoothing are the smoothed weak-gradient columns. [`mollify_fderiv_apply`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L121).

**Theorem · L6 means an integrable sixth power.** For an almost-everywhere strongly measurable field, membership in L6 is equivalent to integrability of its sixth norm power. [`memLp_six_iff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L153).

**Theorem · The L6 mass of distant tails vanishes.** The L6 norm of an L6 field restricted to points of radius at least n plus one tends to zero. [`tail_tendsto`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L159).

**Theorem · The coordinate derivative product rule.** For differentiable scalar and vector fields, a coordinate derivative of their product is the scalar derivative times the vector field plus the scalar times the vector derivative. [`pd_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L190).

**Theorem · Coordinate derivatives preserve addition.** A coordinate derivative of the sum of two differentiable vector fields is the sum of their coordinate derivatives. [`pd_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L199).

**Theorem · The Laplacian product expansion.** For smooth scalar and vector fields, the sum of second coordinate derivatives of their product splits into the scalar Laplacian term, twice the mixed derivative sum and the vector Laplacian term. [`second_sum_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L206).

**Theorem · Second derivatives of a local constant.** If a scalar function is constant near a point, each second coordinate derivative at that point is zero. [`pd_pd_eq_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L226).

**Theorem · The coordinate derivative scaling rule.** Scaling a scalar function's input and output scales its coordinate derivative by the product of the two scale factors. [`pd_scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L237).

**Theorem · Uniform derivative bounds for cutoffs.** One nonnegative constant bounds every positive-radius cutoff's first derivative by that constant divided by the radius, and its Laplacian magnitude by that constant divided by the radius squared. [`cutoff_bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L251).

**Theorem · An annular L2 bound from an L6 tail.** A bounded scalar multiplier supported between radii R and 2R turns the L6 tail norm of a continuous field into the displayed L2 bound, with the multiplier bound, radius and unit-ball volume factors. [`annulus_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L279).

**Theorem · The L2 norm of a real function.** For a real L2 function, its extended L2 norm is the nonnegative-real embedding of the square root of the integral of its square. [`eLpNorm_two_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L334).

**Theorem · The column-energy triangle inequality.** The square root of the sum of squared norms of three vector sums is at most the sum of the corresponding two square roots. [`sqrt_sum_add_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L343).

**Theorem · A smooth field has continuous Laplacian.** The sum of second coordinate derivatives of a smooth vector field is continuous. [`continuous_second_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L350).

**Theorem · Pointwise control by derivative energies.** A smooth L6 field with integrable gradient-square and Laplacian-square energies has its squared value at every point bounded by 1 divided by 2π times the square roots of those two energies. [`smooth_bound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L356).

**Theorem · The supremum estimate for weak fields.** The supremum-norm proposition holds, bounding second-order fields by their first- and second-derivative energies with the stated constant. [`supNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionLossSupNorm.lean#L599).

### Breakdown.FracCell.ReductionPointwiseDefs

This file declares the polynomial-extension, scalar-weight and pointwise-mode interfaces, together with the finite model-support package used to formulate interaction coverage. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Interface · Weighted orthogonal-family interface.** This proposition requires the constructed polynomial family on a nondegenerate interval with continuous nonnegative weight positive in its interior to have exact degree n, positive leading coefficient and identity weighted Gram matrix. [`OrthoFamilyStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L17).

**Interface providers.** [`Breakdown.CellCert.Reduction.orthoFamily_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L158) ([lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean:158](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L158); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.Reduction.ExtendBasesInternal.family_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L92) ([lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean:92](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L92); named reference in type); [`Breakdown.CellCert.Reduction.extendBases_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L111) ([lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean:111](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L111); named reference in type).

**Interface · Basis-extension interface.** This proposition requires the extension of valid finite radial and height bases on a valid cell box to be a full cell basis while preserving every supplied coefficient through the prescribed degree. [`ExtendBasesStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L23).

**Interface providers.** [`Breakdown.CellCert.Reduction.extendBases_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L111) ([lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean:111](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L111); named premises: `OrthoFamilyStatement`).

**Theorems using this interface name.** None found in the library.

**Definition · Completing the face test polynomials.** The extended face segment retains its existing test coefficients through degree D and uses coefficients of the constant-weight orthogonal family on the segment for higher degrees. [`extendSegment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L30).

**Interface · Face-segment extension interface.** This proposition requires valid segment geometry and nonzero supplied leading coefficients through degree D to yield a valid extended face segment preserving all supplied coefficients through D. [`ExtendSegmentStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L34).

**Reader note.** The supplied source slice has no exact named provider or consumer of this proposition; this is a declared interface, not a proved result in this file.

**Interface providers.** No theorem with this exact named interface as its result was found in the library.

**Theorems using this interface name.** None found in the library.

**Interface · Scalar weight requirements interface.** This proposition requires valid weight forms and tests to provide mode separation, positive bounded energy weights, nonnegative bounded vorticity weights, sign symmetry, tail-shift support and the stated lower and upper bounds for symmetric, antisymmetric and velocity weights. [`WeightClausesStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L45).

**Interface providers.** [`Breakdown.CellCert.Reduction.weightClauses_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L113) ([lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean:113](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L113); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Interface · Unresolved-mode inequality interface.** This proposition requires the density form minus the supremum and applicable penalty losses, combined with curl and strain absorption, to be nonnegative for every unresolved mode and compatible trace-free matrix and vector away from the axis. [`UnresolvedPointwiseStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L69).

**Interface providers.** [`Breakdown.CellCert.Reduction.unresolvedPointwise_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L97) ([lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean:97](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L97); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Interface · Resolved-mode inequality interface.** This proposition requires the local matrix form to lie below the density form and the absorbed pair loss to be nonnegative for resolved modes, under valid weight and resolved tests and the stated pointwise trace-free conditions. [`ResolvedPointwiseStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L79).

**Interface providers.** [`Breakdown.CellCert.Reduction.resolvedPointwise_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L96) ([lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean:96](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L96); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** None found in the library.

**Structure · Finite support of model harmonics.** This structure records a finite set outside which the model velocity, curl, strain and curl-gradient modes all vanish in the interior of the cell away from the axis. [`ModelModes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L88).

**Interface · Model interaction cover interface.** This proposition requires a finite model-support cover to place every nonzero interaction between a resolved mode and a mode outside the resolved set and band into one of the declared classes. [`ClassCoverStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseDefs.lean#L94).

**Reader note.** There is no exact named provider or consumer in the supplied slice; GivenModelCover.classCover_of is a specialized analogue with mesh, model and harmonic-cover assumptions, not a proof of this generic interface.

**Interface providers.** No theorem with this exact named interface as its result was found in the library.

**Theorems using this interface name.** None found in the library.

### Breakdown.FracCell.ReductionPointwiseExtendBases_of

This file proves that an orthonormal finite prefix can be joined to the constructed higher-degree polynomial family, yielding radial and height basis extension without changing supplied coefficients. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Theorem · Integrating a polynomial expansion.** For continuous weight and test function, integrating their product with a finite polynomial expansion equals the corresponding finite sum of weighted moments. [`integral_sum_mul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L17).

**Theorem · Orthogonal polynomials' lower moments.** In a weighted orthonormal polynomial family with nonzero leading coefficients, the degree-j polynomial has zero weighted moments against all monomials of lower degree. [`moment_vanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L31).

**Theorem · Lower-degree polynomials are orthogonal.** A polynomial of degree at most n has zero weighted pairing with a higher-index member of an orthonormal polynomial family with nonzero leading coefficients. [`cross_zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L50).

**Theorem · Joining orthogonal polynomial families.** Replacing the first D plus one members of an orthonormal polynomial family by another orthonormal family of the matching bounded degrees preserves orthonormality of the combined family. [`extend_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L65).

**Theorem · Evaluating the degree-indexed family.** If each constructed orthogonal polynomial has degree equal to its index, its evaluation equals the finite sum of its coefficients through that index times the corresponding powers. [`eval_family`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L87).

**Theorem · Orthogonal-family coefficient tests.** The orthogonal-family proposition supplies positive leading coefficients and identity weighted integrals for the explicit coefficient expansions under the stated interval and weight assumptions. [`family_orth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L92).

**Theorem · Inserting a constant integration weight.** The integral of a product over a closed interval is unchanged by explicitly inserting the constant weight one. [`weight_one_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L104).

**Theorem · Orthogonal families extend cell bases.** The weighted orthogonal-family proposition implies the cell-basis extension proposition. [`extendBases_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseExtendBases_of.lean#L111).

### Breakdown.FracCell.ReductionPointwiseOrthoFamily

This file verifies the weighted polynomial Gram-Schmidt construction, proving positivity of its norm, exact degrees and full orthonormality. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Lemma · Integrability of weighted polynomials.** A weight continuous on a closed interval makes the product of that weight with two polynomial evaluations integrable on the interval. [`pair_integrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L13).

**Lemma · Symmetry of the polynomial pairing.** Exchanging the two polynomials leaves their weighted interval pairing unchanged. [`pair_comm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L19).

**Lemma · The pairing distributes over subtraction.** For a continuous interval weight, subtracting in the first polynomial argument subtracts the corresponding weighted pairings. [`pair_sub_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L26).

**Lemma · Scaling a polynomial pairing.** Scaling the first polynomial by a real number scales its weighted interval pairing by that number. [`pair_smul_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L36).

**Lemma · The pairing distributes over finite sums.** For a continuous interval weight, pairing a finite sum of polynomials equals the sum of their weighted pairings. [`pair_sum_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L45).

**Lemma · Positive weighted polynomial norms.** On a nondegenerate interval with continuous nonnegative weight positive in the interior, every nonzero polynomial has strictly positive weighted self-pairing. [`pair_self_pos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L54).

**Lemma · The normalized orthogonalization step.** The nth family polynomial is the monomial of degree n minus its projections on earlier family members, divided by the square root of that remainder's weighted self-pairing. [`family_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L82).

**Lemma · One orthogonalization step.** If the earlier family members have their expected degrees and are orthonormal, the next member has its expected degree, positive leading coefficient, zero pairing with every earlier member and unit self-pairing. [`family_step`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L93).

**Lemma · From triangular to full orthogonality.** For two family members each orthogonal to its predecessors and of unit weighted norm, their weighted pairing is one when their indices agree and zero otherwise. [`delta_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L143).

**Theorem · The weighted orthogonal-family theorem.** The constructed polynomial family satisfies the degree, positive-leading-coefficient and orthonormality requirements of the weighted orthogonal-family proposition. [`orthoFamily_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseOrthoFamily.lean#L158).

### Breakdown.FracCell.ReductionPointwiseResolvedPointwise_of

This file reduces the resolved-mode pointwise inequalities to endpoint bounds and a scaled cross-term estimate, then verifies the full resolved-pointwise interface. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Theorem · Evaluation of the scalar strain matrix.** The sesquilinear form of the scalar strain matrix on a matrix-vector pair equals its scalar coefficient times the matrix's squared-entry sum. [`sesq_scalar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L7).

**Theorem · The matrix squared norm is nonnegative.** The squared-entry sum of a complex matrix is nonnegative. [`sumSq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L26).

**Theorem · The curl square is nonnegative.** The curl-square expression of a complex matrix is nonnegative. [`curlSq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L30).

**Theorem · The vector squared norm is nonnegative.** The squared-entry sum of a complex vector is nonnegative. [`vecSq_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L34).

**Theorem · A linear value is bounded by endpoints.** Multiplying a real number lying between two endpoints by any fixed scalar is at most the larger endpoint product. [`lin_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L38).

**Theorem · Splitting a cross term by scale.** For a positive scale l, twice a real product is at most l times the first square plus the second square divided by l. [`two_mul_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L44).

**Theorem · Scalar absorption for resolved modes.** The displayed radius bounds, nonnegativity assumptions and absorption bounds make the resolved scalar loss expression nonnegative after curl, strain and velocity absorption. [`hbase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L50).

**Theorem · The resolved pointwise estimates.** The resolved pointwise proposition follows from the valid weight form, weight tests and resolved tests specified in that proposition. [`resolvedPointwise_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseResolvedPointwise_of.lean#L96).

### Breakdown.FracCell.ReductionPointwiseUnresolvedPointwise_of

This file uses the angular-action lower bound to control velocity by matrix quantities and proves the unresolved-mode pointwise absorption inequality. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Lemma · Angular action controls vector size.** For a frequency of magnitude at least one, the squared norm of its angular action on a complex vector is at least the vector's squared norm times the squared difference between the frequency magnitude and one. [`turn_lower`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L15).

**Lemma · A linear value is bounded by endpoints.** For a radius between two endpoints, its product with a fixed scalar is at most the larger endpoint product. [`lin_range`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L35).

**Lemma · Scalar absorption for unresolved modes.** Under the displayed radius, frequency, product and penalty bounds, the unresolved scalar error is nonnegative after the prescribed curl and strain absorption terms are added. [`hbase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L41).

**Lemma · Integer magnitude agrees after coercion.** Coercing an integer's natural-number absolute value to the reals gives the absolute value of that integer's real coercion. [`natAbs_real`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L94).

**Theorem · The unresolved pointwise estimate.** The unresolved pointwise proposition follows from the valid weight form and weight tests specified in that proposition. [`unresolvedPointwise_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseUnresolvedPointwise_of.lean#L97).

### Breakdown.FracCell.ReductionPointwiseWeightClauses_of

This file converts finite weight tests into the full family of mode and polynomial-degree inequalities, using monotonicity, sign symmetry and endpoint control. **Reading context:** Appendix B: polynomial bases and resolved or unresolved pointwise cell bounds supporting B.4.

**Theorem · The nonnegative mode number formula.** The mode number is the real absolute value of the integer mode, represented through natAbs, times the rotational order. [`mode_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L15).

**Theorem · Opposite modes have the same size.** Negating an integer mode leaves its mode number unchanged. [`mode_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L19).

**Theorem · The tested upper radius is nonnegative.** A valid cell box and valid weight tests make the upper radial testing parameter nonnegative. [`rHi_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L22).

**Theorem · The strain bound decreases with mode.** Under valid cell and weight tests, the strain-bound expression is nonincreasing in its frequency argument above one, for either Boolean branch. [`strainAt_anti`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L31).

**Theorem · A valid inner radius is nonnegative.** The inner radius of a valid cell box is nonnegative. [`inner_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L54).

**Theorem · Radial eigenvalues increase with degree.** Increasing the radial degree cannot decrease the radial eigenvalue of a cell box. [`radial_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L60).

**Theorem · Height eigenvalues increase with degree.** Increasing the height degree cannot decrease the height eigenvalue of a cell box. [`height_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L68).

**Theorem · Tail eigenvalue monotonicity.** For a valid cell box, increasing either polynomial degree cannot decrease the combined tail eigenvalue. [`tail_mono`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L74).

**Theorem · Angular weights are nonnegative.** Every mode's angular weight is nonnegative on a valid cell box. [`ang_nonneg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L79).

**Theorem · Nonzero modes use the angular constant.** For a nonzero integer mode, the cell's angular weight equals its angular constant. [`ang_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L87).

**Theorem · Increasing the tail-plus-angular bound.** For a valid cell and nonnegative multiplier, increasing the mode argument and moving from zero to arbitrary polynomial degrees cannot decrease the displayed tail-plus-angular expression. [`prod_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L91).

**Theorem · Adding nonnegative angular energy.** For a valid cell and nonnegative multiplier, adding the nonnegative angular-weight square cannot decrease the weighted tail eigenvalue. [`res_le`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L100).

**Theorem · From integer magnitude to mode size.** A natural-number lower bound on an integer mode's absolute value yields that lower bound times the order as a lower bound for its mode number. [`mode_ge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L104).

**Theorem · The scalar weight requirements hold.** The full scalar weight-clauses proposition follows from the valid cell geometry, weight form and finite weight tests specified in that proposition. [`weightClauses_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ReductionPointwiseWeightClauses_of.lean#L113).

### Breakdown.FracCell.RelAxis

This file translates zero-mode flux identities on axis-touching cells into finite relation rows, using weighted polynomial expansions and evaluations on true field data. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Interface · Weighted axis integrability interface.** This proposition requires every gradient-mode entry of a second-order field, multiplied by the radial coordinate, to be integrable on each closed radial-height rectangle starting at the axis. [`AxisModeIntegrableStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L11).

**Interface providers.** [`Breakdown.CellCert.CellFormula.axisModeIntegrable`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisModeIntegrable.lean#L27) ([lean/Breakdown/FracCell/AxisModeIntegrable.lean:27](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisModeIntegrable.lean#L27); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CellCert.CellFormula.axisFlux_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91) ([lean/Breakdown/FracCell/AxisFlux.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:413](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:420](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420); named reference in type); [`Breakdown.CellCert.CellFormula.RelAxisInternal.relAxis_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L279) ([lean/Breakdown/FracCell/RelAxis.lean:279](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L279); named reference in type); [`Breakdown.CellCert.CellFormula.relAxis_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L333) ([lean/Breakdown/FracCell/RelAxis.lean:333](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L333); named reference in type).

**Interface · Zero-mode axis flux interface.** This proposition requires the weighted outer radial strip moment of each horizontal zero-mode component to equal the displayed radial and angular gradient-mode integrals on a rectangle starting at the axis. [`AxisFluxStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L17).

**Interface providers.** [`Breakdown.CellCert.CellFormula.axisFlux_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91) ([lean/Breakdown/FracCell/AxisFlux.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91); named premises: `AngularModeStatement`, `AxisModeIntegrableStatement`, `CellFormula.ModeRadialPartsStatement`).

**Theorems using this interface name.** [`Breakdown.CellCert.CellFormula.relationsHold_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:265](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L265); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:413](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:420](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420); named reference in type); [`Breakdown.CellCert.CellFormula.RelAxisInternal.relAxis_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L279) ([lean/Breakdown/FracCell/RelAxis.lean:279](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L279); named reference in type); [`Breakdown.CellCert.CellFormula.relAxis_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L333) ([lean/Breakdown/FracCell/RelAxis.lean:333](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L333); named reference in type).

**Lemma · Radial basis polynomials are continuous.** Each radial basis polynomial is continuous on the real line. [`radialPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L31).

**Lemma · Height basis polynomials are continuous.** Each height basis polynomial is continuous on the real line. [`heightPoly_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L35).

**Lemma · Radial polynomials span each monomial.** If all radial leading coefficients are positive, the monomial of degree i lies in the span of the radial basis polynomials through degree i. [`pow_mem_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L39).

**Lemma · The radial line weight is continuous.** The cell box's radial line-weight function is continuous. [`lineWeight_continuous`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L58).

**Lemma · Expansion in an orthonormal radial basis.** A function in the span of the radial basis through degree Q is continuous and equals the sum of those basis functions weighted by its line-weighted integral pairings. [`expand_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L64).

**Lemma · Radial expansion of an axis monomial.** For a valid cell basis whose lower radius is zero, any monomial of degree at most Q equals its radius-weighted expansion in radial basis functions through Q. [`pow_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L109).

**Lemma · Expanding a radius-weighted mode moment.** For an axis-touching cell with valid bases and an integrable radius-weighted complex function, the indicated linear combination of its coefficients equals its radial-monomial and height-polynomial moment. [`coef_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L126).

**Lemma · Differentiating a radius-weighted power.** The derivative of r times r to the power i is i plus one times r to the power i. [`deriv_rpow_succ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L153).

**Lemma · A coordinate row reads one datum.** Pairing a unit coordinate row with a data vector returns the selected datum. [`ev_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L161).

**Lemma · Subtracting row evaluations.** Evaluating the difference of two rows against a data vector gives the difference of their evaluations. [`ev_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L164).

**Lemma · Negating a row negates its evaluation.** Evaluating a negated row against a data vector gives the negative of the original evaluation. [`ev_neg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L168).

**Lemma · Scaling a row scales its evaluation.** Evaluating a complex scalar multiple of a row against data scales the row's evaluation by that scalar. [`ev_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L171).

**Lemma · Row evaluation commutes with finite sums.** Evaluating a finite sum of rows against data gives the sum of their evaluations. [`ev_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L176).

**Lemma · Strain rows read gradient coefficients.** Within the stored coefficient degrees, evaluating a strain-coordinate row on true field data gives the corresponding gradient-mode basis coefficient. [`ev_strain`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L181).

**Lemma · An extra row reads its strip datum.** Within the stored degree range, evaluating an extra-coordinate row on true field data gives the corresponding extra value. [`ev_extra`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L188).

**Lemma · The selected zero mode has value zero.** If the layout's zero-mode option selects a mode, that mode's underlying integer is zero. [`zeroMode_val`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L195).

**Lemma · From flux to a coefficient relation.** On an axis-touching cell with valid bases, the displayed flux identity and weighted integrability make the outer flux minus its two finite radial coefficient expansions vanish. [`hbase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L205).

**Lemma · Strain rows read coefficient sums.** Evaluating a weighted finite sum of strain rows on true field data gives the same weighted sum of gradient-mode coefficients. [`ev_strain_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L259).

**Lemma · Negated strain rows read negated modes.** Evaluating the weighted sum of negated strain rows on true data gives the weighted basis coefficients of the negated gradient mode. [`ev_negstrain_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L266).

**Theorem · Each axis relation annihilates true data.** Assuming axis-weighted mode integrability and the zero-mode axis flux identity, every axis relation row of a valid cell layout evaluates to zero on admissible true field data. [`relAxis_main`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L279).

**Theorem · Axis flux supplies relation rows.** The axis-mode integrability and axis-flux propositions together imply the axis-relation proposition. [`relAxis_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelAxis.lean#L333).
<!-- /passage:front -->

