
<!-- passage:front -->
# Library guide 21: Breakdown/FracCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) **21** [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCell.RelHeightCoef` to `Breakdown.FracCell.SharpYDensityRegular` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCell.RelHeightCoef

This file derives the height polynomial eigenvalue equation and uses height-mode integration by parts to express velocity coefficients through vertical-gradient coefficients, proving the corresponding relation rows. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · The polynomial from one coefficient row.** The polynomial hp at degree l is the finite coefficient sum through l for the supplied height coefficient array. [`hp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L18).

**Theorem · Evaluating the coefficient polynomial.** Evaluating hp gives the finite sum of its supplied coefficients times the corresponding real powers. [`hp_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L20).

**Theorem · The height polynomial has bounded degree.** The natural degree of hp at index l is at most l. [`hp_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L23).

**Theorem · The indexed coefficient is preserved.** The coefficient of degree l in hp at index l is the supplied diagonal coefficient. [`hp_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L29).

**Theorem · Nonzero leading terms give a basis.** If every diagonal coefficient is nonzero, every polynomial of degree at most d is a linear combination of the coefficient polynomials through d. [`span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L34).

**Theorem · Pairings recover expansion coefficients.** For an orthonormal height polynomial family, pairing a polynomial's finite expansion with a basis member returns its coefficient within the expansion range and zero beyond it. [`pair_of_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L74).

**Definition · The height endpoint-vanishing polynomial.** The polynomial zp is the quadratic polynomial equal to one minus the square of the affine height coordinate mapping the interval endpoints to minus one and one. [`zp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L87).

**Theorem · The normalized height weight formula.** Evaluating zp at z gives one minus the square of (2z minus the endpoint sum) divided by the interval width. [`zp_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L91).

**Theorem · The height weight at the lower endpoint.** For an increasing height interval, zp vanishes at its lower endpoint. [`zp_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L95).

**Theorem · The height weight at the upper endpoint.** For an increasing height interval, zp vanishes at its upper endpoint. [`zp_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L100).

**Theorem · The height weight is at most quadratic.** The natural degree of zp is at most two. [`zp_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L105).

**Theorem · Quadratic height-weight coefficient.** The quadratic coefficient of zp is minus the square of two divided by the interval width. [`zp_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L109).

**Definition · A weighted height polynomial derivative.** The polynomial gp is the endpoint-vanishing height weight zp multiplied by the derivative of hp. [`gp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L114).

**Definition · The height operator polynomial.** The polynomial tp is the negative derivative of the weighted derivative polynomial gp. [`tp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L117).

**Theorem · Degree of the weighted height derivative.** The natural degree of gp at index l is at most l plus one. [`gp_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L119).

**Theorem · Degree bound for the height operator.** The natural degree of tp at index l is at most l. [`tp_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L129).

**Theorem · The leading height-operator coefficient.** For positive degree l, the degree-l coefficient of tp is l(l+1) times the squared interval scale times the supplied degree-l coefficient. [`tp_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L134).

**Theorem · Polynomial integration by parts.** If the product of two polynomials vanishes at both endpoints, the integral of the first times the derivative of the second is minus the integral of its derivative times the second. [`ibp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L148).

**Theorem · Lower-degree polynomial orthogonality.** In the orthonormal family with nonzero leading coefficients, a polynomial of degree at most d has zero interval pairing with every family member of index greater than d. [`orthog`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L158).

**Theorem · Recovering the height expansion.** In the orthonormal height family with nonzero leading coefficients, a polynomial of degree at most d equals its expansion through d with coefficients given by interval pairings. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L163).

**Theorem · The top pairing uses the leading term.** In the orthonormal height family, pairing a polynomial of degree at most positive l with the lth member depends only on its degree-l coefficient and the corresponding monomial moment. [`pair_lead`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L170).

**Theorem · Lower-mode orthogonality of the operator.** For an increasing height interval and the orthonormal family, the lth operator polynomial tp has zero pairing with each lower-index basis polynomial. [`tp_sym`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L198).

**Theorem · The height eigenvalue equation.** For an increasing interval and positive degree l, the orthonormal height polynomial is an eigenfunction of the negative weighted-derivative operator with eigenvalue l(l+1) times the squared interval scale. [`tp_eigen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L225).

**Theorem · Recovering a mode from its derivative.** For a positive-degree orthonormal height mode on an increasing interval, the polynomial equals minus the derivative of gp divided by its positive eigenvalue. [`hp_of_gp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L234).

**Theorem · Expanding the weighted height derivative.** If Q is at least l plus one, the weighted derivative gp at degree l equals its orthonormal height expansion through Q. [`gp_expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L246).

**Theorem · Height coefficients from derivatives.** Assuming height-mode integration by parts, a positive-height-degree velocity coefficient of a second-order field equals the displayed finite sum of vertical-gradient coefficients weighted by stiffness integrals divided by the height eigenvalue. [`coef_height`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L253).

**Theorem · Evaluating a subtracted row combination.** Pairing a row minus a weighted finite sum of rows with data equals the first evaluation minus the same weighted sum of row evaluations. [`pair_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L342).

**Theorem · A coordinate row reads one datum.** Pairing the layout's unit coordinate row with data returns the selected datum. [`pair_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L349).

**Theorem · Height rows annihilate true data.** Assuming height-mode integration by parts, each height-coefficient relation row of a valid layout evaluates to zero on true data from an admissible field. [`row_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L352).

**Theorem · Height integration gives relation rows.** The height-mode integration-by-parts proposition implies the height-coefficient relation proposition. [`relHeightCoef_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L384).

**Theorem · The height coefficient relation theorem.** The height-coefficient relation proposition holds. [`relHeightCoef_holds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightCoef.lean#L387).

### Breakdown.FracCell.RelHeightSide

This file rewrites upper and lower height strip data as interior moments and finite polynomial coefficient combinations, proving height-side relations from mode integrability and weak integration by parts. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Definition · A weighted rectangular moment.** The quantity J integrates a complex field over the cell rectangle against a real scalar test function. [`J`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L19).

**Theorem · The cell rectangle is compact.** Every closed radial-height cell rectangle is compact. [`rect_compact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L21).

**Theorem · Integrable fields with continuous tests.** Multiplying an integrable complex field on the cell rectangle by a continuous real test function preserves integrability there. [`term_int`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L23).

**Interface · Height weak integration interface.** This proposition requires admissible field modes and their vertical-gradient modes to be line-weight integrable and to satisfy the displayed height integration-by-parts identity for tests vanishing at both height endpoints. [`HeightPartsStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L27).

**Interface providers.** [`Breakdown.CellCert.CellFormula.RelHeightSideInternal.heightParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L37) ([lean/Breakdown/FracCell/RelHeightSide.lean:37](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L37); named premises: `HeightModeIbpStatement`, `ModeIntegrableStatement`).

**Theorems using this interface name.** [`_private.Breakdown.FracCell.RelHeightSide.0.Breakdown.CellCert.CellFormula.relHeightSide_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L287) ([lean/Breakdown/FracCell/RelHeightSide.lean:287](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L287); named reference in type).

**Theorem · Mode facts supply height integration.** The height-mode integration-by-parts proposition and mode-integrability proposition together imply the height weak-integration proposition. [`heightParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L37).

**Theorem · Adding tests inside a moment.** For an integrable complex field and continuous real tests, the moment of the sum of two tests is the sum of their moments. [`J_add`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L68).

**Theorem · Scaling a test scales its moment.** Multiplying a real test by a real scalar multiplies its rectangular moment by that scalar viewed as a complex number. [`J_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L77).

**Theorem · Two-term linearity of moments.** For an integrable complex field and continuous real tests, taking a rectangular moment commutes with a real linear combination of two tests. [`J_lin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L86).

**Theorem · Three-term linearity of moments.** For an integrable complex field and continuous real tests, taking a rectangular moment commutes with a real linear combination of three tests. [`J_lin3`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L92).

**Theorem · Summing tests inside a moment.** For an integrable complex field and continuous real tests, the moment of a finite sum is the sum of the moments. [`J_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L99).

**Theorem · Radial basis polynomials are continuous.** Every radial basis polynomial is continuous. [`radial_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L109).

**Theorem · Height basis polynomials are continuous.** Every height basis polynomial is continuous. [`height_cont`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L113).

**Definition · The finite height polynomial projection.** The projection onto height degrees through D is the sum of the height basis functions weighted by the test function's unweighted interval pairings with them. [`proj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L117).

**Theorem · Height projection on its own span.** For valid cell bases, every function in the span of the first D plus one height polynomials is continuous and equals its finite height projection everywhere. [`proj_span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L120).

**Theorem · Height polynomials span monomials.** Positive height leading coefficients ensure that every monomial of degree at most D belongs to the span of height basis functions through D. [`pow_mem`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L158).

**Theorem · The derivative function of a monomial.** The derivative function of z to the natural power m is m times z to the natural power m minus one. [`deriv_pow_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L180).

**Theorem · Subtracting row evaluations.** Evaluating the difference of two rows against data gives the difference of their evaluations. [`pair_sub`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L185).

**Theorem · Scaling a row scales its evaluation.** Evaluating a complex scalar multiple of a row scales its evaluation by the same scalar. [`pair_smul`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L189).

**Theorem · Row evaluation preserves finite sums.** Evaluating a finite sum of rows against data gives the sum of their evaluations. [`pair_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L193).

**Theorem · A coordinate row reads one datum.** Pairing a unit coordinate row with a data vector returns the selected datum. [`pair_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L198).

**Theorem · An extra row reads its boundary datum.** Within the stored degree range, evaluating an extra-coordinate row on true field data returns the corresponding extra value. [`pair_extra`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L202).

**Theorem · Velocity row sums read coefficient sums.** Within the stored velocity-degree range, a weighted sum of velocity-row evaluations on true data equals the same weighted sum of velocity-mode coefficients. [`sum_vel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L209).

**Theorem · Strain rows read vertical coefficients.** Within the stored strain-degree range, a weighted sum of vertical strain-row evaluations on true data equals the same weighted sum of vertical-gradient mode coefficients. [`sum_strain`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L218).

**Theorem · The upper-height extra value.** The extra datum indexed by three is the upper-height strip moment with radial basis test multiplied by the cell's radial line weight. [`extra_three`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L227).

**Theorem · The lower-height extra value.** The extra datum indexed by two is the lower-height strip moment with radial basis test multiplied by the cell's radial line weight. [`extra_two`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L234).

**Theorem · The two line-weight formulas agree.** The piecewise weight equal to radius for an axis-touching box and one otherwise is the cell box's line-weight function. [`weight_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L241).

**Theorem · Interior formula for the upper strip.** For an increasing height interval and the stated weighted integrability, the upper strip moment splits into a normalized field moment and a vertical-gradient moment weighted by height above the lower endpoint. [`strip_top`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L245).

**Theorem · Interior formula for the lower strip.** For an increasing height interval and the stated weighted integrability, the lower strip moment splits into a normalized field moment and a vertical-gradient moment weighted by height relative to the upper endpoint. [`strip_bottom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L262).

**Theorem · Weak integration gives height-side rows.** The height weak-integration proposition implies the height-side relation proposition. [`relHeightSide_of_parts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L287).

**Theorem · Height mode facts supply side relations.** The height-mode integration-by-parts and mode-integrability propositions together imply the height-side relation proposition. [`relHeightSide_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelHeightSide.lean#L418).

### Breakdown.FracCell.RelRadialCoef

This file derives the radial polynomial eigenvalue equation in both axis-touching and annular cells, then uses radial integration by parts to prove finite velocity-gradient coefficient relations. **Reading context:** Appendix B: weak cylindrical modes, side traces and coefficient relations used to construct the cell data in B.4.

**Interface · Radial weak integration interface.** This proposition requires an L6 field with measurable finite-energy weak gradient to have the stated weighted radial-mode integrability and radial integration-by-parts identity for continuously differentiable tests vanishing at both radial endpoints. [`ModeRadialPartsStatement`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L15).

**Interface providers.** [`Breakdown.CellCert.CellFormula.modeRadialParts_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:267](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L267); named premises: `ModeRadialFormulaStatement`, `ModeVecRectIntegrableStatement`); [`Breakdown.CellCert.CellFormula.modeRadialParts_of_vec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L650) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:650](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L650); named premises: `ModeVecRectIntegrableStatement`); [`Breakdown.CellCert.CellFormula.modeRadialParts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L782) ([lean/Breakdown/FracCell/ModeRadialPartsF.lean:782](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/ModeRadialPartsF.lean#L782); no additional named Statement/Holds premise in its displayed declaration).

**Theorems using this interface name.** [`Breakdown.CertCell.LocalField.localRelRadialCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L18) ([lean/Breakdown/CertCell/LocalRelationsA.lean:18](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L18); named reference in proof body); [`Breakdown.CellCert.CellFormula.axisFlux_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91) ([lean/Breakdown/FracCell/AxisFlux.lean:91](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/AxisFlux.lean#L91); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:413](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L413); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:420](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L420); named reference in type); [`Breakdown.CellCert.CellFormula.relationsHold_of_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L467) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:467](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L467); named reference in type); [`Breakdown.CellCert.CellFormula.shiftedParam_of_core`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L473) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:473](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L473); named reference in type); [`Breakdown.CellCert.CellCoordinates.cellBound_of_leaves`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L506) ([lean/Breakdown/FracCell/CellAnalysisAssembly.lean:506](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellAnalysisAssembly.lean#L506); named reference in type); [`Breakdown.CellCert.CellFormula.relRadialCoef_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L397) ([lean/Breakdown/FracCell/RelRadialCoef.lean:397](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L397); named reference in type).

**Definition · The radial coefficient polynomial.** The polynomial poly at index j is the finite sum of radial coefficients through j multiplied by the corresponding powers of the polynomial variable. [`poly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L31).

**Theorem · Evaluating the radial polynomial.** Evaluating the coefficient polynomial at a real radius gives the corresponding radial basis function. [`poly_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L33).

**Theorem · Radial bases as polynomial functions.** The radial basis function equals the evaluation function of its coefficient polynomial. [`poly_fun`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L36).

**Theorem · The radial polynomial coefficients.** The degree-n coefficient of the jth radial polynomial is the supplied radial coefficient when n is at most j, and zero beyond j. [`poly_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L39).

**Theorem · The radial polynomial has bounded degree.** The natural degree of the jth radial coefficient polynomial is at most j. [`poly_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L44).

**Definition · The polynomial radial line weight.** The weight polynomial is the variable X when the lower radius is zero, and the constant polynomial one otherwise. [`wpoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L50).

**Theorem · Evaluating the line-weight polynomial.** Evaluating the radial weight polynomial gives the cell box's line-weight function. [`wpoly_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L52).

**Definition · The radial weighted polynomial pairing.** The pairing ip integrates the product of two real polynomials and the radial weight polynomial over the closed radial interval. [`ip`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L56).

**Theorem · Polynomial integrability on intervals.** Every real polynomial evaluation is integrable on every closed real interval. [`integ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L58).

**Theorem · Linearity of the radial pairing.** The weighted radial pairing of a finite real linear combination in its first argument is the corresponding combination of pairings. [`ip_sum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L61).

**Theorem · Radial polynomials span bounded degrees.** If every radial leading coefficient is nonzero, every polynomial of degree at most D is a linear combination of the radial coefficient polynomials through D. [`span`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L75).

**Theorem · Recovering radial polynomial expansions.** For an orthonormal radial family with nonzero leading coefficients, a polynomial of degree at most D equals its expansion through D with coefficients given by weighted radial pairings. [`expand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L108).

**Definition · The affine normalized radius polynomial.** The polynomial rho is the affine radial coordinate that rescales the cell's radial interval to the reference interval. [`rho`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L121).

**Theorem · Evaluating the reference radius.** Evaluating rho at a real radius gives the cell box's reference radial coordinate. [`rho_eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L123).

**Definition · The endpoint-vanishing radial weight.** The polynomial Wp multiplies the radial line-weight polynomial by one minus the square of the reference-radius polynomial. [`Wp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L127).

**Theorem · The radial weight at the left endpoint.** On an increasing radial interval, Wp vanishes at its lower endpoint. [`Wp_left`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L129).

**Theorem · The radial weight at the right endpoint.** On an increasing radial interval, Wp vanishes at its upper endpoint. [`Wp_right`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L137).

**Definition · An affine factor for the axis case.** The polynomial Upoly is four divided by the outer radius minus four times the variable divided by the outer radius squared. [`Upoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L145).

**Definition · The radial operator polynomial.** The polynomial F is the differentiated endpoint-weighted derivative, expressed with a separate axis-touching formula so that multiplying by the radial line weight recovers the weighted operator. [`F`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L148).

**Theorem · The weighted radial operator identity.** For an increasing radial interval, multiplying F by the radial line-weight polynomial equals the derivative of the product of Wp and the derivative of the radial basis polynomial. [`F_spec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L154).

**Theorem · Degree bound for the radial operator.** The natural degree of F at index j is at most j. [`F_natDegree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L170).

**Theorem · The leading radial-operator coefficient.** For nonzero degree j, the degree-j coefficient of F is minus the radial eigenvalue times the supplied radial leading coefficient. [`F_coeff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L198).

**Theorem · A derivative pairing for the operator.** On an increasing interval, pairing F with another radial basis polynomial equals minus the integral of the two polynomial derivatives multiplied by Wp. [`ip_F`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L223).

**Theorem · The radial eigenvalue equation.** For an orthonormal radial family with nonzero leading coefficients on an increasing interval, each nonconstant radial polynomial is an eigenfunction of F with eigenvalue minus its radial eigenvalue. [`eigen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L245).

**Theorem · Stiffness entries as radial pairings.** The layout's radial stiffness entry equals the weighted radial pairing of the endpoint-weighted derivative of one basis polynomial with the other basis polynomial. [`stiff_eq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L277).

**Theorem · Radial coefficients from derivatives.** For a valid box and bases, the stated radial integration-by-parts and integrability hypotheses express a nonconstant field coefficient as the finite stiffness-weighted sum of radial-gradient coefficients divided by its radial eigenvalue. [`key`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L286).

**Theorem · A coordinate row reads one datum.** Pairing the layout's unit coordinate row with a data function returns its selected value. [`sum_unit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L390).

**Theorem · Radial integration gives relation rows.** The radial mode weak-integration proposition implies the radial-coefficient relation proposition. [`relRadialCoef_of`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/RelRadialCoef.lean#L397).

### Breakdown.FracCell.RelRadialSide

Turns the weak radial derivative identity into the finite coefficient relation for radial cell faces.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelRadialSide.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.RadialSide.Internal`.

**Finite radial polynomial space.** Definition `polySpan`: The radial polynomial space is the real span of the first M radial basis polynomials.

**The line weight is continuous.** Proved result `lineWeight_continuous`: The cell line weight is continuous.

**Radial polynomials are continuous.** Proved result `radialPoly_continuous`: Every radial basis polynomial is continuous.

**Height polynomials are continuous.** Proved result `heightPoly_continuous`: Every height basis polynomial is continuous.

**The cell rectangle is compact.** Proved result `rect_compact`: The closed radial-height rectangle of a cell is compact. Source: `Breakdown.FracCell.RelRadialSide:29`.

**Low powers lie in the radial span.** Proved result `pow_mem`: For a valid cell basis, every monomial of degree below M belongs to the first M radial polynomials' span.

**Reconstruct a radial polynomial.** Proved result `expand`: A polynomial in the finite radial span is recovered from its line-weighted integrals against an orthonormal cell basis.

**Radial test pair is integrable.** Proved result `intPair`: Integrable field and weighted derivative terms remain integrable after multiplication by the stated continuous radial and height tests.

**Pairing through radial coefficients.** Proved result `coefSum`: For a radial polynomial test, the finite sum of coefficient pairings equals its weighted integral against the field.

**Radial boundary coefficient identity.** Proved result `key`: The weak radial derivative identity equates the difference of the two boundary strip moments with the corresponding finite field and derivative coefficient sums.

**Pairing respects subtraction.** Proved result `pair_sub`: Pairing a difference of finite rows with the data equals the difference of their pairings. Source: `Breakdown.FracCell.RelRadialSide:250`.

**Pairing respects scalar factors.** Proved result `pair_smul`: A complex scalar factor can be pulled out of the finite row pairing. Source: `Breakdown.FracCell.RelRadialSide:254`.

**Pairing respects finite sums.** Proved result `pair_sum`: Pairing a finite sum of rows with the data equals the sum of their pairings. Source: `Breakdown.FracCell.RelRadialSide:258`.

**Unit row selects its datum.** Proved result `pair_unit`: Pairing the unit row at a datum with a data vector returns that datum.

**Extra row selects a face moment.** Proved result `pair_extra`: Within the allowed degree range, the extra-velocity row paired with true data returns its face moment.

**Velocity row selects a coefficient.** Proved result `pair_velocity`: Within the coefficient cutoff, the velocity row paired with true data returns the selected velocity-mode coefficient.

**Strain row selects a coefficient.** Proved result `pair_strain`: Within the strain cutoff, the strain row paired with true data returns the selected gradient-mode coefficient.

**Outer radial face moment.** Proved result `extra_one`: The extra value on face 1 is the strip moment at the outer radial endpoint.

**Inner radial face moment.** Proved result `extra_zero`: The extra value on face 0 is the strip moment at the inner radial endpoint.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Radial side relation from weak form.** Proved result `relRadialSide_of`: The weak radial mode identity implies the radial side relation.

### Breakdown.FracCell.RelSideSplit

Expresses a whole cell face moment as the sum of its segment moments, using the segment polynomial bases.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelSideSplit.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.RelSideSplit.Internal`.

**Interval cover up to null endpoints.** Proved result `icc_ae_union`: A finite covering by contained intervals agrees almost everywhere with the union of their half-open versions.

**Split a rectangle in height.** Proved result `split_snd`: For integrable data, a disjoint interval cover in the second coordinate splits the rectangle integral into a finite sum.

**Split a rectangle in radius.** Proved result `split_fst`: For integrable data, a disjoint interval cover in the first coordinate splits the rectangle integral into a finite sum.

**Polynomial from coefficient rows.** Definition `polyOf`: A coefficient row defines the polynomial obtained by summing its coefficients times powers through the given degree.

**Segment tests are continuous.** Proved result `test_cont`: Every polynomial defined by a segment coefficient row is continuous.

**Monomials span by segment tests.** Proved result `mono_mem`: Nonzero leading coefficients place each monomial through degree M in the span of the first M+1 segment tests.

**Polynomial tests lie in the span.** Proved result `poly_mem`: A polynomial with the stated shifted powers and degree bound belongs to the finite segment-test span.

**Reconstruct a segment test.** Proved result `expand`: An orthonormal segment basis reconstructs every test in its finite span from its integral coefficients.

**Expand a height test in an integral.** Proved result `seg_snd`: An integrable rectangle pairing with a finite height test expands as the sum of its orthonormal segment-basis pairings.

**Expand a radial test in an integral.** Proved result `seg_fst`: An integrable rectangle pairing with a finite radial test expands as the sum of its orthonormal segment-basis pairings.

**Height cover and basis expansion.** Proved result `strip_snd`: A disjoint height-interval cover and its orthonormal test bases turn the full strip pairing into a sum of segment pairings.

**Radial cover and basis expansion.** Proved result `strip_fst`: A disjoint radial-interval cover and its orthonormal test bases turn the full strip pairing into a sum of segment pairings.

**Segment test coefficient formula.** Proved result `test_eq`: The segment test is the polynomial defined by its stored coefficient row.

**Split a radial side moment.** Proved result `radial_side`: A radial side covered by compatible disjoint segments has its strip moment equal to the weighted sum of segment moments.

**Split a height side moment.** Proved result `height_side`: A height side covered by compatible disjoint segments has its strip moment equal to the weighted sum of segment moments.

**Evaluate the side-splitting row.** Proved result `pair_row`: Pairing the side-splitting row with data subtracts the weighted segment values from the whole-face value.

**Whole-face tests are continuous.** Proved result `sideTest_cont`: Every whole-face polynomial test is continuous.

**Radial-side test fits the basis.** Proved result `mem_lo`: With nonzero segment leading coefficients, a radial-side test within its degree bound lies in the segment-test span.

**Height-side test fits the basis.** Proved result `mem_hi`: The axis-dependent height-side degree bound places its test in the segment-test span.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Cell modes are integrable.** Proposition `ModeRectIntegrableStatement`: This proposition requires admissible velocity and gradient modes to be integrable on every valid cell rectangle.

**Source namespace:** `Breakdown.CellCert.CellFormula.RelSideSplit.Internal`.

**Geometry of radial segments.** Proved result `seg_radial`: A valid radial segment lies within the cell's height range and stores the opposite radial endpoint.

**Geometry of height segments.** Proved result `seg_height`: A valid height segment lies within the cell's radial range and stores the opposite height endpoint.

**True face data split over segments.** Proved result `extra_split`: Under mode integrability and the stated axis and degree restrictions, the true extra face value equals the weighted segment-data sum.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Side relations from integrability.** Proved result `relSideSplit_of_integrable`: Integrability of the rectangle modes supplies the side-splitting relation.

### Breakdown.FracCell.RelStream

Derives the stream relation from cylindrical flux cancellation and the constant and linear face tests.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelStream.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Modes are integrable on strips.** Proposition `ModeStripIntegrableStatement`: This proposition requires velocity and gradient modes of second-order fields to be integrable on rectangles reaching the axis.

**Zero flux through a cylinder.** Proposition `CylinderFluxStatement`: This proposition states that the radial boundary flux and the two height boundary fluxes of a second-order field sum to zero.

**Source namespace:** `Breakdown.CellCert.CellFormula.Internal.RelStream`.

**Unit row selects its datum.** Proved result `pairUnit`: Pairing the unit row at a datum with a data vector returns that datum.

**Pairing respects addition.** Proved result `pairAdd`: Pairing a sum of two finite rows with the data equals the sum of their pairings.

**Pairing respects subtraction.** Proved result `pairSub`: Pairing a difference of finite rows with the data equals the difference of their pairings.

**Pairing respects scalar factors.** Proved result `pairSmul`: A complex scalar factor can be pulled out of the finite row pairing.

**Constant segment test.** Proved result `test_zero`: The degree-zero segment test is its constant coefficient.

**Linear segment test.** Proved result `test_one`: The degree-one segment test is its constant coefficient plus its leading coefficient times the coordinate.

**Factor a constant radial test.** Proved result `radialStrip_const`: A constant test factors out of the radial strip moment.

**Recover a radial-weighted moment.** Proved result `split_core`: For integrable data and nonzero constant and linear leading coefficients, the stated combination of the first two tests recovers the difference of radial-weighted strip integrals.

**Zero-width height strip vanishes.** Proved result `strip_point`: A height strip moment over the radial interval from zero to zero vanishes.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Stream relation from cylinder flux.** Proved result `relStream_of`: Strip integrability and cylindrical flux cancellation imply the stream relation.

### Breakdown.FracCell.RelTrace

Passes the divergence-free trace identity to cylindrical Fourier coefficients with the required measure and integrability arguments.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelTrace.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.Internal.RelTrace`.

**Cylindrical coordinate map.** Definition `cylF`: The cylindrical coordinate map sends radius, height and angle to the corresponding point in space.

**Cartesian cylindrical coordinates.** Proved result `cylF_eq`: The cylindrical point has Cartesian coordinates given by radius times cosine, radius times sine, and height.

**Cylindrical map is measurable.** Proved result `measurable_cylF`: The cylindrical coordinate map is measurable.

**Positive-radius angular chart.** Definition `region`: The coordinate region consists of positive radii, arbitrary heights and angles strictly between minus pi and pi.

**The angular chart is measurable.** Proved result `measurableSet_region`: The positive-radius angular chart is measurable.

**Cylindrical integration formula.** Proved result `lintegral_cyl`: Integrating a nonnegative spatial function in the angular chart with radial Jacobian equals its spatial integral.

**Null sets pull back in the chart.** Proved result `region_null`: A measurable spatial null set has null preimage in the positive-radius angular chart.

**Cylindrical null-set preservation.** Proved result `qmp_region`: The cylindrical coordinate map is quasi-measure-preserving from the restricted chart to space.

**The axis is a null set.** Proved result `axis_null`: The zero-radius coordinate set has measure zero.

**A cell chart lies in the region.** Proved result `restrict_le`: The measure on a valid cell's angular chart is bounded by the measure on the positive-radius chart.

**Mode integral over one period.** Proved result `mode_window`: A gradient mode equals its normalized Fourier integral over the angle interval from minus pi to pi.

**Matrix entry in Cartesian axes.** Definition `ent`: A Cartesian matrix entry pairs the operator applied to one coordinate unit vector with another unit vector.

**Rotated diagonal entries.** Definition `diagExp`: The rotated diagonal entries are expressed using sine, cosine and Cartesian matrix entries.

**Radial unit vector in coordinates.** Proved result `radialUnit_eq`: The radial unit vector is cosine times the first Cartesian unit vector plus sine times the second.

**Angular unit vector in coordinates.** Proved result `angularUnit_eq`: The angular unit vector is minus sine times the first Cartesian unit vector plus cosine times the second.

**Axial unit vector in coordinates.** Proved result `axialUnit_eq`: The axial unit vector is the third Cartesian unit vector.

**Diagonal in the cylindrical frame.** Proved result `frameMat_diag`: Each diagonal entry of the cylindrical-frame matrix equals the explicit rotated-diagonal formula.

**Trace survives a frame rotation.** Proved result `diag_sum`: The sum of the cylindrical-frame diagonal entries equals the Cartesian trace.

**Bound a Cartesian matrix entry.** Proved result `abs_ent_le`: The absolute value of a matrix entry is bounded by the norm of its column.

**A bounded factor cannot enlarge.** Proved result `abs_mul_le_of`: Multiplication by a real number of absolute value at most one cannot increase absolute value.

**Bound a rotated diagonal entry.** Proved result `abs_diag_le`: A rotated diagonal entry has absolute value at most five plus twice the sum of squared matrix entries.

**Bound the cylindrical point's norm.** Proved result `norm_cyl_le`: The norm of a cylindrical point is at most twice the absolute radius plus the absolute height.

**Fourier normalization is bounded.** Proved result `norm_coef_le`: The complex norm of the Fourier normalization factor is at most one.

**Weighted cell polynomial test.** Definition `wPoly`: The weighted test multiplies the cell line weight by a radial basis polynomial and a height basis polynomial.

**Fourier phase on the circle.** Definition `phase`: The phase is the complex exponential at the negative azimuthal mode frequency.

**Trace coefficient integrand.** Definition `phi`: The trace-coefficient integrand combines the weighted test, Fourier phase and selected rotated diagonal entry.

**Cell basis product is continuous.** Proved result `continuous_poly`: The product of a radial basis polynomial and a height basis polynomial is continuous.

**Weighted test is continuous.** Proved result `continuous_wPoly`: The weighted cell polynomial test is continuous.

**Fourier phase is continuous.** Proved result `continuous_phase`: The Fourier phase is continuous as a function of angle.

**Matrix entries vary continuously.** Proved result `continuous_ent`: Each Cartesian matrix entry is a continuous function of the linear operator.

**Rotated diagonals are continuous.** Proved result `continuous_diag`: Continuous angles and operators give continuous rotated diagonal entries.

**Measurability of the integrand.** Proved result `aesm_phi`: Almost-everywhere strong measurability of the pulled-back operator implies the same property for the trace-coefficient integrand.

**Weighted test is bounded by radius.** Proved result `wPoly_bound`: On a valid cell rectangle, the weighted test's absolute value is bounded by a nonnegative constant times radius.

**Trace coefficient is integrable.** Proved result `integrableOn_phi`: A measurable operator field with integrable squared entries gives an integrable trace-coefficient integrand on a valid cell chart.

**Coefficient as a chart integral.** Proved result `coef_eq`: For an integrable trace integrand, the diagonal gradient coefficient equals its integral over the cell's angular chart.

**Divergence forces zero trace sum.** Proved result `trace_coef`: A square-integrable operator field with almost-everywhere zero trace has zero sum of diagonal gradient-mode coefficients.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Trace relation holds.** Proved result `relTrace_holds`: For a valid cell layout and admissible field data, every finite trace relation row pairs to zero with the true data vector.

### Breakdown.FracCell.RelTurn

Derives the angular turning relation by shifting radial polynomial coefficients and using the angular mode identity.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelTurn.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Pairing respects subtraction.** Proved result `pair_sub`: Pairing a difference of finite rows with the data equals the difference of their pairings. Source: `Breakdown.FracCell.RelTurn:15`.

**Pairing respects addition.** Proved result `pair_add`: Pairing a sum of two finite rows with the data equals the sum of their pairings.

**Pairing respects scalar factors.** Proved result `pair_smul`: A complex scalar factor can be pulled out of the finite row pairing. Source: `Breakdown.FracCell.RelTurn:23`.

**Pairing respects finite sums.** Proved result `pair_sum`: Pairing a finite sum of rows with the data equals the sum of their pairings. Source: `Breakdown.FracCell.RelTurn:27`.

**Unit row selects its datum.** Proved result `pair_single`: Pairing the singleton unit row with a data vector returns its selected datum.

**Strain row selects a coefficient.** Proved result `pair_strain`: Within the strain degree bounds, pairing the strain row with true data returns the selected gradient coefficient.

**Velocity row selects a coefficient.** Proved result `pair_velocity`: Within the velocity degree bounds, pairing the velocity row with true data returns the selected velocity coefficient.

**Monomials lie in the radial span.** Proved result `mono_mem`: Nonzero radial leading coefficients place every monomial through degree Q in the first Q+1 radial basis polynomials' span.

**Multiply a radial basis by radius.** Proved result `shift_expand`: Multiplication by radius expands a radial basis polynomial in the enlarged finite radial basis when the degree bound allows it.

**Radial polynomials are continuous.** Proved result `radialPoly_cont`: Every radial basis polynomial is continuous.

**Height polynomials are continuous.** Proved result `heightPoly_cont`: Every height basis polynomial is continuous.

**The line weight is continuous.** Proved result `lineWeight_cont`: The cell line weight is continuous.

**Coefficients of the radial shift.** Proved result `shift_eq`: For an orthonormal cell basis, the weighted radial-shift integral gives the corresponding expansion coefficient.

**The cell rectangle is compact.** Proved result `rect_compact`: The closed radial-height rectangle of a cell is compact. Source: `Breakdown.FracCell.RelTurn:117`.

**The product basis is continuous.** Proved result `basis_cont`: The complex-valued product of a radial basis polynomial and a height basis polynomial is continuous.

**Radius is nonzero almost everywhere.** Proved result `axis_null`: The radial coordinate is nonzero almost everywhere for planar Lebesgue measure.

**Shift coefficients by radius.** Proved result `coef_shift`: The finite radial-shift matrix carries the coefficients of F to those of V when V equals radius times F almost everywhere at positive radius.

**Coefficients respect linear sums.** Proved result `coef_lin`: Under the stated weighted integrability hypotheses, cell coefficients preserve complex linear combinations.

**Turning relation from angular modes.** Proved result `relTurn_of`: Mode integrability and the angular mode identity imply the turning relation.

### Breakdown.FracCell.RelZeroMode

Uses rotationally invariant tests and weak derivatives to show that the axial-angular zero Fourier mode vanishes.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelZeroMode.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula.Internal.RelZeroMode`.

**Infinitesimal axial rotation.** Definition `turnVec`: The turning vector is the ninety-degree rotation of the horizontal coordinates with zero axial component.

**Horizontal part of a vector.** Definition `planeVec`: The plane vector keeps the first two coordinates and removes the axial coordinate.

**Rotate around the axis.** Definition `turnAt`: The rotation combines the horizontal vector and its turning vector while preserving height.

**Distance from the axis.** Definition `rad`: The radius is the square root of the sum of the first two squared coordinates.

**Lift a radial-height test.** Definition `lift`: A test on the radial-height plane is lifted to space by composing it with radius and height.

**Axial derivative along rotation.** Definition `axialPart`: The axial part pairs the operator applied to the turning vector with the axial unit vector.

**Positive-radius half-plane.** Definition `halfPlane`: The half-plane consists of positive radii and arbitrary heights.

**Angularly integrated axial part.** Definition `fiberValue`: The fibre value is radius times the angular integral of the axial derivative along rotation.

**The radial half-plane is open.** Proved result `halfPlane_open`: The positive-radius half-plane is open.

**The radial half-plane is measurable.** Proved result `halfPlane_meas`: The positive-radius half-plane is measurable.

**Turning vector in Cartesian axes.** Proved result `turnVec_eq`: The turning vector is minus the second coordinate times the first unit vector plus the first coordinate times the second.

**Zero rotation is the identity.** Proved result `turnAt_zero`: Rotation through zero leaves every point fixed.

**First coordinate after rotation.** Proved result `turnAt_apply0`: The rotated first coordinate is cosine times the first coordinate minus sine times the second.

**Second coordinate after rotation.** Proved result `turnAt_apply1`: The rotated second coordinate is sine times the first coordinate plus cosine times the second.

**Rotation preserves height.** Proved result `turnAt_apply2`: Axial rotation leaves the third coordinate unchanged.

**Lifted tests are rotation invariant.** Proved result `lift_turnAt`: A lifted radial-height test is unchanged by axial rotation.

**Derivative of the rotation orbit.** Proved result `hasDerivAt_turnAt`: At angle zero, the derivative of the rotation orbit is the turning vector.

**Invariant tests have zero turn.** Proved result `fderiv_turnVec`: A differentiable rotation-invariant scalar function has zero derivative in the turning direction.

**Coordinate functions are smooth.** Proved result `coord_contDiff`: Every Cartesian coordinate function is smooth.

**Radius is smooth off the axis.** Proved result `rad_contDiffAt`: The radius function is smooth at points of positive radius.

**Radius is continuous.** Proved result `rad_continuous`: The distance from the axis is continuous.

**Smooth tests lift off the axis.** Proved result `lift_contDiff`: A smooth radial-height test supported in the positive-radius half-plane lifts to a smooth spatial test.

**Compact support survives lifting.** Proved result `lift_hasCompactSupport`: A compactly supported radial-height test has compactly supported spatial lift.

**Matrix columns lie in L2.** Proved result `col_memLp`: A measurable operator field with integrable squared entries has each column in L2.

**Matrix columns are locally integrable.** Proved result `col_li`: A measurable operator field with integrable squared entries has locally integrable columns.

**Cartesian formula for axial turn.** Proved result `axial_eq`: The axial turning derivative equals the first coordinate times one axial matrix entry minus the second coordinate times the other.

**Axial turn is locally integrable.** Proved result `axial_li`: A measurable operator field with integrable squared entries has locally integrable axial turning derivative.

**Derivative of coordinate times test.** Proved result `fderiv_coord_mul`: The directional derivative of a coordinate times a differentiable test obeys the product rule with the coordinate Kronecker term.

**Weak derivative kills invariant tests.** Proved result `weak_axial`: For an L6 field with square-integrable weak gradient, every smooth compactly supported test with zero turning derivative pairs to zero with the axial turning derivative.

**First cylindrical coordinate.** Proved result `cyl_apply0`: The first Cartesian coordinate of a cylindrical point is radius times cosine.

**Second cylindrical coordinate.** Proved result `cyl_apply1`: The second Cartesian coordinate of a cylindrical point is radius times sine.

**Height of a cylindrical point.** Proved result `cyl_apply2`: The third coordinate of a cylindrical point is its height.

**Recover a positive cylinder radius.** Proved result `rad_cyl`: The radius of a cylindrical point with positive radius equals its given radius.

**Squared cylindrical norm.** Proved result `norm_cyl`: The squared norm of a cylindrical point is radius squared plus height squared.

**Angular integration is integrable.** Proved result `fiber_integrable`: An integrable spatial function gives an integrable radial-weighted angular integral on the positive-radius half-plane.

**Fibre values are locally integrable.** Proved result `fiberValue_integrableOn`: The axial fibre value of a square-integrable operator field is integrable on each bounded portion of the positive-radius half-plane.

**Local integrability of axial fibres.** Proved result `fiberValue_loc`: The axial fibre value is locally integrable throughout the positive-radius half-plane.

**Pair a lifted test through fibres.** Proved result `lift_cyl`: The spatial pairing of a smooth compactly supported lifted test with the axial part equals the half-plane pairing with the fibre value.

**The axial fibre vanishes.** Proved result `fiberValue_ae`: For an L6 field with square-integrable weak gradient, the axial fibre value vanishes almost everywhere at positive radius.

**Turning vector along a circle.** Proved result `turnVec_cyl`: At a cylindrical point, the turning vector is radius times the angular unit vector.

**Axial turn in the moving frame.** Proved result `axial_cyl`: The axial turning derivative at a cylindrical point is radius times the axial-angular matrix entry.

**The moving-frame entry is periodic.** Proved result `frame_periodic`: The axial-angular moving-frame matrix entry is periodic in angle with period two pi.

**The axial-angular zero mode vanishes.** Proved result `mode_zero`: The axial-angular zero Fourier mode of an L6 field's square-integrable weak gradient vanishes almost everywhere at positive radius.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Radius is nonzero almost everywhere.** Proved result `ae_fst_ne_zero`: The radial coordinate is nonzero almost everywhere in the radial-height plane.

**Zero-mode relation holds.** Proved result `relZeroMode_holds`: For a valid cell layout and admissible field data, every finite zero-mode relation row pairs to zero with the true data vector.

### Breakdown.FracCell.RelationsHold

Collects the ten local coefficient, trace and face identities into the complete relation predicate.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RelationsHold.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Assemble the ten cell relations.** Proved result `relationsHold_of`: The radial, height, turning, trace, zero-mode, radial-side, height-side, axis, stream and side-splitting relations imply the combined cell-relation statement.

### Breakdown.FracCell.ResolvedEnergy

Applies scalar projection estimates to gradient entries and curl combinations to obtain the resolved energy bound.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ResolvedEnergy.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.ResolvedEnergyInternal`.

**Energy bound for a matrix combination.** Proved result `combo_bound`: Given mode integrability, radial and height weak identities and the scalar component estimate, the resolved energies and tails of any matrix combination are bounded by its full derivative energy.

**Combined derivative energy is integrable.** Proved result `combo_integrable`: The mode square-integrability statement makes the radial-weighted squared derivative energy of every matrix combination integrable.

**Select one matrix entry.** Definition `unitCoef`: The unit coefficient array is one at a selected matrix entry and zero elsewhere.

**Coefficients of a curl component.** Definition `curlCoef`: The curl coefficient array is the permutation-sign combination selecting one curl component.

**Unit coefficients select an entry.** Proved result `unit_sum`: Summing matrix entries against the unit coefficient array returns its selected entry.

**Curl component respects a factor.** Proved result `curl_mul`: A complex factor passes through the algebraic curl-component formula.

**Curl as a coefficient sum.** Proved result `curl_sum`: The finite matrix sum against the curl coefficient array equals the corresponding curl component.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Resolved energy from component bounds.** Proved result `resolvedEnergy_of`: Mode integrability, radial and height weak identities and the scalar component estimate imply the resolved energy statement.

**Resolved energy from cross identities.** Proved result `resolvedEnergy_of_modes`: Mode integrability, the radial and height weak identities and both cross-term cancellations imply the resolved energy statement.

**Resolved energy from weak identities.** Proved result `resolvedEnergy_of_modeFacts`: Mode integrability and the radial and height weak identities suffice for the resolved energy statement.

### Breakdown.FracCell.ResolvedEnergyCore

Proves weighted projection and directional estimates that combine into the scalar resolved-energy inequality.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ResolvedEnergyCore.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.ResolvedEnergyInternal`.

**The cell rectangle is measurable.** Proved result `rect_meas`: The cell's radial-height rectangle is measurable.

**Weighted square is nonnegative.** Proved result `normSq_nonneg`: A nonnegative weight makes the weighted squared norm nonnegative.

**Weighted cross product is integrable.** Proved result `cross_integrable`: Two measurable functions with finite squared norms under a nonnegative measurable weight have an integrable weighted complex cross product.

**Weighted Cauchy-Schwarz inequality.** Proved result `pair_sq_le`: The squared weighted pairing is bounded by the product of the two weighted squared norms under the stated measurability and integrability hypotheses.

**Test supremum is bounded by energy.** Proved result `testSup_le`: For a nonnegative measurable weight and square-integrable tests, the test supremum is bounded by the weighted squared norm of the field.

**The residual square is integrable.** Proved result `sub_sq_integrable`: Two measurable functions with integrable squares under a nonnegative weight have an integrable weighted squared difference.

**Weighted orthogonal decomposition.** Proved result `orth_split`: When the residual is orthogonal to the comparison function under a nonnegative weight, the full squared norm is the sum of the comparison and residual squared norms.

**Cell polynomials are continuous.** Proved result `poly_cont`: Every polynomial in the finite cell polynomial space is continuous.

**Scaled polynomials are continuous.** Proved result `scaled_cont`: Multiplying a cell polynomial by a continuous weight gives a continuous function.

**Zero lies in the polynomial space.** Proved result `zero_mem`: The zero function belongs to every cell polynomial space.

**Projection lies in its polynomial space.** Proved result `proj_mem`: The chosen cell projection belongs to its target finite polynomial space.

**Projection residual is orthogonal.** Proved result `proj_orth`: The residual after cell projection is orthogonal to the projection under the line-weighted pairing.

**Differentiate radial monomials.** Proved result `radialDeriv_formula`: The radial derivative of a finite cell polynomial is obtained by differentiating each radial monomial.

**Differentiate height monomials.** Proved result `heightDeriv_formula`: The height derivative of a finite cell polynomial is obtained by differentiating each height monomial.

**Radial derivative is continuous.** Proved result `radialDeriv_cont`: The radial derivative of a cell polynomial is continuous.

**Height derivative is continuous.** Proved result `heightDeriv_cont`: The height derivative of a cell polynomial is continuous.

**Continuous cell squares are integrable.** Proved result `cont_integrable`: A continuous function on the cell has measurable restriction and integrable weighted square for any continuous weight on the rectangle.

**Combine a weighted energy split.** Proved result `piece`: An orthogonal weighted decomposition and two lower bounds combine into the full radial-weighted energy estimate when the three weights sum to radius.

**Reference radius lies in unit range.** Proved result `refR_sq_le`: On a valid cell, the squared reference radial coordinate is at most one.

**Reference height lies in unit range.** Proved result `refZ_sq_le`: On a valid cell, the squared reference height coordinate is at most one.

**Cell radii are nonnegative.** Proved result `fst_nonneg`: Every point of a valid cell rectangle has nonnegative radius.

**The line weight is continuous.** Proved result `lw_cont`: The cell line weight is continuous. Source: `Breakdown.FracCell.ResolvedEnergyCore:249`.

**Reference radius is continuous.** Proved result `refR_cont`: The affine reference radial coordinate is continuous.

**Reference height is continuous.** Proved result `refZ_cont`: The affine reference height coordinate is continuous.

**Continuous weights are measurable.** Proved result `wcont`: A continuous real weight is almost-everywhere strongly measurable on the cell.

**An integrable majorant suffices.** Proved result `mono_int`: A measurable nonnegative function dominated on the cell by an integrable function is integrable there.

**The effective inner radius is positive.** Proved result `iR_pos`: A valid cell has strictly positive effective inner radius.

**Bound a directional energy split.** Proved result `dir_part`: Under weighted residual orthogonality, the projected square, two test suprema and residual square are bounded by the full directional energy.

**Bound the angular projection and tail.** Proved result `ang_part`: For square-integrable angular data and the stated axis-mode restriction, angular energy plus weighted tail is bounded by the full radial-weighted square.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Scalar energy from cross cancellation.** Proved result `resolvedComponent_of`: The radial and height cross-term identities imply the scalar resolved-component energy bound.

### Breakdown.FracCell.ResolvedEnergyCross

Proves that weighted radial and height derivative residuals are orthogonal to the derivatives of the polynomial projection.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ResolvedEnergyCross.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.ResolvedEnergyInternal`.

**Polynomial space is closed under sums.** Proved result `poly_add`: The sum of two cell polynomials within the same degree bounds stays in that polynomial space.

**Polynomial space is closed under scaling.** Proved result `poly_smul`: Multiplying a cell polynomial by a complex scalar preserves its degree bounds.

**Finite polynomial sums stay in the space.** Proved result `poly_sum`: A finite sum of cell polynomials with common degree bounds belongs to the same polynomial space.

**A bounded monomial lies in the space.** Proved result `poly_mono`: A radial-height monomial belongs to the cell polynomial space when both exponents satisfy its degree bounds.

**Derivative of a complex power.** Proved result `hpow`: The complex-valued power of a real variable has the usual monomial derivative.

**Slope of the reference radius.** Definition `rA`: The slope of the reference radial coordinate is two divided by the radial interval length.

**Offset of the reference radius.** Definition `rB`: The offset of the reference radial coordinate is minus the endpoint sum divided by the radial interval length.

**Reference radius is affine.** Proved result `refR_lin`: The reference radial coordinate equals its slope times radius plus its offset.

**Axis-dependent radial exponent.** Definition `sAx`: The auxiliary exponent is one for a cell touching the axis and zero otherwise.

**Weighted radial monomial operator.** Definition `radialOp`: The radial polynomial operator records the three monomial terms obtained from differentiating the weighted radial derivative.

**Differentiate a weighted radial term.** Proved result `term_deriv`: For a valid cell, differentiating the line-weighted reference-coordinate factor times a monomial derivative yields line weight times the radial operator.

**Radial operator is real-valued.** Proved result `radialOp_conj`: Complex conjugation fixes the radial monomial operator.

**Radial operator preserves the degree.** Proved result `radialOp_mem`: Applying the radial operator coefficientwise keeps the polynomial within the original cell degree bounds.

**Derivative of the weighted conjugate.** Proved result `weighted_deriv`: The derivative of the weighted conjugate radial polynomial derivative equals line weight times the conjugated radial operator value.

**Evaluate a cell polynomial.** Definition `polyVal`: The polynomial value is the finite coefficient sum in radial and height monomials.

**Radial derivative coefficient sum.** Definition `derVal`: The radial derivative value differentiates each radial monomial in the coefficient sum.

**Radial operator coefficient sum.** Definition `opVal`: The operator value applies the weighted radial monomial operator to each coefficient.

**Radial endpoint-vanishing weight.** Definition `wt`: The radial weight is line weight times one minus the square of the reference radial coordinate.

**Conjugation commutes with radial sum.** Proved result `conj_derVal`: Conjugating the radial derivative value is the same as conjugating all coefficients first.

**The polynomial has its radial derivative.** Proved result `polyVal_deriv`: Differentiating the polynomial value in radius gives the radial derivative coefficient sum.

**Polynomial values are continuous.** Proved result `polyVal_cont`: The finite polynomial evaluation is continuous.

**Radial derivative sum is continuous.** Proved result `derVal_cont`: The radial derivative coefficient sum is continuous.

**Radial operator value is continuous.** Proved result `opVal_cont`: The radial operator coefficient sum is continuous.

**Radial weight is continuous.** Proved result `wt_cont`: The endpoint-vanishing radial weight is continuous.

**Radial weight vanishes on the left.** Proved result `wt_left`: For a valid cell, the radial weight vanishes at the inner radial endpoint.

**Radial weight vanishes on the right.** Proved result `wt_right`: For a valid cell, the radial weight vanishes at the outer radial endpoint.

**Integrate a cell in two stages.** Proved result `rect_iterated`: A continuous function's cell integral equals its iterated radial integral followed by its height integral.

**A derivative integral vanishes.** Proved result `interval_zero`: A function with continuous derivative and zero values at both radial endpoints has derivative integral zero.

**Radial integration-by-parts integrand.** Definition `partsFn`: The radial parts integrand combines the polynomial-operator pairing with the weighted derivative square.

**Radial parts integrand is continuous.** Proved result `partsFn_cont`: The radial integration-by-parts integrand is continuous.

**Radial polynomial parts identity.** Proved result `poly_parts`: For a valid cell, the radial integration-by-parts integrand has zero integral.

**The cell line weight is nonnegative.** Proved result `lw_nonneg`: The line weight is nonnegative at every point of a valid cell.

**Line-weighted square is integrable.** Proved result `lw_int`: A measurable function with integrable radial-weighted square also has integrable line-weighted square on a valid cell.

**Radial reference factor vanishes left.** Proved result `refR_left`: The factor one minus reference radius squared vanishes at the inner radial endpoint of a valid cell.

**Radial reference factor vanishes right.** Proved result `refR_right`: The factor one minus reference radius squared vanishes at the outer radial endpoint of a valid cell.

**Radial derivative sum is differentiable.** Proved result `derVal_smooth`: The radial derivative coefficient sum is continuously differentiable.

**Slope of the reference height.** Definition `zA`: The slope of the reference height coordinate is two divided by the height interval length.

**Offset of the reference height.** Definition `zB`: The offset of the reference height coordinate is minus the endpoint sum divided by the height interval length.

**Reference height is affine.** Proved result `refZ_lin`: The reference height coordinate equals its slope times height plus its offset.

**Weighted height monomial operator.** Definition `heightOp`: The height operator records the three monomial terms obtained by differentiating the reference-weighted height derivative.

**Height operator is real-valued.** Proved result `heightOp_conj`: Complex conjugation fixes the height monomial operator.

**Differentiate a weighted height term.** Proved result `hterm_deriv`: Differentiating one minus reference height squared times a monomial derivative gives the height operator.

**Height operator coefficient sum.** Definition `hOpVal`: The height operator value applies the height monomial operator to the polynomial's coefficients.

**Height derivative coefficient sum.** Definition `hderVal`: The height derivative value differentiates each height monomial in the polynomial coefficient sum.

**Height operator preserves the degree.** Proved result `heightOp_mem`: The height operator coefficient sum stays in the original finite cell polynomial space.

**Weighted conjugate height derivative.** Proved result `hweighted_deriv`: Differentiating the weighted conjugate height derivative gives the conjugated height operator value.

**Conjugation commutes with height sum.** Proved result `conj_hderVal`: Conjugating the height derivative sum is equivalent to conjugating all coefficients first.

**The polynomial has its height derivative.** Proved result `hpolyVal_deriv`: Differentiating polynomial evaluation in height gives the height derivative coefficient sum.

**Height derivative sum is continuous.** Proved result `hderVal_cont`: The height derivative coefficient sum is continuous.

**Height operator value is continuous.** Proved result `hOpVal_cont`: The height operator coefficient sum is continuous.

**Height derivative sum is differentiable.** Proved result `hderVal_smooth`: The height derivative coefficient sum is continuously differentiable.

**Height integration-by-parts integrand.** Definition `hpartsFn`: The height parts integrand combines the polynomial-operator pairing and weighted derivative square under the line weight.

**Height parts integrand is continuous.** Proved result `hpartsFn_cont`: The height integration-by-parts integrand is continuous.

**Height reference factor vanishes below.** Proved result `refZ_left`: The factor one minus reference height squared vanishes at the lower height endpoint of a valid cell.

**Height reference factor vanishes above.** Proved result `refZ_right`: The factor one minus reference height squared vanishes at the upper height endpoint of a valid cell.

**Height polynomial parts identity.** Proved result `hpoly_parts`: For a valid cell, the height integration-by-parts integrand has zero integral.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Radial derivative cross term vanishes.** Proved result `radialCross`: The radial derivative residual is orthogonal to the projected derivative under the endpoint-vanishing radial weight.

**Height derivative cross term vanishes.** Proved result `heightCross`: The height derivative residual is orthogonal to the projected derivative under the endpoint-vanishing height weight.

### Breakdown.FracCell.ResolvedEnergySt

Defines the mode integrability, weak derivative and projection-orthogonality interfaces used in the resolved-energy estimate.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ResolvedEnergySt.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Linear combination of gradient modes.** Definition `comboGrad`: The combined gradient mode is the finite matrix-coefficient sum of gradient entries.

**Linear combination of derivative modes.** Definition `comboThird`: The combined third-order mode is the same matrix-coefficient sum of differentiated gradient entries in a chosen direction.

**Combined modes have finite energy.** Proposition `ModeSquareIntegrableStatement`: This proposition requires measurable combined modes and integrable line-weighted gradient squares and radial-weighted derivative squares for second-order fields.

**Weak radial identity for combined modes.** Proposition `ModeRadialPartsStatement`: This proposition requires the radial integration-by-parts identity for combined modes against continuously differentiable tests vanishing at both radial endpoints.

**Weak height identity for combined modes.** Proposition `ModeHeightPartsStatement`: This proposition requires the height integration-by-parts identity for combined modes against continuously differentiable tests vanishing at both height endpoints.

**Radial projection cross cancellation.** Proposition `RadialCrossStatement`: This proposition requires orthogonality between the radial derivative residual and projected derivative under the endpoint-vanishing weight, assuming integrability and the weak radial identity.

**Height projection cross cancellation.** Proposition `HeightCrossStatement`: This proposition requires orthogonality between the height derivative residual and projected derivative under the endpoint-vanishing weight, assuming integrability and the weak height identity.

**Scalar resolved energy bound.** Proposition `ResolvedComponentStatement`: This proposition bounds the radial, height and angular resolved energies and their tails by the full derivative energy under integrability, weak derivative and axis-mode hypotheses.

### Breakdown.FracCell.RowCircleSeries

Expands the high-mode row pairing around each circle into its Fourier coefficient series.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RowCircleSeries.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.RowCircleSeries`.

**Real vector cross product.** Definition `crossR`: The real cross product is defined by the three signed two-by-two coordinate products.

**Adjoint curl matrix of a vector.** Definition `adjR`: The adjoint curl matrix uses permutation signs to turn a vector into its skew matrix entries.

**Circle L2 implies integrability.** Proved result `ii_of`: A real function in L2 on one angular period is interval integrable over that period.

**Bounded factors preserve circle L2.** Proved result `memLp_mul_b`: Multiplying an L2 circle function by a bounded measurable real factor keeps it in L2.

**Fourier coefficients of a difference.** Proved result `cf_sub`: The Fourier coefficient of a difference of two integrable real circle functions is the difference of their coefficients.

**Finite product coefficient formula.** Proved result `conv_fin`: A square-integrable factor times a regular periodic factor with finite Fourier support has the stated finite convolution formula for each coefficient.

**Reverse-order product coefficients.** Proved result `conv_fin'`: Putting the finite-spectrum factor first gives the same finite Fourier convolution formula.

**Conjugated coefficient formula.** Proved result `conj_cf`: The conjugate of a real function's Fourier coefficient uses the positive-frequency phase in the normalized integral.

**A conjugate-symmetric sum is real.** Proved result `self_conj`: A finite Fourier sum over a sign-symmetric index set is real when opposite coefficients are complex conjugates.

**Pair a finite Fourier reconstruction.** Proved result `cst_low`: The product of a real finite Fourier reconstruction and an integrable circle function has the finite coefficient pairing series.

**Circle product from Fourier pairings.** Proved result `cst_pair`: A regular periodic circle function paired with an L2 function has the coefficient-product series supplied by Parseval's identity.

**Coefficients of a vector cross product.** Proved result `cross_coef`: The cross product of an L2 vector and a regular finite-spectrum vector has coefficients given by the finite cross-product convolution.

**Coefficients of the reversed cross.** Proved result `cross_coef'`: Reversing the two vector factors gives the corresponding reversed finite cross-product convolution.

**Coefficients of the adjoint curl.** Proved result `adj_coef`: Applying the adjoint curl matrix to the finite cross-product convolution gives the Fourier coefficient of the corresponding real matrix field.

**Series for the residual row pairing.** Proved result `hbase`: Regular periodic gradient and velocity entries, finite row spectrum and bounded model factors yield the Fourier series for the residual matrix and vector pairings.

**Frame coordinates preserve addition.** Proved result `frameVec_add`: A vector sum has the sum of the corresponding moving-frame coordinates.

**Frame coordinates preserve subtraction.** Proved result `frameVec_sub`: A vector difference has the difference of the corresponding moving-frame coordinates.

**Frame matrices preserve subtraction.** Proved result `frameMat_sub`: The moving-frame matrix of an operator difference is the entrywise difference of its frame matrices.

**Cross product in the moving frame.** Proved result `frameVec_cross`: The moving-frame coordinates of a spatial cross product equal the coordinate cross product.

**Inner product in the moving frame.** Proved result `inner_frame`: The spatial inner product is the sum of products of matching moving-frame coordinates.

**Unfold the high coupling pairing.** Proved result `pt_id`: At positive radius and nonnegative height, the high coupling field paired with a test is the stated residual gradient and velocity coordinate pairing.

**Scale the matrix pairing.** Proved result `ep_smul`: A real scalar multiplying the second matrix argument factors out of its complex entry pairing.

**Scale the vector pairing.** Proved result `vp_smul`: A real scalar multiplying the second vector argument factors out of its complex vector pairing.

**Recover the radial Jacobian.** Proved result `lw_hat`: At positive radius, line weight times the adjusted radial factor equals radius.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Row pairing has its circle series.** Proved result `rowCircleSeries_holds`: The row pairing satisfies the asserted almost-everywhere Fourier series identity.

### Breakdown.FracCell.RowCouplingSquare

Supplies the square-integrability of the row-coupling fields needed to sum the unresolved row terms.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RowCouplingSquare.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Row coupling has finite square norm.** Proved result `rowCouplingSquare_holds`: For valid fractional cell data with axisymmetric weight, every selected row and angular mode has weighted square-integrable strain, velocity and folded row-coupling components.

### Breakdown.FracCell.RowDegreeIndependence

Shows that the multiplier expression depends on the represented row polynomials, allowing a cellwise degree bound to replace a larger system degree.

Appendix B polynomial row representation and test-multiplier bounds; this source module is outside the supplied Solution import closure.

Source: `lean/Breakdown/FracCell/RowDegreeIndependence.lean`. Outside the ordinary and fractional endpoint import closures.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Changing a valid row degree is harmless.** Proved result `multiplierLHS_rowDegree`: When both degree choices represent the same row polynomials in a valid cell basis, the multiplier expression is unchanged.

**Transfer a bound between row degrees.** Proved result `testMultiplierBound_of_systemDegree`: A multiplier bound checked at an alternative valid row degree also holds at the cell entry's stored row degree.

**Source namespace:** `Breakdown.CellCert.CellSystem.RowDegreeInternal`.

**Zero high coefficients lower the degree.** Proved result `evalPoly_mem_of_coef_vanish`: A polynomial whose coefficients vanish above either degree e belongs to the bivariate polynomial space of degree at most e in each variable.

**Cell coefficients lower interior degree.** Proved result `interiorPoly_mem_of_cell_coef`: Vanishing high coefficients in every harmonic of a cell places its interior polynomial in the lower-degree bivariate space.

**Source namespace:** `Breakdown.CellCert.CellSystem`.

**Cellwise model degree bounds row degree.** Proved result `rowPolynomial_of_cellDegree`: If the model's cell coefficients vanish above degree d, the row polynomial condition holds at any degree at least the row-data degree plus d plus two.

**Use a cellwise degree in the bound.** Proved result `testMultiplierBound_of_cellDegree`: The cellwise coefficient vanishing and degree inequality let the system-degree multiplier bound imply the bound at the entry's stored degree.

### Breakdown.FracCell.RowFacePolynomial

Converts segment-basis representations of row traces into polynomial formulas on each whole cell face.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RowFacePolynomial.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Segment-test sum as monomials.** Proved result `test_sum_monomial`: A finite linear combination of segment tests equals the monomial polynomial obtained by collecting their coefficient rows.

**One row has a face polynomial.** Proved result `rowFacePoly_of_segment_row`: Compatible polynomial representations on the segments of a valid layout give a degree-bounded normal row polynomial on each non-axis face.

**All row traces have face polynomials.** Proved result `rowFacePoly_of_segments`: Segment polynomial representations for every selected row give degree-bounded normal row polynomials on all non-axis faces.

### Breakdown.FracCell.RowModeUnfolded

Justifies replacing the unresolved row integral by a summable series of mode integrals, with bounds and conjugation identities for the projected fields.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RowModeUnfolded.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Density of one residual row mode.** Definition `rowModeDensity`: The row-mode density is the line-weighted pairing of residual gradient and velocity modes with their row couplings.

**Average row pairing around a circle.** Definition `circleRowPair`: The circle row pairing is the normalized angular integral of the high coupling field paired with the row.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Circle row pairing has a mode series.** Proposition `RowCircleSeriesStatement`: This proposition requires the real row-mode densities to sum almost everywhere to radius times the circle pairing for admissible fractional cell data with axisymmetric weight.

**Row-mode integral norms are summable.** Proposition `RowSeriesDominationStatement`: This proposition requires summability over modes of the integrals of the row-mode density norms for admissible fractional cell data.

**The row-coupling tail is summable.** Proposition `RowCouplingTailStatement`: This proposition requires summability of the line-weighted squared gradient and velocity row couplings over all modes.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.RowModeUnfolded.Internal`.

**Subtracting a projection keeps L2.** Proved result `low_sq`: A weighted-square-integrable mode remains weighted-square-integrable after optionally subtracting its finite polynomial projection.

**High coupling respects reflection.** Proved result `coupling_mirror_pt`: Away from the mirror plane, the stated parity laws of the field, gradient and model imply mirror covariance of the high coupling field.

**Row pairing respects reflection.** Proved result `coupling_pair_mirror`: For admissible cell data, the row pairing of the high coupling field is mirror-invariant almost everywhere in the cell solid.

**Frame rank-one operators are continuous.** Proved result `op_cont`: The rank-one operator formed from two moving-frame unit vectors varies continuously with angle.

**Frame unit norms are at most one.** Proved result `unit_nm`: Every moving-frame unit vector has norm at most one.

**The polar angle is measurable.** Proved result `angle_m`: The cylindrical angle is measurable.

**Mirror signs are measurable.** Proved result `sign_m`: Each component's mirror-sign function is measurable.

**Mirror signs have unit magnitude.** Proved result `sign_bd`: Every mirror sign has absolute value one.

**Reflected coordinates are continuous.** Proved result `rho_c`: The map from space to radius and absolute height is continuous.

**Finite angular sums are measurable.** Proved result `wsum_m`: A finite Fourier sum with continuous radial-height coefficients gives a measurable real spatial function.

**Finite angular sums are bounded.** Proved result `wsum_bd`: A finite Fourier sum with continuous coefficients is bounded on the cell solid.

**Bound an operator by its entries.** Proved result `op_bd`: The norm of the Cartesian operator reconstructed from a frame matrix is bounded by the sum of the absolute matrix entries.

**Bound a vector by its components.** Proved result `vec_bd`: The norm of a vector reconstructed from frame components is bounded by the sum of their absolute values.

**Cell projection is continuous.** Proved result `proj_c`: Every finite cell polynomial projection is continuous.

**Low gradient field is bounded.** Proved result `lowG_props`: The low gradient field is almost-everywhere strongly measurable and bounded on the cell solid.

**Low velocity field is bounded.** Proved result `lowV_props`: The low velocity field is almost-everywhere strongly measurable and bounded on the cell solid.

**The high row pairing is integrable.** Proved result `pair_integrable`: For admissible cell data and a selected row, the high coupling field's row pairing is spatially integrable.

**Weighted product bound by squares.** Proved result `amgm`: A nonnegative weight times a product is bounded by half the weighted sum of the two squares.

**Matrix pairing bound by squares.** Proved result `entry_bd`: The norm of the complex matrix pairing is bounded by half the sum of the two entry-square norms.

**Vector pairing bound by squares.** Proved result `vec_bd2`: The norm of the complex vector pairing is bounded by half the sum of the two vector-square norms.

**Dominate a row-mode density.** Proved result `density_bd`: For nonnegative line weight, the row-mode density norm is bounded by half the residual square density plus half the coupling square density.

**Entrywise L2 gives a matrix square.** Proved result `sq_int`: Weighted-square integrability of each matrix entry gives integrability of the line-weighted entry-square sum.

**Componentwise L2 gives a vector square.** Proved result `vsq_int`: Weighted-square integrability of each vector component gives integrability of the line-weighted vector-square sum.

**Compare line weight with radius.** Proved result `lw_le`: On a valid cell, line weight is bounded by radius times the stated axis-dependent constant.

**Field mode energies are summable.** Proved result `field_tail`: A second-order field of positive symmetry order has summable integrated line-weighted gradient and velocity mode energies.

**Bound the adjoint curl square.** Proved result `curlAdj_bd`: The entry-square sum of the adjoint curl matrix is at most twice the vector-square sum.

**Bound a difference of products.** Proved result `sub_bd`: The squared norm of a difference of two complex products is at most twice the sum of their squared norms.

**Bound the complex cross product.** Proved result `cross_bd`: The vector-square sum of a complex cross product is at most twice the product of the vector-square sums.

**Conjugation preserves vector squares.** Proved result `conj_sq`: Componentwise complex conjugation preserves the vector-square sum.

**Bound a finite complex sum.** Proved result `fsum_bd`: The squared norm of a finite complex sum is bounded by the number of terms times the sum of squared norms.

**Bound a scaled finite matrix sum.** Proved result `mat_sum_bd`: The entry-square sum of a real-scaled matrix sum is bounded by scale squared times the number of terms times their entry-square sum.

**Bound a scaled finite vector sum.** Proved result `vec_sum_bd`: The vector-square sum of a real-scaled vector sum is bounded by scale squared times the number of terms times their vector-square sum.

**Bound the strain row coupling.** Proved result `rcs_bd`: The strain row-coupling square is bounded by the adjusted radius squared, row-mode count and the stated model-velocity and row-mode square products.

**Bound the velocity row coupling.** Proved result `rcv_bd`: The velocity row-coupling square is bounded by the adjusted radius squared, row-mode count and the stated model-curl and row-mode square products.

**Cell coordinates lie in the solid.** Proved result `cyl_mem`: Every cylindrical point over a valid cell rectangle lies in its solid cell.

**Control the adjusted radial weight.** Proved result `lwr_le`: Line weight times adjusted radius squared is bounded on a valid cell by radius times the maximum of outer radius and one.

**Bound a finite set of slice modes.** Proved result `slice_coef_sq`: A field bounded by C on the cell solid has every finite shifted sum of vector mode squares bounded almost everywhere by three times C squared.

**Row modes have integrable squares.** Proved result `row_mode_int`: A spatial L2 field has integrable radial-weighted squared modes on each valid cell for positive symmetry order.

**Opposite matrix modes are conjugate.** Proved result `modeMat_neg`: The negative matrix Fourier mode is the complex conjugate of the positive mode.

**Opposite vector modes are conjugate.** Proved result `modeVec_neg`: The negative vector Fourier mode is the complex conjugate of the positive mode.

**Coefficients commute with conjugation.** Proved result `coef_conj`: Taking a cell coefficient commutes with complex conjugation.

**Projection commutes with conjugation.** Proved result `proj_conj`: With a valid cell basis and the stated weighted test integrability, cell polynomial projection commutes with conjugation.

**Weighted L2 allows continuous tests.** Proved result `ws_int`: A weighted-square-integrable mode on a valid cell is integrable after multiplication by the line weight and continuous separated tests.

**Low gradient modes are conjugate.** Proved result `lowStrain_neg`: Under weighted-square integrability, the projected negative gradient mode is the conjugate of the projected positive mode.

**Low velocity modes are conjugate.** Proved result `lowVelocity_neg`: Under weighted-square integrability, the projected negative velocity mode is the conjugate of the projected positive mode.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Unfold row modes from dominated series.** Proved result `rowModeUnfolded_of`: Mode-square and projection identities, the circle series and norm-integral summability imply the unfolded row-mode formula.

**Control the row series by square tails.** Proved result `rowSeriesDomination_of`: Mode-square and projection identities together with the row-coupling square tail imply summability of the row-mode integral norms.

**Unfold row modes from square tails.** Proved result `rowModeUnfolded_of_leaves`: Mode-square and projection identities, the circle series and the coupling square tail imply the unfolded row-mode formula.

**Square bounds give the coupling tail.** Proved result `rowCouplingTail_of`: The row-coupling square statement implies summability of the coupling tail.

**Assemble the row-mode formula.** Proved result `rowModeUnfolded_of_circle`: Field mode-square bounds, row-coupling square bounds, projection coefficients and the circle series imply the unfolded row-mode statement.

### Breakdown.FracCell.RowTurnPair

Approximates nonsmooth row fields by rotationally compatible smooth tests and passes the skew turning identity to the rows.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/RowTurnPair.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.FracInternal.RowTurnPair`.

**Expand a vector in coordinate units.** Proved result `unit_expand`: Every vector is the sum of its coordinates times the coordinate unit vectors.

**Apply a linear map coordinatewise.** Proved result `units_sum`: The coordinate sum of a linear map applied to the unit vectors reconstructs its value on any vector.

**A coordinate of the axial turn.** Definition `turnCoord`: The turn-coordinate functional is the selected coordinate of the linear axial-turn map.

**Evaluate a turning coordinate.** Proved result `turnCoord_apply`: The turn-coordinate functional returns the corresponding component of the axial turn.

**A turning coordinate has zero diagonal.** Proved result `turnCoord_unit`: The selected turn-coordinate functional vanishes on its own coordinate unit vector.

**Coordinate test for the turning term.** Definition `testPiece`: The scalar test piece is a turn coordinate times one component of the vector test.

**Derivative of a turning test piece.** Proved result `testPiece_hasFDerivAt`: For a smooth vector test, the derivative of its scalar turning test piece is the stated product-rule linear map.

**Directional turning-test derivative.** Proved result `testPiece_deriv`: In the matching coordinate direction, the turning test's derivative is the turn coordinate times the test-component derivative.

**Turning pieces are valid scalar tests.** Proved result `testPiece_test`: A smooth compactly supported vector test yields valid smooth compactly supported scalar turning pieces.

**Coordinate weak turning identity.** Proved result `coord_weak`: A locally integrable field and weak gradient satisfy the stated coordinate turning integration-by-parts identity with both terms integrable.

**A smooth turning pairing is integrable.** Proved result `integrable_turnInner`: A locally integrable vector field pairs integrably with the axial turn of a smooth compactly supported test.

**Turning is skew under smooth pairing.** Proved result `skew_smooth`: For smooth compactly supported tests, the weak gradient gives skew adjointness of the axial-turn differential operator.

**Pass pairings through local L2 limits.** Proved result `pair_tendsto`: With common support in K and an L2 field on K, L2 convergence of the tests implies convergence of their pairings.

**Finite entry energy gives L2 columns.** Proved result `col_memLp`: A measurable operator field with integrable entry squares has L2 columns.

**An L6 field is locally L2.** Proved result `indicator_memLp_six`: Restricting an L6 field to a compact set gives an L2 field.

**Turning a gradient is locally L2.** Proved result `indicator_memLp_turnGrad`: The gradient applied to the axial turning vector is L2 after restriction to a compact set.

**The turning operator is locally L2.** Proved result `indicator_memLp_turnField`: For a second-order field, its axial-turn differential expression is L2 on every compact set.

**Radial smoothing bump.** Definition `kernRaw`: The unnormalized kernel is a smooth radial bump scaled to radius one divided by n+1.

**The smoothing bump is smooth.** Proved result `kernRaw_contDiff`: Every unnormalized smoothing kernel is smooth.

**The smoothing bump is nonnegative.** Proved result `kernRaw_nonneg`: The unnormalized smoothing kernel is nonnegative.

**The bump vanishes beyond its radius.** Proved result `kernRaw_zero`: The unnormalized kernel vanishes when n+1 times the distance from zero is at least one.

**The bump is supported in a unit ball.** Proved result `kernRaw_support`: Every point where the unnormalized kernel is nonzero has norm at most one.

**The smoothing bump has compact support.** Proved result `kernRaw_compact`: Every unnormalized smoothing kernel has compact support.

**The smoothing mass is positive.** Proved result `kernRaw_integral_pos`: Every unnormalized smoothing kernel has strictly positive integral.

**Normalized smoothing kernel.** Definition `kern`: The smoothing kernel divides the radial bump by its integral.

**The normalized kernel is smooth.** Proved result `kern_contDiff`: Every normalized smoothing kernel is smooth.

**The kernel has compact support.** Proved result `kern_compact`: Every normalized smoothing kernel has compact support.

**The kernel lies in a unit ball.** Proved result `kern_support`: Every point where the normalized kernel is nonzero has norm at most one.

**The kernel is rotation invariant.** Proved result `kern_iso`: The radial kernel is invariant under every linear isometry of space.

**The spatial axis has measure zero.** Proved result `axis_null`: The horizontal distance from the axis is nonzero almost everywhere in space.

**The two axial rotations agree.** Proved result `rot_eq`: The axial rotation and the cell-reduction rotation are the same map.

**Smoothing preserves rotational modes.** Proved result `conv_turn`: Convolution with the radial kernel preserves the stated cosine-sine covariance of a paired mode field.

**Zero rotation is the identity.** Proved result `rot_zero`: Axial rotation through angle zero fixes every vector.

**Differentiate rotational covariance.** Proved result `turn_deriv`: A smooth field satisfying the stated mode covariance has axial-turn differential expression equal to its frequency times the partner field.

**Smoothing has bounded support growth.** Proved result `conv_vanish`: A field vanishing outside radius r has its kernel convolution vanish outside radius r+1.

**Kernel convolution is smooth.** Proved result `conv_smooth`: Convolution of the smooth compact kernel with a locally integrable field is smooth.

**The normalized kernel is nonnegative.** Proved result `kern_nonneg`: Every normalized smoothing kernel is nonnegative.

**The kernel has unit integral.** Proved result `kern_integral`: The normalized smoothing kernel has integral one.

**The kernel has unit absolute mass.** Proved result `kern_lintegral`: The lower integral of the kernel's extended norm is one.

**The support shrinks with n.** Proved result `kern_support_small`: The kernel support lies in the ball of radius one divided by n+1.

**Kernel supports shrink to zero.** Proved result `kern_support_tendsto`: The sequence of kernel supports tends to arbitrarily small neighbourhoods of zero.

**Convolution does not increase L2 energy.** Proved result `conv_sq_le`: Averaging against the normalized nonnegative kernel does not increase the lower integral of the squared norm.

**L2 norm squared as a lower integral.** Proved result `eLpNorm_two_sq`: The extended L2 norm squared equals the lower integral of the squared extended norm.

**Convolution contracts L2 differences.** Proved result `conv_sub_le`: For locally integrable fields, smoothing does not increase the extended L2 norm of their difference.

**Approximation of continuous fields.** Proved result `conv_sq_tendsto_cont`: For a continuous compactly supported field, the squared L2 error of kernel convolution tends to zero.

**Smoothing converges in L2.** Proved result `kern_approx`: The normalized kernels approximate every L2 field in L2 norm.

**Source namespace:** `Breakdown.CellCert.Reduction`.

**Smooth paired rows preserve turning.** Proved result `row_smooth_approx`: Each row and its turning partner admit smooth compactly supported L2 approximations in one common compact set that preserve the exact turning identity.

**Turning identity against a row.** Proved result `turnPair_row`: For a second-order field, pairing its turning expression with a row equals minus the row frequency times the field's pairing with its partner row.

### Breakdown.FracCell.SecondIdentity

Proves the second-order energy identity by expressing curl as coordinate maps and using Fourier compatibility and divergence-free constraints.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SecondIdentity.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Internal.SecondIdentity`.

**Real coordinate curl map.** Definition `curlPart`: The real curl-part linear map uses permutation signs to contribute one derivative direction to curl.

**Complex coordinate curl map.** Definition `curlPartC`: The complex curl-part linear map extends the same permutation-sign formula to complex vectors.

**Coordinates of a unit-vector sum.** Proved result `sum_unit_apply`: The selected coordinate of a unit-vector expansion is its corresponding coefficient.

**Real curl coordinate formula.** Proved result `curlPart_sum_apply`: The coordinate of the sum of real curl-part maps is the signed double sum of vector entries.

**Complex curl coordinate formula.** Proved result `curlPartC_sum_apply`: The coordinate of the sum of complex curl-part maps is the same signed double sum over complex entries.

**Complexification acts coordinatewise.** Proved result `cvec_apply`: The coordinates of a complexified real vector are its real coordinates cast to complex numbers.

**Curl maps commute with complexification.** Proved result `curlPart_compat`: Complexifying a real curl-part value equals applying the complex curl-part map to the complexified vector.

**Curl from its coordinate parts.** Proved result `curlOf_eq`: The curl of an operator is the sum of the curl-part maps applied to its columns.

**Complex vector norm by components.** Proved result `cnorm_sq`: The squared norm of a complex vector is the sum of the squared norms of its coordinates.

**Curl-gradient energy by coordinate maps.** Proved result `curlGradSq_eq`: The curl-gradient square equals the sum of the squared norms of the coordinate curl-part expressions.

**Values of the permutation signs.** Proved result `permSign_vals`: Cyclic triples have permutation sign one, anticyclic triples have sign minus one, and repeated indices give zero.

**Curl preserves compatible energy.** Proved result `curl_norm`: At nonzero frequency, derivative compatibility and zero trace make the curl square equal to the sum of the column squares.

**Fourier transform commutes with maps.** Proved result `hat_sum_map`: For L2 fields, the Fourier transform of a finite sum of compatible real linear images equals the sum of their complex linear Fourier images almost everywhere.

**Zero fields have zero Fourier transform.** Proved result `hat_ae_zero`: An L2 field that vanishes almost everywhere has Fourier transform zero almost everywhere.

**Source namespace:** `Breakdown.CellCert`.

**The second-order energy identity.** Proved result `secondIdentity`: For a second-order field, the full second-derivative and curl-gradient square integrals both equal the integral of the squared second-trace norm, and the curl square integral equals the gradient entry-square integral.

### Breakdown.FracCell.SegmentExpand

Uses finite orthonormal polynomial expansions to assemble radial and height face moments from their segment moments.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentExpand.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Segment tests are continuous.** Proved result `faceSegment_test_continuous`: Every segment test polynomial is continuous.

**Segment tests span bounded polynomials.** Proved result `span_test`: Nonzero leading coefficients let the segment tests span every polynomial through the given degree.

**Reconstruct a polynomial on a segment.** Proved result `segment_expand`: A degree-bounded polynomial is recovered from its integrals against the orthonormal segment tests.

**A finite interval cover agrees a.e..** Proved result `ico_union_ae`: A finite interval cover agrees almost everywhere with the union of its left-closed, right-open intervals.

**Add integrals over height strips.** Proved result `strip_union_right`: Integrals over disjoint height strips add to the integral over their covered rectangle.

**Add integrals over radial strips.** Proved result `strip_union_left`: Integrals over disjoint radial strips add to the integral over their covered rectangle.

**Expand a height polynomial pairing.** Proved result `seg_inner_right`: The finite segment-test coefficient pairing equals the original height-polynomial pairing for integrable data.

**Expand a weighted radial pairing.** Proved result `seg_inner_left`: The finite segment-test coefficient pairing equals the original weighted radial-polynomial pairing under weighted integrability.

**Assemble radial segment moments.** Proved result `radial_segments_sum`: Compatible disjoint segment coverage and orthonormal tests reconstruct the full radial strip moment from the segment moments.

**Assemble height segment moments.** Proved result `height_segments_sum`: Compatible disjoint segment coverage and orthonormal tests reconstruct the full weighted height strip moment from the segment moments.

### Breakdown.FracCell.SegmentIndependence

Shows that a weak face moment is independent of the auxiliary opposite endpoint used to define its strip integral.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentIndependence.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Tent comparisons imply independence.** Proved result `indep_of_tent`: If every pair of opposite-side choices can be compared through an admissible lower point, the moment is independent of the chosen point.

**Embed a strip in a larger box.** Proved result `box_sub`: A rectangle whose lower radial endpoint is at least R lies in the stated larger radial-height box.

**Radial strip terms are integrable.** Proved result `radialTerm_integrableOn`: A radial weak pair and a continuous test give an integrable strip term on the stated nonnegative rectangle with its axis restriction.

**Compare opposite radial strip choices.** Proved result `radialStrip_tent`: The radial weak identity makes the two strip moments at an interior positive radius agree for opposite auxiliary endpoints.

**Height strip terms are integrable.** Proved result `heightTerm_integrableOn`: A height weak pair and a continuous test give an integrable weighted height strip term on every bounded rectangle.

**Compare opposite height strip choices.** Proved result `heightStrip_tent`: For a continuous weight and test, the height weak identity makes the two strip moments at an interior height agree.

**Segment tests are continuous.** Proved result `test_continuous`: Every segment test polynomial is continuous.

**Face moments ignore the opposite end.** Proved result `moment_other_indep`: Two segments with the same face, interval and tests have equal moments despite different admissible opposite endpoints, assuming the appropriate weak pair.

**Equal faces have equal moments.** Proved result `segmentIndependence_holds`: For admissible data, two valid segments with identical orientation, level, interval and test coefficients have equal velocity, normal-gradient and pressure moments, under the stated nonzero-radius and radial-domain conditions.

### Breakdown.FracCell.SegmentIndependenceParts

Extends smooth weak derivative identities to tent tests, including the limiting argument at the axis, to support segment-moment independence.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentIndependenceParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.FracInternal.SegmentParts`.

**Rectangle integrability as a product.** Proved result `prod_int`: Integrability on a product set gives integrability with respect to the product of the restricted measures.

**A compact set stays away from zero.** Proved result `nz_set`: A compact real set excluding zero has a positive lower bound and finite upper bound for absolute value.

**Zero tests force zero radial pairings.** Proved result `fst_slice`: The stated local integrability and vanishing smooth radial tests imply vanishing of every restricted radial-weighted integral.

**Zero tests force zero height pairings.** Proved result `snd_slice`: The stated local integrability and vanishing smooth height tests imply vanishing of every restricted height-weighted integral.

**Use a height tent away from the axis.** Proved result `height_core_nz`: Local integrability and the smooth weak height identity imply the tent-test identity for a compact radial test supported off the axis.

**Radial tent derivative expression.** Definition `rphi`: The radial tent expression is tent slope times the field plus the tent function times its radial weak derivative.

**Height tent derivative expression.** Definition `hphi`: The height tent expression is tent slope times the field plus the tent function times its height weak derivative.

**Height tent integral vanishes.** Proved result `height_zero`: A height weak pair gives zero integral of the tent expression with any radial factor over the stated height interval.

**The radial tent identity off the axis.** Proved result `radial_pos`: A radial weak pair gives zero integral of the tent expression when its lower endpoint is strictly positive.

**Bound the tent slope uniformly.** Proved result `slope_le`: When the lower endpoint is at most half the positive peak, the tent slope is bounded by the stated reciprocal-length expression.

**Bound the tent by the radial coordinate.** Proved result `tent_le`: For nonnegative radius and the stated peak restriction, the tent magnitude is at most twice radius divided by the peak.

**Radial tent identity at the axis.** Proved result `radial_zero`: A radial weak pair and continuous height test give zero tent-expression integral even when the lower radial endpoint is zero.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**The two radial strips cancel.** Proved result `radialStrip_tent_zero`: The piecewise expression using the two radial strip terms has zero integral across a tent interval.

**The two height strips cancel.** Proved result `heightStrip_tent_zero`: The piecewise expression using the two weighted height strip terms has zero integral across a tent interval.

**Cell modes form the needed weak pairs.** Proved result `segment_modes_weak`: Admissible velocity, gradient and pressure modes satisfy the radial and height weak-pair conditions with their stated weights.

### Breakdown.FracCell.SegmentModesGradient

Supplies the weak radial derivative relation between a radial gradient mode and its second derivative mode.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentModesGradient.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Gradient modes form a radial weak pair.** Proved result `modes_radial_pair_gradient`: For admissible data and matching symmetry order, a radial gradient mode and its radial second derivative form a radial weak pair.

### Breakdown.FracCell.SegmentModesHeight

Establishes height weak-pair identities for velocity, gradient and pressure modes, using half-turn symmetry to extend across negative radius.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentModesHeight.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.FracInternal.SegmentRefl`.

**A compact set stays away from zero.** Proved result `nz_set`: A compact real set excluding zero has positive lower and finite upper bounds on absolute value.

**A bounded supported factor is integrable.** Proved result `int_vanish`: A bounded continuous factor vanishing outside a measurable set turns data integrable on that set into a globally integrable product.

**Height weak-test terms are integrable.** Proved result `piece_int`: Smooth compactly supported tests give integrable height derivative and field-derivative terms when both fields are integrable on a containing measurable set.

**Extend the height identity by reflection.** Proved result `height_ident_refl`: A common nonzero radial-reflection factor extends the positive-radius weak height identity to all smooth tests supported away from the axis.

**Source namespace:** `Breakdown.FracInternal.SegmentHeight`.

**Phase of a half-turn.** Definition `halfTurn`: The half-turn phase is the complex exponential of the azimuthal frequency times pi.

**The axial half-turn sign is one.** Proved result `sign_two`: The axial component's half-turn sign is one.

**Half-turn signs are nonzero.** Proved result `sign_ne`: Every frame component's half-turn sign is nonzero.

**The half-turn phase is nonzero.** Proved result `halfTurn_ne`: The complex half-turn phase never vanishes.

**Velocity kernel under a half-turn.** Proved result `vel_k_pi`: Shifting angle by pi changes the velocity Fourier kernel by its half-turn phase and component sign.

**Gradient kernel under a half-turn.** Proved result `grad_k_pi`: Shifting angle by pi changes the gradient kernel by its half-turn phase and its two component signs.

**Second derivative kernel half-turn.** Proved result `third_k_pi`: Shifting angle by pi changes the second derivative kernel by its half-turn phase and three component signs.

**Pressure kernel under a half-turn.** Proved result `pres_k_pi`: Shifting angle by pi changes the pressure kernel by its half-turn phase.

**Velocity mode at negative radius.** Proved result `vel_refl`: Reflecting radius changes a velocity mode by the half-turn phase and its component sign.

**Height gradient at negative radius.** Proved result `grad_refl2`: Reflecting radius changes a height gradient mode by the half-turn phase and its vector-component sign.

**Second height mode at negative radius.** Proved result `third_refl22`: Reflecting radius changes a second height derivative mode by the same half-turn phase and vector-component sign.

**Pressure mode at negative radius.** Proved result `pres_refl'`: Reflecting radius changes a pressure mode by the half-turn phase.

**Weak height identity for gradient modes.** Proved result `weak_height`: Gradient modes of a second-order field satisfy the height integration-by-parts identity for smooth compactly supported tests at positive radius.

**An off-axis set lies in a rectangle.** Proved result `box_sub`: The stated bounds on absolute radius and height place the off-axis set inside the corresponding symmetric rectangle.

**The off-axis rectangle is measurable.** Proved result `box_meas`: The set defined by lower and upper absolute-radius bounds and a height bound is measurable.

**A radius factor preserves integrability.** Proved result `weighted_rect`: Multiplying an integrable function on a bounded symmetric rectangle by radius preserves integrability.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Velocity modes form a height weak pair.** Proved result `modes_height_pair_velocity`: Admissible velocity and height-gradient modes form a height weak pair with unit weight.

**Gradient modes form a height weak pair.** Proved result `modes_height_pair_gradient`: Admissible height-gradient and second height-derivative modes form a height weak pair with radial weight.

**Pressure modes form a height weak pair.** Proved result `modes_height_pair_pressure`: Admissible pressure and height pressure-gradient modes form a height weak pair with radial weight.

### Breakdown.FracCell.SegmentModesPressure

Derives radial weak-pair properties for pressure modes while allowing an arbitrary additive pressure constant.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentModesPressure.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.FracInternal.SegmentModes`.

**Remove a radial weight off the axis.** Proved result `off_axis_int`: On a measurable set bounded away from zero radius, integrability of radius times a function implies integrability of the function itself.

**Compact derivative integrals vanish.** Proved result `deriv_integral_zero`: Every fixed-direction derivative of a compactly supported continuously differentiable scalar function is integrable with integral zero.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Weak gradient ignores pressure constants.** Proved result `pressure_weak`: The canonical potential of a gradient field, shifted by any real constant, has the same weak gradient against scalar tests.

**Pressure modes form a radial weak pair.** Proved result `modes_radial_pair_pressure`: For admissible data and matching order, the pressure mode and its radial pressure-gradient mode form a radial weak pair.

### Breakdown.FracCell.SegmentPairDefs

Defines the weighted local integrability and weak derivative contracts behind radial and height strip moments.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SegmentPairDefs.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellFormula`.

**Radial weak pair contract.** Definition `IsRadialWeakPair`: A radial weak pair consists of a field and radial derivative with the stated integrability up to and away from the axis and the smooth positive-radius weak identity.

**Height weak pair contract.** Definition `IsHeightWeakPair`: A height weak pair has weighted integrability on bounded rectangles, unweighted integrability off the axis and the smooth weak height identity away from zero radius.

**Radial strip moment integrand.** Definition `radialStripTerm`: The radial strip term combines the reciprocal strip width times the field with the affine ramp times its derivative, then multiplies by the height test.

**Height strip moment integrand.** Definition `heightStripTerm`: The height strip term combines the reciprocal strip height times the field with the affine ramp times its derivative, then multiplies by the radial weight and test.

### Breakdown.FracCell.ShapeGrad

Proves global Lipschitz control and the almost-everywhere gradient formula for the piecewise cylindrical fields used as spectral block tests.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/ShapeGrad.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.ShapeSlope`.

**Complex horizontal coordinate.** Definition `planar`: The planar map identifies the first two spatial coordinates with one complex number.

**Planar projection contracts distance.** Proved result `planar_dist`: Distance between horizontal projections is at most spatial distance.

**Radius as the planar norm.** Proved result `radial_eq`: The radial coordinate equals the norm of the complex horizontal projection.

**Angle as the complex argument.** Proved result `angle_eq`: The angular coordinate equals the complex argument of the horizontal projection.

**Control angular direction by distance.** Proved result `unit_bound`: The stated radius-weighted difference of complex angular directions is bounded by twice the difference of the planar points.

**Unit powers have a linear bound.** Proved result `pow_bound`: The difference of the mth powers of two unit complex numbers is bounded by m times their difference.

**Trigonometric modes from complex powers.** Proved result `trig_eq`: Cosine and sine modes are the real and imaginary parts of the corresponding power of the complex phase.

**Trigonometric modes are bounded by one.** Proved result `trig_le`: Every sine or cosine mode has absolute value at most one.

**Control a trigonometric mode difference.** Proved result `trig_dist`: A mode difference is bounded by its frequency times the difference of the unit complex phases.

**Frame vectors have norm at most one.** Proved result `frame_norm`: Each cylindrical-frame basis vector has norm at most one.

**Control the moving-frame difference.** Proved result `frame_dist`: A moving-frame vector's difference at two angles is bounded by the difference of their unit complex phases.

**Angular mode times a frame vector.** Definition `angFactor`: The angular factor is a sine or cosine mode multiplied by the chosen cylindrical-frame vector.

**Angular factors have norm at most one.** Proved result `ang_norm`: Every angular factor has norm at most one.

**Angular factors are Lipschitz off axis.** Proved result `ang_rel`: If the comparison point has radius at least R>0, the angular-factor difference is bounded by twice m+1 divided by R times spatial distance.

**Lipschitz scalar-vector products.** Proved result `prod_slope`: The stated scalar and vector bounds give the product Lipschitz constant equal to the scalar constant plus amplitude times the vector constant.

**Clamping does not enlarge distance.** Proved result `clamp_slope`: Clamping two real numbers to the same interval does not increase their distance.

**Clamping lands in the interval.** Proved result `clamp_mem`: For ordered endpoints, a clamped number lies in the closed interval.

**Clamping fixes interval points.** Proved result `clamp_of_mem`: Clamping a number already in the interval leaves it unchanged.

**Radius is one-Lipschitz.** Proved result `radial_slope`: The difference of two radial coordinates is at most the spatial distance.

**Each coordinate is one-Lipschitz.** Proved result `coord_slope`: The difference of any coordinate is at most the spatial distance.

**Height is one-Lipschitz.** Proved result `height_slopeBound`: The difference in height is at most the spatial distance.

**Clamp coefficients to the cell.** Definition `clampedCoef`: The extended coefficient evaluates the cell coefficient after clamping radius and height to the selected solid cell.

**Membership in a solid cell.** Proved result `solid_mem`: A point belongs to the solid cell exactly when its radius and height lie in their respective closed intervals.

**The solid height endpoints are ordered.** Proved result `solid_le`: An ordered original height interval gives ordered endpoints for both reflected solids.

**Boundary-zero data vanish outside.** Proved result `clamp_zero`: A coefficient vanishing on all four rectangle edges remains zero after clamping a point outside the rectangle.

**Shape field as a clamped mode sum.** Proved result `shape_eq`: For coefficients vanishing on every cell boundary, the shape field equals the finite sum of clamped coefficients times angular factors.

**One shaped term is Lipschitz.** Proved result `term_bound`: Off the axis, a continuously differentiable coefficient vanishing at the inner radius gives a globally Lipschitz clamped angular term.

**Shape fields have a Lipschitz bound.** Proved result `shapeSlope`: For a nondegenerate off-axis block with nonnegative lower height, continuously differentiable amplitudes vanishing on every radial and height boundary produce a globally Lipschitz shaped field.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.ShapeDeriv`.

**Assemble coordinate derivatives.** Proved result `vec_deriv`: If every vector coordinate has the specified derivative, the vector function has that derivative.

**Derivative of the cylindrical frame.** Definition `frameDer`: The radial frame derivative is angular, the angular frame derivative is minus radial, and the axial frame derivative is zero.

**Differentiate a frame vector.** Proved result `frame_deriv`: Each moving-frame vector has the stated angular derivative.

**Recover a point from polar data.** Proved result `polar`: A spatial point equals the cylindrical point formed from its radius, angle and height.

**Recover angle modulo two pi.** Proved result `angle_mod`: At positive radius, the recovered cylindrical angle differs from the input angle by an integer multiple of two pi.

**Integer modes ignore full turns.** Proved result `trig_mod`: An integer-frequency sine or cosine mode is unchanged by an integer number of full turns.

**The frame ignores full turns.** Proved result `frame_mod`: The cylindrical frame is unchanged by an integer number of full turns.

**Local cylindrical mode field.** Definition `localField`: The local field sums the sine and cosine coefficient functions in each cylindrical-frame direction.

**Use the local field inside one solid.** Proved result `shape_local`: At a positive-radius point belonging to only one solid, the shape field equals that solid's local cylindrical mode field.

**Translate a derivative to zero.** Proved result `shift_deriv`: A derivative at r is the derivative at zero of the function evaluated at r plus the increment.

**Radial derivative of the local field.** Proved result `radial_dir`: Differentiating the local field in radius differentiates its radial coefficient functions and keeps the angular factors fixed.

**Height derivative of the local field.** Proved result `height_dir`: Differentiating the local field in height differentiates its height coefficient functions and keeps the angular factors fixed.

**Derivative of sine or cosine.** Definition `tderiv`: The trigonometric derivative is minus sine for the cosine mode and cosine for the sine mode.

**Derivative of the angular phase.** Proved result `turn_inner`: The scaled angular phase along the normalized turning curve has derivative m divided by radius.

**Differentiate a turning mode.** Proved result `trig_turn`: The sine or cosine mode along the normalized turning curve has the chain-rule derivative with factor m divided by radius.

**Derivative of normalized angle.** Proved result `angle_inner`: The normalized angular increment has derivative one divided by radius.

**Differentiate the turning frame.** Proved result `frame_turn`: Along the normalized turning curve, the frame derivative is the angular frame derivative divided by radius.

**Angular derivative of the local field.** Proved result `turn_dir`: At positive radius, the normalized angular derivative of the local field is the stated angular-coefficient expansion.

**A radial curve has radial tangent.** Proved result `curve_r`: The cylindrical curve varying only radius has the radial frame vector as its tangent.

**A height curve has axial tangent.** Proved result `curve_z`: The cylindrical curve varying only height has the axial frame vector as its tangent.

**A turning curve has angular tangent.** Proved result `curve_t`: At nonzero radius, the normalized turning curve has the angular frame vector as its tangent.

**Expand a vector in the moving frame.** Proved result `frame_expand`: Every vector is the sum of its inner products with the cylindrical frame times those frame vectors.

**Gradient applied to a frame direction.** Proved result `grad_apply`: The shaped gradient field applied to a frame direction equals the corresponding shaped column field.

**Strict interior selects one solid.** Proved result `interior_mem`: The stated strict radial and height inequalities place a positive-radius point in exactly the selected reflected solid.

**Differentiate a coefficient in radius.** Proved result `diff_fst`: A continuously differentiable bivariate coefficient has its radial slice derivative at every point.

**Differentiate a coefficient in height.** Proved result `diff_snd`: A continuously differentiable bivariate coefficient has its height slice derivative at every point.

**Small shifts converge to the base point.** Proved result `shift_tendsto`: As the increment tends to zero, a fixed real number plus that increment tends to the fixed number.

**Gradient formula inside the solid.** Proved result `deriv_interior`: At a differentiability point strictly inside a solid away from the axis, the shape-field derivative equals the shaped gradient built from its explicit coefficients.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.ShapeNull`.

**First coordinate of the spatial encoding.** Proved result `coord0`: The spatial encoding returns the first planar coordinate in coordinate zero.

**Second encoded spatial coordinate.** Proved result `coord1`: The spatial encoding returns the second planar coordinate in coordinate one.

**Encoded height coordinate.** Proved result `coord2`: The spatial encoding returns the height in coordinate two.

**A height plane has measure zero.** Proved result `null_height`: Every fixed-height plane has spatial measure zero.

**A circle has planar measure zero.** Proved result `circle_null`: Every planar radius level set has measure zero.

**A radial cylinder has measure zero.** Proved result `null_radial`: Every fixed-radius cylinder has spatial measure zero.

**Source namespace:** `Breakdown.CellCert.Spectral.Internal.ShapeAe`.

**Solid cells are closed.** Proved result `solid_closed`: Each reflected solid cell is closed.

**Exclude the lower solid boundary.** Proved result `lower_ne`: Excluding the two possible original lower endpoints excludes the lower boundary of either reflected solid.

**Exclude the upper solid boundary.** Proved result `upper_ne`: Excluding the two possible original upper endpoints excludes the upper boundary of either reflected solid.

**Source namespace:** `Breakdown.CellCert.Spectral`.

**Shape fields have a Lipschitz bound.** Proved result `shapeSlope_holds`: For a nondegenerate off-axis block with nonnegative lower height, continuously differentiable amplitudes vanishing on every radial and height boundary produce a globally Lipschitz shaped field.

**The shaped field has its a.e. gradient.** Proved result `shapeDeriv_holds`: For a nondegenerate off-axis block with nonnegative lower height and continuously differentiable amplitudes vanishing on every boundary, the shaped field has the explicit shaped-gradient derivative almost everywhere.

### Breakdown.FracCell.SharpBoundCore

Combines the exact row decomposition, the unresolved row-class bound and the residual field estimate into the sharp cell bound.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpBoundCore.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Pairing of an unresolved row mode.** Definition `unresolvedRowPair`: The unresolved row pairing is the real cell integral of the gradient and velocity row couplings, set to zero for modes in the resolved set or band.

**Energy charged to unresolved rows.** Definition `unresolvedRowCharge`: The unresolved-row charge integrates class-weighted velocity and curl deviations against modes outside the resolved set and band.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Exact resolved and unresolved row split.** Proposition `SharpRowIdentityStatement`: This proposition decomposes the normalized high-field row pairing into the sharp coefficient row form and the sum of unresolved row pairings.

**Class bound for unresolved rows.** Proposition `UnresolvedRowClassStatement`: This proposition bounds the negative unresolved row contribution by the weighted multiplier squares plus the unresolved-row energy charge.

**Residual field bound with row charge.** Proposition `SharpYChargeStatement`: This proposition bounds the local cell form, zero-row sharp form and unresolved-row charge by the full mode density and actuator and pin pairings.

**Row form bound with unresolved charge.** Proposition `SharpRowPartStatement`: This proposition bounds the sharp row form minus its multiplier-square penalty by the unresolved charge and the normalized high-field row pairing.

**Row identity gives the row bound.** Proved result `sharpRowPart_of`: The exact sharp row identity and unresolved row-class estimate imply the sharp row-part bound.

**Combine row and residual field bounds.** Proved result `sharpBound_of_parts`: The sharp row-part bound and residual field charge estimate imply the sharp cell bound.

**Assemble the sharp cell bound.** Proved result `sharpBound_of`: The exact row identity, unresolved class estimate and residual field charge estimate imply the sharp bound.

### Breakdown.FracCell.SharpCircleBound

Splits the circle interaction into strain, mean coupling and oscillatory coupling pieces and combines their lower bounds.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCircleBound.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCircleBoundParts`.

**Strain interaction between two modes.** Definition `strainWave`: The strain wave is the negative pairing of two residual curl modes through the intervening model strain mode.

**Symmetrized coupling between modes.** Definition `couplingWave`: The coupling wave averages the two ordered matrix pairings between residual gradient and velocity modes through the model curl-gradient mode.

**Mean and oscillatory coupling loss.** Definition `couplingLoss`: The coupling loss adds the mean square-root product penalty to the split-length oscillatory quadratic penalty.

**Mean coupling loss.** Definition `meanLoss`: The mean loss is the trace-free constant times the mean gradient bound and the square roots of the gradient and velocity squares.

**Oscillatory coupling loss.** Definition `waveLoss`: The wave loss uses the wave gradient bound times the split-length combination of gradient and velocity squares.

**Off-diagonal mode coupling.** Definition `offWave`: The off-diagonal wave equals the coupling wave for distinct modes and is zero on the diagonal.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Mean-mode coupling bound.** Proposition `SharpCircleMeanStatement`: This proposition gives summability of the diagonal coupling and bounds each diagonal real part below by its negative mean loss under residual square summability.

**Off-diagonal circle coupling bound.** Proposition `SharpCircleWaveStatement`: This proposition gives iterated summability of the off-diagonal coupling and bounds its real sum below by the negative summed wave loss.

**Circle strain interaction bound.** Proposition `SharpCircleStrainStatement`: This proposition gives iterated summability of the strain interaction and bounds its real sum below by the strain bound times the negative residual curl energy.

**Full circle coupling bound.** Proposition `SharpCircleCouplingStatement`: This proposition gives iterated summability of the complete coupling wave and bounds its real sum below by the negative total coupling loss.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCircleBoundParts`.

**Matrix square sums are nonnegative.** Proved result `sumSq_nonneg'`: The sum of squared norms of matrix entries is nonnegative.

**Vector square sums are nonnegative.** Proved result `vecSq_nonneg'`: The sum of squared norms of vector components is nonnegative.

**Curl square sums are nonnegative.** Proved result `curlSq_nonneg'`: The sum of squared norms of curl components is nonnegative.

**Bound the square of three terms.** Proved result `sq_sum_three`: The square of a sum of three real numbers is at most three times the sum of their squares.

**Permutation signs have norm at most one.** Proved result `sign_norm_le`: Every complex-cast permutation sign has norm at most one.

**Bound one curl component.** Proved result `curlComp_norm_le`: The norm of a curl component is bounded by the sum of the matrix entry norms.

**Bound curl energy by matrix energy.** Proved result `curlSq_le'`: The curl-square sum is bounded by twenty-seven times the entry-square sum.

**Split strain and coupling interactions.** Proved result `pairWave_split`: The full two-mode interaction is the sum of its strain wave and coupling wave.

**Split the pointwise loss density.** Proved result `supDensity_split`: The supremum density is the strain-bound curl square plus the coupling loss.

**Bound a square-root product.** Proved result `sqrt_mul_le`: For nonnegative a and b, the product of their square roots is at most a+b.

**Mean losses are summable.** Proved result `meanLoss_summable`: A nonnegative mean gradient bound and summable residual gradient and velocity squares give a summable mean-loss sequence.

**Oscillatory losses are summable.** Proved result `waveLoss_summable`: Summable residual gradient and velocity squares give a summable wave-loss sequence.

**Total coupling losses are summable.** Proved result `couplingLoss_summable`: A nonnegative mean gradient bound and summable residual squares give a summable total coupling loss.

**Separate diagonal and off-diagonal terms.** Proved result `coupling_split`: Each coupling wave is its diagonal term, when the two modes agree, plus its off-diagonal term.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Combine mean and wave bounds.** Proved result `sharpCircleCoupling_of`: The mean-mode and off-diagonal wave estimates imply the complete circle coupling bound.

**Combine strain and coupling bounds.** Proved result `sharpCircleBound_of`: The circle strain and coupling estimates imply the circle interaction bound.

### Breakdown.FracCell.SharpCircleMean

Proves the trace-free matrix estimate controlling the mean model curl-gradient coupling of residual modes.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCircleMean.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.SharpCircleMean`.

**Trace-free coupling square identity.** Proved result `couple_identity`: For a trace-free complex matrix, the coupling-map square expands into the stated vector, bracket and mixed matrix products.

**Complex norm squared by conjugation.** Proved result `norm_sq_eq`: The squared norm of a complex number is the real part of the number times its conjugate.

**Vector squares by conjugate products.** Proved result `vecSq_eq`: The vector-square sum is the real part of the sum of component-conjugate products.

**Matrix squares by conjugate products.** Proved result `sumSq_eq`: The matrix-square sum is the real part of the sum of entry-conjugate products.

**Real form of the coupling square.** Proved result `real_identity`: For a trace-free matrix, the coupling entry-square sum equals the stated real vector, bracket and mixed-term expression.

**Bracket matrices have twice the energy.** Proved result `bracket_sq`: Summing the vector squares of all bracket rows gives twice the original vector-square sum.

**Operator bound for vector norm.** Proved result `op_sqrt`: A nonnegative operator bound controls the square root of the image vector-square sum by the same bound times the input norm.

**Complex vector Cauchy-Schwarz bound.** Proved result `vecInner_le`: The norm of a complex coordinate pairing is bounded by the product of the two square-root vector energies.

**Vector square sums are nonnegative.** Proved result `vecSq_nonneg`: The vector-square sum is nonnegative.

**Matrix square sums are nonnegative.** Proved result `sumSq_nonneg`: The matrix entry-square sum is nonnegative.

**Conjugation preserves vector energy.** Proved result `vecSq_conj`: Conjugating every component leaves the vector-square sum unchanged.

**Trace-free coupling square bound.** Proved result `coupling_sq_le`: A trace-free matrix with nonnegative operator bound g gives coupling square at most seven halves times g squared times vector energy.

**Matrix Cauchy-Schwarz bound.** Proved result `pairing_le`: The matrix pairing norm is bounded by the product of the square roots of the entry-square sums.

**Swapping a pairing conjugates it.** Proved result `pairing_swap`: Exchanging the two matrix arguments conjugates the entry pairing.

**Trace-free coupling pairing bound.** Proved result `coupling_norm_le`: A trace-free matrix with operator bound g gives the stated trace-free-constant bound for its coupling paired with any matrix.

**The two entry definitions agree.** Proved result `ent_eq`: The local Cartesian entry function equals the shared matrix-entry function.

**Rotated diagonals are integrable.** Proved result `diag_int`: Integrability of all Cartesian entries around a period implies integrability of every cylindrical-frame diagonal entry.

**The mean mode retains zero trace.** Proved result `zero_trace`: A pointwise trace-free operator around an integrable circle has zero trace in its mean Fourier mode.

**Cell points lie in the interior a.e..** Proved result `open_ae`: Almost every point of a cell rectangle lies in its open radial-height interior.

**Mean curl-gradient mode is trace-free.** Proved result `trace_ae`: For valid form and cell data, the mean model curl-gradient mode has trace zero almost everywhere at positive radius.

**Diagonal coupling as a real pairing.** Proved result `wave_eq`: The diagonal coupling wave is the real part of the residual gradient paired with the mean curl-gradient coupling of residual velocity.

**Mean losses are summable.** Proved result `meanLoss_summable'`: A nonnegative mean gradient bound and summable residual square sequences make the mean losses summable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Mean coupling is bounded by mean loss.** Proved result `sharpCircleMean_holds`: For admissible fractional cell data, summable residual gradient and velocity squares give an almost-everywhere summable diagonal coupling series whose individual real terms are bounded below by minus their mean losses.

### Breakdown.FracCell.SharpCircleSquare

Derives square summability of gradient and velocity Fourier coefficients on almost every circle from spatial Lp regularity.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCircleSquare.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCircleSquare.Internal`.

**Circle Fourier squares are summable.** Proved result `coef_summable`: For positive integer symmetry order, the squared normalized Fourier coefficients of an L2 circle function form a summable sequence.

**Spatial Lp gives circle Lp a.e..** Proved result `slice_memLp`: A spatial Lp function with finite nonzero exponent restricts to an Lp angular function on almost every positive-radius circle.

**Cell measure lies in the half-plane.** Proved result `rect_le`: The restricted measure of a valid cell rectangle is bounded by the positive-radius half-plane measure.

**Norm-controlled frame maps preserve L2.** Proved result `frame_memLp`: A continuous angle-dependent scalar map bounded by the input norm sends an L2 circle field to L2.

**Gradient mode squares are summable a.e..** Proved result `grad_ae`: For a second-order field of positive order, every gradient component's squared Fourier modes are summable on almost every cell circle.

**Velocity mode squares are summable a.e..** Proved result `vel_ae`: For a second-order field of positive order, every velocity component's squared Fourier modes are summable on almost every cell circle.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Residual circle squares are summable.** Proved result `sharpCircleSquare_holds`: For admissible fractional cell data with axisymmetric weight, the residual gradient and velocity square series are summable at almost every cell point.

### Breakdown.FracCell.SharpCircleStrain

Bounds the residual curl interaction with model strain by the cell strain operator bound.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCircleStrain.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCircleStrainParts`.

**Cell points lie in the interior a.e..** Proved result `interior_ae`: Almost every point in the cell rectangle lies in its open interior.

**The radial coordinate is nonzero a.e..** Proved result `fst_ne_ae`: Almost every point of the cell rectangle has nonzero radius.

**One curl square is bounded by entries.** Proved result `curl_sq_le`: The squared norm of any curl component is at most nine times the matrix entry-square sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Strain waves have a curl-energy bound.** Proved result `sharpCircleStrain_holds`: For admissible fractional cell data with summable residual squares, the strain-wave double series is summable almost everywhere and its real total is bounded below by minus the strain bound times the summed residual curl energy.

### Breakdown.FracCell.SharpCircleWave

Uses Fourier reconstruction on the circle and trace-free operator estimates to bound the oscillatory two-mode coupling.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCircleWave.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.SharpCircleWave`.

**Real trace-free coupling map.** Definition `realCoupling`: The real coupling map combines the permutation-sign image of matrix times vector with the stated half-weighted bracket term.

**Real coupling square identity.** Proved result `realCoupling_sq`: For a trace-free real matrix, the coupling square equals the stated seven-quarter, one-quarter and transpose mixed terms.

**Finite real Cauchy-Schwarz inequality.** Proved result `sum_mul_sq_le_three`: The square of a three-coordinate real pairing is bounded by the product of the two square sums.

**Real trace-free coupling bound.** Proved result `realCoupling_le`: A real trace-free matrix with operator bound delta gives coupling square at most seven halves times delta squared times the vector square.

**Separate real and imaginary coupling.** Proved result `couplingMap_ofReal`: Coupling a real matrix with a complex vector is the real coupling of its real part plus i times the real coupling of its imaginary part.

**Restrict a complex bound to real vectors.** Proved result `opBound_real`: A complex operator bound for a real matrix gives the same squared norm bound on real vectors.

**Complex coupling with a real matrix.** Proved result `sumSq_couplingMap_le`: A trace-free real matrix with operator bound delta gives the seven-halves coupling-square bound for complex vectors.

**Matrix pairing norm bound.** Proved result `entryPairing_norm_le`: The entry pairing norm is at most the product of the square-root matrix energies.

**Swapping a pairing conjugates it.** Proved result `entryPairing_swap`: Exchanging the matrix arguments complex-conjugates the entry pairing.

**Bound a real-model coupling pairing.** Proved result `pairing_le`: The trace-free constant and operator bound control the coupling pairing by the square-root vector and matrix energies.

**Coefficients of the coupling map.** Definition `couplingCoef`: The fixed coupling coefficients collect the permutation signs and half-weighted index conditions in the coupling map.

**Expand the coupling map in entries.** Proved result `couplingMap_eq`: Each coupling entry is the finite coefficient sum of matrix-entry and vector-component products.

**Expand a coupling pairing.** Proved result `pairing_expand`: The coupling pairing is the five-index sum of fixed coefficients times a conjugated test entry and a matrix-vector product.

**Expand the conjugated pairing.** Proved result `pairing_expand_swap`: The conjugated coupling pairing is the corresponding five-index sum with conjugated vector and matrix entries.

**Sum five finite families of series.** Proved result `hasSum_sum5`: Five nested finite sums preserve the stated sums of their component series.

**Integrate five finite index sums.** Proved result `integral_sum5`: For integrable component functions, the circle integral commutes with five nested finite sums.

**L2 circle products are integrable.** Proved result `conj_mul_integrable`: The product of a conjugated L2 circle function and another L2 function is integrable.

**Inner Fourier sum for the first pairing.** Proved result `form_first_inner`: The first ordered coupling summed over its inner mode has the stated product Fourier-coefficient expression.

**First pairing as a circle integral.** Proved result `form_first`: The double mode sum of the first ordered coupling equals its reconstructed circle integral.

**Inner Fourier sum for the second pairing.** Proved result `form_second_inner`: For real model coefficients, the second ordered coupling's inner mode sum has the stated Fourier product expression.

**Second pairing as a circle integral.** Proved result `form_second`: For real model coefficients, the double mode sum of the second ordered coupling equals its reconstructed circle integral.

**Split a square-root product.** Proved result `sqrt_mul_le_avg`: For nonnegative a,b and positive split length, their square-root product is bounded by the stated weighted arithmetic mean.

**Matrix Parseval identity for the lift.** Proved result `lift_sumSq_integral`: The integral of the reconstructed matrix-square sum equals the sum of its coefficient matrix energies.

**Vector Parseval identity for the lift.** Proved result `lift_vecSq_integral`: The integral of the reconstructed vector-square sum equals the sum of its coefficient vector energies.

**Bound the reconstructed interaction.** Proved result `form_bound`: A pointwise square-root product bound yields the split-length bound on the norm of the reconstructed circle integral.

**Operator bounds control entries.** Proved result `opBound_entry`: Every matrix entry has norm at most the nonnegative operator bound.

**One entry square is below total energy.** Proved result `sq_entry_le`: The squared norm of a matrix entry is at most the matrix entry-square sum.

**A component square is below total energy.** Proved result `sq_vec_le`: The squared norm of a vector component is at most the vector-square sum.

**Zero model gives zero coupling.** Proved result `couplingMap_zero`: The coupling map of the zero matrix and any vector is zero.

**Zero left matrix pairs to zero.** Proved result `entryPairing_zero_left`: An entry pairing with zero in its first argument is zero.

**Zero right matrix pairs to zero.** Proved result `entryPairing_zero_right`: An entry pairing with zero in its second argument is zero.

**Integrate a circle Fourier mode.** Proved result `integral_circleMode_eq`: The normalized integral of a circle Fourier mode is one for the zero mode and zero otherwise.

**Subtracting a constant changes one mode.** Proved result `coeff_sub_const`: Subtracting a constant changes only the zero Fourier coefficient by that constant.

**Lower bound for an averaged real part.** Proved result `half_re`: If two complex numbers have norm at most X, the real part of their average is at least minus X.

**Bound the full oscillatory double sum.** Proved result `form_total`: For real trace-free model matrices with the stated operator bound, the symmetric double coupling series converges and obeys the split-length lower bound.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Off-diagonal waves have a loss bound.** Proved result `sharpCircleWave_holds`: For admissible fractional cell data with summable residual squares, the off-diagonal wave double series is summable almost everywhere and its real total is bounded below by minus the summed wave losses.

### Breakdown.FracCell.SharpCoefTail

Uses the polynomial basis eigenvalue identities and weighted Bessel bounds to control all high radial and height coefficients.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCoefTail.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCoefTailInternal`.

**Radial basis polynomial derivative.** Definition `rd`: The radial derivative function evaluates the derivative of the radial basis polynomial.

**Height basis polynomial derivative.** Definition `hd`: The height derivative function evaluates the derivative of the height basis polynomial.

**Radial basis derivative is continuous.** Proved result `rd_cont`: Every radial basis derivative is continuous.

**Height basis derivative is continuous.** Proved result `hd_cont`: Every height basis derivative is continuous.

**Radial reference weight is nonnegative.** Proved result `refR_sq_le`: Inside a nondegenerate radial interval, one minus the squared reference radius is nonnegative.

**Height reference weight is nonnegative.** Proved result `refZ_sq_le`: Inside a nondegenerate height interval, one minus the squared reference height is nonnegative.

**Radial eigenvalues are nonnegative.** Proved result `radialEigen_nonneg`: Every radial polynomial eigenvalue is nonnegative.

**Height eigenvalues are nonnegative.** Proved result `heightEigen_nonneg`: Every height polynomial eigenvalue is nonnegative.

**Positive radial eigenvalues.** Proved result `radialEigen_pos`: For a nondegenerate radial interval, each nonzero-degree radial eigenvalue is positive.

**Positive height eigenvalues.** Proved result `heightEigen_pos`: For a nondegenerate height interval, each nonzero-degree height eigenvalue is positive.

**Closed-set and interval integrals agree.** Proved result `icc_interval`: For ordered endpoints, the integral over the closed interval equals the interval integral.

**Weighted radial derivative orthogonality.** Proved result `rad_orth`: Valid radial basis derivatives are orthogonal under the endpoint-vanishing line weight, with diagonal integral equal to their radial eigenvalue.

**Weighted height derivative orthogonality.** Proved result `ht_orth`: Valid height basis derivatives are orthogonal under the endpoint-vanishing height weight, with diagonal integral equal to their height eigenvalue.

**Weighted basis products are integrable.** Proved result `wbb_int'`: A continuous weight times two continuous basis functions is integrable on the compact cell rectangle.

**Weighted field-basis products integrate.** Proved result `g_int'`: A weighted-square-integrable measurable field pairs integrably with a continuous basis function under a nonnegative continuous weight.

**Weighted finite Bessel inequality.** Proved result `sq_coef_le`: For finitely many weighted orthonormal tests, the sum of squared field coefficients is bounded by the weighted field energy.

**Normalize an eigenvalue coefficient.** Proved result `term_eq`: If a positive eigenvalue times a coefficient equals an integral, its weighted squared norm equals the squared norm of the integral divided by the eigenvalue's square root.

**Scale a basis pairing integral.** Proved result `int_scale`: Dividing the test by a real scalar divides the weighted pairing integral by the same scalar.

**Reference radius is continuous.** Proved result `refR_cont`: The reference radial coordinate is continuous.

**Reference height is continuous.** Proved result `refZ_cont`: The reference height coordinate is continuous.

**Radial eigenvalue tail is summable.** Proved result `tail_radial`: The radial coefficient identity and finite weighted derivative energy imply summability of radial-eigenvalue-weighted coefficient squares.

**Height eigenvalue tail is summable.** Proved result `tail_height`: The height coefficient identity and finite weighted derivative energy imply summability of height-eigenvalue-weighted coefficient squares.

**The full coefficient energy is summable.** Proved result `tail_all`: The field square and both weighted derivative squares, together with their coefficient identities, give summability with weight one plus both eigenvalues.

**Polynomial evaluation is differentiable.** Proved result `pcd`: A real polynomial evaluated as a function is continuously differentiable.

**Radial basis inner products.** Proved result `rad_ip_orth`: The polynomial radial basis is orthonormal for the cell's radial inner product.

**Height basis interval orthogonality.** Proved result `ht_int_orth`: The height basis polynomial interval integrals give one on matching degrees and zero on different degrees.

**Radial basis eigenfunction equation.** Proved result `radial_hasDeriv`: For nonzero degree, the derivative of the weighted radial basis derivative is minus the eigenvalue times the line-weighted basis function.

**Height basis eigenfunction equation.** Proved result `height_hasDeriv`: For nonzero degree, the derivative of the weighted height basis derivative is minus the eigenvalue times the basis function.

**Reference radial weight vanishes left.** Proved result `refR_left`: The radial reference factor vanishes at the inner endpoint of a nondegenerate radial interval.

**Reference radial weight vanishes right.** Proved result `refR_right`: The radial reference factor vanishes at the outer endpoint of a nondegenerate radial interval.

**Reference height weight vanishes below.** Proved result `refZ_left`: The height reference factor vanishes at the lower endpoint of a nondegenerate height interval.

**Reference height weight vanishes above.** Proved result `refZ_right`: The height reference factor vanishes at the upper endpoint of a nondegenerate height interval.

**Weighted radial test is differentiable.** Proved result `radF_cd`: The radial basis derivative times the reference factor is continuously differentiable.

**Weighted height test is differentiable.** Proved result `htF_cd`: The height basis derivative times the reference factor is continuously differentiable.

**Radial basis polynomials are C1.** Proved result `rpoly_cd`: Every radial basis polynomial is continuously differentiable.

**Height basis polynomials are C1.** Proved result `hpoly_cd`: Every height basis polynomial is continuously differentiable.

**Separated C1 tests remain C1.** Proved result `prod_cd`: The complex-valued product of a radial C1 function and a height C1 function is C1 on the plane.

**Coefficient as a weighted basis integral.** Proved result `coef_eq`: The cell coefficient is the integral of the field times line weight and the radial-height basis product.

**Matrix selecting one component.** Definition `unitMat`: The unit coefficient matrix is one at its selected entry and zero elsewhere.

**Select one gradient mode.** Proved result `combo_grad`: Using a unit coefficient matrix in the combined gradient returns the selected gradient-mode entry.

**Select one differentiated mode.** Proved result `combo_third`: Using a unit coefficient matrix in the combined derivative returns the selected differentiated gradient-mode entry.

**Radial eigenfunction test derivative.** Proved result `rderiv_psi`: Differentiating the weighted radial derivative test gives minus the radial eigenvalue times the weighted basis product.

**Height eigenfunction test derivative.** Proved result `hderiv_psi`: Differentiating the weighted height derivative test gives minus the height eigenvalue times the basis product.

**Radial gradient coefficient identity.** Proved result `strain_radial`: The weak radial mode identity expresses a nonconstant gradient coefficient times its radial eigenvalue as the weighted differentiated-mode pairing.

**Height gradient coefficient identity.** Proved result `strain_height`: The weak height mode identity expresses a nonconstant gradient coefficient times its height eigenvalue as the weighted differentiated-mode pairing.

**Radial velocity coefficient identity.** Proved result `vel_radial`: The weak radial velocity identity expresses a nonconstant velocity coefficient times its radial eigenvalue as a weighted gradient-mode pairing.

**Height velocity coefficient identity.** Proved result `vel_height`: The height integration-by-parts identity expresses a nonconstant velocity coefficient times its height eigenvalue as a weighted gradient-mode pairing.

**A bounded extra weight preserves energy.** Proved result `wmono`: Multiplying a line-weighted square by a continuous factor between zero and one preserves its integrability.

**Convert radial to line-weighted energy.** Proved result `rmono`: On a valid cell, an integrable radial-weighted square gives an integrable line-weighted square.

**Radial reference factor bounds.** Proved result `gR01`: On a valid cell, one minus squared reference radius lies between zero and one.

**Height reference factor bounds.** Proved result `gZ01`: On a valid cell, one minus squared reference height lies between zero and one.

**Gradient coefficient tail is summable.** Proved result `strain_tail`: Mode square integrability and both weak derivative identities give summability of eigenvalue-weighted gradient coefficient squares.

**Velocity coefficient tail is summable.** Proved result `vel_tail`: The radial and height velocity weak identities give summability of eigenvalue-weighted velocity coefficient squares.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble coefficient tail control.** Proved result `sharpCoefTail_of`: The mode integrability and radial and height weak identities imply the sharp coefficient-tail statement.

### Breakdown.FracCell.SharpCore

Separates row multipliers from the sharp form and combines coefficient-tail and bound statements into the sharp core estimate.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCore.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCoreInternal`.

**Matrix pairing preserves addition.** Proved result `ep_add`: The matrix entry pairing is additive in its second argument.

**Vector pairing preserves addition.** Proved result `vp_add`: The vector pairing is additive in its second argument.

**Split an added strain target.** Proved result `pen_add`: Adding a matrix to the strain target adds exactly its linear strain pairing to the penalty.

**Split an added velocity target.** Proved result `vpen_add`: Adding a vector to the velocity target adds exactly its linear velocity pairing to the penalty.

**Separate the row strain target.** Proved result `target_split`: The full strain target is the zero-row target plus the row-multiplier strain target.

**Separate the row velocity target.** Proved result `vtarget_split`: The full velocity target is the zero-row target plus the row-multiplier velocity target.

**Separate a sharp strain term.** Proved result `strain_split`: Each sharp strain term is its zero-row term plus the corresponding row strain term.

**Separate a sharp velocity term.** Proved result `vel_split`: Each sharp velocity term is its zero-row term plus the corresponding row velocity term.

**Separate the far coefficient term.** Proved result `far_split`: The sharp far term is its zero-row far term plus the row far term.

**Separate the whole sharp row form.** Proved result `form_split`: When the far sums converge, the full sharp form is its zero-row form plus the sharp row form.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The sharp far sum converges.** Proved result `sharpFar_summable`: The target-square statement and summability of the weighted coefficient energy give summability of the sharp far term.

**Core estimate from target and splitting.** Proved result `sharpCore_of`: The target-square and sharp-splitting statements imply the sharp core statement.

**Split from energy and bound statements.** Proved result `sharpSplit_of`: The coefficient energy and sharp bound statements imply the sharp splitting statement.

**Assemble the sharp core estimate.** Proved result `sharpCore_of_parts`: The target-square, coefficient energy and sharp bound statements imply the sharp core statement.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCoreInternal`.

**The combined eigenvalue is nonnegative.** Proved result `eig_nonneg`: The sum of radial and height eigenvalues is nonnegative.

**A linear weight has an absolute bound.** Proved result `lin_bound`: The stated affine upper bound with nonnegative L is dominated by the displayed absolute-value constant times one plus L.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Coefficient tails give sharp energy.** Proved result `sharpEnergy_of`: The coefficient-tail statement implies summability of the sharp coefficient energy.

**Core estimate from coefficient tails.** Proved result `sharpCore_of_leaves`: The target-square, coefficient-tail and sharp bound statements imply the sharp core statement.

### Breakdown.FracCell.SharpCoreSt

Defines the row-dependent sharp coefficient forms and the energy, splitting and bound propositions used by their assembly.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCoreSt.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Linear pairing of strain components.** Definition `strainLin`: The linear strain term is twice the real sum of the symmetric and antisymmetric matrix pairings.

**Linear velocity pairing.** Definition `velLin`: The linear velocity term is twice the real vector pairing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**Row-multiplier strain target.** Definition `rowStrainTarget`: The strain target sums row-multiplier-weighted folded coupling coefficients on the resolved set and band, and is zero on other modes.

**Row-multiplier velocity target.** Definition `rowVelocityTarget`: The velocity target is the row-multiplier-weighted sum of velocity coupling coefficients.

**High coefficient strain row term.** Definition `rowStrainTerm`: The strain row term keeps its linear pairing outside the low resolved coefficient block and is zero inside that block.

**High coefficient velocity row term.** Definition `rowVelocityTerm`: The velocity row term keeps its linear pairing when the maximum polynomial degree is at least the high cutoff.

**Far coefficient row contribution.** Definition `rowFarTerm`: Beyond the near cutoff, the far row term sums the selected strain and resolved velocity row terms and is zero below that cutoff.

**The complete sharp row form.** Definition `sharpRowForm`: The sharp row form adds its finite near-degree strain and velocity sums to the infinite far-degree row sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Common split for field and row bounds.** Proposition `SharpSplitStatement`: This proposition asks for summable coefficient arrays and one common charge that bounds both the residual field form and every supported row-multiplier form.

**Gradient-mode cell coefficients.** Definition `sharpStrainCoef`: The sharp strain coefficients are the cell basis coefficients of each gradient-mode entry.

**Velocity-mode cell coefficients.** Definition `sharpVelocityCoef`: The sharp velocity coefficients are the cell basis coefficients of each velocity-mode component.

**Sharp coefficient energy is summable.** Proposition `SharpEnergyStatement`: This proposition requires summability of the far-degree weighted symmetric, antisymmetric and velocity coefficient energies.

**One charge bounds field and row forms.** Proposition `SharpBoundStatement`: This proposition requires a common real charge controlling the sharp residual field form and all supported row-multiplier forms for the true coefficients.

**Eigenvalue-weighted tails are summable.** Proposition `SharpCoefTailStatement`: This proposition requires square summability of the selected gradient and velocity coefficients with weight one plus radial and height eigenvalues.

### Breakdown.FracCell.SharpCrossYStrainSquare

Supplies the weighted square integrability of the Y strain target needed to justify residual cross integrals.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCrossYStrainSquare.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The Y strain target has finite energy.** Proved result `yStrainSquare_holds`: For admissible fractional cell data, the unfolded Y strain and velocity targets are weighted square integrable in every Y mode.

### Breakdown.FracCell.SharpCrossYTargetSquare

Combines strain and velocity regularity into the square-integrability interface for the Y target.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCrossYTargetSquare.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The Y target has finite energy.** Proved result `yTargetSquare_holds`: For admissible fractional cell data, the folded Y strain target is weighted square integrable on the Y modes and the Y velocity target is weighted square integrable on resolved modes.

### Breakdown.FracCell.SharpCrossYUnfolded

Expands the residual pairing with the Y target into wave, matrix and linear terms, with all integral interchanges justified.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpCrossYUnfolded.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Regularity for the Y pairing expansion.** Proposition `YUnfoldedRegularStatement`: This proposition requires integrability of the residual pairings, both orders of the low-to-sharp wave interaction and the matrix cross density on the specified finite mode sets.

**Wave cross terms are integrable.** Proposition `WaveCrossRegularStatement`: This proposition requires both ordered low-to-sharp wave pairings to be integrable for resolved modes against resolved or band modes.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCrossYUnfolded.Internal`.

**Wave contribution to one mode.** Definition `wavePart`: The wave contribution sums both orders of the resolved-to-sharp interaction when the mode is resolved or in the band, and is zero otherwise.

**Matrix contribution to one mode.** Definition `matPart`: The matrix contribution is the matrix cross density on resolved modes and zero on the remaining modes.

**Linear contribution to one mode.** Definition `linPart`: The linear contribution pairs the residual gradient with the actuator coefficients and twice the pin multipliers, taking real parts.

**Expand the Y pairing pointwise.** Proved result `pointwise`: For symmetric model strain and Hermitian local matrices, twice the line-weighted Y strain and velocity pairing equals radius times the wave, matrix and linear contributions.

**Integrate the three contributions.** Proved result `mode_split`: When the two Y pairings and the wave and matrix terms are integrable, their mode integral splits into the wave, matrix and linear integrals.

**Finite wave contribution is integrable.** Proved result `wave_integrable`: Integrability of every ordered low-to-sharp wave pairing implies integrability of their finite wave contribution.

**Restricted matrix term is integrable.** Proved result `mat_integrable`: Integrability of the matrix cross density on resolved modes implies integrability of its zero-extended matrix contribution.

**Collect all wave cross terms.** Proved result `wave_sum_eq`: Summing wave integrals over any finite set containing the resolved and band modes gives the wave cross term on their union.

**Collect the matrix cross terms.** Proved result `mat_sum_eq`: Summing matrix-contribution integrals over any finite set containing the resolved modes gives the matrix cross term.

**The linear term has finite support.** Proved result `lin_zero`: For valid cell data, the integrated linear contribution vanishes outside the Y mode set.

**Collect the linear residual term.** Proved result `lin_sum_eq`: The sum of the linear contribution integrals over the Y modes equals the linear residual term.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The regular Y expansion holds.** Proved result `yUnfolded_holds`: The regularity interface implies the integral expansion of the Y residual pairing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpCrossYUnfolded.Internal`.

**The residual gradient has finite energy.** Proved result `sharp_grad_square`: The projection-coefficient identity and weighted gradient-mode square integrability imply weighted square integrability of each residual gradient entry on a valid cell basis.

**The residual velocity has finite energy.** Proved result `sharp_vel_square`: The projection-coefficient identity and weighted velocity-mode square integrability imply weighted square integrability of each residual velocity entry on a valid cell basis.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble regularity of the Y expansion.** Proved result `yUnfoldedRegular_of`: The field-mode, projection, Y-strain, density and wave-cross regularity interfaces jointly imply the regularity needed for the Y expansion.

**Assemble the Y pairing expansion.** Proved result `yUnfolded_of_leaves`: The field-mode, projection, Y-strain, density and wave-cross regularity interfaces imply the expanded Y residual pairing.

### Breakdown.FracCell.SharpDensityModeSeries

Proves angular Fourier summability of velocity and gradient mode energies, including angular derivative weights, from second-order field regularity.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpDensityModeSeries.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpDensityModeSeries.Internal`.

**Identify the angular Fourier character.** Proved result `phase_eq`: The complex angular phase is the circle Fourier character with integer frequency minus n times m on the interval from minus pi to pi.

**Finite Fourier coefficient bound.** Proved result `coeff_sq_sum_real`: For a square-integrable circle function and positive mode spacing, every finite sum of sampled Fourier coefficient squares is bounded by its normalized angular square integral.

**Convert a complex square to an enorm.** Proved result `sq_enorm`: The nonnegative-real embedding of a complex norm squared equals the square of its extended norm.

**Extended Fourier coefficient bound.** Proved result `coeff_sq_sum`: For any circle function and positive mode spacing, finite sampled coefficient enorm squares are bounded by the normalized angular lower integral.

**Finite gradient-mode square bound.** Proved result `gm_sum`: A finite sum of one gradient component's mode enorm squares is bounded by the normalized angular lower integral of the full gradient norm squared.

**Finite velocity-mode square bound.** Proved result `mv_sum`: A finite sum of one velocity component's mode enorm squares is bounded by the normalized angular lower integral of the velocity norm squared.

**Finite derivative-mode square bound.** Proved result `mt_sum`: A finite sum of one differentiated-gradient component's mode enorm squares is bounded by the normalized angular lower integral of the full derivative tensor norm squared.

**Compare line weight with radius.** Proved result `weight_le`: On a valid cell, the line weight is nonnegative and bounded by a fixed nonnegative constant times radius.

**Transfer finite energy to the cylinder.** Proved result `fin_bound`: A nonnegative spatial function with finite lower integral has finite cylindrical weighted lower integral under the stated finite geometric bound.

**Summability from finite-sum bounds.** Proved result `summable_of_bound`: A nonnegative integrable family whose finite sums are dominated by a finite-integral function has summable integrals.

**A cell cylinder lies in a fixed ball.** Proved result `cyl_mem_ball`: Every point of the valid cell cylinder lies in the closed ball of radius twice the outer radial endpoint plus the upper height endpoint.

**Velocity-mode energies are summable.** Proved result `vel_part`: For a second-order field and positive mode spacing, the line-weighted square integrals of each velocity component are summable over angular modes.

**The frame-rotation contribution.** Definition `turnCoef`: The frame-rotation coefficient adds the two frame-turn actions on a matrix entry.

**Separate angular frequency and rotation.** Proved result `comb_split`: Multiplication of a matrix entry by the imaginary angular frequency equals the angular combination plus the frame-rotation contribution.

**Frame-turn entries have norm at most one.** Proved result `frameTurn_norm`: Every entry of the frame-turn matrix has norm at most one.

**Bound the frame-rotation contribution.** Proved result `turnCoef_norm`: The frame-rotation coefficient norm is bounded by twice the sum of the matrix-entry norms.

**Square a nine-entry norm sum.** Proved result `sum_sq_le`: The square of the sum of the nine matrix-entry norms is at most nine times their squared-norm sum.

**Bound the square of two complex terms.** Proved result `add_sq_le`: The squared norm of a sum of two complex numbers is at most twice the sum of their squared norms.

**Control the angular frequency weight.** Proved result `comb_bound`: Frequency squared times one matrix-entry square is bounded by twice its angular-combination square plus seventy-two times the full matrix square.

**Convert the matrix square to enorms.** Proved result `sum2_enorm`: Embedding the finite sum of matrix-entry squared norms gives the corresponding sum of extended-norm squares.

**Radius is positive almost everywhere.** Proved result `rect_pos_ae`: On a valid cell rectangle, radius is positive almost everywhere, including when the rectangle reaches the axis.

**Angular derivative identity a.e..** Proved result `angular_ae`: For a second-order field, each angular gradient mode agrees almost everywhere on the cell with the angular combination of gradient modes.

**Frequency-weighted gradient summability.** Proved result `grad_part`: For a second-order field and positive mode spacing, gradient-mode line-weighted square integrals remain summable after multiplication by one plus mode frequency squared.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The mode-energy series interface holds.** Proved result `modeSeries_holds`: Velocity and frequency-weighted gradient mode energies satisfy the mode-series interface.

### Breakdown.FracCell.SharpEnergyModeSum

Uses cell Parseval identities to identify residual strain, curl and velocity energies with their infinite coefficient-square sums.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpEnergyModeSum.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.ModeSquareSumInternal`.

**The line weight is continuous.** Proved result `lw_cont`: The cell line weight is continuous. Source: `Breakdown.FracCell.SharpEnergyModeSum:17`.

**The line weight is nonnegative.** Proved result `lw_nonneg`: On a valid cell, the cell line weight is nonnegative.

**The cell rectangle is measurable.** Proved result `rect_meas`: The closed radial-height cell rectangle is measurable.

**Coefficients respect constant factors.** Proved result `coef_const_mul`: Multiplication by a complex scalar commutes with the cell coefficient integral.

**Weighted squares respect scalar factors.** Proved result `ws_const_mul`: Multiplying a weighted square-integrable function by a complex scalar preserves weighted square integrability.

**Expand a finite complex norm square.** Proved result `sq_expand`: The square of a finite complex sum expands as the double sum of each term times the conjugate of every other term.

**Parseval for a finite linear map.** Proved result `quad_hasSum`: For a weighted square-integrable vector family and a real finite linear map, the coefficient quadratic series sums to the integral of the transformed squared norm.

**Finite quadratic density is integrable.** Proved result `quad_integrable`: Applying a finite real linear map to weighted square-integrable components gives an integrable weighted quadratic density.

**The finite identity matrix.** Definition `idMat`: The identity matrix has entry one on equal indices and zero otherwise.

**Matrix energy as a quadratic form.** Proved result `sumSq_quad`: The sum of squared matrix-entry norms is the quadratic form of the finite identity matrix.

**Vector energy as a quadratic form.** Proved result `vecSq_quad`: The sum of squared vector-entry norms is the quadratic form of the finite identity matrix.

**The matrix-to-curl coefficient map.** Definition `curlMat`: The curl coefficient map is given by the permutation sign on the output and reversed input matrix indices.

**Curl energy as a quadratic form.** Proved result `curlSq_quad`: The curl square equals the quadratic form obtained by applying the curl coefficient map.

**The half-sum parallelogram identity.** Proved result `par_sq`: The squared norms of the half-sum and half-difference of two complex numbers add to half the sum of their squared norms.

**Split matrix energy by symmetry.** Proved result `sym_anti`: The symmetric and antisymmetric matrix squares add to the full matrix-entry square sum.

**Square a complex half-difference.** Proved result `half_sub`: The squared norm of half a complex difference equals one quarter of the squared norm of that difference.

**Curl energy equals twice skew energy.** Proved result `curl_anti`: The curl square of a matrix equals twice its antisymmetric square.

**Residual gradient is square integrable.** Proved result `sharp_ws`: Subtracting the resolved polynomial projection from a weighted square-integrable gradient mode leaves a weighted square-integrable residual.

**Coefficients of the gradient residual.** Proved result `sharp_coef`: The residual gradient coefficient equals the original sharp strain coefficient on the retained strain indices and is zero elsewhere.

**Residual velocity is square integrable.** Proved result `vel_ws`: Subtracting the velocity projection from a weighted square-integrable mode leaves a weighted square-integrable residual.

**Coefficients of the velocity residual.** Proved result `vel_coef`: For a resolved mode and positive degree cutoff, residual velocity coefficients equal the full coefficients at or above the high-degree threshold and vanish below it.

**Finite energy of derivative combinations.** Proved result `third_int`: For a second-order field, every finite linear combination of differentiated gradient modes has integrable radial-weighted square.

**Finite second-derivative mode energy.** Proved result `second_int`: For a second-order field, the radial-weighted second-derivative mode square is integrable on a valid cell.

**Curl-gradient modes have finite energy.** Proved result `curl_int`: For a second-order field, the radial-weighted curl-gradient mode square is integrable on a valid cell.

**Sum the residual strain coefficients.** Proved result `strain_sum`: The selected symmetric and antisymmetric coefficient-square series sums to the line-weighted residual gradient energy.

**Sum the residual curl coefficients.** Proved result `curl_sum`: Twice the selected antisymmetric coefficient-square series sums to the line-weighted residual curl energy.

**Sum the high-degree velocity squares.** Proved result `vel_sum`: For resolved modes and a positive degree cutoff, the high-degree velocity coefficient-square series sums to the residual velocity energy.

**Residual strain energies are integrable.** Proved result `strain_int`: The residual gradient and curl square densities are integrable with the cell line weight.

**Residual velocity energy is integrable.** Proved result `vel_int`: The residual velocity square density is integrable with the cell line weight.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Residual coefficient energy sums hold.** Proved result `modeEnergySum_holds`: The strain, curl and velocity residuals satisfy the mode-energy summation interface.

### Breakdown.FracCell.SharpEnergyStrainIdentity

Combines shifted angular estimates for symmetric and antisymmetric matrices with radial and height spectral tails to control residual strain energy.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpEnergyStrainIdentity.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyStrainIdentityInternal`.

**Rotation acts on both matrix indices.** Definition `turnOp`: The rotation operator is minus the sum of the frame-turn actions on the two matrix indices.

**Split the angular matrix operator.** Proved result `comb_eq`: The angular combination is imaginary frequency times the matrix plus its rotation operator.

**A lower bound for a complex sum.** Proved result `sq_ge`: The squared norm of a complex sum is bounded below by the two squared norms minus twice the product of the norms.

**Sum the complex lower bounds.** Proved result `sum_ge`: The summed square of a finite complex sum has the corresponding lower bound in terms of the two square sums and the norm-product sum.

**Bound the sum of norm products.** Proved result `sum_prod_sq_le`: The square of a finite sum of norm products is bounded by the product of the two squared-norm sums.

**Extract a shifted frequency bound.** Proved result `final`: A quadratic lower bound and a rotation bound by C squared imply the lower bound using the square of the positive part of absolute frequency minus C.

**Rotation bound for symmetric matrices.** Proved result `turn_sym`: The rotation energy of a symmetric complex matrix is at most four times its matrix energy.

**Rotation bound for skew matrices.** Proved result `turn_anti`: The rotation energy of an antisymmetric complex matrix is at most its matrix energy.

**Angular action on the symmetric part.** Proved result `sym_part`: Taking the symmetric part commutes with the angular combination operator.

**Angular action preserves the skew part.** Proved result `anti_part`: Taking the antisymmetric part commutes with the angular combination operator.

**Symmetric and skew energies add.** Proved result `split_sq`: The symmetric and antisymmetric square sums add to the full matrix square sum.

**Shifted angular strain lower bound.** Proved result `comb_bound`: The angular-combination energy bounds the symmetric energy with frequency shift two and the antisymmetric energy with frequency shift one, using positive parts.

**Assemble the shifted strain series.** Proved result `assemble`: Nonnegative spectral weights, summable gradient bounds and angular coefficient bounds give summability and the stated total bound for the shifted symmetric and antisymmetric coefficient series.

**The projection lies in the degree space.** Proved result `proj_mem`: The cell projection is a polynomial within its prescribed radial and height degree bounds.

**Subtract a continuous projection.** Proved result `sub_sq_int`: Subtracting a continuous polynomial from a measurable function with integrable line-weighted square preserves both properties.

**Full coefficient squares satisfy Bessel.** Proved result `coefSq_full`: Weighted square integrability gives a summable coefficient-square series whose total is at most the weighted square norm.

**High coefficients satisfy a tail bound.** Proved result `coefSq_tail`: Weighted square integrability gives summability of the high-degree coefficient squares, with total at most the projection-residual square norm.

**Finite energy of angular gradient modes.** Proved result `ang_int`: For a second-order field, the angular gradient mode is measurable and its line-weighted square is integrable.

**Tail eigenvalues are nonnegative.** Proved result `tailLam_nonneg`: The cell tail eigenvalue is nonnegative under the valid cell hypotheses.

**The angular weight is nonnegative.** Proved result `angularWeight_nonneg`: The cell angular weight is nonnegative under the valid cell hypotheses.

**Finite radial coefficient energy bound.** Proved result `radial_fin`: The radial coefficient identity bounds every finite selected radial-eigenvalue-weighted coefficient sum by the weighted radial derivative energy.

**Finite height coefficient energy bound.** Proved result `height_fin`: The height coefficient identity bounds every finite selected height-eigenvalue-weighted coefficient sum by the weighted height derivative energy.

**Sum the combined derivative coefficients.** Proved result `grad_gen`: The radial and height coefficient identities give summability of the selected tail-eigenvalue series and bound it by inner radius times the two weighted derivative energies.

**Finite radial and height mode energies.** Proved result `third_int`: For a second-order field, radial and height differentiated-gradient modes are measurable and have integrable weighted squares.

**Subtract a polynomial under any weight.** Proved result `sub_sq_intW`: For a continuous nonnegative weight, subtracting a continuous polynomial preserves measurability and weighted square integrability on the cell.

**Radial eigenfunction parts identity.** Proved result `rad_ibp`: The weighted radial derivative pairing with a monomial equals the radial eigenvalue times the corresponding polynomial pairing. Source: `Breakdown.FracCell.SharpEnergyStrainIdentity:562`.

**Height eigenfunction parts identity.** Proved result `ht_ibp`: The weighted height derivative pairing with a monomial equals the height eigenvalue times the corresponding polynomial pairing. Source: `Breakdown.FracCell.SharpEnergyStrainIdentity:589`.

**Differentiate the radial polynomial sum.** Proved result `rderiv_poly`: The radial derivative of a bivariate polynomial coefficient sum is the sum of its differentiated radial monomials.

**Differentiate the height polynomial sum.** Proved result `hderiv_poly`: The height derivative of a bivariate polynomial coefficient sum is the sum of its differentiated height monomials.

**High radial derivative pairings vanish.** Proved result `poly_rad_zero`: A polynomial within the projection degree has zero weighted radial-derivative pairing with a higher basis index when the radial basis degree is nonzero.

**High height derivative pairings vanish.** Proved result `poly_ht_zero`: A polynomial within the projection degree has zero weighted height-derivative pairing with a higher basis index when the height basis degree is nonzero.

**Derivative coefficient tail bound.** Proved result `grad_tail`: The high-degree tail-eigenvalue-weighted coefficient series is summable and bounded by the residual gradient weight.

**Full derivative coefficient bound.** Proved result `grad_full`: The full tail-eigenvalue-weighted coefficient series is summable and bounded by the full gradient weight.

**Angular coefficient tail bound.** Proved result `ang_tail`: The high-degree angular coefficient-square series is summable and bounded by the angular projection-residual square norm.

**Full angular coefficient bound.** Proved result `ang_full`: The full angular coefficient-square series is summable and bounded by the full angular square norm.

**Angular differentiation almost surely.** Proved result `ang_ae`: For second-order fields, the angular differentiated-gradient mode agrees almost everywhere with the angular combination of gradient modes.

**Angular action on the cell coefficients.** Proved result `ang_coef`: Taking a cell coefficient of the angular gradient mode equals applying the angular combination to the gradient coefficients.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The shifted strain identity holds.** Proved result `modeStrainIdentity_holds`: The radial, height and shifted angular bounds establish the mode-strain identity interface.

### Breakdown.FracCell.SharpEnergyTailRegular

Proves the summability needed to add the second-derivative and curl-gradient energy bounds over angular modes.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpEnergyTailRegular.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyTailRegular.Internal`.

**Derivative modes as Fourier coefficients.** Proved result `third_coef`: A differentiated-gradient mode is the angular slice Fourier coefficient of the corresponding rotated derivative-tensor component.

**Derivative-component mode summability.** Proved result `third_sum`: For measurable tensor data with integrable squared entries and positive mode spacing, component mode energies are integrable and their integrals are summable.

**Second-derivative mode summability.** Proved result `second_sum`: For tensor data with integrable squared entries and positive mode spacing, the full second-derivative mode energies have summable integrals.

**Bound the curl-gradient mode energy.** Proved result `curlGrad_le`: The curl-gradient mode square is at most twenty-seven times the full second-derivative mode square.

**Total mode energies are summable.** Proved result `modeEnergy_summable`: For a second-order field and positive mode spacing, the complete cell mode-energy terms form a summable series.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble regularity of the energy tail.** Proved result `energyTailRegular_of_series`: The mode-series interface implies the energy-tail regularity interface.

### Breakdown.FracCell.SharpEnergyVelocityCoef

Proves the high-degree velocity coefficient bound directly using antiderivatives, orthogonal derivative tests and complementary gradient tails.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpEnergyVelocityCoef.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyVelocityCoefInternal`.

**A polynomial antiderivative.** Definition `antider`: The antiderivative is the sum of each polynomial coefficient divided by its successor degree times that successor monomial.

**Differentiate the antiderivative.** Proved result `antider_deriv`: The derivative of the constructed polynomial antiderivative equals the original polynomial.

**Degree of the polynomial antiderivative.** Proved result `antider_deg`: The antiderivative degree is at most one more than the original polynomial degree.

**Radial derivative tests miss low degrees.** Proved result `rad_low`: A radial basis derivative is orthogonal under its derivative weight to a basis polynomial whose degree plus one is smaller.

**Height derivative tests miss low degrees.** Proved result `ht_low`: A height basis derivative is orthogonal under its derivative weight to a basis polynomial whose degree plus one is smaller.

**A smaller weight preserves finite energy.** Proved result `wle_int`: A continuous nonnegative weight bounded by the cell line weight preserves integrability of a weighted square.

**Energy after a finite projection.** Proved result `sq_split`: The square norm after subtracting a finite orthonormal projection equals the full square norm minus the selected coefficient-square sum.

**Joint derivative and projection bound.** Proved result `proj_coef_le`: Weighted orthonormal derivative tests orthogonal to the selected ordinary basis give a joint finite Bessel bound for both sets of coefficients.

**The radial derivative weight.** Definition `wr`: The radial derivative weight is cell line weight times one minus reference radius squared.

**The height derivative weight.** Definition `wz`: The height derivative weight is cell line weight times one minus reference height squared.

**A normalized radial derivative test.** Definition `br`: The radial derivative test is the radial basis derivative times the height basis polynomial divided by the square root of its radial eigenvalue.

**A normalized height derivative test.** Definition `bz`: The height derivative test is the radial basis polynomial times the height basis derivative divided by the square root of its height eigenvalue.

**The radial weight is continuous.** Proved result `wr_cont`: For a fixed cell, the radial energy weight ℓ(r)(1−r̂²), where ℓ is its line weight and r̂ its affine reference coordinate, is continuous in the meridian variables.

**The height weight is continuous.** Proved result `wz_cont`: For a fixed cell, the height energy weight ℓ(r)(1−ẑ²), where ℓ is its radial line weight and ẑ its affine height coordinate, is continuous in the meridian variables.

**Radial derivative tests are continuous.** Proved result `br_cont`: Every normalized radial derivative test is continuous.

**Height derivative tests are continuous.** Proved result `bz_cont`: Every normalized height derivative test is continuous.

**The radial weight is nonnegative.** Proved result `wr_nonneg`: The radial weight is nonnegative on a valid cell rectangle.

**The height weight is nonnegative.** Proved result `wz_nonneg`: The height weight is nonnegative on a valid cell rectangle.

**The radial weight is at most line weight.** Proved result `wr_le`: On a valid cell rectangle, the radial derivative weight is bounded by the cell line weight.

**The height weight is at most line weight.** Proved result `wz_le`: On a valid cell rectangle, the height derivative weight is bounded by the cell line weight.

**Radial derivative tests are orthonormal.** Proved result `br_orth`: For a valid cell basis, normalized radial derivative tests with nonzero radial degree are orthonormal under the radial derivative weight.

**Height derivative tests are orthonormal.** Proved result `bz_orth`: For a valid cell basis, normalized height derivative tests with nonzero height degree are orthonormal under the height derivative weight.

**A high radial test misses low degrees.** Proved result `br_zero`: A normalized radial derivative test is orthogonal to an ordinary basis function whose radial degree plus one lies below its radial degree.

**A high height test misses low degrees.** Proved result `bz_zero`: A normalized height derivative test is orthogonal to an ordinary basis function if their radial indices differ or its height degree is more than one above the ordinary height degree.

**Radial velocity coefficient pairing.** Proved result `radial_term`: The radial-eigenvalue-weighted velocity coefficient square equals the squared pairing of the radial velocity derivative with the normalized radial derivative test.

**Height velocity coefficient pairing.** Proved result `height_term`: The height-eigenvalue-weighted velocity coefficient square equals the squared pairing of the height velocity derivative with the normalized height derivative test.

**Joint finite radial velocity bound.** Proved result `radial_fin`: A finite high-radial-degree velocity coefficient sum plus separated low-degree radial-gradient coefficient squares is bounded by the radial-gradient energy.

**Joint finite height velocity bound.** Proved result `height_fin`: A finite high-height-degree velocity coefficient sum plus its complementary low-degree height-gradient coefficient squares is bounded by the height-gradient energy.

**Exact cell Parseval identity.** Proved result `coef_hasSum`: For a weighted square-integrable function, the full cell coefficient-square series sums to its weighted square norm.

**Remove a bounded complementary series.** Proved result `tail_le`: If a nonnegative term plus every finite complementary coefficient sum is bounded by the full coefficient sum, that term is bounded by the remaining tail.

**Split a selected summable tail.** Proved result `split_le`: A covered selected tail of a nonnegative summable family is bounded by a finite window plus the specified broader tail.

**Split a finite range at a cutoff.** Proved result `range_split`: A finite sum through the upper cutoff splits into its initial range and the conditional remainder above the lower cutoff.

**Identify the top degree contribution.** Proved result `top_eq`: For degree cutoff at least two, the top contribution equals the finite highest-edge gradient coefficient sums.

**Control the two gradient tails.** Proved result `top_bound`: The selected radial and height gradient coefficient tails are bounded by the top-degree contribution plus the coefficients outside the finite degree square.

**Symmetric and skew energies add.** Proved result `sym_anti`: The symmetric and antisymmetric coefficient energies add to the full matrix coefficient energy.

**Finite high-degree velocity bound.** Proved result `fin_bound`: For a positive degree cutoff, every finite eigenvalue-weighted high-degree velocity coefficient sum is bounded by the two selected gradient coefficient tails.

**The weighted velocity tail is summable.** Proved result `vel_summ`: The eigenvalue-weighted high-degree velocity coefficient series is summable under the field and cell hypotheses.

**Bound gradient tails by strain tails.** Proved result `strain_bound`: The selected radial and height gradient coefficient tails are bounded by the full symmetric and antisymmetric strain coefficient tail.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The velocity coefficient bound holds.** Proved result `modeVelocityCoef_holds`: The direct tail estimates establish the velocity coefficient bound interface.

### Breakdown.FracCell.SharpEnergyVorticityIdentity

Derives the residual vorticity estimate from the angular shift-one curl bound and radial and height spectral-tail inequalities.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpEnergyVorticityIdentity.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpEnergyVorticityIdentityInternal`.

**Skew energy equals half curl energy.** Proved result `anti_curl`: Twice the antisymmetric matrix square equals the sum of the three curl-component squares.

**Angular action on curl coordinates.** Proved result `curl_ang`: The curl of the angular matrix combination is the frequency action on the curl vector together with rotation of its first two components.

**The angular curl shift-one bound.** Proved result `ang_w`: The squared positive part of absolute frequency minus one times the vector energy is bounded by its angular frequency-and-rotation energy.

**Shifted angular vorticity bound.** Proved result `ang_ineq`: The angular-combination curl energy bounds the original curl energy weighted by the squared positive part of absolute frequency minus one.

**Angular relation for gradient modes.** Proposition `ModeAngularRelationStatement`: This proposition requires the angular differentiated-gradient mode to agree almost everywhere with the angular combination of gradient modes.

**Polynomials have finite support.** Proposition `PolyCoefTailStatement`: This proposition requires a cell polynomial within degree Q to have zero coefficient whenever either basis degree exceeds Q.

**Radial control of coefficient tails.** Proposition `RadialTailStatement`: This proposition bounds every finite high-degree radial-eigenvalue-weighted coefficient sum by the weighted radial derivative residual norm, given square integrability and the weak radial identity.

**Height control of coefficient tails.** Proposition `HeightTailStatement`: This proposition bounds every finite high-degree height-eigenvalue-weighted coefficient sum by the weighted height derivative residual norm, given square integrability and the weak height identity.

**The angular gradient relation holds.** Proved result `angular_relation`: Second-order field regularity supplies the almost-everywhere angular gradient-mode identity.

**Finite radial coefficient bound.** Proved result `rad_fin`: The radial coefficient identity bounds a finite radial-eigenvalue-weighted coefficient sum by the weighted radial derivative norm.

**Finite height coefficient bound.** Proved result `ht_fin`: The height coefficient identity bounds a finite height-eigenvalue-weighted coefficient sum by the weighted height derivative norm.

**Radial coefficients from the weak form.** Proved result `rad_id`: The weak radial integration-by-parts identity yields the radial-eigenvalue coefficient formula.

**Height coefficients from the weak form.** Proved result `ht_id`: The weak height integration-by-parts identity yields the height-eigenvalue coefficient formula.

**The full finite radial bound.** Proved result `radial_full`: Square integrability and the weak radial identity bound every finite radial-eigenvalue-weighted coefficient sum by the weighted radial derivative norm.

**The full finite height bound.** Proved result `height_full`: Square integrability and the weak height identity bound every finite height-eigenvalue-weighted coefficient sum by the weighted height derivative norm.

**The effective inner radius is positive.** Proved result `iR_pos`: The effective inner radius is strictly positive under the cell hypotheses.

**The angular weight is nonnegative.** Proved result `angW_nonneg`: The angular weight is nonnegative under the cell hypotheses.

**Pairing with a basis is integrable.** Proved result `bas_int`: Weighted square integrability implies integrability of the line-weighted product with any cell basis function.

**Coefficients respect finite combinations.** Proved result `coef_lin`: When the relevant pairings are integrable, cell coefficients commute with finite linear combinations.

**Curl commutes with cell coefficients.** Proved result `coef_curl`: For weighted square-integrable matrix entries, taking curl coordinates commutes with taking cell coefficients.

**Expand curl after a matrix transform.** Proved result `curl_expand`: The curl of a finite matrix-coefficient transformation equals the corresponding reordered sum of transformed entries.

**Skew coefficient energy is curl energy.** Proved result `two_anti`: Twice the antisymmetric cell coefficient energy equals the sum of its curl coefficient squares.

**Angular control of shifted curl.** Proved result `ang_coef`: The angular curl coefficient squares bound the shift-one-weighted curl coefficient energy.

**Angular curl modes have finite energy.** Proved result `omA_int`: The angular curl mode is measurable and has integrable line-weighted square for a second-order field.

**Cell polynomials are continuous.** Proved result `poly_cont`: Every function in the finite cell polynomial space is continuous.

**The projection has the prescribed degree.** Proved result `proj_mem`: The cell projection belongs to the polynomial space with its prescribed radial and height degree bounds.

**A polynomial residual has finite energy.** Proved result `sub_int`: Subtracting a continuous cell polynomial from a measurable weighted square-integrable function preserves those properties.

**The full finite angular bound.** Proved result `ang_full`: Every finite angular curl coefficient-square sum is bounded by the full weighted angular curl norm.

**The finite angular tail bound.** Proved result `ang_tail`: The polynomial coefficient-tail interface bounds finite high-degree angular curl coefficient squares by the angular projection-residual norm.

**Radial bounds for curl coefficients.** Proved result `rad_curl`: The radial full and tail inequalities apply componentwise to the curl coefficients and their radial derivatives.

**Height bounds for curl coefficients.** Proved result `ht_curl`: The height full and tail inequalities apply componentwise to the curl coefficients and their height derivatives.

**Unresolved curl energy bound.** Proved result `unres_pt`: The combined radial, height and angular curl weights are bounded by the radial-weighted curl-gradient mode energy.

**Radial eigenfunction parts identity.** Proved result `rad_ibp`: The weighted radial derivative pairing with a monomial equals the radial eigenvalue times the corresponding polynomial pairing. Source: `Breakdown.FracCell.SharpEnergyVorticityIdentity:779`.

**Height eigenfunction parts identity.** Proved result `ht_ibp`: The weighted height derivative pairing with a monomial equals the height eigenvalue times the corresponding polynomial pairing. Source: `Breakdown.FracCell.SharpEnergyVorticityIdentity:805`.

**Differentiate radial monomials.** Proved result `rderiv_poly`: The radial derivative of a cell polynomial coefficient sum is the sum of the differentiated radial monomials.

**Differentiate height monomials.** Proved result `hderiv_poly`: The height derivative of a cell polynomial coefficient sum is the sum of the differentiated height monomials.

**High radial derivative pairings vanish.** Proved result `poly_rad_zero`: A projected polynomial has zero weighted radial-derivative pairing with a basis index above its degree when the radial degree is nonzero.

**High height derivative pairings vanish.** Proved result `poly_ht_zero`: A projected polynomial has zero weighted height-derivative pairing with a basis index above its degree when the height degree is nonzero.

**Polynomial subtraction preserves energy.** Proved result `subW_int`: For a continuous nonnegative weight, subtracting a continuous polynomial preserves measurability and weighted square integrability.

**The radial coefficient-tail bound holds.** Proved result `radial_tail`: The weak radial identity and weighted regularity imply the radial coefficient-tail interface.

**The height coefficient-tail bound holds.** Proved result `height_tail`: The weak height identity and weighted regularity imply the height coefficient-tail interface.

**High polynomial coefficients vanish.** Proved result `poly_coef_tail`: Orthogonality of a valid cell basis gives the polynomial coefficient-tail interface.

**Combine eigenvalues and shifted curl.** Proved result `term_bound`: The curl-to-skew energy identity and angular lower bound combine with nonnegative derivative weights to give the eigenvalue-plus-shift coefficient bound.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble the vorticity identity.** Proved result `modeVorticityIdentity_of`: Polynomial coefficient tails and the radial and height tail interfaces imply the mode-vorticity identity.

**The mode-vorticity identity holds.** Proved result `modeVorticityIdentity_holds`: The established polynomial, radial and height tail bounds prove the mode-vorticity identity interface.

### Breakdown.FracCell.SharpModeExpansionRegular

Establishes the integrability and absolute summability needed to exchange the residual mode expansion with cell integration.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpModeExpansionRegular.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Second-derivative energies are summable.** Proposition `ThirdSeriesStatement`: This proposition requires summability of the radial-weighted second-derivative mode energies for second-order fields with positive mode spacing.

**Gradient-mode energies are summable.** Proposition `GradSeriesStatement`: This proposition requires summability of each line-weighted angular gradient-mode square integral for measurable square-integrable matrix fields with positive mode spacing.

**Regularity of the residual wave series.** Proposition `ModeWaveRegularStatement`: This proposition requires almost-everywhere wave and field-pair summability, absolute integral summability of resolved cross terms and integrability of the residual double wave sum for admissible fractional cell data.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal`.

**Integrability of an absolute sum.** Proved result `int_tsum`: An integer-indexed series of integrable real functions has an integrable sum when the integrals of their norms are summable.

**Integrate the real part of a series.** Proved result `re_tsum_int`: Almost-everywhere summability and absolute integral summability make the radial-weighted real part of a complex series integrable.

**Select one derivative mode.** Proved result `unit_combo`: The finite derivative-mode combination with a unit coefficient matrix equals the chosen differentiated-gradient component.

**Permutation coefficients give curl modes.** Proved result `curl_combo`: The derivative-mode combination with permutation-sign coefficients equals the corresponding curl component.

**Second-derivative energy is nonnegative.** Proved result `second_nonneg`: The full second-derivative mode square is nonnegative.

**Curl-gradient energy is nonnegative.** Proved result `curlGrad_nonneg`: The curl-gradient mode square is nonnegative.

**Compare curl and derivative energies.** Proved result `curlGrad_le`: The curl-gradient mode square is at most twenty-seven times the second-derivative mode square.

**Second-derivative energy is integrable.** Proved result `second_int`: For a second-order field on a valid cell, the radial-weighted second-derivative mode square is integrable.

**Curl-gradient energy is integrable.** Proved result `curlGrad_int`: For a second-order field on a valid cell, the radial-weighted curl-gradient mode square is integrable.

**Bound the signed derivative energy.** Proved result `energy_abs`: The absolute mode energy is bounded by the second-derivative square times the sum of the absolute viscosity coefficients, with factor twenty-seven for the curl contribution.

**Signed derivative energy is integrable.** Proved result `energy_int`: For a second-order field on a valid cell, the radial-weighted signed mode energy is integrable.

**Local density is absolutely summable.** Proved result `dens_abs`: The mode-series interface and admissible form data give integrability of each absolute local density and summability of their radial-weighted integrals.

**Regularity of the full local density.** Proved result `energy_facts`: The mode and third-derivative series interfaces give integrable mode energies, absolute integral summability of local densities and integrability of their total sum.

**The low-mode wave product is integrable.** Proved result `lowLow_int`: Under valid form and cell geometry, the radial-weighted wave pairing between two polynomial low modes is integrable.

**A field pairs integrably with low modes.** Proved result `fieldLow_int`: A measurable matrix field with integrable entry square has integrable radial-weighted pairing with each polynomial low mode.

**Weighted complex integrability.** Definition `Wt`: This predicate requires a complex function to be almost-everywhere strongly measurable and integrable after multiplication by radius on the cell rectangle.

**Weighted integrability under addition.** Proved result `wt_add`: The sum of two functions satisfying weighted complex integrability satisfies the same predicate.

**Weighted integrability under negation.** Proved result `wt_neg`: Negating a function preserves weighted complex integrability.

**Weighted integrability under subtraction.** Proved result `wt_sub`: Subtracting two functions satisfying weighted complex integrability preserves that property.

**Weighted integrability of finite sums.** Proved result `wt_sum`: A finite sum of functions with weighted complex integrability has weighted complex integrability.

**Multiply by a bounded left factor.** Proved result `wt_bdd_mul`: Multiplication on the left by a bounded measurable cell function preserves weighted complex integrability.

**Multiply by a bounded right factor.** Proved result `wt_mul_bdd`: Multiplication on the right by a bounded measurable cell function preserves weighted complex integrability.

**Weighted integrability under conjugation.** Proved result `wt_conj`: Complex conjugation preserves weighted complex integrability.

**Bounded functions are integrable.** Proved result `wt_of_bdd`: A bounded measurable cell function satisfies weighted complex integrability.

**Square integrability gives integrability.** Proved result `wt_sq`: On a valid cell, a measurable function with integrable line-weighted square satisfies weighted complex integrability.

**Square-integrable factors can be paired.** Proved result `wt_bil`: On a valid cell, the product of one weighted square-integrable measurable function and the conjugate of another satisfies weighted complex integrability.

**Curl preserves weighted integrability.** Proved result `wt_curl`: If every matrix entry satisfies weighted complex integrability, each curl component satisfies it as well.

**Bounded coupling preserves integrability.** Proved result `wt_coupling`: A coupling map with bounded matrix entries and weighted-integrable vector entries has weighted-integrable entries.

**A wave form with integrable right input.** Proved result `wt_wave_right`: Bounded model coefficients and bounded left input give weighted integrability of the wave form when the right input is weighted integrable.

**A wave form with integrable left input.** Proved result `wt_wave_left`: Bounded model coefficients and bounded right input give weighted integrability of the wave form when the left input is weighted integrable.

**Model Fourier coefficients are bounded.** Proved result `model_bdd`: Valid form data give bounded model strain and curl-gradient Fourier coefficients on the cell rectangle.

**The weighted real part is integrable.** Proved result `wt_re`: Weighted complex integrability implies integrability of radius times the real part.

**Residual wave cross terms are integrable.** Proved result `cross_wt`: For valid form data and a second-order field, every low-to-sharp cross pairing satisfies weighted complex integrability.

**Residual field pairings are integrable.** Proved result `field_wt`: For a second-order field and a measurable square-integrable matrix field, each residual field pairing satisfies weighted complex integrability.

**Residual field pairings are summable.** Proved result `field_summ`: The gradient-series interface gives absolute integral summability of residual pairings with a measurable square-integrable matrix field when the mode spacing is positive.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble regularity of the expansion.** Proved result `modeExpansionRegular_of`: The mode, third-derivative, gradient and wave regularity interfaces jointly imply regularity of the full residual mode expansion.

### Breakdown.FracCell.SharpMxGradSeries

Transfers spatial matrix square integrability to summability of the weighted angular gradient-mode energies.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpMxGradSeries.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpMxGradSeries.Internal`.

**Compare weighted and radial integrals.** Proved result `weighted_le`: For a valid cell away from the axis, the line-weighted integral of a nonnegative function is at most the reciprocal inner radius times its radial-weighted integral.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The gradient-series interface holds.** Proved result `gradSeries_holds`: Measurable square-integrable matrix fields satisfy the weighted gradient-mode summability interface.

### Breakdown.FracCell.SharpMxModeWaveRegular

Proves pointwise summability of residual wave interactions and reduces their integral regularity to absolute cross-term summability.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpMxModeWaveRegular.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpMxModeWaveRegular.Internal`.

**A Fourier convolution is summable.** Proved result `atom_sum`: For positive mode spacing, Fourier coefficients of an L2 function convolved with those of a regular periodic slice form a summable series.

**The conjugated convolution is summable.** Proved result `atom_sum_conj`: Under the same L2 and regular periodic slice hypotheses, the shifted conjugated Fourier product with a fixed complex factor is summable.

**Sum a wave form over the right input.** Proved result `right_sum`: Regular periodic derivative and velocity slices and L2 model slices give summability of a wave form over the right Fourier input.

**Sum a wave form over the left input.** Proved result `left_sum`: Regular periodic derivative and velocity slices and L2 model slices give summability of a wave form over the left Fourier input.

**Subtract in the right wave slot.** Proved result `wave_sub_right`: Replacing the right matrix and vector input by differences subtracts the corresponding wave forms.

**The wave form subtracts in the left slot.** Proved result `wave_sub_left`: Replacing the left matrix and vector input by differences subtracts the corresponding wave forms.

**Zero right input gives zero wave form.** Proved result `wave_zero_right`: The wave form vanishes when its right matrix and vector inputs are both zero.

**Zero left input gives zero wave form.** Proved result `wave_zero_left`: The wave form vanishes when its left matrix and vector inputs are both zero.

**The full gradient and velocity wave pair.** Definition `fullPair`: The full wave pair uses the original gradient and velocity modes in both wave-form slots.

**The low-to-full wave pair.** Definition `lowFullPair`: The low-to-full wave pair uses the polynomial low modes in the left slot and the original modes in the right slot.

**The residual-to-low wave pair.** Definition `sharpLowTerm`: The residual-to-low term pairs the residual gradient and velocity in the left slot with polynomial low modes in the right slot.

**Low modes have finite mode support.** Proved result `low_out`: Both the polynomial gradient and velocity modes vanish outside the resolved mode set.

**Decompose the residual wave pair.** Proved result `sharp_split`: The residual-to-residual wave pair equals the full pair minus the low-to-full pair and the residual-to-low pair.

**Right wave summability on a slice.** Proved result `slice_right`: On valid circle-slice data with positive mode spacing, the wave form is summable over its original right mode for any fixed left input.

**Left wave summability on a regular slice.** Proved result `slice_left`: On valid circle-slice data with positive mode spacing, the wave form is summable over its original left mode for any fixed right input.

**The full double wave sum is summable.** Proved result `full_outer`: On valid circle-slice data with positive mode spacing, the inner-summed full wave pairing is summable over its outer mode.

**Sum over the residual right mode.** Proved result `sharp_right`: On valid circle-slice data with positive mode spacing, replacing the right input by residual modes preserves wave summability.

**Sum over the residual left mode.** Proved result `sharp_left`: On valid circle-slice data with positive mode spacing, replacing the left input by residual modes preserves wave summability.

**Matrix entry pairing subtracts.** Proved result `entry_sub`: Pairing a matrix difference with a third matrix equals the difference of the two entry pairings.

**Residual field pairings sum on a slice.** Proved result `field_sum`: A matrix field with L2 angular entries has summable residual field pairings on valid circle-slice data with positive mode spacing.

**All residual wave series sum on a slice.** Proved result `pointwise`: Valid circle-slice data and positive mode spacing give the required residual double-series, resolved cross-series and actuator and pin field-series summability.

**Integrability of angular averages.** Proved result `slice_avg_int`: The radial-weighted angular average of an integrable spatial function is integrable over a valid cell rectangle.

**The mode coupling density is integrable.** Proved result `coupling_int`: For admissible fractional cell data and an axisymmetric weight, the radial-weighted mode coupling density is integrable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Absolute summability of wave crossings.** Proposition `ModeWaveCrossStatement`: This proposition requires the radial-weighted real cross-pair norms to have summable integrals over the second mode for each resolved first mode.

**Integrability of the total residual wave.** Proposition `ModeWaveTotalStatement`: This proposition requires integrability of the radial-weighted real part of the residual double wave sum for admissible fractional cell data.

**Residual wave sums hold almost surely.** Proved result `modeWavePointwise_holds`: Admissible fractional cell data with axisymmetric weight satisfy all required pointwise residual-wave and field-pair summability statements almost everywhere.

**Assemble residual wave regularity.** Proved result `modeWaveRegular_of`: The cross-term and total-wave integral interfaces imply the full residual wave regularity interface.

**Cross sums give total integrability.** Proved result `modeWaveTotal_of`: Absolute integral summability of resolved wave crossings implies integrability of the total residual wave sum.

**Cross summability gives wave regularity.** Proved result `modeWaveRegular_of_cross`: The absolute wave-cross summability interface alone implies the full residual wave regularity interface.

### Breakdown.FracCell.SharpMxThirdSeries

Establishes summability of second-derivative angular-mode energies through lower integrals and the cell weight comparison.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpMxThirdSeries.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpMxThirdSeries.Internal`.

**Radius is bounded by cell line weight.** Proved result `radius_le`: On a valid cell rectangle, radius is at most one plus the outer radius times the line weight.

**Derivative energy in extended norms.** Proved result `second_enorm`: Embedding the second-derivative mode square in the extended nonnegative reals equals the sum of its twenty-seven component enorm squares.

**Second-derivative energies are summable.** Proved result `third_holds`: A second-order field with positive mode spacing has summable radial-weighted second-derivative mode energy integrals on a valid cell.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The third-series interface holds.** Proved result `thirdSeries_holds`: Second-order fields satisfy the required summability interface for differentiated-gradient mode energies.

### Breakdown.FracCell.SharpMxWaveCross

Constructs summable energy envelopes for residual wave crossings and proves the absolute cross-integral summability needed by the mode expansion.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpMxWaveCross.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpMxWaveCross.Internal`.

**Bound a three-term complex sum.** Proved result `sum3`: If three complex terms each have norm at most M, their sum has norm at most three times M.

**Bound a three-term real sum.** Proved result `rsum3`: If three real terms are each at most M, their sum is at most three times M.

**Half a permutation sign is bounded.** Proved result `half_abs`: The absolute value of minus one half times a three-dimensional permutation sign is at most one.

**A quarter permutation sign is bounded.** Proved result `quarter_abs`: The absolute value of one quarter times a three-dimensional permutation sign is at most one.

**Curl is bounded by the matrix norm sum.** Proved result `curl_le`: Every curl component norm is bounded by the sum of all matrix-entry norms.

**Bound a triple product from the right.** Proved result `atom_r`: A real coefficient of absolute value at most one, a first factor bounded by nonnegative L and a last-factor product bounded by T give triple-product norm at most L times T.

**Bound a triple product from the left.** Proved result `atom_l`: A real coefficient of absolute value at most one, a first-factor product bounded by nonnegative T and a last factor bounded by L give triple-product norm at most L times T.

**Bound the five terms of a wave form.** Proved result `five_le`: The norm of a signed five-term complex sum is at most the sum of its five norms.

**A coarse right wave-form bound.** Proved result `wave_right_le`: When the fixed left input is bounded by nonnegative L and every model-times-right-input product is bounded by T, the wave form norm is at most two thousand times L times T.

**A coarse left wave-form bound.** Proved result `wave_left_le`: When the fixed right input is bounded by nonnegative L and every left-input-times-model product is bounded by T, the wave form norm is at most two thousand times L times T.

**A nonnegative entry is below its sum.** Proved result `entry_le2`: Every entry of a nonnegative matrix is at most the sum of all its entries.

**Two square bounds control a product.** Proved result `pair_le`: If the squares of two real numbers are both at most T, their product is at most T.

**Integrable modes with summable integrals.** Definition `Good`: This predicate requires every mode function to be integrable on the cell and the series of its integrals to be summable.

**Add integrable summable mode families.** Proved result `good_add`: The sum of two integrable mode families with summable integrals has the same properties.

**Scale an integrable summable family.** Proved result `good_mul`: Multiplication by any real constant preserves modewise integrability and summability of the integrals.

**Finite sums preserve mode summability.** Proved result `good_sum`: A finite sum of mode families with integrable terms and summable integrals has those properties.

**The cell rectangle is measurable.** Proved result `rect_meas'`: The cell rectangle is a measurable subset of the radial-height plane.

**The matrix entry square is nonnegative.** Proved result `entry_nonneg'`: The sum of squares of a real linear map's matrix entries is nonnegative.

**Summability of bounded model modes.** Proved result `good_mode`: A measurable matrix field bounded on the cell solid has integrable line-weighted mode squares with summable integrals along any injective frequency indexing when the mode spacing is positive.

**The model Fourier square envelope.** Definition `modeSq`: The model square envelope sums all strain-mode and curl-gradient-mode entry squares.

**The residual Fourier square envelope.** Definition `sharpSq`: The residual square envelope adds all residual gradient and velocity component squares.

**The weighted model square envelope.** Definition `modeW`: The weighted model envelope sums the line-weighted strain and curl-gradient mode entry squares.

**An envelope for the residual square.** Definition `fullW`: The full envelope is twice the sum of the line-weighted original and low-mode gradient and velocity squares.

**The model square envelope is nonnegative.** Proved result `modeSq_nonneg`: The model Fourier square envelope is nonnegative.

**The residual square is nonnegative.** Proved result `sharpSq_nonneg`: The residual Fourier square envelope is nonnegative.

**The model envelope bounds strain entries.** Proved result `strain_sq`: Each model strain-mode entry square is bounded by the model square envelope.

**The model envelope bounds curl entries.** Proved result `curlGrad_sq`: Each model curl-gradient-mode entry square is bounded by the model square envelope.

**The envelope bounds gradient squares.** Proved result `sharpGrad_sq`: Each residual gradient entry square is bounded by the residual square envelope.

**The envelope bounds velocity squares.** Proved result `sharpVel_sq`: Each residual velocity entry square is bounded by the residual square envelope.

**Factor the model line weight.** Proved result `modeW_eq`: The line weight times the model square envelope equals the weighted model envelope.

**The full envelope bounds the residual.** Proved result `sharpSq_le`: For nonnegative line weight, the weighted residual square envelope is bounded by the full envelope.

**A summable envelope for wave crossings.** Proved result `cross_le`: A uniform nonnegative bound on the low input bounds each radial-weighted real cross-pair norm by the two shifted model envelopes and the full residual envelope, with the stated geometric constant.

**Low polynomial modes are bounded.** Proved result `low_bound`: Each low gradient and velocity mode has a common finite nonnegative entry bound on the cell rectangle.

**Low gradient square integrals sum.** Proved result `good_lowGrad`: The line-weighted squares of low gradient entries are integrable modewise and their integrals form a summable series.

**Low velocity square integrals sum.** Proved result `good_lowVel`: The line-weighted squares of low velocity entries are integrable modewise and their integrals form a summable series.

**The residual envelope is summable.** Proved result `good_full`: For a second-order field and positive mode spacing, the full residual envelope has integrable terms and summable integrals.

**The model envelope is summable.** Proved result `good_modeW`: Measurable model strain and curl-gradient fields uniformly bounded on the cell solid have integrable weighted envelopes with summable integrals along any injective frequency indexing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Wave crossings are absolutely summable.** Proved result `modeWaveCross_holds`: The wave-cross interface follows from the summable model and residual energy envelopes.

**Residual wave regularity holds.** Proved result `modeWaveRegular_holds`: The established wave-cross summability proves the complete residual wave regularity interface.

### Breakdown.FracCell.SharpRowIdentity

Converts the high coupling field paired with certificate rows into strain and velocity coefficient tails, folding velocity into strain outside resolved modes.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpRowIdentity.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**One row strain coefficient term.** Definition `rowStrainPart`: The row strain term pairs a retained residual strain coefficient with a folded row-coupling coefficient on resolved or band modes and is zero outside those index conditions.

**One row velocity coefficient term.** Definition `rowVelocityPart`: The row velocity term pairs a velocity coefficient at or above the high-degree threshold with the row-coupling velocity coefficient, and vanishes below that threshold.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Coefficient form of a row pairing.** Proposition `RowPairFormStatement`: This proposition requires summability of row strain and velocity coefficient terms and identifies the normalized high-field row pairing with those sums plus twice the unresolved row series.

**Weighted square integrability on a cell.** Definition `IsWeightedSquare`: This predicate requires almost-everywhere strong measurability and integrability of the cell-line-weighted squared norm.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**The folded high-mode row pairing.** Definition `highRowPair`: The high row pairing integrates the residual gradient against the folded row coupling and adds a residual velocity pairing only for resolved modes.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Split a row pairing into mode ranges.** Proposition `RowModeSplitStatement`: This proposition identifies the high-field row pairing with four pi times the finite resolved-and-band high-row sum plus the unresolved row series.

**Field and row modes have finite energy.** Proposition `ModeSquareStatement`: This proposition requires weighted square integrability of gradient and velocity modes and of strain, velocity and folded row-coupling components for admissible fractional cell data.

**Field modes have finite weighted energy.** Proposition `FieldModeSquareStatement`: This proposition requires every gradient and velocity mode of a second-order field to be weighted square integrable on a valid cell.

**Row coupling modes have finite energy.** Proposition `RowCouplingSquareStatement`: This proposition requires all strain, velocity and folded row-coupling components to be weighted square integrable for valid fractional cell data.

**Combine field and row regularity.** Proved result `modeSquare_of`: The field-mode and row-coupling square-integrability interfaces imply the combined mode-square interface.

**Parseval for finite component pairings.** Proposition `BasisEnergySumStatement`: This proposition equates the cell coefficient-pairing series with the weighted integral pairing for finite families of weighted square-integrable functions.

**Coefficients of a projection residual.** Proposition `ProjCoefStatement`: This proposition requires weighted square integrability of a projection residual, zero coefficients inside the projected degree square and unchanged coefficients outside it.

**Velocity turn equals angular gradient.** Proposition `ModeTurnStatement`: This proposition requires the frequency turn of velocity modes to equal radius times the angular gradient column almost everywhere.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.CellScalars`.

**The separate strain and velocity pairing.** Definition `unfoldedRowPair`: The unfolded row pairing integrates the residual gradient and velocity separately against the strain and velocity row couplings.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The unfolded row-mode expansion.** Proposition `RowModeUnfoldedStatement`: This proposition expresses the high-field row pairing as four pi times the resolved-and-band unfolded pairing sum plus the unresolved row series.

**Fold velocity into a strain pairing.** Proposition `FoldPairStatement`: This proposition identifies pairing with the folded target as the sum of strain and velocity pairings when the turn identity holds and the frequency is neither zero nor of square one.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpRowIdentity.Internal`.

**Split a matrix pairing by symmetry.** Proved result `entry_split`: The symmetric-part and antisymmetric-part pairings add to the original matrix entry pairing.

**The strain term is twice a real pairing.** Proved result `strainLin_eq`: The strain linear term equals twice the real part of the matrix entry pairing.

**Pair a real weighted matrix sum.** Proved result `entry_sum`: A matrix pairing with a finite real weighted sum equals the same weighted sum of matrix pairings.

**Pair a real weighted vector sum.** Proved result `vec_sum`: A vector pairing with a finite real weighted sum equals the same weighted sum of vector pairings.

**Take real parts of a real weighted sum.** Proved result `re_sum_real`: The real part of a finite real weighted complex sum equals the weighted sum of its real parts.

**Split the combined row strain term.** Proved result `strain_term`: The combined row strain term equals the sum of individual row strain terms weighted by the row multipliers.

**Split the combined row velocity term.** Proved result `velocity_term`: The combined row velocity term equals the sum of individual row velocity terms weighted by the row multipliers.

**A high-degree restriction is summable.** Proved result `summable_far`: Restricting a summable two-degree family to indices beyond a degree square preserves summability.

**Split a series at a degree square.** Proved result `tsum_split`: A summable two-degree series equals the finite sum inside the degree square plus the series outside it.

**Sum one mode's row strain coefficients.** Proved result `strain_mode`: Weighted regularity, the basis pairing identity and projection coefficients identify the row strain series with twice the real residual-gradient integral against the folded row target.

**Sum one mode's row velocity coefficients.** Proved result `velocity_mode`: For a positive degree cutoff, weighted regularity and the basis and projection interfaces identify the row velocity series with twice the real residual-velocity integral against the row target.

**Row strain terms have finite support.** Proved result `strain_zero`: The row strain coefficient term vanishes outside the union of resolved and band modes.

**The inverse turn preserves the pairing.** Proved result `fold_core`: For frequency neither zero nor of square one, pairing a turned vector with the inverse-adjoint-turned target equals the original vector pairing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The velocity folding identity holds.** Proved result `foldPair`: For frequency neither zero nor of square one and a velocity satisfying the turn identity, the folded strain pairing equals the sum of the original strain and velocity pairings.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpRowIdentity.Internal`.

**The line weight is nonnegative.** Proved result `lw_nonneg_rect`: The cell line weight is nonnegative on a valid cell rectangle.

**Weighted scalar pairings are integrable.** Proved result `pair_int`: Two weighted square-integrable functions have an integrable line-weighted product with complex conjugation.

**Weighted matrix pairings are integrable.** Proved result `entry_int`: Matrices with weighted square-integrable entries have an integrable line-weighted entry pairing.

**Weighted vector pairings are integrable.** Proved result `vec_int`: Vectors with weighted square-integrable entries have an integrable line-weighted vector pairing.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Fold the unfolded row-mode expansion.** Proved result `rowModeSplit_of`: Mode square integrability, the unfolded row expansion and the mode-turn identity imply the folded row-mode split.

**Derive the row coefficient expansion.** Proved result `rowPairForm_of`: Mode square integrability, the folded mode split, basis pairings and projection coefficients imply the row coefficient-pairing form.

**Derive the residual row identity.** Proved result `sharpRowIdentity_of`: The row coefficient-pairing form implies the residual row identity.

**Assemble the residual row identity.** Proved result `sharpRowIdentity_of_parts`: Field and row regularity, the unfolded expansion, the turn identity, basis pairings and projection coefficients jointly imply the residual row identity.

### Breakdown.FracCell.SharpSupremumRegular

Uses summable residual square energies to justify the residual wave supremum estimate and circle-square summability.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpSupremumRegular.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**A uniform residual wave bound.** Proposition `WaveSumBoundStatement`: This proposition bounds the real residual double wave sum by a fixed constant times the summed residual gradient and velocity squares whenever those square series are summable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpSupremumRegular.Internal`.

**The cell rectangle is measurable.** Proved result `rectM`: The closed rectangle of radial and height coordinates associated with any cell box is measurable in R².

**Radius is nonzero almost everywhere.** Proved result `ae_fst_ne`: Radius is nonzero almost everywhere with respect to volume restricted to a cell rectangle.

**The cell rectangle is compact.** Proved result `rectC`: For every cell box, its closed rectangle of radial and height coordinates is compact in R².

**Convert a nonnegative real series.** Proved result `tsum_eq_toReal`: The total of a nonnegative real series equals the real conversion of the corresponding extended-nonnegative series.

**Exchange a nonnegative sum and integral.** Proved result `lint_tsum_eq`: For nonnegative integrable terms with summable integrals, the lower integral of their extended sum equals the extended embedding of the summed integrals.

**Integral bounds give pointwise sums.** Proved result `ae_summable_of`: Nonnegative integrable terms with summable integrals form a summable pointwise series almost everywhere.

**The nonnegative sum is integrable.** Proved result `integrable_tsum_nonneg`: Nonnegative integrable terms with summable integrals have an integrable pointwise sum.

**The wave form is measurable.** Proved result `waveForm_aem`: Almost-everywhere measurable matrix and vector inputs give an almost-everywhere measurable wave form.

**Residual square energies are summable.** Proved result `sharpQ_facts`: For a second-order field with positive mode spacing, radial-weighted residual gradient-plus-velocity squares are integrable modewise and have summable integrals.

**Residual square sums exist almost surely.** Proved result `sharpQ_ae`: For a second-order field with positive mode spacing, the residual gradient and velocity square series are summable almost everywhere.

**The residual wave sum is measurable.** Proved result `waveSum_aem`: For valid form data and a second-order field, the real part of the residual wave sum is almost-everywhere strongly measurable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**A wave bound gives supremum regularity.** Proved result `sharpSupremumRegular_of`: The uniform residual-wave square bound implies the residual supremum regularity interface.

**Residual circle squares are summable.** Proved result `sharpCircleSquare_holds`: For admissible fractional cell data with axisymmetric weight, integrated residual-energy summability gives summability of the residual gradient and velocity square series almost everywhere.

### Breakdown.FracCell.SharpTargetSquare

Builds boundedness and weighted square-integrability tools for Y targets, row couplings and folded velocity targets.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpTargetSquare.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpTargetSquare.Internal`.

**A bounded measurable cell function.** Definition `Bd`: This predicate requires almost-everywhere strong measurability on the cell and a uniform finite norm bound throughout its rectangle.

**The cell weight is nonnegative.** Proved result `wt_nonneg`: The line weight is nonnegative on a valid cell rectangle.

**The cell weight has a uniform bound.** Proved result `wt_le`: The line weight is at most one plus the outer radius on a valid cell rectangle.

**The cell weight is continuous.** Proved result `wt_meas`: The line weight, viewed as a function of the radial-height point, is continuous.

**An integrable bound gives finite energy.** Proved result `W_le`: A measurable function whose line-weighted square is bounded by an integrable function is weighted square integrable on a valid cell.

**Weighted square integrability of a sum.** Proved result `W_add`: Adding two weighted square-integrable cell functions preserves weighted square integrability.

**Weighted energy under subtraction.** Proved result `W_sub`: Subtracting weighted square-integrable cell functions preserves weighted square integrability.

**Weighted energy under negation.** Proved result `W_neg`: Negating a weighted square-integrable function preserves weighted square integrability.

**Multiply by a bounded left factor.** Proved result `W_mul_left`: A bounded measurable left factor preserves weighted square integrability on a valid cell.

**Multiply by a bounded right factor.** Proved result `W_mul_right`: A bounded measurable right factor preserves weighted square integrability on a valid cell.

**Bounded functions have finite energy.** Proved result `W_of_Bd`: A bounded measurable function is weighted square integrable on a valid cell.

**Constant functions are bounded.** Proved result `Bd_const`: Every constant complex function satisfies the bounded measurable cell-function predicate.

**Boundedness under addition.** Proved result `Bd_add`: Adding two bounded measurable cell functions preserves that property.

**Boundedness under subtraction.** Proved result `Bd_sub`: Subtracting bounded measurable cell functions preserves that property.

**Boundedness under negation.** Proved result `Bd_neg`: Negating a bounded measurable cell function preserves that property.

**Boundedness under multiplication.** Proved result `Bd_mul`: Multiplying bounded measurable cell functions preserves that property.

**Boundedness under conjugation.** Proved result `Bd_conj`: Complex conjugation preserves bounded measurability on the cell.

**Boundedness of finite sums.** Proved result `Bd_sum`: A finite sum of bounded measurable cell functions is bounded and measurable on the cell.

**Finite sums preserve weighted energy.** Proved result `W_sum`: A finite sum of weighted square-integrable functions is weighted square integrable on a valid cell.

**A conditional bounded function.** Proved result `Bd_ite`: A function selected by a fixed proposition and set to zero otherwise is bounded and measurable whenever the selected branch is.

**A conditional square-integrable function.** Proved result `W_ite`: Selecting a weighted square-integrable function by a fixed proposition and using zero otherwise preserves weighted square integrability.

**Continuous cell functions are bounded.** Proved result `Bd_cont`: A continuous complex function is bounded and measurable on the compact cell rectangle.

**Radius is a bounded cell function.** Proved result `Bd_fst`: The complex-valued radial coordinate is bounded and measurable on the cell rectangle.

**The radius factor is bounded.** Proved result `Bd_rHat`: The cell's modified radius factor is bounded and measurable on a valid cell rectangle.

**A projection has the prescribed degree.** Proved result `proj_mem'`: The cell projection belongs to the specified finite radial and height polynomial space.

**Cell projections are bounded.** Proved result `Bd_proj`: Every cell polynomial projection is bounded and measurable on the cell rectangle.

**Cell volume lies in positive radius.** Proved result `rect_le`: For a valid cell, restricted rectangle volume is dominated by volume restricted to strictly positive radius and arbitrary height.

**Angular averages are measurable.** Proved result `fiber_meas`: A continuous scalar function of angle and a measurable spatial field has an almost-everywhere strongly measurable angular integral over the cell.

**Bounded fields have bounded averages.** Proved result `fiber_bd`: A uniformly bounded spatial field and a continuous norm-contracting angular map give a bounded measurable normalized angular average.

**Lower-integral Cauchy bound.** Proved result `sq_lintegral_le_aux`: For a measurable nonnegative extended function, the square of its lower integral is at most total measure times the lower integral of its square.

**Cauchy bound without measurability.** Proved result `sq_lintegral_le`: For any nonnegative extended function, the square of its lower integral is at most total measure times the lower integral of its square.

**L2 fields have finite-energy averages.** Proved result `fiber_W`: An L2 spatial field and a continuous norm-contracting angular map give a weighted square-integrable normalized angular average on a valid cell.

**Cylindrical points lie in the cell solid.** Proved result `cyl_solid`: Every angle over a point of a valid cell rectangle maps to a point in the cell's cylindrical solid.

**Bounded matrix fields have bounded modes.** Proved result `modeMat_bd`: A measurable matrix field uniformly bounded on the cell solid has bounded measurable angular-mode entries on the rectangle.

**Bounded vector fields have bounded modes.** Proved result `modeVec_bd`: A measurable vector field uniformly bounded on the cell solid has bounded measurable angular-mode entries on the rectangle.

**Finite energy of L2 matrix modes.** Proved result `modeMat_W`: Every angular-mode entry of an L2 matrix field is weighted square integrable on a valid cell.

**Finite energy of L2 vector modes.** Proved result `modeVec_W`: Every angular-mode entry of an L2 vector field is weighted square integrable on a valid cell.

**Entry-square integrability gives L2.** Proved result `memLp_of_entry`: A measurable matrix field with integrable sum of entry squares belongs to spatial L2.

**Packing entries preserves boundedness.** Proved result `pair_bd`: Packing bounded measurable matrix and vector entries into the twelve-component pair vector gives bounded measurable components.

**A bounded matrix action stays bounded.** Proved result `split_bd`: A matrix with bounded measurable entries acting on a packed bounded matrix-vector input gives bounded measurable strain and velocity outputs.

**The strain wave action stays bounded.** Proved result `wave_bd`: Bounded measurable model coefficients and matrix-vector inputs give bounded measurable strain wave-action entries.

**The velocity wave action stays bounded.** Proved result `waveV_bd`: Bounded measurable curl-gradient coefficients and matrix input give bounded measurable velocity wave-action entries.

**Folding preserves finite weighted energy.** Proved result `fold_W`: Folding a weighted square-integrable strain and velocity target produces weighted square-integrable matrix entries on a valid cell.

**A bounded left cross factor preserves L2.** Proved result `cross_W1`: Crossing a conjugated bounded vector with a weighted square-integrable vector preserves weighted square integrability componentwise.

**A bounded right cross factor.** Proved result `cross_W2`: Crossing a weighted square-integrable vector with a conjugated bounded vector preserves weighted square integrability componentwise.

**The Y strain target has finite energy.** Proved result `yStrain_W`: Bounded radius, wave and local-matrix contributions together with square-integrable actuator and pin modes give weighted square integrability of every Y strain entry.

**The Y velocity target is bounded.** Proved result `yVel_bd`: Bounded radius, wave and local-matrix contributions give bounded measurable Y velocity entries.

**The row strain target has finite energy.** Proved result `rowS_W`: Bounded radius and model-velocity modes together with square-integrable row modes give weighted square integrability of the row strain target.

**Finite energy of the row velocity target.** Proved result `rowV_W`: Bounded radius and model-curl modes together with square-integrable row modes give weighted square integrability of the row velocity target.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**All residual targets have finite energy.** Proved result `sharpTargetSquare`: The boundedness and weighted square estimates establish the residual target-square interface.

### Breakdown.FracCell.SharpWaveSumBound

Bounds the infinite residual wave convolution by its square energy using finite Fourier polynomial estimates and passage to summable series.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpWaveSumBound.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpWaveSumBound.Internal`.

**A normalized angular Fourier coefficient.** Definition `coefAt`: The coefficient is the normalized integral over one full turn against the negative-frequency complex exponential.

**A bounded iterated wave series.** Definition `Good`: This predicate requires each inner series and the resulting outer series to be summable and bounds the norm of their iterated total.

**Enlarge a double-series bound.** Proved result `good_mono`: A bounded iterated series retains the property when its upper bound is increased.

**Equal double series share the bound.** Proved result `good_congr`: Pointwise equal double-indexed families have the same bounded iterated-series property.

**Add bounded iterated series.** Proved result `good_add`: Adding two bounded iterated series gives the sum of their bounds.

**Scale a bounded iterated series.** Proved result `good_mul`: Multiplying a bounded iterated series by a complex scalar multiplies its bound by any upper bound for that scalar's norm.

**Add three bounded iterated series.** Proved result `good_sum3`: Summing three iterated series with a common norm bound gives three times that bound.

**Fourier coefficients inherit a bound.** Proved result `coef_norm_le`: A uniformly bounded angular symbol has every normalized Fourier coefficient bounded by the same constant.

**Real Fourier coefficients conjugate.** Proved result `coef_conj_neg`: For a real angular symbol, conjugating the coefficient at the negative frequency gives the coefficient at the positive frequency.

**Permutation signs have a unit bound.** Proved result `permSign_abs`: Every three-dimensional permutation sign has absolute value at most one.

**A signed factor preserves a unit bound.** Proved result `permSign_norm`: Multiplying a complex number of norm at most one by a permutation sign preserves that norm bound.

**Expand the wave form into five sums.** Proved result `wave_split`: Conjugate symmetry of the curl-gradient symbol expands the wave form into one curl-strain term and four strain-velocity coupling sums.

**Matrix energy bounds each entry square.** Proved result `entry_sq_le`: Every matrix entry square is bounded by the full matrix square sum.

**Vector energy bounds each entry square.** Proved result `vec_sq_le`: Every vector entry square is bounded by the full vector square sum.

**Matrix energy is nonnegative.** Proved result `sumSq_nonneg'`: The matrix square sum is nonnegative.

**Vector energy is nonnegative.** Proved result `vecSq_nonneg'`: The vector square sum is nonnegative.

**A coarse bound for one curl square.** Proved result `curl_sq_le`: Every curl component square is at most eighty-one times the matrix square sum.

**Frame vectors have a unit bound.** Proved result `unit_le`: Each radial, angular or axial frame vector has norm at most one.

**A frame entry is below the operator norm.** Proved result `frame_bound`: Every entry of a linear map in the cylindrical orthonormal frame is bounded in absolute value by its operator norm.

**Symmetrization does not increase norm.** Proved result `symPart_norm`: The norm of the symmetric part of a linear map is at most the original operator norm.

**Coordinate vectors have unit norm.** Proved result `unitVector_norm`: Each coordinate unit vector has norm one.

**Bound the curl-gradient matrix norm.** Proved result `curlGrad_norm`: The curl-gradient matrix norm is at most eighty-one times the second-derivative tensor norm.

**Decay gives a uniform bound.** Proved result `decay_le`: An inverse-square or inverse-cube decay bound by C implies the uniform upper bound given by the maximum of C and zero.

**The model wave symbols are bounded.** Proved result `symbol_bound`: Valid form data give a common global bound for model strain and curl-gradient norms.

**Zero spacing kills unresolved energy.** Proved result `order_zero_vanish`: At zero mode spacing, summability of residual gradient and velocity squares forces every unresolved mode's combined square energy to vanish.

**A finitely supported convolution bound.** Proved result `good_base_fin`: A bounded symbol and coefficient sequences controlled by a finitely supported summable square envelope give a bounded iterated convolution, with the support cardinality factor.

**Split a frequency-difference phase.** Proved result `exp_split`: The exponential at a frequency difference factors into the conjugated first phase times the second phase.

**Integrals of nonzero phases vanish.** Proved result `int_exp`: For positive mode spacing, the full-turn integral of a Fourier phase is two pi at zero frequency and zero otherwise.

**Fourier coefficients of the constant one.** Proved result `coef_one`: For positive mode spacing, the constant-one symbol has coefficient one at zero frequency and zero elsewhere.

**A finite Fourier polynomial.** Definition `wavePoly`: The wave polynomial sums the selected coefficients times their positive-frequency angular phases.

**Fourier polynomials are continuous.** Proved result `wavePoly_cont`: Every finite Fourier polynomial is continuous in angle.

**Convolution as an angular integral.** Proved result `fin_identity`: For an integrable symbol, the finite coefficient convolution equals the normalized integral of the conjugated first Fourier polynomial times the second and the symbol.

**A scaled product-square bound.** Proved result `amgm`: For positive t, a real product is at most half the sum of t times the first square and the second square divided by t.

**Parseval for a finite Fourier polynomial.** Proved result `poly_sq`: For positive mode spacing, the full-turn squared norm integral of a Fourier polynomial equals two pi times its coefficient-square sum.

**Bound a finite Fourier convolution.** Proved result `fin_bound`: A bounded integrable symbol bounds the finite convolution norm by its supremum bound times the scaled arithmetic mean of the two coefficient-square sums.

**Remove a finite-set indicator.** Proved result `ind_sum`: Summing a finite-set indicator over a containing finite set gives the sum over the indicated set.

**A Fourier coefficient column has a bound.** Proved result `col_bound`: For positive mode spacing, any finite square sum along a shifted Fourier-coefficient column is at most the square of the symbol bound plus one.

**The bound allows different supports.** Proved result `finite_pair`: The finite convolution estimate remains valid when the two coefficient sequences are summed over different finite sets.

**An infinite Fourier convolution bound.** Proved result `good_base_pos`: For positive mode spacing, coefficient sequences controlled by a common nonnegative summable square envelope have an iterated convolution bounded by the symbol bound times the envelope sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The residual wave-sum bound holds.** Proved result `waveSumBound_holds`: The finite and infinite convolution estimates establish the uniform residual wave-sum bound interface.

### Breakdown.FracCell.SharpYCharge

Combines density, residual wave, class-cross and coefficient-tail estimates into the final Y charge inequality.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYCharge.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYChargeInternal`.

**Class losses fit within the penalty.** Proved result `charge_point`: Positive class shares and split length, together with the three scalar penalty budgets, bound the summed class loss and row charge by the total strain-velocity penalty.

**The charge rectangle is measurable.** Proved result `rect_meas`: The cell rectangle is measurable, permitting integration of the charge inequality.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Integrate the class and row charges.** Proved result `penaltyCharge_of`: The charge regularity interface implies that the combined class loss and unresolved row charge are bounded by the penalty sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYChargeDensity`.

**Expand a quadratic form at a sum.** Proved result `sesq_add`: Evaluating a matrix quadratic form at two vectors' sum gives the two separate quadratic values and the real sum of both cross terms.

**The radial factors multiply to radius.** Proved result `lw_rhat`: The line weight times the modified radius factor equals the physical radius.

**The line weight is nonnegative.** Proved result `lw_nonneg`: The line weight is nonnegative on a valid cell rectangle.

**Split the packed low and residual field.** Proved result `grad_split`: The packed original gradient and velocity equal the sum of their packed polynomial low modes and residual modes.

**The density rectangle is measurable.** Proved result `rect_meas`: The cell rectangle is measurable for the integrated density comparison.

**Radius is nonzero almost everywhere.** Proved result `first_ne_zero_ae`: Radius is nonzero almost everywhere on a cell rectangle.

**Integrate a three-term inequality.** Proved result `int_comb3`: An almost-everywhere inequality between three integrable signed terms and an integrable bound passes to the corresponding inequality of integrals.

**Integrate a five-term inequality.** Proved result `int_comb4`: An almost-everywhere inequality involving four positive-position terms and one subtracted term passes to the sum and difference of their integrals when all terms are integrable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Derive the residual density inequality.** Proved result `sharpDensity_of`: Density regularity and the trace-free residual-field interface imply the integrated residual density bound.

**Assemble the Y charge inequality.** Proved result `sharpYCharge_of`: The mode expansion, density, supremum, residual cross, class cross, penalty charge and energy-tail bounds jointly imply the Y charge inequality.

**Use regularity to supply penalty charges.** Proved result `sharpYCharge_of_regular`: The charge regularity interface supplies the penalty-charge step in the assembly of the Y charge inequality.

**Assemble Y charge from analytic inputs.** Proved result `sharpYCharge_of_leaves`: Mode expansion, density regularity, trace-free residual fields, supremum and cross estimates, charge regularity and the energy-tail bound jointly imply the Y charge inequality.

### Breakdown.FracCell.SharpYChargeRegular

Proves integrability and absolute summability of class, row and penalty charge densities from angular Bessel bounds and bounded scalar coefficients.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYChargeRegular.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYChargeRegular.Internal`.

**A real slice Fourier coefficient.** Definition `coefAt`: The angular coefficient is the normalized integral of a real slice against its negative-frequency phase over the interval from minus pi to pi.

**The angular interval has positive length.** Proved result `neg_pi_lt`: Minus pi is strictly less than pi.

**The interval Fourier coefficient.** Proved result `coefAt_eq`: The normalized angular slice coefficient equals the interval Fourier coefficient at the integer mode times the spacing.

**Bessel bound for real slice coefficients.** Proved result `coef_sq_sum`: For positive mode spacing and an L2 real slice, coefficient squares are summable and their total is bounded by the normalized angular square integral.

**Measurability of angular slices.** Proved result `slice_meas`: A continuous real function of angle and a measurable spatial field is almost-everywhere strongly measurable along almost every positive-radius cylindrical slice.

**An extended Fourier square bound.** Proved result `slice_bound`: A measurable real angular slice with positive mode spacing has its extended coefficient-square sum bounded by the normalized angular lower square integral.

**Fourier coefficient of a spatial slice.** Definition `sliceCoef`: The slice coefficient applies the angular Fourier integral to a scalar observable of a spatial field along a cylindrical circle.

**Bound integrated mode squares spatially.** Proved result `mode_lint`: A measurable spatial majorant for slice squares bounds the lower integral of all radial-weighted mode squares by its spatial lower integral divided by two pi.

**Finite spatial energy gives mode sums.** Proved result `mode_sum`: A finite spatial square majorant gives integrability of each radial-weighted slice coefficient square and summability of their integrals for positive mode spacing.

**Gradient modes are slice coefficients.** Proved result `gm_coef`: A gradient-mode entry is the slice Fourier coefficient of the corresponding cylindrical-frame matrix entry.

**Velocity modes are slice coefficients.** Proved result `mv_coef`: A velocity-mode entry is the slice Fourier coefficient of the corresponding cylindrical-frame vector entry.

**Gradient square integrals are summable.** Proved result `gm_sum`: A measurable matrix field with integrable entry square has integrable radial-weighted mode squares with summable integrals for positive mode spacing.

**Velocity square integrals are summable.** Proved result `mv_sum`: A second-order field with positive mode spacing has integrable radial-weighted velocity mode squares with summable integrals.

**The full first-order energy is summable.** Proved result `tot_sum`: For a second-order field and positive mode spacing, the combined radial-weighted gradient and velocity mode energies have integrable terms and summable integrals.

**Bound curl energy by matrix energy.** Proved result `curlSq_le`: The curl square is at most twenty-seven times the full matrix square sum.

**Finite sums preserve boundedness.** Proved result `bdd_sum`: A finite family of uniformly bounded real functions on the cell has a uniformly bounded sum.

**A real multiple stays bounded.** Proved result `bdd_mul`: Multiplication by a real constant preserves a uniform absolute bound on the cell.

**Squaring preserves boundedness.** Proved result `bdd_sq`: The square of a uniformly bounded real cell function is uniformly bounded.

**Bounded quadratic densities are summable.** Proved result `dens_reg`: Bounded measurable coefficients multiplying curl, gradient and velocity mode squares, with finitely many modes removed, give integrable densities whose integrals and absolute integrals are summable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The charge regularity interface holds.** Proved result `chargeRegular`: The mode-square summability estimates establish integrability, summability and the unresolved-row series identity required for the charge densities.

### Breakdown.FracCell.SharpYChargeSt

Defines the low-residual decomposition, integrated loss budgets and analytic interfaces whose combination yields the Y charge estimate.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYChargeSt.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpParts`.

**The resolved polynomial gradient.** Definition `lowGrad`: The low gradient is the cell polynomial strain projection on resolved angular modes and zero on other modes.

**The resolved polynomial velocity.** Definition `lowVel`: The low velocity is the cell polynomial velocity projection on resolved angular modes and zero on other modes.

**The gradient residual.** Definition `sharpGrad`: The residual gradient is the original angular gradient mode minus its low polynomial mode.

**The velocity residual.** Definition `sharpVel`: The residual velocity is the original angular velocity mode minus its low polynomial mode.

**A wave pairing at two angular modes.** Definition `pairWave`: The wave pairing inserts model strain and curl-gradient coefficients at the two frequency differences into the matrix-vector wave form.

**The derivative mode-energy sum.** Definition `modeEnergy`: The mode energy sums radial-weighted second-derivative and curl-gradient squares with their viscosity and coercivity coefficients.

**The local density at one angular mode.** Definition `densityAt`: The mode density evaluates the cell density form on the angular gradient matrix.

**The integrated density sum.** Definition `densitySum`: The density sum adds the radial-weighted local density integrals over all angular modes.

**The local matrix on the low modes.** Definition `lowMatrixDensity`: The low matrix density evaluates the local quadratic matrix on the packed low gradient and velocity.

**The integrated low matrix contribution.** Definition `lowMatrixSum`: The low matrix sum integrates the radial-weighted low matrix density over the resolved modes.

**The two local matrix cross terms.** Definition `matrixCrossDensity`: The matrix cross density is the real sum of both low-to-residual and residual-to-low matrix pairings.

**The integrated matrix cross contribution.** Definition `matrixCross`: The matrix cross contribution sums radial-weighted matrix cross-density integrals over resolved modes.

**Wave crossings restricted to a mode set.** Definition `crossOn`: The restricted crossing sums both orders of low-to-residual wave pairing from resolved modes to residual modes in the specified set.

**The integrated residual double wave sum.** Definition `sharpSharp`: The residual wave contribution is the radial-weighted integral of the real iterated wave sum with residual inputs in both slots.

**Residual actuator and pin pairings.** Definition `linearSharp`: The linear residual contribution sums gradient-residual pairings with actuator fields and twice the pin multipliers over all modes.

**One mode's residual supremum loss.** Definition `supDensity`: The supremum density applies the strain, mean-gradient and wave-gradient bounds with the split length to the residual gradient and velocity.

**The integrated residual supremum loss.** Definition `supSum`: The supremum sum adds the radial-weighted residual supremum density integrals over all modes.

**The penalty on unresolved modes.** Definition `penaltyDensity`: The penalty density is zero on resolved and band modes and equals the residual strain-velocity penalty on the remaining modes.

**The integrated unresolved penalty.** Definition `penaltySum`: The penalty sum integrates the radial-weighted penalty density over all angular modes.

**The unresolved class loss density.** Definition `classDensity`: The class density vanishes on resolved and band modes and otherwise sums residual class losses divided by their share weights.

**The integrated unresolved class loss.** Definition `classSum`: The class sum adds the radial-weighted unresolved class-density integrals over all modes.

**The unresolved row charge density.** Definition `rowChargeDensity`: Outside resolved and band modes, the row charge sums twice each row weight times velocity-deviation squared times curl energy plus curl-deviation squared times velocity energy.

**The residual absorption density.** Definition `absorbDensity`: The absorption density combines residual curl and strain squares with their absorption coefficients and includes velocity absorption only on resolved modes.

**The integrated absorption budget.** Definition `absorbSum`: The absorption sum adds line-weighted absorption-density integrals over all angular modes.

**The weighted residual coefficient energy.** Definition `weightedSharp`: The weighted residual energy combines symmetric, antisymmetric and velocity coefficient squares on their retained indices, split into the finite near-degree square and the infinite outer tail.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The integrated low-residual expansion.** Proposition `ModeExpansionStatement`: This proposition bounds the assembled derivative, density, low, cross, residual-wave and linear mode terms by the original integrated local density and field couplings.

**The density funds the residual budgets.** Proposition `SharpDensityStatement`: This proposition bounds the low matrix, matrix cross, supremum and penalty terms minus absorption by the integrated local density.

**The residual wave has a loss lower bound.** Proposition `SharpSupremumStatement`: This proposition bounds the residual double wave contribution below by minus the integrated supremum loss.

**The Y form fits the residual crossings.** Proposition `SharpCrossStatement`: This proposition bounds the Y residual form with zero row multipliers by weighted residual coefficients, resolved-and-band wave crossings, linear residual pairings and matrix crossings.

**Class losses bound unresolved crossings.** Proposition `ClassCrossStatement`: This proposition bounds the wave crossings outside resolved and band modes below by minus the low class term and the unresolved class loss.

**The penalty pays class and row losses.** Proposition `PenaltyChargeStatement`: This proposition bounds the sum of unresolved class loss and unresolved row charge by the penalty sum.

**Regularity of the charge densities.** Proposition `ChargeRegularStatement`: This proposition requires integrability and summability of class, row-charge and penalty densities and identifies the unresolved row charge with its mode-integral series.

**Regularity of the density decomposition.** Proposition `DensityRegularStatement`: This proposition requires integrability of local, supremum, penalty, absorption and resolved matrix densities and summability of the four infinite density-integral series.

**Residual trace and turn constraints.** Proposition `SharpFieldStatement`: This proposition requires every gradient residual to be trace free almost everywhere and the velocity-turn identity to hold on unresolved modes.

**Derivative energy pays coefficient tails.** Proposition `SharpEnergyTailStatement`: This proposition bounds the resolved energy, weighted residual coefficients and absorption budget by the full derivative mode energy.

### Breakdown.FracCell.SharpYClassCross

Derives the unresolved wave-cross lower bound from pointwise class-product estimates and integrability of the class charge densities.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYClassCross.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYClassCrossInternal`.

**Class losses are nonnegative.** Proved result `loss_nonneg`: Positive split length and nonnegative strain and gradient deviations make each class loss nonnegative. Source: `Breakdown.FracCell.SharpYClassCross:17`.

**Negative matrix modes are conjugates.** Proved result `modeMat_neg`: For a real matrix field, the mode at negative frequency is the complex conjugate of the positive-frequency mode.

**Zero model modes give zero crossings.** Proved result `pair_zero`: If the strain and curl-gradient symbols vanish at both frequency differences, the sum of the two ordered wave pairings vanishes.

**Crossings vanish outside all classes.** Proved result `cross_vanish`: At an interior nonzero-radius point of valid cell data, a resolved-to-unresolved crossing vanishes when its frequency difference belongs to no class mode set.

**The cell interior has full measure.** Proved result `ae_open_box`: Almost every point of the closed cell rectangle lies in its open radial-height interior.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Sum the pointwise class-product bounds.** Proved result `classPointwise_of`: The pointwise class-product splitting interface implies the aggregate pointwise class-cross lower bound.

**Integrate the pointwise class bound.** Proved result `classCross_of_pointwise`: The pointwise class-cross interface, cross regularity and charge regularity imply the integrated class-cross inequality.

**Assemble the pointwise class-cross route.** Proved result `classCross_of`: The pointwise class-product splitting, cross regularity and charge regularity interfaces imply the integrated class-cross inequality.

### Breakdown.FracCell.SharpYClassCrossAe

Supplies the closed class-cross proof through almost-everywhere class-product estimates, avoiding the stronger pointwise interface.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYClassCrossAe.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The class-cross bound almost everywhere.** Proposition `ClassPointwiseAeStatement`: This proposition requires the finite class-loss lower bound for resolved-to-unresolved wave crossings at almost every interior nonzero-radius point of a valid cell.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYClassCrossAeInternal`.

**Class losses are nonnegative.** Proved result `loss_nonneg`: Positive split length and nonnegative strain and gradient deviations make each class loss nonnegative. Source: `Breakdown.FracCell.SharpYClassCrossAe:33`.

**Negative matrix modes are conjugates.** Proved result `modeMat_neg`: The matrix mode at negative frequency equals the complex conjugate of the corresponding positive-frequency mode.

**Zero symbols give zero ordered crossings.** Proved result `pair_zero`: Vanishing strain and curl-gradient symbols at both frequency differences makes the sum of the ordered wave pairings zero.

**Crossings vanish outside the class modes.** Proved result `cross_vanish`: At an interior nonzero-radius point of valid cell data, a resolved-to-unresolved crossing vanishes if its frequency difference belongs to no class mode set.

**The open cell has full rectangle measure.** Proved result `ae_open_box`: The open radial-height cell interior contains almost every point of the closed cell rectangle.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Sum almost-everywhere class bounds.** Proved result `classPointwiseAe_of`: The almost-everywhere class-product splitting interface implies the almost-everywhere aggregate class-cross bound.

**Integrate the almost-everywhere bound.** Proved result `classCross_of_pointwiseAe`: The almost-everywhere class-cross estimate, cross regularity and charge regularity imply the integrated class-cross inequality.

**Assemble the almost-everywhere route.** Proved result `classCross_of_ae`: The almost-everywhere class-product splitting and the two regularity interfaces imply the class-cross inequality.

**The integrated class-cross bound holds.** Proved result `classCross_closed`: The supplied almost-everywhere class-product proof and regularity theorems establish the class-cross interface.

### Breakdown.FracCell.SharpYClassCrossSt

Defines finite class-cross densities and the pointwise splitting and integrability interfaces for unresolved wave interactions.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYClassCrossSt.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpParts`.

**One selected wave-cross density.** Definition `classCrossDensity`: The class-cross density is the real sum of both ordered low-to-residual wave pairings when the residual mode lies in the selected set, and zero otherwise.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The finite pointwise class-cross bound.** Proposition `ClassPointwiseStatement`: This proposition requires the low weighted class losses and unresolved reciprocal-share losses to bound finite wave crossings below at every interior nonzero-radius point.

**One class controls a finite wave product.** Proposition `ClassProductSplitStatement`: This proposition requires a class's share-weighted loss on one finite mode set and reciprocal-share loss on another to bound their class-restricted ordered wave product below at every interior nonzero-radius point.

**Integrability of class-cross densities.** Proposition `ClassCrossRegularStatement`: This proposition requires integrability of each resolved-to-unresolved class-cross density and every resolved low-mode class loss for admissible fractional cell data.

### Breakdown.FracCell.SharpYDensityRegular

Proves integrability and summability of each density budget and derives quadratic frequency growth of the absorption coefficients from explicit test matrices.

Fractional cell analysis, analogous to the cell relations and coercive estimates of Appendix B; direct ordinary-route use is recorded separately.

Source: `lean/Breakdown/FracCell/SharpYDensityRegular.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal`.

**Matrix square energy is nonnegative.** Proved result `sumSq_nonneg`: The sum of matrix-entry squared norms is nonnegative.

**Vector square energy is nonnegative.** Proved result `vecSq_nonneg`: The sum of vector-entry squared norms is nonnegative.

**Curl square energy is nonnegative.** Proved result `curlSq_nonneg`: For every complex 3 × 3 gradient matrix, the sum of squared moduli of its three curl components is nonnegative.

**Curl energy has a matrix bound.** Proved result `curlSq_le`: The curl square is at most twenty-seven times the matrix square sum.

**Bound a complex difference square.** Proved result `nsq_sub`: The squared norm of a complex difference is at most twice the sum of the two squared norms.

**Bound a matrix difference square.** Proved result `sumSq_sub`: The matrix square of a difference is at most twice the sum of the two matrix squares.

**Bound a vector difference square.** Proved result `vecSq_sub`: The vector square of a difference is at most twice the sum of the two vector squares.

**Bound a product of square roots.** Proved result `sqrt_mul_le`: For nonnegative real numbers, the product of their square roots is at most their sum.

**The supremum loss has a square bound.** Proved result `supLoss_bd`: For positive split length, the absolute supremum loss is bounded by gradient-plus-velocity square energy times the explicit strain and gradient coefficient bound.

**The zero-angle map is measurable.** Proved result `cyl0_meas`: The cylindrical coordinate map at angle zero is measurable in radius and height.

**Polynomial projections are continuous.** Proved result `proj_cont`: Every cell polynomial projection is continuous.

**Curl square is continuous.** Proved result `continuous_curlSq`: The curl-square function is continuous in its matrix input.

**Matrix square is continuous.** Proved result `continuous_sumSq`: The matrix-entry square-sum function is continuous.

**Vector square is continuous.** Proved result `continuous_vecSq`: The vector-entry square-sum function is continuous.

**Radius is nonnegative on the cell.** Proved result `r_nonneg`: Every point of a valid cell rectangle has nonnegative radius.

**Line weight is nonnegative on the cell.** Proved result `lw_nonneg`: The line weight is nonnegative on a valid cell rectangle.

**Compare radius with the line weight.** Proved result `r_le_lw`: On a valid cell, radius is at most the maximum of one and the outer radius times the line weight.

**The line weight is measurable.** Proved result `lw_aem`: The cell line weight is almost-everywhere measurable on the rectangle.

**The radial coordinate is measurable.** Proved result `r_aem`: Radius is almost-everywhere measurable on the cell rectangle.

**An absolute majorant gives integrability.** Proved result `int_mono`: A measurable real function bounded in absolute value by an integrable function is integrable on the cell rectangle.

**Bound the absolute value of an integral.** Proved result `abs_int_le`: If a real function is bounded in absolute value by an integrable function, its integral's absolute value is at most the majorant's integral.

**Transfer a weighted density bound.** Proved result `wt_bound`: A nonnegative weight controlled by line weight and a density controlled by two energy terms yield the corresponding line-weighted absolute density bound.

**Summability with a finite-support error.** Proved result `summ_of`: An absolute bound by a summable family plus a finitely supported family implies summability of the bounded series.

**Packing entries is continuous.** Proved result `pairVec_cont`: Every component of the packed twelve-entry matrix-vector map is continuous.

**A packed entry is bounded by full energy.** Proved result `pairVec_sq_le`: Each packed matrix-vector entry square is bounded by the sum of matrix and vector energies.

**Bound one sesquilinear product.** Proved result `term_le`: A matrix-entry bound and bounds for the two vector-entry squares control the norm of their conjugated matrix product by the matrix bound times the sum of energies.

**Bound the two matrix cross terms.** Proved result `sesq_bd`: A uniform matrix-entry bound and component square bounds control the real sum of both twelve-dimensional cross terms by two hundred eighty-eight times the matrix bound times the energy sum.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Frequency-weighted mode energy sums.** Proposition `ModeSeriesStatement`: This proposition requires summability of velocity mode energies and of gradient mode energies weighted by one plus frequency squared for second-order fields with positive mode spacing.

**Absorption grows at most quadratically.** Proposition `AbsorbGrowthStatement`: This proposition bounds the absolute curl and strain absorption coefficients outside resolved modes by a constant times one plus frequency squared.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal`.

**The low gradient is continuous.** Proved result `lowGrad_cont`: Each low polynomial gradient mode is continuous on the radial-height plane.

**The low velocity is continuous.** Proved result `lowVel_cont`: Each low polynomial velocity mode is continuous on the radial-height plane.

**Low energy vanishes off resolved modes.** Proved result `low_zero`: The low gradient-plus-velocity square energy is zero outside the resolved mode set.

**Gradient matrix modes are measurable.** Proved result `gmv_aem`: A measurable spatial gradient field has an almost-everywhere measurable matrix of angular-mode entries on a valid cell.

**Velocity modes are measurable.** Proved result `mv_aem`: A second-order field has almost-everywhere measurable angular velocity modes on a valid cell.

**Gradient residuals are measurable.** Proved result `sG_aem`: A measurable spatial gradient field has almost-everywhere measurable gradient residuals on a valid cell.

**Velocity residuals are measurable.** Proved result `sV_aem`: A second-order field has almost-everywhere measurable velocity residuals on a valid cell.

**A full-plus-low residual energy bound.** Proved result `sharp_le`: The residual gradient-plus-velocity square is at most twice the sum of the original and low-mode energies.

**Full first-order energy is integrable.** Proved result `gq_int`: For a second-order field, the line-weighted gradient-plus-velocity mode energy is integrable on a valid cell.

**The weighted low energy is continuous.** Proved result `lq_cont`: The line-weighted low gradient-plus-velocity mode energy is continuous.

**The weighted low energy is integrable.** Proved result `lq_int`: The line-weighted low gradient-plus-velocity mode energy is integrable on the cell rectangle.

**Full first-order energies are summable.** Proved result `gq_summable`: The mode-series interface gives summability of the integrated line-weighted gradient-plus-velocity energies for positive mode spacing.

**A quadratic density is integrable.** Proved result `dens_int`: A measurable density bounded by the original and low-mode energies is integrable under a nonnegative weight controlled by line weight, with the stated integral bound.

**Quadratic bounds give summability.** Proved result `dens_sum`: The mode-series interface and a uniform original-plus-low energy bound imply modewise integrability and summability of a weighted density family.

**Bound the local density form.** Proved result `form_bd`: A bound on the sampled spatial weight gives the explicit absolute density-form bound in terms of the matrix square, coercivity and curl coefficients.

**Bound the strain-velocity penalty.** Proved result `pen_bd`: The absolute penalty is bounded by gradient-plus-velocity energy times the absolute strain, twenty-seven-times-curl and velocity penalty coefficients.

**Bound an absorption quadratic form.** Proved result `absorb_bd`: The absolute curl, strain and conditional velocity absorption combination is bounded by total square energy times the corresponding absolute coefficients.

**Bound the local quadratic form.** Proved result `sesqV_bd`: A common matrix-entry bound and a common vector-entry square bound give the stated finite-dimensional bound for the quadratic form's absolute value.

**Convert a residual-energy density bound.** Proved result `sharp_bd`: A nonnegative multiple of residual square energy is bounded by twice that multiple of the original-plus-low square energy.

**The local density series is regular.** Proved result `dAt_facts`: Valid form data and the mode-series interface give integrability and summability of radial-weighted local densities.

**The supremum loss series is regular.** Proved result `sup_facts`: Valid cell scalars and the mode-series interface give integrability and summability of radial-weighted supremum losses.

**The penalty series is regular.** Proved result `pen_facts`: The mode-series interface gives integrability and summability of radial-weighted unresolved penalty densities.

**The absorption series is regular.** Proved result `absorb_facts`: The mode-series and absorption-growth interfaces give integrability and summability of line-weighted absorption densities.

**The low local matrix is integrable.** Proved result `lowM_facts`: Valid cell scalars and a second-order field make each resolved radial-weighted low-matrix density integrable.

**Local matrix crossings are integrable.** Proved result `cross_facts`: Valid cell scalars and a second-order field make each resolved radial-weighted matrix cross density integrable.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**Assemble density regularity.** Proved result `densityRegular_of`: The mode-series and absorption-growth interfaces jointly imply the density regularity interface.

**Source namespace:** `Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal`.

**A fixed trace-free symmetric test.** Definition `symTest`: The symmetric test matrix is diagonal with entries one, minus one and zero.

**A fixed antisymmetric test.** Definition `antiTest`: The antisymmetric test has first off-diagonal entries one and minus one and all other entries zero.

**The symmetric test has square energy two.** Proved result `symTest_sumSq`: The symmetric test matrix has matrix square sum two.

**The skew test has square energy two.** Proved result `antiTest_sumSq`: The antisymmetric test matrix has matrix square sum two.

**The symmetric test has zero curl energy.** Proved result `symTest_curlSq`: The symmetric test matrix has curl square zero.

**The skew test has curl energy four.** Proved result `antiTest_curlSq`: The antisymmetric test matrix has curl square four.

**The symmetric test is trace free.** Proved result `symTest_tf`: The fixed symmetric test matrix has zero trace.

**The skew test is trace free.** Proved result `antiTest_tf`: The fixed antisymmetric test matrix has zero trace.

**A velocity realizing the symmetric turn.** Proved result `symTest_turn`: If t times the difference between frequency squared and one equals radius, the displayed two-component complex velocity satisfies the turn identity for the symmetric test.

**A velocity realizing the skew turn.** Proved result `antiTest_turn`: If t times the difference between frequency squared and one equals radius, the displayed two-component complex velocity satisfies the turn identity for the antisymmetric test.

**The test velocities have a radius bound.** Proved result `test_vecSq`: When frequency squared is at least nine and the turn denominator relation holds, both test velocities have square energy at most radius squared.

**Bound the test density difference.** Proved result `pt_bound`: For a matrix of square energy two and velocity energy at most outer-radius squared, the absolute density minus supremum loss and optional penalty has the explicit scalar bound.

**A shifted positive part is bounded.** Proved result `max_sq_le`: For a nonnegative shift, the square of the positive part of absolute y minus that shift is at most y squared.

**The constant mode has zero eigenvalue.** Proved result `tailLam_zero`: The combined radial-height tail eigenvalue at degree zero in both variables is zero.

**The angular weight has a uniform bound.** Proved result `angular_bd`: On a valid cell, the angular weight is nonnegative and at most reciprocal outer radius plus its square.

**Source namespace:** `Breakdown.CellCert.CellAnalysis`.

**The absorption growth bound holds.** Proved result `absorbGrowth`: The explicit symmetric and skew test matrices establish the quadratic frequency-growth interface for the absorption coefficients.

**Mode sums give density regularity.** Proved result `densityRegular_of_series`: The mode-series interface alone implies density regularity, using the proved absorption-growth bound.
<!-- /passage:front -->

