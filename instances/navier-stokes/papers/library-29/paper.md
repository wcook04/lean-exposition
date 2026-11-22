
<!-- passage:front -->
# Library guide 29: Fractional statements

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) **29** [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `FractionalCellSystemChallenge` to `FractionalChallenge` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

These three files are the authors' readable statements of the fractional extension, with dissipation exponent between 1 and 5/4, which their README separates from the paper's classical equation. They form their own chain of imports and are read here from that chain.

### FractionalCellSystemChallenge

This statement environment presents the fractional cell reduction, from local Fourier and polynomial coordinates through the global tree, spectral and adjoint conditions.

Reading context: Supplementary fractional-dissipation branch; the authors state that the Fractional files are outside the classical paper. Its organization parallels cell certificates, with a fixed system power of 501/500.

**Source namespace:** Breakdown.CellCert.

**Matrix entry.** A linear map's entry is the selected coordinate of its value on a standard basis vector. Source: Breakdown.CellCert.entry in FractionalCellSystemChallenge, line 33. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L33).

**Curl from a gradient matrix.** The curl vector contracts the gradient matrix with the alternating permutation signs. Source: Breakdown.CellCert.curlOf in FractionalCellSystemChallenge, line 35. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L35).

**Vector cross product.** The cross product uses the three cyclic differences of coordinate products. Source: Breakdown.CellCert.crossVec in FractionalCellSystemChallenge, line 38. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L38).

**Symmetric part of a linear map.** The symmetric part is half the sum of a linear map and its adjoint. Source: Breakdown.CellCert.symPart in FractionalCellSystemChallenge, line 42. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L42).

**Curl gradient from second derivatives.** The curl gradient contracts the second derivative tensor with the alternating permutation signs. Source: Breakdown.CellCert.curlGradMatrix in FractionalCellSystemChallenge, line 44. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L44).

**Resolvent ratio.** The scalar resolvent ratio is x divided by lam plus x. Source: Breakdown.CellCert.ratioFn in FractionalCellSystemChallenge, line 49. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L49).

**Source namespace:** Breakdown.CellCert.FracCellData.

**Gradient of the centre field.** The centre gradient is the Fréchet derivative of the centre field. Source: Breakdown.CellCert.FracCellData.centreGrad in FractionalCellSystemChallenge, line 89. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L89).

**Curl of the centre field.** The centre curl applies the curl contraction to the centre gradient. Source: Breakdown.CellCert.FracCellData.centreCurl in FractionalCellSystemChallenge, line 91. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L91).

**Strain of the centre field.** The centre strain is the symmetric part of the centre gradient. Source: Breakdown.CellCert.FracCellData.centreStrain in FractionalCellSystemChallenge, line 93. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L93).

**Curl gradient of the centre field.** The centre curl gradient contracts the supplied second derivative of the centre. Source: Breakdown.CellCert.FracCellData.centreCurlGrad in FractionalCellSystemChallenge, line 95. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L95).

**Strain approximation error.** The strain error subtracts the model strain from the centre strain. Source: Breakdown.CellCert.FracCellData.strainError in FractionalCellSystemChallenge, line 97. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L97).

**Curl gradient approximation error.** The curl gradient error subtracts the model tensor from the centre tensor. Source: Breakdown.CellCert.FracCellData.curlGradError in FractionalCellSystemChallenge, line 99. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L99).

**Velocity error inside the cells.** The velocity error is the centre minus the model on the cell region and zero outside it. Source: Breakdown.CellCert.FracCellData.velocityError in FractionalCellSystemChallenge, line 101. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L101).

**Curl error inside the cells.** The curl error is the centre curl minus the model curl on the cell region and zero outside it. Source: Breakdown.CellCert.FracCellData.curlError in FractionalCellSystemChallenge, line 103. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L103).

**Fractional spectral gap symbol.** The gap symbol subtracts the split viscosity from x raised to alpha minus one. Source: Breakdown.CellCert.FracCellData.gapSymbol in FractionalCellSystemChallenge, line 105. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L105).

**Coercive spectral symbol.** The full symbol adds the reduced coercivity times one plus weightMin divided by x to the gap symbol. Source: Breakdown.CellCert.FracCellData.fullSymbol in FractionalCellSystemChallenge, line 107. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L107).

**Squared gap over the full symbol.** The ratio symbol divides the square of the spectral gap by the full coercive symbol. Source: Breakdown.CellCert.FracCellData.ratioSymbol in FractionalCellSystemChallenge, line 109. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L109).

**Finite resolvent majorant.** The level sum adds a constant term to the finite weighted sum of resolvent ratios. Source: Breakdown.CellCert.FracCellData.levelSum in FractionalCellSystemChallenge, line 111. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L111).

**Source namespace:** Breakdown.CellCert.Finite.

**Positive form on a subspace.** Positivity on a subspace requires a strictly positive quadratic value for every nonzero vector in it. Source: Breakdown.CellCert.Finite.IsPositiveOn in FractionalCellSystemChallenge, line 132. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L132).

**Finite elimination tree data.** The tree data specify cell forms, parent relations, eliminated coordinates, front matrices and a global form. Source: Breakdown.CellCert.Finite.TreeCertificate in FractionalCellSystemChallenge, line 135. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L135).

**Source namespace:** Breakdown.CellCert.Finite.TreeCertificate.

**Input form at one tree node.** A node's input adds its assigned cell forms to the front matrices of its children. Source: Breakdown.CellCert.Finite.TreeCertificate.nodeInput in FractionalCellSystemChallenge, line 154. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L154).

**Coordinates eliminated in the tree.** A coordinate is eliminated somewhere when it belongs to the eliminated set of at least one node. Source: Breakdown.CellCert.Finite.TreeCertificate.IsEliminatedSomewhere in FractionalCellSystemChallenge, line 159. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L159).

**Coordinates remaining at the root.** The root subspace consists of vectors whose coordinates vanish wherever the tree eliminates them. Source: Breakdown.CellCert.Finite.TreeCertificate.rootSpace in FractionalCellSystemChallenge, line 161. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L161).

**Source namespace:** Breakdown.CellCert.Finite.

**Conditions on the elimination tree.** A valid tree requires ranked parent links, disjoint eliminations, front inequalities and a positive root subspace of sufficient dimension. Source: Breakdown.CellCert.Finite.IsTreeCertificate in FractionalCellSystemChallenge, line 175. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L175).

**Source namespace:** Breakdown.CellCert.Assembly.

**Field and multiplier tuple.** The field tuple groups velocity, first and second derivatives, multiplier coordinates and a pressure gradient. Source: Breakdown.CellCert.Assembly.FieldTuple in FractionalCellSystemChallenge, line 212. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L212).

**Cell splitting data.** A cell split records the spatial cells, global moments, multiplier slots, local matrices and delay forms. Source: Breakdown.CellCert.Assembly.CellSplit in FractionalCellSystemChallenge, line 216. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L216).

**Source namespace:** Breakdown.CellCert.Assembly.CellSplit.

**Global penalty matrix.** The global diagonal form assigns negative coercive penalties to multiplier slots and negative reciprocal pin weights to pin coordinates. Source: Breakdown.CellCert.Assembly.CellSplit.globalMatrix in FractionalCellSystemChallenge, line 232. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L232).

**Source namespace:** Breakdown.CellCert.Exterior.

**Exterior estimate data.** The exterior data record radius bounds, strain and curl gradient bounds, a splitting length and the three scalar estimate coefficients. Source: Breakdown.CellCert.Exterior.ExteriorData in FractionalCellSystemChallenge, line 264. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L264).

**Source namespace:** Breakdown.CellCert.Exterior.ExteriorData.

**Exterior gradient coefficient.** The exterior gradient coefficient combines curl weight, the coercive weight loss, a wave curl-gradient loss and twice the nonpositive part of the strain margin. Source: Breakdown.CellCert.Exterior.ExteriorData.gradientCoef in FractionalCellSystemChallenge, line 280. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L280).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Vector in the cylindrical frame.** The cylindrical vector coordinates pair the vector with the radial, angular and axial unit vectors. Source: Breakdown.CellCert.CellAnalysis.frameVec in FractionalCellSystemChallenge, line 322. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L322).

**Matrix in the cylindrical frame.** The cylindrical matrix coordinates evaluate a linear map on frame vectors and pair its outputs with the same frame. Source: Breakdown.CellCert.CellAnalysis.frameMat in FractionalCellSystemChallenge, line 325. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L325).

**Angular Fourier coefficient of a vector.** The vector mode is the angular average with phase exp of minus i times the selected azimuthal frequency. Source: Breakdown.CellCert.CellAnalysis.modeVec in FractionalCellSystemChallenge, line 330. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L330).

**Angular Fourier coefficient of a matrix.** The matrix mode takes the normalized angular Fourier integral of each cylindrical matrix entry. Source: Breakdown.CellCert.CellAnalysis.modeMat in FractionalCellSystemChallenge, line 334. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L334).

**Cylindrical orthonormal frame.** The frame lists the radial, angular and axial unit vectors in that order. Source: Breakdown.CellCert.CellAnalysis.frameUnit in FractionalCellSystemChallenge, line 393. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L393).

**Second derivative in the frame.** A frame component of the second derivative evaluates the two input directions and pairs the output with a third frame vector. Source: Breakdown.CellCert.CellAnalysis.frameThird in FractionalCellSystemChallenge, line 395. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L395).

**Angular mode of a second derivative.** The third-order mode takes the normalized angular Fourier integral of a frame component of the second derivative. Source: Breakdown.CellCert.CellAnalysis.modeThird in FractionalCellSystemChallenge, line 398. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L398).

**Gradient mode at a radial point.** The gradient-mode accessor evaluates the corresponding matrix mode at the supplied radius and height. Source: Breakdown.CellCert.CellAnalysis.gradMode in FractionalCellSystemChallenge, line 403. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L403).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellBox.

**Angular weight at the axis.** The angular weight has separate axis branches for zero and nonzero modes and uses the reciprocal outer radius off the axis. Source: Breakdown.CellCert.CellAnalysis.CellBox.angularWeight in FractionalCellSystemChallenge, line 426. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L426).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellBases.

**Weighted cell polynomial coefficient.** A cell coefficient integrates the field against the radial and height basis polynomials with the cell's line weight. Source: Breakdown.CellCert.CellAnalysis.CellBases.coef in FractionalCellSystemChallenge, line 449. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L449).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellScalars.

**Physical weight on a cell chart.** The sampled weight evaluates the physical weight at cylindrical angle zero. Source: Breakdown.CellCert.CellAnalysis.CellScalars.sampleWeight in FractionalCellSystemChallenge, line 512. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L512).

**Radial and height tail eigenvalue.** The tail parameter multiplies the sum of radial and height eigenvalues by the cell's inner-radius factor. Source: Breakdown.CellCert.CellAnalysis.CellScalars.tailLam in FractionalCellSystemChallenge, line 516. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L516).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Absolute azimuthal frequency.** The mode number is the absolute value of the azimuthal frequency. Source: Breakdown.CellCert.CellAnalysis.modeNumber in FractionalCellSystemChallenge, line 526. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L526).

**Alternating matrix from a vector.** The bracket matrix contracts a vector with the permutation signs in the indicated index order. Source: Breakdown.CellCert.CellAnalysis.bracketMat in FractionalCellSystemChallenge, line 534. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L534).

**Gradient and velocity coupling.** The coupling map combines the negative bracket of the matrix-vector product with a half-weighted bracket-matrix term. Source: Breakdown.CellCert.CellAnalysis.couplingMap in FractionalCellSystemChallenge, line 537. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L537).

**Complex matrix entry pairing.** The entry pairing sums each entry of the first matrix times the conjugate entry of the second. Source: Breakdown.CellCert.CellAnalysis.entryPairing in FractionalCellSystemChallenge, line 541. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L541).

**Wave interaction form.** The wave form combines the strain pairing of two curls with the two half-weighted gradient and velocity couplings. Source: Breakdown.CellCert.CellAnalysis.waveForm in FractionalCellSystemChallenge, line 543. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L543).

**Harmonic class data.** Each harmonic class records its modes, four deviation bounds, sharing weights and resolved portion. Source: Breakdown.CellCert.CellAnalysis.CellClasses in FractionalCellSystemChallenge, line 548. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L548).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellScalars.

**Model strain Fourier mode.** The strain mode is the selected angular Fourier coefficient of the model strain. Source: Breakdown.CellCert.CellAnalysis.CellScalars.strainMode in FractionalCellSystemChallenge, line 587. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L587).

**Model curl gradient Fourier mode.** The curl gradient mode is the selected angular Fourier coefficient of the model curl gradient. Source: Breakdown.CellCert.CellAnalysis.CellScalars.curlGradMode in FractionalCellSystemChallenge, line 589. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L589).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Adjoint curl contraction.** The adjoint curl contraction builds a matrix from a vector using the transposed permutation-sign contraction. Source: Breakdown.CellCert.CellAnalysis.curlAdj in FractionalCellSystemChallenge, line 599. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L599).

**Adjoint velocity coupling.** The adjoint coupling contracts the matrix argument with conjugated gradient entries and the permutation signs. Source: Breakdown.CellCert.CellAnalysis.couplingAdj in FractionalCellSystemChallenge, line 602. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L602).

**Complex matrix-vector product.** The matrix-vector product sums the three coordinate products in each row. Source: Breakdown.CellCert.CellAnalysis.matVec in FractionalCellSystemChallenge, line 607. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L607).

**Strain part of the wave action.** The strain action adds the negative adjoint curl of the strain-curl product to half the velocity coupling. Source: Breakdown.CellCert.CellAnalysis.waveActionStrain in FractionalCellSystemChallenge, line 609. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L609).

**Velocity part of the wave action.** The velocity action is half the adjoint gradient coupling applied to the strain argument. Source: Breakdown.CellCert.CellAnalysis.waveActionVelocity in FractionalCellSystemChallenge, line 613. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L613).

**First nine strain coordinates.** The strain block reads the first nine coordinates of a twelve-component vector as a three-by-three matrix. Source: Breakdown.CellCert.CellAnalysis.splitStrain in FractionalCellSystemChallenge, line 616. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L616).

**Last three velocity coordinates.** The velocity block reads coordinates nine through eleven of the twelve-component vector. Source: Breakdown.CellCert.CellAnalysis.splitVelocity in FractionalCellSystemChallenge, line 618. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L618).

**Twelve-dimensional matrix action.** The matrix action takes the ordinary finite row sum on twelve complex coordinates. Source: Breakdown.CellCert.CellAnalysis.matAct in FractionalCellSystemChallenge, line 620. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L620).

**Inverse angular adjoint formula.** The angular adjoint inverse is defined by explicit rational expressions with denominators one minus k squared and minus i times k. Source: Breakdown.CellCert.CellAnalysis.turnAdjInv in FractionalCellSystemChallenge, line 628. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L628).

**Fold velocity into angular strain.** Velocity folding adds the radius times the angular adjoint inverse to the angular column of the strain matrix. Source: Breakdown.CellCert.CellAnalysis.foldVelocity in FractionalCellSystemChallenge, line 633. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L633).

**Cell row and far-field data.** The cell row data collect mode sets, selected rows, multiplier and reducer matrices, far support and a far kernel. Source: Breakdown.CellCert.CellAnalysis.CellRows in FractionalCellSystemChallenge, line 636. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L636).

**Complex cross product.** The complex cross product uses the same cyclic coordinate formula as the real vector product. Source: Breakdown.CellCert.CellAnalysis.crossC in FractionalCellSystemChallenge, line 661. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L661).

**Coordinatewise complex conjugation.** Vector conjugation conjugates each of the three complex coordinates. Source: Breakdown.CellCert.CellAnalysis.conjVec3 in FractionalCellSystemChallenge, line 663. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L663).

**Cartesian vector from frame coordinates.** A Cartesian vector is reconstructed as the sum of its three cylindrical frame components. Source: Breakdown.CellCert.CellAnalysis.cartOfFrame in FractionalCellSystemChallenge, line 665. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L665).

**Cartesian map from frame entries.** The reconstructed linear map sums the frame rank-one maps weighted by their matrix entries. Source: Breakdown.CellCert.CellAnalysis.cartOpOfFrame in FractionalCellSystemChallenge, line 667. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L667).

**Cylindrical angle.** The cylindrical angle is the complex argument of the horizontal coordinates. Source: Breakdown.CellCert.CellAnalysis.cylAngle in FractionalCellSystemChallenge, line 670. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L670).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellScalars.

**Angular mode of one row field.** A row mode takes the normalized angular Fourier coefficient of the chosen row field. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowMode in FractionalCellSystemChallenge, line 678. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L678).

**Row coupling to strain.** The strain row coupling sums adjoint curls of cross products between conjugated model velocity modes and row modes. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowCouplingStrain in FractionalCellSystemChallenge, line 680. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L680).

**Row coupling to velocity.** The velocity row coupling sums cross products of row modes with conjugated model curl modes. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowCouplingVelocity in FractionalCellSystemChallenge, line 684. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L684).

**Folded row coupling.** Resolved modes keep the strain row coupling, while other modes fold the velocity coupling into it. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowCouplingFolded in FractionalCellSystemChallenge, line 688. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L688).

**Weighted symmetric matrix pairing.** The weighted pairing takes symmetric and antisymmetric entry pairings with Y first and X conjugated second, divided by their respective weights. Source: Breakdown.CellCert.CellAnalysis.CellScalars.sigmaWeightedPair in FractionalCellSystemChallenge, line 692. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L692).

**Near polynomial row square.** The row square sums selected near-mode coefficient energies with separate strain and velocity thresholds and weights. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowSquare in FractionalCellSystemChallenge, line 696. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L696).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Matrix field of one harmonic class.** The class matrix field reconstructs the selected finite set of angular modes with their oscillatory phases. Source: Breakdown.CellCert.CellAnalysis.classField in FractionalCellSystemChallenge, line 718. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L718).

**Vector field of one harmonic class.** The class vector field reconstructs the selected finite set of vector modes with their oscillatory phases. Source: Breakdown.CellCert.CellAnalysis.classVec in FractionalCellSystemChallenge, line 721. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L721).

**Squared operator bound.** The operator-bound proposition requires the squared output norm to be at most delta squared times the squared input norm. Source: Breakdown.CellCert.CellAnalysis.OpBound in FractionalCellSystemChallenge, line 724. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L724).

**Source namespace:** Breakdown.CellCert.CellFormula.ParamData.

**Solved datum coordinates.** The solved set is the image of the chosen solved-coordinate map. Source: Breakdown.CellCert.CellFormula.ParamData.solvedSet in FractionalCellSystemChallenge, line 753. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L753).

**Free datum coordinates.** The free set contains exactly the datum coordinates outside the solved set. Source: Breakdown.CellCert.CellFormula.ParamData.freeSet in FractionalCellSystemChallenge, line 755. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L755).

**Interior free coordinates.** The interior set removes the skeleton coordinates from the free coordinates. Source: Breakdown.CellCert.CellFormula.ParamData.interiorSet in FractionalCellSystemChallenge, line 757. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L757).

**Free component of a datum vector.** The free component zeroes solved coordinates and preserves the remaining values. Source: Breakdown.CellCert.CellFormula.ParamData.freePart in FractionalCellSystemChallenge, line 761. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L761).

**Solve the finite coordinate relations.** The parameterization corrects the free vector at solved coordinates using the inverse solved block of the relation matrix. Source: Breakdown.CellCert.CellFormula.ParamData.param in FractionalCellSystemChallenge, line 763. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L763).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Weak corner moment.** The corner moment integrates the field and its first and mixed derivatives with the two oriented affine trace weights. Source: Breakdown.CellCert.CellFormula.cornerMoment in FractionalCellSystemChallenge, line 806. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L806).

**Weak scalar potential.** A scalar potential is measurable, locally square integrable and has the prescribed vector field as its distributional gradient. Source: Breakdown.CellCert.CellFormula.IsPotentialOf in FractionalCellSystemChallenge, line 844. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L844).

**Chosen scalar potential.** The potential selector chooses a weak scalar potential when one exists and returns the zero function otherwise. Source: Breakdown.CellCert.CellFormula.potentialOf in FractionalCellSystemChallenge, line 850. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L850).

**Source namespace:** Breakdown.CellCert.CellFormula.CellDatum.

**Pressure datum on a side.** The side-pressure constructor inserts a mode, pressure segment and polynomial degree into the pressure branch of the cell datum type. Source: Breakdown.CellCert.CellFormula.CellDatum.sidePressure in FractionalCellSystemChallenge, line 897. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L897).

**Source namespace:** Breakdown.CellCert.CellFormula.CellLayout.

**Velocity mode of a field tuple.** The velocity-mode accessor extracts the chosen component of the tuple's angular velocity mode. Source: Breakdown.CellCert.CellFormula.CellLayout.velMode in FractionalCellSystemChallenge, line 923. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L923).

**Gradient mode of a field tuple.** The gradient-mode accessor reads the first derivative field from the tuple before taking its angular mode. Source: Breakdown.CellCert.CellFormula.CellLayout.gradModeOf in FractionalCellSystemChallenge, line 926. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L926).

**Second derivative mode of a tuple.** The second-mode accessor reads the second derivative tensor and takes its selected angular component. Source: Breakdown.CellCert.CellFormula.CellLayout.secondModeOf in FractionalCellSystemChallenge, line 929. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L929).

**Pressure gradient mode of a tuple.** The pressure-gradient mode takes an angular vector coefficient of the tuple's pressure-gradient field. Source: Breakdown.CellCert.CellFormula.CellLayout.pressureGradMode in FractionalCellSystemChallenge, line 932. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L932).

**Pressure gauge moment.** The gauge value applies the selected gauge moment to the zero pressure mode and its radial and height derivatives. Source: Breakdown.CellCert.CellFormula.CellLayout.gaugeValue in FractionalCellSystemChallenge, line 935. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L935).

**Gauge moment of a constant.** The gauge unit evaluates the gauge moment on the constant-one field with zero derivatives. Source: Breakdown.CellCert.CellFormula.CellLayout.gaugeUnit in FractionalCellSystemChallenge, line 939. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L939).

**Gauge-fixed pressure potential.** The pressure potential is shifted by the real part of the quotient of its gauge value and its gauge unit. Source: Breakdown.CellCert.CellFormula.CellLayout.pressureOf in FractionalCellSystemChallenge, line 941. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L941).

**Angular mode of gauge-fixed pressure.** The pressure mode takes the normalized angular coefficient of the gauge-fixed scalar potential. Source: Breakdown.CellCert.CellFormula.CellLayout.pressMode in FractionalCellSystemChallenge, line 944. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L944).

**Additional side velocity moment.** The extra-value accessor chooses the oriented radial or height strip moment for the specified side. Source: Breakdown.CellCert.CellFormula.CellLayout.extraValue in FractionalCellSystemChallenge, line 951. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L951).

**Cell data extracted from fields.** The true-data map evaluates each datum branch as a low coefficient, side trace, corner trace, stream moment or additional side moment. Source: Breakdown.CellCert.CellFormula.CellLayout.trueData in FractionalCellSystemChallenge, line 957. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L957).

**Lookup of a low datum coordinate.** The low-entry lookup returns a datum only when its mode and strain or velocity degree bounds fit the layout. Source: Breakdown.CellCert.CellFormula.CellLayout.lowEntry in FractionalCellSystemChallenge, line 1109. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1109).

**Complex coordinates from real pairs.** A complex datum is reconstructed from the paired real and imaginary coordinates. Source: Breakdown.CellCert.CellFormula.CellLayout.realCoord in FractionalCellSystemChallenge, line 1119. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1119).

**Real coordinates of a complex datum.** The real-coordinate map selects the real part for index zero and the imaginary part for index one. Source: Breakdown.CellCert.CellFormula.CellLayout.realPart in FractionalCellSystemChallenge, line 1121. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1121).

**Negated mode with fallback.** The negated-mode selector returns the negative mode when it belongs to the layout and otherwise keeps the original mode. Source: Breakdown.CellCert.CellFormula.CellLayout.negMode in FractionalCellSystemChallenge, line 1233. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1233).

**Conjugate datum index.** The conjugate-datum map applies the layout's negMode selector in every mode-bearing branch and leaves the stream branch unchanged. Source: Breakdown.CellCert.CellFormula.CellLayout.conjDatum in FractionalCellSystemChallenge, line 1235. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1235).

**Angular frequency of a datum.** The datum's mode is its stored angular index, with zero assigned to the stream branch. Source: Breakdown.CellCert.CellFormula.CellLayout.modeOf in FractionalCellSystemChallenge, line 1241. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1241).

**Coordinates removed by reflection.** Plane deletion marks the side, corner and stream coordinates forced out by their position and component on the reflection plane. Source: Breakdown.CellCert.CellFormula.CellLayout.IsPlaneDeleted in FractionalCellSystemChallenge, line 1245. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1245).

**Coordinates removed by the gauge.** Gauge deletion marks the zero-mode pressure coordinates listed in the layout's deleted gauge set. Source: Breakdown.CellCert.CellFormula.CellLayout.IsGaugeDeleted in FractionalCellSystemChallenge, line 1253. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1253).

**Independent real system coordinate.** A system coordinate selects positive modes or the real part of mode zero and excludes plane-deleted and gauge-deleted data. Source: Breakdown.CellCert.CellFormula.CellLayout.IsSystemCoord in FractionalCellSystemChallenge, line 1257. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1257).

**Sign under complex conjugation.** The real coordinate has conjugation sign one and the imaginary coordinate has sign minus one. Source: Breakdown.CellCert.CellFormula.CellLayout.partSign in FractionalCellSystemChallenge, line 1260. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1260).

**Expand independent system coordinates.** System expansion preserves retained coordinates, fills negative modes by signed conjugation and sets all other coordinates to zero. Source: Breakdown.CellCert.CellFormula.CellLayout.expandSystem in FractionalCellSystemChallenge, line 1263. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1263).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Admissible pressure layout.** A pressure layout requires a valid cell layout, conjugation closure and a disjoint orthonormal coverage of the pressure sides. Source: Breakdown.CellCert.CellFormula.IsPressureLayout in FractionalCellSystemChallenge, line 1270. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1270).

**Pressure gauge shift data.** A gauge shift records the left, right and radial-point constants assigned to a field tuple. Source: Breakdown.CellCert.CellFormula.GaugeShift in FractionalCellSystemChallenge, line 1292. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1292).

**Source namespace:** Breakdown.CellCert.CellFormula.CellLayout.

**Pressure data induced by a gauge shift.** A pressure shift changes only zero-mode pressure data through radial-side integrals and horizontal-side endpoint differences of the gauge constants. Source: Breakdown.CellCert.CellFormula.CellLayout.pressureShift in FractionalCellSystemChallenge, line 1303. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1303).

**Cell data after a gauge shift.** Shifted data add the gauge-induced pressure shift to the field's true cell data. Source: Breakdown.CellCert.CellFormula.CellLayout.shiftedData in FractionalCellSystemChallenge, line 1316. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1316).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Gauge edge and root choices.** A gauge specification records an optional edge coordinate and a set of root pressure coordinates. Source: Breakdown.CellCert.CellFormula.GaugeSpec in FractionalCellSystemChallenge, line 1321. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1321).

**Source namespace:** Breakdown.CellCert.CellFormula.CellLayout.

**Left gauge coefficient.** The left coefficient measures how the left pressure constant changes a chosen side-pressure moment. Source: Breakdown.CellCert.CellFormula.CellLayout.shiftCoefLeft in FractionalCellSystemChallenge, line 1329. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1329).

**Right gauge coefficient.** The right coefficient measures how the right pressure constant changes a chosen side-pressure moment. Source: Breakdown.CellCert.CellFormula.CellLayout.shiftCoefRight in FractionalCellSystemChallenge, line 1339. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1339).

**Real zero-mode pressure datum.** The pressure-datum value reads the real zero-mode side-pressure value and returns zero when no zero mode is available. Source: Breakdown.CellCert.CellFormula.CellLayout.pressureDatumValue in FractionalCellSystemChallenge, line 1349. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1349).

**Pressure jump chosen by an edge.** The gauge jump is the negative selected edge pressure datum divided by its right coefficient, with zero when no edge is selected. Source: Breakdown.CellCert.CellFormula.CellLayout.gaugeJump in FractionalCellSystemChallenge, line 1354. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1354).

**Gauge shift from two constants.** The constructed gauge shift uses the right constant at the outer radius and the left constant at every other radius. Source: Breakdown.CellCert.CellFormula.CellLayout.gaugeShiftOf in FractionalCellSystemChallenge, line 1359. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1359).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Conditions on the gauge choices.** A valid gauge specification identifies deleted edge and root data and requires the zero mode, distinct radii and nondegenerate balanced edge coefficients. Source: Breakdown.CellCert.CellFormula.IsGaugeSpec in FractionalCellSystemChallenge, line 1366. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1366).

**Source namespace:** Breakdown.CellCert.CellEnergy.

**Sesquilinear matrix pairing.** The matrix sesquilinear pairing conjugates the first matrix entries before multiplying by the second entries. Source: Breakdown.CellCert.CellEnergy.sumSesq in FractionalCellSystemChallenge, line 1570. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1570).

**Sesquilinear vector pairing.** The vector sesquilinear pairing conjugates each first-vector coordinate before multiplying by the second. Source: Breakdown.CellCert.CellEnergy.vecSesq in FractionalCellSystemChallenge, line 1572. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1572).

**Sesquilinear curl pairing.** The curl pairing applies the sesquilinear vector pairing to the curls of the two matrix arguments. Source: Breakdown.CellCert.CellEnergy.curlSesq in FractionalCellSystemChallenge, line 1574. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1574).

**Pairwise mode energy form.** The pair form combines the model's wave interaction with the local matrix term when the two angular modes agree. Source: Breakdown.CellCert.CellEnergy.pairSesq in FractionalCellSystemChallenge, line 1586. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1586).

**Integrated low-mode pair matrix.** The pair matrix integrates the pairwise mode form against the weighted slot rows on the cell. Source: Breakdown.CellCert.CellEnergy.pairForm in FractionalCellSystemChallenge, line 1591. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1591).

**Harmonic-class loss matrix.** The class matrix integrates the strain and gradient deviation losses on each class's resolved modes. Source: Breakdown.CellCert.CellEnergy.classForm in FractionalCellSystemChallenge, line 1597. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1597).

**Actuator coupling row.** The actuator row pairs the low strain basis with actuator-gradient modes using the half-weighted cell measure. Source: Breakdown.CellCert.CellEnergy.actuatorRow in FractionalCellSystemChallenge, line 1609. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1609).

**Pin coupling row.** The pin row pairs the low strain basis with the model pin-field modes using the weighted cell measure. Source: Breakdown.CellCert.CellEnergy.pinRow in FractionalCellSystemChallenge, line 1614. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1614).

**Combined actuator and pin rows.** The combined row selects the actuator row on the first branch and the pin row on the second. Source: Breakdown.CellCert.CellEnergy.crossRow in FractionalCellSystemChallenge, line 1619. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1619).

**Local block energy matrix.** The local matrix combines the energy, class-loss and pair forms with the conjugate actuator and pin off-diagonal blocks. Source: Breakdown.CellCert.CellEnergy.localForm in FractionalCellSystemChallenge, line 1623. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1623).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Low-mode coefficient index.** A low index records an angular mode, vector component, strain-or-velocity slot and two polynomial degrees. Source: Breakdown.CellCert.CellFormula.LowIndex in FractionalCellSystemChallenge, line 1661. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1661).

**Finite low-mode support.** The low support combines resolved modes, all component slots and polynomial degrees through the high cutoff. Source: Breakdown.CellCert.CellFormula.lowSupport in FractionalCellSystemChallenge, line 1663. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1663).

**Subtype of retained low indices.** The retained low-index type consists of indices belonging to the finite low support. Source: Breakdown.CellCert.CellFormula.LowSupp in FractionalCellSystemChallenge, line 1666. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1666).

**Low, multiplier and pin coordinates.** The augmented coordinate type adjoins multiplier and pin coordinates to the retained low coefficients. Source: Breakdown.CellCert.CellFormula.Aug in FractionalCellSystemChallenge, line 1668. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1668).

**Rank-one Hermitian matrix.** The rank-one matrix has entries equal to the conjugate of one row component times another. Source: Breakdown.CellCert.CellFormula.rankOne in FractionalCellSystemChallenge, line 1670. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1670).

**Complex linear coordinate form.** The linear form sums row coefficients times the supplied complex coordinates without conjugation. Source: Breakdown.CellCert.CellFormula.linForm in FractionalCellSystemChallenge, line 1672. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1672).

**One strain basis component.** A unit strain field places the product basis polynomial in its matching mode and matrix entry and is zero elsewhere. Source: Breakdown.CellCert.CellFormula.unitStrain in FractionalCellSystemChallenge, line 1678. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1678).

**One velocity basis component.** A unit velocity field places the product basis polynomial in its matching mode and velocity component and is zero elsewhere. Source: Breakdown.CellCert.CellFormula.unitVelocity in FractionalCellSystemChallenge, line 1682. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1682).

**Strain from retained coefficients.** Strain synthesis sums the retained strain basis fields weighted by the low-coordinate entries. Source: Breakdown.CellCert.CellFormula.synthStrain in FractionalCellSystemChallenge, line 1686. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1686).

**Velocity from retained coefficients.** Velocity synthesis sums the retained velocity basis fields weighted by the low-coordinate entries. Source: Breakdown.CellCert.CellFormula.synthVelocity in FractionalCellSystemChallenge, line 1689. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1689).

**Multiplier coordinates of a vector.** The multiplier accessor reads the first finite-dimensional branch of the augmented coordinate vector. Source: Breakdown.CellCert.CellFormula.kappaPart in FractionalCellSystemChallenge, line 1692. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1692).

**Pin coordinates of a vector.** The pin accessor reads the second finite-dimensional branch of the augmented coordinate vector. Source: Breakdown.CellCert.CellFormula.pinPart in FractionalCellSystemChallenge, line 1694. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1694).

**Strain residual from mode fields.** The strain residual combines wave interactions, resolved local-matrix action and actuator and pin contributions with the radial factor. Source: Breakdown.CellCert.CellFormula.yStrainOf in FractionalCellSystemChallenge, line 1696. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1696).

**Velocity residual from mode fields.** The velocity residual combines the wave velocity action and the resolved local-matrix velocity block with the radial factor. Source: Breakdown.CellCert.CellFormula.yVelocityOf in FractionalCellSystemChallenge, line 1705. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1705).

**Folded residual field.** Resolved modes keep the strain residual, while other modes fold the velocity residual into the angular strain column. Source: Breakdown.CellCert.CellFormula.yFoldedOf in FractionalCellSystemChallenge, line 1712. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1712).

**Polynomial coefficient of a residual.** The residual coefficient applies the cell basis integral to a component of the folded residual built from the augmented vector. Source: Breakdown.CellCert.CellFormula.yCoef in FractionalCellSystemChallenge, line 1717. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1717).

**Polynomial velocity residual.** The velocity coefficient applies the cell basis integral to the velocity residual synthesized from the retained coordinates. Source: Breakdown.CellCert.CellFormula.yVelCoef in FractionalCellSystemChallenge, line 1720. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1720).

**Residual row on coordinate vectors.** A residual row evaluates the residual coefficient on each unit coordinate vector. Source: Breakdown.CellCert.CellFormula.yVec in FractionalCellSystemChallenge, line 1724. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1724).

**Symmetric residual row.** The symmetric row averages the two residual rows obtained by exchanging the matrix indices. Source: Breakdown.CellCert.CellFormula.symVec in FractionalCellSystemChallenge, line 1726. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1726).

**Antisymmetric residual row.** The antisymmetric row takes half the difference of the exchanged-index residual rows. Source: Breakdown.CellCert.CellFormula.antiVec in FractionalCellSystemChallenge, line 1729. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1729).

**Velocity residual coordinate row.** The velocity row evaluates a velocity residual coefficient on each unit coordinate vector. Source: Breakdown.CellCert.CellFormula.velVec in FractionalCellSystemChallenge, line 1733. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1733).

**Near residual energy matrix.** The near matrix sums weighted rank-one strain and velocity residual matrices beyond their separate retained-degree thresholds. Source: Breakdown.CellCert.CellFormula.nearMatrix in FractionalCellSystemChallenge, line 1742. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1742).

**Strain row coupling coefficient.** The strain row coefficient integrates a folded row coupling against the selected radial and height basis functions. Source: Breakdown.CellCert.CellFormula.rowCouplingCoef in FractionalCellSystemChallenge, line 1754. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1754).

**Velocity row coupling coefficient.** The velocity row coefficient integrates the velocity row coupling against the selected radial and height basis functions. Source: Breakdown.CellCert.CellFormula.rowCouplingVelCoef in FractionalCellSystemChallenge, line 1757. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1757).

**Residual coupling to a row.** The row-residual vector sums weighted pairings of residual rows with conjugated strain and velocity row-coupling coefficients. Source: Breakdown.CellCert.CellFormula.rowYVec in FractionalCellSystemChallenge, line 1760. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1760).

**Augmented index in the far space.** The far-index map forgets the low-support membership proof and preserves multiplier and pin branches. Source: Breakdown.CellCert.CellFormula.augToFar in FractionalCellSystemChallenge, line 1778. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1778).

**Far matrix restricted to its support.** The far matrix evaluates the supplied kernel unless either low-index argument lies outside its support, in which case it returns zero. Source: Breakdown.CellCert.CellFormula.farMatrix in FractionalCellSystemChallenge, line 1781. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1781).

**Fourier coefficient of a row vector.** The row-vector mode is the chosen angular mode of the certificate's row field. Source: Breakdown.CellCert.CellFormula.rowModeVec in FractionalCellSystemChallenge, line 1791. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1791).

**Fourier coefficient of a row gradient.** The row-gradient mode is the chosen angular mode of the Fréchet derivative of the row field. Source: Breakdown.CellCert.CellFormula.rowModeGrad in FractionalCellSystemChallenge, line 1793. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1793).

**Complex vector pairing.** The complex vector pairing sums the first vector times the conjugate of the second. Source: Breakdown.CellCert.CellFormula.pairC in FractionalCellSystemChallenge, line 1796. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1796).

**Position in the cylindrical frame.** The position vector has cylindrical components radius, zero and height. Source: Breakdown.CellCert.CellFormula.frameY in FractionalCellSystemChallenge, line 1798. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1798).

**Rotation of the position vector.** The axial rotation of position has cylindrical components zero, radius and zero. Source: Breakdown.CellCert.CellFormula.frameTurnY in FractionalCellSystemChallenge, line 1800. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1800).

**Axial rotation of a complex vector.** Axial rotation sends the first two coordinates to minus the second and the first and sets the third to zero. Source: Breakdown.CellCert.CellFormula.turnC in FractionalCellSystemChallenge, line 1802. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1802).

**Tensor-product basis value.** The basis value is the product of the chosen radial and height polynomials, regarded as a complex number. Source: Breakdown.CellCert.CellFormula.basisVal in FractionalCellSystemChallenge, line 1804. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1804).

**Interior strain row coefficient.** The strain row coefficient integrates similarity drift, rotation, split viscosity and model-velocity coupling against the row modes. Source: Breakdown.CellCert.CellFormula.strainRowCoef in FractionalCellSystemChallenge, line 1806. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1806).

**Interior velocity row coefficient.** The velocity row coefficient integrates the zeroth-order similarity, rotation and model-curl terms against the row modes. Source: Breakdown.CellCert.CellFormula.velocityRowCoef in FractionalCellSystemChallenge, line 1817. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1817).

**Weak trace against a side test.** The segment trace applies the non-pressure moment to a field and its radial and height derivatives. Source: Breakdown.CellCert.CellFormula.segmentTrace in FractionalCellSystemChallenge, line 1826. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1826).

**Gradient contribution on a side.** The gradient-side row coefficient multiplies the conjugated row trace by the negative split viscosity and oriented boundary weight. Source: Breakdown.CellCert.CellFormula.gradSideRowCoef in FractionalCellSystemChallenge, line 1829. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1829).

**Pressure contribution on a side.** The pressure-side coefficient uses the conjugated normal row trace with its oriented radial or height boundary weight. Source: Breakdown.CellCert.CellFormula.presSideRowCoef in FractionalCellSystemChallenge, line 1834. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1834).

**Normal component of a segment.** A radial segment uses component zero as its normal, while a height segment uses component two. Source: Breakdown.CellCert.CellFormula.segmentNormal in FractionalCellSystemChallenge, line 1840. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1840).

**Normal component of a box side.** The first two box sides use the radial normal component and the remaining two use the height component. Source: Breakdown.CellCert.CellFormula.sideNormal in FractionalCellSystemChallenge, line 1842. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1842).

**Location of a box side.** The side level selects the inner radius, outer radius, lower height or upper height according to the side index. Source: Breakdown.CellCert.CellFormula.faceLevel in FractionalCellSystemChallenge, line 1844. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1844).

**Opposite side coordinate.** The opposite coordinate subtracts the selected side level from the sum of the two corresponding box bounds. Source: Breakdown.CellCert.CellFormula.faceOther in FractionalCellSystemChallenge, line 1847. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1847).

**Normal row coefficient on a face.** The face coefficient integrates the normal row mode against the appropriate height or weighted radial basis polynomial. Source: Breakdown.CellCert.CellFormula.faceRowCoef in FractionalCellSystemChallenge, line 1850. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1850).

**Normal-gradient boundary data.** The normal-face row sums oriented viscosity contributions on all faces except the inner radial face when it lies on the axis. Source: Breakdown.CellCert.CellFormula.normalFaceRowData in FractionalCellSystemChallenge, line 1857. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1857).

**Complete row on cell data.** The layout row combines interior strain and velocity coefficients with tangential gradient, pressure and normal-face boundary terms. Source: Breakdown.CellCert.CellFormula.layoutRowData in FractionalCellSystemChallenge, line 1864. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1864).

**Actuator coefficient in a cell row.** The multiplier row coefficient is the full-space actuator-row pairing divided by four pi. Source: Breakdown.CellCert.CellFormula.layoutRowKappa in FractionalCellSystemChallenge, line 1873. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1873).

**Inputs of the exact cell formula.** The formula inputs record datum coordinates, field traces, low-entry lookup, row maps and the local matrix. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs in FractionalCellSystemChallenge, line 1878. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1878).

**Source namespace:** Breakdown.CellCert.CellFormula.CellFormulaInputs.

**Real coordinates of the cell formula.** The formula coordinate type joins skeleton, interior, multiplier and pin coordinates. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.Coord in FractionalCellSystemChallenge, line 1898. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1898).

**Data with multiplier and pin values.** The data vector appends the real multiplier and pin values as complex coordinates. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.dataVec in FractionalCellSystemChallenge, line 1900. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1900).

**Retained coefficients from cell data.** The augmented data vector reads available low entries, substitutes zero for missing entries and appends multiplier and pin values. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.augOfData in FractionalCellSystemChallenge, line 1903. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1903).

**Value of a cell row.** A row value adds the real part of the datum-row pairing to its multiplier-coordinate contribution. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.rowValue in FractionalCellSystemChallenge, line 1906. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1906).

**Row residual after near coupling.** The row residual subtracts the real residual-coupling form from the original row value. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.residualValue in FractionalCellSystemChallenge, line 1909. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1909).

**Scalar exact cell formula.** The scalar formula subtracts near and far residual energies from the local form, adds reduced residual squares and divides by the split viscosity. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.formulaValue in FractionalCellSystemChallenge, line 1913. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1913).

**Matrix recovered by polarization.** The exact matrix is recovered from the scalar formula by evaluating two unit vectors together and subtracting their separate values, then dividing by two. Source: Breakdown.CellCert.CellFormula.CellFormulaInputs.exactFormula in FractionalCellSystemChallenge, line 1924. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1924).

**Source namespace:** Breakdown.CellCert.CellFormula.

**Real skeleton coordinates.** The skeleton coordinate set retains both real components of every datum belonging to the skeleton. Source: Breakdown.CellCert.CellFormula.skeletonCoords in FractionalCellSystemChallenge, line 1935. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1935).

**Real interior coordinates.** The interior coordinate set retains both real components of every datum in the free interior set. Source: Breakdown.CellCert.CellFormula.interiorCoords in FractionalCellSystemChallenge, line 1937. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1937).

**Embed skeleton and interior values.** Coordinate embedding reads the skeleton or interior vector through its finite enumeration and returns zero elsewhere. Source: Breakdown.CellCert.CellFormula.embedCoords in FractionalCellSystemChallenge, line 1939. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1939).

**Cell formula from canonical data.** The canonical formula inputs assemble the parameterized coordinates, shifted field data, row coefficients and local energy matrix. Source: Breakdown.CellCert.CellFormula.canonicalInputs in FractionalCellSystemChallenge, line 1943. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1943).

**Source namespace:** Breakdown.CellCert.CellCoordinates.

**Independent skeleton coordinates.** System skeleton coordinates filter the skeleton set by the independent-coordinate predicate. Source: Breakdown.CellCert.CellCoordinates.systemSkeletonCoords in FractionalCellSystemChallenge, line 1984. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1984).

**Independent interior coordinates.** System interior coordinates filter the interior set by the independent-coordinate predicate. Source: Breakdown.CellCert.CellCoordinates.systemInteriorCoords in FractionalCellSystemChallenge, line 1988. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1988).

**Vector on independent coordinates.** The system vector inserts the chosen skeleton and interior values and assigns zero to all other coordinates. Source: Breakdown.CellCert.CellCoordinates.systemVector in FractionalCellSystemChallenge, line 1991. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1991).

**Pressure branch of a cell datum.** The pressure-datum predicate holds exactly on the side-pressure branch of the datum type. Source: Breakdown.CellCert.CellCoordinates.IsPressureDatum in FractionalCellSystemChallenge, line 1996. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1996).

**Pressure coordinate viscosity scale.** Pressure coordinates receive the supplied viscosity scale and all other coordinates receive scale one. Source: Breakdown.CellCert.CellCoordinates.presetScale in FractionalCellSystemChallenge, line 2001. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2001).

**Expand and scale system coordinates.** Expanded coordinates restore conjugate data and apply the viscosity factor to pressure coordinates before finite enumeration. Source: Breakdown.CellCert.CellCoordinates.expandedCoords in FractionalCellSystemChallenge, line 2003. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2003).

**Local coordinates and gauge choices.** Cell-coordinate data combine a layout, parameterization, relation choices, global-to-local map, gauge choices and a given matrix. Source: Breakdown.CellCert.CellCoordinates.CellCoords in FractionalCellSystemChallenge, line 2012. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2012).

**Source namespace:** Breakdown.CellCert.CellCoordinates.CellCoords.

**Restrict a global state to one cell.** State restriction applies the skeleton map and divides the multiplier and pin coordinates by the supplied viscosity. Source: Breakdown.CellCert.CellCoordinates.CellCoords.restrictState in FractionalCellSystemChallenge, line 2027. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2027).

**Exact formula for local coordinates.** The cell-coordinate formula builds canonical inputs using the selected left and right gauge shifts. Source: Breakdown.CellCert.CellCoordinates.CellCoords.formula in FractionalCellSystemChallenge, line 2032. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2032).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellBox.

**Radial polynomial projection tail.** The radial tail subtracts retained coefficient squares from the weighted radial squared norm. Source: Breakdown.CellCert.CellAnalysis.CellBox.radialTail in FractionalCellSystemChallenge, line 2065. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2065).

**Height polynomial projection tail.** The height tail subtracts retained coefficient squares from the height squared norm. Source: Breakdown.CellCert.CellAnalysis.CellBox.heightTail in FractionalCellSystemChallenge, line 2070. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2070).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Families of polynomial tail columns.** A tail family records mode sets, multiplier columns, output weights, degree bounds and radial and height majorants. Source: Breakdown.CellCert.CellAnalysis.TailFamily in FractionalCellSystemChallenge, line 2076. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2076).

**Source namespace:** Breakdown.CellCert.CellAnalysis.TailFamily.

**Total radial tail-column bound.** The radial total sums the radial bounds over every family and retained input degree. Source: Breakdown.CellCert.CellAnalysis.TailFamily.radialTotal in FractionalCellSystemChallenge, line 2090. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2090).

**Total height tail-column bound.** The height total sums the height bounds over every family and retained input degree. Source: Breakdown.CellCert.CellAnalysis.TailFamily.heightTotal in FractionalCellSystemChallenge, line 2092. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2092).

**Source namespace:** Breakdown.CellCert.CellAnalysis.

**Radial and height far bounds.** The far-group data supply one radial and one height bound for each input group and degree. Source: Breakdown.CellCert.CellAnalysis.FarGroupBounds in FractionalCellSystemChallenge, line 2096. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2096).

**Far residual majorant data.** The far-majorant data collect the three group bounds, their weights, a sharing parameter and positive-floor candidates. Source: Breakdown.CellCert.CellAnalysis.FarMajorantData in FractionalCellSystemChallenge, line 2100. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2100).

**Source namespace:** Breakdown.CellCert.CellAnalysis.CellScalars.

**Model strain at a frame point.** The pointwise strain matrix is the complex embedding of the model strain in the cylindrical frame. Source: Breakdown.CellCert.CellAnalysis.CellScalars.strainAt in FractionalCellSystemChallenge, line 2116. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2116).

**Model curl gradient at a frame point.** The pointwise curl gradient is the complex embedding of the model tensor in the cylindrical frame. Source: Breakdown.CellCert.CellAnalysis.CellScalars.curlGradAt in FractionalCellSystemChallenge, line 2119. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2119).

**Complex coordinate unit vector.** The unit vector has value one in the selected component and zero in the other components. Source: Breakdown.CellCert.CellAnalysis.CellScalars.unitVec3 in FractionalCellSystemChallenge, line 2122. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2122).

**Complex coordinate unit matrix.** The unit matrix has a single nonzero entry determined by the flattened three-by-three index. Source: Breakdown.CellCert.CellAnalysis.CellScalars.unitMat in FractionalCellSystemChallenge, line 2124. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2124).

**Strain family for the far bound.** The strain tail family contains the curl-strain and gradient-coupling columns with their distinct input degrees. Source: Breakdown.CellCert.CellAnalysis.CellScalars.strainGroupFamily in FractionalCellSystemChallenge, line 2126. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2126).

**Resolved velocity tail family.** The resolved velocity family applies the wave velocity action to the nine unit matrix inputs on resolved modes. Source: Breakdown.CellCert.CellAnalysis.CellScalars.velocityGroupFamily in FractionalCellSystemChallenge, line 2138. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2138).

**Band velocity tail family.** The band velocity family adds the radial folding factor and restricts its output modes to the unresolved band. Source: Breakdown.CellCert.CellAnalysis.CellScalars.bandGroupFamily in FractionalCellSystemChallenge, line 2148. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2148).

**Read low strain coefficients.** The low-strain accessor reads the three-by-three strain components from the low-index branch of the coefficient vector. Source: Breakdown.CellCert.CellAnalysis.CellScalars.lowStrainCoef in FractionalCellSystemChallenge, line 2158. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2158).

**Read low velocity coefficients.** The low-velocity accessor reads component-slot three from the low-index branch. Source: Breakdown.CellCert.CellAnalysis.CellScalars.lowVelocityCoef in FractionalCellSystemChallenge, line 2161. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2161).

**Combined radial and height weight.** The group weight combines total and individual radial and height bounds within the input-degree cutoff and is zero outside it. Source: Breakdown.CellCert.CellAnalysis.CellScalars.groupWeight in FractionalCellSystemChallenge, line 2164. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2164).

**Quadratic far residual majorant.** The far majorant weights the low strain, curl and velocity squares by the corresponding group-tail bounds. Source: Breakdown.CellCert.CellAnalysis.CellScalars.farMajorantForm in FractionalCellSystemChallenge, line 2168. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2168).

**Row tail through a finite degree.** The truncated row tail sums weighted strain and velocity coefficient squares above the near cutoff and through the specified finite degree. Source: Breakdown.CellCert.CellAnalysis.CellScalars.rowSquareUpTo in FractionalCellSystemChallenge, line 2182. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2182).

**Source namespace:** Breakdown.CellCert.CellCoordinates.

**Pressure gauge positions of a datum.** A pressure datum records its segment level or endpoints and which side supplies the gauge constant, while other datum branches record no positions. Source: Breakdown.CellCert.CellCoordinates.pressurePositions in FractionalCellSystemChallenge, line 2223. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2223).

**Coefficient of a finite row list.** The row-entry function sums the coefficients of every list entry carrying the requested global slot. Source: Breakdown.CellCert.CellCoordinates.rowEntries in FractionalCellSystemChallenge, line 2231. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2231).

**Splitting a segment moment.** A segment split requires two subsegments and exact polynomial identities that reconstruct the original velocity, gradient or pressure test. Source: Breakdown.CellCert.CellCoordinates.SegmentSplit in FractionalCellSystemChallenge, line 2234. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2234).

**Stream value on the symmetry axes.** The stream accessor returns zero on either coordinate axis and otherwise reads the stream skeleton key. Source: Breakdown.CellCert.CellCoordinates.streamEval in FractionalCellSystemChallenge, line 2265. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2265).

**Splitting a zero-mode flux.** A flux split reconstructs a zero-mode normal-velocity moment from subsegment moments and compatible stream differences. Source: Breakdown.CellCert.CellCoordinates.FluxSplit in FractionalCellSystemChallenge, line 2268. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2268).

**Global mesh and gauge data.** The mesh data identify owners of shared moments, pressure-gauge classes and paths, and the delay-slot expansions. Source: Breakdown.CellCert.CellCoordinates.MeshData in FractionalCellSystemChallenge, line 2294. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2294).

**Source namespace:** Breakdown.CellCert.CellCoordinates.MeshData.

**Datum behind a local row number.** The row-datum accessor reverses the finite enumeration of independent skeleton coordinates in the selected cell. Source: Breakdown.CellCert.CellCoordinates.MeshData.rowDatum in FractionalCellSystemChallenge, line 2314. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2314).

**Pressure constant at a gauge root.** The root value divides the negative selected root pressure datum by the chosen left or right gauge coefficient. Source: Breakdown.CellCert.CellCoordinates.MeshData.rootValue in FractionalCellSystemChallenge, line 2318. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2318).

**Gauge constant along a class path.** The class value adds the signed gauge jumps along its path to its root constant. Source: Breakdown.CellCert.CellCoordinates.MeshData.classValue in FractionalCellSystemChallenge, line 2323. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2323).

**Canonical left pressure constant.** The canonical left constant is the value of the gauge class attached to the cell's left side. Source: Breakdown.CellCert.CellCoordinates.MeshData.canonicalLeft in FractionalCellSystemChallenge, line 2328. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2328).

**Canonical right pressure constant.** The canonical right constant is the value of the gauge class attached to the cell's right side. Source: Breakdown.CellCert.CellCoordinates.MeshData.canonicalRight in FractionalCellSystemChallenge, line 2330. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2330).

**Scaled local skeleton moment.** The local value reads the canonically shifted real datum and divides by its pressure-dependent viscosity scale. Source: Breakdown.CellCert.CellCoordinates.MeshData.localValue in FractionalCellSystemChallenge, line 2332. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2332).

**Skeleton key of a global owner.** The owner key identifies the skeleton datum belonging to the owner row of a global slot. Source: Breakdown.CellCert.CellCoordinates.MeshData.ownerKey in FractionalCellSystemChallenge, line 2339. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2339).

**Skeleton key of a local row.** The row key identifies the skeleton datum represented by the selected local row. Source: Breakdown.CellCert.CellCoordinates.MeshData.rowKey in FractionalCellSystemChallenge, line 2342. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2342).

**Gauge nodes of an owner moment.** Owner nodes pair the owner's pressure positions with the corresponding gauge classes. Source: Breakdown.CellCert.CellCoordinates.MeshData.ownerNodes in FractionalCellSystemChallenge, line 2346. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2346).

**Gauge nodes of a local row.** Row nodes pair the row's pressure positions with the corresponding gauge classes. Source: Breakdown.CellCert.CellCoordinates.MeshData.rowNodes in FractionalCellSystemChallenge, line 2350. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2350).

**Gauge nodes in a row decomposition.** Participant nodes collect the gauge nodes of the target row and all owner moments in its decomposition. Source: Breakdown.CellCert.CellCoordinates.MeshData.participantNodes in FractionalCellSystemChallenge, line 2354. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2354).

**Global base moment.** A multiplier slot reads its multiplier coordinate, while every other base slot reads the scaled moment from its owner cell. Source: Breakdown.CellCert.CellCoordinates.MeshData.baseMoment in FractionalCellSystemChallenge, line 2358. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2358).

**Global slots reserved for delays.** A delay slot is a global slot selected by the delay-slot map. Source: Breakdown.CellCert.CellCoordinates.MeshData.IsDelaySlot in FractionalCellSystemChallenge, line 2361. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2361).

**Global moment after delay expansion.** The canonical moment expands delay slots into their base moments and uses the base moment directly for every other slot. Source: Breakdown.CellCert.CellCoordinates.MeshData.canonicalMoment in FractionalCellSystemChallenge, line 2364. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2364).

**Linear vector of a delay relation.** A delay vector subtracts its prescribed row coefficients from the unit vector of its delay slot and has zero pin coordinates. Source: Breakdown.CellCert.CellCoordinates.MeshData.delayVector in FractionalCellSystemChallenge, line 2369. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2369).

**Skeleton keys of additional data.** The extra-key map replaces each additional cell datum by its skeleton key while retaining its coefficient. Source: Breakdown.CellCert.CellCoordinates.MeshData.extraKeys in FractionalCellSystemChallenge, line 2372. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2372).

**Gauge nodes of additional data.** The extra-node map collects all pressure positions and gauge classes associated with the additional cell data. Source: Breakdown.CellCert.CellCoordinates.MeshData.extraNodes in FractionalCellSystemChallenge, line 2376. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2376).

**A compatible gauge-deleted key.** A deleted key has a gauge-deleted representative whose pressure classes agree with the target row wherever their radial positions coincide. Source: Breakdown.CellCert.CellCoordinates.MeshData.DeletedKey in FractionalCellSystemChallenge, line 2381. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2381).

**Source namespace:** Breakdown.CellCert.CellCoordinates.

**Conditions on the global mesh.** The mesh predicate requires valid canonical gauges, consistent shared-row decompositions, independent multiplier and delay slots, and compatible pressure paths. Source: Breakdown.CellCert.CellCoordinates.IsMeshData in FractionalCellSystemChallenge, line 2391. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2391).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Horizontal polar angle.** The angular coordinate is the complex argument of the first two spatial coordinates. Source: Breakdown.CellCert.GivenFields.angleOf in FractionalCellSystemChallenge, line 2502. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2502).

**Complementary compactified radius.** The complementary radial chart coordinate is one minus the compactified radius. Source: Breakdown.CellCert.GivenFields.chartS in FractionalCellSystemChallenge, line 2506. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2506).

**Core ratio in the radial chart.** The core ratio divides L0 squared times t squared by that term plus rc squared times the square of one minus t. Source: Breakdown.CellCert.GivenFields.coreRatioT in FractionalCellSystemChallenge, line 2508. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2508).

**Logarithmic radial phase.** The logarithmic phase is half the logarithm of one plus the squared radius divided by the squared core radius. Source: Breakdown.CellCert.GivenFields.logPhase in FractionalCellSystemChallenge, line 2511. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2511).

**Fractional radial decay factor.** The decay factor is the complementary chart coordinate raised to twice the fractional offset. Source: Breakdown.CellCert.GivenFields.decayFactor in FractionalCellSystemChallenge, line 2513. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2513).

**Euclidean vector from three values.** The coordinate constructor inserts the three real components into the standard Euclidean basis. Source: Breakdown.CellCert.GivenFields.ofComponents in FractionalCellSystemChallenge, line 2522. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2522).

**Source namespace:** Breakdown.CellCert.GivenFields.Spline.

**Spline extended by parity.** Spline evaluation uses the absolute polar coordinate and changes sign on its negative half exactly when odd parity is selected. Source: Breakdown.CellCert.GivenFields.Spline.eval in FractionalCellSystemChallenge, line 2548. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2548).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Spline joins and parity conditions.** The spline-class predicate requires the tensor mesh, specified radial and polar derivative joins, and the derivative cancellations imposed by parity. Source: Breakdown.CellCert.GivenFields.IsSplineClass in FractionalCellSystemChallenge, line 2561. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2561).

**Source namespace:** Breakdown.CellCert.GivenFields.Spline.

**Real spline coefficients.** A spline is real when every polynomial coefficient of every piece has zero imaginary part. Source: Breakdown.CellCert.GivenFields.Spline.IsReal in FractionalCellSystemChallenge, line 2572. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2572).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Four spline amplitudes of a mode.** Mode amplitudes contain radial, polar, stream and swirl splines. Source: Breakdown.CellCert.GivenFields.ModeAmp in FractionalCellSystemChallenge, line 2580. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2580).

**Source namespace:** Breakdown.CellCert.GivenFields.ModeAmp.

**Conjugate mode amplitudes.** Amplitude conjugation conjugates all four component splines. Source: Breakdown.CellCert.GivenFields.ModeAmp.conj in FractionalCellSystemChallenge, line 2586. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2586).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Finite harmonic field data.** Field data record a finite mode set, four amplitudes per mode, endpoint orders and the two origin guard constants. Source: Breakdown.CellCert.GivenFields.FieldData in FractionalCellSystemChallenge, line 2589. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2589).

**Radial derivative with phase and decay.** The twisted radial derivative adds the logarithmic-phase and fractional-decay corrections to the ordinary radial scaling derivative. Source: Breakdown.CellCert.GivenFields.twistedScale in FractionalCellSystemChallenge, line 2602. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2602).

**Reduced solenoidal field formula.** The reduced field uses stream and swirl amplitudes at mode zero and derives the nonzero-mode azimuthal component from radial and polar amplitudes. Source: Breakdown.CellCert.GivenFields.reducedField in FractionalCellSystemChallenge, line 2607. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2607).

**Angular and logarithmic mode phase.** The mode phase exponentiates the sum of angular rotation and logarithmic radial phase multiplied by the imaginary unit. Source: Breakdown.CellCert.GivenFields.modePhase in FractionalCellSystemChallenge, line 2623. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2623).

**Physical field from spline amplitudes.** The physical field takes the real part of the finite phased mode sum in the spatial frame and multiplies by the radial decay factor. Source: Breakdown.CellCert.GivenFields.fieldOf in FractionalCellSystemChallenge, line 2626. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2626).

**Admissible harmonic field data.** Admissibility requires conjugate modes, prescribed spline joins and parity, origin guards and sufficient radial and axis orders. Source: Breakdown.CellCert.GivenFields.IsFieldData in FractionalCellSystemChallenge, line 2632. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2632).

**Compactly supported field data.** Compact field data require an admissible field whose four amplitude splines vanish beyond a shared chart break below one. Source: Breakdown.CellCert.GivenFields.IsCompactFieldData in FractionalCellSystemChallenge, line 2648. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2648).

**Polynomial family of profiles.** Profile data combine chart parameters, fractional power, an affine rotation rate, parameter radii and polynomial field and multiplier coefficients. Source: Breakdown.CellCert.GivenFields.ProfileData in FractionalCellSystemChallenge, line 2682. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2682).

**Source namespace:** Breakdown.CellCert.GivenFields.ProfileData.

**Affine rotation rate.** The profile rotation rate adds the parameter-weighted rate slopes to the base rate. Source: Breakdown.CellCert.GivenFields.ProfileData.rate in FractionalCellSystemChallenge, line 2696. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2696).

**Profile phase from the rotation rate.** The profile phase is minus twice the fractional power times the symmetry order and the rotation rate. Source: Breakdown.CellCert.GivenFields.ProfileData.phase in FractionalCellSystemChallenge, line 2698. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2698).

**Parameter monomial.** A parameter monomial is the product of each coordinate raised to its multi-index exponent. Source: Breakdown.CellCert.GivenFields.ProfileData.monomialOf in FractionalCellSystemChallenge, line 2700. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2700).

**Profile evaluated at its parameters.** The profile sums its field components with parameter-monomial weights and the common parameter-dependent phase. Source: Breakdown.CellCert.GivenFields.ProfileData.profile in FractionalCellSystemChallenge, line 2702. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2702).

**Polynomial multiplier family.** The multiplier sums its coefficient vectors with the same parameter-monomial weights. Source: Breakdown.CellCert.GivenFields.ProfileData.multiplier in FractionalCellSystemChallenge, line 2705. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2705).

**Second derivative of a profile.** The profile's second derivative is the Fréchet derivative of its first derivative. Source: Breakdown.CellCert.GivenFields.ProfileData.second in FractionalCellSystemChallenge, line 2708. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2708).

**Chosen weak fractional power.** The power-field selector chooses a weak fractional power when one exists and returns the zero field otherwise. Source: Breakdown.CellCert.GivenFields.ProfileData.powerField in FractionalCellSystemChallenge, line 2712. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2712).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Conditions on the profile family.** Profile admissibility fixes the power to one plus the chart offset and requires nonnegative radii, a downward-closed index set and valid field components. Source: Breakdown.CellCert.GivenFields.IsProfileData in FractionalCellSystemChallenge, line 2717. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2717).

**Identify the profile certificate data.** A profile instance equates the certificate's fields, derivatives, power, rate, radii, symmetry order and multipliers with the constructed profile family. Source: Breakdown.CellCert.GivenFields.IsProfileInstance in FractionalCellSystemChallenge, line 2725. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2725).

**Identify the centre profile.** A centre instance identifies the centre and its second derivative with the profile at parameter zero and matches the symmetry order. Source: Breakdown.CellCert.GivenFields.IsCentreInstance in FractionalCellSystemChallenge, line 2734. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2734).

**Source namespace:** Breakdown.CellCert.Reduction.

**Horizontal Euclidean radius.** The horizontal norm is the square root of the sum of squares of the first two coordinates. Source: Breakdown.CellCert.Reduction.horizontalNorm in FractionalCellSystemChallenge, line 2764. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2764).

**Newtonian shell bound formula.** The shell formula takes the smaller mass-distance and density-shell estimates for positive separation and uses its density expression at nonpositive separation. Source: Breakdown.CellCert.Reduction.kernelShell in FractionalCellSystemChallenge, line 2766. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2766).

**Distance between interval ranges.** The gap distance is the nonnegative separation of two intervals, with absent upper endpoints contributing no finite upper restriction. Source: Breakdown.CellCert.Reduction.gapDist in FractionalCellSystemChallenge, line 2770. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2770).

**Sheet integral formula.** The sheet formula combines an inverse hyperbolic sine term with a length times square-root term, all multiplied by pi. Source: Breakdown.CellCert.Reduction.sheetArea in FractionalCellSystemChallenge, line 2773. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2773).

**Data for sums of cell kernels.** Cell-sum data specify source pieces, target boxes, mass and supremum bounds, sector rules and target-box bounds. Source: Breakdown.CellCert.Reduction.CellSumData in FractionalCellSystemChallenge, line 2775. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2775).

**Source namespace:** Breakdown.CellCert.Reduction.CellSumData.

**Distance between rotated sectors.** The sector distance combines radial separation, reflected or ordinary height separation and angular separation through the sine factor. Source: Breakdown.CellCert.Reduction.CellSumData.sectorDist in FractionalCellSystemChallenge, line 2797. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2797).

**Sum of separated sector bounds.** The sector sum adds twice the shell estimate over the selected half-range of symmetry sectors. Source: Breakdown.CellCert.Reduction.CellSumData.sectorSum in FractionalCellSystemChallenge, line 2803. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2803).

**Angular sector distance coefficient.** The sector constant combines the geometric mean of the two lower radii with the sine-over-angle factor. Source: Breakdown.CellCert.Reduction.CellSumData.sectorConst in FractionalCellSystemChallenge, line 2806. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2806).

**Near-sector kernel estimate.** The near term combines a separated-mass estimate with the difference of two sheet integrals. Source: Breakdown.CellCert.Reduction.CellSumData.nearTerm in FractionalCellSystemChallenge, line 2809. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2809).

**Chosen source-target kernel bound.** The pair term selects the full sector sum, one shell bound or a near-sector bound plus the remaining sectors according to the stored rule. Source: Breakdown.CellCert.Reduction.CellSumData.pairTerm in FractionalCellSystemChallenge, line 2816. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2816).

**Source namespace:** Breakdown.CellCert.Reduction.

**Weak negative Laplacian.** The weak negative-trace predicate equates testing the field against minus the test Laplacian with testing the proposed trace against the test field. Source: Breakdown.CellCert.Reduction.IsWeakNegTraceOf in FractionalCellSystemChallenge, line 2849. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2849).

**Weak divergence of a matrix field.** The weak matrix-divergence predicate requires the integration-by-parts identity with every compact smooth vector test. Source: Breakdown.CellCert.Reduction.IsWeakMatrixDivergenceOf in FractionalCellSystemChallenge, line 2853. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2853).

**Normalizer for a lower fractional power.** The lower-power normalizer integrates one minus cosine against the fractional radial kernel. Source: Breakdown.CellCert.Reduction.lowPowerNormalizer in FractionalCellSystemChallenge, line 2857. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2857).

**Symmetric lower fractional power.** The lower-power formula integrates one half of twice the central value minus the two opposite displaced values against the radial kernel, then divides by its normalizer. Source: Breakdown.CellCert.Reduction.lowPowerAt in FractionalCellSystemChallenge, line 2860. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2860).

**Point on a cylindrical ring.** The ring point uses radius times cosine and sine for its horizontal coordinates and the supplied height. Source: Breakdown.CellCert.Reduction.ringPoint in FractionalCellSystemChallenge, line 2863. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2863).

**Horizontal vector as a complex scalar.** The horizontal component combines the first coordinate with the imaginary unit times the second. Source: Breakdown.CellCert.Reduction.horizontalPart in FractionalCellSystemChallenge, line 2866. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2866).

**Vertical vector as a complex scalar.** The vertical component embeds the third real coordinate into the complex numbers. Source: Breakdown.CellCert.Reduction.verticalPart in FractionalCellSystemChallenge, line 2868. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2868).

**Angular scalar Fourier mode.** The angular mode is the normalized Fourier integral over the interval from minus pi to pi. Source: Breakdown.CellCert.Reduction.angularMode in FractionalCellSystemChallenge, line 2870. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2870).

**Weighted harmonic inverse-square size.** The harmonic size sums weighted horizontal and vertical mode squares with denominators shifted by one half and three halves respectively. Source: Breakdown.CellCert.Reduction.harmonicWeightSqOn in FractionalCellSystemChallenge, line 2873. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2873).

**Adjoint similarity drift.** The adjoint drift combines the zeroth-order similarity coefficient, negative radial differentiation and negative rotation commutator. Source: Breakdown.CellCert.Reduction.driftAdjointField in FractionalCellSystemChallenge, line 2879. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2879).

**Adjoint convection field.** The adjoint convection field combines minus the cross product of the adjoint curl with the velocity and twice the adjoint velocity-gradient action. Source: Breakdown.CellCert.Reduction.convectionAdjointField in FractionalCellSystemChallenge, line 2882. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2882).

**Adjoint dual decomposition data.** Adjoint-dual data collect derivatives, pin potentials, pressure, dual and flux decompositions, harmonic support and their norm bounds. Source: Breakdown.CellCert.Reduction.AdjointDual in FractionalCellSystemChallenge, line 2886. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2886).

**Source namespace:** Breakdown.CellCert.Reduction.AdjointDual.

**Scaled pin dual field.** The pin dual divides the pin trace by its selected positive-scale candidate. Source: Breakdown.CellCert.Reduction.AdjointDual.pinDual in FractionalCellSystemChallenge, line 2922. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2922).

**Adjoint residual field.** The adjoint residual adds drift, sharp trace and convection, subtracts the pin-dual combination and adds the pressure gradient. Source: Breakdown.CellCert.Reduction.AdjointDual.residualField in FractionalCellSystemChallenge, line 2924. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2924).

**Remainder after the dual decomposition.** The remainder removes the dual trace, scaled potential trace and flux divergence from the adjoint residual. Source: Breakdown.CellCert.Reduction.AdjointDual.remainderField in FractionalCellSystemChallenge, line 2929. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2929).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Finite parameter power product.** The multi-power function multiplies the parameter coordinates raised to their multi-index exponents. Source: Breakdown.CellCert.GivenFields.multiPow in FractionalCellSystemChallenge, line 2959. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2959).

**Polynomial family of field data.** A field family records a finite multi-index set and one harmonic field datum for each index. Source: Breakdown.CellCert.GivenFields.FieldFamily in FractionalCellSystemChallenge, line 2961. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2961).

**Source namespace:** Breakdown.CellCert.GivenFields.FieldFamily.

**Evaluate a polynomial field family.** Field-family evaluation sums the phase-adjusted physical fields with parameter-monomial weights. Source: Breakdown.CellCert.GivenFields.FieldFamily.eval in FractionalCellSystemChallenge, line 2965. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2965).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Downward closure of multi-indices.** A finite multi-index set is downward closed when it contains every coordinatewise smaller index of each member. Source: Breakdown.CellCert.GivenFields.IsDownClosed in FractionalCellSystemChallenge, line 2969. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2969).

**Two-part pressure amplitude data.** Pressure data record mode splines, radial orders and axis orders for the two decay components. Source: Breakdown.CellCert.GivenFields.PressureData in FractionalCellSystemChallenge, line 2972. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2972).

**Weighted pressure spline shape.** The pressure shape multiplies its even spline by the prescribed radial, complementary radial and axis powers. Source: Breakdown.CellCert.GivenFields.pressureShape in FractionalCellSystemChallenge, line 2982. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2982).

**Physical pressure from its amplitudes.** The pressure is the real finite mode sum of its two spline shapes with one and two powers of the decay factor. Source: Breakdown.CellCert.GivenFields.pressureOf in FractionalCellSystemChallenge, line 2985. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2985).

**Admissible pressure amplitudes.** Pressure admissibility requires conjugation-compatible continuous splines, sufficient decay orders and matching axis orders. Source: Breakdown.CellCert.GivenFields.IsPressureData in FractionalCellSystemChallenge, line 2989. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2989).

**Helical atom amplitude data.** Atom data record a finite harmonic set and plus, minus and height spline amplitudes. Source: Breakdown.CellCert.GivenFields.AtomData in FractionalCellSystemChallenge, line 2998. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2998).

**Last radial spline cell.** The last radial index is the radial cell count minus one in natural-number arithmetic. Source: Breakdown.CellCert.GivenFields.atomLastT in FractionalCellSystemChallenge, line 3004. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3004).

**Last polar spline cell.** The last polar index is the polar cell count minus one in natural-number arithmetic. Source: Breakdown.CellCert.GivenFields.atomLastX in FractionalCellSystemChallenge, line 3006. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3006).

**Endpoint conditions for an atom.** An atom spline has the stated joins and parity, vanishes at the origin, has two vanishing radial endpoint traces at infinity and satisfies its axis condition. Source: Breakdown.CellCert.GivenFields.IsAtomSpline in FractionalCellSystemChallenge, line 3008. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3008).

**One phased helical atom.** An atom term multiplies the angular and logarithmic phase by an axis factor and the parity-selected spline value. Source: Breakdown.CellCert.GivenFields.atomTerm in FractionalCellSystemChallenge, line 3015. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3015).

**Horizontal component of an atom.** The horizontal atom sums the plus harmonics and conjugated positive minus harmonics with the radial decay factor. Source: Breakdown.CellCert.GivenFields.atomPlane in FractionalCellSystemChallenge, line 3019. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3019).

**Vertical component of an atom.** The vertical atom sum weights mode zero once and positive harmonics twice before applying the radial decay factor. Source: Breakdown.CellCert.GivenFields.atomHeight in FractionalCellSystemChallenge, line 3025. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3025).

**Real vector assembled from an atom.** The atom vector uses the real and imaginary horizontal components and the real vertical component. Source: Breakdown.CellCert.GivenFields.atomOf in FractionalCellSystemChallenge, line 3029. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3029).

**Admissible atom amplitudes.** Atom admissibility requires valid plus, minus and height splines and a real zero-height mode. Source: Breakdown.CellCert.GivenFields.IsAtomData in FractionalCellSystemChallenge, line 3032. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3032).

**Continuity across radial spline joins.** Radial continuity requires a valid tensor mesh and matching polynomial values across every internal radial join. Source: Breakdown.CellCert.GivenFields.IsRadialContinuous in FractionalCellSystemChallenge, line 3038. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3038).

**Flux spline endpoint conditions.** A flux spline has matching radial joins and vanishing value and first radial derivative at the infinity endpoint. Source: Breakdown.CellCert.GivenFields.IsFluxSpline in FractionalCellSystemChallenge, line 3043. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3043).

**Flux amplitudes use atom data.** The flux-data type reuses the atom-amplitude record. Source: Breakdown.CellCert.GivenFields.FluxData in FractionalCellSystemChallenge, line 3048. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3048).

**Radial rank-one flux field.** The flux map sends a vector's radial component into the atom vector through a rank-one linear map. Source: Breakdown.CellCert.GivenFields.fluxOf in FractionalCellSystemChallenge, line 3050. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3050).

**Admissible flux amplitudes.** Flux admissibility requires the flux endpoint conditions for all component splines and a real zero-height amplitude. Source: Breakdown.CellCert.GivenFields.IsFluxData in FractionalCellSystemChallenge, line 3053. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3053).

**Polynomial family of atoms.** An atom family records a finite parameter multi-index set and one atom datum for each index. Source: Breakdown.CellCert.GivenFields.AtomFamily in FractionalCellSystemChallenge, line 3059. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3059).

**Source namespace:** Breakdown.CellCert.GivenFields.AtomFamily.

**Evaluate a polynomial atom family.** Atom-family evaluation sums the physical atoms with parameter-monomial weights and the supplied phase function. Source: Breakdown.CellCert.GivenFields.AtomFamily.eval in FractionalCellSystemChallenge, line 3063. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3063).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Auxiliary certificate field data.** Auxiliary data collect actuators, pin potentials, adjoint families, sharp terms, pressures, dual potentials and flux amplitudes. Source: Breakdown.CellCert.GivenFields.AuxData in FractionalCellSystemChallenge, line 3067. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3067).

**Source namespace:** Breakdown.CellCert.GivenFields.AuxData.

**Affine auxiliary phase.** The auxiliary phase adds the parameter-weighted slopes to its base phase. Source: Breakdown.CellCert.GivenFields.AuxData.phase in FractionalCellSystemChallenge, line 3086. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3086).

**Constructed actuator field.** An actuator field evaluates its harmonic field data at the base phase. Source: Breakdown.CellCert.GivenFields.AuxData.actuatorField in FractionalCellSystemChallenge, line 3088. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3088).

**Constructed pin potential.** A pin potential evaluates its harmonic field data at the base phase. Source: Breakdown.CellCert.GivenFields.AuxData.pinPotentialField in FractionalCellSystemChallenge, line 3090. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3090).

**Scaled gradient pin field.** The smooth pin field divides the derivative of the pin potential by its pin scale. Source: Breakdown.CellCert.GivenFields.AuxData.smoothPinField in FractionalCellSystemChallenge, line 3092. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3092).

**Constructed adjoint field.** The adjoint field evaluates its polynomial field family with the auxiliary phase. Source: Breakdown.CellCert.GivenFields.AuxData.adjointField in FractionalCellSystemChallenge, line 3095. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3095).

**Sharp adjoint correction.** The sharp field subtracts the sharp atom family and viscosity-scaled adjoint from the leading adjoint term. Source: Breakdown.CellCert.GivenFields.AuxData.sharpField in FractionalCellSystemChallenge, line 3098. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3098).

**Constructed dual field.** The dual field evaluates the selected dual atom family with the auxiliary phase. Source: Breakdown.CellCert.GivenFields.AuxData.dualFieldOf in FractionalCellSystemChallenge, line 3101. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3101).

**Constructed potential field.** The potential field evaluates the selected potential atom family with the auxiliary phase. Source: Breakdown.CellCert.GivenFields.AuxData.potentialFieldOf in FractionalCellSystemChallenge, line 3104. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3104).

**Constructed polynomial flux field.** The flux field sums the flux matrices over the adjoint-family multi-indices with parameter-monomial weights. Source: Breakdown.CellCert.GivenFields.AuxData.fluxFieldOf in FractionalCellSystemChallenge, line 3107. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3107).

**Constructed adjoint pressure.** The adjoint pressure sums its pressure shapes over the adjoint-family multi-indices with parameter-monomial weights. Source: Breakdown.CellCert.GivenFields.AuxData.adjointPressureField in FractionalCellSystemChallenge, line 3110. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3110).

**Source namespace:** Breakdown.CellCert.GivenFields.

**Conditions on auxiliary field data.** Auxiliary admissibility requires compact actuator and pin supports, positive pin scales, suitable adjoint decay and valid sharp, pressure, dual and flux shapes. Source: Breakdown.CellCert.GivenFields.IsAuxData in FractionalCellSystemChallenge, line 3115. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3115).

**Identify auxiliary certificate fields.** An auxiliary instance equates the certificate's actuator, pin, adjoint and sharp fields with their constructed counterparts and matches the profile phase slopes. Source: Breakdown.CellCert.GivenFields.IsAuxInstance in FractionalCellSystemChallenge, line 3132. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3132).

**Linear parameter amplitude field.** The amplitude field evaluates the profile component with the selected unit multi-index at the parameter-dependent phase. Source: Breakdown.CellCert.GivenFields.amplitudeFieldAt in FractionalCellSystemChallenge, line 3141. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3141).

**Inverse-square adjoint remainder.** The inverse-square remainder subtracts the non-exact parameter convection shifts from the adjoint-dual remainder. Source: Breakdown.CellCert.GivenFields.inverseSquarePartOf in FractionalCellSystemChallenge, line 3144. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3144).

**Source namespace:** Breakdown.CellCert.Spectral.

**Finite even derivative series.** The even series sums the even derivatives of a polynomial with reciprocal powers of the spectral parameter. Source: Breakdown.CellCert.Spectral.evenSeries in FractionalCellSystemChallenge, line 3175. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3175).

**Smoothed interval polynomial.** Interval smoothing combines the polynomial's even-derivative series with hyperbolic cosine and sine corrections determined by its endpoint values. Source: Breakdown.CellCert.Spectral.intervalSmoothed in FractionalCellSystemChallenge, line 3178. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3178).

**Polynomial interval certificate.** An interval certificate requires a positive spectral parameter and a quadratic smoothing bound for every polynomial through the prescribed degree. Source: Breakdown.CellCert.Spectral.IntervalCertificate in FractionalCellSystemChallenge, line 3185. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3185).

**Weighted axis cutoff functional.** The axis functional integrates cutoff error, radial derivative energy and angular energy with the cylindrical radial weight. Source: Breakdown.CellCert.Spectral.axisFunctional in FractionalCellSystemChallenge, line 3189. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3189).

**Polynomial axis certificate.** An axis certificate requires a Lipschitz cutoff vanishing at one and bounds the axis functional for modes zero and one, with divisibility at mode one. Source: Breakdown.CellCert.Spectral.AxisCertificate in FractionalCellSystemChallenge, line 3193. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3193).

**Axis polynomial gradient bound.** The axis-gradient proposition bounds radial and angular polynomial energy for modes zero and one, requiring a factor of the variable in mode one. Source: Breakdown.CellCert.Spectral.AxisGradientBound in FractionalCellSystemChallenge, line 3198. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3198).

**Best available spectral bound.** The certificate minimum takes the infimum of one and the stored bounds whose spectral parameters are no larger than the requested parameter. Source: Breakdown.CellCert.Spectral.certMin in FractionalCellSystemChallenge, line 3203. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3203).

**Explicit interval spectral bound.** The closed interval estimate adds the degree-squared inverse-square-root term and the degree-fourth reciprocal-parameter term with their stated constants. Source: Breakdown.CellCert.Spectral.intervalClosed in FractionalCellSystemChallenge, line 3206. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3206).

**Explicit axis spectral bound.** The closed axis estimate combines its degree-squared inverse-square-root term with twice the axis-gradient constant divided by the parameter. Source: Breakdown.CellCert.Spectral.axisClosed in FractionalCellSystemChallenge, line 3209. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3209).

**Geometry of one spectral block.** A spectral block records the radial and height bounds, polynomial degree, angular mode and whether the cell meets the axis. Source: Breakdown.CellCert.Spectral.CellBlock in FractionalCellSystemChallenge, line 3212. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3212).

**Spectral certificate tables.** Spectral data contain block geometry, interval and axis certificate sets, axis cutoffs and axis-gradient bounds. Source: Breakdown.CellCert.Spectral.SpectralData in FractionalCellSystemChallenge, line 3221. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3221).

**Source namespace:** Breakdown.CellCert.Spectral.SpectralData.

**Interval estimate from two bounds.** The interval upper bound takes the minimum of the stored-certificate bound and the explicit interval formula. Source: Breakdown.CellCert.Spectral.SpectralData.intervalUpper in FractionalCellSystemChallenge, line 3232. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3232).

**Axis estimate above the cutoff.** The axis upper bound compares the stored-certificate bound with the explicit axis formula when the parameter is at least twenty-four and with one otherwise. Source: Breakdown.CellCert.Spectral.SpectralData.axisUpper in FractionalCellSystemChallenge, line 3234. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3234).

**Spectral bound for a cell block.** The block spectral estimate combines scaled radial and height bounds, adds the angular ratio off the axis and caps the result at one. Source: Breakdown.CellCert.Spectral.SpectralData.blockSpectral in FractionalCellSystemChallenge, line 3237. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3237).

**Spectral tail bound for a block.** The tail formula combines the block's side lengths, polynomial degree, mode and axis-gradient constant with the cutoff's inverse square root. Source: Breakdown.CellCert.Spectral.SpectralData.tailFormula in FractionalCellSystemChallenge, line 3250. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3250).

**Source namespace:** Breakdown.CellCert.Spectral.

**Cylindrical radial coordinate.** The radial coordinate is the Euclidean norm of the horizontal coordinate pair. Source: Breakdown.CellCert.Spectral.radialCoord in FractionalCellSystemChallenge, line 3269. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3269).

**Upper or reflected cell solid.** A cell solid requires the radial interval and either the original or reflected height interval according to the side index. Source: Breakdown.CellCert.Spectral.cellSolid in FractionalCellSystemChallenge, line 3271. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3271).

**Source namespace:** Breakdown.CellCert.GivenModel.

**Finite physical cell mesh.** The cell mesh records finitely many cylindrical boxes and an outer size. Source: Breakdown.CellCert.GivenModel.CellMesh in FractionalCellSystemChallenge, line 3298. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3298).

**Source namespace:** Breakdown.CellCert.GivenModel.CellMesh.

**Region covered by mesh cells.** The mesh region is the union of the solid regions of all its boxes. Source: Breakdown.CellCert.GivenModel.CellMesh.region in FractionalCellSystemChallenge, line 3307. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3307).

**Disjoint piece owned by a cell.** A cell's owned piece removes the solids of all earlier-indexed boxes from its own solid. Source: Breakdown.CellCert.GivenModel.CellMesh.piece in FractionalCellSystemChallenge, line 3309. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3309).

**Field assembled over owned pieces.** Piecewise assembly sums each field restricted to its cell's owned piece and hence gives zero outside the mesh region. Source: Breakdown.CellCert.GivenModel.CellMesh.piecewise in FractionalCellSystemChallenge, line 3312. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3312).

**Source namespace:** Breakdown.CellCert.GivenModel.

**Validity of the cell mesh.** A valid mesh has positive outer size, valid boxes inside it, disjoint interiors and complete coverage of the positive radius-height square. Source: Breakdown.CellCert.GivenModel.IsCellMesh in FractionalCellSystemChallenge, line 3317. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3317).

**Bivariate cell polynomial data.** A cell polynomial is a finite square array of complex coefficients through the chosen degree in each variable. Source: Breakdown.CellCert.GivenModel.CellPoly in FractionalCellSystemChallenge, line 3327. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3327).

**Evaluate a cell polynomial.** Polynomial evaluation sums each coefficient times its radial and height monomials. Source: Breakdown.CellCert.GivenModel.evalPoly in FractionalCellSystemChallenge, line 3329. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3329).

**Real harmonic polynomial field.** Harmonic evaluation takes the real part of the angular polynomial sum, with weight one at mode zero and two at positive modes. Source: Breakdown.CellCert.GivenModel.harmonicValue in FractionalCellSystemChallenge, line 3332. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3332).

**Reflection sign for a vector.** Reflection changes the sign of the vertical vector component below the symmetry plane and preserves the other components. Source: Breakdown.CellCert.GivenModel.vectorSign in FractionalCellSystemChallenge, line 3336. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3336).

**Reflection sign for a pseudovector.** Below the symmetry plane the pseudovector sign is the negative of the vector sign, and above it every component has sign one. Source: Breakdown.CellCert.GivenModel.pseudoSign in FractionalCellSystemChallenge, line 3338. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3338).

**Vector field from harmonic polynomials.** The vector reconstruction applies the vector reflection signs to the harmonic components and converts from the cylindrical frame. Source: Breakdown.CellCert.GivenModel.vectorOf in FractionalCellSystemChallenge, line 3340. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3340).

**Pseudovector from harmonic polynomials.** The pseudovector reconstruction uses the pseudovector reflection signs before converting from the cylindrical frame. Source: Breakdown.CellCert.GivenModel.pseudoOf in FractionalCellSystemChallenge, line 3343. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3343).

**Tensor from harmonic polynomials.** The tensor reconstruction applies one vector reflection sign to each matrix index before converting to a Cartesian linear map. Source: Breakdown.CellCert.GivenModel.tensorOf in FractionalCellSystemChallenge, line 3346. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3346).

**Pseudotensor from harmonic polynomials.** The pseudotensor reconstruction uses a pseudovector sign on its output index and a vector sign on its input index. Source: Breakdown.CellCert.GivenModel.pseudoTensorOf in FractionalCellSystemChallenge, line 3349. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3349).

**Polynomial model field data.** Model data record cellwise harmonic polynomials for velocity, curl, strain, curl gradient, actuator and pin fields. Source: Breakdown.CellCert.GivenModel.ModelData in FractionalCellSystemChallenge, line 3353. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3353).

**Algebraic conditions on the model.** Model admissibility requires symmetric strain, trace-free curl gradient and vanishing model coefficients above each cell's declared harmonic count. Source: Breakdown.CellCert.GivenModel.IsModelData in FractionalCellSystemChallenge, line 3367. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3367).

**Source namespace:** Breakdown.CellCert.GivenModel.ModelData.

**Piecewise model velocity.** The model velocity assembles the vector polynomial fields over the mesh's owned pieces. Source: Breakdown.CellCert.GivenModel.ModelData.velocityField in FractionalCellSystemChallenge, line 3379. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3379).

**Piecewise model curl.** The model curl assembles the pseudovector polynomial fields over the mesh's owned pieces. Source: Breakdown.CellCert.GivenModel.ModelData.curlField in FractionalCellSystemChallenge, line 3381. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3381).

**Model strain with exterior centre.** The model strain uses the polynomial tensor inside the mesh and the centre's symmetric gradient outside the mesh region. Source: Breakdown.CellCert.GivenModel.ModelData.strainField in FractionalCellSystemChallenge, line 3383. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3383).

**Curl gradient with exterior centre.** The model curl gradient uses the polynomial pseudotensor inside the mesh and the centre's curl gradient outside it. Source: Breakdown.CellCert.GivenModel.ModelData.curlGradField in FractionalCellSystemChallenge, line 3386. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3386).

**Piecewise model actuator.** Each model actuator assembles its vector polynomials over the owned cell pieces. Source: Breakdown.CellCert.GivenModel.ModelData.actuatorField in FractionalCellSystemChallenge, line 3390. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3390).

**Piecewise model actuator gradient.** Each model actuator gradient assembles its tensor polynomials over the owned cell pieces. Source: Breakdown.CellCert.GivenModel.ModelData.actuatorGradField in FractionalCellSystemChallenge, line 3392. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3392).

**Piecewise model pin field.** The model pin field assembles the pin-field tensor polynomials over the owned cell pieces. Source: Breakdown.CellCert.GivenModel.ModelData.pinFieldField in FractionalCellSystemChallenge, line 3395. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3395).

**Piecewise pin pairing field.** The pin pairing field assembles the separate pin-value tensor polynomials over the owned cell pieces. Source: Breakdown.CellCert.GivenModel.ModelData.pinValueField in FractionalCellSystemChallenge, line 3397. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3397).

**Source namespace:** Breakdown.CellCert.GivenModel.

**Identify the polynomial model fields.** A model instance equates the certificate's region and all its model and pin fields with the supplied polynomial reconstructions. Source: Breakdown.CellCert.GivenModel.IsModelInstance in FractionalCellSystemChallenge, line 3401. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3401).

**Radial derivative of a polynomial.** The radial polynomial derivative multiplies each coefficient by its radial degree and reduces that exponent by one. Source: Breakdown.CellCert.GivenModel.polyDr in FractionalCellSystemChallenge, line 3418. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3418).

**Height derivative of a polynomial.** The height polynomial derivative multiplies each coefficient by its height degree and reduces that exponent by one. Source: Breakdown.CellCert.GivenModel.polyDz in FractionalCellSystemChallenge, line 3421. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3421).

**Solenoidal polynomial mode.** The solenoidal-profile predicate is the cylindrical divergence identity with radial, angular-frequency and height terms. Source: Breakdown.CellCert.GivenModel.IsSolenoidalProfile in FractionalCellSystemChallenge, line 3424. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3424).

**Cellwise row test data.** Row data record each row's cell, harmonic and polynomial profile together with cell weights and conjugate-pair information. Source: Breakdown.CellCert.GivenModel.RowData in FractionalCellSystemChallenge, line 3428. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3428).

**Source namespace:** Breakdown.CellCert.GivenModel.RowData.

**Row test field on one cell.** A row test field is the real phased polynomial vector supported on its selected cell solid with the appropriate reflection signs. Source: Breakdown.CellCert.GivenModel.RowData.testField in FractionalCellSystemChallenge, line 3441. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3441).

**Zero and nonzero mode pairing.** The pairing density uses the product of real parts at mode zero and half the real Hermitian pairing otherwise. Source: Breakdown.CellCert.GivenModel.RowData.modePairDensity in FractionalCellSystemChallenge, line 3447. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3447).

**Gram matrix of the row tests.** The test-pairing matrix integrates rows in the same cell and harmonic with the four-pi cylindrical factor and is zero for other pairs. Source: Breakdown.CellCert.GivenModel.RowData.testPairing in FractionalCellSystemChallenge, line 3451. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3451).

**Inverse-square-root row mixing.** The row-mixing matrix uses Hermitian functional calculus with the inverse-square-root function and is zero when Hermitianity is unavailable. Source: Breakdown.CellCert.GivenModel.RowData.mix in FractionalCellSystemChallenge, line 3459. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3459).

**Mixed row field.** A row field is the finite linear combination of test fields given by the row-mixing matrix. Source: Breakdown.CellCert.GivenModel.RowData.rowField in FractionalCellSystemChallenge, line 3462. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3462).

**Weight of a row's cell.** The row weight is the weight attached to the row's selected cell. Source: Breakdown.CellCert.GivenModel.RowData.rowWeightOf in FractionalCellSystemChallenge, line 3464. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3464).

**Source namespace:** Breakdown.CellCert.GivenModel.

**Conditions on row test data.** Valid row data require a positive Gram matrix, solenoidal profiles, bounded positive weights, axis regularity and compatible harmonic partners. Source: Breakdown.CellCert.GivenModel.IsRowData in FractionalCellSystemChallenge, line 3468. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3468).

**Piecewise cell weight.** The cell-weight field assigns each owned cell piece its supplied constant weight. Source: Breakdown.CellCert.GivenModel.cellWeightField in FractionalCellSystemChallenge, line 3484. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3484).

**Identify row fields and weights.** A row instance equates the certificate's row fields, row weights, cell weight and cell region with the constructed mesh data. Source: Breakdown.CellCert.GivenModel.IsRowInstance in FractionalCellSystemChallenge, line 3486. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3486).

**Radial boundary of an outer box.** The box radius rescales the outer size by Euclidean radius over the larger cylindrical coordinate and equals the outer size at the origin. Source: Breakdown.CellCert.GivenModel.boxRadius in FractionalCellSystemChallenge, line 3492. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3492).

**Rows belonging to a chosen cell.** A rows instance identifies the physical row family and selects exactly the rows belonging to the chosen mesh cell, with both harmonic signs covered. Source: Breakdown.CellCert.GivenModel.IsRowsInstance in FractionalCellSystemChallenge, line 3501. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3501).

**Spectral block attached to a row.** A row block copies its cell geometry, row degree and symmetry-scaled harmonic and records whether the inner radius is zero. Source: Breakdown.CellCert.GivenModel.rowBlock in FractionalCellSystemChallenge, line 3509. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3509).

**Source namespace:** Breakdown.CellCert.GivenFields.

**All supplied field identifications.** The given-data predicate joins valid profile, auxiliary, mesh, model and row data with each required identification to the certificate. Source: Breakdown.CellCert.GivenFields.IsGivenData in FractionalCellSystemChallenge, line 3539. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3539).

**Source namespace:** Breakdown.CellCert.Reduction.

**Weighted polynomial pairing.** The polynomial pairing integrates the product of two real polynomials against the supplied weight on the closed interval. Source: Breakdown.CellCert.Reduction.polyPair in FractionalCellSystemChallenge, line 3575. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3575).

**Recursive polynomial normalization.** The recursive polynomial family subtracts earlier weighted projections from each monomial and divides by the square root of its squared norm. Source: Breakdown.CellCert.Reduction.orthoFamily in FractionalCellSystemChallenge, line 3578. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3578).

**Canonical radial and height bases.** The canonical bases take coefficients from the weighted radial and unweighted height orthonormal polynomial constructions. Source: Breakdown.CellCert.Reduction.canonicalBases in FractionalCellSystemChallenge, line 3586. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3586).

**Extend the supplied polynomial bases.** Basis extension preserves supplied coefficients through the chosen degree and uses the canonical polynomial family above it. Source: Breakdown.CellCert.Reduction.extendBases in FractionalCellSystemChallenge, line 3591. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3591).

**Conditions on supplied basis terms.** Given bases require positive leading coefficients and weighted radial and unweighted height orthonormality through the specified cutoff. Source: Breakdown.CellCert.Reduction.IsGivenBases in FractionalCellSystemChallenge, line 3595. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3595).

**First nonzero angular weight.** The angular constant is the cell's angular weight evaluated at mode one. Source: Breakdown.CellCert.Reduction.angularConst in FractionalCellSystemChallenge, line 3603. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3603).

**Finite mode-weight parameters.** Weight data record resolved and band cutoffs, energy and vorticity coefficients, absorption parameters and geometric bounds. Source: Breakdown.CellCert.Reduction.WeightData in FractionalCellSystemChallenge, line 3605. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3605).

**Source namespace:** Breakdown.CellCert.Reduction.WeightData.

**Effective frequency beyond the band.** The effective frequency uses the actual frequency through the selected cutoffs and a fixed band-edge frequency above them. Source: Breakdown.CellCert.Reduction.WeightData.kEff in FractionalCellSystemChallenge, line 3630. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3630).

**Strain absorption as a frequency bound.** The strain bound adds constant losses and inverse powers of the frequency minus one, with different penalty contributions inside and outside the band. Source: Breakdown.CellCert.Reduction.WeightData.strainAt in FractionalCellSystemChallenge, line 3633. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3633).

**Symmetric tail weight formula.** The symmetric weight subtracts the strain bound from the energy coefficient times the radial, height and shifted angular spectral terms. Source: Breakdown.CellCert.Reduction.WeightData.symAt in FractionalCellSystemChallenge, line 3638. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3638).

**Antisymmetric tail weight formula.** The antisymmetric weight uses energy plus twice vorticity, then subtracts the curl absorption and strain bound. Source: Breakdown.CellCert.Reduction.WeightData.antiAt in FractionalCellSystemChallenge, line 3642. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3642).

**Source namespace:** Breakdown.CellCert.Reduction.

**Identify all scalar weight formulas.** The weight-form predicate identifies resolved and band sets and the energy, vorticity, absorption and tail formulas for every mode. Source: Breakdown.CellCert.Reduction.IsWeightForm in FractionalCellSystemChallenge, line 3648. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3648).

**Finite tests for positive weights.** The weight tests require coefficient signs, geometric bounds and the resolved, band, exterior and velocity floor inequalities. Source: Breakdown.CellCert.Reduction.IsWeightTests in FractionalCellSystemChallenge, line 3667. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3667).

**Scalar matrix on strain coordinates.** The strain scalar matrix places the supplied scalar on its first nine diagonal entries and zero on the velocity entries. Source: Breakdown.CellCert.Reduction.strainScalarMatrix in FractionalCellSystemChallenge, line 3705. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3705).

**Tests on the resolved local matrix.** Resolved tests fix the local matrix to the strain scalar form and require the stated curl, strain and velocity absorption bounds. Source: Breakdown.CellCert.Reduction.IsResolvedTests in FractionalCellSystemChallenge, line 3708. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3708).

**Floor tests beyond the near cutoff.** The far-floor predicate requires the listed radial, height and angular lower bounds for strain and velocity beyond the near cutoff. Source: Breakdown.CellCert.Reduction.IsFarFloorTests in FractionalCellSystemChallenge, line 3742. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3742).

**Bounds for each tail column.** The tail-column predicate requires measurable multiplier sections and bounds their weighted radial and height projection tails by squared column majorants. Source: Breakdown.CellCert.Reduction.IsTailColumnBound in FractionalCellSystemChallenge, line 3761. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3761).

**Source namespace:** Breakdown.CellCert.CellSystem.

**Numbers controlling row rotation.** The row-turn predicate requires symmetry order at least two and bounds the weighted outer-radius square of every nonzero harmonic row. Source: Breakdown.CellCert.CellSystem.IsRowTurnNumbers in FractionalCellSystemChallenge, line 3804. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3804).

**Geometric and numerical cell sums.** Cell-sum values record source pieces in cylindrical or compactified charts, their mass and supremum bounds, and target-box bounds. Source: Breakdown.CellCert.CellSystem.CellSumValues in FractionalCellSystemChallenge, line 3809. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3809).

**Cylindrical piece with optional bounds.** A piece solid imposes lower radial and height bounds and imposes an upper bound only when one is supplied. Source: Breakdown.CellCert.CellSystem.pieceSolidOf in FractionalCellSystemChallenge, line 3826. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3826).

**Solid in a compactified chart.** A chart solid restricts the compactified radius and the height-to-radius ratio to the supplied intervals. Source: Breakdown.CellCert.CellSystem.chartSolid in FractionalCellSystemChallenge, line 3829. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3829).

**Source namespace:** Breakdown.CellCert.CellSystem.CellSumValues.

**Select a source-piece geometry.** A source piece uses its compactified chart when present and otherwise uses its cylindrical bounds. Source: Breakdown.CellCert.CellSystem.CellSumValues.pieceSolid in FractionalCellSystemChallenge, line 3836. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3836).

**Base cell-sum data.** Base cell-sum data copy the supplied geometry and numerical bounds and initially select the pure sector-sum rule with zero near length. Source: Breakdown.CellCert.CellSystem.CellSumValues.baseData in FractionalCellSystemChallenge, line 3841. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3841).

**Six near-sector trial factors.** The near-factor list is one, one half, one quarter, three twenty-fifths, three fiftieths and three hundredths. Source: Breakdown.CellCert.CellSystem.CellSumValues.nearFactors in FractionalCellSystemChallenge, line 3859. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3859).

**Trial near-sector length.** A trial near length multiplies the sector constant by the selected fraction of the symmetry angle. Source: Breakdown.CellCert.CellSystem.CellSumValues.nearLength in FractionalCellSystemChallenge, line 3861. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3861).

**Admissibility of a near-sector length.** A near length is admissible when it and the sector constant are positive and both source-piece upper bounds are present. Source: Breakdown.CellCert.CellSystem.CellSumValues.NearValid in FractionalCellSystemChallenge, line 3864. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3864).

**Near estimate with a selected length.** The near value adds the near-sector estimate at the chosen length to the remaining separated-sector sum. Source: Breakdown.CellCert.CellSystem.CellSumValues.nearValue in FractionalCellSystemChallenge, line 3867. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3867).

**Choose the best valid near length.** The best-near search accepts the first valid trial length and replaces it only when a later valid length gives a strictly smaller estimate. Source: Breakdown.CellCert.CellSystem.CellSumValues.bestNear in FractionalCellSystemChallenge, line 3872. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3872).

**Choose a kernel estimate rule.** The rule selector chooses the smallest available near, shell or sector estimate, giving ties to near first and shell before sector. Source: Breakdown.CellCert.CellSystem.CellSumValues.ruleOf in FractionalCellSystemChallenge, line 3882. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3882).

**Selected near length or zero.** The selected length reads the best valid near length and returns zero when no such candidate exists. Source: Breakdown.CellCert.CellSystem.CellSumValues.lengthOf in FractionalCellSystemChallenge, line 3889. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3889).

**Cell sums with selected rules.** The final cell-sum data replace the base rule and near length by the automatically selected values. Source: Breakdown.CellCert.CellSystem.CellSumValues.toData in FractionalCellSystemChallenge, line 3892. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3892).

**Source namespace:** Breakdown.CellCert.CellSystem.

**Conditions on cell-sum geometry.** Cell-sum validity requires even symmetry order at least four, admissible source geometry and coverage of the upper half-space and target quadrant. Source: Breakdown.CellCert.CellSystem.IsCellSumValues in FractionalCellSystemChallenge, line 3897. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3897).

**Bounds carried by cell-sum values.** The boundedness predicate requires source supremum and mass bounds and the complete reflected pair sum below each target-box bound. Source: Breakdown.CellCert.CellSystem.IsCellSumBounded in FractionalCellSystemChallenge, line 3911. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3911).

**Numerical bounds for the adjoint dual.** Adjoint-dual numbers require the pin scales and the stated dual, potential, flux, inverse-square and parameter-shift norm bounds. Source: Breakdown.CellCert.CellSystem.IsAdjointDualNumbers in FractionalCellSystemChallenge, line 3916. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3916).

**Derivative with respect to phase.** The phase derivative differentiates the constructed field with respect to its phase parameter. Source: Breakdown.CellCert.CellSystem.phaseDerivField in FractionalCellSystemChallenge, line 3929. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3929).

**Second derivative with respect to phase.** The phase curvature differentiates the phase derivative once more with respect to the phase. Source: Breakdown.CellCert.CellSystem.phaseCurvField in FractionalCellSystemChallenge, line 3932. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3932).

**Linear amplitude and phase correction.** The amplitude correction adds the selected first-order parameter field to the parameter step times the base-field phase derivative. Source: Breakdown.CellCert.CellSystem.ampField in FractionalCellSystemChallenge, line 3935. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3935).

**Squared gradient operator norm.** The gradient square is the squared operator norm of the field's Fréchet derivative. Source: Breakdown.CellCert.CellSystem.gradSq in FractionalCellSystemChallenge, line 3938. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3938).

**Total width of a phase variation.** The split width sums the absolute phase steps times their parameter radii. Source: Breakdown.CellCert.CellSystem.splitWidth in FractionalCellSystemChallenge, line 3940. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3940).

**Stored adjoint estimate numbers.** Adjoint numbers record the potential scale, dual decomposition bounds, parameter-shift bounds and exact parameter set. Source: Breakdown.CellCert.CellSystem.AdjointNumbers in FractionalCellSystemChallenge, line 3942. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3942).

**Chosen sharp negative Laplacian.** The sharp-trace selector chooses a weak negative Laplacian with the required weighted L2 bound and returns zero when none exists. Source: Breakdown.CellCert.CellSystem.sharpTraceOf in FractionalCellSystemChallenge, line 3957. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3957).

**Chosen pin Hessian and trace.** The pin selector chooses a measurable, essentially bounded weak second derivative and negative trace together and returns two zero fields when no witness exists. Source: Breakdown.CellCert.CellSystem.pinSecondTraceOf in FractionalCellSystemChallenge, line 3962. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3962).

**Chosen dual negative Laplacian.** The dual-trace selector chooses a weak negative Laplacian with the required weighted L2 bound and returns zero otherwise. Source: Breakdown.CellCert.CellSystem.dualTraceOf in FractionalCellSystemChallenge, line 3970. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3970).

**Chosen potential negative Laplacian.** The potential-trace selector chooses a weak negative Laplacian with the required weighted L2 bound and returns zero otherwise. Source: Breakdown.CellCert.CellSystem.potentialTraceOf in FractionalCellSystemChallenge, line 3975. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3975).

**Chosen divergence of the flux.** The flux-divergence selector chooses a weak matrix divergence with the required weighted L2 bound and returns zero otherwise. Source: Breakdown.CellCert.CellSystem.fluxDivOf in FractionalCellSystemChallenge, line 3980. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3980).

**Assemble the adjoint-dual core.** The core dual record assembles constructed derivatives, traces, pressure, flux and numerical bounds while initializing its inverse-square field and mode set to zero and empty. Source: Breakdown.CellCert.CellSystem.adjointDualCore in FractionalCellSystemChallenge, line 3986. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L3986).

**Choose a finite-harmonic remainder.** The remainder selector chooses an almost-everywhere equal measurable weighted-L2 field with finite angular support, or keeps the original field with an empty mode set otherwise. Source: Breakdown.CellCert.CellSystem.inverseSquareChoice in FractionalCellSystemChallenge, line 4020. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4020).

**Complete the adjoint-dual data.** The completed dual data replace the core's inverse-square field and mode set with the selected remainder pair. Source: Breakdown.CellCert.CellSystem.adjointDualOf in FractionalCellSystemChallenge, line 4027. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4027).

**Data assigned to one cell entry.** A cell entry records its mesh cell, scalar and basis data, harmonic classes, row forms, deviation constants and far estimates. Source: Breakdown.CellCert.CellSystem.CellEntry in FractionalCellSystemChallenge, line 4033. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4033).

**Source namespace:** Breakdown.CellCert.CellSystem.CellEntry.

**Box selected by a cell entry.** The entry's box is the mesh box selected by its mesh-cell index. Source: Breakdown.CellCert.CellSystem.CellEntry.box in FractionalCellSystemChallenge, line 4057. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4057).

**Complete basis of a cell entry.** The entry's bases extend its given coefficients by the canonical bases above the entry's base degree. Source: Breakdown.CellCert.CellSystem.CellEntry.bases in FractionalCellSystemChallenge, line 4059. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4059).

**Source namespace:** Breakdown.CellCert.CellSystem.

**Data for the complete cell system.** Cell-system data assemble the splitting, tree, spectral and exterior data with all cell entries, shift sums and adjoint numerical bounds. Source: Breakdown.CellCert.CellSystem.CellSystemData in FractionalCellSystemChallenge, line 4063. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4063).

**Identify the fractional cell system.** A system instance fixes the fractional power to 501 over 500 and identifies its weight, exterior geometry, cells, moments, gauges and spectral blocks. Source: Breakdown.CellCert.CellSystem.IsSystemInstance in FractionalCellSystemChallenge, line 4098. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4098).

**Base fractional certificate tests.** The base-system predicate collects sign, coercivity, contraction, defect, parameter-inclusion and nontriviality requirements for a fractional certificate. Source: Breakdown.CellCert.CellSystem.IsBaseSystem in FractionalCellSystemChallenge, line 4122. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4122).

**Numerical cell losses and spectral fit.** Cell numbers bound the model-field errors, allocate their losses and require the finite spectral majorant and tail estimates. Source: Breakdown.CellCert.CellSystem.IsCellNumbers in FractionalCellSystemChallenge, line 4163. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4163).

**Reduced loss and adjoint tests.** Reduced losses require the kernel-sum bounds for model errors, profile parameter shifts and adjoint decompositions across the prescribed parameter box. Source: Breakdown.CellCert.CellSystem.IsReducedLosses in FractionalCellSystemChallenge, line 4188. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4188).

**Exterior coercivity tests.** The exterior predicate requires strain and curl-gradient bounds and the scalar inequality that absorbs the weighted exterior losses. Source: Breakdown.CellCert.CellSystem.IsExteriorSystem in FractionalCellSystemChallenge, line 4258. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4258).

**Geometry and tails of spectral blocks.** A spectral system requires nondegenerate block geometry, the axis cutoff condition, block separation, axis-gradient bounds and a uniform tail bound. Source: Breakdown.CellCert.CellSystem.IsSpectralSystem in FractionalCellSystemChallenge, line 4270. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4270).

**Validity of stored spectral tables.** Spectral bounds require every stored interval and axis certificate to satisfy its respective polynomial inequality. Source: Breakdown.CellCert.CellSystem.IsSpectralBounds in FractionalCellSystemChallenge, line 4290. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4290).

**Independent multiplier slots.** The split-system predicate requires an injective multiplier-slot map whose rows in the free map are zero. Source: Breakdown.CellCert.CellSystem.IsSplitSystem in FractionalCellSystemChallenge, line 4294. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4294).

**Identify the global elimination tree.** The tree-system predicate matches all tree cell forms with cell and delay matrices and identifies the global penalty form. Source: Breakdown.CellCert.CellSystem.IsTreeSystem in FractionalCellSystemChallenge, line 4298. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4298).

**Multiplicity of a real harmonic row.** The system weight is one for a zero-harmonic row and two otherwise. Source: Breakdown.CellCert.CellSystem.systemWeight in FractionalCellSystemChallenge, line 4304. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4304).

**Viscosity scale of a row.** The system scale divides the square root of the split viscosity by the real-harmonic multiplicity. Source: Breakdown.CellCert.CellSystem.systemScale in FractionalCellSystemChallenge, line 4307. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4307).

**Scaled system multiplier matrix.** The test multiplier multiplies the system multiplier by the same diagonal row-scale matrix on both sides. Source: Breakdown.CellCert.CellSystem.testMultiplierOf in FractionalCellSystemChallenge, line 4310. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4310).

**Scaled system reducer matrix.** The test reducer multiplies the system reducer by the diagonal matrix of reciprocal row scales. Source: Breakdown.CellCert.CellSystem.testReducerOf in FractionalCellSystemChallenge, line 4314. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4314).

**Complete row multiplier expression.** The multiplier expression adds row norms, class penalties, the near row square and the finite tail divided by one minus the far share. Source: Breakdown.CellCert.CellSystem.multiplierLHS in FractionalCellSystemChallenge, line 4318. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4318).

**Conditions for one exact cell form.** Cell-system facts require the model, weights, mode coverage, row and tail inequalities, valid coordinates and domination of the given matrix by the exact cell formula. Source: Breakdown.CellCert.CellSystem.IsCellSystemFacts in FractionalCellSystemChallenge, line 4324. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L4324).

### FractionalCertificateChallenge

This statement environment defines weak fractional fields, the rotating certificate norms and the finite-dimensional held problem used by the fractional certificate construction.

Reading context: Supplementary fractional certificate route through Breakdown.FracCert.Main; these definitions precede the cell system and the rotating-profile implication.

**Source namespace:** Breakdown.Held.

**The mixed box and ellipsoid test set.** The test set imposes coordinate bounds on active indices and a weighted squared-norm bound on their complement. Source: Breakdown.Held.testSet in FractionalCertificateChallenge, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L10).

**Source namespace:** Breakdown.SteadyCert.

**Squared Hilbert-Schmidt matrix size.** The entry square sums the squared norms of a linear map's values on the standard basis. Source: Breakdown.SteadyCert.entrySq in FractionalCertificateChallenge, line 19. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L19).

**Hilbert-Schmidt matrix pairing.** The entry inner product sums the pairings of two linear maps on the standard basis. Source: Breakdown.SteadyCert.entryInner in FractionalCertificateChallenge, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L21).

**Trace of a second derivative.** The second trace sums the tensor evaluated twice on each standard basis vector. Source: Breakdown.SteadyCert.secondTrace in FractionalCertificateChallenge, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L23).

**One discrete axial rotation.** The turn step rotates the horizontal coordinates through two pi divided by the symmetry order and preserves height. Source: Breakdown.SteadyCert.turnStep in FractionalCertificateChallenge, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L25).

**Reflection across the middle plane.** The mirror preserves the horizontal coordinates and negates the vertical coordinate. Source: Breakdown.SteadyCert.mirror in FractionalCertificateChallenge, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L30).

**Vector rotation and reflection symmetry.** The vector-class predicate requires equivariance under the discrete rotation and reflection almost everywhere. Source: Breakdown.SteadyCert.IsClassField in FractionalCertificateChallenge, line 33. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L33).

**Scalar rotation and reflection symmetry.** The scalar-class predicate requires pointwise invariance under the discrete rotation and reflection. Source: Breakdown.SteadyCert.IsClassScalar in FractionalCertificateChallenge, line 36. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L36).

**Compact smooth vector tests.** A vector test field is smooth and has compact support. Source: Breakdown.SteadyCert.IsTestVectorField in FractionalCertificateChallenge, line 39. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L39).

**Compact smooth scalar tests.** A scalar test function is smooth and has compact support. Source: Breakdown.SteadyCert.IsTestScalar in FractionalCertificateChallenge, line 41. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L41).

**Distributional first derivative.** The weak-gradient predicate requires the coordinatewise integration-by-parts identity against every compact smooth scalar test. Source: Breakdown.SteadyCert.IsWeakGradientOf in FractionalCertificateChallenge, line 43. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L43).

**Distributional second derivative.** The weak-second-derivative predicate requires the integration-by-parts identity for each component of the first derivative. Source: Breakdown.SteadyCert.IsWeakSecondDerivOf in FractionalCertificateChallenge, line 47. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L47).

**Local integrability on compact sets.** This predicate requires the supplied scalar function itself to be integrable on every compact set. Source: Breakdown.SteadyCert.IsLocalSquareIntegrable in FractionalCertificateChallenge, line 52. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L52).

**Gradient with local square control.** A gradient field has a locally square-integrable scalar potential and vector field satisfying the distributional gradient identity. Source: Breakdown.SteadyCert.IsGradientField in FractionalCertificateChallenge, line 54. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L54).

**Solenoidal vector in L2.** The solenoidal-L2 predicate requires square integrability and zero pairing with every compact smooth scalar gradient. Source: Breakdown.SteadyCert.IsSolenoidalL2 in FractionalCertificateChallenge, line 60. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L60).

**Square-integral vector norm.** The L2 norm is the square root of the integral of the field's squared pointwise norm. Source: Breakdown.SteadyCert.l2Norm in FractionalCertificateChallenge, line 63. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L63).

**Integrated vector pairing.** The L2 pairing is the integral of the pointwise real inner product. Source: Breakdown.SteadyCert.l2Pair in FractionalCertificateChallenge, line 65. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L65).

**Smallest norm after a pressure shift.** The projected norm is the infimum of the L2 norms obtained by adding an admissible gradient and requiring the sum to lie in L2. Source: Breakdown.SteadyCert.projectedNorm in FractionalCertificateChallenge, line 67. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L67).

**Second-order weak field conditions.** A second-order field has measurable velocity and derivatives, L6 velocity, square-integrable derivatives, zero divergence and the prescribed symmetries. Source: Breakdown.SteadyCert.IsSecondOrderField in FractionalCertificateChallenge, line 70. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L70).

**Weak fractional power in L2.** A weak fractional power lies in L2 and satisfies the self-adjoint testing identity against every compact smooth vector field. Source: Breakdown.SteadyCert.IsWeakFractionalPower in FractionalCertificateChallenge, line 83. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L83).

**Rotating similarity drift.** The drift combines the similarity scaling term, radial derivative and rotational commutator with their fractional coefficients. Source: Breakdown.SteadyCert.driftField in FractionalCertificateChallenge, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L87).

**Weighted second-order energy.** The energy adds the squared L2 norm of the second trace to the weighted squared size of the first derivative. Source: Breakdown.SteadyCert.weightedEnergy in FractionalCertificateChallenge, line 90. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L90).

**Energy and multiplier size.** The size norm takes the square root of the field energy plus the squared multiplier scale times the multiplier-coordinate sum of squares. Source: Breakdown.SteadyCert.sizeNorm in FractionalCertificateChallenge, line 94. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L94).

**Pin pairing against a gradient.** A pin value integrates the Hilbert-Schmidt pairing of the gradient with the pin field. Source: Breakdown.SteadyCert.pinValue in FractionalCertificateChallenge, line 98. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L98).

**Euclidean norm of finite coordinates.** The finite-vector norm is the square root of the sum of squared coordinates. Source: Breakdown.SteadyCert.vecNorm in FractionalCertificateChallenge, line 101. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L101).

**Symmetrized transport product.** The symmetric product is half the sum of each field's derivative applied to the other field. Source: Breakdown.SteadyCert.symProduct in FractionalCertificateChallenge, line 103. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L103).

**Weighted row pairing size.** The row size is the square root of the weighted sum of squared L2 pairings with the row fields. Source: Breakdown.SteadyCert.rowSize in FractionalCertificateChallenge, line 107. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L107).

**Row size modulo gradient fields.** The row seminorm takes the infimum of row sizes after adding an admissible gradient field. Source: Breakdown.SteadyCert.rowSeminorm in FractionalCertificateChallenge, line 110. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L110).

**Scalar bound from the quadratic step.** The bound constant uses the stated rational and square-root formula in the forcing, row and pin sizes and the contraction parameter. Source: Breakdown.SteadyCert.boundConst in FractionalCertificateChallenge, line 113. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L113).

**Small root radius formula.** The radius formula is twice the seed size divided by one plus the square root of one minus four times the quadratic coefficient and seed size. Source: Breakdown.SteadyCert.radiusOf in FractionalCertificateChallenge, line 117. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L117).

**Coordinate parameter box.** The parameter box consists of vectors whose coordinate absolute values do not exceed their assigned radii. Source: Breakdown.SteadyCert.box in FractionalCertificateChallenge, line 119. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L119).

**Negative second derivative trace.** The negative trace negates the sum of the diagonal evaluations of the second derivative tensor. Source: Breakdown.SteadyCert.negSecondTrace in FractionalCertificateChallenge, line 121. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L121).

**Source namespace:** Breakdown.SteadyCert.FracCertData.

**Derivative of the approximate profile.** The profile-gradient accessor takes the Fréchet derivative of the profile at the selected parameter. Source: Breakdown.SteadyCert.FracCertData.gradProfile in FractionalCertificateChallenge, line 175. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L175).

**Local bordered linear field.** The local field combines drift, negative split-viscosity second trace, linearized transport and the actuator multiplier sum. Source: Breakdown.SteadyCert.FracCertData.localField in FractionalCertificateChallenge, line 177. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L177).

**Fractional correction to the split.** The split field adds the split viscosity times the second trace to the supplied fractional power field. Source: Breakdown.SteadyCert.FracCertData.splitField in FractionalCertificateChallenge, line 182. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L182).

**Certificate weighted energy.** The certificate energy specializes the second-order energy to the certificate's weight. Source: Breakdown.SteadyCert.FracCertData.energy in FractionalCertificateChallenge, line 185. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L185).

**Certificate correction size.** The certificate size specializes the energy-and-multiplier norm to its multiplier scale and weight. Source: Breakdown.SteadyCert.FracCertData.size in FractionalCertificateChallenge, line 188. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L188).

**Energy of the fractional split.** The split energy is the square root of the split-field pairing with the negative trace plus the reduced-coercivity derivative energy. Source: Breakdown.SteadyCert.FracCertData.splitEnergy in FractionalCertificateChallenge, line 192. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L192).

**Vector of pin values.** The pin vector evaluates each of the certificate's pin fields against the supplied gradient. Source: Breakdown.SteadyCert.FracCertData.pins in FractionalCertificateChallenge, line 197. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L197).

**Defect of the approximate profile.** The defect sums the profile's drift, fractional power, nonlinear transport and actuator multiplier terms. Source: Breakdown.SteadyCert.FracCertData.defect in FractionalCertificateChallenge, line 199. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L199).

**Certificate row size.** The certificate row size uses its row family and row weights in the weighted pairing norm. Source: Breakdown.SteadyCert.FracCertData.rows in FractionalCertificateChallenge, line 203. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L203).

**Certificate row size modulo pressure.** The certificate's pressure-insensitive row size uses its row family and weights in the infimum over gradient shifts. Source: Breakdown.SteadyCert.FracCertData.rowsModGrad in FractionalCertificateChallenge, line 205. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L205).

**Coercivity after low-frequency loss.** The reduced gap subtracts the low-frequency loss from the reduced coercivity. Source: Breakdown.SteadyCert.FracCertData.reducedGap in FractionalCertificateChallenge, line 207. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L207).

**Combined contraction factor.** The contraction factor combines the split and row losses with the pin loss through the square-root expression and reduced gap. Source: Breakdown.SteadyCert.FracCertData.contraction in FractionalCertificateChallenge, line 209. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L209).

**Certificate forcing-size bound.** The bound function specializes the scalar quadratic bound to the certificate's form scale, contraction, gap and pin weight. Source: Breakdown.SteadyCert.FracCertData.boundFn in FractionalCertificateChallenge, line 213. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L213).

**Bound for a unit row forcing.** The row constant evaluates the certificate bound at forcing size one, row size equal to the square root of rowMax and zero pin size. Source: Breakdown.SteadyCert.FracCertData.rowConst in FractionalCertificateChallenge, line 215. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L215).

**Radius of the held correction.** The held radius applies the small-root formula to the certificate's row constant, product constant and seed-size bound. Source: Breakdown.SteadyCert.FracCertData.heldRadius in FractionalCertificateChallenge, line 217. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L217).

**Active box with stiff ellipsoid.** The certificate test box combines its active-coordinate radii with the slope-weighted ellipsoid constraint on the remaining coordinates. Source: Breakdown.SteadyCert.FracCertData.testBox in FractionalCertificateChallenge, line 219. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L219).

**Actuator-adjoint frame error.** The adjoint error subtracts the stored frame entry from each actuator-adjoint L2 pairing. Source: Breakdown.SteadyCert.FracCertData.adjointError in FractionalCertificateChallenge, line 221. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L221).

**Adjusted multiplier coordinate.** The adjusted multiplier subtracts the defect-adjoint pairing and slope coordinate from the frame-transformed multiplier. Source: Breakdown.SteadyCert.FracCertData.adjustedMultiplier in FractionalCertificateChallenge, line 224. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L224).

### FractionalChallenge

This statement environment specifies fractional dissipation, global competitors, rotating profiles and the two conditional breakdown conclusions.

Reading context: Supplementary fractional branch, outside the classical paper; the library supplies its proofs through Breakdown.Frac.SpaceExports and Breakdown.Frac.TorusBlowupExports.

**Source namespace:** Breakdown.

**Second-order Taylor remainder.** The remainder removes the value, first derivative and half the second derivative at the base point from the displaced value. Source: Breakdown.secondOrderRemainder in FractionalChallenge, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L23).

**Fractional dissipation normalizer.** The fractional normalizer integrates cosine minus one plus the quadratic correction against the radial fractional kernel. Source: Breakdown.fractionalNormalizer in FractionalChallenge, line 26. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L26).

**Fractional dissipation integral.** The fractional power divides the kernel integral of the second-order Taylor remainder by the fractional normalizer. Source: Breakdown.fractionalPowerAt in FractionalChallenge, line 29. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L29).

**Smooth fractional solution.** A fractional solution has smooth velocity and pressure on nonnegative times, matches its datum and satisfies momentum and incompressibility for positive times. Source: Breakdown.IsFractionalSolution in FractionalChallenge, line 32. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L32).

**Fractional breakdown on space.** The space-breakdown predicate requires, for every positive viscosity, a smooth compact solenoidal datum admitting no global smooth fractional solution with one uniform energy bound. Source: Breakdown.FractionalBreakdownOnSpace in FractionalChallenge, line 42. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L42).

**Fractional breakdown on the torus.** The torus-breakdown predicate requires, for every positive viscosity, a smooth unit-periodic solenoidal datum admitting no global smooth fractional solution with periodic velocity. Source: Breakdown.FractionalBreakdownOnTorus in FractionalChallenge, line 48. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L48).

**Infinitesimal axial rotation.** The axial generator sends the first two coordinates to minus the second and the first and has zero vertical component. Source: Breakdown.axialTurn in FractionalChallenge, line 54. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L54).

**Rotating fractional profile residual.** The residual adds fractional similarity drift, axial rotation, fractional dissipation, nonlinear transport and the pressure gradient. Source: Breakdown.rotatingProfileResidual in FractionalChallenge, line 57. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L57).

**Nonzero rotating fractional profile.** The profile-existence proposition requires a nonzero smooth solenoidal rotating solution with positive viscosity and derivative decay bounds of the stated fractional orders. Source: Breakdown.RotatingFractionalProfileExists in FractionalChallenge, line 63. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L63).
<!-- /passage:front -->

## Further declarations of these files

<!-- passage:sec-further-declarations-of-these-files -->

The declarations below are stated twice by the authors: in these fractional files and in the classical readable statement files. Each sentence is ours, from our annotation of the same-named declaration in [the statement files](../navier-stokes-statement-files/paper.md) or [the cell reference](../navier-stokes-cell-reference/paper.md), and the link opens this file's declaration.

### FractionalCellSystemChallenge (also in the readable files)

**Laplacian.** Definition. The sum of the three diagonal second directional derivatives represents the vector Laplacian in (1.1). ([`sumSecondPartialsAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L7))

**Orientation of three components.** Definition. The alternating sign fixes the curl convention in cylindrical component arrays. Repeated indices contribute zero; the order of the two gradient indices matters. ([`permSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L28))

**Abstract cell approximation data.** Structure. Also inherits the 46 directly declared fields of Breakdown.SteadyCert.FracCertData; those glosses are stored at the parent declaration. ([`FracCellData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L51))

**Real quadratic form.** Definition. Evaluates the real matrix form on a real vector. Symmetry and positivity are separate requirements, so this evaluator alone supplies neither. ([`quadValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L130))

**Trace free contraction constant.** Definition. This is the square root of seven halves appearing in the mixed gradient-velocity loss. It is the fixed constant before any larger exterior majorant is chosen. ([`traceFreeConst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L262))

**Cylindrical radius.** Definition. Returns r from the first two Cartesian coordinates, leaving the height coordinate out of the norm. ([`cylRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L309))

**Cylindrical height.** Definition. Returns the signed height z; reflection to the stored upper half-plane is performed separately. ([`cylHeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L311))

**Point in cylindrical coordinates.** Definition. Builds the Cartesian point with radius r, angle θ and height z. Here θ is the spatial angle, whereas the paper uses θ for time and φ for angle. ([`cylPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L313))

**Radial frame vector.** Definition. The first vector of the moving cylindrical frame is represented in the fixed Cartesian basis. ([`radialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L316))

**Angular frame vector.** Definition. The second frame vector differentiates the radial direction with respect to angle and is orthogonal to it. ([`angularUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L318))

**Axial frame vector.** Definition. The third frame vector is the constant unit vector in the height direction. ([`axialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L320))

**Spatial harmonic frequency.** Definition. Multiplies an integer mode by the azimuthal order. This one-frequency helper is distinct from the active two-integer label map of (B.2). ([`azimuth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L328))

**Meridian rectangle.** Structure. Stores the four endpoints of a rectangle Q in the nonnegative meridian quadrant. Endpoint ordering is not part of the data record and is imposed by IsCellBox. ([`CellBox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L338))

**Cell meeting the axis.** Proposition. An axis cell is recognised by the exact equality r₁=0, rather than a numerical tolerance. ([`IsAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L348))

**Meridian rectangle as a set.** Definition. The stored meridian rectangle includes all four sides. Later integration permits shared boundaries of measure zero. ([`rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L350))

**Cell reflected and rotated.** Definition. A cell describes all angles and both signs of height because membership uses the absolute value of z. ([`solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L352))

**Weight for radial polynomials.** Definition. Axis cells use radial weight r, whereas off-axis cells use weight one. This is the Jacobi versus Legendre distinction in (B.27). ([`lineWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L356))

**Reference radial coordinate.** Definition. Maps the radial interval affinely to the reference interval from minus one to one. A valid cell supplies the nonzero denominator. ([`refR`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L358))

**Reference height coordinate.** Definition. Maps the height interval affinely to the same reference interval; its orientation follows the ordered cell endpoints. ([`refZ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L360))

**Valid meridian rectangle.** Structure. Requires nonnegative lower endpoints and strictly positive width and height. These inequalities justify the affine reference coordinates and exclude degenerate rectangles. ([`IsCellBox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L364))

**Axis adjusted radial factor.** Definition. The factor is one for axis cells and r₁ otherwise, matching the exceptional convention in (B.27). ([`innerRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L379))

**Derivative in the radial variable.** Definition. Takes a one-variable derivative while holding the height fixed. It is an evaluator, so differentiability must be established separately. ([`radialDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L381))

**Derivative in the height variable.** Definition. Takes a one-variable derivative while holding the radius fixed. This complex-valued derivative is used before the finite matrix forms are assembled. ([`heightDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L383))

**Curl from gradient components.** Definition. The component formula reads the gradient entry with output index first and derivative index second. That convention must be kept when comparing the paper's printed curl array. ([`curlComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L406))

**Polynomial basis coefficients.** Structure. Stores coefficient functions for every natural degree in r and z. A finite file therefore needs a specified continuation beyond the degrees it stores. ([`CellBases`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L437))

**Radial orthonormal polynomial.** Definition. Evaluates degree j using only coefficients numbered zero through j. Coefficients outside that range do not affect this polynomial. ([`radialPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L445))

**Height orthonormal polynomial.** Definition. Evaluates degree l using the height coefficient table. Orthonormality is imposed by IsCellBases, not by the evaluator. ([`heightPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L447))

**Orthonormal cell polynomials.** Structure. The radial basis is orthonormal with lineWeight and the height basis with ordinary measure, with positive leading coefficients at every degree. These requirements fix normalisation and signs beyond the truncated cell unknowns. ([`IsCellBases`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L454))

**Radial polynomial eigenvalue.** Definition. Uses j(j+2) on axis cells and j(j+1) off the axis, with the square of the inverse half-width. Degree zero has eigenvalue zero. ([`radialEigen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L462))

**Height polynomial eigenvalue.** Definition. Uses the Legendre eigenvalue l(l+1) with the square of the inverse half-height. The degree-zero value is deliberately zero. ([`heightEigen`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L465))

**Squared gradient-array norm.** Definition. Adds squared complex moduli of all nine gradient entries, with no symmetry reduction. ([`sumSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L467))

**Squared vector norm.** Definition. Adds squared complex moduli of the three velocity components. ([`vecSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L469))

**Squared curl-array norm.** Definition. Forms curlComp first, then sums the three squared moduli; it is not a sum over all nine entries. ([`curlSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L471))

**Gradient and velocity coordinates.** Definition. Packs nine gradient entries in row-major order 3a+b, then the three velocity entries. This fixes the coordinates of the 12 by 12 matrices in (B.26). ([`pairVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L473))

**Local form coefficients and losses.** Structure. Collects polynomial cutoffs, resolved modes, local matrix fields and tail-absorption weights for the reusable one-frequency estimate. The active certificate supplies corresponding data separately for each space-time label. ([`CellScalars`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L483))

**Ratio of radial measures.** Definition. Divides cylindrical measure r by the basis weight. On an axis cell this agrees with one away from the axis; at r=0 Lean's total division gives zero. ([`rHat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L514))

**Elimination data for cell relations.** Structure. Stores selected relation rows, the unknown solved by each row, and retained skeleton unknowns. It does not itself assert that the solved block is invertible. ([`ParamData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L743))

**Matrix on solved coordinates.** Definition. Extracts the square submatrix by looking up the selected solved coordinate in each relation row. Its determinant is tested by IsParamData. ([`solvedBlock`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L759))

**Invertible solved relation block.** Structure. Requires distinct solved coordinates, no solved coordinate in the skeleton, and a nonzero determinant for the solved block. It does not say that all remaining coordinates are skeleton coordinates. ([`IsParamData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L769))

**Real part of a complex form.** Definition. Uses the conjugate of the first vector in the complex matrix pairing and returns its real part. Hermitian symmetry is a separate condition. ([`quadFormValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L774))

**Orientation of a strip face.** Definition. Chooses the sign from the relative order of the face and opposite-face coordinates. Equality is excluded separately by the face-validity predicate. ([`edgeSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L796))

**Radial strip moment.** Definition. Expresses a trace moment by an integral over the strip between a face and its opposite. The denominator is the signed face separation, and the final test polynomial depends on height. ([`radialStripMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L798))

**Height strip moment.** Definition. The corresponding strip integral differentiates in height and retains a supplied radial weight. Face orientation and the radial measure are independent choices. ([`heightStripMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L802))

**Side segment and test polynomials.** Structure. Stores face direction, face and opposite-face coordinates, interval endpoints and polynomial test coefficients. The opposite face is needed for the strip representation of a trace. ([`FaceSegment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L814))

**Polynomial test on a side.** Definition. Evaluates the finite coefficient prefix for the requested degree. The family remains indexed by every natural degree even when the certificate uses only finitely many. ([`test`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L826))

**Trace moment from a strip.** Definition. Selects a radial or height strip according to the segment direction. The weighted flag changes the radial measure only for height strips. ([`moment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L828))

**Valid side test family.** Structure. Requires a nonzero strip width, positive interval length and nonzero leading test coefficient at every degree. Finite polynomial tables need a continuation satisfying the last condition. ([`IsFaceSegment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L834))

**Pressure mode on a meridian plane.** Definition. This helper takes a normalised angular Fourier coefficient at fixed r and z. It has a single angular integer and no time transform; active space-time modes are supplied later. ([`presMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L839))

**Coordinates of one cell mode.** Structure. Lists volume coefficients, side and pressure segments, corners and auxiliary side coefficients. Optional corner references represent the special axis case, not arbitrary missing data. ([`CellLayout`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L853))

**Eight kinds of cell unknown.** Definition. The disjoint sum distinguishes gradient, velocity, side, pressure, corner, stream and extra-side data. The corner-stream block has no harmonic label, unlike the seven other blocks. ([`CellDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L873))

**Gradient coefficient slot.** Definition. Selects one component and two polynomial degrees of a resolved harmonic's gradient; the cutoff is Q+1 in each direction. ([`lowStrain`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L883))

**Velocity coefficient slot.** Definition. Selects one velocity component with both polynomial degrees below Q. Its degree range is one shorter than the gradient block. ([`lowVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L886))

**Side velocity moment slot.** Definition. Selects a side, component and test degree below q+2 for a resolved harmonic. ([`sideVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L889))

**Side gradient moment slot.** Definition. Selects the side derivative moment with degrees below q+1, a different range from side velocity moments. ([`sideGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L893))

**Corner velocity slot.** Definition. Selects a labelled velocity component at a corner. Axis corners can instead be absent from the layout through an optional lookup. ([`cornerVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L900))

**Corner stream-function slot.** Definition. unlabelled-stream-block: Corner-stream indices have no harmonic parameter. Multiplying this block by the number of modes silently changes every later packed coordinate position. ([`cornerStream`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L903))

**Auxiliary side velocity slot.** Definition. Selects one of four whole-cell sides and a polynomial test degree through Q. These coordinates are later related to the segmented side moments. ([`extraVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L906))

**Unknowns for this cell layout.** Definition. Specialises the eight tagged blocks to the layout's harmonic set, degrees, segment counts and corners. ([`Datum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L916))

**Equality of cell coordinate tags.** Instance. Provides classical equality for the finite tagged coordinate type. This instance is a logical convenience and is not a serialised comparison routine. ([`instDecEqDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L918))

**Enumeration of cell coordinates.** Instance. Derives finiteness from the tagged product-and-sum construction. A decoder's packed ordering must agree with the chosen coordinate map. ([`instFintypeDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L920))

**Whole-side polynomial test.** Definition. Radial faces use height polynomials; height faces use radial polynomials with an extra factor r on axis cells. ([`sideTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L947))

**Ten kinds of cell relation.** Definition. The tagged index separates derivative identities, divergence, axis conditions, stream identities and side-moment consistency. Different tags have different degree ranges. ([`RelIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L982))

**Pairing with a segment test.** Definition. Integrates a supplied one-variable test against a segment polynomial over that segment's interval. ([`segmentTestPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L989))

**Integral on the radial interval.** Definition. This helper uses ordinary one-dimensional measure; callers insert lineWeight explicitly when it is needed. ([`radialInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L992))

**Integral on the height interval.** Definition. Integrates over the closed height interval. Boundary endpoints have no extra mass in the integral. ([`heightInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L994))

**Radial derivative matrix entry.** Definition. Pairs a derivative of one radial basis polynomial with another, using lineWeight and the reference-interval vanishing factor. ([`radialStiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L996))

**Height derivative matrix entry.** Definition. Pairs a height derivative with a basis polynomial using the corresponding reference-interval factor. ([`heightStiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L999))

**Multiplication by the radius.** Definition. Represents multiplication by r in the weighted radial basis through an integral of two basis polynomials. ([`radialShift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1002))

**Coordinate unit row.** Definition. Returns the row that reads one tagged datum. It is an exact algebraic coordinate selector. ([`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1005))

**Read a gradient coefficient.** Definition. Returns the coordinate row when both degrees lie through Q, and the zero row otherwise. The fallback is intentional and must not mask a malformed stored index. ([`strainAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1007))

**Read a velocity coefficient.** Definition. Returns a velocity-coordinate row only for degrees below Q, with zero outside that range. ([`velocityAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1011))

**Angular derivative of velocity.** Definition. Combines multiplication by the angular frequency with rotation of the cylindrical basis. The radial and angular components acquire opposite frame-coupling terms. ([`turnRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1014))

**Read an auxiliary side coefficient.** Definition. Returns an extra-side coordinate row through degree Q and zero beyond it. ([`extraAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1020))

**Read an optional corner stream.** Definition. A present corner selects its stream coordinate; an absent corner contributes zero. Layout validity restricts the absence to the permitted axis case. ([`streamAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1023))

**Find the zero angular mode.** Definition. Looks up zero in the layout's finite mode set. The optional result controls axis and stream relations that exist only for that mode. ([`zeroMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1029))

**Radial integration test.** Definition. Axis cells use powers r^(i+2), while off-axis cells use r^i. The shifted exponent supports the axis boundary identities. ([`radialBeta`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1031))

**All cell relation rows.** Definition. Builds the ten families of exact linear relations from differentiation, divergence, axis behaviour and trace matching. Some index cases deliberately produce zero rows; independent selected rows are checked later. ([`relationRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1033))

**Identify boundary coordinates.** Proposition. Marks side velocity, side gradient, pressure, corner velocity and corner stream blocks as skeleton data. Volume and extra-side coefficients are excluded. ([`IsSkeletonDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1104))

**Geometry and tests of a layout.** Structure. Matches the abstract cell data, degrees and bases, then imposes exact side placement, coverage and orthonormal trace tests. Axis omissions and polynomial degree restrictions are explicit parts of the predicate. ([`IsCellLayout`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1125))

**Selected cell relations.** Structure. Identifies every elimination row with a row of relationRow and restricts the retained skeleton to skeleton data. It deliberately keeps the selector and solved-block data explicit. ([`IsCellParam`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1170))

**Read a corner velocity.** Definition. Reads a corner component when the cell-corner map is present and otherwise gives zero. The layout predicate controls which axis corners can be omitted. ([`cornerAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1179))

**Side derivative moment row.** Definition. Combines segmented gradient moments with the integrals of a whole-side test against each segment test polynomial. ([`sideGradientRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1184))

**Radius of a radial side.** Definition. Uses r₁ for side zero and r₂ otherwise. Its geometric interpretation requires the caller to be in a radial-side branch. ([`sideRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1188))

**Endpoint of a height side.** Definition. Maps whole-side number two to the lower height endpoint and the other branch to the upper one. ([`sideHeightIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1190))

**Endpoint of a radial side.** Definition. Maps side zero to the inner radial endpoint and the other branch to the outer endpoint. ([`sideRadialIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1192))

**Side velocity moment row.** Definition. Combines velocity moments on the side's segments, retaining the q+2 test range. ([`sideVelocityRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1194))

**Angular side derivative row.** Definition. Applies the angular-frequency and cylindrical-frame terms to the assembled side velocity row. ([`turnSideRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1198))

**Gradient trace before divergence.** Definition. Reconstructs a face gradient from tangential integration by parts, angular frame terms or stored normal derivative moments, according to the component and face. ([`faceBaseRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1204))

**Gradient trace using divergence.** Definition. Replaces the normal diagonal entry by minus the other two diagonal entries. This implements the divergence-free trace constraint on either kind of face. ([`strainFaceRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1222))

**Primitive of the radial test weight.** Definition. Integrates ρ times the supplied test function from zero to r. This is a helper for weighted trace identities, rather than a new certificate condition. ([`radialWeightIntegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1297))

**Pull a form back along rows.** Definition. The returned matrix is the conjugate-row pullback of the supplied form. Complex conjugation is on the first row factor. ([`formOfRows`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1403))

**Form from an inverse Gram matrix.** Definition. Pulls back the inverse test Gram matrix. The inverse is total in Lean; the analytical use needs the separate positive-definiteness hypotheses. ([`testSupForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1406))

**Locations of low-order coefficients.** Structure. Abstracts the map from a cell's gradient and velocity coefficients and face rows to a larger coordinate set. ([`LowIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1411))

**Tensor-product cell polynomial.** Definition. Multiplies one radial and one height basis polynomial, with normalisation supplied by the basis predicate. ([`basisFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1417))

**Meridian monomial.** Definition. Uses ordinary r and z powers, unlike CellPoly.eval, which uses affine reference coordinates. ([`monomial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1419))

**Radial derivative of a real test.** Definition. Differentiates a real test function while fixing height; regularity is a separate mathematical input. ([`radialSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1421))

**Height derivative of a real test.** Definition. Differentiates a real test function while fixing radius. ([`heightSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1423))

**Integral over a cell rectangle.** Definition. Uses ordinary two-dimensional measure. Callers supply the cylindrical or polynomial-basis radial weight explicitly. ([`rectIntegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1425))

**Weighted test Gram matrix.** Definition. Forms a complex matrix from real weighted integrals of pairs of tests. It does not itself assert positivity of the weight or matrix. ([`testInnerMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1427))

**Cylindrical frame rotation.** Definition. Records the two nonzero coefficients that couple radial and angular basis directions under rotation. ([`frameTurn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1430))

**Angular derivative of one entry.** Definition. Combines the harmonic frequency with frame rotation in both indices of a gradient array. ([`angularComb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1433))

**Angular derivative of an array.** Definition. Applies angularComb to a linear combination of gradient components, retaining both frame corrections. ([`angularArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1437))

**Select one gradient component.** Definition. The coefficient array isolates a single ordered gradient entry, without imposing symmetry. ([`unitArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1440))

**Select one curl component.** Definition. The alternating array extracts the appropriate difference of gradient entries with the same convention as curlComp. ([`curlArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1442))

**Row for a gradient combination.** Definition. Combines low-gradient coordinate selectors with the supplied component array at one harmonic and one polynomial index. ([`lowRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1449))

**Radial-face component row.** Definition. Combines stored radial-face rows with an array selecting gradient or curl components. ([`radialFaceComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1452))

**Height-face component row.** Definition. The height-face version keeps the same component convention and its own polynomial-index direction. ([`heightFaceComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1455))

**Pair a polynomial test with data.** Definition. Expands a test pairing through the known low-gradient coefficients, using integrals against tensor-product basis functions. ([`lowPairRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1458))

**Height monomial moment.** Definition. Integrates a power of z against a height basis polynomial over the cell interval. ([`heightMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1462))

**Weighted radial monomial moment.** Definition. Integrates a power of r against a radial basis polynomial with the axis-dependent lineWeight. ([`radialMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1464))

**Known radial derivative energy.** Definition. Forms the derivative contribution already determined by low coefficients, including innerRadius and the reference vanishing factor. ([`radialProjForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1466))

**Known height derivative energy.** Definition. Forms the corresponding height derivative contribution using the height reference coordinate. ([`heightProjForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1471))

**Interior radial test weight.** Definition. The weight combines r−r₁ with the radial reference vanishing factor and is used by the off-axis inner form. ([`radialInnerWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1476))

**Interior height test weight.** Definition. Combines r−r₁ with the height reference vanishing factor for the off-axis inner form. ([`heightInnerWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1478))

**Interior radial derivative bound.** Definition. Uses an inverse Gram matrix on degrees below Q−1 in radius and through Q in height. Natural subtraction makes the index empty for small Q. ([`radialInnerForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1480))

**Interior height derivative bound.** Definition. Uses the integration-by-parts test family with degrees below Q in both variables and the height inner weight. ([`heightInnerForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1485))

**Weighted outer radial test.** Definition. Multiplies a meridian monomial by the basis lineWeight; this is a test function, not a coordinate value. ([`radialOuterTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1490))

**Radial boundary derivative row.** Definition. Combines moments on both radial faces with a differentiated interior test. The displayed plus signs follow the reference-coordinate factors already included in the formula. ([`radialOuterRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1492))

**Radial boundary derivative bound.** Definition. Pairs the radial outer rows through the inverse Gram matrix with cylindrical weight r. ([`radialOuterForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1498))

**Height boundary derivative row.** Definition. Combines height-face moments and an interior derivative of r times the height reference coordinate and test monomial. ([`heightOuterRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1502))

**Height boundary derivative bound.** Definition. Uses the inverse Gram matrix for height outer rows, with the radial and height degree ranges in their stated order. ([`heightOuterForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1508))

**Axis-compatible angular test.** Definition. Adds a factor r to the monomial so that the angular test family has the required axis behaviour. ([`angularTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1512))

**Angular energy on an axis cell.** Definition. Uses the axis-compatible tests and a Gram matrix with radial weight r, avoiding a separate inverse-radius diagonal term. ([`angularAxisForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1514))

**Off-axis angular remainder weight.** Definition. The weight is (r₂−r)/(r r₂); the off-axis branch and valid cell provide the positivity and denominator conditions. ([`angularOffWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1518))

**Angular energy off the axis.** Definition. Adds an inverse-r₂ diagonal form to a weighted test-supremum remainder. It is selected only in the off-axis component form. ([`angularOffForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1520))

**Derivative energy of one component.** Definition. Combines radial, height and angular contributions, choosing different constructions on and off the axis. ([`componentForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1528))

**Highest-degree coefficient penalty.** Definition. Selects the upper degree strips of two gradient-column blocks. Its use of Q−1 is natural-number subtraction. ([`topForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1534))

**Resolved gradient and curl energy.** Definition. Sums component derivative forms with mode weights and subtracts the prescribed highest-degree penalty. ([`energyForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1541))

**Gradient or velocity basis slot.** Inductive type. The two constructors distinguish a nine-component gradient basis element from a three-component velocity element, with different degree cutoffs. ([`LowSlot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1549))

**Field represented by one low slot.** Definition. A gradient slot has zero velocity and a velocity slot has zero gradient. Each nonzero component is one tensor-product basis function. ([`slotValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1554))

**Embed a low slot in cell data.** Definition. Routes a gradient or velocity slot through the corresponding map in LowIndex. ([`slotIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1562))

**Read one low coefficient.** Definition. The row is one at the embedded slot and zero elsewhere; it includes a harmonic label as well as the slot constructor. ([`slotRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1566))

**Complex paired local form.** Definition. Evaluates the full complex sesquilinear expression on two packed 12-component vectors, before a real part is taken elsewhere. ([`matrixSesq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1576))

**Low rows supplied by a layout.** Definition. Connects abstract LowIndex to the tagged CellDatum slots and translates two radial plus two height faces into the four-side numbering. ([`layoutIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L1632))

**Identity of a boundary unknown.** Inductive type. A key records the harmonic, geometric face or corner, component and test polynomial data. Interior coordinates receive a private tag and are not identified as boundary values by this key alone. ([`SkeletonKey`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2204))

**Boundary key of a cell coordinate.** Definition. Converts each skeleton block into its geometric key, retaining the full test-coefficient function. Volume and extra-side coordinates are sent to the private constructor. ([`keyOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2212))

**Parameters of the compactified chart.** Structure. Stores the radius scale L and auxiliary core, regularity and azimuthal parameters for the field construction. Positivity belongs to IsChartParams. ([`ChartParams`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2485))

**Valid compactified chart.** Structure. Requires positive L, core radius and auxiliary epsilon, epsilon below one eighth, and positive azimuthal order. The active cell premise later requires the stronger order bound κ≥3. ([`IsChartParams`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2491))

**Height divided by radius.** Definition. This is η=z/|y| in (B.3), with Lean's total value zero at the origin. Origin regularity is supplied by the field-shape conditions. ([`heightRatio`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2498))

**Squared polar sine.** Definition. Computes 1−η², the factor that controls behaviour at the axis in (B.7) and (B.8). ([`qOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2500))

**Compactified radial coordinate.** Definition. This is σ=|y|/(|y|+L) in the paper. The Lean name t does not denote the time variable here. ([`chartT`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2504))

**Radial chart vector.** Definition. Represents y/|y| componentwise and uses the total value zero at y=0. The complete field needs the prescribed vanishing factors at the origin. ([`radialVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2515))

**Weighted polar frame vector.** Definition. Represents the paper's vector p, including the factor that removes the unit polar vector's axis singularity. ([`polarVecQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2517))

**Weighted azimuthal frame vector.** Definition. Represents the paper's vector a, using Cartesian coordinates divided by |y| and vanishing at the axis away from the origin. ([`azimVecQ`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2520))

**Two knot lists for a spline.** Structure. Stores separate radial-chart and nonnegative-height knot lists. No ordering, endpoint or nonemptiness proof is included in the data record. ([`TensorMesh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2525))

**Ordered knots on the unit square.** Structure. Requires strictly increasing knot lists, each beginning at zero and ending at one. These facts provide at least one interval in each direction. ([`IsTensorMesh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2529))

**The interval containing a coordinate.** Definition. Counts internal knots at or below the evaluation point, so an interior knot selects the piece on its right. Values outside the chart range are still defined. ([`cellIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2537))

**Number of spline intervals.** Definition. Uses list length minus one with natural-number subtraction. Mesh validity is needed to rule out malformed short lists. ([`cellCount`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2539))

**Polynomial pieces on a tensor mesh.** Structure. A spline supplies a polynomial for every pair of natural indices. A finite serialisation must specify values outside the valid rectangle indices. ([`Spline`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2541))

**Evaluation of one spline chart.** Definition. Evaluates the polynomial selected by the two knot lists. The definition contains no interpolation or continuity check; join predicates establish those properties. ([`evalHalf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2545))

**Substitute the radial coordinate.** Definition. Replaces the first polynomial variable by a complex constant while leaving the second variable unchanged. ([`atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2551))

**Substitute the height coordinate.** Definition. Replaces the second polynomial variable while preserving the first. This is used in exact polynomial join identities. ([`atSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2554))

**Repeated radial polynomial derivative.** Definition. Iterates formal differentiation in the first variable. Order zero leaves the polynomial unchanged. ([`tDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2557))

**Repeated height polynomial derivative.** Definition. Iterates formal differentiation in the second variable, which represents the chart height rather than a Cartesian coordinate. ([`xDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2559))

**Conjugate spline coefficients.** Definition. Keeps the mesh and conjugates each polynomial coefficient. This is the coefficient-level operation used for harmonic reality conditions. ([`conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2574))

**Zero spline pieces after a cutoff.** Proposition. Quantifies over all natural indices, using one as the default radial knot. Thus a cutoff below one also constrains out-of-range pieces, not only the serialised valid cells. ([`VanishesFrom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2577))

**Prescribed radial endpoint powers.** Definition. Forms σ^e₀(1−σ)^e₁, the origin and infinity factors used in the field formulas. The exponents are natural numbers. ([`weightPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2598))

**Radial derivative in the chart.** Definition. Applies σ(1−σ)∂σ, corresponding to |y|∂|y| in (B.3). Radial phase terms are added by later operators. ([`radialScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2600))

**Derivative in chart height.** Definition. Differentiates the chart coefficient in η while fixing σ. This is separate from the physical height derivative in cylindrical coordinates. ([`heightDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCellSystemChallenge.lean#L2605))

### FractionalCertificateChallenge (also in the readable files)

**Abstract steady certificate data.** Structure. Also inherits the 46 directly declared fields of Breakdown.SteadyCert.FracCertData; those glosses are stored at the parent declaration. ([`FracCertData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalCertificateChallenge.lean#L123))

### FractionalChallenge (also in the readable files)

**Euclidean three-space.** Definition. The paper’s physical and similarity spaces are represented by Euclidean three-vectors with the usual inner-product norm. This fixed dimension is used in the drift integration by parts as well as in the Navier–Stokes operators. ([`Space`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L10))

**Coordinate unit vectors.** Definition. These are the three standard basis vectors used to write the divergence, Laplacian and gradient of (1.1). Coordinates are numbered 0, 1 and 2 in Lean. ([`unitVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L12))

**Divergence.** Definition. This is the trace of the spatial derivative, representing div u in (1.1) and div W in (1.2). The derivative is stored as a continuous linear map. ([`divergenceAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L14))

**Pressure gradient.** Definition. This reconstructs the vector ∇p from the three coordinate derivatives of the scalar pressure. Only the gradient enters the equation, so adding a function of time to p does not change this term. ([`gradientAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L17))

**Nonlinear transport.** Definition. Applying the spatial derivative of v to v itself gives the paper’s (v·∇)v. This order of application fixes the convection convention used throughout the certificate files. ([`advectionAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/FractionalChallenge.lean#L20))
<!-- /passage:sec-further-declarations-of-these-files -->

