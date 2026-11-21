import TorusEuler.PaperParentCoefficientStatements
import TorusEuler.PaperApproximateSolution
import TorusEuler.PaperFlowBounds
import TorusEuler.PaperPhysicalCutoff
import TorusEuler.ActivationPrimaryJetBounds
import TorusEuler.LaterWavePrimaryPressureBound

/-!
Physical graph and cutoff statements of the frozen paper.
The construction for an arbitrary smooth activation cutoff is in
`TorusEuler.PaperPhysicalLaterStep`.

* Proposition 5.1 uses `paperProposition51_parentCoefficients`,
  `ParentLabelJetBound.weighted_sum_le`, and the two composition bounds.
* Lemma 5.7 uses the weighted, unweighted, and phase-independent graph bounds
  together with the centered-cell collar version.
* Lemma 5.8 uses the approximate equation and oscillatory Hölder estimates
  here. The exact supremum, mean and residual estimates are
  `PhysicalApproximationData.oscillation_sup_of_actualLevels`,
  `PhysicalApproximationData.meanCorrection_holder_of_actualLevels` and
  `PhysicalApproximationData.residual_holder_of_actualLaterGraph`.
  `PhysicalApproximationData.exists_parent_activationPrimary_phaseJetBound`
  supplies the primary activation jet estimate for the same seed.
* Lemma 5.9 uses `PhysicalApproximationData.paperLemma59_pressureCenter` on
  the measured hierarchy and its signed leading bound. The nonleading pressure
  contributions are `PhysicalApproximationData.paperLemma59_higherMeanHessians`.
  `exists_parent_leading_pressure_hessian_bound` supplies the uniform leading
  bound. `PhysicalApproximationData.paperLemma59_leadingSeedReadout` proves
  the seed's exact central rank-one derivative.
* Lemma 5.10 uses `PhysicalApproximationData.paperLemma510_flowBounds` for
  arbitrary smooth solenoidal perturbations.
* Proposition 5.11 uses `paperProposition511_physicalCutoff` and
  `periodicPoissonPressure_unique`.
-/
