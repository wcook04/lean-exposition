import Breakdown.Cert.ExtendedAssembly
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.GradInvSpec
import Breakdown.Cert.HalfOrderGraphMem
import Breakdown.Cert.ReadingExists
import Breakdown.Cert.ReadingEnergy
import Breakdown.Cert.TestPairing
import Breakdown.Cert.TestDense
import Breakdown.Cert.TranslationCriterion
import Breakdown.Cert.ContractionFixedPoint
import Breakdown.Cert.FreeInv
import Breakdown.Cert.FreeEnergyLocal
import Breakdown.Cert.FreeEquivariant
import Breakdown.Cert.FreePerturbation
import Breakdown.Cert.PeriodContinuity
import Breakdown.Cert.SliceSupBound
import Breakdown.Cert.SliceReading
import Breakdown.Cert.ProductBound
import Breakdown.Cert.ProductPairing
import Breakdown.Cert.ProductSub
import Breakdown.Cert.SpaceModulus
import Breakdown.Cert.TimeModulus
import Breakdown.Cert.LocalCompactness
import Breakdown.Cert.ExtendedUnitWeight
import Breakdown.Cert.ExtendedAtProfile
import Breakdown.Cert.ExtendedRowNorm
import Breakdown.Cert.ExtendedConvection
import Breakdown.Cert.ExtendedInvariance
import Breakdown.Cert.ExtendedConvectionContinuity
import Breakdown.Cert.ExtendedData
import Breakdown.Cert.ExtendedDataContinuity
import Breakdown.Cert.ExtendedCoerciveBordered
import Breakdown.Cert.ExtendedFrozenBridge
import Breakdown.Cert.ExtendedSupBound
import Breakdown.Cert.ExtendedConvectionCompact
import Breakdown.Cert.ExtendedBorderedInvertible
import Breakdown.Cert.ExtendedHeldMetric
import Breakdown.Cert.ExtendedHeldMapsTo
import Breakdown.Cert.ExtendedHeldContracts
import Breakdown.Cert.ExtendedHeldExistsUnique
import Breakdown.Cert.ExtendedHeldLimit
import Breakdown.Cert.ExtendedMultiplierContinuity
import Breakdown.Cert.ExtendedAdjointPairing
import Breakdown.Cert.ExtendedAdjointEnclosure
import Breakdown.Cert.ExtendedStiffEnclosure
import Breakdown.Cert.ExtendedExistsZeroHeld
import Breakdown.Cert.ExtendedHeldWeakEquation
import Breakdown.Cert.ExtendedHeldNonzero
import Breakdown.Cert.ExtendedSigmaProfileOfHeld
import Breakdown.Held.Exports

namespace Breakdown

open Cert

theorem extended_certificate_orbit_proved (h : ExtendedCertificateHypothesis) :
    WeakPeriodicSimilarityProfileExists := by
  have hProj : ProjectionHolds :=
    ⟨exists_projSpec, norm_solProj_le, inner_solProj, solProj_toPhysH⟩
  have hProp : PropagatorBoundHolds :=
    ⟨fun τ hτ x => by simpa only [neg_div] using norm_slicePropagator_le τ hτ x,
      fun x => GradInv.Internal.continuousOn_slicePropagator x⟩
  have hGradInv : GradInvHolds := fun P _ => ⟨integrable_propagatorIntegrand P, exists_gradInvSpec P⟩
  have hGraph : GraphClosedHolds := fun q => halfSsp_of_xbar q
  exact extended_certificate_orbit_of_nodes extendedUnitWeightHolds extendedAtProfileHolds
    hProj testPairingHolds_proof hGraph
    (fun _ => readingExistsHolds_proof) hProp testDenseHolds_proof
    translationCriterionHolds_proof contractionFixedPointHolds_proof rowNormHolds
    Held.testSetZero Held.adjointEnclosure
    readingEnergyHolds_of (fun _ => hGradInv)
    (fun g c => freeInvHolds_of hProp g c)
    (fun b g f => freeEnergyLocalHolds_of b g hGraph f)
    (fun _ _ f => freeEquivariantHolds_of f)
    (fun b g f e r p t => freePerturbationHolds_of f e r p t b g hGraph)
    (fun _ _ f => periodContinuityHolds_of f)
    sliceSupBoundHolds_of sliceReadingHolds_of productBoundHolds_of productPairingHolds_of
    productSubHolds_of spaceModulusHolds_of
    (fun b g f _ r => timeModulusHolds_of f r hProj b g hGraph)
    (fun tm sm tc f r _ => localCompactnessHolds_of tm sm tc f r)
    extendedConvectionHolds_of extendedInvarianceHolds_of extendedConvectionContinuityHolds_of
    extendedDataHolds_of extendedDataContinuityHolds_of extendedCoerciveBorderedHolds_of
    (fun s f p _ => extendedFrozenBridgeHolds_of s f p)
    extendedSupBoundHolds_of
    (fun l c f _ => extendedConvectionCompactHolds_of l c f)
    (fun cc cb i e _ _ => extendedBorderedInvertibleHolds_of cc cb i e)
    extendedHeldMetricHolds_of extendedHeldMapsToHolds_of extendedHeldContractsHolds_of
    extendedHeldExistsUniqueHolds_of
    (fun pc lc cc dc pp pb _ _ fi _ dd re td => extendedHeldLimitHolds_of pc lc cc dc pp pb fi dd re td)
    extendedMultiplierContinuityHolds_of
    (fun p t _ => extendedAdjointPairingHolds_of p t)
    (fun ap fp re en cv da pp pb tp pj he => extendedAdjointEnclosureHolds_of ap fp re en cv da pb tp pj he)
    extendedStiffEnclosureHolds extendedExistsZeroHeldHolds_of extendedHeldWeakEquationHolds_of
    extendedHeldNonzeroHolds_of extendedSigmaProfileOfHeldHolds_of h

end Breakdown
