import Breakdown.Cert.Statement
import Breakdown.Cert.Assembly
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
import Breakdown.Cert.Convection
import Breakdown.Cert.Invariance
import Breakdown.Cert.ConvectionContinuity
import Breakdown.Cert.Data
import Breakdown.Cert.DataContinuity
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.FrozenBridge
import Breakdown.Cert.SupBound
import Breakdown.Cert.SpaceModulus
import Breakdown.Cert.TimeModulus
import Breakdown.Cert.LocalCompactness
import Breakdown.Cert.ConvectionCompact
import Breakdown.Cert.BorderedInvertible
import Breakdown.Cert.HeldMetric
import Breakdown.Cert.HeldMapsTo
import Breakdown.Cert.HeldContracts
import Breakdown.Cert.HeldExistsUnique
import Breakdown.Cert.HeldLimit
import Breakdown.Cert.MultiplierContinuity
import Breakdown.Cert.ExistsZeroHeld
import Breakdown.Cert.HeldWeakEquation
import Breakdown.Cert.HeldNonzero
import Breakdown.Cert.SigmaProfileOfHeld

namespace Breakdown

open Cert

theorem certificate_orbit_proved (h : CertificateHypothesis) : WeakPeriodicSimilarityProfileExists := by
  obtain ⟨k, d, hd⟩ := h
  have hProj : ProjectionHolds :=
    ⟨exists_projSpec, norm_solProj_le, inner_solProj, solProj_toPhysH⟩
  have hProp : PropagatorBoundHolds :=
    ⟨fun τ hτ x => by simpa only [neg_div] using norm_slicePropagator_le τ hτ x,
      fun x => GradInv.Internal.continuousOn_slicePropagator x⟩
  have hGradInv : GradInvHolds := fun P _ => ⟨integrable_propagatorIntegrand P, exists_gradInvSpec P⟩
  have hGraph : GraphClosedHolds := fun q => halfSsp_of_xbar q
  exact certificate_orbit_of_nodes hProj testPairingHolds_proof hGraph
    (fun _ => readingExistsHolds_proof) hProp testDenseHolds_proof
    translationCriterionHolds_proof contractionFixedPointHolds_proof
    readingEnergyHolds_of (fun _ => hGradInv)
    (fun g c => freeInvHolds_of hProp g c)
    (fun b g f => freeEnergyLocalHolds_of b g hGraph f)
    (fun _ _ f => freeEquivariantHolds_of f)
    (fun b g f e r p t => freePerturbationHolds_of f e r p t b g hGraph)
    (fun _ _ f => periodContinuityHolds_of f)
    sliceSupBoundHolds_of sliceReadingHolds_of productBoundHolds_of productPairingHolds_of
    productSubHolds_of convectionHolds_of invarianceHolds_of convectionContinuityHolds_of
    dataHolds_of dataContinuityHolds_of coerciveBorderedHolds_of frozenBridgeHolds_of
    supBoundHolds_of spaceModulusHolds_of
    (fun b g f _ r => timeModulusHolds_of f r hProj b g hGraph)
    (fun tm sm tc f r _ => localCompactnessHolds_of tm sm tc f r)
    (fun l c f _ => convectionCompactHolds_of l c f)
    borderedInvertibleHolds_of heldMetricHolds_of heldMapsToHolds_of heldContractsHolds_of
    heldExistsUniqueHolds_of heldLimitHolds_of multiplierContinuityHolds_of
    existsZeroHeldHolds_of heldWeakEquationHolds_of heldNonzeroHolds_of
    sigmaProfileOfHeldHolds_of d hd

end Breakdown
