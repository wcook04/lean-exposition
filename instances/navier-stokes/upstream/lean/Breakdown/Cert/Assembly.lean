import Breakdown.Cert.Nodes
import Breakdown.Cert.Rescale

namespace Breakdown.Cert

theorem certificate_orbit_of_nodes
    (hProj : ProjectionHolds) (hTest : TestPairingHolds) (hGraph : GraphClosedHolds)
    (hRead : GraphClosedHolds → ReadingExistsHolds) (hProp : PropagatorBoundHolds)
    (hDense : TestDenseHolds)
    (hTrans : TranslationCriterionHolds) (hFix : ContractionFixedPointHolds)
    (hEnergy : GraphClosedHolds → ReadingEnergyHolds)
    (hGradInv : PropagatorBoundHolds → GradInvHolds)
    (hFree : GradInvHolds → GraphClosedHolds → FreeInvHolds)
    (hLocal : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEnergyLocalHolds)
    (hEquiv : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds)
    (hPert : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds → ReadingExistsHolds → ProjectionHolds →
      TestPairingHolds → FreePerturbationHolds)
    (hPeriod : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → PeriodContinuityHolds)
    (hSliceSup : GraphClosedHolds → SliceSupBoundHolds)
    (hSlice : FreeEnergyLocalHolds → ReadingExistsHolds → GraphClosedHolds → GradInvHolds →
      FreeInvHolds → SliceReadingHolds)
    (hProd : SliceSupBoundHolds → ReadingExistsHolds → ReadingEnergyHolds → ProductBoundHolds)
    (hProdPair : ProductBoundHolds → ProjectionHolds → TestPairingHolds → ReadingExistsHolds →
      ProductPairingHolds)
    (hProdSub : ReadingExistsHolds → ProductBoundHolds → ProductSubHolds)
    (hConv : ReadingExistsHolds → ProjectionHolds → TestPairingHolds → ConvectionHolds)
    (hInv : ConvectionHolds → ProjectionHolds → InvarianceHolds)
    (hConvCont : ConvectionHolds → ConvectionContinuityHolds)
    (hData : ProjectionHolds → TestPairingHolds → ReadingEnergyHolds → DataHolds)
    (hDataCont : DataHolds → DataContinuityHolds)
    (hCoer : ReadingExistsHolds → ReadingEnergyHolds → FreePerturbationHolds → ConvectionHolds →
      DataHolds → TestPairingHolds → CoerciveBorderedHolds)
    (hFrozen : SliceReadingHolds → FreeEquivariantHolds → ProjectionHolds → ConvectionHolds →
      FrozenBridgeHolds)
    (hSup : FreeEnergyLocalHolds → FrozenBridgeHolds → InvarianceHolds → DataHolds →
      ReadingEnergyHolds → ConvectionHolds → FreeEquivariantHolds → SupBoundHolds)
    (hSpace : ReadingExistsHolds → GraphClosedHolds → SpaceModulusHolds)
    (hTime : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreePerturbationHolds → ReadingExistsHolds → TimeModulusHolds)
    (hLoc : TimeModulusHolds → SpaceModulusHolds → TranslationCriterionHolds → FreeInvHolds →
      ReadingExistsHolds → ReadingEnergyHolds → LocalCompactnessHolds)
    (hCpt : LocalCompactnessHolds → ConvectionHolds → FreeInvHolds → ReadingExistsHolds →
      ConvectionCompactHolds)
    (hBord : ConvectionCompactHolds → CoerciveBorderedHolds → InvarianceHolds →
      FreeEquivariantHolds → DataHolds → FreeInvHolds → BorderedInvertibleHolds)
    (hMetric : GraphClosedHolds → ReadingEnergyHolds → HeldMetricHolds)
    (hMaps : BorderedInvertibleHolds → CoerciveBorderedHolds → SupBoundHolds → ProductBoundHolds →
      ProductPairingHolds → DataHolds → InvarianceHolds → FreeEquivariantHolds → HeldMapsToHolds)
    (hContr : BorderedInvertibleHolds → CoerciveBorderedHolds → SupBoundHolds →
      ProductBoundHolds → ProductPairingHolds → ProductSubHolds → DataHolds → InvarianceHolds →
      FreeEquivariantHolds → HeldContractsHolds)
    (hUniq : ContractionFixedPointHolds → HeldMetricHolds → HeldMapsToHolds →
      HeldContractsHolds → BorderedInvertibleHolds → FreeEquivariantHolds → InvarianceHolds →
      HeldExistsUniqueHolds)
    (hLim : PeriodContinuityHolds → LocalCompactnessHolds → ConvectionContinuityHolds →
      DataContinuityHolds → ProductPairingHolds → ProductBoundHolds → HeldMetricHolds →
      InvarianceHolds → FreeInvHolds → ConvectionHolds → DataHolds → ReadingExistsHolds →
      TestDenseHolds → HeldLimitHolds)
    (hMult : HeldLimitHolds → HeldExistsUniqueHolds → MultiplierContinuityHolds)
    (hZero : HeldExistsUniqueHolds → MultiplierContinuityHolds → ExistsZeroHeldHolds)
    (hWeak : FreePerturbationHolds → ConvectionHolds → DataHolds → ProductPairingHolds →
      ProductBoundHolds → TestPairingHolds → HeldWeakEquationHolds)
    (hNonzero : ReadingEnergyHolds → HeldNonzeroHolds)
    (hSigma : SliceReadingHolds → HeldWeakEquationHolds → HeldNonzeroHolds →
      SigmaProfileOfHeldHolds) :
    ∀ {k : ℕ} (d : CertificateData k), IsCertificate d → WeakPeriodicSimilarityProfileExists := by
  have r0 : ReadingExistsHolds := hRead hGraph
  have e1 : ReadingEnergyHolds := hEnergy hGraph
  have g1 : GradInvHolds := hGradInv hProp
  have f1 : FreeInvHolds := hFree g1 hGraph
  have f2 : FreeEnergyLocalHolds := hLocal hProp g1 f1
  have f3 : FreeEquivariantHolds := hEquiv hProp g1 f1
  have f4 : FreePerturbationHolds := hPert hProp g1 f1 f3 r0 hProj hTest
  have s1 : SliceReadingHolds := hSlice f2 r0 hGraph g1 f1
  have p1 : ProductBoundHolds := hProd (hSliceSup hGraph) r0 e1
  have p2 : ProductPairingHolds := hProdPair p1 hProj hTest r0
  have p3 : ProductSubHolds := hProdSub r0 p1
  have c1 : ConvectionHolds := hConv r0 hProj hTest
  have c2 : InvarianceHolds := hInv c1 hProj
  have d1 : DataHolds := hData hProj hTest e1
  have b2 : CoerciveBorderedHolds := hCoer r0 e1 f4 c1 d1 hTest
  have q4 : SupBoundHolds := hSup f2 (hFrozen s1 f3 hProj c1) c2 d1 e1 c1 f3
  have l1 : LocalCompactnessHolds := hLoc (hTime hProp g1 f1 f4 r0) (hSpace r0 hGraph) hTrans f1 r0 e1
  have rs : BorderedInvertibleHolds := hBord (hCpt l1 c1 f1 r0) b2 c2 f3 d1 f1
  have m1 : HeldMetricHolds := hMetric hGraph e1
  have u1 : HeldExistsUniqueHolds := hUniq hFix m1 (hMaps rs b2 q4 p1 p2 d1 c2 f3) (hContr rs b2 q4 p1 p2 p3 d1 c2 f3)
    rs f3 c2
  have lim : HeldLimitHolds := hLim (hPeriod hProp g1 f1) l1 (hConvCont c1) (hDataCont d1) p2 p1 m1 c2 f1 c1 d1 r0 hDense
  have z1 : ExistsZeroHeldHolds := hZero u1 (hMult lim u1)
  have w1 : SigmaProfileOfHeldHolds := hSigma s1 (hWeak f4 c1 d1 p2 p1 hTest) (hNonzero e1)
  intro k d hd
  obtain ⟨p, hp, f, κ, hf, h0⟩ := z1 d hd
  obtain ⟨P, W, G, H, C, hs⟩ := w1 d hd p hp f κ hf h0
  exact weakPeriodicSimilarityProfileExists_of_sigma hs

end Breakdown.Cert
