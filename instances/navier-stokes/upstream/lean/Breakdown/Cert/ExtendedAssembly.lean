import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.Rescale
import Breakdown.Held.Statements

namespace Breakdown.Cert

theorem extended_normal_orbit_of_nodes
    (hProj : ProjectionHolds) (hTest : TestPairingHolds) (hGraph : GraphClosedHolds)
    (hRead : GraphClosedHolds → ReadingExistsHolds) (hProp : PropagatorBoundHolds)
    (hDense : TestDenseHolds)
    (hTrans : TranslationCriterionHolds) (hFix : ContractionFixedPointHolds)
    (hRow : RowNormHolds)
    (hHeldZero : Held.TestSetZeroStatement) (hHeldAdj : Held.AdjointEnclosureStatement)
    (hEnergy : GraphClosedHolds → ReadingEnergyHolds)
    (hGradInv : PropagatorBoundHolds → GradInvHolds)
    (hFree : GradInvHolds → GraphClosedHolds → FreeInvHolds)
    (hLocal : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEnergyLocalHolds)
    (hEquiv : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds)
    (hPert : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds →
      ReadingExistsHolds → ProjectionHolds → TestPairingHolds → FreePerturbationHolds)
    (hPeriod : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → PeriodContinuityHolds)
    (hSliceSup : GraphClosedHolds → SliceSupBoundHolds)
    (hSlice : FreeEnergyLocalHolds → ReadingExistsHolds → GraphClosedHolds → GradInvHolds →
      FreeInvHolds → SliceReadingHolds)
    (hProd : SliceSupBoundHolds → ReadingExistsHolds → ReadingEnergyHolds → ProductBoundHolds)
    (hProdPair : ProductBoundHolds → ProjectionHolds → TestPairingHolds → ReadingExistsHolds →
      ProductPairingHolds)
    (hProdSub : ReadingExistsHolds → ProductBoundHolds → ProductSubHolds)
    (hSpace : ReadingExistsHolds → GraphClosedHolds → SpaceModulusHolds)
    (hTime : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreePerturbationHolds →
      ReadingExistsHolds → TimeModulusHolds)
    (hLoc : TimeModulusHolds → SpaceModulusHolds → TranslationCriterionHolds → FreeInvHolds →
      ReadingExistsHolds → ReadingEnergyHolds → LocalCompactnessHolds)
    (hConv : ReadingExistsHolds → ProjectionHolds → TestPairingHolds → ExtendedConvectionHolds)
    (hInv : ExtendedConvectionHolds → ProjectionHolds → TestPairingHolds → TestDenseHolds →
      ExtendedInvarianceHolds)
    (hConvCont : ExtendedConvectionHolds → ExtendedConvectionContinuityHolds)
    (hData : ProjectionHolds → TestPairingHolds → ReadingEnergyHolds → ExtendedDataHolds)
    (hDataCont : ExtendedDataHolds → ExtendedDataContinuityHolds)
    (hCoer : ReadingExistsHolds → ReadingEnergyHolds → FreePerturbationHolds →
      ExtendedConvectionHolds → ExtendedDataHolds → TestPairingHolds → ExtendedCoerciveBorderedHolds)
    (hFrozen : SliceReadingHolds → FreeEquivariantHolds → ProjectionHolds → ExtendedConvectionHolds →
      ExtendedFrozenBridgeHolds)
    (hSup : FreeEnergyLocalHolds → ExtendedFrozenBridgeHolds → ExtendedInvarianceHolds →
      ExtendedDataHolds → ReadingEnergyHolds → ExtendedConvectionHolds → FreeEquivariantHolds →
      ExtendedSupBoundHolds)
    (hCpt : LocalCompactnessHolds → ExtendedConvectionHolds → FreeInvHolds → ReadingExistsHolds →
      ExtendedConvectionCompactHolds)
    (hBord : ExtendedConvectionCompactHolds → ExtendedCoerciveBorderedHolds →
      ExtendedInvarianceHolds → FreeEquivariantHolds → ExtendedDataHolds → FreeInvHolds →
      ExtendedBorderedInvertibleHolds)
    (hMetric : GraphClosedHolds → ReadingEnergyHolds → ExtendedHeldMetricHolds)
    (hMaps : ExtendedBorderedInvertibleHolds → ExtendedCoerciveBorderedHolds →
      ExtendedSupBoundHolds → ProductBoundHolds → ProductPairingHolds → ExtendedDataHolds →
      ExtendedInvarianceHolds → FreeEquivariantHolds → RowNormHolds → ExtendedHeldMapsToHolds)
    (hContr : ExtendedBorderedInvertibleHolds → ExtendedCoerciveBorderedHolds →
      ExtendedSupBoundHolds → ProductBoundHolds → ProductPairingHolds → ProductSubHolds →
      ExtendedDataHolds → ExtendedInvarianceHolds → FreeEquivariantHolds → RowNormHolds →
      ExtendedHeldContractsHolds)
    (hUniq : ContractionFixedPointHolds → ExtendedHeldMetricHolds → ExtendedHeldMapsToHolds →
      ExtendedHeldContractsHolds → ExtendedBorderedInvertibleHolds → FreeEquivariantHolds →
      ExtendedInvarianceHolds → ExtendedHeldExistsUniqueHolds)
    (hLim : PeriodContinuityHolds → LocalCompactnessHolds → ExtendedConvectionContinuityHolds →
      ExtendedDataContinuityHolds → ProductPairingHolds → ProductBoundHolds →
      ExtendedHeldMetricHolds → ExtendedInvarianceHolds → FreeInvHolds → ExtendedConvectionHolds →
      ExtendedDataHolds → ReadingExistsHolds → TestDenseHolds → ExtendedHeldLimitHolds)
    (hMult : ExtendedHeldLimitHolds → ExtendedHeldExistsUniqueHolds →
      ExtendedMultiplierContinuityHolds)
    (hAdjPair : ProjectionHolds → TestPairingHolds → TestDenseHolds → ExtendedAdjointPairingHolds)
    (hAdj : ExtendedAdjointPairingHolds → FreePerturbationHolds → ReadingExistsHolds →
      ReadingEnergyHolds → ExtendedConvectionHolds → ExtendedDataHolds → ProductPairingHolds →
      ProductBoundHolds → TestPairingHolds → ProjectionHolds → Held.AdjointEnclosureStatement →
      ExtendedAdjointEnclosureHolds)
    (hStiff : ExtendedStiffEnclosureHolds)
    (hZero : ExtendedHeldExistsUniqueHolds → ExtendedMultiplierContinuityHolds →
      ExtendedAdjointEnclosureHolds → ExtendedStiffEnclosureHolds → Held.TestSetZeroStatement →
      ExtendedExistsZeroHeldHolds)
    (hWeak : FreePerturbationHolds → ExtendedConvectionHolds → ExtendedDataHolds →
      ProductPairingHolds → ProductBoundHolds → TestPairingHolds → ExtendedHeldWeakEquationHolds)
    (hNonzero : ReadingEnergyHolds → ExtendedHeldNonzeroHolds)
    (hSigma : SliceReadingHolds → ExtendedHeldWeakEquationHolds → ExtendedHeldNonzeroHolds →
      ExtendedSigmaProfileOfHeldHolds) :
    ExtendedNormalOrbitHolds := by
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
  have c1 : ExtendedConvectionHolds := hConv r0 hProj hTest
  have c2 : ExtendedInvarianceHolds := hInv c1 hProj hTest hDense
  have d1 : ExtendedDataHolds := hData hProj hTest e1
  have b2 : ExtendedCoerciveBorderedHolds := hCoer r0 e1 f4 c1 d1 hTest
  have q4 : ExtendedSupBoundHolds := hSup f2 (hFrozen s1 f3 hProj c1) c2 d1 e1 c1 f3
  have l1 : LocalCompactnessHolds :=
    hLoc (hTime hProp g1 f1 f4 r0) (hSpace r0 hGraph) hTrans f1 r0 e1
  have rs : ExtendedBorderedInvertibleHolds := hBord (hCpt l1 c1 f1 r0) b2 c2 f3 d1 f1
  have m1 : ExtendedHeldMetricHolds := hMetric hGraph e1
  have u1 : ExtendedHeldExistsUniqueHolds :=
    hUniq hFix m1 (hMaps rs b2 q4 p1 p2 d1 c2 f3 hRow) (hContr rs b2 q4 p1 p2 p3 d1 c2 f3 hRow)
      rs f3 c2
  have lim : ExtendedHeldLimitHolds :=
    hLim (hPeriod hProp g1 f1) l1 (hConvCont c1) (hDataCont d1) p2 p1 m1 c2 f1 c1 d1 r0 hDense
  have a1 : ExtendedAdjointEnclosureHolds :=
    hAdj (hAdjPair hProj hTest hDense) f4 r0 e1 c1 d1 p2 p1 hTest hProj hHeldAdj
  have z1 : ExtendedExistsZeroHeldHolds := hZero u1 (hMult lim u1) a1 hStiff hHeldZero
  have w1 : ExtendedSigmaProfileOfHeldHolds := hSigma s1 (hWeak f4 c1 d1 p2 p1 hTest) (hNonzero e1)
  intro k d hd hw hm hg hs
  have hN : IsNormalExtendedCertificate d := ⟨hd, hw, hm, hg, hs⟩
  obtain ⟨q, hq, f, κ, hf, h0⟩ := z1 d hN
  obtain ⟨P, W, G, H, C, hσ⟩ := w1 d hd q hq f κ hf h0
  exact weakPeriodicSimilarityProfileExists_of_sigma hσ

theorem extended_certificate_orbit_of_nodes
    (hUnit : ExtendedUnitWeightHolds) (hAt : ExtendedAtProfileHolds)
    (hProj : ProjectionHolds) (hTest : TestPairingHolds) (hGraph : GraphClosedHolds)
    (hRead : GraphClosedHolds → ReadingExistsHolds) (hProp : PropagatorBoundHolds)
    (hDense : TestDenseHolds)
    (hTrans : TranslationCriterionHolds) (hFix : ContractionFixedPointHolds)
    (hRow : RowNormHolds)
    (hHeldZero : Held.TestSetZeroStatement) (hHeldAdj : Held.AdjointEnclosureStatement)
    (hEnergy : GraphClosedHolds → ReadingEnergyHolds)
    (hGradInv : PropagatorBoundHolds → GradInvHolds)
    (hFree : GradInvHolds → GraphClosedHolds → FreeInvHolds)
    (hLocal : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEnergyLocalHolds)
    (hEquiv : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds)
    (hPert : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreeEquivariantHolds →
      ReadingExistsHolds → ProjectionHolds → TestPairingHolds → FreePerturbationHolds)
    (hPeriod : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → PeriodContinuityHolds)
    (hSliceSup : GraphClosedHolds → SliceSupBoundHolds)
    (hSlice : FreeEnergyLocalHolds → ReadingExistsHolds → GraphClosedHolds → GradInvHolds →
      FreeInvHolds → SliceReadingHolds)
    (hProd : SliceSupBoundHolds → ReadingExistsHolds → ReadingEnergyHolds → ProductBoundHolds)
    (hProdPair : ProductBoundHolds → ProjectionHolds → TestPairingHolds → ReadingExistsHolds →
      ProductPairingHolds)
    (hProdSub : ReadingExistsHolds → ProductBoundHolds → ProductSubHolds)
    (hSpace : ReadingExistsHolds → GraphClosedHolds → SpaceModulusHolds)
    (hTime : PropagatorBoundHolds → GradInvHolds → FreeInvHolds → FreePerturbationHolds →
      ReadingExistsHolds → TimeModulusHolds)
    (hLoc : TimeModulusHolds → SpaceModulusHolds → TranslationCriterionHolds → FreeInvHolds →
      ReadingExistsHolds → ReadingEnergyHolds → LocalCompactnessHolds)
    (hConv : ReadingExistsHolds → ProjectionHolds → TestPairingHolds → ExtendedConvectionHolds)
    (hInv : ExtendedConvectionHolds → ProjectionHolds → TestPairingHolds → TestDenseHolds →
      ExtendedInvarianceHolds)
    (hConvCont : ExtendedConvectionHolds → ExtendedConvectionContinuityHolds)
    (hData : ProjectionHolds → TestPairingHolds → ReadingEnergyHolds → ExtendedDataHolds)
    (hDataCont : ExtendedDataHolds → ExtendedDataContinuityHolds)
    (hCoer : ReadingExistsHolds → ReadingEnergyHolds → FreePerturbationHolds →
      ExtendedConvectionHolds → ExtendedDataHolds → TestPairingHolds → ExtendedCoerciveBorderedHolds)
    (hFrozen : SliceReadingHolds → FreeEquivariantHolds → ProjectionHolds → ExtendedConvectionHolds →
      ExtendedFrozenBridgeHolds)
    (hSup : FreeEnergyLocalHolds → ExtendedFrozenBridgeHolds → ExtendedInvarianceHolds →
      ExtendedDataHolds → ReadingEnergyHolds → ExtendedConvectionHolds → FreeEquivariantHolds →
      ExtendedSupBoundHolds)
    (hCpt : LocalCompactnessHolds → ExtendedConvectionHolds → FreeInvHolds → ReadingExistsHolds →
      ExtendedConvectionCompactHolds)
    (hBord : ExtendedConvectionCompactHolds → ExtendedCoerciveBorderedHolds →
      ExtendedInvarianceHolds → FreeEquivariantHolds → ExtendedDataHolds → FreeInvHolds →
      ExtendedBorderedInvertibleHolds)
    (hMetric : GraphClosedHolds → ReadingEnergyHolds → ExtendedHeldMetricHolds)
    (hMaps : ExtendedBorderedInvertibleHolds → ExtendedCoerciveBorderedHolds →
      ExtendedSupBoundHolds → ProductBoundHolds → ProductPairingHolds → ExtendedDataHolds →
      ExtendedInvarianceHolds → FreeEquivariantHolds → RowNormHolds → ExtendedHeldMapsToHolds)
    (hContr : ExtendedBorderedInvertibleHolds → ExtendedCoerciveBorderedHolds →
      ExtendedSupBoundHolds → ProductBoundHolds → ProductPairingHolds → ProductSubHolds →
      ExtendedDataHolds → ExtendedInvarianceHolds → FreeEquivariantHolds → RowNormHolds →
      ExtendedHeldContractsHolds)
    (hUniq : ContractionFixedPointHolds → ExtendedHeldMetricHolds → ExtendedHeldMapsToHolds →
      ExtendedHeldContractsHolds → ExtendedBorderedInvertibleHolds → FreeEquivariantHolds →
      ExtendedInvarianceHolds → ExtendedHeldExistsUniqueHolds)
    (hLim : PeriodContinuityHolds → LocalCompactnessHolds → ExtendedConvectionContinuityHolds →
      ExtendedDataContinuityHolds → ProductPairingHolds → ProductBoundHolds →
      ExtendedHeldMetricHolds → ExtendedInvarianceHolds → FreeInvHolds → ExtendedConvectionHolds →
      ExtendedDataHolds → ReadingExistsHolds → TestDenseHolds → ExtendedHeldLimitHolds)
    (hMult : ExtendedHeldLimitHolds → ExtendedHeldExistsUniqueHolds →
      ExtendedMultiplierContinuityHolds)
    (hAdjPair : ProjectionHolds → TestPairingHolds → TestDenseHolds → ExtendedAdjointPairingHolds)
    (hAdj : ExtendedAdjointPairingHolds → FreePerturbationHolds → ReadingExistsHolds →
      ReadingEnergyHolds → ExtendedConvectionHolds → ExtendedDataHolds → ProductPairingHolds →
      ProductBoundHolds → TestPairingHolds → ProjectionHolds → Held.AdjointEnclosureStatement →
      ExtendedAdjointEnclosureHolds)
    (hStiff : ExtendedStiffEnclosureHolds)
    (hZero : ExtendedHeldExistsUniqueHolds → ExtendedMultiplierContinuityHolds →
      ExtendedAdjointEnclosureHolds → ExtendedStiffEnclosureHolds → Held.TestSetZeroStatement →
      ExtendedExistsZeroHeldHolds)
    (hWeak : FreePerturbationHolds → ExtendedConvectionHolds → ExtendedDataHolds →
      ProductPairingHolds → ProductBoundHolds → TestPairingHolds → ExtendedHeldWeakEquationHolds)
    (hNonzero : ReadingEnergyHolds → ExtendedHeldNonzeroHolds)
    (hSigma : SliceReadingHolds → ExtendedHeldWeakEquationHolds → ExtendedHeldNonzeroHolds →
      ExtendedSigmaProfileOfHeldHolds) :
    ExtendedCertificateHypothesis → WeakPeriodicSimilarityProfileExists := by
  intro h
  obtain ⟨k, d, hd⟩ := h
  exact extended_normal_orbit_of_nodes hProj hTest hGraph hRead hProp hDense hTrans hFix hRow
    hHeldZero hHeldAdj hEnergy hGradInv hFree hLocal hEquiv hPert hPeriod hSliceSup hSlice hProd
    hProdPair hProdSub hSpace hTime hLoc hConv hInv hConvCont hData hDataCont hCoer hFrozen hSup
    hCpt hBord hMetric hMaps hContr hUniq hLim hMult hAdjPair hAdj hStiff hZero hWeak hNonzero
    hSigma d.withUnitWeight.atProfile (hAt (hUnit hd)) rfl rfl rfl rfl

end Breakdown.Cert
