import Breakdown.FracCell.StCellBound
import Breakdown.FracCell.LocalFormBound
import Breakdown.FracCell.EnergyAssembly
import Breakdown.FracCell.StEnergyProof
import Breakdown.FracCell.FormulaRepresents
import Breakdown.FracCell.FormulaPolar
import Breakdown.FracCell.FormulaRowY
import Breakdown.FracCell.FormulaFar
import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.ShiftedRealReduction
import Breakdown.FracCell.ConjugateData
import Breakdown.FracCell.PlaneDeleted
import Breakdown.FracCell.RelationsHold
import Breakdown.FracCell.RelTrace
import Breakdown.FracCell.RelZeroMode
import Breakdown.FracCell.RelRadialSide
import Breakdown.FracCell.RelAxis
import Breakdown.FracCell.ShiftedParam
import Breakdown.FracCell.TrueParam
import Breakdown.FracCell.ParamRecover
import Breakdown.FracCell.StrainFace
import Breakdown.FracCell.FormulaSymm
import Breakdown.FracCell.CellMatrixBound
import Breakdown.FracCell.FormulaQuadratic
import Breakdown.FracCell.FormulaNear
import Breakdown.FracCell.FormulaSynthesis
import Breakdown.FracCell.EnergyPair
import Breakdown.FracCell.VelocityTail
import Breakdown.FracCell.OneVarTail
import Breakdown.FracCell.ModeRadialLine
import Breakdown.FracCell.ModeHeightLine
import Breakdown.FracCell.HeightProjBound
import Breakdown.FracCell.ProjCompose
import Breakdown.FracCell.LowStrainExpansion
import Breakdown.FracCell.LowVelocityExpansion
import Breakdown.FracCell.CellSharpBound
import Breakdown.FracCell.SharpCore
import Breakdown.FracCell.SharpTargetSquare
import Breakdown.FracCell.FormulaYLinear
import Breakdown.FracCell.GaugeShiftOf
import Breakdown.FracCell.SharpBoundCore
import Breakdown.FracCell.SharpCoefTail
import Breakdown.FracCell.MeshAssembly
import Breakdown.FracCell.MeshFar
import Breakdown.FracCell.MeshTail
import Breakdown.FracCell.MeshRowFar
import Breakdown.FracCell.MeshFluxRadial
import Breakdown.FracCell.MeshFluxHeight
import Breakdown.FracCell.SharpModeExpansionRegular
import Breakdown.FracCell.RowModeUnfolded
import Breakdown.FracCell.RowCircleSeries
import Breakdown.FracCell.SharpMxThirdSeries
import Breakdown.FracCell.SharpMxGradSeries
import Breakdown.FracCell.StrainFaceGuarded
import Breakdown.FracCell.AxisGradModeIntegrable
import Breakdown.FracCell.SharpYClassCrossAe
import Breakdown.FracCell.SharpMxWaveCross
import Breakdown.FracCell.LayoutRowValue
import Breakdown.FracCell.MeshStreamPlane
import Breakdown.FracCell.MeshRootZero
import Breakdown.FracCell.MeshEdgeJump
import Breakdown.FracCell.MeshMomentLinear

import Breakdown.FracCell.CanonicalInputs
import Breakdown.FracCell.EnergyClass
import Breakdown.FracCell.EnergyHeight
import Breakdown.FracCell.EnergyRadial
import Breakdown.FracCell.EnergyAngular
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.EnergyTop
import Breakdown.FracCell.RelRadialCoef
import Breakdown.FracCell.RelHeightCoef
import Breakdown.FracCell.RelTurn
import Breakdown.FracCell.RelHeightSide
import Breakdown.FracCell.RelSideSplit
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.RadialProjBound
import Breakdown.FracCell.StAngularMode
import Breakdown.FracCell.MeshFarRegular
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.AxisFlux
import Breakdown.FracCell.AxisModeIntegrable
import Breakdown.FracCell.ModeRectIntegrable
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ModeStripIntegrable
import Breakdown.FracCell.StrainFaceHeightTurn
import Breakdown.FracCell.CellFormBoundSharp
import Breakdown.FracCell.StrainFaceSideStripIntegrable
import Breakdown.FracCell.HeightModeIbp
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.ModeHeightParts
import Breakdown.FracCell.HeightModeWeak
import Breakdown.FracCell.ModeRadialWeakProof
import Breakdown.FracCell.RadialTrace
import Breakdown.FracCell.CylinderComp
import Breakdown.FracCell.ModeRadialPartsA
import Breakdown.FracCell.ModeRadialPartsF
import Breakdown.FracCell.RadialAxisCross
import Breakdown.FracCell.StrainFaceRadialTangent
import Breakdown.FracCell.StrainFaceRadialTurn
import Breakdown.FracCell.StrainFaceHeightNormal
import Breakdown.FracCell.CylinderFlux
import Breakdown.FracCell.CellDensityModes
import Breakdown.FracCell.MeshFarCoef
import Breakdown.FracCell.StripTrace
import Breakdown.FracCell.RadialMixedWeak
import Breakdown.FracCell.FieldModeSquare
import Breakdown.FracCell.RowCouplingSquare
import Breakdown.FracCell.ModeTurn
import Breakdown.FracCell.BasisEnergySum
import Breakdown.FracCell.ProjCoef
import Breakdown.FracCell.CornerIndependence
import Breakdown.FracCell.SharpYCharge
import Breakdown.FracCell.SharpYModeExpansion
import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.SharpYSharpField
import Breakdown.FracCell.SharpYChargeRegular
import Breakdown.FracCell.SharpCircleBound
import Breakdown.FracCell.SharpSupremumRegular
import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.ResolvedEnergy
import Breakdown.FracCell.UnresolvedEnergy
import Breakdown.FracCell.UnresolvedRowPoint
import Breakdown.FracCell.ClassRowSq
import Breakdown.FracCell.UnresolvedPairIntegrable
import Breakdown.FracCell.UnresolvedChargeFinite
import Breakdown.FracCell.UnresolvedRowClass
import Breakdown.FracCell.GaugeInvariance
import Breakdown.FracCell.SharpCrossYStrainSquare
import Breakdown.FracCell.SharpCrossYTargetSquare
import Breakdown.FracCell.SharpCrossYUnfolded
import Breakdown.FracCell.EnergyCrossIntegrable
import Breakdown.FracCell.SharpEnergyTailRegular
import Breakdown.FracCell.CircleSliceRegular
import Breakdown.FracCell.CircleSliceCoupling
import Breakdown.FracCell.DensitySlice
import Breakdown.FracCell.EnergyPairIntegrable
import Breakdown.FracCell.MeshDataAffine
import Breakdown.FracCell.SharpCircleMean
import Breakdown.FracCell.MeshSkeleton
import Breakdown.FracCell.MeshGaugeLinear
import Breakdown.FracCell.SharpDensityModeSeries
import Breakdown.FracCell.SharpEnergyModeSum
import Breakdown.FracCell.SharpYClassCross
import Breakdown.FracCell.SharpCircleStrain
import Breakdown.FracCell.SharpWaveSumBound
import Breakdown.FracCell.SharpEnergyStrainIdentity
import Breakdown.FracCell.SharpEnergyVelocityCoef
import Breakdown.FracCell.ClassCrossRegular
import Breakdown.FracCell.SharpEnergyVorticityIdentity
import Breakdown.FracCell.SharpCircleWave
import Breakdown.FracCell.SegmentIndependence
import Breakdown.FracCell.MeshStreamInd
import Breakdown.FracCell.MeshFluxHeight

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem cellBound_of_cellData_of (hF : CellFormBoundStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (Sp : CellSplit k N) (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R)
    (K₂ : Fin Sp.cellCount) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet)
    (hW4 : ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤
        4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  fun x hx ζ => le_trans (hW4 x hx ζ)
    (hF α hα₁ hα₂ c hc K S B Cl Sp R hd hd.weight_axisymmetric K₂ hcell hrows x hx ζ)

theorem velocityTail_of_open (hW : ModeRadialWeakStatement) (hG : ModeGradSquareStatement)
    (hV : ModeVelSquareStatement) (hI : CellFormula.HeightModeIbpStatement) (hR : RadialProjBoundStatement) :
    VelocityTailStatement :=
  velocityTail_of_leaves oneVarTailGood (modeRadialLine_of hW hG hV) hR hG (modeHeightLine_of hI hG hV)
    heightProjBound hV projCompose

theorem cellSharpBound_of_leaves (hT : SharpCoefTailStatement) (hB : SharpBoundStatement) :
    CellSharpBoundStatement :=
  cellSharpBound_of sharpTargetSquare (sharpCore_of_leaves sharpTargetSquare hT hB)

theorem cellSharpBound_of_open (hS : ModeSquareIntegrableStatement) (hRP : ModeRadialPartsStatement)
    (hHP : ModeHeightPartsStatement) (hW : ModeRadialWeakStatement) (hIbp : CellFormula.HeightModeIbpStatement)
    (hI : SharpRowIdentityStatement) (hC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement) :
    CellSharpBoundStatement :=
  cellSharpBound_of_leaves (sharpCoefTail_of hS hRP hHP hW hIbp) (sharpBound_of hI hC hY)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

theorem localFormBound_of_leaves (hR : ComponentRadialStatement) (hH : ComponentHeightStatement)
    (hA : ComponentAngularStatement) (hT : TopFormStatement) (hC : ClassFormStatement)
    (hP : PairFormStatement) (hX : CrossFormStatement) : LocalFormBoundStatement :=
  localFormBound_of (energyForm_of hR hH hA hT) hC hP hX

theorem localForm_le_of (hL : LocalFormBoundStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D]
    {k N : ℕ} (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (S : CellScalars) (Cl : CellClasses)
    {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (hm : modes = S.resolved) (hQ : Q = S.degHigh)
    (hq : q = S.degLow) (hK : IsCellBox K) (hB : IsCellBases K B)
    (hS : IsCellScalars α c K S) (hc : Breakdown.CellCert.Assembly.IsFormData α c)
    (hCl : ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
      Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
        |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : SteadyCert.IsSecondOrderField c.order v G H)
    (u : D → ℂ) (hu : Represents K B I c.order v G H u) (κ ζ : Fin k → ℝ) :
    quadFormValue (localForm c K B S Cl I) (dataVector u κ ζ) ≤
      CellScalars.localCellForm c K S Cl κ ζ v G H :=
  hL α c K B S Cl I hm hQ hq hK hB hS hc hCl v G H hv u hu κ ζ

theorem localFormBound_of_parts (hR : ComponentRadialStatement) (hH : ComponentHeightStatement)
    (hA : ComponentAngularStatement) (hT : TopFormStatement) (hC : ClassFormStatement)
    (hI : PairIntegrableStatement) (hLS : LowStrainExpansionStatement) (hLV : LowVelocityExpansionStatement)
    (hX : CrossFormStatement) : LocalFormBoundStatement :=
  localFormBound_of (energyForm_of hR hH hA hT) hC (pairForm_holds_of_parts hI hLS hLV) hX

theorem localFormBound_of_open (hR : ComponentRadialStatement) (hH : ComponentHeightStatement)
    (hA : ComponentAngularStatement) (hT : TopFormStatement) (hC : ClassFormStatement)
    (hI : PairIntegrableStatement) (hX : CrossFormStatement) : LocalFormBoundStatement :=
  localFormBound_of (energyForm_of hR hH hA hT) hC
    (pairForm_holds_of_parts hI lowStrainExpansion lowVelocityExpansion) hX

end Breakdown.CellCert.CellEnergy

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem exactFormula_represents_of_quadratic (hQ : FormulaQuadraticStatement) (h1 : NearIdentityStatement)
    (h2 : RowYIdentityStatement)
    (h3 : FarIdentityStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N slots : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N slots k) (hd : IsCellData α c K S B Cl R) (hfar : R.farSupport ⊆ lowSupport S)
    (hv : 0 < c.splitVisc) (F : CellFormulaInputs k N S) (hF : IsFormulaInputs α c K S B Cl R.rowSet F) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (F.exactFormula c K B R) (F.coordsOf x ζ c.splitVisc) ≤
        cellForm c K S R α B Cl x ζ / c.splitVisc :=
  exactFormula_represents_of polarization hQ h1 h2 h3 α hα₁ hα₂ c hc K S B Cl R hd hfar hv F hF

theorem exactFormulaBound_of_leaves (hQ : FormulaQuadraticStatement) (hN : NearIdentityStatement)
    (hS : SynthesisStatement) (hY : YCoefLinearStatement) : ExactFormulaBoundStatement := by
  intro α hα₁ hα₂ k N slots c hc K S B Cl R hd hfar hv F hF x hx ζ
  exact exactFormula_represents_of polarization hQ hN (rowYIdentity_of hS hY) farIdentity α hα₁ hα₂ c hc K S B
    Cl R hd hfar hv F hF x hx ζ

theorem shiftedRealReduction_of_plane (h : PlaneDeletedStatement) : ShiftedRealReductionStatement :=
  shiftedRealReduction_of conjugateData_holds h

theorem shiftedRealReduction_of_leaves (hS : SegmentIndependenceStatement) (hC : CornerIndependenceStatement) :
    ShiftedRealReductionStatement :=
  shiftedRealReduction_of conjugateData_holds (planeDeleted_of hS hC)

theorem relationsHold_of_leaves (h1 : RelRadialCoefStatement) (h2 : RelHeightCoefStatement)
    (h3 : RelTurnStatement) (h6 : ModeRadialWeakStatement) (h7 : RelHeightSideStatement)
    (h8 : AxisModeIntegrableStatement) (h9 : AxisFluxStatement) (h10 : RelStreamStatement)
    (h11 : RelSideSplitStatement) : RelationsHoldStatement :=
  relationsHold_of h1 h2 h3 relTrace_holds relZeroMode_holds (relRadialSide_of h6) h7 (relAxis_of h8 h9) h10 h11

theorem shiftedParam_of (h1 : TrueParamStatement) : ShiftedParamStatement :=
  shiftedParam_of_recover h1 paramRecover

theorem shiftedParam_of_relations (h : RelationsHoldStatement) : ShiftedParamStatement :=
  shiftedParam_of (trueParam_of h paramRecover)

theorem strainFace_of_leaves (hV : SideVelocityEvalStatement) (hG : SideGradientEvalStatement)
    (hRT : RadialTangentStatement) (hRU : RadialTurnStatement) (hHN : HeightNormalStatement)
    (hHU : HeightTurnStatement) (hTF : FaceTraceFreeStatement) : StrainFaceStatement :=
  strainFace_of hV hG hRT hRU hHN hHU hTF

theorem exactFormula_represents (h1 : NearIdentityStatement) (h2 : RowYIdentityStatement)
    (h3 : FarIdentityStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N slots : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N slots k) (hd : IsCellData α c K S B Cl R) (hfar : R.farSupport ⊆ lowSupport S)
    (hv : 0 < c.splitVisc) (F : CellFormulaInputs k N S) (hF : IsFormulaInputs α c K S B Cl R.rowSet F) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      Finite.quadValue (F.exactFormula c K B R) (F.coordsOf x ζ c.splitVisc) ≤
        cellForm c K S R α B Cl x ζ / c.splitVisc :=
  exactFormula_represents_of polarization formulaQuadratic h1 h2 h3 α hα₁ hα₂ c hc K S B Cl R hd hfar hv F hF

theorem exactFormulaBound_of_coefLinear (hY : YCoefLinearStatement) : ExactFormulaBoundStatement :=
  exactFormulaBound_of_leaves formulaQuadratic (nearIdentity_of synthesis hY) synthesis hY

theorem exactFormulaBound_holds : ExactFormulaBoundStatement :=
  exactFormulaBound_of_coefLinear yCoefLinear

theorem gaugeShiftOf_holds : GaugeShiftOfStatement :=
  gaugeShiftOf_of conjugateData_holds

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellMatrix_le_cellForm_of_coords_of (h1 : ExactFormulaBoundStatement) (h2 : CanonicalInputsValidStatement)
    (h3 : PlaneDeletedStatement) (h4 : GaugeShiftOfStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (Sp : CellSplit k N) (hS : ∀ x, IsAdmissible c x → ∀ i,
      Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i) (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ 4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ :=
  cellMatrix_le_cellForm_of_parts h1 h2 (shiftedRealReduction_of_plane h3) h4 α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC
    hC.param_conj_closed

theorem cellBound_of_coords (hF : CellFormBoundStatement) (h1 : ExactFormulaBoundStatement)
    (h2 : CanonicalInputsValidStatement) (h3 : PlaneDeletedStatement) (h4 : GaugeShiftOfStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_cellData_of hF α hα₁ hα₂ c hc K S B Cl Sp R hd K₂ hcell hrows
    (cellMatrix_le_cellForm_of_coords_of h1 h2 h3 h4 α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC)

theorem cellMatrix_le_cellForm_of_open (h2 : CanonicalInputsValidStatement) (hSeg : SegmentIndependenceStatement)
    (hCor : CornerIndependenceStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (Sp : CellSplit k N) (hS : ∀ x, IsAdmissible c x → ∀ i,
      Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i) (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ 4 * Real.pi * CellScalars.cellForm c K S R α B Cl x ζ :=
  cellMatrix_le_cellForm_of_parts exactFormulaBound_holds h2 (shiftedRealReduction_of_leaves hSeg hCor) gaugeShiftOf_holds α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC
    hC.param_conj_closed

theorem cellBound_of_open (hF : CellFormBoundStatement) (h2 : CanonicalInputsValidStatement)
    (hSeg : SegmentIndependenceStatement) (hCor : CornerIndependenceStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_cellData_of hF α hα₁ hα₂ c hc K S B Cl Sp R hd K₂ hcell hrows
    (cellMatrix_le_cellForm_of_open h2 hSeg hCor α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC)

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem farMajorant_of_open (hcoef : FarCoefStatement) (hcyl : CylinderCompStatement) : FarMajorantStatement :=
  farMajorant_of tailMajorant_holds hcoef hcyl

theorem rowFarFinite_closed : RowFarFiniteStatement := rowFarFinite_holds

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

theorem fluxStream_of_open (hC : CylinderFluxStatement) (hA : RadialAxisCrossStatement)
    (hI : StreamIndependenceStatement) (hH : FluxHeightStatement) : FluxStreamStatement :=
  fluxStream_of (fluxRadial_of hC hA hI) hH (streamPlane_of hI)

theorem meshCompatibility_of_slot (hK : MeshSkeletonSlotStatement) (hG : MeshGaugeLinearStatement)
    (hT : DataAffineStatement) : MeshCompatibilityStatement :=
  meshCompatibility_of hK meshRootZero meshEdgeJump hG (meshMomentLinear hG hT)

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem modeIntegrable_holds : ModeIntegrableStatement := by
  intro m v G H hs K hK n a
  exact ⟨CellAnalysis.LowEntry.Internal.modeVec_int K hK m n hs.velocity_six a,
    fun b => CellAnalysis.LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a b⟩

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

theorem localFormBound_of_modes (hT : RadialTraceStatement) (hW : HeightModeWeakStatement)
    (hC : CircleWeakStatement) (hI : PairIntegrableStatement) (hX : CrossFormStatement) : LocalFormBoundStatement :=
  localFormBound_of_open (componentRadial hT) (componentHeight hW)
    (componentAngular_of (angularFrame_of_circle hC) modeIntegrable_holds) (topForm_holds modeIntegrable_holds)
    classForm_holds hI hX

end Breakdown.CellCert.CellEnergy

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem relationsHold_of_modes (hRP : CellFormula.ModeRadialPartsStatement) (hIbp : HeightModeIbpStatement)
    (hA : AngularModeStatement) (hW : ModeRadialWeakStatement) (hAI : AxisModeIntegrableStatement)
    (hAF : AxisFluxStatement) (hS : ModeStripIntegrableStatement) (hF : CylinderFluxStatement)
    (hR : ModeRectIntegrableStatement) : RelationsHoldStatement :=
  relationsHold_of_leaves (relRadialCoef_of hRP) (relHeightCoef_of hIbp) (relTurn_of modeIntegrable_holds hA) hW
    (relHeightSide_of hIbp modeIntegrable_holds) hAI hAF (relStream_of hS hF) (relSideSplit_of_integrable hR)

theorem shiftedParam_of_modes (hRP : CellFormula.ModeRadialPartsStatement) (hIbp : HeightModeIbpStatement)
    (hA : AngularModeStatement) (hW : ModeRadialWeakStatement) (hAI : AxisModeIntegrableStatement)
    (hAF : AxisFluxStatement) (hS : ModeStripIntegrableStatement) (hF : CylinderFluxStatement)
    (hR : ModeRectIntegrableStatement) : ShiftedParamStatement :=
  shiftedParam_of_relations (relationsHold_of_modes hRP hIbp hA hW hAI hAF hS hF hR)

theorem canonicalInputsValid_of_open (hL : LayoutRowValueStatement) (hG : GaugeInvarianceStatement)
    (hLF : CellEnergy.LocalFormBoundStatement) (hSP : ShiftedParamStatement) (hSeg : SegmentIndependenceStatement)
    (hCor : CornerIndependenceStatement) (hSF : StrainFaceStatement) : CanonicalInputsValidStatement :=
  canonicalInputsValid_of hL hG hLF lowEntry_holds hSP (shiftedRealReduction_of_leaves hSeg hCor) hSF

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_parts (hF : CellFormBoundStatement) (hL : LayoutRowValueStatement)
    (hG : GaugeInvarianceStatement) (hLF : CellEnergy.LocalFormBoundStatement) (hSP : ShiftedParamStatement)
    (hSF : StrainFaceStatement) (hSeg : SegmentIndependenceStatement) (hCor : CornerIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_open hF (canonicalInputsValid_of_open hL hG hLF hSP hSeg hCor hSF) hSeg hCor α hα₁ hα₂ c hc Sp hS
    hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

theorem velocityTail_of_weak (hW : ModeRadialWeakStatement) (hI : CellFormula.HeightModeIbpStatement) :
    VelocityTailStatement :=
  velocityTail_of_open hW modeGradSquare modeVelSquare hI radialProjBound

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem relationsHold_of_core (hRP : CellFormula.ModeRadialPartsStatement) (hIbp : HeightModeIbpStatement)
    (hC : CellEnergy.CircleWeakStatement) (hW : ModeRadialWeakStatement) (hF : CylinderFluxStatement) :
    RelationsHoldStatement :=
  relationsHold_of_modes hRP hIbp (angularMode hC) hW axisModeIntegrable
    (axisFlux_of axisModeIntegrable hRP (angularMode hC)) modeStripIntegrable hF modeRectIntegrable

theorem shiftedParam_of_core (hRP : CellFormula.ModeRadialPartsStatement) (hIbp : HeightModeIbpStatement)
    (hC : CellEnergy.CircleWeakStatement) (hW : ModeRadialWeakStatement) (hF : CylinderFluxStatement) :
    ShiftedParamStatement :=
  shiftedParam_of_relations (relationsHold_of_core hRP hIbp hC hW hF)

theorem strainFace_of_core (hI : SideStripIntegrableStatement) (hRT : RadialTangentStatement)
    (hRU : RadialTurnStatement) (hHN : HeightNormalStatement) (hC : CellEnergy.CircleWeakStatement)
    (hTF : FaceTraceFreeStatement) : StrainFaceStatement :=
  strainFace_of_traces hI hRT hRU hHN (heightTurn_of_circle hI hC) hTF

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem cellSharpBound_of_modes (hRP : ModeRadialPartsStatement) (hHP : ModeHeightPartsStatement)
    (hW : ModeRadialWeakStatement) (hIbp : CellFormula.HeightModeIbpStatement) (hI : SharpRowIdentityStatement)
    (hC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement) : CellSharpBoundStatement :=
  cellSharpBound_of_open modeSquareIntegrable hRP hHP hW hIbp hI hC hY

theorem cellFormBound_of_open (hD : CellDensityModesStatement) (hRP : ModeRadialPartsStatement)
    (hHP : ModeHeightPartsStatement) (hW : ModeRadialWeakStatement) (hIbp : CellFormula.HeightModeIbpStatement)
    (hI : SharpRowIdentityStatement) (hC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement) :
    CellFormBoundStatement :=
  cellFormBound_of_sharp hD (cellSharpBound_of_modes hRP hHP hW hIbp hI hC hY)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_leaves (hD : CellDensityModesStatement) (hRPa : CellAnalysis.ModeRadialPartsStatement)
    (hHP : ModeHeightPartsStatement) (hW : ModeRadialWeakStatement) (hIbp : HeightModeIbpStatement)
    (hI : SharpRowIdentityStatement) (hUC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement)
    (hL : LayoutRowValueStatement) (hG : GaugeInvarianceStatement) (hT : CellEnergy.RadialTraceStatement)
    (hWh : CellEnergy.HeightModeWeakStatement) (hCi : CellEnergy.CircleWeakStatement)
    (hPI : CellEnergy.PairIntegrableStatement) (hX : CellEnergy.CrossFormStatement)
    (hRPf : CellFormula.ModeRadialPartsStatement) (hF : CylinderFluxStatement) (hSI : SideStripIntegrableStatement)
    (hRT : RadialTangentStatement) (hRU : RadialTurnStatement) (hHN : HeightNormalStatement)
    (hTF : FaceTraceFreeStatement) (hSeg : SegmentIndependenceStatement) (hCor : CornerIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_parts (cellFormBound_of_open hD hRPa hHP hW hIbp hI hUC hY) hL hG
    (CellEnergy.localFormBound_of_modes hT hWh hCi hPI hX) (shiftedParam_of_core hRPf hIbp hCi hW hF)
    (strainFace_of_core hSI hRT hRU hHN hCi hTF) hSeg hCor α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem velocityTail_holds : VelocityTailStatement :=
  velocityTail_of_weak modeRadialWeak CellFormula.heightModeIbp_holds

theorem farMajorant_of_coef (hcoef : FarCoefStatement) : FarMajorantStatement :=
  farMajorant_of tailMajorant_holds hcoef cylinderComp

theorem cellSharpBound_of_remaining (hI : SharpRowIdentityStatement) (hC : UnresolvedRowClassStatement)
    (hY : SharpYChargeStatement) : CellSharpBoundStatement :=
  cellSharpBound_of_modes modeRadialParts modeHeightParts modeRadialWeak CellFormula.heightModeIbp_holds hI hC hY

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem cylinderFlux_of_trace (hT : StripTraceStatement) : CylinderFluxStatement :=
  cylinderFlux_of modeStripIntegrable (angularMode CellEnergy.circleWeak) hT

theorem strainFace_of_remaining (hM : RadialMixedWeakStatement) (hTF : FaceTraceFreeStatement) :
    StrainFaceStatement :=
  strainFace_of_core sideStripIntegrable_holds radialTangent_holds radialTurn_holds
    (heightNormal_holds CellAnalysis.modeRadialWeak hM) CellEnergy.circleWeak hTF

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem fluxStream_of_stream (hT : StripTraceStatement) (hI : StreamIndependenceStatement)
    (hH : FluxHeightStatement) : FluxStreamStatement :=
  fluxStream_of_open (cylinderFlux_of_trace hT) radialAxisCross hI hH

theorem cellBound_of_remaining (hDS : DensitySliceStatement) (hI : SharpRowIdentityStatement)
    (hUC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement) (hL : LayoutRowValueStatement)
    (hG : GaugeInvarianceStatement) (hPI : CellEnergy.PairIntegrableStatement) (hX : CellEnergy.CrossFormStatement)
    (hT : StripTraceStatement) (hM : RadialMixedWeakStatement) (hTF : FaceTraceFreeStatement)
    (hSeg : SegmentIndependenceStatement) (hCor : CornerIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_parts (cellFormBound_of_sharp (cellDensityModes_of hDS) (cellSharpBound_of_remaining hI hUC hY)) hL hG
    (CellEnergy.localFormBound_of_modes CellEnergy.radialTrace CellEnergy.heightModeWeak CellEnergy.circleWeak hPI hX)
    (shiftedParam_of_core CellFormula.modeRadialParts heightModeIbp_holds CellEnergy.circleWeak
      CellAnalysis.modeRadialWeak (cylinderFlux_of_trace hT))
    (strainFace_of_remaining hM hTF) hSeg hCor α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem farMajorant_holds : FarMajorantStatement :=
  farMajorant_of tailMajorant_holds (farCoef cylinderComp) cylinderComp

theorem sharpRowIdentity_of_unfolded (hU : RowModeUnfoldedStatement) : SharpRowIdentityStatement :=
  sharpRowIdentity_of_parts (modeSquare_of fieldModeSquare_holds rowCouplingSquare_holds) hU modeTurn_holds
    basisEnergySum_holds projCoef_holds

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem cylinderFlux_holds : CylinderFluxStatement :=
  cylinderFlux_of_trace stripTrace_holds

theorem strainFace_of_trace (hTF : FaceTraceFreeStatement) : StrainFaceStatement :=
  strainFace_of_remaining radialMixedWeak_holds hTF

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem fluxStream_of_segment (hI : StreamIndependenceStatement) (hH : FluxHeightStatement) :
    FluxStreamStatement :=
  fluxStream_of_open cylinderFlux_holds radialAxisCross hI hH

theorem cellBound_of_final (hDS : DensitySliceStatement) (hU : RowModeUnfoldedStatement)
    (hUC : UnresolvedRowClassStatement) (hY : SharpYChargeStatement) (hL : LayoutRowValueStatement)
    (hG : GaugeInvarianceStatement) (hPI : CellEnergy.PairIntegrableStatement) (hX : CellEnergy.CrossFormStatement)
    (hTF : FaceTraceFreeStatement) (hSeg : SegmentIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_parts (cellFormBound_of_sharp (cellDensityModes_of hDS)
      (cellSharpBound_of_remaining (sharpRowIdentity_of_unfolded hU) hUC hY)) hL hG
    (CellEnergy.localFormBound_of_modes CellEnergy.radialTrace CellEnergy.heightModeWeak CellEnergy.circleWeak hPI hX)
    (shiftedParam_of_core CellFormula.modeRadialParts heightModeIbp_holds CellEnergy.circleWeak
      CellAnalysis.modeRadialWeak cylinderFlux_holds)
    (strainFace_of_trace hTF) hSeg cornerIndependence_holds α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem sharpEnergyTail_of_open (hP : ModeEnergySumStatement) (hSI : ModeStrainIdentityStatement)
    (hVI : ModeVorticityIdentityStatement) (hVC : ModeVelocityCoefStatement)
    (hR : EnergyTailRegularStatement) : SharpEnergyTailStatement :=
  sharpEnergyTail_of_parts hP
    (modeStrainCoef_of (resolvedEnergy_of_modeFacts modeSquareIntegrable modeRadialParts modeHeightParts)
      unresolvedEnergy hSI)
    (modeVorticityCoef_of (resolvedEnergy_of_modeFacts modeSquareIntegrable modeRadialParts modeHeightParts) hVI)
    hVC hR

theorem sharpSupremum_of_open (hS : SharpCircleStrainStatement) (hM : SharpCircleMeanStatement)
    (hW : SharpCircleWaveStatement) (hB : WaveSumBoundStatement) : SharpSupremumStatement :=
  sharpSupremum_of sharpCircleSquare_holds (sharpCircleBound_of hS (sharpCircleCoupling_of hM hW))
    (sharpSupremumRegular_of hB)

theorem sharpYCharge_of_open (hX : ModeExpansionRegularStatement) (hMS : ModeSeriesStatement)
    (hS : SharpCircleStrainStatement) (hM : SharpCircleMeanStatement) (hW : SharpCircleWaveStatement)
    (hB : WaveSumBoundStatement) (hC : SharpCrossStatement) (hK : ClassCrossStatement)
    (hP : ModeEnergySumStatement) (hSI : ModeStrainIdentityStatement) (hVI : ModeVorticityIdentityStatement)
    (hVC : ModeVelocityCoefStatement) (hR : EnergyTailRegularStatement) : SharpYChargeStatement :=
  sharpYCharge_of_leaves (modeExpansion hX) (densityRegular_of_series hMS) sharpField
    (sharpSupremum_of_open hS hM hW hB) hC hK chargeRegular (sharpEnergyTail_of_open hP hSI hVI hVC hR)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem densitySlice_holds : DensitySliceStatement :=
  densitySlice_of circleSliceRegular_holds circleSliceCoupling_holds

theorem unresolvedRowClass_holds : UnresolvedRowClassStatement :=
  unresolvedRowClass_of unresolvedRowPoint_holds unresolvedPairIntegrable_holds classRowSq_holds
    unresolvedChargeFinite_holds

theorem sharpEnergyTail_of_rest (hSI : ModeStrainIdentityStatement) (hVI : ModeVorticityIdentityStatement)
    (hVC : ModeVelocityCoefStatement) : SharpEnergyTailStatement :=
  sharpEnergyTail_of_open modeEnergySum_holds hSI hVI hVC (energyTailRegular_of_series modeSeries_holds)

theorem sharpSupremum_of_rest (hS : SharpCircleStrainStatement) (hW : SharpCircleWaveStatement)
    (hB : WaveSumBoundStatement) : SharpSupremumStatement :=
  sharpSupremum_of_open hS sharpCircleMean_holds hW hB

theorem sharpCrossSymm_of_rest (hX : WaveCrossRegularStatement) : SharpCrossSymmStatement :=
  sharpCross_of_leaves basisEnergySum_holds projCoef_holds fieldModeSquare_holds yTargetSquare_holds
    yStrainSquare_holds modeTurn_holds
    (sharpEnergy_of (sharpCoefTail_of modeSquareIntegrable modeRadialParts modeHeightParts modeRadialWeak
      CellFormula.heightModeIbp_holds))
    (yUnfolded_of_leaves fieldModeSquare_holds projCoef_holds yStrainSquare_holds
      (densityRegular_of_series modeSeries_holds) hX)

theorem sharpYCharge_of_rest (hX : ModeExpansionRegularStatement) (hS : SharpCircleStrainStatement)
    (hW : SharpCircleWaveStatement) (hB : WaveSumBoundStatement) (hC : SharpCrossStatement)
    (hK : ClassCrossStatement) (hSI : ModeStrainIdentityStatement) (hVI : ModeVorticityIdentityStatement)
    (hVC : ModeVelocityCoefStatement) : SharpYChargeStatement :=
  sharpYCharge_of_leaves (modeExpansion hX) (densityRegular_of_series modeSeries_holds) sharpField
    (sharpSupremum_of_rest hS hW hB) hC hK chargeRegular (sharpEnergyTail_of_rest hSI hVI hVC)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem meshCompatibility_of_rest (hK : MeshSkeletonSlotStatement) : MeshCompatibilityStatement :=
  meshCompatibility_of_slot hK meshGaugeLinear dataAffine

theorem cellBound_of_rest (hU : RowModeUnfoldedStatement) (hY : SharpYChargeStatement)
    (hL : LayoutRowValueStatement) (hTF : FaceTraceFreeStatement) (hSeg : SegmentIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_final densitySlice_holds hU unresolvedRowClass_holds hY hL gaugeInvariance_holds
    CellEnergy.pairIntegrable_holds CellEnergy.crossForm_closed hTF hSeg α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd
    C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem waveCrossRegular_of_expansion (h : ModeExpansionRegularStatement) : WaveCrossRegularStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx n hn m _
  obtain ⟨_, _, _, _, _, _, _, _, _, hW, _⟩ := h α ha1 ha2 c hc K S B Cl R hd hw x hx
  exact hW n hn m

theorem sharpCrossSymm_of_expansion (hX : ModeExpansionRegularStatement) : SharpCrossSymmStatement :=
  sharpCrossSymm_of_rest (waveCrossRegular_of_expansion hX)

theorem classCross_of_rest (hY : ClassProductSplitStatement) (hR : ClassCrossRegularStatement) : ClassCrossStatement :=
  classCross_of hY hR chargeRegular

theorem sharpYCharge_of_leafset (hX : ModeExpansionRegularStatement) (hS : SharpCircleStrainStatement)
    (hW : SharpCircleWaveStatement) (hB : WaveSumBoundStatement) (hC : SharpCrossStatement)
    (hY : ClassProductSplitStatement) (hR : ClassCrossRegularStatement) (hSI : ModeStrainIdentityStatement)
    (hVI : ModeVorticityIdentityStatement) (hVC : ModeVelocityCoefStatement) : SharpYChargeStatement :=
  sharpYCharge_of_rest hX hS hW hB hC (classCross_of_rest hY hR) hSI hVI hVC

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_leafset (hU : RowModeUnfoldedStatement) (hX : ModeExpansionRegularStatement)
    (hSS : SharpCircleStrainStatement) (hSW : SharpCircleWaveStatement) (hB : WaveSumBoundStatement)
    (hSC : SharpCrossStatement) (hY : ClassProductSplitStatement) (hR : ClassCrossRegularStatement)
    (hSI : ModeStrainIdentityStatement) (hVI : ModeVorticityIdentityStatement) (hVC : ModeVelocityCoefStatement)
    (hL : LayoutRowValueStatement) (hTF : FaceTraceFreeStatement) (hSeg : SegmentIndependenceStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_rest hU
    (sharpYCharge_of_leafset hX hSS hSW hB hSC hY hR hSI hVI hVC) hL hTF hSeg α hα₁ hα₂ c hc Sp hS hfree K₂ K S B
    Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem sharpEnergyTail_holds : SharpEnergyTailStatement :=
  sharpEnergyTail_of_rest modeStrainIdentity_holds modeVorticityIdentity_holds modeVelocityCoef_holds

theorem sharpSupremum_holds : SharpSupremumStatement :=
  sharpSupremum_of_rest sharpCircleStrain_holds sharpCircleWave_holds waveSumBound_holds

theorem classCross_of_productSplit (hY : ClassProductSplitStatement) : ClassCrossStatement :=
  classCross_of_rest hY classCrossRegular_holds

theorem sharpYCharge_of_final (hX : ModeExpansionRegularStatement) (hC : SharpCrossStatement)
    (hY : ClassProductSplitStatement) : SharpYChargeStatement :=
  sharpYCharge_of_leafset hX sharpCircleStrain_holds sharpCircleWave_holds waveSumBound_holds hC hY
    classCrossRegular_holds modeStrainIdentity_holds modeVorticityIdentity_holds modeVelocityCoef_holds

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem fluxStream_holds : FluxStreamStatement :=
  fluxStream_of_segment streamIndependence_holds fluxHeight

theorem meshCompatibility_holds : MeshCompatibilityStatement :=
  meshCompatibility_of_rest (meshSkeletonSlot_of streamIndependence_holds fluxStream_holds)

theorem cellBound_of_core (hU : RowModeUnfoldedStatement) (hX : ModeExpansionRegularStatement)
    (hSC : SharpCrossStatement) (hY : ClassProductSplitStatement) (hL : LayoutRowValueStatement)
    (hTF : FaceTraceFreeStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_rest hU (sharpYCharge_of_final hX hSC hY) hL hTF segmentIndependence_holds α hα₁ hα₂ c hc Sp hS
    hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem modeExpansionRegular_of_series (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) : ModeExpansionRegularStatement :=
  modeExpansionRegular_of modeSeries_holds hT hG hW

theorem sharpCrossSymm_of_series (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) : SharpCrossSymmStatement :=
  sharpCrossSymm_of_expansion (modeExpansionRegular_of_series hT hG hW)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_tail (hU : RowModeUnfoldedStatement) (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) (hSC : SharpCrossStatement) (hY : ClassProductSplitStatement)
    (hL : LayoutRowValueStatement) (hTF : FaceTraceFreeStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_core hU (modeExpansionRegular_of_series hT hG hW) hSC hY hL hTF α hα₁ hα₂ c hc Sp hS hfree K₂ K S
    B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem sharpCross_of_symm (h : SharpCrossSymmStatement) : SharpCrossStatement :=
  fun α h1 h2 _ _ c hc K S B Cl _ R hd hw x hx ζ => h α h1 h2 c hc hd.model_strain_symm K S B Cl R hd hw x hx ζ

theorem sharpCross_of_series (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) : SharpCrossStatement :=
  sharpCross_of_symm (sharpCrossSymm_of_series hT hG hW)

theorem sharpYCharge_of_series (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) (hY : ClassProductSplitStatement) : SharpYChargeStatement :=
  sharpYCharge_of_final (modeExpansionRegular_of_series hT hG hW) (sharpCross_of_series hT hG hW) hY

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_last (hU : RowModeUnfoldedStatement) (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) (hY : ClassProductSplitStatement) (hL : LayoutRowValueStatement)
    (hTF : FaceTraceFreeStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_tail hU hT hG hW (sharpCross_of_series hT hG hW) hY hL hTF α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R
    hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem sharpYCharge_of_cross (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) (hK : ClassCrossStatement) : SharpYChargeStatement :=
  sharpYCharge_of_rest (modeExpansionRegular_of_series hT hG hW) sharpCircleStrain_holds sharpCircleWave_holds
    waveSumBound_holds (sharpCross_of_series hT hG hW) hK modeStrainIdentity_holds modeVorticityIdentity_holds
    modeVelocityCoef_holds

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_cross (hU : RowModeUnfoldedStatement) (hT : ThirdSeriesStatement) (hG : GradSeriesStatement)
    (hW : ModeWaveRegularStatement) (hK : ClassCrossStatement) (hL : LayoutRowValueStatement)
    (hTF : FaceTraceFreeStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_rest hU (sharpYCharge_of_cross hT hG hW hK) hL hTF segmentIndependence_holds α hα₁ hα₂ c hc Sp hS
    hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

theorem rowModeUnfolded_holds : RowModeUnfoldedStatement :=
  rowModeUnfolded_of_circle fieldModeSquare_holds rowCouplingSquare_holds projCoef_holds rowCircleSeries_holds

theorem sharpYCharge_of_wave (hW : ModeWaveRegularStatement) (hK : ClassCrossStatement) : SharpYChargeStatement :=
  sharpYCharge_of_cross thirdSeries_holds gradSeries_holds hW hK

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem strainFace_holds : StrainFaceStatement :=
  strainFace_of_axis axisGradModeIntegrable_holds

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_wave (hW : ModeWaveRegularStatement) (hK : ClassCrossStatement) (hL : LayoutRowValueStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_parts (cellFormBound_of_sharp (cellDensityModes_of densitySlice_holds)
      (cellSharpBound_of_remaining (sharpRowIdentity_of_unfolded rowModeUnfolded_holds) unresolvedRowClass_holds
        (sharpYCharge_of_wave hW hK))) hL gaugeInvariance_holds
    (CellEnergy.localFormBound_of_modes CellEnergy.radialTrace CellEnergy.heightModeWeak CellEnergy.circleWeak
      CellEnergy.pairIntegrable_holds CellEnergy.crossForm_closed)
    (shiftedParam_of_core CellFormula.modeRadialParts heightModeIbp_holds CellEnergy.circleWeak
      CellAnalysis.modeRadialWeak cylinderFlux_holds)
    strainFace_holds segmentIndependence_holds cornerIndependence_holds α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd
    C hC hcell hrows

end Breakdown.CellCert.CellCoordinates

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula _root_.Breakdown.CellCert.Finite

theorem cellBound_of_waveRegular (hW : ModeWaveRegularStatement) (hL : LayoutRowValueStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_wave hW classCross_closed hL α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows


theorem cellBound_of_layoutRow (hL : LayoutRowValueStatement)
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_waveRegular modeWaveRegular_holds hL α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows


theorem cellBound_closed
    (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) (Sp : CellSplit k N)
    (hS : ∀ x, IsAdmissible c x → ∀ i, Sp.moment x (Sp.kappaSlot i) = x.2.2.2.1 i)
    (hfree : ∀ i j, Sp.freeMap (Sp.kappaSlot i) j = 0)
    (K₂ : Fin Sp.cellCount) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses)
    (R : CellRows N Sp.slots k) (hd : IsCellData α c K S B Cl R) (C : CellCoords k Sp.slots)
    (hC : IsCellCoords α c Sp K₂ K S B Cl R C) (hcell : Sp.cell K₂ =ᵐ[volume] K.solid)
    (hrows : ∀ a, Sp.rowCell a = K₂ ↔ a ∈ R.rowSet) :
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      quadValue (Sp.cellMatrix K₂) (Sp.stateOf x ζ) ≤ Sp.cellPart c α K₂ x ζ :=
  cellBound_of_layoutRow CellFormula.layoutRowValue_holds α hα₁ hα₂ c hc Sp hS hfree K₂ K S B Cl R hd C hC hcell hrows

end Breakdown.CellCert.CellCoordinates
