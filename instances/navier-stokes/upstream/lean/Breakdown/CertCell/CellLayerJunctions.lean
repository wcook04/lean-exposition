import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.CellLayerStatements
import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.CreditEvalStatements
import Breakdown.CertCell.AssemblyExteriorValueSets
import Breakdown.CertCell.ShapeLogPhase
import Breakdown.CertCell.ShapeOriginProfile
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineDeriv
import Breakdown.CertCell.ShapeSplineReflect
import Breakdown.CertCell.ShapeSplineConj
import Breakdown.CertCell.ShapeSplineAgree
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeJetReflect
import Breakdown.CertCell.ShapeJetConjReflect
import Breakdown.CertCell.ShapeJetStart
import Breakdown.CertCell.ShapeJetVanish
import Breakdown.CertCell.ShapeJetValid
import Breakdown.CertCell.ShapeClosureData
import Breakdown.CertCell.ShapeAngularFactor
import Breakdown.CertCell.ShapeTypeOneOff
import Breakdown.CertCell.ShapeTypeOneOrigin
import Breakdown.CertCell.ShapeTypeOneSmooth
import Breakdown.CertCell.ShapeTypeOneDecay
import Breakdown.CertCell.ShapeTypeTwoOff
import Breakdown.CertCell.ShapeTypeTwoOrigin
import Breakdown.CertCell.ShapeTypeTwoSmooth
import Breakdown.CertCell.ShapeTypeTwoDecay
import Breakdown.CertCell.ShapeSphericalDiv
import Breakdown.CertCell.ShapeKeyDivergence
import Breakdown.CertCell.ShapeKeyTime
import Breakdown.CertCell.ShapeKeyRotation
import Breakdown.CertCell.ShapeKeyFlip
import Breakdown.CertCell.ShapeKeyConj
import Breakdown.CertCell.ShapeFieldSmooth
import Breakdown.CertCell.ShapeFieldDiv
import Breakdown.CertCell.ShapeFieldWeak
import Breakdown.CertCell.ShapeFieldDecay
import Breakdown.CertCell.ShapeFieldClassClosed
import Breakdown.CertCell.ShapeFieldSecondDerivFlip
import Breakdown.CertCell.ShapeFieldModes
import Breakdown.CertCell.ShapeFieldExpandGrad
import Breakdown.CertCell.ShapeFieldExpansion
import Breakdown.CertCell.ShapeCompactSupport
import Breakdown.CertCell.ShapeActuator
import Breakdown.CertCell.ShapeMeasurable
import Breakdown.CertCell.ShapeSecondSymmetric
import Breakdown.CertCell.ShapeSecondSymmetricProof
import Breakdown.CertCell.ScalarPlaneMin
import Breakdown.CertCell.ModeDensityBridgeLinks
import Breakdown.CertCell.ClassSupportLinks
import Breakdown.CertCell.ModeOffLattice
import Breakdown.CertCell.HalfPlaneReduction
import Breakdown.CertCell.RotationAverage
import Breakdown.CertCell.SecondDerivEnergyIdentity
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor
import Breakdown.CertCell.ModeFlip
import Breakdown.CertCell.LabelArithmetic
import Breakdown.CertCell.ModeTermFlip
import Breakdown.CertCell.StretchFlip
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.PlaneDataFlipLinks
import Breakdown.CertCell.TraceFlip
import Breakdown.CertCell.TraceMatch
import Breakdown.CertCell.ModeHeightDerivative
import Breakdown.CertCell.StripMomentTrace
import Breakdown.CertCell.TraceHeight
import Breakdown.CertCell.StripDataFlipLinks
import Breakdown.CertCell.CornerDataFlipLinks
import Breakdown.CertCell.ScalarPlaneFlip
import Breakdown.CertCell.ScalarHeightDerivative
import Breakdown.CertCell.CornerFlip
import Breakdown.CertCell.CornerMatch
import Breakdown.CertCell.CornerTrace

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

theorem joinedSplineGradSlopeBound_closed : JoinedSplineGradSlopeBound :=
  joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth

theorem typeOneKeySmooth_closed : TypeOneKeySmooth :=
  typeOneKeySmooth_of_off_origin (typeOneKey_off_of angularFactor_contDiffOn)
    (fun P D κ σ hP hD hκ h1 => typeOneKey_origin joinedSplineSmooth joinedSplineGradSlopeBound_closed
      splineDerivatives_holds P D κ σ hP hD hκ h1)

theorem typeTwoKeySmooth_closed : TypeTwoKeySmooth :=
  typeTwoKeySmooth_of
    (fun P D κ σ hP hD hκ h2 => typeTwoKey_offOrigin_of joinedSplineSmooth splineDerivatives_holds
      joinedSplineGradSlopeBound_closed originProfileSmooth P D κ σ hP hD hκ h2)
    (fun P D κ σ hP hD hκ h0 => typeTwoKey_near_origin_of joinedSplineSmooth joinedSplineGradSlopeBound_closed
      P D κ σ hP hD hκ h0)

theorem framedDivergenceFormula_closed : FramedDivergenceFormula :=
  fun P κ σ U _y hP hy hU => complexDivergence_framedField_offAxis P hP κ σ U (Or.inr hy) hU

theorem keyDivergenceFree_closed : KeyDivergenceFree :=
  keyDivergenceFree_of framedDivergenceFormula_closed joinedSplineSmooth typeOneKeySmooth_closed
    typeTwoKeySmooth_closed

theorem fieldHarmonicExpansion_closed : FieldHarmonicExpansion :=
  fieldHarmonicExpansion_of_spans fun P D S hP hD hS hSy =>
    ⟨fieldSpan_of_keys P D S hD hS hSy,
      gradientSpan_of_keySmooth typeOneKeySmooth_closed typeTwoKeySmooth_closed P D S hP hD hS hSy⟩

theorem shapeParts_closed : ShapeParts where
  log_phase := logPhaseIsRadial
  origin_profile := originProfileSmooth
  spline_smooth := joinedSplineSmooth
  spline_slope_bound := joinedSplineGradSlopeBound_closed
  spline_derivatives := splineDerivatives_holds
  spline_reflection := splineReflection
  spline_conjugation := splineConjugation
  agreement_rules := splineAgreementRules
  jet_joined := jetSplineJoined
  jet_reflection := jetReflection
  jet_conj_reflection := jetConjReflection_of_jetReflection jetReflection
  jet_start := jetStartVanish
  jet_vanish := jetSplineVanishesFrom
  closure_valid := closureDataValid
  type_one_smooth := typeOneKeySmooth_closed
  type_two_smooth := typeTwoKeySmooth_closed
  type_one_decay := typeOneKeyDecay_of_smooth typeOneKeySmooth_closed
  type_two_decay := typeTwoKeyDecay_of_smooth typeTwoKeySmooth_closed
  key_divergence := keyDivergenceFree_closed
  key_time := keyTimeShift_holds
  key_rotation := keyRotation
  key_flip := keyFlip_holds
  key_conjugate := keyConjugate
  field_smooth := fieldJointSmooth_of typeOneKeySmooth_closed typeTwoKeySmooth_closed
  field_divergence := fieldDivergenceFree_of typeOneKeySmooth_closed typeTwoKeySmooth_closed keyDivergenceFree_closed
  field_weak_hessian := fieldWeakSecondDeriv_of typeOneKeySmooth_closed typeTwoKeySmooth_closed
  field_decay := fieldDecay_of (typeOneKeyDecay_of_smooth typeOneKeySmooth_closed)
    (typeTwoKeyDecay_of_smooth typeTwoKeySmooth_closed) typeOneKeySmooth_closed typeTwoKeySmooth_closed
  field_class := fieldClassInvariant_holds
  field_hess_flip := fieldSecondDerivFlip_holds
  field_modes := fieldModeFormula
  field_expansion := fieldHarmonicExpansion_closed
  compact_support := compactFieldSupport_holds
  actuator_shape := actuatorShape_of (fieldJointSmooth_of typeOneKeySmooth_closed typeTwoKeySmooth_closed)
    (fieldDecay_of (typeOneKeyDecay_of_smooth typeOneKeySmooth_closed)
      (typeTwoKeyDecay_of_smooth typeTwoKeySmooth_closed) typeOneKeySmooth_closed typeTwoKeySmooth_closed)
    compactFieldSupport_holds fieldClassInvariant_holds fieldModeFormula

theorem jetParts_closed : JetParts :=
  ⟨shapeParts_closed, givenJetDataValid⟩

theorem fieldSecondSymmetric_closed : FieldSecondSymmetric :=
  fieldSecondSymmetric_of_smooth typeOneKeySmooth_closed typeTwoKeySmooth_closed

end GivenShape

theorem modeDensityBridge_closed : Bridge.ModeDensityBridgeHolds :=
  Bridge.modeDensityBridge Bridge.halfPlaneReduction Bridge.rotationAverage Bridge.secondDerivEnergyIdentity
    Bridge.modeShiftRotate Bridge.modeShiftRotateTensor Bridge.modeFlip
    (Bridge.classSupport (Bridge.modeOffLattice Bridge.modeShiftRotate Bridge.modeShiftRotateTensor)
      Bridge.labelArithmetic)
    Bridge.labelArithmetic Bridge.modeTermFlip Bridge.stretchFlip

theorem velocitySixthIntegral_closed : Bridge.VelocitySixthIntegralHolds :=
  Bridge.velocitySixthIntegral ⟨4 / 3, sixthPowerGradientBound_four_thirds⟩

theorem modeHeightDeriv_closed : Bridge.ModeHeightDerivHolds :=
  Bridge.modeHeightDeriv Bridge.secondDerivEnergyIdentity

theorem planeDataFlip_closed : Bridge.PlaneDataFlipHolds :=
  Bridge.planeDataFlip Bridge.traceFlip Bridge.traceMatch modeHeightDeriv_closed Bridge.modeFlip

theorem stripDataFlip_closed : Bridge.StripDataFlipHolds :=
  Bridge.stripDataFlip planeDataFlip_closed Bridge.stripMomentTrace Bridge.traceHeight modeHeightDeriv_closed
    Bridge.secondDerivEnergyIdentity velocitySixthIntegral_closed

theorem cornerDataFlip_closed : Bridge.CornerDataFlipHolds :=
  Bridge.cornerDataFlip Bridge.modeFlip Bridge.modeShiftRotate Bridge.modeShiftRotateTensor Bridge.cornerFlip
    Bridge.cornerMatch Bridge.cornerTrace Bridge.traceHeight modeHeightDeriv_closed Bridge.secondDerivEnergyIdentity
    Bridge.traceFlip Bridge.traceMatch

theorem scalarPlaneFlip_closed : Bridge.ScalarPlaneFlipHolds :=
  Bridge.scalarPlaneFlip Bridge.traceFlip Bridge.traceMatch Bridge.scalarHeightDeriv

section Closure

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem cellJunctions_of_parts (hW : CellLayerParts) (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e) (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T)
    (hY : CellLayerEntryConditions D R T e Y) : CellJunctions D R e T := by
  obtain ⟨F, S, Hs, hSR, -⟩ := h.given_shape
  have hJR := GivenShape.givenJetEntry_of_scaled hW.scaled_jets D X F S hSR
  have hsymF := GivenShape.givenSecondSymmetric_of_jets GivenShape.jetParts_closed
    GivenShape.fieldSecondSymmetric_closed _ X F S.toJets hJR
  have hsym : ∀ σ y u w, D.givenHess σ y u w = D.givenHess σ y w u := by
    intro σ y u w
    rw [hSR.givenHess_eq]
    unfold GivenShape.knotZeroHess KnotZero.zeroOn
    split_ifs
    · rfl
    · exact hsymF σ y u w
  have hL : LayerJunctionFacts D X :=
    layerJunctionFacts_of_hypothesis GivenShape.jetParts_closed hW.scaled_jets D X R T e h hT
  have hLF := GivenShape.layerShapeFacts_of_scaled GivenShape.jetParts_closed hW.scaled_jets D X F S hSR
  have hadm := admissible_of_hypothesis hW.instance_parts D X R T e h hL
  obtain ⟨B, hB⟩ := hL.model_state
  obtain ⟨BT, hBT⟩ := h.bound_valueSets
  have hbm := GivenShape.boundsMeasurable_of_entry ScalarShape.chartBoundFacts D BT hBT
  obtain ⟨E, hE⟩ := h.continuum_conditions_given.coefficients
  have hCL : CoefficientLowerBounds D D.coercivity :=
    coefficientLowerBounds_of_entries D E hE h.box_uniform.c_eq hadm
  have hN : FormNegFinite D D.coercivity :=
    hW.form_negative D _ B (by have := h.azimuth_ge; omega) hCL hB
  have hact : ∀ i, ∃ S : Finset (ℤ × ℤ), Instance.ActuatorShapeFacts D.azimuthOrder S (D.cert.actuator i) :=
    fun i => ⟨X.actuatorModes i, hL.actuator_shape i⟩
  have hFR : Assembly.FieldRegular D :=
    { mesh_valid := h.mesh_valid
      azimuth_pos := by have := h.azimuth_ge; omega
      model_state := ⟨B, hB⟩
      model_harmonics := hLF.model_harmonics
      hessian_symmetric := hsym
      admissible := hadm
      bounds_measurable := hbm
      mode_class := h.mode_class
      actuators := hact }
  have hAR : Assembly.AssemblyRegular D R := ⟨hFR, hY.charges_regular,
    fun K g ι a b => ⟨(h.cell_conditions.pair_profile_regular K g ι).1 a b,
      (h.cell_conditions.pair_profile_regular K g ι).2.elim fun c hc => ⟨c, fun p hp => hc p hp a b⟩⟩, hY.leaves⟩
  have htf := hW.true_field D hFR
  have hAM : Assembly.AmplitudesMeasurable D :=
    ⟨fun q hq β => (hbm q hq).amplitudes_measurable β, fun q hq => (hbm q hq).sups_measurable⟩
  have hAC : Assembly.AssemblyConditions D R Y.assembly Y.coupling Y.rows :=
    { mesh_valid := h.mesh_valid
      cell_conditions := h.cell_conditions
      coefficient_bounds := hCL
      charges_regular := hY.charges_regular
      regular := hAR
      amplitudes_measurable := hAM
      admissible := hadm
      model_state := ⟨B, hB⟩
      row_values := ⟨_, h.instance_entry.rows.values⟩
      potential := hY.potential h.mesh_valid h.cell_conditions hLF.model_harmonics ⟨B, hB⟩ hFR.azimuth_pos
        hY.charges_regular hAR hFR.hessian_symmetric
      pairing := hY.pairing
      rows := hY.rows
      row_functionals := hY.row_functionals
      tails := hY.tails
      top_block := hY.top_block
      elimination := hY.elimination
      rows_gauge_blind := hY.rows_gauge_blind
      rows_head_blind := hY.rows_head_blind
      pressure_blind := hY.pressure_blind }
  have hPF : Assembly.PressureFacts D := ⟨⟨B, hB⟩, h.box_uniform.model_eq, h.mode_class, hL.flip_model, hact⟩
  obtain ⟨ep, hsur, -⟩ := h.pair_surrogate
  have hRec : PressureRecovered D := hW.pressure D hPF
  have hFlip : Assembly.ChosenPressureFlips D := hW.pressure_flip D hPF
  have hRF : Assembly.RowsMatchFields D R T Y.rows :=
    hW.rows_fields D R e T Y.rows h.mode_class h.mesh_valid h.cell_conditions hW.relations
      Bridge.stripMomentTrace Bridge.traceMatch Bridge.traceHeight Bridge.cornerTrace Bridge.cornerMatch
      modeHeightDeriv_closed stripDataFlip_closed cornerDataFlip_closed scalarPlaneFlip_closed hPF
      hY.gauge_keys hY.real_keys (hW.field_gauge D R T hY.gauge_keys.values) hY.gauge_transport hY.tree_rows
  have hstretch : Assembly.ExteriorStretchCharged D Y.exterior.charges :=
    hW.exterior_stretch D Y.exterior hFR htf ⟨B, hB⟩ hLF.model_harmonics
      (hW.exterior_values ScalarShape.chartBoundFacts D Y.farField hY.far_field_given)
      hY.exterior_stretch_const hY.exterior_cover
  refine
    { off_modes := hW.off_modes D R Y.offModes hAR htf hadm h.mesh_valid hY.off_mode_cover
      exterior := hW.exterior D Y.exterior hFR htf hadm h.mode_class h.mesh_valid hN h.box_uniform.c_eq
        hY.exterior_cover hstretch
      pressure := hRec
      cell_residual := hW.residual D R Y.assembly Y.coupling T Y.rows hN h.box_uniform.c_eq hsur.slack_weight_pos hAC
        (hW.states_in D R e T Y.rows h.mesh_valid h.cell_conditions hY.tree_rows hRF)
      tree_state := hW.tree_state D R e T Y.rows h.cell_conditions hY.gauge_keys hY.tree_rows
        (hW.rows_state D R T Y.rows hPF hRec hFlip hRF) hFlip }

theorem rowRestClause_of_parts (hW : CellLayerParts) (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e) (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T)
    (hY : CellLayerEntryConditions D R T e Y) :
    CoerciveWeak.RowRestClause D.cert D.pieces D.bounds D.modelHess D.coercivity D.pinWeight :=
  rowRestClause_of_cellHypothesis modeDensityBridge_closed hW.actuator_pairing hW.form_negative hW.initial_state
    hW.state_certificate hW.pair_shares hW.credit_leaves hW.support_radius hW.cell_form hW.row_shares
    hW.instance_parts ScalarShape.chartBoundFacts D X R T e h GivenShape.jetParts_closed hW.scaled_jets hT
    (cellJunctions_of_parts hW D X R T e h hT Y hY)

theorem extendedCoerciveClause_of_parts (hW : CellLayerParts) (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R) (e : ℝ)
    (h : CellHypothesis D X R T e) (hT : GivenShape.ShapeValuesFacts D) (Y : CellLayerEntries D R T)
    (hY : CellLayerEntryConditions D R T e Y)
    (hrad : ∀ j ∈ D.cert.adjointSet, 0 ≤ D.cert.radius j)
    (hwup : ∀ y, D.cert.weightFn y ≤ D.cert.weightMax)
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖D.cert.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (D.cert.actuatorBound ^ 2))
    {epsSup epsGradSup ratio : ℝ}
    (hm : ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q)
      D.cert.weightFn (D.cert.model q) (D.modelHess q) D.cert.weight epsSup epsGradSup ratio)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt D.cert.weight) ^ 2 / D.coercivity
      + ratio / (D.pieces 0).cμ) / Real.sqrt D.coercivity ≤ D.cert.coerciveL2)
    (hPin : Real.sqrt (D.pinWeight / D.coercivity) ≤ D.cert.coercivePin) :
    CoerciveWeak.ExtendedCoerciveClause D.cert := by
  have hL : LayerJunctionFacts D X :=
    layerJunctionFacts_of_hypothesis GivenShape.jetParts_closed hW.scaled_jets D X R T e h hT
  exact extendedCoerciveClause_of_cellLayer modeDensityBridge_closed hW.actuator_pairing hW.form_negative
    hW.initial_state hW.state_certificate hW.pair_shares hW.credit_leaves hW.support_radius hW.cell_form
    hW.row_shares hW.instance_parts ScalarShape.chartBoundFacts D X R T e h GivenShape.jetParts_closed
    hW.scaled_jets hT (cellJunctions_of_parts hW D X R T e h hT Y hY) hrad hwup
    (fun i => (hL.actuator_shape i).measurable) (fun i => (hL.actuator_shape i).periodic) hnorm hm hL2 hPin

end Closure

end CertCell

end Breakdown
