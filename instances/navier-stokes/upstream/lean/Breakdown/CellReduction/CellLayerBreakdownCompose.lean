import Breakdown.CellReduction.CellLayerBreakdown
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff ENNReal
open MeasureTheory Breakdown.CertCell Breakdown.CertCell.GivenShape

noncomputable section

namespace Breakdown

namespace CellLayerSystem

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem layerJunctionFacts_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) : LayerJunctionFacts D X := by
  exact layerJunctionFacts_of_hypothesis GivenShape.jetParts_closed cellLayerParts_closed.scaled_jets D X R T _
    h.cell h.shape_valueSets

theorem admissible_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) : ∀ q ∈ D.cert.params,
      CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.cert.model q)
        (D.modelHess q) D.cert.weight N.epsSup N.epsGradSup N.ratio := by
  have hL := layerJunctionFacts_of_parts h
  intro q hq
  rw [h.cell.box_uniform.model_eq q hq]
  exact Instance.isAdmissibleWeak_of_parts
    ((instanceConsequences_of_hypothesis cellLayerParts_closed.instance_parts D X R T _ h.cell hL).weights q hq).1
    (InstanceSplit.otherAdmissibleClauses_of_split (hL.shape_admissible q hq) (h.enclosure_numbers q hq))

theorem coerciveClause_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) : CoerciveWeak.ExtendedCoerciveClause D.cert :=
  extendedCoerciveClause_closed D X R T _ h.cell h.shape_valueSets Y h.entry_conditions h.certificate.radius_nonneg
    (fun y => (h.shape_valueSets.weight_const y).le.trans h.certificate.weight_le_weightMax)
    h.certificate.actuator_norm (admissible_of_parts h) h.coerciveL2_ge h.coercivePin_ge

theorem bridgeStanding_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) (b : ℝ)
    (hS : CellReduction.Instantiation.StructuralClauses ({ D.cert with decay := b } : ExtendedCertificateData k)) :
    CertReduction.BridgeStanding D.cert := by
  have hL := layerJunctionFacts_of_parts h
  obtain ⟨HB, hB⟩ := hL.model_state
  exact {
    weight_pos := h.shape_valueSets.weight_pos
    weightFn_const := funext h.shape_valueSets.weight_const
    model_state := fun q hq => ⟨D.givenHess, HB, by rw [h.cell.box_uniform.model_eq q hq]; exact hB⟩
    profile_smooth := fun q _ => hS.profile_smooth.comp (contDiff_const.prodMk contDiff_id)
    profile_decay := fun q hq => ⟨b, fun σ y => ⟨(hS.profile_decay q hq σ y).1, (hS.profile_decay q hq σ y).2.1⟩⟩
    adjoint_measurable := hS.adjoint_measurable }

theorem periodContinuous_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) :
    ContinuousOn D.cert.period D.cert.params := by
  have he := h.offset_expansion.period_eq
  have hp := h.shape_valueSets.period_pos
  refine (ContinuousOn.inv₀ (f := fun q : Fin k → ℝ => B.offset.freqCentre + ∑ i, q i * B.offset.freqTangent i)
    (continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul continuous_const)).continuousOn ?_).congr ?_
  · intro q hq
    rw [← he q hq]
    exact (one_div_pos.mpr (hp q hq)).ne'
  · intro q hq
    show D.cert.period q = (B.offset.freqCentre + ∑ i, q i * B.offset.freqTangent i)⁻¹
    rw [← he q hq, one_div, inv_inv]

theorem multiplierContinuous_of_parts {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) :
    ContinuousOn D.cert.multiplier D.cert.params := by
  have hcont : Continuous (fun q : Fin k → ℝ => fun l => B.offset.multCentre l + ∑ i, q i * B.offset.multTangent i l) :=
    continuous_pi fun l => continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul continuous_const)
  refine hcont.continuousOn.congr ?_
  intro q hq
  funext l
  exact h.offset_expansion.multiplier_eq q hq l

theorem shiftValid_of_parts (hSm : CertReduction.SmoothShiftPiecesHolds) {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k}
    (h : CellSystemCondition D X R T Y N B) (b : ℝ)
    (hS : CellReduction.Instantiation.StructuralClauses ({ D.cert with decay := b } : ExtendedCertificateData k)) :
    CertReduction.ShiftPiecesValid D.cert (shiftPiecesOfSystem B.profile D.given B.shift) := by
  have hL := layerJunctionFacts_of_parts h
  obtain ⟨HB, hB⟩ := hL.model_state
  have hIP := h.instantiation.1
  have hN := h.shift_numbers
  have hPf : ∀ q : Fin k → ℝ, ContDiff ℝ 1 (fun z : ℝ × Space => B.profile.field q z.1 z.2) := by
    intro q
    have h1 : ContDiff ℝ 1 (fun z : ℝ × Space => D.cert.profile q z.1 z.2) :=
      hS.profile_smooth.comp ((contDiff_const (c := q)).prodMk contDiff_id)
    rw [hIP.profile_eq q] at h1
    exact h1
  have hval : ∀ q ∈ D.cert.params, ∀ σ y, D.cert.profile q σ y - D.cert.model q σ y =
      ∑ a, (shiftPiecesOfSystem B.profile D.given B.shift).piece a q σ y := by
    intro q hq σ y
    rw [hIP.profile_eq q, h.cell.box_uniform.model_eq q hq]
    show _ = ∑ a : Fin 2, shiftPieceFields B.profile D.given a q σ y
    simp only [Fin.sum_univ_two, shiftPieceFields, Matrix.cons_val_zero, Matrix.cons_val_one]
    abel
  have hC1 : ∀ a, ∀ q ∈ D.cert.params,
      ContDiff ℝ 1 (fun z : ℝ × Space => (shiftPiecesOfSystem B.profile D.given B.shift).piece a q z.1 z.2) := by
    show ∀ a : Fin 2, _
    intro a q _
    fin_cases a
    · exact (hPf 0).sub hB.smooth
    · exact (hPf q).sub (hPf 0)
  obtain ⟨hgrad, hm1, hm2⟩ := hSm k D.cert _ (bridgeStanding_of_parts h b hS) hC1 (fun _ _ _ _ => rfl) hval
  exact {
    decompose := hval
    decompose_grad := hgrad
    piece_measurable := hm1
    pieceGrad_measurable := hm2
    supNum_nonneg := by
      show ∀ a : Fin 2, _
      intro a
      fin_cases a
      exacts [hN.centreSup_nonneg, hN.boxSup_nonneg]
    gradNum_nonneg := by
      show ∀ a : Fin 2, _
      intro a
      fin_cases a
      exacts [hN.centreGrad_nonneg, hN.boxGrad_nonneg]
    piece_sup := by
      show ∀ a : Fin 2, _
      intro a q hq σ y
      fin_cases a
      exacts [hN.centre_sup σ y, hN.box_sup q hq σ y]
    piece_grad := by
      show ∀ a : Fin 2, _
      intro a q hq σ
      fin_cases a
      exacts [hN.centre_grad σ, hN.box_grad q hq σ] }

theorem adjointPotentialFacts_of_parts (hPN : PotentialShape.PotentialPieces) {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k}
    (h : CellSystemCondition D X R T Y N B) :
    ∀ j ∈ D.cert.adjointSet, AdjointDefect.AdjointPotentialFacts D.cert j (B.adjointDefect j) := by
  intro j hj
  have hP := h.potential_entries
  obtain ⟨C₁, hC⟩ := PotentialShape.potentialData_of_series hPN (B.potentials.params j) (B.potentials.series j)
    (hP.params_valid j hj) (hP.series_valid j hj)
  obtain ⟨C₂, R₀, hpin⟩ := PotentialShape.pinData_of_entry hPN B.potentials.pins hP.pins_valid
  refine ⟨⟨C₁, ?_, ?_⟩, ⟨C₂, R₀, ?_⟩⟩
  · rw [hP.centre_eq j hj]
    exact hC
  · intro i hi
    rw [h.adjoint_links.fitted_empty j hj] at hi
    simp at hi
  · rw [h.cell.instance_entry.pins.pin_eq, ← hP.pinField_eq, hP.pins_eq j hj]
    exact hpin

theorem instantiationBounded_with_givenHess {D : CellLayerData k C nE nM} {R Pr Z}
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (h : CellReduction.Instantiation.InstantiationBounded D R Pr Z) :
    CellReduction.Instantiation.InstantiationBounded { D with givenHess := H } R Pr Z :=
  ⟨{ h.1 with }, { h.2.1 with }, { h.2.2 with }⟩

theorem offsetExpansion_with_givenHess {D : CellLayerData k C nE nM} {R Pr Z O}
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (h : CellReduction.Instantiation.IsOffsetExpansionEntry D R Pr Z O) :
    CellReduction.Instantiation.IsOffsetExpansionEntry { D with givenHess := H } R Pr Z O :=
  { h with }

theorem isExtendedCertificate_of_parts (hI : CellReduction.Instantiation.InstantiationHolds) (hO : CellReduction.Instantiation.OffsetClauseHolds)
    (hG : CertReduction.GapTransferBridgeHolds) (hF : CertReduction.FormShiftBridgeHolds) (hM : CertReduction.FrozenFormBridgeHolds)
    (hQ : CertReduction.AdjointQuadraticBridgeHolds) (hA : AdjointDefect.AdjointDefectBridgeHolds)
    (hAS : CellReduction.Instantiation.AdjointStructureHolds) (hSm : CertReduction.SmoothShiftPiecesHolds)
    (hPN : PotentialShape.PotentialPieces)
    {D : CellLayerData k C nE nM} {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R} {Y : CellLayerEntries D R T} {N : CoerciveNumbers}
    {B : ReductionEntries k} (h : CellSystemCondition D X R T Y N B) :
    ∃ b : ℝ, IsExtendedCertificate ({ D.cert with decay := b } : ExtendedCertificateData k) := by
  have hL := layerJunctionFacts_of_parts h
  have hIC := instanceConsequences_of_hypothesis cellLayerParts_closed.instance_parts D X R T _ h.cell hL
  have hc := h.certificate
  have hT := h.shape_valueSets
  obtain ⟨b, hS⟩ := hI D B.profile B.pressure B.adjointFields h.cell.instance_entry.symmetries hc.scale_ne_zero
    hIC.pin_measurable hIC.pin_finite h.instantiation
  obtain ⟨F, S, Hs, hSR, -⟩ := h.cell.given_shape
  have hJR := GivenShape.givenJetEntry_of_scaled cellLayerParts_closed.scaled_jets D X F S hSR
  have hOff := hO { D with givenHess := shapeHess F.params F.model } X F B.profile B.pressure B.adjointFields
    B.offset hc.scale_ne_zero (GivenShape.givenShapeEntry_of_jets GivenShape.jetParts_closed _ X F S.toJets hJR)
    (instantiationBounded_with_givenHess _ h.instantiation) (offsetExpansion_with_givenHess _ h.offset_expansion)
    hc.defect_l2 hc.adjoint_l2
  have hStruct := hAS D B.profile B.pressure B.adjointFields B.offset B.adjointDefect hc.scale_ne_zero
    h.instantiation h.offset_expansion.period_eq h.adjoint_links
  obtain ⟨HB, hB⟩ := hL.model_state
  have hw : D.cert.weightFn = fun _ => D.cert.weight := funext hT.weight_const
  have hstand := bridgeStanding_of_parts h b hS
  have hvalid := shiftValid_of_parts hSm h b hS
  have hGc : CertReduction.GapTransferBounded D.cert (shiftPiecesOfSystem B.profile D.given B.shift) :=
    ⟨hvalid, by
      show (∑ a : Fin 2, _) ≤ _
      rw [Fin.sum_univ_two]
      exact h.shift_numbers.gap_sum⟩
  have hFc : CertReduction.FormShiftBounded D.cert (shiftPiecesOfSystem B.profile D.given B.shift) :=
    ⟨hvalid, by
      show (∑ a : Fin 2, _) ≤ _
      rw [Fin.sum_univ_two]
      exact h.shift_numbers.shift_sum⟩
  exact ⟨b, {
    radius_nonneg := hc.radius_nonneg
    stiffRadius_nonneg := hc.stiffRadius_nonneg
    scale_ne_zero := hc.scale_ne_zero
    multiplierWeight_pos := hc.multiplierWeight_pos
    coerciveL2_nonneg := hc.coerciveL2_nonneg
    coercivePin_nonneg := hc.coercivePin_nonneg
    rowBound_nonneg := hc.rowBound_nonneg
    gapSize_nonneg := hc.gapSize_nonneg
    formShift_nonneg := hc.formShift_nonneg
    transfer_lt := hc.transfer_lt
    coerciveTotal_ge := hc.coerciveTotal_ge
    coerciveTotal_pos := hc.coerciveTotal_pos
    actuatorBound_nonneg := hc.actuatorBound_nonneg
    modelFormBound_nonneg := hc.modelFormBound_nonneg
    formBound_ge := hc.formBound_ge
    sizeBound_nonneg := hc.sizeBound_nonneg
    supBound_pos := hc.supBound_pos
    period_continuous := periodContinuous_of_parts h
    period_le := hc.period_le
    twist_pos := hc.twist_pos
    twist_mem := hc.twist_mem
    multiplier_continuous := multiplierContinuous_of_parts h
    actuator_norm := hc.actuator_norm
    defect_nonneg := hc.defect_nonneg
    defect_l2 := hc.defect_l2
    defect_rows := hc.defect_rows
    defect_le := hc.defect_le
    size := hc.size
    small_first := hc.small_first
    small_second := hc.small_second
    small_third := hc.small_third
    frame_unit := hc.frame_unit
    adjoint_l2 := hc.adjoint_l2
    adjointL2_nonneg := hc.adjointL2_nonneg
    adjointDefect_nonneg := hc.adjointDefect_nonneg
    adjointQuad_nonneg := hc.adjointQuad_nonneg
    adjoint_inclusion := hc.adjoint_inclusion
    stiffNorm_nonneg := hc.stiffNorm_nonneg
    stiff_norm := hc.stiff_norm
    stiff_offset := hc.stiff_offset
    stiff_inclusion := hc.stiff_inclusion
    nontrivial := hc.nontrivial
    target_continuous := hS.target_continuous
    profile_smooth := hS.profile_smooth
    profile_periodic := hS.profile_periodic
    profile_divergence := hS.profile_divergence
    profile_decay := hS.profile_decay
    profileSecondDeriv_measurable := hS.profileSecondDeriv_measurable
    profileSecondDeriv_periodic := hS.profileSecondDeriv_periodic
    profileSecondDeriv_weak := hS.profileSecondDeriv_weak
    profile_invariant := hS.profile_invariant
    pressureGrad_measurable := hS.pressureGrad_measurable
    pressureGrad_periodic := hS.pressureGrad_periodic
    pressureGrad_orthogonal := hS.pressureGrad_orthogonal
    adjoint_measurable := hS.adjoint_measurable
    adjoint_periodic := hS.adjoint_periodic
    rowField_measurable := hIC.rowField_measurable
    rowField_periodic := hIC.rowField_periodic
    rowField_finite := hIC.rowField_finite
    rowField_orthonormal := hIC.rowField_orthonormal
    rowWeight_nonneg := hIC.rowWeight_nonneg
    rowWeight_le := hIC.rowWeight_le
    actuator_invariant := hIC.actuator_invariant
    pin_measurable := hIC.pin_measurable
    pin_finite := hIC.pin_finite
    adjoint_offset := hOff
    gap_transfer := hG k D.cert _ hstand hGc
    form_shift := hF k D.cert _ hstand hFc
    frozen_form := hM k D.cert B.modelForm hstand h.frozen_form
    adjoint_quadratic := hQ k D.cert B.adjointQuad hstand h.adjoint_quadratic
    adjoint_defect := hA D.cert B.adjointDefect hw hT.weight_pos hStruct (adjointPotentialFacts_of_parts hPN h) h.adjoint_defect
    weight_pos := hT.weight_pos
    weightFn_measurable := by show Measurable D.cert.weightFn; rw [hw]; exact measurable_const
    weightFn_lower := fun y => (hT.weight_const y).ge
    weightFn_upper := fun y => (hT.weight_const y).le.trans hc.weight_le_weightMax
    weightFn_invariant := fun γ _ y => by show D.cert.weightFn (γ.1 y) = D.cert.weightFn y; rw [hT.weight_const, hT.weight_const]
    period_pos := hT.period_pos
    actuator_measurable := fun i => (hL.actuator_shape i).measurable
    actuator_periodic := fun i => (hL.actuator_shape i).periodic
    model_smooth := fun q hq => by show ContDiff ℝ 1 (fun z : ℝ × Space => D.cert.model q z.1 z.2); rw [h.cell.box_uniform.model_eq q hq]; exact hB.smooth
    model_periodic := fun q hq => by show IsTimePeriodic (D.cert.model q); rw [h.cell.box_uniform.model_eq q hq]; exact hB.periodic
    coercive := coerciveClause_of_parts h }⟩

theorem breakdownOnSpace_of_cell_system_condition_of_parts (hI : CellReduction.Instantiation.InstantiationHolds) (hO : CellReduction.Instantiation.OffsetClauseHolds)
    (hG : CertReduction.GapTransferBridgeHolds) (hF : CertReduction.FormShiftBridgeHolds) (hM : CertReduction.FrozenFormBridgeHolds)
    (hQ : CertReduction.AdjointQuadraticBridgeHolds) (hA : AdjointDefect.AdjointDefectBridgeHolds)
    (hAS : CellReduction.Instantiation.AdjointStructureHolds) (hSm : CertReduction.SmoothShiftPiecesHolds)
    (hPN : PotentialShape.PotentialPieces)
    (D : CellLayerData k C nE nM) (X : Instance.InstanceData k C nE nM) (R : CellCalculus.CellCalculusEntry D)
    (T : TreeEntry D R) (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) : BreakdownOnSpace := by
  obtain ⟨b, hb⟩ := isExtendedCertificate_of_parts hI hO hG hF hM hQ hA hAS hSm hPN h
  exact breakdownOnSpace_of_weak (extended_certificate_orbit_proved ⟨k, _, hb⟩)

end CellLayerSystem

end Breakdown
