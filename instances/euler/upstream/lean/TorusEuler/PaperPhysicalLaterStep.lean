import TorusEuler.PaperGenericWaveSwitchDepth
import TorusEuler.PaperGenericPhysicalResidual
import TorusEuler.PaperGenericPhysicalPressure
import TorusEuler.PaperPhysicalApproximationBounds
import TorusEuler.PaperPhysicalParentInputs
import TorusEuler.PaperPhysicalStepBudget

/-! Lemmas 5.8–5.10 for one finite hierarchy of a general truncated parent. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open ChildFlow InductiveEulerStage LocalizedAmplitude PhysicalApproximationData

noncomputable section

local notation "I(" T ")" => Icc (0 : ℝ) T
local notation "J(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

set_option maxHeartbeats 9000000 in
/-- One localized seed of the prescribed central wave serves every cutoff.
Each cutoff produces one hierarchy with all the estimates of Lemmas 5.8–5.10. -/
theorem exists_paper_physicalLaterStep :
    ∃ a bExp : ℕ, 30 ≤ a ∧ 1 ≤ bExp ∧
      ∃ (Γ : ℕ → ℝ) (oscCost meanCost : ℕ → ℕ → ℝ),
        (∀ depth, 1 ≤ Γ depth) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
          {T t₀ D freq : ℝ} {hT : 0 < T}
          {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          (hOdd : ∀ t ∈ I(T), Function.Odd (U t)) →
          (∀ t ∈ I(T), Function.Odd (momentumResidual I(T) U p t)) →
          ContDiffOn ℝ ∞ (Function.uncurry p) J(T) →
          (∀ t ∈ I(T), SpatiallyPeriodic (p t)) →
          (∀ t ∈ I(T), ∀ x, divergence (U t) x = 0) →
          0 ≤ t₀ → t₀ < T →
          ∀ {depth : ℕ}, 2 ≤ depth →
          let ell := (D ^ a)⁻¹
          let h := freq ^ (-1 / 2 : ℝ)
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖
          let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
          let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t
          ‖κ t₀ 0‖ = freq →
          CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          Γ depth * D ^ bExp * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          ∃ (Cseed : ℝ) (w : SeedOn M κ center t₀ T ell D Cseed)
            (reg : w.HierarchyRegularity 0 h)
            (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)),
            ∀ cutoff : PaperWaveCutoff t₀ T, ∃ cfg : PhysicalApproximationData d p depth,
              cfg.leading = PhysicalLeadingInput.ofPaperCutoff d w reg cutoff data.flow data.velocity_smooth
                data.velocity_periodic hOdd hAmp ∧
              PaperPhysicalApproximationBounds cfg t₀ D freq (Γ depth) bExp cutoff.value
                (cutoff.derivativeSize γ) center (oscCost depth) (meanCost depth) := by
  obtain ⟨R, C, e, hR, hC, hInputs⟩ := exists_physicalParentInputs
  obtain ⟨aHierarchy, b₀, haHierarchy, _, Clevel, Ctotal, _, hCtotal, hHierarchy⟩ :=
    exists_paper_hierarchy_depth_of_cutoff
  obtain ⟨aPrimary, Cprimary, _, hCprimary, hPrimary⟩ :=
    exists_parent_activationPrimary_phaseJetBound R hR
  obtain ⟨aLead, Clead, _, hClead, hLead⟩ := exists_parent_genericLeading_pressure_hessian_bound R hR
  let a := max aHierarchy (max aPrimary aLead)
  let r := 2 * a + b₀
  let aMean := a + 24 + e
  let bExp := paperPhysicalStepExponent a r aMean
  let L := stageCoframeOrderConstant C
  let Cfixed (depth : ℕ) := paperPhysicalLevelCostThrough (fun n => Ctotal n depth) 1
  have hL := stageCoframeOrderConstant_ge_one C hC
  have hCfixed (depth : ℕ) : 0 ≤ Cfixed depth := Finset.sum_nonneg fun j _ => hCtotal j depth
  have hCparent : 0 ≤ 3 * R 2 := mul_nonneg (by norm_num) (hR 2)
  have hΓexists (depth : ℕ) := exists_paperPhysicalStepBudget a r aMean depth C hC
    (zero_le_one.trans (hL 2)) (zero_le_one.trans (hL 2)) (hCfixed depth) (hCtotal 2 depth)
    hCprimary hClead hCparent
  choose Γ hBudget using hΓexists
  have ha : 30 ≤ a := haHierarchy.trans (le_max_left _ _)
  have hPrimaryRadius : aPrimary ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have hLeadRadius : aLead ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨a, bExp, ha, by dsimp only [bExp, paperPhysicalStepExponent]; omega,
    Γ, fun depth => paperPhysicalOscillationHolderCost depth (fun n => Ctotal n depth) L,
    fun depth => paperPhysicalMeanHolderCost depth (fun n => Ctotal n depth) L,
    fun depth => (hBudget depth 1 le_rfl).gamma_ge_one, ?_⟩
  intro U X p T t₀ D freq hT k center d data hOdd hOddRes hp hpper hDiv ht₀ htT depth hDepth
    ell h γ M κ hLaunch hCenter hγmax hSmall
  have hD : 1 ≤ D := one_le_two.trans data.scale_ge_two
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hf := data.frequency_ge_one
  have hfpos := zero_lt_one.trans_le hf
  let inputs := hInputs data ⟨ht₀, htT.le⟩ hLaunch a (by omega)
  let budget := hBudget depth D hD
  have hHierarchySmall := budget.hierarchySmall hD hf hSmall
  obtain ⟨Cseed, w, reg, hAmp, hBuild⟩ :=
    hHierarchy data hOdd hOddRes hp hpper ht₀ htT a (le_max_left _ _)
      hLaunch hCenter hγmax hHierarchySmall
  refine ⟨Cseed, w, reg, hAmp, ?_⟩
  intro cutoff
  obtain ⟨cfg, hLeading, hLevels⟩ := hBuild cutoff hDepth
  have props := cfg.assemble_of_parent hDepth data.flow data.velocity_smooth hp
    data.velocity_periodic hpper hOdd hDiv
  have hγ : ContinuousOn γ (Icc t₀ T) := (HasDerivWithinAt.continuousOn hCenter.amplitude).norm.const_mul _
  have hpos (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < γ t :=
    mul_pos (Real.rpow_pos_of_pos hfpos _) (norm_pos_iff.mpr (hCenter.nonzero t ht).2.1)
  let S := tsupport (periodizeCentered (radialEnvelope ell))
  have hS : IsClosed S := isClosed_tsupport _
  have hInactive : cfg.leading.Inactive t₀ S := by
    rw [hLeading]
    exact PhysicalLeadingInput.ofPaperCutoff_inactive d w reg cutoff data.flow data.velocity_smooth
      data.velocity_periodic hOdd hAmp hS (subset_tsupport _)
  have hInactiveOsc (t : ℝ) (ht : t ∈ I(T)) (hpre : t < t₀) :
      cfg.oscillation t = 0 :=
    funext fun x => (cfg.inactive (by omega : 1 ≤ depth) hS hInactive ht x (Or.inl hpre)).1
  let B (t : ℝ) (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  have hLoss : 1 ≤ D ^ r := one_le_pow₀ hD
  have hCfixed_le (n : ℕ) (hn : n ≤ 2) : Ctotal n depth ≤ Cfixed depth :=
    Finset.single_le_sum (fun j _ => hCtotal j depth) (Finset.mem_range.mpr (by omega))
  have hLevel (n : ℕ) (i : ℕ) (hi : i ∈ Finset.Icc 1 depth) :
      HierarchyLevelBound
        (actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch cfg.parentResidual
          freq (zero_le_one.trans hf) ell h hT ht₀ htT.le γ hγ hpos) freq (D ^ r) (Ctotal n depth) n i :=
    (hLevels n).2.2.2.2 i hi
  have hLevel₂ (n : ℕ) (hn : n ≤ 2) (i : ℕ) (hi : i ∈ Finset.Icc 1 depth) :
      HierarchyLevelBound
        (actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch cfg.parentResidual
          freq (zero_le_one.trans hf) ell h hT ht₀ htT.le γ hγ hpos) freq (D ^ r) (Cfixed depth) n i :=
    (hLevel n i hi).mono hf hLoss (hCfixed_le n hn)
  have hD₁ : 1 ≤ depth := by omega
  have hHolder := cfg.paperLemma58_profileHolder_of_levels hD₁ props (fun n => Ctotal n depth) L
    (fun n => hCtotal n depth) hL hD hf inputs.radius_pos reg.phase_pos inputs.radius_inverse.le
    rfl inputs.carrier budget.graphPower budget.hierarchyPower ht₀ htT.le γ hγ hpos hγmax
    hInactiveOsc hLevel B inputs.inverse_smooth inputs.coframe_readout inputs.coframe_smooth inputs.scaled_coframe
  have hOsc := cfg.oscillation_sup_of_actualLevels hD₁ hf hLoss (hCfixed depth) ht₀ htT.le γ hγ hpos hγmax
    hInactiveOsc (hLevel₂ 0 (by decide)) budget.oscillationSup
  have hγ₀ (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 ≤ γ t := (hpos t ht).le
  have hRadius : ell ≤ (D ^ aPrimary)⁻¹ :=
    inv_anti₀ (pow_pos hDpos _) (pow_le_pow_right₀ hD hPrimaryRadius)
  have hPrimary' := hPrimary (g := d) data.time_le_one data.scale_ge_two hRadius inputs.radius_inverse.le hf hLaunch
    data.flow data.velocity_smooth data.velocity_periodic data.deformation_le data.inverse_deformation_le
    inputs.velocity_jets hCenter w reg
  have hResidual := cfg.residual_holder_of_paperCutoff w reg cutoff data.flow data.velocity_smooth data.velocity_periodic
    hOdd hAmp hLeading hD hf (hL 2) (hCtotal 2 depth) hCprimary inputs.radius_inverse.le rfl inputs.carrier
    (inputs.scaled_coframe 2) (hLevels 2).2.2.2.1 hγ hPrimary' hγ₀ budget.residualTail budget.residualPrimary
  have hPeak (t : ℝ) (ht : t ∈ Icc t₀ T) : ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ) := by
    rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg hfpos.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hfpos _)).mpr (by
      simpa only [γ, mul_comm] using hγmax t ht)
  have hLeadPress : ∀ t ∈ I(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (cfg.leadingPressure t)) x v⟫_ℝ ≤
        ((Clead * D ^ (2 * a + 74)) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
    intro t ht x v
    unfold leadingPressure
    rw [hLeading]
    exact hLead hT data.time_le_one data.scale_ge_two hf hLeadRadius inputs.radius_inverse hLaunch inputs.carrier data.flow
      data.velocity_smooth data.velocity_periodic data.deformation_le data.inverse_deformation_le
      inputs.velocity_jets hPeak hCenter w reg cutoff t ht x v
  have hLeadCenter (t : ℝ) (ht : t ∈ Icc t₀ T) :
      fderiv ℝ (cfg.leadingVelocity t) 0 = cutoff.value t •
        InnerProductSpace.rankOne ℝ (center t) (labelWaveVector X 0 0 k t) := by
    unfold leadingVelocity
    rw [hLeading]
    exact SeedOn.genericLeading_parentGraph_center (seed := w) reg cutoff data.flow data.velocity_smooth
      data.velocity_periodic hOdd ht
  let Cjet := L 2 * D ^ (24 : ℕ)
  let CHigher := higherOscillatoryHessianPrefactor depth (Cfixed depth) (D ^ r) Cjet (D ^ a) D
  let CMean := (48 * ‖pressureHessianMultiplier‖ * (13824 * (((Finset.Icc 2 depth).card : ℝ) * Cfixed depth)) *
    (1 + 3 * R 2)) * D ^ (6 * r + 2 * aMean + 2)
  have hLevel₀ := hCfixed depth
  have hCjet : 0 ≤ Cjet := mul_nonneg (zero_le_one.trans (hL 2)) (pow_nonneg hDpos.le _)
  have hCHigher : 0 ≤ CHigher := by dsimp only [CHigher, higherOscillatoryHessianPrefactor]; positivity
  have hCMean : 0 ≤ CMean := by dsimp only [CMean]; positivity
  have hPressBounds := cfg.paperLemma59_higherMeanHessians hD₁ data.flow data.velocity_smooth
    data.velocity_periodic hDiv hS hInactive hD hf inputs.radius_pos rfl inputs.radius_inverse.le inputs.carrier
    (hCfixed depth) hCjet hCparent inputs.pressure_cost inputs.parent_gradient ht₀ htT.le γ hγ hpos hγmax
    inputs.pressure_coframe inputs.pressure_adjoint inputs.pressure_strain inputs.pressure_projection hLevel₂
  obtain ⟨hPressure, hCentral⟩ := cfg.paperLemma59_pressureCenter props hD₁ hf ht₀ htT.le hSmall
    data.flow data.velocity_smooth data.velocity_periodic hLeadCenter hCHigher hCMean budget.pressure
    hLeadPress hPressBounds.1 hPressBounds.2 γ hγ hpos hγmax inputs.radius_pos reg.phase_pos hD (hL 2)
    (hCfixed depth) inputs.radius_inverse.le rfl inputs.carrier
    (fun t ht j hj => inputs.scaled_coframe 2 t ht j (hj.trans (by decide)))
    (hLevel₂ 1 (by decide)) budget.center
  refine ⟨cfg, hLeading,
    ⟨props, hOsc, hHolder.1, hHolder.2, hResidual, hPressure, hCentral, ?_⟩⟩
  intro v hv hvPer hvDiv hvSize
  exact cfg.paperLemma510_flowBounds data.flow data.velocity_smooth data.velocity_periodic hDiv
    inputs.deformation inputs.coframe_smooth inputs.coframe_jets inputs.radius_pos inputs.radius_le_one
    inputs.radius_scale inputs.radius_inverse.le inputs.carrier hD hC hf rfl props hDepth
    (hCfixed depth) ht₀ htT.le hS hInactive γ hγ hpos hγmax hLevel₂
    budget.flowPower budget.flowConstant hSmall hv hvPer hvDiv hvSize

end

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
