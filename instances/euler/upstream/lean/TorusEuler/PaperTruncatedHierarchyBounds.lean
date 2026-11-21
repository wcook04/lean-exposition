import TorusEuler.HierarchySelectedRecurrence
import TorusEuler.HierarchySelectedDepthTail
import TorusEuler.HierarchyStageCoefficientCaps
import TorusEuler.HierarchyNormalizedTransverseBudget
import TorusEuler.ParentResidualEstimates
import TorusEuler.HierarchyPhysicalMeanBounds
import TorusEuler.ParentVelocityEstimates
import TorusEuler.HierarchyTwistedCoefficientNorms

/-! Uniform finite profile estimates for any physical truncated parent in §5. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T : ℝ} {k : Vec3} {hT : 0 < T}

local notation "I" => Icc 0 T
local notation "Labels" => UnitAddTorus (Fin 3)

/-- The band, flow, and residual hypotheses in §5.1 for the hierarchy of a
physical truncated parent. The parent geometry has already incorporated
the momentum-Hessian hypothesis. -/
structure TruncatedHierarchyParent (d : ParentGeometry hT U X k) (p : Pressure) (D freq : ℝ) where
  time_le_one : T ≤ 1
  scale_ge_two : 2 ≤ D
  frequency_ge_one : 1 ≤ freq
  flow : IsLabelFlowOn U X I
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry U) (I ×ˢ (univ : Set Vec3))
  velocity_periodic : ∀ t ∈ I, SpatiallyPeriodic (U t)
  deformation_le : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D
  inverse_deformation_le : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D
  velocity_gradient_le : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D
  mean_inverse_le : d.mean.inverse_bound ≤ D
  mean_strain_le : d.mean.strain_bound ≤ D
  torusVelocity : ℝ → C(Labels, Vec3)
  torusResidual : ℝ → C(Labels, Vec3)
  velocity_lift : ∀ t ∈ I, (fun x => torusVelocity t (toUnitTorus x)) = U t
  residual_lift : ∀ t ∈ I, ∀ x, torusResidual t (toUnitTorus x) = momentumResidual I U p t x
  velocity_band : ∀ t ∈ I, RealTorusFourierBand (2 * D) (torusVelocity t)
  residual_band : ∀ t ∈ I, RealTorusFourierBand (4 * D) (torusResidual t)
  residual_size : ∀ t ∈ I, ‖torusResidual t‖ ≤ freq ^ (-5 / 2 : ℝ)

namespace TruncatedHierarchyParent

open PhysicalApproximationData

/-- The standing physical bounds supply the truncated-parent inputs and
the endpoint mean geometry for a prescribed nonzero carrier. -/
theorem exists_of_physical_bounds {D freq : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 2 ≤ D) (hf : 1 ≤ freq) (hk : k ≠ 0)
    (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (I ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hp : ∀ t ∈ I, ∀ x, DifferentiableAt ℝ (gradient (p t)) x)
    (hF : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D)
    (hG : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D)
    (hM : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D)
    (hupper : ∀ t ∈ I, ∀ x v : Vec3,
      ⟪(fderiv ℝ (gradient (p t)) x - fderiv ℝ (momentumResidual I U p t) x) v, v⟫_ℝ ≤ ‖v‖ ^ 2)
    (u R : ℝ → C(Labels, Vec3))
    (hu : ∀ t ∈ I, (fun x => u t (toUnitTorus x)) = U t)
    (hR : ∀ t ∈ I, ∀ x, R t (toUnitTorus x) = momentumResidual I U p t x)
    (hUBand : ∀ t ∈ I, RealTorusFourierBand (2 * D) (u t))
    (hRBand : ∀ t ∈ I, RealTorusFourierBand (4 * D) (R t))
    (hRsize : ∀ t ∈ I, ‖R t‖ ≤ freq ^ (-5 / 2 : ℝ)) :
    ∃ d : ParentGeometry hT U X k, Nonempty (TruncatedHierarchyParent d p D freq) := by
  have hD₁ := one_le_two.trans hD
  obtain ⟨d, hInverse, hStrain⟩ := exists_parentGeometry_withBounds hT hX hk hU hper hp
    hD₁ (zero_le_one.trans hD₁) hG hM hupper
  exact ⟨d, ⟨⟨hT₁, hD, hf, hX, hU, hper, hF, hG, hM, hInverse.le, hStrain.le,
    u, R, hu, hR, hUBand, hRBand, hRsize⟩⟩⟩

/-- The parent's finite Fourier band controls all velocity jets at the
Bernstein scale, with constants independent of the parent. -/
theorem exists_velocityJetBounds :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T D freq : ℝ}
        {hT : 0 < T} {k : Vec3} {d : ParentGeometry hT U X k},
        TruncatedHierarchyParent d p D freq →
        ∀ n j, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ V n * D ^ j := by
  obtain ⟨V, hV, hVelocity⟩ := exists_parentVelocityJetBounds
  refine ⟨V, hV, ?_⟩
  intro U X p T D freq hT k d data n j hj hjn t ht x
  have hD := one_le_two.trans data.scale_ge_two
  have hD₀ := zero_le_one.trans hD
  rw [← data.velocity_lift t ht]
  apply hVelocity (data.torusVelocity t) hD ?_ ?_ n j hj hjn x
  · intro q hq
    apply data.velocity_band t ht q
    exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hD₀).trans_lt hq
  · intro x
    rw [data.velocity_lift t ht]
    exact data.velocity_gradient_le t ht x

private theorem ordered_power {D A B : ℝ} {q r : ℕ}
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hAB : A ≤ B) (hqr : q ≤ r) :
    A * D ^ q ≤ B * D ^ r :=
  mul_le_mul hAB (pow_le_pow_right₀ hD hqr) (pow_nonneg (zero_le_one.trans hD) _) (hA.trans hAB)

set_option maxHeartbeats 10000000 in
/-- The actual selected hierarchy has its measured recurrence and the
all-order tail for the physical assumptions of §5.1. The analytic costs
are chosen independently of the particular truncated parent and depth. -/
theorem exists_profileBounds_at_order :
    ∃ a₀ b₀ : ℕ, 30 ≤ a₀ ∧ 32 ≤ b₀ ∧
      ∀ seedCost : ℕ → ℝ, (∀ m, 0 ≤ seedCost m) →
      ∃ K : ℕ → ℝ, (∀ H, 1 ≤ K H) ∧
        ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T t₀ D freq : ℝ}
          {hT : 0 < T} {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
          (data : TruncatedHierarchyParent d p D freq) →
          ∀ (a : ℕ), a₀ ≤ a → ∀ (H : ℕ) {depth : ℕ}, 2 ≤ depth →
          ∀ (cfg : PhysicalApproximationData d p depth) (_lead : LeadingRelayData cfg)
            (ht₀ : 0 ≤ t₀) (htT : t₀ < T),
          let ℓ := (D ^ a)⁻¹;
          let h := freq ^ (-1 / 2 : ℝ);
          let L := D ^ (2 * a + b₀);
          let γ (t : ℝ) := freq ^ (3 / 4 : ℝ) * ‖center t‖;
          ‖labelWaveVector X 0 0 k t₀‖ = freq →
          LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (U t) (X 0 t 0))
            (fun t => labelWaveVector X 0 0 k t) center t₀ T D →
          cfg.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t),
          (∀ t ∈ Icc t₀ T, γ t ≤ 1) →
          (∀ r ≤ H,
            amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.V +
              freq * amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.p ≤
            seedCost r * D ^ (20 : ℕ) * freq ^ hierarchyOscExponent 1) →
          L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 →
          let s := actualMeasuredLevels cfg.operators cfg.profiles depth cfg.leading.completionSwitch
            cfg.parentResidual freq (zero_le_one.trans data.frequency_ge_one)
            ℓ h hT ht₀ htT.le γ hγ hpos;
          let C := hierarchyLevelConstant depth (K H) depth;
          HierarchyNormRecurrence s freq L (K H) depth H ∧
            ∀ n : ℕ, n + 1 + 3 * depth ≤ H →
              unweightedSeminorm False ℓ h n hT (cfg.operators.remainder cfg.profiles depth) ≤
                2 * K H * (C + 1) ^ 2 *
                  (1 + ((hierarchyTailPairs depth 0).card : ℝ) + 2 * ((hierarchyTailPairs depth 1).card : ℝ)) *
                    freq ^ hierarchyOscExponent (depth + 1) := by
  obtain ⟨V, hV, hVelocity⟩ := exists_velocityJetBounds
  obtain ⟨aT, CT, haT, hCT, hTrans⟩ := exists_physicalTransverseSolveBudget V hV
  obtain ⟨pM, aM, CM, hCM, hMean⟩ := exists_physicalSolvers_meanSeminormBound V hV
  obtain ⟨JR, hJR, hResidual⟩ := exists_parentResidualLabelJetBounds V hV
  obtain ⟨CC, hCC, hCaps⟩ := exists_parent_coefficientJetBounds V hV
  obtain ⟨CL, hCL, hRelay⟩ := exists_transportedWaveRelayCoefficientBudget V hV
  let a₀ := max aT aM
  let b₀ := pM + 32
  refine ⟨a₀, b₀, haT.trans (le_max_left _ _), by dsimp [b₀]; omega, ?_⟩
  intro seedCost hSeedCost
  let CR (r : ℕ) := (hierarchyAdmissibleWords (Fin 4) r).card * ∑ j ∈ Finset.range (r + 1), JR j
  let rowCost (r : ℕ) := InductiveEulerStage.stageCoefficientOrderConstant CC r
  let advCost (r : ℕ) := InductiveEulerStage.stageSourceCoefficientCost CC r
  let completionCost (r : ℕ) := completionOrderConstant r * (2 * CL r) ^ 2
  let relayCost (r : ℕ) := waveRelayOrderConstant r * (2 * CL r) ^ 2
  let orderCost (r : ℕ) := CT r + CM r + CR r + advCost r + completionCost r + relayCost r + seedCost r
  let K (H : ℕ) := 1 + ∑ r ∈ Finset.range (H + 1), orderCost r
  have hCR (r : ℕ) : 0 ≤ CR r :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => hJR j)
  have hCompletionCost (r : ℕ) : 0 ≤ completionCost r := by
    dsimp [completionCost, completionOrderConstant]
    positivity
  have hRelayCost (r : ℕ) : 0 ≤ relayCost r := by
    dsimp [relayCost, waveRelayOrderConstant]
    positivity
  have hOrderCost (r : ℕ) : 0 ≤ orderCost r :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hCT r) (hCM r)
      ) (hCR r)) (InductiveEulerStage.stageSourceCoefficientCost_nonneg CC hCC r)) (hCompletionCost r))
      (hRelayCost r)) (hSeedCost r)
  have hK (H : ℕ) : 1 ≤ K H := le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => hOrderCost r)
  refine ⟨K, hK, ?_⟩
  intro U X p T t₀ D freq hT k center d data a ha H depth hDepth cfg lead ht₀ htT
    ℓ h L γ hCarrier hCenter inactive hγ hpos hγle hSeed hsmall s C
  have hD := data.scale_ge_two
  have hD₁ : 1 ≤ D := one_le_two.trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD₁
  have hL : 1 ≤ L := one_le_pow₀ hD₁
  have hf := data.frequency_ge_one
  have hfpos := zero_lt_one.trans_le hf
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hh : 0 < h := Real.rpow_pos_of_pos hfpos _
  have ht₀T : t₀ ∈ Icc 0 T := ⟨ht₀, htT.le⟩
  have haT' : aT ≤ a := (le_max_left _ _).trans ha
  have haM' : aM ≤ a := (le_max_right _ _).trans ha
  have ha₃₀ : 30 ≤ a := haT.trans haT'
  have hRadius : ℓ ≤ (D ^ aT)⁻¹ :=
    inv_anti₀ (pow_pos hDpos _) (pow_le_pow_right₀ hD₁ haT')
  have hScale {j : ℕ} (hj : j ≤ a) : ℓ * D ^ j ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD₁ hj) hℓ.le).trans
      (inv_mul_cancel₀ (pow_ne_zero _ hDpos.ne')).le
  have hSquareExp : (15 + a) * 2 ≤ 2 * a + b₀ := by dsimp only [b₀]; omega
  have hMeanExp : pM + 2 + 2 * a ≤ 2 * a + b₀ := by dsimp only [b₀]; omega
  have hOscExp : 20 ≤ 2 * a + b₀ := by dsimp only [b₀]; omega
  have hH (r : ℕ) (hr : r ≤ H) :
      CT r ≤ K H ∧ CM r ≤ K H ∧ CR r ≤ K H ∧ advCost r ≤ K H ∧
        completionCost r ≤ K H ∧ relayCost r ≤ K H ∧ seedCost r ≤ K H := by
    have ht : orderCost r ≤ K H :=
      (Finset.single_le_sum (fun i _ => hOrderCost i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))).trans
        (le_add_of_nonneg_left zero_le_one)
    have h₁ := hCT r
    have h₂ := hCM r
    have h₃ := hCR r
    have h₄ := InductiveEulerStage.stageSourceCoefficientCost_nonneg CC hCC r
    have h₅ := hCompletionCost r
    have h₆ := hRelayCost r
    have h₇ := hSeedCost r
    dsimp only [orderCost, advCost] at ht ⊢
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hVel := hVelocity data
  have hG (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      d.inverse.val.val.val (t,x,0) = fderiv ℝ (X t 0) (X 0 t x) :=
    d.inverse_value (t,x,0) ⟨ht, mem_univ _⟩
  have hκ (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      d.covector.val.val.val (t,x,0) = labelWaveVector X 0 x k t :=
    d.covector_value (t,x,0) ⟨ht, mem_univ _⟩
  have hJets := hCaps hT data.time_le_one hD₁ data.flow data.velocity_smooth data.velocity_periodic
    data.deformation_le data.inverse_deformation_le hVel k hfpos ht₀T hCarrier
  let rowCap (r : ℕ) := rowCost r * D ^ (a + 1)
  let relayCap (r : ℕ) := 2 * CL r * D ^ (15 + a)
  have hRow (r : ℕ) (i : Fin 3) : unweightedSeminorm False ℓ h r hT
      (scaledCoframeRowProfile ℓ d.inverse i) ≤ rowCap r := by
    refine (unweightedSeminorm_scaledCoframeRowProfile_le_of_parent_power_bound
      (n := r) (h := h) (D := D) (L := 1) (q := 7) (p := 1) (C := CC) hT d.inverse
      d.mean.inverse_independent hℓ.le hDpos.le zero_le_one (hScale (by omega : 7 ≤ a))
      (fun j _ => hCC j) ?_ i).trans_eq ?_
    · intro t ht j _ x
      simpa only [hG t ht, mul_one] using (hJets j t ht x).2.1
    · have he : ℓ⁻¹ = D ^ a := inv_inv _
      dsimp only [rowCap, rowCost, InductiveEulerStage.stageCoefficientOrderConstant]
      rw [he, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hDpos.le _), mul_one, pow_one, pow_succ]
      ring
  have hFast (r : ℕ) : unweightedSeminorm False ℓ h r hT (scaledPhaseCoefficientProfile h d.covector) ≤
      rowCost r * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ) := by
    refine unweightedSeminorm_scaledPhaseCoefficient_le_of_normalizedJets hT d.covector
      d.oscillation.covector_independent hℓ.le hDpos.le (hScale (by omega : 7 ≤ a)) hfpos rfl
      r CC (fun j _ => hCC j) ?_
    intro j _ t ht x
    simpa only [hκ t ht] using (hJets j t ht x).2.2.2.2.1
  have hSource (r : ℕ) (hr : r ≤ H) :
      2 * (3 * hierarchyQuadraticConstant (Fin 4) r ^ 2 * rowCap r) ≤ K H * L ∧
      (2 * hierarchyQuadraticConstant (Fin 4) r ^ 2) *
          unweightedSeminorm False ℓ h r hT (scaledPhaseCoefficientProfile h d.covector) ≤
        K H * L * freq ^ (3 / 2 : ℝ) := by
    let Q := hierarchyQuadraticConstant (Fin 4) r
    have hRowCost : 0 ≤ rowCost r := InductiveEulerStage.stageCoefficientOrderConstant_nonneg CC hCC r
    have hAdv := InductiveEulerStage.stageSourceCoefficientCost_nonneg CC hCC r
    have hAdvK := (hH r hr).2.2.2.1
    constructor
    · calc
        _ = advCost r * D ^ (a + 1) := by dsimp [advCost, rowCap, rowCost, InductiveEulerStage.stageSourceCoefficientCost]; ring
        _ ≤ _ := ordered_power hD₁ hAdv hAdvK (by omega)
    · have hA : 2 * Q ^ 2 * rowCost r ≤ K H := by
        refine (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 6 by norm_num) (sq_nonneg Q)) hRowCost).trans ?_
        exact hAdvK
      calc
        _ ≤ (2 * Q ^ 2) * (rowCost r * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hFast r) (by positivity)
        _ = (2 * Q ^ 2 * rowCost r) * D ^ (2 : ℕ) * freq ^ (3 / 2 : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (ordered_power hD₁ (by positivity) hA (by omega))
          (Real.rpow_nonneg hfpos.le _)
  have hWidth : ‖ℓ⁻¹‖ ≤ D ^ a := by
    rw [show ℓ⁻¹ = D ^ a from inv_inv _, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hDpos.le _)]
  have hCoefficient (r : ℕ) :=
    (hRelay hT data.time_le_one hD₁ data.flow data.velocity_smooth data.velocity_periodic
      data.deformation_le data.inverse_deformation_le hVel hfpos ht₀T hCarrier
      d.inverse d.strain d.covector hG
      (fun t ht x => d.strain_value (t,x,0) ⟨ht, mem_univ _⟩) hκ
      (Icc_subset_Icc_left ht₀) (h := h) hℓ.le (hScale (by omega : 16 ≤ a)) r).absorb_inverse_width
        hD₁ (hCL r) hWidth
  have hComplete (r : ℕ) (hr : r ≤ H) : completionOrderConstant r * relayCap r ^ 2 ≤ K H * L := by
    calc
      _ = completionCost r * D ^ ((15 + a) * 2) := by
        dsimp only [relayCap]
        rw [mul_pow, ← pow_mul]
        simp only [completionCost, mul_assoc]
      _ ≤ _ := ordered_power hD₁ (hCompletionCost r) (hH r hr).2.2.2.2.1 hSquareExp
  have hRelayCap (r : ℕ) (hr : r ≤ H) : waveRelayOrderConstant r * relayCap r ^ 2 ≤ K H * L := by
    calc
      _ = relayCost r * D ^ ((15 + a) * 2) := by
        dsimp only [relayCap]
        rw [mul_pow, ← pow_mul]
        simp only [relayCost, mul_assoc]
      _ ≤ _ := ordered_power hD₁ (hRelayCost r) (hH r hr).2.2.2.2.2.1 hSquareExp
  have hRes (r : ℕ) (hr : r ≤ H) :
      unweightedSeminorm False ℓ h r hT cfg.parentResidual ≤ K H * freq ^ hierarchyMeanExponent 2 := by
    let A := freq ^ (-5 / 2 : ℝ)
    have hA : 0 ≤ A := Real.rpow_nonneg hfpos.le _
    let R (t : Icc (0 : ℝ) T) (a : Vec3) := data.torusResidual t (toUnitTorus (X 0 t a))
    have hRaw := hResidual hT data.time_le_one hD₁ hA data.flow data.velocity_smooth data.velocity_periodic
      data.deformation_le data.inverse_deformation_le
      (fun n _ j hj => hVel n j (by omega)) data.torusResidual data.residual_size data.residual_band
    have hval (t : Icc (0 : ℝ) T) (x : Vec3 × ℝ) :
        cfg.parentResidual.val.val.val (t,x) = R t x.1 :=
      (cfg.parentResidual_value (t,x) ⟨t.property, mem_univ _⟩).trans
        (data.residual_lift t t.property (X 0 t x.1)).symm
    have hSmooth (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (R t) := (hRaw t t.property).1
    have hcap := HierarchyRelayCoefficientJets.of_parent_power_bound (h := h) (q := 6) (n := r)
      hℓ.le hDpos.le hA (hScale (by omega : 6 ≤ a)) hSmooth
      (fun j _ => hJR j) (fun t j _ x => (hRaw t t.property).2 j x)
    calc
      _ ≤ CR r * A := (unweightedSeminorm_le_of_labelCoefficientJets hT ℓ h r cfg.parentResidual
        R hval hcap).trans_eq (by simp only [CR, mul_assoc])
      _ ≤ _ := by
        have he : hierarchyMeanExponent 2 = -5 / 2 := by norm_num [hierarchyMeanExponent]
        rw [he]
        exact mul_le_mul_of_nonneg_right (hH r hr).2.2.1 hA
  have hSeed' (r : ℕ) (hr : r ≤ H) :
      amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.V +
        freq * amplitudeSeminorm False ℓ h r hT ht₀ htT.le γ hγ hpos cfg.leading.output.p ≤
      K H * L * freq ^ hierarchyOscExponent 1 :=
    (hSeed r hr).trans (mul_le_mul_of_nonneg_right
      (ordered_power hD₁ (hSeedCost r) (hH r hr).2.2.2.2.2.2 hOscExp)
      (Real.rpow_nonneg hfpos.le _))
  have hSolveMean (r : ℕ) (hr : r ≤ H) (F : HierarchyTwistedProfile T k Vec3)
      (hF : cfg.operators.average F = F) :
      unweightedSeminorm False ℓ h r hT (cfg.solvers.solveMean F hF).val.B ≤
        K H * L * unweightedSeminorm False ℓ h (r + 1) hT F := by
    have hv := hMean hT cfg.time_le_one hD data.flow data.velocity_smooth data.velocity_periodic
      data.deformation_le data.inverse_deformation_le hVel d.inverse d.strain d.covector d.mean
      data.mean_inverse_le data.mean_strain_le (fun _ ht x => d.deformation_value _ ht x)
      (fun t ht x => (d.mean.strain_value (t,x,0) ⟨ht,mem_univ _⟩).symm.trans
        (d.strain_value (t,x,0) ⟨ht,mem_univ _⟩)) d.oscillation a haM' h r F hF
    exact hv.trans (mul_le_mul_of_nonneg_right
      (ordered_power hD₁ (hCM r) (hH r hr).2.1 hMeanExp) (apply_nonneg _ _))
  have hDepth₁ : 1 ≤ depth := by omega
  have hγraw : ContinuousOn (fun t => ‖center t‖) (Icc t₀ T) :=
    (HasDerivWithinAt.continuousOn hCenter.amplitude).norm
  have hγraw₀ (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < ‖center t‖ :=
    norm_pos_iff.mpr (hCenter.nonzero t ht).2.1
  have hc : 0 < freq ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hfpos _
  have hTransverse := hTrans (h := h) ht₀ htT hD hℓ hRadius hfpos hCarrier d data.flow
    data.velocity_smooth data.velocity_periodic data.deformation_le data.inverse_deformation_le
    data.velocity_gradient_le hVel hCenter cfg hDepth₁ inactive hγraw hγraw₀
  have hSolveOsc (r : ℕ) (hr : r ≤ H) (i : ℕ) (hi : i ∈ Finset.Icc 2 depth) :
      s.osc r i ≤ K H * L * s.oscSource r i := by
    have he := actualMeasuredLevels_mul_weight_osc cfg.operators cfg.profiles depth
      cfg.leading.completionSwitch cfg.parentResidual freq hfpos.le ℓ h hT ht₀ htT.le
      (fun t => ‖center t‖) hγraw hγraw₀ hc hγ hpos r i
    dsimp only at he
    have hb : s.osc r i ≤ CT r * D ^ (20 : ℕ) * s.oscSource r i := by
      dsimp only [s]
      rw [he.1, he.2]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hTransverse r i hi) (inv_nonneg.mpr hc.le)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (ordered_power hD₁ (hCT r) (hH r hr).1 hOscExp) (s.nonneg r i).1)
  have hEnvelope := isClosed_tsupport (periodizeCentered (radialEnvelope ℓ))
  have hrec : HierarchyNormRecurrence s freq L (K H) depth H :=
    cfg.selectedNormRecurrence lead hDepth₁ data.flow data.velocity_smooth data.velocity_periodic ht₀ htT.le
      hEnvelope inactive ℓ h hℓ.ne' hh.ne' γ hγ hpos hγle hfpos
      (zero_le_one.trans hL) (zero_le_one.trans (hK H)) rowCap relayCap
      (fun r _ i => hRow r i)
      (fun r hr => (hSource r (Nat.le_of_succ_le hr)).1)
      (fun r hr => (hSource r (Nat.le_of_succ_le hr)).2)
      (fun r _ => hCoefficient r)
      (fun r hr => hComplete r (Nat.le_of_succ_le hr))
      (fun r hr => hRelayCap r (Nat.le_of_succ_le hr))
      (fun r hr => hRes r (Nat.le_of_succ_le hr)) hSeed'
      (fun r hr => hSolveMean r (Nat.le_of_succ_le hr)) hSolveOsc
  refine ⟨hrec, fun n hn => ?_⟩
  have hHn : n ≤ H := by omega
  have hRowNonneg : 0 ≤ rowCap n := (apply_nonneg _ _).trans (hRow n 0)
  have hRowCap : 3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * rowCap n ≤ K H * L :=
    (le_mul_of_one_le_left (by positivity : 0 ≤ 3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * rowCap n)
      (by norm_num : (1 : ℝ) ≤ 2)).trans (hSource n hHn).1
  have hFastCap : hierarchyQuadraticConstant (Fin 4) n ^ 2 *
      unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h d.covector) ≤
      K H * L * freq ^ (3 / 2 : ℝ) := by
    refine (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).trans ?_
    simpa only [mul_assoc] using (hSource n hHn).2
  have hC : 0 ≤ C :=
    zero_le_one.trans (hierarchyLevelConstant_one_le (P := depth) (zero_le_one.trans (hK H)) depth)
  have hlevels (i : ℕ) (hi : i ∈ Finset.Icc 1 depth) :
      HierarchyLevelBound s freq L C (n + 1) i := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    exact (hierarchy_level_bounds hrec hf hL (hK H) hsmall i hlo hhi (n + 1) (by omega)).mono hf hL
      (hierarchyLevelConstant_monotone (zero_le_one.trans (hK H)) hhi)
  exact cfg.unweightedSeminorm_remainder_le hDepth data.flow (data.velocity_smooth.of_le (by simp))
    data.velocity_periodic ℓ h hℓ.ne' hh.ne' n hf hL (zero_le_one.trans (hK H)) hC
    hsmall ht₀ htT.le γ hγ hpos hγle hEnvelope inactive (hRow n) hRowCap hFastCap
    (hCoefficient n) (hRelayCap n hHn) hlevels

end TruncatedHierarchyParent
end
end TorusEuler.HierarchyTwistedProfile
