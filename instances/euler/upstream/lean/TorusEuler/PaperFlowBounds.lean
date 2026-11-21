import TorusEuler.InductiveStageProfileFlowBounds

/-! The deformation of the perturbed physical flow in Lemma 5.10. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

open ChildFlow

noncomputable section

variable {T : ℝ} {k : Vec3} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}

local notation "I" => Icc (0 : ℝ) T

private theorem smooth_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → Vec3}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

set_option maxHeartbeats 4500000 in
/-- Lemma 5.10 for the actual measured hierarchy and an arbitrary smooth,
solenoidal periodic perturbation. The perturbation contributes only to
the pulled-back phase mean. A uniform C² bound is more than sufficient
for the first-order jet of this contribution. -/
theorem paperLemma510_flowBounds
    {d : ParentGeometry hT U X k} {depth a lossPower bExp : ℕ} {D ell h freq Γ : ℝ} {C : ℕ → ℝ}
    (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hUDiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0)
    (hParent : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D)
    (hCoframeReg : ∀ t ∈ I, ContDiff ℝ ∞ (fun x => fderiv ℝ (X t 0) (X 0 t x)))
    (hCoframe : ∀ j, ∀ t ∈ I, ∀ x : Vec3,
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (X t 0) (X 0 t y)) x‖ ≤ C j * D ^ (7 * j + 1))
    (hEll : 0 < ell) (hEll₁ : ell ≤ 1) (hScale : ell * D ^ (7 : ℕ) ≤ 1)
    (hLabel : ell⁻¹ ≤ D ^ a) (hCarrier : ‖k‖ ≤ D * freq)
    (hD : 1 ≤ D) (hC : ∀ j, 0 ≤ C j) (hf : 1 ≤ freq) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (b : PhysicalApproximationData d p depth)
    (props : PhysicalApproximationProperties b) (hDepth : 2 ≤ depth)
    {levelConstant : ℝ} (hLevelC : 0 ≤ levelConstant)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {S : Set Vec3} (hS : IsClosed S)
    (hInactive : b.leading.Inactive t₀ S)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hLevels : ∀ m ≤ 2, ∀ j ∈ Finset.Icc 1 depth, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ell h hT ht₀ htT γ hγ hpos) freq (D ^ lossPower) levelConstant m j)
    (hExp : max a 1 + (max a 1 + profileFlowJetPower lossPower) + 1 ≤ bExp)
    (hΓ : 1 + 40 * profileFlowJetConstant C depth levelConstant ≤ Γ)
    (hsmall : Γ * D ^ bExp * freq ^ (-1 / 12 : ℝ) ≤ 1)
    {v : Velocity}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hvPer : ∀ t ∈ I, SpatiallyPeriodic (v t))
    (hvDiv : ∀ t ∈ I, ∀ x, divergence (v t) x = 0)
    (hvSize : ∀ t ∈ I, PhaseJetBound 2 (freq ^ (-5 / 2 : ℝ)) (v t)) :
    ∃ Y : ℝ → Velocity, DeformationOn (b.velocity + v) Y T (Γ * D ^ bExp * freq ^ (1 / 4 : ℝ)) := by
  let B := profileFlowJetConstant C depth levelConstant
  let power := profileFlowJetPower lossPower
  let Aosc := profileFlowOscillationCost C depth levelConstant
  let Amean := profileFlowMeanCost C depth levelConstant
  let ε := freq ^ (-5 / 2 : ℝ)
  let W := b.profileVelocity
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hCoefficient (m : ℕ) := inverseCoframe_unweighted_le_of_parent (h := h)
    d hEll.le hD hScale hC m hCoframeReg hCoframe
  obtain ⟨hAosc, hAmean, hOscRaw, hMeanRaw⟩ :=
    uncutPullbackProfileJetBounds_of_actualLevels hCoefficient hD hC hf b (by omega)
      hLevelC ht₀ htT hS hInactive γ hγ hpos hγmax hLevels
  have hB : 0 ≤ B := add_nonneg (add_nonneg hAosc hAmean) (add_nonneg zero_le_one (hC 1))
  have hOscPower : 2 * lossPower + 1 ≤ power := by dsimp only [power, profileFlowJetPower]; omega
  have hMeanPower : 6 * lossPower + 1 ≤ power := by dsimp only [power, profileFlowJetPower]; omega
  have hTailPower : 8 ≤ power := by dsimp only [power, profileFlowJetPower]; omega
  have hOscCoeff : Aosc ≤ B :=
    (le_add_of_nonneg_right hAmean).trans (le_add_of_nonneg_right (add_nonneg zero_le_one (hC 1)))
  have hTailCoeff : max D (D * D + C 1 * D ^ (8 : ℕ)) ≤ (1 + C 1) * D ^ power := by
    have hCoef₁ := hC 1
    have hD₈' : D ≤ D ^ (8 : ℕ) :=
      le_self_pow₀ hD (by decide)
    have hD₂ : D * D ≤ D ^ (8 : ℕ) := by
      rw [← pow_two]
      exact pow_le_pow_right₀ hD (by decide)
    refine (max_le ?_ ?_).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hTailPower) (add_nonneg zero_le_one hCoef₁))
    · exact hD₈'.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    · rw [add_mul, one_mul]
      exact add_le_add hD₂ le_rfl
  have hW : ContDiffOn ℝ ∞ (Function.uncurry fun t => Function.uncurry (W t))
      (Icc 0 T ×ˢ (univ : Set PhaseState)) :=
    HierarchySmoothProfile.smooth (b.profiles.velocity depth).val.val
  have hForward := hX.contDiffOn_forwardLabelFlow hT hU hPer
  have hUncut := contDiffOn_pullbackField_of_parent hT hX hU hPer hW
    (v := (0 : Velocity)) contDiffOn_const
  have hCorrected := contDiffOn_pullbackField_of_parent hT hX hU hPer hW hv
  have hWphase (t : ℝ) (ht : t ∈ I) (x : Vec3) : Continuous (W t x) :=
    ((b.profileVelocity_smooth t ht).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hOsc (t : ℝ) (ht : t ∈ I) :
      PhaseJetBound 2 (B * D ^ power * freq ^ (-5 / 4 : ℝ))
        (scaledPhaseProfile ell h (fun x => phaseOscillation
          (fun r => pullbackField X W v t (x, r)))) := by
    rw [show (fun x => phaseOscillation (fun r => pullbackField X W v t (x, r))) =
      (fun x => phaseOscillation (fun r => pullbackField X W 0 t (x, r))) from
      funext fun x => phaseOscillation_pullbackField_eq_uncut (hWphase t ht x)]
    intro j hj x
    exact (hOscRaw t ht j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hOscCoeff (pow_le_pow_right₀ hD hOscPower) (pow_nonneg hD₀ _) hB)
      (Real.rpow_nonneg (zero_le_one.trans hf) _))
  have hMean (t : ℝ) (ht : t ∈ I) :
      PhaseJetBound 1 (B * D ^ power * ε)
        (scaledPhaseProfile ell h (fun x _ => phaseMean
          (fun r => pullbackField X W v t (x, r)))) := by
    let A := X 0 t
    let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
    let f (x : Vec3) (r : ℝ) := pullbackField X W 0 t (x, r)
    let mean := scaledPhaseProfile ell h (fun x _ => phaseMean (f x))
    let tail := scaledPhaseProfile ell h (fun x _ => G x (v t (A x)))
    let L : PhaseState →L[ℝ] Vec3 := ell • ContinuousLinearMap.fst ℝ Vec3 ℝ
    have hA := smooth_slice hForward ht
    have hG := hCoframeReg t ht
    have hVreg := smooth_slice hv ht
    have hFreg := smooth_slice hUncut ht
    have hFmean : ContDiff ℝ ∞ (fun x => phaseMean (f x)) :=
      contDiffOn_univ.mp (contDiffOn_phaseMean (f := f) convex_univ uniqueDiffOn_univ hFreg.contDiffOn)
    have hMeanDiff : Differentiable ℝ mean := (hFmean.comp L.contDiff).differentiable (by simp)
    have hTailDiff : Differentiable ℝ tail :=
      ((hG.clm_apply (hVreg.comp hA)).comp L.contDiff).differentiable (by simp)
    have hTailJet : PhaseJetBound 1 (max D (D * D + C 1 * D ^ (8 : ℕ)) * ε) tail :=
      scaledPerturbation_phaseJetBound_one
        (by rw [abs_of_pos hEll]; exact hEll₁)
        (hA.differentiable (by simp)) (hG.differentiable (by simp))
        (fun x => (hParent t ht x).1) (fun x => (hParent t ht (A x)).2)
        (fun x => by simpa only [norm_iteratedFDeriv_one, Nat.reduceMul, Nat.reduceAdd] using hCoframe 1 t ht x) (hVreg.differentiable (by simp))
        (fun x => by simpa only [norm_iteratedFDeriv_zero] using hvSize t ht 0 (by decide) x)
        (fun x => by simpa only [norm_iteratedFDeriv_one] using hvSize t ht 1 (by decide) x)
    have eqMean : scaledPhaseProfile ell h (fun x _ => phaseMean
        (fun r => pullbackField X W v t (x, r))) = mean + tail := by
      funext z
      exact phaseMean_pullbackField_eq_add (hWphase t ht (L z))
    rw [eqMean]
    intro j hj z
    refine (TruncatedChildStage.phaseJetBound_one_add hMeanDiff hTailDiff (hMeanRaw t ht)
      hTailJet j hj z).trans ?_
    have hε : 0 ≤ ε := by dsimp only [ε]; positivity
    calc
      _ ≤ Amean * D ^ power * ε + (1 + C 1) * D ^ power * ε :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hMeanPower) hAmean) hε)
          (mul_le_mul_of_nonneg_right hTailCoeff hε)
      _ = (Amean + (1 + C 1)) * D ^ power * ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (add_le_add (le_add_of_nonneg_left hAosc) le_rfl) (pow_nonneg hD₀ _)) hε
  obtain ⟨Y, hY⟩ := ChildFlow.exists_childFlow_of_profile_jet_bounds (v := v)
    (p := power) (B := B) hT b.time_le_one hX (hU.of_le (by simp)) hPer hUDiv
    (fun t ht x => ((smooth_slice hForward ht).of_le (by simp)).contDiffAt)
    hParent hD hf hEll hB hLabel hWidth hCarrier hExp hΓ
    hsmall hCorrected b.profileVelocity_smooth (fun t _ => b.profileVelocity_periodic t)
    (fun t _ => b.profileVelocity_skew t) props.profile_divergence hvPer
    (fun t ht x => ⟨(smooth_slice hv ht).differentiable (by simp) x, hvDiv t ht x⟩) hOsc hMean
  exact ⟨Y, hY⟩

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
