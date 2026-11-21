import TorusEuler.PaperTruncatedHierarchyBounds
import TorusEuler.LaterWaveHierarchyInput

/-! The localized seed and its regularity for a physical truncated parent. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open LocalizedAmplitude

set_option maxHeartbeats 2000000 in
/-- One width threshold gives the actual localized seed for the prescribed
central wave. The seed shares the parent carrier and has the smoothness
and evenness needed by the switched hierarchy. -/
theorem exists_localizedSeed :
    ∃ A : ℕ, 3 ≤ A ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T t₀ D freq r : ℝ}
        {hT : 0 < T} {k : Vec3} {center : ℝ → Vec3} {d : ParentGeometry hT U X k},
        TruncatedHierarchyParent d p D freq →
        (∀ t ∈ Icc 0 T, Function.Odd (U t)) →
        0 ≤ t₀ → t₀ < T → 0 ≤ r →
        ∀ a : ℕ, A ≤ a →
        let ℓ := (D ^ a)⁻¹;
        let h := freq ^ (-1 / 2 : ℝ);
        let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x);
        let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t;
        ‖κ t₀ 0‖ = freq →
        CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
        ∃ Cseed : ℝ, ∃ w : SeedOn M κ center t₀ T ℓ D Cseed,
          w.HierarchyRegularity r h ∧ ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t) := by
  obtain ⟨V, hV, hVelocity⟩ := exists_velocityJetBounds
  obtain ⟨C, A, _, hA, hSeed⟩ := exists_seedOn_of_parent_bounds V hV
  refine ⟨A, hA, ?_⟩
  intro U X p T t₀ D freq r hT k center d data hOdd ht₀ htT hr a ha ℓ h M κ hFreq hCenter
  have hD : 1 ≤ D := one_le_two.trans data.scale_ge_two
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hVel := hVelocity data
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hWidth {j : ℕ} (hj : j ≤ a) : ℓ ≤ (D ^ j)⁻¹ :=
    inv_anti₀ (pow_pos hDpos _) (pow_le_pow_right₀ hD hj)
  have hfit : 2 * ℓ < 1 / 2 := by
    have hCube : (2 : ℝ) ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ zero_le_two data.scale_ge_two 3
    have hEighth : ℓ ≤ (1 / 8 : ℝ) := (hWidth (hA.trans ha)).trans (by
      simpa only [show ((2 : ℝ) ^ 3)⁻¹ = 1 / 8 by norm_num] using
        inv_anti₀ (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 3) hCube)
    linarith only [hEighth]
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    data.velocity_smooth.of_le (by simp)
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hStart : t₀ ∈ Icc 0 T := ⟨ht₀, htT.le⟩
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (hU₂.of_le (by norm_num)) data.velocity_periodic
  have hFix (t : ℝ) (ht : t ∈ Icc 0 T) : X 0 t (0 : Vec3) = 0 := by
    have he := data.flow.odd hL hOdd h0 ht (0 : Vec3)
    rw [neg_zero] at he
    ext i
    have hi := congrArg (fun y : Vec3 => y i) he
    simp only [PiLp.neg_apply] at hi
    simpa only [PiLp.zero_apply] using (show (X 0 t 0) i = 0 by linarith)
  have hCenterAtOrigin : CenterWaveOn (fun t => fderiv ℝ (U t) (0 : Vec3))
      (fun t => κ t 0) center t₀ T D :=
    hCenter.congr_gradient (fun t ht => by simp only [M, hFix t ⟨ht₀.trans ht.1, ht.2⟩])
  have hInverse := (data.flow.labelDerivative_inverse hT hU₂ data.velocity_periodic h0 hStart
    (0 : Vec3)).1
  have hLaunch : (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀ 0) = k := by
    change ((fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint.comp
      (fderiv ℝ (X t₀ 0) (X 0 t₀ 0)).adjoint) k = k
    rw [← ContinuousLinearMap.adjoint_comp, hInverse, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_apply]
  have hk : k ≠ 0 := by
    intro he
    have hZero : κ t₀ 0 = 0 := by simp [κ, labelWaveVector, he]
    have hFalse : (0 : ℝ) = freq := by simpa only [hZero, norm_zero] using hFreq
    linarith only [hFalse, data.frequency_ge_one]
  have hw := hSeed hT data.time_le_one hStart data.scale_ge_two data.flow data.velocity_smooth
    data.velocity_periodic hOdd data.deformation_le data.inverse_deformation_le
    data.velocity_gradient_le hVel hCenterAtOrigin hℓ (hWidth ha)
  rw [hLaunch] at hw
  obtain ⟨w⟩ := hw
  obtain ⟨reg, hEven, _, _⟩ := SeedOn.hierarchyRegularity_of_parent ht₀ htT data.flow
    data.velocity_smooth data.velocity_periodic hOdd hk w hr hℓ hfit
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le data.frequency_ge_one) _)
    (Real.rpow_le_one_of_one_le_of_nonpos data.frequency_ge_one (by norm_num : (-1 / 2 : ℝ) ≤ 0))
  exact ⟨amplitudeLabelSlope D (C * D ^ 24) (C * D ^ 24) (C * D ^ 24) (C * D ^ 24),
    w, reg, hEven⟩

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent
