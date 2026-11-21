import TorusEuler.InductiveParentGeometry
import TorusEuler.ParentVelocityEstimates
import TorusEuler.HierarchyTransverseBudgets

/-! The physical oscillatory solve budget from the inductive parent stage. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.InductiveEulerStage.OnSlab

variable {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
  {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}

/-- Both raw coframe operators obey the common parent coefficient scale. -/
theorem raw_coframe_norm_le_frequency_nine (d : s.OnSlab hT k) (hf : 2 ≤ P.frequency n)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    ‖fderiv ℝ (s.flow 0 t) a‖ ≤ P.frequency n ^ 9 ∧
      ‖fderiv ℝ (s.flow t 0) (s.flow 0 t a)‖ ≤ P.frequency n ^ 9 := by
  have hPow : P.frequency n ≤ P.frequency n ^ 9 := calc
    _ = P.frequency n ^ (1 : ℕ) := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ P.frequency n) (by decide)
  obtain ⟨_, hF, hG⟩ := d.deformationOn.bounds t ht
  exact ⟨(hF a).2.trans hPow, (hG (s.flow 0 t a)).2.trans hPow⟩

/-- The material strain bound controls the raw velocity gradient at every
Eulerian point, using the inverse transition to select its label. -/
theorem raw_strain_norm_le_frequency_nine (d : s.OnSlab hT k)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) : ‖fderiv ℝ (s.velocity t) x‖ ≤ P.frequency n ^ 9 := by
  let a := s.flow t 0 x
  have hx : s.flow 0 t a = x := (d.deformationOn.bounds t ht).1.2 x
  have hpa : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hstrain : d.geometry.mean.strain (t, toUnitTorus a) = fderiv ℝ (s.velocity t) x := by
    rw [← d.geometry.mean.strain_value _ hpa, d.geometry.strain_value _ hpa]
    change fderiv ℝ (s.velocity t) (s.flow 0 t a) = _
    rw [hx]
  have h := d.geometry.mean.norm_strain_le (toUnitTorus a) t ht
  rwa [hstrain, d.strain_bound] at h

/-- Universal Bernstein constants bound all positive orders of the actual
parent velocity jets on every reduced slab. -/
theorem exists_raw_velocityJetBounds :
    ∃ V : ℕ → ℝ, (∀ N, 0 ≤ V N) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3},
        (d : s.OnSlab hT k) → 2 ≤ P.frequency n →
        ∀ N j : ℕ, 1 ≤ j → j ≤ N → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (s.velocity t) x‖ ≤ V N * (P.frequency n ^ 9) ^ j := by
  obtain ⟨V, hV, hJet⟩ := exists_parentVelocityJetBounds
  refine ⟨V, hV, ?_⟩
  intro P n activation T s hT k d hf N j hj₁ hjN t ht x
  have hf₁ : 1 ≤ P.frequency n := by linarith
  have hD₁ : 1 ≤ P.frequency n ^ 9 := one_le_pow₀ hf₁
  have hRadius : 2 * P.frequency n ^ 5 ≤ 4 * P.frequency n ^ 9 := calc
    _ ≤ 4 * P.frequency n ^ 5 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (zero_le_one.trans hf₁) 5)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hf₁ (by decide : 5 ≤ 9)) (by norm_num)
  have hBand : RealTorusFourierBand (4 * (P.frequency n ^ 9)) (s.torusVelocity t) :=
    fun l hl => s.velocity_band t (d.subset ht) l (hRadius.trans_lt hl)
  exact hJet (s.torusVelocity t) hD₁ hBand (d.raw_strain_norm_le_frequency_nine ht) N j hj₁ hjN x

/-- The odd parent velocity fixes the center on the reduced slab. -/
theorem flow_center_zero (d : s.OnSlab hT k) {t : ℝ} (ht : t ∈ Icc 0 T) :
    s.flow 0 t 0 = 0 := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (d.smooth_velocity.of_le (by simp)) (fun t _ => s.periodic_velocity t)
  have h := (d.deformationOn.flow.odd hK (fun t ht => s.odd_velocity t (d.subset ht))
    ⟨le_rfl, hT.le⟩ ht) (0 : Vec3)
  rw [neg_zero] at h
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Vec3 => z i) h
  simp only [PiLp.neg_apply] at hi
  rw [PiLp.zero_apply]
  linarith

open HierarchyTwistedProfile

/-- The launch covector reproduces the actual central covector at every
active time. -/
theorem centerCovector_eq_labelWaveVector (d : s.OnSlab hT k) {t₀ : ℝ}
    {κ : ℝ → Vec3} (ht₀ : t₀ ∈ Icc 0 T)
    (hLaunch : k = (fderiv ℝ (s.flow 0 t₀) (0 : Vec3)).adjoint (κ t₀))
    (hκ : ∀ t ∈ Icc t₀ T, HasDerivWithinAt κ
      (-((fderiv ℝ (s.velocity t) (0 : Vec3)).adjoint (κ t))) (Icc t₀ T) t)
    {t : ℝ} (ht : t ∈ Icc t₀ T) : κ t = labelWaveVector s.flow 0 0 k t := by
  have h := (d.deformationOn.flow.center_coframe_covector_eq hT
    (d.smooth_velocity.of_le (by simp)) (fun t _ => s.periodic_velocity t)
    (fun t ht => s.odd_velocity t (d.subset ht)) ht₀ hκ).2 t ht
  rw [labelWaveVector, d.flow_center_zero (Icc_subset_Icc_left ht₀.1 ht), hLaunch, h]

/-- The prescribed central wave is represented by the chosen launch
covector on the whole active slab. -/
theorem centerWaveOn_labelWaveVector (d : s.OnSlab hT k) {t₀ D : ℝ}
    {κ b : ℝ → Vec3} (ht₀ : t₀ ∈ Icc 0 T)
    (hLaunch : k = (fderiv ℝ (s.flow 0 t₀) (0 : Vec3)).adjoint (κ t₀))
    (hCenter : LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (s.velocity t) 0) κ b t₀ T D) :
    LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (s.velocity t) (s.flow 0 t 0))
      (fun t => labelWaveVector s.flow 0 0 k t) b t₀ T D := by
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀.1
  have hM : EqOn (fun t => fderiv ℝ (s.velocity t) 0)
      (fun t => fderiv ℝ (s.velocity t) (s.flow 0 t 0)) (Icc t₀ T) := by
    intro t ht
    dsimp only
    rw [d.flow_center_zero (hsub ht)]
  have hc := hCenter.congr_gradient hM
  have hk (t : ℝ) (ht : t ∈ Icc t₀ T) : κ t = labelWaveVector s.flow 0 0 k t :=
    d.centerCovector_eq_labelWaveVector ht₀ hLaunch hCenter.covector ht
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · have h := hc.covector t ht
    rw [hk t ht] at h
    exact h.congr_of_mem (fun r hr => (hk r hr).symm) ht
  · rw [← hk t ht]
    exact hc.nonzero t ht
  · rw [← hk t ht]
    exact hc.amplitude t ht
  · intro z hz hperp u v hu hv huv
    refine hc.stability z (fun t ht => ?_) (fun t ht => ?_) hu hv huv
    · rw [hk t ht]
      exact hz t ht
    · rw [hk t ht]
      exact hperp t ht
  · rw [← hk t ht]
    exact hc.coupling t ht

set_option maxHeartbeats 1500000 in
/-- The actual parent on the child slab supplies the oscillatory solve row
at all retained correction levels, using the center amplitude weight. -/
theorem exists_physicalTransverseSolveBudget_of_stage :
    ∃ (A : ℕ) (Krec : ℕ → ℝ), 30 ≤ A ∧ (∀ m, 0 ≤ Krec m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T t₀ ℓ h freq : ℝ}
        {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3} {κ b : ℝ → Vec3},
        (d : s.OnSlab hT k) → 2 ≤ P.frequency n →
        (ht₀ : 0 ≤ t₀) → (htT : t₀ < T) → 0 < ℓ → ℓ ≤ ((P.frequency n ^ 9) ^ A)⁻¹ →
        (hfreq : 0 < freq) → ‖κ t₀‖ = freq →
        k = (fderiv ℝ (s.flow 0 t₀) (0 : Vec3)).adjoint (κ t₀) →
        LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (s.velocity t) 0) κ b t₀ T
          (P.frequency n ^ 9) →
        ∀ {p : Pressure} {N : ℕ}, (cfg : PhysicalApproximationData d.geometry p N) → 1 ≤ N →
          cfg.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn (fun t => ‖b t‖) (Icc t₀ T))
            (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < ‖b t‖),
          let levels := actualMeasuredLevels cfg.operators cfg.profiles N cfg.leading.completionSwitch
            cfg.parentResidual freq hfreq.le ℓ h hT ht₀ htT.le (fun t => ‖b t‖) hγ hγ₀
          ∀ m i : ℕ, i ∈ Finset.Icc 2 N →
            levels.osc m i ≤ Krec m * (P.frequency n ^ 9) ^ 20 * levels.oscSource m i := by
  obtain ⟨V, hV, hJets⟩ := exists_raw_velocityJetBounds
  obtain ⟨A, Krec, hA, hKrec, hBudget⟩ := exists_physicalTransverseSolveBudget V hV
  refine ⟨A, Krec, hA, hKrec, ?_⟩
  intro P n activation T t₀ ℓ h freq s hT k κ b d hf ht₀ htT hℓ hEll hfreq hFreq hLaunch hCenter
    p N cfg hN hInactive hγ hγ₀
  have hD : 2 ≤ P.frequency n ^ 9 := hf.trans (by
    calc
      _ = P.frequency n ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ P.frequency n) (by decide : 1 ≤ 9))
  have ht : t₀ ∈ Icc 0 T := ⟨ht₀, htT.le⟩
  have hc := d.centerWaveOn_labelWaveVector ht hLaunch hCenter
  have hEq : ‖labelWaveVector s.flow 0 0 k t₀‖ = freq := by
    rw [← d.centerCovector_eq_labelWaveVector ht hLaunch hCenter.covector ⟨le_rfl, htT.le⟩, hFreq]
  exact hBudget (h := h) ht₀ htT hD hℓ hEll hfreq hEq d.geometry d.deformationOn.flow
    d.smooth_velocity (fun t _ => s.periodic_velocity t)
    (fun t ht a => (d.raw_coframe_norm_le_frequency_nine hf ht a).1)
    (fun t ht a => (d.raw_coframe_norm_le_frequency_nine hf ht a).2)
    (fun _ ht => d.raw_strain_norm_le_frequency_nine ht) (hJets d hf) hc cfg hN hInactive hγ hγ₀

end TorusEuler.InductiveEulerStage.OnSlab
