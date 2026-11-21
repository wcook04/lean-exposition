import TorusEuler.HierarchyInductiveTransverseBudget

/-! Constant normalization of the actual amplitude weight. -/

open Set

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

/-- Multiplying the amplitude weight by a positive constant divides the seminorm by it. -/
theorem amplitudeSeminorm_mul_weight {T : ℝ} {k : Vec3} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (holder : Prop) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    {c : ℝ} (hc : 0 < c)
    (hγ' : ContinuousOn (fun t => c * γ t) (Icc t₀ T))
    (hpos' : ∀ t ∈ Icc t₀ T, 0 < c * γ t)
    (f : HierarchyTwistedProfile T k E) :
    amplitudeSeminorm holder ℓ h n hT ht₀ htT (fun t => c * γ t) hγ' hpos' f =
      c⁻¹ * amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos f := by
  have hSlices :
      weightedSlices (Icc t₀ T) (fun t => (c * γ t)⁻¹) f =
        weightedSlices (Icc t₀ T) (fun t => (γ t)⁻¹) (c⁻¹ • f) := by
    funext t x
    change (c * γ t)⁻¹ • f.val.val.val (t, x) = (γ t)⁻¹ • c⁻¹ • f.val.val.val (t, x)
    rw [mul_inv_rev, smul_smul]
  calc
    _ = amplitudeSeminorm holder ℓ h n hT ht₀ htT γ hγ hpos (c⁻¹ • f) := by
      simp only [amplitudeSeminorm_apply, hSlices]
    _ = _ := by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]

/-- The oscillation and its forcing scale by the same reciprocal weight factor. -/
theorem actualMeasuredLevels_mul_weight_osc {T : ℝ} {k : Vec3}
    (A : HierarchyOperators (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (P : ℕ) (completionSwitch parentResidual : HierarchyTwistedProfile T k Vec3)
    (freq : ℝ) (hf : 0 ≤ freq) (ℓ h : ℝ) (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    {c : ℝ} (hc : 0 < c)
    (hγ' : ContinuousOn (fun t => c * γ t) (Icc t₀ T))
    (hpos' : ∀ t ∈ Icc t₀ T, 0 < c * γ t) (n i : ℕ) :
    let old := actualMeasuredLevels A u P completionSwitch parentResidual freq hf ℓ h hT ht₀ htT
      γ hγ hpos
    let new := actualMeasuredLevels A u P completionSwitch parentResidual freq hf ℓ h hT ht₀ htT
      (fun t => c * γ t) hγ' hpos'
    new.osc n i = c⁻¹ * old.osc n i ∧ new.oscSource n i = c⁻¹ * old.oscSource n i := by
  intro old new
  constructor
  · change
      amplitudeSeminorm False ℓ h n hT ht₀ htT (fun t => c * γ t) hγ' hpos' (u.V i) +
        freq * amplitudeSeminorm False ℓ h n hT ht₀ htT (fun t => c * γ t) hγ' hpos' (u.p i) = _
    rw [amplitudeSeminorm_mul_weight False ℓ h n hT ht₀ htT γ hγ hpos hc hγ' hpos',
      amplitudeSeminorm_mul_weight False ℓ h n hT ht₀ htT γ hγ hpos hc hγ' hpos']
    change _ = c⁻¹ * (amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos (u.V i) +
      freq * amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos (u.p i))
    ring
  · let H := A.sourceBeforeMean u P completionSwitch i
    let F := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)
    change (if i = 1 then 0 else amplitudeSeminorm False ℓ h n hT ht₀ htT
        (fun t => c * γ t) hγ' hpos' F) =
      c⁻¹ * (if i = 1 then 0 else amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos F)
    by_cases hi : i = 1
    · simp only [hi, ite_true, mul_zero]
    · simp only [ite_eq_right hi,
        amplitudeSeminorm_mul_weight False ℓ h n hT ht₀ htT γ hγ hpos hc hγ' hpos']

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.InductiveEulerStage.OnSlab

open HierarchyTwistedProfile

/-- The selected transverse solve obeys its budget with the normalized central amplitude. -/
theorem exists_normalizedPhysicalTransverseSolveBudget_of_stage :
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
          ∀ (hγ : ContinuousOn (fun t => freq ^ (3 / 4 : ℝ) * ‖b t‖) (Icc t₀ T))
            (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < freq ^ (3 / 4 : ℝ) * ‖b t‖),
          let levels := actualMeasuredLevels cfg.operators cfg.profiles N cfg.leading.completionSwitch
            cfg.parentResidual freq hfreq.le ℓ h hT ht₀ htT.le
            (fun t => freq ^ (3 / 4 : ℝ) * ‖b t‖) hγ hγ₀
          ∀ m i : ℕ, i ∈ Finset.Icc 2 N →
            levels.osc m i ≤ Krec m * (P.frequency n ^ 9) ^ 20 * levels.oscSource m i := by
  obtain ⟨A, Krec, hA, hK, hbudget⟩ := exists_physicalTransverseSolveBudget_of_stage
  refine ⟨A, Krec, hA, hK, ?_⟩
  intro P n activation T t₀ ℓ h freq s hT k κ b d hparent ht₀ htT hℓ hAℓ hfreq hFreq hLaunch
    hCenter p N cfg hN hInactive hγ hγ₀ levels m i hi
  have hγraw : ContinuousOn (fun t => ‖b t‖) (Icc t₀ T) :=
    (HasDerivWithinAt.continuousOn hCenter.amplitude).norm
  have hγraw₀ (t : ℝ) (ht : t ∈ Icc t₀ T) : 0 < ‖b t‖ :=
    norm_pos_iff.mpr (hCenter.nonzero t ht).2.1
  have hc : 0 < freq ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hfreq _
  have hs := actualMeasuredLevels_mul_weight_osc cfg.operators cfg.profiles N
    cfg.leading.completionSwitch cfg.parentResidual freq hfreq.le ℓ h hT ht₀ htT.le
    (fun t => ‖b t‖) hγraw hγraw₀ hc hγ hγ₀ m i
  dsimp only at hs
  have hbound := hbudget (h := h) d hparent ht₀ htT hℓ hAℓ hfreq hFreq hLaunch
    hCenter cfg hN hInactive hγraw hγraw₀ m i hi
  dsimp only [levels]
  rw [hs.1, hs.2]
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hc.le)

end TorusEuler.InductiveEulerStage.OnSlab
