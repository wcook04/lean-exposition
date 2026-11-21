import TorusEuler.HierarchyNormalizedTransverseBudget
import TorusEuler.TerminalHierarchyTime
import TorusEuler.TerminalSelectedTransverseTime

/-! The normalized transverse time estimate on every selected inductive slab. -/

open Set
open scoped ContDiff

namespace TorusEuler.InductiveEulerStage.OnSlab

open HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 1800000 in
/-- The ordinary normalized spatial estimate supplies the initial time-order
bound on the exact selected stage. A common old-parent cap for its four
differentiated coefficients then gives the transverse row of the factorial
time-norm recurrence at every retained correction level. -/
theorem exists_normalizedPhysicalTransverseTimeBudget_of_stage :
    ∃ (A : ℕ) (Krec : ℕ → ℝ), 30 ≤ A ∧ (∀ m, 0 ≤ Krec m) ∧
      ∀ {P : InductiveEulerParameters} {j : ℕ} {activation T t₀ ℓ h freq : ℝ}
        {stage : InductiveEulerStage P j activation} {hT : 0 < T} {k : Vec3} {κ b : ℝ → Vec3},
        (d : stage.OnSlab hT k) → 2 ≤ P.frequency j →
        (ht₀ : 0 ≤ t₀) → (htT : t₀ < T) → 0 < ℓ → ℓ ≤ ((P.frequency j ^ 9) ^ A)⁻¹ →
        (hfreq : 0 < freq) → ‖κ t₀‖ = freq →
        k = (fderiv ℝ (stage.flow 0 t₀) (0 : Vec3)).adjoint (κ t₀) →
        LocalizedAmplitude.CenterWaveOn (fun t => fderiv ℝ (stage.velocity t) 0) κ b t₀ T
          (P.frequency j ^ 9) →
        ∀ {p : Pressure} {N : ℕ}, (cfg : PhysicalApproximationData d.geometry p N) → 1 ≤ N →
          cfg.leading.Inactive t₀ (tsupport (periodizeCentered (radialEnvelope ℓ))) →
          ∀ (hγ : ContinuousOn (fun t => freq ^ (3 / 4 : ℝ) * ‖b t‖) (Icc t₀ T))
            (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < freq ^ (3 / 4 : ℝ) * ‖b t‖)
            (q e : ℕ) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) →
          let D := P.frequency j ^ 9
          let coeff := d.geometry.oscillation.timeCoefficients freq hfreq.ne'
          let U n := timeJetSeminorm hT q (unweightedSeminorm (k := k) (E := Vec3) False ℓ h n hT)
          let Uforce n := timeJetSeminorm hT (q - 1) (unweightedSeminorm (k := k) (E := Vec3) False ℓ h n hT)
          let W n := timeJetSeminorm hT q (amplitudeSeminorm (k := k) (E := Vec3)
            False ℓ h n hT ht₀ htT.le _ hγ hγ₀)
          let Q n := timeJetSeminorm hT q (amplitudeSeminorm (k := k) (E := ℝ)
            False ℓ h n hT ht₀ htT.le _ hγ hγ₀)
          let levels := HierarchyMeasuredLevels.ofProfilesWithMeanForce cfg.operators cfg.profiles N
            cfg.leading.completionSwitch cfg.parentResidual freq hfreq.le U Uforce W Q
          (∀ m, let NM := unweightedSeminorm (k := k) (E := Vec3 →L[ℝ] Vec3) False ℓ h m hT
                let NP := unweightedSeminorm (k := k) (E := Vec3 →L[ℝ] ℝ) False ℓ h m hT
                let B := C m * D ^ e
                timeJetSeminorm hT q NM coeff.velocity ≤ B ∧
                timeJetSeminorm hT q NM coeff.source ≤ B ∧
                timeJetSeminorm hT q NP coeff.pressureVelocity ≤ B ∧
                timeJetSeminorm hT q NP coeff.pressureSource ≤ B) →
          ∀ m i : ℕ, i ∈ Finset.Icc 2 N →
            levels.osc m i ≤
              (transverseTimeCost 1 m q (Krec m) (C m) * D ^ (20 + e * (q + 1))) *
                levels.oscSource m i := by
  obtain ⟨A, Krec, hA, hKrec, hold⟩ := exists_normalizedPhysicalTransverseSolveBudget_of_stage
  refine ⟨A, Krec, hA, hKrec, ?_⟩
  intro P j activation T t₀ ℓ h freq stage hT k κ b d hParent ht₀ htT hℓ hRad
    hfreq hFreq hLaunch hCenter p N cfg hN hInactive hγ hγ₀ q e C hC D coeff U Uforce W Q levels
    hCoeff m i hi
  have hSpatial := hold (h := h) d hParent ht₀ htT hℓ hRad hfreq hFreq hLaunch hCenter cfg hN hInactive
    hγ hγ₀ m i hi
  have hD : 1 ≤ D := one_le_pow₀ (one_le_two.trans hParent)
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hC₀ : 0 ≤ Krec m * D ^ (20 : ℕ) := mul_nonneg (hKrec m) (pow_nonneg hD₀ _)
  have hC₁ : 0 ≤ C m * D ^ e := mul_nonneg (hC m) (pow_nonneg hD₀ _)
  obtain ⟨hV, hF, hP, hQ⟩ := hCoeff m
  have hBound := cfg.selectedTransverse_timeJet_le_of_spatialRow hi ht₀ htT.le hfreq hγ hγ₀ ℓ h m q
    hC₀ hC₁ hSpatial hV hF hP hQ
  have hCost : transverseTimeCost T m q (Krec m * D ^ (20 : ℕ)) (C m * D ^ e) ≤
      transverseTimeCost 1 m q (Krec m) (C m) * D ^ (20 + e * (q + 1)) :=
    transverseTimeCost_le_parentPower (a := 20) (b := e) hT.le cfg.time_le_one hD hC₀ hC₁
      le_rfl le_rfl
  have hi₁ : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
  change W m (cfg.profiles.V i) + freq * Q m (cfg.profiles.p i) ≤
      (transverseTimeCost 1 m q (Krec m) (C m) * D ^ (20 + e * (q + 1))) *
        (if i = 1 then 0 else W m (cfg.selectedTransverseForce i))
  rw [ite_eq_right hi₁]
  exact hBound.trans (mul_le_mul_of_nonneg_right hCost (apply_nonneg (W m) _))

end

end TorusEuler.InductiveEulerStage.OnSlab
