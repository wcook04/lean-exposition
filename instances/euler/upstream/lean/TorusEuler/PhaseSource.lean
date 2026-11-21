import TorusEuler.PhaseCalculus
import TorusEuler.Statement

open scoped InnerProductSpace

namespace TorusEuler

/-- The completion contribution to the averaged fast source in (5.42).
At fixed time and label, `C` is the completion profile, `Y` is the differentiated
profile, and `divV` is the scalar profile of the pulled-back divergence of `V`. -/
theorem phaseMean_fastSource (κ : Vec3) (C Y Y_s : ℝ → Vec3) (divV : ℝ → ℝ)
    (hCper : Function.Periodic C 1) (hYper : Function.Periodic Y 1)
    (hY : ∀ s, HasDerivAt Y (Y_s s) s) (hYs : Continuous Y_s) (hdivV : Continuous divV)
    (hslave : ∀ s, ⟪C s, κ⟫_ℝ = -phasePrimitive divV s) :
    phaseMean (fun s => ⟪C s, κ⟫_ℝ • Y_s s) = phaseMean (fun s => divV s • Y s) := by
  have hweight : ∀ s, HasDerivAt (fun r => ⟪C r, κ⟫_ℝ) (-divV s) s := by
    have heq : (fun r => ⟪C r, κ⟫_ℝ) = fun r => -phasePrimitive divV r := funext hslave
    intro s
    rw [heq]
    exact (hasDerivAt_phasePrimitive hdivV s).neg
  have hweightper : Function.Periodic (fun s => ⟪C s, κ⟫_ℝ) 1 := by
    intro s
    exact congrArg (fun v => ⟪v, κ⟫_ℝ) (hCper s)
  rw [phaseMean_smul_deriv hweight hY hdivV.neg hYs hweightper hYper]
  simp [phaseMean, neg_smul]

/-- A phase-independent fast coefficient gives zero mean against a phase derivative. -/
theorem phaseMean_meanFastSource (κ B : Vec3) (Y Y_s : ℝ → Vec3)
    (hYper : Function.Periodic Y 1) (hY : ∀ s, HasDerivAt Y (Y_s s) s)
    (hYs : Continuous Y_s) :
    phaseMean (fun s => ⟪B, κ⟫_ℝ • Y_s s) = 0 := by
  rw [phaseMean_const_smul, phaseMean_deriv hY hYs hYper, smul_zero]

end TorusEuler
