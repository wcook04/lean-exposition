import Breakdown.Cert.CoerciveFrequencySeminormTransportModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

theorem transport_mode_normSq (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, ((2 * Real.pi * ι.1 / P) ^ 2 + 1 / 4) * cnormSq (modeVel ι v z.1 z.2) =
      cnormSq (fun i => modeVel ι g z.1 z.2 i
        - (1 / 2 : ℂ) * ∑ j : Fin 3, modeGrad ι G z.1 z.2 (i, j) * ((z.2 j : ℝ) : ℂ)) := by
  have h0 := ae_transportDefect hv hP0 ι 0
  have h1 : ∀ᵐ z : ℝ × Space, transportDefect P ι v G g 0 z.2 = 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))).ae h0
  filter_upwards [h1] with z hz
  set e : ℂ := Complex.exp (((2 * Real.pi * ι.1 * z.1 : ℝ) : ℂ) * Complex.I) with he
  have hen : ‖e‖ = 1 := by rw [he, Complex.norm_exp_ofReal_mul_I]
  set c : ℂ := ((2 * Real.pi * ι.1 / P : ℝ) : ℂ) * Complex.I + 1 / 2 with hc
  have key : (fun i => modeVel ι g z.1 z.2 i
        - (1 / 2 : ℂ) * ∑ j : Fin 3, modeGrad ι G z.1 z.2 (i, j) * ((z.2 j : ℝ) : ℂ)) =
      fun i => c * modeVel ι v z.1 z.2 i := by
    funext i
    have hi := congrFun hz i
    simp only [transportDefect, Pi.zero_apply] at hi
    rw [modeVel_shift ι hv.periodic_derivative z.1 z.2, modeVel_shift ι hv.periodic_velocity z.1 z.2,
      modeGrad_shift ι hv.periodic_gradient z.1 z.2]
    simp only
    have e2 : ∑ j : Fin 3, e * modeGrad ι G 0 z.2 (i, j) * ((z.2 j : ℝ) : ℂ) =
        e * ∑ j : Fin 3, modeGrad ι G 0 z.2 (i, j) * ((z.2 j : ℝ) : ℂ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    linear_combination (-e) * hi
  rw [key, cnormSq_smul, hc, norm_sq_transport_factor]

end Internal

end FrequencySeminorm

end Coercive

end Breakdown
