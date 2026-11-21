import Breakdown.FracCell.StAssembly
import Breakdown.FracCert.SecondOrderComplete
import Breakdown.FracCert.GradientAdd

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Assembly

open SteadyCert

namespace AdmissibleLinearInternal

theorem turnStep_zero (m : ℕ) : turnStep m 0 = 0 := by
  ext i
  fin_cases i <;> simp [turnStep]

theorem mirror_zero : mirror 0 = 0 := by
  ext i
  fin_cases i <;> simp [mirror]

theorem turnStep_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem mirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror]
  ring

theorem turnStep_smul (m : ℕ) (r : ℝ) (a : Space) : turnStep m (r • a) = r • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem mirror_smul (r : ℝ) (a : Space) : mirror (r • a) = r • mirror a := by
  ext i
  fin_cases i <;> simp [mirror]

theorem class_zero (m : ℕ) : IsClassField m (0 : Space → Space) := by
  refine ⟨Filter.Eventually.of_forall fun y => ?_, Filter.Eventually.of_forall fun y => ?_⟩
  · simp [turnStep_zero]
  · simp [mirror_zero]

theorem class_add {m : ℕ} {v u : Space → Space} (hv : IsClassField m v) (hu : IsClassField m u) :
    IsClassField m (v + u) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hv.1, hu.1] with y h1 h2
    simp [Pi.add_apply, h1, h2, turnStep_add]
  · filter_upwards [hv.2, hu.2] with y h1 h2
    simp [Pi.add_apply, h1, h2, mirror_add]

theorem class_smul {m : ℕ} (r : ℝ) {v : Space → Space} (hv : IsClassField m v) :
    IsClassField m (r • v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hv.1] with y h1
    simp [Pi.smul_apply, h1, turnStep_smul]
  · filter_upwards [hv.2] with y h1
    simp [Pi.smul_apply, h1, mirror_smul]

theorem gradient_zero : IsGradientField (0 : Space → Space) := by
  refine ⟨fun _ => 0, ?_, ?_, aestronglyMeasurable_const, ?_⟩
  · intro K _
    simp
  · intro K _
    simp
  · intro φ _ j
    simp

theorem gradient_smul (r : ℝ) {Q : Space → Space} (hQ : IsGradientField Q) :
    IsGradientField (r • Q) := by
  obtain ⟨q, hq, hQ2, hQm, hid⟩ := hQ
  refine ⟨fun y => r * q y, ?_, ?_, hQm.const_smul r, ?_⟩
  · intro K hK
    have h := (hq K hK).const_mul (r ^ 2)
    refine IntegrableOn.congr_fun h (fun y _ => ?_) hK.measurableSet
    ring
  · intro K hK
    have h := (hQ2 K hK).const_mul (r ^ 2)
    refine IntegrableOn.congr_fun h (fun y _ => ?_) hK.measurableSet
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  · intro φ hφ j
    have h := hid φ hφ j
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) * (r * q y)) =
        fun y => r * (fderiv ℝ φ y (unitVector j) * q y) := by
      funext y; ring
    have e2 : (fun y => φ y * inner ℝ ((r • Q) y) (unitVector j)) =
        fun y => r * (φ y * inner ℝ (Q y) (unitVector j)) := by
      funext y; simp only [Pi.smul_apply, real_inner_smul_left]; ring
    rw [e1, e2, integral_const_mul, integral_const_mul, h]
    ring

theorem second_zero (m : ℕ) :
    IsSecondOrderField m (0 : Space → Space) (0 : Space → (Space →L[ℝ] Space))
      (0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)) where
  measurable_velocity := aestronglyMeasurable_const
  measurable_gradient := aestronglyMeasurable_const
  measurable_second := aestronglyMeasurable_const
  velocity_six := MemLp.zero
  gradient_two := by simp [entrySq]
  second_two := by simp
  weak_gradient := by
    intro φ _ j
    simp
  weak_second := by
    intro φ _ i j
    simp
  divergence := Filter.Eventually.of_forall fun y => by simp
  symmetric := class_zero m

end AdmissibleLinearInternal

open AdmissibleLinearInternal

theorem admissibleLinear : AdmissibleLinearStatement := by
  intro k N c
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨second_zero c.order, gradient_zero, class_zero c.order⟩
  · rintro x x' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, class_add h3 h3'⟩
    · have h := secondOrderLinear c.order _ _ _ _ _ _ 1 h1 h1'
      simp only [one_smul] at h
      exact h
    · exact gradientAdd _ _ h2 h2'
  · rintro r x ⟨h1, h2, h3⟩
    refine ⟨?_, gradient_smul r h2, class_smul r h3⟩
    have h := secondOrderLinear c.order _ _ _ _ _ _ r (second_zero c.order) h1
    simp only [Pi.zero_apply, zero_add] at h
    exact h

end Assembly

end CellCert

end Breakdown
