/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The phase mean, oscillatory projection and integration-by-parts arguments
adapt `CCPoint/Framework/Cascade3/Periodic.lean` from the preserved September
11 CCPoint archive to a single phase of period one. The primitive uses the
integral from zero and subtraction of its average as in Appendix D.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Phase average over the frozen paper's unit period. -/
def phaseMean (f : ℝ → E) : E :=
  ∫ s in (0 : ℝ)..1, f s

/-- The oscillatory part of a profile at fixed time and label. -/
def phaseOscillation (f : ℝ → E) (s : ℝ) : E :=
  f s - phaseMean f

theorem phaseMean_add {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    phaseMean (fun s => f s + g s) = phaseMean f + phaseMean g :=
  intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)

theorem phaseMean_sub {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    phaseMean (fun s => f s - g s) = phaseMean f - phaseMean g :=
  intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)

theorem phaseMean_const_smul (c : ℝ) (f : ℝ → E) :
    phaseMean (fun s => c • f s) = c • phaseMean f :=
  intervalIntegral.integral_smul c f

theorem periodic_phaseOscillation {f : ℝ → E} (hf : Function.Periodic f 1) :
    Function.Periodic (phaseOscillation f) 1 := by
  intro s
  simp only [phaseOscillation, hf s]

/-- The primitive based at phase zero, shifted to have zero phase mean. -/
def phasePrimitive (f : ℝ → E) : ℝ → E :=
  phaseOscillation (fun s => ∫ σ in (0 : ℝ)..s, f σ)

theorem periodic_phasePrimitive {f : ℝ → E} (hf : Continuous f) (hper : Function.Periodic f 1)
    (hmean : phaseMean f = 0) : Function.Periodic (phasePrimitive f) 1 := by
  apply periodic_phaseOscillation
  intro s
  have h := hper.intervalIntegral_add_eq_add 0 s (fun a b => hf.intervalIntegrable a b)
  rw [zero_add, ← phaseMean, hmean, add_zero] at h
  exact h

theorem norm_phaseMean_le {f : ℝ → E} {M : ℝ}
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f s‖ ≤ M) : ‖phaseMean f‖ ≤ M := by
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (f := f) (fun s hs => by
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact hM s ⟨hs.1.le, hs.2⟩)
  simpa [phaseMean] using bound

theorem norm_phaseOscillation_le {f : ℝ → E} {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) (s : ℝ) :
    ‖phaseOscillation f s‖ ≤ 2 * M := by
  calc
    ‖phaseOscillation f s‖ ≤ ‖f s‖ + ‖phaseMean f‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hM s) (norm_phaseMean_le (fun σ _ => hM σ))
    _ = 2 * M := (two_mul M).symm

/-- The order-zero primitive bound of Appendix D, uniform in the phase. -/
theorem norm_phasePrimitive_le {f : ℝ → E} (hf : Continuous f) (hper : Function.Periodic f 1)
    (hmean : phaseMean f = 0) {M : ℝ} (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f s‖ ≤ M)
    (s : ℝ) : ‖phasePrimitive f s‖ ≤ 2 * M := by
  have hM0 := (norm_nonneg (f 0)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hbase : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ‖∫ τ in (0 : ℝ)..σ, f τ‖ ≤ M := by
    intro σ hσ
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := σ) (f := f) (fun τ hτ => by
        rw [Set.uIoc_of_le hσ.1] at hτ
        exact hM τ ⟨hτ.1.le, hτ.2.trans hσ.2⟩)
    rw [sub_zero, abs_of_nonneg hσ.1] at hnorm
    exact hnorm.trans (mul_le_of_le_one_right hM0 hσ.2)
  have hs : Int.fract s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  have hshift : phasePrimitive f (Int.fract s) = phasePrimitive f s := by
    simpa only [Int.fract, mul_one] using
      (periodic_phasePrimitive hf hper hmean).sub_int_mul_eq (x := s) ⌊s⌋
  rw [← hshift]
  calc
    ‖phasePrimitive f (Int.fract s)‖ ≤
        ‖∫ τ in (0 : ℝ)..Int.fract s, f τ‖ + ‖phaseMean (fun σ => ∫ τ in (0 : ℝ)..σ, f τ)‖ :=
      norm_sub_le _ _
    _ ≤ M + M := add_le_add (hbase _ hs) (norm_phaseMean_le hbase)
    _ = 2 * M := (two_mul M).symm

variable [CompleteSpace E]

@[simp] theorem phaseMean_const (c : E) : phaseMean (fun _ => c) = c := by
  simp [phaseMean]

theorem phaseMean_phaseOscillation {f : ℝ → E} (hf : Continuous f) :
    phaseMean (phaseOscillation f) = 0 := by
  unfold phaseOscillation
  rw [phaseMean_sub hf continuous_const, phaseMean_const, sub_self]

theorem hasDerivAt_phasePrimitive {f : ℝ → E} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (phasePrimitive f) (f s) s := by
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 s)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).sub_const _

theorem phaseMean_phasePrimitive {f : ℝ → E} (hf : Continuous f) :
    phaseMean (phasePrimitive f) = 0 :=
  phaseMean_phaseOscillation (intervalIntegral.differentiable_integral_of_continuous hf).continuous

theorem phaseMean_deriv {f df : ℝ → E} (hderiv : ∀ s, HasDerivAt f (df s) s)
    (hdf : Continuous df) (hper : Function.Periodic f 1) : phaseMean df = 0 := by
  have hclose : f 1 = f 0 := by simpa only [zero_add] using hper 0
  unfold phaseMean
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hdf.intervalIntegrable 0 1), hclose, sub_self]

/-- Integrating a phase derivative recovers its profile up to the phase mean. -/
theorem phasePrimitive_deriv {f df : ℝ → E} (hderiv : ∀ s, HasDerivAt f (df s) s)
    (hdf : Continuous df) : phasePrimitive df = phaseOscillation f := by
  have hbase : (fun s => ∫ σ in (0 : ℝ)..s, df σ) = fun s => f s - f 0 := by
    funext s
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
      (hdf.intervalIntegrable 0 s)
  have hf : Differentiable ℝ f := fun s => (hderiv s).differentiableAt
  unfold phasePrimitive phaseOscillation
  rw [hbase, phaseMean_sub hf.continuous continuous_const, phaseMean_const]
  funext s
  exact sub_sub_sub_cancel_right (f s) (phaseMean f) (f 0)

/-- Periodic integration by parts for the scalar weight and vector profile in §5. -/
theorem phaseMean_smul_deriv {u du : ℝ → ℝ} {v dv : ℝ → E}
    (hu : ∀ s, HasDerivAt u (du s) s) (hv : ∀ s, HasDerivAt v (dv s) s)
    (hdu : Continuous du) (hdv : Continuous dv)
    (huper : Function.Periodic u 1) (hvper : Function.Periodic v 1) :
    phaseMean (fun s => u s • dv s) = -phaseMean (fun s => du s • v s) := by
  have huclose : u 1 = u 0 := by simpa only [zero_add] using huper 0
  have hvclose : v 1 = v 0 := by simpa only [zero_add] using hvper 0
  unfold phaseMean
  rw [intervalIntegral.integral_smul_deriv_eq_deriv_smul (fun s _ => hu s) (fun s _ => hv s)
    (hdu.intervalIntegrable 0 1) (hdv.intervalIntegrable 0 1), huclose, hvclose, sub_self, zero_sub]

end

end TorusEuler
