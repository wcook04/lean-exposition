import Breakdown.Frac.StTorusCoef
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

open FreqTrSeries.Internal

private theorem norm_complexify_eq (v : Space) : ‖complexify v‖ = ‖v‖ := by
  simp [complexify, EuclideanSpace.norm_eq]

private theorem integrableOn_coef_of {G : Space → Space} (hG : IntegrableOn G cell) (k : Lattice) :
    IntegrableOn (fun x => character k x • complexify (G x)) cell := by
  have h1 : IntegrableOn (fun x => complexify (G x)) cell :=
    Integrable.mono' hG.norm (continuous_complexify.comp_aestronglyMeasurable hG.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (norm_complexify_eq (G x)).le)
  exact h1.continuousOn_smul (continuous_character k).continuousOn isCompact_cell

private theorem coef_apply_of {G : Space → Space} (hG : IntegrableOn G cell) (k : Lattice) (i : Fin 3) :
    (freqTrCoef G k).ofLp i = ∫ x in cell, character k x * ((G x).ofLp i : ℂ) := by
  have h := (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm (integrableOn_coef_of hG k)
  unfold freqTrCoef
  change EuclideanSpace.proj (𝕜 := ℂ) i _ = _
  rw [← h]
  rfl

private theorem inner_smul_single (v : Space) (c : ℝ) (i : Fin 3) :
    inner ℝ v (c • EuclideanSpace.single i (1 : ℝ)) = c * v.ofLp i := by
  rw [real_inner_smul_right]
  simp [EuclideanSpace.inner_single_right]

private theorem character_eq (k : Lattice) (x : Space) :
    character k x = (Real.cos (inner ℝ ((2 * π) • freq k) x + 0) : ℂ) -
      Complex.I * (Real.cos (inner ℝ ((2 * π) • freq k) x + (-(π / 2))) : ℂ) := by
  have e : -(2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) =
      ((-(2 * π * inner ℝ (freq k) x) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [character, e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, real_inner_smul_left, add_zero, ← sub_eq_add_neg, Real.cos_sub_pi_div_two]
  push_cast
  ring

private theorem integrableOn_cos_mul {G : Space → Space} (hG : IntegrableOn G cell) (ξ : Space)
    (φ : ℝ) (i : Fin 3) :
    IntegrableOn (fun x => Real.cos (inner ℝ ξ x + φ) * (G x).ofLp i) cell := by
  have hc : IntegrableOn (fun x => (G x).ofLp i) cell :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hG
  refine hc.continuousOn_mul ?_ isCompact_cell
  exact (by fun_prop : Continuous fun x : Space => Real.cos (inner ℝ ξ x + φ)).continuousOn

private theorem coef_split {G : Space → Space} (hG : IntegrableOn G cell) (k : Lattice) (i : Fin 3) :
    (freqTrCoef G k).ofLp i =
      ((∫ x in cell, Real.cos (inner ℝ ((2 * π) • freq k) x + 0) * (G x).ofLp i : ℝ) : ℂ) -
        Complex.I * ((∫ x in cell, Real.cos (inner ℝ ((2 * π) • freq k) x + (-(π / 2))) *
          (G x).ofLp i : ℝ) : ℂ) := by
  rw [coef_apply_of hG, ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul, ← integral_sub]
  · congr 1
    funext x
    rw [character_eq]
    push_cast
    ring
  · exact (integrableOn_cos_mul hG _ _ i).ofReal
  · exact ((integrableOn_cos_mul hG _ _ i).ofReal).const_mul _

private theorem contDiff_wave (ξ c : Space) (φ : ℝ) :
    ContDiff ℝ ∞ (fun y : Space => Real.cos (inner ℝ ξ y + φ) • c) :=
  (Real.contDiff_cos.comp ((ContDiff.inner ℝ contDiff_const contDiff_id).add contDiff_const)).smul
    contDiff_const

private theorem isPeriodic_wave (k : Lattice) (c : Space) (φ : ℝ) :
    IsPeriodic (fun y : Space => Real.cos (inner ℝ ((2 * π) • freq k) y + φ) • c) := by
  intro j x
  simp only
  rw [inner_add_right, real_inner_smul_left (freq k) (unitVector j),
    CoefCalculus.Internal.inner_freq_unitVector,
    show inner ℝ ((2 * π) • freq k) x + 2 * π * (k j : ℝ) + φ =
      inner ℝ ((2 * π) • freq k) x + φ + (k j : ℤ) * (2 * π) by ring,
    Real.cos_add_int_mul_two_pi]

private theorem cos_integral_scale (α : ℝ) (hE : PlaneWaveEigen α) (hP : PeriodicSymmetry α)
    {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f) (k : Lattice) (φ : ℝ)
    (i : Fin 3) :
    (∫ x in cell, Real.cos (inner ℝ ((2 * π) • freq k) x + φ) * (fractionalPowerAt α f x).ofLp i) =
      (2 * π * ‖freq k‖) ^ (2 * α) *
        ∫ x in cell, Real.cos (inner ℝ ((2 * π) • freq k) x + φ) * (f x).ofLp i := by
  set ξ : Space := (2 * π) • freq k with hξ
  have hn : ‖ξ‖ = 2 * π * ‖freq k‖ := by
    rw [hξ, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have key := (hP f (fun y => Real.cos (inner ℝ ξ y + φ) • EuclideanSpace.single i (1 : ℝ)) hf
    (contDiff_wave _ _ _) hp (isPeriodic_wave k _ φ)).2
  simp only [inner_smul_single] at key
  rw [key]
  simp only [hE ξ (EuclideanSpace.single i (1 : ℝ)) φ, inner_smul_single, hn]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem coefFractional_of (α : ℝ) (hE : PlaneWaveEigen α) (hP : PeriodicSymmetry α) :
    CoefFractional α := by
  intro f hf hp k
  have hF : IntegrableOn (fractionalPowerAt α f) cell := (hP f f hf hf hp hp).1
  have hf' : IntegrableOn f cell := hf.continuous.continuousOn.integrableOn_compact isCompact_cell
  ext i
  rw [PiLp.smul_apply, coef_split hF, coef_split hf', cos_integral_scale α hE hP hf hp,
    cos_integral_scale α hE hP hf hp, Complex.real_smul]
  push_cast
  ring

end Breakdown.Periodic
