import Breakdown.Frac.StTorusCoef
import Breakdown.Frac.StOperator

open MeasureTheory Real

noncomputable section

namespace Breakdown.Periodic

namespace TorusPlaneWave

private lemma phaseHasFDerivAt (ξ : Space) (φ₀ : ℝ) (y : Space) :
    HasFDerivAt (fun y : Space => inner ℝ ξ y + φ₀) (innerSL ℝ ξ) y := by
  have h := ((innerSL ℝ ξ).hasFDerivAt (x := y)).add_const φ₀
  simpa [innerSL_apply_apply] using h

private lemma cosHasFDerivAt (ξ : Space) (φ₀ : ℝ) (y : Space) :
    HasFDerivAt (fun y : Space => Real.cos (inner ℝ ξ y + φ₀))
      ((-Real.sin (inner ℝ ξ y + φ₀)) • innerSL ℝ ξ) y :=
by
  have h := (Real.hasDerivAt_cos (inner ℝ ξ y + φ₀)).comp_hasFDerivAt y (phaseHasFDerivAt ξ φ₀ y)
  exact h

private lemma sinHasFDerivAt (ξ : Space) (φ₀ : ℝ) (y : Space) :
    HasFDerivAt (fun y : Space => Real.sin (inner ℝ ξ y + φ₀))
      (Real.cos (inner ℝ ξ y + φ₀) • innerSL ℝ ξ) y :=
by
  have h := (Real.hasDerivAt_sin (inner ℝ ξ y + φ₀)).comp_hasFDerivAt y (phaseHasFDerivAt ξ φ₀ y)
  exact h

private lemma waveFirst (ξ c : Space) (φ₀ : ℝ) (y : Space) :
    HasFDerivAt (fun y : Space => Real.cos (inner ℝ ξ y + φ₀) • c)
      ((-Real.sin (inner ℝ ξ y + φ₀)) • (innerSL ℝ ξ).smulRight c) y := by
  have h := (cosHasFDerivAt ξ φ₀ y).smul_const c
  refine h.congr_fderiv ?_
  ext z : 1
  simp [smul_smul]

private lemma waveFderiv (ξ c : Space) (φ₀ : ℝ) :
    fderiv ℝ (fun y : Space => Real.cos (inner ℝ ξ y + φ₀) • c) =
      fun y => (-Real.sin (inner ℝ ξ y + φ₀)) • (innerSL ℝ ξ).smulRight c := by
  funext y
  exact (waveFirst ξ c φ₀ y).fderiv

private lemma waveSecond (ξ c : Space) (φ₀ : ℝ) (y : Space) :
    HasFDerivAt (fun y : Space => (-Real.sin (inner ℝ ξ y + φ₀)) • (innerSL ℝ ξ).smulRight c)
      ((-(Real.cos (inner ℝ ξ y + φ₀) • innerSL ℝ ξ)).smulRight ((innerSL ℝ ξ).smulRight c)) y :=
  (sinHasFDerivAt ξ φ₀ y).neg.smul_const _

private lemma waveIterated (ξ c : Space) (φ₀ : ℝ) (x z : Space) :
    iteratedFDeriv ℝ 2 (fun y : Space => Real.cos (inner ℝ ξ y + φ₀) • c) x ![z, z] =
      (-(Real.cos (inner ℝ ξ x + φ₀) * (inner ℝ ξ z * inner ℝ ξ z))) • c := by
  rw [iteratedFDeriv_two_apply, waveFderiv, (waveSecond ξ c φ₀ x).fderiv]
  simp [smul_smul, mul_comm, mul_assoc]

private lemma waveRemainder (ξ c : Space) (φ₀ : ℝ) (x z : Space) :
    secondOrderRemainder (fun y : Space => Real.cos (inner ℝ ξ y + φ₀) • c) x z =
      (Real.cos (inner ℝ ξ x + φ₀) * (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2)
        - Real.sin (inner ℝ ξ x + φ₀) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) • c := by
  unfold secondOrderRemainder
  rw [waveIterated, (waveFirst ξ c φ₀ x).fderiv]
  have hadd : inner ℝ ξ (x + z) + φ₀ = (inner ℝ ξ x + φ₀) + inner ℝ z ξ := by
    rw [inner_add_right, real_inner_comm z ξ]
    ring
  have hcomm : inner ℝ ξ z = inner ℝ z ξ := real_inner_comm z ξ
  have hc := Real.cos_add (inner ℝ ξ x + φ₀) (inner ℝ z ξ)
  simp only [hadd, hc, hcomm, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul, ← sub_smul]
  congr 1
  ring

end TorusPlaneWave

open TorusPlaneWave in
theorem planeWaveEigen_of (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2) (hS : SymbolScalarStatement)
    (hN : NormalizerStatement) : PlaneWaveEigen α := by
  intro ξ c φ₀ x
  obtain ⟨hI1, hE1, hI2, hE2⟩ := hS α h1 h2 ξ
  have hM : 0 < fractionalNormalizer α := (hN α h1 (by linarith)).2
  set a := inner ℝ ξ x + φ₀ with ha
  have hpt : (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) •
      secondOrderRemainder (fun y : Space => Real.cos (inner ℝ ξ y + φ₀) • c) x z) =
      fun z => (Real.cos a * (‖z‖ ^ (-(3 + 2 * α)) *
          (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2))
        - Real.sin a * (‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ))) • c := by
    funext z
    rw [waveRemainder, smul_smul]
    congr 1
    ring
  unfold fractionalPowerAt
  rw [hpt, integral_smul_const, integral_sub (hI1.const_mul _) (hI2.const_mul _),
    integral_const_mul, integral_const_mul, hE1, hE2, smul_smul]
  congr 1
  field_simp
  ring

end Breakdown.Periodic
