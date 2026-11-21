import Breakdown.CertCell.ShapeKeyTime

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

def keyTimeFactor (κ : FieldKey) (σ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I)

theorem keyTimeFactor_ne_zero (κ : FieldKey) (σ : ℝ) : keyTimeFactor κ σ ≠ 0 :=
  Complex.exp_ne_zero _

theorem keyTimeFactor_add_one (κ : FieldKey) (σ : ℝ) : keyTimeFactor κ (σ + 1) = keyTimeFactor κ σ := by
  unfold keyTimeFactor
  have h : (((2 * Real.pi * (labelTime κ.label : ℝ) * (σ + 1) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) +
        ((labelTime κ.label : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem contDiff_keyTimeFactor (κ : FieldKey) {n : WithTop ℕ∞} : ContDiff ℝ n (keyTimeFactor κ) := by
  unfold keyTimeFactor
  refine Complex.contDiff_exp.comp ?_
  refine ContDiff.mul ?_ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)

theorem keyVector_eq_timeFactor (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) :
    keyVector P κ A σ = keyTimeFactor κ σ • keyVector P κ A 0 := by
  funext y i
  have h := keyPhase_add_time P κ 0 σ y
  rw [zero_add] at h
  simp only [keyVector, Pi.smul_apply, smul_eq_mul, h, keyTimeFactor]
  ring

theorem keySecondDeriv_eq_timeFactor (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (y : Space) :
    keyHess P κ A σ y = keyTimeFactor κ σ • keyHess P κ A 0 y := by
  have := invertibleOfNonzero (keyTimeFactor_ne_zero κ σ)
  unfold keyHess
  rw [keyVector_eq_timeFactor]
  have h : (fun x => fderiv ℝ (keyTimeFactor κ σ • keyVector P κ A 0) x) =
      keyTimeFactor κ σ • fun x => fderiv ℝ (keyVector P κ A 0) x :=
    funext fun x => fderiv_const_smul_of_invertible (keyTimeFactor κ σ)
  rw [h, fderiv_const_smul_of_invertible]

theorem keyVector_add_one (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) :
    keyVector P κ A (σ + 1) = keyVector P κ A σ := by
  rw [keyVector_eq_timeFactor, keyTimeFactor_add_one, ← keyVector_eq_timeFactor]

end Internal

open Internal in
theorem fieldJointSmooth_of (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) : FieldJointSmooth := by
  intro P D hP hD
  have hsm : ∀ κ ∈ D.keys, ContDiff ℝ 1 (keyVector P κ (D.amp κ) 0) := by
    intro κ hκ
    by_cases h : κ.label.1 = 0
    · exact (h2 P D κ 0 hP hD hκ h).smooth
    · exact (h1 P D κ 0 hP hD hκ h).smooth
  have hfield : (fun z : ℝ × Space => shapeInfoField P D z.1 z.2) =
      fun z => realPartVec (∑ κ ∈ D.keys, keyTimeFactor κ z.1 • keyVector P κ (D.amp κ) 0 z.2) := by
    funext z
    simp only [shapeInfoField, complexField]
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [keyVector_eq_timeFactor]
    rfl
  have hhess : (fun z : ℝ × Space => shapeHess P D z.1 z.2) =
      fun z => ∑ κ ∈ D.keys, (ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] (Fin 3 → ℂ)) (Space →L[ℝ] Space)
        (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec))
          (keyTimeFactor κ z.1 • keyHess P κ (D.amp κ) 0 z.2) := by
    funext z
    simp only [shapeHess]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [keySecondDeriv_eq_timeFactor P κ (D.amp κ) z.1 z.2]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfield]
    refine realPartVec.contDiff.comp (ContDiff.sum fun κ hκ => ?_)
    exact ((contDiff_keyTimeFactor κ).comp contDiff_fst).smul ((hsm κ hκ).comp contDiff_snd)
  · intro σ y
    simp only [shapeInfoField, complexField, keyVector_add_one]
  · rw [hhess]
    refine (Finset.measurable_sum _ fun κ _ => ?_).aestronglyMeasurable
    refine (ContinuousLinearMap.continuous _).measurable.comp ?_
    exact ((contDiff_keyTimeFactor κ (n := 0)).continuous.measurable.comp measurable_fst).smul
      ((measurable_fderiv ℝ _).comp measurable_snd)
  · intro σ y
    simp only [shapeHess, keyHess, keyVector_add_one]

end GivenShape

end CertCell

end Breakdown
