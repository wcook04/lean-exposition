import Breakdown.Profile.StatementsField

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma fderiv_smul_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a c : ℝ) (f : Space → F) :
    fderiv ℝ (fun y => a • f (c • y)) = fun x => (a * c) • fderiv ℝ f (c • x) := by
  have h : (fun y => a • f (c • y)) = a • (fun y => f (c • y)) := rfl
  rw [h, fderiv_const_smul_field]
  funext x
  rw [Pi.smul_apply, fderiv_comp_smul, smul_smul]

private lemma fderiv_dilateField (μ : ℝ) (f : Space → Space) :
    fderiv ℝ (dilateField μ f) =
      fun x => (Real.sqrt μ * Real.sqrt μ) • fderiv ℝ f (Real.sqrt μ • x) :=
  fderiv_smul_comp_smul _ _ f

private lemma fderiv_fderiv_dilateField (μ : ℝ) (f : Space → Space) :
    fderiv ℝ (fderiv ℝ (dilateField μ f)) =
      fun x => (Real.sqrt μ * Real.sqrt μ * Real.sqrt μ) •
        fderiv ℝ (fderiv ℝ f) (Real.sqrt μ • x) := by
  rw [fderiv_dilateField]
  exact fderiv_smul_comp_smul _ _ (fderiv ℝ f)

theorem decayFieldSub_holds : DecayFieldSub := by
  intro f g hf hg
  obtain ⟨hfs, hfd, Cf, hCf⟩ := hf
  obtain ⟨hgs, hgd, Cg, hCg⟩ := hg
  have hfD : Differentiable ℝ f := hfs.differentiable (by simp)
  have hgD : Differentiable ℝ g := hgs.differentiable (by simp)
  have hder : ∀ y, fderiv ℝ (f - g) y = fderiv ℝ f y - fderiv ℝ g y :=
    fun y => fderiv_sub (hfD y) (hgD y)
  refine ⟨hfs.sub hgs, ?_, Cf + Cg, ?_⟩
  · intro y
    have h1 := hfd y
    have h2 := hgd y
    unfold divergenceAt at h1 h2 ⊢
    simp only [hder, sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib,
      h1, h2, sub_zero]
  · intro y
    obtain ⟨hf1, hf2⟩ := hCf y
    obtain ⟨hg1, hg2⟩ := hCg y
    refine ⟨?_, ?_⟩
    · calc ‖(f - g) y‖ = ‖f y - g y‖ := rfl
        _ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
        _ ≤ Cf / (1 + ‖y‖) + Cg / (1 + ‖y‖) := add_le_add hf1 hg1
        _ = (Cf + Cg) / (1 + ‖y‖) := (add_div _ _ _).symm
    · calc ‖fderiv ℝ (f - g) y‖ = ‖fderiv ℝ f y - fderiv ℝ g y‖ := by rw [hder]
        _ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_sub_le _ _
        _ ≤ Cf / (1 + ‖y‖) ^ 2 + Cg / (1 + ‖y‖) ^ 2 := add_le_add hf2 hg2
        _ = (Cf + Cg) / (1 + ‖y‖) ^ 2 := (add_div _ _ _).symm

theorem dilateCalculus_holds : DilateCalculus := by
  intro μ f _ x
  refine ⟨?_, ?_, ?_⟩
  · rw [fderiv_dilateField, sq]
  · unfold sumSecondPartialsAt
    simp only [iteratedFDeriv_two_apply, fderiv_fderiv_dilateField,
      smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_three, mul_assoc]
  · unfold advectionAt
    rw [fderiv_dilateField]
    simp only [dilateField, smul_apply, map_smul, smul_smul]
    rw [pow_three]

theorem gradientScale_holds : GradientScale := by
  intro c g _ x
  unfold gradientAt
  have h : fderiv ℝ (fun y => g (c • y)) x = c • fderiv ℝ g (c • x) := fderiv_comp_smul c
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, smul_eq_mul, mul_smul]

end Breakdown
