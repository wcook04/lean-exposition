import Breakdown.Cert.ExtendedCoerciveNodes

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.SecondDerivSymm

theorem locallyIntegrable_apply {F : Space → (Space →L[ℝ] Space)}
    (hF : LocallyIntegrable F volume) (v : Space) :
    LocallyIntegrable (fun y => F y v) volume := by
  rw [locallyIntegrable_iff] at hF ⊢
  intro K hK
  exact (hF K hK).apply_continuousLinearMap v

theorem integral_smul_fderiv_of_test {f : Space → Space} (hf : ContDiff ℝ 1 f)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (e : Space) :
    ∫ y, ψ y • fderiv ℝ f y e = -∫ y, fderiv ℝ ψ y e • f y := by
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · apply Continuous.integrable_of_hasCompactSupport
    · exact ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).smul hf.continuous
    · exact (hc.fderiv_apply (𝕜 := ℝ) e).smul_right
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hψ.continuous.smul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    · exact hc.smul_right
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hψ.continuous.smul hf.continuous
    · exact hc.smul_right
  · exact fun x _ => (hψ.differentiable (by simp)) x
  · exact fun x _ => (hf.differentiable (by simp)) x

theorem fderiv_fderiv_apply {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (e v y : Space) :
    fderiv ℝ (fun x => fderiv ℝ φ x e) y v = fderiv ℝ (fderiv ℝ φ) y v e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

theorem pairing_eq {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {f : Space → Space} (hf : ContDiff ℝ 1 f) (i j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ f y (unitVector j) =
      -∫ y, fderiv ℝ (fderiv ℝ φ) y (unitVector i) (unitVector j) • f y := by
  have hψ : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (unitVector i)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [integral_smul_fderiv_of_test hf hψ (hc.fderiv_apply (𝕜 := ℝ) (unitVector i)) (unitVector j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [fderiv_fderiv_apply hφ, (hφ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) (unitVector j) (unitVector i)]

theorem bilinear_symm_of_basis {A : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ i j : Fin 3, A (unitVector i) (unitVector j) = A (unitVector j) (unitVector i))
    (a b : Space) : A a b = A b a := by
  have hx : ∀ x : Space, x = ∑ i : Fin 3, x i • unitVector i := fun x => by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp [unitVector]
  rw [hx a, hx b]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h, mul_comm]

end Internal.SecondDerivSymm

open Internal.SecondDerivSymm in
theorem weakSecondDerivSymmetricHolds_proof : WeakSecondDerivSymmetricHolds := by
  intro W HW D hW σ
  have hf : ContDiff ℝ 1 (W σ) :=
    hW.smooth.comp ((contDiff_const (c := σ)).prodMk contDiff_id)
  have hij : ∀ i j : Fin 3,
      ∀ᵐ y, HW σ y (unitVector i) (unitVector j) = HW σ y (unitVector j) (unitVector i) := by
    intro i j
    obtain ⟨-, hLj, hj⟩ := hW.secondDeriv_weak σ j
    obtain ⟨-, hLi, hi⟩ := hW.secondDeriv_weak σ i
    refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_apply hLj (unitVector i))
      (locallyIntegrable_apply hLi (unitVector j)) fun φ hφ hc => ?_
    have e1 := hj φ ⟨hφ, hc⟩ i
    have e2 := hi φ ⟨hφ, hc⟩ j
    simp only [ContinuousLinearMap.flip_apply] at e1 e2
    rw [e1, e2, pairing_eq hφ hc hf i j, pairing_eq hφ hc hf j i]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [(hφ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) (unitVector i) (unitVector j)]
  have hall : ∀ᵐ y, ∀ i j : Fin 3,
      HW σ y (unitVector i) (unitVector j) = HW σ y (unitVector j) (unitVector i) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact hij i
  filter_upwards [hall] with y hy a b
  exact bilinear_symm_of_basis hy a b

end CoerciveWeak

end Breakdown
