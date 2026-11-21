import Breakdown.Profile.StatementsField

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem smooth_dir {h : Space → Space} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

private theorem smooth_dir_scalar {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

private theorem integrable_inner_right {a b : Space → Space} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport b) : Integrable (fun x => inner ℝ (a x) (b x)) := by
  refine (ha.inner hb).integrable_of_hasCompactSupport (hs.mono' ?_)
  intro x hx
  apply subset_tsupport
  intro h
  apply hx
  simp [h]

private theorem integrable_mul_right {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport b) : Integrable (fun x => a x * b x) := by
  refine (ha.mul hb).integrable_of_hasCompactSupport (hs.mono' ?_)
  intro x hx
  apply subset_tsupport
  intro h
  apply hx
  simp [h]

private theorem second_dir {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x v : Space) :
    iteratedFDeriv ℝ 2 f x ![v, v] = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

private theorem sumSecondPartials_eq {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x : Space) :
    sumSecondPartialsAt f x = ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) x (unitVector i) := by
  unfold sumSecondPartialsAt
  exact Finset.sum_congr rfl fun i _ => second_dir hf x (unitVector i)

private theorem one_pair {f φ : Space → Space} (hf : ContDiff ℝ ∞ f) (hφ : IsTestField φ) (i : Fin 3) :
    ∫ x, inner ℝ (fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) x (unitVector i)) (φ x) =
      -∫ x, inner ℝ (fderiv ℝ f x (unitVector i)) (fderiv ℝ φ x (unitVector i)) := by
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hF := smooth_dir hf (unitVector i)
  have hFF := smooth_dir hF (unitVector i)
  have hΦ := smooth_dir hφs (unitVector i)
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := innerSL ℝ) (v := unitVector i)
    (f := fun y => fderiv ℝ f y (unitVector i)) (g := φ)
    (integrable_inner_right hFF.continuous hφs.continuous hφc)
    (integrable_inner_right hF.continuous hΦ.continuous (hφc.fderiv_apply (𝕜 := ℝ) _))
    (integrable_inner_right hF.continuous hφs.continuous hφc)
    (fun x _ => (hF.differentiable (by simp)) x)
    (fun x _ => (hφs.differentiable (by simp)) x)
  change ∫ x, inner ℝ (fderiv ℝ f x (unitVector i)) (fderiv ℝ φ x (unitVector i)) =
    -∫ x, inner ℝ (fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) x (unitVector i)) (φ x) at key
  rw [key, neg_neg]

private theorem coord_smooth {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => φ y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hφ

private theorem coord_dir {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => φ y i) x v = fderiv ℝ φ x v i := by
  have hd : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have e : (fun y => φ y i) = (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ φ := by
    funext y
    simp
  rw [e, h]
  simp

private theorem gradient_inner (g : Space → ℝ) (x w : Space) :
    inner ℝ (gradientAt g x) w = ∑ i : Fin 3, fderiv ℝ g x (unitVector i) * w i := by
  unfold gradientAt
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]
  simp

private theorem one_grad {g : Space → ℝ} {φ : Space → Space} (hg : ContDiff ℝ ∞ g) (hφs : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    ∫ x, fderiv ℝ g x (unitVector i) * φ x i =
      -∫ x, g x * fderiv ℝ (fun y => φ y i) x (unitVector i) := by
  have hψs := coord_smooth hφs i
  have hψc : HasCompactSupport (fun y => φ y i) :=
    hφc.comp_left (g := fun w : Space => w i) (by simp)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (v := unitVector i) (f := g) (g := fun y => φ y i)
    (integrable_mul_right (smooth_dir_scalar hg _).continuous hψs.continuous hψc)
    (integrable_mul_right hg.continuous (smooth_dir_scalar hψs _).continuous
      (hψc.fderiv_apply (𝕜 := ℝ) _))
    (integrable_mul_right hg.continuous hψs.continuous hψc)
    (fun x _ => (hg.differentiable (by simp)) x)
    (fun x _ => (hψs.differentiable (by simp)) x)
  rw [key, neg_neg]

theorem sumSecondPartialsPairing_holds : SumSecondPartialsPairing := by
  intro f φ hf hφ
  obtain ⟨hφs, hφc, hφd⟩ := hφ
  have hφ : IsTestField φ := ⟨hφs, hφc, hφd⟩
  unfold gradientPairing
  simp_rw [sumSecondPartials_eq hf, sum_inner]
  rw [integral_finsetSum _ (fun i _ => integrable_inner_right
      (smooth_dir (smooth_dir hf (unitVector i)) (unitVector i)).continuous hφs.continuous hφc),
    integral_finsetSum _ (fun i _ => integrable_inner_right
      (smooth_dir hf (unitVector i)).continuous (smooth_dir hφs (unitVector i)).continuous
      (hφc.fderiv_apply (𝕜 := ℝ) _)), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => one_pair hf hφ i

theorem gradientPairingZero_holds : GradientPairingZero := by
  intro g φ hg hφ
  obtain ⟨hφs, hφc, hφd⟩ := hφ
  have hψc : ∀ i : Fin 3, HasCompactSupport (fun y => φ y i) := fun i =>
    hφc.comp_left (g := fun w : Space => w i) (by simp)
  simp_rw [gradient_inner]
  rw [integral_finsetSum _ (fun i _ => integrable_mul_right
      (smooth_dir_scalar hg _).continuous (coord_smooth hφs i).continuous (hψc i))]
  simp_rw [one_grad hg hφs hφc]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => integrable_mul_right
      hg.continuous (smooth_dir_scalar (coord_smooth hφs i) _).continuous
      ((hψc i).fderiv_apply (𝕜 := ℝ) _))]
  have hz : (fun x => ∑ i : Fin 3, g x * fderiv ℝ (fun y => φ y i) x (unitVector i)) = fun _ => 0 := by
    funext x
    rw [← Finset.mul_sum]
    simp_rw [coord_dir hφs]
    have := hφd x
    unfold divergenceAt at this
    rw [this, mul_zero]
  rw [hz, integral_zero, neg_zero]

end Breakdown
