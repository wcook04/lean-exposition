import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private def entryMap (j k : Fin 3) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) j)

private theorem entryMap_apply (j k : Fin 3) (w : Fin 3 → Fin 3 → ℝ) : entryMap j k w = w j k :=
  rfl

private theorem norm_entryMap_le (j k : Fin 3) : ‖entryMap j k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [entryMap_apply, one_mul]
  exact le_trans (norm_le_pi_norm (w j) k) (norm_le_pi_norm w j)

private theorem hasFDerivAt_kernelComponent (hKm : LerayKernelMeasurable) (hMass : KernelMassBound)
    {C : ℝ} (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {τ : ℝ} (hτ : 0 < τ) {G : Space → Fin 3 → Fin 3 → ℝ} {A : ℝ} (hG : ContDiff ℝ 1 G)
    (hGA : ∀ z, ‖G z‖ ≤ A) (hDA : ∀ z, ‖fderiv ℝ G z‖ ≤ A) (i : Fin 3) (y : Space) :
    HasFDerivAt (fun y => ∫ x, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * G (y - x) j k)
      (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k τ x • (entryMap j k).comp (fderiv ℝ G (y - x))) y ∧
    Integrable (fun x => ∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k τ x • (entryMap j k).comp (fderiv ℝ G (y - x))) := by
  have hKmeas : ∀ j k : Fin 3, Measurable (fun x : Space => lerayKernel i j k τ x) := fun j k =>
    (hKm i j k).comp (measurable_const.prodMk measurable_id)
  have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcont : Continuous G := hG.continuous
  have hDcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hbint : Integrable (fun x : Space => 9 * (C * A) * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹) := by
    have h := (hMass τ hτ 0).1
    simp only [zero_sub, norm_neg] at h
    exact h.const_mul _
  have hKle : ∀ j k x, |lerayKernel i j k τ x| ≤ C * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹ := by
    intro j k x
    rw [← div_eq_mul_inv]
    exact hC i j k τ x hτ
  have hsum9 : ∀ x : Space, ∑ _j : Fin 3, ∑ _k : Fin 3, C * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹ * A =
      9 * (C * A) * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹ := by
    intro x
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hFbound : ∀ y x : Space, ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * G (y - x) j k‖ ≤
      9 * (C * A) * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹ := by
    intro y x
    rw [← hsum9 x]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hKle j k x)
      (le_trans (le_trans (norm_le_pi_norm (G (y - x) j) k) (norm_le_pi_norm (G (y - x)) j)) (hGA _))
      (norm_nonneg _) (le_trans (abs_nonneg _) (hKle j k x))
  have hF'bound : ∀ y x : Space, ‖∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k τ x • (entryMap j k).comp (fderiv ℝ G (y - x))‖ ≤
        9 * (C * A) * ((‖x‖ + Real.sqrt τ) ^ 4)⁻¹ := by
    intro y x
    rw [← hsum9 x]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (hKle j k x) ?_ (norm_nonneg _) (le_trans (abs_nonneg _) (hKle j k x))
    calc ‖(entryMap j k).comp (fderiv ℝ G (y - x))‖
        ≤ ‖entryMap j k‖ * ‖fderiv ℝ G (y - x)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * A := mul_le_mul (norm_entryMap_le j k) (hDA _) (norm_nonneg _) zero_le_one
      _ = A := one_mul A
  have hFmeas : ∀ y : Space, AEStronglyMeasurable
      (fun x => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * G (y - x) j k) volume := by
    intro y
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    refine (hKmeas j k).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact (continuous_apply k).comp ((continuous_apply j).comp
      (hcont.comp (continuous_sub_left y)))
  have hF'meas : ∀ y : Space, AEStronglyMeasurable (fun x => ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k τ x • (entryMap j k).comp (fderiv ℝ G (y - x))) volume := by
    intro y
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    refine (hKmeas j k).aestronglyMeasurable.smul (Continuous.aestronglyMeasurable ?_)
    exact Continuous.clm_comp continuous_const (hDcont.comp (continuous_sub_left y))
  have hdiffx : ∀ x y : Space, HasFDerivAt
      (fun y => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * G (y - x) j k)
      (∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k τ x • (entryMap j k).comp (fderiv ℝ G (y - x))) y := by
    intro x y
    have hGy : HasFDerivAt (fun y => G (y - x)) (fderiv ℝ G (y - x)) y := by
      have h := HasFDerivAt.comp y (hdiff (y - x)).hasFDerivAt ((hasFDerivAt_id y).sub_const x)
      simpa [Function.comp_def] using h
    refine HasFDerivAt.fun_sum fun j _ => ?_
    refine HasFDerivAt.fun_sum fun k _ => ?_
    exact ((entryMap j k).hasFDerivAt.comp y hGy).const_mul (lerayKernel i j k τ x)
  refine ⟨?_, (hbint.mono' (hF'meas y) (Eventually.of_forall (hF'bound y)))⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) univ_mem
    (Eventually.of_forall hFmeas) (hbint.mono' (hFmeas y) (Eventually.of_forall (hFbound y)))
    (hF'meas y) (Eventually.of_forall fun x y' _ => hF'bound y' x) hbint
    (Eventually.of_forall fun x y' _ => hdiffx x y')

theorem kernelConvDeriv_of_mass : LerayKernelMeasurable → KernelMassBound → KernelConvDeriv := by
  intro hKm hMass hK τ hτ G A hG hGA hDA y
  obtain ⟨C, hC⟩ := hK
  have hshift : ∀ (H : Space → Fin 3 → Fin 3 → ℝ) (i : Fin 3) (y : Space),
      ∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * H z j k =
        ∫ x, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * H (y - x) j k := by
    intro H i y
    have h := integral_sub_left_eq_self
      (fun x => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * H (y - x) j k) volume y
    simp only [sub_sub_cancel] at h
    exact h
  have hfun : kernelConv τ G = fun y => ∑ i : Fin 3,
      (∫ x, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ x * G (y - x) j k) • unitVector i := by
    funext y
    unfold kernelConv
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hshift G i y]
  have hD := HasFDerivAt.fun_sum (u := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
    (hasFDerivAt_kernelComponent hKm hMass hC hτ hG hGA hDA i y).1.smul_const (unitVector i)
  rw [← hfun] at hD
  refine ⟨hD.differentiableAt, fun v => ?_⟩
  rw [hD.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  unfold kernelConv
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h := hshift (fun z => fderiv ℝ G z v) i y
  rw [h, ContinuousLinearMap.integral_apply
    (hasFDerivAt_kernelComponent hKm hMass hC hτ hG hGA hDA i y).2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, entryMap_apply, smul_eq_mul]

end Breakdown.FarField
