import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FundSol

private theorem hasFDerivAt_norm_of_ne {z : Space} (hz : z ≠ 0) :
    HasFDerivAt (fun w : Space => ‖w‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sqrt (pow_ne_zero 2 hr)
  have hf : (fun w : Space => √(‖w‖ ^ 2)) = fun w => ‖w‖ :=
    funext fun w => Real.sqrt_sq (norm_nonneg w)
  rw [hf, Real.sqrt_sq (norm_nonneg z)] at h
  refine h.congr_fderiv ?_
  rw [two_smul, smul_add, ← add_smul]
  congr 1
  field_simp
  ring

private theorem hasFDerivAt_inv_norm {z : Space} (hz : z ≠ 0) :
    HasFDerivAt (fun w : Space => ‖w‖⁻¹) (-(‖z‖⁻¹ ^ 3) • innerSL ℝ z) z := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h := (hasDerivAt_inv hr).comp_hasFDerivAt z (hasFDerivAt_norm_of_ne hz)
  refine h.congr_fderiv ?_
  ext v
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_kernel {z : Space} (hz : z ≠ 0) :
    HasFDerivAt kernel (innerSL ℝ (kernelGrad z)) z := by
  have h := (hasFDerivAt_inv_norm hz).const_mul (-(4 * π)⁻¹)
  have hk : kernel = fun w : Space => -(4 * π)⁻¹ * ‖w‖⁻¹ := rfl
  rw [hk]
  refine h.congr_fderiv ?_
  ext v
  simp only [kernelGrad, innerSL_apply_apply, real_inner_smul_left, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiffOn_kernel : ContDiffOn ℝ ∞ kernel {0}ᶜ := by
  intro z hz
  have hz' : z ≠ 0 := hz
  have h : ContDiffAt ℝ ∞ (fun w : Space => -(4 * π)⁻¹ * ‖w‖⁻¹) z :=
    contDiffAt_const.mul ((contDiffAt_norm ℝ hz').inv (norm_ne_zero_iff.mpr hz'))
  exact h.contDiffWithinAt

theorem secondPartial_kernel {z : Space} (hz : z ≠ 0) (i j : Fin 3) :
    secondPartial kernel i j z = kernelSecondDeriv i j z := by
  have hev : fderiv ℝ kernel =ᶠ[nhds z] fun w => innerSL ℝ (kernelGrad w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    exact (hasFDerivAt_kernel hw).fderiv
  have ha := ((hasFDerivAt_inv_norm hz).pow 3).const_mul ((4 * π)⁻¹)
  have hG := ha.smul (hasFDerivAt_id z)
  have hI := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp z hG
  have hI' : HasFDerivAt (fun w => innerSL ℝ (kernelGrad w)) _ z := hI
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [secondPartial, iteratedFDeriv_two_apply, hev.fderiv_eq, hI'.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, add_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, unitVector, kernelSecondDeriv]
  have hin : ∀ a b : Space, (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ) a b = inner ℝ a b :=
    fun a b => rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [hin, EuclideanSpace.inner_single_right, PiLp.single_apply, one_mul, conj_trivial]
  rcases eq_or_ne i j with rfl | h
  · simp only [if_true, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
    ring
  · simp only [h, Ne.symm h, if_false, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      show (3 : ℕ) - 1 = 2 from rfl]
    ring

theorem norm_kernelGrad (z : Space) : ‖kernelGrad z‖ = (4 * π)⁻¹ * ‖z‖⁻¹ ^ 2 := by
  rw [kernelGrad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases eq_or_ne ‖z‖ 0 with h | h
  · simp [h]
  · field_simp

theorem abs_kernelSecondDeriv_le (i j : Fin 3) (z : Space) : |kernelSecondDeriv i j z| ≤ ‖z‖⁻¹ ^ 3 := by
  have hcomp : ∀ k, |z k| ≤ ‖z‖ := fun k => by
    have hn := EuclideanSpace.real_norm_sq_eq z
    have hk : z k ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [hn]
      exact Finset.single_le_sum (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)
    exact (sq_le_sq.mp hk).trans_eq (abs_norm z)
  rcases eq_or_ne z 0 with rfl | hz
  · simp [kernelSecondDeriv]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hij : |z i * z j| ≤ ‖z‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (hcomp i) (hcomp j) (abs_nonneg _) hr.le
  have hd : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have hpi : 1 ≤ π := by linarith [Real.pi_gt_three]
  have e1 : |(if i = j then (1 : ℝ) else 0) * ‖z‖⁻¹ ^ 3| ≤ ‖z‖⁻¹ ^ 3 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖z‖⁻¹ ^ 3)]
    exact mul_le_of_le_one_left (by positivity) hd
  have e2 : |3 * z i * z j * ‖z‖⁻¹ ^ 5| ≤ 3 * ‖z‖ ^ 2 * ‖z‖⁻¹ ^ 5 := by
    rw [show 3 * z i * z j * ‖z‖⁻¹ ^ 5 = 3 * (z i * z j) * ‖z‖⁻¹ ^ 5 by ring, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by positivity : (0 : ℝ) < ‖z‖⁻¹ ^ 5)]
    gcongr
  have e3 : 3 * ‖z‖ ^ 2 * ‖z‖⁻¹ ^ 5 = 3 * ‖z‖⁻¹ ^ 3 := by
    field_simp
  rw [kernelSecondDeriv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹)]
  calc (4 * π)⁻¹ * |(if i = j then (1 : ℝ) else 0) * ‖z‖⁻¹ ^ 3 - 3 * z i * z j * ‖z‖⁻¹ ^ 5|
      ≤ (4 * π)⁻¹ * (4 * ‖z‖⁻¹ ^ 3) := by
        gcongr
        calc _ ≤ _ := abs_sub _ _
          _ ≤ ‖z‖⁻¹ ^ 3 + 3 * ‖z‖ ^ 2 * ‖z‖⁻¹ ^ 5 := add_le_add e1 e2
          _ = 4 * ‖z‖⁻¹ ^ 3 := by rw [e3]; ring
    _ = π⁻¹ * ‖z‖⁻¹ ^ 3 := by field_simp
    _ ≤ ‖z‖⁻¹ ^ 3 := mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hpi)

theorem sum_kernelSecondDeriv_diag {z : Space} (hz : z ≠ 0) : ∑ i, kernelSecondDeriv i i z = 0 := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hn := EuclideanSpace.real_norm_sq_eq z
  simp only [Fin.sum_univ_three] at hn
  simp only [kernelSecondDeriv, Fin.sum_univ_three, if_true]
  field_simp
  linear_combination 3 * hn

private theorem iteratedFDeriv_kernel_smul (k : ℕ) {c : ℝ} (hc : 0 < c) {z : Space}
    (hz : z ≠ 0) :
    c ^ k * ‖iteratedFDeriv ℝ k kernel (c • z)‖ = c⁻¹ * ‖iteratedFDeriv ℝ k kernel z‖ := by
  have hs : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hu : UniqueDiffOn ℝ ({0}ᶜ : Set Space) := hs.uniqueDiffOn
  have hz' : z ∈ ({0}ᶜ : Set Space) := hz
  set L : Space →L[ℝ] Space := c • ContinuousLinearMap.id ℝ Space with hL
  have hLz : L z = c • z := rfl
  have hpre : L ⁻¹' ({0}ᶜ : Set Space) = {0}ᶜ := by
    ext w
    simp [hL, hc.ne']
  have hcz : c • z ∈ ({0}ᶜ : Set Space) := smul_ne_zero hc.ne' hz
  have hk : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have h1 := L.iteratedFDerivWithin_comp_right contDiffOn_kernel hu (by rw [hpre]; exact hu)
    (by rw [hLz]; exact hcz) hk
  rw [hpre] at h1
  have hfun : kernel ∘ L = c⁻¹ • kernel := by
    funext w
    simp only [Function.comp_apply, hL, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_eq_mul, kernel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc, mul_inv]
    ring
  have h2 := iteratedFDerivWithin_const_smul_apply (a := c⁻¹) ((contDiffOn_kernel z hz').of_le hk)
    hu hz'
  rw [hfun, h2, hLz, iteratedFDerivWithin_of_isOpen k hs hz',
    iteratedFDerivWithin_of_isOpen k hs hcz] at h1
  have h3 : (iteratedFDeriv ℝ k kernel (c • z)).compContinuousLinearMap (fun _ => L) =
      c ^ k • iteratedFDeriv ℝ k kernel (c • z) := by
    ext m
    simp [hL, ContinuousMultilinearMap.map_smul_univ]
  rw [h3] at h1
  have h4 := congrArg norm h1
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc),
    abs_of_pos (pow_pos hc k)] at h4
  exact h4.symm

theorem norm_iteratedFDeriv_kernel_le (k : ℕ) : ∃ C : ℝ, ∀ z : Space, z ≠ 0 →
    ‖iteratedFDeriv ℝ k kernel z‖ ≤ C * ‖z‖⁻¹ ^ (k + 1) := by
  have hs : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hk : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcont : ContinuousOn (iteratedFDeriv ℝ k kernel) (Metric.sphere (0 : Space) 1) := by
    have h := contDiffOn_kernel.continuousOn_iteratedFDerivWithin hk hs.uniqueDiffOn
    have h' : ContinuousOn (iteratedFDeriv ℝ k kernel) ({0}ᶜ : Set Space) :=
      h.congr (fun w hw => (iteratedFDerivWithin_of_isOpen k hs hw).symm)
    refine h'.mono (fun w hw => ?_)
    have hw1 : ‖w‖ = 1 := by simpa using hw
    intro h0
    rw [Set.mem_singleton_iff.mp h0, norm_zero] at hw1
    exact zero_ne_one hw1
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn hcont
  refine ⟨C, fun z hz => ?_⟩
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu1 : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : Space) 1 := by
    simp [norm_smul, hr.ne']
  have hu0 : ‖z‖⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero hr.ne') hz
  have hzu : ‖z‖ • ‖z‖⁻¹ • z = z := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have key := iteratedFDeriv_kernel_smul k hr hu0
  rw [hzu] at key
  have hb := hC _ hu1
  have he : ‖iteratedFDeriv ℝ k kernel z‖ =
      ‖z‖⁻¹ ^ (k + 1) * ‖iteratedFDeriv ℝ k kernel (‖z‖⁻¹ • z)‖ := by
    calc ‖iteratedFDeriv ℝ k kernel z‖
        = (‖z‖ ^ k)⁻¹ * (‖z‖ ^ k * ‖iteratedFDeriv ℝ k kernel z‖) :=
          (inv_mul_cancel_left₀ (pow_ne_zero k hr.ne') _).symm
      _ = _ := by rw [key]; ring
  rw [he, mul_comm C]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem locallyIntegrable_kernel : LocallyIntegrable kernel volume := by
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hm : Measurable kernel := by
    unfold kernel
    fun_prop
  refine locallyIntegrable_of_norm_le_rpow (C := (4 * π)⁻¹) (α := 1) (by rw [hdim]; norm_num)
    (by rw [hdim]; norm_num) (Filter.Eventually.of_forall fun x => ?_) hm.aestronglyMeasurable
  rw [Real.rpow_neg_one]
  simp [kernel, abs_of_pos Real.pi_pos]

theorem locallyIntegrable_kernelGrad : LocallyIntegrable kernelGrad volume := by
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hm : Measurable kernelGrad := by
    unfold kernelGrad
    fun_prop
  refine locallyIntegrable_of_norm_le_rpow (C := (4 * π)⁻¹) (α := 2) (by rw [hdim]; norm_num)
    (by rw [hdim]; norm_num) (Filter.Eventually.of_forall fun x => ?_) hm.aestronglyMeasurable
  rw [norm_kernelGrad, Real.rpow_neg (norm_nonneg x), Real.rpow_two, inv_pow]

end Breakdown.FundSol
