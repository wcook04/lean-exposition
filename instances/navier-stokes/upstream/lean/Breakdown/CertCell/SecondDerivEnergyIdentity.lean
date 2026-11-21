import Breakdown.CertCell.BridgeStatements

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.SecondDerivEnergy

private def partialOf (k : Fin 3) (ψ : Space → ℝ) : Space → ℝ :=
  fun x => fderiv ℝ ψ x (unitVector k)

private def conv (ψ f : Space → ℝ) : Space → ℝ :=
  ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

private theorem partialOf_contDiff {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (k : Fin 3) :
    ContDiff ℝ ∞ (partialOf k ψ) :=
  (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem partialOf_hasCompactSupport {ψ : Space → ℝ} (hc : HasCompactSupport ψ) (k : Fin 3) :
    HasCompactSupport (partialOf k ψ) :=
  hc.fderiv_apply (𝕜 := ℝ) (unitVector k)

private theorem partialOf_comm {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i j : Fin 3) :
    partialOf j (partialOf i ψ) = partialOf i (partialOf j ψ) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have key : ∀ a b : Fin 3, partialOf b (partialOf a ψ) x =
      fderiv ℝ (fderiv ℝ ψ) x (unitVector b) (unitVector a) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ ψ y (unitVector a)) x (unitVector b) = _
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hψ.contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) _ _

private theorem conv_hasLineDerivAt {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hf : LocallyIntegrable f volume) (k : Fin 3) (x : Space) :
    HasLineDerivAt ℝ (conv ψ f) (conv (partialOf k ψ) f x) x (unitVector k) := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hψ.of_le (by exact_mod_cast le_top)) hf x
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) (hψ.continuous_fderiv (by simp)) hf x
  have e : ((fderiv ℝ ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) x) (unitVector k) =
      conv (partialOf k ψ) f x := by
    rw [convolution_def, ContinuousLinearMap.integral_apply hex]
    simp [conv, partialOf, convolution_def]
  rw [← e]
  exact hd.hasLineDerivAt _

private theorem conv_weak {ψ f g : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (k : Fin 3)
    (hw : ∀ φ, IsTestFunction φ → ∫ y, φ y * g y = -∫ y, fderiv ℝ φ y (unitVector k) * f y) (x : Space) :
    conv ψ g x = conv (partialOf k ψ) f x := by
  have htest : IsTestFunction (fun t => ψ (x - t)) :=
    ⟨hψ.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hder : ∀ t, fderiv ℝ (fun t => ψ (x - t)) t (unitVector k) = -partialOf k ψ (x - t) := by
    intro t
    have h1 : HasFDerivAt (fun t => ψ (x - t))
        ((fderiv ℝ ψ (x - t)).comp (-ContinuousLinearMap.id ℝ Space)) t := by
      have hin : HasFDerivAt (fun t : Space => x - t) (-ContinuousLinearMap.id ℝ Space) t := by
        simpa using (hasFDerivAt_id t).const_sub x
      exact (hψ.differentiable (by simp) (x - t)).hasFDerivAt.comp t hin
    rw [h1.fderiv]
    simp [partialOf]
  have e := hw _ htest
  simp only [hder, neg_mul, integral_neg, neg_neg] at e
  simp only [conv, convolution_eq_swap, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact e

private theorem lintegral_mul_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B : X → ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    (∫⁻ x, A x * B x ∂μ) ^ 2 ≤ (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x => A x ^ (1 / 2 : ℝ)) (g := fun x => A x ^ (1 / 2 : ℝ) * B x)
    (hA.pow_const _) ((hA.pow_const _).mul hB)
  have e1 : ∀ x, A x ^ (1 / 2 : ℝ) * (A x ^ (1 / 2 : ℝ) * B x) = A x * B x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (A x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 2 : ℝ) * B x) ^ (2 : ℝ) = A x * B x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂μ) ^ 2
      ≤ ((∫⁻ x, A x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, A x * B x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, A x ∂μ) * ∫⁻ x, A x * B x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

private theorem conv_sq_le {ψ f : Space → ℝ} (hψ : Continuous ψ) (hfin : ∫⁻ t, ‖ψ t‖ₑ ≠ ⊤)
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖conv ψ f x‖ₑ ^ 2 ≤ (∫⁻ t, ‖ψ t‖ₑ) * ((∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
  have hA : Measurable (fun t => ‖ψ t‖ₑ) := hψ.measurable.enorm
  have hB : ∀ x, AEMeasurable (fun t => ‖f (x - t)‖ₑ) volume := fun x =>
    hf.aemeasurable.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  have hpt : ∀ x, ‖conv ψ f x‖ₑ ^ 2 ≤ (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ ^ 2 := by
    intro x
    have h1 : ‖conv ψ f x‖ₑ ≤ ∫⁻ t, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      simp [enorm_mul]
    calc ‖conv ψ f x‖ₑ ^ 2 ≤ (∫⁻ t, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ _ := lintegral_mul_sq_le hA.aemeasurable (hB x)
  have hjoint : AEMeasurable (Function.uncurry fun x t => ‖ψ t‖ₑ * ‖f (x - t)‖ₑ ^ 2)
      ((volume : Measure Space).prod volume) := by
    have h2 : AEMeasurable (fun p : Space × Space => ‖f (p.1 - p.2)‖ₑ)
        ((volume : Measure Space).prod volume) :=
      hf.aemeasurable.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact (hA.comp measurable_snd).aemeasurable.mul (h2.pow_const 2)
  calc ∫⁻ x, ‖conv ψ f x‖ₑ ^ 2
      ≤ ∫⁻ x, (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ ^ 2 := lintegral_mono hpt
    _ = (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ x, ∫⁻ t, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ ^ 2 := lintegral_const_mul' _ _ hfin
    _ = (∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖ψ t‖ₑ * ‖f (x - t)‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap hjoint]
    _ = (∫⁻ t, ‖ψ t‖ₑ) * ((∫⁻ t, ‖ψ t‖ₑ) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
        congr 1
        rw [← lintegral_mul_const _ hA]
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ 2) t]

private theorem memLp_two_of_lintegral {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 < ⊤) : MemLp f 2 volume :=
  (memLp_two_iff_integrable_sq hf).2 ⟨hf.pow 2, by simpa [HasFiniteIntegral, enorm_pow] using h⟩

private theorem lintegral_enorm_lt_top {ψ : Space → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∫⁻ t, ‖ψ t‖ₑ ≠ ⊤ :=
  (hψ.integrable_of_hasCompactSupport hc).hasFiniteIntegral.ne

private theorem conv_memLp {ψ f : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hf : LocallyIntegrable f volume) (hL : ∫⁻ x, ‖f x‖ₑ ^ 2 < ⊤) : MemLp (conv ψ f) 2 volume := by
  refine memLp_two_of_lintegral
    (hc.continuous_convolution_left _ hψ.continuous hf).aestronglyMeasurable ?_
  have hfin := lintegral_enorm_lt_top hψ.continuous hc
  refine (conv_sq_le hψ.continuous hfin hf.aestronglyMeasurable).trans_lt ?_
  exact ENNReal.mul_lt_top hfin.lt_top (ENNReal.mul_lt_top hfin.lt_top hL)

private theorem conv_sum {ψ : Space → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {f : Fin 3 → Space → ℝ} (hf : ∀ i, LocallyIntegrable (f i) volume) (x : Space) :
    conv ψ (fun y => ∑ i, f i y) x = ∑ i, conv ψ (f i) x := by
  simp only [conv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Finset.mul_sum]
  exact integral_finsetSum _ fun i _ =>
    hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ (hf i) x

private theorem enorm_sq_eq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a * a) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs, sq]

private theorem smooth_identity {ρ u : Space → ℝ} {g : Fin 3 → Space → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hc : HasCompactSupport ρ) (hg : ∀ j, LocallyIntegrable (g j) volume)
    (hL : ∀ j, ∫⁻ x, ‖g j x‖ₑ ^ 2 < ⊤)
    (wu : ∀ i, ∀ φ, IsTestFunction φ → ∫ y, φ y * g i y = -∫ y, fderiv ℝ φ y (unitVector i) * u y)
    (i j : Fin 3) :
    ∫ x, conv (partialOf i ρ) (g j) x * conv (partialOf i ρ) (g j) x =
      ∫ x, conv (partialOf i ρ) (g i) x * conv (partialOf j ρ) (g j) x := by
  have d1 : ∀ k, ContDiff ℝ ∞ (partialOf k ρ) := partialOf_contDiff hρ
  have c1 : ∀ k, HasCompactSupport (partialOf k ρ) := partialOf_hasCompactSupport hc
  have d2 : ∀ k l, ContDiff ℝ ∞ (partialOf l (partialOf k ρ)) := fun k => partialOf_contDiff (d1 k)
  have c2 : ∀ k l, HasCompactSupport (partialOf l (partialOf k ρ)) :=
    fun k => partialOf_hasCompactSupport (c1 k)
  have mW : ∀ k, MemLp (conv ρ (g k)) 2 volume := fun k => conv_memLp hρ hc (hg k) (hL k)
  have mA : ∀ k l, MemLp (conv (partialOf k ρ) (g l)) 2 volume :=
    fun k l => conv_memLp (d1 k) (c1 k) (hg l) (hL l)
  have mD : ∀ k l m, MemLp (conv (partialOf l (partialOf k ρ)) (g m)) 2 volume :=
    fun k l m => conv_memLp (d2 k l) (c2 k l) (hg m) (hL m)
  have sym : ∀ a b x, conv (partialOf a ρ) (g b) x = conv (partialOf b ρ) (g a) x := by
    intro a b x
    rw [conv_weak (d1 a) (c1 a) b (wu b) x, conv_weak (d1 b) (c1 b) a (wu a) x, partialOf_comm hρ]
  have ibp1 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (v := unitVector j)
    (f := conv ρ (g i)) (f' := conv (partialOf j ρ) (g i))
    (g := conv (partialOf i ρ) (g j)) (g' := conv (partialOf j (partialOf i ρ)) (g j))
    ((mA j i).integrable_mul (mA i j)) ((mW i).integrable_mul (mD i j j)) ((mW i).integrable_mul (mA i j))
    (fun x _ => conv_hasLineDerivAt hρ hc (hg i) j x)
    (fun x _ => conv_hasLineDerivAt (d1 i) (c1 i) (hg j) j x)
  have ibp2 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (v := unitVector i)
    (f := conv ρ (g i)) (f' := conv (partialOf i ρ) (g i))
    (g := conv (partialOf j ρ) (g j)) (g' := conv (partialOf i (partialOf j ρ)) (g j))
    ((mA i i).integrable_mul (mA j j)) ((mW i).integrable_mul (mD j i j)) ((mW i).integrable_mul (mA j j))
    (fun x _ => conv_hasLineDerivAt hρ hc (hg i) i x)
    (fun x _ => conv_hasLineDerivAt (d1 j) (c1 j) (hg j) i x)
  simp only [ContinuousLinearMap.mul_apply'] at ibp1 ibp2
  rw [partialOf_comm hρ i j] at ibp1
  have e : ∫ x, conv (partialOf j ρ) (g i) x * conv (partialOf i ρ) (g j) x =
      ∫ x, conv (partialOf i ρ) (g i) x * conv (partialOf j ρ) (g j) x := by
    linarith
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [sym j i x]

private theorem mollified_identity {ρ u : Space → ℝ} {g : Fin 3 → Space → ℝ} {h : Fin 3 → Fin 3 → Space → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (hg : ∀ j, LocallyIntegrable (g j) volume)
    (hL : ∀ j, ∫⁻ x, ‖g j x‖ₑ ^ 2 < ⊤)
    (wu : ∀ i, ∀ φ, IsTestFunction φ → ∫ y, φ y * g i y = -∫ y, fderiv ℝ φ y (unitVector i) * u y)
    (wg : ∀ i j, ∀ φ, IsTestFunction φ →
      ∫ y, φ y * h i j y = -∫ y, fderiv ℝ φ y (unitVector i) * g j y) :
    ∫⁻ x, ∑ i, ∑ j, ‖conv ρ (h i j) x‖ₑ ^ 2 = ∫⁻ x, ‖∑ i, conv ρ (h i i) x‖ₑ ^ 2 := by
  have hA : ∀ i j x, conv ρ (h i j) x = conv (partialOf i ρ) (g j) x :=
    fun i j x => conv_weak hρ hc i (wg i j) x
  simp only [hA, enorm_sq_eq]
  have mA : ∀ k l, MemLp (conv (partialOf k ρ) (g l)) 2 volume :=
    fun k l => conv_memLp (partialOf_contDiff hρ k) (partialOf_hasCompactSupport hc k) (hg l) (hL l)
  have iA : ∀ a b c d, Integrable
      (fun x => conv (partialOf a ρ) (g b) x * conv (partialOf c ρ) (g d) x) volume :=
    fun a b c d => (mA a b).integrable_mul (mA c d)
  have l1 : ∫⁻ x, ∑ i, ∑ j, ENNReal.ofReal (conv (partialOf i ρ) (g j) x * conv (partialOf i ρ) (g j) x) =
      ENNReal.ofReal (∫ x, ∑ i, ∑ j, conv (partialOf i ρ) (g j) x * conv (partialOf i ρ) (g j) x) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _]
      exact Finset.sum_congr rfl fun i _ =>
        (ENNReal.ofReal_sum_of_nonneg fun j _ => mul_self_nonneg _).symm
    · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA i j i j
    · exact Eventually.of_forall fun x =>
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have l2 : ∫⁻ x, ENNReal.ofReal ((∑ i, conv (partialOf i ρ) (g i) x) * (∑ i, conv (partialOf i ρ) (g i) x)) =
      ENNReal.ofReal (∫ x, (∑ i, conv (partialOf i ρ) (g i) x) * (∑ i, conv (partialOf i ρ) (g i) x)) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · simp_rw [Finset.sum_mul_sum]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA i i j j
    · exact Eventually.of_forall fun x => mul_self_nonneg _
  rw [l1, l2]
  congr 1
  have r1 : ∫ x, ∑ i, ∑ j, conv (partialOf i ρ) (g j) x * conv (partialOf i ρ) (g j) x =
      ∑ i, ∑ j, ∫ x, conv (partialOf i ρ) (g j) x * conv (partialOf i ρ) (g j) x := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA i j i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => iA i j i j
  have r2 : ∫ x, (∑ i, conv (partialOf i ρ) (g i) x) * (∑ i, conv (partialOf i ρ) (g i) x) =
      ∑ i, ∑ j, ∫ x, conv (partialOf i ρ) (g i) x * conv (partialOf j ρ) (g j) x := by
    simp_rw [Finset.sum_mul_sum]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA i i j j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => iA i i j j
  rw [r1, r2]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    smooth_identity hρ hc hg hL wu i j

private def bumpSeq (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

private def mollifier (n : ℕ) : Space → ℝ := (bumpSeq n).normed volume

private theorem mollifier_contDiff (n : ℕ) : ContDiff ℝ ∞ (mollifier n) :=
  (bumpSeq n).contDiff_normed

private theorem mollifier_hasCompactSupport (n : ℕ) : HasCompactSupport (mollifier n) :=
  (bumpSeq n).hasCompactSupport_normed

private theorem mollifier_lintegral (n : ℕ) : ∫⁻ t, ‖mollifier n t‖ₑ = 1 := by
  have h : ∀ t, ‖mollifier n t‖ₑ = ENNReal.ofReal (mollifier n t) := fun t => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (show 0 ≤ mollifier n t from (bumpSeq n).nonneg_normed t)]
  simp_rw [h]
  show ∫⁻ t, ENNReal.ofReal ((bumpSeq n).normed volume t) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (bumpSeq n).integrable_normed
    (Eventually.of_forall fun t => (bumpSeq n).nonneg_normed t)]
  simp [(bumpSeq n).integral_normed]

private theorem mollifier_sq_le (n : ℕ) {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖conv (mollifier n) f x‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have h := conv_sq_le (ψ := mollifier n) (mollifier_contDiff n).continuous
    (by rw [mollifier_lintegral]; exact ENNReal.one_ne_top) hf
  rwa [mollifier_lintegral, one_mul, one_mul] at h

private theorem mollifier_tendsto {f : Space → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, Tendsto (fun n => conv (mollifier n) f x) atTop (𝓝 (f x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) (φ := bumpSeq)
    (by
      change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
    (Eventually.of_forall fun n => le_of_eq (by
      change 1 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1) / 2)
      ring)) hf

private theorem lintegral_le_of_ae_tendsto {F : ℕ → Space → ℝ≥0∞} {L : Space → ℝ≥0∞} {C : ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) volume) (hT : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (L x)))
    (hC : ∀ n, ∫⁻ x, F n x ≤ C) : ∫⁻ x, L x ≤ C :=
  calc ∫⁻ x, L x = ∫⁻ x, liminf (fun n => F n x) atTop :=
        lintegral_congr_ae (hT.mono fun _ hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, F n x) atTop := lintegral_liminf_le' hF
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hC)

private theorem scalar_identity {u : Space → ℝ} {g : Fin 3 → Space → ℝ} {h : Fin 3 → Fin 3 → Space → ℝ}
    (hg : ∀ j, LocallyIntegrable (g j) volume) (hh : ∀ i j, LocallyIntegrable (h i j) volume)
    (hL : ∀ j, ∫⁻ x, ‖g j x‖ₑ ^ 2 < ⊤)
    (wu : ∀ i, ∀ φ, IsTestFunction φ → ∫ y, φ y * g i y = -∫ y, fderiv ℝ φ y (unitVector i) * u y)
    (wg : ∀ i j, ∀ φ, IsTestFunction φ →
      ∫ y, φ y * h i j y = -∫ y, fderiv ℝ φ y (unitVector i) * g j y) :
    ∫⁻ x, ∑ i, ∑ j, ‖h i j x‖ₑ ^ 2 = ∫⁻ x, ‖∑ i, h i i x‖ₑ ^ 2 := by
  have hE := fun n => mollified_identity (mollifier_contDiff n) (mollifier_hasCompactSupport n) hg hL wu wg
  have hT : ∀ᵐ x, ∀ i j, Tendsto (fun n => conv (mollifier n) (h i j) x) atTop (𝓝 (h i j x)) := by
    simp only [ae_all_iff]
    exact fun i j => mollifier_tendsto (hh i j)
  have hcont : ∀ n i j, Continuous (conv (mollifier n) (h i j)) := fun n i j =>
    (mollifier_hasCompactSupport n).continuous_convolution_left _ (mollifier_contDiff n).continuous (hh i j)
  have hsm : ∀ i j, AEStronglyMeasurable (h i j) volume := fun i j => (hh i j).aestronglyMeasurable
  have hsum : ∀ n x, ∑ i, conv (mollifier n) (h i i) x = conv (mollifier n) (fun y => ∑ i, h i i y) x :=
    fun n x => (conv_sum (mollifier_contDiff n).continuous (mollifier_hasCompactSupport n)
      (fun i => hh i i) x).symm
  refine le_antisymm ?_ ?_
  · refine lintegral_le_of_ae_tendsto
      (F := fun n x => ∑ i, ∑ j, ‖conv (mollifier n) (h i j) x‖ₑ ^ 2) ?_ ?_ ?_
    · intro n
      exact Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
        ((hcont n i j).measurable.enorm.pow_const 2).aemeasurable
    · filter_upwards [hT] with x hx
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto _).comp (hx i j)
    · intro n
      rw [hE n]
      simp_rw [hsum n]
      exact mollifier_sq_le n (Finset.aestronglyMeasurable_fun_sum _ fun i _ => hsm i i)
  · refine lintegral_le_of_ae_tendsto
      (F := fun n x => ‖∑ i, conv (mollifier n) (h i i) x‖ₑ ^ 2) ?_ ?_ ?_
    · intro n
      exact ((continuous_finsetSum _ fun i _ => hcont n i i).measurable.enorm.pow_const 2).aemeasurable
    · filter_upwards [hT] with x hx
      exact (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto _).comp
        (tendsto_finsetSum _ fun i _ => hx i i)
    · intro n
      rw [← hE n, lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
          ((hcont n i j).measurable.enorm.pow_const 2).aemeasurable,
        lintegral_finsetSum' _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ =>
          (hsm i j).aemeasurable.enorm.pow_const 2]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [lintegral_finsetSum' _ fun j _ => ((hcont n i j).measurable.enorm.pow_const 2).aemeasurable,
        lintegral_finsetSum' _ fun j _ => (hsm i j).aemeasurable.enorm.pow_const 2]
      exact Finset.sum_le_sum fun j _ => mollifier_sq_le n (hsm i j)

private theorem locallyIntegrable_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Space → E}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun y => L (f y)) volume :=
  (hf.smul ‖L‖).mono (L.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun y => by
      rw [Pi.smul_apply, norm_smul, norm_norm]
      exact L.le_opNorm _)

private theorem coord_weak {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f F) (i k : Fin 3) (φ : Space → ℝ) (hφ : IsTestFunction φ) :
    ∫ y, φ y * F y (unitVector i) k = -∫ y, fderiv ℝ φ y (unitVector i) * f y k := by
  have e := hw.2.2 φ hφ i
  have hFi : LocallyIntegrable (fun y => F y (unitVector i)) volume :=
    locallyIntegrable_clm (ContinuousLinearMap.apply ℝ Space (unitVector i)) hw.2.1
  have i1 : Integrable (fun y => φ y • F y (unitVector i)) volume :=
    hFi.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f y) volume :=
    hw.1.integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i))
  have e2 := congrArg (EuclideanSpace.proj k : Space →L[ℝ] ℝ) e
  rw [← (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm i1, map_neg,
    ← (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm i2] at e2
  simpa using e2

private theorem norm_sq_coord (x : Space) : ‖x‖ ^ 2 = ∑ k, x k ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

private theorem coord_sq_le (x : Space) (k : Fin 3) : x k ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_coord]
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) (Finset.mem_univ k)

private theorem coord_sum (f : Fin 3 → Space) (k : Fin 3) : (∑ j, f j) k = ∑ j, f j k := by
  simp [Fin.sum_univ_three]

private theorem ofReal_triple_sum (F : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ENNReal.ofReal (∑ a, ∑ b, ∑ c, F a b c * F a b c) =
      ∑ a, ∑ b, ∑ c, ENNReal.ofReal (F a b c * F a b c) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => mul_self_nonneg _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b _ => Finset.sum_nonneg fun c _ => mul_self_nonneg _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ => mul_self_nonneg _]

private theorem slice_identity {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hw : IsWeakGradient w G)
    (hH : ∀ j, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (hG : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (Bridge.hessFrobSq (H y)) =
      ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2) := by
  have sg : ∀ k j, LocallyIntegrable (fun y => G y (unitVector j) k) volume :=
    fun k j => locallyIntegrable_clm (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (hH j).1
  have sh : ∀ k i j, LocallyIntegrable (fun y => H y (unitVector i) (unitVector j) k) volume :=
    fun k i j => by
      simpa using locallyIntegrable_clm (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
        (locallyIntegrable_clm (ContinuousLinearMap.apply ℝ Space (unitVector i)) (hH j).2.1)
  have wg : ∀ k i j, ∀ φ, IsTestFunction φ → ∫ y, φ y * H y (unitVector i) (unitVector j) k =
      -∫ y, fderiv ℝ φ y (unitVector i) * G y (unitVector j) k :=
    fun k i j φ hφ => by simpa using coord_weak (hH j) i k φ hφ
  have hL : ∀ k j, ∫⁻ y, ‖G y (unitVector j) k‖ₑ ^ 2 < ⊤ := by
    intro k j
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hG
    rw [enorm_sq_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    calc G y (unitVector j) k * G y (unitVector j) k = G y (unitVector j) k ^ 2 := (sq _).symm
      _ ≤ ‖G y (unitVector j)‖ ^ 2 := coord_sq_le _ k
      _ ≤ matSq (G y) := Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hbase := fun k => scalar_identity (u := fun y => w y k) (g := fun j y => G y (unitVector j) k)
    (h := fun i j y => H y (unitVector i) (unitVector j) k) (sg k) (sh k) (hL k)
    (fun i φ hφ => coord_weak hw i k φ hφ) (wg k)
  have e1 : ∀ y, ENNReal.ofReal (Bridge.hessFrobSq (H y)) =
      ∑ k, ∑ i, ∑ j, ‖H y (unitVector i) (unitVector j) k‖ₑ ^ 2 := by
    intro y
    simp only [enorm_sq_eq]
    rw [← ofReal_triple_sum]
    congr 1
    simp only [Bridge.hessFrobSq, norm_sq_coord, Fin.sum_univ_three]
    ring
  have e2 : ∀ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2) =
      ∑ k, ‖∑ i, H y (unitVector i) (unitVector i) k‖ₑ ^ 2 := by
    intro y
    rw [norm_sq_coord, ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [enorm_sq_eq, secondDerivTrace, coord_sum, sq]
  simp_rw [e1, e2]
  rw [lintegral_finsetSum' _ fun k _ => Finset.aemeasurable_fun_sum _ fun i _ =>
      Finset.aemeasurable_fun_sum _ fun j _ => (sh k i j).aestronglyMeasurable.aemeasurable.enorm.pow_const 2,
    lintegral_finsetSum' _ fun k _ =>
      ((Finset.aestronglyMeasurable_fun_sum _ fun i _ => (sh k i i).aestronglyMeasurable).aemeasurable.enorm.pow_const 2)]
  exact Finset.sum_congr rfl fun k _ => hbase k

end Internal.SecondDerivEnergy

namespace Bridge

theorem secondDerivEnergyIdentity : HessianEnergyIdentityHolds := by
  intro Γ P v G H g hp
  have hc : Continuous (fun A : Space →L[ℝ] Space => matSq A) :=
    continuous_finsetSum _ fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2
  have hjoint : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2)))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hc.comp_aestronglyMeasurable hp.measurable_gradient).aemeasurable
  have hsec : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y)))
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) :=
    hjoint.lintegral_prod_right'.mono_measure Measure.restrict_le_self
  have hfin := ae_lt_top' hsec hp.gradient_finite.ne
  unfold periodLIntegral
  refine lintegral_congr_ae ?_
  filter_upwards [hfin, ae_restrict_of_ae hp.weak_gradient, ae_restrict_of_ae hp.weak_secondDeriv]
    with σ h1 h2 h3
  exact Internal.SecondDerivEnergy.slice_identity h2 h3 h1

end Bridge

end CertCell

end Breakdown
