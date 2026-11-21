import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private theorem kernelConv_const_smul (τ c : ℝ) (G : Space → Fin 3 → Fin 3 → ℝ) (y : Space) :
    kernelConv τ (fun z => c • G z) y = c • kernelConv τ G y := by
  unfold kernelConv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hasFDerivAt_slice {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2)) (t : ℝ) (z : Space) :
    HasFDerivAt (F t) ((fderiv ℝ (fun p : ℝ × Space => F p.1 p.2) (t, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space)) z := by
  have h1 : HasFDerivAt (fun p : ℝ × Space => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × Space => F p.1 p.2) (t, z)) (t, z) :=
    (hF.differentiable one_ne_zero (t, z)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Space => ((t, w) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) z :=
    hasFDerivAt_prodMk_right t z
  exact h1.comp z h2

private theorem continuous_fderiv_slice {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2)) :
    Continuous (fun p : ℝ × Space => fderiv ℝ (F p.1) p.2) := by
  have h : (fun p : ℝ × Space => fderiv ℝ (F p.1) p.2) = fun p =>
      (fderiv ℝ (fun q : ℝ × Space => F q.1 q.2) p).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext p
    exact (hasFDerivAt_slice hF p.1 p.2).fderiv
  rw [h]
  exact (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const

private theorem contDiff_shift {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2)) (s τ : ℝ) :
    ContDiff ℝ 1 (tensorShift F s τ) := by
  have ht : ContDiff ℝ 1 (F (s - Real.log (1 + τ))) :=
    hF.comp ((contDiff_const (c := s - Real.log (1 + τ))).prodMk contDiff_id)
  exact ht.comp (contDiff_id.const_smul ((Real.sqrt (1 + τ))⁻¹))

private theorem hasFDerivAt_shift {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2)) (s τ : ℝ) (z : Space) :
    HasFDerivAt (tensorShift F s τ)
      ((fderiv ℝ (F (s - Real.log (1 + τ))) ((Real.sqrt (1 + τ))⁻¹ • z)).comp
        ((Real.sqrt (1 + τ))⁻¹ • ContinuousLinearMap.id ℝ Space)) z := by
  have h1 : HasFDerivAt (F (s - Real.log (1 + τ)))
      (fderiv ℝ (F (s - Real.log (1 + τ))) ((Real.sqrt (1 + τ))⁻¹ • z))
      ((Real.sqrt (1 + τ))⁻¹ • z) :=
    (hasFDerivAt_slice hF _ _).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun w : Space => (Real.sqrt (1 + τ))⁻¹ • w)
      ((Real.sqrt (1 + τ))⁻¹ • ContinuousLinearMap.id ℝ Space) z :=
    (hasFDerivAt_id z).const_smul ((Real.sqrt (1 + τ))⁻¹)
  exact h1.comp z h2

private theorem fderiv_shift_apply {F : ℝ → Space → Fin 3 → Fin 3 → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2)) (s τ : ℝ) (z v : Space) :
    fderiv ℝ (tensorShift F s τ) z v =
      (Real.sqrt (1 + τ))⁻¹ • tensorShift (directionalTensor F v) s τ z := by
  rw [(hasFDerivAt_shift hF s τ z).fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul]
  rfl

private theorem norm_fderiv_shift_le {F : ℝ → Space → Fin 3 → Fin 3 → ℝ} {A : ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2))
    (hAd : ∀ s z, ‖fderiv ℝ (F s) z‖ ≤ A) (hA0 : 0 ≤ A) (s : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (z : Space) : ‖fderiv ℝ (tensorShift F s τ) z‖ ≤ A := by
  have ha0 : 0 ≤ (Real.sqrt (1 + τ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have ha1 : (Real.sqrt (1 + τ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt (by linarith)))
  refine ContinuousLinearMap.opNorm_le_bound _ hA0 fun v => ?_
  rw [fderiv_shift_apply hF s τ z v, norm_smul, Real.norm_of_nonneg ha0]
  calc _ ≤ 1 * (A * ‖v‖) :=
        mul_le_mul ha1 ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hAd _ _) (norm_nonneg v))) (norm_nonneg _) zero_le_one
    _ = A * ‖v‖ := one_mul _

private theorem measurable_kernelConv_shift (hKm : LerayKernelMeasurable)
    {H : ℝ → Space → Fin 3 → Fin 3 → ℝ} (hH : Measurable (fun p : ℝ × Space => H p.1 p.2))
    (s : ℝ) (x : Space) :
    Measurable (fun τ : ℝ => kernelConv τ (tensorShift H s τ) x) := by
  have hg : Measurable (fun p : ℝ × Space =>
      ((s - Real.log (1 + p.1), (Real.sqrt (1 + p.1))⁻¹ • p.2) : ℝ × Space)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_const.sub (Real.measurable_log.comp (measurable_const.add measurable_fst))
    · exact ((Real.continuous_sqrt.measurable.comp (measurable_const.add measurable_fst)).inv).smul
        measurable_snd
  have hHc : Measurable (fun p : ℝ × Space => tensorShift H s p.1 p.2) := hH.comp hg
  have hi : ∀ i : Fin 3, Measurable (fun τ : ℝ =>
      ∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (x - z) * tensorShift H s τ z j k) := by
    intro i
    refine (StronglyMeasurable.integral_prod_right
      (f := fun τ z => ∑ j : Fin 3, ∑ k : Fin 3,
        lerayKernel i j k τ (x - z) * tensorShift H s τ z j k) ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    show Measurable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      lerayKernel i j k p.1 (x - p.2) * tensorShift H s p.1 p.2 j k)
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    refine Measurable.mul ?_ ?_
    · exact (hKm i j k).comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
    · exact (measurable_pi_apply k).comp ((measurable_pi_apply j).comp hHc)
  unfold kernelConv
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (continuous_id.smul continuous_const).measurable.comp (hi i)

private theorem clm_eq_sum_columns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Space →L[ℝ] E) :
    L = ∑ k : Fin 3, (EuclideanSpace.proj k : Space →L[ℝ] ℝ).smulRight (L (unitVector k)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ k : Fin 3, v k • unitVector k := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [unitVector]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, ContinuousLinearMap.smulRight_apply]

theorem profileOpDeriv_holds (hKm : LerayKernelMeasurable) (hKs : KernelConvSup)
    (hCD : KernelConvDeriv) (hSmall : SmallTimeIntegrable) : ProfileOpDeriv := by
  intro hK β hβ F A hF hA hAd s y
  obtain ⟨C, hC⟩ := hKs
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA s 0)
  have hsq : ∀ τ : ℝ, 0 < τ → τ ^ (-(1 / 2 : ℝ)) = (Real.sqrt τ)⁻¹ := by
    intro τ hτ
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hτ.le]
  have hw : ∀ τ : ℝ, 0 < τ → (1 + τ) ^ (-β) ≤ (1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) := by
    intro τ hτ
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
    linarith
  have hwn : ∀ τ : ℝ, 0 < τ → 0 ≤ (1 + τ) ^ (-β) := fun τ hτ => Real.rpow_nonneg (by linarith) _
  have hwn' : ∀ τ : ℝ, 0 < τ → 0 ≤ (1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) :=
    fun τ hτ => Real.rpow_nonneg (by linarith) _
  have hg : Integrable (fun τ : ℝ => max C 0 * A *
      ((1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) * (Real.sqrt τ)⁻¹)) (volume.restrict (Ioi (0 : ℝ))) :=
    (hSmall 0).const_mul (max C 0 * A)
  have hCsq : ∀ τ : ℝ, 0 < τ → ∀ B : ℝ, 0 ≤ B →
      C * τ ^ (-(1 / 2 : ℝ)) * B ≤ max C 0 * (Real.sqrt τ)⁻¹ * B := by
    intro τ hτ B hB
    rw [hsq τ hτ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))) hB
  have hder : ∀ τ : ℝ, 0 < τ → ∀ x : Space,
      DifferentiableAt ℝ (kernelConv τ (tensorShift F s τ)) x ∧
        ∀ v, fderiv ℝ (kernelConv τ (tensorShift F s τ)) x v =
          (Real.sqrt (1 + τ))⁻¹ • kernelConv τ (tensorShift (directionalTensor F v) s τ) x := by
    intro τ hτ x
    have h := hCD hK τ hτ (tensorShift F s τ) A (contDiff_shift hF s τ) (fun z => hA _ _)
      (fun z => norm_fderiv_shift_le hF hAd hA0 s hτ z) x
    refine ⟨h.1, fun v => ?_⟩
    rw [h.2 v, ← kernelConv_const_smul]
    congr 1
    funext z
    exact fderiv_shift_apply hF s τ z v
  have hopb : ∀ τ : ℝ, 0 < τ → ∀ x : Space,
      ‖fderiv ℝ (kernelConv τ (tensorShift F s τ)) x‖ ≤ max C 0 * (Real.sqrt τ)⁻¹ * A := by
    intro τ hτ x
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (le_max_right _ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hA0)
      fun v => ?_
    have h := hCD hK τ hτ (tensorShift F s τ) A (contDiff_shift hF s τ) (fun z => hA _ _)
      (fun z => norm_fderiv_shift_le hF hAd hA0 s hτ z) x
    rw [h.2 v]
    have hm : Measurable (fun z => fderiv ℝ (tensorShift F s τ) z v) :=
      (((contDiff_shift hF s τ).continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
    have hb := hC τ hτ _ hm (A * ‖v‖) (fun z => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_shift_le hF hAd hA0 s hτ z) (norm_nonneg v))) x
    calc _ ≤ C * τ ^ (-(1 / 2 : ℝ)) * (A * ‖v‖) := hb
      _ ≤ max C 0 * (Real.sqrt τ)⁻¹ * (A * ‖v‖) := hCsq τ hτ _ (mul_nonneg hA0 (norm_nonneg v))
      _ = max C 0 * (Real.sqrt τ)⁻¹ * A * ‖v‖ := by ring
  have hf'b : ∀ τ : ℝ, 0 < τ → ∀ x : Space,
      ‖(1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) x‖ ≤
        max C 0 * A * ((1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) * (Real.sqrt τ)⁻¹) := by
    intro τ hτ x
    rw [norm_smul, Real.norm_of_nonneg (hwn τ hτ)]
    calc _ ≤ (1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) * (max C 0 * (Real.sqrt τ)⁻¹ * A) :=
          mul_le_mul (hw τ hτ) (hopb τ hτ x) (norm_nonneg _) (hwn' τ hτ)
      _ = _ := by ring
  have hfb : ∀ τ : ℝ, 0 < τ →
      ‖(1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) y‖ ≤
        max C 0 * A * ((1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) * (Real.sqrt τ)⁻¹) := by
    intro τ hτ
    rw [norm_smul, Real.norm_of_nonneg (hwn τ hτ)]
    have hb := hC τ hτ (tensorShift F s τ) (contDiff_shift hF s τ).continuous.measurable A
      (fun z => hA _ _) y
    calc _ ≤ (1 + τ) ^ (-(1 + ((0 : ℕ) : ℝ) / 2)) * (max C 0 * (Real.sqrt τ)⁻¹ * A) :=
          mul_le_mul (hw τ hτ) (hb.trans (hCsq τ hτ A hA0)) (norm_nonneg _) (hwn' τ hτ)
      _ = _ := by ring
  have hFm : Measurable (fun p : ℝ × Space => F p.1 p.2) := hF.continuous.measurable
  have hfm : ∀ x : Space, AEStronglyMeasurable
      (fun τ : ℝ => (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) x)
      (volume.restrict (Ioi (0 : ℝ))) := fun x =>
    (((measurable_const.add measurable_id).pow_const (-β)).smul
      (measurable_kernelConv_shift hKm hFm s x)).aestronglyMeasurable
  have hcol : ∀ τ ∈ Ioi (0 : ℝ), ∀ v : Space,
      ((1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y) v =
        (1 + τ) ^ (-(β + 1 / 2)) • kernelConv τ (tensorShift (directionalTensor F v) s τ) y := by
    intro τ hτ v
    have hτ' : (0 : ℝ) < τ := hτ
    have h1 : (0 : ℝ) < 1 + τ := by linarith
    rw [smul_apply, (hder τ hτ' y).2 v, smul_smul]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h1.le, ← Real.rpow_add h1]
    congr 1
    ring
  have hcolm : ∀ v : Space, Measurable (fun τ : ℝ =>
      (1 + τ) ^ (-(β + 1 / 2)) • kernelConv τ (tensorShift (directionalTensor F v) s τ) y) := by
    intro v
    have hDm : Measurable (fun p : ℝ × Space => directionalTensor F v p.1 p.2) :=
      ((continuous_fderiv_slice hF).clm_apply continuous_const).measurable
    exact ((measurable_const.add measurable_id).pow_const _).smul
      (measurable_kernelConv_shift hKm hDm s y)
  have hf'm : AEStronglyMeasurable
      (fun τ : ℝ => (1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hsum : (fun τ : ℝ => (1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y) =
        ∑ k : Fin 3, fun τ : ℝ => (EuclideanSpace.proj k : Space →L[ℝ] ℝ).smulRight
          (((1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y) (unitVector k)) := by
      funext τ
      rw [Finset.sum_apply]
      exact clm_eq_sum_columns _
    rw [hsum]
    refine Finset.aestronglyMeasurable_sum _ fun k _ => ?_
    have hk : AEStronglyMeasurable (fun τ : ℝ =>
        ((1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y) (unitVector k))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (hcolm (unitVector k)).aestronglyMeasurable.congr
        ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => (hcol τ hτ _).symm)
    exact (ContinuousLinearMap.smulRightL ℝ Space Space
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable hk
  have hf'int : Integrable
      (fun τ : ℝ => (1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hg.mono' hf'm ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => hf'b τ hτ y)
  have hfint : Integrable (fun τ : ℝ => (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) y)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hg.mono' (hfm y) ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => hfb τ hτ)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x τ => (1 + τ) ^ (-β) • kernelConv τ (tensorShift F s τ) x)
    (F' := fun x τ => (1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) x)
    (x₀ := y) (s := univ) univ_mem (Eventually.of_forall hfm) hfint hf'm
    ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ x _ => hf'b τ hτ x) hg
    ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ x _ =>
      ((hder τ hτ x).1.hasFDerivAt.const_smul ((1 + τ) ^ (-β))))
  have hP : HasFDerivAt (profileOp β F s)
      (-∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-β) • fderiv ℝ (kernelConv τ (tensorShift F s τ)) y) y :=
    key.neg
  refine ⟨hP.differentiableAt, fun v => ?_⟩
  rw [hP.fderiv, neg_apply, ContinuousLinearMap.integral_apply hf'int]
  unfold profileOp
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ => hcol τ hτ v

end Breakdown.FarField
