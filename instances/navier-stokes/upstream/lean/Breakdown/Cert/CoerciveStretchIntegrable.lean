import Breakdown.Cert.CoerciveStretchFibre

open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace StretchIntegrableInternal

open Internal.ModeRotation

private theorem partial_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ × Space → E) (hΦ : Differentiable ℝ Φ) (σ : ℝ) (x : Space) :
    fderiv ℝ (fun x => Φ (σ, x)) x = (fderiv ℝ Φ (σ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  ((hΦ (σ, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right σ x)).fderiv

private theorem continuous_partial_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ × Space → E) (hΦ : ContDiff ℝ 1 Φ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => Φ (z.1, x)) z.2) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (fun x => Φ (z.1, x)) z.2)
      = fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact partial_fderiv_eq Φ (hΦ.differentiable (by norm_num)) z.1 z.2
  rw [h]
  exact (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const

private theorem continuous_fderiv_slice (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
  continuous_partial_fderiv (fun z : ℝ × Space => W z.1 z.2) (hW.of_le (by norm_num))

private theorem continuous_fderiv2_slice (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) := by
  set F : ℝ × Space → Space := fun z => W z.1 z.2 with hF
  set D : ℝ × Space → (Space →L[ℝ] Space) :=
    fun z => (fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ ℝ Space) with hD
  have hDc : ContDiff ℝ 1 D := (hW.fderiv_right (m := 1) (by norm_num)).clm_comp contDiff_const
  have he : ∀ σ, (fun x => fderiv ℝ (W σ) x) = fun x => D (σ, x) := by
    intro σ
    funext x
    exact partial_fderiv_eq F (hW.differentiable (by norm_num)) σ x
  have h : (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2)
      = fun z => fderiv ℝ (fun x => D (z.1, x)) z.2 := by
    funext z
    rw [he z.1]
  rw [h]
  exact continuous_partial_fderiv D hDc

private theorem opNorm_sq_le_matSq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have hle : ‖A‖ ≤ ‖A (unitVector 0)‖ + ‖A (unitVector 1)‖ + ‖A (unitVector 2)‖ := by
    refine A.opNorm_le_bound (by positivity) (fun x => ?_)
    have hx : x = x 0 • unitVector 0 + x 1 • unitVector 1 + x 2 • unitVector 2 := by
      ext i
      fin_cases i <;> simp [unitVector]
    have h0 : ‖x 0‖ ≤ ‖x‖ := PiLp.norm_apply_le x 0
    have h1 : ‖x 1‖ ≤ ‖x‖ := PiLp.norm_apply_le x 1
    have h2 : ‖x 2‖ ≤ ‖x‖ := PiLp.norm_apply_le x 2
    conv_lhs => rw [hx, map_add, map_add, map_smul, map_smul, map_smul]
    refine (norm_add₃_le).trans ?_
    rw [norm_smul, norm_smul, norm_smul]
    have := norm_nonneg (A (unitVector 0))
    have := norm_nonneg (A (unitVector 1))
    have := norm_nonneg (A (unitVector 2))
    nlinarith [mul_le_mul_of_nonneg_right h0 (norm_nonneg (A (unitVector 0))),
      mul_le_mul_of_nonneg_right h1 (norm_nonneg (A (unitVector 1))),
      mul_le_mul_of_nonneg_right h2 (norm_nonneg (A (unitVector 2)))]
  have hA0 := norm_nonneg A
  simp only [matSq, Fin.sum_univ_three]
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖), sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖),
    norm_nonneg (A (unitVector 0)), norm_nonneg (A (unitVector 1)), norm_nonneg (A (unitVector 2))]

private theorem box_ae_mem' : ∀ᵐ p ∂boxMeasure, p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have h : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))), p ∈ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [h] with p hp
  exact ⟨Set.Ioc_subset_Icc_self hp.1, Set.Ioc_subset_Icc_self hp.2⟩

private def fibreStretch (W : ℝ → Space → Space) (y : Space)
    (q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space))) : ℝ :=
  stretchForm W (fun _ _ => q.2.1) (fun _ _ => q.2.2) q.1.1 (axialRot q.1.2 y)

private theorem continuous_fibreStretch (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (y : Space) :
    Continuous (fibreStretch W y) := by
  have h2 : Continuous (fun q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space)) => ((q.1.2, y) : ℝ × Space)) := by
    fun_prop
  have h3 : Continuous (fun q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space)) => axialRot q.1.2 y) := by
    have h := continuous_axialRot.comp h2
    exact h
  have hpath : Continuous (fun q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space)) =>
      ((q.1.1, axialRot q.1.2 y) : ℝ × Space)) := by
    fun_prop
  have hC1 : Continuous (fun q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space)) =>
      fderiv ℝ (W q.1.1) (axialRot q.1.2 y)) := (continuous_fderiv_slice W hW).comp hpath
  have hC2 : Continuous (fun q : (ℝ × ℝ) × (Space × (Space →L[ℝ] Space)) =>
      fderiv ℝ (fun x => fderiv ℝ (W q.1.1) x) (axialRot q.1.2 y)) :=
    (continuous_fderiv2_slice W hW).comp hpath
  have hcoord : ∀ i : Fin 3, Continuous (fun x : Space => x i) := fun i => (EuclideanSpace.proj i).continuous
  unfold fibreStretch stretchForm curlVec vortGrad
  fun_prop

private theorem curlVec_smul (t : ℝ) (A : Space →L[ℝ] Space) : curlVec (t • A) = t • curlVec A := by
  unfold curlVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem fibreStretch_smul (W : ℝ → Space → Space) (y : Space) (p : ℝ × ℝ)
    (w : Space × (Space →L[ℝ] Space)) (t : ℝ) :
    fibreStretch W y (p, t • w) = t ^ 2 * fibreStretch W y (p, w) := by
  simp only [fibreStretch, stretchForm, Prod.smul_fst, Prod.smul_snd, curlVec_smul, PiLp.smul_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp only [mul_add, mul_neg, Finset.mul_sum]
  congr 1
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))))
    ring

private theorem fibreStretch_bound (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (y : Space) :
    ∃ K, 0 ≤ K ∧ ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
      ∀ w : Space × (Space →L[ℝ] Space), |fibreStretch W y (p, w)| ≤ K * ‖w‖ ^ 2 := by
  obtain ⟨K, hK⟩ := ((isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))).prod
    (isCompact_sphere (0 : Space × (Space →L[ℝ] Space)) 1)).exists_bound_of_continuousOn
      (continuous_fibreStretch W hW y).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun p hp w => ?_⟩
  rcases eq_or_ne w 0 with h0 | h0
  · subst h0
    have e := fibreStretch_smul W y p 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at e
    rw [e, abs_zero]
    positivity
  · have ht : 0 < ‖w‖ := norm_pos_iff.2 h0
    have hs : (‖w‖⁻¹ • w) ∈ Metric.sphere (0 : Space × (Space →L[ℝ] Space)) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
    have hb := hK (p, ‖w‖⁻¹ • w) ⟨hp, hs⟩
    rw [Real.norm_eq_abs, fibreStretch_smul W y p w ‖w‖⁻¹, abs_mul, abs_of_nonneg (sq_nonneg _)] at hb
    have h2 : |fibreStretch W y (p, w)| = ‖w‖ ^ 2 * (‖w‖⁻¹ ^ 2 * |fibreStretch W y (p, w)|) := by
      field_simp
    rw [h2]
    calc ‖w‖ ^ 2 * (‖w‖⁻¹ ^ 2 * |fibreStretch W y (p, w)|) ≤ ‖w‖ ^ 2 * max K 0 :=
          mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (sq_nonneg _)
      _ = max K 0 * ‖w‖ ^ 2 := mul_comm _ _

theorem fibre_stretch_integrable (hRot : AxialRotationHolds)
    (hLoc : PerturbationLocalSquareIntegrabilityHolds) (Γ : Set Symmetry) (P : ℝ)
    (W : ℝ → Space → Space) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space, Integrable (fun p : ℝ × ℝ => stretchForm W v G p.1 (axialRot p.2 y)) boxMeasure := by
  have hGfin : ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖G σ y‖ ^ 2) < ⊤ := by
    intro R
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 3)) hv.gradient_finite)
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun σ => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono (fun y => ?_))
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (opNorm_sq_le_matSq (G σ y))
  have hGm := StretchFibreInternal.ae_memLp_fibre hRot (E := Space →L[ℝ] Space) (u := G)
    hv.measurable_gradient hGfin
  have hVm := StretchFibreInternal.ae_memLp_fibre_vel hRot hLoc hv
  filter_upwards [hGm, hVm] with y hG hV
  obtain ⟨K, hK0, hK⟩ := fibreStretch_bound W hW y
  have hV2 : MemLp (fun p : ℝ × ℝ => v p.1 (axialRot p.2 y)) ((2 : ℕ) : ENNReal) boxMeasure := by
    simpa using hV
  have hG2 : MemLp (fun p : ℝ × ℝ => G p.1 (axialRot p.2 y)) ((2 : ℕ) : ENNReal) boxMeasure := by
    simpa using hG
  have hint : Integrable (fun p : ℝ × ℝ =>
      K * (‖v p.1 (axialRot p.2 y)‖ ^ 2 + ‖G p.1 (axialRot p.2 y)‖ ^ 2)) boxMeasure :=
    ((hV2.integrable_norm_pow (by norm_num)).add (hG2.integrable_norm_pow (by norm_num))).const_mul K
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      fibreStretch W y (p, (v p.1 (axialRot p.2 y), G p.1 (axialRot p.2 y)))) boxMeasure :=
    (continuous_fibreStretch W hW y).comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk (hV.1.prodMk hG.1))
  show Integrable (fun p : ℝ × ℝ =>
    fibreStretch W y (p, (v p.1 (axialRot p.2 y), G p.1 (axialRot p.2 y)))) boxMeasure
  refine Integrable.mono' hint hmeas ?_
  filter_upwards [box_ae_mem'] with p hp
  rw [Real.norm_eq_abs]
  refine (hK p hp _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [Prod.norm_def]
  rcases max_choice ‖v p.1 (axialRot p.2 y)‖ ‖G p.1 (axialRot p.2 y)‖ with h | h <;> rw [h] <;>
    nlinarith [sq_nonneg ‖v p.1 (axialRot p.2 y)‖, sq_nonneg ‖G p.1 (axialRot p.2 y)‖]

end StretchIntegrableInternal

end Coercive

end Breakdown
