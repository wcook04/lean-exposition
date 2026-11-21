import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma rpow_split_one (x : ℝ≥0∞) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    x ^ s * x ^ t = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ hs ht, hst, ENNReal.rpow_one]

private lemma three_factor_split (α κ β : ℝ≥0∞) :
    α * κ * β = (α ^ (3 / 2 : ℝ) * κ ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
      (κ ^ (6 / 5 : ℝ) * β ^ (2 : ℝ)) ^ (1 / 3 : ℝ) * (α ^ (3 / 2 : ℝ) * β ^ (2 : ℝ)) ^ (1 / 6 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  simp only [← ENNReal.rpow_mul]
  calc α * κ * β = (α ^ (3 / 2 * (1 / 2) : ℝ) * α ^ (3 / 2 * (1 / 6) : ℝ)) *
        (κ ^ (6 / 5 * (1 / 2) : ℝ) * κ ^ (6 / 5 * (1 / 3) : ℝ)) *
        (β ^ (2 * (1 / 3) : ℝ) * β ^ (2 * (1 / 6) : ℝ)) := by
        rw [rpow_split_one α (by norm_num) (by norm_num) (by norm_num),
          rpow_split_one κ (by norm_num) (by norm_num) (by norm_num),
          rpow_split_one β (by norm_num) (by norm_num) (by norm_num)]
    _ = _ := by ring

private lemma three_norm_combine (A K B : ℝ≥0∞) :
    (A * K) ^ (1 / 2 : ℝ) * (K * B) ^ (1 / 3 : ℝ) * (A * B) ^ (1 / 6 : ℝ) =
      A ^ (2 / 3 : ℝ) * K ^ (5 / 6 : ℝ) * B ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  have eA : A ^ (2 / 3 : ℝ) = A ^ (1 / 2 : ℝ) * A ^ (1 / 6 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have eK : K ^ (5 / 6 : ℝ) = K ^ (1 / 2 : ℝ) * K ^ (1 / 3 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have eB : B ^ (1 / 2 : ℝ) = B ^ (1 / 3 : ℝ) * B ^ (1 / 6 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  rw [eA, eK, eB]
  ring

theorem lintegral_productBound_trilinear {a b k : Space → ℝ≥0∞} (ha : AEMeasurable a volume)
    (hb : AEMeasurable b volume) (hk : AEMeasurable k volume) :
    ∫⁻ x, ∫⁻ y, a x * k (x - y) * b y ≤
      (∫⁻ x, a x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) * (∫⁻ z, k z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
        (∫⁻ y, b y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hkd : AEMeasurable (fun z : Space × Space => k (z.1 - z.2)) (volume.prod volume) :=
    hk.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
  have hA : AEMeasurable (fun z : Space × Space => a z.1 ^ (3 / 2 : ℝ)) (volume.prod volume) :=
    (ha.pow_const _).comp_fst
  have hB : AEMeasurable (fun z : Space × Space => b z.2 ^ (2 : ℝ)) (volume.prod volume) :=
    (hb.pow_const _).comp_snd
  have hK : AEMeasurable (fun z : Space × Space => k (z.1 - z.2) ^ (6 / 5 : ℝ))
      (volume.prod volume) := hkd.pow_const _
  have hAK : AEMeasurable (fun z : Space × Space => a z.1 ^ (3 / 2 : ℝ) * k (z.1 - z.2) ^ (6 / 5 : ℝ))
      (volume.prod volume) := hA.mul hK
  have hKB : AEMeasurable (fun z : Space × Space => k (z.1 - z.2) ^ (6 / 5 : ℝ) * b z.2 ^ (2 : ℝ))
      (volume.prod volume) := hK.mul hB
  have hprod : AEMeasurable (fun z : Space × Space => a z.1 * k (z.1 - z.2) * b z.2)
      (volume.prod volume) := (ha.comp_fst.mul hkd).mul hb.comp_snd
  have h1 : ∫⁻ z, a z.1 ^ (3 / 2 : ℝ) * k (z.1 - z.2) ^ (6 / 5 : ℝ) ∂(volume.prod volume) =
      (∫⁻ x, a x ^ (3 / 2 : ℝ)) * ∫⁻ z, k z ^ (6 / 5 : ℝ) := by
    rw [lintegral_prod _ hAK]
    have hin : ∀ x : Space, ∫⁻ y, a x ^ (3 / 2 : ℝ) * k (x - y) ^ (6 / 5 : ℝ) =
        a x ^ (3 / 2 : ℝ) * ∫⁻ z, k z ^ (6 / 5 : ℝ) := by
      intro x
      have hm : AEMeasurable (fun y : Space => k (x - y) ^ (6 / 5 : ℝ)) volume :=
        (hk.pow_const _).comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
      rw [lintegral_const_mul'' _ hm]
      rw [lintegral_sub_left_eq_self (fun z => k z ^ (6 / 5 : ℝ)) x]
    simp only [hin]
    rw [lintegral_mul_const'' _ (ha.pow_const _)]
  have h2 : ∫⁻ z, k (z.1 - z.2) ^ (6 / 5 : ℝ) * b z.2 ^ (2 : ℝ) ∂(volume.prod volume) =
      (∫⁻ z, k z ^ (6 / 5 : ℝ)) * ∫⁻ y, b y ^ (2 : ℝ) := by
    rw [lintegral_prod_symm _ hKB]
    have hin : ∀ y : Space, ∫⁻ x, k (x - y) ^ (6 / 5 : ℝ) * b y ^ (2 : ℝ) =
        (∫⁻ z, k z ^ (6 / 5 : ℝ)) * b y ^ (2 : ℝ) := by
      intro y
      have hm : AEMeasurable (fun x : Space => k (x - y) ^ (6 / 5 : ℝ)) volume :=
        (hk.pow_const _).comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume y).quasiMeasurePreserving
      rw [lintegral_mul_const'' _ hm]
      rw [lintegral_sub_right_eq_self (fun z => k z ^ (6 / 5 : ℝ)) y]
    simp only [hin]
    rw [lintegral_const_mul'' _ (hb.pow_const _)]
  have h3 : ∫⁻ z, a z.1 ^ (3 / 2 : ℝ) * b z.2 ^ (2 : ℝ) ∂(volume.prod volume) =
      (∫⁻ x, a x ^ (3 / 2 : ℝ)) * ∫⁻ y, b y ^ (2 : ℝ) :=
    lintegral_prod_mul (ha.pow_const _) (hb.pow_const _)
  let F : Fin 3 → Space × Space → ℝ≥0∞ :=
    ![fun z => a z.1 ^ (3 / 2 : ℝ) * k (z.1 - z.2) ^ (6 / 5 : ℝ),
      fun z => k (z.1 - z.2) ^ (6 / 5 : ℝ) * b z.2 ^ (2 : ℝ),
      fun z => a z.1 ^ (3 / 2 : ℝ) * b z.2 ^ (2 : ℝ)]
  let w : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) (volume.prod volume) := by
    intro i _
    fin_cases i
    · exact hA.mul hK
    · exact hK.mul hB
    · exact hA.mul hB
  have hw : ∑ i ∈ (Finset.univ : Finset (Fin 3)), w i = 1 := by
    simp [w, Fin.sum_univ_three]; norm_num
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i <;> simp [w]
  have hH := ENNReal.lintegral_prod_norm_pow_le (μ := volume.prod volume) Finset.univ hF hw hw0
  simp only [Fin.prod_univ_three, F, w, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hH
  calc ∫⁻ x, ∫⁻ y, a x * k (x - y) * b y
      = ∫⁻ z, a z.1 * k (z.1 - z.2) * b z.2 ∂(volume.prod volume) :=
        (lintegral_prod _ hprod).symm
    _ = ∫⁻ z, (a z.1 ^ (3 / 2 : ℝ) * k (z.1 - z.2) ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
          (k (z.1 - z.2) ^ (6 / 5 : ℝ) * b z.2 ^ (2 : ℝ)) ^ (1 / 3 : ℝ) *
          (a z.1 ^ (3 / 2 : ℝ) * b z.2 ^ (2 : ℝ)) ^ (1 / 6 : ℝ) ∂(volume.prod volume) := by
        congr 1
        funext z
        exact three_factor_split _ _ _
    _ ≤ _ := hH
    _ = _ := by rw [h1, h2, h3, three_norm_combine]

private lemma lintegral_radial_eq (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ f s)
    (hint : IntegrableOn (fun y : ℝ => y ^ 2 * f y) (Ioi 0)) :
    ∫⁻ z : Space, ENNReal.ofReal (f ‖z‖) =
      ENNReal.ofReal (4 * π * ∫ y in Ioi (0 : ℝ), y ^ 2 * f y) := by
  have hfin : Module.finrank ℝ Space = 3 := by simp
  have hI : Integrable (fun z : Space => f ‖z‖) volume := by
    rw [integrable_fun_norm_addHaar volume (f := f), hfin]
    simpa using hint
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun z => hf0 _),
    integral_fun_norm_addHaar volume f, hfin]
  congr 1
  simp [Measure.real, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

private lemma rpow_inner_kernel {y : ℝ} (hy : 0 < y) :
    y ^ 2 * (y⁻¹ ^ 2) ^ (6 / 5 : ℝ) = y ^ (-2 / 5 : ℝ) := by
  have h1 : y⁻¹ ^ 2 = y ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hy.le, inv_pow]; norm_cast
  rw [h1, ← Real.rpow_mul hy.le, ← Real.rpow_two, ← Real.rpow_add hy]
  norm_num

private lemma rpow_outer_kernel {y : ℝ} (hy : 0 < y) :
    y ^ 2 * (y⁻¹ ^ 3) ^ (2 : ℝ) = y ^ (-4 : ℝ) := by
  have h1 : y⁻¹ ^ 3 = y ^ (-3 : ℝ) := by
    rw [Real.rpow_neg hy.le, inv_pow]; norm_cast
  rw [h1, ← Real.rpow_mul hy.le, ← Real.rpow_two, ← Real.rpow_add hy]
  norm_num

theorem lintegral_inner_kernel_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in Metric.ball (0 : Space) r, ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤
      ENNReal.ofReal (20 * π / 3 * r ^ (3 / 5 : ℝ)) := by
  set g : ℝ → ℝ := (Iio r).indicator (fun s => (s⁻¹ ^ 2) ^ (6 / 5 : ℝ)) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s =>
    Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (sq_nonneg _) _) s
  have hpt : ∀ z : Space, (Metric.ball (0 : Space) r).indicator
      (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ)) z = ENNReal.ofReal (g ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ < r
    · rw [Set.indicator_of_mem (by simpa using hz), hg,
        Set.indicator_of_mem (show ‖z‖ ∈ Iio r from hz),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
    · rw [Set.indicator_of_notMem (by simpa using hz), hg,
        Set.indicator_of_notMem (show ‖z‖ ∉ Iio r from hz), ENNReal.ofReal_zero]
  have hEq : EqOn (fun y : ℝ => y ^ 2 * g y)
      ((Ioo 0 r).indicator (fun y => y ^ (-2 / 5 : ℝ))) (Ioi 0) := by
    intro y hy
    simp only [hg]
    by_cases hyr : y < r
    · rw [Set.indicator_of_mem (show y ∈ Iio r from hyr),
        Set.indicator_of_mem (show y ∈ Ioo 0 r from ⟨hy, hyr⟩)]
      exact rpow_inner_kernel hy
    · rw [Set.indicator_of_notMem (show y ∉ Iio r from hyr),
        Set.indicator_of_notMem (fun h => hyr h.2), mul_zero]
  have hloc : IntegrableOn (fun y : ℝ => y ^ (-2 / 5 : ℝ)) (Ioo 0 r) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r)
      (by norm_num : (-1 : ℝ) < -2 / 5)).1).mono_set Ioo_subset_Ioc_self
  have hint : IntegrableOn (fun y : ℝ => y ^ 2 * g y) (Ioi 0) :=
    ((hloc.integrable_indicator measurableSet_Ioo).integrableOn).congr_fun hEq.symm
      measurableSet_Ioi
  have hval : ∫ y in Ioi (0 : ℝ), y ^ 2 * g y = 5 / 3 * r ^ (3 / 5 : ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, setIntegral_indicator measurableSet_Ioo,
      show Ioi (0 : ℝ) ∩ Ioo 0 r = Ioo 0 r from Set.inter_eq_right.2 Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl (by norm_num))]
    have he : (-2 / 5 : ℝ) + 1 = 3 / 5 := by norm_num
    rw [he, Real.zero_rpow (by norm_num)]
    ring
  rw [← lintegral_indicator measurableSet_ball]
  simp only [hpt]
  rw [lintegral_radial_eq g hg0 hint, hval]
  apply le_of_eq
  congr 1
  ring

theorem lintegral_outer_kernel_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in (Metric.ball (0 : Space) r)ᶜ, ENNReal.ofReal (‖z‖⁻¹ ^ 3) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * π / 3 * r⁻¹ ^ 3) := by
  set g : ℝ → ℝ := (Ici r).indicator (fun s => (s⁻¹ ^ 3) ^ (2 : ℝ)) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s =>
    Set.indicator_nonneg (fun t ht => Real.rpow_nonneg
      (pow_nonneg (inv_nonneg.2 (hr.le.trans (show r ≤ t from ht))) _) _) s
  have hpt : ∀ z : Space, (Metric.ball (0 : Space) r)ᶜ.indicator
      (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 3) ^ (2 : ℝ)) z = ENNReal.ofReal (g ‖z‖) := by
    intro z
    by_cases hz : r ≤ ‖z‖
    · rw [Set.indicator_of_mem (by simpa using hz), hg,
        Set.indicator_of_mem (show ‖z‖ ∈ Ici r from hz),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    · rw [Set.indicator_of_notMem (by simpa using hz), hg,
        Set.indicator_of_notMem (show ‖z‖ ∉ Ici r from hz), ENNReal.ofReal_zero]
  have hEq : EqOn (fun y : ℝ => y ^ 2 * g y)
      ((Ici r).indicator (fun y => y ^ (-4 : ℝ))) (Ioi 0) := by
    intro y hy
    simp only [hg]
    by_cases hyr : r ≤ y
    · rw [Set.indicator_of_mem (show y ∈ Ici r from hyr),
        Set.indicator_of_mem (show y ∈ Ici r from hyr)]
      exact rpow_outer_kernel hy
    · rw [Set.indicator_of_notMem (show y ∉ Ici r from hyr),
        Set.indicator_of_notMem (show y ∉ Ici r from hyr), mul_zero]
  have hloc : IntegrableOn (fun y : ℝ => y ^ (-4 : ℝ)) (Ici r) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (hb := enorm_ne_top)).2 (integrableOn_Ioi_rpow_of_lt (by norm_num) hr)
  have hint : IntegrableOn (fun y : ℝ => y ^ 2 * g y) (Ioi 0) :=
    ((hloc.integrable_indicator measurableSet_Ici).integrableOn).congr_fun hEq.symm
      measurableSet_Ioi
  have hval : ∫ y in Ioi (0 : ℝ), y ^ 2 * g y = r⁻¹ ^ 3 / 3 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici r = Ici r from Set.inter_eq_right.2 (Ici_subset_Ioi.2 hr),
      integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) hr]
    have he : r ^ ((-4 : ℝ) + 1) = r⁻¹ ^ 3 := by
      rw [show (-4 : ℝ) + 1 = -(3 : ℝ) by norm_num, Real.rpow_neg hr.le, inv_pow]
      norm_cast
    rw [he]
    ring
  rw [← lintegral_indicator measurableSet_ball.compl]
  simp only [hpt]
  rw [lintegral_radial_eq g hg0 hint, hval]
  apply le_of_eq
  congr 1
  ring

end Breakdown
