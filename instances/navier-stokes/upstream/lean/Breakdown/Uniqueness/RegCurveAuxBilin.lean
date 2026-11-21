import Breakdown.Uniqueness.RegCurveAuxMeasure

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem bilin_weight_ge_one (m : ℕ) (ξ : Space) : 1 ≤ (1 + ‖ξ‖) ^ m :=
  one_le_pow₀ (by linarith [norm_nonneg ξ])

private theorem bilin_weight_measurable (m : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ m)) := by
  fun_prop

private theorem bilin_volume_ac (m : ℕ) : (volume : Measure Space) ≪ weightedVolume m := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [weightedVolume, withDensity_apply _ hs] at h0
  have h1 : ∫⁻ _ in s, (1 : ℝ≥0∞) ≤ ∫⁻ ξ in s, ENNReal.ofReal ((1 + ‖ξ‖) ^ m) :=
    lintegral_mono fun ξ => by simpa using ENNReal.ofReal_le_ofReal (bilin_weight_ge_one m ξ)
  rw [h0] at h1
  simpa using h1

private theorem bilin_weighted_ac (m : ℕ) : weightedVolume m ≪ (volume : Measure Space) :=
  withDensity_absolutelyContinuous _ _

private theorem bilin_lintegral_weighted (m : ℕ) {g : Space → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ∫⁻ ξ, g ξ ∂weightedVolume m = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ m) * g ξ := by
  rw [weightedVolume, lintegral_withDensity_eq_lintegral_mul₀ (bilin_weight_measurable m).aemeasurable hg]
  rfl

private theorem bilin_memLp_iff (m : ℕ) (f : Space → CSpace) :
    MemLp f 1 (weightedVolume m) ↔ AEStronglyMeasurable f volume ∧
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ m) * ‖f ξ‖ₑ < ⊤ := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : AEStronglyMeasurable f volume := h1.mono_ac (bilin_volume_ac m)
    refine ⟨h3, ?_⟩
    rwa [eLpNorm_one_eq_lintegral_enorm, bilin_lintegral_weighted m h3.enorm] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1.mono_ac (bilin_weighted_ac m), ?_⟩
    rwa [eLpNorm_one_eq_lintegral_enorm, bilin_lintegral_weighted m h1.enorm]

private theorem bilin_ofReal_norm (m : ℕ) (F : Lp CSpace 1 (weightedVolume m)) :
    ENNReal.ofReal ‖F‖ = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ m) * ‖(F : Space → CSpace) ξ‖ₑ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F), eLpNorm_one_eq_lintegral_enorm,
    bilin_lintegral_weighted m ((Lp.aestronglyMeasurable F).mono_ac (bilin_volume_ac m)).enorm]

private theorem bilin_integrable_weight {m : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume m)) :
    Integrable (fun η => (1 + ‖η‖) ^ m * ‖f η‖) volume := by
  obtain ⟨h1, h2⟩ := (bilin_memLp_iff m f).1 hf
  refine ⟨(by fun_prop : Continuous fun η : Space => (1 + ‖η‖) ^ m).aestronglyMeasurable.mul h1.norm, ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun η => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (by positivity), enorm_norm]

private theorem bilin_comp_aesm {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) (j : Fin 3) :
    AEStronglyMeasurable (fun η => f η j) volume :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hf

private theorem bilin_integrable_left {m : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume m))
    (j : Fin 3) : Integrable (fun η => f η j) volume := by
  refine (bilin_integrable_weight hf).mono' (bilin_comp_aesm ((bilin_memLp_iff m f).1 hf).1 j)
    (Eventually.of_forall fun η => ?_)
  calc ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le _ _
    _ = 1 * ‖f η‖ := (one_mul _).symm
    _ ≤ (1 + ‖η‖) ^ m * ‖f η‖ := by gcongr; exact bilin_weight_ge_one m η

private theorem bilin_integrable_right {k : ℕ} {g : Space → CSpace} (hg : MemLp g 1 (weightedVolume (k + 1)))
    (i j : Fin 3) :
    Integrable (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) volume := by
  refine ((bilin_integrable_weight hg).const_mul (2 * π)).mono'
    (((by fun_prop : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ))).aestronglyMeasurable.mul
      (bilin_comp_aesm ((bilin_memLp_iff _ g).1 hg).1 i)) (Eventually.of_forall fun η => ?_)
  have h1 : ‖g η i‖ ≤ ‖g η‖ := PiLp.norm_apply_le _ _
  have h2 : |η j| ≤ ‖η‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le η j
  have h3 : ‖η‖ ≤ (1 + ‖η‖) ^ (k + 1) :=
    (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (by linarith [norm_nonneg η]) (by omega))
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos,
    Complex.norm_ofNat, mul_one]
  calc 2 * π * |η j| * ‖g η i‖ ≤ 2 * π * ‖η‖ * ‖g η‖ := by gcongr
    _ ≤ 2 * π * ((1 + ‖η‖) ^ (k + 1) * ‖g η‖) := by
      rw [← mul_assoc]; gcongr


private theorem bilin_integrand_norm_le (a b : CSpace) (x : Space) (i j : Fin 3) :
    ‖a j * (2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * b i)‖ ≤ 2 * π * (‖a‖ * (‖x‖ * ‖b‖)) := by
  have h1 : ‖a j‖ ≤ ‖a‖ := PiLp.norm_apply_le _ _
  have h2 : ‖b i‖ ≤ ‖b‖ := PiLp.norm_apply_le _ _
  have h3 : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos,
    Complex.norm_ofNat, mul_one]
  calc ‖a j‖ * (2 * π * |x j| * ‖b i‖) = 2 * π * (‖a j‖ * (|x j| * ‖b i‖)) := by ring
    _ ≤ _ := by gcongr

private theorem bilin_norm_le_sum (v : CSpace) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three]
  have := norm_nonneg (v 0); have := norm_nonneg (v 1); have := norm_nonneg (v 2)
  nlinarith

private theorem bilin_enorm_le_sum (v : CSpace) : ‖v‖ₑ ≤ ∑ i, ‖v i‖ₑ := by
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (∑ i, ‖v i‖) := ENNReal.ofReal_le_ofReal (bilin_norm_le_sum v)
    _ = ∑ i, ‖v i‖ₑ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
      simp only [ofReal_norm]

private theorem bilin_adv_apply (f g : Space → CSpace) (ξ : Space) (i : Fin 3) :
    advectionBilin f g ξ i = ∑ j, ∫ η, f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * g (ξ - η) i) := by
  simp only [advectionBilin, convC]

private theorem bilin_adv_enorm_le (f g : Space → CSpace) (ξ : Space) :
    ‖advectionBilin f g ξ‖ₑ ≤
      9 * (ENNReal.ofReal (2 * π) * ∫⁻ η, ‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ)) := by
  have hpt : ∀ i j, ‖∫ η, f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * g (ξ - η) i)‖ₑ ≤
      ENNReal.ofReal (2 * π) * ∫⁻ η, ‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ) := by
    intro i j
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun η => ?_
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (bilin_integrand_norm_le _ _ _ i j)
  calc ‖advectionBilin f g ξ‖ₑ ≤ ∑ i, ‖advectionBilin f g ξ i‖ₑ := bilin_enorm_le_sum _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
        ENNReal.ofReal (2 * π) * ∫⁻ η, ‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [bilin_adv_apply]
      exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hpt i j)
    _ = _ := by simp [Finset.sum_const]; ring

private theorem bilin_weight_mul_le (k : ℕ) (ξ η : Space) :
    (1 + ‖ξ‖) ^ k * ‖ξ - η‖ ≤ (1 + ‖η‖) ^ (k + 1) * (1 + ‖ξ - η‖) ^ (k + 1) := by
  have ha : 0 ≤ ‖η‖ := norm_nonneg _
  have hb : 0 ≤ ‖ξ - η‖ := norm_nonneg _
  have h1 : 1 + ‖ξ‖ ≤ (1 + ‖η‖) * (1 + ‖ξ - η‖) := by
    have : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
      calc ‖ξ‖ = ‖η + (ξ - η)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    nlinarith
  have h2 : ‖ξ - η‖ ≤ (1 + ‖η‖) * (1 + ‖ξ - η‖) := by nlinarith
  calc (1 + ‖ξ‖) ^ k * ‖ξ - η‖ ≤ ((1 + ‖η‖) * (1 + ‖ξ - η‖)) ^ k * ((1 + ‖η‖) * (1 + ‖ξ - η‖)) := by
        gcongr
    _ = _ := by rw [← pow_succ, mul_pow]

private theorem bilin_lintegral_conv (a b : Space → ℝ≥0∞) (ha : AEMeasurable a volume)
    (hb : AEMeasurable b volume) :
    ∫⁻ ξ, ∫⁻ η, a η * b (ξ - η) = (∫⁻ η, a η) * ∫⁻ η, b η := by
  have hm : AEMeasurable (Function.uncurry fun ξ η : Space => a η * b (ξ - η))
      ((volume : Measure Space).prod volume) :=
    (ha.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (hb.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  rw [lintegral_lintegral_swap hm]
  have h : ∀ η : Space, ∫⁻ ξ, a η * b (ξ - η) = a η * ∫⁻ ξ, b ξ := fun η => by
    have hb' : AEMeasurable (fun ξ => b (ξ - η)) volume :=
      hb.comp_quasiMeasurePreserving (measurePreserving_sub_right volume η).quasiMeasurePreserving
    rw [lintegral_const_mul'' _ hb', lintegral_sub_right_eq_self]
  simp_rw [h]
  rw [lintegral_mul_const'' _ ha]


private theorem bilin_lintegral_adv_le (k : ℕ) {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖advectionBilin f g ξ‖ₑ ≤
      9 * ENNReal.ofReal (2 * π) *
        ((∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖f η‖ₑ) *
          ∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖g η‖ₑ) := by
  have ha : AEMeasurable (fun η => ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖f η‖ₑ) volume :=
    (bilin_weight_measurable _).aemeasurable.mul hf.enorm
  have hb : AEMeasurable (fun η => ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖g η‖ₑ) volume :=
    (bilin_weight_measurable _).aemeasurable.mul hg.enorm
  have hpt : ∀ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖advectionBilin f g ξ‖ₑ ≤
      9 * ENNReal.ofReal (2 * π) * ∫⁻ η, (ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖f η‖ₑ) *
        (ENNReal.ofReal ((1 + ‖ξ - η‖) ^ (k + 1)) * ‖g (ξ - η)‖ₑ) := by
    intro ξ
    calc _ ≤ ENNReal.ofReal ((1 + ‖ξ‖) ^ k) *
          (9 * (ENNReal.ofReal (2 * π) * ∫⁻ η, ‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ))) := by
          gcongr; exact bilin_adv_enorm_le f g ξ
      _ = 9 * ENNReal.ofReal (2 * π) * ∫⁻ η, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) *
          (‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring
      _ ≤ _ := by
          refine mul_le_mul' le_rfl (lintegral_mono fun η => ?_)
          have hw : ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ENNReal.ofReal ‖ξ - η‖ ≤
              ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ENNReal.ofReal ((1 + ‖ξ - η‖) ^ (k + 1)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (bilin_weight_mul_le k ξ η)
          calc ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * (‖f η‖ₑ * (ENNReal.ofReal ‖ξ - η‖ * ‖g (ξ - η)‖ₑ))
              = (ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ENNReal.ofReal ‖ξ - η‖) * (‖f η‖ₑ * ‖g (ξ - η)‖ₑ) := by
                ring
            _ ≤ (ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ENNReal.ofReal ((1 + ‖ξ - η‖) ^ (k + 1))) *
                (‖f η‖ₑ * ‖g (ξ - η)‖ₑ) := by gcongr
            _ = _ := by ring
  calc _ ≤ ∫⁻ ξ, 9 * ENNReal.ofReal (2 * π) * ∫⁻ η, (ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖f η‖ₑ) *
        (ENNReal.ofReal ((1 + ‖ξ - η‖) ^ (k + 1)) * ‖g (ξ - η)‖ₑ) := lintegral_mono hpt
    _ = 9 * ENNReal.ofReal (2 * π) * ∫⁻ ξ, ∫⁻ η, (ENNReal.ofReal ((1 + ‖η‖) ^ (k + 1)) * ‖f η‖ₑ) *
        (ENNReal.ofReal ((1 + ‖ξ - η‖) ^ (k + 1)) * ‖g (ξ - η)‖ₑ) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    _ = _ := by rw [bilin_lintegral_conv _ _ ha hb]

private theorem bilin_convC_aesm {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) : AEStronglyMeasurable (convC u v) volume :=
  (hu.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hv).integral_prod_right'

private theorem bilin_adv_aesm {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (advectionBilin f g) volume := by
  have hc : ∀ i j : Fin 3, AEStronglyMeasurable (convC (fun η => f η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i)) volume := fun i j =>
    bilin_convC_aesm (bilin_comp_aesm hf j)
      ((by fun_prop : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ)
        ).aestronglyMeasurable.mul (bilin_comp_aesm hg i))
  have hs : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => ∑ j, convC (fun η => f η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) ξ) volume := fun i =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => hc i j
  have he : advectionBilin f g = fun ξ => ∑ i, (∑ j, convC (fun η => f η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) ξ) •
        EuclideanSpace.single i (1 : ℂ) := by
    funext ξ
    ext l
    simp [advectionBilin, Pi.single_apply, mul_ite]
  rw [he]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hs i).smul_const _

private theorem bilin_adv_congr {f f' g g' : Space → CSpace} (hf : f =ᵐ[volume] f')
    (hg : g =ᵐ[volume] g') : advectionBilin f g = advectionBilin f' g' := by
  funext ξ
  ext i
  rw [bilin_adv_apply, bilin_adv_apply]
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  have hg' : (g ∘ fun η => ξ - η) =ᵐ[volume] (g' ∘ fun η => ξ - η) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae_eq_comp hg
  filter_upwards [hf, hg'] with η h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

private theorem bilin_memLp (k : ℕ) {f g : Space → CSpace} (hf : MemLp f 1 (weightedVolume (k + 1)))
    (hg : MemLp g 1 (weightedVolume (k + 1))) : MemLp (advectionBilin f g) 1 (weightedVolume k) := by
  obtain ⟨hf1, hf2⟩ := (bilin_memLp_iff _ f).1 hf
  obtain ⟨hg1, hg2⟩ := (bilin_memLp_iff _ g).1 hg
  refine (bilin_memLp_iff k _).2 ⟨bilin_adv_aesm hf1 hg1, ?_⟩
  refine lt_of_le_of_lt (bilin_lintegral_adv_le k hf1 hg1) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
    (ENNReal.mul_lt_top hf2 hg2)


private theorem bilin_integrable_at {u v : Space → ℂ} {ξ : Space}
    (h : ConvolutionExistsAt u v ξ (ContinuousLinearMap.mul ℂ ℂ) volume) :
    Integrable (fun η => u η * v (ξ - η)) volume :=
  h.congr (Eventually.of_forall fun _ => ContinuousLinearMap.mul_apply' _ _ _ _)

private theorem bilin_ae_exists {k : ℕ} {f g : Space → CSpace} (hf : MemLp f 1 (weightedVolume (k + 1)))
    (hg : MemLp g 1 (weightedVolume (k + 1))) :
    ∀ᵐ ξ ∂volume, ∀ i j : Fin 3, Integrable (fun η : Space =>
      f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * g (ξ - η) i)) volume := by
  have h : ∀ i j : Fin 3, ∀ᵐ ξ ∂volume, Integrable (fun η : Space =>
      f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * g (ξ - η) i)) volume := fun i j =>
    ((bilin_integrable_left hf j).ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ)
      (bilin_integrable_right hg i j)).mono fun ξ hξ => bilin_integrable_at hξ
  simp only [ae_all_iff]
  exact h

private theorem bilin_adv_add_left {k : ℕ} {f₁ f₂ g : Space → CSpace}
    (hf₁ : MemLp f₁ 1 (weightedVolume (k + 1))) (hf₂ : MemLp f₂ 1 (weightedVolume (k + 1)))
    (hg : MemLp g 1 (weightedVolume (k + 1))) :
    advectionBilin (f₁ + f₂) g =ᵐ[volume] advectionBilin f₁ g + advectionBilin f₂ g := by
  filter_upwards [bilin_ae_exists hf₁ hg, bilin_ae_exists hf₂ hg] with ξ h₁ h₂
  ext i
  rw [Pi.add_apply, PiLp.add_apply, bilin_adv_apply, bilin_adv_apply, bilin_adv_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (h₁ i j) (h₂ i j)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply, PiLp.add_apply, add_mul]

private theorem bilin_adv_add_right {k : ℕ} {f g₁ g₂ : Space → CSpace}
    (hf : MemLp f 1 (weightedVolume (k + 1))) (hg₁ : MemLp g₁ 1 (weightedVolume (k + 1)))
    (hg₂ : MemLp g₂ 1 (weightedVolume (k + 1))) :
    advectionBilin f (g₁ + g₂) =ᵐ[volume] advectionBilin f g₁ + advectionBilin f g₂ := by
  filter_upwards [bilin_ae_exists hf hg₁, bilin_ae_exists hf hg₂] with ξ h₁ h₂
  ext i
  rw [Pi.add_apply, PiLp.add_apply, bilin_adv_apply, bilin_adv_apply, bilin_adv_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (h₁ i j) (h₂ i j)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply, PiLp.add_apply, mul_add]

private theorem bilin_adv_smul_left (c : ℝ) (f g : Space → CSpace) :
    advectionBilin (c • f) g = c • advectionBilin f g := by
  funext ξ
  ext i
  rw [Pi.smul_apply, PiLp.smul_apply, bilin_adv_apply, bilin_adv_apply, Complex.real_smul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]
  ring

private theorem bilin_adv_smul_right (c : ℝ) (f g : Space → CSpace) :
    advectionBilin f (c • g) = c • advectionBilin f g := by
  funext ξ
  ext i
  rw [Pi.smul_apply, PiLp.smul_apply, bilin_adv_apply, bilin_adv_apply, Complex.real_smul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]
  ring

private def advectionLp (k : ℕ) (F G : Lp CSpace 1 (weightedVolume (k + 1))) :
    Lp CSpace 1 (weightedVolume k) :=
  (bilin_memLp k (Lp.memLp F) (Lp.memLp G)).toLp _

private theorem advectionLp_coe (k : ℕ) (F G : Lp CSpace 1 (weightedVolume (k + 1))) :
    (advectionLp k F G : Space → CSpace) =ᵐ[weightedVolume k] advectionBilin F G :=
  MemLp.coeFn_toLp _

private theorem advectionLp_add_left (k : ℕ) (F₁ F₂ G : Lp CSpace 1 (weightedVolume (k + 1))) :
    advectionLp k (F₁ + F₂) G = advectionLp k F₁ G + advectionLp k F₂ G := by
  refine Lp.ext_iff.2 ((advectionLp_coe k _ _).trans ?_)
  rw [bilin_adv_congr ((bilin_volume_ac _).ae_le (Lp.coeFn_add F₁ F₂)) EventuallyEq.rfl]
  filter_upwards [(bilin_weighted_ac k).ae_le
      (bilin_adv_add_left (Lp.memLp F₁) (Lp.memLp F₂) (Lp.memLp G)),
    Lp.coeFn_add (advectionLp k F₁ G) (advectionLp k F₂ G), advectionLp_coe k F₁ G,
    advectionLp_coe k F₂ G] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄]

private theorem advectionLp_add_right (k : ℕ) (F G₁ G₂ : Lp CSpace 1 (weightedVolume (k + 1))) :
    advectionLp k F (G₁ + G₂) = advectionLp k F G₁ + advectionLp k F G₂ := by
  refine Lp.ext_iff.2 ((advectionLp_coe k _ _).trans ?_)
  rw [bilin_adv_congr EventuallyEq.rfl ((bilin_volume_ac _).ae_le (Lp.coeFn_add G₁ G₂))]
  filter_upwards [(bilin_weighted_ac k).ae_le
      (bilin_adv_add_right (Lp.memLp F) (Lp.memLp G₁) (Lp.memLp G₂)),
    Lp.coeFn_add (advectionLp k F G₁) (advectionLp k F G₂), advectionLp_coe k F G₁,
    advectionLp_coe k F G₂] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄]

private theorem advectionLp_smul_left (k : ℕ) (c : ℝ) (F G : Lp CSpace 1 (weightedVolume (k + 1))) :
    advectionLp k (c • F) G = c • advectionLp k F G := by
  refine Lp.ext_iff.2 ((advectionLp_coe k _ _).trans ?_)
  rw [bilin_adv_congr ((bilin_volume_ac _).ae_le (Lp.coeFn_smul c F)) EventuallyEq.rfl,
    bilin_adv_smul_left]
  filter_upwards [Lp.coeFn_smul c (advectionLp k F G), advectionLp_coe k F G] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply, Pi.smul_apply, h₂]

private theorem advectionLp_smul_right (k : ℕ) (c : ℝ) (F G : Lp CSpace 1 (weightedVolume (k + 1))) :
    advectionLp k F (c • G) = c • advectionLp k F G := by
  refine Lp.ext_iff.2 ((advectionLp_coe k _ _).trans ?_)
  rw [bilin_adv_congr EventuallyEq.rfl ((bilin_volume_ac _).ae_le (Lp.coeFn_smul c G)),
    bilin_adv_smul_right]
  filter_upwards [Lp.coeFn_smul c (advectionLp k F G), advectionLp_coe k F G] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply, Pi.smul_apply, h₂]

private theorem advectionLp_norm_le (k : ℕ) (F G : Lp CSpace 1 (weightedVolume (k + 1))) :
    ‖advectionLp k F G‖ ≤ 18 * π * ‖F‖ * ‖G‖ := by
  have hF := (Lp.aestronglyMeasurable F).mono_ac (bilin_volume_ac (k + 1))
  have hG := (Lp.aestronglyMeasurable G).mono_ac (bilin_volume_ac (k + 1))
  have h : ENNReal.ofReal ‖advectionLp k F G‖ ≤ ENNReal.ofReal (18 * π * ‖F‖ * ‖G‖) := by
    rw [bilin_ofReal_norm]
    have he : ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖(advectionLp k F G : Space → CSpace) ξ‖ₑ =
        ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖advectionBilin F G ξ‖ₑ :=
      lintegral_congr_ae (Filter.Eventually.mono ((bilin_volume_ac k).ae_le (advectionLp_coe k F G))
        fun ξ hξ => by simp only [hξ])
    rw [he]
    refine (bilin_lintegral_adv_le k hF hG).trans (le_of_eq ?_)
    rw [← bilin_ofReal_norm, ← bilin_ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

theorem exists_bilin_advection (k : ℕ) :
    ∃ B : Lp CSpace 1 (weightedVolume (k + 1)) →L[ℝ] Lp CSpace 1 (weightedVolume (k + 1)) →L[ℝ]
        Lp CSpace 1 (weightedVolume k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightedVolume (k + 1)))
        (hg : MemLp g 1 (weightedVolume (k + 1))),
        ∃ h : MemLp (advectionBilin f g) 1 (weightedVolume k),
          B (hf.toLp f) (hg.toLp g) = h.toLp _ := by
  refine ⟨(LinearMap.mk₂ ℝ (advectionLp k) (advectionLp_add_left k) (advectionLp_smul_left k)
    (advectionLp_add_right k) (advectionLp_smul_right k)).mkContinuous₂ (18 * π)
      (fun F G => by rw [LinearMap.mk₂_apply]; exact advectionLp_norm_le k F G), fun f g hf hg => ⟨bilin_memLp k hf hg, ?_⟩⟩
  rw [LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => congrFun (bilin_adv_congr
    ((bilin_volume_ac _).ae_le (MemLp.coeFn_toLp hf))
    ((bilin_volume_ac _).ae_le (MemLp.coeFn_toLp hg))) ξ)

end Breakdown.SmoothFlow
