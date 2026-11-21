import Breakdown.Uniqueness.RegAprioriAuxMildPart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def l2e (u : Space → ℂ) : ℝ≥0∞ := (∫⁻ η, ‖u η‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

private theorem aesm_shift {v : Space → ℂ} (hv : AEStronglyMeasurable v volume) (ξ : Space) :
    AEStronglyMeasurable (fun η => v (ξ - η)) volume :=
  hv.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ)

private theorem lintegral_prod_shift_le {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (ξ : Space) :
    ∫⁻ η, ‖u η‖ₑ * ‖v (ξ - η)‖ₑ ≤ l2e u * l2e v := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hu.enorm (aesm_shift hv ξ).enorm
  have e : ∫⁻ η, ‖v (ξ - η)‖ₑ ^ (2 : ℝ) = ∫⁻ η, ‖v η‖ₑ ^ (2 : ℝ) :=
    lintegral_sub_left_eq_self (fun η => ‖v η‖ₑ ^ (2 : ℝ)) ξ
  simp only [Pi.mul_apply] at h
  rw [e] at h
  simpa [l2e] using h

private theorem enorm_convC_le {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (ξ : Space) :
    ‖convC u v ξ‖ₑ ≤ l2e u * l2e v := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp only [enorm_mul]
  exact lintegral_prod_shift_le hu hv ξ

private theorem integrable_prod_shift {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hu2 : l2e u < ⊤) (hv2 : l2e v < ⊤) (ξ : Space) :
    Integrable (fun η => u η * v (ξ - η)) volume := by
  refine ⟨hu.mul (aesm_shift hv ξ), ?_⟩
  simp only [HasFiniteIntegral, enorm_mul]
  exact (lintegral_prod_shift_le hu hv ξ).trans_lt (ENNReal.mul_lt_top hu2 hv2)

private theorem convC_sub_eq {u v u' v' : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hu' : AEStronglyMeasurable u' volume)
    (hv' : AEStronglyMeasurable v' volume) (h1 : l2e (u - u') < ⊤) (h2 : l2e (v - v') < ⊤)
    (h3 : l2e u' < ⊤) (h4 : l2e v' < ⊤) (ξ : Space) :
    convC u v ξ - convC u' v' ξ = convC (u - u') (v - v') ξ + convC (u - u') v' ξ +
      convC u' (v - v') ξ := by
  have ha := integrable_prod_shift (hu.sub hu') (hv.sub hv') h1 h2 ξ
  have hb := integrable_prod_shift (hu.sub hu') hv' h1 h4 ξ
  have hc := integrable_prod_shift hu' (hv.sub hv') h3 h2 ξ
  have hd := integrable_prod_shift hu' hv' h3 h4 ξ
  have e : (fun η => u η * v (ξ - η)) = fun η => (u - u') η * (v - v') (ξ - η) +
      (u - u') η * v' (ξ - η) + u' η * (v - v') (ξ - η) + u' η * v' (ξ - η) := by
    funext η
    simp only [Pi.sub_apply]
    ring
  unfold convC
  have k1 := integral_add ((ha.add hb).add hc) hd
  have k2 := integral_add (ha.add hb) hc
  have k3 := integral_add ha hb
  simp only [Pi.add_apply] at k1 k2 k3
  rw [e, k1, k2, k3]
  ring

private theorem l2e_comp_le (m : ℕ) (h : Space → CSpace) (j : Fin 3) :
    l2e (fun η => h η j) ≤ hsNormSq m h ^ (1 / 2 : ℝ) := by
  unfold l2e hsNormSq
  refine ENNReal.rpow_le_rpow (lintegral_mono fun η => ?_) (by norm_num)
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hsWeight m η) := by
    rw [ENNReal.one_le_ofReal]
    unfold hsWeight
    exact one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  rw [ENNReal.rpow_two]
  calc ‖h η j‖ₑ ^ 2 ≤ ‖h η‖ₑ ^ 2 := by gcongr; exact PiLp.enorm_apply_le _ _
    _ = 1 * ‖h η‖ₑ ^ 2 := (one_mul _).symm
    _ ≤ _ := by gcongr

private theorem aesm_comp {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) (j : Fin 3) :
    AEStronglyMeasurable (fun η => f η j) volume :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hf

private theorem measurable_convC {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) : Measurable (fun ξ => convC u v ξ) := by
  have e : (fun ξ => convC u v ξ) = fun ξ => ∫ η, hu.mk u η * hv.mk v (ξ - η) := by
    funext ξ
    unfold convC
    refine integral_congr_ae ?_
    have h2 := (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae_eq_comp hv.ae_eq_mk
    filter_upwards [hu.ae_eq_mk, h2] with η h1 h3
    simp only [Function.comp_apply] at h3
    rw [h1, h3]
  rw [e]
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right (f := fun ξ η => hu.mk u η * hv.mk v (ξ - η)) ?_
  exact (hu.stronglyMeasurable_mk.comp_measurable measurable_snd).mul
    (hv.stronglyMeasurable_mk.comp_measurable (measurable_fst.sub measurable_snd))

private theorem continuousOn_convC_curve {m : ℕ} {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) (i j : Fin 3) (ξ : Space) :
    ContinuousOn (fun s => convC (fun η => F s η j) (fun η => F s η i) ξ) (Icc 0 T) := by
  intro s₀ hs₀
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  have hd := hF.2 s₀ hs₀
  have hD : Tendsto (fun s => hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ)) (𝓝[Icc 0 T] s₀) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp hd
  have hfin : hsNormSq m (F s₀) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hF.1 s₀ hs₀).2.ne
  have hN : ∀ k, l2e (fun η => F s₀ η k) < ⊤ := fun k => (l2e_comp_le m _ k).trans_lt hfin
  set N := hsNormSq m (F s₀) ^ (1 / 2 : ℝ)
  have hB : Tendsto (fun s => hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ) *
      hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ) + hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ) * N +
      N * hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ)) (𝓝[Icc 0 T] s₀) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul hD (Or.inr ENNReal.zero_ne_top) hD (Or.inr ENNReal.zero_ne_top)
    have h2 := ENNReal.Tendsto.mul_const hD (Or.inr hfin.ne)
    have h3 := ENNReal.Tendsto.const_mul hD (Or.inr hfin.ne)
    simpa using (h1.add h2).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun _ => zero_le) ?_
  have hlt := hd.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))
  filter_upwards [hlt, self_mem_nhdsWithin] with s hs1 hs
  have hDf : hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hs1.trans ENNReal.one_lt_top).ne
  have esub : ∀ k, ((fun η => F s η k) - fun η => F s₀ η k) = fun η => (F s - F s₀) η k := by
    intro k
    funext η
    simp
  have hsub : ∀ k, l2e ((fun η => F s η k) - fun η => F s₀ η k) ≤
      hsNormSq m (F s - F s₀) ^ (1 / 2 : ℝ) := by
    intro k
    rw [esub k]
    exact l2e_comp_le m _ k
  have hm := (hF.1 s hs).1
  have hm₀ := (hF.1 s₀ hs₀).1
  rw [edist_eq_enorm_sub, convC_sub_eq (aesm_comp hm j) (aesm_comp hm i) (aesm_comp hm₀ j)
    (aesm_comp hm₀ i) ((hsub j).trans_lt hDf) ((hsub i).trans_lt hDf) (hN j) (hN i) ξ]
  refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · refine (enorm_convC_le ((aesm_comp hm j).sub (aesm_comp hm₀ j))
      ((aesm_comp hm i).sub (aesm_comp hm₀ i)) ξ).trans ?_
    exact mul_le_mul' (hsub j) (hsub i)
  · refine (enorm_convC_le ((aesm_comp hm j).sub (aesm_comp hm₀ j)) (aesm_comp hm₀ i) ξ).trans ?_
    exact mul_le_mul' (hsub j) (l2e_comp_le m _ i)
  · refine (enorm_convC_le (aesm_comp hm₀ j) ((aesm_comp hm i).sub (aesm_comp hm₀ i)) ξ).trans ?_
    exact mul_le_mul' (l2e_comp_le m _ j) (hsub i)

theorem aemeasurable_convEnormSum_curve {m : ℕ} (hm : 3 ≤ m) {T t : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) (ht : t ∈ Icc 0 T) :
    AEMeasurable (fun p : ℝ × Space => convEnormSum (F p.1) p.2)
      ((volume.restrict (Ioo 0 t)).prod volume) := by
  have hsub : ∀ s, ((projIcc 0 t ht.1 s : ℝ)) ∈ Icc 0 T := fun s =>
    ⟨(projIcc 0 t ht.1 s).2.1, (projIcc 0 t ht.1 s).2.2.trans ht.2⟩
  have hu : ∀ i j : Fin 3, Measurable (Function.uncurry fun s ξ =>
      convC (fun η => F (projIcc 0 t ht.1 s : ℝ) η j)
        (fun η => F (projIcc 0 t ht.1 s : ℝ) η i) ξ) := by
    intro i j
    refine measurable_uncurry_of_continuous_of_measurable (fun ξ => ?_) (fun s => ?_)
    · exact (continuousOn_convC_curve hF i j ξ).comp_continuous
        (continuous_subtype_val.comp continuous_projIcc) hsub
    · exact measurable_convC (aesm_comp (hF.1 _ (hsub s)).1 j) (aesm_comp (hF.1 _ (hsub s)).1 i)
  have hG : Measurable (fun p : ℝ × Space => ∑ i, ∑ j,
      ‖convC (fun η => F (projIcc 0 t ht.1 p.1 : ℝ) η j)
        (fun η => F (projIcc 0 t ht.1 p.1 : ℝ) η i) p.2‖ₑ) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (hu i j).enorm
  refine hG.aemeasurable.congr ?_
  have hS : MeasurableSet {p : ℝ × Space | p.1 ∈ Ioo 0 t} := measurable_fst measurableSet_Ioo
  have hae : ∀ᵐ p ∂((volume.restrict (Ioo 0 t)).prod (volume : Measure Space)), p.1 ∈ Ioo 0 t := by
    rw [Measure.ae_prod_iff_ae_ae hS]
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with s hs
    exact Eventually.of_forall fun _ => hs
  filter_upwards [hae] with p hp
  have e : ((projIcc 0 t ht.1 p.1 : ℝ)) = p.1 := by
    rw [projIcc_of_mem ht.1 ⟨hp.1.le, hp.2.le⟩]
  simp only [convEnormSum, e]

end Breakdown.SmoothFlow
