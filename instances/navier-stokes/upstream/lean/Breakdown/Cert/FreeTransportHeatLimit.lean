import Breakdown.Cert.Basic
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.PropagatorTrace

open Breakdown.Freq.Internal.Heat Breakdown.Freq.Internal.Dilation Breakdown.Freq.Internal.Phi

def rescaledHeat (r : ℝ) (x : Freq.X) : Freq.X :=
  (Real.sqrt (Real.exp (-r)))⁻¹ • dilX (Real.exp (-r)) (heatX (1 - Real.exp (-r)) x)

theorem smoothH_coe {t : ℝ} (ht : 0 < t) (x : Freq.X) :
    (smoothH t x : L2C) = fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) x :=
  restrictX_coe (fun _ hx => scalarOp_mem fieldOpRealized_holds (continuous_phiFactor t) (phiFactor_le ht)
    (fun ξ => by simp only [phiFactor, norm_neg]) hx) x

theorem isHalfSspOf_smoothH {t : ℝ} (ht : 0 < t) (x : Freq.X) :
    IsHalfSspOf (heatX t x) (smoothH t x) := by
  unfold IsHalfSspOf
  rw [smoothH_coe ht, heat_holds.2.2.2.2.2 t x]
  filter_upwards [scalarOp_ae fieldOpRealized_holds (continuous_phiFactor t) (phiFactor_le ht) (x : L2C),
    heat_ae fieldOpRealized_holds t (x : L2C)] with ξ e1 e2
  rw [e1, e2, smul_smul]
  congr 1
  rw [phiFactor, heatFactor, max_eq_left ht.le]

theorem isHalfSspOf_dilX {g h : Freq.X} (hgh : IsHalfSspOf g h) {μ : ℝ} (hμ : 0 < μ) :
    IsHalfSspOf ((Real.sqrt μ)⁻¹ • dilX μ g) (dilX μ h) := by
  have hc0 : 0 < (Real.sqrt μ)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hμ)
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc0.ne'
  have e : ((h : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => (2 * Real.pi * ‖ξ‖) • ((g : L2C) : Space → CSpace) ξ :=
    hgh
  have hcomp := hq.ae_eq_comp e
  unfold IsHalfSspOf
  rw [Submodule.coe_smul, dilation_holds.2.2.2.2 μ hμ g, dilation_holds.2.2.2.2 μ hμ h]
  filter_upwards [Lp.coeFn_smul ((Real.sqrt μ)⁻¹) (dilL2 μ (g : L2C)), dilL2_ae fieldOpRealized_holds hμ (g : L2C),
    dilL2_ae fieldOpRealized_holds hμ (h : L2C), hcomp] with ξ a b c d
  simp only [Function.comp_apply] at d
  rw [c, d, a, Pi.smul_apply, b]
  simp only [smul_smul]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
  ring

theorem velocity_slicePropagator_ae {r : ℝ} (hr : 0 < r) (x : Freq.X) :
    (velocity (slicePropagator r x) : Space → Space) =ᵐ[volume]
      (toPhysH (rescaledHeat r x) : Space → Space) := by
  have ht : 0 < 1 - Real.exp (-r) := sub_pos.2 (by
    have h := Real.exp_lt_exp.2 (neg_lt_zero.2 hr)
    rwa [Real.exp_zero] at h)
  have e1 : slicePropagator r x = dilX (Real.exp (-r)) (smoothH (1 - Real.exp (-r)) x) := rfl
  have e2 : toPhysH (rescaledHeat r x) = toPhys (rescaledHeat r x : L2C) := rfl
  rw [e1, e2]
  exact velocityInverts_holds _ _ (isHalfSspOf_dilX (isHalfSspOf_smoothH ht x) (Real.exp_pos (-r)))

theorem tendsto_exp_neg : Tendsto (fun r : ℝ => Real.exp (-r)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => Real.exp (-r)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
    (Real.continuous_exp.comp continuous_neg).tendsto 0
  rw [neg_zero, Real.exp_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_heat_trace (x : Freq.X) :
    Tendsto (fun r : ℝ => heatX (1 - Real.exp (-r)) x) (𝓝[>] 0) (𝓝 x) := by
  have ht : Tendsto (fun r : ℝ => 1 - Real.exp (-r)) (𝓝[>] 0) (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr => ?_⟩
    · have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_exp_neg
      rw [sub_self] at h
      exact h
    · exact Set.mem_Ici.2 (sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (le_of_lt hr))))
  have h := ((heat_holds.2.2.2.1 x) 0 (Set.mem_Ici.2 le_rfl)).tendsto.comp ht
  rw [heat_holds.1, ContinuousLinearMap.id_apply] at h
  exact h

theorem tendsto_rescaledHeat (x : Freq.X) :
    Tendsto (fun r => rescaledHeat r x) (𝓝[>] 0) (𝓝 x) := by
  have hμ' : Tendsto (fun r : ℝ => Real.exp (-r)) (𝓝[>] 0) (𝓝[Set.Ioi 0] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_exp_neg, Eventually.of_forall fun r => Real.exp_pos _⟩
  have hdil1 : Tendsto (fun r : ℝ => dilX (Real.exp (-r)) x) (𝓝[>] 0) (𝓝 x) := by
    have h := ((dilationCont_holds x) 1 (Set.mem_Ioi.2 one_pos)).tendsto.comp hμ'
    rw [dilation_holds.2.1, ContinuousLinearMap.id_apply] at h
    exact h
  have hdil2 : Tendsto (fun r : ℝ => dilX (Real.exp (-r)) (heatX (1 - Real.exp (-r)) x - x))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm (fun r => (dilation_holds.1 _ (Real.exp_pos _) _).le) ?_
    have h := (tendsto_exp_neg.rpow_const (p := 1 / 4) (Or.inr (by norm_num))).mul
      (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_heat_trace x))
    rw [mul_zero] at h
    exact h
  have hdil : Tendsto (fun r : ℝ => dilX (Real.exp (-r)) (heatX (1 - Real.exp (-r)) x)) (𝓝[>] 0) (𝓝 x) := by
    have h := hdil2.add hdil1
    rw [zero_add] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    show dilX (Real.exp (-r)) (heatX (1 - Real.exp (-r)) x - x) + dilX (Real.exp (-r)) x =
      dilX (Real.exp (-r)) (heatX (1 - Real.exp (-r)) x)
    rw [map_sub, sub_add_cancel]
  have hc : Tendsto (fun r : ℝ => (Real.sqrt (Real.exp (-r)))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have h := (tendsto_exp_neg.sqrt).inv₀ (by rw [Real.sqrt_one]; exact one_ne_zero)
    rw [Real.sqrt_one, inv_one] at h
    exact h
  have h := hc.smul hdil
  rw [one_smul] at h
  exact h

theorem pairing_bound {χ : ℝ → Space → Space} (hχc : Continuous (fun z : ℝ × Space => χ z.1 z.2))
    (R M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ r y, ‖χ r y‖ ≤ M)
    (hzero : ∀ r y, y ∉ Metric.closedBall (0 : Space) R → χ r y = 0) (F : L2R) :
    Integrable (fun y => M * ‖(Metric.closedBall (0 : Space) R).indicator (F : Space → Space) y‖) ∧
    (∀ r y, ‖inner ℝ ((F : Space → Space) y) (χ r y)‖ ≤
      M * ‖(Metric.closedBall (0 : Space) R).indicator (F : Space → Space) y‖) ∧
    ∀ r, Integrable (fun y => inner ℝ ((F : Space → Space) y) (χ r y)) ∧
      |∫ y, inner ℝ ((F : Space → Space) y) (χ r y)| ≤
        M * (volume (Metric.closedBall (0 : Space) R) ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal * ‖F‖ := by
  have hB : MeasurableSet (Metric.closedBall (0 : Space) R) := Metric.isClosed_closedBall.measurableSet
  have hVt : volume (Metric.closedBall (0 : Space) R) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  have hwm : AEStronglyMeasurable (F : Space → Space) volume := Lp.aestronglyMeasurable _
  have hpt : ∀ r y, ‖inner ℝ ((F : Space → Space) y) (χ r y)‖ ≤
      M * ‖(Metric.closedBall (0 : Space) R).indicator (F : Space → Space) y‖ := fun r y => by
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      calc ‖inner ℝ ((F : Space → Space) y) (χ r y)‖
          ≤ ‖(F : Space → Space) y‖ * ‖χ r y‖ := norm_inner_le_norm _ _
        _ ≤ ‖(F : Space → Space) y‖ * M := by
          gcongr
          exact hM r y
        _ = M * ‖(F : Space → Space) y‖ := mul_comm _ _
    · rw [hzero r y hy, inner_zero_right, Set.indicator_of_notMem hy, norm_zero, norm_zero, mul_zero]
  have hL1 : eLpNorm ((Metric.closedBall (0 : Space) R).indicator (F : Space → Space)) 1 volume ≤
      volume (Metric.closedBall (0 : Space) R) ^
        (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) * ‖F‖ₑ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hB]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hwm.restrict).trans ?_
    rw [Measure.restrict_apply_univ, mul_comm (volume (Metric.closedBall (0 : Space) R) ^ _)]
    have h4 : eLpNorm (F : Space → Space) 2 (volume.restrict (Metric.closedBall (0 : Space) R)) ≤ ‖F‖ₑ :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (Lp.enorm_def F).symm.le
    gcongr
  have hfin : volume (Metric.closedBall (0 : Space) R) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) * ‖F‖ₑ < ⊤ :=
    ENNReal.mul_lt_top hVt enorm_lt_top
  have hI1 : Integrable ((Metric.closedBall (0 : Space) R).indicator (F : Space → Space)) :=
    memLp_one_iff_integrable.1 ⟨hwm.indicator hB, hL1.trans_lt hfin⟩
  have hg := hI1.norm.const_mul M
  refine ⟨hg, hpt, fun r => ?_⟩
  have hmeas : AEStronglyMeasurable (fun y => inner ℝ ((F : Space → Space) y) (χ r y)) volume :=
    hwm.inner (hχc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hg.mono' hmeas (ae_of_all _ (hpt r)), ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ (hpt r))).trans ?_
  rw [integral_const_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  rw [integral_norm_eq_lintegral_enorm hI1.1, ← eLpNorm_one_eq_lintegral_enorm]
  calc (eLpNorm ((Metric.closedBall (0 : Space) R).indicator (F : Space → Space)) 1 volume).toReal
      ≤ (volume (Metric.closedBall (0 : Space) R) ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) * ‖F‖ₑ).toReal :=
        ENNReal.toReal_mono hfin.ne hL1
    _ = (volume (Metric.closedBall (0 : Space) R) ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal * ‖F‖ := by
        rw [ENNReal.toReal_mul, toReal_enorm]

theorem tendsto_pairing_of_bound {χ : ℝ → Space → Space}
    (hχc : Continuous (fun z : ℝ × Space => χ z.1 z.2))
    (R M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ r y, ‖χ r y‖ ≤ M)
    (hzero : ∀ r y, y ∉ Metric.closedBall (0 : Space) R → χ r y = 0)
    {F : ℝ → L2R} {F0 : L2R} {l : Filter ℝ} (hF : Tendsto F l (𝓝 F0)) (hl : l ≤ 𝓝 0) :
    Tendsto (fun r => ∫ y, inner ℝ ((F r : Space → Space) y) (χ r y)) l
      (𝓝 (∫ y, inner ℝ ((F0 : Space → Space) y) (χ 0 y))) := by
  have hb := pairing_bound hχc R M hM0 hM hzero
  have hcr : Continuous (fun r => ∫ y, inner ℝ ((F0 : Space → Space) y) (χ r y)) :=
    continuous_of_dominated (fun r => ((hb F0).2.2 r).1.1) (fun r => ae_of_all _ ((hb F0).2.1 r))
      (hb F0).1 (ae_of_all _ fun y => continuous_const.inner (hχc.comp (continuous_id.prodMk continuous_const)))
  have h2 := (hcr.tendsto 0).mono_left hl
  have hn : Tendsto (fun r => M * (volume (Metric.closedBall (0 : Space) R) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal * ‖F r - F0‖) l (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.1 hF).const_mul (M * (volume (Metric.closedBall (0 : Space) R) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal)
    rw [mul_zero] at h
    exact h
  have h1 : Tendsto (fun r => ∫ y, inner ℝ (((F r - F0 : L2R) : Space → Space) y) (χ r y)) l (𝓝 0) :=
    squeeze_zero_norm (fun r => (Real.norm_eq_abs _).le.trans ((hb (F r - F0)).2.2 r).2) hn
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr' (Eventually.of_forall fun r => ?_)
  show (∫ y, inner ℝ (((F r - F0 : L2R) : Space → Space) y) (χ r y)) +
      ∫ y, inner ℝ ((F0 : Space → Space) y) (χ r y) = ∫ y, inner ℝ ((F r : Space → Space) y) (χ r y)
  rw [← integral_add ((hb (F r - F0)).2.2 r).1 ((hb F0).2.2 r).1]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (F r) F0] with y hy
  rw [hy, Pi.sub_apply, ← inner_add_left, sub_add_cancel]

theorem tendsto_propagator_pairing_of_bound (x : HBar) {χ : ℝ → Space → Space}
    (hχc : Continuous (fun z : ℝ × Space => χ z.1 z.2))
    (R M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ r y, ‖χ r y‖ ≤ M)
    (hzero : ∀ r y, y ∉ Metric.closedBall (0 : Space) R → χ r y = 0) :
    Tendsto (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y))
      (𝓝[>] 0) (𝓝 (∫ y, inner ℝ ((toPhysH x : Space → Space) y) (χ 0 y))) := by
  have h := tendsto_pairing_of_bound hχc R M hM0 hM hzero
    ((toPhysH.continuous.tendsto x).comp (tendsto_rescaledHeat x)) nhdsWithin_le_nhds
  refine h.congr' (eventually_nhdsWithin_of_forall fun r hr => ?_)
  show (∫ y, inner ℝ ((toPhysH (rescaledHeat r x) : Space → Space) y) (χ r y)) =
    ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y)
  refine integral_congr_ae ?_
  filter_upwards [velocity_slicePropagator_ae hr x] with y hy
  rw [hy]

end Internal.PropagatorTrace

theorem tendsto_propagator_pairing (x : HBar) {χ : ℝ → Space → Space}
    (hχc : Continuous (fun z : ℝ × Space => χ z.1 z.2))
    (hχs : HasCompactSupport (fun z : ℝ × Space => χ z.1 z.2)) :
    Tendsto (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y))
      (𝓝[>] 0) (𝓝 (∫ y, inner ℝ ((toPhysH x : Space → Space) y) (χ 0 y))) :=
  Exists.elim (hχs.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)) fun R hR =>
    Exists.elim (hχc.bounded_above_of_compact_support hχs) fun M hM =>
      Internal.PropagatorTrace.tendsto_propagator_pairing_of_bound x hχc R M
        ((norm_nonneg _).trans (hM (0, 0))) (fun r y => hM (r, y))
        (fun r y hy => image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => χ z.1 z.2)
          (x := (r, y)) fun ht => hy (by
            have h1 := hR ht
            rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
            exact (norm_snd_le _).trans h1))

end Breakdown.Cert
