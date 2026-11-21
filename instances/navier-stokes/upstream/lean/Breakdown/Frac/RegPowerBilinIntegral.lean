import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegIdentifyAuxSwap
import Breakdown.Uniqueness.RegIdentifyAuxTime
import Breakdown.Uniqueness.RegEmbed
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem integral_fracPhiFactor_smul (α t : ℝ) (ξ : Space) (v : ℝ → CSpace) :
    ∫ s in (0 : ℝ)..t, ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) •
        ∫ s in (0 : ℝ)..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • v s := by
  have hfac : ∀ s, ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • (((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • v s) := by
    intro s
    rw [smul_smul]
    congr 1
    simp only [fracPhiFactor, powerHeatSymbol]
    push_cast
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_smul]

private theorem continuous_fracPhiFactor_joint (α t : ℝ) (hα : 1 < α) :
    Continuous fun p : ℝ × Space => ((fracPhiFactor α (t - p.1) p.2 : ℝ) : ℂ) := by
  have hpow : Continuous fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α) :=
    (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by linarith))
  unfold fracPhiFactor
  exact Complex.continuous_ofReal.comp
    ((continuous_const.mul (continuous_norm.comp continuous_snd)).mul
      (Real.continuous_exp.comp
        (((continuous_const.sub continuous_fst).mul (hpow.comp continuous_snd)).neg)))

theorem powerBilinIntegral_of (α : ℝ) (hα : 1 < α) (h1 : PowerBilinPhysStatement α)
    (h2 : PowerBilinContinuousStatement α) (h3 : PowerHeatXStatement α) :
    PowerBilinIntegralStatement α := by
  intro T hT F hF hd hs t ht
  obtain ⟨hcontAll, C, hC⟩ := h2 T hT F hF hs
  have hm : ∀ s ∈ Icc 0 T, AEStronglyMeasurable (F s) volume := fun s hs' => ((hF 0).1 s hs').1
  have hfin : ∀ s ∈ Icc 0 T, ∀ m, hsNormSq m (F s) < ⊤ := fun s hs' m => ((hF m).1 s hs').2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hII : IntervalIntegrable
      (fun s => fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))))
      volume 0 t := by
    have hcont := hcontAll t ht
    have hpow : IntervalIntegrable (fun s => C * (t - s) ^ (-(1 / (2 * α)))) volume 0 t := by
      have hr : -1 < -(1 / (2 * α)) := by
        have hpos : 0 < 2 * α := by linarith
        have : 1 / (2 * α) < 1 := by rw [div_lt_one hpos]; linarith
        linarith
      have h1' := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
        (r := -(1 / (2 * α))) hr).comp_sub_left t
      simp only [sub_self, sub_zero] at h1'
      exact h1'.const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1] at hpow ⊢
    refine Integrable.mono' hpow
      ((hcont.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs' => ?_)
    exact hC s ⟨hs'.1.le, hs'.2.le.trans ht.2⟩ (t - s) (sub_pos.2 hs'.2)
  refine ⟨hII, ?_⟩
  have hphi := continuous_fracPhiFactor_joint α t hα
  apply coe_intervalIntegral_ae ht.1
  · intro s hs'
    have hsT := hsub (Ioo_subset_Icc_self hs')
    exact h1 (F s) (hm s hsT) (hs s hsT) (hfin s hsT) (t - s) (sub_pos.2 hs'.2)
  · exact hII
  · have hN := aestronglyMeasurable_uncurry_nonlinSymbol hF hs
    have e1 : (volume.restrict (Ioc 0 t)).prod (volume : Measure Space) =
        ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 t ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have e2 : (volume.restrict (Icc 0 T)).prod (volume : Measure Space) =
        ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Icc 0 T ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e2] at hN
    rw [e1]
    have hN' := hN.mono_set (prod_mono (Ioc_subset_Icc_self.trans hsub) subset_rfl)
    exact hphi.aestronglyMeasurable.smul hN'
  · intro ξ
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    have hc1 : Continuous fun s : ℝ => ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) := by
      unfold fracPhiFactor
      exact Complex.continuous_ofReal.comp (continuous_const.mul
        (Real.continuous_exp.comp ((continuous_const.sub continuous_id).mul continuous_const).neg))
    exact hc1.continuousOn.smul ((continuousOn_nonlinSymbol_apply hF hs ξ).mono hsub)
  · have e0 := coe_embedX_physField fieldOpRealized_holds (hm 0 h0) (hs 0 h0) (hfin 0 h0)
    have et := coe_embedX_physField fieldOpRealized_holds (hm t ht) (hs t ht) (hfin t ht)
    have eh := h3 t (embedX (physField (F 0)))
    have esub := Lp.coeFn_sub ((embedX (physField (F t)) : X) : L2C)
      ((fracHeatX α t (embedX (physField (F 0))) : X) : L2C)
    refine (Lp.memLp (((embedX (physField (F t)) : X) : L2C) -
      ((fracHeatX α t (embedX (physField (F 0))) : X) : L2C))).ae_eq ?_
    filter_upwards [e0, et, eh, esub] with ξ h0' ht' hh' hs'
    rw [hs', Pi.sub_apply, ht', hh', h0', integral_fracPhiFactor_smul]
    have hheat : fracHeatFactor α t ξ = powerHeatSymbol α (t - 0) ξ := by
      simp only [fracHeatFactor, powerHeatSymbol, sub_zero, max_eq_left ht.1]
    rw [hheat, smul_comm ((powerHeatSymbol α (t - 0) ξ : ℝ) : ℂ) (((2 * π * ‖ξ‖ : ℝ)) : ℂ),
      ← smul_sub, hd t ht ξ, add_sub_cancel_left]

end Breakdown.SmoothFlow
