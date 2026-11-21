import Breakdown.Uniqueness.RegIdentifyAuxHeat
import Breakdown.Uniqueness.RegIdentifyAuxCont
import Breakdown.Uniqueness.RegIdentifyAuxBilin
import Breakdown.Uniqueness.RegIdentifyAuxSwap
import Breakdown.Uniqueness.RegIdentifyAuxTime
import Breakdown.Uniqueness.RegIdentifyAuxVecIntegral

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem integral_phiFactor_smul (t : ℝ) (ξ : Space) (v : ℝ → CSpace) :
    ∫ s in (0 : ℝ)..t, ((phiFactor (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • ∫ s in (0 : ℝ)..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • v s := by
  have hfac : ∀ s, ((phiFactor (t - s) ξ : ℝ) : ℂ) • v s =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • (((heatSymbol (t - s) ξ : ℝ) : ℂ) • v s) := by
    intro s
    rw [smul_smul]
    congr 1
    simp only [phiFactor, heatSymbol]
    push_cast
    ring
  simp_rw [hfac]
  rw [intervalIntegral.integral_smul]

theorem intervalIntegrable_bilinX_physField (hR : FieldOpRealized) (hB : BilinH1Formula)
    {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable
      (fun s => bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) volume 0 t := by
  obtain ⟨C, hC⟩ := norm_bilinX_physField_le hR hB hT hF hs
  have hcont := continuousOn_bilinX_physField hR hB hT hF hs ht
  have hpow : IntervalIntegrable (fun s => C * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
    have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t
    simp only [sub_self, sub_zero] at h1
    exact h1.const_mul C
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1] at hpow ⊢
  refine Integrable.mono' hpow
    ((hcont.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs' => ?_)
  exact hC s ⟨hs'.1.le, hs'.2.le.trans ht.2⟩ (t - s) (sub_pos.2 hs'.2)

theorem coe_integral_bilinX_physField (hH : HeatSemigroup) (hR : FieldOpRealized)
    (hB : BilinH1Formula) {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hd : IsVarConstSymbol F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (((∫ s in (0 : ℝ)..t,
        bilinX (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) : X) :
          Space → CSpace) =ᵐ[volume]
      fun ξ => ∫ s in (0 : ℝ)..t, ((phiFactor (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
  have hm : ∀ s ∈ Icc 0 T, AEStronglyMeasurable (F s) volume := fun s hs' => ((hF 0).1 s hs').1
  have hfin : ∀ s ∈ Icc 0 T, ∀ m, hsNormSq m (F s) < ⊤ := fun s hs' m => ((hF m).1 s hs').2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hphi : Continuous fun p : ℝ × Space => ((phiFactor (t - p.1) p.2 : ℝ) : ℂ) := by
    unfold phiFactor
    fun_prop
  apply coe_intervalIntegral_ae ht.1
  · intro s hs'
    have hsT := hsub (Ioo_subset_Icc_self hs')
    exact coe_bilinX_physField hR hB (hm s hsT) (hs s hsT) (hfin s hsT) (sub_pos.2 hs'.2)
  · exact intervalIntegrable_bilinX_physField hR hB hT hF hs ht
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
    have h1 : Continuous fun s : ℝ => ((phiFactor (t - s) ξ : ℝ) : ℂ) := by
      unfold phiFactor
      fun_prop
    exact h1.continuousOn.smul ((continuousOn_nonlinSymbol_apply hF hs ξ).mono hsub)
  · have e0 := coe_embedX_physField hR (hm 0 h0) (hs 0 h0) (hfin 0 h0)
    have et := coe_embedX_physField hR (hm t ht) (hs t ht) (hfin t ht)
    have eh := coe_heatX_ae hH hR t (embedX (physField (F 0)))
    have esub := Lp.coeFn_sub ((embedX (physField (F t)) : X) : L2C)
      ((heatX t (embedX (physField (F 0))) : X) : L2C)
    refine (Lp.memLp (((embedX (physField (F t)) : X) : L2C) -
      ((heatX t (embedX (physField (F 0))) : X) : L2C))).ae_eq ?_
    filter_upwards [e0, et, eh, esub] with ξ h0' ht' hh' hs'
    rw [hs', Pi.sub_apply, ht', hh', h0', integral_phiFactor_smul]
    have hheat : heatFactor t ξ = heatSymbol (t - 0) ξ := by
      simp only [heatFactor, heatSymbol, sub_zero, max_eq_left ht.1]
    rw [hheat, smul_comm ((heatSymbol (t - 0) ξ : ℝ) : ℂ) (((2 * π * ‖ξ‖ : ℝ)) : ℂ), ← smul_sub,
      hd t ht ξ, add_sub_cancel_left]

end Breakdown.SmoothFlow
