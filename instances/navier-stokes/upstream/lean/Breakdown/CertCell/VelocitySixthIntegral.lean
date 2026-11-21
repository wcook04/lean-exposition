import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.SixthPowerStatements

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private lemma continuous_matSq : Continuous matSq := by
  unfold matSq
  fun_prop

private lemma matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A := by
  unfold matSq
  positivity

private lemma rpow_sixth_le_one_add_rpow_third (a : ℝ≥0∞) :
    a ^ ((1 : ℝ) / 6) ≤ 1 + a ^ ((1 : ℝ) / 3) := by
  rcases le_total a 1 with h | h
  · exact (ENNReal.rpow_le_one h (by norm_num)).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)).trans le_add_self

private lemma ofReal_integral_eq_lintegral_of_lt_top {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (h0 : ∀ y, 0 ≤ f y) (hfin : ∫⁻ y, ENNReal.ofReal (f y) < ⊤) :
    ENNReal.ofReal (∫ y, f y) = ∫⁻ y, ENNReal.ofReal (f y) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf]
  exact ENNReal.ofReal_toReal hfin.ne

private lemma sixth_root_le_of_gradient {C : ℝ} (hC : SixthPowerGradientBound C) (w : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (hW : IsWeakGradient w G)
    (hwm : AEStronglyMeasurable w volume) (hGm : AEStronglyMeasurable G volume)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤) :
    (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) ^ ((1 : ℝ) / 6)
      ≤ 1 + ENNReal.ofReal (max C 0) * ∫⁻ y, ENNReal.ofReal (matSq (G y)) := by
  refine (rpow_sixth_le_one_add_rpow_third _).trans (add_le_add le_rfl ?_)
  have hA := ofReal_integral_eq_lintegral_of_lt_top (f := fun y => ‖w y‖ ^ 6)
    ((continuous_norm.pow 6).comp_aestronglyMeasurable hwm) (fun y => by positivity) h6
  have hB := ofReal_integral_eq_lintegral_of_lt_top (f := fun y => matSq (G y))
    (continuous_matSq.comp_aestronglyMeasurable hGm) (fun y => matSq_nonneg' (G y)) h2
  rw [← hA, ← hB, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (le_max_right C 0)]
  apply ENNReal.ofReal_le_ofReal
  refine (hC w G hW h6 h2).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left C 0) (integral_nonneg fun y => matSq_nonneg' (G y))

theorem velocitySixthIntegral (hS : ∃ C : ℝ, SixthPowerGradientBound C) : VelocitySixthIntegralHolds := by
  obtain ⟨C, hC⟩ := hS
  intro Γ P v G H g hp
  have hvm := hp.measurable_velocity
  have hGm := hp.measurable_gradient
  rw [Measure.volume_eq_prod] at hvm hGm
  have hBm : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y)))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine AEMeasurable.restrict ?_
    exact AEMeasurable.lintegral_prod_right' (f := fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2)))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_matSq.comp_aestronglyMeasurable hGm).aemeasurable)
  have hfin : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ := hp.gradient_finite
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6)
        ≤ 1 + ENNReal.ofReal (max C 0) * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    have h1 := ae_lt_top' hBm hfin.ne
    have h2 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1)
      (hp.weak_gradient.and (hp.sixth_power.and (hvm.prodMk_left.and hGm.prodMk_left)))
    filter_upwards [h1, h2] with σ hB hσ
    exact sixth_root_le_of_gradient hC (v σ) (G σ) hσ.1 hσ.2.2.1 hσ.2.2.2 hσ.2.1 hB
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩
  simp

end Bridge

end CertCell

end Breakdown
