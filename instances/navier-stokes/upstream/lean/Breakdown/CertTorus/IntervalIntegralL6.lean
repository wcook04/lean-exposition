import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.IntervalIntegralL6

private lemma lintegral_enorm_le (h : L6R) (K : Set Space) :
    ∫⁻ y in K, ‖(h : Space → Space) y‖ₑ ≤ ‖h‖ₑ * volume K ^ (5 / 6 : ℝ) := by
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) = (5 / 6 : ℝ) := by
    rw [ENNReal.toReal_one, ENNReal.toReal_ofNat]; norm_num
  calc eLpNorm (h : Space → Space) 1 (volume.restrict K)
      ≤ eLpNorm (h : Space → Space) 6 (volume.restrict K) *
          (volume.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (Lp.aestronglyMeasurable h).restrict
    _ ≤ ‖h‖ₑ * volume K ^ (5 / 6 : ℝ) := by
        rw [Measure.restrict_apply_univ, Lp.enorm_def, hexp]
        gcongr
        exact Measure.restrict_le_self

private lemma integrableOn_of_mem (h : L6R) {K : Set Space} (hK : volume K < ∞) :
    IntegrableOn (h : Space → Space) K := by
  refine ⟨(Lp.aestronglyMeasurable h).restrict, ?_⟩
  unfold HasFiniteIntegral
  exact (lintegral_enorm_le h K).trans_lt
    (ENNReal.mul_lt_top enorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.ne))

def setIntegralL6 (K : Set Space) (hK : volume K < ∞) : L6R →L[ℝ] Space :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ y in K, (h : Space → Space) y
      map_add' := fun h₁ h₂ => by
        rw [← integral_add (integrableOn_of_mem h₁ hK) (integrableOn_of_mem h₂ hK)]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add h₁ h₂))
      map_smul' := fun c h => by
        rw [RingHom.id_apply, ← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c h)) }
    ((volume K ^ (5 / 6 : ℝ)).toReal) (fun h => by
      have h1 := (enorm_integral_le_lintegral_enorm (μ := volume.restrict K)
        (fun y => (h : Space → Space) y)).trans (lintegral_enorm_le h K)
      show ‖∫ y in K, (h : Space → Space) y‖ ≤ _
      rw [← toReal_enorm (∫ y in K, (h : Space → Space) y), ← toReal_enorm h, mul_comm,
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top enorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.ne)) h1)

lemma setIntegralL6_apply (K : Set Space) (hK : volume K < ∞) (h : L6R) :
    setIntegralL6 K hK h = ∫ y in K, (h : Space → Space) y := rfl

end Internal.IntervalIntegralL6

open Internal.IntervalIntegralL6 in
theorem intervalIntegralL6_holds : IntervalIntegralL6 := by
  intro f a b hab hf G hG hfG
  simp_rw [intervalIntegral.integral_of_le hab]
  have hfi : Integrable f (volume.restrict (Ioc a b)) := hf.1
  have hIoo : ∀ᵐ σ ∂(volume.restrict (Ioc a b)), σ ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hprod : ∀ K : Set Space, volume K < ∞ →
      Integrable (fun p : ℝ × Space => G p.1 p.2) ((volume.restrict (Ioc a b)).prod (volume.restrict K)) := by
    intro K hK
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (hG.enorm.aemeasurable)]
    calc ∫⁻ σ, (∫⁻ y in K, ‖G σ y‖ₑ) ∂(volume.restrict (Ioc a b))
        ≤ ∫⁻ σ, ‖f σ‖ₑ * volume K ^ (5 / 6 : ℝ) ∂(volume.restrict (Ioc a b)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hIoo] with σ hσ
          calc ∫⁻ y in K, ‖G σ y‖ₑ
              = ∫⁻ y in K, ‖(f σ : Space → Space) y‖ₑ :=
                lintegral_congr_ae (ae_restrict_of_ae ((hfG σ hσ).mono fun y hy => by
                  dsimp only; rw [hy]))
            _ ≤ ‖f σ‖ₑ * volume K ^ (5 / 6 : ℝ) := lintegral_enorm_le (f σ) K
      _ = (∫⁻ σ, ‖f σ‖ₑ ∂(volume.restrict (Ioc a b))) * volume K ^ (5 / 6 : ℝ) :=
          lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.ne)
      _ < ∞ := ENNReal.mul_lt_top hfi.2 (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.ne)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun K _ hK => integrableOn_of_mem _ hK) (fun K _ hK => (hprod K hK).integral_prod_right) ?_
  intro K _ hK
  rw [← setIntegralL6_apply K hK, ← (setIntegralL6 K hK).integral_comp_comm hfi]
  have e2 : ∫ σ, setIntegralL6 K hK (f σ) ∂(volume.restrict (Ioc a b)) =
      ∫ σ, (∫ y in K, G σ y) ∂(volume.restrict (Ioc a b)) := by
    refine integral_congr_ae ?_
    filter_upwards [hIoo] with σ hσ
    exact integral_congr_ae (ae_restrict_of_ae (hfG σ hσ))
  rw [e2]
  exact integral_integral_swap (hprod K hK)

end Breakdown.FarField
