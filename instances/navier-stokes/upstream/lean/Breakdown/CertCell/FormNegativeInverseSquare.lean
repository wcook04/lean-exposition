import Breakdown.CertCell.TopStatements
import Breakdown.FracCert.InverseSquare

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal

private theorem matSq_nonneg_slice (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem matSq_continuous_slice : Continuous matSq := by
  unfold matSq
  fun_prop

theorem slice_inverseSquare_lintegral (w : Space → Space) (A : Space → (Space →L[ℝ] Space))
    (hw : AEStronglyMeasurable w volume) (hA : AEStronglyMeasurable A volume)
    (hg : IsWeakGradient w A) (h6 : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * ∫⁻ y, ENNReal.ofReal (matSq (A y)) := by
  by_cases hfin : ∫⁻ y, ENNReal.ofReal (matSq (A y)) = ⊤
  · rw [hfin, ENNReal.mul_top (by norm_num)]
    exact le_top
  have heq : (fun y => SteadyCert.entrySq (A y)) = fun y => matSq (A y) := rfl
  have hm : AEStronglyMeasurable (fun y => matSq (A y)) volume :=
    matSq_continuous_slice.comp_aestronglyMeasurable hA
  have hint : Integrable (fun y => SteadyCert.entrySq (A y)) := by
    rw [heq]
    exact ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => matSq_nonneg_slice _)).2
      (lt_top_iff_ne_top.2 hfin)⟩
  have h6i : Integrable (fun y => ‖w y‖ ^ 6) :=
    ⟨hw.norm.pow 6, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 h6⟩
  have hL6 : MemLp w 6 volume := by
    refine (integrable_norm_rpow_iff hw (by norm_num) (by norm_num)).1 ?_
    simpa using h6i
  have hwg : SteadyCert.IsWeakGradientOf w A := by
    intro φ hφ j
    rw [hg.2.2 φ hφ j, neg_neg]
  obtain ⟨hi, hle⟩ := SteadyCert.inverseSquareBound w A hw hL6 hint hwg
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => by positivity)]
  have hE : ∫⁻ y, ENNReal.ofReal (matSq (A y)) = ENNReal.ofReal (∫ y, SteadyCert.entrySq (A y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => matSq_nonneg_slice _)]
    rfl
  rw [hE, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hle

end Internal

theorem perturbation_inverseSquare (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * periodLIntegral (fun σ y => matSq (G σ y)) := by
  have hvs : ∀ᵐ σ, AEStronglyMeasurable (v σ) volume := hv.measurable_velocity.prodMk_left
  have hGs : ∀ᵐ σ, AEStronglyMeasurable (G σ) volume := hv.measurable_gradient.prodMk_left
  have hpt : ∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hvs, hGs, hv.weak_gradient, hv.sixth_power] with σ h1 h2 h3 h4
    exact Internal.slice_inverseSquare_lintegral (v σ) (G σ) h1 h2 h3 h4
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ (by norm_num)]
  exact lintegral_mono_ae (ae_restrict_of_ae hpt)

end CertCell

end Breakdown
