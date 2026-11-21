import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem ae_of_ae_unitInterval {p : ℝ → Prop} (hper : ∀ σ, p (Int.fract σ) → p σ)
    (h : ∀ᵐ σ, σ ∈ Set.Icc (0 : ℝ) 1 → p σ) : ∀ᵐ σ, p σ := by
  have hn : ∀ n : ℤ, ∀ᵐ σ : ℝ, σ - (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 → p (σ - (n : ℝ)) := fun n =>
    (measurePreserving_sub_right volume (n : ℝ)).quasiMeasurePreserving.ae h
  rw [← ae_all_iff] at hn
  filter_upwards [hn] with σ hσ
  apply hper
  have hf : σ - ((⌊σ⌋ : ℤ) : ℝ) = Int.fract σ := Int.self_sub_floor σ
  have hmem := hσ ⌊σ⌋
  rw [hf] at hmem
  exact hmem ⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩

theorem continuous_matSq_fun : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_id.clm_apply continuous_const).norm).pow 2

theorem continuous_secondDerivTrace_fun : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem slice_lintegral_ae_lt_top {E : Type*} [TopologicalSpace E] (F : ℝ → Space → E)
    (φ : E → ℝ) (hφ : Continuous φ)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hper : ∀ σ y, F (σ + 1) y = F σ y)
    (hfin : periodLIntegral (fun σ y => φ (F σ y)) < ⊤) :
    ∀ᵐ σ, (∫⁻ y, ENNReal.ofReal (φ (F σ y))) < ⊤ := by
  have hjoint : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (φ (F z.1 z.2))) volume :=
    (hφ.comp_aestronglyMeasurable hF).aemeasurable.ennreal_ofReal
  have hslice : AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (φ (F σ y))) volume :=
    hjoint.lintegral_prod_right'
  have hIcc : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (∫⁻ y, ENNReal.ofReal (φ (F σ y))) < ⊤ :=
    ae_lt_top' hslice.restrict hfin.ne
  have hper' : Function.Periodic (fun σ => ∫⁻ y, ENNReal.ofReal (φ (F σ y))) 1 := by
    intro σ
    simp only [hper]
  apply ae_of_ae_unitInterval
  · intro σ hσ
    have h1 := hper'.sub_int_mul_eq (x := σ) ⌊σ⌋
    rw [mul_one, Int.self_sub_floor] at h1
    rw [← h1]
    exact hσ
  · exact (ae_restrict_iff' measurableSet_Icc).1 hIcc

end Internal

theorem perturbationSliceHolds : PerturbationSliceHolds := by
  intro Γ P v G H g hp
  have hG := Internal.slice_lintegral_ae_lt_top G matSq Internal.continuous_matSq_fun
    hp.measurable_gradient hp.periodic_gradient hp.gradient_finite
  have hH := Internal.slice_lintegral_ae_lt_top H (fun h => ‖secondDerivTrace h‖ ^ 2)
    (Internal.continuous_secondDerivTrace_fun.norm.pow 2)
    hp.measurable_secondDeriv hp.periodic_secondDeriv hp.sumSecondPartials_finite
  filter_upwards [hp.weak_gradient, hp.weak_secondDeriv, hp.sixth_power, hG, hH] with σ h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end CertReduction

end Breakdown
