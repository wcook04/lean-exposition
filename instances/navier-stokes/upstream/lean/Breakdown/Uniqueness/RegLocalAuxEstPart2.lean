import Breakdown.Uniqueness.RegLocalAuxSymm

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem measurable_convC_of {p q : Space → ℂ} (hp : StronglyMeasurable p)
    (hq : StronglyMeasurable q) : Measurable (convC p q) := by
  have h : StronglyMeasurable (Function.uncurry fun ξ η : Space => p η * q (ξ - η)) :=
    (hp.comp_measurable measurable_snd).mul (hq.comp_measurable (measurable_fst.sub measurable_snd))
  exact (h.integral_prod_right (ν := (volume : Measure Space))).measurable

private theorem measurable_advectionBilin_self {f : Space → CSpace} (hf : StronglyMeasurable f) :
    Measurable (advectionBilin f f) := by
  unfold advectionBilin
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_lambda _ fun i => ?_
  refine Finset.measurable_sum _ fun j _ => measurable_convC_of ?_ ?_
  · exact (PiLp.continuous_apply 2 _ j).comp_stronglyMeasurable hf
  · refine (Continuous.stronglyMeasurable ?_).mul
      ((PiLp.continuous_apply 2 _ i).comp_stronglyMeasurable hf)
    fun_prop

private theorem measurable_divFreeC_comp {g : Space → CSpace} (hg : Measurable g) :
    Measurable (fun ξ => divFreeC ξ (g ξ)) := by
  have hc : ∀ i : Fin 3, Measurable (fun ξ => g ξ i) := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable.comp hg
  have hf : Measurable (fun ξ : Space => freqVec ξ) := complexifyVec.continuous.measurable
  have hs : Measurable (fun ξ : Space => ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * g ξ i)) := by
    refine Measurable.mul ?_ (Finset.measurable_sum _ fun i _ => ?_)
    · exact Complex.measurable_ofReal.comp ((measurable_norm.pow_const 2).inv)
    · exact (Complex.measurable_ofReal.comp ((PiLp.continuous_apply 2 _ i).measurable)).mul (hc i)
  unfold divFreeC
  exact hg.sub (hs.smul hf)

theorem measurable_nonlinSymbol {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    Measurable (nonlinSymbol f) := by
  rw [nonlinSymbol_congr_ae hf.ae_eq_mk]
  exact (measurable_divFreeC_comp (measurable_advectionBilin_self hf.stronglyMeasurable_mk)).neg

theorem exists_measurable_nonlin_curve {G : ℝ → Space → CSpace} {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ s ∈ Icc a b, AEStronglyMeasurable (G s) volume)
    (hc : ∀ ξ, ContinuousOn (fun s => nonlinSymbol (G s) ξ) (Icc a b)) :
    ∃ u : ℝ → Space → CSpace, Measurable (Function.uncurry u) ∧
      ∀ s ∈ Icc a b, u s = nonlinSymbol (G s) := by
  refine ⟨fun s => nonlinSymbol (G (projIcc a b hab s : ℝ)), ?_, ?_⟩
  · refine measurable_uncurry_of_continuous_of_measurable (fun ξ => ?_) (fun s => ?_)
    · exact (hc ξ).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun s => (projIcc a b hab s).2)
    · exact measurable_nonlinSymbol (hmeas _ (projIcc a b hab s).2)
  · intro s hs
    simp only [projIcc_of_mem hab hs]

end Breakdown.SmoothFlow
