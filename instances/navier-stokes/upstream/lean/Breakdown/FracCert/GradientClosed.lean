import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.SolenoidalSplit
import Breakdown.FracCert.GradientOrthogonal

open scoped ContDiff ENNReal InnerProductSpace
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown.SteadyCert

namespace GradientClosedInternal

open Internal.SolenoidalSplit

theorem gradient_congr {Q Q' : Space → Space} (hQ : IsGradientField Q) (h' : MemLp Q' 2 volume)
    (he : Q =ᵐ[volume] Q') : IsGradientField Q' := by
  obtain ⟨q, hq, -, -, hw⟩ := hQ
  refine ⟨q, hq, fun K _ => (h'.integrable_norm_pow two_ne_zero).integrableOn, h'.1, fun φ hφ j => ?_⟩
  rw [hw φ hφ j]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [he] with y hy
  rw [hy]

theorem norm_sub_sq (f g : L2F) {F G : Space → Space} (hf : (f : Space → Space) =ᵐ[volume] F)
    (hg : (g : Space → Space) =ᵐ[volume] G) : ‖f - g‖ ^ 2 = ∫ y, ‖F y - G y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g, hf, hg] with y h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, real_inner_self_eq_norm_sq]

theorem closed_of_orthogonal (horth : GradientOrthogonalStatement) : GradientClosedStatement := by
  intro Q Q₀ hg hL h0L ht
  let u : L2F := h0L.toLp Q₀
  let un : ℕ → L2F := fun n => (hL n).toLp (Q n)
  have hconv : Tendsto un atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : (fun n => ‖un n - u‖) = fun n => Real.sqrt (∫ y, ‖Q n y - Q₀ y‖ ^ 2) := by
      funext n
      rw [← norm_sub_sq _ _ (hL n).coeFn_toLp h0L.coeFn_toLp, Real.sqrt_sq (norm_nonneg _)]
    rw [hs]
    have h := (Real.continuous_sqrt.tendsto 0).comp ht
    rw [Real.sqrt_zero] at h
    exact h
  have hmem : u ∈ gradClosure := by
    rw [← Submodule.orthogonal_orthogonal gradClosure, Submodule.mem_orthogonal]
    intro z hz
    have hzero : ∀ n, inner ℝ z (un n) = 0 := by
      intro n
      rw [MeasureTheory.L2.inner_def, ← horth (Q n) z (hg n) (hL n) (solenoidal_of_mem hz)]
      refine integral_congr_ae ?_
      filter_upwards [(hL n).coeFn_toLp] with y hy
      rw [hy, real_inner_comm]
    have hlim : Tendsto (fun n => inner ℝ z (un n)) atTop (𝓝 (inner ℝ z u)) :=
      tendsto_const_nhds.inner hconv
    simp only [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  exact gradient_congr (gradient_of_mem hmem) h0L h0L.coeFn_toLp

end GradientClosedInternal

theorem gradientClosed_of_orthogonal (h : GradientOrthogonalStatement) : GradientClosedStatement :=
  GradientClosedInternal.closed_of_orthogonal h

theorem gradientClosed : GradientClosedStatement :=
  gradientClosed_of_orthogonal gradientOrthogonal

end Breakdown.SteadyCert
