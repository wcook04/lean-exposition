import Breakdown.FreqTr.Phi

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace HeatDivFreeCont.Internal

open Breakdown.Freq Breakdown.Freq.Internal.Phi

def phiOp (τ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace)

theorem continuous_phiFactor_time (ξ : Space) : Continuous (fun τ => phiFactor τ ξ) := by
  unfold phiFactor
  fun_prop

theorem phiOp_ae (h : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (g : L2C) :
    (phiOp τ g : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • (g : Space → CSpace) ξ :=
  scalarOp_ae h (continuous_phiFactor τ) (phiFactor_le hτ) g

theorem sub_sq_phiFactor_le {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hτ : τ₀ / 2 < τ) (ξ : Space) :
    (phiFactor τ ξ - phiFactor τ₀ ξ) ^ 2 ≤ 6 / τ₀ := by
  have hpos : 0 < τ := by linarith
  have h1 : phiFactor τ ξ ^ 2 ≤ τ⁻¹ := phiFactor_sq_le hpos ξ
  have h2 : phiFactor τ₀ ξ ^ 2 ≤ τ₀⁻¹ := phiFactor_sq_le hτ₀ ξ
  have h3 : τ⁻¹ ≤ 2 / τ₀ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hpos hτ₀]
    linarith
  have h4 : τ₀⁻¹ = 1 / τ₀ := inv_eq_one_div τ₀
  have h5 : 6 / τ₀ = 2 * (2 / τ₀) + 2 * (1 / τ₀) := by ring
  rw [h5]
  nlinarith [sq_nonneg (phiFactor τ ξ + phiFactor τ₀ ξ)]

theorem phiOp_continuousOn (h : FieldOpRealized) (g : L2C) :
    ContinuousOn (fun τ => phiOp τ g) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ τ, 0 < τ → ‖phiOp τ g - phiOp τ₀ g‖ ^ 2 =
      ∫ ξ, (phiFactor τ ξ - phiFactor τ₀ ξ) ^ 2 * ‖(g : Space → CSpace) ξ‖ ^ 2 := by
    intro τ hτ
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (phiOp τ g) (phiOp τ₀ g), phiOp_ae h hτ g, phiOp_ae h hτ₀' g]
      with ξ hs ha hb
    rw [hs, Pi.sub_apply, ha, hb, ← sub_smul, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ξ => ‖(g : Space → CSpace) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hev : ∀ᶠ τ in 𝓝[Ioi 0] τ₀, τ₀ / 2 < τ :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
  have hlim : Tendsto (fun τ => ∫ ξ, (phiFactor τ ξ - phiFactor τ₀ ξ) ^ 2 *
      ‖(g : Space → CSpace) ξ‖ ^ 2) (𝓝[Ioi 0] τ₀)
      (𝓝 (∫ ξ, (phiFactor τ₀ ξ - phiFactor τ₀ ξ) ^ 2 * ‖(g : Space → CSpace) ξ‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => 6 / τ₀ * ‖(g : Space → CSpace) ξ‖ ^ 2) ?_ ?_ (hint.const_mul _) ?_
    · refine Eventually.of_forall fun τ => ?_
      exact ((((continuous_phiFactor τ).sub (continuous_phiFactor τ₀)).pow 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable g).norm.pow 2))
    · filter_upwards [hev] with τ hτ
      refine Eventually.of_forall fun ξ => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (sub_sq_phiFactor_le hτ₀' hτ ξ) (by positivity)
    · refine Eventually.of_forall fun ξ => ?_
      have hc : Continuous (fun τ => (phiFactor τ ξ - phiFactor τ₀ ξ) ^ 2 *
          ‖(g : Space → CSpace) ξ‖ ^ 2) :=
        (((continuous_phiFactor_time ξ).sub continuous_const).pow 2).mul continuous_const
      exact (hc.tendsto τ₀).mono_left nhdsWithin_le_nhds
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    integral_zero] at hlim
  have hsq : Tendsto (fun τ => ‖phiOp τ g - phiOp τ₀ g‖ ^ 2) (𝓝[Ioi 0] τ₀) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (heq τ hτ).symm
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end HeatDivFreeCont.Internal

open HeatDivFreeCont.Internal in
theorem heatDivFree_continuousOn (h : Freq.FieldOpRealized) :
    ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0) := by
  intro A
  exact Freq.projX.continuous.comp_continuousOn
    (phiOp_continuousOn h (Freq.freqTrR (Freq.complexify A)))

end Breakdown.Periodic
