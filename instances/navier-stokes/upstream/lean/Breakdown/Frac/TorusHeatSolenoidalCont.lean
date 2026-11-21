import Breakdown.Frac.StTorusShell
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace FracHeatProjCont.Internal

open Breakdown.Freq Breakdown.Freq.Internal.Phi

def fracPhiOp (α τ : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)

theorem factor_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor; positivity

theorem factor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ 1 + τ⁻¹ := by
  unfold fracPhiFactor
  set s := 2 * π * ‖ξ‖ with hs_def
  have hs : 0 ≤ s := by positivity
  have hq : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
  have he : Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  rcases le_or_gt s 1 with h1 | h1
  · have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
      calc s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 * 1 :=
            mul_le_mul h1 he (Real.exp_pos _).le zero_le_one
        _ = 1 := by ring
    linarith
  · have hsp : s ≤ s ^ (2 * α) := by
      calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hex := Real.add_one_le_exp (τ * s ^ (2 * α))
    have heq : Real.exp (-(τ * s ^ (2 * α))) * Real.exp (τ * s ^ (2 * α)) = 1 := by
      rw [← Real.exp_add]; simp
    have hk : τ * (s * Real.exp (-(τ * s ^ (2 * α)))) ≤ 1 := by
      have hE := Real.exp_pos (-(τ * s ^ (2 * α)))
      have h3 : τ * s ≤ Real.exp (τ * s ^ (2 * α)) := by nlinarith
      calc τ * (s * Real.exp (-(τ * s ^ (2 * α))))
          = (τ * s) * Real.exp (-(τ * s ^ (2 * α))) := by ring
        _ ≤ Real.exp (τ * s ^ (2 * α)) * Real.exp (-(τ * s ^ (2 * α))) :=
            mul_le_mul_of_nonneg_right h3 hE.le
        _ = 1 := by rw [mul_comm]; exact heq
    have hk2 : s * Real.exp (-(τ * s ^ (2 * α))) ≤ τ⁻¹ := by
      calc s * Real.exp (-(τ * s ^ (2 * α)))
          = τ⁻¹ * (τ * (s * Real.exp (-(τ * s ^ (2 * α))))) := by field_simp
        _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left hk hti.le
        _ = τ⁻¹ := mul_one _
    linarith

theorem abs_factor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    |fracPhiFactor α τ ξ| ≤ 1 + τ⁻¹ := by
  rw [abs_of_nonneg (factor_nonneg α τ ξ)]
  exact factor_le hα hτ ξ

theorem continuous_factor {α : ℝ} (hα : 1 < α) (τ : ℝ) : Continuous (fracPhiFactor α τ) := by
  unfold fracPhiFactor
  have h : Continuous (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) :=
    (by fun_prop : Continuous (fun ξ : Space => 2 * π * ‖ξ‖)).rpow_const
      (fun _ => Or.inr (by linarith))
  fun_prop

theorem continuous_factor_time (α : ℝ) (ξ : Space) :
    Continuous (fun τ => fracPhiFactor α τ ξ) := by
  unfold fracPhiFactor
  fun_prop

theorem fracPhiOp_ae {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (g : L2C) :
    (fracPhiOp α τ g : Space → CSpace) =ᵐ[volume]
      fun ξ => fracPhiFactor α τ ξ • (g : Space → CSpace) ξ :=
  scalarOp_ae fieldOpRealized_holds (continuous_factor hα τ) (abs_factor_le hα hτ) g

theorem sub_sq_factor_le {α τ₀ τ : ℝ} (hα : 1 < α) (hτ₀ : 0 < τ₀) (hτ : τ₀ / 2 < τ)
    (ξ : Space) :
    (fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ) ^ 2 ≤ (2 * (1 + 2 / τ₀)) ^ 2 := by
  have hpos : 0 < τ := by linarith
  have h1 := factor_le hα hpos ξ
  have h2 := factor_le hα hτ₀ ξ
  have n1 := factor_nonneg α τ ξ
  have n2 := factor_nonneg α τ₀ ξ
  have h3 : τ⁻¹ ≤ 2 / τ₀ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hpos hτ₀]
    linarith
  have h4 : τ₀⁻¹ ≤ 2 / τ₀ := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) hτ₀.le
  have hab : |fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ| ≤ 2 * (1 + 2 / τ₀) := by
    rw [abs_le]; constructor <;> linarith
  calc (fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ) ^ 2
      = |fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * (1 + 2 / τ₀)) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) hab 2

theorem fracPhiOp_continuousOn {α : ℝ} (hα : 1 < α) (g : L2C) :
    ContinuousOn (fun τ => fracPhiOp α τ g) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ τ, 0 < τ → ‖fracPhiOp α τ g - fracPhiOp α τ₀ g‖ ^ 2 =
      ∫ ξ, (fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ) ^ 2 * ‖(g : Space → CSpace) ξ‖ ^ 2 := by
    intro τ hτ
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (fracPhiOp α τ g) (fracPhiOp α τ₀ g), fracPhiOp_ae hα hτ g,
      fracPhiOp_ae hα hτ₀' g] with ξ hs ha hb
    rw [hs, Pi.sub_apply, ha, hb, ← sub_smul, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ξ => ‖(g : Space → CSpace) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hev : ∀ᶠ τ in 𝓝[Ioi 0] τ₀, τ₀ / 2 < τ :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
  have hlim : Tendsto (fun τ => ∫ ξ, (fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ) ^ 2 *
      ‖(g : Space → CSpace) ξ‖ ^ 2) (𝓝[Ioi 0] τ₀)
      (𝓝 (∫ ξ, (fracPhiFactor α τ₀ ξ - fracPhiFactor α τ₀ ξ) ^ 2 *
        ‖(g : Space → CSpace) ξ‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (2 * (1 + 2 / τ₀)) ^ 2 * ‖(g : Space → CSpace) ξ‖ ^ 2) ?_ ?_
      (hint.const_mul _) ?_
    · refine Eventually.of_forall fun τ => ?_
      exact ((((continuous_factor hα τ).sub (continuous_factor hα τ₀)).pow 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable g).norm.pow 2))
    · filter_upwards [hev] with τ hτ
      refine Eventually.of_forall fun ξ => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (sub_sq_factor_le hα hτ₀' hτ ξ) (by positivity)
    · refine Eventually.of_forall fun ξ => ?_
      have hc : Continuous (fun τ => (fracPhiFactor α τ ξ - fracPhiFactor α τ₀ ξ) ^ 2 *
          ‖(g : Space → CSpace) ξ‖ ^ 2) :=
        (((continuous_factor_time α ξ).sub continuous_const).pow 2).mul continuous_const
      exact (hc.tendsto τ₀).mono_left nhdsWithin_le_nhds
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    integral_zero] at hlim
  have hsq : Tendsto (fun τ => ‖fracPhiOp α τ g - fracPhiOp α τ₀ g‖ ^ 2) (𝓝[Ioi 0] τ₀) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (heq τ hτ).symm
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end FracHeatProjCont.Internal

open FracHeatProjCont.Internal in
theorem fracHeatSolenoidalContinuous (α : ℝ) (hα : 1 < α) : FracHeatSolenoidalContinuous α := by
  intro A
  exact Freq.projX.continuous.comp_continuousOn
    (fracPhiOp_continuousOn hα (Freq.freqTrR (Freq.complexify A)))

end Breakdown.Periodic
